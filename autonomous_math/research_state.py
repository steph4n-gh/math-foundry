"""Durable run snapshots and validation of content-bound Lean verification receipts."""
from __future__ import annotations

import fcntl
import hashlib
import json
import os
from pathlib import Path
import time
import math
import threading
import copy
from functools import lru_cache
from contextlib import contextmanager

ROOT = Path(__file__).resolve().parent.parent
ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
_fingerprint_cache = {}
_fingerprint_lock = threading.RLock()


def json_safe(value):
    if isinstance(value, float) and not math.isfinite(value):
        return {"$float": str(value)}
    if isinstance(value, dict):
        return {k: json_safe(v) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [json_safe(v) for v in value]
    return value


def json_restore(value):
    return float(value["$float"]) if set(value) == {"$float"} else value


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def atomic_save_json(data, path) -> None:
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.{time.time_ns()}.tmp")
    try:
        with temporary.open("w", encoding="utf-8") as stream:
            json.dump(json_safe(data), stream, indent=2, allow_nan=False)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
        fd = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(fd)
        finally:
            os.close(fd)
    finally:
        temporary.unlink(missing_ok=True)


def atomic_save_text(text, path):
    path = Path(path)
    expected = hashlib.sha256(text.encode()).hexdigest()
    if path.exists():
        if sha256(path) != expected:
            raise ValueError(f"Immutable artifact was changed: {path}")
        return
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    try:
        with temporary.open("w") as stream:
            stream.write(text)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    finally:
        temporary.unlink(missing_ok=True)


@contextmanager
def writer_lock(directory):
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    with (directory / ".writer.lock").open("a+") as stream:
        try:
            fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise RuntimeError(f"Another research writer owns {directory}") from exc
        try:
            yield
        finally:
            fcntl.flock(stream, fcntl.LOCK_UN)


def workspace_fingerprint(workspace) -> str:
    """Bind receipts to source and compiled dependencies, including local changes."""
    with _fingerprint_lock:
        return _workspace_fingerprint(workspace)


def _workspace_fingerprint(workspace) -> str:
    workspace = Path(workspace).resolve()
    paths = []
    for directory, subdirectories, files in os.walk(workspace):
        subdirectories[:] = [name for name in subdirectories if name != ".git"]
        paths.extend(Path(directory) / name for name in files
                     if Path(name).suffix in {".lean", ".olean", ".so", ".dylib"}
                     or name in {"lean-toolchain", "lake-manifest.json"})
    paths.sort()
    signature = tuple((str(p), stat.st_mtime_ns, stat.st_size)
                      for p in paths for stat in [p.stat()])
    cached = _fingerprint_cache.get(str(workspace))
    if cached and cached[0] == signature:
        return cached[1]
    digest = hashlib.sha256()
    for path in paths:
        digest.update(str(path.relative_to(workspace)).encode())
        digest.update(sha256(path).encode())
    result = digest.hexdigest()
    _fingerprint_cache[str(workspace)] = (signature, result)
    return result


def validate_receipt(receipt_path, expected_id=None, fingerprints=None):
    """Return receipt or a reason it cannot support certification."""
    try:
        receipt = json.loads(Path(receipt_path).read_text())
        if receipt.get("schema_version") != 1 or receipt.get("status") != "KERNEL_VERIFIED":
            raise ValueError("No kernel verification receipt")
        if expected_id is not None and receipt.get("conjecture_id") != expected_id:
            raise ValueError("Receipt belongs to another conjecture")
        if not set(receipt["axioms"]).issubset(ALLOWED_AXIOMS):
            raise ValueError("Nonpermitted axiom dependency")
        if not receipt.get("statement_checked") or receipt.get("duration_ms", -1) < 0:
            raise ValueError("Incomplete verification receipt")
        for field in ("source", "challenge"):
            if sha256(Path(receipt[f"{field}_path"])) != receipt[f"{field}_sha256"]:
                raise ValueError(f"Changed {field} artifact")
        source = Path(receipt["source_path"]).read_text()
        challenge = Path(receipt["challenge_path"]).read_text()
        # Local `have ... := by` blocks belong to the proof, not its statement.
        # Locate the target declaration before finding its first proof delimiter.
        import re
        name = receipt["theorem_name"].split(".")[-1]
        def target_prefix(code):
            matches = list(re.finditer(r"\btheorem\s+" + re.escape(name) + r"(?=\s|[({:])", code))
            if not matches:
                raise ValueError("Missing target theorem declaration")
            delimiter = code.find(":= by", matches[-1].end())
            if delimiter < 0:
                raise ValueError("Missing target theorem proof")
            return code[:delimiter]
        if target_prefix(source) != target_prefix(challenge):
            raise ValueError("Changed theorem statement")
        if receipt.get("conjecture"):
            from autonomous_math.core.ast import Conjecture
            from autonomous_math.prover.trusted_lean import render_challenge
            expected, name = render_challenge(Conjecture.from_dict(receipt["conjecture"]))
            expected_target = expected[expected.index(f"theorem {name} "):].split(":= by", 1)[0]
            actual_target = challenge[challenge.rindex(f"theorem {name} "):].split(":= by", 1)[0]
            if actual_target != expected_target:
                raise ValueError("Lean statement does not match the structured conjecture")
        workspace = receipt["workspace"]
        if fingerprints is None:
            fingerprint = workspace_fingerprint(workspace)
        else:
            if workspace not in fingerprints:
                fingerprints[workspace] = workspace_fingerprint(workspace)
            fingerprint = fingerprints[workspace]
        if fingerprint != receipt["workspace_sha256"]:
            raise ValueError("Changed proof dependencies")
        if sha256(Path(receipt["lean_binary"])) != receipt["lean_binary_sha256"]:
            raise ValueError("Changed Lean compiler")
        return receipt, None
    except (OSError, ValueError, KeyError, TypeError) as exc:
        return None, str(exc)


def reconcile(atlas):
    """Derive current result counts; historical generation counts are separate."""
    records = list(atlas.get("theorems", {}).values())
    fingerprints = {}
    for record in records:
        proof = record.get("lean_proof") or {}
        receipt, error = validate_receipt(proof.get("receipt_path", ""), record["id"], fingerprints)
        if receipt and (not receipt.get("conjecture") or record.get("conjecture") != receipt.get("conjecture")):
            receipt, error = None, "Receipt does not match the stored conjecture AST"
        if receipt:
            from autonomous_math.core.ast import Conjecture
            record["statement"] = Conjecture.from_dict(receipt["conjecture"]).to_latex()
            record["status"] = "LEAN_CERTIFIED"
            record["lean_proof"] = {"verified": True, "receipt_path": proof["receipt_path"],
                "artifact_path": receipt["source_path"], "duration_ms": receipt["duration_ms"],
                "tactic": receipt.get("tactic"), "axioms": receipt["axioms"],
                "theorem_name": receipt["theorem_name"]}
            for field in ("proof_origin", "explanation", "explanation_status", "synthesis_attempts",
                          "used_lemma_ids", "transitive_used_lemma_ids", "context_lemma_ids", "reference_tracking"):
                if field in receipt:
                    record["lean_proof"][field] = receipt[field]
        elif proof or record.get("status") == "LEAN_CERTIFIED":
            record["legacy_proof"] = record.get("legacy_proof", proof)
            record["lean_proof"] = None
            record["verification_error"] = error
            if record.get("status") != "REFUTED":
                record["status"] = "UNVERIFIED"
    atlas["total_survived"] = sum(r.get("status") in {"EMPIRICAL_SURVIVOR", "LEAN_CERTIFIED"} for r in records)
    atlas["total_current_refuted"] = sum(r.get("status") == "REFUTED" for r in records)
    atlas["total_inconclusive"] = sum(r.get("status") in {"INCONCLUSIVE", "UNVERIFIED"} for r in records)
    atlas["total_lean_certified"] = sum(r.get("status") == "LEAN_CERTIFIED" for r in records)
    atlas["total_candidate_novel"] = 0  # an unmatched registry entry is not evidence of novelty
    atlas["total_unknown_literature"] = sum(r.get("novelty_status") not in
        {"VERIFIED_REDISCOVERY", "TEXTBOOK_FOLKLORE"} for r in records)
    atlas["total_verified_rediscoveries"] = sum(r.get("novelty_status") in
        {"VERIFIED_REDISCOVERY", "TEXTBOOK_FOLKLORE"} for r in records)
    return atlas


def proof_reuse_summary(atlas):
    """Observed references in validated proof records, not causal learning gains.

    Old receipts have no reference accounting. Keep those explicitly unknown
    instead of describing an unmeasured proof as using zero previous lemmas.
    """
    records = {key: r for key, r in atlas.get("theorems", {}).items() if r.get("status") == "LEAN_CERTIFIED"}
    tracked, reused, edges, usage, compositions = 0, 0, 0, {}, 0
    for key, record in records.items():
        proof = record.get("lean_proof") or {}
        if proof.get("reference_tracking") != "source_identifier_references":
            continue
        tracked += 1
        direct = (set(proof.get("used_lemma_ids", [])) & records.keys()) - {key}
        reused += bool(direct)
        edges += len(direct)
        for parent in direct:
            usage[parent] = usage.get(parent, 0) + 1
        if (record.get("conjecture", {}).get("metadata", {}).get("origin") == "checked_transitivity"
                and proof.get("proof_origin") != "codex_synthesis"):
            compositions += 1
    return {"tracked_proofs": tracked, "untracked_proofs": len(records) - tracked,
        "proofs_referencing_prior_lemmas": reused, "direct_reference_edges": edges,
        "distinct_referenced_lemmas": len(usage), "model_free_compositions": compositions,
        "lemma_use_counts": dict(sorted(usage.items(), key=lambda item: (-item[1], item[0]))),
        "interpretation": "References observed in checked proof source. Counts do not establish that a lemma was necessary or that search improved; older untracked receipts remain unknown."}


@lru_cache(maxsize=1)
def _validated_seed(content):
    """Validate the checked-in mathematical corpus once per exact file content."""
    from autonomous_math.core.ast import Conjecture
    from autonomous_math.sieve.certificates import CounterexampleCertificate, CounterexampleCertificateVerifier
    data = json.loads(content, object_hook=json_restore)
    if data.get("schema_version") != 1 or not isinstance(data.get("records"), list):
        raise ValueError("Invalid mathematical seed")
    records = {}
    for item in data["records"]:
        candidate = Conjecture.from_dict(item["conjecture"])
        cert = CounterexampleCertificate.from_dict(item["counterexample"])
        if item["id"] != candidate.id or cert.conjecture_id != candidate.id or cert.compute_hash() != cert.verification_hash:
            raise ValueError("Mathematical seed identity or hash mismatch")
        valid, errors = CounterexampleCertificateVerifier.verify_with_details(cert, candidate)
        if not valid:
            raise ValueError(f"Invalid mathematical seed refutation: {errors}")
        if candidate.id in records:
            raise ValueError("Duplicate mathematical seed identity")
        records[candidate.id] = dict(item, statement=candidate.statement, status="REFUTED", lean_proof=None,
            novelty_status="UNKNOWN_IN_LITERATURE", baseline_seed=True, discovered_iteration=0)
    return records


def load_snapshot(directory):
    path = Path(directory) / "cumulative_discovery_atlas.json"
    if not path.exists():
        seed_path = ROOT / "seed/counterexamples.json"
        records = copy.deepcopy(_validated_seed(seed_path.read_bytes())) if seed_path.exists() else {}
        return {"schema_version": 2, "total_iterations": 0, "total_conjectures_generated": 0,
                "total_refuted": 0, "theorems": records, "recent_refutations": [], "baseline_boundary_graphs": len(records)}
    atlas = json.loads(path.read_text(), object_hook=json_restore)
    if not isinstance(atlas, dict) or not isinstance(atlas.get("theorems"), dict):
        raise ValueError(f"Invalid research snapshot: {path}")
    return reconcile(atlas)
