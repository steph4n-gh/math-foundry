"""Read-only, bounded exports of checked mathematics and its research evidence."""
from __future__ import annotations

import argparse
import base64
from datetime import datetime, timezone
import hashlib
import io
import json
import os
from pathlib import Path
import re
import stat
import zipfile

from autonomous_math.core.ast import Conjecture
from autonomous_math.research_state import json_safe, validate_receipt

MAX_FILE_BYTES = 2 * 1024 * 1024
MAX_PACKET_BYTES = 12 * 1024 * 1024
SOURCE_LABELS = {"checked_local_theorem": "Checked local theorem", "local_mathlib": "Local Mathlib declaration excerpts",
                 "primary_literature": "Primary literature excerpts", "bibliographic_metadata": "Bibliographic metadata"}


def _json(value):
    return json.dumps(json_safe(value), indent=2, ensure_ascii=False, allow_nan=False) + "\n"


def _hash(raw):
    return hashlib.sha256(raw).hexdigest()


def _read(path, *, root=None, suffix=None):
    """Read a bounded regular file; never follow a symlink or a traversal path."""
    path = Path(path)
    if ".." in path.parts:
        raise ValueError("Parent traversal is not allowed in packet evidence paths")
    if root is not None:
        root = Path(root).absolute()
        path = path if path.is_absolute() else root / path
        if not path.absolute().is_relative_to(root):
            raise ValueError("Evidence is outside the research output directory")
    path = path.absolute()
    if any(part.is_symlink() for part in (path, *path.parents)):
        raise ValueError("Symlink evidence is not allowed")
    if suffix and path.suffix != suffix:
        raise ValueError("Unexpected evidence file type")
    info = path.stat()
    if not stat.S_ISREG(info.st_mode) or info.st_size > MAX_FILE_BYTES:
        raise ValueError("Evidence is not a bounded regular file")
    fd = os.open(path, os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0) | getattr(os, "O_NONBLOCK", 0))
    with os.fdopen(fd, "rb") as stream:
        info = os.fstat(stream.fileno())
        if not stat.S_ISREG(info.st_mode) or info.st_size > MAX_FILE_BYTES:
            raise ValueError("Evidence is not a bounded regular file")
        raw = stream.read(MAX_FILE_BYTES + 1)
    if len(raw) > MAX_FILE_BYTES:
        raise ValueError("Evidence exceeds the packet size limit")
    return raw


def proof_writeup(record, receipt=None):
    """Explain the checked AST; keep prospective model commentary visibly separate."""
    receipt = receipt or {}
    c = Conjecture.from_dict(record["conjecture"])
    metadata = record["conjecture"].get("metadata") or {}
    variables = c.lhs_expr.variables | c.rhs_expr.variables | (c.guard_predicate.variables if c.guard_predicate else set())
    guard = c.guard_predicate.to_latex() if c.guard_predicate else "True (all finite simple graphs)"
    relation = {"<=": "≤", ">=": "≥", "==": "="}.get(c.rel, c.rel)
    what = f"Lean proves {c.lhs_expr.to_latex()} {relation} {c.rhs_expr.to_latex()} under the guard {guard}. "
    universal = c.guard_predicate is None or c.guard_predicate.predicate_type == "universal"
    left, right = record["conjecture"]["lhs_expr"], record["conjecture"]["rhs_expr"]
    pair = ((left.get("name"), right.get("name")) if left.get("node_type") == right.get("node_type") == "invariant" else None)
    if c.rel == ">=" and pair:
        pair = pair[::-1]
    if c.rel not in {"<=", ">="}:
        pair = None
    foundation = {
        ("chromatic_number", "order"): (
            "Every finite simple graph can be colored using no more colors than it has vertices: give each vertex its own color and adjacent vertices automatically differ.",
            "This familiar ceiling on chromatic number is a base case for coloring arguments. A checked proof can be combined with lower bounds, such as clique number, to constrain other graph parameters."),
        ("clique_number", "chromatic_number"): (
            "Every pair of vertices in a clique is adjacent, so each vertex in that clique must receive a different color. The largest clique therefore gives a lower bound on the number of colors needed for the whole graph.",
            "This known relation turns a concrete subgraph structure into a global coloring constraint. It connects clique bounds with coloring bounds and provides a reusable step in composed proofs."),
        ("clique_number", "order"): (
            "A graph’s largest clique is a subset of its vertices, so its size cannot exceed the total vertex count.",
            "This known cardinality bound is a universal ceiling on clique size. It also supplies a consistency check when the engine combines clique and coloring inequalities; the formalization contribution is the checked reusable statement."),
    }
    meanings = {"order": "order counts vertices", "size": "size counts edges",
        "chromatic_number": "chromatic number is the minimum number of colors in a proper coloring",
        "clique_number": "clique number is the largest pairwise-adjacent vertex set size",
        "max_degree": "maximum degree is the largest number of neighbors at a vertex",
        "min_degree": "minimum degree is the smallest number of neighbors at a vertex",
        "average_degree": "average degree is the mean number of neighbors",
        "density": "density records edge saturation relative to the available vertex pairs",
        "graph_energy": "graph energy sums the absolute adjacency eigenvalues",
        "spectral_radius": "spectral radius is the largest absolute adjacency eigenvalue",
        "estrada_index": "Estrada index sums the exponentials of the adjacency eigenvalues",
        "parity_code_dimension": "code dimension is the nullity of the adjacency matrix over GF(2)",
        "parity_code_distance": "code distance is minimum nonzero Hamming weight, using n+1 for the zero code",
        "unique_neighbor_radius": "unique-neighbor radius is the largest k≤n for which every nonempty variable set of size at most k has a check with exactly one neighbor"}
    model_origin = metadata.get("origin") == "codex_proposal"
    saved = metadata.get("writeup")
    if universal and pair in foundation:
        body, why = foundation[pair]
    else:
        definitions = "; ".join(meanings[name] for name in sorted(variables) if name in meanings)
        body = ("Here, " + definitions + ". ") if definitions else ""
        body += "The displayed guard is part of the theorem and limits where this relation may be used."
        if {"parity_code_distance", "unique_neighbor_radius"} <= variables:
            why = "This connects the smallest nonzero codeword support with the unique-neighbor obstruction underlying stopping sets. The checked relation gives an exact step for comparing distance and local parity-check structure under the displayed premises, which are essential when considering stronger converse or equality statements."
        elif "parity_code_distance" in variables:
            why = "A distance bound constrains the smallest support of a nonzero codeword. Recording the dimension premises and the zero-code convention n+1 prevents a vacuous large distance from being mistaken for a useful nonzero coding construction."
        elif "parity_code_dimension" in variables:
            why = "Dimension counts independent binary information coordinates. A checked dimension bound distinguishes nontrivial codes from the zero code and supplies a precise constraint when relating code rate, block length, and distance; it does not itself construct a code with a good tradeoff."
        elif "unique_neighbor_radius" in variables:
            why = "This constrains the range of variable-set sizes guaranteed to contain a uniquely incident parity check. Such premises are the combinatorial starting point for stopping-set and code-distance arguments; this theorem certifies only the relation displayed above."
        elif variables & {"graph_energy", "spectral_radius", "estrada_index"}:
            why = "The relation constrains spectral quantities that capture different aspects of the same graph: aggregate eigenvalue mass, extremal eigenvalues, or their exponential sum. Connecting them to the other displayed parameters provides certified comparison bounds and exposes which graph-family assumptions are needed; no numerical speedup or new spectral theory follows from certification alone."
        elif variables & {"max_degree", "min_degree", "average_degree", "density", "size"}:
            why = "Degree and density constraints connect local neighbor counts with global edge structure. This exact relation can rule out infeasible combinations of the displayed parameters and serve as an intermediate lemma; restrictions such as regularity, connectivity, or a numeric guard must remain attached when it is reused."
        elif variables & {"clique_number", "chromatic_number"}:
            why = "This relates coloring or clique constraints to the other displayed graph parameters within the stated domain. Its value is a reusable structural bound with explicit premises, rather than an unrestricted assertion about every graph."
        else:
            quantities = ", ".join(name.replace("_", " ") for name in sorted(variables)) or "the displayed constants"
            why = f"This restricts the feasible relationship between {quantities} under the exact premise. A later proof may use that relationship without repeating its derivation; applications or stronger generalizations need their own statements and evidence."
    if isinstance(saved, str) and saved.strip() and not model_origin:
        body = saved.strip()
    what += body
    commentary = next((value.strip() for value in
        ((saved if model_origin else None), metadata.get("explanation"), receipt.get("explanation"),
         (record.get("lean_proof") or {}).get("explanation"), record.get("explanation"))
        if isinstance(value, str) and value.strip()), None)
    scope = "Lean certification establishes the stated finite-graph result, not mathematical originality."
    if variables & {"parity_code_distance", "parity_code_dimension", "unique_neighbor_radius"}:
        scope += " C(G)=ker A(G) over GF(2); these statements alone do not establish cryptographic security or decoding performance."
    result = {"what": what, "context": body, "why": why, "scope": scope,
              "provenance": "checked AST with saved writeup" if isinstance(saved, str) and saved.strip() and not model_origin else "checked AST with mathematical context"}
    if commentary:
        result["model_commentary" if model_origin else "recorded_commentary"] = commentary
        result["commentary_scope"] = "Proposal/commentary retained for context; it is not part of the certified statement or an independently checked contribution claim."
    return result


def _selected(obj, keys):
    return {key: obj[key] for key in keys if key in obj}


def _review_export(review):
    """Export research evidence, not arbitrary request traces or raw stderr."""
    clean = _selected(review, ("id", "fingerprint", "status", "summary", "contribution", "closest_results",
        "checks", "uncertainties", "expert_review", "assessment", "assessment_gate", "reviewed_at",
        "automatic_status", "automatic_assessment", "classification_revision"))
    search = review.get("search") or {}
    clean["search"] = _selected(search, ("status", "provider", "query", "searched_at", "results"))
    ai = review.get("ai_review") or {}
    if ai:
        clean["ai_review"] = _selected(ai, ("status", "outcome", "summary", "contribution", "comparisons",
            "checks", "uncertainties", "model", "reasoning_effort", "usage", "duration_ms", "started_at",
            "assessed_at", "attempts", "retry_at", "superseded", "superseded_reason", "fingerprint",
            "revision", "source_pack_sha256", "reviewer_kind", "source_coverage", "coverage", "evidence_digest",
            "sources_revision", "evidence_key", "evidence_current", "refresh_pending"))
    return clean


def _evidence(review, data_dir, files, gaps):
    ai = review.get("ai_review") or {}
    sources = {}
    if ai.get("comparisons"):
        try:
            trace = Path(ai.get("trace_path") or "missing")
            raw = _read(trace.parent / "source_pack.json", root=data_dir, suffix=".json")
            if not ai.get("source_pack_sha256") or _hash(raw) != ai["source_pack_sha256"]:
                raise ValueError("Saved AI source pack hash is missing or changed")
            pack = json.loads(raw)
            if pack.get("id") != review.get("id") or pack.get("fingerprint") != review.get("fingerprint"):
                raise ValueError("Saved AI source pack belongs to a different proof review")
            sources = {source["source_id"]: source for source in pack.get("sources", [])}
        except (OSError, ValueError, KeyError, TypeError) as exc:
            gaps.append("Original AI source context could not be bound: " + str(exc))
    evidence = []
    for index, comparison in enumerate(ai.get("comparisons", [])[:16]):
        entry = _selected(comparison, ("source_id", "source_type", "theorem_id", "title", "url", "locator",
            "version", "source_sha256", "text_sha256", "hash", "quote", "comparison", "relationship", "cache_files"))
        source = sources.get(comparison.get("source_id"))
        quote = comparison.get("quote", "")
        bound = False
        if source:
            for key in ("source_type", "locator", "version", "source_sha256", "text_sha256", "url"):
                if not entry.get(key) and source.get(key):
                    entry[key] = source[key]
            text = source.get("text", "")
            bound = (isinstance(quote, str) and bool(quote.strip()) and quote in text
                     and source.get("text_sha256") == _hash(text.encode())
                     and all(not comparison.get(key) or comparison[key] == source.get(key)
                             for key in ("source_sha256", "text_sha256", "source_type", "locator", "version")))
        entry["quote_binding"] = "matched saved source context" if bound else "not independently bound in this packet"
        if not bound:
            gaps.append(f"Comparison {index + 1}: the quoted text is not bound to available saved source context.")
        missing = [key for key in ("locator", "version", "source_sha256") if not entry.get(key)]
        if missing:
            gaps.append(f"Comparison {index + 1}: missing " + ", ".join(missing) + ".")
        if isinstance(quote, str) and quote:
            if len(quote.encode()) > 8192:
                raise ValueError("Cited excerpt exceeds the packet excerpt limit")
            name = f"evidence/comparison-{index + 1:02d}.txt"
            files[name] = quote.encode()
            entry["excerpt_file"] = name
            entry["excerpt_sha256"] = _hash(files[name])
        evidence.append(entry)
    return evidence


def build_research_packet(record, review, data_dir, *, fingerprints=None):
    """Return a ZIP and manifest; read proof files only after exact receipt validation."""
    if record.get("status") != "LEAN_CERTIFIED":
        raise ValueError("A research packet requires a currently certified proof")
    identifier = record["id"]
    receipt_path = (record.get("lean_proof") or {}).get("receipt_path", "")
    receipt_raw = _read(receipt_path, suffix=".json")
    candidate = json.loads(receipt_raw)
    # Reject unsafe paths before the shared validator reads them.
    for key in ("source_path", "challenge_path"):
        _read(candidate[key], suffix=".lean")
    receipt, error = validate_receipt(receipt_path, identifier, fingerprints)
    if not receipt or receipt.get("conjecture") != record.get("conjecture") or receipt.get("conjecture", {}).get("id") != identifier:
        raise ValueError("Exact proof receipt validation failed: " + str(error or "statement mismatch"))
    if json.loads(_read(receipt_path, suffix=".json")) != receipt:
        raise ValueError("Receipt changed while exporting")
    files = {}
    for kind, name in (("source", "proof.lean"), ("challenge", "challenge.lean")):
        raw = _read(receipt[kind + "_path"], suffix=".lean")
        if _hash(raw) != receipt[kind + "_sha256"]:
            raise ValueError("Checked proof artifact changed while exporting")
        files[name] = raw
    review = review or {"id": identifier, "status": "awaiting_review", "summary": "Originality has not been assessed."}
    if review.get("id") != identifier:
        raise ValueError("Review belongs to a different theorem")
    gaps = []
    if not review.get("fingerprint"):
        gaps.append("No saved review fingerprint is available; mathematical originality remains unassessed.")
    else:
        identity = {"conjecture": record["conjecture"], "receipt_schema_version": receipt["schema_version"],
            "receipt_sha256": _hash(receipt_raw), "source_sha256": receipt["source_sha256"],
            "challenge_sha256": receipt["challenge_sha256"], "workspace_sha256": receipt["workspace_sha256"]}
        if review["fingerprint"] != _hash(json.dumps(identity, sort_keys=True, allow_nan=False).encode()):
            raise ValueError("Review fingerprint does not match the current exact proof")
    evidence = _evidence(review, Path(data_dir), files, gaps)
    ai = review.get("ai_review") or {}
    coverage = ai.get("source_coverage") or ai.get("coverage") or {}
    if not coverage:
        gaps.append("Source coverage was not recorded for this assessment.")
    if not coverage.get("primary_literature"):
        gaps.append("No primary-literature text coverage is recorded; local proofs and bibliographic metadata cannot establish originality.")
    if ai.get("status") != "complete":
        gaps.append("The AI mathematical assessment has not completed.")
    if ai.get("refresh_pending") or ai.get("evidence_current") is False:
        gaps.append("Source evidence changed. The saved AI assessment and coverage are historical; a fresh assessment is queued.")
    if (review.get("expert_review") or {}).get("status", "pending") == "pending":
        gaps.append("Independent expert assessment is pending.")
    gaps.extend(str(item) for item in review.get("uncertainties", []))
    gaps.extend(str(item) for item in ai.get("uncertainties", []))
    receipt_export = _selected(receipt, ("schema_version", "status", "conjecture_id", "theorem_name", "axioms",
        "statement_checked", "source_path", "source_sha256", "challenge_path", "challenge_sha256", "workspace",
        "workspace_sha256", "lean_binary", "lean_binary_sha256", "lean_version", "tactic", "duration_ms", "conjecture"))
    files["receipt.json"] = _json(receipt_export).encode()
    c = Conjecture.from_dict(record["conjecture"])
    from autonomous_math.prover.trusted_lean import render_guard
    writeup = proof_writeup(record, receipt)
    packet = {"schema_version": 1, "theorem_id": identifier,
        "exported_at": datetime.now(timezone.utc).isoformat(),
        "purpose": "Inspectable research evidence; this packet does not certify mathematical novelty.",
        "writeup": writeup, "statement": c.to_latex(), "conjecture": record["conjecture"],
        "guard": record["conjecture"].get("guard_predicate"), "guard_lean": render_guard(c.guard_predicate),
        "review": _review_export(review),
        "source_coverage": coverage, "comparisons": evidence, "evidence_gaps": list(dict.fromkeys(gaps)),
        "provenance": {"receipt_sha256": _hash(receipt_raw), "receipt_export": "receipt.json",
            "receipt_export_scope": "Verification fields and exact conjecture; raw compiler diagnostics omitted.",
            "source_sha256": receipt["source_sha256"], "challenge_sha256": receipt["challenge_sha256"],
            "workspace_sha256": receipt["workspace_sha256"], "lean_version": receipt.get("lean_version"),
            "scope": "Stored receipt and content bindings validated at export; no new Lean replay was performed."},
        "omissions": ["Runtime logs, raw model/worker errors, credentials, full papers, compiler binaries and the dependency tree are not bundled."]}
    lines = [f"# Research packet: {identifier}", "", packet["purpose"], "", "## What this proves", "", writeup["what"],
        "", "## Why it matters", "", writeup["why"], "", writeup["scope"], "", "## Exact statement and assumptions", "",
        packet["statement"], "", f"Lean guard: `{packet['guard_lean']}`", "",
        "The complete guard and structured AST are in `research.json`; `challenge.lean` is the exact Lean target.",
        "", "## Formal verification", "", f"- Lean: {receipt.get('lean_version', 'not recorded')}",
        f"- Theorem: `{receipt['theorem_name']}`", f"- Source SHA-256: `{receipt['source_sha256']}`",
        f"- Workspace SHA-256: `{receipt['workspace_sha256']}`", f"- Kernel axioms: {', '.join(receipt['axioms']) or 'none'}",
        "", packet["provenance"]["scope"], "", "The compiler and pinned Mathlib dependency tree must be supplied separately to replay the proof.",
        "", "## Mathematical contribution and comparisons", "", f"Authoritative review status: {review.get('status', 'awaiting_review')}.",
        str(review.get("contribution") or "A mathematical contribution beyond the checked formalization is not established."), "",
        f"AI outcome: {ai.get('outcome', 'not recorded')} (provisional).", str(ai.get("summary") or "No completed AI comparison is recorded."),
        "", "## Source coverage", "", *[f"- {label}: {coverage.get(key, 'not recorded')}" for key, label in SOURCE_LABELS.items()]]
    for entry in review.get("closest_results", [])[:32]:
        lines += ["", f"### Recorded comparison: {entry.get('title') or entry.get('citation') or 'reference'}", "",
            str(entry.get("comparison") or "No comparison explanation recorded."),
            f"Relationship: {entry.get('relationship', 'not recorded')}",
            f"Citation: {entry.get('citation', 'not recorded')}",
            f"Checked theorem ID: {entry.get('theorem_id') or 'not recorded'}",
            f"URL: {entry.get('url') or 'not recorded'}"]
    commentary = writeup.get("model_commentary") or writeup.get("recorded_commentary")
    if commentary:
        lines += ["", "## Model commentary (not certified)" if writeup.get("model_commentary") else "## Recorded commentary (not certified)",
                  "", commentary, "", writeup["commentary_scope"]]
    for index, entry in enumerate(evidence, 1):
        lines += ["", f"### Comparison {index}: {entry.get('title', entry.get('source_id', 'source'))}", "",
            f"Source type: {entry.get('source_type', 'not recorded')}. {entry.get('quote_binding')}",
            f"Locator: {entry.get('locator', 'not recorded')}", f"Version: {entry.get('version', 'not recorded')}",
            f"Source SHA-256: {entry.get('source_sha256', 'not recorded')}", f"URL: {entry.get('url') or 'not recorded'}", "",
            str(entry.get("comparison") or "No comparison explanation recorded.")]
        if entry.get("excerpt_file"):
            lines += ["", f"Exact cited excerpt: `{entry['excerpt_file']}` (SHA-256 `{entry['excerpt_sha256']}`)."]
    lines += ["", "## Missing evidence and limits", "", *["- " + gap for gap in packet["evidence_gaps"]], "", *packet["omissions"], ""]
    import html
    files["README.md"] = "\n".join(html.escape(line, quote=False) for line in lines).encode()
    files["research.json"] = _json(packet).encode()
    manifest = {"schema_version": 1, "theorem_id": identifier, "files": [
        {"path": name, "bytes": len(raw), "sha256": _hash(raw)} for name, raw in sorted(files.items())]}
    files["manifest.json"] = _json(manifest).encode()
    if sum(map(len, files.values())) > MAX_PACKET_BYTES:
        raise ValueError("Research packet exceeds the bounded export size")
    output = io.BytesIO()
    with zipfile.ZipFile(output, "w", compression=zipfile.ZIP_DEFLATED) as archive:
        for name, raw in sorted(files.items()):
            archive.writestr(name, raw)
    return output.getvalue(), manifest


def packet_response(record, review, data_dir):
    archive, manifest = build_research_packet(record, review, data_dir)
    name = re.sub(r"[^a-zA-Z0-9._-]", "_", record["id"])[:120] or "proof"
    return {"found": True, "theorem_id": record["id"], "filename": name + ".research.zip",
            "archive_base64": base64.b64encode(archive).decode(), "manifest": manifest}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data-dir", type=Path, required=True)
    choice = parser.add_mutually_exclusive_group(required=True)
    choice.add_argument("--theorem")
    choice.add_argument("--all", action="store_true", help="Export every currently certified theorem")
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args(argv)
    from autonomous_math.dashboard.data_service import DashboardDataService
    service = DashboardDataService(data_dir=args.data_dir)
    atlas = service.load_atlas()
    reviews = {r["id"]: r for r in service.get_novelty_reviews(atlas).get("records", [])}
    records = [r for r in atlas.get("theorems", {}).values() if
               r.get("status") == "LEAN_CERTIFIED" and (args.all or r["id"] == args.theorem)]
    if not records:
        parser.error("No matching currently certified theorem")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    fingerprints = {}
    for record in records:
        archive, _ = build_research_packet(record, reviews.get(record["id"]), args.data_dir, fingerprints=fingerprints)
        name = re.sub(r"[^a-zA-Z0-9._-]", "_", record["id"])[:100] + "-" + _hash(record["id"].encode())[:8]
        path = args.output_dir / (name + ".research.zip")
        with path.open("xb") as stream:
            stream.write(archive)
        print(path)
    print(f"Exported {len(records)} certified research packet(s).")


if __name__ == "__main__":
    main()
