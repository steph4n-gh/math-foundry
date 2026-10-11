#!/usr/bin/env python3
"""Review certified statements and record evidence-bound originality assessments."""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
import fcntl
import hashlib
import json
from pathlib import Path
import threading
import time

from autonomous_math.novelty.review import get_reviews, save_assessment, update_reviews
from autonomous_math.research_state import atomic_save_json, load_snapshot


def review_unresolved(atlas, directory, report_path, *, identifiers=None, workers=4,
                      model="gpt-6.1-sol", reasoning_effort="xhigh", timeout=1200):
    """Recompare a fixed set using the existing reviewer, with exclusive ownership.

    The supplied atlas freezes comparison context. Each saved result is also
    checked against the output directory's current exact theorem receipt.
    At most two requests per target; source-validation failures remain visible.
    """
    from autonomous_math.novelty.model_review import build_review_source_pack, validate_completed_review
    from autonomous_math.novelty.review_worker import ReviewWorker
    from autonomous_math.prover.codex_synthesis import CodexProofSynthesizer
    if not 1 <= workers <= 4 or not 0 < timeout <= 1200:
        raise ValueError("Review batch permits 1–4 workers and finite requests up to1200 seconds")
    directory, report_path = Path(directory).resolve(), Path(report_path).resolve()
    if report_path.exists():
        raise ValueError("Refusing to overwrite a previous batch report")
    stopped, synthesizers = threading.Event(), []
    report = {"state": "preparing", "started_at": time.time(), "workers": workers,
              "request_timeout_sec": timeout, "requests_per_target": 2,
              "target_deadline_sec": timeout * 2, "model": model, "effort": reasoning_effort,
              "tier": "Standard", "results": [], "source_preparation": []}
    owner = (directory / ".novelty_model_worker.lock").open("a+")
    try:
        fcntl.flock(owner, fcntl.LOCK_EX | fcntl.LOCK_NB)
        public = get_reviews(atlas, directory)
        selected = set(identifiers) if identifiers is not None else {
            r["id"] for r in public["records"] if r.get("ai_review", {}).get("outcome") == "unresolved"}
        records = [r for r in public["records"] if r["id"] in selected]
        if {r["id"] for r in records} != selected:
            raise ValueError("Batch IDs must all have current certified review records")
        report["target_ids"] = sorted(selected)
        report["frozen_atlas_sha256"] = hashlib.sha256(
            json.dumps(atlas, sort_keys=True).encode()).hexdigest()
        atomic_save_json(report, report_path)
        # Warm the shared cache sequentially. Model requests do not race paper downloads.
        for record in records:
            pack = build_review_source_pack(record, atlas["theorems"][record["id"]], atlas,
                directory=directory, deadline=time.monotonic()+20, online=True)
            report["source_preparation"].append({"id": record["id"],
                "coverage": pack["source_coverage"], "evidence_key": pack["evidence_key"]})
            atomic_save_json(report, report_path)
        report["state"] = "running"

        def one(record):
            synthesizer = CodexProofSynthesizer(workspace_dir=Path(__file__).resolve().parent / "certified_lean",
                model=model, reasoning_effort=reasoning_effort, timeout_per_request=timeout)
            synthesizers.append(synthesizer)
            worker = ReviewWorker(directory, synthesizer, stop_requested=stopped.is_set,
                                  deadline=time.monotonic()+timeout*2)
            attempts = []
            ai = record.get("ai_review", {})
            try:
                for _ in range(2):
                    if worker.stopped(): break
                    worker._review_one(atlas, record)
                    record = next(r for r in get_reviews(atlas, directory)["records"] if r["id"] == record["id"])
                    ai = record.get("ai_review", {})
                    attempts.append({"status": ai.get("status"), "error": ai.get("error"),
                        "trace_path": ai.get("trace_path"), "duration_ms": ai.get("duration_ms"),
                        "usage": ai.get("usage") or None})
                    if ai.get("status") == "complete":
                        validate_completed_review(record, atlas, directory)
                        break
                return {"id": record["id"], "status": ai.get("status"), "outcome": ai.get("outcome"),
                        "attempts": attempts, "error": ai.get("error"),
                        "source_coverage": ai.get("source_coverage"),
                        "assessment_sha256": ai.get("assessment_sha256")}
            finally:
                synthesizer.cancel()

        with ThreadPoolExecutor(max_workers=workers) as pool:
            pending = {pool.submit(one, record): record["id"] for record in records}
            try:
                while pending:
                    done, _ = wait(pending, timeout=2, return_when=FIRST_COMPLETED)
                    for future in done:
                        identifier = pending.pop(future)
                        try:
                            result = future.result()
                        except Exception as exc:
                            result = {"id": identifier, "status": "error", "error": str(exc)}
                        report["results"].append(result)
                        print(json.dumps({"completed": len(report["results"]), "total": len(records), **result}), flush=True)
                    atomic_save_json(dict(report, heartbeat=time.time(), pending=len(pending)), report_path)
            except BaseException:
                stopped.set()
                for future in pending:
                    future.cancel()
                # A request can start between the worker's stop check and
                # Popen. Repeat cancellation before executor shutdown waits,
                # including synthesizers created after the first stop signal.
                cleanup_started = time.monotonic()
                while any(not future.done() for future in pending):
                    for synthesizer in list(synthesizers):
                        synthesizer.cancel()
                    wait(pending, timeout=0.1)
                report["cancellation_duration_sec"] = time.monotonic() - cleanup_started
                raise
        report.update(state="completed" if all(r["status"] == "complete" for r in report["results"]) else "completed_with_errors",
                      finished_at=time.time())
        atomic_save_json(report, report_path)
        return report
    except BaseException as exc:
        stopped.set()
        for synthesizer in synthesizers: synthesizer.cancel()
        report.update(state="interrupted" if isinstance(exc, KeyboardInterrupt) else "failed", error=str(exc), finished_at=time.time())
        atomic_save_json(report, report_path)
        raise
    finally:
        owner.close()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path(__file__).resolve().parent / "research_outputs",
                        help="Existing research output directory (the atlas is read-only).")
    parser.add_argument("--max-searches", type=int, default=2,
                        help="Maximum scholarly API requests in this invocation (default: 2).")
    parser.add_argument("--offline", action="store_true", help="Classify and reuse saved evidence without network calls.")
    parser.add_argument("--assessment", type=Path,
                        help="Save an evidence-bearing JSON assessment bound to an exported review fingerprint.")
    parser.add_argument("--ai-unresolved", action="store_true", help="Recompare unresolved reviews with bounded exclusive AI workers.")
    parser.add_argument("--ids", type=Path, help="JSON list of exact IDs for a fixed AI review batch.")
    parser.add_argument("--frozen-atlas", type=Path, help="Use this atlas as fixed comparison context; target receipts must still be current.")
    parser.add_argument("--report", type=Path, help="New durable batch report path, required for --ai-unresolved.")
    parser.add_argument("--review-workers", type=int, default=4)
    parser.add_argument("--model", default="gpt-6.1-sol")
    parser.add_argument("--reasoning-effort", default="xhigh")
    parser.add_argument("--request-timeout", type=float, default=1200)
    args = parser.parse_args(argv)
    if not 0 <= args.max_searches <= 100:
        parser.error("--max-searches must be between 0 and 100")
    if args.ai_unresolved and (args.report is None or args.assessment or args.offline):
        parser.error("--ai-unresolved requires --report and cannot combine with --assessment or --offline")
    directory = args.output_dir.resolve()
    if not (directory / "cumulative_discovery_atlas.json").is_file():
        parser.error("--output-dir must contain an existing cumulative_discovery_atlas.json")
    try:
        atlas = json.loads(args.frozen_atlas.read_text()) if args.frozen_atlas else load_snapshot(directory)
        if args.ai_unresolved:
            result = review_unresolved(atlas, directory, args.report,
                identifiers=json.loads(args.ids.read_text()) if args.ids else None,
                workers=args.review_workers, model=args.model, reasoning_effort=args.reasoning_effort,
                timeout=args.request_timeout)
            print(json.dumps({"path": str(args.report), "state": result["state"], "completed": len(result["results"])}))
            return 0 if result["state"] == "completed" else 1
        if args.assessment:
            assessment = json.loads(args.assessment.read_text())
            if not isinstance(assessment, dict):
                raise ValueError("Assessment must be a JSON object")
            result = save_assessment(atlas, directory, assessment)
        else:
            result = update_reviews(atlas, directory, max_searches=args.max_searches,
                                    online=not args.offline, timeout_sec=3)
    except (OSError, ValueError, RuntimeError, KeyError, TypeError) as exc:
        parser.error(str(exc))
    print(json.dumps({"path": str(directory / "novelty_reviews.json"),
                      "counts": result["counts"], "updated_at": result.get("updated_at")}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
