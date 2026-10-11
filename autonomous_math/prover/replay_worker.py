"""Resumable exact-source Lean replay alongside generation; never writes the atlas."""
from __future__ import annotations
import fcntl
import hashlib
import json
import logging
from pathlib import Path
import threading
import time

from autonomous_math.prover.lean_prover import LeanToolchain, _target_axiom_report
from autonomous_math.research_state import ALLOWED_AXIOMS, atomic_save_json, sha256, validate_receipt

logger = logging.getLogger(__name__)


def replay_record(record, toolchain, timeout=60, stop_requested=lambda: False):
    """Replay retained bytes in a fresh compiler invocation, then recheck bindings."""
    if not 0 < timeout <= 120:
        raise ValueError("Replay timeout must be finite and at most 120 seconds")
    path = Path(record['lean_proof']['receipt_path'])
    receipt_hash = sha256(path)
    receipt, error = validate_receipt(path, record['id'])
    if not receipt or receipt.get('conjecture') != record['conjecture']:
        raise ValueError(error or 'Replay record differs from receipt AST')
    if Path(receipt['workspace']).resolve() != toolchain.workspace_dir.resolve():
        raise ValueError('Replay requires the receipt workspace')
    started = time.monotonic()
    source = Path(receipt['source_path']).read_text()
    if stop_requested():
        raise InterruptedError('Replay cancelled before compiler launch')
    code, stdout, stderr = toolchain.run_lean_code(
        source + '\n#print axioms ' + receipt['theorem_name'] + '\n', timeout=timeout)
    axioms, audit_error = _target_axiom_report(stdout, receipt['theorem_name'])
    passed = (code == 0 and audit_error is None and set(axioms) <= ALLOWED_AXIOMS
        and 'error:' not in stdout + stderr and 'declaration uses' not in stdout + stderr)
    after, changed = validate_receipt(path, record['id'])
    if not after or sha256(path) != receipt_hash or after != receipt:
        raise ValueError(changed or 'Receipt bindings changed during replay')
    return {'id': record['id'], 'receipt_path': str(path), 'receipt_sha256': receipt_hash,
        'source_sha256': receipt['source_sha256'], 'challenge_sha256': receipt['challenge_sha256'],
        'workspace_sha256': receipt['workspace_sha256'], 'lean_binary_sha256': receipt['lean_binary_sha256'],
        'theorem_name': receipt['theorem_name'], 'passed': passed,
        'state': 'passed' if passed else 'timeout' if code == 124 else 'failed',
        'exit_code': code, 'axioms': axioms, 'audit_error': audit_error,
        'stdout': stdout, 'stderr': stderr, 'elapsed_sec': time.monotonic()-started,
        'completed_at': time.time(), 'timeout_sec': timeout, 'model_requests': 0}


def replay_fingerprint(record):
    """Receipt and exact AST identify a replay; missing/changed files cannot be cached."""
    payload = {'receipt_sha256': sha256(Path(record['lean_proof']['receipt_path'])),
        'id': record['id'], 'conjecture': record['conjecture']}
    return hashlib.sha256(json.dumps(payload, sort_keys=True).encode()).hexdigest()


class ReplayWorker:
    def __init__(self, directory, stop_requested=lambda: False, deadline=float('inf')):
        self.directory = Path(directory)
        self.output = self.directory / 'independent_replay'
        self.stop_requested, self.deadline = stop_requested, deadline
        self._stop, self._wake = threading.Event(), threading.Event()
        self._thread = self._owner = self.toolchain = None
        self.state = {'state': 'idle', 'current_id': None, 'passed': 0, 'failed': 0,
            'pending': 0, 'error': None, 'timeout_sec': 60}

    def stopped(self):
        return self._stop.is_set() or self.stop_requested() or time.monotonic() >= self.deadline

    def pulse(self):
        atomic_save_json(dict(self.state, heartbeat=time.time()), self.output / 'worker.json')

    def start(self):
        self.output.mkdir(parents=True, exist_ok=True)
        self._owner = (self.output / '.worker.lock').open('a+')
        try:
            fcntl.flock(self._owner, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BaseException:
            self._owner.close(); self._owner = None
            raise
        self._thread = threading.Thread(target=self._run, name='lean-replay', daemon=True)
        self._thread.start()

    def wake(self):
        self._wake.set()

    def _run(self):
        report_path = self.output / 'report.json'
        try:
            report = json.loads(report_path.read_text()) if report_path.exists() else {'schema_version': 1, 'records': {}}
            while not self.stopped():
                # Raw committed snapshot: reconciliation must not hide invalid certificates.
                checkpoint = self.directory / 'cumulative_discovery_atlas.json'
                if not checkpoint.exists():
                    self.pulse(); self._wake.wait(2); self._wake.clear(); continue
                atlas = json.loads(checkpoint.read_text())
                fingerprints = {}
                certified = [r for r in atlas['theorems'].values() if r.get('status') == 'LEAN_CERTIFIED']
                pending, current = [], {}
                for record in sorted(certified, key=lambda r: (-r.get('discovered_iteration', 0), r['id'])):
                    try:
                        fingerprint = replay_fingerprint(record)
                        receipt, error = validate_receipt(record['lean_proof']['receipt_path'], record['id'], fingerprints)
                        if not receipt: raise ValueError(error)
                    except (OSError, ValueError, KeyError, TypeError) as exc:
                        self.state.update(error=str(exc), state='error', current_id=record.get('id'))
                        self.pulse(); raise
                    prior = report['records'].get(record['id'], {})
                    current[record['id']] = fingerprint
                    if prior.get('fingerprint') != fingerprint or (not prior.get('passed') and time.time() >= prior.get('retry_at', 0)):
                        pending.append((record, fingerprint))
                def counts():
                    bound = [r for identity, r in report['records'].items()
                        if current.get(identity) == r.get('fingerprint')]
                    return dict(passed=sum(bool(r['passed']) for r in bound),
                        failed=sum(not r['passed'] for r in bound))
                self.state.update(**counts())
                self.state['pending'] = len(pending)
                for record, fingerprint in pending:
                    if self.stopped(): break
                    self.state.update(state='running', current_id=record['id'], error=None)
                    self.pulse()
                    if self.toolchain is None:
                        receipt, _ = validate_receipt(record['lean_proof']['receipt_path'], record['id'], fingerprints)
                        self.toolchain = LeanToolchain(workspace_dir=receipt['workspace'])
                        if not self.toolchain.ensure_workspace_built():
                            raise RuntimeError('Pinned genuine Lean/Mathlib unavailable for replay')
                    row = replay_record(record, self.toolchain, stop_requested=self.stopped)
                    row['fingerprint'] = fingerprint
                    if not row['passed']: row['retry_at'] = time.time() + 3600
                    # Keep prior failed attempts even when a later replay succeeds.
                    prior = report['records'].get(record['id'])
                    if prior:
                        row['previous_attempts'] = prior.get('previous_attempts', []) + [{k: v for k, v in prior.items() if k != 'previous_attempts'}]
                    report['records'][record['id']] = row
                    report.update(updated_at=time.time(), checkpoint=atlas['total_iterations'])
                    atomic_save_json(report, report_path)
                    self.state.update(**counts(), pending=self.state['pending']-1)
                self.state.update(state='idle', current_id=None)
                self.pulse(); self._wake.wait(15); self._wake.clear()
        except BaseException as exc:
            self.state.update(state='error' if not self.stopped() else 'stopped', error=str(exc))
            if not self.stopped(): logger.exception('Independent proof replay stopped')
        finally:
            if self.toolchain: self.toolchain.cancel()
            self.pulse()

    def close(self):
        self._stop.set(); self._wake.set()
        until = time.monotonic() + 5
        if self._thread:
            while self._thread.is_alive() and time.monotonic() < until:
                if self.toolchain: self.toolchain.cancel()
                self._thread.join(timeout=0.25)
            if self._thread.is_alive(): raise RuntimeError('Replay worker did not stop')
        if self._owner:
            fcntl.flock(self._owner, fcntl.LOCK_UN); self._owner.close(); self._owner = None
        self.state.update(state='stopped', current_id=None); self.pulse()
