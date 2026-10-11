#!/usr/bin/env python3
"""Observe a frozen live release without changing its research state.

The elapsed-time gate is real wall time. A stopped observer, stale heartbeat,
changed source revision, failed endpoint or lost certificate fails qualification;
it cannot turn missing observations into an unattended-run success.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import subprocess
import time
import urllib.parse
import urllib.request

from autonomous_math.research_state import atomic_save_json, json_restore, reconcile, validate_receipt

ROOT = Path(__file__).resolve().parent
REVIEW_PROGRESS_ALLOWANCE_SEC = 4500


def _committed_atlas(directory):
    """Read claims before reconciliation can downgrade an invalid certificate."""
    path = Path(directory) / 'cumulative_discovery_atlas.json'
    atlas = json.loads(path.read_text(), object_hook=json_restore)
    if not isinstance(atlas, dict) or not isinstance(atlas.get('theorems'), dict):
        raise ValueError('Invalid committed research snapshot: ' + str(path))
    return atlas


def source_identity(root=ROOT):
    revision = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
    paths = subprocess.check_output(['git', 'ls-files', '-z'], cwd=root).decode().split('\0')
    hashes = {name: hashlib.sha256((root / name).read_bytes()).hexdigest()
              for name in paths if name and (root / name).is_file()}
    return {'revision': revision, 'tracked_sha256': hashlib.sha256(
        json.dumps(hashes, sort_keys=True).encode()).hexdigest()}


def _local_url(url):
    parsed = urllib.parse.urlsplit(url)
    if (parsed.scheme != 'http' or parsed.hostname not in {'127.0.0.1', 'localhost', '::1'}
            or parsed.username or parsed.password or parsed.query or parsed.fragment):
        raise ValueError('Qualification requires a local HTTP dashboard URL')
    return url.rstrip('/')


def collect(directory, url, retries=2):
    directory = Path(directory)
    atlas = _committed_atlas(directory)
    validate_library(directory, atlas)
    atlas = reconcile(atlas)
    runner = json.loads((directory / 'run_status.json').read_text())
    with urllib.request.urlopen(_local_url(url) + '/api/novelty_reviews', timeout=20) as response:
        raw = response.read(16 * 1024 * 1024 + 1)
    if len(raw) > 16 * 1024 * 1024:
        raise ValueError('Dashboard response exceeded qualification bound')
    reviews = json.loads(raw)
    if reviews.get('schema_version') != 1 or not isinstance(reviews.get('records'), list):
        raise ValueError('Dashboard did not return an originality review snapshot')
    if _committed_atlas(directory)['total_iterations'] != atlas['total_iterations']:
        if retries:
            return collect(directory, url, retries - 1)
        raise ValueError('Cannot obtain a consistent committed checkpoint for observation')
    certified = {name: record for name, record in atlas.get('theorems', {}).items()
                 if record.get('status') == 'LEAN_CERTIFIED'}
    reviewed = {record['id'] for record in reviews['records']}
    from autonomous_math.novelty.model_review import validate_completed_review
    completions, review_errors, fingerprints = [], [], {}
    now = time.time()
    for record in reviews['records']:
        if record.get('ai_review', {}).get('status') != 'complete':
            continue
        try:
            validated = validate_completed_review(record, atlas, directory, fingerprints=fingerprints)
            assessed_at = validated['assessment'].get('assessed_at')
            if (type(assessed_at) not in {int, float} or not math.isfinite(assessed_at)
                    or not 0 < assessed_at <= now + 5):
                raise ValueError('Completed assessment lacks a valid completion timestamp')
            binding = validated['artifact_binding']
            identity = hashlib.sha256(json.dumps([record['id'], record['fingerprint'],
                binding['assessment_sha256'], binding['source_pack_sha256']], sort_keys=True).encode()).hexdigest()
            completions.append({'id': record['id'], 'identity': identity, 'assessed_at': assessed_at})
        except (ValueError, OSError, KeyError, TypeError) as exc:
            review_errors.append({'id': record.get('id'), 'error': str(exc)[:500]})
    return {'at': time.time(), 'source': source_identity(), 'runner': runner,
            'iteration': atlas['total_iterations'], 'certified_ids': sorted(certified),
            'review_ids': sorted(reviewed), 'counts': reviews['counts'],
            'validated_review_completions': sorted(completions, key=lambda item: (item['assessed_at'], item['identity'])),
            'review_validation_errors': review_errors,
            'review_worker': reviews.get('automation', {}),
            'current_reviews': [{key: item.get('ai_review', {}).get(key)
                for key in ('started_at', 'status', 'attempts')}
                for item in reviews['records'] if item['id'] == reviews.get('automation', {}).get('current_id')]}


def check_sample(sample, baseline, previous=None, max_gap=150):
    problems = []
    now = sample['at']
    if sample['source'] != baseline['source']:
        problems.append('Frozen tracked source or revision changed')
    runner = sample['runner']
    if runner.get('model_selection') != baseline['runner'].get('model_selection'):
        problems.append('Research model or reasoning effort changed during qualification')
    if runner.get('state') != 'running':
        problems.append('Research runner is not running')
    age = now - runner.get('heartbeat', 0)
    if age < -5 or age > 30:
        problems.append('Research heartbeat is stale or in the future')
    if not set(baseline['certified_ids']) <= set(sample['certified_ids']):
        problems.append('A previously certified proof disappeared from the atlas')
    if set(sample['certified_ids']) != set(sample['review_ids']):
        problems.append('Dashboard reviews do not cover the current valid proof library')
    if runner.get('model_selection', {}).get('enabled'):
        worker = sample['review_worker']
        if worker.get('state') not in {'idle', 'running'}:
            problems.append('Automatic review worker is stopped or failed')
        age = now - worker.get('heartbeat', 0)
        if age < -5 or age > 30:
            problems.append('Automatic review heartbeat is stale or in the future')
        for active in sample['current_reviews']:
            if active.get('status') == 'running' and now - (active.get('started_at') or now) > 420:
                problems.append('Automatic review exceeded its bounded request allowance')
    if previous:
        if not 0 < now - previous['at'] <= max_gap:
            problems.append('Observation gap or clock discontinuity prevents unattended qualification')
        if sample['iteration'] < previous['iteration']:
            problems.append('Committed research checkpoint moved backwards')
    return problems


def check_review_progress(sample, state):
    """Bounded scalar state: only a newly validated completion resets backlog time.

    Heartbeats, errors, attempt counts and unchanged source-cache refreshes never
    count as progress. An empty queue or a disabled model needs no AI completion.
    """
    now = sample['at']
    latest = max(sample.get('validated_review_completions', []),
                 key=lambda item: (item['assessed_at'], item['identity']), default=None)
    previous_at = state.get('latest_completion_at', 0)
    newly_completed = latest is not None and latest['assessed_at'] > previous_at
    if newly_completed:
        state.update(latest_completion_at=latest['assessed_at'], latest_completion_identity=latest['identity'])
    counts = sample.get('counts', {})
    backlog = sum(counts.get(key, 0) for key in ('ai_pending', 'ai_running', 'ai_errors'))
    state['backlog'] = backlog
    if not sample['runner'].get('model_selection', {}).get('enabled') or not backlog:
        state['waiting_since'] = None
        return []
    if state.get('waiting_since') is None:
        state['waiting_since'] = now
    # A completion predating this continuous backlog window cannot reset it.
    if newly_completed and latest['assessed_at'] >= state['waiting_since']:
        state['waiting_since'] = latest['assessed_at']
    if now - state['waiting_since'] > REVIEW_PROGRESS_ALLOWANCE_SEC:
        return ['Automatic review backlog made no validated completion progress for 75 minutes']
    return []


def validate_library(directory, atlas=None):
    atlas = _committed_atlas(directory) if atlas is None else atlas
    fingerprints, results = {}, []
    for name, record in atlas.get('theorems', {}).items():
        if record.get('status') != 'LEAN_CERTIFIED':
            continue
        if record.get('id') != name:
            raise ValueError(f'Committed certified identity differs for {name}')
        receipt, error = validate_receipt((record.get('lean_proof') or {}).get('receipt_path', ''), name, fingerprints)
        if not receipt or receipt.get('conjecture') != record.get('conjecture'):
            raise ValueError(f'Invalid current receipt for {name}: {error or "AST mismatch"}')
        results.append(name)
    return sorted(results)


def verdict(samples, errors, duration_sec):
    if errors:
        return 'failed'
    if len(samples) < 2 or samples[-1]['at'] - samples[0]['at'] < duration_sec:
        return 'running'
    if samples[-1]['iteration'] <= samples[0]['iteration']:
        return 'failed'
    return 'passed'


def watch(directory, output, url, duration_sec=86400, interval=60):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    initial_ids = validate_library(directory)
    baseline = collect(directory, url)
    if initial_ids != baseline['certified_ids']:
        # A new committed round during the initial validation is harmless, but
        # validate the complete new set before starting the timed window.
        if validate_library(directory) != baseline['certified_ids']:
            raise ValueError('Research state changed repeatedly during qualification setup')
    review_progress = {}
    errors = check_sample(baseline, baseline) + check_review_progress(baseline, review_progress)
    if errors:
        raise ValueError('Qualification cannot start: ' + '; '.join(errors))
    started = time.monotonic()
    manifest = {'schema_version': 1, 'research_dir': str(Path(directory).resolve()),
        'dashboard_url': _local_url(url), 'duration_sec': duration_sec, 'interval_sec': interval,
        'started_at': baseline['at'], 'eligible_at': baseline['at'] + duration_sec,
        'source': baseline['source'], 'initial_iteration': baseline['iteration'],
        'initial_certified': len(initial_ids), 'model_selection': baseline['runner'].get('model_selection'),
        'review_progress_allowance_sec': REVIEW_PROGRESS_ALLOWANCE_SEC,
        'scope': 'Live operational qualification; not a novelty or speedup claim.'}
    atomic_save_json(manifest, output / 'manifest.json')
    samples = [baseline]
    last_progress = baseline['at']
    journal = output / 'samples.jsonl'
    with journal.open('x') as stream:
        stream.write(json.dumps(baseline) + '\n')
        stream.flush()
        try:
            while True:
                report = {'schema_version': 1, 'status': verdict(samples, errors, duration_sec),
                    'started_at': baseline['at'], 'sampled_at': samples[-1]['at'],
                    'elapsed_sec': samples[-1]['at'] - baseline['at'],
                    'required_sec': duration_sec, 'samples': len(samples), 'errors': errors,
                    'initial_iteration': baseline['iteration'], 'latest_iteration': samples[-1]['iteration'],
                    'latest_certified': len(samples[-1]['certified_ids']),
                    'review_counts': samples[-1]['counts'], 'review_progress': dict(review_progress), 'source': baseline['source']}
                if report['status'] == 'passed':
                    if time.monotonic() - started < duration_sec:
                        errors.append({'at': time.time(), 'problems': ['Wall clock advanced without required elapsed time']})
                        report.update(status='failed', errors=errors)
                    else:
                        report['validated_final_receipts'] = len(validate_library(directory))
                atomic_save_json(report, output / 'status.json')
                if report['status'] != 'running':
                    print(json.dumps(report), flush=True)
                    return report
                time.sleep(min(interval, max(0.01, duration_sec - (time.monotonic() - started))))
                sample = collect(directory, url)
                problems = check_sample(sample, baseline, samples[-1], max_gap=interval * 2 + 30)
                problems.extend(check_review_progress(sample, review_progress))
                if sample['iteration'] > samples[-1]['iteration']:
                    last_progress = sample['at']
                if sample['at'] - last_progress > 3600:
                    problems.append('No committed research progress for one hour')
                if problems:
                    errors.append({'at': sample['at'], 'problems': problems})
                stream.write(json.dumps(sample) + '\n')
                stream.flush()
                samples.append(sample)
        except BaseException as exc:
            atomic_save_json({'schema_version': 1, 'status': 'failed', 'sampled_at': time.time(),
                'started_at': baseline['at'], 'required_sec': duration_sec,
                'errors': errors + [{'at': time.time(), 'problems': [f'{type(exc).__name__}: {exc}']}]}, output / 'status.json')
            raise


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--research-dir', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--dashboard-url', default='http://127.0.0.1:8050')
    parser.add_argument('--hours', type=float, default=24)
    parser.add_argument('--interval-sec', type=float, default=60)
    args = parser.parse_args(argv)
    if not 0 < args.hours <= 168 or not 1 <= args.interval_sec <= 300:
        parser.error('Hours must be in (0, 168] and interval in [1, 300] seconds')
    try:
        result = watch(args.research_dir, args.output_dir, args.dashboard_url, args.hours * 3600, args.interval_sec)
    except (OSError, ValueError) as exc:
        parser.error(str(exc))
    return 0 if result['status'] == 'passed' else 1


if __name__ == '__main__':
    raise SystemExit(main())
