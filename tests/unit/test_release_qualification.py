import copy
from contextlib import nullcontext
import io
import json
import math

import pytest

import qualify_release as qualification
from qualify_release import _local_url, check_sample, check_review_progress, verdict


def sample(at=100, iteration=3):
    return {'at': at, 'source': {'revision': 'frozen', 'tracked_sha256': 'same'},
        'runner': {'state': 'running', 'heartbeat': at, 'model_selection': {'enabled': True}},
        'iteration': iteration, 'certified_ids': ['proof'], 'review_ids': ['proof'],
        'review_worker': {'state': 'running', 'heartbeat': at},
        'current_reviews': [{'status': 'running', 'started_at': at - 10}]}


def test_elapsed_time_cannot_be_replaced_by_many_samples():
    items = [sample(100 + n, iteration=3+n) for n in range(1000)]
    assert verdict(items, [], 86400) == 'running'
    assert verdict([sample(100), sample(86500, 4)], [], 86400) == 'passed'
    assert verdict([sample(100), sample(86500, 3)], [], 86400) == 'failed'


def test_any_observed_failure_prevents_pass():
    assert verdict([sample(100), sample(86500, 4)], [{'problems': ['stale']}], 86400) == 'failed'


@pytest.mark.parametrize('change', [
    lambda s: s['runner'].update(state='stopped'),
    lambda s: s['runner'].update(heartbeat=0),
    lambda s: s['source'].update(revision='changed'),
    lambda s: s.update(certified_ids=[]),
    lambda s: s.update(review_ids=[]),
    lambda s: s['review_worker'].update(state='error'),
    lambda s: s['review_worker'].update(heartbeat=0),
    lambda s: s['current_reviews'][0].update(started_at=-1000),
])
def test_health_and_provenance_failures_are_detected(change):
    baseline = sample(); current = copy.deepcopy(baseline)
    change(current)
    assert check_sample(current, baseline)


def test_growth_is_allowed_but_missing_observations_are_not():
    baseline = sample(); current = sample(160, 4)
    current['certified_ids'].append('new'); current['review_ids'].append('new')
    assert not check_sample(current, baseline, baseline)
    assert check_sample(sample(900), baseline, baseline)
    assert check_sample(sample(99), baseline, baseline)


def test_completed_idle_review_queue_is_healthy():
    current = sample(); current['review_worker']['state'] = 'idle'; current['current_reviews'] = []
    assert not check_sample(current, current)


@pytest.mark.parametrize('url', ['https://example.org', 'http://127.0.0.1.evil.test',
                                 'http://name:secret@127.0.0.1:8050', 'file:///tmp/a'])
def test_observer_only_probes_local_dashboard(url):
    with pytest.raises(ValueError):
        _local_url(url)


def backlog_sample(at, iteration=3):
    result = sample(at, iteration)
    result.update(counts={'ai_pending': 35, 'ai_running': 0, 'ai_errors': 1},
                  validated_review_completions=[], current_reviews=[])
    result['review_worker']['state'] = 'idle'
    return result


def test_1441_healthy_heartbeats_cannot_qualify_zero_review_progress():
    items = [backlog_sample(1000 + 60 * i, 133 + i) for i in range(1441)]
    progress, errors = {}, []
    for index, item in enumerate(items):
        assert not check_sample(item, items[0], items[index - 1] if index else None)
        errors.extend(check_review_progress(item, progress))
    assert items[-1]['at'] - items[0]['at'] == 86400
    assert errors and '75 minutes' in errors[0]
    assert verdict(items, errors, 86400) == 'failed'
    assert len(progress) <= 4  # State does not grow with the number of samples.


def test_only_a_new_validated_completion_resets_the_backlog_allowance():
    progress = {}
    initial = backlog_sample(100)
    initial['validated_review_completions'] = [{'id': 'proof', 'identity': 'old-assessment', 'assessed_at': 90}]
    assert not check_review_progress(initial, progress)
    accepted = backlog_sample(4600)
    accepted['validated_review_completions'] = [{'id': 'proof', 'identity': 'new-assessment', 'assessed_at': 4590}]
    assert not check_review_progress(accepted, progress)
    assert progress['waiting_since'] == 4590
    refreshed_cache = copy.deepcopy(accepted)
    refreshed_cache['at'] = 9000
    # Attempt counts/cache timestamps do not alter the immutable assessment.
    refreshed_cache['review_worker'].update(attempts=99, heartbeat=9000, source_refresh_at=9000)
    assert not check_review_progress(refreshed_cache, progress)
    refreshed_cache['at'] = 9091
    assert check_review_progress(refreshed_cache, progress)


@pytest.mark.parametrize('no_ai', [False, True])
def test_empty_queue_or_disabled_ai_needs_no_review_completion(no_ai):
    progress = {}
    for at in (100, 10000, 86500):
        current = backlog_sample(at)
        if no_ai: current['runner']['model_selection']['enabled'] = False
        else: current['counts'] = {'ai_pending': 0, 'ai_running': 0, 'ai_errors': 0}
        assert not check_review_progress(current, progress)
        assert progress['waiting_since'] is None


def test_empty_queue_ends_continuous_backlog_window():
    progress = {}
    assert not check_review_progress(backlog_sample(100), progress)
    empty = backlog_sample(4500); empty['counts'] = {}
    assert not check_review_progress(empty, progress)
    assert not check_review_progress(backlog_sample(8000), progress)
    assert progress['waiting_since'] == 8000
    assert not check_review_progress(backlog_sample(12500), progress)
    assert check_review_progress(backlog_sample(12501), progress)


def test_timeout_attempts_never_count_as_successful_review_progress():
    progress = {}
    for at in (100, 3600, 4000, 4600):
        current = backlog_sample(at)
        current['counts'] = {'ai_errors': int(at), 'ai_pending': 1, 'ai_running': 0}
        current['current_reviews'] = [{'status': 'error', 'attempts': int(at), 'finished_at': at}]
        assert not check_review_progress(current, progress)
    assert check_review_progress(backlog_sample(4601), progress)


def write_claim(tmp_path):
    raw = {'total_iterations': 133, 'theorems': {'proof': {'id': 'proof', 'status': 'LEAN_CERTIFIED',
           'conjecture': {'id': 'proof', 'rel': '<=', 'value': 1}, 'lean_proof': {'receipt_path': 'claimed.receipt.json'}}},
           'measurement': {'$float': 'inf'}}
    (tmp_path / 'cumulative_discovery_atlas.json').write_text(json.dumps(raw))
    return raw


def test_invalid_raw_certified_claim_fails_before_reconciliation(tmp_path, monkeypatch):
    write_claim(tmp_path)
    monkeypatch.setattr(qualification, 'validate_receipt', lambda *args: (None, 'missing source'))
    monkeypatch.setattr(qualification, 'reconcile', lambda atlas: {'total_iterations': 133, 'theorems': {}})
    with pytest.raises(ValueError, match='Invalid current receipt for proof: missing source'):
        qualification.validate_library(tmp_path)
    with pytest.raises(ValueError, match='Invalid current receipt'):
        qualification.collect(tmp_path, 'http://127.0.0.1:8050')
    assert math.isinf(qualification._committed_atlas(tmp_path)['measurement'])


@pytest.mark.parametrize('bad', ['id', 'ast'])
def test_raw_committed_identity_and_ast_must_match_receipt(tmp_path, monkeypatch, bad):
    raw = write_claim(tmp_path)
    receipt = {'conjecture': copy.deepcopy(raw['theorems']['proof']['conjecture'])}
    if bad == 'id':
        raw['theorems']['proof']['id'] = 'other'
        (tmp_path / 'cumulative_discovery_atlas.json').write_text(json.dumps(raw))
    else: receipt['conjecture']['value'] = 2
    monkeypatch.setattr(qualification, 'validate_receipt', lambda *args: (receipt, None))
    with pytest.raises(ValueError, match='identity differs|AST mismatch'):
        qualification.validate_library(tmp_path)


@pytest.mark.parametrize('valid', [True, False])
def test_collect_counts_only_current_source_validated_assessment(tmp_path, monkeypatch, valid):
    from autonomous_math.novelty import model_review
    raw = write_claim(tmp_path)
    record = {'id': 'proof', 'fingerprint': 'current', 'ai_review': {'status': 'complete', 'assessed_at': 990}}
    response = {'schema_version': 1, 'records': [record], 'counts': {'ai_pending': 1}, 'automation': {}}
    (tmp_path / 'run_status.json').write_text(json.dumps({'state': 'running'}))
    monkeypatch.setattr(qualification, 'validate_receipt', lambda *args: ({'conjecture': raw['theorems']['proof']['conjecture']}, None))
    monkeypatch.setattr(qualification, 'reconcile', lambda atlas: atlas)
    monkeypatch.setattr(qualification, 'source_identity', lambda: {'revision': 'test'})
    monkeypatch.setattr(qualification.time, 'time', lambda: 1000)
    monkeypatch.setattr(qualification.urllib.request, 'urlopen', lambda *args, **kwargs: nullcontext(io.BytesIO(json.dumps(response).encode())))
    def validate(review, atlas, directory, fingerprints=None):
        assert review == record and atlas['theorems']['proof']['status'] == 'LEAN_CERTIFIED'
        if not valid: raise ValueError('Quoted source bytes changed')
        return {'assessment': {'assessed_at': 990}, 'artifact_binding': {'assessment_sha256': 'saved', 'source_pack_sha256': 'sources'}}
    monkeypatch.setattr(model_review, 'validate_completed_review', validate)
    collected = qualification.collect(tmp_path, 'http://127.0.0.1:8050')
    assert collected['certified_ids'] == ['proof']
    if valid:
        assert collected['validated_review_completions'][0]['assessed_at'] == 990
        assert collected['validated_review_completions'][0]['identity']
        assert not collected['review_validation_errors']
    else:
        assert not collected['validated_review_completions']
        assert collected['review_validation_errors'][0]['error'] == 'Quoted source bytes changed'


def test_qualification_model_and_effort_must_remain_fixed():
    baseline = sample()
    baseline["runner"]["model_selection"].update(model="gpt-6.1-sol", reasoning_effort="xhigh")
    for field, value in (("model", "gpt-6-astra"), ("reasoning_effort", "low"), ("enabled", False)):
        current = copy.deepcopy(baseline)
        current["runner"]["model_selection"][field] = value
        assert any("model or reasoning effort changed" in error for error in check_sample(current, baseline))
