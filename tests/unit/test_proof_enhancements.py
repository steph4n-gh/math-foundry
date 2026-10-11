import copy
import json
from pathlib import Path
from types import SimpleNamespace
import pytest
from autonomous_math.core.ast import Conjecture, ConstantNode, GuardPredicate, InvariantNode
from autonomous_math.conjecturing.model_proposals import missing_lemma_candidates
from autonomous_math.prover.codex_synthesis import CodexProofSynthesizer, validate_synthesis_response
from autonomous_math.prover.lean_prover import LeanProofSearch
from autonomous_math.sieve.model_counterexamples import counterexample_order_limit
from autonomous_math.prover import replay_worker


def bound(name='parent', left='parity_code_distance', guard=None):
    return Conjecture.create(id=name, lhs=InvariantNode(left), rel='<=', rhs=InvariantNode('order'), guard=guard)


def helper(left='min_degree'):
    return {'lhs_json': json.dumps({'node_type':'invariant','name':left}), 'rhs_json':json.dumps({'node_type':'invariant','name':'order'}),
        'rel':'<=','guard_json':None,'explanation':'A simpler bound to support the blocked proof.'}


def unknown(helpers=()):
    return {'outcome':'unknown','proof_body':'','imports':[],'explanation':'Missing graph lemma.','counterexample':None,'missing_lemmas':list(helpers)}


def test_missing_helpers_are_strict_unproved_ast_proposals():
    assert validate_synthesis_response(unknown([helper()]), ())['missing_lemmas']
    broken=helper();broken['lhs_json']='{"node_type":"invariant","name":"invented"}'
    with pytest.raises(ValueError):validate_synthesis_response(unknown([broken]), ())
    data=unknown([helper()]);data.update(outcome='proof',proof_body='simp')
    with pytest.raises(ValueError,match='Only unknown'):validate_synthesis_response(data, ())
    with pytest.raises(ValueError):validate_synthesis_response(unknown([helper()]*3), ())


def test_helpers_deduplicate_link_parents_and_reject_target_repetition():
    a,b=bound('a'),bound('b');atlas={'theorems':{c.id:{'id':c.id,'status':'EMPIRICAL_SURVIVOR','conjecture':c.to_dict(),'proof_attempt':unknown([helper()])} for c in [a,b]}}
    tasks,errors=missing_lemma_candidates(atlas,focus=['parity_code_distance'])
    assert not errors and len(tasks)==1 and tasks[0].metadata['helper_for']==['a','b']
    assert tasks[0].metadata['literature_status']=='UNREVIEWED'
    atlas['theorems']['a']['proof_attempt']=unknown([helper('parity_code_distance')])
    tasks,errors=missing_lemma_candidates(atlas)
    assert errors and 'repeats' in errors[0]['reason']
    atlas['theorems']['b']['status']='LEAN_CERTIFIED'
    assert not missing_lemma_candidates(atlas,focus=['clique_number'])[0]


def test_guard_only_code_invariants_constrain_counterexample_domain():
    assert counterexample_order_limit(bound())==16
    assert counterexample_order_limit(bound(left='size'))==64
    guard=GuardPredicate(predicate_type='comparison',invariant='unique_neighbor_radius',op='>=',threshold=2)
    assert counterexample_order_limit(bound(left='size',guard=guard))==16


def test_live_request_schema_and_prompt_use_exact_domain(tmp_path):
    synth=CodexProofSynthesizer(workspace_dir=tmp_path);synth.conjecture=bound()
    seen={}
    def request(prompt,schema,*args):
        seen.update(prompt=prompt,schema=schema);return unknown([helper()]),{}
    synth.request_json=request
    data,trace=synth.generate_candidate('trusted target',[],tmp_path/'attempt',9999999)
    graph=seen['schema']['properties']['counterexample']['anyOf'][1]['properties']
    assert graph['order']['maximum']==16 and graph['edges']['maxItems']==120
    assert '0 to 16' in seen['prompt'] and 'missing_lemmas' in seen['schema']['required']
    assert trace['counterexample_max_order']==16 and data['missing_lemmas']


def test_third_repair_requires_measured_compiler_progress():
    before={'phase':'codex_synthesis','failure_kind':'compiler_rejection','error_count':3,'first_error_line':20}
    after={**before,'error_count':1,'first_error_line':80}
    assert LeanProofSearch._repair_progress([before,after])
    assert not LeanProofSearch._repair_progress([before,before])
    assert not LeanProofSearch._repair_progress([before,{**after,'failure_kind':'compiler_timeout'}])
    assert LeanProofSearch._repair_progress([{**before,'failure_kind':'compiler_timeout'},{**before,'phase':'codex_synthesis_timeout_retry'},after])


def test_guarded_declarations_can_be_retrieved_but_premises_need_lean():
    weak=bound('weak',guard=GuardPredicate('is_connected'))
    strong=bound('strong',guard=GuardPredicate(predicate_type='conjunction',guards=[GuardPredicate('is_connected'),GuardPredicate('is_regular')]))
    receipt={'theorem_name':'weak','conjecture_id':'weak','conjecture':weak.to_dict()}
    selected=LeanProofSearch()._select_reuse(strong,[receipt])
    assert selected==[receipt]
    assert any('(by first | aesop | linarith)' in t for t in LeanProofSearch._reuse_tactics(selected,strong))
    assert ' h_guard' not in LeanProofSearch._reuse_tactics(selected,strong)[-1]


def test_replay_never_accepts_disallowed_axioms_and_detects_changes(monkeypatch,tmp_path):
    receipt_path=tmp_path/'receipt.json';receipt_path.write_text('{}');source=tmp_path/'proof.lean';source.write_text('theorem target : True := by trivial')
    record={'id':'target','conjecture':{'id':'target'},'lean_proof':{'receipt_path':str(receipt_path)}}
    receipt={'conjecture':record['conjecture'],'workspace':str(tmp_path),'source_path':str(source),'theorem_name':'target',
        'source_sha256':'source','challenge_sha256':'challenge','workspace_sha256':'workspace','lean_binary_sha256':'compiler'}
    monkeypatch.setattr(replay_worker,'validate_receipt',lambda *args:(receipt,None))
    tool=SimpleNamespace(workspace_dir=tmp_path,run_lean_code=lambda *a,**k:(0,"'target' depends on axioms: [Lean.ofReduceBool]\n",''))
    assert not replay_worker.replay_record(record,tool)['passed']
    tool.run_lean_code=lambda *a,**k:(0,"'target' depends on axioms: [propext, Classical.choice, Quot.sound]\n",'')
    assert replay_worker.replay_record(record,tool)['passed']
    def mutate(*args,**kwargs):
        receipt_path.write_text('{"changed":true}');return 0,"'target' does not depend on any axioms\n",''
    tool.run_lean_code=mutate
    with pytest.raises(ValueError,match='changed'):replay_worker.replay_record(record,tool)


def test_replay_cache_is_bound_to_ast_and_receipt(tmp_path):
    path=tmp_path/'receipt';path.write_text('one')
    record={'id':'x','conjecture':{'x':1},'lean_proof':{'receipt_path':str(path)}}
    before=replay_worker.replay_fingerprint(record);record['conjecture']['x']=2
    assert replay_worker.replay_fingerprint(record)!=before
    record['conjecture']['x']=1;path.write_text('two')
    assert replay_worker.replay_fingerprint(record)!=before


def test_duplicate_replay_worker_is_rejected_and_close_reaps(monkeypatch,tmp_path):
    worker=replay_worker.ReplayWorker(tmp_path);worker.start()
    other=replay_worker.ReplayWorker(tmp_path)
    try:
        with pytest.raises(BlockingIOError):other.start()
    finally:worker.close()
    assert not worker._thread.is_alive() and worker.state['state']=='stopped'


def test_cached_replay_counts_resume_without_another_compiler(monkeypatch,tmp_path):
    import time
    path=tmp_path/'receipt.json';path.write_text('{}')
    record={'id':'cached','status':'LEAN_CERTIFIED','conjecture':{},'lean_proof':{'receipt_path':str(path)}}
    (tmp_path/'cumulative_discovery_atlas.json').write_text(json.dumps({'theorems':{'cached':record},'total_iterations':1}))
    output=tmp_path/'independent_replay';output.mkdir()
    (output/'report.json').write_text(json.dumps({'schema_version':1,'records':{'cached':{'passed':True,'fingerprint':replay_worker.replay_fingerprint(record)}}}))
    monkeypatch.setattr(replay_worker,'validate_receipt',lambda *args:({'conjecture':{}},None))
    def unexpected(*args,**kwargs):raise AssertionError('A bound cached proof must not launch Lean again')
    monkeypatch.setattr(replay_worker,'LeanToolchain',unexpected)
    worker=replay_worker.ReplayWorker(tmp_path);worker.start()
    try:
        until=time.monotonic()+3
        while worker.state['passed']!=1 and time.monotonic()<until:time.sleep(.02)
        assert worker.state['passed']==1 and worker.state['pending']==0 and not worker.state['error']
    finally:worker.close()


def test_replay_close_cancels_a_real_owned_compiler(tmp_path):
    import os,threading,time
    from autonomous_math.prover.lean_prover import LeanToolchain
    worker=replay_worker.ReplayWorker(tmp_path)
    worker.toolchain=LeanToolchain()
    result=[]
    def compile_until_cancelled():
        try:
            result.append(worker.toolchain.run_lean_code('#eval IO.sleep 30000',timeout=40))
        except InterruptedError as exc:
            result.append(exc)
    worker._thread=threading.Thread(target=compile_until_cancelled)
    worker._thread.start()
    until=time.monotonic()+10
    while not worker.toolchain.active_process_groups() and worker._thread.is_alive() and time.monotonic()<until:time.sleep(.02)
    groups=worker.toolchain.active_process_groups()
    assert groups,'The genuine compiler should be active for this cancellation control'
    worker.close()
    assert not worker._thread.is_alive() and result
    assert isinstance(result[0], InterruptedError) or result[0][0]!=0
    for group in groups:
        with pytest.raises(ProcessLookupError):os.killpg(group,0)


@pytest.mark.parametrize('progress', [True, False])
def test_third_request_is_admitted_only_after_compiler_progress(tmp_path, monkeypatch, progress):
    from tests.unit.test_proof_efficiency import retry_prover
    prover,target,tool,synth=retry_prover(monkeypatch,[1,1,0])
    synth.max_rounds=3
    calls=[]
    def compile_candidate(code, timeout):
        calls.append(code)
        if len(calls)==3:
            return 0,"'retry_target' does not depend on any axioms\n",''
        errors=3 if len(calls)==1 or not progress else 1
        return 1,'\n'.join('<stdin>:20:2: error: unknown identifier' for _ in range(errors)),''
    tool.run_lean_code=compile_candidate
    result=prover.prove_challenge(target,tmp_path,save_verified_artifact=False)
    assert len(synth.requests)==(3 if progress else 2)
    assert result.is_proven == progress


def test_helper_pipeline_refutes_false_tasks_and_certifies_before_retrieval(tmp_path):
    import run_research as runner
    from autonomous_math.sieve.instance_db import InstanceDatabase
    parent=Conjecture.create(id='blocked_code_parent',lhs=InvariantNode('parity_code_dimension'),rel='>=',rhs=ConstantNode(0))
    good=helper('min_degree');good.update(rel='>=',rhs_json=json.dumps({'node_type':'constant','value':0}))
    bad=helper('order');bad.update(rel='<=',rhs_json=json.dumps({'node_type':'constant','value':0}))
    atlas={'theorems':{parent.id:{'id':parent.id,'status':'EMPIRICAL_SURVIVOR','conjecture':parent.to_dict(),'proof_attempt':unknown([good,bad])}},
        'total_iterations':0,'total_conjectures_generated':1,'total_refuted':0,'recent_refutations':[]}
    options=dict(runner._options(proof_backend='none',model_candidates=0),focus_invariants=['parity_code_dimension'])
    InstanceDatabase.clear_cache()
    try:
        runner._coordinate_candidates([],atlas,tmp_path,1,runner.GracefulDaemonInterrupt(),
            __import__('time').monotonic()+150,{},options,synchronous=True)
        tasks=[r for r in atlas['theorems'].values() if r['id']!=parent.id]
        assert {r['status'] for r in tasks}=={'LEAN_CERTIFIED','REFUTED'}
        verified=next(r for r in tasks if r['status']=='LEAN_CERTIFIED')
        assert verified['conjecture']['metadata']['helper_for']==[parent.id]
        search=runner._prover(runner._snapshot(atlas),tmp_path/'retrieval',options)
        assert any(r['conjecture_id']==verified['id'] for r in search._validated_reuse(parent))
        before=copy.deepcopy(verified)
        second=parent.model_copy(update={'id':'second_blocked_parent','lhs_expr':InvariantNode('parity_code_distance')})
        atlas['theorems'][second.id]={'id':second.id,'status':'EMPIRICAL_SURVIVOR','conjecture':second.to_dict(),'proof_attempt':unknown([good])}
        options['focus_invariants'].append('parity_code_distance')
        runner._coordinate_candidates([],atlas,tmp_path/'repeat',0,runner.GracefulDaemonInterrupt(),
            __import__('time').monotonic()+150,{},options,synchronous=True)
        assert atlas['theorems'][verified['id']]['conjecture']==before['conjecture']
        search=runner._prover(runner._snapshot(atlas),tmp_path/'second_retrieval',options)
        assert any(r['conjecture_id']==verified['id'] for r in search._validated_reuse(second))
    finally:InstanceDatabase.clear_cache()


def test_real_guarded_reuse_and_independent_replay_preserve_bindings(tmp_path):
    from autonomous_math.prover.lean_prover import LeanToolchain
    from autonomous_math.prover.trusted_lean import render_challenge
    from autonomous_math.research_state import validate_receipt
    weak=Conjecture.create(id='weak_connected_bound',lhs=InvariantNode('order'),rel='>=',rhs=ConstantNode(0),guard=GuardPredicate('is_connected'))
    result=LeanProofSearch(max_attempts=1,timeout_per_attempt=30).prove_conjecture(weak,tmp_path/'checked')
    assert result.is_proven,result.diagnostics
    receipt,error=validate_receipt(result.receipt_path,weak.id)
    assert receipt and not error
    strong=weak.model_copy(update={'id':'strong_connected_bound','guard_predicate':GuardPredicate(predicate_type='conjunction',guards=[GuardPredicate('is_connected'),GuardPredicate('is_regular')])})
    tool=LeanToolchain(workspace_dir=receipt['workspace'])
    challenge,context=LeanProofSearch._reuse_context(render_challenge(strong)[0],[receipt],[receipt])
    tactic='exact '+LeanProofSearch._reuse_tactics([receipt],strong)[-1].removeprefix('exact ')
    code,stdout,stderr=tool.run_lean_code(challenge.replace('sorry',tactic)+'\n#print axioms strong_connected_bound\n',timeout=30)
    assert code==0,(stdout,stderr)
    unguarded=weak.model_copy(update={'id':'unguarded_bound','guard_predicate':None})
    challenge,_=LeanProofSearch._reuse_context(render_challenge(unguarded)[0],[receipt],[receipt])
    code,stdout,stderr=tool.run_lean_code(challenge.replace('sorry',LeanProofSearch._reuse_tactics([receipt],unguarded)[-1]),timeout=30)
    assert code!=0 and 'error:' in stdout+stderr
    record={'id':weak.id,'conjecture':weak.to_dict(),'lean_proof':{'receipt_path':str(result.receipt_path)}}
    replay=replay_worker.replay_record(record,tool)
    assert replay['passed'] and replay['model_requests']==0
    source=Path(receipt['source_path']);source.write_text(source.read_text()+'\n-- tamper\n')
    with pytest.raises(ValueError):replay_worker.replay_record(record,tool)
