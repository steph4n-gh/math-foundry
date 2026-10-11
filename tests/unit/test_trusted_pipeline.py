"""Adversarial tests for the mathematical and operational trust boundaries."""
import copy,json,os,signal,subprocess,sys,time
from pathlib import Path
import networkx as nx
import numpy as np
import pytest
from autonomous_math.core.ast import Conjecture,InvariantNode,ConstantNode,BinaryOpNode,GuardPredicate
from autonomous_math.core.invariants import compute_normalized_laplacian_spectral_radius
from autonomous_math.prover.lean_prover import LeanProofSearch,LeanToolchain
from autonomous_math.prover.flywheel import LemmaFlywheel
from autonomous_math.prover.search import ProverSkepticSearch
from autonomous_math.research_state import atomic_save_json,validate_receipt,load_snapshot,writer_lock,reconcile
from autonomous_math.dashboard.data_service import DashboardDataService
from autonomous_math.sieve.instance_db import InstanceDatabase
from spectral_pruning.solvers import SpectralCliqueSolver
from spectral_pruning.bitset_solvers import BitsetBaselineSolver,BitsetSpectralSolver
from run_research import independent_holdout,run_continuous_daemon

@pytest.fixture(scope='module')
def checked(tmp_path_factory):
    out=tmp_path_factory.mktemp('real_proof')
    c=Conjecture.create(id='verified_chromatic_order',lhs=InvariantNode('chromatic_number'),rel='<=',rhs=InvariantNode('order'))
    result=LeanProofSearch(max_attempts=1,timeout_per_attempt=30).prove_conjecture(c,output_dir=out)
    assert result.is_proven,result.diagnostics
    return c,result

@pytest.mark.parametrize('name',['mcclelland_false','greedy_false','caro_wei_false','clique_chromatic_false'])
def test_false_proof_names(name):
    c=Conjecture.create(id=name,lhs=InvariantNode('order'),rel='<=',rhs=ConstantNode(0),statement='chi <= Delta + 1')
    assert not ProverSkepticSearch().prove(c).is_proven

@pytest.mark.parametrize('g',[nx.disjoint_union(nx.path_graph(2),nx.empty_graph(1)),nx.disjoint_union(nx.complete_graph(3),nx.complete_graph(3))])
def test_cached_disconnected_spectrum(g):
    from autonomous_math.core.graph_types import GraphInstance
    value=InstanceDatabase._compute_instance_invariants(GraphInstance.from_networkx(g),g)
    assert value['normalized_laplacian_spectral_radius']==pytest.approx(compute_normalized_laplacian_spectral_radius(g))

@pytest.mark.parametrize('kind',['tree','complete'])
def test_independent_family_holdout(kind):
    if kind=='tree':
        c=Conjecture.create(id='bad_tree',lhs=InvariantNode('chromatic_number'),rel='<=',rhs=BinaryOpNode('+',BinaryOpNode('*',ConstantNode(3.5),InvariantNode('density')),ConstantNode(1)),guard=GuardPredicate(property_name='is_tree'))
    else:
        c=Conjecture.create(id='bad_spread',lhs=InvariantNode('spectral_spread'),rel='<=',rhs=BinaryOpNode('+',BinaryOpNode('*',ConstantNode(.25),InvariantNode('order')),ConstantNode(9.03862)),guard=GuardPredicate(property_name='is_connected'))
    assert independent_holdout(c).is_refuted

def test_fiedler_crossing_clique():
    import itertools
    g=nx.disjoint_union(nx.gnp_random_graph(20,.4,seed=0),nx.gnp_random_graph(20,.4,seed=100))
    g.add_edges_from(itertools.combinations([0,1,2,3,20,21,22,23],2))
    size,witness,metrics=SpectralCliqueSolver().solve(g,3)
    assert metrics.completed and size==max(map(len,nx.find_cliques(g)))==8
    assert all(g.has_edge(u,v) for u,v in itertools.combinations(witness,2))

def test_upper_bound_is_safe():
    g=nx.disjoint_union(nx.complete_graph(8),nx.star_graph(80))
    s=SpectralCliqueSolver(enable_fiedler=False);s.adj={u:set(g.neighbors(u)) for u in g}
    _,upper=s._compute_perron_ordering_and_wilf(list(g))
    assert int(np.floor(upper))+1>=8

@pytest.mark.parametrize('solver',[BitsetBaselineSolver,BitsetSpectralSolver,SpectralCliqueSolver])
def test_timeout_is_not_an_optimality_claim(solver):
    _,_,m=solver().solve(nx.complete_graph(12),timeout_sec=0)
    assert m.timed_out and not m.completed

def test_kernel_receipt_and_changed_source(checked,tmp_path):
    c,result=checked
    receipt,error=validate_receipt(result.receipt_path,c.id)
    assert receipt and not error
    changed=copy.deepcopy(receipt)
    source=tmp_path/'changed.lean';source.write_text(Path(receipt['source_path']).read_text()+'\n-- modified\n')
    changed['source_path']=str(source)
    path=tmp_path/'receipt.json';atomic_save_json(changed,path)
    assert validate_receipt(path,c.id)[0] is None
    assert set(receipt['axioms'])<={'propext','Quot.sound','Classical.choice'}

def test_custom_axiom_is_rejected(tmp_path):
    code='import Mathlib.Data.Nat.Basic\naxiom magic : False\ntheorem false_result : False := by\n  exact magic\n'
    result=LeanProofSearch(max_attempts=1).prove_challenge(code,output_dir=tmp_path)
    assert not result.is_proven
    assert any('magic' in d['axioms'] for d in result.diagnostics)

def test_legacy_shim_is_not_a_toolchain():
    root=Path(__file__).resolve().parents[2]
    assert not LeanToolchain(workspace_dir=root/'lean_workspace').ensure_workspace_built()

def test_unsupported_guard_does_not_certify(tmp_path):
    c=Conjecture.create(id='guarded',lhs=InvariantNode('order'),rel='>=',rhs=ConstantNode(0),guard=GuardPredicate(property_name='is_planar'))
    r=LeanProofSearch().prove_conjecture(c,output_dir=tmp_path)
    assert not r.is_proven and 'Guard' in r.error_message

def test_real_proof_body_reuse(checked,tmp_path):
    c,result=checked
    flywheel=LemmaFlywheel(storage_path=tmp_path/'lemmas.json')
    flywheel.register_lemma(c,result.successful_tactic,receipt_path=result.receipt_path)
    goal=Conjecture.create(id='derived_bound',lhs=InvariantNode('chromatic_number'),rel='<=',rhs=BinaryOpNode('+',InvariantNode('order'),ConstantNode(1)))
    r=LeanProofSearch(flywheel=flywheel,max_attempts=2,timeout_per_attempt=30).prove_conjecture(goal,output_dir=tmp_path/'verified')
    assert r.is_proven,r.diagnostics
    assert c.id in r.verified_lean_code and 'axiom ' not in r.verified_lean_code
    assert 'have h' in r.successful_tactic
    assert LemmaFlywheel(storage_path=tmp_path/'lemmas.json').lemmas.keys()==flywheel.lemmas.keys()


def test_fake_file_and_old_metadata_are_not_certified(tmp_path):
    out=tmp_path/'research_outputs';out.mkdir()
    fake=tmp_path/'exports/verified_theorems/fake.lean';fake.parent.mkdir(parents=True);fake.write_text('theorem fake : False := by sorry')
    atomic_save_json({'theorems':{'fake':{'id':'fake','statement':'false','status':'LEAN_CERTIFIED','lean_proof':{'artifact_path':str(fake)}}}},out/'cumulative_discovery_atlas.json')
    ds=DashboardDataService(repo_root=tmp_path)
    assert ds.get_telemetry()['total_lean_certified']==0
    assert not ds.get_theorems(filter_type='LEAN_CERTIFIED')
    assert not ds.get_lean_code('fake')['found']

def test_receipt_is_bound_to_ast(checked):
    c,r=checked
    altered=c.model_copy(update={'rhs_expr':ConstantNode(0)})
    atlas={'theorems':{c.id:{'id':c.id,'statement':'false','conjecture':altered.to_dict(),'lean_proof':{'receipt_path':str(r.receipt_path)}}}}
    assert reconcile(atlas)['total_lean_certified']==0

def test_corrupt_checkpoint_is_not_replaced(tmp_path):
    path=tmp_path/'cumulative_discovery_atlas.json';path.write_text('{broken')
    with pytest.raises(ValueError):run_continuous_daemon(tmp_path,max_iterations=0)
    assert path.read_text()=='{broken'

def test_duplicate_writer(tmp_path):
    with writer_lock(tmp_path):
        with pytest.raises(RuntimeError):
            with writer_lock(tmp_path):pass

def test_failed_write_preserves_committed_snapshot(tmp_path,monkeypatch):
    target=tmp_path/'state.json';atomic_save_json({'committed':1},target)
    def fail(*args):raise OSError('simulated disk failure')
    monkeypatch.setattr(os,'replace',fail)
    with pytest.raises(OSError):atomic_save_json({'committed':2},target)
    assert json.loads(target.read_text())=={'committed':1}

def test_process_timeout_and_resume(tmp_path):
    root=Path(__file__).resolve().parents[2]
    cmd=[sys.executable,'-B',str(root/'run_research.py'),'--continuous','--max-iterations','1','--timeout-sec','.5','--output-dir',str(tmp_path)]
    start=time.monotonic();subprocess.run(cmd,check=True,timeout=10)
    assert time.monotonic()-start<10
    assert load_snapshot(tmp_path)['total_iterations']==0
    assert json.loads((tmp_path/'run_status.json').read_text())['state']=='stopped'
    assert run_continuous_daemon(tmp_path,max_iterations=0)['total_iterations']==0


def test_guard_constructor_preserves_supplied_condition():
    guard=GuardPredicate(property_name='is_tree')
    assert guard.predicate_type=='property'
    assert not guard.evaluate(nx.cycle_graph(5))
    with pytest.raises(ValueError):GuardPredicate(predicate_type='universal',property_name='is_tree')


def test_no_applicable_checks_is_inconclusive():
    from autonomous_math.core.ast import UnaryOpNode
    c=Conjecture.create(id='undefined_domain',lhs=UnaryOpNode('log1p',ConstantNode(-2)),rel='<=',rhs=ConstantNode(0))
    result=InstanceDatabase().sieve_conjecture(c)
    assert result.status=='INCONCLUSIVE' and result.checked_instances_count==0
    assert result.undefined_instances_count>0
    assert independent_holdout(c).status=='INCONCLUSIVE'


def test_certificate_canonical_node_order():
    from autonomous_math.sieve.certificates import CounterexampleCertificate,CounterexampleCertificateVerifier
    graph=nx.Graph();graph.add_nodes_from([30,20,10,50]);graph.add_edges_from([(30,20),(20,10)])
    c=Conjecture.create(id='false_noncontiguous',lhs=InvariantNode('order'),rel='<=',rhs=ConstantNode(0))
    cert=CounterexampleCertificate.from_counterexample_graph(graph,c)
    valid,errors=CounterexampleCertificateVerifier.verify_with_details(cert,c)
    assert valid,errors


def test_overlapping_checked_proofs_are_reused_once(checked,tmp_path):
    c,result=checked
    flywheel=LemmaFlywheel(storage_path=tmp_path/'lemmas.json')
    flywheel.register_lemma(c,result.successful_tactic,receipt_path=result.receipt_path)
    for delta in (1,2,3):
        goal=Conjecture.create(id=f'sibling_{delta}',lhs=InvariantNode('chromatic_number'),rel='<=',rhs=BinaryOpNode('+',InvariantNode('order'),ConstantNode(delta)))
        r=LeanProofSearch(flywheel=flywheel,max_attempts=2,timeout_per_attempt=30).prove_conjecture(goal,output_dir=tmp_path/'verified')
        assert r.is_proven,r.diagnostics
        assert r.verified_lean_code.count(f'theorem {c.id} ')==1


def test_proof_storage_failure_is_an_operational_error(checked,tmp_path,monkeypatch):
    import autonomous_math.research_state as state
    def fail(*args):raise OSError('simulated artifact write failure')
    monkeypatch.setattr(state,'atomic_save_text',fail)
    c,_=checked
    result=LeanProofSearch(max_attempts=1,timeout_per_attempt=30).prove_conjecture(c,output_dir=tmp_path)
    assert result.status=='ERROR' and not result.is_proven


def test_dependency_change_invalidates_receipt(checked,tmp_path,monkeypatch):
    import autonomous_math.research_state as state
    c,result=checked
    monkeypatch.setattr(state,'workspace_fingerprint',lambda p:'modified dependency fingerprint')
    receipt,error=state.validate_receipt(result.receipt_path,c.id)
    assert receipt is None and 'dependencies' in error


def test_http_errors_report_corrupt_checkpoint(tmp_path):
    import urllib.request,urllib.error
    from autonomous_math.dashboard.server import run_dashboard
    (tmp_path/'cumulative_discovery_atlas.json').write_text('{broken')
    server=run_dashboard(port=0,block=False,data_dir=tmp_path)
    try:
        with pytest.raises(urllib.error.HTTPError) as error:urllib.request.urlopen(f'http://127.0.0.1:{server.server_port}/api/snapshot')
        assert error.value.code==500
        assert json.loads(error.value.read())['error']
    finally:
        server.shutdown();server.server_close()


def test_pointcloud_excludes_undefined_coordinates():
    data=DashboardDataService().get_pointcloud('girth','diameter')
    assert data['excluded_undefined_points']>0
    assert all(np.isfinite(p['x']) and np.isfinite(p['y']) for p in data['points'])


def test_final_checkpoint_failure_reports_failed(tmp_path,monkeypatch):
    import run_research as runner
    original=runner.atomic_save_json
    def fail(data,path):
        if Path(path).name=='cumulative_discovery_atlas.json':raise OSError('simulated checkpoint failure')
        original(data,path)
    monkeypatch.setattr(runner,'atomic_save_json',fail)
    with pytest.raises(OSError):runner.run_continuous_daemon(tmp_path,max_iterations=0)
    assert json.loads((tmp_path/'run_status.json').read_text())['state']=='failed'


def test_counterexample_changes_next_sieve_dataset(monkeypatch):
    from run_research import replay_counterexamples
    from autonomous_math.sieve.certificates import CounterexampleCertificate
    db=InstanceDatabase()
    for name in ('_cached_nx','_cached_gi','_cached_invariants'):
        monkeypatch.setattr(InstanceDatabase,name,list(getattr(InstanceDatabase,name)))
    monkeypatch.setattr(InstanceDatabase,'_cached_matrix',{key:values.copy() for key,values in db._cached_matrix.items()})
    c=Conjecture.create(id='order_cap',lhs=InvariantNode('order'),rel='<=',rhs=ConstantNode(13))
    cert=CounterexampleCertificate.from_counterexample_graph(nx.complete_graph(24),c)
    atlas={'theorems':{c.id:{'id':c.id,'conjecture':c.to_dict(),'counterexample':cert.to_dict()}}}
    before=len(db)
    assert replay_counterexamples(atlas)==1 and len(db)==before+1
    assert replay_counterexamples(atlas)==0
    assert db._cached_matrix['order'][-1]==24
    bad=copy.deepcopy(atlas);bad['theorems'][c.id]['counterexample']['graph_size']=0
    with pytest.raises(ValueError):replay_counterexamples(bad)


def test_extended_graph_invariants_are_compared():
    c=Conjecture.create(id='false_universal_diameter',lhs=InvariantNode('diameter'),rel='<=',rhs=InvariantNode('order'))
    result=InstanceDatabase().sieve_conjecture(c)
    assert result.is_refuted and np.isinf(result.counterexample_certificate.invariants['diameter'])


@pytest.mark.parametrize('name',['order','size','chromatic_number','clique_number','max_degree'])
def test_supported_invariants_have_genuine_mathlib_types(checked,tmp_path,name):
    c=Conjecture.create(id=f'nonnegative_{name}',lhs=InvariantNode(name),rel='>=',rhs=ConstantNode(0))
    result=LeanProofSearch(max_attempts=3,timeout_per_attempt=30).prove_conjecture(c,output_dir=tmp_path)
    assert result.is_proven,result.diagnostics


def test_clique_chromatic_bound_is_kernel_proved(checked,tmp_path):
    c=Conjecture.create(id='clique_chromatic_types',lhs=InvariantNode('clique_number'),rel='<=',rhs=InvariantNode('chromatic_number'))
    result=LeanProofSearch(max_attempts=2,timeout_per_attempt=30).prove_conjecture(c,output_dir=tmp_path)
    assert result.is_proven,result.diagnostics


def test_checked_bounds_generate_and_prove_transitive_target(checked,tmp_path):
    from run_research import compose_checked_bounds
    c,base=checked
    flywheel=LemmaFlywheel(storage_path=tmp_path/'lemmas.json')
    flywheel.register_lemma(c,base.successful_tactic,receipt_path=base.receipt_path)
    lower=Conjecture.create(id='clique_le_chromatic',lhs=InvariantNode('clique_number'),rel='<=',rhs=InvariantNode('chromatic_number'))
    proof=LeanProofSearch(max_attempts=2,timeout_per_attempt=30).prove_conjecture(lower,output_dir=tmp_path/'verified')
    assert proof.is_proven,proof.diagnostics
    flywheel.register_lemma(lower,proof.successful_tactic,receipt_path=proof.receipt_path)
    atlas={'theorems':{x.id:{'id':x.id,'conjecture':x.to_dict(),'lean_proof':{'receipt_path':str(r.receipt_path)}} for x,r in [(c,base),(lower,proof)]}}
    reconcile(atlas)
    targets=compose_checked_bounds(atlas)
    assert len(targets)==1
    target=targets[0]
    assert target.lhs_expr.name=='clique_number' and target.rhs_expr.name=='order'
    derived=LeanProofSearch(flywheel=flywheel,max_attempts=1,timeout_per_attempt=30).prove_conjecture(target,output_dir=tmp_path/'verified')
    assert derived.is_proven,derived.diagnostics
    assert derived.successful_tactic == 'exact le_trans (clique_le_chromatic G) (verified_chromatic_order G)'
    assert derived.used_lemma_ids == sorted([lower.id, c.id])
