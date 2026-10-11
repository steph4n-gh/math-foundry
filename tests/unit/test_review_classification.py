"""Exact, conservative review decisions; no compiler/model/network calls."""
import copy
import json

import pytest

from autonomous_math.core.ast import BinaryOpNode as B, ConstantNode as C, Conjecture, GuardPredicate as G, InvariantNode as I
from autonomous_math.novelty.review_classification import classify_record
from autonomous_math.novelty.literature_crosscheck import KnownTheorem, KnownTheoremRegistry, LiteratureCrossChecker
from autonomous_math.prover.trusted_lean import expander_code_candidates


def record(left, rel, right, guard=None, ident='arbitrary_label', metadata=None):
    c=Conjecture.create(id=ident,lhs=left,rel=rel,rhs=right,guard=guard,metadata=metadata or {})
    return {'id':ident,'status':'LEAN_CERTIFIED','conjecture':c.to_dict(),'statement':'ignored model prose'}


def review(row, rows=()):
    return classify_record(row,{'theorems':{r['id']:r for r in rows}})


def statuses(result):
    return {c['label']:c['status'] for c in result['checks']}


def positive(threshold=1,op='>='):
    return G(predicate_type='comparison',invariant='parity_code_dimension',op=op,threshold=threshold)


@pytest.mark.parametrize('candidate',expander_code_candidates())
def test_four_foundations_match_math_not_ids(candidate):
    row={'id':'different_id','status':'LEAN_CERTIFIED','conjecture':candidate.to_dict()}
    row['conjecture']['id']='not_a_seed_name'
    result=review(row)
    assert result['status']=='known_result'
    assert statuses(result)['restatement']=='fail'
    assert result['closest_results']
    json.dumps(result)


def test_singleton_inverted_relation_commutative_sides_and_actual_scope():
    row=record(B('+',C(1),I('order')),'>=',B('+',I('parity_code_distance'),I('parity_code_dimension')),positive())
    result=review(row)
    assert result['status']=='known_result'
    assert 'Singleton' in result['summary']
    assert result['closest_results'][0]['url']=='https://doi.org/10.1109/TIT.1964.1053661'
    assert 'adjacency' in result['contribution']


def test_singleton_name_and_model_claim_cannot_promote_other_math():
    row=record(I('parity_code_distance'),'<=',B('+',I('order'),C(1.0000001)),ident='model_f62f129648dab0844b7e')
    row['matched_theorem']={'theorem_name':'Singleton','citation':'Invented exact-match claim'}
    # This is not the exact sentinel either.
    assert review(row)['status']=='awaiting_review'


@pytest.mark.parametrize('guard',[None,positive(0),positive(1.000001),positive(1,'<=')])
def test_nonzero_distance_bound_needs_exact_positive_dimension_premise(guard):
    assert review(record(I('parity_code_distance'),'<=',I('order'),guard))['status']=='awaiting_review'


@pytest.mark.parametrize('left,right',[(I('parity_code_distance'),B('+',I('order'),C(1))),
    (I('unique_neighbor_radius'),I('order')),
    (B('+',I('unique_neighbor_radius'),C(1)),B('+',I('order'),C(1)))])
def test_sentinel_and_radius_consequences_are_routine(left,right):
    result=review(record(left,'<=',right))
    assert result['status']=='routine_consequence'
    assert statuses(result)['routine_consequence']=='fail' # Exclusion gate fails when detected.


def test_regular_guarded_bridge_is_a_specialization():
    row=record(I('parity_code_distance'),'>=',B('+',I('unique_neighbor_radius'),C(1)),G('is_regular'))
    result=review(row)
    assert result['status']=='routine_consequence'
    assert statuses(result)['specialization']=='fail'


def test_degree_two_equality_remains_pending_with_specific_context():
    guard=G(predicate_type='conjunction',guards=[G(predicate_type='comparison',invariant='max_degree',op='<=',threshold=2),positive()])
    row=record(I('parity_code_distance'),'==',B('+',I('unique_neighbor_radius'),C(1)),guard)
    result=review(row)
    assert result['status']=='awaiting_review'
    assert 'zero or two' in result['contribution']
    assert result['closest_results'][0]['relationship']=='related_context'
    assert 'No exact publication match' in ' '.join(result['uncertainties'])
    assert all(statuses(result)[label]=='unknown' for label in ('restatement','specialization','routine_consequence'))
    row['conjecture']['guard_predicate']['guards'][0]['threshold']=3
    assert 'zero or two' not in review(row)['contribution']


def test_exact_restatement_and_guarded_specialization_name_compared_result():
    original=record(I('spectral_radius'),'<=',B('+',I('order'),C(3)),ident='prior')
    duplicate=copy.deepcopy(original);duplicate['id']='current';duplicate['conjecture']['id']='current'
    original['discovered_iteration']=1
    duplicate['discovered_iteration']=2
    for row,expected in [(duplicate,'restatement'),(record(I('spectral_radius'),'<=',B('+',I('order'),C(3)),G('is_tree'),ident='restricted'),'specialization')]:
        result=review(row,[original,row])
        assert result['status']=='routine_consequence'
        assert statuses(result)[expected]=='fail'
        assert result['closest_results'][0]['theorem_id']=='prior'


def test_adding_equal_unknown_result_preserves_canonical_original_for_review():
    first=record(I('spectral_radius'),'<=',B('+',I('order'),C(17)),ident='z_first')
    first['discovered_iteration']=1
    second=copy.deepcopy(first);second['id']='a_later';second['conjecture']['id']='a_later';second['discovered_iteration']=2
    assert review(first,[first])['status']=='awaiting_review'
    for rows in ([first,second],[second,first]):
        assert review(first,rows)['status']=='awaiting_review'
        result=review(second,rows)
        assert result['status']=='routine_consequence'
        assert result['closest_results'][0]['theorem_id']=='z_first'
    first['discovered_iteration']=second['discovered_iteration']=2
    # Stable identity breaks an otherwise identical discovery-time tie.
    assert review(second,[first,second])['status']=='awaiting_review'
    assert review(first,[first,second])['status']=='routine_consequence'


def test_later_universal_result_can_subsume_earlier_guarded_result_without_cycle():
    restricted=record(I('spectral_radius'),'<=',B('+',I('order'),C(17)),G('is_tree'),ident='restricted')
    restricted['discovered_iteration']=1
    universal=record(I('spectral_radius'),'<=',B('+',I('order'),C(17)),ident='universal')
    universal['discovered_iteration']=2
    rows=[restricted,universal]
    assert review(universal,rows)['status']=='awaiting_review'
    result=review(restricted,rows)
    assert result['status']=='routine_consequence'
    assert result['closest_results'][0]['theorem_id']=='universal'


def test_composition_hints_require_oriented_exact_middle_and_matching_guards():
    a=record(I('max_degree'),'>=',I('spectral_radius'),ident='a')
    b=record(I('max_degree'),'<=',B('+',I('order'),C(3)),ident='b')
    row=record(I('spectral_radius'),'<=',B('+',I('order'),C(3)),ident='target',metadata={'origin':'checked_transitivity','parents':['a','b']})
    result=review(row,[a,b,row])
    assert result['status']=='routine_consequence'
    assert {r['theorem_id'] for r in result['closest_results']}=={'a','b'}
    a['conjecture']['guard_predicate']=G('is_regular').to_dict()
    assert review(row,[a,b,row])['status']=='awaiting_review'
    a['conjecture']['guard_predicate']=None
    b['conjecture']['lhs_expr']=I('min_degree').to_dict()
    result=review(row,[a,b,row])
    assert result['status']=='awaiting_review'
    assert statuses(result)['composition_metadata']=='fail'


def test_composition_cannot_cite_the_current_statement_as_its_own_parent():
    row=record(I('spectral_radius'),'<=',B('+',I('order'),C(17)),ident='target',metadata={'origin':'checked_transitivity','parents':['target','reflexive']})
    reflexive=record(B('+',I('order'),C(17)),'<=',B('+',I('order'),C(17)),ident='reflexive')
    result=review(row,[row,reflexive])
    assert result['status']=='awaiting_review'
    assert statuses(result)['composition_metadata']=='fail'


def test_unknown_malformed_or_uncertified_never_promoted_and_inputs_untouched():
    row=record(I('spectral_radius'),'<=',B('+',I('order'),C(17)))
    before=copy.deepcopy(row)
    assert review(row)['status']=='awaiting_review'
    assert row==before
    row['conjecture']['lhs_expr']['ignored_field']=True
    assert statuses(review(row))['structured_statement']=='fail'
    row=before;row['conjecture']['guard_predicate']=17
    assert review(row)['status']=='awaiting_review'
    row['status']='EMPIRICAL_SURVIVOR'
    assert statuses(review(row))['structured_statement']=='fail'
    row=record(I('parity_code_distance'),'<=',I('order'),positive())
    row['conjecture']['guard_predicate']['ignored_negation']=True
    assert statuses(review(row))['structured_statement']=='fail'


def test_registry_exact_match_is_supported_but_shifted_form_not_auto_known():
    row=record(I('chromatic_number'),'<=',B('+',I('spectral_radius'),C(1)))
    assert review(row)['status']=='known_result'
    shifted=record(B('+',I('chromatic_number'),C(1)),'<=',B('+',I('spectral_radius'),C(2)))
    assert review(shifted)['status']=='awaiting_review'


def test_greedy_delta_plus_one_is_not_attributed_to_full_brooks_theorem():
    result=review(record(I('chromatic_number'),'<=',B('+',I('max_degree'),C(1))))
    assert result['status']=='known_result'
    assert result['closest_results'][0]['title']=='Greedy coloring maximum-degree bound'


def registry_with_guard(guard):
    registry=KnownTheoremRegistry()
    registry._theorems=[]
    registry.register(KnownTheorem(id='test',name='Fixture bound',author='Test',year=2026,citation='Test-only fixture',
        lhs=I('spectral_radius'),rel='<=',rhs=I('max_degree'),guard=guard))
    return registry


def test_registry_nearby_inequality_is_not_equivalent():
    registry=KnownTheoremRegistry()
    candidate=Conjecture.from_dict(record(I('chromatic_number'),'<=',B('+',I('spectral_radius'),C(.9999999)))['conjecture'])
    assert registry.match(candidate) is None


@pytest.mark.parametrize('wrong',[G(predicate_type='comparison',invariant='order',op='>=',threshold=2.00001),
    G(predicate_type='comparison',invariant='order',op='>=',threshold=2,negated=True),G(predicate_type='comparison',invariant='order',op='<=',threshold=2)])
def test_registry_numeric_premises_are_complete_exact_not_nearby(wrong):
    required=G(predicate_type='comparison',invariant='order',op='>=',threshold=2)
    registry=registry_with_guard(required)
    assert registry.match(Conjecture.from_dict(record(I('spectral_radius'),'<=',I('max_degree'),required)['conjecture']))
    assert registry.match(Conjecture.from_dict(record(I('spectral_radius'),'<=',I('max_degree'),wrong)['conjecture'])) is None


def test_registry_wrong_negated_property_and_missing_conjunction_clause():
    for required,wrong in [(G('is_triangle_free'),G('is_triangle_free',negated=True)),
        (G(predicate_type='conjunction',guards=[G('is_regular'),G('is_connected')]),G('is_regular'))]:
        registry=registry_with_guard(required)
        assert registry.match(Conjecture.from_dict(record(I('spectral_radius'),'<=',I('max_degree'),wrong)['conjecture'])) is None


def test_registry_does_not_cancel_partial_division_into_an_algebraic_match():
    registry=KnownTheoremRegistry()
    candidate=record(B('+',I('chromatic_number'),B('/',I('order'),I('order'))),'<=',B('+',I('spectral_radius'),C(2)))
    assert registry.match(Conjecture.from_dict(candidate['conjecture'])) is None


def test_query_uses_real_coding_terms_and_accurate_domain():
    checker=LiteratureCrossChecker()
    q=checker.construct_scholarly_query(expander_code_candidates()[0])
    assert 'minimum distance' in q and 'stopping distance' in q and 'coding theory' in q
    assert 'parity code distance' not in q and 'spectral graph theory' not in q


def scaled_energy_pair(left_scale=1, right_scale=.5, relation='<=', guard=None):
    guard = G('is_regular') if guard is None else guard
    prior = record(I('graph_energy'), '>=', B('*', C(2), I('average_degree')), guard, ident='energy_prior')
    prior['discovered_iteration'] = 1
    later = record(B('*', C(left_scale), I('average_degree')), relation,
                   B('*', C(right_scale), I('graph_energy')), guard, ident='energy_later')
    later['discovered_iteration'] = 2
    return prior, later


@pytest.fixture
def no_registry(monkeypatch):
    # Isolate local-library ordering/guard comparisons from the independent
    # registry's already-known universal energy lower bound.
    class EmptyRegistry:
        theorems = {}
    monkeypatch.setattr('autonomous_math.novelty.review_classification.KnownTheoremRegistry', EmptyRegistry)


@pytest.mark.parametrize('left_scale,right_scale', [(1,.5),(2,1),(6,3),(.25,.125)])
def test_exact_positive_rational_rescaling_finds_observed_energy_restatement(left_scale, right_scale, no_registry):
    prior, later = scaled_energy_pair(left_scale, right_scale)
    before = copy.deepcopy([prior, later])
    result = review(later, [later, prior])
    assert result['status'] == 'routine_consequence'
    assert result['closest_results'][0]['theorem_id'] == 'energy_prior'
    assert statuses(result)['rational_rescaling'] == 'pass'
    assert statuses(result)['restatement'] == 'fail'
    assert review(prior, [prior, later])['status'] == 'awaiting_review'
    assert [prior, later] == before


def test_literal_rescaling_preserves_first_representative_and_stable_tie_order(no_registry):
    prior, later = scaled_energy_pair()
    assert review(prior, [prior, later])['status'] == 'awaiting_review'
    assert review(later, [prior, later])['status'] == 'routine_consequence'
    prior['discovered_iteration'] = later['discovered_iteration'] = 2
    # energy_later sorts before energy_prior at the same discovery time.
    assert review(later, [prior, later])['status'] == 'awaiting_review'
    assert review(prior, [prior, later])['status'] == 'routine_consequence'


@pytest.mark.parametrize('left_scale,right_scale,relation', [
    (1,.5,'>='),(1,.5,'<'),(1,.5000001,'<='),(1,.4999999,'<='),
    (0,0,'<='),(-1,-.5,'<='),(1,-.5,'<='),(-1,.5,'<='),
])
def test_rescaling_never_matches_wrong_direction_near_constants_zero_or_negative(left_scale, right_scale, relation, no_registry):
    prior, later = scaled_energy_pair(left_scale, right_scale, relation)
    assert review(later, [prior, later])['status'] == 'awaiting_review'


@pytest.mark.parametrize('wrong,target_expected,parent_expected', [
    (None, 'awaiting_review', 'routine_consequence'),
    (G('is_bipartite'), 'awaiting_review', 'awaiting_review'),
    (G('is_regular', negated=True), 'awaiting_review', 'awaiting_review'),
    (G(predicate_type='conjunction', guards=[G('is_regular'), G('is_connected')]), 'routine_consequence', 'awaiting_review')])
def test_rescaling_respects_direction_of_complete_guard_entailment(wrong, target_expected, parent_expected, no_registry):
    prior, later = scaled_energy_pair()
    later['conjecture']['guard_predicate'] = wrong.to_dict() if wrong else None
    assert review(later, [prior, later])['status'] == target_expected
    # Moving the record earlier does not reverse the direction of implication.
    later['discovered_iteration'] = 0
    assert review(prior, [prior, later])['status'] == parent_expected


def test_scaled_local_rule_does_not_use_variable_division_or_nonlinear_cancellation(no_registry):
    prior, later = scaled_energy_pair()
    original_guard = G('is_regular')
    # Multiplying by a variable is not a positive literal rational scale.
    nonlinear = record(B('*', I('order'), I('average_degree')), '<=',
                       B('*', I('order'), B('*', C(.5), I('graph_energy'))), original_guard, ident='nonlinear')
    nonlinear['discovered_iteration'] = 2
    assert review(nonlinear, [prior, nonlinear])['status'] == 'awaiting_review'
    divided = record(B('/', I('average_degree'), I('order')), '<=',
                     B('/', B('*', C(.5), I('graph_energy')), I('order')),
                     G(predicate_type='conjunction', guards=[original_guard,
                         G(predicate_type='comparison', invariant='order', op='>=', threshold=1)]), ident='divided')
    divided['discovered_iteration'] = 2
    assert review(divided, [prior, divided])['status'] == 'awaiting_review'
    squared = record(B('^', I('average_degree'), C(2)), '<=',
                     B('*', C(.25), B('^', I('graph_energy'), C(2))), original_guard, ident='squared')
    squared['discovered_iteration'] = 2
    assert review(squared, [prior, squared])['status'] == 'awaiting_review'


def test_exact_affine_rearrangement_covers_additions_and_distributed_literal_factors(no_registry):
    prior, later = scaled_energy_pair()
    shifted = record(B('+', I('average_degree'), C(1)), '<=',
                     B('+', B('*', C(.5), I('graph_energy')), C(1)), G('is_regular'), ident='shifted')
    shifted['discovered_iteration'] = 2
    assert review(shifted, [prior, shifted])['status'] == 'routine_consequence'
    prior = record(I('graph_energy'), '<=', B('+', I('order'), C(17)), ident='prior')
    prior['discovered_iteration'] = 1
    distributed = record(B('*', C(2), I('graph_energy')), '<=',
                         B('+', B('*', C(2), I('order')), C(34)), ident='distributed')
    distributed['discovered_iteration'] = 2
    assert review(distributed, [prior, distributed])['status'] == 'routine_consequence'


def test_rescaled_registry_reference_is_known_and_keeps_greedy_attribution():
    row = record(B('*', C(2), I('chromatic_number')), '<=',
                 B('*', C(2), B('+', I('max_degree'), C(1))))
    result = review(row)
    assert result['status'] == 'known_result'
    assert statuses(result)['rational_rescaling'] == 'pass'
    assert result['closest_results'][0]['title'] == 'Greedy coloring maximum-degree bound'
    # New rescaling comparisons do not invent an exact registry guard match.
    row['conjecture']['guard_predicate'] = G('is_regular').to_dict()
    assert review(row)['status'] == 'awaiting_review'


def test_positive_nested_literal_factors_and_swapped_equality_are_supported(no_registry):
    prior, later = scaled_energy_pair()
    later['conjecture']['lhs_expr'] = B('*', C(.5), B('*', I('average_degree'), C(2))).to_dict()
    assert review(later, [prior, later])['status'] == 'routine_consequence'
    prior['conjecture']['rel'] = '=='
    later['conjecture']['rel'] = '=='
    assert review(later, [prior, later])['status'] == 'routine_consequence'


def test_looser_affine_bound_is_described_as_weakening_and_tighter_bound_remains_eligible(no_registry):
    prior = record(I('graph_energy'), '<=', B('+', I('order'), C(17)), ident='prior')
    prior['discovered_iteration'] = 1
    loose = record(I('graph_energy'), '<=', B('+', I('order'), C(18)), ident='loose')
    loose['discovered_iteration'] = 2
    result = review(loose, [prior, loose])
    assert result['status'] == 'routine_consequence'
    assert statuses(result)['weakening'] == 'fail'
    assert result['summary'] == 'Weaker conclusion of an existing checked result.'
    assert 'implication' in result['closest_results'][0]['comparison']
    tight = record(I('graph_energy'), '<=', B('+', I('order'), C(16)), ident='tight')
    tight['discovered_iteration'] = 2
    assert review(tight, [prior, tight])['status'] == 'awaiting_review'
