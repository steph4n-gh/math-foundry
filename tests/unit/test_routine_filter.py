"""Exact local routine matching; adverse controls preserve the ordinary queue."""
import copy
from fractions import Fraction
from types import SimpleNamespace

import pytest

from autonomous_math.core.ast import BinaryOpNode as B, ConstantNode as C, Conjecture, GuardPredicate as G, InvariantNode as I
from autonomous_math.novelty.routine_filter import affine_signature, check_local_implication, find_routine_variant, guard_implies


def comparison(name, op, threshold):
    return G(predicate_type='comparison', invariant=name, op=op, threshold=threshold)


def conjecture(left, relation, right, guard=None, ident='target', metadata=None):
    return Conjecture.create(id=ident, lhs=left, rel=relation, rhs=right, guard=guard, metadata=metadata or {})


def row(c, iteration=1, **kwargs):
    return {'id': c.id, 'status': 'LEAN_CERTIFIED', 'conjecture': c.to_dict(), 'discovered_iteration': iteration, **kwargs}


def base(guard=None):
    return conjecture(B('+', I('parity_code_dimension'), B('*', C(2), I('unique_neighbor_radius'))), '<=', I('order'), guard, 'parent')


@pytest.mark.parametrize('target', [
    conjecture(B('-', I('order'), I('parity_code_dimension')), '>=', B('*', C(2), I('unique_neighbor_radius'))),
    conjecture(B('+', B('*', C(3), I('parity_code_dimension')), B('*', C(6), I('unique_neighbor_radius'))), '<=', B('*', C(3), I('order'))),
    conjecture(B('+', I('parity_code_dimension'), B('*', C(2), I('unique_neighbor_radius'))), '<=', B('+', I('order'), B('-', C(7), C(7)))),
])
def test_exact_rational_affine_rearrangements(target):
    parent = row(base())
    untouched = copy.deepcopy([parent, target.to_dict()])
    match = find_routine_variant(target, [parent])
    assert match['relationship'] == 'restatement'
    assert match['parent_ids'] == ['parent']
    assert len(match['binding_sha256']) == 64
    assert match['certifies_target'] is False
    assert [parent, target.to_dict()] == untouched


@pytest.mark.parametrize('op,threshold,expected', [
    ('>=', 1.00000009, True), ('>=', 1.00000011, False),
    ('>', .9999999, False), ('>', .9999998, True),
    ('<=', .9999999, True), ('<', 1.0000001, False),
])
def test_integer_guard_boundary_respects_exact_tolerance(op, threshold, expected):
    # Target k=1 implies the required constraint precisely when 1 satisfies it.
    actual = comparison('parity_code_dimension', '==', 1)
    assert guard_implies(actual, comparison('parity_code_dimension', op, threshold)) is expected


@pytest.mark.parametrize('actual,required,expected', [
    (comparison('order', '>=', 2), comparison('order', '>=', 1), True),
    (comparison('order', '>=', 1), comparison('order', '>=', 2), False),
    (comparison('order', '==', 2), comparison('order', '<=', 2), True),
    (comparison('order', '>', 1), comparison('order', '>=', 2), True),
    (comparison('graph_energy', '>=', 2), comparison('graph_energy', '>', 2), False),
    (comparison('graph_energy', '>', 2), comparison('graph_energy', '>=', 2), True),
    (G('is_tree'), G('is_connected'), False),
    (G('is_tree'), G('is_tree', negated=True), False),
    (None, comparison('parity_code_dimension', '>=', 1), False),
])
def test_guard_containment_has_no_unsound_domain_or_property_inference(actual, required, expected):
    assert guard_implies(actual, required) is expected


def test_strengthened_conjunction_and_normalized_integer_thresholds():
    prior_guard = G(predicate_type='conjunction', guards=[comparison('min_degree', '>=', 1), comparison('max_degree', '>=', 1), comparison('parity_code_dimension', '>=', 1)])
    target_guard = G(predicate_type='conjunction', guards=[comparison('min_degree', '>=', .9999999), comparison('max_degree', '>=', 1.9999999), comparison('parity_code_dimension', '>=', .9999999), G('is_connected')])
    parent = row(base(prior_guard))
    target = base(target_guard).model_copy(update={'id': 'target'})
    match = find_routine_variant(target, [parent])
    assert match['relationship'] == 'specialization'
    assert guard_implies(target_guard, prior_guard)
    assert not guard_implies(prior_guard, target_guard)


def test_normalized_equal_guards_keep_first_representative_and_helper_metadata():
    parent = row(base(comparison('parity_code_dimension', '>=', 1)))
    target = conjecture(base().lhs_expr, '<=', I('order'), comparison('parity_code_dimension', '>=', .9999999), metadata={'helper_for': ['target_parent']})
    match = find_routine_variant(target, [parent])
    assert match['relationship'] == 'restatement'
    assert match['helper_for'] == ['target_parent']
    current = row(target, iteration=0)
    assert find_routine_variant(target, [parent], current_record=current) is None


@pytest.mark.parametrize('target', [
    conjecture(B('*', C(-1), base().lhs_expr), '<=', B('*', C(-1), I('order'))),
    conjecture(base().lhs_expr, '<', I('order')),
    conjecture(base().lhs_expr, '<=', B('-', I('order'), C(.0000001))),
    conjecture(B('*', I('order'), base().lhs_expr), '<=', B('*', I('order'), I('order'))),
    conjecture(B('/', base().lhs_expr, I('order')), '<=', C(1), comparison('order', '>=', 1)),
])
def test_negative_sign_strictness_nearby_conclusions_and_variable_cancellation_are_not_matches(target):
    assert find_routine_variant(target, [row(base())]) is None


def test_constant_division_is_exact_but_zero_or_unprotected_variable_division_is_not():
    assert find_routine_variant(conjecture(B('/', base().lhs_expr, C(2)), '<=', B('/', I('order'), C(2))), [row(base())])
    assert find_routine_variant(conjecture(B('/', base().lhs_expr, C(0)), '<=', I('order')), [row(base())]) is None
    assert find_routine_variant(conjecture(B('/', base().lhs_expr, I('order')), '<=', C(1)), [row(base())]) is None


def test_nonlinear_atoms_can_be_rearranged_but_are_never_algebraically_cancelled():
    nonlinear = B('*', I('order'), I('max_degree'))
    parent = conjecture(nonlinear, '<=', B('+', I('graph_energy'), C(7)), ident='parent')
    target = conjecture(B('-', nonlinear, I('graph_energy')), '<=', C(7))
    assert find_routine_variant(target, [row(parent)])
    divided = conjecture(I('max_degree'), '<=', B('/', B('+', I('graph_energy'), C(7)), I('order')), comparison('order', '>=', 1))
    assert find_routine_variant(divided, [row(parent)]) is None


def test_zero_code_and_empty_graph_scope_never_inferred_from_other_graph_properties():
    parent = conjecture(I('parity_code_distance'), '<=', I('order'), comparison('parity_code_dimension', '>=', 1), 'parent')
    assert find_routine_variant(conjecture(I('parity_code_distance'), '<=', I('order')), [row(parent)]) is None
    assert find_routine_variant(conjecture(I('parity_code_distance'), '<=', I('order'), G('is_connected')), [row(parent)]) is None


def test_malformed_or_uncertified_library_and_contradictory_guards_cannot_filter():
    parent = row(base())
    parent['status'] = 'EMPIRICAL_SURVIVOR'
    assert find_routine_variant(base().model_copy(update={'id': 'target'}), [parent]) is None
    parent = row(base())
    parent['conjecture']['lhs_expr']['ignored'] = True
    assert find_routine_variant(base().model_copy(update={'id': 'target'}), [parent]) is None
    guard = G(predicate_type='conjunction', guards=[comparison('order', '>=', 3), comparison('order', '<=', 2)])
    assert find_routine_variant(base(guard).model_copy(update={'id': 'target'}), [row(base())]) is None


def test_equality_permits_reversing_sign_but_inequality_does_not():
    parent = conjecture(I('order'), '==', B('+', I('parity_code_dimension'), C(7)), ident='parent')
    target = conjecture(B('-', I('parity_code_dimension'), I('order')), '==', C(-7))
    assert find_routine_variant(target, [row(parent)])


@pytest.mark.parametrize('parent_relation,target_relation,slack,expected', [
    ('<=', '<=', 0, True), ('<', '<=', 0, True),
    ('<', '<', 0, True), ('<=', '<', 0, False),
    ('<=', '<=', 1, True), ('<=', '<', 1, True),
    ('<', '<=', 1, True), ('<', '<', 1, True),
    ('<=', '<=', -1, False), ('<', '<', -1, False),
    ('<', '<=', -1, False), ('<=', '<', -1, False),
])
def test_constant_slack_and_strictness_implication(parent_relation, target_relation, slack, expected):
    parent = conjecture(I('max_degree'), parent_relation, I('size'), ident='parent')
    target = conjecture(I('max_degree'), target_relation, B('+', I('size'), C(slack)))
    match = find_routine_variant(target, [row(parent)])
    assert bool(match) is expected
    if match and (slack or parent_relation != target_relation):
        assert match['relationship'] == 'weakening'
        assert match['conclusion_implication']['normalized_constant_slack'] == str(slack)
        assert match['certifies_target'] is False


@pytest.mark.parametrize('scale', [.5, 2, 7])
def test_positive_rational_scaling_and_lower_bound_orientation(scale):
    parent = conjecture(I('size'), '>=', I('max_degree'), ident='parent')
    target = conjecture(B('*', C(scale), I('max_degree')), '<',
                        B('+', B('*', C(scale), I('size')), C(.25)))
    match = find_routine_variant(target, [row(parent)])
    assert match['relationship'] == 'weakening'
    assert Fraction(match['conclusion_implication']['positive_scale']) == Fraction(str(scale))
    assert Fraction(match['conclusion_implication']['normalized_constant_slack']) == Fraction(1, 4) / Fraction(str(scale))


@pytest.mark.parametrize('scale', [0, -1, -2])
def test_zero_or_negative_scale_cannot_establish_implication(scale):
    parent = conjecture(I('max_degree'), '<=', I('size'), ident='parent')
    target = conjecture(B('*', C(scale), I('max_degree')), '<=',
                        B('+', B('*', C(scale), I('size')), C(1)))
    assert find_routine_variant(target, [row(parent)]) is None


def test_positive_slack_is_exact_and_tighter_true_bound_is_retained():
    parent = conjecture(I('max_degree'), '<=', B('+', I('size'), C(1)), ident='parent')
    tighter_true_bound = conjecture(I('max_degree'), '<=', I('size'))
    assert find_routine_variant(tighter_true_bound, [row(parent)]) is None
    near = conjecture(I('max_degree'), '<', B('+', I('size'), C(1.000000000001)))
    match = find_routine_variant(near, [row(parent)])
    assert Fraction(match['conclusion_implication']['normalized_constant_slack']) == Fraction(1, 10**12)
    assert find_routine_variant(conjecture(I('max_degree'), '<=', B('+', I('size'), C(.999999999999))), [row(parent)]) is None


def test_equivalent_representative_protection_does_not_preserve_loose_old_bounds():
    old = conjecture(I('max_degree'), '<=', B('+', I('size'), C(1)), ident='old')
    stronger_later = row(conjecture(I('max_degree'), '<=', I('size'), ident='later'), iteration=2)
    match = find_routine_variant(old, [stronger_later], current_record=row(old, iteration=1))
    assert match['relationship'] == 'weakening'
    equal_later = row(old.model_copy(update={'id': 'later'}), iteration=2)
    assert find_routine_variant(old, [equal_later], current_record=row(old, iteration=1)) is None


def test_equality_and_unsupported_evidence_do_not_infer_inequality_weakening():
    parent = row(conjecture(I('max_degree'), '==', I('size'), ident='parent'))
    target = conjecture(I('max_degree'), '<=', B('+', I('size'), C(1)))
    assert find_routine_variant(target, [parent]) is None
    parent = row(conjecture(I('max_degree'), '<=', I('size'), ident='parent'))
    parent['status'] = 'EMPIRICAL_SURVIVOR'
    assert find_routine_variant(target, [parent]) is None
    parent['status'] = 'LEAN_CERTIFIED'
    parent['conjecture']['rhs_expr']['ignored'] = True
    assert find_routine_variant(target, [parent]) is None


def test_local_lean_fallback_has_finite_model_free_budget_and_requires_used_parent(monkeypatch, tmp_path):
    calls = []
    class Search:
        def __init__(self, **kwargs):
            calls.append(kwargs)
            assert kwargs['synthesizer'] is None
            assert kwargs['auto_register_flywheel'] is False
            assert kwargs['total_timeout_sec'] == 20
            assert kwargs['max_attempts'] == 2
        def prove_challenge(self, target, **kwargs):
            calls.append(kwargs)
            return SimpleNamespace(is_machine_checked=True, used_lemma_ids=['parent'], receipt_path=tmp_path/'proof.receipt.json', status='MACHINE_CHECKED_PROVEN', diagnostics=[], to_dict=lambda: {'status': 'MACHINE_CHECKED_PROVEN'})
        def cancel(self):
            calls.append('cancelled')
    monkeypatch.setattr('autonomous_math.prover.lean_prover.LeanProofSearch', Search)
    parent = row(base(), lean_proof={'receipt_path': '/checked.receipt.json'})
    result = check_local_implication(base().model_copy(update={'id': 'target'}), [parent], tmp_path)
    assert result['certifies_target'] is True
    assert calls[-1] == 'cancelled'


def test_local_lean_fallback_without_receipt_does_not_launch(monkeypatch, tmp_path):
    monkeypatch.setattr('autonomous_math.prover.lean_prover.LeanProofSearch', lambda **kw: pytest.fail('compiler launched'))
    assert check_local_implication(base(), [row(base())], tmp_path) is None


# Exact mathematical AST/guard slices of the three reviewed checkpoint260 claims.
# Epistemic prose is omitted; it is never an assumption of this matcher.
REVIEWED_AST_INPUTS = [{'id': 'hull_signless_laplacian_spectral_radius_le_1_size_1_9b51f8e6875e',
  'statement': 'q_1(G) <= m + 1',
  'lhs_expr': {'name': 'signless_laplacian_spectral_radius', 'node_type': 'invariant'},
  'rel': '<=',
  'rhs_expr': {'left': {'name': 'size', 'node_type': 'invariant'},
               'node_type': 'binary_op',
               'op': '+',
               'right': {'node_type': 'constant', 'value': 1.0}},
  'guard_predicate': None,
  'complexity': 5},
 {'id': 'hull_spectral_radius_le_0.25_size_1.5_fafb16939177',
  'statement': '\\lambda_1(G) <= \\frac{1}{4} \\cdot m + 1.5',
  'lhs_expr': {'name': 'spectral_radius', 'node_type': 'invariant'},
  'rel': '<=',
  'rhs_expr': {'left': {'left': {'node_type': 'constant', 'value': 0.25},
                        'node_type': 'binary_op',
                        'op': '*',
                        'right': {'name': 'size', 'node_type': 'invariant'}},
               'node_type': 'binary_op',
               'op': '+',
               'right': {'node_type': 'constant', 'value': 1.5}},
  'guard_predicate': None,
  'complexity': 7},
 {'id': 'model_ad89177ba7a4bf76dbff',
  'statement': 'G \\in \\mathcal{G}_{\\text{connected}} \\land n \\ge 4 ==> n \\cdot q_1(G) \\cdot '
               '\\left(q_1(G) - (2 \\cdot \\left(\\omega(G) - (1)\\right))\\right) >= \\mu_2(G) \\cdot '
               '\\left(n \\cdot q_1(G) - (2 \\cdot \\omega(G) \\cdot \\left(\\omega(G) - '
               '(1)\\right))\\right)',
  'lhs_expr': {'left': {'left': {'name': 'order', 'node_type': 'invariant'},
                        'node_type': 'binary_op',
                        'op': '*',
                        'right': {'name': 'signless_laplacian_spectral_radius',
                                  'node_type': 'invariant'}},
               'node_type': 'binary_op',
               'op': '*',
               'right': {'left': {'name': 'signless_laplacian_spectral_radius',
                                  'node_type': 'invariant'},
                         'node_type': 'binary_op',
                         'op': '-',
                         'right': {'left': {'node_type': 'constant', 'value': 2.0},
                                   'node_type': 'binary_op',
                                   'op': '*',
                                   'right': {'left': {'name': 'clique_number', 'node_type': 'invariant'},
                                             'node_type': 'binary_op',
                                             'op': '-',
                                             'right': {'node_type': 'constant', 'value': 1.0}}}}},
  'rel': '>=',
  'rhs_expr': {'left': {'name': 'algebraic_connectivity', 'node_type': 'invariant'},
               'node_type': 'binary_op',
               'op': '*',
               'right': {'left': {'left': {'name': 'order', 'node_type': 'invariant'},
                                  'node_type': 'binary_op',
                                  'op': '*',
                                  'right': {'name': 'signless_laplacian_spectral_radius',
                                            'node_type': 'invariant'}},
                         'node_type': 'binary_op',
                         'op': '-',
                         'right': {'left': {'left': {'node_type': 'constant', 'value': 2.0},
                                            'node_type': 'binary_op',
                                            'op': '*',
                                            'right': {'name': 'clique_number',
                                                      'node_type': 'invariant'}},
                                   'node_type': 'binary_op',
                                   'op': '*',
                                   'right': {'left': {'name': 'clique_number', 'node_type': 'invariant'},
                                             'node_type': 'binary_op',
                                             'op': '-',
                                             'right': {'node_type': 'constant', 'value': 1.0}}}}},
  'guard_predicate': {'guards': [{'guards': None,
                                  'invariant': None,
                                  'negated': False,
                                  'node_type': 'guard',
                                  'op': None,
                                  'predicate_type': 'property',
                                  'property_name': 'is_connected',
                                  'threshold': None},
                                 {'guards': None,
                                  'invariant': 'order',
                                  'negated': False,
                                  'node_type': 'guard',
                                  'op': '>=',
                                  'predicate_type': 'comparison',
                                  'property_name': None,
                                  'threshold': 4.0}],
                      'invariant': None,
                      'negated': False,
                      'node_type': 'guard',
                      'op': None,
                      'predicate_type': 'conjunction',
                      'property_name': None,
                      'threshold': None},
  'complexity': 28}]


@pytest.mark.parametrize('raw', REVIEWED_AST_INPUTS, ids=lambda raw: raw['id'])
def test_reviewed_claim_restatement_slack_strengthening_and_helper(raw):
    reviewed = Conjecture.from_dict(raw)
    parent = reviewed.model_copy(update={'id': 'checked_parent'})
    library = [row(parent)]
    assert find_routine_variant(reviewed, library)['relationship'] == 'restatement'
    side = 'lhs_expr' if reviewed.rel == '>=' else 'rhs_expr'
    weaker = reviewed.model_copy(update={side: B('+', getattr(reviewed, side), C(.125)),
                                        'metadata': {'helper_for': ['nontrivial_parent']}})
    untouched = copy.deepcopy([weaker.to_dict(), library])
    match = find_routine_variant(weaker, library)
    assert match['relationship'] == 'weakening'
    assert match['helper_for'] == ['nontrivial_parent']
    assert match['certifies_target'] is False
    assert [weaker.to_dict(), library] == untouched
    tighter = reviewed.model_copy(update={side: B('-', getattr(reviewed, side), C(.125))})
    assert find_routine_variant(tighter, library) is None
    extended_guard = G(predicate_type='conjunction', guards=[
        reviewed.guard_predicate or G(predicate_type='universal'), comparison('order', '>=', 5)])
    assert find_routine_variant(reviewed.model_copy(update={'guard_predicate': extended_guard}), library)['relationship'] == 'specialization'
    guarded_parent = row(parent.model_copy(update={'guard_predicate': extended_guard}))
    assert find_routine_variant(weaker, [guarded_parent]) is None


def test_reviewed_nonlinear_claim_never_cancels_a_positive_guarded_variable_factor():
    reviewed = Conjecture.from_dict(REVIEWED_AST_INPUTS[-1])
    parent = reviewed.model_copy(update={'id': 'checked_parent'})
    multiplied = reviewed.model_copy(update={
        'lhs_expr': B('*', I('order'), reviewed.lhs_expr),
        'rhs_expr': B('*', I('order'), reviewed.rhs_expr)})
    assert find_routine_variant(multiplied, [row(parent)]) is None
    assert find_routine_variant(reviewed.model_copy(update={'guard_predicate': None}), [row(parent)]) is None


def test_reversing_a_negative_scale_and_inequality_is_valid_rewriting():
    parent = conjecture(I('max_degree'), '<=', I('size'), ident='parent')
    target = conjecture(B('*', C(-2), I('max_degree')), '>=', B('*', C(-2), I('size')))
    assert find_routine_variant(target, [row(parent)])['relationship'] == 'restatement'
