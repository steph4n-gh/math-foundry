"""Sound, bounded routine-variant checks before expensive model proof requests.

``find_routine_variant`` requires an already receipt-validated certified library.
It establishes only a local implication, never a new certification or priority
claim. Exact rational affine arithmetic treats nonlinear subexpressions as
opaque atoms. It never cancels variable factors or variable denominators.
"""
from fractions import Fraction
import hashlib
import json
import math
from types import SimpleNamespace
from pathlib import Path

from autonomous_math.core.ast import BinaryOpNode, ConstantNode, Conjecture, InvariantNode, UnaryOpNode
from autonomous_math.core.invariants import INVARIANT_ALIASES
from autonomous_math.prover.trusted_lean import _GUARD_TOLERANCE, _INTEGER_INVARIANTS, render_challenge, render_guard


def expression_key(node):
    if isinstance(node, InvariantNode):
        return ('invariant', INVARIANT_ALIASES.get(node.name, node.name))
    if isinstance(node, ConstantNode):
        return ('constant', Fraction(str(node.value)))
    if isinstance(node, UnaryOpNode):
        return ('unary', node.op, expression_key(node.child))
    if isinstance(node, BinaryOpNode):
        children = [expression_key(node.left), expression_key(node.right)]
        if node.op in {'+', '*'}:
            children.sort(key=repr)
        return ('binary', node.op, *children)
    raise ValueError('Unrecognized expression')


def _add(a, b, multiplier=Fraction(1)):
    result = dict(a)
    for key, value in b.items():
        result[key] = result.get(key, Fraction(0)) + multiplier * value
        if not result[key]:
            del result[key]
    return result


def _scale(a, scalar):
    return {key: scalar * value for key, value in a.items() if scalar * value}


def _affine(node):
    if isinstance(node, ConstantNode):
        return {('constant',): Fraction(str(node.value))} if node.value else {}
    if isinstance(node, UnaryOpNode) and node.op == 'neg':
        return _scale(_affine(node.child), Fraction(-1))
    if isinstance(node, BinaryOpNode):
        if node.op in {'+', '-'}:
            return _add(_affine(node.left), _affine(node.right), Fraction(1 if node.op == '+' else -1))
        if node.op == '*':
            for scalar, expression in ((node.left, node.right), (node.right, node.left)):
                if isinstance(scalar, ConstantNode):
                    return _scale(_affine(expression), Fraction(str(scalar.value)))
        if node.op == '/' and isinstance(node.right, ConstantNode) and node.right.value:
            return _scale(_affine(node.left), 1 / Fraction(str(node.right.value)))
    return {expression_key(node): Fraction(1)}


def affine_signature(conjecture):
    """Exact equivalent proposition key; positive scaling preserves inequalities."""
    left, right, relation = conjecture.lhs_expr, conjecture.rhs_expr, conjecture.rel
    if relation in {'>=', '>'}:
        left, right, relation = right, left, {'>=': '<=', '>': '<'}[relation]
    difference = _add(_affine(left), _affine(right), Fraction(-1))
    if not difference:
        return relation, ()
    terms = sorted(difference.items(), key=lambda term: repr(term[0]))
    # Equality permits either sign; an inequality permits only a positive scale.
    scale = terms[0][1] if relation == '==' else abs(terms[0][1])
    return relation, tuple((key, value / scale) for key, value in terms)


def _inequality_bound(conjecture):
    """Write an inequality as F + c <= 0 (or < 0), scaling positively.

    F contains the nonconstant affine terms, including opaque nonlinear atoms.
    A constant-only proposition has no matching direction and is left to the
    existing exact-equivalence check.
    """
    left, right, relation = conjecture.lhs_expr, conjecture.rhs_expr, conjecture.rel
    if relation in {'>=', '>'}:
        left, right, relation = right, left, {'>=': '<=', '>': '<'}[relation]
    if relation not in {'<=', '<'}:
        return None
    difference = _add(_affine(left), _affine(right), Fraction(-1))
    constant = difference.pop(('constant',), Fraction(0))
    terms = sorted(difference.items(), key=lambda term: repr(term[0]))
    if not terms:
        return None
    scale = abs(terms[0][1])
    return relation, tuple((key, value / scale) for key, value in terms), constant / scale, scale


def _inequality_implication(target, parent):
    if target is None or parent is None or target[1] != parent[1]:
        return None
    target_relation, _, target_constant, target_scale = target
    parent_relation, _, parent_constant, parent_scale = parent
    slack = parent_constant - target_constant
    if slack < 0 or (slack == 0 and parent_relation == '<=' and target_relation == '<'):
        return None
    return {'positive_scale': str(target_scale / parent_scale),
            'normalized_constant_slack': str(slack),
            'parent_relation': parent_relation, 'target_relation': target_relation}


def _tighten(current, value, strict, lower):
    if current is None:
        return value, strict
    old, old_strict = current
    if value == old:
        return value, strict or old_strict
    return (value, strict) if (value > old if lower else value < old) else current


def _guard_constraints(guard):
    """Intervals are exact translator semantics, including the 1e-7 guard shift."""
    properties, intervals = set(), {}
    def include(g):
        if isinstance(g, str):
            from autonomous_math.core.ast import GuardPredicate
            g = GuardPredicate.from_dict(g)
        if g is None or g.predicate_type == 'universal':
            return
        if g.predicate_type == 'conjunction':
            for child in g.guards or []:
                include(child)
            return
        if g.predicate_type == 'property':
            properties.add((g.property_name, g.negated))
            return
        if g.predicate_type != 'comparison':
            raise ValueError('Unsupported guard')
        name = INVARIANT_ALIASES.get(g.invariant or 'order', g.invariant or 'order')
        threshold = Fraction(str(g.threshold or 0))
        low, high = intervals.get(name, (None, None))
        if g.op in {'>=', '>', '=='}:
            strict = g.op == '>'
            value = threshold + _GUARD_TOLERANCE if strict else threshold - _GUARD_TOLERANCE
            if name in _INTEGER_INVARIANTS:
                value = Fraction(math.floor(value) + 1 if strict else math.ceil(value))
                strict = False
            low = _tighten(low, value, strict, True)
        if g.op in {'<=', '<', '=='}:
            strict = g.op == '<'
            value = threshold - _GUARD_TOLERANCE if strict else threshold + _GUARD_TOLERANCE
            if name in _INTEGER_INVARIANTS:
                value = Fraction(math.ceil(value) - 1 if strict else math.floor(value))
                strict = False
            high = _tighten(high, value, strict, False)
        intervals[name] = low, high
    render_guard(guard)  # Reject unsupported/malformed premises before comparison.
    include(guard)
    if any((name, not negated) in properties for name, negated in properties):
        raise ValueError('Contradictory property guard')
    for low, high in intervals.values():
        if low and high and (low[0] > high[0] or (low[0] == high[0] and (low[1] or high[1]))):
            raise ValueError('Contradictory numeric guard')
    return frozenset(properties), intervals


def _endpoint_implies(actual, required, lower):
    if required is None:
        return True
    if actual is None:
        return False
    av, astrict = actual
    rv, rstrict = required
    return (av > rv if lower else av < rv) or (av == rv and (not rstrict or astrict))


def guard_implies(actual, required):
    """Conservative exact containment; no inferred graph-property implications."""
    try:
        ap, ai = _guard_constraints(actual)
        rp, ri = _guard_constraints(required)
        return rp <= ap and all(
            _endpoint_implies(ai.get(name, (None, None))[0], low, True)
            and _endpoint_implies(ai.get(name, (None, None))[1], high, False)
            for name, (low, high) in ri.items())
    except (TypeError, ValueError, AttributeError):
        return False


def parse_conjecture(raw):
    """Refuse ignored expression/guard fields and unsupported expression domains."""
    if isinstance(raw, dict) and not isinstance(raw.get('guard_predicate'), (dict, str, type(None))):
        raise ValueError('Malformed structured guard')
    c = raw if isinstance(raw, Conjecture) else Conjecture.from_dict(raw)
    if isinstance(raw, dict):
        if any(raw[side] != c.to_dict()[side] for side in ('lhs_expr', 'rhs_expr')):
            raise ValueError('Noncanonical or ignored expression fields')
        def check(g):
            if isinstance(g, dict):
                allowed = {'node_type', 'predicate_type', 'property_name', 'negated',
                           'invariant', 'op', 'threshold', 'guards'}
                if set(g) - allowed:
                    raise ValueError('Ignored guard fields')
                for child in g.get('guards') or []:
                    check(child)
        check(raw.get('guard_predicate'))
    render_challenge(c)
    return c


def _record_order(row):
    value = row.get('discovered_iteration')
    if not isinstance(value, (int, float)) or isinstance(value, bool) or not math.isfinite(value) or value < 0:
        value = math.inf
    return value, str(row.get('id', ''))


def find_routine_variant(conjecture, validated_library, *, current_record=None):
    """Return auditable implication evidence, or None to retain the ordinary queue.

    Library rows must already have passed current receipt/AST binding validation.
    A helper remains available to its parent: callers may keep a matched helper
    as a task while avoiding a redundant discovery/proof request. ``current_record``
    preserves the earliest representative when classifying an existing library.
    """
    try:
        c = parse_conjecture(conjecture)
        target = affine_signature(c)
        target_bound = _inequality_bound(c)
        rows = validated_library.values() if isinstance(validated_library, dict) else validated_library
        for row in sorted(rows, key=_record_order):
            if row.get('status') != 'LEAN_CERTIFIED' or row.get('id') == c.id:
                continue
            try:
                parent = parse_conjecture(row['conjecture'])
                equivalent_conclusions = target == affine_signature(parent)
                implication = _inequality_implication(target_bound, _inequality_bound(parent))
                if (not equivalent_conclusions and implication is None) or not guard_implies(c.guard_predicate, parent.guard_predicate):
                    continue
                equivalent_guards = guard_implies(parent.guard_predicate, c.guard_predicate)
                if current_record is not None and equivalent_conclusions and equivalent_guards and _record_order(row) >= _record_order(current_record):
                    continue
                binding = {'parent_id': row['id'], 'target': c.to_dict(), 'parent': parent.to_dict()}
                return {'method': 'exact_rational_affine_implication',
                        'relationship': ('restatement' if equivalent_guards else 'specialization') if equivalent_conclusions else 'weakening',
                        'parent_ids': [row['id']],
                        'binding_sha256': hashlib.sha256(json.dumps(binding, sort_keys=True).encode()).hexdigest(),
                        'guard_rule': 'Exact property containment and tolerance-correct rational/integer interval containment.',
                        'expression_rule': 'Identical nonconstant affine terms up to positive rational scale, with a weaker constant or compatible strictness; nonlinear atoms are opaque.',
                        'conclusion_implication': implication,
                        'helper_for': list(c.metadata.get('helper_for', [])),
                        'certifies_target': False}
            except (KeyError, TypeError, ValueError, AttributeError):
                continue
    except (KeyError, TypeError, ValueError, AttributeError):
        pass
    return None


def check_local_implication(conjecture, validated_library, output_dir, *, workspace_dir=None,
                            total_timeout_sec=20, max_attempts=2):
    """Reuse the existing bounded local prover; never invoke a model or add axioms.

    Returns an exact new receipt only if the target kernel proof actually names
    a validated library dependency. Unresolved/timeouts retain the normal queue.
    This optional fallback belongs in an owned proof worker, not an unbounded
    proposal loop. Receipt validation and process cancellation remain those of
    LeanProofSearch. No new search or compiler implementation is introduced.
    """
    from autonomous_math.prover.lean_prover import LeanProofSearch
    c = parse_conjecture(conjecture)
    rows = validated_library.values() if isinstance(validated_library, dict) else validated_library
    lemmas = {}
    for row in rows:
        path = (row.get('lean_proof') or {}).get('receipt_path')
        if row.get('status') == 'LEAN_CERTIFIED' and row.get('id') != c.id and path:
            lemmas[row['id']] = SimpleNamespace(lemma_id=row['id'], receipt_path=path,
                                               helper_for=(row.get('conjecture') or {}).get('metadata', {}).get('helper_for', []))
    if not lemmas:
        return None
    search = LeanProofSearch(workspace_dir=workspace_dir, flywheel=SimpleNamespace(lemmas=lemmas),
        auto_register_flywheel=False, synthesizer=None, max_attempts=max_attempts,
        timeout_per_attempt=min(10, total_timeout_sec), total_timeout_sec=total_timeout_sec)
    try:
        result = search.prove_challenge(c, output_dir=output_dir, save_verified_artifact=True)
        from autonomous_math.research_state import atomic_save_json
        atomic_save_json({'target': c.to_dict(), 'candidate_parent_ids': sorted(lemmas),
                          'request_timeout_sec': total_timeout_sec, 'result': result.to_dict()},
                         Path(output_dir) / 'routine_implication_attempt.json')
        if result.is_machine_checked and set(result.used_lemma_ids) & set(lemmas):
            return {'method': 'bounded_local_lean_implication', 'parent_ids': result.used_lemma_ids,
                    'receipt_path': str(result.receipt_path), 'certifies_target': True,
                    'status': result.status, 'diagnostics': result.diagnostics}
        return None
    finally:
        search.cancel()
