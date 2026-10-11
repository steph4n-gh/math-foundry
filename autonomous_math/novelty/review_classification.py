"""Conservative mathematical review of already validated certified records.

The caller must validate the current receipt and exact AST, and pass an atlas
containing only currently validated certified records. This module neither
certifies proofs nor establishes publication priority. Labels depend on the
structured proposition and premises, never IDs, names, explanations or scores.
"""
from fractions import Fraction

from autonomous_math.core.ast import BinaryOpNode, ConstantNode, Conjecture, InvariantNode, UnaryOpNode
from autonomous_math.core.invariants import INVARIANT_ALIASES
from autonomous_math.prover.trusted_lean import render_challenge, render_guard
from autonomous_math.novelty.literature_crosscheck import KnownTheoremRegistry, _exact_guard_key
from autonomous_math.novelty.routine_filter import expression_key as _key, find_routine_variant, parse_conjecture

_PIN = 'd13f23b723b8a846827a245b89c10fc7d3f11612'
_MATHLIB = f'https://github.com/leanprover-community/mathlib4/blob/{_PIN}/Mathlib/'
_SINGLETON = {'title': 'Maximum distance q-nary codes', 'url': 'https://doi.org/10.1109/TIT.1964.1053661',
    'citation': 'R. C. Singleton (1964), IEEE Transactions on Information Theory 10(2), 116–118.',
    'statement': 'For a nonzero [n,k,d] linear code, k+d≤n+1.', 'scope': 'Finite-alphabet codes; the current theorem concerns the binary adjacency kernel.'}
_STOPPING = {'title': 'On the Stopping Distance and the Stopping Redundancy of Codes', 'url': 'https://arxiv.org/abs/cs/0503058',
    'citation': 'M. Schwartz and A. Vardy (2006), IEEE Transactions on Information Theory 52(3), 922–932; arXiv:cs/0503058.',
    'statement': 'Stopping distance s(H)≤minimum code distance d; s(H) depends on the parity-check matrix.',
    'scope': 'Binary linear codes with a specified parity-check matrix; here s(A_G)=u+1.'}
_DIMENSION = {'title': 'Submodule dimension and coordinate-space dimension',
    'url': _MATHLIB+'LinearAlgebra/Dimension/Constructions.lean',
    'citation': 'Pinned Mathlib: Submodule.finrank_le and Module.finrank_fintype_fun_eq_card.',
    'statement': 'The dimension of a subspace of F₂^n is at most n.', 'scope': 'Finite-dimensional vector spaces, including adjacency kernels.'}
_HAMMING = {'title': 'Hamming weight is at most the coordinate count', 'url': _MATHLIB+'InformationTheory/Hamming.lean',
    'citation': 'Pinned Mathlib: hammingNorm_le_card_fintype.',
    'statement': 'Every word on n coordinates has Hamming weight at most n.', 'scope': 'Finite coordinate sets; d≤n requires a nonzero codeword.'}
_RADIUS_DEFINITION = {'title': 'Native unique-neighbor radius definition', 'url': None,
    'citation': 'Reviewed trusted_lean.py: unique_neighbor_radius is a natural-number minimum minus one, cast to ℝ.',
    'statement': 'u=maximal guaranteed unique-neighbor radius, with 0≤u≤n.',
    'scope': 'The engine’s exact stopping-set definition with sentinel n+1.'}


def _bound(left, rel, right):
    a, b = _key(left), _key(right)
    if rel in {'>=', '>'}:
        a, b, rel = b, a, {'>=': '<=', '>': '<'}[rel]
    if rel == '==':
        a, b = sorted((a, b), key=repr)
    return rel, a, b


def _signature(c):
    return _bound(c.lhs_expr, c.rel, c.rhs_expr)


def _positive_scalar(node):
    """Extract positive literal factors; all remaining mathematics stays opaque."""
    if isinstance(node, ConstantNode):
        value = Fraction(str(node.value))
        return (value, ('constant', Fraction(1))) if value > 0 else None
    if isinstance(node, BinaryOpNode) and node.op == '*':
        for scalar, expression in ((node.left, node.right), (node.right, node.left)):
            if isinstance(scalar, ConstantNode):
                value = Fraction(str(scalar.value))
                rest = _positive_scalar(expression)
                if value <= 0 or rest is None:
                    return None
                return value * rest[0], rest[1]
    return Fraction(1), _key(node)


def _scalar_bound(left, rel, right):
    """An exact common-positive-scale key, without rewriting either core side."""
    if rel in {'>=', '>'}:
        left, right, rel = right, left, {'>=': '<=', '>': '<'}[rel]
    a, b = _positive_scalar(left), _positive_scalar(right)
    if a is None or b is None:
        return None  # Never divide by zero or reverse a negative multiplier.
    if rel == '==':
        a, b = sorted((a, b), key=lambda item: (repr(item[1]), item[0]))
    return rel, a[1], b[1], b[0] / a[0]


def _scalar_signature(c):
    return _scalar_bound(c.lhs_expr, c.rel, c.rhs_expr)


def _parse(record):
    return parse_conjecture(record['conjecture'])


def _guard(c):
    render_guard(c.guard_predicate)
    return _exact_guard_key(c.guard_predicate)


def _check(result, label, status, detail):
    result['checks'] = [check for check in result['checks'] if check['label'] != label]
    result['checks'].append({'label': label, 'status': status, 'detail': detail})


def _closest(source, relationship, comparison):
    return {**source, 'relationship': relationship, 'comparison': comparison}


def _text(node):
    if isinstance(node, InvariantNode):
        return INVARIANT_ALIASES.get(node.name, node.name)
    if isinstance(node, ConstantNode):
        return str(Fraction(str(node.value)))
    if isinstance(node, UnaryOpNode):
        return f'{node.op}({_text(node.child)})'
    return f'({_text(node.left)} {node.op} {_text(node.right)})'


def _library_result(row, c, relationship, comparison):
    return {'title': 'Existing checked library result', 'url': None,
        'citation': 'Existing checked library', 'theorem_id': row['id'],
        'statement': f'{_text(c.lhs_expr)} {c.rel} {_text(c.rhs_expr)}',
        'scope': 'Finite simple graphs under the exact stored premises.',
        'relationship': relationship, 'comparison': comparison}


def _guard_contains(guard, clause):
    return guard == clause or (guard is not None and guard[0] == 'conjunction'
                              and any(_guard_contains(child, clause) for child in guard[1]))


def _finish(result, status, summary, contribution, source=None, comparison=''):
    result.update(status=status, summary=summary, contribution=contribution)
    if source:
        result['closest_results'].append(_closest(source, status, comparison))
    # These three labels are exclusion gates: pass means the possibility was
    # ruled out, fail means the result was detected, unknown means not resolved.
    _check(result, 'routine_consequence', 'fail' if status == 'routine_consequence' else 'unknown', contribution)
    if status == 'known_result':
        _check(result, 'restatement', 'fail', 'Matches an established or foundational result; not an originality finding.')
    return result


def classify_record(record, atlas):
    """Return a sidecar assessment; the record, atlas and proof artifacts are untouched."""
    result = {'status': 'awaiting_review',
        'summary': 'Certified statement awaiting mathematical and literature review.',
        'contribution': 'A kernel-checked theorem has been added; originality has not been established.',
        'closest_results': [], 'checks': [],
        'uncertainties': ['This automated comparison is not an exhaustive literature or publication-priority audit.']}
    for label in ('restatement', 'specialization', 'routine_consequence'):
        _check(result, label, 'unknown', 'This potential exclusion has not yet been ruled out.')
    _check(result, 'receipt_binding', 'info', 'Requires the caller’s current receipt/dependency and exact-AST validation; this classifier does not run Lean.')
    try:
        if record.get('status') != 'LEAN_CERTIFIED':
            raise ValueError('Only certified records are eligible')
        c = _parse(record)
        sig, guard, scalar_sig = _signature(c), _guard(c), _scalar_signature(c)
    except (KeyError, TypeError, ValueError) as exc:
        _check(result, 'structured_statement', 'fail', str(exc))
        return result
    _check(result, 'structured_statement', 'pass', 'Compared the parsed, natively renderable AST and complete guard; ignored labels and model prose.')
    _check(result, 'comparison_method', 'info', 'Exact rational constants and relation orientation; library comparison also uses rational affine rearrangement and tolerance-correct guard containment. Nonlinear terms remain opaque; no variable cancellation or approximate conclusion matching.')

    n, d, k, u = map(InvariantNode, ('order', 'parity_code_distance', 'parity_code_dimension', 'unique_neighbor_radius'))
    zero, one = ConstantNode(0), ConstantNode(1)
    add = lambda a, b: BinaryOpNode('+', a, b)
    positive = ('comparison', 'parity_code_dimension', '>=', Fraction(1), False)
    if sig == _bound(add(k, d), '<=', add(n, one)):
        _check(result, 'known_result_match', 'pass', 'Exact Singleton rate–distance inequality for the native binary kernel; n+1 sentinel also covers the zero code.')
        return _finish(result, 'known_result', 'Singleton’s classical code dimension–distance bound.',
            'Certifies the familiar information-capacity versus minimum-distance ceiling for adjacency-kernel codes; useful for screening code parameters.',
            _SINGLETON, 'Exact inequality; the current guard is retained, while the zero-code sentinel permits the universal extension.')

    foundations = [
        (_bound(add(u, one), '<=', d), 'Unique-neighbor code-distance foundation.',
         'Every nonzero kernel word has a stopping support, so u+1≤d. The finite sentinels cover zero codes and empty graphs.', _STOPPING),
        (_bound(k, '<=', n), 'Binary kernel dimension is at most its length.',
         'A standard subspace-dimension bound; checks code capacity without implying a new coding construction.', _DIMENSION),
        (_bound(zero, '<=', u), 'The unique-neighbor radius is nonnegative by its native definition.',
         'A foundational sanity fact: u is a natural-number stopping-set minimum minus one, then cast to ℝ.', _RADIUS_DEFINITION),
    ]
    for pattern, summary, contribution, source in foundations:
        if sig == pattern:
            status = 'known_result' if guard is None else 'routine_consequence'
            if guard is not None:
                _check(result, 'specialization', 'fail', 'Detected added premises on a universal foundational inequality; they are unnecessary for this mathematical implication.')
                summary = 'Guarded specialization of a universal foundation: '+summary
            return _finish(result, status, summary, contribution, source, 'Exact foundational inequality, with the stored premises preserved.')
    if sig == _bound(d, '<=', n) and guard == positive:
        return _finish(result, 'known_result', 'A nonzero binary code has minimum distance at most its length.',
            'Positive kernel dimension supplies a nonzero word; its Hamming weight is at most n. The premise is essential because the zero code has d=n+1.',
            _HAMMING, 'Exact bound with the explicit positive-dimension premise.')
    if sig == _bound(d, '<=', add(n, one)):
        return _finish(result, 'routine_consequence', 'Direct consequence of the finite distance sentinel.',
            'The distance definition includes n+1 in its finite minimum, so d≤n+1 adds no independent coding restriction.')
    if sig in {_bound(u, '<=', n), _bound(add(u, one), '<=', add(n, one))}:
        return _finish(result, 'routine_consequence', 'The unique-neighbor radius is bounded by the number of variables.',
            'Follows from the stopping-set sentinel, or by transitivity of u+1≤d≤n+1; this mathematical comparison does not identify causal proof dependencies.')

    # Check explicit composition hints by their actual mathematics, not their names.
    metadata = c.metadata or {}
    parents = metadata.get('parents')
    if metadata.get('origin') == 'checked_transitivity' and isinstance(parents, list) and len(parents) == 2:
        try:
            rows = [atlas['theorems'][ident] for ident in parents]
            if record.get('id') in parents or parents[0] == parents[1]:
                raise ValueError('Composition does not identify two distinct prior results')
            if any(row.get('status') != 'LEAN_CERTIFIED' for row in rows):
                raise ValueError('A parent is not currently validated/certified')
            pcs = [_parse(row) for row in rows]
            ps = [_signature(pc) for pc in pcs]
            if any(_guard(pc) not in (None, guard) for pc in pcs):
                raise ValueError('Parent premises do not follow from the exact current premise')
            valid = any(a[0] == b[0] == sig[0] == '<=' and a[2] == b[1]
                        and sig[1:] == (a[1], b[2]) for a, b in (ps, ps[::-1]))
            if not valid:
                raise ValueError('The two exact parent inequalities do not compose to this target')
            result['closest_results'].extend(_library_result(row, pc, 'transitivity_parent',
                'One of two exact oriented parent inequalities with a shared middle expression and compatible premises.')
                for row, pc in zip(rows, pcs))
            return _finish(result, 'routine_consequence', 'Exact transitive consequence of two existing checked bounds.',
                'The oriented parent inequalities have the same middle expression and compatible premises; no new intermediate mathematical argument is required.')
        except (KeyError, TypeError, ValueError) as exc:
            _check(result, 'composition_metadata', 'fail', str(exc))

    routine = find_routine_variant(c, atlas.get('theorems', {}), current_record=record)
    if routine:
        other = atlas['theorems'][routine['parent_ids'][0]]
        pc = _parse(other)
        relationship = routine['relationship']
        _check(result, relationship, 'fail', 'An existing validated theorem entails the current statement by exact rational affine rewriting and complete guard containment.')
        _check(result, 'affine_implication', 'pass', routine['expression_rule']+' '+routine['guard_rule'])
        if _scalar_signature(c) is not None and _scalar_signature(c) == _scalar_signature(pc):
            _check(result, 'rational_rescaling', 'pass', 'Exact positive rational scaling is included in the affine implication check.')
        result['routine_evidence'] = routine
        result['closest_results'].append(_library_result(other, pc, relationship,
            'Exact rational affine conclusion implication; current premises entail all parent premises.'))
        summaries = {
            'restatement': 'Restatement of an existing checked result.',
            'specialization': 'Guarded specialization of an existing checked result.',
            'weakening': 'Weaker conclusion of an existing checked result.',
        }
        return _finish(result, 'routine_consequence',
            summaries[relationship],
            'Adds a certified presentation, narrower premise or weaker conclusion to mathematics already in the validated library.')

    if sig[1] == sig[2] and sig[0] in {'<=', '=='}:
        return _finish(result, 'routine_consequence', 'Reflexive identity or inequality.', 'Both structured sides are the same expression.')

    # Registry comparisons retain exact premises and core expressions. The
    # legacy polynomial matcher and cancellation rules are not used here.
    for theorem in KnownTheoremRegistry().theorems:
        tg = _exact_guard_key(theorem.guard)
        direct = _bound(theorem.lhs, theorem.rel, theorem.rhs) == sig
        rescaled = (not direct and scalar_sig is not None and tg == guard
                    and scalar_sig == _scalar_bound(theorem.lhs, theorem.rel, theorem.rhs))
        if not (direct or rescaled) or (tg is not None and tg != guard):
            continue
        source = {'title': theorem.name, 'url': theorem.url, 'citation': theorem.citation,
                  'statement': f'{_text(theorem.lhs)} {theorem.rel} {_text(theorem.rhs)}',
                  'scope': 'Finite simple graphs with the registry’s explicit premises.'}
        # The Δ+1 bound is greedy coloring, not the stronger exceptions-sensitive Brooks theorem.
        if (sig == _bound(InvariantNode('chromatic_number'), '<=', add(InvariantNode('max_degree'), one))
                or rescaled and scalar_sig == _scalar_bound(InvariantNode('chromatic_number'), '<=', add(InvariantNode('max_degree'), one))):
            source.update(title='Greedy coloring maximum-degree bound',
                citation='Bondy and Murty (1976), Graph Theory with Applications, vertex colourings.',
                url='https://math.arizona.edu/~kglasner/math443/BondyMurtyGTWA.pdf')
        _check(result, 'known_result_match', 'pass', 'Exact local registry proposition'+(' up to a common positive literal rational factor with identical complete premises.' if rescaled else ' and compatible complete premises; no broad algebraic near-match used.'))
        if rescaled:
            _check(result, 'rational_rescaling', 'pass', 'Both complete sides differ by the same strictly positive rational factor; opaque core expressions and complete guards match.')
        result['uncertainties'].append('The registry citation is an attribution, not a fresh verification of every source’s statement or historical priority.')
        specialized = tg is None and guard is not None
        if specialized:
            _check(result, 'specialization', 'fail', 'Detected a restriction of a universal registry proposition.')
        return _finish(result, 'routine_consequence' if specialized else 'known_result',
            ('Guarded specialization of ' if specialized else 'Exact structured match to ')+source['title']+'.',
            'Known inequality reproduced for the current native graph definitions and stored premises.', source,
            ('Exact positive rational rescaling of both sides; complete premises match.' if rescaled
             else 'Exact sides and relation; '+('extra current premises specialize a universal result.' if specialized else 'required premises match exactly.')))

    variables = c.lhs_expr.variables | c.rhs_expr.variables
    if {'parity_code_distance', 'unique_neighbor_radius'} <= variables:
        result['closest_results'].append(_closest(_STOPPING, 'related_context',
            'Establishes the standard s(H)≤d context; this is not an exact prior-art match for the current proposition.'))
        if sig == _bound(d, '==', add(u, one)):
            result['summary'] = 'Useful stopping-distance/code-distance equality awaiting literature review.'
            result['contribution'] = 'Characterizes when the erasure stopping threshold reaches code distance under the stored premises.'
            if _guard_contains(guard, ('comparison', 'max_degree', '<=', Fraction(2), False)):
                result['contribution'] += ' With maximum degree≤2, each stopping-set check intersection has zero or two positions, so its indicator is a binary kernel word.'
            result['uncertainties'].append('No exact publication match or originality conclusion has been established for this structural equality.')
    if {'parity_code_distance', 'parity_code_dimension'} <= variables:
        result['closest_results'].append(_closest(_SINGLETON, 'related_context',
            'Relevant rate–distance ceiling; no exact match or consequence established for this proposition.'))
    return result
