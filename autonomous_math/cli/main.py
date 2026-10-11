"""Feature 16: Unified Orchestration CLI for Autonomous Mathematical Discovery.

Provides subcommands:
- `conjecture`: Formulate candidate graph-theoretic bounds (exhaustive, archetypes, guarded).
- `sieve`: Filter candidate conjectures against empirical extremal instance database and CEGAR.
- `prove`: Search deductive derivation trees using Prover-Skeptic AO* loop.
- `export`: Generate academic LaTeX preprints and Lean 4 comparator challenges.
- `demo`: Run end-to-end discovery demonstration scenarios (C5 refutation, greedy bound, clique bound).
- `discover`: Execute full autonomous discovery cycle (conjecture -> sieve -> prove -> export).
"""

from __future__ import annotations

import argparse
import ast
import json
import logging
from pathlib import Path
import re
import sys
import time
from typing import Any, Dict, List, Literal, Optional, Sequence, Tuple, Union

from autonomous_math.core.ast import (
    BinaryOpNode,
    Conjecture,
    ConstantNode,
    ExpressionNode,
    GuardPredicate,
    InvariantNode,
    UnaryOpNode,
    deserialize_expression,
)
from autonomous_math.core.invariants import INVARIANT_ALIASES, GraphInvariantEvaluator
from autonomous_math.conjecturing.generator import ConjectureGenerator
from autonomous_math.sieve.certificates import (
    CounterexampleCertificate,
    SieveResult,
    build_c5_counterexample_certificate,
)
from autonomous_math.sieve.instance_db import InstanceDatabase
from autonomous_math.sieve.z3_sieve import EmpiricalSieveRunner
from autonomous_math.prover.dag import LemmaDAG
from autonomous_math.prover.search import ProofResult, ProverSkepticSearch
from autonomous_math.export.latex_generator import LatexPreprintGenerator
from autonomous_math.export.lean_generator import LeanComparatorGenerator
from autonomous_math.export.validator import ArtifactValidator

logger = logging.getLogger("autonomous_math.cli.main")


# ============================================================================
# Polymorphic Expression & Conjecture Parsers
# ============================================================================


def _parse_expr_str(expr_str: str) -> ExpressionNode:
    """Parse mathematical arithmetic string into an ExpressionNode AST tree.

    Supports binary ops (+, -, *, /, ^), unary ops (sqrt, abs, neg),
    and graph invariant symbols or functions (e.g. chi(G), Delta, alpha).
    """
    s = expr_str.strip().replace("^", "**")
    if not s:
        return InvariantNode(name="order")

    try:
        py_ast = ast.parse(s, mode="eval").body
    except Exception:
        # Fallback for raw identifier
        return InvariantNode(name=s)

    def _convert(node: ast.AST) -> ExpressionNode:
        if isinstance(node, ast.Constant):
            return ConstantNode(value=float(node.value))
        elif isinstance(node, ast.Name):
            return InvariantNode(name=node.id)
        elif isinstance(node, ast.BinOp):
            op_map = {
                ast.Add: "+",
                ast.Sub: "-",
                ast.Mult: "*",
                ast.Div: "/",
                ast.Pow: "^",
            }
            op_str = op_map.get(type(node.op), "+")
            return BinaryOpNode(op_str, _convert(node.left), _convert(node.right))
        elif isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return UnaryOpNode("neg", _convert(node.operand))
        elif isinstance(node, ast.Call):
            func_name = node.func.id if isinstance(node.func, ast.Name) else ""
            # Handle invariant function calls like chi(G), Delta(G)
            if (
                len(node.args) == 1
                and isinstance(node.args[0], ast.Name)
                and node.args[0].id in {"G", "g"}
            ):
                return InvariantNode(name=func_name)
            if func_name in {"sqrt", "sqr", "floor", "ceil", "abs", "inv", "log1p"} and len(node.args) >= 1:
                return UnaryOpNode(func_name, _convert(node.args[0]))
            if func_name in {"max", "min"} and len(node.args) == 2:
                return BinaryOpNode(func_name, _convert(node.args[0]), _convert(node.args[1]))
            return InvariantNode(name=func_name or "order")
        raise ValueError(f"Cannot parse AST node: {ast.dump(node)}")

    try:
        return _convert(py_ast)
    except Exception:
        return InvariantNode(name=s)


# Expose parse_expr_str as alias to guarantee no NameError in any context
parse_expr_str = _parse_expr_str


def _resolve_conjecture_from_dict(data: Any) -> Conjecture:
    """Polymorphically resolve a Conjecture instance from dict or AST model.

    Handles:
    - Full AST dict with lhs_expr and rhs_expr
    - SieveResult or ProofResult dictionaries with nested conjecture
    - Minimal dictionaries containing only id, statement, rel, complexity
    - Guard predicate premise strings (e.g. is_triangle_free ==> chi <= 2)
    """
    if isinstance(data, Conjecture):
        return data
    if not isinstance(data, dict):
        raise TypeError(f"Expected dict or Conjecture, got {type(data).__name__}")

    # 1. Unpack nested conjecture from SieveResult or ProofResult
    if "conjecture" in data and isinstance(data["conjecture"], (dict, Conjecture)):
        return _resolve_conjecture_from_dict(data["conjecture"])

    # 2. Try standard Conjecture.from_dict if full AST fields exist
    if "lhs_expr" in data and "rhs_expr" in data:
        try:
            return Conjecture.from_dict(data)
        except Exception:
            pass

    # 3. Synthesize AST nodes from statement and relation
    conj_id = str(data.get("id", "c_synthesized"))
    stmt = str(data.get("statement", "")).strip()
    rel = data.get("rel")

    guard_obj: Optional[GuardPredicate] = None
    core_stmt = stmt

    # Split premise guard if present
    for delim in ["==>", "-->", r"\implies", "implies"]:
        if delim in core_stmt:
            g_part, core_stmt = core_stmt.split(delim, 1)
            g_part = g_part.strip()
            g_part = re.sub(r"^\\forall\s+[^,]+,\s*", "", g_part)
            if g_part.startswith("is_"):
                prop_name = g_part.split("(")[0].strip()
                guard_obj = GuardPredicate(property_name_or_type=prop_name)
            else:
                m = re.match(r"([a-zA-Z_]+)\s*(<=|>=|==|<|>)\s*([0-9.]+)", g_part)
                if m:
                    guard_obj = GuardPredicate(
                        predicate_type="comparison",
                        invariant=m.group(1),
                        op=m.group(2),
                        threshold=float(m.group(3)),
                    )
                else:
                    guard_obj = GuardPredicate(property_name_or_type=g_part)
            break

    if not guard_obj and "guard_predicate" in data:
        gp = data["guard_predicate"]
        if isinstance(gp, str):
            guard_obj = GuardPredicate(property_name_or_type=gp)
        elif isinstance(gp, dict):
            guard_obj = GuardPredicate.from_dict(gp)

    # Locate relational operator and split LHS/RHS
    known_rels = ["<=", ">=", "==", "<", ">", "≤", "≥"]
    rel_found = None
    lhs_part = ""
    rhs_part = ""

    if rel and rel in core_stmt:
        rel_found = rel
        lhs_part, rhs_part = core_stmt.split(rel, 1)
    else:
        for r_cand in known_rels:
            if r_cand in core_stmt:
                rel_found = r_cand
                lhs_part, rhs_part = core_stmt.split(r_cand, 1)
                break

    if rel_found in {"<=", "≤"}:
        rel_norm: Literal["<=", ">=", "==", "<", ">"] = "<="
    elif rel_found in {">=", "≥"}:
        rel_norm = ">="
    elif rel_found in {"==", "<", ">"}:
        rel_norm = rel_found  # type: ignore
    else:
        rel_norm = "<="

    lhs_node = _parse_expr_str(lhs_part) if lhs_part.strip() else InvariantNode(name="chromatic_number")
    rhs_node = _parse_expr_str(rhs_part) if rhs_part.strip() else ConstantNode(value=1.0)

    complexity = int(data.get("complexity", lhs_node.complexity + rhs_node.complexity + 1))

    return Conjecture.create(
        id=conj_id,
        lhs=lhs_node,
        rel=rel_norm,
        rhs=rhs_node,
        guard=guard_obj,
        statement=stmt or f"{lhs_node.to_latex()} {rel_norm} {rhs_node.to_latex()}",
        metadata={"complexity": complexity},
    )


def _load_conjectures_from_file(file_path: Path) -> Tuple[List[Conjecture], bool]:
    """Load and polymorphically resolve conjectures from a JSON file.

    Returns (conjectures, is_batch).
    """
    raw_text = file_path.read_text(encoding="utf-8")
    data = json.loads(raw_text)

    if isinstance(data, list):
        conjectures = [_resolve_conjecture_from_dict(item) for item in data]
        return conjectures, True
    elif isinstance(data, dict):
        conjecture = _resolve_conjecture_from_dict(data)
        return [conjecture], False
    else:
        raise ValueError(f"Unexpected JSON root type: {type(data).__name__}")


def _guard_matches(conj: Conjecture, target_guard: str) -> bool:
    """Check if a conjecture matches a specified premise guard."""
    if not target_guard:
        return True
    g = conj.guard_predicate
    if g is None:
        return False
    if isinstance(g, str):
        return g.lower() == target_guard.lower() or target_guard.lower() in g.lower()
    if isinstance(g, GuardPredicate):
        if g.property_name and g.property_name.lower() == target_guard.lower():
            return True
        if g.predicate_type == "property" and g.property_name and target_guard.lower() in g.property_name.lower():
            return True
        if g.invariant and target_guard.lower() in g.invariant.lower():
            return True
    if target_guard.lower() in (conj.statement or "").lower():
        return True
    return False


# ============================================================================
# Subcommand Handlers
# ============================================================================


def _cmd_conjecture(args: argparse.Namespace) -> int:
    """Execute `conjecture` subcommand."""
    generator = ConjectureGenerator()
    limit = max(1, args.limit)

    conjectures: List[Conjecture] = []

    if args.strategy == "archetypes":
        all_archetypes = generator.generate_archetypal()
        if args.guard:
            conjectures = [c for c in all_archetypes if _guard_matches(c, args.guard)]
        else:
            conjectures = all_archetypes
        if args.limit is not None and args.limit > 0:
            conjectures = conjectures[: max(limit, len(all_archetypes) if args.limit >= len(all_archetypes) else limit)]
    elif args.guard:
        guard_obj = GuardPredicate(property_name_or_type=args.guard)
        conjectures = generator.generate_recursive(guards=[guard_obj], limit=limit)
        if len(conjectures) < limit:
            arch_matches = [c for c in generator.generate_archetypal() if _guard_matches(c, args.guard)]
            conjectures = (conjectures + arch_matches)[:limit]
    else:
        conjectures = generator.generate_exhaustive(limit=limit)

    out_data = [c.to_dict() for c in conjectures]
    json_str = json.dumps(out_data, indent=2)

    if args.output:
        out_path = Path(args.output)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json_str, encoding="utf-8")
        logger.info("Generated %d conjectures -> %s", len(conjectures), out_path)
    else:
        print(json_str)

    return 0


def _cmd_sieve(args: argparse.Namespace) -> int:
    """Execute `sieve` subcommand."""
    in_path = Path(args.input)
    if not in_path.exists():
        print(f"Error: Input file does not exist: {in_path}", file=sys.stderr)
        return 1

    try:
        conjectures, _ = _load_conjectures_from_file(in_path)
    except Exception as exc:
        print(f"Error reading input conjectures: {exc}", file=sys.stderr)
        return 1

    db = InstanceDatabase()
    results: List[SieveResult] = []

    if args.tier1_only:
        for c in conjectures:
            results.append(db.sieve_conjecture(c))
    else:
        sieve_runner = EmpiricalSieveRunner(instance_db=db, enable_z3_fallback=True)
        for c in conjectures:
            res = sieve_runner.run(c, max_smt_order=min(max(1, args.cegar_max_rounds), 5))
            results.append(res)

    out_data = [r.to_dict() for r in results]
    json_str = json.dumps(out_data, indent=2)

    if args.output:
        out_path = Path(args.output)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json_str, encoding="utf-8")
        logger.info("Sieved %d conjectures -> %s", len(results), out_path)
    else:
        print(json_str)

    return 0


def _cmd_prove(args: argparse.Namespace) -> int:
    """Execute `prove` subcommand."""
    in_path = Path(args.input)
    if not in_path.exists():
        print(f"Error: Input file does not exist: {in_path}", file=sys.stderr)
        return 1

    try:
        conjectures, is_batch = _load_conjectures_from_file(in_path)
    except Exception as exc:
        print(f"Error reading input conjectures: {exc}", file=sys.stderr)
        return 1

    prover = ProverSkepticSearch(max_depth=args.max_depth)
    proof_results: List[ProofResult] = []

    for c in conjectures:
        res = prover.prove(c, max_depth=args.max_depth)
        proof_results.append(res)

    if is_batch:
        out_data: Union[List[Dict[str, Any]], Dict[str, Any]] = [r.to_dict() for r in proof_results]
    else:
        out_data = proof_results[0].to_dict()

    json_str = json.dumps(out_data, indent=2)

    if args.output:
        out_path = Path(args.output)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json_str, encoding="utf-8")
        logger.info("Synthesized proofs for %d target(s) -> %s", len(proof_results), out_path)
    else:
        print(json_str)

    return 0


def _cmd_export(args: argparse.Namespace) -> int:
    """Execute `export` subcommand."""
    in_path = Path(args.input)
    if not in_path.exists():
        print(f"Error: Input file does not exist: {in_path}", file=sys.stderr)
        return 1

    try:
        raw_target = json.loads(in_path.read_text(encoding="utf-8"))
    except Exception as exc:
        print(f"Error loading export target JSON: {exc}", file=sys.stderr)
        return 1

    target = raw_target[0] if isinstance(raw_target, list) and raw_target else raw_target

    out_dir = Path(args.output_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    fmt = getattr(args, "format", "all")

    if fmt in {"all", "latex"}:
        latex_gen = LatexPreprintGenerator()
        latex_gen.generate(target, output_dir=out_dir)

    if fmt in {"all", "lean"}:
        lean_gen = LeanComparatorGenerator()
        lean_out_dir = out_dir / "lean" if fmt == "all" else out_dir
        lean_gen.generate(target, output_dir=lean_out_dir)

    val_res = ArtifactValidator.validate_export_bundle(out_dir)
    if not val_res.is_valid:
        logger.warning("Artifact validation reported warnings/errors: %s", val_res.errors)

    logger.info("Deliverables exported to %s (format: %s)", out_dir, fmt)
    return 0


def _cmd_demo(args: argparse.Namespace) -> int:
    """Execute `demo` subcommand (Feature 17)."""
    from autonomous_math.cli.demo import run_demo

    return run_demo(
        scenario=args.scenario,
        output_dir=Path(args.output_dir) if args.output_dir else None,
    )


def _cmd_discover(args: argparse.Namespace) -> int:
    """Execute `discover` end-to-end autonomous discovery loop."""
    out_dir = Path(args.output_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    limit = max(1, getattr(args, "conjectures_limit", 3))
    guard_filter = getattr(args, "guard", None)

    # 1. Conjecture Generation
    generator = ConjectureGenerator()
    if guard_filter:
        guard_obj = GuardPredicate(property_name_or_type=guard_filter)
        conjectures = generator.generate_recursive(guards=[guard_obj], limit=limit)
        if len(conjectures) < limit:
            arch_matches = [c for c in generator.generate_archetypal() if _guard_matches(c, guard_filter)]
            conjectures = (conjectures + arch_matches)[:limit]
    else:
        conjectures = generator.generate_archetypal()[:limit]
        if len(conjectures) < limit:
            conjectures.extend(generator.generate_exhaustive(limit=limit - len(conjectures)))

    conj_file = out_dir / "conjectures.json"
    conj_file.write_text(json.dumps([c.to_dict() for c in conjectures], indent=2), encoding="utf-8")

    # 2. Empirical Sieve
    db = InstanceDatabase()
    sieve_results = [db.sieve_conjecture(c) for c in conjectures]
    sieve_file = out_dir / "sieve_results.json"
    sieve_file.write_text(json.dumps([sr.to_dict() for sr in sieve_results], indent=2), encoding="utf-8")

    # 3. Prover-Skeptic Search
    prover = ProverSkepticSearch()
    proof_results: List[ProofResult] = []
    primary_target: Any = sieve_results[0] if sieve_results else None

    for sr in sieve_results:
        if sr.status == "SURVIVED":
            pr = prover.prove(sr.conjecture)
            proof_results.append(pr)
            if primary_target is None or getattr(primary_target, "status", "") != "PROVEN":
                primary_target = pr
        else:
            refuted_pr = ProofResult(
                status="REFUTED",
                conjecture=sr.conjecture,
                dag=LemmaDAG(root_node_id=sr.conjecture.id),
                critique_summary={
                    "status": "refuted",
                    "counterexample": sr.counterexample_certificate.to_dict()
                    if sr.counterexample_certificate
                    else None,
                },
            )
            proof_results.append(refuted_pr)

    proof_file = out_dir / "proof_results.json"
    proof_file.write_text(json.dumps([pr.to_dict() for pr in proof_results], indent=2), encoding="utf-8")

    # 4. Export Artifacts
    if primary_target is not None:
        latex_gen = LatexPreprintGenerator()
        latex_gen.generate(primary_target, output_dir=out_dir / "paper")
        lean_gen = LeanComparatorGenerator()
        lean_gen.generate(primary_target, output_dir=out_dir / "lean")

        if getattr(args, "verify_lean", False):
            from autonomous_math.prover.lean_prover import LeanProofSearch
            lean_prover = LeanProofSearch()
            v_dir = out_dir / "lean" / "verified"
            v_dir.mkdir(parents=True, exist_ok=True)
            for pr_item in proof_results:
                if getattr(pr_item, "status", "") == "PROVEN":
                    lean_prover.prove_conjecture(pr_item, output_dir=v_dir)

    logger.info("Autonomous discovery run completed cleanly at %s", out_dir)
    return 0


def _cmd_prove_lean(args: argparse.Namespace) -> int:
    """Execute `prove-lean` subcommand."""
    from autonomous_math.prover.lean_prover import LeanProofSearch
    prover = LeanProofSearch(timeout_per_attempt=args.timeout)
    in_path = Path(args.input)
    if not in_path.exists():
        print(f"Error: Input file does not exist: {in_path}", file=sys.stderr)
        return 1

    out_dir = Path(args.output_dir) if args.output_dir else None

    if in_path.suffix == ".lean":
        res = prover.prove_challenge(in_path, output_dir=out_dir)
        results = [res]
    else:
        try:
            conjectures, is_batch = _load_conjectures_from_file(in_path)
            results = [prover.prove_conjecture(c, output_dir=out_dir) for c in conjectures]
        except Exception as exc:
            print(f"Error reading input: {exc}", file=sys.stderr)
            return 1

    out_data = [r.to_dict() for r in results]
    output_obj = out_data if len(results) > 1 else out_data[0]
    json_str = json.dumps(output_obj, indent=2)

    if args.output:
        out_path = Path(args.output)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json_str, encoding="utf-8")
        logger.info("Lean verification results -> %s", out_path)
    else:
        print(json_str)

    return 0


# ============================================================================
# Argument Parser Construction
# ============================================================================


def build_parser() -> argparse.ArgumentParser:
    """Construct unified command line interface argument parser."""
    parser = argparse.ArgumentParser(
        prog="autonomous-math",
        description="Autonomous Mathematical Discovery Pipeline Orchestration CLI.",
    )

    subparsers = parser.add_subparsers(
        dest="subcommand",
        title="subcommands",
        description="Available discovery pipeline subcommands",
        required=True,
    )

    # 1. conjecture
    p_conj = subparsers.add_parser(
        "conjecture", help="Generate candidate mathematical conjectures."
    )
    p_conj.add_argument(
        "--limit", "-n", type=int, default=5, help="Number of candidate conjectures to generate (default: 5)."
    )
    p_conj.add_argument(
        "--guard", "-g", type=str, default=None, help="Premise guard predicate filter (e.g. 'is_triangle_free')."
    )
    p_conj.add_argument(
        "--strategy", "-s", type=str, default=None, help="Conjecture formulation strategy ('archetypes', 'exhaustive')."
    )
    p_conj.add_argument(
        "--output", "-o", type=str, default=None, help="Destination JSON file path."
    )

    # 2. sieve
    p_sieve = subparsers.add_parser(
        "sieve", help="Filter candidate conjectures through empirical falsification sieve."
    )
    p_sieve.add_argument(
        "--input", "-i", type=str, required=True, help="Input JSON file containing candidate conjecture(s)."
    )
    p_sieve.add_argument(
        "--output", "-o", type=str, default=None, help="Output JSON file for SieveResult models."
    )
    p_sieve.add_argument(
        "--tier1-only", action="store_true", default=False, dest="tier1_only", help="Execute only fast Tier 1 catalog sieve without Z3 fallback."
    )
    p_sieve.add_argument(
        "--cegar-max-rounds", type=int, default=5, dest="cegar_max_rounds", help="Maximum CEGAR refinement rounds (default: 5)."
    )

    # 3. prove
    p_prove = subparsers.add_parser(
        "prove", help="Synthesize deductive proofs via Prover-Skeptic search loop."
    )
    p_prove.add_argument(
        "--input", "-i", type=str, required=True, help="Input JSON file containing conjecture or SieveResult."
    )
    p_prove.add_argument(
        "--output", "-o", type=str, default=None, help="Output JSON file for ProofResult."
    )
    p_prove.add_argument(
        "--max-depth", "-d", type=int, default=4, dest="max_depth", help="Maximum AO* goal decomposition depth (default: 4)."
    )
    p_prove.add_argument(
        "--timeout", "-t", type=float, default=10.0, dest="timeout", help="Search timeout in seconds (default: 10.0)."
    )

    # 4. export
    p_export = subparsers.add_parser(
        "export", help="Compile preprint manuscripts and Lean 4 comparator challenges."
    )
    p_export.add_argument(
        "--input", "-i", type=str, required=True, help="Input JSON file containing ProofResult, SieveResult, or Conjecture."
    )
    p_export.add_argument(
        "--output-dir", "-o", type=str, required=True, dest="output_dir", help="Destination directory for exported deliverables."
    )
    p_export.add_argument(
        "--format", "-f", type=str, default="all", choices=["all", "latex", "lean"], help="Export format ('all', 'latex', 'lean')."
    )

    # 5. demo
    p_demo = subparsers.add_parser(
        "demo", help="Run end-to-end mathematical discovery demonstration pipelines."
    )
    p_demo.add_argument(
        "--scenario", "-s", type=str, required=True, help="Demonstration scenario ('c5_refutation', 'greedy_coloring_bound', 'clique_chromatic_bound')."
    )
    p_demo.add_argument(
        "--output-dir", "-o", type=str, default=None, dest="output_dir", help="Optional destination directory to persist deliverables."
    )

    # 6. discover
    p_disc = subparsers.add_parser(
        "discover", help="Run autonomous end-to-end discovery loop (conjecture -> sieve -> prove -> export)."
    )
    p_disc.add_argument(
        "--conjectures-limit", "-n", type=int, default=3, dest="conjectures_limit", help="Number of candidate conjectures to generate (default: 3)."
    )
    p_disc.add_argument(
        "--guard", "-g", type=str, default=None, help="Premise guard predicate filter."
    )
    p_disc.add_argument(
        "--output-dir", "-o", type=str, required=True, dest="output_dir", help="Destination directory for all discovery artifacts."
    )
    p_disc.add_argument(
        "--verify-lean", action="store_true", default=False, dest="verify_lean", help="Formally certify generated Lean 4 challenge specs."
    )

    # 7. prove-lean
    p_prove_lean = subparsers.add_parser(
        "prove-lean", help="Formally verify Lean 4 challenge specs using automated tactic search."
    )
    p_prove_lean.add_argument(
        "--input", "-i", type=str, required=True, help="Input .lean challenge file or conjecture JSON."
    )
    p_prove_lean.add_argument(
        "--output-dir", "-o", type=str, default=None, dest="output_dir", help="Directory to save verified Lean artifacts."
    )
    p_prove_lean.add_argument(
        "--output-json", type=str, default=None, dest="output", help="Optional path to output result JSON."
    )
    p_prove_lean.add_argument(
        "--timeout", "-t", type=float, default=10.0, dest="timeout", help="Timeout per tactic attempt in seconds (default: 10.0)."
    )

    # 8. dashboard
    p_dash = subparsers.add_parser(
        "dashboard", help="Launch interactive visual discovery dashboard web server."
    )
    p_dash.add_argument(
        "--port", "-p", type=int, default=8050, help="Port to serve dashboard on (default: 8050)."
    )
    p_dash.add_argument(
        "--host", type=str, default="127.0.0.1", help="Host address (default: 127.0.0.1)."
    )
    p_dash.add_argument("--output-dir", type=Path, default=None, help="Authoritative research snapshot directory.")

    return parser


def _cmd_dashboard(args: argparse.Namespace) -> int:
    """Execute dashboard web server."""
    from autonomous_math.dashboard.server import run_dashboard
    run_dashboard(port=args.port, host=args.host, block=True, data_dir=args.output_dir)
    return 0


# ============================================================================
# Main Entrypoint
# ============================================================================


def main(args: Optional[Sequence[str]] = None) -> int:
    """Unified command-line interface entrypoint for autonomous_math.

    Parameters
    ----------
    args : Optional[Sequence[str]]
        Command line arguments list. If None, parses sys.argv[1:].

    Returns
    -------
    int
        0 on success; non-zero integer on error.
    """
    parser = build_parser()

    # Do not catch SystemExit here: allow invalid/missing arguments to raise
    # SystemExit with code != 0, satisfying test_r5_cli_invalid_arguments_exit_code
    parsed_args = parser.parse_args(args if args is not None else sys.argv[1:])

    subcommand = parsed_args.subcommand

    dispatch_map = {
        "conjecture": _cmd_conjecture,
        "sieve": _cmd_sieve,
        "prove": _cmd_prove,
        "export": _cmd_export,
        "demo": _cmd_demo,
        "discover": _cmd_discover,
        "prove-lean": _cmd_prove_lean,
        "dashboard": _cmd_dashboard,
    }

    handler = dispatch_map.get(subcommand)
    if handler is None:
        print(f"Error: Unknown subcommand '{subcommand}'", file=sys.stderr)
        return 1

    try:
        return handler(parsed_args)
    except Exception as exc:
        logger.exception("Subcommand '%s' failed with unhandled exception", subcommand)
        print(f"Error executing '{subcommand}': {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
