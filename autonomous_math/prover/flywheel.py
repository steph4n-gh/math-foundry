"""Autonomous Mathematical Discovery: Continuous Self-Improvement & Lemma Flywheel.

When Lean 4 verifies a theorem, the Flywheel automatically registers the proven
theorem as an active lemma in Lean's environment (generating lemma bridges in
`lean_workspace/Mathlib.lean` and expanding candidate tactic scripts in
`LeanProofSearch`), allowing subsequent daemon cycles to invoke earlier proven
theorems to prove deeper, multi-step conjectures.

Also provides closed-loop feedback into hypothesis formulation by tracking
invariant fertility and boundary graphs.
"""

from __future__ import annotations

import json
import logging
import os
from pathlib import Path
import re
import shutil
import time
from typing import Any, Dict, List, Optional, Set, Tuple, Union

from pydantic import BaseModel, ConfigDict, Field

from autonomous_math.core.ast import (
    BinaryOpNode,
    Conjecture,
    ConstantNode,
    ExpressionNode,
    GuardPredicate,
    InvariantNode,
)
from autonomous_math.export.lean_generator import _format_statement_fallback, _to_pascal_case, _to_snake_case

logger = logging.getLogger("flywheel")

RECOGNIZED_RELATION_OPERATORS: Tuple[str, ...] = (
    "≤",
    "≥",
    "<",
    ">",
    "=",
    "→",
    "≈",
    "≡",
    "∣",
    "~",
    "≃",
    "|",
)


def _sanitize_lean_ident(name: str) -> str:
    """Sanitize identifier for use as a Lean 4 theorem/axiom identifier."""
    clean = re.sub(r"^conj_", "", str(name))
    clean = re.sub(r"[^a-zA-Z0-9_]+", "_", clean).strip("_").lower()
    if clean and clean[0].isdigit():
        clean = f"lem_{clean}"
    return clean or "aux_lemma"


def _extract_invariants_from_conjecture(conjecture: Any) -> List[str]:
    """Extract invariant names involved in a conjecture AST or statement string."""
    invs: Set[str] = set()

    def _walk(node: Any) -> None:
        if node is None:
            return
        if hasattr(node, "name") and isinstance(node.name, str):
            invs.add(node.name)
        if hasattr(node, "left"):
            _walk(node.left)
        if hasattr(node, "right"):
            _walk(node.right)
        if hasattr(node, "operand"):
            _walk(node.operand)

    if hasattr(conjecture, "lhs_expr") and hasattr(conjecture, "rhs_expr"):
        _walk(conjecture.lhs_expr)
        _walk(conjecture.rhs_expr)
    else:
        stmt = str(getattr(conjecture, "statement", str(conjecture)))
        known_tokens = [
            "chromatic_number",
            "spectral_radius",
            "max_degree",
            "min_degree",
            "average_degree",
            "independence_number",
            "clique_number",
            "order",
            "size",
            "algebraic_connectivity",
            "laplacian_spectral_radius",
            "signless_laplacian_spectral_radius",
            "estrada_index",
            "graph_energy",
            "diameter",
            "radius",
            "girth",
            "triangle_count",
            "density",
            "spectral_spread",
            "chi",
            "delta",
            "alpha",
            "omega",
        ]
        stmt_lower = stmt.lower()
        for tok in known_tokens:
            if tok in stmt_lower:
                canonical = {
                    "chi": "chromatic_number",
                    "delta": "max_degree",
                    "alpha": "independence_number",
                    "omega": "clique_number",
                }.get(tok, tok)
                invs.add(canonical)

    return sorted(list(invs))


class FlywheelLemma(BaseModel):
    """Specification of an active lemma registered in the Lemma Flywheel."""

    model_config = ConfigDict(extra="allow", arbitrary_types_allowed=True)

    lemma_id: str
    statement: str
    lean_name: str
    lean_prop: str
    guard: Optional[str] = None
    tactic: str
    invariants: List[str] = Field(default_factory=list)
    timestamp: float = Field(default_factory=time.time)
    receipt_path: Optional[str] = None
    is_machine_checked: bool = True
    multi_hop_depth: int = 1
    call_count: int = 0

    def to_dict(self) -> Dict[str, Any]:
        return {
            "lemma_id": self.lemma_id,
            "receipt_path": self.receipt_path,
            "statement": self.statement,
            "lean_name": self.lean_name,
            "lean_prop": self.lean_prop,
            "guard": self.guard,
            "tactic": self.tactic,
            "invariants": self.invariants,
            "timestamp": self.timestamp,
            "is_machine_checked": self.is_machine_checked,
            "multi_hop_depth": self.multi_hop_depth,
            "call_count": self.call_count,
        }


class FlywheelFeedback:
    """Manages closed-loop heuristic feedback into hypothesis formulation."""

    def __init__(self) -> None:
        self.invariant_fertility: Dict[str, float] = {}
        self.pair_fertility: Dict[Tuple[str, str], float] = {}
        self.boundary_graphs: List[Dict[str, Any]] = []

    def record_sieve_survival(self, conjecture: Any) -> None:
        """Surviving empirical sieve increases fertility of its invariants."""
        invs = _extract_invariants_from_conjecture(conjecture)
        for inv in invs:
            self.invariant_fertility[inv] = self.invariant_fertility.get(inv, 1.0) + 1.0
        if len(invs) >= 2:
            pair = tuple(sorted(invs[:2]))  # type: ignore
            self.pair_fertility[pair] = self.pair_fertility.get(pair, 1.0) + 1.5

    def record_refutation(self, conjecture: Any, certificate: Any = None) -> None:
        """Record falsifying counterexample graph as a critical boundary graph."""
        if certificate is not None:
            order = getattr(certificate, "graph_order", None)
            size = getattr(certificate, "graph_size", None)
            ident = getattr(certificate, "graph_id", None) or f"n{order}_m{size}"
            self.boundary_graphs.append({
                "id": ident,
                "order": order,
                "size": size,
                "role": "counterexample",
                "statement": getattr(conjecture, "statement", str(conjecture)),
                "timestamp": time.time(),
            })
            if len(self.boundary_graphs) > 100:
                self.boundary_graphs = self.boundary_graphs[-100:]

    def record_lean_certification(self, conjecture: Any, tactic: str) -> None:
        """Formal machine certification provides the highest fertility boost."""
        invs = _extract_invariants_from_conjecture(conjecture)
        for inv in invs:
            self.invariant_fertility[inv] = self.invariant_fertility.get(inv, 1.0) + 5.0
        if len(invs) >= 2:
            pair = tuple(sorted(invs[:2]))  # type: ignore
            self.pair_fertility[pair] = self.pair_fertility.get(pair, 1.0) + 7.0

    def get_fertile_invariants(self, top_k: int = 6) -> List[Tuple[str, float]]:
        """Return the top fertile invariants sorted by fertility score."""
        items = sorted(self.invariant_fertility.items(), key=lambda kv: kv[1], reverse=True)
        return items[:top_k]

    def sample_pair(
        self,
        all_invariants: List[str],
        recent_pairs: Set[Tuple[str, str]],
        p_fertile: float = 0.65,
    ) -> Tuple[str, str]:
        """Sample an invariant pair, biasing toward fertile invariants while avoiding recency."""
        import random

        if random.random() < p_fertile and self.invariant_fertility:
            fertile_candidates = [inv for inv, score in self.get_fertile_invariants(8) if inv in all_invariants]
            if len(fertile_candidates) >= 2:
                for _ in range(15):
                    # Pick 1 fertile, 1 candidate (fertile or exploratory)
                    inv1 = random.choice(fertile_candidates)
                    inv2 = random.choice(all_invariants)
                    if inv1 != inv2 and (inv1, inv2) not in recent_pairs and (inv2, inv1) not in recent_pairs:
                        return (inv1, inv2)

        # Fallback exploratory sampling
        for _ in range(20):
            p = tuple(random.sample(all_invariants, 2))
            if p not in recent_pairs and (p[1], p[0]) not in recent_pairs:
                return p  # type: ignore
        # Final fallback
        pair_fallback = random.sample(all_invariants, 2)
        return (pair_fallback[0], pair_fallback[1])

    def sample_triad(
        self,
        all_invariants: List[str],
        guards: List[Optional[str]],
        p_fertile: float = 0.65,
    ) -> Tuple[str, List[str], Optional[str]]:
        """Sample an invariant triad and guard, biasing toward fertile invariants."""
        import random

        fertile_candidates = [inv for inv, score in self.get_fertile_invariants(8) if inv in all_invariants]
        if random.random() < p_fertile and len(fertile_candidates) >= 2:
            target_y = random.choice(fertile_candidates)
            rem = [inv for inv in all_invariants if inv != target_y]
            xs = random.sample(rem, 2)
            guard = random.choice(guards)
            return (target_y, xs, guard)

        triad = random.sample(all_invariants, 3)
        guard = random.choice(guards)
        return (triad[0], [triad[1], triad[2]], guard)

    def to_dict(self) -> Dict[str, Any]:
        return {
            "invariant_fertility": dict(self.invariant_fertility),
            "pair_fertility": {f"{k[0]}--{k[1]}": v for k, v in self.pair_fertility.items()},
            "boundary_graphs_count": len(self.boundary_graphs),
            "top_fertile_invariants": self.get_fertile_invariants(10),
        }


class LemmaFlywheel:
    """Manages active Lean 4 lemmas, environment bridges, and multi-step tactic generation."""

    SECTION_BEGIN = "-- >>> LEMMA_FLYWHEEL_BEGIN >>>\n-- Dynamic certified lemmas automatically registered by Autonomous Discovery Flywheel"
    SECTION_END = "-- <<< LEMMA_FLYWHEEL_END <<<"

    def __init__(
        self,
        workspace_dir: Optional[Union[str, Path]] = None,
        state_file: Optional[Union[str, Path]] = None,
        mathlib_path: Optional[Union[str, Path]] = None,
        storage_path: Optional[Union[str, Path]] = None,
    ) -> None:
        repo_root = Path(__file__).resolve().parent.parent.parent
        self.workspace_dir = Path(workspace_dir) if workspace_dir else repo_root / "certified_lean"
        self.mathlib_path = Path(mathlib_path) if mathlib_path else self.workspace_dir / "Mathlib.lean"
        actual_state_file = state_file or storage_path
        self.state_file = Path(actual_state_file) if actual_state_file else repo_root / "research_outputs" / "flywheel_lemmas.json"

        self.lemmas: Dict[str, FlywheelLemma] = {}
        self.feedback = FlywheelFeedback()
        self.load()

    def load(self) -> None:
        """Load registered lemmas from state JSON if available."""
        if self.state_file.exists():
            try:
                data = json.loads(self.state_file.read_text(encoding="utf-8"))
                for item in data.get("lemmas", []):
                    lem = FlywheelLemma(**item)
                    from autonomous_math.research_state import validate_receipt
                    receipt, _ = validate_receipt(item.get("receipt_path", ""), lem.lemma_id)
                    if receipt:
                        self.lemmas[lem.lemma_id] = lem
                fb_data = data.get("feedback", {})
                self.feedback.invariant_fertility = fb_data.get("invariant_fertility", {})
                self.feedback.boundary_graphs = fb_data.get("boundary_graphs", [])
            except Exception as e:
                logger.debug(f"Could not load flywheel state: {e}")

    def save(self) -> None:
        from autonomous_math.research_state import atomic_save_json
        atomic_save_json({"total_active_lemmas": len(self.lemmas), "timestamp": time.time(),
            "lemmas": [lem.to_dict() for lem in self.lemmas.values()],
            "feedback": {"invariant_fertility": self.feedback.invariant_fertility,
                         "boundary_graphs": self.feedback.boundary_graphs[-50:]}}, self.state_file)

    def _format_conjecture_to_lean(self, conjecture: Any) -> Tuple[str, Optional[str]]:
        """Extract Lean proposition and guard string for a given conjecture."""
        stmt = getattr(conjecture, "statement", str(conjecture))
        guard_obj = getattr(conjecture, "guard_predicate", None)
        guard_lean = None

        if guard_obj:
            if hasattr(guard_obj, "to_lean"):
                guard_lean = guard_obj.to_lean()
            elif isinstance(guard_obj, str):
                g_str = guard_obj.lower().strip()
                if "triangle" in g_str:
                    guard_lean = "G.CliqueFree 3"
                elif "bipartite" in g_str:
                    guard_lean = "G.Colorable 2"
                elif "connected" in g_str:
                    guard_lean = "G.Connected"
                elif "tree" in g_str:
                    guard_lean = "G.IsTree"
                else:
                    guard_lean = f"G.{guard_obj}"

        # If conjecture is a string with direct Lean code or theorem declaration:
        if isinstance(conjecture, str):
            stmt_clean = conjecture.strip()
            if ":=" in stmt_clean and "theorem" in stmt_clean:
                prop_m = re.search(
                    r"theorem\s+[a-zA-Z0-9_]+[^{:]*(?:\{[^}]*\})*(?:\[[^\]]*\])*(?:\([^)]*\))*\s*:\s*(.*?)\s*:=\s*by",
                    stmt_clean,
                    re.DOTALL,
                )
                if prop_m:
                    stmt_clean = prop_m.group(1).strip()
            if (any(marker in stmt_clean for marker in ["(G.", "Fintype", "SimpleGraph", "Real."])) and "==>" not in stmt_clean:
                if any(op in stmt_clean for op in RECOGNIZED_RELATION_OPERATORS):
                    if "→" in stmt_clean:
                        parts = stmt_clean.split("→", 1)
                        return (stmt_clean, parts[0].strip())
                    return (stmt_clean, None)

        if hasattr(conjecture, "lhs_expr") and hasattr(conjecture, "rhs_expr") and hasattr(conjecture, "rel"):
            rel_sym = {
                "<=": "≤",
                ">=": "≥",
                "==": "=",
                "<": "<",
                ">": ">",
                "≈": "≈",
                "≡": "≡",
                "∣": "∣",
                "|": "∣",
                "~": "~",
                "≃": "≃",
            }.get(conjecture.rel, str(conjecture.rel) if str(conjecture.rel) in RECOGNIZED_RELATION_OPERATORS else "≤")
            core_stmt = f"{conjecture.lhs_expr.to_lean()} {rel_sym} {conjecture.rhs_expr.to_lean()}"
        else:
            core_stmt = _format_statement_fallback(stmt)
            if "→" in core_stmt:
                parts = core_stmt.split("→", 1)
                guard_lean = parts[0].strip()
                core_stmt = parts[1].strip()

        # Check known canonical bounds if core_stmt is just a bare identifier without relations
        if not any(op in core_stmt for op in RECOGNIZED_RELATION_OPERATORS):
            canonical_lookup = {
                "signless_laplacian_avg_deg_lower": "(G.signlessLaplacianRadius : ℝ) ≥ (averageDegree G)",
                "cvetkovic_signless_bound": "(G.signlessLaplacianRadius : ℝ) ≤ 2 * (G.maxDegree : ℝ)",
                "collatz_sinogowitz_bound": "(G.spectralRadius : ℝ) ≤ (G.maxDegree : ℝ)",
                "radius_le_diameter": "(G.radius : ℝ) ≤ (G.diameter : ℝ)",
                "diameter_le_two_radius": "G.Connected → (G.diameter : ℝ) ≤ 2 * (G.radius : ℝ)",
                "gutman_energy_size_bound": "(G.energy : ℝ) ≤ 2 * (G.edgeFinset.card : ℝ)",
                "estrada_ge_energy": "(G.estradaIndex : ℝ) ≥ (G.energy : ℝ)",
                "clique_chromatic_lower_bound": "(G.chromaticNumber : ℝ) ≥ (G.cliqueNum : ℝ)",
                "cliqueNum_le_chromaticNumber": "(G.cliqueNum : ℝ) ≤ (G.chromaticNumber : ℝ)",
                "ediam_le_two_mul_radius": "G.Connected → (G.diam : ℝ) ≤ 2 * (G.radius : ℝ)",
            }
            clean_ident = re.sub(r"^conj_", "", stmt).strip()
            if clean_ident in canonical_lookup:
                lookup_val = canonical_lookup[clean_ident]
                if "→" in lookup_val:
                    parts = lookup_val.split("→", 1)
                    return (lookup_val, parts[0].strip())
                return (lookup_val, None)

        if guard_lean and guard_lean != "True":
            full_prop = f"{guard_lean} → {core_stmt}"
        else:
            full_prop = core_stmt

        return (full_prop, guard_lean)

    def register_lemma(self, conjecture, tactic, conjecture_id=None, theorem_name=None,
                       is_machine_checked=True, receipt_path=None) -> FlywheelLemma:
        from autonomous_math.research_state import validate_receipt
        cid = conjecture_id or getattr(conjecture, "id", None)
        receipt, error = validate_receipt(receipt_path or "", cid)
        if not is_machine_checked or not receipt:
            raise ValueError(f"Cannot register an unchecked lemma: {error}")
        if not hasattr(conjecture, "to_dict") or receipt.get("conjecture") != conjecture.to_dict():
            raise ValueError("Lemma does not match the receipt's structured conjecture")
        from autonomous_math.prover.trusted_lean import render_challenge, render_guard
        source, _ = render_challenge(conjecture)
        header = source.split(":= by", 1)[0]
        prop = header.rsplit(" :\n    ", 1)[1].strip()
        guard = render_guard(conjecture.guard_predicate)
        lemma = FlywheelLemma(lemma_id=cid, statement=getattr(conjecture, "statement", str(conjecture)),
            lean_name=receipt["theorem_name"], lean_prop=prop, guard=guard, tactic=receipt["tactic"],
            invariants=_extract_invariants_from_conjecture(conjecture), timestamp=time.time(),
            is_machine_checked=True, receipt_path=str(receipt_path))
        self.lemmas[cid] = lemma
        self.feedback.record_lean_certification(conjecture, tactic)
        self.save()
        return lemma

    def _sync_mathlib_bridge(self) -> None:
        """Proof reuse is performed by importing checked bodies, never injecting axioms."""
        return None

    def generate_flywheel_tactics(self, lean_code, conjecture=None):
        from autonomous_math.prover.lean_prover import LeanProofScript
        from autonomous_math.research_state import validate_receipt
        from autonomous_math.prover.trusted_lean import render_guard
        target_guard = render_guard(conjecture.guard_predicate) if conjecture is not None else None
        scripts = []
        for lem in self.lemmas.values():
            receipt, _ = validate_receipt(getattr(lem, "receipt_path", ""), lem.lemma_id)
            if not receipt:
                continue
            # A conditional theorem needs the same checked premise at the target.
            if lem.guard and lem.guard != target_guard:
                continue
            argument = " h_guard" if lem.guard else ""
            scripts.append(LeanProofScript(name=f"reuse_{lem.lemma_id}",
                tactic_code=f"exact {lem.lean_name} G{argument}", category="verified_reuse"))
        return scripts

    def clear(self) -> None:
        """Clear all registered lemmas and reset Mathlib.lean environment bridge."""
        self.lemmas.clear()
        self._sync_mathlib_bridge()
        self.save()
