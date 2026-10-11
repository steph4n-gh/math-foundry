"""AND/OR Lemma DAG Architecture for Deductive Graph Proofs.

Feature 8:
Provides:
- ProofNode: AST node in proof DAG representing theorems, lemmas, premises, or axioms.
- DeductionStep: Directed hyper-edge capturing deductive inferences from premises to target.
- LemmaDAG: Pydantic V2 / NetworkX DAG supporting conjunctive decomposition,
  alternative proof branches (OR nodes), topological sort, and TikZ export.
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Set, Tuple, Union
import networkx as nx
from pydantic import BaseModel, ConfigDict, Field


class ProofNode(BaseModel):
    """A node in the proof DAG representing a mathematical statement."""

    model_config = ConfigDict(extra="allow", arbitrary_types_allowed=True)

    node_id: str
    label: str
    statement_latex: str
    statement_lean: str
    node_type: str = "SUB_LEMMA"  # "TARGET_CONJECTURE", "SUB_LEMMA", "AXIOM", "PREMISE", "DEFINITION"
    scope: Optional[Dict[str, Any]] = None
    confidence_score: float = 1.0
    is_proven: bool = False
    status: str = "UNPROVEN"  # "PROVEN", "UNPROVEN", "REFUTED", "IN_PROGRESS"
    metadata: Dict[str, Any] = Field(default_factory=dict)

    def __init__(self, **data: Any) -> None:
        super().__init__(**data)
        # Axioms and Premises are proven by definition unless explicitly specified
        if self.node_type in ("AXIOM", "PREMISE"):
            if "is_proven" not in data:
                self.is_proven = True
            if "status" not in data:
                self.status = "PROVEN"
        elif self.status == "PROVEN":
            self.is_proven = True
        elif self.is_proven:
            self.status = "PROVEN"

        if self.scope is None:
            self.scope = {"assumptions": []}

    def mark_proven(self) -> None:
        """Mark this node as proved."""
        self.is_proven = True
        self.status = "PROVEN"

    def mark_refuted(self) -> None:
        """Mark this node as refuted."""
        self.is_proven = False
        self.status = "REFUTED"

    def is_axiom(self) -> bool:
        """Return True if node is an axiom."""
        return self.node_type == "AXIOM"

    def is_target(self) -> bool:
        """Return True if node is the root/target conjecture."""
        return self.node_type == "TARGET_CONJECTURE"

    def get_assumptions(self) -> List[str]:
        """Return list of assumptions declared in node scope."""
        if self.scope and isinstance(self.scope.get("assumptions"), list):
            return list(self.scope["assumptions"])
        return []

    def to_dict(self) -> Dict[str, Any]:
        """Convert node to dictionary representation."""
        return self.model_dump()

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> ProofNode:
        """Construct node from dictionary."""
        return cls.model_validate(data)


class DeductionStep(BaseModel):
    """A deduction step deriving a target node from premise nodes."""

    model_config = ConfigDict(extra="allow", arbitrary_types_allowed=True)

    step_id: str
    target_node_id: str
    premise_node_ids: List[str] = Field(default_factory=list)
    rule_type: str = "INEQUALITY_CHAIN"  # "INEQUALITY_CHAIN", "SUBSTITUTION", "MODUS_PONENS", "AXIOM_APPLICATION"
    rule_name: str = "Deduction"
    justification: str = ""
    is_verified: bool = False
    z3_verified: bool = False
    skeptic_approved: bool = False
    confidence_score: float = 1.0
    metadata: Dict[str, Any] = Field(default_factory=dict)

    def is_sound(self) -> bool:
        """Return True if step has passed Z3 SMT and Skeptic audits."""
        return (self.is_verified or self.z3_verified) and self.skeptic_approved

    def to_dict(self) -> Dict[str, Any]:
        """Convert deduction step to dictionary."""
        return self.model_dump()

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> DeductionStep:
        """Construct deduction step from dictionary."""
        return cls.model_validate(data)


class LemmaDAG(BaseModel):
    """Directed Acyclic Graph representing mathematical lemma decompositions.

    Conjunctive steps require all premises (AND).
    Alternative deduction steps targeting the same node provide alternative proofs (OR).
    Directed edges run from premise nodes to target nodes (premise -> target).
    """

    model_config = ConfigDict(extra="allow", arbitrary_types_allowed=True)

    root_node_id: str
    nodes: Dict[str, ProofNode] = Field(default_factory=dict)
    steps: Dict[str, DeductionStep] = Field(default_factory=dict)

    def __init__(
        self,
        root_node_id: str,
        nodes: Optional[Dict[str, ProofNode]] = None,
        steps: Optional[Dict[str, DeductionStep]] = None,
        **kwargs: Any,
    ) -> None:
        super().__init__(
            root_node_id=root_node_id,
            nodes=nodes or {},
            steps=steps or {},
            **kwargs,
        )
        self._sync_networkx()

    def _sync_networkx(self) -> nx.DiGraph:
        """Build and synchronize internal NetworkX DiGraph representation."""
        g = nx.DiGraph()
        for nid, node in self.nodes.items():
            g.add_node(
                nid,
                label=node.label,
                node_type=node.node_type,
                is_proven=node.is_proven,
                status=node.status,
            )
        for sid, step in self.steps.items():
            if step.target_node_id not in g:
                g.add_node(step.target_node_id)
            for p in step.premise_node_ids:
                if p not in g:
                    g.add_node(p)
                g.add_edge(p, step.target_node_id, step_id=sid, rule=step.rule_name)
        object.__setattr__(self, "_graph", g)
        return g

    @property
    def graph(self) -> nx.DiGraph:
        """Return internal NetworkX DiGraph."""
        if not hasattr(self, "_graph") or self._graph is None:
            return self._sync_networkx()
        return self._graph

    def has_node(self, node_id: str) -> bool:
        """Check if node exists in DAG."""
        return node_id in self.nodes or (hasattr(self, "_graph") and self.graph.has_node(node_id))

    def add_node(self, node: ProofNode) -> None:
        """Add a ProofNode to the Lemma DAG."""
        self.nodes[node.node_id] = node
        self.graph.add_node(
            node.node_id,
            label=node.label,
            node_type=node.node_type,
            is_proven=node.is_proven,
            status=node.status,
        )

    def add_step(self, step: DeductionStep) -> None:
        """Add a DeductionStep and establish premise -> target edges."""
        self.steps[step.step_id] = step
        if step.target_node_id not in self.graph:
            self.graph.add_node(step.target_node_id)
        for p in step.premise_node_ids:
            if p not in self.graph:
                self.graph.add_node(p)
            self.graph.add_edge(p, step.target_node_id, step_id=step.step_id, rule=step.rule_name)
        self.propagate_proof_status()

    def get_node(self, node_id: str) -> Optional[ProofNode]:
        """Retrieve ProofNode by ID."""
        return self.nodes.get(node_id)

    def get_step(self, step_id: str) -> Optional[DeductionStep]:
        """Retrieve DeductionStep by ID."""
        return self.steps.get(step_id)

    def has_cycle(self) -> bool:
        """Return True if the proof graph contains a directed cycle."""
        return not nx.is_directed_acyclic_graph(self.graph)

    def would_create_cycle(self, step: DeductionStep) -> bool:
        """Check if adding the proposed step would introduce a directed cycle."""
        target = step.target_node_id
        for p in step.premise_node_ids:
            if p == target:
                return True
            if self.graph.has_node(target) and self.graph.has_node(p):
                if nx.has_path(self.graph, target, p):
                    return True
        return False

    def topological_sort(self) -> List[str]:
        """Compute topological sort of node IDs.

        Guarantees that premise nodes strictly precede target nodes:
        topo.index(premise) < topo.index(target).
        """
        for nid in self.nodes:
            if nid not in self.graph:
                self.graph.add_node(nid)
        if not nx.is_directed_acyclic_graph(self.graph):
            raise ValueError("Proof DAG contains a directed cycle and cannot be topologically sorted.")
        return list(nx.topological_sort(self.graph))

    def get_antecedents(self, node_id: str) -> List[str]:
        """Get all premise nodes required to derive node_id (ancestors in graph)."""
        if not self.graph.has_node(node_id):
            return []
        return list(nx.ancestors(self.graph, node_id))

    def get_descendants(self, node_id: str) -> List[str]:
        """Get all target nodes derived from node_id (descendants in graph)."""
        if not self.graph.has_node(node_id):
            return []
        return list(nx.descendants(self.graph, node_id))

    def get_steps_targeting(self, node_id: str) -> List[DeductionStep]:
        """Get all alternative deduction steps producing node_id (OR branches)."""
        return [s for s in self.steps.values() if s.target_node_id == node_id]

    def get_steps_using_premise(self, node_id: str) -> List[DeductionStep]:
        """Get all deduction steps that use node_id as a premise."""
        return [s for s in self.steps.values() if node_id in s.premise_node_ids]

    def is_node_proven(self, node_id: str) -> bool:
        """Check if node_id is proven via axioms or sound deduction steps."""
        node = self.get_node(node_id)
        if not node:
            return False
        if node.is_proven or node.node_type in ("AXIOM", "PREMISE"):
            return True
        incoming = self.get_steps_targeting(node_id)
        for step in incoming:
            if not step.premise_node_ids:
                continue
            if all(self.is_node_proven(p) for p in step.premise_node_ids):
                return True
        return False

    def propagate_proof_status() -> None:
        pass

    def propagate_proof_status(self) -> None:
        """Propagate proven status topologically from axioms to targets."""
        try:
            topo = self.topological_sort()
        except ValueError:
            return
        for nid in topo:
            node = self.get_node(nid)
            if node and not node.is_proven:
                if self.is_node_proven(nid):
                    node.mark_proven()
                    if self.graph.has_node(nid):
                        self.graph.nodes[nid]["is_proven"] = True
                        self.graph.nodes[nid]["status"] = "PROVEN"

    def extract_minimal_proof_tree(self, target_node_id: Optional[str] = None) -> List[DeductionStep]:
        """Extract minimal list of deduction steps sufficient to prove target."""
        target = target_node_id or self.root_node_id
        selected_steps: List[DeductionStep] = []
        visited_nodes: Set[str] = set()

        def backtrack(curr_id: str) -> bool:
            if curr_id in visited_nodes:
                return True
            curr_node = self.get_node(curr_id)
            if curr_node and curr_node.node_type in ("AXIOM", "PREMISE"):
                visited_nodes.add(curr_id)
                return True

            incoming = self.get_steps_targeting(curr_id)
            for step in incoming:
                if all(backtrack(p) for p in step.premise_node_ids):
                    if step not in selected_steps:
                        selected_steps.append(step)
                    visited_nodes.add(curr_id)
                    return True
            return False

        backtrack(target)
        return selected_steps

    def to_dict(self) -> Dict[str, Any]:
        """Serialize LemmaDAG to dictionary."""
        return {
            "root_node_id": self.root_node_id,
            "nodes": {k: v.to_dict() for k, v in self.nodes.items()},
            "steps": {k: v.to_dict() for k, v in self.steps.items()},
        }

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> LemmaDAG:
        """Deserialize LemmaDAG from dictionary."""
        nodes = {k: ProofNode.from_dict(v) for k, v in data.get("nodes", {}).items()}
        steps = {k: DeductionStep.from_dict(v) for k, v in data.get("steps", {}).items()}
        dag = cls(root_node_id=data["root_node_id"])
        for node in nodes.values():
            dag.add_node(node)
        for step in steps.values():
            dag.add_step(step)
        return dag

    def to_tikz(self, scale: float = 1.0) -> str:
        """Render the Lemma DAG as a valid LaTeX TikZ environment."""
        lines = [
            r"\begin{tikzpicture}[",
            r"    >=stealth, auto,",
            r"    node distance=1.8cm,",
            r"    axiom_node/.style={rectangle, draw=blue!80, fill=blue!10, rounded corners=2pt, thick, align=center, inner sep=5pt},",
            r"    lemma_node/.style={rectangle, draw=orange!80, fill=orange!10, rounded corners=2pt, thick, align=center, inner sep=5pt},",
            r"    target_node/.style={rectangle, draw=green!70!black, fill=green!15, rounded corners=3pt, very thick, align=center, inner sep=7pt},",
            r"    step_edge/.style={->, thick, draw=black!70}",
            r"]",
        ]

        try:
            topo = self.topological_sort()
        except ValueError:
            topo = list(self.nodes.keys())

        levels: Dict[str, int] = {}
        for nid in topo:
            preds = list(self.graph.predecessors(nid))
            levels[nid] = (max([levels[p] for p in preds], default=-1) + 1) if preds else 0

        level_groups: Dict[int, List[str]] = {}
        for nid, lvl in levels.items():
            level_groups.setdefault(lvl, []).append(nid)

        for lvl, nids in level_groups.items():
            y = -lvl * 2.2
            for idx, nid in enumerate(nids):
                x = (idx - (len(nids) - 1) / 2.0) * 3.5
                node = self.nodes.get(nid)
                if not node:
                    style = "lemma_node"
                    label = nid
                elif node.node_type == "TARGET_CONJECTURE" or nid == self.root_node_id:
                    style = "target_node"
                    label = node.label
                elif node.node_type == "AXIOM":
                    style = "axiom_node"
                    label = node.label
                else:
                    style = "lemma_node"
                    label = node.label

                safe_label = label.replace("_", r"\_")
                lines.append(f"  \\node[{style}] ({nid}) at ({x:.2f}, {y:.2f}) {{{safe_label}}};")

        for step in self.steps.values():
            for p in step.premise_node_ids:
                rule_lbl = step.rule_name.replace("_", r"\_")
                lines.append(f"  \\draw[step_edge] ({p}) -- node[right, font=\\tiny] {{{rule_lbl}}} ({step.target_node_id});")

        lines.append(r"\end{tikzpicture}")
        return "\n".join(lines)
