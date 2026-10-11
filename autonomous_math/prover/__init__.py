"""Prover-Skeptic Search Engine Package (Milestone 3).

Provides:
- ProofNode, DeductionStep, LemmaDAG (Feature 8)
- AxiomLibrary, AxiomDefinition (Feature 9)
- DeductiveInferenceEngine, LeapValidationResult (Feature 10)
- AdversarialSkeptic (Feature 11)
- ProofResult, ProverSkepticSearch (Feature 12)
"""

from __future__ import annotations

from autonomous_math.prover.dag import (
    DeductionStep,
    LemmaDAG,
    ProofNode,
)
from autonomous_math.prover.axioms import (
    AxiomDefinition,
    AxiomLibrary,
)
from autonomous_math.prover.inference import (
    DeductiveInferenceEngine,
    LeapValidationResult,
)
from autonomous_math.prover.skeptic import (
    AdversarialSkeptic,
)
from autonomous_math.prover.search import (
    ProofResult,
    ProverSkepticSearch,
)
from autonomous_math.prover.lean_prover import (
    LeanProofScript,
    LeanProofSearch,
    LeanToolchain,
    LeanVerificationResult,
)

__all__ = [
    "ProofNode",
    "DeductionStep",
    "LemmaDAG",
    "AxiomLibrary",
    "AxiomDefinition",
    "DeductiveInferenceEngine",
    "LeapValidationResult",
    "AdversarialSkeptic",
    "ProofResult",
    "ProverSkepticSearch",
    "LeanProofScript",
    "LeanProofSearch",
    "LeanToolchain",
    "LeanVerificationResult",
]
