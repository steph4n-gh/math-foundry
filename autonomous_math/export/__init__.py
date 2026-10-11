"""Autonomous Math Discovery Pipeline: Export and Validation Module.

Provides:
- LatexPreprintGenerator: Publication-grade academic LaTeX manuscript generation.
- LaTeXPreprintGenerator: Parity alias for LatexPreprintGenerator.
- LeanComparatorGenerator: Lean 4 Mathlib scaffolding & openai/math comparator challenges.
- Lean4ChallengeGenerator: Parity alias for LeanComparatorGenerator.
- ChallengeArtifacts: Container tuple for generated challenge files.
- ComparatorChallengeSpec: Pydantic V2 schema for comparator JSON specifications.
- DEFAULT_PERMITTED_AXIOMS: Classical axioms triad constant.
- ArtifactValidator: Pure Python syntax and completeness validator for LaTeX & Lean.
- OutputSyntaxValidator: Compatibility alias for ArtifactValidator.
- ArtifactValidationResult: Validation outcome model with tuple unpacking support.
"""

from autonomous_math.export.comparator_schema import (
    DEFAULT_PERMITTED_AXIOMS,
    ComparatorChallengeSpec,
)
from autonomous_math.export.latex_generator import (
    LatexPreprintGenerator,
    LaTeXPreprintGenerator,
)
from autonomous_math.export.lean_generator import (
    ChallengeArtifacts,
    Lean4ChallengeGenerator,
    LeanComparatorGenerator,
)
from autonomous_math.export.validator import (
    ArtifactValidationResult,
    ArtifactValidator,
    OutputSyntaxValidator,
)

__all__ = [
    "DEFAULT_PERMITTED_AXIOMS",
    "ComparatorChallengeSpec",
    "LatexPreprintGenerator",
    "LaTeXPreprintGenerator",
    "LeanComparatorGenerator",
    "Lean4ChallengeGenerator",
    "ChallengeArtifacts",
    "ArtifactValidationResult",
    "ArtifactValidator",
    "OutputSyntaxValidator",
]
