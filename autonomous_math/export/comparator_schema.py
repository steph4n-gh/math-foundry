"""openai/math Lean 4 Comparator Challenge Schema.

Defines Pydantic V2 specification model ComparatorChallengeSpec matching
the benchmark conventions established in math/lean/ComparatorChallenges/.
"""

from __future__ import annotations

import json
from typing import Any, Dict, List, Optional
from pydantic import BaseModel, ConfigDict, Field

DEFAULT_PERMITTED_AXIOMS: List[str] = [
    "propext",
    "Quot.sound",
    "Classical.choice",
]


class ComparatorChallengeSpec(BaseModel):
    """Specification metadata for Lean 4 comparator challenges.

    Adheres strictly to openai/math benchmark format:
    - challenge_module: Module path for the challenge (e.g. 'ComparatorChallenges.GreedyColoring')
    - solution_module: Module path for the solution (e.g. 'OAI.Combinatorics.Coloring.Main')
    - theorem_names: Fully-qualified theorem targets in Lean 4
    - definition_names: Optional definitions exported in challenge
    - permitted_axioms: Standard classical triad allowed for proof verification
    - enable_nanoda: Boolean flag for nanoda checker
    """

    model_config = ConfigDict(extra="ignore")

    challenge_module: str
    solution_module: str
    theorem_names: List[str]
    definition_names: List[str] = Field(default_factory=list)
    permitted_axioms: List[str] = Field(
        default_factory=lambda: list(DEFAULT_PERMITTED_AXIOMS)
    )
    enable_nanoda: bool = False

    def to_dict(self) -> Dict[str, Any]:
        """Convert specification to JSON-serializable dictionary."""
        return self.model_dump()

    def to_json(self, indent: Optional[int] = 2) -> str:
        """Serialize specification to formatted JSON string."""
        return json.dumps(self.to_dict(), indent=indent)

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> ComparatorChallengeSpec:
        """Instantiate specification from dictionary."""
        return cls.model_validate(data)

    @classmethod
    def from_json(cls, json_str: str) -> ComparatorChallengeSpec:
        """Instantiate specification from JSON string."""
        return cls.model_validate_json(json_str)
