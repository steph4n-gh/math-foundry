## Apply Occam's Razor

- Prefer the simplest design and implementation that fully satisfies the current, demonstrated requirements.
- Do not add abstractions, layers, configuration, extension points, dependencies, or infrastructure for hypothetical future needs. Introduce them only when concrete requirements or repeated patterns justify their cost.
- Before adding code, consider whether the goal can be met by deleting, consolidating, or reusing existing code.
- When multiple approaches are correct, choose the one with fewer concepts, moving parts, and maintenance obligations, unless evidence shows that a more complex approach is necessary.
- Treat patterns and principles as tools, not goals. Do not apply SOLID, design patterns, or architectural boundaries in ways that make a small solution more complicated than the problem requires.

## Mathematical evidence

- Keep the pinned genuine Mathlib workspace and exact structured theorem checks.
- A finite empirical survivor is a candidate. A universal theorem requires its own valid Lean receipt.
- Preserve refutations, timeouts, and negative benchmark results. Claims must match the checks actually performed.
- Use a separate output directory for experiments; the live runner owns its checkpoint directory.
