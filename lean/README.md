# Lean proof project

This project proves or refutes six complete graph-theoretic targets for Erdős
#612 using Lean 4.33.1 and mathlib v4.33.1.

## Files

- `Erdos612/Definitions.lean`: rational potentials and endpoint identities.
- `Erdos612/GreedyCover.lean`: finite greedy complement-cover argument.
- `Erdos612/BFS.lean`: BFS layers, diameter geodesic, layer sums, and localization.
- `Erdos612/Local.lean`: nonlinear four-layer algebra.
- `Erdos612/GraphLocal.lean`: derives the local inequalities from clique-freeness.
- `Erdos612/Telescoping.lean` and `Main.lean`: finite telescoping and endpoints.
- `Erdos612/GraphTheorems.lean`: exact K₅-free and K₄-free graph bounds.
- `Erdos612/Conjectures.lean`: the actual asymptotic/divisible conjecture definitions.
- `Erdos612Final.lean`: the three positive `answer(True)` targets.
- `K7Counterexample/`: the 71-layer `K₇`-free family refuting original `r=3`
  and amended `k=6`.
- `AmendedK6/`: the 33-layer `K₆`-free family refuting amended `k=5`.
- `Erdos612All.lean`: all six FC-shaped targets and the final axiom audit.

No local inequality, telescoping assertion, or unproved graph property is
assumed by the final targets. The `#print axioms` audit contains no `sorryAx`.

## Build

```bash
lake update
lake exe cache get
lake build
```
