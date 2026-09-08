# Lean4Web editions

The directory contains three standalone files:

- [`Erdos612Lean4Web.lean`](Erdos612Lean4Web.lean): original `r=2` and amended
  `k=3,4`;
- [`Erdos612K7Lean4Web.lean`](Erdos612K7Lean4Web.lean): original `r=3` and
  amended `k=6` counterexamples;
- [`Erdos612AmendedK6Lean4Web.lean`](Erdos612AmendedK6Lean4Web.lean): amended
  `k=5` counterexample.

Together they include:

1. the greedy clique-cover lemma;
2. BFS layers and diameter identities;
3. both local nonlinear four-layer inequalities;
4. telescoping and endpoint algebra;
5. the exact K₅-free and K₄-free graph bounds;
6. the actual original K₅/K₇ and amended K₄/K₅/K₆/K₇ targets;
7. `#check` and `#print axioms` for all six final targets.

The final theorem statements are the complete finite-graph claims. The positive
targets assume only connectedness and clique-freeness; the refutations explicitly
construct and verify the required graph families.

Local verification:

```bash
cd ../lean
lake env lean ../lean4web/Erdos612Lean4Web.lean
lake env lean ../lean4web/Erdos612K7Lean4Web.lean
lake env lean ../lean4web/Erdos612AmendedK6Lean4Web.lean
```
