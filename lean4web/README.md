# Lean4Web edition

[`Erdos612Lean4Web.lean`](Erdos612Lean4Web.lean) is a 1,500-line standalone
version of the complete proof. It includes:

1. the greedy clique-cover lemma;
2. BFS layers and diameter identities;
3. both local nonlinear four-layer inequalities;
4. telescoping and endpoint algebra;
5. the exact K₅-free and K₄-free graph bounds;
6. the actual original K₅ and amended K₄/K₅ targets;
7. `#check` and `#print axioms` for all three final targets.

The final theorem statements assume only connectedness and clique-freeness. They
do not accept a local inequality, BFS sequence, or telescoping result as a hypothesis.

Local verification:

```bash
cd ../lean
lake env lean ../lean4web/Erdos612Lean4Web.lean
```
