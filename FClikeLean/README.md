# Prospective Formal Conjectures statement

This directory contains an **unofficial, AI-assisted draft** for
[Erdős Problem #612](https://www.erdosproblems.com/612), written in the style of
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures).

It is not an official Formal Conjectures file and has not been submitted, reviewed,
approved, or merged. At the checked upstream revision
`8323e878b83fcd7f4a448256069352a265460d75`, there is no
`FormalConjectures/ErdosProblems/612.lean`; the problem is represented by open
[issue #828](https://github.com/google-deepmind/formal-conjectures/issues/828).

## Statement choices

`FClikeLean.lean` separates the material into named targets:

- `erdos_612.parts.i`: the original even-clique clause;
- `erdos_612.parts.ii`: the original odd-clique clause;
- `erdos_612.variants.original_k3` through `.original_k7`, plus
  `.original_k_ge8`: fixed-clique variants of the original conjecture;
- `erdos_612.variants.czabarka_singgih_szekely`: the amended conjecture for all `k`;
- `erdos_612.variants.amended_k3` through `.amended_k6`, plus
  `.amended_k_ge7`: fixed-clique variants of the amended conjecture;

The `O(1)` term is represented by an existential real constant outside the graph
quantifiers. The coefficient may depend on the fixed parameter `r` or `k`, exactly
as in the mathematical statement.

The `category research solved/open` attribute records the mathematical research
status, not whether a proof term is embedded in this submission-style catalog.
The six project targets are proved or refuted in the sibling `lean/` project
and in the three standalone files under `lean4web/`, using the same
propositions. Other literature-settled entries remain statement-only here.

For the main multi-part problem, both universal clauses are now recorded as
`research solved` with `answer(False)`: the even clause was already refuted in
the literature, and the new `r = 3` counterexample refutes the odd clause.

The exact finite bounds, greedy covering lemma, BFS facts, local inequalities,
telescoping lemma, and endpoint algebra are proof-engineering details rather
than separate Formal Conjectures targets. They live in `lean/` and `lean4web/`.

## Proof status of this project's targets

The complete graph arguments for `original_k5`, `amended_k3`, `amended_k4`,
`original_k7`, `amended_k5`, and `amended_k6` are kernel-checked. Their axiom
audit contains no `sorryAx`; the `sorry` declarations in `FClikeLean.lean`
belong to the submission-style statement catalog.

## AI usage disclosure

This statement draft and packaging were developed with assistance from OpenAI
Codex, Astra, and ChatGPT under the direction of KitaKen1 (Kenta Kitamura).
