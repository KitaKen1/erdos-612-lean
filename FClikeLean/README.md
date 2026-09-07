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
The three project targets are proved in the sibling `lean/` project and in the
standalone `lean4web/Erdos612Lean4Web.lean` file using the same propositions.
Other literature-settled entries remain statement-only here.

For the main multi-part problem, `parts.i` is `research solved` and `parts.ii` is
`research open`, matching the current official OPEN status of Erdős #612. The
fixed high-`r` counterexample ranges are recorded separately as solved variants.

The exact finite bounds, greedy covering lemma, BFS facts, local inequalities,
telescoping lemma, and endpoint algebra are proof-engineering details rather
than separate Formal Conjectures targets. They live in `lean/` and `lean4web/`.

## Proof status of this project's targets

The complete graph arguments for `original_k5`, `amended_k3`, and `amended_k4`
are kernel-checked. Their axiom audit contains no `sorryAx`; the remaining
`sorry` declarations in `FClikeLean.lean` belong to the broader statement catalog.

## AI usage disclosure

This statement draft and packaging were developed with assistance from OpenAI
Codex under the direction of KitaKen1 (Kenta Kitamura).
