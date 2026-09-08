# Erdős Problem #612 in Lean

This repository has seven contributions: one statement catalog, three positive
results, and three counterexample results.

1. **Contribution 1 — Prospective Formal Conjectures formalization.**
   [`FClikeLean/FClikeLean.lean`](FClikeLean/FClikeLean.lean) separates the
   original and amended conjectures and their fixed-clique variants.
2. **Contribution 2 — Original K₅ (r=2).** Every connected K₅-free finite graph satisfies
   `2δ(D+1)+4 ≤ 5n`; hence the original K₅ target holds, even without its
   divisibility restriction.
3. **Contribution 3 — Amended K₄ (k=3).** Every connected K₄-free finite graph satisfies
   `3δ(D+1)+6 ≤ 7n`.
4. **Contribution 4 — Amended K₅ (k=4).** This follows from the stronger
   Contribution 2 bound.
5. **Contribution 5 — Original K₇ (r=3).** An explicit periodic family of
   connected K₇-free finite graphs refutes the original fixed-clique target.
6. **Contribution 6 — Amended K₆ (k=5).** A separate explicit 33-layer
   periodic family refutes the amended K₆-free target.
7. **Contribution 7 — Amended K₇ (k=6).** The K₇-free family from Contribution
   5 also refutes the amended K₇-free target.

**Try it in Lean4Web:**

- [Contributions 2–4](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ferdos-612-lean%2Frefs%2Fheads%2Fmain%2Flean4web%2FErdos612Lean4Web.lean)
- [Contributions 5 and 7](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ferdos-612-lean%2Frefs%2Fheads%2Fmain%2Flean4web%2FErdos612K7Lean4Web.lean)
- [Contribution 6](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Ferdos-612-lean%2Frefs%2Fheads%2Fmain%2Flean4web%2FErdos612AmendedK6Lean4Web.lean)

Contributions 2–7 are full finite-graph targets. The positive results are proved
from connectedness and clique-freeness alone. The counterexample results define
the graph families and prove their connectedness, clique-freeness, minimum degree,
order, diameter lower bounds, and unbounded excess over the proposed main terms.

## Formal Conjectures-shaped proved targets

### Contribution 2 — Original K₅ (r=2)

```lean
theorem erdos_612.variants.original_k5 :
    answer(True) ↔ Erdos612.OriginalOddConjectureAt 2
```

### Contribution 3 — Amended K₄ (k=3)

```lean
theorem erdos_612.variants.amended_k3 :
    answer(True) ↔ Erdos612.AmendedConjectureAt 3
```

### Contribution 4 — Amended K₅ (k=4)

```lean
theorem erdos_612.variants.amended_k4 :
    answer(True) ↔ Erdos612.AmendedConjectureAt 4
```

### Contribution 5 — Original K₇ (r=3)

```lean
theorem erdos_612.variants.original_k7 :
    answer(False) ↔ Erdos612.OriginalOddConjectureAt 3
```

### Contribution 6 — Amended K₆ (k=5)

```lean
theorem erdos_612.variants.amended_k5 :
    answer(False) ↔ Erdos612.AmendedConjectureAt 5
```

### Contribution 7 — Amended K₇ (k=6)

```lean
theorem erdos_612.variants.amended_k6 :
    answer(False) ↔ Erdos612.AmendedConjectureAt 6
```

These are the actual graph statements, not algebraic kernels with a local
inequality supplied as a hypothesis. The final `#print axioms` audit reports no
`sorryAx` and no project-specific mathematical axioms.

## Directory layout

| Directory | Contents |
|---|---|
| [`FClikeLean/`](FClikeLean/) | Unofficial FC-style problem and variant catalog |
| [`lean/`](lean/) | Modular proofs and counterexample constructions for all six targets |
| [`lean4web/`](lean4web/) | Three standalone Lean4Web files covering the same six targets |

## Verification

```bash
cd lean
lake update
lake exe cache get
lake build
```

The standalone files can also be checked directly in that environment:

```bash
cd lean
lake env lean ../lean4web/Erdos612Lean4Web.lean
lake env lean ../lean4web/Erdos612K7Lean4Web.lean
lake env lean ../lean4web/Erdos612AmendedK6Lean4Web.lean
```

## Mathmatical Explanation (AI generated)

### Contribution 2 — Original K₅ (r=2)

For four consecutive BFS layer sizes `(a,b,c,d)`, the proof establishes directly
from K₅-freeness the local inequality for

```text
Hδ(a,b,c) = b/2 + c - (c-a)(2δ-b)/(10(a+c)).
```

Telescoping these inequalities gives

```text
5n ≥ 2δ(D+1) + 2(s₀+sD) ≥ 2δ(D+1) + 4.
```

This implies the original coefficient `5/2` with additive constant `C=0`.
The original divisibility condition `5 ∣ δ` is not needed.

### Contribution 3 — Amended K₄ (k=3)

The K₄-free proof uses

```text
Hδ(a,b,c) = b/2 + c - (c-a)(3δ-b)/(14(a+c))
```

and proves the corresponding local inequality from clique-freeness. Telescoping gives

```text
7n ≥ 3δ(D+1) + 3(s₀+sD) ≥ 3δ(D+1) + 6,
```

which implies the amended coefficient `7/3` with `C=0`.

### Contribution 4 — Amended K₅ (k=4)

Dropping `+4` from Contribution 2 gives `2δ(D+1) ≤ 5n`, hence the amended
K₅ coefficient `5/2`, again with `C=0`.

### Contributions 5 and 7 — Original K₇ (r=3) and amended K₇ (k=6)

The 71-layer periodic construction has minimum degree `800`, order
`21296p+960`, and diameter at least `71p+1`. Its excess over the coefficient
`8/3` is at least

```text
p/75 - 11/5,
```

which is unbounded. Since `8 ∣ 800`, the family refutes both the original
`r=3` target and the amended `k=6` target.

### Contribution 6 — Amended K₆ (k=5)

The 33-layer periodic construction has minimum degree `2200`, order
`27923m+8800`, and diameter at least `33m+3`. Its excess over the amended
coefficient `13/5` is at least

```text
m/11000 - 37/5,
```

so no uniform additive constant can make the amended `k=5` bound hold.

## References

- [Erdős Problem #612](https://www.erdosproblems.com/612)
- [Formal Conjectures issue #828](https://github.com/google-deepmind/formal-conjectures/issues/828)
- Erdős, Pach, Pollack, and Tuza, *Radius, diameter, and minimum degree*, JCTB 47 (1989), 73–79.
- Czabarka, Singgih, and Székely, *Counterexamples to a conjecture of Erdős, Pach, Pollack and Tuza*, JCTB 151 (2021), 38–45.
- [Czabarka, Smith, and Székely, *Maximum diameter of 3- and 4-colorable graphs*](https://arxiv.org/abs/2109.13887)
- [Chen–Chen, *Counterexamples to two conjectures on the diameter of clique-free graphs*](https://arxiv.org/abs/2609.03346)
- [Working report for Erdős #612](https://erdosproblemaday.com/report/612)

## AI usage disclosure

This formalization, proof development, and documentation were produced with
assistance from OpenAI Codex, Astra, and ChatGPT under the direction of
KitaKen1 (Kenta Kitamura).

## Appendix A — Status by clique size K

| **Original conjecture (1989) — non-Lean statement** |
|---|
| For connected `K₂ᵣ`-free graphs: `D ≤ [2(r−1)(3r+2)/(2r²−1)] n/δ + O(1)`, assuming `(r−1)(3r+2) ∣ δ`. |
| For connected `K₂ᵣ₊₁`-free graphs: `D ≤ [(3r−1)/r] n/δ + O(1)`, assuming `(3r−1) ∣ δ`. |

| **Amended conjecture — non-Lean statement** |
|---|
| Every connected `Kₖ₊₁`-free graph satisfies `D ≤ (3−2/k)n/δ + O(1)` for `k≥3`. |

| Original K | Prior status |
|---|---|
| K₁, K₂ | Out of scope |
| K₃ | SOLVED |
| K₄, K₆ | REFUTED |
| K₅, K₇ | **OPEN** |
| K≥8 | REFUTED |

| Amended K | Prior status |
|---|---|
| K₁–K₃ | Out of scope |
| K₄–K₇ | **OPEN** |
| K≥8 | REFUTED |

### This project's contributions

| Target | Result |
|---|---|
| Original K₅ (r=2) | **OPEN → SOLVED** — This project claim |
| Amended K₄ (k=3) | **OPEN → SOLVED** — This project claim |
| Amended K₅ (k=4) | **OPEN → SOLVED** — This project claim |
| Original K₇ (r=3) | **OPEN → REFUTED** — This project claim |
| Amended K₆ (k=5) | **OPEN → REFUTED** — This project claim |
| Amended K₇ (k=6) | **OPEN → REFUTED** — This project claim |

## Appendix B — Conjecture formalization in FClikeLean

In Formal Conjectures terminology, a refuted proposition is **SOLVED** with
`answer(False)`.

### Original conjecture targets

| Target | Status |
|---|---|
| Even family `erdos_612.parts.i` | SOLVED · `answer(False)` |
| Odd family `erdos_612.parts.ii` | SOLVED · `answer(False)` |

### Original conjecture variant targets

| K / target | Status |
|---|---|
| K₃ `original_k3` | SOLVED |
| K₄ `original_k4`; K₆ `original_k6`; K≥8 `original_k_ge8` | SOLVED · `answer(False)` |
| K₅ `original_k5` | SOLVED · This project claim |
| K₇ `original_k7` | SOLVED · `answer(False)` · This project claim |

### Amended conjecture targets

| Target | Status |
|---|---|
| Full family `czabarka_singgih_szekely` | SOLVED · `answer(False)` |

### Amended conjecture variant targets

| K / target | Status |
|---|---|
| K₄ `amended_k3`; K₅ `amended_k4` | SOLVED · This project claim |
| K₆ `amended_k5`; K₇ `amended_k6` | SOLVED · `answer(False)` · This project claim |
| K≥8 `amended_k_ge7` | SOLVED · `answer(False)` |
