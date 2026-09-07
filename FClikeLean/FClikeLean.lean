/-
This Lean file was created by KitaKen1 (Kenta Kitamura) with assistance from OpenAI Codex.

It imitates the style of Formal Conjectures for a prospective Erdős #612 statement.
It is not an official Formal Conjectures file and has not been reviewed, approved, or merged.
-/

import FormalConjecturesUtil

/-!
# Erdős Problem 612

*References:*
- [erdosproblems.com/612](https://www.erdosproblems.com/612)
- [EPPT89] Erdős, P., Pach, J., Pollack, R., and Tuza, Z., *Radius, diameter, and minimum
  degree*. J. Combin. Theory Ser. B 47 (1989), 73–79.
- [CSS21] Czabarka, É., Singgih, I., and Székely, L. A., *Counterexamples to a conjecture
  of Erdős, Pach, Pollack and Tuza*. J. Combin. Theory Ser. B 151 (2021), 38–45.
- [CDS09] Czabarka, É., Dankelmann, P., and Székely, L. A., *Diameter of 4-colourable
  graphs*. European J. Combin. 30 (2009), 1082–1089.
- [CSS23] Czabarka, É., Smith, S. J., and Székely, L. A., *Maximum diameter of 3- and
  4-colorable graphs*. J. Graph Theory 102 (2023), 262–270.
- [CaJo25] Cambie, S. and Jooken, J., *Sharp results for the Erdős, Pach, Pollack and
  Tuza problem*. arXiv:2502.08626 (2025).
- [CC26] Chen, H. and Chen, Y., *Counterexamples to two conjectures on the diameter
  of clique-free graphs*. arXiv:2609.03346 (2026).
-/

open scoped BigOperators
open SimpleGraph

namespace Erdos612

/--
There is a uniform additive constant in the diameter bound for all connected finite graphs
with no clique of the given size.
-/
def HasAsymptoticDiameterBound (cliqueSize : ℕ) (coefficient : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Connected → G.CliqueFree cliqueSize →
      (G.diam : ℝ) ≤ coefficient * (n : ℝ) / (G.minDegree : ℝ) + C

/-- The same bound, restricted to minimum degrees divisible by `divisor`. -/
def HasDivisibleDiameterBound (cliqueSize divisor : ℕ) (coefficient : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Connected → G.CliqueFree cliqueSize → divisor ∣ G.minDegree →
      (G.diam : ℝ) ≤ coefficient * (n : ℝ) / (G.minDegree : ℝ) + C

/-- The Czabarka–Singgih–Székely amended conjecture at a fixed `k`. -/
def AmendedConjectureAt (k : ℕ) : Prop :=
  HasAsymptoticDiameterBound (k + 1) (3 - 2 / (k : ℝ))

/-- The original even-clique conjecture at a fixed `r`. -/
def OriginalEvenConjectureAt (r : ℕ) : Prop :=
  HasDivisibleDiameterBound (2 * r) ((r - 1) * (3 * r + 2))
    (((2 * (r - 1) * (3 * r + 2) : ℕ) : ℝ) /
      ((2 * r ^ 2 - 1 : ℕ) : ℝ))

/-- The original odd-clique conjecture at a fixed `r`. -/
def OriginalOddConjectureAt (r : ℕ) : Prop :=
  HasDivisibleDiameterBound (2 * r + 1) (3 * r - 1)
    (((3 * r - 1 : ℕ) : ℝ) / (r : ℝ))

/--
Let $G$ be a connected graph with $n$ vertices, minimum degree $d$, and diameter $D$.
Show that if $G$ contains no $K_{2r}$ and $(r-1)(3r+2)\mid d$, then
\[
D\leq \frac{2(r-1)(3r+2)}{2r^2-1}\frac{n}{d}+O(1).
\]

This universal even-clique clause was disproved by Czabarka, Singgih, and
Székely [CSS21].
-/
@[category research solved, AMS 5]
theorem erdos_612.parts.i :
    answer(False) ↔
      ∀ r : ℕ, 2 ≤ r → OriginalEvenConjectureAt r := by
  sorry

/--
Let $G$ be a connected graph with $n$ vertices, minimum degree $d$, and diameter $D$.
Show that if $G$ contains no $K_{2r+1}$ and $3r-1\mid d$, then
\[
D\leq \frac{3r-1}{r}\frac{n}{d}+O(1).
\]

Chen and Chen [CC26] report counterexamples for `r ≥ 4`. However, Erdős
Problems #612 remains officially OPEN as of 2026-09-07, with no proof claim;
the remaining low-`r` story has not yet been incorporated as a settled result.
-/
@[category research open, AMS 5]
theorem erdos_612.parts.ii :
    answer(sorry) ↔
      ∀ r : ℕ, 1 ≤ r → OriginalOddConjectureAt r := by
  sorry

/-! ## Fixed-clique variants of the original conjecture -/

/-- Original odd case `r = 1`: connected `K₃`-free graphs, proved in [EPPT89]. -/
@[category research solved, AMS 5]
theorem erdos_612.variants.original_k3 :
    answer(True) ↔ OriginalOddConjectureAt 1 := by
  sorry

/-- Original even case `r = 2`: connected `K₄`-free graphs, disproved in [CSS21]. -/
@[category research solved, AMS 5]
theorem erdos_612.variants.original_k4 :
    answer(False) ↔ OriginalEvenConjectureAt 2 := by
  sorry

/--
Original odd case `r = 2`: connected `K₅`-free graphs.
The sibling Lean proof proves the stronger exact `K₅`-free bound
`2δ(D+1)+4 ≤ 5n` without the divisibility restriction.
-/
@[category research solved, AMS 5]
theorem erdos_612.variants.original_k5 :
    answer(True) ↔ OriginalOddConjectureAt 2 := by
  sorry

/-- Original even case `r = 3`: connected `K₆`-free graphs, disproved in [CSS21]. -/
@[category research solved, AMS 5]
theorem erdos_612.variants.original_k6 :
    answer(False) ↔ OriginalEvenConjectureAt 3 := by
  sorry

/-- Original odd case `r = 3`: connected `K₇`-free graphs. -/
@[category research open, AMS 5]
theorem erdos_612.variants.original_k7 :
    answer(sorry) ↔ OriginalOddConjectureAt 3 := by
  sorry

/--
The original conjecture restricted to every forbidden clique size at least eight:
the even cases `r ≥ 4` and the odd cases `r ≥ 4`.

The even cases are disproved in [CSS21], and the odd cases are disproved in [CC26].
-/
@[category research solved, AMS 5]
theorem erdos_612.variants.original_k_ge8 :
    answer(False) ↔
      (∀ r : ℕ, 4 ≤ r → OriginalEvenConjectureAt r) ∧
      (∀ r : ℕ, 4 ≤ r → OriginalOddConjectureAt r) := by
  sorry

/--
Czabarka, Singgih, and Székely [CSS21] proposed the amended conjecture that every connected
$K_{k+1}$-free graph on $n$ vertices with minimum degree $d$ has diameter at most
\[
\left(3-\frac{2}{k}\right)\frac{n}{d}+O(1).
\]

Chen and Chen [CC26] disproved this universal conjecture for every `k ≥ 7`.
-/
@[category research solved, AMS 5]
theorem erdos_612.variants.czabarka_singgih_szekely :
    answer(False) ↔ ∀ k : ℕ, 3 ≤ k → AmendedConjectureAt k := by
  sorry

/--
The `k = 3` case of the amended conjecture, for all connected `K₄`-free graphs.
The sibling Lean proof proves the stronger exact `K₄`-free bound
`3δ(D+1)+6 ≤ 7n`.
-/
@[category research solved, AMS 5]
theorem erdos_612.variants.amended_k3 :
    answer(True) ↔ AmendedConjectureAt 3 := by
  sorry

/--
The `k = 4` case of the amended conjecture, for all connected `K₅`-free graphs.
It follows from the kernel-checked exact `K₅`-free bound in the sibling Lean proof.
-/
@[category research solved, AMS 5]
theorem erdos_612.variants.amended_k4 :
    answer(True) ↔ AmendedConjectureAt 4 := by
  sorry

/-- The `k = 5` case of the amended conjecture, for all connected `K₆`-free graphs. -/
@[category research open, AMS 5]
theorem erdos_612.variants.amended_k5 :
    answer(sorry) ↔ AmendedConjectureAt 5 := by
  sorry

/-- The `k = 6` case of the amended conjecture, for all connected `K₇`-free graphs. -/
@[category research open, AMS 5]
theorem erdos_612.variants.amended_k6 :
    answer(sorry) ↔ AmendedConjectureAt 6 := by
  sorry

/--
The amended conjecture restricted to `k ≥ 7`, equivalently `K₈`-free and above.
This family was disproved by Chen and Chen [CC26].
-/
@[category research solved, AMS 5]
theorem erdos_612.variants.amended_k_ge7 :
    answer(False) ↔ ∀ k : ℕ, 7 ≤ k → AmendedConjectureAt k := by
  sorry

end Erdos612
