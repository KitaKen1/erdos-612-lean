import Erdos612.Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Finite telescoping inequalities

This file isolates the purely algebraic summation step. No graph-theoretic
assumption is used here.
-/

open scoped BigOperators

namespace Erdos612

/-- A pointwise upper bound on consecutive differences telescopes along a finite chain. -/
theorem telescope_sub (D : ℕ) (P q : ℕ → ℝ)
    (hstep : ∀ i < D, P (i + 1) - P i ≤ q i) :
    P D - P 0 ≤ ∑ i ∈ Finset.range D, q i := by
  have htel : ∑ i ∈ Finset.range D, (P (i + 1) - P i) = P D - P 0 := by
    clear hstep
    induction D with
    | zero => simp
    | succ D ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  rw [← htel]
  exact Finset.sum_le_sum fun i hi ↦ hstep i (Finset.mem_range.mp hi)

/--
The endpoint calculation for the `K₅`-free BFS argument after telescoping.
The hypotheses `1 ≤ s₀` and `1 ≤ sD` encode the nonempty endpoint layers.
-/
theorem k5_endpoint_closure (D : ℕ) (δ n s₀ s₁ sD P₀ PD : ℝ)
    (htotal : PD - P₀ ≤ n - s₀ - s₁ - 2 * δ * D / 5)
    (hleft : P₀ = 3 * s₀ / 5 + s₁ - δ / 5)
    (hright : PD = 2 * sD / 5 + δ / 5)
    (hs₀ : 1 ≤ s₀) (hsD : 1 ≤ sD) :
    2 * δ * (D + 1) + 4 ≤ 5 * n := by
  norm_num at htotal hleft hright ⊢
  rw [hleft, hright] at htotal
  nlinarith

/--
The endpoint calculation for the `K₄`-free BFS argument after telescoping.
The hypotheses `1 ≤ s₀` and `1 ≤ sD` encode the nonempty endpoint layers.
-/
theorem k4_endpoint_closure (D : ℕ) (δ n s₀ s₁ sD P₀ PD : ℝ)
    (htotal : PD - P₀ ≤ n - s₀ - s₁ - 3 * δ * D / 7)
    (hleft : P₀ = 4 * s₀ / 7 + s₁ - 3 * δ / 14)
    (hright : PD = 3 * sD / 7 + 3 * δ / 14)
    (hs₀ : 1 ≤ s₀) (hsD : 1 ≤ sD) :
    3 * δ * (D + 1) + 6 ≤ 7 * n := by
  norm_num at htotal hleft hright ⊢
  rw [hleft, hright] at htotal
  nlinarith

end Erdos612
