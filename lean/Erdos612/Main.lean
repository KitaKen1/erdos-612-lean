import Erdos612.Telescoping

/-!
# Erdős 612: the verified BFS telescoping kernels

These theorems are the local-to-global summation stages of the proposed sharp
`K₅`-free and `K₄`-free proofs. Each graph-theoretic local inequality is supplied
as `hstep`; the theorems prove that its sum and the endpoint values force the
claimed global coefficient and additive constant.
-/

open scoped BigOperators

namespace Erdos612

/--
The abstract BFS telescoping target for the proposed `K₅`-free bound.
-/
theorem k5_bfs_telescoping (D : ℕ) (δ n s₀ s₁ sD P₀ PD : ℝ) (P q : ℕ → ℝ)
    (hstep : ∀ i < D, P (i + 1) - P i ≤ q i)
    (hsum : (∑ i ∈ Finset.range D, q i) = n - s₀ - s₁ - 2 * δ * D / 5)
    (hP₀ : P 0 = P₀) (hPD : P D = PD)
    (hleft : P₀ = 3 * s₀ / 5 + s₁ - δ / 5)
    (hright : PD = 2 * sD / 5 + δ / 5)
    (hs₀ : 1 ≤ s₀) (hsD : 1 ≤ sD) :
    2 * δ * (D + 1) + 4 ≤ 5 * n := by
  have htel := telescope_sub D P q hstep
  rw [hP₀, hPD, hsum] at htel
  exact k5_endpoint_closure D δ n s₀ s₁ sD P₀ PD htel hleft hright hs₀ hsD

/--
The amended `K₅` target obtained by dropping the positive endpoint constant
from the stronger original `K₅` bound.
-/
theorem amended_k5_bfs_telescoping (D : ℕ) (δ n s₀ s₁ sD P₀ PD : ℝ)
    (P q : ℕ → ℝ)
    (hstep : ∀ i < D, P (i + 1) - P i ≤ q i)
    (hsum : (∑ i ∈ Finset.range D, q i) = n - s₀ - s₁ - 2 * δ * D / 5)
    (hP₀ : P 0 = P₀) (hPD : P D = PD)
    (hleft : P₀ = 3 * s₀ / 5 + s₁ - δ / 5)
    (hright : PD = 2 * sD / 5 + δ / 5)
    (hs₀ : 1 ≤ s₀) (hsD : 1 ≤ sD) :
    2 * δ * (D + 1) ≤ 5 * n := by
  have hstrong := k5_bfs_telescoping D δ n s₀ s₁ sD P₀ PD P q
    hstep hsum hP₀ hPD hleft hright hs₀ hsD
  linarith

/--
A version whose endpoint values are obtained directly from the rational `K₅`
potential.
-/
theorem k5_bfs_telescoping_with_potential (D : ℕ) (δ n s₀ s₁ sPrev sD : ℝ)
    (P q : ℕ → ℝ)
    (hstep : ∀ i < D, P (i + 1) - P i ≤ q i)
    (hsum : (∑ i ∈ Finset.range D, q i) = n - s₀ - s₁ - 2 * δ * D / 5)
    (hP₀ : P 0 = k5Potential δ 0 s₀ s₁)
    (hPD : P D = k5Potential δ sPrev sD 0)
    (hs₁ : s₁ ≠ 0) (hsPrev : sPrev ≠ 0)
    (hs₀ : 1 ≤ s₀) (hsD : 1 ≤ sD) :
    2 * δ * (D + 1) + 4 ≤ 5 * n := by
  apply k5_bfs_telescoping D δ n s₀ s₁ sD
      (k5Potential δ 0 s₀ s₁) (k5Potential δ sPrev sD 0) P q hstep hsum
      hP₀ hPD
  · exact k5Potential_left_endpoint δ s₀ s₁ hs₁
  · exact k5Potential_right_endpoint δ sPrev sD hsPrev
  · exact hs₀
  · exact hsD

/--
The abstract BFS telescoping target for the proposed `K₄`-free bound.

`P i` is the potential on the triple centered at the `i`-th BFS layer. The function
`q` is the local right-hand side. The hypothesis `hsum` is the reindexed layer sum
after the two initial layers have been removed.
-/
theorem k4_bfs_telescoping (D : ℕ) (δ n s₀ s₁ sD P₀ PD : ℝ) (P q : ℕ → ℝ)
    (hstep : ∀ i < D, P (i + 1) - P i ≤ q i)
    (hsum : (∑ i ∈ Finset.range D, q i) = n - s₀ - s₁ - 3 * δ * D / 7)
    (hP₀ : P 0 = P₀) (hPD : P D = PD)
    (hleft : P₀ = 4 * s₀ / 7 + s₁ - 3 * δ / 14)
    (hright : PD = 3 * sD / 7 + 3 * δ / 14)
    (hs₀ : 1 ≤ s₀) (hsD : 1 ≤ sD) :
    3 * δ * (D + 1) + 6 ≤ 7 * n := by
  have htel := telescope_sub D P q hstep
  rw [hP₀, hPD, hsum] at htel
  exact k4_endpoint_closure D δ n s₀ s₁ sD P₀ PD htel hleft hright hs₀ hsD

/--
A version whose endpoint values are obtained directly from the rational `K₄`
potential. The adjacent endpoint layer sizes must be nonzero so the endpoint
fractions are defined by their intended cancellation.
-/
theorem k4_bfs_telescoping_with_potential (D : ℕ) (δ n s₀ s₁ sPrev sD : ℝ)
    (P q : ℕ → ℝ)
    (hstep : ∀ i < D, P (i + 1) - P i ≤ q i)
    (hsum : (∑ i ∈ Finset.range D, q i) = n - s₀ - s₁ - 3 * δ * D / 7)
    (hP₀ : P 0 = k4Potential δ 0 s₀ s₁)
    (hPD : P D = k4Potential δ sPrev sD 0)
    (hs₁ : s₁ ≠ 0) (hsPrev : sPrev ≠ 0)
    (hs₀ : 1 ≤ s₀) (hsD : 1 ≤ sD) :
    3 * δ * (D + 1) + 6 ≤ 7 * n := by
  apply k4_bfs_telescoping D δ n s₀ s₁ sD
      (k4Potential δ 0 s₀ s₁) (k4Potential δ sPrev sD 0) P q hstep hsum
      hP₀ hPD
  · exact k4Potential_left_endpoint δ s₀ s₁ hs₁
  · exact k4Potential_right_endpoint δ sPrev sD hsPrev
  · exact hs₀
  · exact hsD

end Erdos612
