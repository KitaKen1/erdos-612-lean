import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Aesop
import Lean.Elab.Tactic.Omega

/-!
# Erdős Problem 612 — complete standalone Lean4Web proof

This single file proves the actual original K₅ and amended K₄/K₅ graph targets.
It assumes only connectedness and clique-freeness; the greedy cover, BFS layers,
local nonlinear inequalities, telescope, endpoint algebra, and axiom audit are included.
-/


/-!
# Erdős 612: potentials and endpoint identities

The proposed sharp `K₄`-free and `K₅`-free diameter proofs use rational potentials
on triples of consecutive BFS layer sizes. This file records both potentials and
verifies their endpoint evaluations.
-/

namespace Erdos612

/-- The potential used by the proposed sharp `K₄`-free argument. -/
noncomputable def k4Potential (δ a b c : ℝ) : ℝ :=
  b / 2 + c - (c - a) * (3 * δ - b) / (14 * (a + c))

/-- The potential used by the proposed sharp `K₅`-free argument. -/
noncomputable def k5Potential (δ a b c : ℝ) : ℝ :=
  b / 2 + c - (c - a) * (2 * δ - b) / (10 * (a + c))

/-- Evaluation of the `K₄` potential at the left auxiliary layer. -/
theorem k4Potential_left_endpoint (δ b c : ℝ) (hc : c ≠ 0) :
    k4Potential δ 0 b c = 4 * b / 7 + c - 3 * δ / 14 := by
  simp only [k4Potential, zero_add, sub_zero]
  field_simp [hc]
  ring

/-- Evaluation of the `K₄` potential at the right auxiliary layer. -/
theorem k4Potential_right_endpoint (δ a b : ℝ) (ha : a ≠ 0) :
    k4Potential δ a b 0 = 3 * b / 7 + 3 * δ / 14 := by
  simp only [k4Potential, add_zero, zero_sub]
  field_simp [ha]
  ring

/-- Evaluation of the `K₅` potential at the left auxiliary layer. -/
theorem k5Potential_left_endpoint (δ b c : ℝ) (hc : c ≠ 0) :
    k5Potential δ 0 b c = 3 * b / 5 + c - δ / 5 := by
  simp only [k5Potential, zero_add, sub_zero]
  field_simp [hc]
  ring

/-- Evaluation of the `K₅` potential at the right auxiliary layer. -/
theorem k5Potential_right_endpoint (δ a b : ℝ) (ha : a ≠ 0) :
    k5Potential δ a b 0 = 2 * b / 5 + δ / 5 := by
  simp only [k5Potential, add_zero, zero_sub]
  field_simp [ha]
  ring

end Erdos612

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

/-!
# Local four-layer inequalities for Erdős Problem 612

This file verifies the nonlinear algebra that was previously left outside the
Lean development.  The hypotheses are precisely the numerical output of the
finite-graph greedy covering lemma: after orienting a four-layer window so
that `a ≤ d`, `t` is the smaller closed non-neighbourhood bound, `e = d-a`,
and `k` is the number of greedily selected vertices in the left middle layer.
-/

namespace Erdos612

/-- The nonlinear local inequality used for the `K₅`-free bound. -/
theorem k5_local_four_layer
    (a b c d δ t e : ℝ) (k : ℕ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (had : a ≤ d)
    (hac : 0 < a + c) (hbd : 0 < b + d)
    (ht : t = a + b + c - δ) (he : e = d - a)
    (hk₁ : 1 ≤ k) (hk₄ : k ≤ 4)
    (hbkt : b ≤ (k : ℝ) * t)
    (hcover : 0 ≤ 4 * t + (4 - (k : ℝ)) * e - b - c) :
    k5Potential δ b c d - k5Potential δ a b c ≤ d - 2 * δ / 5 := by
  have he0 : 0 ≤ e := by rw [he]; linarith
  have ht0 : 0 ≤ t := by
    have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk₁
    nlinarith
  let L : ℝ := 4 * t + (4 - (k : ℝ)) * e - b - c
  let A : ℝ := b * (e + t - c) + c * t
  let B : ℝ := b * (4 * t - b - c) + (b + 2 * t) * e
  have hL : 0 ≤ L := by simpa [L] using hcover
  have hB : 0 ≤ B := by
    have hBid : B = b * L + ((k : ℝ) - 3) * b * e + 2 * t * e := by
      simp only [B, L]
      ring
    rw [hBid]
    interval_cases k <;> norm_num at hbkt ⊢
    · nlinarith [mul_nonneg hb hL, mul_nonneg (sub_nonneg.mpr (by linarith : b ≤ t)) he0]
    · nlinarith [mul_nonneg hb hL, mul_nonneg (sub_nonneg.mpr (by linarith : b ≤ 2 * t)) he0,
        mul_nonneg ht0 he0]
    · nlinarith [mul_nonneg hb hL, mul_nonneg ht0 he0]
    · nlinarith [mul_nonneg hb hL, mul_nonneg hb he0, mul_nonneg ht0 he0]
  have hA : 0 ≤ A := by
    by_cases hbt : b ≤ t
    · have htc : 0 ≤ c * (t - b) := mul_nonneg hc (sub_nonneg.mpr hbt)
      have hbe : 0 ≤ b * e := mul_nonneg hb he0
      have hbt' : 0 ≤ b * t := mul_nonneg hb ht0
      simp only [A]
      nlinarith
    · have htb : t - b ≤ 0 := by linarith
      have hcBound : c ≤ 4 * t + (4 - (k : ℝ)) * e - b := by
        simpa [L] using hL
      have hmul := mul_le_mul_of_nonpos_left hcBound htb
      interval_cases k <;> norm_num at hbkt hmul ⊢
      · exfalso
        linarith
      · have hp : 0 ≤ (2 * t - b) * (2 * t + e - b) :=
          mul_nonneg (by linarith) (by linarith)
        simp only [A]
        nlinarith
      · have hs : 0 ≤ (b - 2 * t) ^ 2 := sq_nonneg _
        have het : 0 ≤ e * t := mul_nonneg he0 ht0
        simp only [A]
        nlinarith
      · have hs : 0 ≤ (b - 2 * t) ^ 2 := sq_nonneg _
        have heb : 0 ≤ b * e := mul_nonneg hb he0
        simp only [A]
        nlinarith
  have hden : 0 < 10 * (a + c) * (b + d) := by positivity
  have hid :
      10 * (a + c) * (b + d) *
          ((d - 2 * δ / 5) - (k5Potential δ b c d - k5Potential δ a b c)) =
        2 * (a * (2 * A) + c * B) := by
    simp only [k5Potential, A, B]
    rw [ht, he]
    field_simp
    ring
  apply sub_nonneg.mp
  apply (mul_nonneg_iff_of_pos_left hden).mp
  rw [hid]
  positivity

/-- The nonlinear local inequality used for the `K₄`-free bound. -/
theorem k4_local_four_layer
    (a b c d δ t e : ℝ) (k : ℕ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (had : a ≤ d)
    (hac : 0 < a + c) (hbd : 0 < b + d)
    (ht : t = a + b + c - δ) (he : e = d - a)
    (hk₁ : 1 ≤ k) (hk₃ : k ≤ 3)
    (hbkt : b ≤ (k : ℝ) * t)
    (hcover : 0 ≤ 3 * t + (3 - (k : ℝ)) * e - b - c) :
    k4Potential δ b c d - k4Potential δ a b c ≤ d - 3 * δ / 7 := by
  have he0 : 0 ≤ e := by rw [he]; linarith
  have ht0 : 0 ≤ t := by
    have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk₁
    nlinarith
  let L : ℝ := 3 * t + (3 - (k : ℝ)) * e - b - c
  let A : ℝ := (3 * t - 4 * b) * c + 3 * b * (t + e)
  let B : ℝ := b * (6 * t - 2 * b - 2 * c) + (b + 3 * t) * e
  have hL : 0 ≤ L := by simpa [L] using hcover
  have hB : 0 ≤ B := by
    have hBid : B = 2 * b * L + (3 * t + (2 * (k : ℝ) - 5) * b) * e := by
      simp only [B, L]
      ring
    rw [hBid]
    interval_cases k <;> norm_num at hbkt ⊢
    · nlinarith [mul_nonneg hb hL, mul_nonneg (sub_nonneg.mpr (by linarith : b ≤ t)) he0]
    · nlinarith [mul_nonneg hb hL, mul_nonneg (sub_nonneg.mpr (by linarith : b ≤ 2 * t)) he0,
        mul_nonneg ht0 he0]
    · nlinarith [mul_nonneg hb hL, mul_nonneg hb he0, mul_nonneg ht0 he0]
  have hA : 0 ≤ A := by
    by_cases hcase : 4 * b ≤ 3 * t
    · have hfirst : 0 ≤ (3 * t - 4 * b) * c :=
        mul_nonneg (sub_nonneg.mpr hcase) hc
      have hsecond : 0 ≤ 3 * b * (t + e) := by positivity
      simp only [A]
      nlinarith
    · have hcoef : 0 ≤ 4 * b - 3 * t := by linarith
      have hsq : 0 ≤ (2 * b - 3 * t) ^ 2 := sq_nonneg _
      have hAL : 0 ≤ (4 * b - 3 * t) * L := mul_nonneg hcoef hL
      have hAid :
          A = (2 * b - 3 * t) ^ 2 +
              ((9 - 3 * (k : ℝ)) * t + (4 * (k : ℝ) - 9) * b) * e +
              (4 * b - 3 * t) * L := by
        simp only [A, L]
        ring
      rw [hAid]
      interval_cases k <;> norm_num at hbkt ⊢
      · have hmid : 0 ≤ (6 * t - 5 * b) * e :=
          mul_nonneg (by linarith) he0
        nlinarith
      · have hmid : 0 ≤ (3 * t - b) * e :=
          mul_nonneg (by linarith) he0
        nlinarith
      · have hmid : 0 ≤ 3 * b * e := by positivity
        nlinarith
  have hden : 0 < 14 * (a + c) * (b + d) := by positivity
  have hid :
      14 * (a + c) * (b + d) *
          ((d - 3 * δ / 7) - (k4Potential δ b c d - k4Potential δ a b c)) =
        2 * (a * A + c * B) := by
    simp only [k4Potential, A, B]
    rw [ht, he]
    field_simp
    ring
  apply sub_nonneg.mp
  apply (mul_nonneg_iff_of_pos_left hden).mp
  rw [hid]
  positivity

end Erdos612

/-!
# A greedy clique-covering lemma

For a graph with no `(m+1)`-clique, two disjoint vertex blocks `B,C` are
covered by closed non-neighbourhoods of at most `m` vertices.  Maximising first
inside `B` records how many of the covering vertices use the sharper `B` bound.
This is the combinatorial input to the four-layer inequalities.
-/

open scoped BigOperators Finset
open SimpleGraph

namespace Erdos612

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertices of `U` equal or nonadjacent to `v`.  This is the closed
neighbourhood of `v` in the complement of the graph induced on `U`. -/
def closedNonneighborFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (v : V) : Finset V :=
  U.filter fun w ↦ w = v ∨ ¬ G.Adj v w

@[simp]
theorem mem_closedNonneighborFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (v w : V) :
    w ∈ closedNonneighborFinset G U v ↔ w ∈ U ∧ (w = v ∨ ¬ G.Adj v w) := by
  simp [closedNonneighborFinset]

/-- A finite vertex set contains a clique of maximum cardinality among its
clique subsets. -/
theorem exists_maximum_clique_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) :
    ∃ S : Finset V, S ⊆ U ∧ G.IsClique (S : Set V) ∧
      ∀ T : Finset V, T ⊆ U → G.IsClique (T : Set V) → #T ≤ #S := by
  classical
  let candidates := U.powerset.filter fun S : Finset V ↦ G.IsClique (S : Set V)
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, SimpleGraph.isClique_empty]
  obtain ⟨S, hS, hmax⟩ := candidates.exists_max_image Finset.card hcandidates
  have hSmem : S ⊆ U ∧ G.IsClique (S : Set V) := by
    simpa [candidates] using hS
  refine ⟨S, hSmem.1, hSmem.2, ?_⟩
  intro T hTU hTc
  exact hmax T (by simpa [candidates] using ⟨hTU, hTc⟩)

/-- A clique inside `U` can be extended to one of maximum size among the
cliques inside `U` that contain it. -/
theorem exists_maximum_clique_extension (G : SimpleGraph V) [DecidableRel G.Adj]
    (U S : Finset V) (hSU : S ⊆ U) (hSc : G.IsClique (S : Set V)) :
    ∃ T : Finset V, S ⊆ T ∧ T ⊆ U ∧ G.IsClique (T : Set V) ∧
      ∀ R : Finset V, S ⊆ R → R ⊆ U → G.IsClique (R : Set V) → #R ≤ #T := by
  classical
  let candidates := U.powerset.filter fun T ↦ S ⊆ T ∧ G.IsClique (T : Set V)
  have hcandidates : candidates.Nonempty := by
    refine ⟨S, ?_⟩
    simp [candidates, hSU, hSc]
  obtain ⟨T, hT, hmax⟩ := candidates.exists_max_image Finset.card hcandidates
  have hTmem : T ⊆ U ∧ S ⊆ T ∧ G.IsClique (T : Set V) := by
    simpa [candidates] using hT
  refine ⟨T, hTmem.2.1, hTmem.1, hTmem.2.2, ?_⟩
  intro R hSR hRU hRc
  exact hmax R (by simpa [candidates] using ⟨hRU, hSR, hRc⟩)

/-- A maximum-cardinality clique in `U` covers `U` by its closed
non-neighbourhoods. -/
theorem subset_biUnion_closedNonneighbor_of_maximum
    (G : SimpleGraph V) [DecidableRel G.Adj] (U S : Finset V)
    (hSU : S ⊆ U) (hSc : G.IsClique (S : Set V))
    (hmax : ∀ T : Finset V, T ⊆ U → G.IsClique (T : Set V) → #T ≤ #S) :
    U ⊆ S.biUnion (closedNonneighborFinset G U) := by
  classical
  intro x hxU
  by_cases hxS : x ∈ S
  · exact Finset.mem_biUnion.mpr ⟨x, hxS, by simp [hxU]⟩
  · have hinsertU : insert x S ⊆ U := by simpa [Finset.insert_subset_iff] using ⟨hxU, hSU⟩
    have hnotClique : ¬ G.IsClique ((insert x S : Finset V) : Set V) := by
      intro hcl
      have hcard := hmax (insert x S) hinsertU hcl
      simp [hxS] at hcard
    have hnotCliqueSet : ¬ G.IsClique (insert x (S : Set V)) := by
      simpa using hnotClique
    rw [SimpleGraph.isClique_insert_of_notMem (by simpa using hxS)] at hnotCliqueSet
    simp only [hSc, true_and] at hnotCliqueSet
    push_neg at hnotCliqueSet
    obtain ⟨y, hyS, hxy⟩ := hnotCliqueSet
    exact Finset.mem_biUnion.mpr ⟨y, hyS, by
      rw [mem_closedNonneighborFinset]
      exact ⟨hxU, Or.inr (fun hyx ↦ hxy hyx.symm)⟩⟩

/-- The same covering fact for a clique that is maximum among the cliques in
`U` containing a fixed base clique. -/
theorem subset_biUnion_closedNonneighbor_of_extension_maximum
    (G : SimpleGraph V) [DecidableRel G.Adj] (U S T : Finset V)
    (hST : S ⊆ T) (hTU : T ⊆ U) (hTc : G.IsClique (T : Set V))
    (hmax : ∀ R : Finset V, S ⊆ R → R ⊆ U →
      G.IsClique (R : Set V) → #R ≤ #T) :
    U ⊆ T.biUnion (closedNonneighborFinset G U) := by
  classical
  intro x hxU
  by_cases hxT : x ∈ T
  · exact Finset.mem_biUnion.mpr ⟨x, hxT, by simp [hxU]⟩
  · have hinsertU : insert x T ⊆ U := by
      simpa [Finset.insert_subset_iff] using ⟨hxU, hTU⟩
    have hSinsert : S ⊆ insert x T := hST.trans (Finset.subset_insert x T)
    have hnotClique : ¬ G.IsClique ((insert x T : Finset V) : Set V) := by
      intro hcl
      have hcard := hmax (insert x T) hSinsert hinsertU hcl
      simp [hxT] at hcard
    have hnotCliqueSet : ¬ G.IsClique (insert x (T : Set V)) := by
      simpa using hnotClique
    rw [SimpleGraph.isClique_insert_of_notMem (by simpa using hxT)] at hnotCliqueSet
    simp only [hTc, true_and] at hnotCliqueSet
    push_neg at hnotCliqueSet
    obtain ⟨y, hyT, hxy⟩ := hnotCliqueSet
    exact Finset.mem_biUnion.mpr ⟨y, hyT, by
      rw [mem_closedNonneighborFinset]
      exact ⟨hxU, Or.inr (fun hyx ↦ hxy hyx.symm)⟩⟩

/-- Two-block greedy covering inequality.  `t` bounds closed
non-neighbourhoods centred in `B`, while `u` bounds those centred in `C`. -/
theorem cliqueFree_greedy_cover
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B C : Finset V) (m t u : ℕ)
    (hBC : Disjoint B C) (hBne : B.Nonempty)
    (hfree : G.CliqueFree (m + 1))
    (hBt : ∀ v ∈ B, #(closedNonneighborFinset G (B ∪ C) v) ≤ t)
    (hCu : ∀ v ∈ C, #(closedNonneighborFinset G (B ∪ C) v) ≤ u) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ #B ≤ k * t ∧ #(B ∪ C) ≤ k * t + (m - k) * u := by
  classical
  obtain ⟨S, hSB, hSc, hSmax⟩ := exists_maximum_clique_subset G B
  obtain ⟨T, hST, hTU, hTc, hTmax⟩ :=
    exists_maximum_clique_extension G (B ∪ C) S (hSB.trans Finset.subset_union_left) hSc
  have hS_inter : T ∩ B = S := by
    have hsub : S ⊆ T ∩ B := by
      intro x hxS
      exact Finset.mem_inter.mpr ⟨hST hxS, hSB hxS⟩
    have hcard : #(T ∩ B) ≤ #S :=
      hSmax (T ∩ B) Finset.inter_subset_right
        (hTc.subset (by simpa using (Finset.inter_subset_left : T ∩ B ⊆ T)))
    exact (Finset.eq_of_subset_of_card_le hsub hcard).symm
  have hSpos : 1 ≤ #S := by
    obtain ⟨x, hxB⟩ := hBne
    have hxcl : G.IsClique (({x} : Finset V) : Set V) := by
      simpa using (SimpleGraph.isClique_singleton (G := G) x)
    have hxcard := hSmax {x} (by simpa using hxB) hxcl
    simpa using hxcard
  have hTcard : #T ≤ m := by
    by_contra h
    have hm1 : m + 1 ≤ #T := by omega
    obtain ⟨R, hRT, hRcard⟩ := Finset.exists_subset_card_eq hm1
    exact hfree R ⟨hTc.subset (by simpa using hRT), hRcard⟩
  have hScard : #S ≤ m := (Finset.card_le_card hST).trans hTcard
  have hBcover : B ⊆ S.biUnion (closedNonneighborFinset G B) :=
    subset_biUnion_closedNonneighbor_of_maximum G B S hSB hSc hSmax
  have hbad_mono (v : V) :
      closedNonneighborFinset G B v ⊆ closedNonneighborFinset G (B ∪ C) v := by
    intro x hx
    rw [mem_closedNonneighborFinset] at hx ⊢
    exact ⟨Finset.mem_union_left C hx.1, hx.2⟩
  have hBcard : #B ≤ #S * t := by
    calc
      #B ≤ #(S.biUnion (closedNonneighborFinset G B)) := Finset.card_le_card hBcover
      _ ≤ ∑ v ∈ S, #(closedNonneighborFinset G B v) := Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ S, t := by
        apply Finset.sum_le_sum
        intro v hv
        exact (Finset.card_le_card (hbad_mono v)).trans (hBt v (hSB hv))
      _ = #S * t := by simp
  have hUcover : B ∪ C ⊆ T.biUnion (closedNonneighborFinset G (B ∪ C)) := by
    exact subset_biUnion_closedNonneighbor_of_extension_maximum
      G (B ∪ C) S T hST hTU hTc hTmax
  have hrestC : T \ S ⊆ C := by
    intro x hx
    have hxT := (Finset.mem_sdiff.mp hx).1
    have hxS := (Finset.mem_sdiff.mp hx).2
    rcases Finset.mem_union.mp (hTU hxT) with hxB | hxC
    · have : x ∈ S := by
        rw [← hS_inter]
        exact Finset.mem_inter.mpr ⟨hxT, hxB⟩
      exact False.elim (hxS this)
    · exact hxC
  have hsumS :
      (∑ v ∈ S, #(closedNonneighborFinset G (B ∪ C) v)) ≤ #S * t := by
    calc
      _ ≤ ∑ _v ∈ S, t := by
        apply Finset.sum_le_sum
        intro v hv
        exact hBt v (hSB hv)
      _ = #S * t := by simp
  have hsumRest :
      (∑ v ∈ T \ S, #(closedNonneighborFinset G (B ∪ C) v)) ≤ #(T \ S) * u := by
    calc
      _ ≤ ∑ _v ∈ T \ S, u := by
        apply Finset.sum_le_sum
        intro v hv
        exact hCu v (hrestC hv)
      _ = #(T \ S) * u := by simp
  have hsumT :
      (∑ v ∈ T, #(closedNonneighborFinset G (B ∪ C) v))
        ≤ #S * t + #(T \ S) * u := by
    calc
      _ = (∑ v ∈ T \ S, #(closedNonneighborFinset G (B ∪ C) v)) +
            ∑ v ∈ S, #(closedNonneighborFinset G (B ∪ C) v) :=
        (Finset.sum_sdiff hST).symm
      _ = (∑ v ∈ S, #(closedNonneighborFinset G (B ∪ C) v)) +
            ∑ v ∈ T \ S, #(closedNonneighborFinset G (B ∪ C) v) := by ac_rfl
      _ ≤ #S * t + #(T \ S) * u := Nat.add_le_add hsumS hsumRest
  have hrestcard : #(T \ S) ≤ m - #S := by
    rw [Finset.card_sdiff_of_subset hST]
    exact Nat.sub_le_sub_right hTcard #S
  have hUcard : #(B ∪ C) ≤ #S * t + (m - #S) * u := by
    calc
      #(B ∪ C) ≤ #(T.biUnion (closedNonneighborFinset G (B ∪ C))) :=
        Finset.card_le_card hUcover
      _ ≤ ∑ v ∈ T, #(closedNonneighborFinset G (B ∪ C) v) :=
        Finset.card_biUnion_le
      _ ≤ #S * t + #(T \ S) * u := hsumT
      _ ≤ #S * t + (m - #S) * u := Nat.add_le_add_left (Nat.mul_le_mul_right u hrestcard) _
  exact ⟨#S, hSpos, hScard, hBcard, hUcard⟩

end Erdos612

/-!
# BFS layers in a finite connected graph
-/

open scoped BigOperators Finset
open SimpleGraph

namespace Erdos612

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertices at graph distance exactly `i` from `root`. -/
noncomputable def bfsLayer (G : SimpleGraph V) (root : V) (i : ℕ) : Finset V :=
  Finset.univ.filter fun v ↦ G.dist root v = i

@[simp]
theorem mem_bfsLayer (G : SimpleGraph V) (root v : V) (i : ℕ) :
    v ∈ bfsLayer G root i ↔ G.dist root v = i := by
  simp [bfsLayer]

theorem bfsLayer_disjoint (G : SimpleGraph V) (root : V) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (bfsLayer G root i) (bfsLayer G root j) := by
  rw [Finset.disjoint_left]
  intro v hvi hvj
  rw [mem_bfsLayer] at hvi hvj
  exact hij (hvi.symm.trans hvj)

@[simp]
theorem bfsLayer_zero {G : SimpleGraph V} (hconn : G.Connected) (root : V) :
    bfsLayer G root 0 = {root} := by
  ext v
  simp [bfsLayer, hconn.dist_eq_zero_iff, eq_comm]

/-- The auxiliary layer before layer zero. -/
noncomputable def bfsPrevLayer (G : SimpleGraph V) (root : V) (i : ℕ) : Finset V :=
  if i = 0 then ∅ else bfsLayer G root (i - 1)

@[simp]
theorem bfsPrevLayer_zero (G : SimpleGraph V) (root : V) :
    bfsPrevLayer G root 0 = ∅ := by simp [bfsPrevLayer]

@[simp]
theorem bfsPrevLayer_succ (G : SimpleGraph V) (root : V) (i : ℕ) :
    bfsPrevLayer G root (i + 1) = bfsLayer G root i := by
  simp [bfsPrevLayer]

/-- Every prefix of a shortest walk is shortest. -/
theorem dist_getVert_eq_of_length_eq_dist
    {G : SimpleGraph V} (hconn : G.Connected) {x y : V}
    (p : G.Walk x y) (hp : p.length = G.dist x y) {i : ℕ} (hi : i ≤ p.length) :
    G.dist x (p.getVert i) = i := by
  have hleft : G.dist x (p.getVert i) ≤ i := by
    calc
      G.dist x (p.getVert i) ≤ (p.take i).length := SimpleGraph.dist_le (p.take i)
      _ = i := by simp [SimpleGraph.Walk.take_length, Nat.min_eq_left hi]
  have hright : G.dist (p.getVert i) y ≤ p.length - i := by
    calc
      G.dist (p.getVert i) y ≤ (p.drop i).length := SimpleGraph.dist_le (p.drop i)
      _ = p.length - i := SimpleGraph.Walk.drop_length p i
  have htri : G.dist x y ≤ G.dist x (p.getVert i) + G.dist (p.getVert i) y :=
    hconn.dist_triangle
  omega

/-- A connected finite graph has a diametral shortest walk, whose `i`th
vertex lies in BFS layer `i`. -/
theorem exists_diametral_walk (G : SimpleGraph V) (hconn : G.Connected) :
    ∃ (x y : V) (p : G.Walk x y),
      p.length = G.diam ∧ ∀ i ≤ G.diam, G.dist x (p.getVert i) = i := by
  letI : Nonempty V := hconn.nonempty
  obtain ⟨x, y, hxy⟩ := G.exists_dist_eq_diam
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x y
  have hplen : p.length = G.diam := hp.trans hxy
  refine ⟨x, y, p, hplen, ?_⟩
  intro i hi
  exact dist_getVert_eq_of_length_eq_dist hconn p hp (by omega)

theorem bfsLayer_nonempty_of_diametral
    {G : SimpleGraph V} {x y : V} (p : G.Walk x y)
    (hplen : p.length = G.diam)
    (hgeo : ∀ i ≤ G.diam, G.dist x (p.getVert i) = i)
    {i : ℕ} (hi : i ≤ G.diam) :
    (bfsLayer G x i).Nonempty := by
  refine ⟨p.getVert i, ?_⟩
  rw [mem_bfsLayer]
  exact hgeo i hi

theorem bfsLayer_eq_empty_of_diam_lt
    {G : SimpleGraph V} (hconn : G.Connected) (root : V) {i : ℕ}
    (hi : G.diam < i) : bfsLayer G root i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  rw [mem_bfsLayer] at hv
  letI : Nonempty V := hconn.nonempty
  have htop : G.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.mp hconn
  have := G.dist_le_diam htop (u := root) (v := v)
  omega

theorem biUnion_bfsLayer_eq_univ
    {G : SimpleGraph V} (hconn : G.Connected) (root : V) :
    (Finset.range (G.diam + 1)).biUnion (bfsLayer G root) = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro v
  apply Finset.mem_biUnion.mpr
  letI : Nonempty V := hconn.nonempty
  have htop : G.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.mp hconn
  have hle := G.dist_le_diam htop (u := root) (v := v)
  exact ⟨G.dist root v, Finset.mem_range.mpr (by omega), by simp⟩

theorem sum_bfsLayer_card
    {G : SimpleGraph V} (hconn : G.Connected) (root : V) :
    ∑ i ∈ Finset.range (G.diam + 1), #(bfsLayer G root i) = Fintype.card V := by
  have hpair : ((Finset.range (G.diam + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (bfsLayer G root) := by
    intro i hi j hj hij
    exact bfsLayer_disjoint G root hij
  have hcard := Finset.card_biUnion hpair
  rw [biUnion_bfsLayer_eq_univ hconn root, Finset.card_univ] at hcard
  exact hcard.symm

/-- Neighbours of a vertex in layer `i` lie in layers `i-1,i,i+1`. -/
theorem neighborFinset_subset_left_three
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V) (i : ℕ)
    {v : V} (hv : v ∈ bfsLayer G root i) :
    G.neighborFinset v ⊆
      bfsPrevLayer G root i ∪ bfsLayer G root i ∪ bfsLayer G root (i + 1) := by
  intro w hw
  have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp hw
  have hdist := hadj.diff_dist_adj (u := root)
  rw [mem_bfsLayer] at hv
  rw [hv] at hdist
  rcases hdist with hsame | hnext | hprev
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (mem_bfsLayer G root w i |>.mpr hsame))
  · exact Finset.mem_union_right _ (mem_bfsLayer G root w (i + 1) |>.mpr hnext)
  · cases i with
    | zero =>
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          (mem_bfsLayer G root w 0 |>.mpr (by simpa using hprev)))
    | succ j =>
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (by simpa using (mem_bfsLayer G root w j |>.mpr (by simpa using hprev))))

/-- Neighbours of a vertex in layer `i+1` lie in layers `i,i+1,i+2`. -/
theorem neighborFinset_subset_right_three
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V) (i : ℕ)
    {v : V} (hv : v ∈ bfsLayer G root (i + 1)) :
    G.neighborFinset v ⊆
      bfsLayer G root i ∪ bfsLayer G root (i + 1) ∪ bfsLayer G root (i + 2) := by
  intro w hw
  have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp hw
  have hdist := hadj.diff_dist_adj (u := root)
  rw [mem_bfsLayer] at hv
  rw [hv] at hdist
  rcases hdist with hsame | hnext | hprev
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      (mem_bfsLayer G root w (i + 1) |>.mpr hsame))
  · exact Finset.mem_union_right _ (mem_bfsLayer G root w (i + 2) |>.mpr (by simpa [Nat.add_assoc] using hnext))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (mem_bfsLayer G root w i |>.mpr (by simpa using hprev)))

/-- A closed non-neighbourhood in the two middle layers is bounded by
the size of the surrounding three layers minus the degree. -/
theorem closedNonneighbor_card_le_of_neighbor_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W : Finset V) (v : V)
    (hUW : U ⊆ W) (hneigh : G.neighborFinset v ⊆ W) :
    #(closedNonneighborFinset G U v) ≤ #W - G.degree v := by
  have hbad : closedNonneighborFinset G U v ⊆ W \ G.neighborFinset v := by
    intro x hx
    rw [mem_closedNonneighborFinset] at hx
    rw [Finset.mem_sdiff, G.mem_neighborFinset]
    exact ⟨hUW hx.1, fun hadj ↦ hx.2.elim
      (fun hxv ↦ by subst x; exact G.loopless.irrefl v hadj)
      (fun hnot ↦ hnot hadj)⟩
  calc
    #(closedNonneighborFinset G U v) ≤ #(W \ G.neighborFinset v) := Finset.card_le_card hbad
    _ = #W - G.degree v := by
      rw [Finset.card_sdiff_of_subset hneigh, G.card_neighborFinset_eq_degree]

end Erdos612

/-!
# From clique-free BFS windows to the local potential inequalities
-/

open scoped BigOperators Finset
open SimpleGraph

namespace Erdos612

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem card_three_union_le (A B C : Finset V) :
    #(A ∪ B ∪ C) ≤ #A + #B + #C := by
  calc
    #(A ∪ B ∪ C) ≤ #(A ∪ B) + #C := Finset.card_union_le _ _
    _ ≤ (#A + #B) + #C := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ = #A + #B + #C := rfl

/-- Numerical data supplied by the clique-free greedy lemma for an oriented
four-layer BFS window. -/
theorem fourLayer_greedy_data
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (root : V) (i m : ℕ)
    (hBne : (bfsLayer G root i).Nonempty)
    (hCne : (bfsLayer G root (i + 1)).Nonempty)
    (hfree : G.CliqueFree (m + 1))
    (horient : #(bfsPrevLayer G root i) ≤ #(bfsLayer G root (i + 2))) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧
      ((#(bfsLayer G root i) : ℕ) : ℝ) ≤
        (k : ℝ) *
          (((#(bfsPrevLayer G root i) : ℕ) : ℝ) +
            ((#(bfsLayer G root i) : ℕ) : ℝ) +
            ((#(bfsLayer G root (i + 1)) : ℕ) : ℝ) - (G.minDegree : ℝ)) ∧
      0 ≤ (m : ℝ) *
          (((#(bfsPrevLayer G root i) : ℕ) : ℝ) +
            ((#(bfsLayer G root i) : ℕ) : ℝ) +
            ((#(bfsLayer G root (i + 1)) : ℕ) : ℝ) - (G.minDegree : ℝ)) +
        ((m : ℝ) - (k : ℝ)) *
          (((#(bfsLayer G root (i + 2)) : ℕ) : ℝ) -
            ((#(bfsPrevLayer G root i) : ℕ) : ℝ)) -
        ((#(bfsLayer G root i) : ℕ) : ℝ) -
        ((#(bfsLayer G root (i + 1)) : ℕ) : ℝ) := by
  classical
  let A := bfsPrevLayer G root i
  let B := bfsLayer G root i
  let C := bfsLayer G root (i + 1)
  let R := bfsLayer G root (i + 2)
  let Wₗ := A ∪ B ∪ C
  let Wᵣ := B ∪ C ∪ R
  let t := #A + #B + #C - G.minDegree
  let u := #B + #C + #R - G.minDegree
  have hBU : B ∪ C ⊆ Wₗ := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxB | hxC
    · exact Finset.mem_union_left C (Finset.mem_union_right A hxB)
    · exact Finset.mem_union_right (A ∪ B) hxC
  have hCU : B ∪ C ⊆ Wᵣ := Finset.subset_union_left
  have hBt : ∀ v ∈ B, #(closedNonneighborFinset G (B ∪ C) v) ≤ t := by
    intro v hv
    have hbad := closedNonneighbor_card_le_of_neighbor_subset G (B ∪ C) Wₗ v hBU
      (by simpa [Wₗ, A, B, C] using neighborFinset_subset_left_three G root i hv)
    have hW : #Wₗ ≤ #A + #B + #C := by
      simpa [Wₗ] using card_three_union_le A B C
    have hdeg := G.minDegree_le_degree v
    simp only [t]
    omega
  have hCu : ∀ v ∈ C, #(closedNonneighborFinset G (B ∪ C) v) ≤ u := by
    intro v hv
    have hbad := closedNonneighbor_card_le_of_neighbor_subset G (B ∪ C) Wᵣ v hCU
      (by simpa [Wᵣ, B, C, R, Nat.add_assoc] using
        neighborFinset_subset_right_three G root i hv)
    have hW : #Wᵣ ≤ #B + #C + #R := by
      simpa [Wᵣ] using card_three_union_le B C R
    have hdeg := G.minDegree_le_degree v
    simp only [u]
    omega
  have hBC : Disjoint B C := by
    exact bfsLayer_disjoint G root (by omega)
  obtain ⟨k, hk1, hkm, hBk, hU⟩ :=
    cliqueFree_greedy_cover G B C m t u hBC (by simpa [B] using hBne) hfree hBt hCu
  have hdeltaL : G.minDegree ≤ #A + #B + #C := by
    obtain ⟨v, hv⟩ := hBne
    have hneigh := neighborFinset_subset_left_three G root i hv
    have hdegcard : G.degree v ≤ #Wₗ := by
      rw [← G.card_neighborFinset_eq_degree]
      exact Finset.card_le_card (by simpa [Wₗ, A, B, C] using hneigh)
    have hW : #Wₗ ≤ #A + #B + #C := by
      simpa [Wₗ] using card_three_union_le A B C
    have hmindeg := G.minDegree_le_degree v
    omega
  have hdeltaR : G.minDegree ≤ #B + #C + #R := by
    obtain ⟨v, hv⟩ := hCne
    have hneigh := neighborFinset_subset_right_three G root i hv
    have hdegcard : G.degree v ≤ #Wᵣ := by
      rw [← G.card_neighborFinset_eq_degree]
      exact Finset.card_le_card (by simpa [Wᵣ, B, C, R, Nat.add_assoc] using hneigh)
    have hW : #Wᵣ ≤ #B + #C + #R := by
      simpa [Wᵣ] using card_three_union_le B C R
    have hmindeg := G.minDegree_le_degree v
    omega
  have htu : u = t + (#R - #A) := by
    simp only [u, t, A, B, C, R] at hdeltaL hdeltaR horient ⊢
    omega
  have hUcard : #(B ∪ C) = #B + #C := Finset.card_union_of_disjoint hBC
  have hcoverNat : #B + #C ≤ m * t + (m - k) * (#R - #A) := by
    rw [hUcard] at hU
    calc
      #B + #C ≤ k * t + (m - k) * u := hU
      _ = k * t + (m - k) * (t + (#R - #A)) := by rw [htu]
      _ = m * t + (m - k) * (#R - #A) := by
        have hmk : k + (m - k) = m := Nat.add_sub_of_le hkm
        calc
          _ = (k + (m - k)) * t + (m - k) * (#R - #A) := by ring
          _ = m * t + (m - k) * (#R - #A) := by rw [hmk]
  have htcast :
      (t : ℝ) = (#A : ℝ) + (#B : ℝ) + (#C : ℝ) - (G.minDegree : ℝ) := by
    simp only [t]
    rw [Nat.cast_sub hdeltaL]
    push_cast
    ring
  have hBkReal : (#B : ℝ) ≤ (k : ℝ) * (t : ℝ) := by exact_mod_cast hBk
  have hcoverReal :
      (#B : ℝ) + (#C : ℝ) ≤
        (m : ℝ) * (t : ℝ) + ((m - k : ℕ) : ℝ) * ((#R - #A : ℕ) : ℝ) := by
    exact_mod_cast hcoverNat
  rw [Nat.cast_sub hkm, Nat.cast_sub horient] at hcoverReal
  refine ⟨k, hk1, hkm, ?_, ?_⟩
  · rw [htcast] at hBkReal
    simpa [A, B, C] using hBkReal
  · have := hcoverReal
    rw [htcast] at this
    simp only [A, B, C, R] at this ⊢
    linarith

/-- The same numerical data with the four-layer window read from right to
left.  This is needed when the right outer layer is smaller. -/
theorem fourLayer_greedy_data_reverse
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (root : V) (i m : ℕ)
    (hBne : (bfsLayer G root i).Nonempty)
    (hCne : (bfsLayer G root (i + 1)).Nonempty)
    (hfree : G.CliqueFree (m + 1))
    (horient : #(bfsLayer G root (i + 2)) ≤ #(bfsPrevLayer G root i)) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧
      ((#(bfsLayer G root (i + 1)) : ℕ) : ℝ) ≤
        (k : ℝ) *
          (((#(bfsLayer G root (i + 2)) : ℕ) : ℝ) +
            ((#(bfsLayer G root (i + 1)) : ℕ) : ℝ) +
            ((#(bfsLayer G root i) : ℕ) : ℝ) - (G.minDegree : ℝ)) ∧
      0 ≤ (m : ℝ) *
          (((#(bfsLayer G root (i + 2)) : ℕ) : ℝ) +
            ((#(bfsLayer G root (i + 1)) : ℕ) : ℝ) +
            ((#(bfsLayer G root i) : ℕ) : ℝ) - (G.minDegree : ℝ)) +
        ((m : ℝ) - (k : ℝ)) *
          (((#(bfsPrevLayer G root i) : ℕ) : ℝ) -
            ((#(bfsLayer G root (i + 2)) : ℕ) : ℝ)) -
        ((#(bfsLayer G root (i + 1)) : ℕ) : ℝ) -
        ((#(bfsLayer G root i) : ℕ) : ℝ) := by
  classical
  let A := bfsLayer G root (i + 2)
  let B := bfsLayer G root (i + 1)
  let C := bfsLayer G root i
  let R := bfsPrevLayer G root i
  let Wₗ := A ∪ B ∪ C
  let Wᵣ := B ∪ C ∪ R
  let t := #A + #B + #C - G.minDegree
  let u := #B + #C + #R - G.minDegree
  have hBU : B ∪ C ⊆ Wₗ := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxB | hxC
    · exact Finset.mem_union_left C (Finset.mem_union_right A hxB)
    · exact Finset.mem_union_right (A ∪ B) hxC
  have hCU : B ∪ C ⊆ Wᵣ := Finset.subset_union_left
  have hBt : ∀ v ∈ B, #(closedNonneighborFinset G (B ∪ C) v) ≤ t := by
    intro v hv
    have hneigh0 := neighborFinset_subset_right_three G root i hv
    have hneigh : G.neighborFinset v ⊆ Wₗ := by
      simpa [Wₗ, A, B, C, Finset.union_assoc, Finset.union_comm, Finset.union_left_comm]
        using hneigh0
    have hbad := closedNonneighbor_card_le_of_neighbor_subset G (B ∪ C) Wₗ v hBU hneigh
    have hW : #Wₗ ≤ #A + #B + #C := by
      simpa [Wₗ] using card_three_union_le A B C
    have hdeg := G.minDegree_le_degree v
    simp only [t]
    omega
  have hCu : ∀ v ∈ C, #(closedNonneighborFinset G (B ∪ C) v) ≤ u := by
    intro v hv
    have hneigh0 := neighborFinset_subset_left_three G root i hv
    have hneigh : G.neighborFinset v ⊆ Wᵣ := by
      simpa [Wᵣ, B, C, R, Finset.union_assoc, Finset.union_comm, Finset.union_left_comm]
        using hneigh0
    have hbad := closedNonneighbor_card_le_of_neighbor_subset G (B ∪ C) Wᵣ v hCU hneigh
    have hW : #Wᵣ ≤ #B + #C + #R := by
      simpa [Wᵣ] using card_three_union_le B C R
    have hdeg := G.minDegree_le_degree v
    simp only [u]
    omega
  have hBC : Disjoint B C := by
    exact (bfsLayer_disjoint G root (by omega)).symm
  obtain ⟨k, hk1, hkm, hBk, hU⟩ :=
    cliqueFree_greedy_cover G B C m t u hBC (by simpa [B] using hCne) hfree hBt hCu
  have hdeltaL : G.minDegree ≤ #A + #B + #C := by
    obtain ⟨v, hv⟩ := hCne
    have hneigh0 := neighborFinset_subset_right_three G root i hv
    have hneigh : G.neighborFinset v ⊆ Wₗ := by
      simpa [Wₗ, A, B, C, Finset.union_assoc, Finset.union_comm, Finset.union_left_comm]
        using hneigh0
    have hdegcard : G.degree v ≤ #Wₗ := by
      rw [← G.card_neighborFinset_eq_degree]
      exact Finset.card_le_card hneigh
    have hW : #Wₗ ≤ #A + #B + #C := by
      simpa [Wₗ] using card_three_union_le A B C
    have hmindeg := G.minDegree_le_degree v
    omega
  have hdeltaR : G.minDegree ≤ #B + #C + #R := by
    obtain ⟨v, hv⟩ := hBne
    have hneigh0 := neighborFinset_subset_left_three G root i hv
    have hneigh : G.neighborFinset v ⊆ Wᵣ := by
      simpa [Wᵣ, B, C, R, Finset.union_assoc, Finset.union_comm, Finset.union_left_comm]
        using hneigh0
    have hdegcard : G.degree v ≤ #Wᵣ := by
      rw [← G.card_neighborFinset_eq_degree]
      exact Finset.card_le_card hneigh
    have hW : #Wᵣ ≤ #B + #C + #R := by
      simpa [Wᵣ] using card_three_union_le B C R
    have hmindeg := G.minDegree_le_degree v
    omega
  have htu : u = t + (#R - #A) := by
    simp only [u, t, A, B, C, R] at hdeltaL hdeltaR horient ⊢
    omega
  have hUcard : #(B ∪ C) = #B + #C := Finset.card_union_of_disjoint hBC
  have hcoverNat : #B + #C ≤ m * t + (m - k) * (#R - #A) := by
    rw [hUcard] at hU
    calc
      #B + #C ≤ k * t + (m - k) * u := hU
      _ = k * t + (m - k) * (t + (#R - #A)) := by rw [htu]
      _ = m * t + (m - k) * (#R - #A) := by
        have hmk : k + (m - k) = m := Nat.add_sub_of_le hkm
        calc
          _ = (k + (m - k)) * t + (m - k) * (#R - #A) := by ring
          _ = m * t + (m - k) * (#R - #A) := by rw [hmk]
  have htcast :
      (t : ℝ) = (#A : ℝ) + (#B : ℝ) + (#C : ℝ) - (G.minDegree : ℝ) := by
    simp only [t]
    rw [Nat.cast_sub hdeltaL]
    push_cast
    ring
  have hBkReal : (#B : ℝ) ≤ (k : ℝ) * (t : ℝ) := by exact_mod_cast hBk
  have hcoverReal :
      (#B : ℝ) + (#C : ℝ) ≤
        (m : ℝ) * (t : ℝ) + ((m - k : ℕ) : ℝ) * ((#R - #A : ℕ) : ℝ) := by
    exact_mod_cast hcoverNat
  rw [Nat.cast_sub hkm, Nat.cast_sub horient] at hcoverReal
  refine ⟨k, hk1, hkm, ?_, ?_⟩
  · rw [htcast] at hBkReal
    simpa [A, B, C] using hBkReal
  · rw [htcast] at hcoverReal
    simp only [A, B, C, R] at hcoverReal ⊢
    linarith

/-- Local potential step for every four-layer window in a `K₅`-free graph. -/
theorem k5_graph_local_step
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (root : V) (i : ℕ)
    (hBne : (bfsLayer G root i).Nonempty)
    (hCne : (bfsLayer G root (i + 1)).Nonempty)
    (hfree : G.CliqueFree 5) :
    k5Potential (G.minDegree : ℝ)
        (#(bfsLayer G root i) : ℝ) (#(bfsLayer G root (i + 1)) : ℝ)
        (#(bfsLayer G root (i + 2)) : ℝ) -
      k5Potential (G.minDegree : ℝ)
        (#(bfsPrevLayer G root i) : ℝ) (#(bfsLayer G root i) : ℝ)
        (#(bfsLayer G root (i + 1)) : ℝ) ≤
      (#(bfsLayer G root (i + 2)) : ℝ) - 2 * (G.minDegree : ℝ) / 5 := by
  let a := #(bfsPrevLayer G root i)
  let b := #(bfsLayer G root i)
  let c := #(bfsLayer G root (i + 1))
  let d := #(bfsLayer G root (i + 2))
  by_cases had : a ≤ d
  · obtain ⟨k, hk1, hk4, hbk, hcover⟩ :=
      fourLayer_greedy_data G hconn root i 4 hBne hCne (by simpa using hfree) had
    refine k5_local_four_layer (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ)
      (G.minDegree : ℝ)
      ((a : ℝ) + b + c - G.minDegree) ((d : ℝ) - a) k
      (by positivity) (by positivity) (by positivity) (by positivity) ?_ ?_ ?_
      rfl rfl hk1 hk4 ?_ ?_
    · exact_mod_cast had
    · have hcpos : 0 < c := by simpa [c] using hCne.card_pos
      positivity
    · have hbpos : 0 < b := by simpa [b] using hBne.card_pos
      positivity
    · simpa [a, b, c, d] using hbk
    · simpa [a, b, c, d] using hcover
  · have hda : d ≤ a := by omega
    -- Apply the oriented result to the reversed four-layer window.
    -- The potential defect is invariant under reversal.
    have hrev :
        k5Potential (G.minDegree : ℝ) (c : ℝ) (b : ℝ) (a : ℝ) -
          k5Potential (G.minDegree : ℝ) (d : ℝ) (c : ℝ) (b : ℝ) ≤
          (a : ℝ) - 2 * (G.minDegree : ℝ) / 5 := by
      obtain ⟨k, hk1, hk4, hck, hcover⟩ :=
        fourLayer_greedy_data_reverse G hconn root i 4 hBne hCne
          (by simpa using hfree) hda
      refine k5_local_four_layer (d : ℝ) (c : ℝ) (b : ℝ) (a : ℝ)
        (G.minDegree : ℝ)
        ((d : ℝ) + c + b - G.minDegree) ((a : ℝ) - d) k
        (by positivity) (by positivity) (by positivity) (by positivity) ?_ ?_ ?_
        rfl rfl hk1 hk4 ?_ ?_
      · exact_mod_cast hda
      · have hbpos : 0 < b := by simpa [b] using hBne.card_pos
        positivity
      · have hcpos : 0 < c := by simpa [c] using hCne.card_pos
        positivity
      · simpa [a, b, c, d] using hck
      · simpa [a, b, c, d] using hcover
    have hid :
        ((d : ℝ) - 2 * (G.minDegree : ℝ) / 5) -
            (k5Potential (G.minDegree : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) -
              k5Potential (G.minDegree : ℝ) (a : ℝ) (b : ℝ) (c : ℝ)) =
          ((a : ℝ) - 2 * (G.minDegree : ℝ) / 5) -
            (k5Potential (G.minDegree : ℝ) (c : ℝ) (b : ℝ) (a : ℝ) -
              k5Potential (G.minDegree : ℝ) (d : ℝ) (c : ℝ) (b : ℝ)) := by
      simp only [k5Potential]
      have hbpos : (0 : ℝ) < b := by exact_mod_cast hBne.card_pos
      have hcpos : (0 : ℝ) < c := by exact_mod_cast hCne.card_pos
      field_simp
      ring
    simp only [a, b, c, d] at *
    linarith

/-- Local potential step for every four-layer window in a `K₄`-free graph. -/
theorem k4_graph_local_step
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (root : V) (i : ℕ)
    (hBne : (bfsLayer G root i).Nonempty)
    (hCne : (bfsLayer G root (i + 1)).Nonempty)
    (hfree : G.CliqueFree 4) :
    k4Potential (G.minDegree : ℝ)
        (#(bfsLayer G root i) : ℝ) (#(bfsLayer G root (i + 1)) : ℝ)
        (#(bfsLayer G root (i + 2)) : ℝ) -
      k4Potential (G.minDegree : ℝ)
        (#(bfsPrevLayer G root i) : ℝ) (#(bfsLayer G root i) : ℝ)
        (#(bfsLayer G root (i + 1)) : ℝ) ≤
      (#(bfsLayer G root (i + 2)) : ℝ) - 3 * (G.minDegree : ℝ) / 7 := by
  let a := #(bfsPrevLayer G root i)
  let b := #(bfsLayer G root i)
  let c := #(bfsLayer G root (i + 1))
  let d := #(bfsLayer G root (i + 2))
  by_cases had : a ≤ d
  · obtain ⟨k, hk1, hk3, hbk, hcover⟩ :=
      fourLayer_greedy_data G hconn root i 3 hBne hCne (by simpa using hfree) had
    refine k4_local_four_layer (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ)
      (G.minDegree : ℝ)
      ((a : ℝ) + b + c - G.minDegree) ((d : ℝ) - a) k
      (by positivity) (by positivity) (by positivity) (by positivity) ?_ ?_ ?_
      rfl rfl hk1 hk3 ?_ ?_
    · exact_mod_cast had
    · have hcpos : 0 < c := by simpa [c] using hCne.card_pos
      positivity
    · have hbpos : 0 < b := by simpa [b] using hBne.card_pos
      positivity
    · simpa [a, b, c, d] using hbk
    · simpa [a, b, c, d] using hcover
  · have hda : d ≤ a := by omega
    have hrev :
        k4Potential (G.minDegree : ℝ) (c : ℝ) (b : ℝ) (a : ℝ) -
          k4Potential (G.minDegree : ℝ) (d : ℝ) (c : ℝ) (b : ℝ) ≤
          (a : ℝ) - 3 * (G.minDegree : ℝ) / 7 := by
      obtain ⟨k, hk1, hk3, hck, hcover⟩ :=
        fourLayer_greedy_data_reverse G hconn root i 3 hBne hCne
          (by simpa using hfree) hda
      refine k4_local_four_layer (d : ℝ) (c : ℝ) (b : ℝ) (a : ℝ)
        (G.minDegree : ℝ)
        ((d : ℝ) + c + b - G.minDegree) ((a : ℝ) - d) k
        (by positivity) (by positivity) (by positivity) (by positivity) ?_ ?_ ?_
        rfl rfl hk1 hk3 ?_ ?_
      · exact_mod_cast hda
      · have hbpos : 0 < b := by simpa [b] using hBne.card_pos
        positivity
      · have hcpos : 0 < c := by simpa [c] using hCne.card_pos
        positivity
      · simpa [a, b, c, d] using hck
      · simpa [a, b, c, d] using hcover
    have hid :
        ((d : ℝ) - 3 * (G.minDegree : ℝ) / 7) -
            (k4Potential (G.minDegree : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) -
              k4Potential (G.minDegree : ℝ) (a : ℝ) (b : ℝ) (c : ℝ)) =
          ((a : ℝ) - 3 * (G.minDegree : ℝ) / 7) -
            (k4Potential (G.minDegree : ℝ) (c : ℝ) (b : ℝ) (a : ℝ) -
              k4Potential (G.minDegree : ℝ) (d : ℝ) (c : ℝ) (b : ℝ)) := by
      simp only [k4Potential]
      have hbpos : (0 : ℝ) < b := by exact_mod_cast hBne.card_pos
      have hcpos : (0 : ℝ) < c := by exact_mod_cast hCne.card_pos
      field_simp
      ring
    simp only [a, b, c, d] at *
    linarith

end Erdos612

/-!
# Fully graph-theoretic bounds for the `K₅`-free and `K₄`-free cases

Unlike the earlier kernel statements, the theorems in this file assume only
connectedness and clique-freeness.  BFS layers, the greedy complement argument,
the local inequalities, and the telescope are all internal to the proof.
-/

open scoped BigOperators Finset
open SimpleGraph

namespace Erdos612

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem sum_range_shift_two (f : ℕ → ℝ) (D : ℕ) :
    ∑ i ∈ Finset.range (D + 2), f i =
      f 0 + f 1 + ∑ i ∈ Finset.range D, f (i + 2) := by
  induction D with
  | zero => norm_num [Finset.sum_range_succ]
  | succ D ih =>
      rw [show D + 1 + 2 = (D + 2) + 1 by omega]
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
      ring

private theorem minDegree_eq_zero_of_connected_diam_eq_zero
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hdiam : G.diam = 0) : G.minDegree = 0 := by
  letI : Nonempty V := hconn.nonempty
  have htop : G.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.mp hconn
  have hsub : Subsingleton V := by
    rw [SimpleGraph.diam_eq_zero] at hdiam
    exact hdiam.resolve_left htop
  letI : Subsingleton V := hsub
  exact G.minDegree_of_subsingleton

/-- Exact `K₅`-free diameter bound.  This is the graph theorem underlying
the original `r=2` target and the amended `k=4` target. -/
theorem k5_free_exact_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hfree : G.CliqueFree 5) :
    2 * (G.minDegree : ℝ) * ((G.diam : ℝ) + 1) + 4 ≤ 5 * (Fintype.card V : ℝ) := by
  letI : Nonempty V := hconn.nonempty
  by_cases hD : G.diam = 0
  · have hδ : G.minDegree = 0 := minDegree_eq_zero_of_connected_diam_eq_zero G hconn hD
    have hn : 1 ≤ Fintype.card V := Fintype.card_pos
    have hnR : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn
    norm_num [hD, hδ]
    linarith
  · obtain ⟨root, far, p, hplen, hgeo⟩ := exists_diametral_walk G hconn
    let s : ℕ → ℝ := fun j ↦ (#(bfsLayer G root j) : ℝ)
    let P : ℕ → ℝ := fun j ↦
      k5Potential (G.minDegree : ℝ) (#(bfsPrevLayer G root j) : ℝ) (s j) (s (j + 1))
    let q : ℕ → ℝ := fun j ↦ s (j + 2) - 2 * (G.minDegree : ℝ) / 5
    have hs_nonempty : ∀ j ≤ G.diam, (bfsLayer G root j).Nonempty := by
      intro j hj
      exact bfsLayer_nonempty_of_diametral p hplen hgeo hj
    have hstep : ∀ j < G.diam, P (j + 1) - P j ≤ q j := by
      intro j hj
      have hB := hs_nonempty j (by omega)
      have hC := hs_nonempty (j + 1) (by omega)
      simpa [P, q, s, Nat.add_assoc] using k5_graph_local_step G hconn root j hB hC hfree
    have hlastLayer : bfsLayer G root (G.diam + 1) = ∅ :=
      bfsLayer_eq_empty_of_diam_lt hconn root (by omega)
    have hsLast : s (G.diam + 1) = 0 := by simp [s, hlastLayer]
    have htotalNat := sum_bfsLayer_card hconn root
    have htotal : ∑ j ∈ Finset.range (G.diam + 1), s j = (Fintype.card V : ℝ) := by
      simp only [s]
      rw [← Nat.cast_sum]
      exact_mod_cast htotalNat
    have hshift : ∑ j ∈ Finset.range G.diam, s (j + 2) =
        (Fintype.card V : ℝ) - s 0 - s 1 := by
      have hid := sum_range_shift_two s G.diam
      rw [show G.diam + 2 = (G.diam + 1) + 1 by omega, Finset.sum_range_succ,
        hsLast, add_zero, htotal] at hid
      linarith
    have hsum : ∑ j ∈ Finset.range G.diam, q j =
        (Fintype.card V : ℝ) - s 0 - s 1 - 2 * (G.minDegree : ℝ) * G.diam / 5 := by
      simp only [q, Finset.sum_sub_distrib]
      rw [hshift]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    have hs0 : s 0 = 1 := by simp [s, bfsLayer_zero hconn root]
    have hs1pos : s 1 ≠ 0 := by
      have := (hs_nonempty 1 (by omega)).card_pos
      simp only [s]
      exact_mod_cast (Nat.ne_of_gt this)
    have hsDpos : s G.diam ≠ 0 := by
      have := (hs_nonempty G.diam le_rfl).card_pos
      simp only [s]
      exact_mod_cast (Nat.ne_of_gt this)
    have hs0le : 1 ≤ s 0 := by rw [hs0]
    have hsDle : 1 ≤ s G.diam := by
      have := (hs_nonempty G.diam le_rfl).card_pos
      simp only [s]
      exact_mod_cast this
    have hprevLayer : bfsPrevLayer G root G.diam = bfsLayer G root (G.diam - 1) := by
      simp [bfsPrevLayer, hD]
    have hsPrevpos : (#(bfsLayer G root (G.diam - 1)) : ℝ) ≠ 0 := by
      have hle : G.diam - 1 ≤ G.diam := Nat.sub_le _ _
      have := (hs_nonempty (G.diam - 1) hle).card_pos
      exact_mod_cast (Nat.ne_of_gt this)
    have hP0 : P 0 = k5Potential (G.minDegree : ℝ) 0 (s 0) (s 1) := by
      simp [P, bfsPrevLayer]
    have hPD : P G.diam =
        k5Potential (G.minDegree : ℝ) (#(bfsLayer G root (G.diam - 1)) : ℝ)
          (s G.diam) 0 := by
      simp [P, hprevLayer, hsLast]
    exact k5_bfs_telescoping_with_potential G.diam (G.minDegree : ℝ)
      (Fintype.card V : ℝ) (s 0) (s 1)
      (#(bfsLayer G root (G.diam - 1)) : ℝ) (s G.diam) P q
      hstep hsum hP0 hPD hs1pos hsPrevpos hs0le hsDle

/-- Exact `K₄`-free diameter bound.  This is the graph theorem underlying
the amended `k=3` target. -/
theorem k4_free_exact_bound
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hfree : G.CliqueFree 4) :
    3 * (G.minDegree : ℝ) * ((G.diam : ℝ) + 1) + 6 ≤ 7 * (Fintype.card V : ℝ) := by
  letI : Nonempty V := hconn.nonempty
  by_cases hD : G.diam = 0
  · have hδ : G.minDegree = 0 := minDegree_eq_zero_of_connected_diam_eq_zero G hconn hD
    have hn : 1 ≤ Fintype.card V := Fintype.card_pos
    have hnR : (1 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn
    norm_num [hD, hδ]
    linarith
  · obtain ⟨root, far, p, hplen, hgeo⟩ := exists_diametral_walk G hconn
    let s : ℕ → ℝ := fun j ↦ (#(bfsLayer G root j) : ℝ)
    let P : ℕ → ℝ := fun j ↦
      k4Potential (G.minDegree : ℝ) (#(bfsPrevLayer G root j) : ℝ) (s j) (s (j + 1))
    let q : ℕ → ℝ := fun j ↦ s (j + 2) - 3 * (G.minDegree : ℝ) / 7
    have hs_nonempty : ∀ j ≤ G.diam, (bfsLayer G root j).Nonempty := by
      intro j hj
      exact bfsLayer_nonempty_of_diametral p hplen hgeo hj
    have hstep : ∀ j < G.diam, P (j + 1) - P j ≤ q j := by
      intro j hj
      have hB := hs_nonempty j (by omega)
      have hC := hs_nonempty (j + 1) (by omega)
      simpa [P, q, s, Nat.add_assoc] using k4_graph_local_step G hconn root j hB hC hfree
    have hlastLayer : bfsLayer G root (G.diam + 1) = ∅ :=
      bfsLayer_eq_empty_of_diam_lt hconn root (by omega)
    have hsLast : s (G.diam + 1) = 0 := by simp [s, hlastLayer]
    have htotalNat := sum_bfsLayer_card hconn root
    have htotal : ∑ j ∈ Finset.range (G.diam + 1), s j = (Fintype.card V : ℝ) := by
      simp only [s]
      rw [← Nat.cast_sum]
      exact_mod_cast htotalNat
    have hshift : ∑ j ∈ Finset.range G.diam, s (j + 2) =
        (Fintype.card V : ℝ) - s 0 - s 1 := by
      have hid := sum_range_shift_two s G.diam
      rw [show G.diam + 2 = (G.diam + 1) + 1 by omega, Finset.sum_range_succ,
        hsLast, add_zero, htotal] at hid
      linarith
    have hsum : ∑ j ∈ Finset.range G.diam, q j =
        (Fintype.card V : ℝ) - s 0 - s 1 - 3 * (G.minDegree : ℝ) * G.diam / 7 := by
      simp only [q, Finset.sum_sub_distrib]
      rw [hshift]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    have hs0 : s 0 = 1 := by simp [s, bfsLayer_zero hconn root]
    have hs1pos : s 1 ≠ 0 := by
      have := (hs_nonempty 1 (by omega)).card_pos
      simp only [s]
      exact_mod_cast (Nat.ne_of_gt this)
    have hsDpos : s G.diam ≠ 0 := by
      have := (hs_nonempty G.diam le_rfl).card_pos
      simp only [s]
      exact_mod_cast (Nat.ne_of_gt this)
    have hs0le : 1 ≤ s 0 := by rw [hs0]
    have hsDle : 1 ≤ s G.diam := by
      have := (hs_nonempty G.diam le_rfl).card_pos
      simp only [s]
      exact_mod_cast this
    have hprevLayer : bfsPrevLayer G root G.diam = bfsLayer G root (G.diam - 1) := by
      simp [bfsPrevLayer, hD]
    have hsPrevpos : (#(bfsLayer G root (G.diam - 1)) : ℝ) ≠ 0 := by
      have hle : G.diam - 1 ≤ G.diam := Nat.sub_le _ _
      have := (hs_nonempty (G.diam - 1) hle).card_pos
      exact_mod_cast (Nat.ne_of_gt this)
    have hP0 : P 0 = k4Potential (G.minDegree : ℝ) 0 (s 0) (s 1) := by
      simp [P, bfsPrevLayer]
    have hPD : P G.diam =
        k4Potential (G.minDegree : ℝ) (#(bfsLayer G root (G.diam - 1)) : ℝ)
          (s G.diam) 0 := by
      simp [P, hprevLayer, hsLast]
    exact k4_bfs_telescoping_with_potential G.diam (G.minDegree : ℝ)
      (Fintype.card V : ℝ) (s 0) (s 1)
      (#(bfsLayer G root (G.diam - 1)) : ℝ) (s G.diam) P q
      hstep hsum hP0 hPD hs1pos hsPrevpos hs0le hsDle

end Erdos612

/-!
# The actual Formal-Conjectures-shaped graph targets

The definitions in this file agree with the prospective statement in
`FClikeLean/FClikeLean.lean`.  The three project targets below are proved from
connectedness and clique-freeness alone; no local inequality or telescoping
hypothesis appears in their statements.
-/

open SimpleGraph

namespace Erdos612

/-- A uniform additive-constant diameter bound for connected finite graphs. -/
def HasAsymptoticDiameterBound (cliqueSize : ℕ) (coefficient : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Connected → G.CliqueFree cliqueSize →
      (G.diam : ℝ) ≤ coefficient * (n : ℝ) / (G.minDegree : ℝ) + C

/-- The same bound with a divisibility restriction on minimum degree. -/
def HasDivisibleDiameterBound (cliqueSize divisor : ℕ) (coefficient : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Connected → G.CliqueFree cliqueSize → divisor ∣ G.minDegree →
      (G.diam : ℝ) ≤ coefficient * (n : ℝ) / (G.minDegree : ℝ) + C

/-- The amended conjecture at fixed parameter `k`. -/
def AmendedConjectureAt (k : ℕ) : Prop :=
  HasAsymptoticDiameterBound (k + 1) (3 - 2 / (k : ℝ))

/-- The original odd-clique conjecture at fixed parameter `r`. -/
def OriginalOddConjectureAt (r : ℕ) : Prop :=
  HasDivisibleDiameterBound (2 * r + 1) (3 * r - 1)
    (((3 * r - 1 : ℕ) : ℝ) / (r : ℝ))

private theorem k5_diameter_ratio_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hfree : G.CliqueFree 5) :
    (G.diam : ℝ) ≤ (5 / 2 : ℝ) * (Fintype.card V : ℝ) / (G.minDegree : ℝ) := by
  classical
  by_cases hnontrivial : Nontrivial V
  · letI : Nontrivial V := hnontrivial
    have hδNat : 0 < G.minDegree := hconn.preconnected.minDegree_pos_of_nontrivial
    have hδ : (0 : ℝ) < (G.minDegree : ℝ) := by exact_mod_cast hδNat
    have hexact := k5_free_exact_bound G hconn hfree
    apply (le_div_iff₀ hδ).2
    nlinarith
  · have hsub : Subsingleton V := not_nontrivial_iff_subsingleton.mp hnontrivial
    letI : Subsingleton V := hsub
    have hdiam : G.diam = 0 := SimpleGraph.diam_eq_zero.mpr (Or.inr hsub)
    simp [hdiam]

private theorem k4_diameter_ratio_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hfree : G.CliqueFree 4) :
    (G.diam : ℝ) ≤ (7 / 3 : ℝ) * (Fintype.card V : ℝ) / (G.minDegree : ℝ) := by
  classical
  by_cases hnontrivial : Nontrivial V
  · letI : Nontrivial V := hnontrivial
    have hδNat : 0 < G.minDegree := hconn.preconnected.minDegree_pos_of_nontrivial
    have hδ : (0 : ℝ) < (G.minDegree : ℝ) := by exact_mod_cast hδNat
    have hexact := k4_free_exact_bound G hconn hfree
    apply (le_div_iff₀ hδ).2
    nlinarith
  · have hsub : Subsingleton V := not_nontrivial_iff_subsingleton.mp hnontrivial
    letI : Subsingleton V := hsub
    have hdiam : G.diam = 0 := SimpleGraph.diam_eq_zero.mpr (Or.inr hsub)
    simp [hdiam]

/-- Contribution 2: the original `K₅` target (`r = 2`). -/
theorem original_k5 : OriginalOddConjectureAt 2 := by
  unfold OriginalOddConjectureAt HasDivisibleDiameterBound
  norm_num
  refine ⟨0, ?_⟩
  intro n G _ hconn hfree _
  simpa using k5_diameter_ratio_bound G hconn hfree

/-- Contribution 3: the amended `K₄` target (`k = 3`). -/
theorem amended_k4 : AmendedConjectureAt 3 := by
  unfold AmendedConjectureAt HasAsymptoticDiameterBound
  norm_num
  refine ⟨0, ?_⟩
  intro n G _ hconn hfree
  simpa using k4_diameter_ratio_bound G hconn hfree

/-- Contribution 4: the amended `K₅` target (`k = 4`). -/
theorem amended_k5 : AmendedConjectureAt 4 := by
  unfold AmendedConjectureAt HasAsymptoticDiameterBound
  norm_num
  refine ⟨0, ?_⟩
  intro n G _ hconn hfree
  simpa using k5_diameter_ratio_bound G hconn hfree

end Erdos612

/-!
# Erdős 612: the actual Formal-Conjectures-shaped targets

These are the same graph statements as the three project targets in
`FClikeLean/FClikeLean.lean`. They quantify over every connected finite graph
with the stated forbidden clique. No local inequality, BFS sequence, potential,
or telescoping statement occurs as an assumption.
-/

syntax:max "answer(" term ")" : term

macro_rules
  | `(answer($p)) => `($p)

/-- Contribution 2: original `K₅` (`r = 2`). -/
theorem erdos_612.variants.original_k5 :
    answer(True) ↔ Erdos612.OriginalOddConjectureAt 2 := by
  rw [true_iff]
  exact Erdos612.original_k5

/-- Contribution 3: amended `K₄` (`k = 3`). -/
theorem erdos_612.variants.amended_k3 :
    answer(True) ↔ Erdos612.AmendedConjectureAt 3 := by
  rw [true_iff]
  exact Erdos612.amended_k4

/-- Contribution 4: amended `K₅` (`k = 4`). -/
theorem erdos_612.variants.amended_k4 :
    answer(True) ↔ Erdos612.AmendedConjectureAt 4 := by
  rw [true_iff]
  exact Erdos612.amended_k5

#check erdos_612.variants.original_k5
#check erdos_612.variants.amended_k3
#check erdos_612.variants.amended_k4

#print axioms Erdos612.k5_graph_local_step
#print axioms Erdos612.k4_graph_local_step
#print axioms Erdos612.k5_free_exact_bound
#print axioms Erdos612.k4_free_exact_bound
#print axioms Erdos612.original_k5
#print axioms Erdos612.amended_k4
#print axioms Erdos612.amended_k5
#print axioms erdos_612.variants.original_k5
#print axioms erdos_612.variants.amended_k3
#print axioms erdos_612.variants.amended_k4
