import Erdos612.GraphLocal
import Erdos612.Main
import Mathlib.Algebra.BigOperators.Ring.Finset

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
