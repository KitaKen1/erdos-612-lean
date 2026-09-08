import K7Counterexample.Arithmetic
import K7Counterexample.Graph
import Erdos612.Conjectures

/-!
# The verified K₇ counterexample family

This file assembles the separately checked finite table, graph construction,
clique-free proof, degree calculation, and diameter estimate.
-/

namespace Erdos612K7

/-- The complete graph-theoretic certificate for every positive number of
repeated 71-layer blocks. -/
theorem counterexample_family (p : ℕ) (hp : 0 < p) :
    (graph p).Connected ∧
    (graph p).CliqueFree 7 ∧
    (graph p).minDegree = 800 ∧
    Fintype.card (Vertex p) = 21296 * p + 960 ∧
    71 * p + 1 ≤ (graph p).diam := by
  exact ⟨graph_connected hp, graph_cliqueFree_seven p, minDegree_eq_800 hp,
    vertex_card p, diameter_lower_bound hp⟩

/-- For the actual graphs, the excess over the proposed original K₇ main
term is larger than every prescribed natural additive constant. -/
theorem graph_gap_exceeds_every_nat_constant (C : ℕ) :
    let p := 75 * (C + 3)
    (C : ℚ) <
      ((graph p).diam : ℚ) -
        (8 / 3 : ℚ) * (Fintype.card (Vertex p) : ℚ) /
          ((graph p).minDegree : ℚ) := by
  dsimp only
  let p := 75 * (C + 3)
  have hp : 0 < p := by simp [p]
  have hdiam : counterexampleDiameter p ≤ (graph p).diam := by
    simpa [counterexampleDiameter] using diameter_lower_bound hp
  have hdiamQ : (counterexampleDiameter p : ℚ) ≤ ((graph p).diam : ℚ) := by
    exact_mod_cast hdiam
  have hgap := gap_exceeds_every_constant C
  have hcalc :
      (C : ℚ) <
        ((graph p).diam : ℚ) -
          (8 / 3 : ℚ) * (counterexampleOrder p : ℚ) / counterexampleMinDegree :=
    hgap.trans_le (sub_le_sub_right hdiamQ _)
  rw [minDegree_eq_800 hp, vertex_card]
  simpa [p, counterexampleOrder, counterexampleMinDegree] using hcalc

/-- Consequently there is no natural-number additive constant that makes the
original K₇ asymptotic bound hold on this family. -/
theorem no_natural_additive_constant :
    ¬ ∃ C : ℕ, ∀ p : ℕ, 0 < p →
      ((graph p).diam : ℚ) ≤
        (8 / 3 : ℚ) * (Fintype.card (Vertex p) : ℚ) /
          ((graph p).minDegree : ℚ) + C := by
  rintro ⟨C, hC⟩
  let p := 75 * (C + 3)
  have hp : 0 < p := by simp [p]
  have hupper := hC p hp
  have hlower := graph_gap_exceeds_every_nat_constant C
  dsimp only at hlower
  change (C : ℚ) <
    ((graph p).diam : ℚ) -
      (8 / 3 : ℚ) * (Fintype.card (Vertex p) : ℚ) /
        ((graph p).minDegree : ℚ) at hlower
  linarith

/-- The actual `O(1)` quantifier uses a real constant; this family defeats
that formulation as well. -/
theorem no_real_additive_constant :
    ¬ ∃ C : ℝ, ∀ p : ℕ, 0 < p →
      ((graph p).diam : ℝ) ≤
        (8 / 3 : ℝ) * (Fintype.card (Vertex p) : ℝ) /
          ((graph p).minDegree : ℝ) + C := by
  rintro ⟨C, hC⟩
  obtain ⟨N : ℕ, hCN⟩ := exists_nat_ge C
  let p := 75 * (N + 3)
  have hp : 0 < p := by simp [p]
  have hupper := hC p hp
  have hdiam : counterexampleDiameter p ≤ (graph p).diam := by
    simpa [counterexampleDiameter] using diameter_lower_bound hp
  have hdiamR : (counterexampleDiameter p : ℝ) ≤ ((graph p).diam : ℝ) := by
    exact_mod_cast hdiam
  have hbase : (N : ℝ) <
      (counterexampleDiameter p : ℝ) -
        (8 / 3 : ℝ) * (counterexampleOrder p : ℝ) / counterexampleMinDegree := by
    dsimp [p, counterexampleDiameter, counterexampleOrder, counterexampleMinDegree]
    push_cast
    norm_num
    linarith
  have hcalc : (N : ℝ) <
      ((graph p).diam : ℝ) -
        (8 / 3 : ℝ) * (counterexampleOrder p : ℝ) / counterexampleMinDegree :=
    hbase.trans_le (sub_le_sub_right hdiamR _)
  have hlowerR : (N : ℝ) <
      ((graph p).diam : ℝ) -
        (8 / 3 : ℝ) * (Fintype.card (Vertex p) : ℝ) /
          ((graph p).minDegree : ℝ) := by
    rw [minDegree_eq_800 hp, vertex_card]
    simpa [counterexampleOrder, counterexampleMinDegree] using hcalc
  linarith

/-! ## The exact `Fin n` formulation used by the Formal Conjectures draft -/

noncomputable def vertexEquivFin (p : ℕ) :
    Vertex p ≃ Fin (Fintype.card (Vertex p)) := Fintype.equivFin _

noncomputable def graphFin (p : ℕ) :
    SimpleGraph (Fin (Fintype.card (Vertex p))) :=
  (graph p).map (vertexEquivFin p).toEmbedding

noncomputable def graphIsoFin (p : ℕ) : graph p ≃g graphFin p :=
  SimpleGraph.Iso.map (vertexEquivFin p) (graph p)

noncomputable instance graphFin_decidableAdj (p : ℕ) :
    DecidableRel (graphFin p).Adj := Classical.decRel _

theorem graphFin_connected {p : ℕ} (hp : 0 < p) : (graphFin p).Connected :=
  (graphIsoFin p).connected_iff.mp (graph_connected hp)

theorem graphFin_cliqueFree_seven (p : ℕ) : (graphFin p).CliqueFree 7 := by
  letI : Nonempty (Vertex p) := ⟨leftHub p⟩
  rw [graphFin, SimpleGraph.cliqueFree_map_iff]
  exact graph_cliqueFree_seven p

theorem graphFin_minDegree_eq_800 {p : ℕ} (hp : 0 < p) :
    (graphFin p).minDegree = 800 := by
  rw [← (graphIsoFin p).minDegree_eq]
  exact minDegree_eq_800 hp

theorem graphFin_endpoint_dist_lower_bound {p : ℕ} (hp : 0 < p) :
    71 * p + 1 ≤
      (graphFin p).dist
        (vertexEquivFin p (leftHub p)) (vertexEquivFin p (rightHub p)) := by
  obtain ⟨W, hW⟩ := (graphFin_connected hp).exists_walk_length_eq_dist
    (vertexEquivFin p (leftHub p)) (vertexEquivFin p (rightHub p))
  let W' := W.map (graphIsoFin p).symm.toHom
  have hleft :
      (graphIsoFin p).symm.toHom (vertexEquivFin p (leftHub p)) = leftHub p := by
    change (vertexEquivFin p).symm (vertexEquivFin p (leftHub p)) = leftHub p
    exact (vertexEquivFin p).symm_apply_apply (leftHub p)
  have hright :
      (graphIsoFin p).symm.toHom (vertexEquivFin p (rightHub p)) = rightHub p := by
    change (vertexEquivFin p).symm (vertexEquivFin p (rightHub p)) = rightHub p
    exact (vertexEquivFin p).symm_apply_apply (rightHub p)
  have hW' :
      Nat.dist (layerPos (leftHub p)) (layerPos (rightHub p)) ≤ W'.length :=
    by
      simpa only [hleft, hright] using walk_layer_dist_le_length W'
  calc
    71 * p + 1 = Nat.dist (layerPos (leftHub p)) (layerPos (rightHub p)) := by
      simp [Nat.dist]
    _ ≤ W'.length := hW'
    _ = W.length := by simp [W']
    _ = (graphFin p).dist
          (vertexEquivFin p (leftHub p)) (vertexEquivFin p (rightHub p)) := hW

theorem graphFin_diameter_lower_bound {p : ℕ} (hp : 0 < p) :
    71 * p + 1 ≤ (graphFin p).diam := by
  have hc := graphFin_connected hp
  letI : Nonempty (Fin (Fintype.card (Vertex p))) := hc.nonempty
  have htop : (graphFin p).ediam ≠ ⊤ :=
    (SimpleGraph.connected_iff_ediam_ne_top).mp hc
  exact (graphFin_endpoint_dist_lower_bound hp).trans (SimpleGraph.dist_le_diam htop)

/-- This is the original `r = 3` (`K₇`-free) statement, written exactly with
graphs on `Fin n` as in the prospective Formal Conjectures definition. -/
abbrev OriginalK7BoundOnFin : Prop := Erdos612.OriginalOddConjectureAt 3

/-- The constructed family formally refutes the exact `Fin n` version of the
original K₇ conjecture.  The same graphs also refute the amended `k = 6`
target, whose coefficient is again `8/3` and which has no divisibility
assumption. -/
theorem not_originalK7BoundOnFin : ¬OriginalK7BoundOnFin := by
  rintro ⟨C, hC⟩
  obtain ⟨N : ℕ, hCN⟩ := exists_nat_ge C
  let p := 75 * (N + 3)
  have hp : 0 < p := by simp [p]
  have hconn := graphFin_connected hp
  have hfree := graphFin_cliqueFree_seven p
  have hmin := graphFin_minDegree_eq_800 hp
  have hdiv : 8 ∣ (graphFin p).minDegree := by rw [hmin]; norm_num
  have hupper := hC (Fintype.card (Vertex p)) (graphFin p) hconn hfree hdiv
  have hcardR : (Fintype.card (Vertex p) : ℝ) = (21296 * p + 960 : ℕ) := by
    exact_mod_cast vertex_card p
  rw [hmin, hcardR] at hupper
  push_cast at hupper
  have hdiam := graphFin_diameter_lower_bound hp
  have hdiamR : (71 * p + 1 : ℝ) ≤ ((graphFin p).diam : ℝ) := by
    exact_mod_cast hdiam
  have hgap : (N : ℝ) <
      (71 * p + 1 : ℝ) - (8 / 3 : ℝ) * (21296 * p + 960 : ℝ) / 800 := by
    dsimp [p]
    push_cast
    norm_num
    linarith
  linarith

/-- The amended `k = 6` statement (equivalently, the amended forbidden-`K₇`
case) has the same `8/3` coefficient and drops the divisibility restriction. -/
def AmendedK7BoundOnFin : Prop :=
  ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.Connected → G.CliqueFree 7 →
      (G.diam : ℝ) ≤ (8 / 3 : ℝ) * (n : ℝ) / (G.minDegree : ℝ) + C

theorem not_amendedK7BoundOnFin : ¬AmendedK7BoundOnFin := by
  rintro ⟨C, hC⟩
  apply not_originalK7BoundOnFin
  refine ⟨C, ?_⟩
  intro n G _ hconn hfree _
  exact hC n G hconn hfree

end Erdos612K7

namespace Erdos612

/-- Main target: the original `r = 3` (`K₇`-free) conjecture is false. -/
theorem original_k7_refuted : ¬OriginalOddConjectureAt 3 :=
  Erdos612K7.not_originalK7BoundOnFin

/-- Main target: the amended `k = 6` (`K₇`-free) conjecture is false. -/
theorem amended_k6_refuted : ¬AmendedConjectureAt 6 := by
  intro h
  apply Erdos612K7.not_amendedK7BoundOnFin
  norm_num [AmendedConjectureAt, HasAsymptoticDiameterBound] at h ⊢
  exact h

end Erdos612
