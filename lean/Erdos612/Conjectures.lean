import Erdos612.GraphTheorems

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
