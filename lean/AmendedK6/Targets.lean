import AmendedK6.Conjecture
import AmendedK6.Graph
import AmendedK6.Arithmetic

/-!
# Final target: refuting the amended K₆ case

This file uses the constructed graph to refute the amended `K₆` case.
The final theorem has no additional local-inequality or telescoping assumptions.
-/

namespace Erdos612

open Erdos612AmendedK6
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Final target: the amended `k = 5` (`K₆`-free) conjecture is false. -/
theorem amended_k5_refuted : ¬ AmendedConjectureAt 5 := by
  intro h
  rcases amended_k5_iff.mp h with ⟨C, hC⟩
  obtain ⟨N : ℕ, hCN⟩ := exists_nat_ge C
  let m := 11000 * (N + 8)
  have hm : 0 < m := by simp [m]
  have hupper := hC (order m) (graphFin m)
    (graphFin_connected hm) (graphFin_cliqueFree_six m)
  simp only [graphFin_minDegree hm] at hupper
  have hdiam : (diameterLower m : ℝ) ≤ ((graphFin m).diam : ℝ) := by
    exact_mod_cast graphFin_diameter_lower hm
  have hgap : (N : ℝ) <
      (diameterLower m : ℝ) - (13 / 5 : ℝ) * (order m : ℝ) / 2200 :=
    excess_exceeds_nat N
  linarith

end Erdos612
