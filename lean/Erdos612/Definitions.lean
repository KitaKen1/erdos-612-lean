import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

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
