import K7Counterexample.Data

namespace Erdos612K7

def counterexampleOrder (p : ℕ) : ℕ := 21296 * p + 960
def counterexampleDiameter (p : ℕ) : ℕ := 71 * p + 1
def counterexampleMinDegree : ℕ := 800

theorem minDegree_divisible_by_eight : 8 ∣ counterexampleMinDegree := by
  norm_num [counterexampleMinDegree]

/-- The exact excess over the proposed original `K₇` main term. -/
theorem exact_gap (p : ℕ) :
    (counterexampleDiameter p : ℚ)
        - (8 / 3 : ℚ) * (counterexampleOrder p : ℚ) / counterexampleMinDegree
      = (p : ℚ) / 75 - 11 / 5 := by
  norm_num [counterexampleDiameter, counterexampleOrder, counterexampleMinDegree]
  ring

/-- No additive constant can repair the proposed bound: this explicit choice
of `p` makes the excess larger than the prescribed natural constant `C`. -/
theorem gap_exceeds_every_constant (C : ℕ) :
    (C : ℚ) <
      (counterexampleDiameter (75 * (C + 3)) : ℚ)
        - (8 / 3 : ℚ) *
            (counterexampleOrder (75 * (C + 3)) : ℚ) / counterexampleMinDegree := by
  rw [exact_gap]
  push_cast
  norm_num
  linarith

end Erdos612K7
