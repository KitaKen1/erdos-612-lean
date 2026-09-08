import AmendedK6.Data

/-!
# Diverging excess calculation

This calculation is independent of the graph-theoretic lemmas.
The minimum degree is fixed at 2200 while `m` grows.
-/

namespace Erdos612AmendedK6

/-- The algebraic identity for the excess over the proposed main term. -/
theorem excess_identity (m : ℕ) :
    (diameterLower m : ℝ) - (13 / 5 : ℝ) * (order m : ℝ) / 2200 =
      (m : ℝ) / 11000 - 37 / 5 := by
  unfold diameterLower order
  push_cast
  ring

/-- An explicit number of periods whose excess is larger than any given `N`. -/
theorem excess_exceeds_nat (N : ℕ) :
    let m := 11000 * (N + 8)
    (N : ℝ) <
      (diameterLower m : ℝ) - (13 / 5 : ℝ) * (order m : ℝ) / 2200 := by
  dsimp only
  rw [excess_identity]
  push_cast
  linarith

end Erdos612AmendedK6
