import Erdos612.Conjectures

/-!
# Target specialization

The conjecture definitions are imported from `Erdos612.Conjectures`; those
definitions agree with the prospective statement in `FClikeLean/FClikeLean.lean`.
This module records the numerical specialization needed by the counterexample.

Here `k = 5` corresponds to forbidden clique `K₆`. The target is
`¬ AmendedConjectureAt 5`; `AmendedConjectureAt 6` is the `K₇` case.
-/

namespace Erdos612

/-- Substituting `k = 5` gives forbidden clique size 6 and coefficient `13/5`. -/
theorem amended_k5_iff :
    AmendedConjectureAt 5 ↔ HasAsymptoticDiameterBound 6 (13 / 5) := by
  norm_num [AmendedConjectureAt]

end Erdos612
