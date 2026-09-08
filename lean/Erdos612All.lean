import Erdos612Final
import K7Counterexample
import AmendedK6

/-!
# Erdős Problem 612: all proved and refuted targets

This root module collects the three previously published positive targets and
the three new refuted targets. Each statement is the full finite-graph
conjecture, with no unproved graph-theoretic assumptions added to its type.
-/

/-- New target 1: the original `r = 3` (`K₇`-free) case is false. -/
theorem erdos_612.variants.original_k7 :
    answer(False) ↔ Erdos612.OriginalOddConjectureAt 3 := by
  constructor
  · intro h
    exact h.elim
  · exact Erdos612.original_k7_refuted

/-- New target 2: the amended `k = 5` (`K₆`-free) case is false. -/
theorem erdos_612.variants.amended_k5 :
    answer(False) ↔ Erdos612.AmendedConjectureAt 5 := by
  constructor
  · intro h
    exact h.elim
  · exact Erdos612.amended_k5_refuted

/-- New target 3: the amended `k = 6` (`K₇`-free) case is false. -/
theorem erdos_612.variants.amended_k6 :
    answer(False) ↔ Erdos612.AmendedConjectureAt 6 := by
  constructor
  · intro h
    exact h.elim
  · exact Erdos612.amended_k6_refuted

#check erdos_612.variants.original_k5
#check erdos_612.variants.amended_k3
#check erdos_612.variants.amended_k4
#check erdos_612.variants.original_k7
#check erdos_612.variants.amended_k5
#check erdos_612.variants.amended_k6

#print axioms Erdos612.original_k7_refuted
#print axioms Erdos612.amended_k5_refuted
#print axioms Erdos612.amended_k6_refuted
#print axioms erdos_612.variants.original_k7
#print axioms erdos_612.variants.amended_k5
#print axioms erdos_612.variants.amended_k6
