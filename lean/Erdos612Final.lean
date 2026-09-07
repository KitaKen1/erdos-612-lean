import Erdos612.Conjectures

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
