import AmendedK6.Targets

/-!
# Amended K₆ counterexample

The target is `¬ Erdos612.AmendedConjectureAt 5`.
The forbidden clique is `K₆`, and the proposed coefficient is `13/5`.

The development includes the graph construction and proofs of connectedness,
`K₆`-freeness, minimum degree, and the required diameter lower bound.
-/

#check Erdos612.amended_k5_refuted

-- Finite-data and arithmetic checks.
#check Erdos612AmendedK6.period_order
#check Erdos612AmendedK6.localDegree_ge_2200
#check Erdos612AmendedK6.vertex_card
#check Erdos612AmendedK6.excess_identity
#print axioms Erdos612AmendedK6.localDegree_ge_2200
#print axioms Erdos612AmendedK6.excess_identity

-- Audit the axioms of the final target (in particular, no `sorryAx`).
#print axioms Erdos612.amended_k5_refuted
