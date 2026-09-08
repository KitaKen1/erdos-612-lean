import K7Counterexample.Results

/-!
This is the root module for the formalized `K₇` counterexample family for
Erdős Problem 612.
-/

#check Erdos612K7.vertex_card
#check Erdos612K7.graph_connected
#check Erdos612K7.graph_cliqueFree_seven
#check Erdos612K7.minDegree_eq_800
#check Erdos612K7.diameter_lower_bound
#check Erdos612K7.counterexample_family
#check Erdos612K7.graph_gap_exceeds_every_nat_constant
#check Erdos612K7.no_natural_additive_constant
#check Erdos612K7.no_real_additive_constant
#check Erdos612K7.not_originalK7BoundOnFin
#check Erdos612K7.not_amendedK7BoundOnFin
#check Erdos612.original_k7_refuted
#check Erdos612.amended_k6_refuted

#print axioms Erdos612K7.counterexample_family
#print axioms Erdos612.original_k7_refuted
#print axioms Erdos612.amended_k6_refuted
