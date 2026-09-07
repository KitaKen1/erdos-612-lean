import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Push
import Aesop
import Lean.Elab.Tactic.Omega

/-!
# A greedy clique-covering lemma

For a graph with no `(m+1)`-clique, two disjoint vertex blocks `B,C` are
covered by closed non-neighbourhoods of at most `m` vertices.  Maximising first
inside `B` records how many of the covering vertices use the sharper `B` bound.
This is the combinatorial input to the four-layer inequalities.
-/

open scoped BigOperators Finset
open SimpleGraph

namespace Erdos612

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertices of `U` equal or nonadjacent to `v`.  This is the closed
neighbourhood of `v` in the complement of the graph induced on `U`. -/
def closedNonneighborFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (v : V) : Finset V :=
  U.filter fun w ↦ w = v ∨ ¬ G.Adj v w

@[simp]
theorem mem_closedNonneighborFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (v w : V) :
    w ∈ closedNonneighborFinset G U v ↔ w ∈ U ∧ (w = v ∨ ¬ G.Adj v w) := by
  simp [closedNonneighborFinset]

/-- A finite vertex set contains a clique of maximum cardinality among its
clique subsets. -/
theorem exists_maximum_clique_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) :
    ∃ S : Finset V, S ⊆ U ∧ G.IsClique (S : Set V) ∧
      ∀ T : Finset V, T ⊆ U → G.IsClique (T : Set V) → #T ≤ #S := by
  classical
  let candidates := U.powerset.filter fun S : Finset V ↦ G.IsClique (S : Set V)
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, SimpleGraph.isClique_empty]
  obtain ⟨S, hS, hmax⟩ := candidates.exists_max_image Finset.card hcandidates
  have hSmem : S ⊆ U ∧ G.IsClique (S : Set V) := by
    simpa [candidates] using hS
  refine ⟨S, hSmem.1, hSmem.2, ?_⟩
  intro T hTU hTc
  exact hmax T (by simpa [candidates] using ⟨hTU, hTc⟩)

/-- A clique inside `U` can be extended to one of maximum size among the
cliques inside `U` that contain it. -/
theorem exists_maximum_clique_extension (G : SimpleGraph V) [DecidableRel G.Adj]
    (U S : Finset V) (hSU : S ⊆ U) (hSc : G.IsClique (S : Set V)) :
    ∃ T : Finset V, S ⊆ T ∧ T ⊆ U ∧ G.IsClique (T : Set V) ∧
      ∀ R : Finset V, S ⊆ R → R ⊆ U → G.IsClique (R : Set V) → #R ≤ #T := by
  classical
  let candidates := U.powerset.filter fun T ↦ S ⊆ T ∧ G.IsClique (T : Set V)
  have hcandidates : candidates.Nonempty := by
    refine ⟨S, ?_⟩
    simp [candidates, hSU, hSc]
  obtain ⟨T, hT, hmax⟩ := candidates.exists_max_image Finset.card hcandidates
  have hTmem : T ⊆ U ∧ S ⊆ T ∧ G.IsClique (T : Set V) := by
    simpa [candidates] using hT
  refine ⟨T, hTmem.2.1, hTmem.1, hTmem.2.2, ?_⟩
  intro R hSR hRU hRc
  exact hmax R (by simpa [candidates] using ⟨hRU, hSR, hRc⟩)

/-- A maximum-cardinality clique in `U` covers `U` by its closed
non-neighbourhoods. -/
theorem subset_biUnion_closedNonneighbor_of_maximum
    (G : SimpleGraph V) [DecidableRel G.Adj] (U S : Finset V)
    (hSU : S ⊆ U) (hSc : G.IsClique (S : Set V))
    (hmax : ∀ T : Finset V, T ⊆ U → G.IsClique (T : Set V) → #T ≤ #S) :
    U ⊆ S.biUnion (closedNonneighborFinset G U) := by
  classical
  intro x hxU
  by_cases hxS : x ∈ S
  · exact Finset.mem_biUnion.mpr ⟨x, hxS, by simp [hxU]⟩
  · have hinsertU : insert x S ⊆ U := by simpa [Finset.insert_subset_iff] using ⟨hxU, hSU⟩
    have hnotClique : ¬ G.IsClique ((insert x S : Finset V) : Set V) := by
      intro hcl
      have hcard := hmax (insert x S) hinsertU hcl
      simp [hxS] at hcard
    have hnotCliqueSet : ¬ G.IsClique (insert x (S : Set V)) := by
      simpa using hnotClique
    rw [SimpleGraph.isClique_insert_of_notMem (by simpa using hxS)] at hnotCliqueSet
    simp only [hSc, true_and] at hnotCliqueSet
    push_neg at hnotCliqueSet
    obtain ⟨y, hyS, hxy⟩ := hnotCliqueSet
    exact Finset.mem_biUnion.mpr ⟨y, hyS, by
      rw [mem_closedNonneighborFinset]
      exact ⟨hxU, Or.inr (fun hyx ↦ hxy hyx.symm)⟩⟩

/-- The same covering fact for a clique that is maximum among the cliques in
`U` containing a fixed base clique. -/
theorem subset_biUnion_closedNonneighbor_of_extension_maximum
    (G : SimpleGraph V) [DecidableRel G.Adj] (U S T : Finset V)
    (hST : S ⊆ T) (hTU : T ⊆ U) (hTc : G.IsClique (T : Set V))
    (hmax : ∀ R : Finset V, S ⊆ R → R ⊆ U →
      G.IsClique (R : Set V) → #R ≤ #T) :
    U ⊆ T.biUnion (closedNonneighborFinset G U) := by
  classical
  intro x hxU
  by_cases hxT : x ∈ T
  · exact Finset.mem_biUnion.mpr ⟨x, hxT, by simp [hxU]⟩
  · have hinsertU : insert x T ⊆ U := by
      simpa [Finset.insert_subset_iff] using ⟨hxU, hTU⟩
    have hSinsert : S ⊆ insert x T := hST.trans (Finset.subset_insert x T)
    have hnotClique : ¬ G.IsClique ((insert x T : Finset V) : Set V) := by
      intro hcl
      have hcard := hmax (insert x T) hSinsert hinsertU hcl
      simp [hxT] at hcard
    have hnotCliqueSet : ¬ G.IsClique (insert x (T : Set V)) := by
      simpa using hnotClique
    rw [SimpleGraph.isClique_insert_of_notMem (by simpa using hxT)] at hnotCliqueSet
    simp only [hTc, true_and] at hnotCliqueSet
    push_neg at hnotCliqueSet
    obtain ⟨y, hyT, hxy⟩ := hnotCliqueSet
    exact Finset.mem_biUnion.mpr ⟨y, hyT, by
      rw [mem_closedNonneighborFinset]
      exact ⟨hxU, Or.inr (fun hyx ↦ hxy hyx.symm)⟩⟩

/-- Two-block greedy covering inequality.  `t` bounds closed
non-neighbourhoods centred in `B`, while `u` bounds those centred in `C`. -/
theorem cliqueFree_greedy_cover
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B C : Finset V) (m t u : ℕ)
    (hBC : Disjoint B C) (hBne : B.Nonempty)
    (hfree : G.CliqueFree (m + 1))
    (hBt : ∀ v ∈ B, #(closedNonneighborFinset G (B ∪ C) v) ≤ t)
    (hCu : ∀ v ∈ C, #(closedNonneighborFinset G (B ∪ C) v) ≤ u) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧ #B ≤ k * t ∧ #(B ∪ C) ≤ k * t + (m - k) * u := by
  classical
  obtain ⟨S, hSB, hSc, hSmax⟩ := exists_maximum_clique_subset G B
  obtain ⟨T, hST, hTU, hTc, hTmax⟩ :=
    exists_maximum_clique_extension G (B ∪ C) S (hSB.trans Finset.subset_union_left) hSc
  have hS_inter : T ∩ B = S := by
    have hsub : S ⊆ T ∩ B := by
      intro x hxS
      exact Finset.mem_inter.mpr ⟨hST hxS, hSB hxS⟩
    have hcard : #(T ∩ B) ≤ #S :=
      hSmax (T ∩ B) Finset.inter_subset_right
        (hTc.subset (by simpa using (Finset.inter_subset_left : T ∩ B ⊆ T)))
    exact (Finset.eq_of_subset_of_card_le hsub hcard).symm
  have hSpos : 1 ≤ #S := by
    obtain ⟨x, hxB⟩ := hBne
    have hxcl : G.IsClique (({x} : Finset V) : Set V) := by
      simpa using (SimpleGraph.isClique_singleton (G := G) x)
    have hxcard := hSmax {x} (by simpa using hxB) hxcl
    simpa using hxcard
  have hTcard : #T ≤ m := by
    by_contra h
    have hm1 : m + 1 ≤ #T := by omega
    obtain ⟨R, hRT, hRcard⟩ := Finset.exists_subset_card_eq hm1
    exact hfree R ⟨hTc.subset (by simpa using hRT), hRcard⟩
  have hScard : #S ≤ m := (Finset.card_le_card hST).trans hTcard
  have hBcover : B ⊆ S.biUnion (closedNonneighborFinset G B) :=
    subset_biUnion_closedNonneighbor_of_maximum G B S hSB hSc hSmax
  have hbad_mono (v : V) :
      closedNonneighborFinset G B v ⊆ closedNonneighborFinset G (B ∪ C) v := by
    intro x hx
    rw [mem_closedNonneighborFinset] at hx ⊢
    exact ⟨Finset.mem_union_left C hx.1, hx.2⟩
  have hBcard : #B ≤ #S * t := by
    calc
      #B ≤ #(S.biUnion (closedNonneighborFinset G B)) := Finset.card_le_card hBcover
      _ ≤ ∑ v ∈ S, #(closedNonneighborFinset G B v) := Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ S, t := by
        apply Finset.sum_le_sum
        intro v hv
        exact (Finset.card_le_card (hbad_mono v)).trans (hBt v (hSB hv))
      _ = #S * t := by simp
  have hUcover : B ∪ C ⊆ T.biUnion (closedNonneighborFinset G (B ∪ C)) := by
    exact subset_biUnion_closedNonneighbor_of_extension_maximum
      G (B ∪ C) S T hST hTU hTc hTmax
  have hrestC : T \ S ⊆ C := by
    intro x hx
    have hxT := (Finset.mem_sdiff.mp hx).1
    have hxS := (Finset.mem_sdiff.mp hx).2
    rcases Finset.mem_union.mp (hTU hxT) with hxB | hxC
    · have : x ∈ S := by
        rw [← hS_inter]
        exact Finset.mem_inter.mpr ⟨hxT, hxB⟩
      exact False.elim (hxS this)
    · exact hxC
  have hsumS :
      (∑ v ∈ S, #(closedNonneighborFinset G (B ∪ C) v)) ≤ #S * t := by
    calc
      _ ≤ ∑ _v ∈ S, t := by
        apply Finset.sum_le_sum
        intro v hv
        exact hBt v (hSB hv)
      _ = #S * t := by simp
  have hsumRest :
      (∑ v ∈ T \ S, #(closedNonneighborFinset G (B ∪ C) v)) ≤ #(T \ S) * u := by
    calc
      _ ≤ ∑ _v ∈ T \ S, u := by
        apply Finset.sum_le_sum
        intro v hv
        exact hCu v (hrestC hv)
      _ = #(T \ S) * u := by simp
  have hsumT :
      (∑ v ∈ T, #(closedNonneighborFinset G (B ∪ C) v))
        ≤ #S * t + #(T \ S) * u := by
    calc
      _ = (∑ v ∈ T \ S, #(closedNonneighborFinset G (B ∪ C) v)) +
            ∑ v ∈ S, #(closedNonneighborFinset G (B ∪ C) v) :=
        (Finset.sum_sdiff hST).symm
      _ = (∑ v ∈ S, #(closedNonneighborFinset G (B ∪ C) v)) +
            ∑ v ∈ T \ S, #(closedNonneighborFinset G (B ∪ C) v) := by ac_rfl
      _ ≤ #S * t + #(T \ S) * u := Nat.add_le_add hsumS hsumRest
  have hrestcard : #(T \ S) ≤ m - #S := by
    rw [Finset.card_sdiff_of_subset hST]
    exact Nat.sub_le_sub_right hTcard #S
  have hUcard : #(B ∪ C) ≤ #S * t + (m - #S) * u := by
    calc
      #(B ∪ C) ≤ #(T.biUnion (closedNonneighborFinset G (B ∪ C))) :=
        Finset.card_le_card hUcover
      _ ≤ ∑ v ∈ T, #(closedNonneighborFinset G (B ∪ C) v) :=
        Finset.card_biUnion_le
      _ ≤ #S * t + #(T \ S) * u := hsumT
      _ ≤ #S * t + (m - #S) * u := Nat.add_le_add_left (Nat.mul_le_mul_right u hrestcard) _
  exact ⟨#S, hSpos, hScard, hBcard, hUcard⟩

end Erdos612
