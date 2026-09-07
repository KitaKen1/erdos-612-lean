import Erdos612.BFS
import Erdos612.Local
import Mathlib.Tactic.NormNum

/-!
# From clique-free BFS windows to the local potential inequalities
-/

open scoped BigOperators Finset
open SimpleGraph

namespace Erdos612

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem card_three_union_le (A B C : Finset V) :
    #(A ∪ B ∪ C) ≤ #A + #B + #C := by
  calc
    #(A ∪ B ∪ C) ≤ #(A ∪ B) + #C := Finset.card_union_le _ _
    _ ≤ (#A + #B) + #C := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ = #A + #B + #C := rfl

/-- Numerical data supplied by the clique-free greedy lemma for an oriented
four-layer BFS window. -/
theorem fourLayer_greedy_data
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (root : V) (i m : ℕ)
    (hBne : (bfsLayer G root i).Nonempty)
    (hCne : (bfsLayer G root (i + 1)).Nonempty)
    (hfree : G.CliqueFree (m + 1))
    (horient : #(bfsPrevLayer G root i) ≤ #(bfsLayer G root (i + 2))) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧
      ((#(bfsLayer G root i) : ℕ) : ℝ) ≤
        (k : ℝ) *
          (((#(bfsPrevLayer G root i) : ℕ) : ℝ) +
            ((#(bfsLayer G root i) : ℕ) : ℝ) +
            ((#(bfsLayer G root (i + 1)) : ℕ) : ℝ) - (G.minDegree : ℝ)) ∧
      0 ≤ (m : ℝ) *
          (((#(bfsPrevLayer G root i) : ℕ) : ℝ) +
            ((#(bfsLayer G root i) : ℕ) : ℝ) +
            ((#(bfsLayer G root (i + 1)) : ℕ) : ℝ) - (G.minDegree : ℝ)) +
        ((m : ℝ) - (k : ℝ)) *
          (((#(bfsLayer G root (i + 2)) : ℕ) : ℝ) -
            ((#(bfsPrevLayer G root i) : ℕ) : ℝ)) -
        ((#(bfsLayer G root i) : ℕ) : ℝ) -
        ((#(bfsLayer G root (i + 1)) : ℕ) : ℝ) := by
  classical
  let A := bfsPrevLayer G root i
  let B := bfsLayer G root i
  let C := bfsLayer G root (i + 1)
  let R := bfsLayer G root (i + 2)
  let Wₗ := A ∪ B ∪ C
  let Wᵣ := B ∪ C ∪ R
  let t := #A + #B + #C - G.minDegree
  let u := #B + #C + #R - G.minDegree
  have hBU : B ∪ C ⊆ Wₗ := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxB | hxC
    · exact Finset.mem_union_left C (Finset.mem_union_right A hxB)
    · exact Finset.mem_union_right (A ∪ B) hxC
  have hCU : B ∪ C ⊆ Wᵣ := Finset.subset_union_left
  have hBt : ∀ v ∈ B, #(closedNonneighborFinset G (B ∪ C) v) ≤ t := by
    intro v hv
    have hbad := closedNonneighbor_card_le_of_neighbor_subset G (B ∪ C) Wₗ v hBU
      (by simpa [Wₗ, A, B, C] using neighborFinset_subset_left_three G root i hv)
    have hW : #Wₗ ≤ #A + #B + #C := by
      simpa [Wₗ] using card_three_union_le A B C
    have hdeg := G.minDegree_le_degree v
    simp only [t]
    omega
  have hCu : ∀ v ∈ C, #(closedNonneighborFinset G (B ∪ C) v) ≤ u := by
    intro v hv
    have hbad := closedNonneighbor_card_le_of_neighbor_subset G (B ∪ C) Wᵣ v hCU
      (by simpa [Wᵣ, B, C, R, Nat.add_assoc] using
        neighborFinset_subset_right_three G root i hv)
    have hW : #Wᵣ ≤ #B + #C + #R := by
      simpa [Wᵣ] using card_three_union_le B C R
    have hdeg := G.minDegree_le_degree v
    simp only [u]
    omega
  have hBC : Disjoint B C := by
    exact bfsLayer_disjoint G root (by omega)
  obtain ⟨k, hk1, hkm, hBk, hU⟩ :=
    cliqueFree_greedy_cover G B C m t u hBC (by simpa [B] using hBne) hfree hBt hCu
  have hdeltaL : G.minDegree ≤ #A + #B + #C := by
    obtain ⟨v, hv⟩ := hBne
    have hneigh := neighborFinset_subset_left_three G root i hv
    have hdegcard : G.degree v ≤ #Wₗ := by
      rw [← G.card_neighborFinset_eq_degree]
      exact Finset.card_le_card (by simpa [Wₗ, A, B, C] using hneigh)
    have hW : #Wₗ ≤ #A + #B + #C := by
      simpa [Wₗ] using card_three_union_le A B C
    have hmindeg := G.minDegree_le_degree v
    omega
  have hdeltaR : G.minDegree ≤ #B + #C + #R := by
    obtain ⟨v, hv⟩ := hCne
    have hneigh := neighborFinset_subset_right_three G root i hv
    have hdegcard : G.degree v ≤ #Wᵣ := by
      rw [← G.card_neighborFinset_eq_degree]
      exact Finset.card_le_card (by simpa [Wᵣ, B, C, R, Nat.add_assoc] using hneigh)
    have hW : #Wᵣ ≤ #B + #C + #R := by
      simpa [Wᵣ] using card_three_union_le B C R
    have hmindeg := G.minDegree_le_degree v
    omega
  have htu : u = t + (#R - #A) := by
    simp only [u, t, A, B, C, R] at hdeltaL hdeltaR horient ⊢
    omega
  have hUcard : #(B ∪ C) = #B + #C := Finset.card_union_of_disjoint hBC
  have hcoverNat : #B + #C ≤ m * t + (m - k) * (#R - #A) := by
    rw [hUcard] at hU
    calc
      #B + #C ≤ k * t + (m - k) * u := hU
      _ = k * t + (m - k) * (t + (#R - #A)) := by rw [htu]
      _ = m * t + (m - k) * (#R - #A) := by
        have hmk : k + (m - k) = m := Nat.add_sub_of_le hkm
        calc
          _ = (k + (m - k)) * t + (m - k) * (#R - #A) := by ring
          _ = m * t + (m - k) * (#R - #A) := by rw [hmk]
  have htcast :
      (t : ℝ) = (#A : ℝ) + (#B : ℝ) + (#C : ℝ) - (G.minDegree : ℝ) := by
    simp only [t]
    rw [Nat.cast_sub hdeltaL]
    push_cast
    ring
  have hBkReal : (#B : ℝ) ≤ (k : ℝ) * (t : ℝ) := by exact_mod_cast hBk
  have hcoverReal :
      (#B : ℝ) + (#C : ℝ) ≤
        (m : ℝ) * (t : ℝ) + ((m - k : ℕ) : ℝ) * ((#R - #A : ℕ) : ℝ) := by
    exact_mod_cast hcoverNat
  rw [Nat.cast_sub hkm, Nat.cast_sub horient] at hcoverReal
  refine ⟨k, hk1, hkm, ?_, ?_⟩
  · rw [htcast] at hBkReal
    simpa [A, B, C] using hBkReal
  · have := hcoverReal
    rw [htcast] at this
    simp only [A, B, C, R] at this ⊢
    linarith

/-- The same numerical data with the four-layer window read from right to
left.  This is needed when the right outer layer is smaller. -/
theorem fourLayer_greedy_data_reverse
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (root : V) (i m : ℕ)
    (hBne : (bfsLayer G root i).Nonempty)
    (hCne : (bfsLayer G root (i + 1)).Nonempty)
    (hfree : G.CliqueFree (m + 1))
    (horient : #(bfsLayer G root (i + 2)) ≤ #(bfsPrevLayer G root i)) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ m ∧
      ((#(bfsLayer G root (i + 1)) : ℕ) : ℝ) ≤
        (k : ℝ) *
          (((#(bfsLayer G root (i + 2)) : ℕ) : ℝ) +
            ((#(bfsLayer G root (i + 1)) : ℕ) : ℝ) +
            ((#(bfsLayer G root i) : ℕ) : ℝ) - (G.minDegree : ℝ)) ∧
      0 ≤ (m : ℝ) *
          (((#(bfsLayer G root (i + 2)) : ℕ) : ℝ) +
            ((#(bfsLayer G root (i + 1)) : ℕ) : ℝ) +
            ((#(bfsLayer G root i) : ℕ) : ℝ) - (G.minDegree : ℝ)) +
        ((m : ℝ) - (k : ℝ)) *
          (((#(bfsPrevLayer G root i) : ℕ) : ℝ) -
            ((#(bfsLayer G root (i + 2)) : ℕ) : ℝ)) -
        ((#(bfsLayer G root (i + 1)) : ℕ) : ℝ) -
        ((#(bfsLayer G root i) : ℕ) : ℝ) := by
  classical
  let A := bfsLayer G root (i + 2)
  let B := bfsLayer G root (i + 1)
  let C := bfsLayer G root i
  let R := bfsPrevLayer G root i
  let Wₗ := A ∪ B ∪ C
  let Wᵣ := B ∪ C ∪ R
  let t := #A + #B + #C - G.minDegree
  let u := #B + #C + #R - G.minDegree
  have hBU : B ∪ C ⊆ Wₗ := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxB | hxC
    · exact Finset.mem_union_left C (Finset.mem_union_right A hxB)
    · exact Finset.mem_union_right (A ∪ B) hxC
  have hCU : B ∪ C ⊆ Wᵣ := Finset.subset_union_left
  have hBt : ∀ v ∈ B, #(closedNonneighborFinset G (B ∪ C) v) ≤ t := by
    intro v hv
    have hneigh0 := neighborFinset_subset_right_three G root i hv
    have hneigh : G.neighborFinset v ⊆ Wₗ := by
      simpa [Wₗ, A, B, C, Finset.union_assoc, Finset.union_comm, Finset.union_left_comm]
        using hneigh0
    have hbad := closedNonneighbor_card_le_of_neighbor_subset G (B ∪ C) Wₗ v hBU hneigh
    have hW : #Wₗ ≤ #A + #B + #C := by
      simpa [Wₗ] using card_three_union_le A B C
    have hdeg := G.minDegree_le_degree v
    simp only [t]
    omega
  have hCu : ∀ v ∈ C, #(closedNonneighborFinset G (B ∪ C) v) ≤ u := by
    intro v hv
    have hneigh0 := neighborFinset_subset_left_three G root i hv
    have hneigh : G.neighborFinset v ⊆ Wᵣ := by
      simpa [Wᵣ, B, C, R, Finset.union_assoc, Finset.union_comm, Finset.union_left_comm]
        using hneigh0
    have hbad := closedNonneighbor_card_le_of_neighbor_subset G (B ∪ C) Wᵣ v hCU hneigh
    have hW : #Wᵣ ≤ #B + #C + #R := by
      simpa [Wᵣ] using card_three_union_le B C R
    have hdeg := G.minDegree_le_degree v
    simp only [u]
    omega
  have hBC : Disjoint B C := by
    exact (bfsLayer_disjoint G root (by omega)).symm
  obtain ⟨k, hk1, hkm, hBk, hU⟩ :=
    cliqueFree_greedy_cover G B C m t u hBC (by simpa [B] using hCne) hfree hBt hCu
  have hdeltaL : G.minDegree ≤ #A + #B + #C := by
    obtain ⟨v, hv⟩ := hCne
    have hneigh0 := neighborFinset_subset_right_three G root i hv
    have hneigh : G.neighborFinset v ⊆ Wₗ := by
      simpa [Wₗ, A, B, C, Finset.union_assoc, Finset.union_comm, Finset.union_left_comm]
        using hneigh0
    have hdegcard : G.degree v ≤ #Wₗ := by
      rw [← G.card_neighborFinset_eq_degree]
      exact Finset.card_le_card hneigh
    have hW : #Wₗ ≤ #A + #B + #C := by
      simpa [Wₗ] using card_three_union_le A B C
    have hmindeg := G.minDegree_le_degree v
    omega
  have hdeltaR : G.minDegree ≤ #B + #C + #R := by
    obtain ⟨v, hv⟩ := hBne
    have hneigh0 := neighborFinset_subset_left_three G root i hv
    have hneigh : G.neighborFinset v ⊆ Wᵣ := by
      simpa [Wᵣ, B, C, R, Finset.union_assoc, Finset.union_comm, Finset.union_left_comm]
        using hneigh0
    have hdegcard : G.degree v ≤ #Wᵣ := by
      rw [← G.card_neighborFinset_eq_degree]
      exact Finset.card_le_card hneigh
    have hW : #Wᵣ ≤ #B + #C + #R := by
      simpa [Wᵣ] using card_three_union_le B C R
    have hmindeg := G.minDegree_le_degree v
    omega
  have htu : u = t + (#R - #A) := by
    simp only [u, t, A, B, C, R] at hdeltaL hdeltaR horient ⊢
    omega
  have hUcard : #(B ∪ C) = #B + #C := Finset.card_union_of_disjoint hBC
  have hcoverNat : #B + #C ≤ m * t + (m - k) * (#R - #A) := by
    rw [hUcard] at hU
    calc
      #B + #C ≤ k * t + (m - k) * u := hU
      _ = k * t + (m - k) * (t + (#R - #A)) := by rw [htu]
      _ = m * t + (m - k) * (#R - #A) := by
        have hmk : k + (m - k) = m := Nat.add_sub_of_le hkm
        calc
          _ = (k + (m - k)) * t + (m - k) * (#R - #A) := by ring
          _ = m * t + (m - k) * (#R - #A) := by rw [hmk]
  have htcast :
      (t : ℝ) = (#A : ℝ) + (#B : ℝ) + (#C : ℝ) - (G.minDegree : ℝ) := by
    simp only [t]
    rw [Nat.cast_sub hdeltaL]
    push_cast
    ring
  have hBkReal : (#B : ℝ) ≤ (k : ℝ) * (t : ℝ) := by exact_mod_cast hBk
  have hcoverReal :
      (#B : ℝ) + (#C : ℝ) ≤
        (m : ℝ) * (t : ℝ) + ((m - k : ℕ) : ℝ) * ((#R - #A : ℕ) : ℝ) := by
    exact_mod_cast hcoverNat
  rw [Nat.cast_sub hkm, Nat.cast_sub horient] at hcoverReal
  refine ⟨k, hk1, hkm, ?_, ?_⟩
  · rw [htcast] at hBkReal
    simpa [A, B, C] using hBkReal
  · rw [htcast] at hcoverReal
    simp only [A, B, C, R] at hcoverReal ⊢
    linarith

/-- Local potential step for every four-layer window in a `K₅`-free graph. -/
theorem k5_graph_local_step
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (root : V) (i : ℕ)
    (hBne : (bfsLayer G root i).Nonempty)
    (hCne : (bfsLayer G root (i + 1)).Nonempty)
    (hfree : G.CliqueFree 5) :
    k5Potential (G.minDegree : ℝ)
        (#(bfsLayer G root i) : ℝ) (#(bfsLayer G root (i + 1)) : ℝ)
        (#(bfsLayer G root (i + 2)) : ℝ) -
      k5Potential (G.minDegree : ℝ)
        (#(bfsPrevLayer G root i) : ℝ) (#(bfsLayer G root i) : ℝ)
        (#(bfsLayer G root (i + 1)) : ℝ) ≤
      (#(bfsLayer G root (i + 2)) : ℝ) - 2 * (G.minDegree : ℝ) / 5 := by
  let a := #(bfsPrevLayer G root i)
  let b := #(bfsLayer G root i)
  let c := #(bfsLayer G root (i + 1))
  let d := #(bfsLayer G root (i + 2))
  by_cases had : a ≤ d
  · obtain ⟨k, hk1, hk4, hbk, hcover⟩ :=
      fourLayer_greedy_data G hconn root i 4 hBne hCne (by simpa using hfree) had
    refine k5_local_four_layer (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ)
      (G.minDegree : ℝ)
      ((a : ℝ) + b + c - G.minDegree) ((d : ℝ) - a) k
      (by positivity) (by positivity) (by positivity) (by positivity) ?_ ?_ ?_
      rfl rfl hk1 hk4 ?_ ?_
    · exact_mod_cast had
    · have hcpos : 0 < c := by simpa [c] using hCne.card_pos
      positivity
    · have hbpos : 0 < b := by simpa [b] using hBne.card_pos
      positivity
    · simpa [a, b, c, d] using hbk
    · simpa [a, b, c, d] using hcover
  · have hda : d ≤ a := by omega
    -- Apply the oriented result to the reversed four-layer window.
    -- The potential defect is invariant under reversal.
    have hrev :
        k5Potential (G.minDegree : ℝ) (c : ℝ) (b : ℝ) (a : ℝ) -
          k5Potential (G.minDegree : ℝ) (d : ℝ) (c : ℝ) (b : ℝ) ≤
          (a : ℝ) - 2 * (G.minDegree : ℝ) / 5 := by
      obtain ⟨k, hk1, hk4, hck, hcover⟩ :=
        fourLayer_greedy_data_reverse G hconn root i 4 hBne hCne
          (by simpa using hfree) hda
      refine k5_local_four_layer (d : ℝ) (c : ℝ) (b : ℝ) (a : ℝ)
        (G.minDegree : ℝ)
        ((d : ℝ) + c + b - G.minDegree) ((a : ℝ) - d) k
        (by positivity) (by positivity) (by positivity) (by positivity) ?_ ?_ ?_
        rfl rfl hk1 hk4 ?_ ?_
      · exact_mod_cast hda
      · have hbpos : 0 < b := by simpa [b] using hBne.card_pos
        positivity
      · have hcpos : 0 < c := by simpa [c] using hCne.card_pos
        positivity
      · simpa [a, b, c, d] using hck
      · simpa [a, b, c, d] using hcover
    have hid :
        ((d : ℝ) - 2 * (G.minDegree : ℝ) / 5) -
            (k5Potential (G.minDegree : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) -
              k5Potential (G.minDegree : ℝ) (a : ℝ) (b : ℝ) (c : ℝ)) =
          ((a : ℝ) - 2 * (G.minDegree : ℝ) / 5) -
            (k5Potential (G.minDegree : ℝ) (c : ℝ) (b : ℝ) (a : ℝ) -
              k5Potential (G.minDegree : ℝ) (d : ℝ) (c : ℝ) (b : ℝ)) := by
      simp only [k5Potential]
      have hbpos : (0 : ℝ) < b := by exact_mod_cast hBne.card_pos
      have hcpos : (0 : ℝ) < c := by exact_mod_cast hCne.card_pos
      field_simp
      ring
    simp only [a, b, c, d] at *
    linarith

/-- Local potential step for every four-layer window in a `K₄`-free graph. -/
theorem k4_graph_local_step
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (root : V) (i : ℕ)
    (hBne : (bfsLayer G root i).Nonempty)
    (hCne : (bfsLayer G root (i + 1)).Nonempty)
    (hfree : G.CliqueFree 4) :
    k4Potential (G.minDegree : ℝ)
        (#(bfsLayer G root i) : ℝ) (#(bfsLayer G root (i + 1)) : ℝ)
        (#(bfsLayer G root (i + 2)) : ℝ) -
      k4Potential (G.minDegree : ℝ)
        (#(bfsPrevLayer G root i) : ℝ) (#(bfsLayer G root i) : ℝ)
        (#(bfsLayer G root (i + 1)) : ℝ) ≤
      (#(bfsLayer G root (i + 2)) : ℝ) - 3 * (G.minDegree : ℝ) / 7 := by
  let a := #(bfsPrevLayer G root i)
  let b := #(bfsLayer G root i)
  let c := #(bfsLayer G root (i + 1))
  let d := #(bfsLayer G root (i + 2))
  by_cases had : a ≤ d
  · obtain ⟨k, hk1, hk3, hbk, hcover⟩ :=
      fourLayer_greedy_data G hconn root i 3 hBne hCne (by simpa using hfree) had
    refine k4_local_four_layer (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ)
      (G.minDegree : ℝ)
      ((a : ℝ) + b + c - G.minDegree) ((d : ℝ) - a) k
      (by positivity) (by positivity) (by positivity) (by positivity) ?_ ?_ ?_
      rfl rfl hk1 hk3 ?_ ?_
    · exact_mod_cast had
    · have hcpos : 0 < c := by simpa [c] using hCne.card_pos
      positivity
    · have hbpos : 0 < b := by simpa [b] using hBne.card_pos
      positivity
    · simpa [a, b, c, d] using hbk
    · simpa [a, b, c, d] using hcover
  · have hda : d ≤ a := by omega
    have hrev :
        k4Potential (G.minDegree : ℝ) (c : ℝ) (b : ℝ) (a : ℝ) -
          k4Potential (G.minDegree : ℝ) (d : ℝ) (c : ℝ) (b : ℝ) ≤
          (a : ℝ) - 3 * (G.minDegree : ℝ) / 7 := by
      obtain ⟨k, hk1, hk3, hck, hcover⟩ :=
        fourLayer_greedy_data_reverse G hconn root i 3 hBne hCne
          (by simpa using hfree) hda
      refine k4_local_four_layer (d : ℝ) (c : ℝ) (b : ℝ) (a : ℝ)
        (G.minDegree : ℝ)
        ((d : ℝ) + c + b - G.minDegree) ((a : ℝ) - d) k
        (by positivity) (by positivity) (by positivity) (by positivity) ?_ ?_ ?_
        rfl rfl hk1 hk3 ?_ ?_
      · exact_mod_cast hda
      · have hbpos : 0 < b := by simpa [b] using hBne.card_pos
        positivity
      · have hcpos : 0 < c := by simpa [c] using hCne.card_pos
        positivity
      · simpa [a, b, c, d] using hck
      · simpa [a, b, c, d] using hcover
    have hid :
        ((d : ℝ) - 3 * (G.minDegree : ℝ) / 7) -
            (k4Potential (G.minDegree : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) -
              k4Potential (G.minDegree : ℝ) (a : ℝ) (b : ℝ) (c : ℝ)) =
          ((a : ℝ) - 3 * (G.minDegree : ℝ) / 7) -
            (k4Potential (G.minDegree : ℝ) (c : ℝ) (b : ℝ) (a : ℝ) -
              k4Potential (G.minDegree : ℝ) (d : ℝ) (c : ℝ) (b : ℝ)) := by
      simp only [k4Potential]
      have hbpos : (0 : ℝ) < b := by exact_mod_cast hBne.card_pos
      have hcpos : (0 : ℝ) < c := by exact_mod_cast hCne.card_pos
      field_simp
      ring
    simp only [a, b, c, d] at *
    linarith

end Erdos612
