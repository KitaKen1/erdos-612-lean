import Erdos612.GreedyCover
import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# BFS layers in a finite connected graph
-/

open scoped BigOperators Finset
open SimpleGraph

namespace Erdos612

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The vertices at graph distance exactly `i` from `root`. -/
noncomputable def bfsLayer (G : SimpleGraph V) (root : V) (i : ℕ) : Finset V :=
  Finset.univ.filter fun v ↦ G.dist root v = i

@[simp]
theorem mem_bfsLayer (G : SimpleGraph V) (root v : V) (i : ℕ) :
    v ∈ bfsLayer G root i ↔ G.dist root v = i := by
  simp [bfsLayer]

theorem bfsLayer_disjoint (G : SimpleGraph V) (root : V) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (bfsLayer G root i) (bfsLayer G root j) := by
  rw [Finset.disjoint_left]
  intro v hvi hvj
  rw [mem_bfsLayer] at hvi hvj
  exact hij (hvi.symm.trans hvj)

@[simp]
theorem bfsLayer_zero {G : SimpleGraph V} (hconn : G.Connected) (root : V) :
    bfsLayer G root 0 = {root} := by
  ext v
  simp [bfsLayer, hconn.dist_eq_zero_iff, eq_comm]

/-- The auxiliary layer before layer zero. -/
noncomputable def bfsPrevLayer (G : SimpleGraph V) (root : V) (i : ℕ) : Finset V :=
  if i = 0 then ∅ else bfsLayer G root (i - 1)

@[simp]
theorem bfsPrevLayer_zero (G : SimpleGraph V) (root : V) :
    bfsPrevLayer G root 0 = ∅ := by simp [bfsPrevLayer]

@[simp]
theorem bfsPrevLayer_succ (G : SimpleGraph V) (root : V) (i : ℕ) :
    bfsPrevLayer G root (i + 1) = bfsLayer G root i := by
  simp [bfsPrevLayer]

/-- Every prefix of a shortest walk is shortest. -/
theorem dist_getVert_eq_of_length_eq_dist
    {G : SimpleGraph V} (hconn : G.Connected) {x y : V}
    (p : G.Walk x y) (hp : p.length = G.dist x y) {i : ℕ} (hi : i ≤ p.length) :
    G.dist x (p.getVert i) = i := by
  have hleft : G.dist x (p.getVert i) ≤ i := by
    calc
      G.dist x (p.getVert i) ≤ (p.take i).length := SimpleGraph.dist_le (p.take i)
      _ = i := by simp [SimpleGraph.Walk.take_length, Nat.min_eq_left hi]
  have hright : G.dist (p.getVert i) y ≤ p.length - i := by
    calc
      G.dist (p.getVert i) y ≤ (p.drop i).length := SimpleGraph.dist_le (p.drop i)
      _ = p.length - i := SimpleGraph.Walk.drop_length p i
  have htri : G.dist x y ≤ G.dist x (p.getVert i) + G.dist (p.getVert i) y :=
    hconn.dist_triangle
  omega

/-- A connected finite graph has a diametral shortest walk, whose `i`th
vertex lies in BFS layer `i`. -/
theorem exists_diametral_walk (G : SimpleGraph V) (hconn : G.Connected) :
    ∃ (x y : V) (p : G.Walk x y),
      p.length = G.diam ∧ ∀ i ≤ G.diam, G.dist x (p.getVert i) = i := by
  letI : Nonempty V := hconn.nonempty
  obtain ⟨x, y, hxy⟩ := G.exists_dist_eq_diam
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist x y
  have hplen : p.length = G.diam := hp.trans hxy
  refine ⟨x, y, p, hplen, ?_⟩
  intro i hi
  exact dist_getVert_eq_of_length_eq_dist hconn p hp (by omega)

theorem bfsLayer_nonempty_of_diametral
    {G : SimpleGraph V} {x y : V} (p : G.Walk x y)
    (hplen : p.length = G.diam)
    (hgeo : ∀ i ≤ G.diam, G.dist x (p.getVert i) = i)
    {i : ℕ} (hi : i ≤ G.diam) :
    (bfsLayer G x i).Nonempty := by
  refine ⟨p.getVert i, ?_⟩
  rw [mem_bfsLayer]
  exact hgeo i hi

theorem bfsLayer_eq_empty_of_diam_lt
    {G : SimpleGraph V} (hconn : G.Connected) (root : V) {i : ℕ}
    (hi : G.diam < i) : bfsLayer G root i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  rw [mem_bfsLayer] at hv
  letI : Nonempty V := hconn.nonempty
  have htop : G.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.mp hconn
  have := G.dist_le_diam htop (u := root) (v := v)
  omega

theorem biUnion_bfsLayer_eq_univ
    {G : SimpleGraph V} (hconn : G.Connected) (root : V) :
    (Finset.range (G.diam + 1)).biUnion (bfsLayer G root) = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro v
  apply Finset.mem_biUnion.mpr
  letI : Nonempty V := hconn.nonempty
  have htop : G.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.mp hconn
  have hle := G.dist_le_diam htop (u := root) (v := v)
  exact ⟨G.dist root v, Finset.mem_range.mpr (by omega), by simp⟩

theorem sum_bfsLayer_card
    {G : SimpleGraph V} (hconn : G.Connected) (root : V) :
    ∑ i ∈ Finset.range (G.diam + 1), #(bfsLayer G root i) = Fintype.card V := by
  have hpair : ((Finset.range (G.diam + 1) : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (bfsLayer G root) := by
    intro i hi j hj hij
    exact bfsLayer_disjoint G root hij
  have hcard := Finset.card_biUnion hpair
  rw [biUnion_bfsLayer_eq_univ hconn root, Finset.card_univ] at hcard
  exact hcard.symm

/-- Neighbours of a vertex in layer `i` lie in layers `i-1,i,i+1`. -/
theorem neighborFinset_subset_left_three
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V) (i : ℕ)
    {v : V} (hv : v ∈ bfsLayer G root i) :
    G.neighborFinset v ⊆
      bfsPrevLayer G root i ∪ bfsLayer G root i ∪ bfsLayer G root (i + 1) := by
  intro w hw
  have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp hw
  have hdist := hadj.diff_dist_adj (u := root)
  rw [mem_bfsLayer] at hv
  rw [hv] at hdist
  rcases hdist with hsame | hnext | hprev
  · exact Finset.mem_union_left _ (Finset.mem_union_right _ (mem_bfsLayer G root w i |>.mpr hsame))
  · exact Finset.mem_union_right _ (mem_bfsLayer G root w (i + 1) |>.mpr hnext)
  · cases i with
    | zero =>
        exact Finset.mem_union_left _ (Finset.mem_union_right _
          (mem_bfsLayer G root w 0 |>.mpr (by simpa using hprev)))
    | succ j =>
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (by simpa using (mem_bfsLayer G root w j |>.mpr (by simpa using hprev))))

/-- Neighbours of a vertex in layer `i+1` lie in layers `i,i+1,i+2`. -/
theorem neighborFinset_subset_right_three
    (G : SimpleGraph V) [DecidableRel G.Adj] (root : V) (i : ℕ)
    {v : V} (hv : v ∈ bfsLayer G root (i + 1)) :
    G.neighborFinset v ⊆
      bfsLayer G root i ∪ bfsLayer G root (i + 1) ∪ bfsLayer G root (i + 2) := by
  intro w hw
  have hadj : G.Adj v w := (G.mem_neighborFinset v w).mp hw
  have hdist := hadj.diff_dist_adj (u := root)
  rw [mem_bfsLayer] at hv
  rw [hv] at hdist
  rcases hdist with hsame | hnext | hprev
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      (mem_bfsLayer G root w (i + 1) |>.mpr hsame))
  · exact Finset.mem_union_right _ (mem_bfsLayer G root w (i + 2) |>.mpr (by simpa [Nat.add_assoc] using hnext))
  · exact Finset.mem_union_left _ (Finset.mem_union_left _
      (mem_bfsLayer G root w i |>.mpr (by simpa using hprev)))

/-- A closed non-neighbourhood in the two middle layers is bounded by
the size of the surrounding three layers minus the degree. -/
theorem closedNonneighbor_card_le_of_neighbor_subset
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U W : Finset V) (v : V)
    (hUW : U ⊆ W) (hneigh : G.neighborFinset v ⊆ W) :
    #(closedNonneighborFinset G U v) ≤ #W - G.degree v := by
  have hbad : closedNonneighborFinset G U v ⊆ W \ G.neighborFinset v := by
    intro x hx
    rw [mem_closedNonneighborFinset] at hx
    rw [Finset.mem_sdiff, G.mem_neighborFinset]
    exact ⟨hUW hx.1, fun hadj ↦ hx.2.elim
      (fun hxv ↦ by subst x; exact G.loopless.irrefl v hadj)
      (fun hnot ↦ hnot hadj)⟩
  calc
    #(closedNonneighborFinset G U v) ≤ #(W \ G.neighborFinset v) := Finset.card_le_card hbad
    _ = #W - G.degree v := by
      rw [Finset.card_sdiff_of_subset hneigh, G.card_neighborFinset_eq_degree]

end Erdos612
