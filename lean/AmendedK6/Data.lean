import Mathlib

/-!
# The 33-layer data table (`h = 22`)

This file contains no proof holes. Finite table checks use `decide`, not
`native_decide`.
-/

namespace Erdos612AmendedK6

open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- One row of the data table, `(qᵢ, aᵢ, bᵢ)`. -/
structure LayerSpec where
  q : ℕ
  a : ℕ
  b : ℕ
  deriving DecidableEq, Repr

def specs : Array LayerSpec := #[
  ⟨3,25,7⟩, ⟨1,0,0⟩, ⟨2,22,21⟩, ⟨4,26,1⟩,
  ⟨2,3,1⟩, ⟨2,11,9⟩, ⟨3,29,29⟩, ⟨2,11,11⟩,
  ⟨2,1,1⟩, ⟨3,26,25⟩, ⟨2,24,23⟩, ⟨1,0,0⟩,
  ⟨3,24,5⟩, ⟨3,26,19⟩, ⟨2,1,1⟩, ⟨2,14,14⟩,
  ⟨3,28,28⟩, ⟨2,8,8⟩, ⟨2,4,4⟩, ⟨3,28,24⟩,
  ⟨2,20,20⟩, ⟨1,0,0⟩, ⟨3,25,10⟩, ⟨3,25,15⟩,
  ⟨1,0,0⟩, ⟨2,18,17⟩, ⟨3,28,27⟩, ⟨2,5,5⟩,
  ⟨2,6,6⟩, ⟨3,28,28⟩, ⟨2,16,16⟩, ⟨1,0,0⟩,
  ⟨3,25,18⟩
]

theorem specs_size : specs.size = 33 := by decide

def spec (i : Fin 33) : LayerSpec :=
  specs[i.val]'(by simpa only [specs_size] using i.isLt)

def partCount (i : Fin 33) : ℕ := (spec i).q

/-- Ordinary classes have `22aᵢ` vertices; the final class has
`max(1,22bᵢ)` vertices. -/
def partSize (i : Fin 33) (a : Fin (partCount i)) : ℕ :=
  if a.val + 1 = partCount i then max 1 (22 * (spec i).b)
  else 22 * (spec i).a

def layerSize (i : Fin 33) : ℕ := ∑ a : Fin (partCount i), partSize i a

def cyclicPrev (i : Fin 33) : Fin 33 := ⟨(i.val + 32) % 33, Nat.mod_lt _ (by decide)⟩
def cyclicNext (i : Fin 33) : Fin 33 := ⟨(i.val + 1) % 33, Nat.mod_lt _ (by decide)⟩

theorem partCount_bounds : ∀ i : Fin 33, 1 ≤ partCount i ∧ partCount i ≤ 4 := by
  decide

theorem partSize_pos : ∀ i : Fin 33, ∀ a : Fin (partCount i), 0 < partSize i a := by
  decide

theorem adjacent_partCount_le_six :
    ∀ i : Fin 33, partCount i + partCount (cyclicNext i) ≤ 6 := by
  decide

theorem period_order : (∑ i : Fin 33, layerSize i) = 27923 := by decide

/-- When adjacent layers have six classes in total, delete the edges between
their final classes. -/
def crossAllowed (i j : Fin 33)
    (a : Fin (partCount i)) (b : Fin (partCount j)) : Bool :=
  !((partCount i + partCount j == 6) &&
    (a.val + 1 == partCount i) && (b.val + 1 == partCount j))

/-- The number of neighbors of a vertex in class `a` within one period. -/
def localDegree (i : Fin 33) (a : Fin (partCount i)) : ℕ :=
  (Finset.univ.filter fun b : Fin (partCount (cyclicPrev i)) =>
    crossAllowed i (cyclicPrev i) a b).sum (partSize (cyclicPrev i))
  + (Finset.univ.filter fun b : Fin (partCount i) => b ≠ a).sum (partSize i)
  + (Finset.univ.filter fun b : Fin (partCount (cyclicNext i)) =>
    crossAllowed i (cyclicNext i) a b).sum (partSize (cyclicNext i))

theorem localDegree_ge_2200 :
    ∀ i : Fin 33, ∀ a : Fin (partCount i), 2200 ≤ localDegree i a := by
  decide

abbrev LayerVertex (i : Fin 33) := Σ a : Fin (partCount i), Fin (partSize i a)
abbrev BlockVertex := Σ i : Fin 33, LayerVertex i

/-- Two cap layers on either side, each with 2200 vertices. -/
abbrev CapVertex := Fin 2 × Fin 2200

/-- Two left cap layers, `m` periods, and two right cap layers. -/
abbrev Vertex (m : ℕ) := CapVertex ⊕ ((Fin m × BlockVertex) ⊕ CapVertex)

def order (m : ℕ) : ℕ := 27923 * m + 8800
def diameterLower (m : ℕ) : ℕ := 33 * m + 3

theorem block_card : Fintype.card BlockVertex = 27923 := by
  simpa only [BlockVertex, LayerVertex, Fintype.card_sigma, Fintype.card_fin,
    layerSize] using period_order

theorem vertex_card (m : ℕ) : Fintype.card (Vertex m) = order m := by
  simp only [Vertex, CapVertex, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, block_card]
  unfold order
  omega

end Erdos612AmendedK6
