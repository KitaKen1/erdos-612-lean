import Mathlib

/-!
# The 71-layer certificate for the Erdős 612, K₇ counterexample

This file contains the finite numerical data.  A non-star entry lists the
*actual* part sizes of a complete multipartite layer.  A star is `[1]`.
-/

namespace Erdos612K7

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The 36 layer types `A₀, …, A₃₅`, using actual part sizes. -/
def halfSpecs : Array (List ℕ) := #[
  [160, 160, 160],
  [1],
  [152, 152, 16],
  [168, 168, 168, 128],
  [8, 8],
  [80, 80],
  [176, 176, 176, 176],
  [56, 56],
  [24, 16],
  [168, 168, 168, 168],
  [128, 128],
  [1],
  [160, 160, 160, 64],
  [160, 160, 96],
  [1],
  [160, 160, 64],
  [160, 160, 160, 96],
  [1],
  [112, 112],
  [176, 176, 176, 160],
  [32, 32],
  [48, 32],
  [176, 176, 176, 176],
  [96, 96],
  [1],
  [160, 160, 160, 128],
  [160, 160, 32],
  [1],
  [160, 160, 128],
  [160, 160, 160, 32],
  [1],
  [160, 128],
  [160, 160, 160, 160, 32],
  [1],
  [64, 64],
  [192, 192, 192, 160]
]

theorem halfSpecs_size : halfSpecs.size = 36 := by decide

/-- The actual part sizes of `Aᵢ`. -/
def halfSpec (i : Fin 36) : List ℕ :=
  halfSpecs[i.1]'(by simpa [halfSpecs] using i.2)

/-- `A₀,A₁,…,A₃₄,A₃₅,A₃₄,…,A₁,A₀`. -/
def halfIndex (i : Fin 71) : Fin 36 :=
  if h : i.1 ≤ 35 then
    ⟨i.1, by omega⟩
  else
    ⟨70 - i.1, by omega⟩

def blockSpec (i : Fin 71) : List ℕ := halfSpec (halfIndex i)

def cyclicPrev (i : Fin 71) : Fin 71 :=
  if h : i.1 = 0 then ⟨70, by omega⟩ else ⟨i.1 - 1, by omega⟩

def cyclicNext (i : Fin 71) : Fin 71 :=
  if h : i.1 = 70 then ⟨0, by omega⟩ else ⟨i.1 + 1, by omega⟩

def partCount (i : Fin 71) : ℕ := (blockSpec i).length
def layerSize (i : Fin 71) : ℕ := (blockSpec i).sum
def partSize (i : Fin 71) (a : Fin (partCount i)) : ℕ :=
  (blockSpec i).get a

theorem partCount_pos : ∀ i : Fin 71, 0 < partCount i := by decide
theorem partSize_pos : ∀ i : Fin 71, ∀ a : Fin (partCount i), 0 < partSize i a := by
  decide

/-- A uniform coordinate box large enough for every part in the table. -/
abbrev Coord := Fin 5 × Fin 192

/-- Size of part `a`; unused part numbers have size zero. -/
def sizeAt (i : Fin 71) (a : Fin 5) : ℕ := (blockSpec i).getD a.1 0

def ValidCoord (i : Fin 71) (c : Coord) : Prop := c.2.1 < sizeAt i c.1

instance (i : Fin 71) : DecidablePred (ValidCoord i) := fun _ => by
  unfold ValidCoord
  infer_instance

/-- Vertices in block layer `i`, represented in the uniform coordinate box. -/
abbrev LayerVertex (i : Fin 71) := {c : Coord // ValidCoord i c}

abbrev A0Vertex := LayerVertex ⟨0, by omega⟩
abbrev BlockVertex := Σ i : Fin 71, LayerVertex i

/-- Two end layers and `p` disjoint copies of the 71-layer block. -/
abbrev Vertex (p : ℕ) := A0Vertex ⊕ ((Fin p × BlockVertex) ⊕ A0Vertex)

theorem a0_card : Fintype.card A0Vertex = 480 := by decide
theorem block_card : Fintype.card BlockVertex = 21296 := by decide

theorem vertex_card (p : ℕ) : Fintype.card (Vertex p) = 21296 * p + 960 := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  rw [a0_card, block_card]
  omega

/-- The missing cross-part occurs only when the two part counts total seven
and both vertices lie in the final part of their layer. -/
def crossAllowed (i j : Fin 71) (a : Fin (partCount i)) (b : Fin (partCount j)) : Bool :=
  !((partCount i + partCount j == 7) &&
    (a.1 + 1 == partCount i) && (b.1 + 1 == partCount j))

/-- The number of neighbours of a vertex of part `a` in the periodic
three-layer window around block position `i`. -/
def localDegree (i : Fin 71) (a : Fin (partCount i)) : ℕ :=
  (Finset.univ.filter fun b : Fin (partCount (cyclicPrev i)) =>
      crossAllowed i (cyclicPrev i) a b).sum (partSize (cyclicPrev i))
  + (Finset.univ.filter fun b : Fin (partCount i) => b ≠ a).sum (partSize i)
  + (Finset.univ.filter fun b : Fin (partCount (cyclicNext i)) =>
      crossAllowed i (cyclicNext i) a b).sum (partSize (cyclicNext i))

theorem adjacent_part_count_le_six_or_seven :
    ∀ i : Fin 71,
      partCount i + partCount (cyclicNext i) ≤ 7 := by
  decide

theorem localDegree_ge_800 :
    ∀ i : Fin 71, ∀ a : Fin (partCount i), 800 ≤ localDegree i a := by
  decide

def crossAllowedFixed (i j : Fin 71) (a b : Fin 5) : Bool :=
  !((partCount i + partCount j == 7) &&
    (a.1 + 1 == partCount i) && (b.1 + 1 == partCount j))

def localDegreeFixed (i : Fin 71) (a : Fin 5) : ℕ :=
  (Finset.univ.filter fun b : Fin 5 => crossAllowedFixed i (cyclicPrev i) a b).sum
      (sizeAt (cyclicPrev i))
  + (Finset.univ.filter fun b : Fin 5 => b ≠ a).sum (sizeAt i)
  + (Finset.univ.filter fun b : Fin 5 => crossAllowedFixed i (cyclicNext i) a b).sum
      (sizeAt (cyclicNext i))

theorem partCount_le_five : ∀ i : Fin 71, partCount i ≤ 5 := by decide

theorem first_part_nonempty : ∀ i : Fin 71, 0 < sizeAt i ⟨0, by omega⟩ := by
  decide

theorem validCoord_part_lt_count :
    ∀ i : Fin 71, ∀ c : Coord, ValidCoord i c → c.1.1 < partCount i := by
  decide

theorem localDegreeFixed_ge_800 :
    ∀ i : Fin 71, ∀ a : Fin 5, 0 < sizeAt i a → 800 ≤ localDegreeFixed i a := by
  decide

def blockOrder : ℕ := ∑ i : Fin 71, layerSize i

theorem blockOrder_eq : blockOrder = 21296 := by decide

end Erdos612K7
