import K7Counterexample.Data

namespace Erdos612K7

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Position of the layer containing a vertex, from `0` to `71p+1`. -/
def layerPos {p : ℕ} : Vertex p → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl (b, ⟨i, _⟩)) => 71 * b.1 + i.1 + 1
  | Sum.inr (Sum.inr _) => 71 * p + 1

/-- Number of multipartite parts in the vertex's layer. -/
def vertexPartCount {p : ℕ} : Vertex p → ℕ
  | Sum.inl _ => partCount ⟨0, by omega⟩
  | Sum.inr (Sum.inl (_, ⟨i, _⟩)) => partCount i
  | Sum.inr (Sum.inr _) => partCount ⟨0, by omega⟩

/-- Part number of a vertex inside its layer. -/
def vertexPart {p : ℕ} : Vertex p → ℕ
  | Sum.inl v => v.1.1.1
  | Sum.inr (Sum.inl (_, ⟨_, v⟩)) => v.1.1.1
  | Sum.inr (Sum.inr v) => v.1.1.1

theorem vertexPartCount_le_five {p : ℕ} (v : Vertex p) : vertexPartCount v ≤ 5 := by
  rcases v with v | ⟨⟨b, i, v⟩ | v⟩
  · exact partCount_le_five ⟨0, by omega⟩
  · exact partCount_le_five i
  · exact partCount_le_five ⟨0, by omega⟩

/-- Cross-layer adjacency deletes precisely the last-part/last-part pair
when the two layers have seven parts in total. -/
def crossAllowedV {p : ℕ} (v w : Vertex p) : Prop :=
  ¬(vertexPartCount v + vertexPartCount w = 7 ∧
    vertexPart v + 1 = vertexPartCount v ∧
    vertexPart w + 1 = vertexPartCount w)

instance {p : ℕ} (v w : Vertex p) : Decidable (crossAllowedV v w) := by
  unfold crossAllowedV
  infer_instance

def adjRel {p : ℕ} (v w : Vertex p) : Prop :=
  (layerPos v = layerPos w ∧ vertexPart v ≠ vertexPart w) ∨
  (Nat.dist (layerPos v) (layerPos w) = 1 ∧ crossAllowedV v w)

instance {p : ℕ} : DecidableRel (@adjRel p) := fun _ _ => by
  unfold adjRel
  infer_instance

theorem crossAllowedV_comm {p : ℕ} (v w : Vertex p) :
    crossAllowedV v w ↔ crossAllowedV w v := by
  unfold crossAllowedV
  constructor <;> rintro h ⟨hs, hv, hw⟩
  · exact h ⟨by omega, hw, hv⟩
  · exact h ⟨by omega, hw, hv⟩

/-- The finite graph in the counterexample family. -/
def graph (p : ℕ) : SimpleGraph (Vertex p) where
  Adj := adjRel
  symm := by
    constructor
    intro v w h
    rcases h with h | h
    · exact Or.inl ⟨h.1.symm, Ne.symm h.2⟩
    · exact Or.inr ⟨by simpa [Nat.dist_comm] using h.1,
        (crossAllowedV_comm v w).mp h.2⟩
  loopless := by
    constructor
    intro v h
    rcases h with h | h
    · exact h.2 rfl
    · simpa using h.1

instance {p : ℕ} : DecidableRel (graph p).Adj := fun v w => by
  change Decidable (adjRel v w)
  infer_instance

@[simp] theorem graph_adj {p : ℕ} {v w : Vertex p} :
    (graph p).Adj v w ↔ adjRel v w := Iff.rfl

private def firstCoord (i : Fin 71) : LayerVertex i :=
  ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), first_part_nonempty i⟩

def leftHub (p : ℕ) : Vertex p := Sum.inl (firstCoord ⟨0, by omega⟩)

def coreHub {p : ℕ} (b : Fin p) (i : Fin 71) : Vertex p :=
  Sum.inr (Sum.inl (b, ⟨i, firstCoord i⟩))

def rightHub (p : ℕ) : Vertex p := Sum.inr (Sum.inr (firstCoord ⟨0, by omega⟩))

@[simp] theorem layerPos_leftHub (p : ℕ) : layerPos (leftHub p) = 0 := rfl
@[simp] theorem layerPos_coreHub {p : ℕ} (b : Fin p) (i : Fin 71) :
    layerPos (coreHub b i) = 71 * b.1 + i.1 + 1 := rfl
@[simp] theorem layerPos_rightHub (p : ℕ) : layerPos (rightHub p) = 71 * p + 1 := rfl

@[simp] theorem vertexPart_leftHub (p : ℕ) : vertexPart (leftHub p) = 0 := rfl
@[simp] theorem vertexPart_coreHub {p : ℕ} (b : Fin p) (i : Fin 71) :
    vertexPart (coreHub b i) = 0 := rfl
@[simp] theorem vertexPart_rightHub (p : ℕ) : vertexPart (rightHub p) = 0 := rfl

theorem adj_of_dist_one_right_first {p : ℕ} {v w : Vertex p}
    (hd : Nat.dist (layerPos v) (layerPos w) = 1)
    (hw : vertexPart w = 0) : (graph p).Adj v w := by
  rw [graph_adj]
  exact Or.inr ⟨hd, by
    intro h
    rcases h with ⟨hs, _, hlast⟩
    have hv := vertexPartCount_le_five v
    omega⟩

theorem adj_of_dist_one_left_first {p : ℕ} {v w : Vertex p}
    (hd : Nat.dist (layerPos v) (layerPos w) = 1)
    (hv : vertexPart v = 0) : (graph p).Adj v w := by
  exact (adj_of_dist_one_right_first
    (by simpa [Nat.dist_comm] using hd) hv
    ).symm

def corePrevHub {p : ℕ} (b : Fin p) (i : Fin 71) : Vertex p :=
  if hi : i.1 = 0 then
    if hb : b.1 = 0 then
      leftHub p
    else
      coreHub ⟨b.1 - 1, by omega⟩ ⟨70, by omega⟩
  else
    coreHub b ⟨i.1 - 1, by omega⟩

@[simp] theorem vertexPart_corePrevHub {p : ℕ} (b : Fin p) (i : Fin 71) :
    vertexPart (corePrevHub b i) = 0 := by
  unfold corePrevHub
  split
  · split <;> rfl
  · rfl

theorem core_prev_dist {p : ℕ} (b : Fin p) (i : Fin 71) :
    Nat.dist (layerPos (coreHub b i)) (layerPos (corePrevHub b i)) = 1 := by
  unfold corePrevHub
  split
  · split <;>
      simp only [layerPos_coreHub, layerPos_leftHub, Nat.dist] <;>
      omega
  · simp only [layerPos_coreHub, Nat.dist]
    omega

theorem core_vertex_reachable_hub {p : ℕ} (b : Fin p) (i : Fin 71)
    (v : LayerVertex i) :
    (graph p).Reachable
      (Sum.inr (Sum.inl (b, ⟨i, v⟩))) (coreHub b i) := by
  let x : Vertex p := Sum.inr (Sum.inl (b, ⟨i, v⟩))
  have hxpos : layerPos x = layerPos (coreHub b i) := rfl
  have h₁ : (graph p).Adj x (corePrevHub b i) :=
    adj_of_dist_one_right_first (by simpa [hxpos] using core_prev_dist b i)
      (vertexPart_corePrevHub b i)
  have h₂ : (graph p).Adj (corePrevHub b i) (coreHub b i) :=
    adj_of_dist_one_right_first
      (by simpa [Nat.dist_comm] using core_prev_dist b i)
      (vertexPart_coreHub b i)
  exact h₁.reachable.trans h₂.reachable

def firstBlock {p : ℕ} (hp : 0 < p) : Fin p := ⟨0, hp⟩
def lastBlock {p : ℕ} (hp : 0 < p) : Fin p := ⟨p - 1, by omega⟩

theorem left_core_start_adj {p : ℕ} (hp : 0 < p) :
    (graph p).Adj (leftHub p) (coreHub (firstBlock hp) ⟨0, by omega⟩) := by
  apply adj_of_dist_one_left_first
  · simp [Nat.dist, firstBlock]
  · rfl

theorem core_adj_of_layer_succ {p : ℕ} (b : Fin p) (i j : Fin 71)
    (hij : i.1 + 1 = j.1) :
    (graph p).Adj (coreHub b i) (coreHub b j) := by
  apply adj_of_dist_one_left_first
  · simp only [layerPos_coreHub]
    simp [Nat.dist]
    omega
  · rfl

theorem core_adj_of_block_succ {p : ℕ} (b c : Fin p) (hbc : b.1 + 1 = c.1) :
    (graph p).Adj (coreHub b ⟨70, by omega⟩) (coreHub c ⟨0, by omega⟩) := by
  apply adj_of_dist_one_left_first
  · simp only [layerPos_coreHub]
    simp [Nat.dist]
    omega
  · rfl

theorem last_core_right_adj {p : ℕ} (hp : 0 < p) :
    (graph p).Adj (coreHub (lastBlock hp) ⟨70, by omega⟩) (rightHub p) := by
  apply adj_of_dist_one_left_first
  · simp only [layerPos_coreHub, layerPos_rightHub]
    simp [Nat.dist, lastBlock]
    omega
  · rfl

private theorem core_reachable_from_start {p : ℕ} (b : Fin p)
    (hstart : (graph p).Reachable (leftHub p) (coreHub b ⟨0, by omega⟩))
    (i : Fin 71) :
    (graph p).Reachable (leftHub p) (coreHub b i) := by
  induction i using Fin.strong_induction_on with
  | h i ih =>
      by_cases hi : i.1 = 0
      · have hieq : i = ⟨0, by omega⟩ := Fin.ext hi
        simpa [hieq] using hstart
      · let j : Fin 71 := ⟨i.1 - 1, by omega⟩
        have hjlt : j < i := by
          change i.1 - 1 < i.1
          omega
        have hji : j.1 + 1 = i.1 := by simp [j]; omega
        exact (ih j hjlt).trans (core_adj_of_layer_succ b j i hji).reachable

theorem left_reachable_core {p : ℕ} (hp : 0 < p) (b : Fin p) (i : Fin 71) :
    (graph p).Reachable (leftHub p) (coreHub b i) := by
  revert i
  induction b using Fin.strong_induction_on with
  | h b ih =>
      intro i
      by_cases hb : b.1 = 0
      · have hbeq : b = firstBlock hp := Fin.ext hb
        subst b
        exact core_reachable_from_start (firstBlock hp)
          (left_core_start_adj hp).reachable i
      · let c : Fin p := ⟨b.1 - 1, by omega⟩
        have hclt : c < b := by
          change b.1 - 1 < b.1
          omega
        have hcb : c.1 + 1 = b.1 := by simp [c]; omega
        have hend := ih c hclt ⟨70, by omega⟩
        have hstart : (graph p).Reachable (leftHub p) (coreHub b ⟨0, by omega⟩) :=
          hend.trans (core_adj_of_block_succ c b hcb).reachable
        exact core_reachable_from_start b hstart i

theorem left_vertex_reachable_hub {p : ℕ} (hp : 0 < p) (v : A0Vertex) :
    (graph p).Reachable (Sum.inl v) (leftHub p) := by
  let bridge := coreHub (firstBlock hp) ⟨0, by omega⟩
  have h₁ : (graph p).Adj (Sum.inl v) bridge := by
    apply adj_of_dist_one_right_first
    · change Nat.dist 0 1 = 1
      decide
    · rfl
  have h₂ : (graph p).Adj bridge (leftHub p) := by
    apply adj_of_dist_one_right_first
    · simp [bridge, Nat.dist, firstBlock]
    · rfl
  exact h₁.reachable.trans h₂.reachable

theorem right_vertex_reachable_hub {p : ℕ} (hp : 0 < p) (v : A0Vertex) :
    (graph p).Reachable (Sum.inr (Sum.inr v)) (rightHub p) := by
  let bridge := coreHub (lastBlock hp) ⟨70, by omega⟩
  have h₁ : (graph p).Adj (Sum.inr (Sum.inr v)) bridge := by
    apply adj_of_dist_one_right_first
    · change Nat.dist (71 * p + 1) (71 * (p - 1) + 71) = 1
      simp [Nat.dist]
      omega
    · rfl
  have h₂ : (graph p).Adj bridge (rightHub p) := last_core_right_adj hp
  exact h₁.reachable.trans h₂.reachable

theorem graph_connected {p : ℕ} (hp : 0 < p) : (graph p).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨leftHub p, ?_⟩
  intro v
  rcases v with v | ⟨⟨b, i, v⟩ | v⟩
  · exact (left_vertex_reachable_hub hp v).symm
  · exact (left_reachable_core hp b i).trans (core_vertex_reachable_hub b i v).symm
  · have hend := (left_reachable_core hp (lastBlock hp) ⟨70, by omega⟩).trans
        (last_core_right_adj hp).reachable
    exact hend.trans (right_vertex_reachable_hub hp v).symm

theorem adj_layer_dist_le_one {p : ℕ} {v w : Vertex p} (h : (graph p).Adj v w) :
    Nat.dist (layerPos v) (layerPos w) ≤ 1 := by
  rcases h with h | h
  · simp [h.1]
  · omega

theorem walk_layer_dist_le_length {p : ℕ} {u v : Vertex p}
    (W : (graph p).Walk u v) : Nat.dist (layerPos u) (layerPos v) ≤ W.length := by
  induction W with
  | nil => simp
  | @cons u v w huv W ih =>
      calc
        Nat.dist (layerPos u) (layerPos w)
            ≤ Nat.dist (layerPos u) (layerPos v) + Nat.dist (layerPos v) (layerPos w) :=
              Nat.dist.triangle_inequality _ _ _
        _ ≤ 1 + W.length := Nat.add_le_add (adj_layer_dist_le_one huv) ih
        _ = (SimpleGraph.Walk.cons huv W).length := by simp; omega

theorem endpoint_dist_lower_bound {p : ℕ} (hp : 0 < p) :
    71 * p + 1 ≤ (graph p).dist (leftHub p) (rightHub p) := by
  obtain ⟨W, hW⟩ := (graph_connected hp).exists_walk_length_eq_dist
    (leftHub p) (rightHub p)
  calc
    71 * p + 1 = Nat.dist (layerPos (leftHub p)) (layerPos (rightHub p)) := by
      simp [Nat.dist]
    _ ≤ W.length := walk_layer_dist_le_length W
    _ = (graph p).dist (leftHub p) (rightHub p) := hW

theorem diameter_lower_bound {p : ℕ} (hp : 0 < p) :
    71 * p + 1 ≤ (graph p).diam := by
  have hc := graph_connected hp
  letI : Nonempty (Vertex p) := hc.nonempty
  have htop : (graph p).ediam ≠ ⊤ :=
    (SimpleGraph.connected_iff_ediam_ne_top).mp hc
  exact (endpoint_dist_lower_bound hp).trans (SimpleGraph.dist_le_diam htop)

/-! ## The local-neighbour certificate and minimum degree -/

abbrev LocalCandidate (i : Fin 71) :=
  LayerVertex (cyclicPrev i) ⊕ (LayerVertex i ⊕ LayerVertex (cyclicNext i))

def localCrossAllowed (i j : Fin 71) (a b : Fin 5) : Prop :=
  ¬(partCount i + partCount j = 7 ∧
    a.1 + 1 = partCount i ∧ b.1 + 1 = partCount j)

instance (i j : Fin 71) (a b : Fin 5) : Decidable (localCrossAllowed i j a b) := by
  unfold localCrossAllowed
  infer_instance

def IsLocalNeighbor (i : Fin 71) (a : Fin 5) : LocalCandidate i → Prop
  | Sum.inl x => localCrossAllowed i (cyclicPrev i) a x.1.1
  | Sum.inr (Sum.inl x) => x.1.1 ≠ a
  | Sum.inr (Sum.inr x) => localCrossAllowed i (cyclicNext i) a x.1.1

instance (i : Fin 71) (a : Fin 5) : DecidablePred (IsLocalNeighbor i a) := fun x => by
  rcases x with x | (x | x) <;> simp only [IsLocalNeighbor] <;> infer_instance

abbrev LocalNeighbor (i : Fin 71) (a : Fin 5) :=
  {x : LocalCandidate i // IsLocalNeighbor i a x}

theorem localNeighbor_card_ge_800 :
    ∀ i : Fin 71, ∀ a : Fin 5,
      0 < sizeAt i a → 800 ≤ Fintype.card (LocalNeighbor i a) := by
  decide

def vertexCoord {p : ℕ} : Vertex p → Coord
  | Sum.inl v => v.1
  | Sum.inr (Sum.inl (_, ⟨_, v⟩)) => v.1
  | Sum.inr (Sum.inr v) => v.1

def embedPrev {p : ℕ} (b : Fin p) (i : Fin 71)
    (x : LayerVertex (cyclicPrev i)) : Vertex p :=
  if hi : i.1 = 0 then
    if hb : b.1 = 0 then
      Sum.inl ⟨x.1, by
        simpa [cyclicPrev, hi, ValidCoord, sizeAt, blockSpec, halfIndex,
          halfSpec, halfSpecs] using x.2⟩
    else
      Sum.inr (Sum.inl (⟨b.1 - 1, by omega⟩,
        ⟨⟨70, by omega⟩, ⟨x.1, by
          simpa [cyclicPrev, hi] using x.2⟩⟩))
  else
    Sum.inr (Sum.inl (b,
      ⟨⟨i.1 - 1, by omega⟩, ⟨x.1, by
        simpa [cyclicPrev, hi] using x.2⟩⟩))

def embedSame {p : ℕ} (b : Fin p) (i : Fin 71) (x : LayerVertex i) : Vertex p :=
  Sum.inr (Sum.inl (b, ⟨i, x⟩))

def embedNext {p : ℕ} (b : Fin p) (i : Fin 71)
    (x : LayerVertex (cyclicNext i)) : Vertex p :=
  if hi : i.1 = 70 then
    if hb : b.1 + 1 = p then
      Sum.inr (Sum.inr ⟨x.1, by
        simpa [cyclicNext, hi, ValidCoord, sizeAt, blockSpec, halfIndex,
          halfSpec, halfSpecs] using x.2⟩)
    else
      Sum.inr (Sum.inl (⟨b.1 + 1, by omega⟩,
        ⟨⟨0, by omega⟩, ⟨x.1, by
          simpa [cyclicNext, hi] using x.2⟩⟩))
  else
    Sum.inr (Sum.inl (b,
      ⟨⟨i.1 + 1, by omega⟩, ⟨x.1, by
        simpa [cyclicNext, hi] using x.2⟩⟩))

@[simp] theorem vertexCoord_embedPrev {p : ℕ} (b : Fin p) (i : Fin 71)
    (x : LayerVertex (cyclicPrev i)) : vertexCoord (embedPrev b i x) = x.1 := by
  unfold embedPrev
  split
  · split <;> rfl
  · rfl

@[simp] theorem vertexCoord_embedSame {p : ℕ} (b : Fin p) (i : Fin 71)
    (x : LayerVertex i) : vertexCoord (embedSame b i x) = x.1 := rfl

@[simp] theorem vertexCoord_embedNext {p : ℕ} (b : Fin p) (i : Fin 71)
    (x : LayerVertex (cyclicNext i)) : vertexCoord (embedNext b i x) = x.1 := by
  unfold embedNext
  split
  · split <;> rfl
  · rfl

theorem layerPos_embedPrev {p : ℕ} (b : Fin p) (i : Fin 71)
    (x : LayerVertex (cyclicPrev i)) :
    layerPos (embedPrev b i x) + 1 = 71 * b.1 + i.1 + 1 := by
  unfold embedPrev
  split
  · split <;> simp [layerPos] <;> omega
  · simp [layerPos]
    omega

theorem layerPos_embedSame {p : ℕ} (b : Fin p) (i : Fin 71) (x : LayerVertex i) :
    layerPos (embedSame b i x) = 71 * b.1 + i.1 + 1 := rfl

theorem layerPos_embedNext {p : ℕ} (b : Fin p) (i : Fin 71)
    (x : LayerVertex (cyclicNext i)) :
    layerPos (embedNext b i x) = 71 * b.1 + i.1 + 2 := by
  unfold embedNext
  split
  · split <;> simp [layerPos] <;> omega
  · simp [layerPos]
    omega

@[simp] theorem vertexPart_embedPrev {p : ℕ} (b : Fin p) (i : Fin 71)
    (x : LayerVertex (cyclicPrev i)) : vertexPart (embedPrev b i x) = x.1.1.1 := by
  unfold embedPrev
  split
  · split <;> rfl
  · rfl

@[simp] theorem vertexPart_embedSame {p : ℕ} (b : Fin p) (i : Fin 71)
    (x : LayerVertex i) : vertexPart (embedSame b i x) = x.1.1.1 := rfl

@[simp] theorem vertexPart_embedNext {p : ℕ} (b : Fin p) (i : Fin 71)
    (x : LayerVertex (cyclicNext i)) : vertexPart (embedNext b i x) = x.1.1.1 := by
  unfold embedNext
  split
  · split <;> rfl
  · rfl

@[simp] theorem vertexPartCount_embedPrev {p : ℕ} (b : Fin p) (i : Fin 71)
    (x : LayerVertex (cyclicPrev i)) :
    vertexPartCount (embedPrev b i x) = partCount (cyclicPrev i) := by
  unfold embedPrev
  split
  · rename_i hi
    split
    · simp [vertexPartCount, cyclicPrev, hi, partCount, blockSpec, halfIndex,
        halfSpec, halfSpecs]
    · simp [vertexPartCount, cyclicPrev, hi]
  · rename_i hi
    simp [vertexPartCount, cyclicPrev, hi]

@[simp] theorem vertexPartCount_embedSame {p : ℕ} (b : Fin p) (i : Fin 71)
    (x : LayerVertex i) : vertexPartCount (embedSame b i x) = partCount i := rfl

@[simp] theorem vertexPartCount_embedNext {p : ℕ} (b : Fin p) (i : Fin 71)
    (x : LayerVertex (cyclicNext i)) :
    vertexPartCount (embedNext b i x) = partCount (cyclicNext i) := by
  unfold embedNext
  split
  · rename_i hi
    split
    · simp [vertexPartCount, cyclicNext, hi, partCount, blockSpec, halfIndex,
        halfSpec, halfSpecs]
    · simp [vertexPartCount, cyclicNext, hi]
  · rename_i hi
    simp [vertexPartCount, cyclicNext, hi]

def embedLocal {p : ℕ} (b : Fin p) (i : Fin 71) : LocalCandidate i → Vertex p
  | Sum.inl x => embedPrev b i x
  | Sum.inr (Sum.inl x) => embedSame b i x
  | Sum.inr (Sum.inr x) => embedNext b i x

theorem embedLocal_injective {p : ℕ} (b : Fin p) (i : Fin 71) :
    Function.Injective (embedLocal b i) := by
  intro x y hxy
  rcases x with x | (x | x) <;> rcases y with y | (y | y)
  · have hval : x.1 = y.1 := by
      simpa only [embedLocal, vertexCoord_embedPrev] using congrArg vertexCoord hxy
    exact congrArg Sum.inl (Subtype.ext hval)
  · change embedPrev b i x = embedSame b i y at hxy
    have hp := congrArg layerPos hxy
    have hx := layerPos_embedPrev b i x
    have hy := layerPos_embedSame b i y
    omega
  · change embedPrev b i x = embedNext b i y at hxy
    have hp := congrArg layerPos hxy
    have hx := layerPos_embedPrev b i x
    have hy := layerPos_embedNext b i y
    omega
  · change embedSame b i x = embedPrev b i y at hxy
    have hp := congrArg layerPos hxy
    have hx := layerPos_embedSame b i x
    have hy := layerPos_embedPrev b i y
    omega
  · have hval : x.1 = y.1 := by
      simpa only [embedLocal, vertexCoord_embedSame] using congrArg vertexCoord hxy
    exact congrArg Sum.inr (congrArg Sum.inl (Subtype.ext hval))
  · change embedSame b i x = embedNext b i y at hxy
    have hp := congrArg layerPos hxy
    have hx := layerPos_embedSame b i x
    have hy := layerPos_embedNext b i y
    omega
  · change embedNext b i x = embedPrev b i y at hxy
    have hp := congrArg layerPos hxy
    have hx := layerPos_embedNext b i x
    have hy := layerPos_embedPrev b i y
    omega
  · change embedNext b i x = embedSame b i y at hxy
    have hp := congrArg layerPos hxy
    have hx := layerPos_embedNext b i x
    have hy := layerPos_embedSame b i y
    omega
  · have hval : x.1 = y.1 := by
      simpa only [embedLocal, vertexCoord_embedNext] using congrArg vertexCoord hxy
    exact congrArg Sum.inr (congrArg Sum.inr (Subtype.ext hval))

theorem embedLocal_is_adjacent {p : ℕ} (b : Fin p) (i : Fin 71)
    (center : LayerVertex i) (x : LocalNeighbor i center.1.1) :
    (graph p).Adj (embedSame b i center) (embedLocal b i x.1) := by
  rcases x with ⟨x | (x | x), hx⟩
  · change (graph p).Adj (embedSame b i center) (embedPrev b i x)
    rw [graph_adj]
    right
    refine ⟨?_, ?_⟩
    · have hp := layerPos_embedPrev b i x
      rw [layerPos_embedSame]
      simp [Nat.dist]
      omega
    · change localCrossAllowed i (cyclicPrev i) center.1.1 x.1.1 at hx
      change crossAllowedV (embedSame b i center) (embedPrev b i x)
      simpa [crossAllowedV, localCrossAllowed] using hx
  · change (graph p).Adj (embedSame b i center) (embedSame b i x)
    rw [graph_adj]
    left
    change x.1.1 ≠ center.1.1 at hx
    refine ⟨rfl, ?_⟩
    intro hnat
    exact hx (Fin.ext hnat.symm)
  · change (graph p).Adj (embedSame b i center) (embedNext b i x)
    rw [graph_adj]
    right
    refine ⟨?_, ?_⟩
    · have hp := layerPos_embedNext b i x
      rw [layerPos_embedSame]
      simp [Nat.dist]
      omega
    · change localCrossAllowed i (cyclicNext i) center.1.1 x.1.1 at hx
      change crossAllowedV (embedSame b i center) (embedNext b i x)
      simpa [crossAllowedV, localCrossAllowed] using hx

def localNeighborEmbedding {p : ℕ} (b : Fin p) (i : Fin 71) (center : LayerVertex i) :
    LocalNeighbor i center.1.1 ↪ (graph p).neighborSet (embedSame b i center) where
  toFun x := ⟨embedLocal b i x.1, embedLocal_is_adjacent b i center x⟩
  inj' h := by
    intro y hxy
    apply Subtype.ext
    exact embedLocal_injective b i (congrArg Subtype.val hxy)

theorem core_degree_ge_800 {p : ℕ} (b : Fin p) (i : Fin 71) (v : LayerVertex i) :
    800 ≤ (graph p).degree (embedSame b i v) := by
  have hv := v.2
  unfold ValidCoord at hv
  have hvpos : 0 < sizeAt i v.1.1 := by omega
  have hcard := localNeighbor_card_ge_800 i v.1.1 hvpos
  have hle := Fintype.card_le_of_injective
    (localNeighborEmbedding b i v) (localNeighborEmbedding b i v).injective
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using hcard.trans hle

abbrev OuterCandidate := A0Vertex ⊕ A0Vertex

def IsOuterNeighbor (a : Fin 5) : OuterCandidate → Prop
  | Sum.inl x => x.1.1 ≠ a
  | Sum.inr _ => True

instance (a : Fin 5) : DecidablePred (IsOuterNeighbor a) := fun x => by
  rcases x with x | x <;> simp only [IsOuterNeighbor] <;> infer_instance

abbrev OuterNeighbor (a : Fin 5) := {x : OuterCandidate // IsOuterNeighbor a x}

theorem outerNeighbor_card_eq_800 :
    ∀ a : Fin 5, 0 < sizeAt ⟨0, by omega⟩ a →
      Fintype.card (OuterNeighbor a) = 800 := by
  decide

def leftOuterMap {p : ℕ} (hp : 0 < p) : OuterCandidate → Vertex p
  | Sum.inl x => Sum.inl x
  | Sum.inr x => embedSame (firstBlock hp) ⟨0, by omega⟩ x

theorem leftOuterMap_injective {p : ℕ} (hp : 0 < p) :
    Function.Injective (leftOuterMap hp) := by
  intro x y h
  rcases x with x | x <;> rcases y with y | y
  · exact congrArg Sum.inl (Sum.inl.inj h)
  · contradiction
  · contradiction
  · have hc := congrArg vertexCoord h
    exact congrArg Sum.inr (Subtype.ext (by simpa [leftOuterMap] using hc))

theorem leftOuterMap_is_adjacent {p : ℕ} (hp : 0 < p) (center : A0Vertex)
    (x : OuterNeighbor center.1.1) :
    (graph p).Adj (Sum.inl center) (leftOuterMap hp x.1) := by
  rcases x with ⟨x | x, hx⟩
  · rw [graph_adj]
    left
    refine ⟨rfl, ?_⟩
    intro hnat
    exact hx (Fin.ext hnat.symm)
  · rw [graph_adj]
    right
    refine ⟨?_, ?_⟩
    · change Nat.dist 0 1 = 1
      decide
    · change crossAllowedV (Sum.inl center)
        (embedSame (firstBlock hp) ⟨0, by omega⟩ x)
      intro h
      rcases h with ⟨hs, _, _⟩
      norm_num [vertexPartCount, embedSame, partCount, blockSpec, halfIndex,
        halfSpec, halfSpecs] at hs

def leftOuterEmbedding {p : ℕ} (hp : 0 < p) (center : A0Vertex) :
    OuterNeighbor center.1.1 ↪ (graph p).neighborSet (Sum.inl center) where
  toFun x := ⟨leftOuterMap hp x.1, leftOuterMap_is_adjacent hp center x⟩
  inj' x := by
    intro y hxy
    apply Subtype.ext
    exact leftOuterMap_injective hp (congrArg Subtype.val hxy)

def a0ToLast (x : A0Vertex) : LayerVertex ⟨70, by omega⟩ :=
  ⟨x.1, by
    simpa [ValidCoord, sizeAt, blockSpec, halfIndex, halfSpec, halfSpecs] using x.2⟩

def rightOuterMap {p : ℕ} (hp : 0 < p) : OuterCandidate → Vertex p
  | Sum.inl x => Sum.inr (Sum.inr x)
  | Sum.inr x => embedSame (lastBlock hp) ⟨70, by omega⟩ (a0ToLast x)

theorem rightOuterMap_injective {p : ℕ} (hp : 0 < p) :
    Function.Injective (rightOuterMap hp) := by
  intro x y h
  rcases x with x | x <;> rcases y with y | y
  · exact congrArg Sum.inl (Sum.inr.inj (Sum.inr.inj h))
  · change Sum.inr (Sum.inr x) =
      embedSame (lastBlock hp) ⟨70, by omega⟩ (a0ToLast y) at h
    simp [embedSame] at h
  · change embedSame (lastBlock hp) ⟨70, by omega⟩ (a0ToLast x) =
      Sum.inr (Sum.inr y) at h
    simp [embedSame] at h
  · have hc := congrArg vertexCoord h
    apply congrArg Sum.inr
    apply Subtype.ext
    simpa [rightOuterMap, a0ToLast] using hc

theorem rightOuterMap_is_adjacent {p : ℕ} (hp : 0 < p) (center : A0Vertex)
    (x : OuterNeighbor center.1.1) :
    (graph p).Adj (Sum.inr (Sum.inr center)) (rightOuterMap hp x.1) := by
  rcases x with ⟨x | x, hx⟩
  · rw [graph_adj]
    left
    refine ⟨rfl, ?_⟩
    intro hnat
    exact hx (Fin.ext hnat.symm)
  · rw [graph_adj]
    right
    refine ⟨?_, ?_⟩
    · change Nat.dist (71 * p + 1) (71 * (p - 1) + 71) = 1
      simp [Nat.dist]
      omega
    · change crossAllowedV (Sum.inr (Sum.inr center))
        (embedSame (lastBlock hp) ⟨70, by omega⟩ (a0ToLast x))
      intro h
      rcases h with ⟨hs, _, _⟩
      norm_num [vertexPartCount, embedSame, partCount, blockSpec, halfIndex,
        halfSpec, halfSpecs, a0ToLast] at hs

def rightOuterEmbedding {p : ℕ} (hp : 0 < p) (center : A0Vertex) :
    OuterNeighbor center.1.1 ↪ (graph p).neighborSet (Sum.inr (Sum.inr center)) where
  toFun x := ⟨rightOuterMap hp x.1, rightOuterMap_is_adjacent hp center x⟩
  inj' x := by
    intro y hxy
    apply Subtype.ext
    exact rightOuterMap_injective hp (congrArg Subtype.val hxy)

theorem left_degree_ge_800 {p : ℕ} (hp : 0 < p) (v : A0Vertex) :
    800 ≤ (graph p).degree (Sum.inl v) := by
  have hv := v.2
  unfold ValidCoord at hv
  have hvpos : 0 < sizeAt ⟨0, by omega⟩ v.1.1 := by omega
  have hcard := outerNeighbor_card_eq_800 v.1.1 hvpos
  have hle := Fintype.card_le_of_injective
    (leftOuterEmbedding hp v) (leftOuterEmbedding hp v).injective
  rw [hcard] at hle
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using hle

theorem right_degree_ge_800 {p : ℕ} (hp : 0 < p) (v : A0Vertex) :
    800 ≤ (graph p).degree (Sum.inr (Sum.inr v)) := by
  have hv := v.2
  unfold ValidCoord at hv
  have hvpos : 0 < sizeAt ⟨0, by omega⟩ v.1.1 := by omega
  have hcard := outerNeighbor_card_eq_800 v.1.1 hvpos
  have hle := Fintype.card_le_of_injective
    (rightOuterEmbedding hp v) (rightOuterEmbedding hp v).injective
  rw [hcard] at hle
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using hle

theorem all_degrees_ge_800 {p : ℕ} (hp : 0 < p) (v : Vertex p) :
    800 ≤ (graph p).degree v := by
  rcases v with v | ⟨⟨b, i, v⟩ | v⟩
  · exact left_degree_ge_800 hp v
  · exact core_degree_ge_800 b i v
  · exact right_degree_ge_800 hp v

theorem leftHub_neighbor_cases {p : ℕ} (hp : 0 < p)
    (w : (graph p).neighborSet (leftHub p)) :
    ∃ x : OuterNeighbor ⟨0, by omega⟩,
      (leftOuterEmbedding hp (firstCoord ⟨0, by omega⟩)) x = w := by
  rcases w with ⟨w, hw⟩
  change adjRel (leftHub p) w at hw
  rcases w with x | (⟨b, ⟨i, x⟩⟩ | x)
  · rcases hw with hw | hw
    · let z : OuterNeighbor ⟨0, by omega⟩ := ⟨Sum.inl x, by
        change x.1.1 ≠ ⟨0, by omega⟩
        intro hx
        apply hw.2
        change 0 = x.1.1.1
        exact (congrArg Fin.val hx).symm⟩
      refine ⟨z, ?_⟩
      apply Subtype.ext
      rfl
    · simp [leftHub, layerPos, Nat.dist] at hw
  · rcases hw with hw | hw
    · simp [leftHub, layerPos] at hw
    · have hpos : 71 * b.1 + i.1 + 1 = 1 := by
        simpa [leftHub, layerPos, Nat.dist] using hw.1
      have hbval : b.1 = 0 := by omega
      have hival : i.1 = 0 := by omega
      have hb : b = firstBlock hp := Fin.ext hbval
      have hi : i = (0 : Fin 71) := Fin.ext hival
      subst b
      subst i
      let z : OuterNeighbor ⟨0, by omega⟩ := ⟨Sum.inr x, by trivial⟩
      refine ⟨z, ?_⟩
      apply Subtype.ext
      rfl
  · rcases hw with hw | hw
    · simp [leftHub, layerPos] at hw
    · have hpos : 71 * p + 1 = 1 := by
        simpa [leftHub, layerPos, Nat.dist] using hw.1
      omega

theorem leftHub_degree_le_800 {p : ℕ} (hp : 0 < p) :
    (graph p).degree (leftHub p) ≤ 800 := by
  have hsurj : Function.Surjective
      (leftOuterEmbedding hp (firstCoord (0 : Fin 71))) :=
    leftHub_neighbor_cases hp
  have hle := Fintype.card_le_of_surjective
    (leftOuterEmbedding hp (firstCoord (0 : Fin 71))) hsurj
  have hcard : Fintype.card
      (OuterNeighbor (firstCoord (0 : Fin 71)).1.1) = 800 := by
    apply outerNeighbor_card_eq_800
    exact first_part_nonempty (0 : Fin 71)
  rw [hcard] at hle
  change (graph p).degree (Sum.inl (firstCoord (0 : Fin 71))) ≤ 800
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using hle

theorem minDegree_eq_800 {p : ℕ} (hp : 0 < p) : (graph p).minDegree = 800 := by
  letI : Nonempty (Vertex p) := ⟨leftHub p⟩
  apply Nat.le_antisymm
  · exact (graph p).minDegree_le_degree (leftHub p) |>.trans (leftHub_degree_le_800 hp)
  · exact (graph p).le_minDegree_of_forall_le_degree 800 (all_degrees_ge_800 hp)

/-! ## Clique number -/

theorem vertexPart_lt_count {p : ℕ} (v : Vertex p) :
    vertexPart v < vertexPartCount v := by
  rcases v with v | (⟨b, ⟨i, v⟩⟩ | v)
  · simpa [vertexPart, vertexPartCount] using
      validCoord_part_lt_count (0 : Fin 71) v.1 v.2
  · simpa [vertexPart, vertexPartCount] using validCoord_part_lt_count i v.1 v.2
  · simpa [vertexPart, vertexPartCount] using
      validCoord_part_lt_count (0 : Fin 71) v.1 v.2

theorem partCount_eq_of_layerPos_eq {p : ℕ} {v w : Vertex p}
    (h : layerPos v = layerPos w) : vertexPartCount v = vertexPartCount w := by
  rcases v with v | v
  · rcases w with w | w
    · rfl
    · rcases w with ⟨c, ⟨j, w⟩⟩ | w
      · simp [layerPos] at h
      · simp [layerPos] at h
  · rcases v with ⟨b, ⟨i, v⟩⟩ | v
    · rcases w with w | w
      · simp [layerPos] at h
      · rcases w with ⟨c, ⟨j, w⟩⟩ | w
        · have hi : i.1 = j.1 := by
            simp only [layerPos] at h
            omega
          exact congrArg partCount (Fin.ext hi)
        · simp [layerPos] at h
          omega
    · rcases w with w | w
      · simp [layerPos] at h
      · rcases w with ⟨c, ⟨j, w⟩⟩ | w
        · simp [layerPos] at h
          omega
        · rfl

theorem successive_layers_partCount_le_seven {p : ℕ} {v w : Vertex p}
    (h : layerPos v + 1 = layerPos w) :
    vertexPartCount v + vertexPartCount w ≤ 7 := by
  rcases v with v | v
  · rcases w with w | w
    · simp [layerPos] at h
    · rcases w with ⟨c, ⟨j, w⟩⟩ | w
      · have hc : c.1 = 0 := by simp [layerPos] at h; omega
        have hj : j.1 = 0 := by simp [layerPos] at h; omega
        have hjeq : j = (0 : Fin 71) := Fin.ext hj
        change partCount (0 : Fin 71) + partCount j ≤ 7
        rw [hjeq]
        norm_num [vertexPartCount, partCount, blockSpec, halfIndex, halfSpec, halfSpecs]
      · simp [layerPos] at h
        have hp : p = 0 := by omega
        subst p
        norm_num [vertexPartCount, partCount, blockSpec, halfIndex, halfSpec, halfSpecs]
  · rcases v with ⟨b, ⟨i, v⟩⟩ | v
    · rcases w with w | w
      · simp [layerPos] at h
      · rcases w with ⟨c, ⟨j, w⟩⟩ | w
        · have hjeq : j = cyclicNext i := by
            apply Fin.ext
            simp only [layerPos] at h
            by_cases hi : i.1 = 70
            · simp [cyclicNext, hi]
              omega
            · simp [cyclicNext, hi]
              omega
          have hcount := adjacent_part_count_le_six_or_seven i
          simpa [vertexPartCount, hjeq] using hcount
        · have hi : i.1 = 70 := by simp only [layerPos] at h; omega
          have hieq : i = (70 : Fin 71) := Fin.ext hi
          subst i
          norm_num [vertexPartCount, partCount, blockSpec, halfIndex, halfSpec, halfSpecs]
    · rcases w with w | w
      · simp [layerPos] at h
      · rcases w with ⟨c, ⟨j, w⟩⟩ | w <;> simp [layerPos] at h <;> omega

def partKey {p : ℕ} (v : Vertex p) : ℕ × ℕ := (layerPos v, vertexPart v)

theorem partKey_injOn_clique {p : ℕ} {s : Finset (Vertex p)}
    (hc : (graph p).IsClique s) : Set.InjOn partKey (↑s : Set (Vertex p)) := by
  intro v hv w hw hkey
  by_contra hvw
  have hadj := hc hv hw hvw
  have hpos : layerPos v = layerPos w := congrArg Prod.fst hkey
  have hpart : vertexPart v = vertexPart w := congrArg Prod.snd hkey
  rcases hadj with hadj | hadj
  · exact hadj.2 hpart
  · rw [hpos, Nat.dist_self] at hadj
    omega

theorem clique_position_window {p : ℕ} {s : Finset (Vertex p)}
    (hc : (graph p).IsClique s) (hs : s.Nonempty) :
    ∃ (u : Vertex p) (hu : u ∈ s),
      ∀ v ∈ s, layerPos u ≤ layerPos v ∧ layerPos v ≤ layerPos u + 1 := by
  let positions : Finset ℕ := s.image layerPos
  have hpne : positions.Nonempty := hs.image layerPos
  let m : ℕ := positions.min' hpne
  have hmmem : m ∈ positions := Finset.min'_mem positions hpne
  obtain ⟨u, hu, hum⟩ := Finset.mem_image.mp hmmem
  refine ⟨u, hu, ?_⟩
  intro v hv
  have hmin : m ≤ layerPos v :=
    Finset.min'_le positions (layerPos v) (Finset.mem_image_of_mem layerPos hv)
  have hdist : Nat.dist m (layerPos v) ≤ 1 := by
    by_cases huv : u = v
    · subst v
      simp [hum]
    · have hadj := hc hu hv huv
      simpa [hum] using adj_layer_dist_le_one hadj
  constructor
  · simpa [hum] using hmin
  · rw [Nat.dist_eq_sub_of_le hmin] at hdist
    omega

theorem not_adj_of_successive_last_parts {p : ℕ} {v w : Vertex p}
    (hpos : layerPos v + 1 = layerPos w)
    (hsum : vertexPartCount v + vertexPartCount w = 7)
    (hvlast : vertexPart v + 1 = vertexPartCount v)
    (hwlast : vertexPart w + 1 = vertexPartCount w) :
    ¬(graph p).Adj v w := by
  intro hadj
  rcases hadj with hadj | hadj
  · omega
  · exact hadj.2 ⟨hsum, hvlast, hwlast⟩

/-- Every clique in the constructed graph has at most six vertices.  The proof
is an explicit six-coloring of the one or two layers occupied by the clique. -/
theorem clique_card_le_six {p : ℕ} {s : Finset (Vertex p)}
    (hc : (graph p).IsClique s) : s.card ≤ 6 := by
  by_cases hsempty : s = ∅
  · simp [hsempty]
  have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hsempty
  obtain ⟨u, hu, hwindow⟩ := clique_position_window hc hsne
  have hpos (x : {v // v ∈ s}) :
      layerPos x.1 = layerPos u ∨ layerPos x.1 = layerPos u + 1 := by
    have hx := hwindow x.1 x.2
    omega
  by_cases hupp : ∃ w ∈ s, layerPos w = layerPos u + 1
  · obtain ⟨w, hw, hwpos⟩ := hupp
    have hsumle : vertexPartCount u + vertexPartCount w ≤ 7 := by
      apply successive_layers_partCount_le_seven
      omega
    by_cases hsum6 : vertexPartCount u + vertexPartCount w ≤ 6
    · let rawColor : {v // v ∈ s} → ℕ := fun x =>
        if layerPos x.1 = layerPos u then vertexPart x.1
        else vertexPartCount u + vertexPart x.1
      have hraw_lt (x : {v // v ∈ s}) : rawColor x < 6 := by
        have hxpart := vertexPart_lt_count x.1
        have hxpos := hpos x
        by_cases hxlow : layerPos x.1 = layerPos u
        · have huq := vertexPartCount_le_five u
          have hxu := partCount_eq_of_layerPos_eq hxlow
          simp [rawColor, hxlow]
          rw [hxu] at hxpart
          omega
        · have hxupper : layerPos x.1 = layerPos w := by omega
          have hxq := partCount_eq_of_layerPos_eq hxupper
          simp [rawColor, hxlow]
          rw [hxq] at hxpart
          omega
      let color : {v // v ∈ s} → Fin 6 := fun x => ⟨rawColor x, hraw_lt x⟩
      have hcolorinj : Function.Injective color := by
        intro x y hxy
        have hraw : rawColor x = rawColor y := congrArg Fin.val hxy
        have hxpos := hpos x
        have hypos := hpos y
        by_cases hxlow : layerPos x.1 = layerPos u <;>
          by_cases hylow : layerPos y.1 = layerPos u
        · apply Subtype.ext
          apply partKey_injOn_clique hc x.2 y.2
          apply Prod.ext
          · exact hxlow.trans hylow.symm
          · simpa [partKey, rawColor, hxlow, hylow] using hraw
        · have hypart := vertexPart_lt_count y.1
          have hyupper : layerPos y.1 = layerPos w := by omega
          have hyq := partCount_eq_of_layerPos_eq hyupper
          simp [rawColor, hxlow, hylow] at hraw
          have hxpart := vertexPart_lt_count x.1
          have hxu := partCount_eq_of_layerPos_eq hxlow
          omega
        · have hxpart := vertexPart_lt_count x.1
          have hxupper : layerPos x.1 = layerPos w := by omega
          have hxq := partCount_eq_of_layerPos_eq hxupper
          simp [rawColor, hxlow, hylow] at hraw
          have hypart := vertexPart_lt_count y.1
          have hyu := partCount_eq_of_layerPos_eq hylow
          omega
        · have hxupper : layerPos x.1 = layerPos w := by omega
          have hyupper : layerPos y.1 = layerPos w := by omega
          apply Subtype.ext
          apply partKey_injOn_clique hc x.2 y.2
          apply Prod.ext
          · exact hxupper.trans hyupper.symm
          · simp [rawColor, hxlow, hylow] at hraw
            change vertexPart x.1 = vertexPart y.1
            omega
      have hcard := Fintype.card_le_of_injective color hcolorinj
      simpa using hcard
    · have hsum7 : vertexPartCount u + vertexPartCount w = 7 := by omega
      have huPos : 0 < vertexPartCount u := by
        have := vertexPart_lt_count u
        omega
      let rawColor : {v // v ∈ s} → ℕ := fun x =>
        if layerPos x.1 = layerPos u then vertexPart x.1
        else if vertexPart x.1 + 1 = vertexPartCount x.1 then
          vertexPartCount u - 1
        else vertexPartCount u + vertexPart x.1
      have hraw_lt (x : {v // v ∈ s}) : rawColor x < 6 := by
        have hxpart := vertexPart_lt_count x.1
        have hxpos := hpos x
        by_cases hxlow : layerPos x.1 = layerPos u
        · have huq := vertexPartCount_le_five u
          have hxu := partCount_eq_of_layerPos_eq hxlow
          simp [rawColor, hxlow]
          rw [hxu] at hxpart
          omega
        · have hxupper : layerPos x.1 = layerPos w := by omega
          have hxq := partCount_eq_of_layerPos_eq hxupper
          by_cases hxlast : vertexPart x.1 + 1 = vertexPartCount x.1
          · simp [rawColor, hxlow, hxlast]
            omega
          · simp [rawColor, hxlow, hxlast]
            rw [hxq] at hxpart
            omega
      let color : {v // v ∈ s} → Fin 6 := fun x => ⟨rawColor x, hraw_lt x⟩
      have hcolorinj : Function.Injective color := by
        intro x y hxy
        have hraw : rawColor x = rawColor y := congrArg Fin.val hxy
        have hxpos := hpos x
        have hypos := hpos y
        have hxpart := vertexPart_lt_count x.1
        have hypart := vertexPart_lt_count y.1
        by_cases hxlow : layerPos x.1 = layerPos u <;>
          by_cases hylow : layerPos y.1 = layerPos u
        · apply Subtype.ext
          apply partKey_injOn_clique hc x.2 y.2
          apply Prod.ext
          · exact hxlow.trans hylow.symm
          · simpa [partKey, rawColor, hxlow, hylow] using hraw
        · have hyupper : layerPos y.1 = layerPos w := by omega
          have hyq := partCount_eq_of_layerPos_eq hyupper
          have hxu := partCount_eq_of_layerPos_eq hxlow
          by_cases hylast : vertexPart y.1 + 1 = vertexPartCount y.1
          · have hxlast : vertexPart x.1 + 1 = vertexPartCount x.1 := by
              simp [rawColor, hxlow, hylow, hylast] at hraw
              omega
            have hne : x.1 ≠ y.1 := by
              intro h
              have := congrArg layerPos h
              omega
            have hadj := hc x.2 y.2 hne
            exact False.elim
              ((not_adj_of_successive_last_parts (p := p) (v := x.1) (w := y.1)
                (by omega) (by omega) hxlast hylast) hadj)
          · simp [rawColor, hxlow, hylow, hylast] at hraw
            omega
        · have hxupper : layerPos x.1 = layerPos w := by omega
          have hxq := partCount_eq_of_layerPos_eq hxupper
          have hyu := partCount_eq_of_layerPos_eq hylow
          by_cases hxlast : vertexPart x.1 + 1 = vertexPartCount x.1
          · have hylast : vertexPart y.1 + 1 = vertexPartCount y.1 := by
              simp [rawColor, hxlow, hylow, hxlast] at hraw
              omega
            have hne : y.1 ≠ x.1 := by
              intro h
              have := congrArg layerPos h
              omega
            have hadj := hc y.2 x.2 hne
            exact False.elim
              ((not_adj_of_successive_last_parts (p := p) (v := y.1) (w := x.1)
                (by omega) (by omega) hylast hxlast) hadj)
          · simp [rawColor, hxlow, hylow, hxlast] at hraw
            omega
        · have hxupper : layerPos x.1 = layerPos w := by omega
          have hyupper : layerPos y.1 = layerPos w := by omega
          have hxq := partCount_eq_of_layerPos_eq hxupper
          have hyq := partCount_eq_of_layerPos_eq hyupper
          by_cases hxlast : vertexPart x.1 + 1 = vertexPartCount x.1 <;>
            by_cases hylast : vertexPart y.1 + 1 = vertexPartCount y.1
          · apply Subtype.ext
            apply partKey_injOn_clique hc x.2 y.2
            apply Prod.ext
            · exact hxupper.trans hyupper.symm
            · change vertexPart x.1 = vertexPart y.1
              omega
          · simp [rawColor, hxlow, hylow, hxlast, hylast] at hraw
            omega
          · simp [rawColor, hxlow, hylow, hxlast, hylast] at hraw
            omega
          · apply Subtype.ext
            apply partKey_injOn_clique hc x.2 y.2
            apply Prod.ext
            · exact hxupper.trans hyupper.symm
            · simp [rawColor, hxlow, hylow, hxlast, hylast] at hraw
              change vertexPart x.1 = vertexPart y.1
              omega
      have hcard := Fintype.card_le_of_injective color hcolorinj
      simpa using hcard
  · let color : {v // v ∈ s} → Fin 6 := fun x =>
      ⟨vertexPart x.1, by
        have hx := vertexPart_lt_count x.1
        have hq := vertexPartCount_le_five x.1
        omega⟩
    have hsame (x : {v // v ∈ s}) : layerPos x.1 = layerPos u := by
      rcases hpos x with hx | hx
      · exact hx
      · exact False.elim (hupp ⟨x.1, x.2, hx⟩)
    have hcolorinj : Function.Injective color := by
      intro x y hxy
      apply Subtype.ext
      apply partKey_injOn_clique hc x.2 y.2
      apply Prod.ext
      · exact (hsame x).trans (hsame y).symm
      · exact congrArg Fin.val hxy
    have hcard := Fintype.card_le_of_injective color hcolorinj
    simpa using hcard

theorem graph_cliqueFree_seven (p : ℕ) : (graph p).CliqueFree 7 := by
  intro s hs
  have hle := clique_card_le_six hs.1
  have heq := hs.card_eq
  omega

end Erdos612K7
