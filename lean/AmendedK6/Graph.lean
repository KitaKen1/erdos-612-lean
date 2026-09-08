import AmendedK6.Data

/-!
# The constructed graph

The definition implements the stated edge rule. This file proves connectedness,
`K₆`-freeness, the minimum degree, and the required diameter lower bound.
-/

namespace Erdos612AmendedK6

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def layerPos {m : ℕ} : Vertex m → ℕ
  | Sum.inl c => c.1.val
  | Sum.inr (Sum.inl (b, ⟨i, _⟩)) => 33 * b.val + i.val + 2
  | Sum.inr (Sum.inr c) => 33 * m + 2 + c.1.val

def vertexPartCount {m : ℕ} : Vertex m → ℕ
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl (_, ⟨i, _⟩)) => partCount i
  | Sum.inr (Sum.inr _) => 1

def vertexPart {m : ℕ} : Vertex m → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl (_, ⟨_, ⟨a, _⟩⟩)) => a.val
  | Sum.inr (Sum.inr _) => 0

def crossAllowedV {m : ℕ} (v w : Vertex m) : Prop :=
  ¬(vertexPartCount v + vertexPartCount w = 6 ∧
    vertexPart v + 1 = vertexPartCount v ∧
    vertexPart w + 1 = vertexPartCount w)

instance {m : ℕ} (v w : Vertex m) : Decidable (crossAllowedV v w) := by
  unfold crossAllowedV
  infer_instance

def adjRel {m : ℕ} (v w : Vertex m) : Prop :=
  (layerPos v = layerPos w ∧ vertexPart v ≠ vertexPart w) ∨
  (Nat.dist (layerPos v) (layerPos w) = 1 ∧ crossAllowedV v w)

instance {m : ℕ} : DecidableRel (@adjRel m) := fun _ _ => by
  unfold adjRel
  infer_instance

theorem crossAllowedV_comm {m : ℕ} (v w : Vertex m) :
    crossAllowedV v w ↔ crossAllowedV w v := by
  unfold crossAllowedV
  constructor <;> rintro h ⟨hs, hv, hw⟩
  · exact h ⟨by omega, hw, hv⟩
  · exact h ⟨by omega, hw, hv⟩

def graph (m : ℕ) : SimpleGraph (Vertex m) where
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

instance (m : ℕ) : DecidableRel (graph m).Adj := fun _ _ => by
  change Decidable (adjRel _ _)
  infer_instance

@[simp] theorem graph_adj {m : ℕ} {v w : Vertex m} :
    (graph m).Adj v w ↔ adjRel v w := Iff.rfl

/-! ## Transfer to `SimpleGraph (Fin n)`, as used by the FClike statement -/

noncomputable def vertexEquivFin (m : ℕ) :
    Vertex m ≃ Fin (order m) := Fintype.equivFinOfCardEq (vertex_card m)

noncomputable def graphFin (m : ℕ) :
    SimpleGraph (Fin (order m)) :=
  (graph m).map (vertexEquivFin m).toEmbedding

noncomputable def graphIsoFin (m : ℕ) : graph m ≃g graphFin m :=
  SimpleGraph.Iso.map (vertexEquivFin m) (graph m)

noncomputable instance graphFin_decidableAdj (m : ℕ) :
    DecidableRel (graphFin m).Adj := Classical.decRel _

theorem vertexPartCount_le_four {m : ℕ} (v : Vertex m) :
    vertexPartCount v ≤ 4 := by
  rcases v with v | ⟨⟨b, i, v⟩ | v⟩
  · simp [vertexPartCount]
  · exact (partCount_bounds i).2
  · simp [vertexPartCount]

theorem vertexPart_lt_count {m : ℕ} (v : Vertex m) :
    vertexPart v < vertexPartCount v := by
  rcases v with v | ⟨⟨b, i, ⟨a, x⟩⟩ | v⟩
  · simp [vertexPart, vertexPartCount]
  · exact a.isLt
  · simp [vertexPart, vertexPartCount]

theorem partCount_eq_of_layerPos_eq {m : ℕ} {v w : Vertex m}
    (h : layerPos v = layerPos w) : vertexPartCount v = vertexPartCount w := by
  rcases v with v | ⟨⟨b, i, x⟩ | v⟩
  · rcases w with w | ⟨⟨c, j, y⟩ | w⟩
    · simp [vertexPartCount]
    · simp [layerPos] at h; omega
    · simp [layerPos] at h; omega
  · rcases w with w | ⟨⟨c, j, y⟩ | w⟩
    · simp [layerPos] at h; omega
    · have hb : b.val = c.val := by simp [layerPos] at h; omega
      have hi : i.val = j.val := by simp [layerPos] at h; omega
      simpa [vertexPartCount] using congrArg partCount (Fin.ext hi)
    · simp [layerPos] at h; omega
  · rcases w with w | ⟨⟨c, j, y⟩ | w⟩
    · simp [layerPos] at h; omega
    · simp [layerPos] at h; omega
    · simp [vertexPartCount]

theorem successive_layers_partCount_le_six {m : ℕ} {v w : Vertex m}
    (h : layerPos v + 1 = layerPos w) :
    vertexPartCount v + vertexPartCount w ≤ 6 := by
  rcases v with v | ⟨⟨b, i, x⟩ | v⟩
  · rcases w with w | ⟨⟨c, j, y⟩ | w⟩
    · norm_num [vertexPartCount]
    · have hq := (partCount_bounds j).2
      simp [vertexPartCount]
      omega
    · norm_num [vertexPartCount]
  · rcases w with w | ⟨⟨c, j, y⟩ | w⟩
    · simp [layerPos, vertexPartCount] at h ⊢; omega
    · have hij : j = cyclicNext i := by
        apply Fin.ext
        simp only [layerPos] at h
        by_cases hi : i.1 = 32
        · simp [cyclicNext, hi]; omega
        · simp [cyclicNext, hi]; omega
      have hq : partCount j = partCount (cyclicNext i) := congrArg partCount hij
      change partCount i + partCount j ≤ 6
      rw [hq]
      exact adjacent_partCount_le_six i
    · simp [vertexPartCount] at ⊢
      exact Nat.add_le_add_right (partCount_bounds i).2 1 |>.trans (by decide)
  · rcases w with w | ⟨⟨c, j, y⟩ | w⟩ <;>
      simp [layerPos, vertexPartCount] at h ⊢ <;> omega

theorem adj_layer_dist_le_one {m : ℕ} {v w : Vertex m}
    (h : (graph m).Adj v w) : Nat.dist (layerPos v) (layerPos w) ≤ 1 := by
  rcases h with h | h
  · simp [h.1]
  · exact Nat.le_of_eq h.1

theorem partKey_injOn_clique {m : ℕ} {s : Finset (Vertex m)}
    (hc : (graph m).IsClique s) :
    Set.InjOn (fun v : Vertex m => (layerPos v, vertexPart v)) (↑s : Set (Vertex m)) := by
  intro v hv w hw hkey
  by_contra hvw
  have hadj := hc hv hw hvw
  have hpos : layerPos v = layerPos w := congrArg Prod.fst hkey
  have hpart : vertexPart v = vertexPart w := congrArg Prod.snd hkey
  rcases hadj with hadj | hadj
  · exact hadj.2 hpart
  · rw [hpos, Nat.dist_self] at hadj
    omega

theorem clique_position_window {m : ℕ} {s : Finset (Vertex m)}
    (hc : (graph m).IsClique s) (hs : s.Nonempty) :
    ∃ (u : Vertex m) (hu : u ∈ s),
      ∀ v ∈ s, layerPos u ≤ layerPos v ∧ layerPos v ≤ layerPos u + 1 := by
  let positions : Finset ℕ := s.image layerPos
  have hpne : positions.Nonempty := hs.image layerPos
  let z : ℕ := positions.min' hpne
  obtain ⟨u, hu, hzu⟩ := Finset.mem_image.mp (Finset.min'_mem positions hpne)
  refine ⟨u, hu, ?_⟩
  intro v hv
  have hmin : z ≤ layerPos v :=
    Finset.min'_le positions _ (Finset.mem_image_of_mem layerPos hv)
  have hdist : Nat.dist z (layerPos v) ≤ 1 := by
    by_cases huv : u = v
    · subst v; simp [z, hzu]
    · have hadj := hc hu hv huv
      simpa [hzu] using adj_layer_dist_le_one hadj
  constructor
  · simpa [hzu] using hmin
  · rw [Nat.dist_eq_sub_of_le hmin] at hdist
    omega

theorem not_adj_of_successive_last_parts {m : ℕ} {v w : Vertex m}
    (hpos : layerPos v + 1 = layerPos w)
    (hsum : vertexPartCount v + vertexPartCount w = 6)
    (hvlast : vertexPart v + 1 = vertexPartCount v)
    (hwlast : vertexPart w + 1 = vertexPartCount w) :
    ¬(graph m).Adj v w := by
  intro hadj
  rcases hadj with hadj | hadj
  · omega
  · exact hadj.2 ⟨hsum, hvlast, hwlast⟩

theorem clique_card_le_five {m : ℕ} {s : Finset (Vertex m)}
    (hc : (graph m).IsClique s) : s.card ≤ 5 := by
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
    have hsumle : vertexPartCount u + vertexPartCount w ≤ 6 := by
      apply successive_layers_partCount_le_six
      omega
    by_cases hsum5 : vertexPartCount u + vertexPartCount w ≤ 5
    · let rawColor : {v // v ∈ s} → ℕ := fun x =>
        if layerPos x.1 = layerPos u then vertexPart x.1
        else vertexPartCount u + vertexPart x.1
      have hraw_lt (x : {v // v ∈ s}) : rawColor x < 5 := by
        have hxpart := vertexPart_lt_count x.1
        have hxpos := hpos x
        by_cases hxlow : layerPos x.1 = layerPos u
        · have hxu := partCount_eq_of_layerPos_eq hxlow
          simp [rawColor, hxlow]
          rw [hxu] at hxpart
          omega
        · have hxupper : layerPos x.1 = layerPos w := by omega
          have hxq := partCount_eq_of_layerPos_eq hxupper
          simp [rawColor, hxlow]
          rw [hxq] at hxpart
          omega
      let color : {v // v ∈ s} → Fin 5 := fun x => ⟨rawColor x, hraw_lt x⟩
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
          · simpa [rawColor, hxlow, hylow] using hraw
        · have hyupper : layerPos y.1 = layerPos w := by omega
          have hyq := partCount_eq_of_layerPos_eq hyupper
          have hxu := partCount_eq_of_layerPos_eq hxlow
          have hxpart := vertexPart_lt_count x.1
          have hypart := vertexPart_lt_count y.1
          simp [rawColor, hxlow, hylow] at hraw
          omega
        · have hxupper : layerPos x.1 = layerPos w := by omega
          have hxq := partCount_eq_of_layerPos_eq hxupper
          have hyu := partCount_eq_of_layerPos_eq hylow
          have hxpart := vertexPart_lt_count x.1
          have hypart := vertexPart_lt_count y.1
          simp [rawColor, hxlow, hylow] at hraw
          omega
        · apply Subtype.ext
          apply partKey_injOn_clique hc x.2 y.2
          apply Prod.ext
          · have hxupper : layerPos x.1 = layerPos w := by omega
            have hyupper : layerPos y.1 = layerPos w := by omega
            exact hxupper.trans hyupper.symm
          · simp [rawColor, hxlow, hylow] at hraw
            exact hraw
      have hcard := Fintype.card_le_of_injective color hcolorinj
      simpa using hcard
    · have hsum6 : vertexPartCount u + vertexPartCount w = 6 := by omega
      let rawColor : {v // v ∈ s} → ℕ := fun x =>
        if layerPos x.1 = layerPos u then vertexPart x.1
        else if vertexPart x.1 + 1 = vertexPartCount x.1 then
          vertexPartCount u - 1
        else vertexPartCount u + vertexPart x.1
      have hraw_lt (x : {v // v ∈ s}) : rawColor x < 5 := by
        have hxpart := vertexPart_lt_count x.1
        have hxpos := hpos x
        by_cases hxlow : layerPos x.1 = layerPos u
        · have hxu := partCount_eq_of_layerPos_eq hxlow
          have huq := vertexPartCount_le_four u
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
      let color : {v // v ∈ s} → Fin 5 := fun x => ⟨rawColor x, hraw_lt x⟩
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
          · simpa [rawColor, hxlow, hylow] using hraw
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
              ((not_adj_of_successive_last_parts (v := x.1) (w := y.1)
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
              ((not_adj_of_successive_last_parts (v := y.1) (w := x.1)
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
            have huq := vertexPartCount_le_four u
            have huPos : 0 < vertexPartCount u := by
              have hu := vertexPart_lt_count u
              omega
            omega
          · simp [rawColor, hxlow, hylow, hxlast, hylast] at hraw
            have huq := vertexPartCount_le_four u
            have huPos : 0 < vertexPartCount u := by
              have hu := vertexPart_lt_count u
              omega
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
  · let color : {v // v ∈ s} → Fin 5 := fun x =>
      ⟨vertexPart x.1, by
        have hx := vertexPart_lt_count x.1
        have hq := vertexPartCount_le_four x.1
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

theorem graph_cliqueFree_six_raw (m : ℕ) : (graph m).CliqueFree 6 := by
  intro s hs
  have hle := clique_card_le_five hs.1
  have heq := hs.card_eq
  omega

/-! ## Degree certificates -/

def localCrossAllowed (i j : Fin 33)
    (a : Fin (partCount i)) (b : Fin (partCount j)) : Prop :=
  crossAllowed i j a b = true

instance (i j : Fin 33) (a : Fin (partCount i)) (b : Fin (partCount j)) :
    Decidable (localCrossAllowed i j a b) := by
  unfold localCrossAllowed
  infer_instance

abbrev LocalCandidate (i : Fin 33) :=
  LayerVertex (cyclicPrev i) ⊕ (LayerVertex i ⊕ LayerVertex (cyclicNext i))

def IsLocalNeighbor (i : Fin 33) (a : Fin (partCount i)) :
    LocalCandidate i → Prop
  | Sum.inl x => localCrossAllowed i (cyclicPrev i) a x.1
  | Sum.inr (Sum.inl x) => x.1 ≠ a
  | Sum.inr (Sum.inr x) => localCrossAllowed i (cyclicNext i) a x.1

instance (i : Fin 33) (a : Fin (partCount i)) :
    DecidablePred (IsLocalNeighbor i a) := fun x => by
  rcases x with x | (x | x) <;> simp only [IsLocalNeighbor] <;> infer_instance

abbrev LocalNeighbor (i : Fin 33) (a : Fin (partCount i)) :=
  {x : LocalCandidate i // IsLocalNeighbor i a x}

private theorem card_layer_subtype_sum (i : Fin 33) (P : Fin (partCount i) → Prop)
    [DecidablePred P] :
    Fintype.card {x : LayerVertex i // P x.1} =
      (Finset.univ.filter P).sum (partSize i) := by
  classical
  rw [Fintype.card_congr (Equiv.subtypeSigmaEquiv (fun a : Fin (partCount i) =>
    Fin (partSize i a)) P)]
  simp only [Fintype.card_sigma, Fintype.card_subtype, Fintype.card_fin]
  simpa using (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
    (f := partSize i) (p := P))

theorem localNeighbor_card_eq (i : Fin 33) (a : Fin (partCount i)) :
    Fintype.card (LocalNeighbor i a) = localDegree i a := by
  classical
  let e₁ : LocalNeighbor i a ≃
      {x : LayerVertex (cyclicPrev i) // localCrossAllowed i (cyclicPrev i) a x.1} ⊕
      {x : LayerVertex i ⊕ LayerVertex (cyclicNext i) //
        IsLocalNeighbor i a (Sum.inr x)} :=
    Equiv.subtypeSum
  let e₂ : {x : LayerVertex i ⊕ LayerVertex (cyclicNext i) //
      IsLocalNeighbor i a (Sum.inr x)} ≃
      {x : LayerVertex i // x.1 ≠ a} ⊕
      {x : LayerVertex (cyclicNext i) // localCrossAllowed i (cyclicNext i) a x.1} :=
    Equiv.subtypeSum
  have hc := Fintype.card_congr (e₁.trans ((Equiv.refl _).sumCongr e₂))
  rw [hc]
  simp only [Fintype.card_sum]
  rw [card_layer_subtype_sum]
  have hmid := card_layer_subtype_sum i (fun x => x ≠ a)
  rw [hmid]
  rw [card_layer_subtype_sum]
  have hprev : Finset.filter (localCrossAllowed i (cyclicPrev i) a) Finset.univ =
      Finset.filter (fun b => crossAllowed i (cyclicPrev i) a b) Finset.univ := by
    ext b
    rfl
  have hnext : Finset.filter (localCrossAllowed i (cyclicNext i) a) Finset.univ =
      Finset.filter (fun b => crossAllowed i (cyclicNext i) a b) Finset.univ := by
    ext b
    rfl
  rw [hprev, hnext]
  simp [localDegree, Nat.add_assoc]
theorem localNeighbor_card_ge_2200 :
    ∀ i : Fin 33, ∀ a : Fin (partCount i),
      0 < partSize i a → 2200 ≤ Fintype.card (LocalNeighbor i a) := by
  intro i a ha
  rw [localNeighbor_card_eq]
  exact localDegree_ge_2200 i a

private theorem layerVertex_transport_fst {i j : Fin 33} (h : i = j)
    (x : LayerVertex i) : (h ▸ x).1.val = x.1.val := by
  cases h
  rfl

def coreEmbedPrev {m : ℕ} (hm : 0 < m) (b : Fin m) (i : Fin 33)
    (x : LayerVertex (cyclicPrev i)) : Vertex m :=
  if hi : i.1 = 0 then
    Sum.inl (⟨1, ⟨0, by omega⟩⟩)
  else
    let j : Fin 33 := ⟨i.1 - 1, by omega⟩
    have hj : cyclicPrev i = j := by
      apply Fin.ext
      have hi_le : i.1 ≤ 32 := by omega
      have hi_pos : 1 ≤ i.1 := by omega
      change (i.1 + 32) % 33 = i.1 - 1
      rw [Nat.mod_eq_sub_mod (by omega : i.1 + 32 ≥ 33)]
      rw [Nat.mod_eq_of_lt (by omega : i.1 + 32 - 33 < 33)]
      omega
    Sum.inr (Sum.inl (b, ⟨j, hj ▸ x⟩))

def coreEmbedSame {m : ℕ} (b : Fin m) (i : Fin 33)
    (x : LayerVertex i) : Vertex m :=
  Sum.inr (Sum.inl (b, ⟨i, x⟩))

def coreEmbedNext {m : ℕ} (hm : 0 < m) (b : Fin m) (i : Fin 33)
    (x : LayerVertex (cyclicNext i)) : Vertex m :=
  if hi : i.1 = 32 then
    Sum.inr (Sum.inr (⟨0, by omega⟩, ⟨0, by omega⟩))
  else
    have hi' : i.1 ≤ 31 := by omega
    have hij : i.1 + 1 ≤ 32 := by omega
    let j : Fin 33 := ⟨i.1 + 1, Nat.lt_succ_iff.mpr hij⟩
    have hj : cyclicNext i = j := by
      apply Fin.ext
      change (i.1 + 1) % 33 = i.1 + 1
      rw [Nat.mod_eq_of_lt (by omega)]
    Sum.inr (Sum.inl (b, ⟨j, hj ▸ x⟩))

def coreEmbedLocal {m : ℕ} (hm : 0 < m) (b : Fin m) (i : Fin 33) :
    LocalCandidate i → Vertex m
  | Sum.inl x => coreEmbedPrev hm b i x
  | Sum.inr (Sum.inl x) => coreEmbedSame b i x
  | Sum.inr (Sum.inr x) => coreEmbedNext hm b i x

@[simp] theorem coreEmbedSame_layerPos {m : ℕ} (b : Fin m) (i : Fin 33)
    (x : LayerVertex i) : layerPos (coreEmbedSame b i x) = 33 * b.1 + i.1 + 2 := rfl

theorem coreEmbedPrev_layerPos {m : ℕ} (hm : 0 < m) (b : Fin m) (i : Fin 33)
    (x : LayerVertex (cyclicPrev i)) (hi : i.1 ≠ 0) :
    layerPos (coreEmbedPrev hm b i x) + 1 = 33 * b.1 + i.1 + 2 := by
  simp [coreEmbedPrev, hi, layerPos]
  omega

theorem coreEmbedNext_layerPos {m : ℕ} (hm : 0 < m) (b : Fin m) (i : Fin 33)
    (x : LayerVertex (cyclicNext i)) (hi : i.1 ≠ 32) :
    layerPos (coreEmbedNext hm b i x) = 33 * b.1 + i.1 + 3 := by
  simp [coreEmbedNext, hi, layerPos]
  omega

@[simp] theorem coreEmbedSame_part {m : ℕ} (b : Fin m) (i : Fin 33)
    (x : LayerVertex i) : vertexPart (coreEmbedSame b i x) = x.1.1 := rfl

theorem coreEmbedPrev_part {m : ℕ} (hm : 0 < m) (b : Fin m) (i : Fin 33)
    (x : LayerVertex (cyclicPrev i)) (hi : i.1 ≠ 0) :
    vertexPart (coreEmbedPrev hm b i x) = x.1.1 := by
  simp only [coreEmbedPrev, dif_neg hi, vertexPart]
  exact layerVertex_transport_fst _ x

theorem coreEmbedNext_part {m : ℕ} (hm : 0 < m) (b : Fin m) (i : Fin 33)
    (x : LayerVertex (cyclicNext i)) (hi : i.1 ≠ 32) :
    vertexPart (coreEmbedNext hm b i x) = x.1.1 := by
  simp only [coreEmbedNext, dif_neg hi, vertexPart]
  exact layerVertex_transport_fst _ x

theorem coreEmbedPrev_count {m : ℕ} (hm : 0 < m) (b : Fin m) (i : Fin 33)
    (x : LayerVertex (cyclicPrev i)) (hi : i.1 ≠ 0) :
    vertexPartCount (coreEmbedPrev hm b i x) = partCount (cyclicPrev i) := by
  let j : Fin 33 := ⟨i.1 - 1, by omega⟩
  have hj : cyclicPrev i = j := by
    apply Fin.ext
    change (i.1 + 32) % 33 = i.1 - 1
    rw [Nat.mod_eq_sub_mod (by omega : i.1 + 32 ≥ 33)]
    rw [Nat.mod_eq_of_lt (by omega : i.1 + 32 - 33 < 33)]
    omega
  simp [coreEmbedPrev, hi, vertexPartCount, j, hj]

theorem coreEmbedNext_count {m : ℕ} (hm : 0 < m) (b : Fin m) (i : Fin 33)
    (x : LayerVertex (cyclicNext i)) (hi : i.1 ≠ 32) :
    vertexPartCount (coreEmbedNext hm b i x) = partCount (cyclicNext i) := by
  let j : Fin 33 := ⟨i.1 + 1, by omega⟩
  have hj : cyclicNext i = j := by
    apply Fin.ext
    change (i.1 + 1) % 33 = i.1 + 1
    rw [Nat.mod_eq_of_lt (by omega)]
  simp [coreEmbedNext, hi, vertexPartCount, j, hj]

theorem coreEmbedLocal_injective {m : ℕ} (hm : 0 < m) (b : Fin m) (i : Fin 33)
    (hi0 : i.1 ≠ 0) (hi32 : i.1 ≠ 32) :
    Function.Injective (coreEmbedLocal hm b i) := by
  intro x y hxy
  rcases x with x | (x | x) <;> rcases y with y | (y | y)
  · have hp := congrArg layerPos hxy
    simp only [coreEmbedLocal] at hp
    have hx := coreEmbedPrev_layerPos hm b i x hi0
    have hy := coreEmbedPrev_layerPos hm b i y hi0
    simpa [coreEmbedLocal, coreEmbedPrev, hi0] using hxy
  · have hp := congrArg layerPos hxy
    simp only [coreEmbedLocal] at hp
    have hx := coreEmbedPrev_layerPos hm b i x hi0
    have hy := coreEmbedSame_layerPos b i y
    omega
  · have hp := congrArg layerPos hxy
    simp only [coreEmbedLocal] at hp
    have hx := coreEmbedPrev_layerPos hm b i x hi0
    have hy := coreEmbedNext_layerPos hm b i y hi32
    omega
  · have hp := congrArg layerPos hxy
    simp only [coreEmbedLocal] at hp
    have hx := coreEmbedSame_layerPos b i x
    have hy := coreEmbedPrev_layerPos hm b i y hi0
    omega
  · simpa [coreEmbedLocal, coreEmbedSame] using hxy
  · have hp := congrArg layerPos hxy
    simp only [coreEmbedLocal] at hp
    have hx := coreEmbedSame_layerPos b i x
    have hy := coreEmbedNext_layerPos hm b i y hi32
    omega
  · have hp := congrArg layerPos hxy
    simp only [coreEmbedLocal] at hp
    have hx := coreEmbedNext_layerPos hm b i x hi32
    have hy := coreEmbedPrev_layerPos hm b i y hi0
    omega
  · have hp := congrArg layerPos hxy
    simp only [coreEmbedLocal] at hp
    have hx := coreEmbedNext_layerPos hm b i x hi32
    have hy := coreEmbedSame_layerPos b i y
    omega
  · simpa [coreEmbedLocal, coreEmbedNext, hi32] using hxy

theorem coreEmbedLocal_is_adjacent {m : ℕ} (hm : 0 < m) (b : Fin m) (i : Fin 33)
    (hi0 : i.1 ≠ 0) (hi32 : i.1 ≠ 32) (center : LayerVertex i)
    (x : LocalNeighbor i center.1) :
    (graph m).Adj (coreEmbedSame b i center) (coreEmbedLocal hm b i x.1) := by
  rcases x with ⟨x | (x | x), hx⟩
  · rw [graph_adj]
    change (graph m).Adj (coreEmbedSame b i center) (coreEmbedPrev hm b i x)
    right
    refine ⟨?_, ?_⟩
    · have hp := coreEmbedPrev_layerPos hm b i x hi0
      rw [coreEmbedSame_layerPos]
      simp [Nat.dist]
      omega
    · change localCrossAllowed i (cyclicPrev i) center.1 x.1 at hx
      change crossAllowedV (coreEmbedSame b i center) (coreEmbedPrev hm b i x)
      have hcount := coreEmbedPrev_count hm b i x hi0
      have hpart := coreEmbedPrev_part hm b i x hi0
      have hcountc : vertexPartCount (coreEmbedSame b i center) = partCount i := rfl
      have hpartc : vertexPart (coreEmbedSame b i center) = center.1.1 := rfl
      intro hdel
      rcases hdel with ⟨hs, hc, hl⟩
      have hs' : partCount i + partCount (cyclicPrev i) = 6 := by
        simpa [hcountc, hcount] using hs
      have hc' : center.1.1 + 1 = partCount i := by
        simpa [hcountc, hpartc] using hc
      have hl' : x.1.1 + 1 = partCount (cyclicPrev i) := by
        simpa [hcount, hpart] using hl
      have hxa := hx
      simp [localCrossAllowed, crossAllowed] at hxa
      rcases hxa with hxa | hxa
      · rcases hxa with hxa | hxa
        · exact hxa hs'
        · exact hxa hc'
      · exact hxa hl'
  · rw [graph_adj]
    change (graph m).Adj (coreEmbedSame b i center) (coreEmbedSame b i x)
    left
    refine ⟨rfl, ?_⟩
    intro h
    apply hx
    exact Fin.ext h.symm
  · rw [graph_adj]
    change (graph m).Adj (coreEmbedSame b i center) (coreEmbedNext hm b i x)
    right
    refine ⟨?_, ?_⟩
    · have hp := coreEmbedNext_layerPos hm b i x hi32
      rw [coreEmbedSame_layerPos]
      simp [Nat.dist]
      omega
    · change localCrossAllowed i (cyclicNext i) center.1 x.1 at hx
      change crossAllowedV (coreEmbedSame b i center) (coreEmbedNext hm b i x)
      have hcount := coreEmbedNext_count hm b i x hi32
      have hpart := coreEmbedNext_part hm b i x hi32
      have hcountc : vertexPartCount (coreEmbedSame b i center) = partCount i := rfl
      have hpartc : vertexPart (coreEmbedSame b i center) = center.1.1 := rfl
      intro hdel
      rcases hdel with ⟨hs, hc, hl⟩
      have hs' : partCount i + partCount (cyclicNext i) = 6 := by
        simpa [hcountc, hcount] using hs
      have hc' : center.1.1 + 1 = partCount i := by
        simpa [hcountc, hpartc] using hc
      have hl' : x.1.1 + 1 = partCount (cyclicNext i) := by
        simpa [hcount, hpart] using hl
      have hxa := hx
      simp [localCrossAllowed, crossAllowed] at hxa
      rcases hxa with hxa | hxa
      · rcases hxa with hxa | hxa
        · exact hxa hs'
        · exact hxa hc'
      · exact hxa hl'

def coreLocalEmbedding {m : ℕ} (hm : 0 < m) (b : Fin m) (i : Fin 33)
    (hi0 : i.1 ≠ 0) (hi32 : i.1 ≠ 32) (center : LayerVertex i) :
    LocalNeighbor i center.1 ↪
      (graph m).neighborSet (coreEmbedSame b i center) where
  toFun x := ⟨coreEmbedLocal hm b i x.1,
    coreEmbedLocal_is_adjacent hm b i hi0 hi32 center x⟩
  inj' x y hxy := by
    apply Subtype.ext
    exact coreEmbedLocal_injective hm b i hi0 hi32 (congrArg Subtype.val hxy)

theorem core_degree_ge_2200 {m : ℕ} (hm : 0 < m) (b : Fin m) (i : Fin 33)
    (hi0 : i.1 ≠ 0) (hi32 : i.1 ≠ 32) (v : LayerVertex i) :
    2200 ≤ (graph m).degree (coreEmbedSame b i v) := by
  have hcard := localNeighbor_card_ge_2200 i v.1 (by
    exact partSize_pos i v.1)
  have hle := Fintype.card_le_of_injective
    (coreLocalEmbedding hm b i hi0 hi32 v)
    (coreLocalEmbedding hm b i hi0 hi32 v).injective
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using hcard.trans hle

private def firstVertex (i : Fin 33) : LayerVertex i :=
  ⟨⟨0, (partCount_bounds i).1⟩,
    ⟨0, partSize_pos i ⟨0, (partCount_bounds i).1⟩⟩⟩

def leftHub (m : ℕ) : Vertex m := Sum.inl (⟨0, ⟨0, by omega⟩⟩)
def leftBridge (m : ℕ) : Vertex m := Sum.inl (⟨1, ⟨0, by omega⟩⟩)
def coreHub {m : ℕ} (b : Fin m) (i : Fin 33) : Vertex m :=
  Sum.inr (Sum.inl (b, ⟨i, firstVertex i⟩))
def rightHub (m : ℕ) : Vertex m := Sum.inr (Sum.inr (⟨1, by omega⟩, ⟨0, by omega⟩))

@[simp] theorem layerPos_leftHub (m : ℕ) : layerPos (leftHub m) = 0 := rfl
@[simp] theorem layerPos_coreHub {m : ℕ} (b : Fin m) (i : Fin 33) :
    layerPos (coreHub b i) = 33 * b.1 + i.1 + 2 := rfl
@[simp] theorem layerPos_rightHub (m : ℕ) : layerPos (rightHub m) = 33 * m + 3 := by
  simp [rightHub, layerPos]

@[simp] theorem vertexPart_leftHub (m : ℕ) : vertexPart (leftHub m) = 0 := rfl
@[simp] theorem vertexPart_coreHub {m : ℕ} (b : Fin m) (i : Fin 33) :
    vertexPart (coreHub b i) = 0 := rfl
@[simp] theorem vertexPart_rightHub (m : ℕ) : vertexPart (rightHub m) = 0 := rfl

theorem adj_of_dist_one_right_first {m : ℕ} {v w : Vertex m}
    (hd : Nat.dist (layerPos v) (layerPos w) = 1)
    (hw : vertexPart w = 0) : (graph m).Adj v w := by
  rw [graph_adj]
  exact Or.inr ⟨hd, by
    intro h
    rcases h with ⟨hs, _, hlast⟩
    have hv := vertexPartCount_le_four v
    omega⟩

def corePrevHub {m : ℕ} (b : Fin m) (i : Fin 33) : Vertex m :=
  if hi : i.1 = 0 then
    if hb : b.1 = 0 then
      Sum.inl (⟨1, ⟨0, by omega⟩⟩)
    else
      coreHub ⟨b.1 - 1, by omega⟩ ⟨32, by omega⟩
  else
    coreHub b ⟨i.1 - 1, by omega⟩

@[simp] theorem vertexPart_corePrevHub {m : ℕ} (b : Fin m) (i : Fin 33) :
    vertexPart (corePrevHub b i) = 0 := by
  unfold corePrevHub
  split
  · split <;> rfl
  · rfl

theorem core_prev_dist {m : ℕ} (b : Fin m) (i : Fin 33) :
    Nat.dist (layerPos (coreHub b i)) (layerPos (corePrevHub b i)) = 1 := by
  have hb := b.isLt
  unfold corePrevHub
  split <;> rename_i hi
  · split <;> rename_i hb0
    · simp [coreHub, layerPos, hi, hb0, Nat.dist]
    · simp [coreHub, layerPos, hi, hb0, Nat.dist]
      omega
  · simp [coreHub, layerPos, hi, Nat.dist]
    omega

theorem core_vertex_reachable_hub {m : ℕ} (b : Fin m) (i : Fin 33)
    (v : LayerVertex i) :
    (graph m).Reachable
      (Sum.inr (Sum.inl (b, ⟨i, v⟩))) (coreHub b i) := by
  let x : Vertex m := Sum.inr (Sum.inl (b, ⟨i, v⟩))
  have h₁ : (graph m).Adj x (corePrevHub b i) :=
    adj_of_dist_one_right_first (by
      change Nat.dist (layerPos (coreHub b i)) (layerPos (corePrevHub b i)) = 1
      exact core_prev_dist b i)
      (vertexPart_corePrevHub b i)
  have h₂ : (graph m).Adj (corePrevHub b i) (coreHub b i) :=
    adj_of_dist_one_right_first
      (by simpa [Nat.dist_comm] using core_prev_dist b i)
      (vertexPart_coreHub b i)
  exact h₁.reachable.trans h₂.reachable

def firstBlock {m : ℕ} (hm : 0 < m) : Fin m := ⟨0, hm⟩
def lastBlock {m : ℕ} (hm : 0 < m) : Fin m := ⟨m - 1, by omega⟩

theorem left_core_start_adj {m : ℕ} (hm : 0 < m) :
    (graph m).Adj (leftBridge m) (coreHub (firstBlock hm) ⟨0, by omega⟩) := by
  apply adj_of_dist_one_right_first
  · simp [leftBridge, coreHub, layerPos, firstBlock, Nat.dist]
  · rfl

theorem left_bridge_hub_adj {m : ℕ} :
    (graph m).Adj (leftBridge m) (leftHub m) := by
  apply adj_of_dist_one_right_first
  · simp [leftBridge, leftHub, layerPos, Nat.dist]
  · rfl

theorem core_adj_of_layer_succ {m : ℕ} (b : Fin m) (i j : Fin 33)
    (hij : i.1 + 1 = j.1) :
    (graph m).Adj (coreHub b i) (coreHub b j) := by
  apply adj_of_dist_one_right_first
  · simp only [layerPos_coreHub]
    simp [Nat.dist]
    omega
  · rfl

theorem core_adj_of_block_succ {m : ℕ} (b c : Fin m) (hbc : b.1 + 1 = c.1) :
    (graph m).Adj (coreHub b ⟨32, by omega⟩) (coreHub c ⟨0, by omega⟩) := by
  apply adj_of_dist_one_right_first
  · simp only [layerPos_coreHub]
    simp [Nat.dist]
    omega
  · rfl

def rightBridge {m : ℕ} (hm : 0 < m) : Vertex m :=
  Sum.inr (Sum.inr (⟨0, by omega⟩, ⟨0, by omega⟩))

theorem last_core_right_adj {m : ℕ} (hm : 0 < m) :
    (graph m).Adj (coreHub (lastBlock hm) ⟨32, by omega⟩) (rightBridge hm) := by
  apply adj_of_dist_one_right_first
  · change Nat.dist (33 * (lastBlock hm).1 + 32 + 2)
      (33 * m + 2) = 1
    simp [lastBlock, Nat.dist]
    omega
  · rfl

theorem right_bridge_hub_adj {m : ℕ} (hm : 0 < m) :
    (graph m).Adj (rightBridge hm) (rightHub m) := by
  apply adj_of_dist_one_right_first
  · simp [rightBridge, rightHub, layerPos, Nat.dist]
  · rfl

/-! Every cap vertex sees all 2200 vertices in the other cap layer. -/

def leftCapMap {m : ℕ} (v : CapVertex) (x : Fin 2200) : Vertex m :=
  Sum.inl (⟨if v.1.1 = 0 then 1 else 0, x⟩)

theorem leftCapMap_injective {m : ℕ} (v : CapVertex) :
    Function.Injective (leftCapMap (m := m) v) := by
  intro x y h
  have h' : (if v.1.1 = 0 then 1 else 0, x) =
      (if v.1.1 = 0 then 1 else 0, y) := by
    simpa [leftCapMap] using h
  exact congrArg Prod.snd h'

theorem leftCapMap_adj {m : ℕ} (v : CapVertex) (x : Fin 2200) :
    (graph m).Adj (Sum.inl v) (leftCapMap (m := m) v x) := by
  apply adj_of_dist_one_right_first
  · unfold leftCapMap layerPos
    by_cases hv : v.1.1 = 0
    · simp [hv, Nat.dist]
    · have hv1 : v.1.1 = 1 := by have := v.1.isLt; omega
      simp [hv, hv1, Nat.dist]
  · rfl

def leftCapEmbedding {m : ℕ} (v : CapVertex) :
    (Fin 2200) ↪ (graph m).neighborSet (Sum.inl v) where
  toFun x := ⟨leftCapMap (m := m) v x, leftCapMap_adj v x⟩
  inj' x y hxy := leftCapMap_injective v (congrArg Subtype.val hxy)

def rightCapMap {m : ℕ} (v : CapVertex) (x : Fin 2200) : Vertex m :=
  Sum.inr (Sum.inr (⟨if v.1.1 = 0 then 1 else 0, x⟩))

theorem rightCapMap_injective {m : ℕ} (v : CapVertex) :
    Function.Injective (rightCapMap (m := m) v) := by
  intro x y h
  have h' : (if v.1.1 = 0 then 1 else 0, x) =
      (if v.1.1 = 0 then 1 else 0, y) := by
    simpa [rightCapMap] using h
  exact congrArg Prod.snd h'

theorem rightCapMap_adj {m : ℕ} (v : CapVertex) (x : Fin 2200) :
    (graph m).Adj (Sum.inr (Sum.inr v)) (rightCapMap (m := m) v x) := by
  apply adj_of_dist_one_right_first
  · unfold rightCapMap layerPos
    by_cases hv : v.1.1 = 0
    · simp [hv, Nat.dist]
    · have hv1 : v.1.1 = 1 := by have := v.1.isLt; omega
      simp [hv, hv1, Nat.dist]
  · rfl

def rightCapEmbedding {m : ℕ} (v : CapVertex) :
    (Fin 2200) ↪ (graph m).neighborSet (Sum.inr (Sum.inr v)) where
  toFun x := ⟨rightCapMap (m := m) v x, rightCapMap_adj v x⟩
  inj' x y hxy := rightCapMap_injective v (congrArg Subtype.val hxy)

theorem left_cap_degree_ge_2200 {m : ℕ} (v : CapVertex) :
    2200 ≤ (graph m).degree (Sum.inl v) := by
  have hle := Fintype.card_le_of_injective (leftCapEmbedding (m := m) v)
    (leftCapEmbedding (m := m) v).injective
  simpa only [Fintype.card_fin, SimpleGraph.card_neighborSet_eq_degree] using hle

theorem right_cap_degree_ge_2200 {m : ℕ} (v : CapVertex) :
    2200 ≤ (graph m).degree (Sum.inr (Sum.inr v)) := by
  have hle := Fintype.card_le_of_injective (rightCapEmbedding (m := m) v)
    (rightCapEmbedding (m := m) v).injective
  simpa only [Fintype.card_fin, SimpleGraph.card_neighborSet_eq_degree] using hle

/-! The last core layer sees the right cap layer of size 2200. -/

def lastBlockCapMap {m : ℕ} (hm : 0 < m) (x : Fin 2200) : Vertex m :=
  Sum.inr (Sum.inr (⟨0, by omega⟩, x))

theorem lastBlockCapMap_injective {m : ℕ} (hm : 0 < m) :
    Function.Injective (lastBlockCapMap (m := m) hm) := by
  intro x y h
  have h' : (0, x) = (0, y) := by
    simpa [lastBlockCapMap] using h
  exact congrArg Prod.snd h'

theorem lastBlockCapMap_adj {m : ℕ} (hm : 0 < m)
    (center : LayerVertex (⟨32, by omega⟩ : Fin 33)) (x : Fin 2200) :
    (graph m).Adj
      (Sum.inr (Sum.inl (lastBlock hm, ⟨32, center⟩)))
      (lastBlockCapMap hm x) := by
  apply adj_of_dist_one_right_first
  · change Nat.dist (33 * (m - 1) + 32 + 2) (33 * m + 2) = 1
    simp [Nat.dist]
    omega
  · rfl

def lastBlockCapEmbedding {m : ℕ} (hm : 0 < m)
    (center : LayerVertex (⟨32, by omega⟩ : Fin 33)) :
    (Fin 2200) ↪ (graph m).neighborSet
      (Sum.inr (Sum.inl (lastBlock hm, ⟨32, center⟩))) where
  toFun x := ⟨lastBlockCapMap hm x, lastBlockCapMap_adj hm center x⟩
  inj' x y hxy := lastBlockCapMap_injective hm (congrArg Subtype.val hxy)

theorem last_block_degree_ge_2200 {m : ℕ} (hm : 0 < m)
    (center : LayerVertex (⟨32, by omega⟩ : Fin 33)) :
    2200 ≤ (graph m).degree
      (Sum.inr (Sum.inl (lastBlock hm, ⟨32, center⟩))) := by
  have hle := Fintype.card_le_of_injective (lastBlockCapEmbedding hm center)
    (lastBlockCapEmbedding hm center).injective
  simpa only [Fintype.card_fin, SimpleGraph.card_neighborSet_eq_degree] using hle

abbrev LeftBoundaryCandidate (a : Fin (partCount (0 : Fin 33))) :=
  LayerVertex (cyclicPrev (0 : Fin 33)) ⊕ LayerVertex (0 : Fin 33)

def IsLeftBoundaryNeighbor (a : Fin (partCount (0 : Fin 33))) :
    LeftBoundaryCandidate a → Prop
  | Sum.inl x => localCrossAllowed (0 : Fin 33) (cyclicPrev 0) a x.1
  | Sum.inr x => x.1 ≠ a

instance (a : Fin (partCount (0 : Fin 33))) :
    DecidablePred (IsLeftBoundaryNeighbor a) := fun x => by
  rcases x with x | x <;> simp only [IsLeftBoundaryNeighbor] <;> infer_instance

abbrev LeftBoundaryNeighbor (a : Fin (partCount (0 : Fin 33))) :=
  {x : LeftBoundaryCandidate a // IsLeftBoundaryNeighbor a x}

theorem leftBoundary_card_ge :
    ∀ a : Fin (partCount (0 : Fin 33)), 2200 ≤ Fintype.card (LeftBoundaryNeighbor a) := by
  decide

def leftBoundaryMap {m : ℕ} (b : Fin m) (hb : b.1 ≠ 0)
    (a : Fin (partCount (0 : Fin 33))) :
    LeftBoundaryCandidate a → Vertex m
  | Sum.inl x =>
      Sum.inr (Sum.inl (⟨b.1 - 1, by omega⟩,
        ⟨cyclicPrev 0, x⟩))
  | Sum.inr x =>
      Sum.inr (Sum.inl (b, ⟨0, x⟩))

theorem leftBoundaryMap_injective {m : ℕ} (b : Fin m) (hb : b.1 ≠ 0)
    (a : Fin (partCount (0 : Fin 33))) : Function.Injective (leftBoundaryMap b hb a) := by
  intro x y hxy
  rcases x with x | x <;> rcases y with y | y
  · cases hxy
    rfl
  · have hp := congrArg layerPos hxy
    simp [leftBoundaryMap, layerPos, Nat.dist] at hp
    omega
  · have hp := congrArg layerPos hxy
    simp [leftBoundaryMap, layerPos, Nat.dist] at hp
    omega
  · cases hxy
    rfl

theorem leftBoundaryMap_adj {m : ℕ} (b : Fin m) (hb : b.1 ≠ 0)
    (center : LayerVertex (0 : Fin 33)) (x : LeftBoundaryNeighbor center.1) :
    (graph m).Adj (Sum.inr (Sum.inl (b, ⟨0, center⟩)))
      (leftBoundaryMap b hb center.1 x.1) := by
  rcases x with ⟨x | x, hx⟩
  · rw [graph_adj]
    right
    refine ⟨?_, ?_⟩
    · norm_num [leftBoundaryMap, layerPos, cyclicPrev, Nat.dist]
      omega
    · change localCrossAllowed (0 : Fin 33) (cyclicPrev 0) center.1 x.1 at hx
      change crossAllowedV _ _
      intro hdel
      rcases hdel with ⟨hs, hc, hl⟩
      have hxa := hx
      simp [localCrossAllowed, crossAllowed] at hxa
      rcases hxa with hxa | hxa
      · rcases hxa with hxa | hxa
        · exact hxa (by simpa [leftBoundaryMap, vertexPartCount, vertexPart] using hs)
        · exact hxa (by simpa [leftBoundaryMap, vertexPartCount, vertexPart] using hc)
      · exact hxa (by simpa [leftBoundaryMap, vertexPartCount, vertexPart] using hl)
  · rw [graph_adj]
    left
    refine ⟨rfl, ?_⟩
    intro heq
    exact hx (Fin.ext heq.symm)

def leftBoundaryEmbedding {m : ℕ} (b : Fin m) (hb : b.1 ≠ 0)
    (center : LayerVertex (0 : Fin 33)) :
    LeftBoundaryNeighbor center.1 ↪
      (graph m).neighborSet (Sum.inr (Sum.inl (b, ⟨0, center⟩))) where
  toFun x := ⟨leftBoundaryMap b hb center.1 x.1, leftBoundaryMap_adj b hb center x⟩
  inj' x y hxy := by
    apply Subtype.ext
    exact leftBoundaryMap_injective b hb center.1 (congrArg Subtype.val hxy)

theorem left_boundary_degree_ge_2200 {m : ℕ} (b : Fin m) (hb : b.1 ≠ 0)
    (center : LayerVertex (0 : Fin 33)) :
    2200 ≤ (graph m).degree
      (Sum.inr (Sum.inl (b, ⟨0, center⟩))) := by
  have hle := Fintype.card_le_of_injective (leftBoundaryEmbedding b hb center)
    (leftBoundaryEmbedding b hb center).injective
  have hcard := leftBoundary_card_ge center.1
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using hcard.trans hle

def firstBlockCapMap {m : ℕ} (center : LayerVertex (0 : Fin 33)) (x : Fin 2200) : Vertex m :=
  Sum.inl (⟨1, x⟩)

theorem firstBlockCapMap_injective {m : ℕ} (center : LayerVertex (0 : Fin 33)) :
    Function.Injective (firstBlockCapMap (m := m) center) := by
  intro x y h
  have h' : (1, x) = (1, y) := by
    simpa [firstBlockCapMap] using h
  exact congrArg Prod.snd h'

theorem firstBlockCapMap_adj {m : ℕ} (hm : 0 < m)
    (center : LayerVertex (0 : Fin 33)) (x : Fin 2200) :
    (graph m).Adj
      (Sum.inr (Sum.inl (⟨0, hm⟩, ⟨0, center⟩))) (firstBlockCapMap center x) := by
  apply adj_of_dist_one_right_first
  · simp [firstBlockCapMap, layerPos, Nat.dist]
  · rfl

def firstBlockCapEmbedding {m : ℕ} (hm : 0 < m)
    (center : LayerVertex (0 : Fin 33)) :
    (Fin 2200) ↪ (graph m).neighborSet
      (Sum.inr (Sum.inl (⟨0, hm⟩, ⟨0, center⟩))) where
  toFun x := ⟨firstBlockCapMap center x, firstBlockCapMap_adj hm center x⟩
  inj' x y hxy := firstBlockCapMap_injective center (congrArg Subtype.val hxy)

theorem first_block_degree_ge_2200 {m : ℕ} (hm : 0 < m)
    (center : LayerVertex (0 : Fin 33)) :
    2200 ≤ (graph m).degree
      (Sum.inr (Sum.inl (⟨0, hm⟩, ⟨0, center⟩))) := by
  have hle := Fintype.card_le_of_injective (firstBlockCapEmbedding hm center)
    (firstBlockCapEmbedding hm center).injective
  simpa only [Fintype.card_fin, SimpleGraph.card_neighborSet_eq_degree] using hle

abbrev RightBoundaryCandidate (a : Fin (partCount (⟨32, by omega⟩ : Fin 33))) :=
  LayerVertex (⟨32, by omega⟩ : Fin 33) ⊕
    LayerVertex (cyclicNext (⟨32, by omega⟩ : Fin 33))

def IsRightBoundaryNeighbor
    (a : Fin (partCount (⟨32, by omega⟩ : Fin 33))) :
    RightBoundaryCandidate a → Prop
  | Sum.inl x => x.1 ≠ a
  | Sum.inr x => localCrossAllowed (⟨32, by omega⟩ : Fin 33)
      (cyclicNext 32) a x.1

instance (a : Fin (partCount (⟨32, by omega⟩ : Fin 33))) :
    DecidablePred (IsRightBoundaryNeighbor a) := fun x => by
  rcases x with x | x <;> simp only [IsRightBoundaryNeighbor] <;> infer_instance

abbrev RightBoundaryNeighbor
    (a : Fin (partCount (⟨32, by omega⟩ : Fin 33))) :=
  {x : RightBoundaryCandidate a // IsRightBoundaryNeighbor a x}

theorem rightBoundary_card_ge :
    ∀ a : Fin (partCount (⟨32, by omega⟩ : Fin 33)),
      2200 ≤ Fintype.card (RightBoundaryNeighbor a) := by
  decide

def rightBoundaryMap {m : ℕ} (b : Fin m) (hb : b.1 + 1 ≠ m)
    (a : Fin (partCount (⟨32, by omega⟩ : Fin 33))) :
    RightBoundaryCandidate a → Vertex m
  | Sum.inl x => Sum.inr (Sum.inl (b, ⟨32, x⟩))
  | Sum.inr x => Sum.inr (Sum.inl (⟨b.1 + 1, by omega⟩,
      ⟨cyclicNext (⟨32, by omega⟩ : Fin 33), x⟩))

theorem rightBoundaryMap_injective {m : ℕ} (b : Fin m) (hb : b.1 + 1 ≠ m)
    (a : Fin (partCount (⟨32, by omega⟩ : Fin 33))) :
    Function.Injective (rightBoundaryMap b hb a) := by
  intro x y hxy
  rcases x with x | x <;> rcases y with y | y
  · cases hxy
    rfl
  · have hp := congrArg layerPos hxy
    simp [rightBoundaryMap, layerPos] at hp
    omega
  · have hp := congrArg layerPos hxy
    simp [rightBoundaryMap, layerPos] at hp
    omega
  · cases hxy
    rfl

theorem rightBoundaryMap_adj {m : ℕ} (b : Fin m) (hb : b.1 + 1 ≠ m)
    (center : LayerVertex (⟨32, by omega⟩ : Fin 33))
    (x : RightBoundaryNeighbor center.1) :
    (graph m).Adj (Sum.inr (Sum.inl (b, ⟨32, center⟩)))
      (rightBoundaryMap b hb center.1 x.1) := by
  rcases x with ⟨x | x, hx⟩
  · rw [graph_adj]
    left
    refine ⟨rfl, ?_⟩
    intro heq
    exact hx (Fin.ext heq.symm)
  · rw [graph_adj]
    right
    refine ⟨?_, ?_⟩
    · norm_num [rightBoundaryMap, layerPos, cyclicNext, Nat.dist]
      omega
    · change localCrossAllowed (⟨32, by omega⟩ : Fin 33)
        (cyclicNext 32) center.1 x.1 at hx
      change crossAllowedV _ _
      intro hdel
      rcases hdel with ⟨hs, hc, hl⟩
      have hxa := hx
      simp [localCrossAllowed, crossAllowed] at hxa
      rcases hxa with hxa | hxa
      · rcases hxa with hxa | hxa
        · exact hxa (by simpa [rightBoundaryMap, vertexPartCount] using hs)
        · exact hxa (by simpa [rightBoundaryMap, vertexPartCount, vertexPart] using hc)
      · exact hxa (by simpa [rightBoundaryMap, vertexPartCount, vertexPart] using hl)

def rightBoundaryEmbedding {m : ℕ} (b : Fin m) (hb : b.1 + 1 ≠ m)
    (center : LayerVertex (⟨32, by omega⟩ : Fin 33)) :
    RightBoundaryNeighbor center.1 ↪
      (graph m).neighborSet (Sum.inr (Sum.inl (b, ⟨32, center⟩))) where
  toFun x := ⟨rightBoundaryMap b hb center.1 x.1, rightBoundaryMap_adj b hb center x⟩
  inj' x y hxy := by
    apply Subtype.ext
    exact rightBoundaryMap_injective b hb center.1 (congrArg Subtype.val hxy)

theorem right_boundary_degree_ge_2200 {m : ℕ} (b : Fin m) (hb : b.1 + 1 ≠ m)
    (center : LayerVertex (⟨32, by omega⟩ : Fin 33)) :
    2200 ≤ (graph m).degree (Sum.inr (Sum.inl (b, ⟨32, center⟩))) := by
  have hle := Fintype.card_le_of_injective (rightBoundaryEmbedding b hb center)
    (rightBoundaryEmbedding b hb center).injective
  have hcard := rightBoundary_card_ge center.1
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using hcard.trans hle

/-! The outer left cap layer has exactly 2200 neighbors for its layer-0 vertex. -/

theorem leftHub_neighbor_cases {m : ℕ} (w : (graph m).neighborSet (leftHub m)) :
    ∃ x : Fin 2200, w.1 = Sum.inl (⟨1, x⟩) := by
  rcases w with ⟨w, hw⟩
  change ∃ x : Fin 2200, w = Sum.inl (⟨1, x⟩)
  rcases w with v | (⟨b, ⟨i, x⟩⟩ | v)
  · change (graph m).Adj (leftHub m) (Sum.inl v) at hw
    rw [graph_adj] at hw
    rcases hw with hw | hw
    · have hp := hw.1
      exfalso
      exact hw.2 rfl
    · have hv1 : v.1.1 = 1 := by
        simp [leftHub, layerPos, Nat.dist] at hw
        omega
      have hv : v = (1, v.2) := by
        apply Prod.ext
        · exact Fin.ext hv1
        · rfl
      exact ⟨v.2, congrArg Sum.inl hv⟩
  · change (graph m).Adj (leftHub m)
      (Sum.inr (Sum.inl (b, ⟨i, x⟩))) at hw
    rw [graph_adj] at hw
    exfalso
    rcases hw with hw | hw
    · simp [leftHub, layerPos, Nat.dist] at hw
    · simp [leftHub, layerPos, Nat.dist] at hw
  · change (graph m).Adj (leftHub m) (Sum.inr (Sum.inr v)) at hw
    rw [graph_adj] at hw
    exfalso
    rcases hw with hw | hw
    · have hv := v.1.isLt
      simp [leftHub, layerPos, Nat.dist] at hw
      omega
    · have hv := v.1.isLt
      simp [leftHub, layerPos, Nat.dist] at hw
      omega

noncomputable def leftHubNeighborCoord {m : ℕ}
    (w : (graph m).neighborSet (leftHub m)) : Fin 2200 :=
  Classical.choose (leftHub_neighbor_cases w)

theorem leftHubNeighborCoord_spec {m : ℕ}
    (w : (graph m).neighborSet (leftHub m)) :
    w.1 = Sum.inl (⟨1, leftHubNeighborCoord w⟩) := by
  exact Classical.choose_spec (leftHub_neighbor_cases w)

noncomputable def leftHubEmbedding {m : ℕ} :
    (graph m).neighborSet (leftHub m) ↪ Fin 2200 where
  toFun := leftHubNeighborCoord
  inj' w z h := by
    apply Subtype.ext
    rw [leftHubNeighborCoord_spec w, leftHubNeighborCoord_spec z, h]

theorem leftHub_degree_le_2200 {m : ℕ} :
    (graph m).degree (leftHub m) ≤ 2200 := by
  have hle := Fintype.card_le_of_injective (leftHubEmbedding (m := m))
    (leftHubEmbedding (m := m)).injective
  simpa only [Fintype.card_fin, SimpleGraph.card_neighborSet_eq_degree] using hle

theorem all_degrees_ge_2200 {m : ℕ} (hm : 0 < m) (v : Vertex m) :
    2200 ≤ (graph m).degree v := by
  rcases v with v | (⟨b, ⟨i, x⟩⟩ | v)
  · exact left_cap_degree_ge_2200 (m := m) v
  · by_cases hi0 : i.1 = 0
    · have hieq : i = (0 : Fin 33) := Fin.ext hi0
      subst i
      by_cases hb0 : b.1 = 0
      · have hbeq : b = firstBlock hm := Fin.ext hb0
        subst b
        exact first_block_degree_ge_2200 hm x
      · exact left_boundary_degree_ge_2200 b hb0 x
    · by_cases hi32 : i.1 = 32
      · have hieq : i = (⟨32, by omega⟩ : Fin 33) := Fin.ext hi32
        let x32 : LayerVertex (⟨32, by omega⟩ : Fin 33) := hieq ▸ x
        have hblock : (⟨i, x⟩ : BlockVertex) =
            ⟨(⟨32, by omega⟩ : Fin 33), x32⟩ := by
          exact Sigma.ext hieq (by simp [x32])
        by_cases hblast : b.1 + 1 = m
        · have hbeq : b = lastBlock hm := by
            apply Fin.ext
            simp [lastBlock]
            omega
          subst b
          rw [hblock]
          exact last_block_degree_ge_2200 hm x32
        · rw [hblock]
          exact right_boundary_degree_ge_2200 b hblast x32
      · exact core_degree_ge_2200 hm b i hi0 hi32 x
  · exact right_cap_degree_ge_2200 (m := m) v

theorem graph_minDegree_eq_2200 {m : ℕ} (hm : 0 < m) :
    (graph m).minDegree = 2200 := by
  letI : Nonempty (Vertex m) := ⟨leftHub m⟩
  apply Nat.le_antisymm
  · exact (graph m).minDegree_le_degree (leftHub m) |>.trans
      (leftHub_degree_le_2200 (m := m))
  · exact (graph m).le_minDegree_of_forall_le_degree 2200
      (all_degrees_ge_2200 hm)

private theorem core_reachable_from_start {m : ℕ} (b : Fin m)
    (hstart : (graph m).Reachable (leftHub m) (coreHub b ⟨0, by omega⟩))
    (i : Fin 33) :
    (graph m).Reachable (leftHub m) (coreHub b i) := by
  induction i using Fin.strong_induction_on with
  | h i ih =>
      by_cases hi : i.1 = 0
      · have hieq : i = ⟨0, by omega⟩ := Fin.ext hi
        simpa [hieq] using hstart
      · let j : Fin 33 := ⟨i.1 - 1, by omega⟩
        have hjlt : j < i := by change i.1 - 1 < i.1; omega
        have hji : j.1 + 1 = i.1 := by simp [j]; omega
        exact (ih j hjlt).trans (core_adj_of_layer_succ b j i hji).reachable

theorem left_reachable_core {m : ℕ} (hm : 0 < m) (b : Fin m) (i : Fin 33) :
    (graph m).Reachable (leftHub m) (coreHub b i) := by
  revert i
  induction b using Fin.strong_induction_on with
  | h b ih =>
      intro i
      by_cases hb : b.1 = 0
      · have hbeq : b = firstBlock hm := Fin.ext hb
        subst b
        exact core_reachable_from_start (firstBlock hm)
          ((left_bridge_hub_adj (m := m)).symm.reachable.trans
            (left_core_start_adj hm).reachable) i
      · let c : Fin m := ⟨b.1 - 1, by omega⟩
        have hclt : c < b := by change b.1 - 1 < b.1; omega
        have hcb : c.1 + 1 = b.1 := by simp [c]; omega
        have hend := ih c hclt ⟨32, by omega⟩
        have hstart : (graph m).Reachable (leftHub m) (coreHub b ⟨0, by omega⟩) :=
          hend.trans (core_adj_of_block_succ c b hcb).reachable
        exact core_reachable_from_start b hstart i

theorem left_vertex_reachable_hub {m : ℕ} (hm : 0 < m) (v : CapVertex) :
    (graph m).Reachable (Sum.inl v) (leftHub m) := by
  by_cases hv : v.1.1 = 0
  · have h₁ : (graph m).Adj (Sum.inl v) (leftBridge m) := by
      apply adj_of_dist_one_right_first
      · simp [leftBridge, layerPos, hv, Nat.dist]
      · rfl
    exact h₁.reachable.trans (left_bridge_hub_adj (m := m)).reachable
  · have h₁ : (graph m).Adj (Sum.inl v) (leftHub m) := by
      apply adj_of_dist_one_right_first
      · have hv1 : v.1.1 = 1 := by have := v.1.isLt; omega
        simp [leftHub, layerPos, hv1, Nat.dist]
      · rfl
    exact h₁.reachable

theorem right_vertex_reachable_hub {m : ℕ} (hm : 0 < m) (v : CapVertex) :
    (graph m).Reachable (Sum.inr (Sum.inr v)) (rightHub m) := by
  by_cases hv : v.1.1 = 0
  · have h₁ : (graph m).Adj (Sum.inr (Sum.inr v)) (rightHub m) := by
      apply adj_of_dist_one_right_first
      · simp [rightHub, layerPos, hv, Nat.dist]
      · rfl
    exact h₁.reachable
  · have h₁ : (graph m).Adj (Sum.inr (Sum.inr v)) (rightBridge hm) := by
      apply adj_of_dist_one_right_first
      · have hv1 : v.1.1 = 1 := by have := v.1.isLt; omega
        simp [rightBridge, layerPos, hv1, Nat.dist]
      · rfl
    exact h₁.reachable.trans (right_bridge_hub_adj hm).reachable

theorem graph_connected_raw {m : ℕ} (hm : 0 < m) : (graph m).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨leftHub m, ?_⟩
  intro v
  rcases v with v | ⟨⟨b, i, v⟩ | v⟩
  · exact (left_vertex_reachable_hub hm v).symm
  · exact (left_reachable_core hm b i).trans (core_vertex_reachable_hub b i v).symm
  · have hend := (left_reachable_core hm (lastBlock hm) ⟨32, by omega⟩).trans
        (last_core_right_adj hm).reachable |>.trans (right_bridge_hub_adj hm).reachable
    exact hend.trans (right_vertex_reachable_hub hm v).symm

theorem adj_layer_dist_le_one' {m : ℕ} {v w : Vertex m}
    (h : (graph m).Adj v w) : Nat.dist (layerPos v) (layerPos w) ≤ 1 :=
  adj_layer_dist_le_one h

theorem walk_layer_dist_le_length {m : ℕ} {u v : Vertex m}
    (W : (graph m).Walk u v) : Nat.dist (layerPos u) (layerPos v) ≤ W.length := by
  induction W with
  | nil => simp
  | @cons u v w huv W ih =>
      calc
        Nat.dist (layerPos u) (layerPos w)
            ≤ Nat.dist (layerPos u) (layerPos v) + Nat.dist (layerPos v) (layerPos w) :=
              Nat.dist.triangle_inequality _ _ _
        _ ≤ 1 + W.length := Nat.add_le_add (adj_layer_dist_le_one huv) ih
        _ = (SimpleGraph.Walk.cons huv W).length := by simp; omega

theorem endpoint_dist_lower_bound {m : ℕ} (hm : 0 < m) :
    33 * m + 3 ≤ (graph m).dist (leftHub m) (rightHub m) := by
  obtain ⟨W, hW⟩ := (graph_connected_raw hm).exists_walk_length_eq_dist
    (leftHub m) (rightHub m)
  calc
    33 * m + 3 = Nat.dist (layerPos (leftHub m)) (layerPos (rightHub m)) := by
      simp [Nat.dist, rightHub, leftHub, layerPos]
    _ ≤ W.length := walk_layer_dist_le_length W
    _ = (graph m).dist (leftHub m) (rightHub m) := hW

theorem diameter_lower_raw {m : ℕ} (hm : 0 < m) :
    33 * m + 3 ≤ (graph m).diam := by
  have hc := graph_connected_raw hm
  letI : Nonempty (Vertex m) := hc.nonempty
  have htop : (graph m).ediam ≠ ⊤ :=
    (SimpleGraph.connected_iff_ediam_ne_top).mp hc
  exact (endpoint_dist_lower_bound hm).trans (SimpleGraph.dist_le_diam htop)

/-- Connectedness is preserved by the finite-vertex equivalence. -/
theorem graphFin_connected {m : ℕ} (hm : 0 < m) : (graphFin m).Connected := by
  exact (graphIsoFin m).connected_iff.mp (graph_connected_raw hm)

/-- The constructed graph is six-clique-free. -/
theorem graphFin_cliqueFree_six (m : ℕ) : (graphFin m).CliqueFree 6 := by
  letI : Nonempty (Vertex m) := ⟨leftHub m⟩
  rw [graphFin, SimpleGraph.cliqueFree_map_iff]
  exact graph_cliqueFree_six_raw m

/-- The minimum-degree certificate is proved below. -/
theorem graphFin_minDegree {m : ℕ} (hm : 0 < m) :
    (graphFin m).minDegree = 2200 := by
  calc
    (graphFin m).minDegree = (graph m).minDegree :=
      (graphIsoFin m).minDegree_eq.symm
    _ = 2200 := graph_minDegree_eq_2200 hm

/-- The diameter lower bound is preserved by the finite-vertex equivalence. -/
theorem graphFin_diameter_lower {m : ℕ} (hm : 0 < m) :
    diameterLower m ≤ (graphFin m).diam := by
  let u : Fin (order m) := vertexEquivFin m (leftHub m)
  let v : Fin (order m) := vertexEquivFin m (rightHub m)
  obtain ⟨W, hW⟩ := (graphFin_connected hm).exists_walk_length_eq_dist u v
  let WL := W.map (graphIsoFin m).symm.toHom
  have hu : (graphIsoFin m).symm.toHom u = leftHub m := by
    change (vertexEquivFin m).symm (vertexEquivFin m (leftHub m)) = leftHub m
    simp [u]
  have hv : (graphIsoFin m).symm.toHom v = rightHub m := by
    change (vertexEquivFin m).symm (vertexEquivFin m (rightHub m)) = rightHub m
    simp [v]
  have hmap : (graph m).dist (leftHub m) (rightHub m) ≤ WL.length := by
    have h := (graph m).dist_le WL
    simpa only [hu, hv] using h
  have hfin : 33 * m + 3 ≤ (graphFin m).dist u v := by
    calc
      33 * m + 3 ≤ (graph m).dist (leftHub m) (rightHub m) :=
        endpoint_dist_lower_bound hm
      _ ≤ WL.length := hmap
      _ = W.length := SimpleGraph.Walk.length_map _ _
      _ = (graphFin m).dist u v := hW
  letI : Nonempty (Fin (order m)) := ⟨u⟩
  have htop : (graphFin m).ediam ≠ ⊤ :=
    (SimpleGraph.connected_iff_ediam_ne_top).mp (graphFin_connected hm)
  have hfin' : diameterLower m ≤ (graphFin m).dist u v := by
    simpa [diameterLower] using hfin
  exact hfin'.trans ((graphFin m).dist_le_diam htop)

end Erdos612AmendedK6
