import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5461

open PEqualNP.CircuitLowerBounds

theorem getD_snoc {α : Type} (L : List α) (a d : α) (w : ℕ) :
    (L ++ [a]).getD w d = if w < L.length then L.getD w d else if w = L.length then a else d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    rw [List.getElem?_eq_none (by simp; omega)]; simp

-- one step of evaluation and one step of the dependency sets
def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def dstep (D : List (Finset ℕ)) (g : Gate) : List (Finset ℕ) :=
  D ++ [g.inputs.toFinset.biUnion fun i => D.getD i ∅]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl wstep x := rfl

theorem sem (P : ℕ → Prop) : ∀ (gs : List Gate) (W1 W2 : List Bool) (D : List (Finset ℕ)),
    W1.length = D.length → W2.length = D.length →
    (∀ w, (∀ i ∈ D.getD w ∅, P i) → W1.getD w false = W2.getD w false) →
    ∀ w, (∀ i ∈ (gs.foldl dstep D).getD w ∅, P i) →
      (gs.foldl wstep W1).getD w false = (gs.foldl wstep W2).getD w false := by
  intro gs
  induction gs with
  | nil => intro W1 W2 D _ _ h; simpa using h
  | cons g gs ih =>
    intro W1 W2 D h1 h2 h
    simp only [List.foldl_cons]
    apply ih
    · simp [wstep, dstep, h1]
    · simp [wstep, dstep, h2]
    · intro w hw
      simp only [wstep, dstep] at hw ⊢
      rw [getD_snoc, getD_snoc]
      rw [getD_snoc] at hw
      rw [h1, h2]
      split_ifs with c1 c2
      · rw [if_pos c1] at hw; exact h w hw
      · rw [if_neg c1, if_pos c2] at hw
        congr 1
        apply List.map_congr_left
        intro j hj
        apply h j
        intro i hi
        apply hw
        rw [Finset.mem_biUnion]
        exact ⟨j, List.mem_toFinset.mpr hj, hi⟩
      · rfl

theorem cardb : ∀ (gs : List Gate) (D : List (Finset ℕ)) (k : ℕ),
    (∀ g ∈ gs, g.inputs.length ≤ 2) →
    (∀ T : Finset ℕ, (T.biUnion fun w => D.getD w ∅).card ≤ T.card + k) →
    ∀ T : Finset ℕ, (T.biUnion fun w => (gs.foldl dstep D).getD w ∅).card ≤
      T.card + k + gs.length := by
  intro gs
  induction gs with
  | nil => intro D k _ h T; simpa using h T
  | cons g gs ih =>
    intro D k hg h T
    simp only [List.foldl_cons, List.length_cons]
    have := ih (dstep D g) (k + 1) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) ?_ T
    · omega
    intro T
    have hsub : (T.biUnion fun w => (dstep D g).getD w ∅) ⊆
        ((T.erase D.length) ∪ g.inputs.toFinset).biUnion fun w => D.getD w ∅ := by
      intro i hi
      rw [Finset.mem_biUnion] at hi
      obtain ⟨w, hw, hi⟩ := hi
      simp only [dstep] at hi
      rw [getD_snoc] at hi
      rw [Finset.mem_biUnion]
      split_ifs at hi with c1 c2
      · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by omega, hw⟩), hi⟩
      · rw [Finset.mem_biUnion] at hi
        obtain ⟨j, hj, hi⟩ := hi
        exact ⟨j, Finset.mem_union_right _ hj, hi⟩
      · simp at hi
    have hc := h ((T.erase D.length) ∪ g.inputs.toFinset)
    have h3 := Finset.card_union_le (T.erase D.length) g.inputs.toFinset
    have h4 := List.toFinset_card_le g.inputs
    have h5 := hg g List.mem_cons_self
    have h6 := Finset.card_le_card hsub
    by_cases hm : D.length ∈ T
    · have h7 := Finset.card_erase_of_mem hm
      have h8 : 1 ≤ T.card := Finset.card_pos.mpr ⟨_, hm⟩
      omega
    · have h9 : (T.biUnion fun w => (dstep D g).getD w ∅) =
          T.biUnion fun w => D.getD w ∅ := by
        apply Finset.biUnion_congr rfl
        intro w hw
        simp only [dstep]
        rw [getD_snoc]
        have : w ≠ D.length := fun e => hm (e ▸ hw)
        split_ifs with c1
        · rfl
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      rw [h9]; have := h T; omega

theorem base_card (n : ℕ) (T : Finset ℕ) :
    (T.biUnion fun w => ((List.range n).map fun i => ({i} : Finset ℕ)).getD w ∅).card ≤
      T.card + 0 := by
  refine le_trans Finset.card_biUnion_le ?_
  rw [Nat.add_zero]
  calc (∑ w ∈ T, (((List.range n).map fun i => ({i} : Finset ℕ)).getD w ∅).card)
      ≤ ∑ w ∈ T, 1 := by
        apply Finset.sum_le_sum
        intro w _
        rw [List.getD_eq_getElem?_getD]
        by_cases hw : w < n
        · simp [hw]
        · rw [List.getElem?_eq_none (by simp; omega)]; simp
    _ = T.card := by simp

-- the dependency set of the output wire
def depS (n : ℕ) (C : Circuit) : Finset ℕ :=
  (C.gates.foldl dstep ((List.range n).map fun j => ({j} : Finset ℕ))).getD C.output ∅

theorem depS_card (n : ℕ) (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (depS n C).card ≤ C.size + 1 := by
  have hc := cardb C.gates ((List.range n).map fun j => ({j} : Finset ℕ)) 0 hfan (base_card n)
    {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton] at hc
  unfold depS PEqualNP.CircuitLowerBounds.Circuit.size
  omega

theorem dep (C : Circuit) (n i : ℕ) (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (hxy : ∀ j, j ≠ i → x.getD j false = y.getD j false) (hi : i ∉ depS n C) :
    C.eval x = C.eval y := by
  have key := sem (fun j => x.getD j false = y.getD j false) C.gates x y
    ((List.range n).map fun j => ({j} : Finset ℕ)) (by simp [hx]) (by simp [hy]) ?_ C.output ?_
  · unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [wires_eq, wires_eq]; exact key
  · intro w hw
    by_cases hwn : w < n
    · apply hw w
      simp [List.getD_eq_getElem?_getD, hwn]
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  · intro j hj
    have hji : j ≠ i := fun e => hi (by unfold depS; exact e ▸ hj)
    exact hxy j hji

theorem all_mono (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i, f i = true → g i = true) :
    (l.map f).all id = true → (l.map g).all id = true := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true, id]
    exact fun ⟨h1, h2⟩ => ⟨h a h1, ih h2⟩

theorem any_mono (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i, f i = true → g i = true) :
    (l.map f).any id = true → (l.map g).any id = true := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, Bool.or_eq_true, id]
    rintro (h1 | h2)
    · exact Or.inl (h a h1)
    · exact Or.inr (ih h2)

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool),
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → W1.length = W2.length →
    (∀ w, W1.getD w false = true → W2.getD w false = true) →
    ∀ w, (gs.foldl wstep W1).getD w false = true → (gs.foldl wstep W2).getD w false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ h; simpa using h
  | cons g gs ih =>
    intro W1 W2 hop hl h
    simp only [List.foldl_cons]
    apply ih
    · exact fun g' hg' => hop g' (List.mem_cons_of_mem _ hg')
    · simp [wstep, hl]
    · intro w hw
      simp only [wstep] at hw ⊢
      rw [getD_snoc] at hw
      rw [getD_snoc, ← hl]
      by_cases c1 : w < W1.length
      · rw [if_pos c1] at hw ⊢; exact h w hw
      · rw [if_neg c1] at hw ⊢
        by_cases c2 : w = W1.length
        · rw [if_pos c2] at hw ⊢
          rcases hop g List.mem_cons_self with e | e
          · rw [e] at hw ⊢
            exact all_mono _ _ _ h hw
          · rw [e] at hw ⊢
            exact any_mono _ _ _ h hw
        · rw [if_neg c2] at hw; exact absurd hw (by decide)

theorem evmono (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C) (x y : List Bool)
    (hl : x.length = y.length) (h : ∀ w, x.getD w false = true → y.getD w false = true) :
    C.eval x = true → C.eval y = true := by
  have hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hm g hg).1
    simpa using this
  unfold PEqualNP.CircuitLowerBounds.Circuit.eval
  rw [wires_eq, wires_eq]
  exact mono C.gates x y hop hl h C.output

theorem key3 (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C) (i : ℕ)
    (hi : i ∉ depS 8 C) (x y z : List Bool) (hx : x.length = 8) (hy : y.length = 8)
    (hz : z.length = 8)
    (hxy : ∀ j < 8, j ≠ i → x.getD j false = y.getD j false)
    (hyz : ∀ j < 8, y.getD j false = true → z.getD j false = true)
    (ex : C.eval x = true) (ez : C.eval z = false) : False := by
  have hxy' : ∀ j, j ≠ i → x.getD j false = y.getD j false := by
    intro j hj
    by_cases hj8 : j < 8
    · exact hxy j hj8 hj
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  have hyz' : ∀ j, y.getD j false = true → z.getD j false = true := by
    intro j hj
    by_cases hj8 : j < 8
    · exact hyz j hj8 hj
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hj
      exact absurd hj (by decide)
  have e1 := dep C 8 i x y hx hy hxy' hi
  have e2 := evmono C hm y z (by omega) hyz' (e1 ▸ ex)
  rw [ez] at e2
  exact absurd e2 (by decide)

abbrev A : Fin 4 → Fin 4 → Bool := fun u v : Fin 4 => (119 : ℕ).testBit (4 * u.val + v.val)

theorem upper : PEqualNP.Represents.RepSizeAtMost A 4 := by
  refine ⟨⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [9, 6]⟩,
    ⟨GateOp.and, [8, 10]⟩], 11⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide

theorem lower : ¬ PEqualNP.Represents.RepSizeAtMost A 3 := by
  rintro ⟨C, hm, hs, hr⟩
  have hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg => (hm g hg).2
  have hc := depS_card 8 C hfan
  have r00 : C.eval [true, false, false, false, true, false, false, false] = true := by
    have h := hr 0 0
    have e : PEqualNP.Represents.oneEach (0 : Fin 4) (0 : Fin 4) =
        [true, false, false, false, true, false, false, false] := by decide
    rw [e] at h; rw [h]; decide
  have r10 : C.eval [false, true, false, false, true, false, false, false] = true := by
    have h := hr 1 0
    have e : PEqualNP.Represents.oneEach (1 : Fin 4) (0 : Fin 4) =
        [false, true, false, false, true, false, false, false] := by decide
    rw [e] at h; rw [h]; decide
  have r01 : C.eval [true, false, false, false, false, true, false, false] = true := by
    have h := hr 0 1
    have e : PEqualNP.Represents.oneEach (0 : Fin 4) (1 : Fin 4) =
        [true, false, false, false, false, true, false, false] := by decide
    rw [e] at h; rw [h]; decide
  have r02 : C.eval [true, false, false, false, false, false, true, false] = true := by
    have h := hr 0 2
    have e : PEqualNP.Represents.oneEach (0 : Fin 4) (2 : Fin 4) =
        [true, false, false, false, false, false, true, false] := by decide
    rw [e] at h; rw [h]; decide
  have r30 : C.eval [false, false, false, true, true, false, false, false] = false := by
    have h := hr 3 0
    have e : PEqualNP.Represents.oneEach (3 : Fin 4) (0 : Fin 4) =
        [false, false, false, true, true, false, false, false] := by decide
    rw [e] at h; rw [h]; decide
  have r03 : C.eval [true, false, false, false, false, false, false, true] = false := by
    have h := hr 0 3
    have e : PEqualNP.Represents.oneEach (0 : Fin 4) (3 : Fin 4) =
        [true, false, false, false, false, false, false, true] := by decide
    rw [e] at h; rw [h]; decide
  have hsub : ({0, 1, 4, 5, 6} : Finset ℕ) ⊆ depS 8 C := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    by_contra hni
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact key3 C hm 0 hni _ [false, false, false, false, true, false, false, false] _
        rfl rfl rfl (by decide) (by decide) r00 r30
    · exact key3 C hm 1 hni _ [false, false, false, false, true, false, false, false] _
        rfl rfl rfl (by decide) (by decide) r10 r30
    · exact key3 C hm 4 hni _ [true, false, false, false, false, false, false, false] _
        rfl rfl rfl (by decide) (by decide) r00 r03
    · exact key3 C hm 5 hni _ [true, false, false, false, false, false, false, false] _
        rfl rfl rfl (by decide) (by decide) r01 r03
    · exact key3 C hm 6 hni _ [true, false, false, false, false, false, false, false] _
        rfl rfl rfl (by decide) (by decide) r02 r03
  have h5 := Finset.card_le_card hsub
  have h6 : ({0, 1, 4, 5, 6} : Finset ℕ).card = 5 := by decide
  unfold PEqualNP.CircuitLowerBounds.Circuit.size at hs
  unfold PEqualNP.CircuitLowerBounds.Circuit.size at hc
  omega

end PEqualNP.Outside.L_meta_5461

theorem PEqualNP.Outside.L_meta_5461 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (119 : ℕ).testBit (4 * u.val + v.val)) 4 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (119 : ℕ).testBit (4 * u.val + v.val)) 3 := by
  exact ⟨PEqualNP.Outside.L_meta_5461.upper, PEqualNP.Outside.L_meta_5461.lower⟩
