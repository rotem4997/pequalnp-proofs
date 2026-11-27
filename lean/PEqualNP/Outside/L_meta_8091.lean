import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8091

open PEqualNP.CircuitLowerBounds

def stepF (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def mapG (f : ℕ → ℕ) (g : Gate) : Gate := { op := g.op, inputs := g.inputs.map f }

def mapC (f : ℕ → ℕ) (C : Circuit) : Circuit :=
  { gates := C.gates.map (mapG f), output := f C.output }

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepF x := rfl

theorem fold_inv (f : ℕ → ℕ) (n N : ℕ) (hf : ∀ i, f i = i ∨ (f i = N ∧ i < n)) :
    ∀ (gs : List Gate) (w w' : List Bool), w.length = w'.length → n ≤ w.length →
      w.length + gs.length ≤ N → (∀ i, w.getD (f i) false = w'.getD i false) →
      ∀ i, ((gs.map (mapG f)).foldl stepF w).getD (f i) false
        = (gs.foldl stepF w').getD i false := by
  intro gs
  induction gs with
  | nil => intro w w' _ _ _ h; simpa using h
  | cons g gs ih =>
    intro w w' hl hn hN h
    simp only [List.map_cons, List.foldl_cons]
    have hab : (mapG f g).op.eval ((mapG f g).inputs.map fun i => w.getD i false)
        = g.op.eval (g.inputs.map fun i => w'.getD i false) := by
      simp only [mapG, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact h j
    simp only [List.length_cons] at hN
    apply ih
    · simp [stepF, hl]
    · simp [stepF]; omega
    · simp [stepF]; omega
    · intro i
      simp only [stepF]
      rw [hab]
      rcases hf i with h1 | ⟨h1, h2⟩
      · rw [h1]
        have hi' := h i
        rw [h1] at hi'
        rcases lt_trichotomy i w.length with hi | hi | hi
        · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hl ▸ hi)]
          exact hi'
        · subst hi
          rw [List.getD_append_right _ _ _ _ le_rfl,
            List.getD_append_right _ _ _ _ (le_of_eq hl.symm)]
          simp [hl]
        · rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]
      · rw [h1]
        have hi' := h i
        rw [h1, List.getD_eq_default _ _ (by omega)] at hi'
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]
        exact hi'

theorem eval_map (f : ℕ → ℕ) (n N : ℕ) (hf : ∀ i, f i = i ∨ (f i = N ∧ i < n))
    (C : Circuit) (hN : n + C.size ≤ N) (x x' : List Bool) (hx : x.length = n)
    (hx' : x'.length = n) (h : ∀ i, x.getD (f i) false = x'.getD i false) :
    (mapC f C).eval x = C.eval x' := by
  unfold Circuit.eval
  rw [wires_eq, wires_eq]
  simp only [mapC]
  exact fold_inv f n N hf C.gates x x' (by omega) (by omega)
    (by simp only [Circuit.size] at hN; omega) h C.output

theorem getD_oa {a b : ℕ} (p : Fin a → Bool) (q : Fin b → Bool) (i : ℕ) :
    (List.ofFn p ++ List.ofFn q).getD i false
      = if h : i < a then p ⟨i, h⟩ else if h2 : i - a < b then q ⟨i - a, h2⟩ else false := by
  split_ifs with h h2
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    simp [List.getD_eq_getElem?_getD, h]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, h2]
  · rw [List.getD_eq_default _ _ (by simp; omega)]

end PEqualNP.Outside.L_meta_8091

open PEqualNP.Outside.L_meta_8091 in
theorem PEqualNP.Outside.L_meta_8091 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   have x5 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Fin x1 × Fin x2) → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Finset (Fin x1 × Fin x2)) => ∀ (x7 : Fin x1 → Bool) (x8 : Fin x2 → Bool), x5.eval (List.ofFn x7 ++ List.ofFn x8) = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x6 ∧ x7 x9 = Bool.true ∧ x8 x10 = Bool.true);   PEqualNP.MetaComplexity.Monotone2 x4 → x5 x4 x3 → (Finset.image Prod.fst x3).card + (Finset.image Prod.snd x3).card ≤ (2 : ℕ) * (x4.size + (1 : ℕ)) ∧ ∀ (x8 : Finset (Fin x1)) (x9 : Finset (Fin x2)), ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size ≤ x4.size ∧ x5 x10 ({x11 ∈ x3 | x11.1 ∈ x8 ∧ x11.2 ∈ x9}) := by
  intro x1 x2 x3 x4
  dsimp only
  intro hM hC
  classical
  refine ⟨?_, ?_⟩
  · -- every relevant variable is read by some gate or is the output
    let R : List ℕ := x4.output :: x4.gates.flatMap (fun g => g.inputs)
    have irr : ∀ i : ℕ, i < x1 + x2 → i ∉ R → ∀ (p : Fin x1 → Bool) (q : Fin x2 → Bool),
        x4.eval (List.ofFn p ++ List.ofFn q)
          = x4.eval (List.ofFn (fun a => p a && decide (a.val ≠ i))
              ++ List.ofFn (fun b => q b && decide (x1 + b.val ≠ i))) := by
      intro i hin hi p q
      have hR := hi
      simp only [R, List.mem_cons, List.mem_flatMap, not_or, not_exists, not_and] at hR
      obtain ⟨ho, hg⟩ := hR
      have hmap : mapC (fun j => if j = i then x1 + x2 + x4.size else j) x4 = x4 := by
        unfold mapC
        have hgs : x4.gates.map (mapG (fun j => if j = i then x1 + x2 + x4.size else j))
            = x4.gates := by
          conv_rhs => rw [← List.map_id x4.gates]
          apply List.map_congr_left
          intro g hgm
          unfold mapG
          have hin2 : g.inputs.map (fun j => if j = i then x1 + x2 + x4.size else j)
              = g.inputs := by
            conv_rhs => rw [← List.map_id g.inputs]
            apply List.map_congr_left
            intro j hj
            have hji : j ≠ i := fun e => hg g hgm (e ▸ hj)
            simp [hji]
          rw [hin2]
          rfl
        rw [hgs]
        beta_reduce
        rw [if_neg (fun (e : x4.output = i) => ho e.symm)]
      conv_lhs => rw [← hmap]
      apply eval_map _ (x1 + x2) (x1 + x2 + x4.size) _ x4 le_rfl _ _ (by simp) (by simp)
      · intro j
        by_cases hj : j = i
        · subst hj
          beta_reduce
          rw [if_pos rfl]
          rw [getD_oa, getD_oa, dif_neg (by omega), dif_neg (by omega)]
          split_ifs with h1 h2
          · simp
          · have : x1 + (j - x1) = j := by omega
            simp [this]
          · rfl
        · simp only [if_neg hj]
          rw [getD_oa, getD_oa]
          split_ifs with h1 h2
          · simp [hj]
          · have : x1 + (j - x1) = j := by omega
            simp [this, hj]
          · rfl
      · intro j
        by_cases hj : j = i
        · right; exact ⟨if_pos hj, hj ▸ hin⟩
        · left; exact if_neg hj
    have mem1 : ∀ a ∈ x3.image Prod.fst, (a.val) ∈ R := by
      intro a ha
      obtain ⟨⟨a', b⟩, hab, rfl⟩ := Finset.mem_image.mp ha
      by_contra hR
      have e := irr a'.val (by have := a'.isLt; omega) hR
        (fun c => decide (c = a')) (fun d => decide (d = b))
      have hT : x4.eval (List.ofFn (fun c => decide (c = a')) ++ List.ofFn (fun d => decide (d = b)))
          = true := by
        rw [hC, decide_eq_true_iff]
        exact ⟨a', b, hab, by simp, by simp⟩
      have hF : x4.eval (List.ofFn (fun c => decide (c = a') && decide (c.val ≠ a'.val))
          ++ List.ofFn (fun d => decide (d = b) && decide (x1 + d.val ≠ a'.val))) = false := by
        rw [hC, decide_eq_false_iff_not]
        rintro ⟨c, d, _, hc, _⟩
        simp at hc
        obtain ⟨h1, h2⟩ := hc
        subst h1
        exact h2 rfl
      have := hT.symm.trans (e.trans hF)
      simp at this
    have mem2 : ∀ b ∈ x3.image Prod.snd, (x1 + b.val) ∈ R := by
      intro b hb
      obtain ⟨⟨a, b'⟩, hab, rfl⟩ := Finset.mem_image.mp hb
      by_contra hR
      have e := irr (x1 + b'.val) (by have := b'.isLt; omega) hR
        (fun c => decide (c = a)) (fun d => decide (d = b'))
      have hT : x4.eval (List.ofFn (fun c => decide (c = a)) ++ List.ofFn (fun d => decide (d = b')))
          = true := by
        rw [hC, decide_eq_true_iff]
        exact ⟨a, b', hab, by simp, by simp⟩
      have hF : x4.eval (List.ofFn (fun c => decide (c = a) && decide (c.val ≠ x1 + b'.val))
          ++ List.ofFn (fun d => decide (d = b') && decide (x1 + d.val ≠ x1 + b'.val)))
          = false := by
        rw [hC, decide_eq_false_iff_not]
        rintro ⟨c, d, _, _, hd⟩
        simp at hd
        obtain ⟨h1, h2⟩ := hd
        subst h1
        exact h2 rfl
      have := hT.symm.trans (e.trans hF)
      simp at this
    have hRlen : R.length ≤ 2 * x4.size + 1 := by
      simp only [R, List.length_cons, List.length_flatMap]
      have := List.sum_le_card_nsmul (x4.gates.map fun g => g.inputs.length) 2 (by
        intro k hk
        obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hk
        exact (hM g hg).2)
      simp only [List.length_map, smul_eq_mul] at this
      simp only [PEqualNP.CircuitLowerBounds.Circuit.size]
      omega
    have hdisj : Disjoint ((x3.image Prod.fst).image (fun a => a.val))
        ((x3.image Prod.snd).image (fun b => x1 + b.val)) := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨b, _, hb⟩ := Finset.mem_image.mp h2
      have := a.isLt
      omega
    have hsub : ((x3.image Prod.fst).image (fun a => a.val)
        ∪ (x3.image Prod.snd).image (fun b => x1 + b.val)) ⊆ R.toFinset := by
      intro j hj
      rw [List.mem_toFinset]
      rcases Finset.mem_union.mp hj with hj | hj
      · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hj
        exact mem1 a ha
      · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hj
        exact mem2 b hb
    have hc1 : ((x3.image Prod.fst).image (fun a => a.val)).card = (x3.image Prod.fst).card :=
      Finset.card_image_of_injective _ Fin.val_injective
    have hc2 : ((x3.image Prod.snd).image (fun b => x1 + b.val)).card
        = (x3.image Prod.snd).card :=
      Finset.card_image_of_injective _ (fun u v huv => Fin.ext (by simpa using huv))
    have hu := Finset.card_union_of_disjoint hdisj
    have h3 := Finset.card_le_card hsub
    have h4 := List.toFinset_card_le R
    omega
  · intro X8 X9
    let keep : ℕ → Prop := fun i =>
      (∃ a : Fin x1, a.val = i ∧ a ∈ X8) ∨ (∃ b : Fin x2, x1 + b.val = i ∧ b ∈ X9)
    let f : ℕ → ℕ := fun i => if i < x1 + x2 ∧ ¬ keep i then x1 + x2 + x4.size else i
    have hf : ∀ i, f i = i ∨ (f i = x1 + x2 + x4.size ∧ i < x1 + x2) := by
      intro i
      by_cases h : i < x1 + x2 ∧ ¬ keep i
      · right; exact ⟨if_pos h, h.1⟩
      · left; exact if_neg h
    refine ⟨mapC f x4, ?_, ?_, ?_⟩
    · intro g hg
      simp only [mapC, List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      simp only [mapG, List.length_map]
      exact hM g0 hg0
    · simp [mapC, PEqualNP.CircuitLowerBounds.Circuit.size]
    · intro p q
      have hinv : ∀ i, (List.ofFn p ++ List.ofFn q).getD (f i) false
          = (List.ofFn (fun a => p a && decide (a ∈ X8))
              ++ List.ofFn (fun b => q b && decide (b ∈ X9))).getD i false := by
        intro i
        by_cases hlt : i < x1
        · have hk : keep i ↔ (⟨i, hlt⟩ : Fin x1) ∈ X8 := by
            constructor
            · rintro (⟨a, ha, hm⟩ | ⟨b, hb, _⟩)
              · have : a = ⟨i, hlt⟩ := Fin.ext ha
                rw [this] at hm
                exact hm
              · omega
            · intro h
              exact Or.inl ⟨_, rfl, h⟩
          by_cases hm : (⟨i, hlt⟩ : Fin x1) ∈ X8
          · have hfi : f i = i := if_neg (fun h => h.2 (hk.mpr hm))
            rw [hfi, getD_oa, getD_oa]
            simp [hlt, hm]
          · have hfi : f i = x1 + x2 + x4.size := if_pos ⟨by omega, fun h => hm (hk.mp h)⟩
            rw [hfi, getD_oa, getD_oa, dif_neg (by omega), dif_neg (by omega), dif_pos hlt]
            simp [hm]
        · by_cases hlt2 : i < x1 + x2
          · have hk : keep i ↔ (⟨i - x1, by omega⟩ : Fin x2) ∈ X9 := by
              constructor
              · rintro (⟨a, ha, _⟩ | ⟨b', hb', hm⟩)
                · have := a.isLt
                  omega
                · have : b' = ⟨i - x1, by omega⟩ := Fin.ext (by simp; omega)
                  rw [this] at hm
                  exact hm
              · intro h
                exact Or.inr ⟨_, by simp; omega, h⟩
            by_cases hm : (⟨i - x1, by omega⟩ : Fin x2) ∈ X9
            · have hfi : f i = i := if_neg (fun h => h.2 (hk.mpr hm))
              rw [hfi, getD_oa, getD_oa, dif_neg hlt, dif_neg hlt, dif_pos (by omega),
                dif_pos (by omega)]
              simp [hm]
            · have hfi : f i = x1 + x2 + x4.size := if_pos ⟨hlt2, fun h => hm (hk.mp h)⟩
              rw [hfi, getD_oa, getD_oa, dif_neg (by omega), dif_neg (by omega), dif_neg hlt,
                dif_pos (by omega)]
              simp [hm]
          · have hfi : f i = i := if_neg (fun h => hlt2 h.1)
            rw [hfi, getD_oa, getD_oa, dif_neg hlt, dif_neg hlt, dif_neg (by omega),
              dif_neg (by omega)]
      rw [eval_map f (x1 + x2) (x1 + x2 + x4.size) hf x4 le_rfl _ _ (by simp) (by simp) hinv,
        hC]
      apply decide_eq_decide.mpr
      constructor
      · rintro ⟨a, b, h1, h2, h3⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h2 h3
        exact ⟨a, b, Finset.mem_filter.mpr ⟨h1, h2.2, h3.2⟩, h2.1, h3.1⟩
      · rintro ⟨a, b, h1, h2, h3⟩
        obtain ⟨h1, h4, h5⟩ := Finset.mem_filter.mp h1
        exact ⟨a, b, h1, by simp [h2, h4], by simp [h3, h5]⟩
