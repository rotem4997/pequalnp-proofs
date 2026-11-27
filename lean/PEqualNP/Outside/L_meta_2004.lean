import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2004

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wv (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

lemma wv_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wv (gs ++ [g]) x = step (wv gs x) g := by
  simp [wv, List.foldl_append]

lemma wv_len (gs : List Gate) (x : List Bool) : (wv gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wv]
  | append_singleton gs g ih =>
    rw [wv_snoc]
    simp [step, ih]
    omega

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) :
    (step w g).getD i false = if i < w.length then w.getD i false
      else if i = w.length then g.op.eval (g.inputs.map fun k => w.getD k false) else false := by
  unfold step
  rcases lt_trichotomy i w.length with hi | hi | hi
  · rw [List.getD_append _ _ _ _ hi]
    simp [hi]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hi]
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    obtain ⟨k, hk⟩ : ∃ k, i - w.length = k + 1 := ⟨i - w.length - 1, by omega⟩
    have h1 : ¬ i < w.length := by omega
    have h2 : i ≠ w.length := by omega
    rw [hk]
    simp [h1, h2]

lemma gate_cases (l : List ℕ) (h : l.length ≤ 2) :
    l = [] ∨ (∃ a, l = [a]) ∨ ∃ a b, l = [a, b] := by
  match l, h with
  | [], _ => exact Or.inl rfl
  | [a], _ => exact Or.inr (Or.inl ⟨a, rfl⟩)
  | [a, b], _ => exact Or.inr (Or.inr ⟨a, b, rfl⟩)
  | _ :: _ :: _ :: _, h => simp at h

lemma image_merge {ι : Type} [DecidableEq ι] (X : Finset ι) (a b : ι) :
    X.card ≤ (X.image (fun x => if x = a then b else x)).card + 1 := by
  have h1 : X.erase a ⊆ X.image (fun x => if x = a then b else x) := by
    intro x hx
    rw [Finset.mem_erase] at hx
    exact Finset.mem_image.mpr ⟨x, hx.2, by simp [hx.1]⟩
  have h2 := Finset.card_le_card h1
  have h3 := Finset.pred_card_le_card_erase (s := X) (a := a)
  omega

lemma ofFn_getD (n : ℕ) (f : Fin n → Bool) (i : ℕ) :
    (List.ofFn f).getD i false = if h : i < n then f ⟨i, h⟩ else false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split <;> simp

lemma cf_eq (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    PEqualNP.MetaComplexity.circuitFun n C x = (wv C.gates (List.ofFn x)).getD C.output false :=
  rfl

lemma gate_key (n : ℕ) (W : (Fin n → Bool) → ℕ → Bool) (c : Fin n → Fin n)
    (hc : ∀ i, ∃ k, ∀ x y : Fin n → Bool, (∀ j, c j = c k → x j = y j) → W x i = W y i)
    (g : Gate) (hlen : g.inputs.length ≤ 2) :
    ∃ c' : Fin n → Fin n,
      (Finset.univ.image c).card ≤ (Finset.univ.image c').card + 1 ∧
      (∀ v v', c v = c v' → c' v = c' v') ∧
      ∃ k, ∀ x y : Fin n → Bool, (∀ j, c' j = c' k → x j = y j) →
        g.op.eval (g.inputs.map (W x)) = g.op.eval (g.inputs.map (W y)) := by
  rcases gate_cases g.inputs hlen with hi | ⟨a, hi⟩ | ⟨a, b, hi⟩
  · obtain ⟨k, _⟩ := hc 0
    refine ⟨c, Nat.le_add_right _ _, fun _ _ h => h, k, ?_⟩
    intro x y _
    rw [hi]
    rfl
  · obtain ⟨k, hk⟩ := hc a
    refine ⟨c, Nat.le_add_right _ _, fun _ _ h => h, k, ?_⟩
    intro x y h
    rw [hi, List.map_singleton, List.map_singleton, hk x y h]
  · obtain ⟨ka, hka⟩ := hc a
    obtain ⟨kb, hkb⟩ := hc b
    refine ⟨fun v => if c v = c ka then c kb else c v, ?_, ?_, kb, ?_⟩
    · have e : Finset.univ.image (fun v => if c v = c ka then c kb else c v) =
          (Finset.univ.image c).image (fun x => if x = c ka then c kb else x) := by
        rw [Finset.image_image]
        rfl
      rw [e]
      exact image_merge (Finset.univ.image c) (c ka) (c kb)
    · intro v v' h
      simp only [h]
    · intro x y h
      have e : (if c kb = c ka then c kb else c kb) = c kb := by split <;> rfl
      simp only [e] at h
      have h1 : W x a = W y a := by
        apply hka
        intro j hj
        apply h
        simp [hj]
      have h2 : W x b = W y b := by
        apply hkb
        intro j hj
        apply h
        simp [hj]
      rw [hi]
      simp only [List.map_cons, List.map_nil, h1, h2]

lemma core (n : ℕ) (k0 : Fin n) (gs : List Gate) :
    (∀ g ∈ gs, g.inputs.length ≤ 2) →
    ∃ c : Fin n → Fin n,
      n ≤ (Finset.univ.image c).card + gs.length ∧
      ∀ i, ∃ k, ∀ x y : Fin n → Bool, (∀ j, c j = c k → x j = y j) →
        (wv gs (List.ofFn x)).getD i false = (wv gs (List.ofFn y)).getD i false := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨id, by simp, ?_⟩
    intro i
    by_cases hin : i < n
    · refine ⟨⟨i, hin⟩, ?_⟩
      intro x y h
      show (List.ofFn x).getD i false = (List.ofFn y).getD i false
      rw [ofFn_getD, ofFn_getD]
      simp only [hin, dite_true]
      exact h _ rfl
    · refine ⟨k0, ?_⟩
      intro x y _
      show (List.ofFn x).getD i false = (List.ofFn y).getD i false
      rw [ofFn_getD, ofFn_getD]
      simp [hin]
  | append_singleton gs g ih =>
    intro hm
    obtain ⟨c, hc1, hc2⟩ := ih (fun g' hg' => hm g' (by simp [hg']))
    have hg := hm g (by simp)
    obtain ⟨c', k1, k2, k3, hk3⟩ := gate_key n (fun x i => (wv gs (List.ofFn x)).getD i false)
      c hc2 g hg
    refine ⟨c', ?_, ?_⟩
    · rw [List.length_append, List.length_singleton]
      omega
    · intro i
      by_cases hi : i < n + gs.length
      · obtain ⟨k, hk⟩ := hc2 i
        refine ⟨k, ?_⟩
        intro x y h
        rw [wv_snoc, wv_snoc, step_getD, step_getD, wv_len, wv_len]
        simp only [List.length_ofFn, hi, ite_true]
        exact hk x y (fun j hj => h j (k2 j k hj))
      · by_cases hi2 : i = n + gs.length
        · refine ⟨k3, ?_⟩
          intro x y h
          rw [wv_snoc, wv_snoc, step_getD, step_getD, wv_len, wv_len]
          simp only [List.length_ofFn, hi2, ite_true, lt_irrefl, ite_false]
          exact hk3 x y h
        · refine ⟨k0, ?_⟩
          intro x y _
          rw [wv_snoc, wv_snoc, step_getD, step_getD, wv_len, wv_len]
          simp [hi, hi2]

lemma main (n : ℕ) (C : Circuit) (hM : PEqualNP.MetaComplexity.Monotone2 C)
    (he : ∀ i : Fin n, ∃ (x : Fin n → Bool) (y : Fin n → Bool), (∀ j : Fin n, j ≠ i → x j = y j) ∧
      PEqualNP.MetaComplexity.circuitFun n C x ≠ PEqualNP.MetaComplexity.circuitFun n C y) :
    n ≤ C.size + 1 := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · omega
  obtain ⟨c, hc1, hc2⟩ := core n ⟨0, hpos⟩ C.gates (fun g hg => (hM g hg).2)
  obtain ⟨k, hk⟩ := hc2 C.output
  have hle : (Finset.univ.image c).card ≤ 1 := by
    have hall : ∀ i, c i = c k := by
      intro i
      obtain ⟨x, y, hxy, hne⟩ := he i
      by_contra hci
      apply hne
      rw [cf_eq, cf_eq]
      apply hk
      intro j hj
      apply hxy
      rintro rfl
      exact hci hj
    rw [Finset.card_le_one]
    intro a ha a' ha'
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v', _, rfl⟩ := Finset.mem_image.mp ha'
    rw [hall v, hall v']
  have : C.size = C.gates.length := rfl
  omega

end PEqualNP.Outside.L_meta_2004

theorem PEqualNP.Outside.L_meta_2004 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → (∀ (x4 : Fin x1), ∃ (x5 : Fin x1 → Bool) (x6 : Fin x1 → Bool), (∀ (x7 : Fin x1), x7 ≠ x4 → x5 x7 = x6 x7) ∧ PEqualNP.MetaComplexity.circuitFun x1 x2 x5 ≠ PEqualNP.MetaComplexity.circuitFun x1 x2 x6) → x1 ≤ x2.size + (1 : ℕ) := by
  intro x1 x2 h1 h2
  exact PEqualNP.Outside.L_meta_2004.main x1 x2 h1 h2
