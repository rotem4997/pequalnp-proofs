import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7796

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Wf (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem Wf_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    Wf (gs ++ [g]) x = Wf gs x ++ [g.op.eval (g.inputs.map fun i => (Wf gs x).getD i false)] := by
  simp [Wf, List.foldl_append]

theorem Wf_length (gs : List Gate) (x : List Bool) : (Wf gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [Wf]
  | append_singleton gs g ih => rw [Wf_snoc]; simp [ih]; omega

theorem getD_snoc {α : Type} (l : List α) (a d : α) (t : ℕ) :
    (l ++ [a]).getD t d =
      if t < l.length then l.getD t d else if t = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [if_pos h1, List.getElem?_append_left h1]
  · rw [if_neg h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [if_neg h2]
      have : t - l.length ≠ 0 := by omega
      simp [List.getElem?_cons, this]

theorem getD_false_lt {l : List Bool} {t : ℕ} (h : l.getD t false = true) : t < l.length := by
  by_contra h'
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
  simp at h

def Le (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true

theorem eval_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro i hi; exact h i hi (he i hi)
  · obtain ⟨i, hi, hv⟩ := he; exact ⟨i, hi, h i hi hv⟩

theorem Wf_mono (gs : List Gate) (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : Le x y) : Le (Wf gs x) (Wf gs y) := by
  induction gs using List.reverseRecOn with
  | nil => simpa [Wf] using hxy
  | append_singleton gs g ih =>
    have ih := ih (fun g' hg' => hm g' (by simp [hg']))
    intro t ht
    have hlen : (Wf gs x).length = (Wf gs y).length := by simp [Wf_length, hl]
    rw [Wf_snoc, getD_snoc] at ht ⊢
    rw [← hlen]
    by_cases h1 : t < (Wf gs x).length
    · rw [if_pos h1] at ht ⊢; exact ih t ht
    · rw [if_neg h1] at ht ⊢
      by_cases h2 : t = (Wf gs x).length
      · rw [if_pos h2] at ht ⊢
        exact eval_mono g (hm g (by simp)) _ _ (fun i _ => ih i) ht
      · rw [if_neg h2] at ht; simp at ht

theorem fun_mono (C : Circuit) (hC : Monotone2 C) (x y : Fin 26 → Bool)
    (hxy : ∀ i, x i = true → y i = true) (h : circuitFun 26 C x = true) :
    circuitFun 26 C y = true := by
  have hm : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hC g hg).1
    simpa using this
  have hle : Le (List.ofFn x) (List.ofFn y) := by
    intro i hi
    by_cases h26 : i < 26
    · have e1 : (List.ofFn x).getD i false = x ⟨i, h26⟩ := by
        rw [List.getD_eq_getElem _ _ (by simpa using h26), List.getElem_ofFn]
      have e2 : (List.ofFn y).getD i false = y ⟨i, h26⟩ := by
        rw [List.getD_eq_getElem _ _ (by simpa using h26), List.getElem_ofFn]
      rw [e1] at hi
      rw [e2]
      exact hxy _ hi
    · exfalso
      have := getD_false_lt hi
      simp at this
      omega
  have key := Wf_mono C.gates hm (List.ofFn x) (List.ofFn y) (by simp) hle
  exact key C.output h

def XS : List (Finset (Fin 13)) := [{0, 1, 2}, {3, 4, 5}, {6, 8, 12}, {7, 9, 10, 11}, {2, 4, 7}, {0, 4, 6, 9}, {0, 3, 8, 11}, {3, 10, 12}, {2, 5, 8, 10}, {1, 6, 7}, {1, 2, 9, 12}, {5, 6, 11}, {7, 8, 9}, {0, 4, 10, 12}, {2, 3, 6}, {1, 10, 11}, {5, 7, 12}, {4, 11, 12}, {1, 3, 4, 8}, {0, 3, 7}, {0, 5, 9}, {2, 3, 9}, {0, 1, 5}, {1, 6, 10}, {0, 2, 11}]
def YS : List (Finset (Fin 13)) := [{3, 7, 8, 9}, {6, 10, 11, 12}, {0, 1, 2, 4}, {3, 5, 12}, {0, 5, 9, 10}, {2, 7, 11}, {1, 6, 9}, {4, 5, 6, 8}, {0, 3, 11}, {2, 8, 9, 12}, {4, 7, 10}, {0, 1, 7, 12}, {1, 2, 3, 10}, {2, 5, 6}, {4, 8, 9, 11}, {3, 4, 6, 12}, {0, 1, 8, 10}, {0, 5, 6, 7}, {6, 9, 10}, {1, 5, 8, 9}, {1, 3, 7, 11}, {4, 5, 10, 11}, {3, 6, 7, 8}, {2, 4, 8, 12}, {3, 5, 7, 9}]

def X (i : Fin 25) : Finset (Fin 13) := XS.getD i ∅
def Y (i : Fin 25) : Finset (Fin 13) := YS.getD i ∅

set_option maxRecDepth 100000 in
theorem good : ∀ i : Fin 25,
    ((∀ l : Fin 13, l ∈ Y i ↔ ∀ p ∈ X i, ¬(p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)) ∧
    (∀ p ∉ X i, ∃ l ∈ Y i, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)) ∧
    (¬∃ l : Fin 13, ∀ p ∈ X i, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)) ∧
    ¬∃ p : Fin 13, ∀ l ∈ Y i, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)) := by
  decide

set_option maxRecDepth 100000 in
theorem cover : ∀ a b : Fin 26,
    (¬∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
      (a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l ∨ b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l)) →
    ∃ i : Fin 25, Fin.addCases (fun p => decide (p ∈ X i)) (fun l => decide (l ∈ Y i)) a = true ∧
      Fin.addCases (fun p => decide (p ∈ X i)) (fun l => decide (l ∈ Y i)) b = true := by
  decide

theorem main (C : Circuit) (hC : Monotone2 C)
    (hF : ∀ X Y : Finset (Fin 13),
      ((∀ l : Fin 13, l ∈ Y ↔ ∀ p ∈ X, ¬(p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)) ∧
      (∀ p ∉ X, ∃ l ∈ Y, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)) ∧
      (¬∃ l : Fin 13, ∀ p ∈ X, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)) ∧
      ¬∃ p : Fin 13, ∀ l ∈ Y, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9)) →
      circuitFun 26 C (fun w => Fin.addCases (fun p => decide (p ∈ X)) (fun l => decide (l ∈ Y)) w)
        = false)
    (a b : Fin 26)
    (hne : ¬∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
      (a = Fin.castAdd 13 p ∧ b = Fin.natAdd 13 l ∨ b = Fin.castAdd 13 p ∧ a = Fin.natAdd 13 l)) :
    circuitFun 26 C (fun w => decide (w = a ∨ w = b)) = false := by
  obtain ⟨i, ha, hb⟩ := cover a b hne
  have h1 := hF (X i) (Y i) (good i)
  cases hv : circuitFun 26 C (fun w => decide (w = a ∨ w = b)) with
  | false => rfl
  | true =>
    have hmono := fun_mono C hC _ _ (by
      intro w hw
      simp only [decide_eq_true_eq] at hw
      rcases hw with rfl | rfl
      · exact ha
      · exact hb) hv
    rw [h1] at hmono
    exact absurd hmono (by decide)

end PEqualNP.Outside.L_meta_7796

theorem PEqualNP.Outside.L_meta_7796 : let x1 : Type := Fin (13 : ℕ); let x2 : Type := Finset x1; have x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => x3 = x4 ∨ x3 = x4 + (1 : x1) ∨ x3 = x4 + (3 : x1) ∨ x3 = x4 + (9 : x1); have x4 : PEqualNP.CircuitLowerBounds.Circuit → x2 → x2 → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : x2) => PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x4 fun (x7 : Fin (26 : ℕ)) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x5)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x6)) x7; have x5 : x2 → x2 → Prop := fun (x5 x6 : x2) => (∀ (x7 : x1), x7 ∈ x6 ↔ ∀ x8 ∈ x5, ¬x3 x8 x7) ∧ (∀ x7 ∉ x5, ∃ x9 ∈ x6, x3 x7 x9) ∧ (¬∃ (x7 : x1), ∀ x8 ∈ x5, x3 x8 x7) ∧ ¬∃ (x7 : x1), ∀ x8 ∈ x6, x3 x7 x8; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 → (∀ (x8 x9 : x2), x5 x8 x9 → x4 x6 x8 x9 = Bool.false) → ∀ (x9 x10 : Fin (26 : ℕ)), (¬∃ (x11 : x1) (x12 : x1), x3 x11 x12 ∧ (x9 = Fin.castAdd (13 : ℕ) x11 ∧ x10 = Fin.natAdd (13 : ℕ) x12 ∨ x10 = Fin.castAdd (13 : ℕ) x11 ∧ x9 = Fin.natAdd (13 : ℕ) x12)) → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x6 fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = x9 ∨ x12 = x10)) = Bool.false := by
  intro x1 x2 x3 x4 x5 C hC hF a b hne
  exact PEqualNP.Outside.L_meta_7796.main C hC hF a b hne
