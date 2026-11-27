import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18524_aux
open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem preserve (gs : List Gate) (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (a b : List Bool) (hlen : b.length = a.length)
    (h : ∀ i, a.getD i false = true → b.getD i false = true) :
    ∀ i, (gs.foldl step a).getD i false = true → (gs.foldl step b).getD i false = true := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    apply ih (fun t ht => ops t (by simp [ht])) (step a g) (step b g) (by simp [step,hlen])
    intro i hv
    by_cases lt : i < a.length
    · simpa only [step,List.getD_eq_getElem?_getD,List.getElem?_append_left lt,List.getElem?_append_left (show i < b.length by omega)] using (h i (by simpa only [step,List.getD_eq_getElem?_getD,List.getElem?_append_left lt] using hv))
    by_cases eq : i = a.length
    · subst i
      simp only [step,List.getD_eq_getElem?_getD,List.getElem?_append_right (Nat.le_refl _),List.getElem?_append_right (show b.length ≤ a.length by omega),hlen,Nat.sub_self,List.getElem?_cons_zero,Option.getD_some] at hv ⊢
      have transfer (i) (hm : i ∈ g.inputs) : a.getD i false = true → b.getD i false = true :=
        h i
      rcases ops g (by simp) with op|op
      · simp only [op,GateOp.eval,List.all_map,Function.comp_def,List.all_eq_true] at hv ⊢
        exact fun j hj => transfer j hj (hv j hj)
      · simp only [op,GateOp.eval,List.any_map,Function.comp_def,List.any_eq_true] at hv ⊢
        obtain ⟨j,hj,v⟩ := hv
        exact ⟨j,hj,transfer j hj v⟩
    · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (show (step a g).length ≤ i by simp [step]; omega)] at hv

private theorem maxTest : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ (x3 x4 : Fin (7 : ℕ)), x4 ≠ (1 : Fin (7 : ℕ)) → x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ)) → x1.eval (List.ofFn fun (x7 : Fin (14 : ℕ)) => Decidable.decide (x7 = Fin.castAdd (7 : ℕ) x3 ∨ x7 = Fin.natAdd (7 : ℕ) x4)) = Bool.true) → (∀ (x4 : Fin (14 : ℕ) → Bool), Maximal (fun (x5 : Fin (14 : ℕ) → Bool) => ¬∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true) x4 → x1.eval (List.ofFn x4) = Bool.false) → ∀ (x5 : Fin (14 : ℕ) → Bool), (x1.eval (List.ofFn x5) = Bool.true → ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x8) = Bool.true) ∧ ((∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), x7 ≠ (1 : Fin (7 : ℕ)) ∧ (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true) → x1.eval (List.ofFn x5) = Bool.true) := by
  intro C ao hpos hneg x
  have mono (a b : Fin 14 → Bool) (hab : a ≤ b) :
      C.eval (List.ofFn a) = true → C.eval (List.ofFn b) = true := by
    apply preserve C.gates ao.1 (List.ofFn a) (List.ofFn b) (by simp) _ C.output
    intro i
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn]
    by_cases hi : i < 14
    · simpa only [dite_eq_left hi,Option.getD_some] using (show a ⟨i,hi⟩ = true → b ⟨i,hi⟩ = true from by
        have h := hab ⟨i,hi⟩
        intro ha
        exact Bool.eq_true_of_true_le (ha ▸ h))
    · simp [hi]
  constructor
  · intro yes
    by_contra bad
    obtain ⟨y,hxy,hy⟩ := Finite.exists_le_maximal (a := x) (p := fun z : Fin 14 → Bool => ¬ ∃ (p l : Fin 7), (p = l ∨ p = l+1 ∨ p = l+3) ∧ z (Fin.castAdd 7 p) = true ∧ z (Fin.natAdd 7 l) = true) bad
    have ht := mono x y hxy yes
    rw [hneg y hy] at ht
    contradiction
  · rintro ⟨p,l,h1,hinc,hp,hl⟩
    apply mono _ x _ (hpos p l h1 hinc)
    intro i
    change decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l) ≤ x i
    by_cases e : i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l
    · rw [decide_eq_true e]
      rcases e with rfl|rfl
      · rw [hp]
      · rw [hl]
    · rw [decide_eq_false e]
      exact Bool.false_le _
end PEqualNP.Outside.L_meta_18524_aux

open PEqualNP.Outside.L_meta_18524_aux in
theorem PEqualNP.Outside.L_meta_18524 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ (x3 x4 : Fin (7 : ℕ)), x4 ≠ (1 : Fin (7 : ℕ)) → x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ)) → x1.eval (List.ofFn fun (x7 : Fin (14 : ℕ)) => Decidable.decide (x7 = Fin.castAdd (7 : ℕ) x3 ∨ x7 = Fin.natAdd (7 : ℕ) x4)) = Bool.true) → (∀ (x4 : Fin (14 : ℕ) → Bool), Maximal (fun (x5 : Fin (14 : ℕ) → Bool) => ¬∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true) x4 → x1.eval (List.ofFn x4) = Bool.false) → ∀ (x5 : Fin (14 : ℕ) → Bool), (x1.eval (List.ofFn x5) = Bool.true → ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x8) = Bool.true) ∧ ((∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), x7 ≠ (1 : Fin (7 : ℕ)) ∧ (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x5 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x5 (Fin.natAdd (7 : ℕ) x7) = Bool.true) → x1.eval (List.ofFn x5) = Bool.true)) := maxTest
