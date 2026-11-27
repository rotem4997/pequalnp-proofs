import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18430_aux
open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem preserve (gs : List Gate) (ops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (hskip : ∀ g ∈ gs, 2 ∉ g.inputs) (a b : List Bool) (hlen : b.length = a.length)
    (h : ∀ i, i ≠ 2 → a.getD i false = true → b.getD i false = true) :
    ∀ i, i ≠ 2 → (gs.foldl step a).getD i false = true → (gs.foldl step b).getD i false = true := by
  induction gs generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    apply ih (fun t ht => ops t (by simp [ht])) (fun t ht => hskip t (by simp [ht])) (step a g) (step b g) (by simp [step,hlen])
    intro i hi hv
    by_cases lt : i < a.length
    · simpa only [step,List.getD_eq_getElem?_getD,List.getElem?_append_left lt,List.getElem?_append_left (show i < b.length by omega)] using (h i hi (by simpa only [step,List.getD_eq_getElem?_getD,List.getElem?_append_left lt] using hv))
    by_cases eq : i = a.length
    · subst i
      simp only [step,List.getD_eq_getElem?_getD,List.getElem?_append_right (Nat.le_refl _),List.getElem?_append_right (show b.length ≤ a.length by omega),hlen,Nat.sub_self,List.getElem?_cons_zero,Option.getD_some] at hv ⊢
      have transfer (i) (hm : i ∈ g.inputs) : a.getD i false = true → b.getD i false = true :=
        h i (fun eq => hskip g (by simp) (eq ▸ hm))
      rcases ops g (by simp) with op|op
      · simp only [op,GateOp.eval,List.all_map,Function.comp_def,List.all_eq_true] at hv ⊢
        exact fun j hj => transfer j hj (hv j hj)
      · simp only [op,GateOp.eval,List.any_map,Function.comp_def,List.any_eq_true] at hv ⊢
        obtain ⟨j,hj,v⟩ := hv
        exact ⟨j,hj,transfer j hj v⟩
    · simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none (show (step a g).length ≤ i by simp [step]; omega)] at hv

private theorem blind : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x3 ∈ x1.gates, (2 : ℕ) ∉ x3.inputs) → ∀ (x4 : ℕ), x4 ≠ (2 : ℕ) → ∀ (x6 x7 : Fin (14 : ℕ) → Bool), (∀ (x8 : Fin (14 : ℕ)), x8 ≠ (2 : Fin (14 : ℕ)) → x6 x8 = Bool.true → x7 x8 = Bool.true) → PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x6 x4 = Bool.true → PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x7 x4 = Bool.true := by
  intro C ao hskip i hi x y h
  apply preserve C.gates ao.1 hskip (List.ofFn x) (List.ofFn y) (by simp) _ i hi
  intro j hj
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  by_cases lt : j < 14
  · simpa [lt] using h ⟨j,lt⟩ (fun e => hj (congrArg Fin.val e))
  · simp [lt]
end PEqualNP.Outside.L_meta_18430_aux

open PEqualNP.Outside.L_meta_18430_aux in
theorem PEqualNP.Outside.L_meta_18430 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x3 ∈ x1.gates, (2 : ℕ) ∉ x3.inputs) → ∀ (x4 : ℕ), x4 ≠ (2 : ℕ) → ∀ (x6 x7 : Fin (14 : ℕ) → Bool), (∀ (x8 : Fin (14 : ℕ)), x8 ≠ (2 : Fin (14 : ℕ)) → x6 x8 = Bool.true → x7 x8 = Bool.true) → PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x6 x4 = Bool.true → PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x7 x4 = Bool.true) := blind
