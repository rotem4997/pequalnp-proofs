import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18654

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Rel (w w' : List Bool) : Prop := w.length = w'.length ∧ ∀ i, w.getD i false = true → w'.getD i false = true

theorem getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i < w.length then w.getD i false else if i = w.length then b else false := by
  rcases Nat.lt_or_ge i w.length with h | h
  · simp [h, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rcases Nat.eq_or_lt_of_le h with h | h
    · subst h; simp [List.getD_eq_getElem?_getD]
    · have h1 : ¬ i < w.length := by omega
      have h2 : i ≠ w.length := by omega
      simp only [h1, h2, if_false]
      rw [List.getD_eq_default]
      simp; omega

theorem eval_mono (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (w w' : List Bool) (h : Rel w w')
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp only [GateOp.eval, List.all_map, List.any_map, List.all_eq_true, List.any_eq_true, Function.comp, id] at he ⊢
  · intro i hi; exact h.2 i (he i hi)
  · obtain ⟨i, hi, hv⟩ := he; exact ⟨i, hi, h.2 i hv⟩

theorem fold_mono : ∀ (gs : List Gate), (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) →
    ∀ w w' : List Bool, Rel w w' →
    Rel (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w')
  | [], _, w, w', h => h
  | g :: gs, hg, w, w', h => by
    simp only [List.foldl_cons]
    apply fold_mono gs (fun x hx => hg x (List.mem_cons_of_mem _ hx))
    refine ⟨by simp [h.1], ?_⟩
    intro i hi
    rw [getD_snoc] at hi ⊢
    rw [← h.1]
    split_ifs at hi ⊢ with h1 h2
    · exact h.2 i hi
    · exact eval_mono g (hg g (List.mem_cons_self ..)) w w' h hi

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_18654

theorem PEqualNP.Outside.L_meta_18654 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → ∀ (x4 x5 : Fin x1 → Bool), (∀ (x6 : Fin x1), x4 x6 = Bool.true → x5 x6 = Bool.true) → ∀ (x7 : ℕ), PEqualNP.ReadTwo.wval x2 x4 x7 = Bool.true → PEqualNP.ReadTwo.wval x2 x5 x7 = Bool.true := by
  intro x1 x2 hao x4 x5 hle x7 h
  have hr : L_meta_18654.Rel (List.ofFn x4) (List.ofFn x5) := by
    refine ⟨by simp, ?_⟩
    intro i hi
    rcases Nat.lt_or_ge i x1 with h | h
    · rw [List.getD_eq_getElem _ _ (by simpa using h)] at hi ⊢
      simp only [List.getElem_ofFn] at hi ⊢
      exact hle _ hi
    · rw [List.getD_eq_default _ _ (by simpa using h)] at hi
      exact absurd hi (by simp)
  have hop : ∀ g ∈ x2.gates, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) := by
    intro g hg
    rcases hao.1 g hg with e | e <;> simp [e]
  exact (L_meta_18654.fold_mono x2.gates hop _ _ hr).2 x7 h
