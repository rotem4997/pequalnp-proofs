import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7676_aux

open PEqualNP.CircuitLowerBounds

theorem step (gs : List Gate) (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w v : List Bool), w.length = v.length →
      (∀ i, w.getD i false = true → v.getD i false = true) →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
        = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) v).length ∧
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false = true →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) v).getD i false = true := by
  induction gs with
  | nil => intro w v hl hm; exact ⟨hl, hm⟩
  | cons g gs ih =>
    intro w v hl hm
    simp only [List.foldl_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    · simp [hl]
    · have hab : g.op.eval (g.inputs.map fun i => w.getD i false) = true →
          g.op.eval (g.inputs.map fun i => v.getD i false) = true := by
        rcases hg g (List.mem_cons_self) with h | h
        · rw [h]; simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
          rintro H x ⟨j, hj, rfl⟩
          exact hm j (H _ ⟨j, hj, rfl⟩)
        · rw [h]; simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
          rintro ⟨x, ⟨j, hj, rfl⟩, hx⟩
          exact ⟨_, ⟨j, hj, rfl⟩, hm j hx⟩
      intro i hi
      rcases lt_trichotomy i w.length with h1 | h1 | h1
      · rw [List.getD_append _ _ _ _ h1] at hi
        rw [List.getD_append _ _ _ _ (hl ▸ h1)]
        exact hm i hi
      · subst h1
        rw [List.getD_append_right _ _ _ _ le_rfl] at hi
        rw [hl, List.getD_append_right _ _ _ _ le_rfl] at *
        simp at hi ⊢
        exact hab hi
      · rw [List.getD_eq_default] at hi
        · simp at hi
        · simp; omega

theorem base {n : ℕ} (x y : Fin n → Bool) (hxy : ∀ j, x j = true → y j = true) :
    ∀ i, (List.ofFn x).getD i false = true → (List.ofFn y).getD i false = true := by
  intro i hi
  by_cases h : i < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h, Option.getD] at hi ⊢
    simp_all
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    simp at hi

end PEqualNP.Outside.L_meta_7676_aux

open PEqualNP.Outside.L_meta_7676_aux in
theorem PEqualNP.Outside.L_meta_7676 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (21 : ℕ) x1 → ∀ (x3 x4 : Fin (21 : ℕ) → Bool), (∀ (x5 : Fin (21 : ℕ)), x3 x5 = Bool.true → x4 x5 = Bool.true) → ∀ (x6 : ℕ), (x1.wires (List.ofFn x3)).getD x6 Bool.false = Bool.true → (x1.wires (List.ofFn x4)).getD x6 Bool.false = Bool.true := by
  intro C hC x y hxy k hk
  refine (step C.gates hC.1 (List.ofFn x) (List.ofFn y) (by simp) (base x y hxy)).2 k hk
