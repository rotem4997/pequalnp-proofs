import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9071
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

end PEqualNP.Outside.L_meta_9071

open PEqualNP.Outside.L_meta_9071 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_9071 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (26 : ℕ) → PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x4 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), (x5 = x6 ∨ x5 = x6 + (1 : Fin (13 : ℕ)) ∨ x5 = x6 + (3 : Fin (13 : ℕ)) ∨ x5 = x6 + (9 : Fin (13 : ℕ))) ∧ x5 ≠ (0 : Fin (13 : ℕ)) ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) → (59 : ℕ) ≤ x1.size := by
  intro C ho _ hf
  exfalso
  have hval : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = x ⟨C.output, ho⟩ := by
    intro x
    show (wf C.gates (List.ofFn x)).getD C.output false = _
    rw [wf_keep _ _ _ (by simpa using ho)]
    exact getD_ofFn x ⟨C.output, ho⟩
  have h1 := (hf (fun i => decide (i = (⟨C.output, ho⟩ : Fin 26)))).1 (by rw [hval]; simp)
  obtain ⟨p, l, _, _, hp, hl⟩ := h1
  have e1 : Fin.castAdd 13 p = (⟨C.output, ho⟩ : Fin 26) := by simpa using hp
  have e2 : Fin.natAdd 13 l = (⟨C.output, ho⟩ : Fin 26) := by simpa using hl
  have e3 := e1.trans e2.symm
  have e4 := congrArg Fin.val e3
  simp at e4
  omega
