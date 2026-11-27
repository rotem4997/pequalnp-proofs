import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3467_aux

open PEqualNP.CircuitLowerBounds

theorem foldl_prefix (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ t, ?_⟩
    rw [List.foldl_cons, ht, List.append_assoc]

theorem eval_input (C : Circuit) (xs : List Bool) (h : C.output < xs.length) :
    C.eval xs = xs.getD C.output false := by
  obtain ⟨t, ht⟩ := foldl_prefix C.gates xs
  unfold Circuit.eval Circuit.wires
  rw [ht, List.getD_append _ _ _ _ h]

end PEqualNP.Outside.L_meta_3467_aux

theorem PEqualNP.Outside.L_meta_3467 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro x1 x2 x3 x4 h1 h2 h3 h4 h5 ho h6 hf
  clear h2 h3 h4 h5 h6
  exfalso
  by_cases hc : x4.output < x2
  · have e := hf {⟨x4.output, hc⟩} ∅ (by simp) (by simp [PEqualNP.GenericRejection.IsFalseInput])
    rw [PEqualNP.Outside.L_meta_3467_aux.eval_input _ _ (by simp [PEqualNP.GenericRejection.incidenceInput]; omega)] at e
    unfold PEqualNP.GenericRejection.incidenceInput at e
    rw [List.getD_append _ _ _ _ (by simpa using hc)] at e
    simp [hc] at e
  · have e := hf ∅ {⟨x4.output - x2, by omega⟩} (by simp; omega) (by simp [PEqualNP.GenericRejection.IsFalseInput])
    rw [PEqualNP.Outside.L_meta_3467_aux.eval_input _ _ (by simp [PEqualNP.GenericRejection.incidenceInput]; omega)] at e
    unfold PEqualNP.GenericRejection.incidenceInput at e
    rw [List.getD_append_right _ _ _ _ (by simpa using (show x2 ≤ x4.output by omega))] at e
    have hl : x4.output - x2 < x2 := by omega
    simp [hl] at e
