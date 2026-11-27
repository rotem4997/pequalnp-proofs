import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7842_aux

open PEqualNP.CircuitLowerBounds

theorem fold_prefix (gs : List Gate) (w : List Bool) :
    ∃ t, gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, by rw [List.foldl_cons, ht]; simp⟩

end PEqualNP.Outside.L_meta_7842_aux

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7842 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (16 : ℕ) + x1.size → (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (16 : ℕ) + x3 ∧ x7 < (16 : ℕ) + x3) → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x4.size ≤ x1.size + (2 : ℕ) ∧ x4.output < (14 : ℕ) + x4.size ∧ (15 : ℕ) < (14 : ℕ) + x4.size ∧ (∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x5]? = Option.some x6 → (x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x8 : ℕ) (x9 : ℕ), x6.inputs = [x8, x9] ∧ x8 ≠ x9 ∧ x8 < (14 : ℕ) + x5 ∧ x9 < (14 : ℕ) + x5) ∧ ∀ (x5 : Fin (14 : ℕ) → Bool), x4.eval (List.ofFn x5) = x1.eval (List.ofFn x5 ++ [x5 (7 : Fin (14 : ℕ)) || x5 (13 : Fin (14 : ℕ)), x5 (7 : Fin (14 : ℕ)) || x5 (13 : Fin (14 : ℕ)) || x5 (11 : Fin (14 : ℕ))]) ∧ (x4.wires (List.ofFn x5)).getD (15 : ℕ) Bool.false = (x5 (7 : Fin (14 : ℕ)) || x5 (13 : Fin (14 : ℕ)) || x5 (11 : Fin (14 : ℕ))) := by
  intro x1 hout hg
  have hw : ∀ x5 : Fin 14 → Bool, (Circuit.mk (⟨GateOp.or, [7, 13]⟩ :: ⟨GateOp.or, [14, 11]⟩ :: x1.gates) x1.output).wires (List.ofFn x5) = x1.wires (List.ofFn x5 ++ [x5 7 || x5 13, x5 7 || x5 13 || x5 11]) := by
    intro x5
    simp only [Circuit.wires, List.foldl_cons]
    congr 1
    simp [GateOp.eval, List.getD_eq_getElem?_getD, Bool.or_assoc]
  refine ⟨Circuit.mk (⟨GateOp.or, [7, 13]⟩ :: ⟨GateOp.or, [14, 11]⟩ :: x1.gates) x1.output, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Circuit.size]
  · simp [Circuit.size] at hout ⊢; omega
  · simp [Circuit.size]; omega
  · intro x5 x6 h
    match x5, h with
    | 0, h =>
      simp at h; subst h
      exact ⟨Or.inr rfl, 7, 13, rfl, by decide, by omega, by omega⟩
    | 1, h =>
      simp at h; subst h
      exact ⟨Or.inr rfl, 14, 11, rfl, by decide, by omega, by omega⟩
    | j + 2, h =>
      simp at h
      obtain ⟨h1, a, b, h2, h3, h4, h5⟩ := hg j x6 h
      exact ⟨h1, a, b, h2, h3, by omega, by omega⟩
  · intro x5
    refine ⟨?_, ?_⟩
    · simp only [Circuit.eval]
      rw [hw]
    · rw [hw]
      obtain ⟨t, ht⟩ := PEqualNP.Outside.L_meta_7842_aux.fold_prefix x1.gates (List.ofFn x5 ++ [x5 7 || x5 13, x5 7 || x5 13 || x5 11])
      simp only [Circuit.wires]
      rw [ht]
      simp [List.getD_eq_getElem?_getD]
