import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8520

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8520

theorem PEqualNP.Outside.L_meta_8520 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∀ (x3 : Bool) (x4 x5 : ℕ), ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size ≤ x1.size + (1 : ℕ) ∧ ∀ (x7 : List Bool), x6.eval x7 = x1.eval (x7 ++ [if x4 = (56 : ℕ) then x3 else if x3 = Bool.true then x7.getD x4 Bool.false && x7.getD x5 Bool.false else x7.getD x4 Bool.false || x7.getD x5 Bool.false]) := by
  intro C hC b p q
  by_cases hp : p = 56
  · refine ⟨⟨⟨if b = true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ :: C.gates, C.output⟩, ?_, by simp [PEqualNP.CircuitLowerBounds.Circuit.size], fun x => ?_⟩
    · intro g hg
      rcases List.mem_cons.1 hg with rfl | h
      · cases b <;> exact ⟨by simp, by simp⟩
      · exact hC g h
    · simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons, if_pos hp]
      cases b <;> simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  · refine ⟨⟨⟨if b = true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or, [p, q]⟩ :: C.gates, C.output⟩, ?_, by simp [PEqualNP.CircuitLowerBounds.Circuit.size], fun x => ?_⟩
    · intro g hg
      rcases List.mem_cons.1 hg with rfl | h
      · cases b <;> exact ⟨by simp, by simp⟩
      · exact hC g h
    · simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons, if_neg hp]
      cases b <;> simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
