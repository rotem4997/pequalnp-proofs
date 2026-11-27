import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_2569 : ∀ (x1 x2 : ℕ) (x3 x4 : Fin x1) (x5 : PEqualNP.CircuitLowerBounds.GateOp) (x6 : PEqualNP.CircuitLowerBounds.Circuit), x5 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x5 = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.MetaComplexity.Monotone2 x6 → x6.size ≤ x2 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x10 ∧ x10.size ≤ x2 + (1 : ℕ) ∧ ∀ (x11 : Fin x1 → Bool), x10.eval (List.ofFn x11) = x6.eval (List.ofFn x11 ++ [x5.eval [x11 x3, x11 x4]]) := by
  intro n s a b op C hop hC hs
  refine ⟨⟨⟨op, [a.val, b.val]⟩ :: C.gates, C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_cons.mp hg with h | h
    · subst h
      constructor
      · rcases hop with h | h <;> simp [h]
      · simp
    · exact hC g h
  · simp [Circuit.size] at hs ⊢
    omega
  · intro x
    simp only [Circuit.eval, Circuit.wires, List.foldl_cons]
    congr 3
    have ha : (List.ofFn x).getD a.val false = x a := by simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp
    have hb : (List.ofFn x).getD b.val false = x b := by simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp
    simp only [List.map_cons, List.map_nil, ha, hb]
