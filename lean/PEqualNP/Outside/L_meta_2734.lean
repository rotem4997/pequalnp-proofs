import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_2734 : ∀ (x1 x2 : ℕ) (x3 x4 : Fin x1) (x5 x6 : Fin (x1 + (1 : ℕ))) (x7 x8 : PEqualNP.CircuitLowerBounds.GateOp),   x7 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x7 = PEqualNP.CircuitLowerBounds.GateOp.or →     x8 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x8 = PEqualNP.CircuitLowerBounds.GateOp.or →       ∀ (x11 : PEqualNP.CircuitLowerBounds.Circuit),         PEqualNP.MetaComplexity.Monotone2 x11 →           x11.size ≤ x2 →             ∃ (x14 : PEqualNP.CircuitLowerBounds.Circuit),               PEqualNP.MetaComplexity.Monotone2 x14 ∧                 x14.size ≤ x2 + (2 : ℕ) ∧                   ∀ (x15 : Fin x1 → Bool),                     have x16 : List Bool := List.ofFn x15 ++ [x7.eval [x15 x3, x15 x4]];                     x14.eval (List.ofFn x15) = x11.eval (x16 ++ [x8.eval [x16.getD (↑x5) Bool.false, x16.getD (↑x6) Bool.false]]) := by
  intro n s a b c d op1 op2 hop1 hop2 C hC hs
  refine ⟨⟨⟨op1, [a.val, b.val]⟩ :: ⟨op2, [c.val, d.val]⟩ :: C.gates, C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_cons.mp hg with h | h
    · subst h
      constructor
      · rcases hop1 with h | h <;> simp [h]
      · simp
    · rcases List.mem_cons.mp h with h | h
      · subst h
        constructor
        · rcases hop2 with h | h <;> simp [h]
        · simp
      · exact hC g h
  · simp [Circuit.size] at hs ⊢
    omega
  · intro x
    simp only [Circuit.eval, Circuit.wires, List.foldl_cons]
    have ha : (List.ofFn x).getD a.val false = x a := by simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp
    have hb : (List.ofFn x).getD b.val false = x b := by simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp
    simp only [List.map_cons, List.map_nil, ha, hb]
