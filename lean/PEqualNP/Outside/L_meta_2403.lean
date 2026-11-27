import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2403_aux

open PEqualNP.CircuitLowerBounds

theorem ofFn_last (x : Fin 26 → Bool) (v : Bool) :
    List.ofFn (fun (y : Fin (26 + 1)) => Fin.lastCases v x y) = List.ofFn x ++ [v] := by
  rw [List.ofFn_succ']
  simp only [Fin.lastCases_castSucc, List.concat_eq_append]
  congr 2

end PEqualNP.Outside.L_meta_2403_aux

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_2403 : ∀ (x1 : Fin (26 : ℕ)) (x2 : Bool) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x3 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x6 ∧ x6.size ≤ x3.size + (1 : ℕ) ∧ ∀ (x7 : Fin (26 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x6 x7 = PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x3 fun (x8 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (if x2 = Bool.true then x7 (0 : Fin (26 : ℕ)) && x7 x1 else x7 (0 : Fin (26 : ℕ)) || x7 x1) x7 x8 := by
  intro i b C hC _
  refine ⟨⟨⟨if b = true then GateOp.and else GateOp.or, [0, i.val]⟩ :: C.gates, C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_cons.mp hg with h | h
    · subst h
      constructor
      · cases b <;> simp
      · simp
    · exact hC g h
  · simp [Circuit.size]
  · intro x
    simp only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval, Circuit.wires, List.foldl_cons]
    rw [PEqualNP.Outside.L_meta_2403_aux.ofFn_last]
    congr 3
    have h0 : (List.ofFn x).getD 0 false = x 0 := by simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp
    have hi : (List.ofFn x).getD i.val false = x i := by simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp
    cases b <;> simp only [GateOp.eval, List.map_cons, List.map_nil, h0, hi] <;> simp
