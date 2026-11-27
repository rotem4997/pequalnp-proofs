import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19230

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨GateOp.not, [3]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.and, [8, 10]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [11, 12]⟩], 13⟩

theorem main_proof :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (7919 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro u v
    fin_cases u <;> fin_cases v <;> decide

end PEqualNP.Outside.L_meta_19230

theorem PEqualNP.Outside.L_meta_19230 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (7919 : ℕ).testBit (4 * u.val + v.val)) C
    := PEqualNP.Outside.L_meta_19230.main_proof
