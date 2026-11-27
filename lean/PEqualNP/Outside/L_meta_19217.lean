import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19217_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.or, [4, 0]⟩,
    ⟨GateOp.not, [4]⟩,
    ⟨GateOp.or, [8, 1]⟩,
    ⟨GateOp.not, [1]⟩,
    ⟨GateOp.or, [9, 11]⟩,
    ⟨GateOp.and, [12, 10]⟩
    ]
    output := 13 }

theorem C_fanInTwo : FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 6 := by decide

set_option maxHeartbeats 800000 in
theorem C_rep : Represents (fun u v : Fin 4 => (4591 : ℕ).testBit (4 * u.val + v.val)) C := by
  intro u v
  revert u v
  decide

end PEqualNP.Outside.L_meta_19217_aux

theorem PEqualNP.Outside.L_meta_19217 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4591 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19217_aux.C, PEqualNP.Outside.L_meta_19217_aux.C_fanInTwo, PEqualNP.Outside.L_meta_19217_aux.C_size, PEqualNP.Outside.L_meta_19217_aux.C_rep⟩
