import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19180_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.and, [4, 8]⟩,
    ⟨GateOp.and, [2, 5]⟩,
    ⟨GateOp.or, [4, 10]⟩,
    ⟨GateOp.or, [8, 11]⟩,
    ⟨GateOp.or, [12, 8]⟩,
    ⟨GateOp.not, [9]⟩,
    ⟨GateOp.and, [13, 14]⟩
    ]
    output := 15 }

theorem C_fanInTwo : FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 8 := by decide

set_option maxHeartbeats 800000 in
theorem C_rep : Represents (fun u v : Fin 4 => (5102 : ℕ).testBit (4 * u.val + v.val)) C := by
  intro u v
  revert u v
  decide

end PEqualNP.Outside.L_meta_19180_aux

theorem PEqualNP.Outside.L_meta_19180 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (5102 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19180_aux.C, PEqualNP.Outside.L_meta_19180_aux.C_fanInTwo, PEqualNP.Outside.L_meta_19180_aux.C_size, PEqualNP.Outside.L_meta_19180_aux.C_rep⟩
