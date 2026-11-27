import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19089_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.not, [0]⟩,
    ⟨GateOp.and, [6, 1]⟩,
    ⟨GateOp.and, [7, 8]⟩,
    ⟨GateOp.or, [3, 10]⟩,
    ⟨GateOp.or, [6, 11]⟩,
    ⟨GateOp.not, [12]⟩,
    ⟨GateOp.or, [13, 9]⟩
    ]
    output := 14 }

theorem C_fanInTwo : FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 7 := by decide

theorem C_rep : Represents (fun u v : Fin 4 => (891 : ℕ).testBit (4 * u.val + v.val)) C := by
  intro u v
  revert u v
  decide

end PEqualNP.Outside.L_meta_19089_aux

theorem PEqualNP.Outside.L_meta_19089 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (891 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19089_aux.C, PEqualNP.Outside.L_meta_19089_aux.C_fanInTwo, PEqualNP.Outside.L_meta_19089_aux.C_size, PEqualNP.Outside.L_meta_19089_aux.C_rep⟩
