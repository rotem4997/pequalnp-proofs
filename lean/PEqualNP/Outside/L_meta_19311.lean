import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19311_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.and, [7, 10]⟩,
    ⟨GateOp.or, [11, 0]⟩,
    ⟨GateOp.and, [10, 8]⟩,
    ⟨GateOp.or, [9, 7]⟩,
    ⟨GateOp.or, [12, 13]⟩,
    ⟨GateOp.or, [14, 15]⟩,
    ⟨GateOp.not, [16]⟩,
    ⟨GateOp.and, [14, 15]⟩,
    ⟨GateOp.or, [17, 18]⟩
    ]
    output := 19 }

theorem C_ok : FanInTwo C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 10 := by decide +kernel

set_option maxRecDepth 20000 in
theorem C_rep : Represents (fun u v : Fin 5 => (7581044 : ℕ).testBit (5 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_19311_aux

theorem PEqualNP.Outside.L_meta_19311 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7581044 : ℕ).testBit (5 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19311_aux.C, PEqualNP.Outside.L_meta_19311_aux.C_ok, PEqualNP.Outside.L_meta_19311_aux.C_size, PEqualNP.Outside.L_meta_19311_aux.C_rep⟩
