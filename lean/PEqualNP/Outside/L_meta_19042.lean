import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19042

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def C : Circuit := ⟨[⟨GateOp.or, [6, 2]⟩, ⟨GateOp.or, [0, 4]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [8, 9]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [14, 11]⟩, ⟨GateOp.not, [15]⟩], 16⟩

theorem gatesOK : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem sizeOK : C.size ≤ 9 := by decide

set_option maxRecDepth 20000 in
theorem repOK : PEqualNP.Represents.Represents (fun u v : Fin 4 => (5755 : ℕ).testBit (4 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_19042

theorem PEqualNP.Outside.L_meta_19042 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (5755 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19042.C, PEqualNP.Outside.L_meta_19042.gatesOK, PEqualNP.Outside.L_meta_19042.sizeOK, PEqualNP.Outside.L_meta_19042.repOK⟩
