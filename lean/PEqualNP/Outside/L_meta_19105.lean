import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19105

open PEqualNP.CircuitLowerBounds

/-- A 8-gate AND/OR/NOT circuit (wires `0..3` left, `4..7` right), found by SAT search. -/
def circ : Circuit := ⟨[⟨GateOp.or, [5, 7]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.and, [2, 8]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.and, [9, 12]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.not, [14]⟩], 15⟩

theorem fanin : PEqualNP.MetaComplexity.FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem represents : PEqualNP.Represents.Represents (fun u v : Fin 4 => (13807 : ℕ).testBit (4 * u.val + v.val)) circ := by
  decide

end PEqualNP.Outside.L_meta_19105

theorem PEqualNP.Outside.L_meta_19105 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (13807 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19105.circ, PEqualNP.Outside.L_meta_19105.fanin, by decide, PEqualNP.Outside.L_meta_19105.represents⟩
