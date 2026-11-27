import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19248

open PEqualNP.CircuitLowerBounds

def circ : Circuit :=
  ⟨[⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [1, 10]⟩, ⟨GateOp.or, [2, 11]⟩, ⟨GateOp.or, [0, 7]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.not, [14]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.and, [15, 16]⟩], 17⟩

theorem fanin : PEqualNP.MetaComplexity.FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : PEqualNP.Represents.Represents (fun u v : Fin 5 => (7573372 : ℕ).testBit (5 * u.val + v.val)) circ := by
  decide

end PEqualNP.Outside.L_meta_19248

theorem PEqualNP.Outside.L_meta_19248 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7573372 : ℕ).testBit (5 * u.val + v.val)) C) :=
  ⟨PEqualNP.Outside.L_meta_19248.circ, PEqualNP.Outside.L_meta_19248.fanin, by decide, PEqualNP.Outside.L_meta_19248.rep⟩
