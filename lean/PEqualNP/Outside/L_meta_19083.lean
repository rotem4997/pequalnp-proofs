import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19083

open PEqualNP.CircuitLowerBounds

/-- Six gates on wires `0..3` (left vertices) and `4..7` (right vertices):
`g8 = x2 ∨ y1`, `g9 = ¬g8`, `g10 = x1 ∨ g9`, `g11 = x0 ∨ g8`, `g12 = y0 ∨ g10`,
output `g13 = g11 ∧ g12`. Found by SAT search; no circuit with at most five gates exists. -/
def circ : Circuit :=
  ⟨[⟨GateOp.or, [2, 5]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.or, [0, 8]⟩,
    ⟨GateOp.or, [4, 10]⟩, ⟨GateOp.and, [11, 12]⟩], 13⟩

theorem fanin : PEqualNP.MetaComplexity.FanInTwo circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem represents :
    PEqualNP.Represents.Represents (fun u v : Fin 4 => (301 : ℕ).testBit (4 * u.val + v.val)) circ := by
  decide

end PEqualNP.Outside.L_meta_19083

theorem PEqualNP.Outside.L_meta_19083 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (301 : ℕ).testBit (4 * u.val + v.val)) C :=
  ⟨PEqualNP.Outside.L_meta_19083.circ, PEqualNP.Outside.L_meta_19083.fanin, by decide,
    PEqualNP.Outside.L_meta_19083.represents⟩
