import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9097

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- A 13 gate AND/OR circuit for the 10-cycle u-u, u-(u+1) on 5 + 5 vertices.
def circ : Circuit :=
  ⟨[⟨GateOp.or, [1, 9]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.or, [7, 4]⟩, ⟨GateOp.or, [5, 2]⟩,
    ⟨GateOp.or, [12, 11]⟩, ⟨GateOp.or, [2, 13]⟩, ⟨GateOp.and, [14, 10]⟩,
    ⟨GateOp.or, [13, 11]⟩, ⟨GateOp.and, [12, 15]⟩, ⟨GateOp.or, [0, 8]⟩,
    ⟨GateOp.and, [19, 17]⟩, ⟨GateOp.or, [20, 18]⟩, ⟨GateOp.or, [16, 21]⟩], 22⟩

theorem circ_mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem circ_rep :
    Represents (fun u v : Fin 5 => (18624707 : ℕ).testBit (5 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_9097

theorem PEqualNP.Outside.L_meta_9097 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (18624707 : ℕ).testBit (5 * u.val + v.val)) 13 := by
  exact ⟨PEqualNP.Outside.L_meta_9097.circ, PEqualNP.Outside.L_meta_9097.circ_mono, by decide,
    PEqualNP.Outside.L_meta_9097.circ_rep⟩
