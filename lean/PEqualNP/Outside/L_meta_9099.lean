import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9099

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨GateOp.or, [2,6]⟩, ⟨GateOp.or, [0,9]⟩, ⟨GateOp.or, [4,7]⟩, ⟨GateOp.or, [5,10]⟩, ⟨GateOp.or, [8,9]⟩, ⟨GateOp.or, [5,14]⟩, ⟨GateOp.and, [3,15]⟩, ⟨GateOp.or, [8,12]⟩, ⟨GateOp.or, [12,13]⟩, ⟨GateOp.or, [10,17]⟩, ⟨GateOp.and, [1,19]⟩, ⟨GateOp.and, [13,17]⟩, ⟨GateOp.or, [11,21]⟩, ⟨GateOp.and, [18,22]⟩, ⟨GateOp.or, [20,23]⟩, ⟨GateOp.or, [16,24]⟩], 25⟩

theorem mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun u v : Fin 5 => (20771271 : ℕ).testBit (5 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_9099

theorem PEqualNP.Outside.L_meta_9099 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (20771271 : ℕ).testBit (5 * u.val + v.val)) 16 :=
  ⟨PEqualNP.Outside.L_meta_9099.circ, PEqualNP.Outside.L_meta_9099.mono, by decide, PEqualNP.Outside.L_meta_9099.rep⟩
