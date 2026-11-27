import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_9289 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => (42746759055 : ℕ).testBit (6 * u.val + v.val)) 22 := by
  refine ⟨⟨[⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [7, 3]⟩, ⟨GateOp.or, [9, 4]⟩, ⟨GateOp.or, [14, 2]⟩, ⟨GateOp.or, [2, 12]⟩, ⟨GateOp.or, [13, 16]⟩, ⟨GateOp.or, [11, 0]⟩, ⟨GateOp.or, [10, 0]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.or, [5, 19]⟩, ⟨GateOp.or, [5, 15]⟩, ⟨GateOp.or, [16, 21]⟩, ⟨GateOp.or, [13, 22]⟩, ⟨GateOp.and, [18, 24]⟩, ⟨GateOp.and, [23, 20]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [27, 26]⟩, ⟨GateOp.or, [21, 14]⟩, ⟨GateOp.and, [17, 29]⟩, ⟨GateOp.and, [13, 28]⟩, ⟨GateOp.or, [30, 25]⟩, ⟨GateOp.or, [32, 28]⟩], 33⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
