import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9293

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.or, [13, 10]⟩, ⟨GateOp.or, [3, 16]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [15, 17]⟩, ⟨GateOp.or, [12, 19]⟩, ⟨GateOp.and, [13, 15]⟩, ⟨GateOp.and, [4, 11]⟩, ⟨GateOp.or, [4, 11]⟩, ⟨GateOp.or, [12, 23]⟩, ⟨GateOp.and, [10, 18]⟩, ⟨GateOp.and, [19, 24]⟩, ⟨GateOp.or, [14, 26]⟩, ⟨GateOp.and, [20, 27]⟩, ⟨GateOp.or, [22, 28]⟩, ⟨GateOp.or, [25, 29]⟩, ⟨GateOp.or, [21, 30]⟩], 31⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => (47075416983 : ℕ).testBit (6 * u.val + v.val)) 20 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_9293

theorem PEqualNP.Outside.L_meta_9293 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => (47075416983 : ℕ).testBit (6 * u.val + v.val)) 20 :=
  PEqualNP.Outside.L_meta_9293.main_aux
