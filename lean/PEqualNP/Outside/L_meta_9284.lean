import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9284

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 10]⟩, ⟨GateOp.or, [1, 11]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.or, [5, 9]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.or, [18, 14]⟩, ⟨GateOp.and, [12, 19]⟩, ⟨GateOp.or, [18, 17]⟩, ⟨GateOp.and, [13, 21]⟩, ⟨GateOp.or, [16, 17]⟩, ⟨GateOp.and, [14, 23]⟩, ⟨GateOp.and, [15, 17]⟩, ⟨GateOp.or, [20, 22]⟩, ⟨GateOp.or, [24, 25]⟩, ⟨GateOp.or, [26, 27]⟩], 28⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => (38417843079 : ℕ).testBit (6 * u.val + v.val)) 20 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_9284

theorem PEqualNP.Outside.L_meta_9284 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => (38417843079 : ℕ).testBit (6 * u.val + v.val)) 20 :=
  PEqualNP.Outside.L_meta_9284.main_aux
