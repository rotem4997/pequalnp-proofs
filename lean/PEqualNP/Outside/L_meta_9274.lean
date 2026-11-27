import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9274

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.or, [12, 10]⟩, ⟨GateOp.or, [16, 1]⟩, ⟨GateOp.and, [14, 17]⟩, ⟨GateOp.or, [13, 1]⟩, ⟨GateOp.or, [19, 11]⟩, ⟨GateOp.and, [15, 20]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.and, [4, 22]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [18, 21]⟩, ⟨GateOp.or, [25, 23]⟩, ⟨GateOp.or, [26, 24]⟩], 27⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => (36245127555 : ℕ).testBit (6 * u.val + v.val)) 16 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_9274

theorem PEqualNP.Outside.L_meta_9274 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => (36245127555 : ℕ).testBit (6 * u.val + v.val)) 16 :=
  PEqualNP.Outside.L_meta_9274.main_aux
