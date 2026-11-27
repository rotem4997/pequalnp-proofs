import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9282

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [7, 10]⟩, ⟨GateOp.and, [15, 16]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.and, [18, 19]⟩, ⟨GateOp.or, [14, 17]⟩, ⟨GateOp.or, [21, 20]⟩], 22⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => (38959203465 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_9282

theorem PEqualNP.Outside.L_meta_9282 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => (38959203465 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  PEqualNP.Outside.L_meta_9282.main_aux
