import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19388

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [4, 9]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [13, 2]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.and, [10, 15]⟩, ⟨GateOp.or, [3, 11]⟩, ⟨GateOp.and, [12, 17]⟩, ⟨GateOp.or, [11, 2]⟩, ⟨GateOp.and, [7, 19]⟩, ⟨GateOp.or, [16, 18]⟩, ⟨GateOp.or, [21, 20]⟩], 22⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3675834 : ℕ).testBit (5 * u.val + v.val)) 14 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_19388

theorem PEqualNP.Outside.L_meta_19388 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3675834 : ℕ).testBit (5 * u.val + v.val)) 14 :=
  PEqualNP.Outside.L_meta_19388.main_aux
