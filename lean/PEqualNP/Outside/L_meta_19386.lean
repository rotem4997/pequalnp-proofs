import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19386

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.or, [4, 9]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.or, [15, 10]⟩, ⟨GateOp.and, [11, 16]⟩, ⟨GateOp.or, [12, 10]⟩, ⟨GateOp.and, [13, 18]⟩, ⟨GateOp.and, [10, 14]⟩, ⟨GateOp.or, [17, 19]⟩, ⟨GateOp.or, [21, 20]⟩], 22⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3320506 : ℕ).testBit (5 * u.val + v.val)) 15 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_19386

theorem PEqualNP.Outside.L_meta_19386 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (3320506 : ℕ).testBit (5 * u.val + v.val)) 15 :=
  PEqualNP.Outside.L_meta_19386.main_aux
