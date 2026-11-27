import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9278

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [0, 7]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [2, 11]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.or, [4, 9]⟩, ⟨GateOp.or, [5, 8]⟩, ⟨GateOp.or, [13, 17]⟩, ⟨GateOp.and, [12, 18]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.and, [16, 20]⟩, ⟨GateOp.or, [15, 17]⟩, ⟨GateOp.and, [14, 22]⟩, ⟨GateOp.or, [19, 21]⟩, ⟨GateOp.or, [24, 23]⟩], 25⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => (36803003013 : ℕ).testBit (6 * u.val + v.val)) 16 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_9278

theorem PEqualNP.Outside.L_meta_9278 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => (36803003013 : ℕ).testBit (6 * u.val + v.val)) 16 :=
  PEqualNP.Outside.L_meta_9278.main_aux
