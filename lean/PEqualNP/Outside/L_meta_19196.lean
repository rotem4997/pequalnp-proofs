import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19196

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 11]⟩, ⟨GateOp.or, [0, 9]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.and, [13, 14]⟩,
    ⟨GateOp.or, [3, 7]⟩, ⟨GateOp.or, [1, 13]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [5, 8]⟩,
    ⟨GateOp.and, [18, 19]⟩, ⟨GateOp.or, [10, 17]⟩, ⟨GateOp.and, [16, 21]⟩, ⟨GateOp.or, [10, 11]⟩,
    ⟨GateOp.and, [4, 23]⟩, ⟨GateOp.or, [22, 24]⟩, ⟨GateOp.or, [15, 20]⟩, ⟨GateOp.or, [25, 26]⟩], 27⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => decide (v.val = u.val ∨ v.val = (u.val + 1) % 6)) 16 :=
  ⟨wit, wit_mono, by decide, by decide⟩

end PEqualNP.Outside.L_meta_19196

theorem PEqualNP.Outside.L_meta_19196 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 6 => decide (v.val = u.val ∨ v.val = (u.val + 1) % 6)) 16 :=
  PEqualNP.Outside.L_meta_19196.main_aux
