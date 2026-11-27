import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18534
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [3, 8]⟩,
        ⟨GateOp.or, [4, 9]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.and, [11, 15]⟩, ⟨GateOp.or, [12, 14]⟩,
        ⟨GateOp.and, [13, 17]⟩, ⟨GateOp.and, [14, 10]⟩, ⟨GateOp.or, [16, 18]⟩, ⟨GateOp.or, [20, 19]⟩ ],
    output := 21 }

end PEqualNP.Outside.L_meta_18534

theorem PEqualNP.Outside.L_meta_18534 :
    (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => decide (v.val = (u.val + 1) % 5 ∨ u.val = (v.val + 1) % 5)) 12) := by
  refine ⟨PEqualNP.Outside.L_meta_18534.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_18534.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
