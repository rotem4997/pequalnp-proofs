import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19050
open PEqualNP.CircuitLowerBounds

def C : Circuit :=
  { gates :=
      [ ⟨GateOp.or, [0, 4]⟩,
        ⟨GateOp.or, [2, 6]⟩,
        ⟨GateOp.not, [9]⟩,
        ⟨GateOp.and, [8, 10]⟩,
        ⟨GateOp.and, [1, 6]⟩,
        ⟨GateOp.and, [2, 5]⟩,
        ⟨GateOp.or, [12, 13]⟩,
        ⟨GateOp.or, [11, 14]⟩ ],
    output := 15 }

end PEqualNP.Outside.L_meta_19050

theorem PEqualNP.Outside.L_meta_19050 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4699 : ℕ).testBit (4 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19050.C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19050.C, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with h | h | h | h | h | h | h | h <;> subst h <;> simp
  · unfold PEqualNP.Represents.Represents
    decide +kernel
