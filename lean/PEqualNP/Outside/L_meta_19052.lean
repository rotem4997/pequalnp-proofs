import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19052

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [2, 5]⟩, ⟨.not, [8]⟩, ⟨.and, [2, 5]⟩,
    ⟨.or, [0, 4]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [11, 12]⟩,
    ⟨.and, [9, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩

theorem legal : FanInTwo witness := by simp [FanInTwo, witness]

theorem represents : PEqualNP.Represents.Represents
    (fun u v : Fin 4 => (4701 : Nat).testBit (4 * u.val + v.val)) witness := by
  unfold PEqualNP.Represents.Represents
  decide +kernel

end PEqualNP.Outside.L_meta_19052

theorem PEqualNP.Outside.L_meta_19052 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (4701 : ℕ).testBit (4 * u.val + v.val)) C) := by
  exact ⟨PEqualNP.Outside.L_meta_19052.witness, PEqualNP.Outside.L_meta_19052.legal,
    by decide, PEqualNP.Outside.L_meta_19052.represents⟩
