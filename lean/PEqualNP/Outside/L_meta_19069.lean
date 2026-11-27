import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19069 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (382 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨⟨[⟨.not, [7]⟩, ⟨.or, [0, 4]⟩, ⟨.not, [4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [2, 10]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
  · decide +kernel
