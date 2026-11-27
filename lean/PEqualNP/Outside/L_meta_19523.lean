import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19523 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (12060214 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨⟨[
    ⟨.or, [5, 4]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.or, [12, 11]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [2, 14]⟩,
    ⟨.and, [13, 15]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.not, [16]⟩,
    ⟨.and, [18, 17]⟩
  ], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
