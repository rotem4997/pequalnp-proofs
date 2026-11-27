import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19490 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧
      PEqualNP.Represents.Represents
        (fun u v : Fin 5 => (3585117 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨⟨[⟨.or, [1, 4]⟩,
      ⟨.or, [0, 6]⟩,
      ⟨.or, [9, 10]⟩,
      ⟨.and, [11, 12]⟩,
      ⟨.or, [6, 12]⟩,
      ⟨.not, [14]⟩,
      ⟨.or, [5, 15]⟩,
      ⟨.or, [4, 15]⟩,
      ⟨.and, [16, 17]⟩,
      ⟨.or, [13, 18]⟩], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
