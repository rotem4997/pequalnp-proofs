import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19483 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (3257437 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [1, 6] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [2, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [6, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [12, 14] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [16] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [15, 17] }], output := 18 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
