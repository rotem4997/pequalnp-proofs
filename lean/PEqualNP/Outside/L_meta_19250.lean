import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19250 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7577150 : ℕ).testBit (5 * u.val + v.val)) C := by
  refine ⟨({ gates := [{ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [0, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [9, 5] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [1, 11] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [12, 0] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [8, 9] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [13] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [14, 1] }, { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [16, 15] }, { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [10, 17] }, { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [18] }], output := 19 } : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
