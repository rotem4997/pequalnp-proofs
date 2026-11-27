import PEqualNP.CircuitLowerBounds.Helpers.ShannonBound
import PEqualNP.MetaComplexity.L019

/-- Every language has circuits of size `(n + 2) * 2 ^ n`: at each length, the Shannon
expansion of its slice, one variable at a time. -/
theorem PEqualNP.CircuitLowerBounds.L004 : ∀ L : Language Bool,
    L ∈ PEqualNP.CircuitLowerBounds.SIZE (fun n => (n + 2) * 2 ^ n) := by
  intro L
  rw [PEqualNP.MetaComplexity.L019]
  intro n
  classical
  refine ⟨fun x => decide (List.ofFn x ∈ L), ?_, ?_⟩
  · simp
  · exact PEqualNP.CircuitLowerBounds.Helpers.hasCircuitSize_all n _
