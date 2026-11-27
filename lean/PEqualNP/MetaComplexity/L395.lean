import PEqualNP.MetaComplexity.Helpers.CoverCircB

/-- With every owner list nonempty, the root cover circuit has (sum of list lengths) + (owners) - 1 gates. -/
theorem PEqualNP.MetaComplexity.L395 : ∀ (n : ℕ) (own : List (ℕ × List ℕ)), own ≠ [] → (∀ p ∈ own, p.2 ≠ []) → (PEqualNP.MetaComplexity.coverCircuitB n own).size + 1 = (own.map (fun p : ℕ × List ℕ => p.2.length)).sum + own.length :=
  fun n own hne h => PEqualNP.MetaComplexity.Helpers.CoverCircB.circuit_size n own hne h
