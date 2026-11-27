import PEqualNP.MetaComplexity.Helpers.LocalHardPatch

/-- Changing few entries of a partial table changes its partial circuit size by little. -/
theorem PEqualNP.MetaComplexity.L053 : ∀ (n' k s : ℕ) (T T' : List (Option Bool)), (Finset.univ.filter fun x : Fin n' → Bool => T.getD (PEqualNP.MetaComplexity.tableIndex x) none ≠ T'.getD (PEqualNP.MetaComplexity.tableIndex x) none).card ≤ k → (∃ f : (Fin n' → Bool) → Bool, PEqualNP.MetaComplexity.Consistent n' T' f ∧ PEqualNP.MetaComplexity.HasCircuitSize n' f s) → ∃ g : (Fin n' → Bool) → Bool, PEqualNP.MetaComplexity.Consistent n' T g ∧ PEqualNP.MetaComplexity.HasCircuitSize n' g (s + (2 * n' + 2) * k) :=
  PEqualNP.MetaComplexity.Helpers.LocalHardPatch.lipschitz
