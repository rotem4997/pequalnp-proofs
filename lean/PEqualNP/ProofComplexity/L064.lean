import PEqualNP.ProofComplexity.Helpers.LinKSplit

namespace PEqualNP.ProofComplexity

/-- L-pcx-064: in Res(k, ⊕) every sound case split of a term into `c` terms is derivable in
fewer than `3 (k + 1) ^ c` further lines. -/
theorem L064 : ∀ (V : Type) [DecidableEq V] (k : ℕ) (F : Set (PEqualNP.ProofComplexity.LinKLine V)) (π : List (PEqualNP.ProofComplexity.LinKLine V)) (L : PEqualNP.ProofComplexity.LinKLine V) (T : PEqualNP.ProofComplexity.LinTerm V) (S : PEqualNP.ProofComplexity.LinKLine V), 1 ≤ k → PEqualNP.ProofComplexity.IsLinKDerivation k PEqualNP.ProofComplexity.IsLinKWeakening F π → L ∈ π → (∀ U ∈ S, U.card ≤ k) → (∀ a : V → Bool, PEqualNP.ProofComplexity.LinTermSat a T → ∃ U ∈ S, PEqualNP.ProofComplexity.LinTermSat a U) → ∃ new : List (PEqualNP.ProofComplexity.LinKLine V), new.length + 2 ≤ 3 * (k + 1) ^ S.card ∧ PEqualNP.ProofComplexity.IsLinKDerivation k PEqualNP.ProofComplexity.IsLinKWeakening F (new ++ π) ∧ L.erase T ∪ S ∈ new := by
  intro V _ k F π L T S hk h hL hS hsem
  obtain ⟨new, hl, hπ, hm⟩ := Helpers.LinKSplit.split_any hk h hL T S hS hsem
  exact ⟨new, by have := Helpers.LinKSplit.splitCost_le hk S.card; omega, hπ, hm⟩

end PEqualNP.ProofComplexity
