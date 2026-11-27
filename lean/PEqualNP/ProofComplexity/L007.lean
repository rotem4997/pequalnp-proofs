import PEqualNP.ProofComplexity.Helpers.CookReckhow

/-- L-pcx-007 (Cook and Reckhow 1979): a nonempty language is in NP exactly when it is the
range of a polynomial-time function under which every member has a proof of polynomial
length. -/
theorem PEqualNP.ProofComplexity.L007 : ∀ L : Language Bool, Set.Nonempty L → (L ∈ PEqualNP.Library.NP ↔ ∃ f : List Bool → List Bool, PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f ∧ Set.range f = L ∧ ∃ p : Polynomial ℕ, ∀ x ∈ L, ∃ w : List Bool, w.length ≤ p.eval x.length ∧ f w = x) :=
  fun L hne => ⟨fun hL => PEqualNP.ProofComplexity.Helpers.cr_np_range L hne hL,
    fun ⟨f, hf, hr, p, hp⟩ => PEqualNP.ProofComplexity.Helpers.cr_range_np L f hf hr p hp⟩
