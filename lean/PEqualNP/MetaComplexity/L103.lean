import PEqualNP.MetaComplexity.Helpers.CoverPromise

/-- Promise vertex cover: from a CNF formula, an explicit graph and an explicit vertex cover of
it, always within one of every vertex cover, and a minimum cover exactly when the formula is
unsatisfiable. -/
theorem PEqualNP.MetaComplexity.L103 : ∀ φ : PEqualNP.Search.CNF, PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ) (PEqualNP.MetaComplexity.CoverPromise.cvcCover φ) ∧ (∀ S : Finset PEqualNP.MetaComplexity.CoverPromise.Vertex, PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ) S → (PEqualNP.MetaComplexity.CoverPromise.cvcCover φ).card ≤ S.card + 1) ∧ ((∀ S : Finset PEqualNP.MetaComplexity.CoverPromise.Vertex, PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (PEqualNP.MetaComplexity.CoverPromise.cvcGraph φ) S → (PEqualNP.MetaComplexity.CoverPromise.cvcCover φ).card ≤ S.card) ↔ ¬ PEqualNP.Search.Satisfiable φ) :=
  fun φ => ⟨PEqualNP.MetaComplexity.CoverPromise.cvc_cover φ,
    PEqualNP.MetaComplexity.CoverPromise.cvc_within_one φ,
    PEqualNP.MetaComplexity.CoverPromise.cvc_minimum_iff φ⟩
