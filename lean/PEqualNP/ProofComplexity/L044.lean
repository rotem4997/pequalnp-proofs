import PEqualNP.ProofComplexity.Helpers.MonoRank

namespace PEqualNP.ProofComplexity

/-- L-pcx-044: the normalised rank of low-degree polynomials modulo a subspace closed under
multiplication by variables and containing the Boolean multiples is nonincreasing in the
degree. -/
theorem L044 : ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (Z : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (K k : ℕ), (∀ p ∈ Z, p.totalDegree < K → ∀ i : σ, MvPolynomial.X i * p ∈ Z) → (∀ (d : σ →₀ ℕ) (i : σ), d.degree + 2 ≤ K → MvPolynomial.monomial d (1 : ZMod 2) * (MvPolynomial.X i ^ 2 - MvPolynomial.X i) ∈ Z) → k + 1 ≤ K → Module.finrank (ZMod 2) ((MvPolynomial.restrictTotalDegree σ (ZMod 2) (k + 1)).map Z.mkQ) * (∑ j ∈ Finset.range (k + 1), (Fintype.card σ).choose j) ≤ Module.finrank (ZMod 2) ((MvPolynomial.restrictTotalDegree σ (ZMod 2) k).map Z.mkQ) * (∑ j ∈ Finset.range (k + 2), (Fintype.card σ).choose j) :=
  fun σ _ _ Z K k hX hB hk => Helpers.MonoRank.rank_ratio_monotone Z K hX hB k hk

end PEqualNP.ProofComplexity
