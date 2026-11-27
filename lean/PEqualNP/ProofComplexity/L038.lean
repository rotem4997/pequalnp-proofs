import PEqualNP.ProofComplexity.Helpers.BoolVanish
import PEqualNP.ProofComplexity.Helpers.LowRankBlock
import PEqualNP.ProofComplexity.Helpers.BlockRemoval

namespace PEqualNP.ProofComplexity

/-- L-pcx-038, block removal (Lemma 7.7 of the unrefereed arXiv:2609.23015): a degree-D
refutation of the old system with extension blocks puts the weight `f` in the degree
`k (D + 1)` closure of the old system. -/
theorem L038 : ∀ (σ β : Type) (s h k D : ℕ) (F : Set (MvPolynomial σ (ZMod 2))) (g : β → Fin s → MvPolynomial σ (ZMod 2)) (f : MvPolynomial σ (ZMod 2)), (∀ v : σ, MvPolynomial.X v * MvPolynomial.X v + MvPolynomial.X v ∈ F) → (∀ b i, (g b i).totalDegree ≤ 1) → 1 ≤ h → 1 ≤ k → 2 * h + 1 ≤ D → f.totalDegree ≤ k → (∀ b : β, h * (k + 1) < Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (g b))) → (1 : MvPolynomial σ (ZMod 2)) ∈ Submodule.span (ZMod 2) (Set.range (g b)) ∨ ∃ a : Fin s → MvPolynomial σ (ZMod 2), (∀ i, (a i).totalDegree ≤ k - 1) ∧ f = ∑ i, a i * g b i) → PEqualNP.ProofComplexity.PCRefutable ((MvPolynomial.rename (Sum.inl : σ → σ ⊕ (β × Fin h × Fin s))) '' F ∪ {p | ∃ (b : β) (i : Fin s), p = MvPolynomial.rename Sum.inl (g b i) * ∏ u : Fin h, (1 + ∑ i' : Fin s, MvPolynomial.X (Sum.inr (b, u, i')) * MvPolynomial.rename Sum.inl (g b i'))} ∪ {p | ∃ t : β × Fin h × Fin s, p = MvPolynomial.X (Sum.inr t) * MvPolynomial.X (Sum.inr t) + MvPolynomial.X (Sum.inr t)}) D → PEqualNP.ProofComplexity.PCDerivable F (k * (D + 1)) f :=
  Helpers.BlockRemoval.of_lemmas Helpers.BoolVanish.vanish_derivable Helpers.LowRankBlock.low_rank

end PEqualNP.ProofComplexity
