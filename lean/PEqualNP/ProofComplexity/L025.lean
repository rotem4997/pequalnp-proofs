import PEqualNP.ProofComplexity.Helpers.PCToolkit

namespace PEqualNP.ProofComplexity

/-- L-pcx-025: weighted replay of a polynomial calculus derivation under a substitution. -/
theorem L025 : ∀ (σ τ : Type) (F : Set (MvPolynomial σ (ZMod 2))) (G : Set (MvPolynomial τ (ZMod 2))) (T D s : ℕ) (φ : σ → MvPolynomial τ (ZMod 2)) (w : MvPolynomial τ (ZMod 2)) (p : MvPolynomial σ (ZMod 2)), (∀ j, (φ j).totalDegree ≤ T) → w.totalDegree ≤ s → (∀ a ∈ F, a.totalDegree ≤ D → PEqualNP.ProofComplexity.PCDerivable G (T * D + s) (w * MvPolynomial.bind₁ φ a)) → PEqualNP.ProofComplexity.PCDerivable F D p → PEqualNP.ProofComplexity.PCDerivable G (T * D + s) (w * MvPolynomial.bind₁ φ p) := by
  intro σ τ F G T D s φ w p hφ hw hax h; exact Helpers.pcDerivable_replay φ hφ w hw hax h

end PEqualNP.ProofComplexity
