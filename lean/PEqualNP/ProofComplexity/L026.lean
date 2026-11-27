import PEqualNP.ProofComplexity.Helpers.PCToolkit

namespace PEqualNP.ProofComplexity

/-- L-pcx-026: polynomial calculus is sound, and the bit pigeonhole system has no common zero. -/
theorem L026 : ∀ (m l B : ℕ), 2 ^ l < m → (¬ ∃ a : Fin m × Fin l → ZMod 2, ∀ f ∈ PEqualNP.ProofComplexity.bitPHPSystem m l, MvPolynomial.eval a f = 0) ∧ ∀ (σ : Type) (F : Set (MvPolynomial σ (ZMod 2))), PEqualNP.ProofComplexity.PCRefutable F B → ¬ ∃ a : σ → ZMod 2, ∀ f ∈ F, MvPolynomial.eval a f = 0 := by
  intro m l B hml; exact ⟨Helpers.bitPHPSystem_no_common_zero hml, fun σ F h => Helpers.pcRefutable_no_common_zero h⟩

end PEqualNP.ProofComplexity
