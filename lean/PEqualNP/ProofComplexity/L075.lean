import PEqualNP.ProofComplexity.Helpers.Recomb

namespace PEqualNP.ProofComplexity

/-- L-pcx-075: recombination at a hyperplane, rank form. A derivation of the unit line
`f0 = 1 - c0` at rank `k` and a derivation inside the other half at relative rank `k` give a
refutation at rank `k`, when `k` exceeds the rank of the axioms. -/
theorem L075 : ∀ (n : ℕ) (A : Set (PEqualNP.ProofComplexity.LinClause (Fin n))) (w k : ℕ) (f0 : Finset (Fin n)) (c0 : Bool), f0.Nonempty → (∀ C ∈ A, PEqualNP.ProofComplexity.linRank C ≤ w) → w + 1 ≤ k → (∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin n)), PEqualNP.ProofComplexity.IsLinDerivation A π ∧ ({(f0, !c0)} : PEqualNP.ProofComplexity.LinClause (Fin n)) ∈ π ∧ ∀ L ∈ π, PEqualNP.ProofComplexity.linRank L ≤ k) → (∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin n)), PEqualNP.ProofComplexity.IsLinDerivation ((fun C => insert (f0, c0) C) '' A) π ∧ ({(f0, c0)} : PEqualNP.ProofComplexity.LinClause (Fin n)) ∈ π ∧ ∀ L ∈ π, (f0, c0) ∈ L ∧ PEqualNP.ProofComplexity.linRank L ≤ k + 1) → ∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin n)), PEqualNP.ProofComplexity.IsLinDerivation A π ∧ (∅ : PEqualNP.ProofComplexity.LinClause (Fin n)) ∈ π ∧ ∀ L ∈ π, PEqualNP.ProofComplexity.linRank L ≤ k :=
  fun _ A w k f0 c0 => Recomb.recomb A w k f0 c0

end PEqualNP.ProofComplexity
