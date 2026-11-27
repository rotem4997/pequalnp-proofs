import PEqualNP.ProofComplexity.Helpers.General

namespace PEqualNP.ProofComplexity

/-- L-pcx-041: the size of a Res(⊕) refutation of a CNF bounds the dimension of any space of
low-degree polynomials that avoids the low-degree polynomial calculus closure. -/
theorem L041 : ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V)) (π : List (PEqualNP.ProofComplexity.LinClause V)) (w h k : ℕ) (U : Submodule (ZMod 2) (MvPolynomial V (ZMod 2))), 1 ≤ h → 1 ≤ k → (∀ C ∈ F, C.card ≤ w) → PEqualNP.ProofComplexity.IsLinRefutation F π → (∀ f ∈ U, f.totalDegree ≤ k) → (∀ f ∈ U, f ≠ 0 → ¬ PEqualNP.ProofComplexity.PCDerivable (PEqualNP.ProofComplexity.cnfSystem F) (k * (max (2 * h + w) (4 * h + 1) + 1)) f) → Module.finrank (ZMod 2) U ≤ π.length * (Fintype.card V - (h * (k + 1) + 1) + k).choose k :=
  Helpers.generalCriterion

end PEqualNP.ProofComplexity
