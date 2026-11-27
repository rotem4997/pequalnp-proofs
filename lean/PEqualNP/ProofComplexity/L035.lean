import PEqualNP.ProofComplexity.Helpers.Assembly

namespace PEqualNP.ProofComplexity

/-- L-pcx-035: the assembly of the chain. From the degree lower bound for row-linear
polynomials, the simulation of Res(⊕) by block systems and the elimination of the blocks,
every Res(⊕) refutation of bit pigeonhole with `2 ^ l + 1` pigeons and `l ≥ 32` bits has
more than `exp (2 ^ l / (32768 * l ^ 2))` lines. -/
theorem L035 : (∀ (m l k B : ℕ) (f : MvPolynomial (Fin m × Fin l) (ZMod 2)), 2 ≤ l → 1 ≤ k → k ≤ B → 4 * (k - 1) < 2 ^ l → 2 * B + 2 * k ≤ 2 ^ l + 1 → f ≠ 0 → PEqualNP.ProofComplexity.IsRowLinear m l k f → ¬ PEqualNP.ProofComplexity.PCDerivable (PEqualNP.ProofComplexity.bitPHPSystem m l) B f) → (∀ (m l h : ℕ) (π : List (PEqualNP.ProofComplexity.LinClause (Fin m × Fin l))), 1 ≤ h → PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.BPHP m l) π → ∃ (M W : ℕ) (g : Fin M → Fin W → MvPolynomial (Fin m × Fin l) (ZMod 2)), M ≤ 3 * π.length + m.choose 2 ∧ (∀ (j : Fin M) (i : Fin W), (g j i).totalDegree ≤ 1) ∧ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.blockSystem (PEqualNP.ProofComplexity.bitPHPSystem m l) h M W g) (max (2 * h + l) (4 * h + 1))) → (∀ (m l k D M W : ℕ) (g : Fin M → Fin W → MvPolynomial (Fin m × Fin l) (ZMod 2)), 0 < m → 1 ≤ l → 1 ≤ k → 1 ≤ M → k ≤ m → (m : ℝ) * Real.log (4 * (M : ℝ)) ≤ (k : ℝ) ^ 2 → 2 * (3 * l) + 1 ≤ D → (∀ (j : Fin M) (i : Fin W), (g j i).totalDegree ≤ 1) → PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.blockSystem (PEqualNP.ProofComplexity.bitPHPSystem m l) (3 * l) M W g) D → ∃ f : MvPolynomial (Fin m × Fin l) (ZMod 2), f ≠ 0 ∧ PEqualNP.ProofComplexity.IsRowLinear m l k f ∧ PEqualNP.ProofComplexity.PCDerivable (PEqualNP.ProofComplexity.bitPHPSystem m l) (k * (D + 1)) f) → ∀ (l : ℕ) (π : List (PEqualNP.ProofComplexity.LinClause (Fin (2 ^ l + 1) × Fin l))), 32 ≤ l → PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) π → Real.exp ((2 : ℝ) ^ l / (32768 * (l : ℝ) ^ 2)) < (π.length : ℝ) :=
  fun HB HC HD l π hl hπ => Helpers.assembly HB HC HD l π hl hπ

end PEqualNP.ProofComplexity
