import Mathlib
import PEqualNP.Defs

/-- The permanent polynomial and the two notions of determinantal expression, written out. -/
theorem PEqualNP.Gct.L082 : ∀ (m n : ℕ), (PEqualNP.Gct.permPoly ℂ m = ∑ σ : Equiv.Perm (Fin m), ∏ i : Fin m, (MvPolynomial.X (σ i, i) : MvPolynomial (Fin m × Fin m) ℂ)) ∧ ∀ p : MvPolynomial (Fin m × Fin m) ℂ, (PEqualNP.Gct.HasDetExpression p n ↔ ∃ A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m × Fin m) ℂ), (∀ i j : Fin n, (A i j).totalDegree ≤ 1) ∧ A.det = p) ∧ (PEqualNP.Gct.HasBorderDetExpression p n ↔ ∃ A : ℕ → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m × Fin m) ℂ), (∀ (k : ℕ) (i j : Fin n), (A k i j).totalDegree ≤ 1) ∧ ∀ s : Fin m × Fin m →₀ ℕ, Filter.Tendsto (fun k : ℕ => (A k).det.coeff s) Filter.atTop (nhds (p.coeff s))) := by
  intro m n
  refine ⟨rfl, fun p => ⟨Iff.rfl, ?_⟩⟩
  constructor
  · rintro ⟨q, hq, hlim⟩
    choose A hA hdet using hq
    refine ⟨A, fun k i j => hA k i j, fun s => ?_⟩
    have e : (fun k : ℕ => (A k).det.coeff s) = (fun k : ℕ => (q k).coeff s) := by
      funext k
      rw [hdet k]
    rw [e]
    exact hlim s
  · rintro ⟨A, hA, hlim⟩
    exact ⟨fun k => (A k).det, fun k => ⟨A k, hA k, rfl⟩, hlim⟩
