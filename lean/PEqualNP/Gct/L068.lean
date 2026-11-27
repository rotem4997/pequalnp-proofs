import Mathlib
import PEqualNP.Defs

/-- The red team's restatement of L-gct-064, written from its plain sentence, is equivalent to
the recorded statement. -/
theorem PEqualNP.Gct.L068 : (∀ (m n : ℕ) (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m × Fin m) ℂ)), 3 ≤ m → (∀ i j : Fin n, (A i j).totalDegree ≤ 1) → A.det = ∑ σ : Equiv.Perm (Fin m), ∏ i : Fin m, (MvPolynomial.X (σ i, i) : MvPolynomial (Fin m × Fin m) ℂ) → (2 * (m : ℝ) ^ 2 - 10 * (m : ℝ) + 11) / 3 ≤ (n : ℝ)) ↔ (∀ m n : ℕ, 3 ≤ m → PEqualNP.Gct.HasDetExpression (PEqualNP.Gct.permPoly ℂ m) n → 2 * m ^ 2 + 11 ≤ 3 * n + 10 * m) := by
  have key : ∀ m : ℕ, PEqualNP.Gct.permPoly ℂ m = ∑ σ : Equiv.Perm (Fin m), ∏ i : Fin m, (MvPolynomial.X (σ i, i) : MvPolynomial (Fin m × Fin m) ℂ) := fun _ => rfl
  have arith : ∀ m n : ℕ, ((2 * (m : ℝ) ^ 2 - 10 * (m : ℝ) + 11) / 3 ≤ (n : ℝ)) ↔ (2 * m ^ 2 + 11 ≤ 3 * n + 10 * m) := by
    intro m n
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    constructor
    · intro h
      have h' : (2 * (m : ℝ) ^ 2 + 11) ≤ 3 * (n : ℝ) + 10 * (m : ℝ) := by linarith
      exact_mod_cast h'
    · intro h
      have h' : (2 * (m : ℝ) ^ 2 + 11) ≤ 3 * (n : ℝ) + 10 * (m : ℝ) := by exact_mod_cast h
      linarith
  constructor
  · intro h m n hm hE
    obtain ⟨A, hA, hdet⟩ := hE
    exact (arith m n).mp (h m n A hm hA (hdet.trans (key m)))
  · intro h m n A hm hA hdet
    exact (arith m n).mpr (h m n hm ⟨A, hA, hdet.trans (key m).symm⟩)
