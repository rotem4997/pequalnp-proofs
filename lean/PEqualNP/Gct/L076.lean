import Mathlib
import PEqualNP.Defs

/-- The red team's restatement of L-gct-070, written from its plain sentence, is equivalent to
the recorded statement. -/
theorem PEqualNP.Gct.L076 : (∀ (m n : ℕ) (A : ℕ → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m × Fin m) ℂ)), 3 ≤ m → (∀ (k : ℕ) (i j : Fin n), (A k i j).totalDegree ≤ 1) → (∀ s : Fin m × Fin m →₀ ℕ, Filter.Tendsto (fun k : ℕ => (A k).det.coeff s) Filter.atTop (nhds ((∑ σ : Equiv.Perm (Fin m), ∏ i : Fin m, (MvPolynomial.X (σ i, i) : MvPolynomial (Fin m × Fin m) ℂ)).coeff s))) → (2 * (m : ℝ) ^ 2 - 10 * (m : ℝ) + 11) / 3 ≤ (n : ℝ)) ↔ (∀ m n : ℕ, 3 ≤ m → PEqualNP.Gct.HasBorderDetExpression (PEqualNP.Gct.permPoly ℂ m) n → 2 * m ^ 2 + 11 ≤ 3 * n + 10 * m) := by
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
  · intro h m n hm hB
    obtain ⟨q, hq, hlim⟩ := hB
    choose A hA hdet using hq
    refine (arith m n).mp (h m n A hm (fun k i j => hA k i j) ?_)
    intro s
    have e : (fun k : ℕ => (A k).det.coeff s) = (fun k : ℕ => (q k).coeff s) := by
      funext k
      rw [hdet k]
    rw [e]
    exact hlim s
  · intro h m n A hm hA hlim
    exact (arith m n).mpr (h m n hm ⟨fun k => (A k).det, fun k => ⟨A k, hA k, rfl⟩, hlim⟩)
