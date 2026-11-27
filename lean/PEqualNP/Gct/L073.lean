import Mathlib
import PEqualNP.Defs

/-- The red team's restatement of L-gct-056, written from its plain sentence, is equivalent to
the recorded statement. -/
theorem PEqualNP.Gct.L073 : (∀ R m0 : ℕ, ∃ m : ℕ, m0 ≤ m ∧ 1 ≤ m ∧ ∀ (n : ℕ) (A : ℕ → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m × Fin m) ℂ)), (∀ (k : ℕ) (i j : Fin n), (A k i j).totalDegree ≤ 1) → (∀ s : Fin m × Fin m →₀ ℕ, Filter.Tendsto (fun k : ℕ => (A k).det.coeff s) Filter.atTop (nhds ((∑ σ : Equiv.Perm (Fin m), ∏ i : Fin m, (MvPolynomial.X (σ i, i) : MvPolynomial (Fin m × Fin m) ℂ)).coeff s))) → (R : ℝ) * (m : ℝ) ^ 2 ≤ (n : ℝ)) ↔ (∀ R m0 : ℕ, ∃ m : ℕ, m0 ≤ m ∧ 1 ≤ m ∧ ∀ n : ℕ, PEqualNP.Gct.HasBorderDetExpression (PEqualNP.Gct.permPoly ℂ m) n → R * m ^ 2 ≤ n) := by
  constructor
  · intro h R m0
    obtain ⟨m, h1, h2, h3⟩ := h R m0
    refine ⟨m, h1, h2, ?_⟩
    intro n hB
    obtain ⟨q, hq, hlim⟩ := hB
    choose A hA hdet using hq
    have key := h3 n A (fun k i j => hA k i j) (by
      intro s
      have e : (fun k : ℕ => (A k).det.coeff s) = (fun k : ℕ => (q k).coeff s) := by
        funext k
        rw [hdet k]
      rw [e]
      exact hlim s)
    exact_mod_cast key
  · intro h R m0
    obtain ⟨m, h1, h2, h3⟩ := h R m0
    refine ⟨m, h1, h2, ?_⟩
    intro n A hA hlim
    have key := h3 n ⟨fun k => (A k).det, fun k => ⟨A k, hA k, rfl⟩, hlim⟩
    exact_mod_cast key
