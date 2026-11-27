import PEqualNP.Defs
import PEqualNP.Gct.Helpers.WeakFermat

/-! L-gct-063: for `n ≥ 19`, a complex linear space in `ℂ^(n×n)` on which the second and third
power sums vanish satisfies `2 dim W + 6 n + 4 ≤ n^2`. From L-gct-061, `3 dim W ≤ n^2`. -/

theorem PEqualNP.Gct.L063 : ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ W : Submodule ℂ (Fin n × Fin n → ℂ), (∀ x ∈ W, ∑ i, x i ^ 2 = 0) → (∀ x ∈ W, ∑ i, x i ^ 3 = 0) → 2 * Module.finrank ℂ W + 6 * n + 4 ≤ n * n := by
  refine ⟨19, fun n hn W h2 h3 => ?_⟩
  have h := PEqualNP.Gct.Helpers.fermat_prod n W h2 h3
  nlinarith
