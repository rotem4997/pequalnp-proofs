import PEqualNP.Defs
import PEqualNP.Gct.Helpers.DimCount

/-! L-gct-019: if `M` is singular with nonzero adjugate and `adj(M) A0 = 0 = A0 adj(M)` with
`A0 ≠ 0`, then a space of matrices `D` with `D A0 = 0 = A0 D` and `D M` in `adj(M)` times
matrices has dimension at most `2n - 3`. -/

theorem PEqualNP.Gct.L019 :
    ∀ (n : ℕ) (M A0 : Matrix (Fin n) (Fin n) ℂ), M.det = 0 → M.adjugate ≠ 0 →
      M.adjugate * A0 = 0 → A0 * M.adjugate = 0 → A0 ≠ 0 →
      ∀ s : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ),
        (∀ D ∈ s, D * A0 = 0 ∧ A0 * D = 0 ∧ ∃ X : Matrix (Fin n) (Fin n) ℂ,
          D * M = M.adjugate * X) → Module.finrank ℂ s + 3 ≤ 2 * n :=
  fun _ M A0 hdet hadj h1 h2 hA0 s hs =>
    PEqualNP.Gct.Helpers.finrank_le_dimcount M A0 hdet hadj h1 h2 hA0 s hs
