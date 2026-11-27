import PEqualNP.Defs
import PEqualNP.Gct.L009

/-! L-gct-008: for `m ≥ 3`, `perm_m` is not the determinant of an `m × m` matrix of affine forms
over `ℂ` (Marcus and Minc 1961). A corollary of L-gct-009: `m² ≤ 2m` forces `m ≤ 2`. -/

theorem PEqualNP.Gct.L008 :
    ∀ m : ℕ, 3 ≤ m → ¬ PEqualNP.Gct.HasDetExpression (PEqualNP.Gct.permPoly ℂ m) m := by
  intro m hm hp
  have := PEqualNP.Gct.L009 m m hp
  nlinarith
