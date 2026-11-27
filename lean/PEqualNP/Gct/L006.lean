import PEqualNP.Defs
import PEqualNP.Gct.Helpers.OrbitClosure

/-! L-gct-006: if `perm_m` has a determinantal expression of size `n + 1` with `m ≤ n`, then the
padded permanent lies in the orbit closure of `det_{n+1}` (Mulmuley and Sohoni 2001).
Homogenizing the expression writes the padded permanent exactly as `det_{n+1}` after a linear
change of variables, and any such matrix is a limit of invertible ones. -/

theorem PEqualNP.Gct.L006 :
    ∀ m n : ℕ, m ≤ n → PEqualNP.Gct.HasDetExpression (PEqualNP.Gct.permPoly ℂ m) (n + 1) →
      PEqualNP.Gct.paddedPerm ℂ m n ∈ PEqualNP.Gct.orbitClosure (PEqualNP.Gct.detPoly ℂ (n + 1)) := by
  intro m n hmn ⟨A, hA, hdet⟩
  rw [← PEqualNP.Gct.Helpers.linSubst_homMat hmn A hA hdet]
  exact PEqualNP.Gct.Helpers.linSubst_mem_orbitClosure _ _
