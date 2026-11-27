import PEqualNP.Defs
import PEqualNP.Gct.Helpers.BlockIsotropic

/-! L-gct-055, the block-only case. If the permanent of `3 × 3` matrices keeps the value `6` on
`J + W`, with `J` the all ones matrix and `W` a linear space, then `W` has dimension at most
four. Proof: comparing the values at `J + (t + u)`, `J - (t + u)`, `J + (t - u)` and
`J - (t - u)` shows that the polar form of the quadratic part of the permanent at `J` vanishes
on `W × W`; that form has the invertible matrix `(J₃ - I₃) ⊗ (J₃ - I₃)`, so `W` embeds in its
own annihilator in the dual of a nine-dimensional space. -/

open PEqualNP.Gct.Helpers.BlockIso

theorem PEqualNP.Gct.L055 : ∀ W : Submodule ℂ (Fin 3 × Fin 3 → ℂ), (∀ t ∈ W, MvPolynomial.eval ((fun _ => (1 : ℂ)) + t) (PEqualNP.Gct.permPoly ℂ 3) = 6) → Module.finrank ℂ W ≤ 4 := by
  intro W h
  exact finrank_le_four W fun t ht u hu => isotropic W h t u ht hu
