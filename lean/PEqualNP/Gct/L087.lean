import PEqualNP.Defs
import PEqualNP.Gct.Helpers.Sigma4Space

/-! L-gct-087. There is a linear space `L` of `4 × 4` complex matrices, of dimension at least
seven, such that the permanent vanishes on the translate of `L` through the all ones matrix
with corner entry `-3`. Proof: with `w ^ 2 + w + 1 = 0`, an explicit seven parameter family of
matrices containing that point, whose permanent is a multiple of `w ^ 2 + w + 1`; the family is
a linear space, so its translate through one of its members is itself. -/

theorem PEqualNP.Gct.L087 : ∃ L : Submodule ℂ (Fin 4 × Fin 4 → ℂ), 7 ≤ Module.finrank ℂ L ∧ ∀ t ∈ L, MvPolynomial.eval ((fun p : Fin 4 × Fin 4 => if p.1.val = 3 ∧ p.2.val = 3 then (-3 : ℂ) else 1) + t) (PEqualNP.Gct.permPoly ℂ 4) = 0 :=
  PEqualNP.Gct.Helpers.Sigma4Space.main
