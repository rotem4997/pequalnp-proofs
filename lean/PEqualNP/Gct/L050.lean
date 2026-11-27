import PEqualNP.Defs
import PEqualNP.Gct.Helpers.ConeReduction

/-! L-gct-050, cone reduction for the linear-space method on the permanent. If the permanent
vanishes on the affine space `y + L`, with `L` a linear space, then it vanishes on
`y + (L + span y)`: the zero set of a form is a cone, so the affine space may be enlarged by
the line through `y`. Proof: a point of `y + (L + span y)` is `u • y + l` with `l` in `L`; for
`u ≠ 0` homogeneity gives the value `u ^ m` times a value on `y + L`, and `u = 0` follows by
continuity in `u`. -/

open MvPolynomial PEqualNP.Gct.Helpers.ConeRed

theorem PEqualNP.Gct.L050 : ∀ (m : ℕ) (y : Fin m × Fin m → ℂ) (L : Submodule ℂ (Fin m × Fin m → ℂ)), (∀ t ∈ L, MvPolynomial.eval (y + t) (PEqualNP.Gct.permPoly ℂ m) = 0) → ∀ t ∈ L ⊔ Submodule.span ℂ {y}, MvPolynomial.eval (y + t) (PEqualNP.Gct.permPoly ℂ m) = 0 := by
  intro m y L h t ht
  obtain ⟨l, hl, z, hz, rfl⟩ := Submodule.mem_sup.mp ht
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have e : y + (l + c • y) = (1 + c) • y + l := by
    rw [add_smul, one_smul]; abel
  rw [e]
  exact eval_smul_add_eq_zero m y L h l hl (1 + c)
