import PEqualNP.Defs
import PEqualNP.Gct.Helpers.Extension.Gradient

/-! Helper for L-gct-091 (LS(4) <= 5). The permanent is invariant under permuting rows and
columns and under transposition, for every `n`. Hence the linear map `t ↦ t ∘ e` induced by
`e = σ × τ` (or by the swap of coordinates) sends a level space (`perm (J + t) = n!` on it) to a
level space of the same finrank. -/

namespace PEqualNP.Gct.LS4

open Finset PEqualNP.Gct.Extension

variable {n : ℕ}

theorem eval_perm_rowCol (σ τ : Equiv.Perm (Fin n)) (z : Fin n × Fin n → ℂ) :
    MvPolynomial.eval (fun p => z (σ p.1, τ p.2)) (PEqualNP.Gct.permPoly ℂ n) =
      MvPolynomial.eval z (PEqualNP.Gct.permPoly ℂ n) := by
  rw [eval_perm, eval_perm]
  have h1 : ∀ π : Equiv.Perm (Fin n), ∏ i, z (σ (π i), τ i) = ∏ i, z ((σ * π * τ⁻¹) i, i) := by
    intro π
    rw [← τ.symm.prod_comp]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [Equiv.Perm.inv_def]
  simp only [h1]
  exact Fintype.sum_equiv ((Equiv.mulLeft σ).trans (Equiv.mulRight τ⁻¹)) _ _
    (fun π => by simp [mul_assoc])

theorem eval_perm_transpose (z : Fin n × Fin n → ℂ) :
    MvPolynomial.eval (fun p => z (p.2, p.1)) (PEqualNP.Gct.permPoly ℂ n) =
      MvPolynomial.eval z (PEqualNP.Gct.permPoly ℂ n) := by
  rw [eval_perm, eval_perm]
  have h1 : ∀ π : Equiv.Perm (Fin n), ∏ i, z (i, π i) = ∏ i, z (π⁻¹ i, i) := by
    intro π
    rw [← π.symm.prod_comp]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [Equiv.Perm.inv_def]
  simp only [h1]
  exact Fintype.sum_equiv (Equiv.inv _) _ _ (fun π => rfl)

/-- Level form of the row/column symmetry. -/
theorem level_rowCol (σ τ : Equiv.Perm (Fin n)) (t : Fin n × Fin n → ℂ) :
    MvPolynomial.eval (fun p => 1 + t (σ p.1, τ p.2)) (PEqualNP.Gct.permPoly ℂ n) =
      MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) :=
  eval_perm_rowCol σ τ (fun p => 1 + t p)

theorem level_transpose (t : Fin n × Fin n → ℂ) :
    MvPolynomial.eval (fun p => 1 + t (p.2, p.1)) (PEqualNP.Gct.permPoly ℂ n) =
      MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) :=
  eval_perm_transpose (fun p => 1 + t p)

/-- The linear equivalence `t ↦ t ∘ e` for a bijection `e` of the index set. -/
noncomputable abbrev reindex (e : Fin n × Fin n ≃ Fin n × Fin n) :
    (Fin n × Fin n → ℂ) ≃ₗ[ℂ] (Fin n × Fin n → ℂ) :=
  LinearEquiv.funCongrLeft ℂ ℂ e

/-- A bijection of the index set preserving the permanent of `J + t`. -/
def PermInvariant (e : Fin n × Fin n ≃ Fin n × Fin n) : Prop :=
  ∀ t : Fin n × Fin n → ℂ,
    MvPolynomial.eval (fun p => 1 + t (e p)) (PEqualNP.Gct.permPoly ℂ n) =
      MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n)

theorem permInvariant_rowCol (σ τ : Equiv.Perm (Fin n)) :
    PermInvariant (Equiv.prodCongr σ τ) := fun t => level_rowCol σ τ t

theorem permInvariant_transpose : PermInvariant (Equiv.prodComm (Fin n) (Fin n)) :=
  fun t => level_transpose t

/-- The image of a level space under an invariant reindexing is level, with the same finrank. -/
theorem map_level (e : Fin n × Fin n ≃ Fin n × Fin n) (he : PermInvariant e)
    (L : Submodule ℂ (Fin n × Fin n → ℂ))
    (hL : ∀ t ∈ L, MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) =
      (Nat.factorial n : ℂ)) :
    (∀ t ∈ L.map (reindex e).toLinearMap,
      MvPolynomial.eval (fun p => 1 + t p) (PEqualNP.Gct.permPoly ℂ n) =
        (Nat.factorial n : ℂ)) ∧
      Module.finrank ℂ (L.map (reindex e).toLinearMap) = Module.finrank ℂ L := by
  refine ⟨?_, LinearEquiv.finrank_map_eq _ _⟩
  rintro _ ⟨t, ht, rfl⟩
  rw [← hL t ht, ← he t]
  rfl

end PEqualNP.Gct.LS4
