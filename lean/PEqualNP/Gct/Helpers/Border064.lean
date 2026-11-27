import PEqualNP.Defs
import PEqualNP.Gct.L061
import PEqualNP.Gct.L062
import PEqualNP.Gct.Helpers.PermHessian

/-! Border form of L-gct-064, conditional on the border subspace reduction (the statement of
L-gct-069, the border form of L-gct-035). Mirrors `bound_of_fermat` in `MainAssembly`: the zero
`J - m E_11`, L-gct-062 and L-gct-061 are unchanged; only the L-gct-035 step is replaced by the
hypothesis. Helper, not a recorded lemma. -/

namespace PEqualNP.Gct.Helpers

open Finset MvPolynomial

theorem border064_of
    (h069 : ∀ (m n k : ℕ) (y : Fin m × Fin m → ℂ), MvPolynomial.eval y (PEqualNP.Gct.permPoly ℂ m) = 0 → (∀ L : Submodule ℂ (Fin m × Fin m → ℂ), (∀ t ∈ L, MvPolynomial.eval (y + t) (PEqualNP.Gct.permPoly ℂ m) = 0) → Module.finrank ℂ L ≤ k) → PEqualNP.Gct.HasBorderDetExpression (PEqualNP.Gct.permPoly ℂ m) n → m ^ 2 ≤ k + n) :
    ∀ m n : ℕ, 3 ≤ m → PEqualNP.Gct.HasBorderDetExpression (PEqualNP.Gct.permPoly ℂ m) n → 2 * m ^ 2 + 11 ≤ 3 * n + 10 * m := by
  intro m n hm hA
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  -- Step 1: transfer the Fermat statement to the index `Fin (k+2) × Fin (k+2)`.
  have hW : ∀ W : Submodule ℂ (Fin (k + 2) × Fin (k + 2) → ℂ),
      (∀ x ∈ W, ∑ i, x i ^ 2 = 0) → (∀ x ∈ W, ∑ i, x i ^ 3 = 0) →
      Module.finrank ℂ W ≤ (k + 2) * (k + 2) / 3 := by
    intro W h2 h3
    let e : (Fin (k + 2) × Fin (k + 2) → ℂ) ≃ₗ[ℂ] (Fin ((k + 2) * (k + 2)) → ℂ) :=
      LinearEquiv.funCongrLeft ℂ ℂ finProdFinEquiv.symm
    have hs : ∀ (r : ℕ) (x : Fin (k + 2) × Fin (k + 2) → ℂ),
        ∑ i, (e x) i ^ r = ∑ j, x j ^ r := fun r x =>
      Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun _ => rfl)
    have key := PEqualNP.Gct.L061 ((k + 2) * (k + 2)) (W.map (e : _ →ₗ[ℂ] _))
      (by
        rintro y ⟨x, hx, rfl⟩
        exact (hs 2 x).trans (h2 x hx))
      (by
        rintro y ⟨x, hx, rfl⟩
        exact (hs 3 x).trans (h3 x hx))
    rw [LinearEquiv.finrank_map_eq] at key
    omega
  -- Step 2: L062.
  have h62 := PEqualNP.Gct.L062 (k + 2) ((k + 2) * (k + 2) / 3) (by omega) hW
  -- Step 3: the point is the Mignon-Ressayre point, a zero of the permanent.
  have hpt : (fun p : Fin (k + 2 + 1) × Fin (k + 2 + 1) =>
      if p.1.val = 0 ∧ p.2.val = 0 then 1 - (((k + 2 : ℕ) : ℂ) + 1) else 1) = mrPoint (k + 1) := by
    funext p
    simp only [mrPoint, Prod.ext_iff, Fin.ext_iff, Fin.val_zero]
    split_ifs <;> first | rfl | (push_cast; ring)
  rw [hpt] at h62
  have hy : eval (mrPoint (k + 1)) (PEqualNP.Gct.permPoly ℂ (k + 1 + 2)) = 0 := perm_mrPoint (k + 1)
  -- Step 4: the border subspace reduction (hypothesis h069).
  have h35 := h069 (k + 3) n (4 * (k + 2) + (k + 2) * (k + 2) / 3)
    (mrPoint (k + 1)) hy h62 hA
  -- Step 5: arithmetic.
  have hd := Nat.div_mul_le_self ((k + 2) * (k + 2)) 3
  nlinarith

end PEqualNP.Gct.Helpers
