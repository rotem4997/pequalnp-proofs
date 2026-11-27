import PEqualNP.Defs
import PEqualNP.Gct.Helpers.SubspaceReduction

/-! L-gct-035, subspace reduction. If `y` is a zero of `perm_m` such that every linear subspace
`L` with `perm_m` vanishing on `y + L` has dimension at most `k`, then every determinantal
expression of `perm_m` has size at least `m ^ 2 - k`. Proof: write `A (y + t) = A y + B t` with
`B` linear, pick `u ≠ 0` in the kernel of `A y`, and take `L` the kernel of `t ↦ B t u`; its
dimension is at least `m ^ 2 - n` by rank-nullity. -/

open Finset MvPolynomial PEqualNP.Gct.Helpers.SubspaceReduction

theorem PEqualNP.Gct.L035 : ∀ (m n k : ℕ) (y : Fin m × Fin m → ℂ),
    MvPolynomial.eval y (PEqualNP.Gct.permPoly ℂ m) = 0 →
    (∀ L : Submodule ℂ (Fin m × Fin m → ℂ),
      (∀ t ∈ L, MvPolynomial.eval (y + t) (PEqualNP.Gct.permPoly ℂ m) = 0) →
      Module.finrank ℂ L ≤ k) →
    PEqualNP.Gct.HasDetExpression (PEqualNP.Gct.permPoly ℂ m) n → m ^ 2 ≤ k + n := by
  intro m n k y hy hL hA
  obtain ⟨A, hdeg, hdet⟩ := hA
  have heval : ∀ z : Fin m × Fin m → ℂ,
      eval z (PEqualNP.Gct.permPoly ℂ m) = (A.map (eval z)).det := by
    intro z
    rw [← hdet, RingHom.map_det]
    rfl
  have h0 : (A.map (eval y)).det = 0 := by rw [← heval]; exact hy
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  let c : Fin n → Fin n → (Fin m × Fin m) → ℂ :=
    fun i j v => (A i j).coeff (Finsupp.single v 1)
  let Φ : (Fin m × Fin m → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    LinearMap.pi (fun i => ∑ j, ∑ v, (c i j v * u j) • LinearMap.proj v)
  have hΦ : ∀ t i, Φ t i = ∑ j, (∑ v, c i j v * t v) * u j := by
    intro t i
    simp only [Φ, LinearMap.pi_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  have hzero : ∀ t ∈ LinearMap.ker Φ,
      eval (y + t) (PEqualNP.Gct.permPoly ℂ m) = 0 := by
    intro t ht
    rw [heval]
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨u, hu0, ?_⟩
    funext i
    have hti : Φ t i = 0 := by rw [LinearMap.mem_ker.mp ht]; rfl
    have hui : (A.map (eval y)).mulVec u i = 0 := by rw [hu]; rfl
    rw [hΦ] at hti
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply] at hui ⊢
    rw [Pi.zero_apply]
    simp only [eval_add_of_totalDegree_le_one _ (hdeg _ _), add_mul, sum_add_distrib]
    rw [hui, zero_add]
    exact hti
  have hk := hL (LinearMap.ker Φ) hzero
  have hrn := LinearMap.finrank_range_add_finrank_ker Φ
  have hdom : Module.finrank ℂ (Fin m × Fin m → ℂ) = m ^ 2 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, sq]
  have hran : Module.finrank ℂ (LinearMap.range Φ) ≤ n := by
    have := Submodule.finrank_le (LinearMap.range Φ)
    rwa [Module.finrank_fin_fun] at this
  omega
