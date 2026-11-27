import Mathlib
import PEqualNP.Defs

/-! Assembly of a cubic lower bound on the border determinantal complexity of the permanent
from three ingredients taken as hypotheses. Helper for L-gct-027. -/

namespace PEqualNP.Gct.Helpers

open MvPolynomial

/-- The substitution that turns the permanent of size `N + 1` into the permanent of size `N`:
the first row and column become `(1, 0, ..., 0)` and the other variables are shifted down. -/
noncomputable def dropSubst (N : ℕ) :
    Fin (N + 1) × Fin (N + 1) → MvPolynomial (Fin N × Fin N) ℂ :=
  fun p => Fin.cases (Fin.cases 1 (fun _ => 0) p.2)
    (fun i => Fin.cases 0 (fun j => X (i, j)) p.2) p.1

theorem totalDegree_dropSubst (N : ℕ) (p : Fin (N + 1) × Fin (N + 1)) :
    (dropSubst N p).totalDegree ≤ 1 := by
  obtain ⟨i, j⟩ := p
  cases i using Fin.cases <;> cases j using Fin.cases <;> simp [dropSubst]

/-- The permanent of the block matrix `[[1, 0], [0, X]]` is the permanent of `X`. -/
theorem bind₁_dropSubst_permPoly (N : ℕ) :
    bind₁ (dropSubst N) (PEqualNP.Gct.permPoly ℂ (N + 1)) = PEqualNP.Gct.permPoly ℂ N := by
  simp only [PEqualNP.Gct.permPoly, Matrix.permanent, map_sum, map_prod,
    Matrix.mvPolynomialX_apply, bind₁_X_right]
  rw [← Equiv.sum_comp (Equiv.Perm.decomposeFin (n := N)).symm, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single 0]
  · refine Finset.sum_congr rfl fun e _ => ?_
    rw [Fin.prod_univ_succ]
    simp [dropSubst]
  · intro p _ hp
    refine Finset.sum_eq_zero fun e _ => ?_
    refine Finset.prod_eq_zero (Finset.mem_univ 0) ?_
    obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hp
    simp [dropSubst]
  · simp

/-- If border determinantal expressions pass through affine substitutions, then a border
expression of a larger permanent gives one of the same size for a smaller permanent. -/
theorem border_perm_drop
    (H1 : ∀ (σ τ : Type) [Finite σ] (p : MvPolynomial σ ℂ) (g : σ → MvPolynomial τ ℂ) (n : ℕ),
      (∀ i, (g i).totalDegree ≤ 1) → PEqualNP.Gct.HasBorderDetExpression p n →
        PEqualNP.Gct.HasBorderDetExpression (MvPolynomial.bind₁ g p) n)
    (N e n : ℕ)
    (h : PEqualNP.Gct.HasBorderDetExpression (PEqualNP.Gct.permPoly ℂ (N + e)) n) :
    PEqualNP.Gct.HasBorderDetExpression (PEqualNP.Gct.permPoly ℂ N) n := by
  induction e with
  | zero => exact h
  | succ e ih =>
    apply ih
    have h' := H1 _ _ (PEqualNP.Gct.permPoly ℂ (N + e + 1)) (dropSubst (N + e)) n
      (totalDegree_dropSubst _) h
    rwa [bind₁_dropSubst_permPoly] at h'

/-- The arithmetic at the end of the assembly. -/
theorem cubic_arith (k m r d n : ℕ) (hk : 128 ≤ k) (hm : m < 11 * k + 11) (hr : k ≤ 3 * r)
    (hd : k ^ 2 ≤ 100 * d + 100) (h : (r - 1) * (d - 1) ≤ 11 * n) :
    m ^ 3 ≤ 15206400 * n := by
  have hkk : 16384 ≤ k ^ 2 := by nlinarith
  have h4 : k ≤ 4 * (r - 1) := by omega
  have h200 : k ^ 2 ≤ 200 * (d - 1) := by
    generalize k ^ 2 = K at hd hkk
    omega
  have hk3 : k ^ 3 ≤ 800 * ((r - 1) * (d - 1)) := by
    calc k ^ 3 = k * k ^ 2 := by ring
      _ ≤ (4 * (r - 1)) * (200 * (d - 1)) := Nat.mul_le_mul h4 h200
      _ = 800 * ((r - 1) * (d - 1)) := by ring
  have hm12 : m ≤ 12 * k := by omega
  calc m ^ 3 ≤ (12 * k) ^ 3 := Nat.pow_le_pow_left hm12 3
    _ = 1728 * k ^ 3 := by ring
    _ ≤ 1728 * (800 * (11 * n)) :=
      Nat.mul_le_mul_left _ (hk3.trans (Nat.mul_le_mul_left _ h))
    _ = 15206400 * n := by ring

/-- The assembly: closure of border expressions under affine substitutions, a lower bound for
smooth forms, and a family of smooth forms that are affine substitutions of permanents
together give a cubic lower bound for the permanent. -/
theorem cubic_assembly :
    (∀ (σ τ : Type) [Finite σ] (p : MvPolynomial σ ℂ) (g : σ → MvPolynomial τ ℂ) (n : ℕ),
      (∀ i, (g i).totalDegree ≤ 1) → PEqualNP.Gct.HasBorderDetExpression p n →
        PEqualNP.Gct.HasBorderDetExpression (MvPolynomial.bind₁ g p) n) →
    (∀ (d r n : ℕ) (G : MvPolynomial (Fin d) ℂ), 2 ≤ d → 2 ≤ r → G.IsHomogeneous r →
      (∀ x : Fin d → ℂ, (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i G) = 0) → x = 0) →
        PEqualNP.Gct.HasBorderDetExpression G n → (r - 1) * (d - 1) ≤ 11 * n) →
    (∀ k : ℕ, 128 ≤ k → ∃ (r d : ℕ) (G : MvPolynomial (Fin d) ℂ)
      (g : Fin (11 * k) × Fin (11 * k) → MvPolynomial (Fin d) ℂ),
        k ≤ 3 * r ∧ k ^ 2 ≤ 100 * d + 100 ∧ G.IsHomogeneous r ∧
        (∀ x : Fin d → ℂ, (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i G) = 0) → x = 0) ∧
        (∀ i, (g i).totalDegree ≤ 1) ∧
        MvPolynomial.bind₁ g (PEqualNP.Gct.permPoly ℂ (11 * k)) = G) →
    (∃ (c m0 : ℕ), 0 < c ∧ ∀ m n : ℕ, m0 ≤ m →
      PEqualNP.Gct.HasBorderDetExpression (PEqualNP.Gct.permPoly ℂ m) n → m ^ 3 ≤ c * n) := by
  intro H1 H2 H3
  refine ⟨15206400, 1408, by norm_num, fun m n hm hb => ?_⟩
  have hk : 128 ≤ m / 11 := by omega
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (Nat.mul_div_le m 11)
  have he11 : e < 11 := by omega
  generalize m / 11 = k at hk he
  subst he
  obtain ⟨r, d, G, g, hr, hd, hG, hsm, hg, hbind⟩ := H3 k hk
  have hb' := border_perm_drop H1 (11 * k) e n hb
  have hGb := H1 _ _ _ g n hg hb'
  rw [hbind] at hGb
  have hd2 : 2 ≤ d := by
    have hkk : 16384 ≤ k ^ 2 := by nlinarith
    generalize k ^ 2 = K at hd hkk
    omega
  have hfin := H2 d r n G hd2 (by omega) hG hsm hGb
  exact cubic_arith k _ r d n hk (by omega) hr hd hfin

end PEqualNP.Gct.Helpers
