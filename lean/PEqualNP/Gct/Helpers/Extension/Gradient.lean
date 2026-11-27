import PEqualNP.Defs

/-! Helpers for L-gct-083, the first-order extension bound for level spaces. With
`P z = ∑ σ, ∏ i, z (σ i, i)` (the permanent) and the polarization
`D a l = ∑ σ, ∑ i, l (σ i, i) * ∏ j ≠ i, a (σ j, j)`:
* the finite difference `P (a + e_q) - P a` is `D a e_q` (the permanent is affine in each
  variable), so `∑ q, (P (a + e_q) - P a) * l q = D a l`;
* if `s ↦ P (a + s l)` is constant then `D a l = 0` (it is the derivative at `0`). -/

namespace PEqualNP.Gct.Extension

open Finset

variable {n : ℕ}

theorem eval_perm (z : Fin n × Fin n → ℂ) :
    MvPolynomial.eval z (PEqualNP.Gct.permPoly ℂ n) =
      ∑ σ : Equiv.Perm (Fin n), ∏ i, z (σ i, i) := by
  simp [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply]

/-- The polarization of the permanent at `a` in direction `l`. -/
noncomputable def D (a l : Fin n × Fin n → ℂ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), ∑ i, l (σ i, i) * ∏ j ∈ univ.erase i, a (σ j, j)

theorem prod_add_sub {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ι → ℂ) (i0 : ι)
    (hb : ∀ i, i ≠ i0 → b i = 0) :
    ∏ i, (a i + b i) - ∏ i, a i = b i0 * ∏ j ∈ univ.erase i0, a j := by
  rw [← Finset.mul_prod_erase univ _ (mem_univ i0), ← Finset.mul_prod_erase univ a (mem_univ i0)]
  have : ∏ j ∈ univ.erase i0, (a j + b j) = ∏ j ∈ univ.erase i0, a j := by
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [hb j (Finset.ne_of_mem_erase hj), add_zero]
  rw [this]
  ring

theorem diff_eq_D (a : Fin n × Fin n → ℂ) (q : Fin n × Fin n) :
    (∑ σ : Equiv.Perm (Fin n), ∏ i, (a (σ i, i) + if (σ i, i) = q then 1 else 0)) -
      ∑ σ : Equiv.Perm (Fin n), ∏ i, a (σ i, i) =
      D a (fun p => if p = q then 1 else 0) := by
  rw [← Finset.sum_sub_distrib, D]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hb : ∀ i, i ≠ q.2 → (if (σ i, i) = q then (1 : ℂ) else 0) = 0 := by
    intro i hi
    have hne : (σ i, i) ≠ q := fun h => hi (by rw [← h])
    simp [hne]
  rw [prod_add_sub (fun i => a (σ i, i)) (fun i => if (σ i, i) = q then (1 : ℂ) else 0) q.2 hb]
  rw [Finset.sum_eq_single q.2]
  · intro i _ hi
    rw [hb i hi, zero_mul]
  · intro h
    exact absurd (mem_univ _) h

theorem sum_D_single (a l : Fin n × Fin n → ℂ) :
    ∑ q, D a (fun p => if p = q then 1 else 0) * l q = D a l := by
  simp only [D, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp [mul_comm]

theorem D_eq_zero (a l : Fin n × Fin n → ℂ) (c : ℂ)
    (h : ∀ s : ℂ, ∑ σ : Equiv.Perm (Fin n), ∏ i, (a (σ i, i) + s * l (σ i, i)) = c) :
    D a l = 0 := by
  classical
  let f : Polynomial ℂ := ∑ σ : Equiv.Perm (Fin n), ∏ i,
    (Polynomial.C (a (σ i, i)) + Polynomial.C (l (σ i, i)) * Polynomial.X)
  have hf : f = Polynomial.C c := by
    apply Polynomial.funext
    intro s
    rw [Polynomial.eval_C, ← h s]
    simp only [f, Polynomial.eval_finsetSum, Polynomial.eval_prod, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    refine Finset.sum_congr rfl fun σ _ => Finset.prod_congr rfl fun i _ => ?_
    ring
  have hd : (Polynomial.derivative f).eval 0 = 0 := by
    rw [hf, Polynomial.derivative_C, Polynomial.eval_zero]
  rw [← hd]
  simp only [f, D, Polynomial.derivative_sum, Polynomial.derivative_prod_finset,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_prod,
    Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_mul,
    Polynomial.derivative_X, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_zero, Polynomial.eval_one]
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun i _ => ?_
  ring_nf

end PEqualNP.Gct.Extension
