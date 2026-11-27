import Mathlib
import PEqualNP.Defs

/-!
Helpers for L-gct-034 (hard link H4): polar points of a form.

For a form `G` of degree `r` in `h + 2` variables, a covector `a` and directions `v k`, the polar
system is `(G, a.x - 1, D_{v_1} G, .., D_{v_h} G)`. The main result here,
`polar_jacobian_det_ne_zero`, says that its Jacobian at a zero `x` is invertible as soon as the
`h + 1` gradients of the homogeneous equations `G, D_{v_1} G, .., D_{v_h} G` at `x` are linearly
independent. The covector row drops out by Euler's identity, since `a.x = 1` while every
gradient of a form vanishes on `x`. So H4 reduces to the purely homogeneous statement that, for
generic `v`, the cone of common zeros of `G, D_{v_k} G` is reduced (this independence at every
nonzero zero), plus the choice of `a` off the finitely many resulting lines.
-/

namespace PEqualNP.Gct.Helpers

open MvPolynomial

/-- The polar derivative `D_{v k} G = sum_j v k j * dG/dx_j`. -/
noncomputable def polarD {n h : ℕ} (G : MvPolynomial (Fin n) ℂ) (v : Fin h → Fin n → ℂ)
    (k : Fin h) : MvPolynomial (Fin n) ℂ :=
  ∑ j, C (v k j) * pderiv j G

/-- Euler's identity at a point. -/
theorem eval_euler {n r : ℕ} {φ : MvPolynomial (Fin n) ℂ} (hφ : φ.IsHomogeneous r)
    (x : Fin n → ℂ) : ∑ j, x j * eval x (pderiv j φ) = (r : ℂ) * eval x φ := by
  have := congrArg (eval x) hφ.sum_X_mul_pderiv
  simpa [map_sum, nsmul_eq_mul] using this

theorem polarD_isHomogeneous {n h r : ℕ} {G : MvPolynomial (Fin n) ℂ} (hG : G.IsHomogeneous r)
    (v : Fin h → Fin n → ℂ) (k : Fin h) : (polarD G v k).IsHomogeneous (r - 1) := by
  unfold polarD
  exact IsHomogeneous.sum _ _ _ fun j _ => (hG.pderiv (i := j)).C_mul _

theorem eval_pderiv_affine {n : ℕ} (a x : Fin n → ℂ) (j : Fin n) :
    eval x (pderiv j (∑ l, C (a l) * X l - 1 : MvPolynomial (Fin n) ℂ)) = a j := by
  classical
  simp [map_sum, pderiv_X, Pi.single_apply]

/-- The Jacobian of the polar system is invertible at a zero `x` (with `a.x = 1`) whenever the
gradients of `G, D_{v_1} G, .., D_{v_h} G` at `x` are linearly independent. -/
theorem polar_jacobian_det_ne_zero {h r : ℕ} (G : MvPolynomial (Fin (h + 2)) ℂ)
    (hG : G.IsHomogeneous r) (a : Fin (h + 2) → ℂ) (v : Fin h → Fin (h + 2) → ℂ)
    (x : Fin (h + 2) → ℂ) (hGx : eval x G = 0) (hax : ∑ j, a j * x j = 1)
    (hDx : ∀ k, eval x (polarD G v k) = 0)
    (hind : LinearIndependent ℂ
      (Fin.cons (fun j => eval x (pderiv j G))
        (fun k j => eval x (pderiv j (polarD G v k))) : Fin (h + 1) → Fin (h + 2) → ℂ)) :
    (Matrix.of fun i j : Fin (h + 2) => eval x (pderiv j
      ((Fin.cons G (Fin.cons (∑ j, C (a j) * X j - 1) (fun k : Fin h => polarD G v k)) :
        Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i))).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  -- the row relation, column by column
  have hrow : ∀ j, c 0 * eval x (pderiv j G) + c 1 * a j +
      ∑ k : Fin h, c k.succ.succ * eval x (pderiv j (polarD G v k)) = 0 := by
    intro j
    have := congrFun hc j
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [Fin.sum_univ_succ (n := h + 1), Fin.sum_univ_succ (n := h)] at this
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.succ_zero_eq_one] at this
    have h1 : (Fin.cons G (Fin.cons (∑ j, C (a j) * X j - 1) (fun k => polarD G v k)) :
        Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) 1 = ∑ j, C (a j) * X j - 1 := rfl
    rw [h1, eval_pderiv_affine] at this
    simpa [add_assoc] using this
  -- pair with x: Euler kills the homogeneous rows
  have hc1 : c 1 = 0 := by
    have hsum : ∑ j, x j * (c 0 * eval x (pderiv j G) + c 1 * a j +
        ∑ k : Fin h, c k.succ.succ * eval x (pderiv j (polarD G v k))) = 0 := by
      simp [hrow]
    have e0 := eval_euler hG x
    have ek : ∀ k, ∑ j, x j * eval x (pderiv j (polarD G v k)) = 0 := fun k => by
      rw [eval_euler (polarD_isHomogeneous hG v k) x, hDx k, mul_zero]
    have expand : ∑ j, x j * (c 0 * eval x (pderiv j G) + c 1 * a j +
        ∑ k : Fin h, c k.succ.succ * eval x (pderiv j (polarD G v k))) =
        c 0 * ∑ j, x j * eval x (pderiv j G) + c 1 * ∑ j, a j * x j +
        ∑ k : Fin h, c k.succ.succ * ∑ j, x j * eval x (pderiv j (polarD G v k)) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      · congr 1 <;> refine Finset.sum_congr rfl fun j _ => by ring
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    rw [expand, e0, hGx, hax] at hsum
    simpa [ek] using hsum
  -- the remaining relation contradicts independence
  have hrel : ∑ i : Fin (h + 1), (Fin.cons (c 0) (fun k : Fin h => c k.succ.succ) : Fin (h + 1) → ℂ) i •
      (Fin.cons (fun j => eval x (pderiv j G))
        (fun k j => eval x (pderiv j (polarD G v k))) : Fin (h + 1) → Fin (h + 2) → ℂ) i = 0 := by
    funext j
    rw [Fin.sum_univ_succ]
    have := hrow j
    rw [hc1] at this
    simpa using this
  have hz := linearIndependent_iff'.mp hind Finset.univ _ hrel
  apply hc0
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => ?_) i) i
  · simpa using hz 0 (Finset.mem_univ _)
  · simpa using hc1
  · simpa using hz k.succ (Finset.mem_univ _)

end PEqualNP.Gct.Helpers
