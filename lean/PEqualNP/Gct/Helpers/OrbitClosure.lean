import PEqualNP.Defs
import PEqualNP.Gct.Helpers.DetExprHessian

/-! A determinantal expression puts the padded permanent in the orbit closure of the
determinant. Helper for L-gct-006. -/

namespace PEqualNP.Gct.Helpers

open Finset MvPolynomial

theorem eval_linSubst {ι : Type} [Fintype ι] (g : Matrix ι ι ℂ) (f : MvPolynomial ι ℂ)
    (w : ι → ℂ) : eval w (PEqualNP.Gct.linSubst g f) = eval (g.mulVec w) f := by
  unfold PEqualNP.Gct.linSubst
  show eval₂Hom (RingHom.id ℂ) w _ = _
  rw [eval₂Hom_bind₁]
  change eval (fun i => eval w (∑ j, C (g i j) * X j)) f = _
  have : (fun i => eval w (∑ j, C (g i j) * X j)) = g.mulVec w := by
    funext i; simp [Matrix.mulVec, dotProduct]
  rw [this]

theorem degree_le_one_cases {τ : Type} (s : τ →₀ ℕ) (hs : (s.sum fun _ e => e) ≤ 1) :
    s = 0 ∨ ∃ v, s = Finsupp.single v 1 := by
  by_cases h0 : s = 0
  · exact Or.inl h0
  · obtain ⟨v, hv⟩ := Finsupp.ne_iff.mp h0
    exact Or.inr ⟨v, eq_single_of_degree_le_one s v hs (by simpa using hv)⟩

/-- An affine polynomial is its constant term plus its linear terms. -/
theorem affine_decomp {τ : Type} [Fintype τ] [DecidableEq τ] (q : MvPolynomial τ ℂ)
    (hq : q.totalDegree ≤ 1) :
    q = C (q.coeff 0) + ∑ v, C (q.coeff (Finsupp.single v 1)) * X v := by
  ext s
  simp only [MvPolynomial.coeff_add, coeff_C, coeff_sum, coeff_C_mul, coeff_X']
  by_cases hs0 : s = 0
  · subst hs0
    simp [Finsupp.single_ne_zero]
  · rw [if_neg (Ne.symm hs0), zero_add]
    by_cases hsupp : s ∈ q.support
    · obtain ⟨v, rfl⟩ := (degree_le_one_cases s ((le_totalDegree hsupp).trans hq)).resolve_left hs0
      rw [sum_eq_single v]
      · simp
      · intro u _ hu
        have : Finsupp.single u 1 ≠ Finsupp.single v 1 := by
          intro e; exact hu (Finsupp.single_left_injective one_ne_zero e)
        simp [this]
      · simp
    · rw [notMem_support_iff.mp hsupp]
      refine (sum_eq_zero fun v _ => ?_).symm
      split_ifs with h
      · subst h; simpa using notMem_support_iff.mp hsupp
      · simp

theorem eval_affine {τ : Type} [Fintype τ] [DecidableEq τ] (q : MvPolynomial τ ℂ)
    (hq : q.totalDegree ≤ 1) (y : τ → ℂ) :
    eval y q = q.coeff 0 + ∑ v, q.coeff (Finsupp.single v 1) * y v := by
  conv_lhs => rw [affine_decomp q hq]
  simp

/-- The permanent is homogeneous of degree `m`. -/
theorem eval_perm_smul (m : ℕ) (c : ℂ) (x : Fin m × Fin m → ℂ) :
    eval (c • x) (PEqualNP.Gct.permPoly ℂ m) = c ^ m * eval x (PEqualNP.Gct.permPoly ℂ m) := by
  simp only [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply, map_sum,
    map_prod, eval_X, Pi.smul_apply, smul_eq_mul, prod_mul_distrib, prod_const, card_univ,
    Fintype.card_fin, mul_sum]


/-- The (possibly singular) matrix that homogenizes a determinantal expression `A`. -/
noncomputable def homMat {m n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin m × Fin m) ℂ)) :
    Matrix (Fin (n + 1) × Fin (n + 1)) (Fin (n + 1) × Fin (n + 1)) ℂ :=
  fun r j => (if j = (0, 0) then (A r.1 r.2).coeff 0 else 0) +
    ∑ v, if j = PEqualNP.Gct.padIndex m n v then (A r.1 r.2).coeff (Finsupp.single v 1) else 0

theorem homMat_mulVec {m n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin m × Fin m) ℂ))
    (w : Fin (n + 1) × Fin (n + 1) → ℂ) (r : Fin (n + 1) × Fin (n + 1)) :
    (homMat A).mulVec w r = (A r.1 r.2).coeff 0 * w (0, 0) +
      ∑ v, (A r.1 r.2).coeff (Finsupp.single v 1) * w (PEqualNP.Gct.padIndex m n v) := by
  simp only [Matrix.mulVec, dotProduct, homMat, add_mul, sum_add_distrib, ite_mul, zero_mul,
    sum_ite_eq', mem_univ, if_true, sum_mul]
  rw [sum_comm]
  simp [sum_ite_eq']

/-- Homogenizing a size `n + 1` expression of `perm_m` gives the padded permanent. -/
theorem linSubst_homMat {m n : ℕ} (hmn : m ≤ n)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (MvPolynomial (Fin m × Fin m) ℂ))
    (hA : ∀ i j, (A i j).totalDegree ≤ 1) (hdet : A.det = PEqualNP.Gct.permPoly ℂ m) :
    PEqualNP.Gct.linSubst (homMat A) (PEqualNP.Gct.detPoly ℂ (n + 1)) =
      PEqualNP.Gct.paddedPerm ℂ m n := by
  have hX : (X (0, 0) : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) ≠ 0 := X_ne_zero _
  refine mul_left_cancel₀ hX (MvPolynomial.funext fun w => ?_)
  simp only [map_mul, eval_X, eval_linSubst]
  set z := w (0, 0)
  by_cases hz : z = 0
  · rw [hz, zero_mul, zero_mul]
  congr 1
  set x : Fin m × Fin m → ℂ := fun v => w (PEqualNP.Gct.padIndex m n v) with hx
  have hmat : (Matrix.of fun r s => (homMat A).mulVec w (r, s)) =
      z • (Matrix.of fun r s => eval (z⁻¹ • x) (A r s)) := by
    refine Matrix.ext fun r s => ?_
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, homMat_mulVec,
      eval_affine _ (hA r s), Pi.smul_apply, mul_add, mul_sum, hx]
    congr 1
    · ring
    · refine sum_congr rfl fun v _ => ?_
      field_simp
  have hev : (Matrix.of fun r s => eval (z⁻¹ • x) (A r s)).det = (z⁻¹) ^ m * eval x
      (PEqualNP.Gct.permPoly ℂ m) := by
    rw [← eval_perm_smul, ← hdet, RingHom.map_det]
    rfl
  rw [PEqualNP.Gct.detPoly, Matrix.eval_det_mvPolynomialX, hmat, Matrix.det_smul, hev,
    Fintype.card_fin, PEqualNP.Gct.paddedPerm, map_mul, map_pow, eval_X, eval_rename]
  have hsplit : n + 1 = (n + 1 - m) + m := by omega
  conv_lhs => rw [hsplit, pow_add]
  have : z ^ m * z⁻¹ ^ m = 1 := by rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
  calc z ^ (n + 1 - m) * z ^ m * (z⁻¹ ^ m * eval x (PEqualNP.Gct.permPoly ℂ m))
      = z ^ (n + 1 - m) * (z ^ m * z⁻¹ ^ m) * eval x (PEqualNP.Gct.permPoly ℂ m) := by ring
    _ = _ := by rw [this, mul_one]; rfl


/-- Each coefficient of `linSubst (g + ε • 1) f` is a polynomial function of `ε`. -/
theorem coeff_linSubst_poly {ι : Type} [Fintype ι] [DecidableEq ι] (g : Matrix ι ι ℂ)
    (f : MvPolynomial ι ℂ) (s : ι →₀ ℕ) :
    ∃ P : Polynomial ℂ, ∀ ε : ℂ,
      (PEqualNP.Gct.linSubst (g + ε • (1 : Matrix ι ι ℂ)) f).coeff s = P.eval ε := by
  let G : Matrix ι ι (Polynomial ℂ) :=
    g.map (Polynomial.C : ℂ →+* Polynomial ℂ) + (Polynomial.X : Polynomial ℂ) • (1 : Matrix ι ι (Polynomial ℂ))
  refine ⟨(PEqualNP.Gct.linSubst G (map Polynomial.C f)).coeff s, fun ε => ?_⟩
  have hmap : map (Polynomial.evalRingHom ε) (PEqualNP.Gct.linSubst G (map Polynomial.C f)) =
      PEqualNP.Gct.linSubst (g + ε • (1 : Matrix ι ι ℂ)) f := by
    unfold PEqualNP.Gct.linSubst
    rw [map_bind₁, MvPolynomial.map_map]
    have hid : (Polynomial.evalRingHom ε).comp Polynomial.C = RingHom.id ℂ := by
      ext; simp
    rw [hid, MvPolynomial.map_id]
    have hfun : (fun i => map (Polynomial.evalRingHom ε) (∑ j, C (G i j) * X j)) =
        fun i => ∑ j, C ((g + ε • (1 : Matrix ι ι ℂ)) i j) * X j := by
      funext i
      simp only [map_sum, map_mul, map_C, map_X]
      refine sum_congr rfl fun j _ => ?_
      have hG : Polynomial.evalRingHom ε (G i j) = (g + ε • (1 : Matrix ι ι ℂ)) i j := by
        simp only [G, Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
          smul_eq_mul, map_add, map_mul, Polynomial.coe_evalRingHom, Polynomial.eval_C,
          Polynomial.eval_X]
        split_ifs <;> simp
      rw [hG]
    rw [hfun]
  rw [← hmap, coeff_map]
  rfl

/-- A linear substitution by any matrix lands in the orbit closure: approximate the matrix by
invertible ones. -/
theorem linSubst_mem_orbitClosure {ι : Type} [Fintype ι] [DecidableEq ι] (g : Matrix ι ι ℂ)
    (f : MvPolynomial ι ℂ) :
    PEqualNP.Gct.linSubst g f ∈ PEqualNP.Gct.orbitClosure f := by
  classical
  set ε : ℕ → ℂ := fun k => 1 / ((k : ℂ) + 1) with hε
  have hε0 : Filter.Tendsto ε Filter.atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set cp := (-g).charpoly with hcp
  have hdet : ∀ e : ℂ, (g + e • (1 : Matrix ι ι ℂ)).det = cp.eval e := by
    intro e
    rw [hcp, Matrix.eval_charpoly]
    congr 1
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply, add_comm]
  have hfin : Set.Finite {e : ℂ | cp.IsRoot e} :=
    Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic _).ne_zero
  have hinj : Function.Injective ε := by
    intro a b hab
    simp only [hε, one_div, inv_inj, add_left_inj, Nat.cast_inj] at hab
    exact hab
  have hbad : Set.Finite {k : ℕ | cp.IsRoot (ε k)} :=
    hfin.preimage (hinj.injOn)
  have hgood : ∀ᶠ k in Filter.atTop, IsUnit (g + ε k • (1 : Matrix ι ι ℂ)).det := by
    rw [← Nat.cofinite_eq_atTop]
    filter_upwards [hbad.eventually_cofinite_notMem] with k hk
    rw [hdet]
    exact isUnit_iff_ne_zero.mpr hk
  let gk : ℕ → Matrix.GeneralLinearGroup ι ℂ := fun k =>
    if h : IsUnit (g + ε k • (1 : Matrix ι ι ℂ)).det then
      Matrix.nonsingInvUnit _ h else 1
  refine ⟨gk, fun s => ?_⟩
  obtain ⟨P, hP⟩ := coeff_linSubst_poly g f s
  have hlim : Filter.Tendsto (fun k => P.eval (ε k)) Filter.atTop (nhds (P.eval 0)) :=
    (P.continuous.tendsto 0).comp hε0
  have h0 : P.eval 0 = (PEqualNP.Gct.linSubst g f).coeff s := by
    rw [← hP]; simp
  rw [← h0]
  refine hlim.congr' ?_
  filter_upwards [hgood] with k hk
  simp only [gk, dif_pos hk]
  rw [← hP]
  rfl

end PEqualNP.Gct.Helpers
