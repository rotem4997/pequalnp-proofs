import PEqualNP.Defs
import PEqualNP.Gct.L009
import PEqualNP.Gct.L012
import PEqualNP.Gct.L020
import PEqualNP.Gct.Helpers.OrbitClosure

/-! The pointwise Mignon-Ressayre plus one argument: at a smooth zero `y` of `perm_m` with
nondegenerate Hessian, a small determinantal expression `A = A₀ + L` of `perm_m` has
`adj (A y) * A₀ = 0 = A₀ * adj (A y)`. Homogenize `A` with a new variable `s`; its determinant is
`s ^ (n - m) * perm`, whose Hessian at `(1, y)` has a kernel. The rank bound on the Hessian of the
determinant forces a kernel vector of `Hess det (A y) * J`, which is a multiple of
`(1 + c) A₀ - c A y`, and L-gct-020 finishes. -/

namespace PEqualNP.Gct.Helpers

open Finset MvPolynomial Matrix

/-- If `Jᵀ Q J` has a nonzero kernel vector, `Q` is symmetric and its rank is at most the width
of `J`, then `Q J` has a nonzero kernel vector. -/
theorem exists_ker_of_rank_le {ι σ : Type} [Fintype ι] [Fintype σ] [DecidableEq ι]
    [DecidableEq σ] (Q : Matrix ι ι ℂ) (J : Matrix ι σ ℂ) (hQ : Qᵀ = Q)
    (hr : Q.rank ≤ Fintype.card σ) (v : σ → ℂ) (hv : v ≠ 0) (hB : (Jᵀ * Q * J) *ᵥ v = 0) :
    ∃ w : σ → ℂ, w ≠ 0 ∧ (Q * J) *ᵥ w = 0 := by
  by_contra hcon
  push Not at hcon
  have hker : LinearMap.ker (Q * J).mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    by_contra hw0
    exact hcon w hw0 hw
  have hrk : (Q * J).rank = Fintype.card σ := by
    have := (Q * J).mulVecLin.finrank_range_add_finrank_ker
    rw [hker, finrank_bot, add_zero, Module.finrank_fintype_fun_eq_card] at this
    exact this
  have hP : Jᵀ * Q = (Q * J)ᵀ := by rw [Matrix.transpose_mul, hQ]
  have hrk' : (Jᵀ * Q).rank = Fintype.card σ := by rw [hP, Matrix.rank_transpose, hrk]
  have h1 := (Jᵀ * Q).mulVecLin.finrank_range_add_finrank_ker
  have h2 := Q.mulVecLin.finrank_range_add_finrank_ker
  have hle : LinearMap.ker Q.mulVecLin ≤ LinearMap.ker (Jᵀ * Q).mulVecLin := by
    intro x hx
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hx ⊢
    rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  have heq : LinearMap.ker Q.mulVecLin = LinearMap.ker (Jᵀ * Q).mulVecLin := by
    refine Submodule.eq_of_le_of_finrank_le hle ?_
    have e1 : (Jᵀ * Q).rank = Module.finrank ℂ (LinearMap.range (Jᵀ * Q).mulVecLin) := rfl
    have e2 : Q.rank = Module.finrank ℂ (LinearMap.range Q.mulVecLin) := rfl
    omega
  have hJv : J *ᵥ v ∈ LinearMap.ker (Jᵀ * Q).mulVecLin := by
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
    exact hB
  rw [← heq] at hJv
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec] at hJv
  exact hcon v hv hJv

/-- A square matrix of full rank has trivial kernel. -/
theorem eq_zero_of_rank_eq_card {σ : Type} [Fintype σ] [DecidableEq σ] (H : Matrix σ σ ℂ)
    (hH : H.rank = Fintype.card σ) (z : σ → ℂ) (hz : H *ᵥ z = 0) : z = 0 := by
  have h := H.mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at h
  have e : H.rank = Module.finrank ℂ (LinearMap.range H.mulVecLin) := rfl
  have h0 : Module.finrank ℂ (LinearMap.ker H.mulVecLin) = 0 := by omega
  rw [Submodule.finrank_eq_zero] at h0
  have hmem : z ∈ LinearMap.ker H.mulVecLin := by simpa using hz
  rw [h0] at hmem
  simpa using hmem

theorem perm_isHomogeneous (m : ℕ) : (PEqualNP.Gct.permPoly ℂ m).IsHomogeneous m := by
  unfold PEqualNP.Gct.permPoly Matrix.permanent
  refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have := IsHomogeneous.prod (univ : Finset (Fin m))
    (fun i => (Matrix.mvPolynomialX (Fin m) (Fin m) ℂ) (σ i) i) (fun _ => 1)
    (fun i _ => isHomogeneous_X ℂ _)
  simpa using this

/-- Euler's identity for the permanent at a point. -/
theorem euler_grad {m : ℕ} (y : Fin m × Fin m → ℂ) :
    ∑ a, eval y (pderiv a (PEqualNP.Gct.permPoly ℂ m)) * y a =
      m * eval y (PEqualNP.Gct.permPoly ℂ m) := by
  have := congrArg (eval y) (perm_isHomogeneous m).sum_X_mul_pderiv
  simp only [map_sum, map_mul, eval_X, nsmul_eq_mul, map_natCast] at this
  rw [← this]
  exact sum_congr rfl fun a _ => mul_comm _ _

/-- Euler's identity for the first partials of the permanent. -/
theorem euler_hess {m : ℕ} (hm : 1 ≤ m) (y : Fin m × Fin m → ℂ) (a : Fin m × Fin m) :
    ∑ b, eval y (pderiv a (pderiv b (PEqualNP.Gct.permPoly ℂ m))) * y b =
      ((m : ℂ) - 1) * eval y (pderiv a (PEqualNP.Gct.permPoly ℂ m)) := by
  have := congrArg (eval y) ((perm_isHomogeneous m).pderiv (i := a)).sum_X_mul_pderiv
  simp only [map_sum, map_mul, eval_X, nsmul_eq_mul, Nat.cast_sub hm, map_sub, map_one, map_natCast,
    Nat.cast_one] at this
  rw [← this]
  refine sum_congr rfl fun b _ => ?_
  rw [pderiv_comm]
  ring

theorem pderiv_none_rename {τ : Type} [DecidableEq τ] (q : MvPolynomial τ ℂ) :
    pderiv (none : Option τ) (rename some q) = 0 := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p a h => simp [Derivation.leibniz, h, pderiv_X]

theorem eval_rename_some {τ : Type} (y : τ → ℂ) (q : MvPolynomial τ ℂ) :
    eval (fun o : Option τ => o.elim 1 y) (rename some q) = eval y q := by
  rw [eval_rename]; rfl

section HessHom

variable {τ : Type} [DecidableEq τ] (k : ℕ) (p : MvPolynomial τ ℂ) (y : τ → ℂ)

theorem hess_hom_nn (hy : eval y p = 0) :
    hess (X none ^ k * rename some p) (fun o => o.elim 1 y) none none = 0 := by
  simp [hess, Derivation.leibniz, pderiv_none_rename, eval_rename_some, hy]

theorem hess_hom_ns (b : τ) :
    hess (X none ^ k * rename some p) (fun o => o.elim 1 y) none (some b) =
      k * eval y (pderiv b p) := by
  simp [hess, Derivation.leibniz, pderiv_none_rename, eval_rename_some,
    pderiv_rename (Option.some_injective τ), Derivation.leibniz_pow, mul_comm]

theorem hess_hom_sn (a : τ) :
    hess (X none ^ k * rename some p) (fun o => o.elim 1 y) (some a) none =
      k * eval y (pderiv a p) := by
  simp [hess, Derivation.leibniz, pderiv_none_rename, eval_rename_some,
    pderiv_rename (Option.some_injective τ), Derivation.leibniz_pow]

theorem hess_hom_ss (a b : τ) :
    hess (X none ^ k * rename some p) (fun o => o.elim 1 y) (some a) (some b) =
      eval y (pderiv a (pderiv b p)) := by
  simp [hess, Derivation.leibniz, eval_rename_some, pderiv_rename (Option.some_injective τ)]

end HessHom

variable {m n : ℕ}

/-- The homogenized entries `s * A₀ + L(z)`. -/
noncomputable def homEntry (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m × Fin m) ℂ))
    (q : Fin n × Fin n) : MvPolynomial (Option (Fin m × Fin m)) ℂ :=
  C ((A q.1 q.2).coeff 0) * X none +
    ∑ v, C ((A q.1 q.2).coeff (Finsupp.single v 1)) * X (some v)

/-- The (constant) Jacobian of `homEntry`. -/
noncomputable def homJac (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m × Fin m) ℂ))
    (q : Fin n × Fin n) (o : Option (Fin m × Fin m)) : ℂ :=
  o.elim ((A q.1 q.2).coeff 0) fun v => (A q.1 q.2).coeff (Finsupp.single v 1)

theorem pderiv_homEntry (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m × Fin m) ℂ))
    (q : Fin n × Fin n) (o : Option (Fin m × Fin m)) :
    pderiv o (homEntry A q) = C (homJac A q o) := by
  cases o with
  | none => simp [homEntry, homJac, pderiv_X]
  | some a => simp [homEntry, homJac, pderiv_X, Pi.single_apply]

theorem eval_homEntry (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m × Fin m) ℂ))
    (q : Fin n × Fin n) (w : Option (Fin m × Fin m) → ℂ) :
    eval w (homEntry A q) = (A q.1 q.2).coeff 0 * w none +
      ∑ v, (A q.1 q.2).coeff (Finsupp.single v 1) * w (some v) := by
  simp [homEntry]

theorem eval_bind_det (φ : Fin n × Fin n → MvPolynomial (Option (Fin m × Fin m)) ℂ)
    (w : Option (Fin m × Fin m) → ℂ) :
    eval w (bind₁ φ (PEqualNP.Gct.detPoly ℂ n)) =
      (Matrix.of fun i j => eval w (φ (i, j))).det := by
  have : eval w (bind₁ φ (PEqualNP.Gct.detPoly ℂ n)) =
      eval (fun q => eval w (φ q)) (PEqualNP.Gct.detPoly ℂ n) := by
    show eval₂Hom (RingHom.id ℂ) w _ = _
    rw [eval₂Hom_bind₁]
    rfl
  rw [this, PEqualNP.Gct.detPoly, Matrix.eval_det_mvPolynomialX]

/-- Homogenization: `det (s A₀ + L(z)) = s ^ (n - m) * perm z`. -/
theorem bind_homEntry_det (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m × Fin m) ℂ))
    (hA : ∀ i j, (A i j).totalDegree ≤ 1) (hdet : A.det = PEqualNP.Gct.permPoly ℂ m)
    (hmn : m ≤ n) :
    bind₁ (homEntry A) (PEqualNP.Gct.detPoly ℂ n) =
      X none ^ (n - m) * rename some (PEqualNP.Gct.permPoly ℂ m) := by
  have hX : (X none : MvPolynomial (Option (Fin m × Fin m)) ℂ) ≠ 0 := X_ne_zero _
  refine mul_left_cancel₀ hX (MvPolynomial.funext fun w => ?_)
  simp only [map_mul, eval_X, map_pow, eval_rename, eval_bind_det]
  set s := w none
  by_cases hs : s = 0
  · rw [hs, zero_mul, zero_mul]
  congr 1
  set z : Fin m × Fin m → ℂ := w ∘ some with hz
  have hmat : (Matrix.of fun i j => eval w (homEntry A (i, j))) =
      s • (Matrix.of fun i j => eval (s⁻¹ • z) (A i j)) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, eval_homEntry,
      eval_affine _ (hA i j), Pi.smul_apply, mul_add, mul_sum, hz, Function.comp]
    congr 1
    · ring
    · refine sum_congr rfl fun v _ => ?_
      field_simp
  have hev : (Matrix.of fun i j => eval (s⁻¹ • z) (A i j)).det = (s⁻¹) ^ m * eval z
      (PEqualNP.Gct.permPoly ℂ m) := by
    rw [← eval_perm_smul, ← hdet, RingHom.map_det]
    rfl
  rw [hmat, Matrix.det_smul, hev, Fintype.card_fin]
  have hsplit : n = (n - m) + m := by omega
  conv_lhs => rw [hsplit, pow_add]
  have : s ^ m * s⁻¹ ^ m = 1 := by rw [← mul_pow, mul_inv_cancel₀ hs, one_pow]
  calc s ^ (n - m) * s ^ m * (s⁻¹ ^ m * eval z (PEqualNP.Gct.permPoly ℂ m))
      = s ^ (n - m) * (s ^ m * s⁻¹ ^ m) * eval z (PEqualNP.Gct.permPoly ℂ m) := by ring
    _ = _ := by rw [this, mul_one]

theorem pointwise_mr {m n : ℕ} (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin m × Fin m) ℂ))
    (hm : 3 ≤ m) (hsmall : 2 * n ≤ m ^ 2 + 1) (hA : ∀ i j, (A i j).totalDegree ≤ 1)
    (hdet : A.det = PEqualNP.Gct.permPoly ℂ m) (y : Fin m × Fin m → ℂ)
    (hy : MvPolynomial.eval y (PEqualNP.Gct.permPoly ℂ m) = 0)
    (hH : (Matrix.of fun a b : Fin m × Fin m => MvPolynomial.eval y (MvPolynomial.pderiv a
      (MvPolynomial.pderiv b (PEqualNP.Gct.permPoly ℂ m)))).rank = m ^ 2) :
    (A.map (MvPolynomial.eval y)).adjugate * A.map (fun q => q.coeff 0) = 0 ∧
      A.map (fun q => q.coeff 0) * (A.map (MvPolynomial.eval y)).adjugate = 0 := by
  classical
  set p := PEqualNP.Gct.permPoly ℂ m with hp
  set M := A.map (MvPolynomial.eval y) with hMdef
  set A0 := A.map (fun q => q.coeff 0) with hA0def
  have hnm : m < n := by
    have := PEqualNP.Gct.L009 m n ⟨A, hA, hdet⟩
    nlinarith
  have hn2 : 2 ≤ n := by omega
  have hdetM : M.det = 0 := by
    have : M.det = eval y A.det := by rw [RingHom.map_det]; rfl
    rw [this, hdet, hy]
  set k := n - m with hk
  set y' : Option (Fin m × Fin m) → ℂ := fun o => o.elim 1 y with hy'
  set x : Fin n × Fin n → ℂ := fun q => M q.1 q.2 with hx
  set Q := hess (PEqualNP.Gct.detPoly ℂ n) x with hQ
  set J : Matrix (Fin n × Fin n) (Option (Fin m × Fin m)) ℂ := Matrix.of (homJac A) with hJ
  have hφx : (fun q => eval y' (homEntry A q)) = x := by
    funext q
    simp [eval_homEntry, hx, hMdef, hy', eval_affine _ (hA q.1 q.2)]
  set B := Jᵀ * Q * J with hBdef
  have hB : hess (X none ^ k * rename some p) y' = B := by
    rw [← bind_homEntry_det A hA hdet hnm.le, hess_bind₁ (homEntry A) (homJac A)
      (pderiv_homEntry A) _ y', hφx]
  set H := hess p y with hHdef
  have hHrank : H.rank = Fintype.card (Fin m × Fin m) := by
    rw [hHdef, hess, hH]; simp [sq]
  set g := fun a => eval y (pderiv a p) with hg
  have hm1 : (m : ℂ) - 1 ≠ 0 := by
    intro h
    have : (m : ℂ) = 1 := by linear_combination h
    exact absurd (by exact_mod_cast this : m = 1) (by omega)
  set cc : ℂ := (k : ℂ) / ((m : ℂ) - 1) with hccdef
  have hcc : cc * ((m : ℂ) - 1) = k := div_mul_cancel₀ _ hm1
  have h1cc : 1 + cc ≠ 0 := by
    intro h
    have : ((m + k : ℕ) : ℂ) = 1 := by push_cast; linear_combination ((m : ℂ) - 1) * h - hcc
    exact absurd (by exact_mod_cast this : m + k = 1) (by omega)
  have e_nn : B none none = 0 := by rw [← hB]; exact hess_hom_nn k p y hy
  have e_ns : ∀ b, B none (some b) = k * g b := fun b => by rw [← hB]; exact hess_hom_ns k p y b
  have e_sn : ∀ a, B (some a) none = k * g a := fun a => by rw [← hB]; exact hess_hom_sn k p y a
  have e_ss : ∀ a b, B (some a) (some b) = H a b := fun a b => by
    rw [← hB]; exact hess_hom_ss k p y a b
  have hEg := euler_grad y
  have hEh := euler_hess (m := m) (by omega) y
  set v0 : Option (Fin m × Fin m) → ℂ := fun o => o.elim 1 (fun a => -cc * y a) with hv0def
  have hv0 : v0 ≠ 0 := fun h => by have := congrFun h none; simp [v0] at this
  have hBv0 : B *ᵥ v0 = 0 := by
    funext o
    cases o with
    | none =>
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_option, e_nn, e_ns, hv0def,
        Option.elim, Pi.zero_apply]
      have : ∑ b, (k : ℂ) * g b * (-cc * y b) = -(k * cc) * ∑ b, g b * y b := by
        rw [mul_sum]; exact sum_congr rfl fun b _ => by ring
      rw [this, hg]
      simp only
      rw [hEg, ← hp, hy]; ring
    | some a =>
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_option, e_sn, e_ss, hv0def,
        Option.elim, Pi.zero_apply]
      have : ∑ b, H a b * (-cc * y b) = -cc * ∑ b, H a b * y b := by
        rw [mul_sum]; exact sum_congr rfl fun b _ => by ring
      rw [this, hHdef]
      simp only [hess, Matrix.of_apply]
      rw [hEh a, hg]
      simp only
      linear_combination (-(eval y (pderiv a p))) * hcc
  have hQsymm : Qᵀ = Q := by
    ext a b
    simp [hQ, hess, pderiv_comm]
  have hQrank : Q.rank ≤ Fintype.card (Option (Fin m × Fin m)) := by
    have hx0 : eval x (PEqualNP.Gct.detPoly ℂ n) = 0 := by
      rw [PEqualNP.Gct.detPoly, Matrix.eval_det_mvPolynomialX]
      exact hdetM
    have := PEqualNP.Gct.L012 n x hx0
    rw [hQ, hess]
    simp only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin]
    have : m ^ 2 = m * m := sq m
    omega
  obtain ⟨w, hw0, hQJw⟩ := exists_ker_of_rank_le Q J hQsymm hQrank v0 hv0 hBv0
  have hBw : B *ᵥ w = 0 := by
    rw [hBdef, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hQJw, Matrix.mulVec_zero]
  set s0 := w none with hs0def
  have hz : (fun a => w (some a) + cc * s0 * y a) = 0 := by
    apply eq_zero_of_rank_eq_card H hHrank
    funext a
    have h := congrFun hBw (some a)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_option, e_sn, e_ss,
      Pi.zero_apply] at h
    simp only [Matrix.mulVec, dotProduct, mul_add, sum_add_distrib, Pi.zero_apply]
    have : ∑ b, H a b * (cc * s0 * y b) = cc * s0 * ∑ b, H a b * y b := by
      rw [mul_sum]; exact sum_congr rfl fun b _ => by ring
    rw [this]
    have h2 : ∑ b, H a b * y b = ((m : ℂ) - 1) * g a := by
      rw [hHdef, hg]; simp only [hess, Matrix.of_apply]; exact hEh a
    rw [h2]
    linear_combination h + (s0 * g a) * hcc
  have hw : ∀ v, w (some v) = -(cc * s0 * y v) := fun v =>
    eq_neg_of_add_eq_zero_left (congrFun hz v)
  have hs0 : s0 ≠ 0 := by
    intro h
    apply hw0
    funext o
    cases o with
    | none => exact h
    | some a => simp [hw a, h]
  set E : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => (J *ᵥ w) (i, j) with hEdef
  have hE : E = s0 • ((1 + cc) • A0 - cc • M) := by
    ext i j
    simp only [hEdef, hJ, Matrix.of_apply, Matrix.mulVec, dotProduct, Fintype.sum_option,
      homJac, Option.elim, hw, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, hA0def,
      hMdef, Matrix.map_apply, eval_affine _ (hA i j) y]
    have : ∑ v, (A i j).coeff (Finsupp.single v 1) * -(cc * s0 * y v) =
        -(cc * s0) * ∑ v, (A i j).coeff (Finsupp.single v 1) * y v := by
      rw [mul_sum]; exact sum_congr rfl fun b _ => by ring
    rw [this]
    ring
  have hker : ∀ a : Fin n × Fin n, ∑ b : Fin n × Fin n, MvPolynomial.eval (fun p => M p.1 p.2)
      (MvPolynomial.pderiv a (MvPolynomial.pderiv b (PEqualNP.Gct.detPoly ℂ n))) *
        E b.1 b.2 = 0 := by
    intro a
    have h := congrFun hQJw a
    rw [← Matrix.mulVec_mulVec] at h
    simpa [Matrix.mulVec, dotProduct, hQ, hess, hEdef] using h
  obtain ⟨h1, h2⟩ := PEqualNP.Gct.L020 n M E hn2 hdetM hker
  have hadjM : M.adjugate * M = 0 := by rw [Matrix.adjugate_mul, hdetM, zero_smul]
  have hMadj : M * M.adjugate = 0 := by rw [Matrix.mul_adjugate, hdetM, zero_smul]
  rw [hE] at h1 h2
  rw [Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, hadjM, smul_zero,
    sub_zero, smul_smul] at h1
  rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, hMadj, smul_zero,
    sub_zero, smul_smul] at h2
  exact ⟨(smul_eq_zero.mp h1).resolve_left (mul_ne_zero hs0 h1cc),
    (smul_eq_zero.mp h2).resolve_left (mul_ne_zero hs0 h1cc)⟩

end PEqualNP.Gct.Helpers
