import Mathlib
import PEqualNP.Defs
import PEqualNP.Gct.Helpers.PolarLift1

/-! The polar lift: simple polar points of a determinant of affine forms lift to nondegenerate
zeros of a bilinear system in the point and the two kernel vectors, and the weighted Bezout
statement on the lifted system gives the weighted count of the polar points. -/

namespace PEqualNP.Gct.Helpers

open Finset Matrix MvPolynomial

/-- The unknowns of the lifted system: the point, the right kernel vector, the left kernel
vector, and one slack unknown. -/
abbrev LVar (h n : ℕ) : Type := Fin (h + 2) ⊕ (Fin n ⊕ (Fin n ⊕ Unit))

section Lift

variable {h n : ℕ}

/-- A point of the lifted space. -/
def lpt (x : Fin (h + 2) → ℂ) (u v : Fin n → ℂ) (t : ℂ) : LVar h n → ℂ :=
  Sum.elim x (Sum.elim u (Sum.elim v fun _ => t))

/-- The components of a lifted vector. -/
def dxp (dz : LVar h n → ℂ) : Fin (h + 2) → ℂ := fun l => dz (Sum.inl l)

def dup (dz : LVar h n → ℂ) : Fin n → ℂ := fun j => dz (Sum.inr (Sum.inl j))

def dvp (dz : LVar h n → ℂ) : Fin n → ℂ := fun j => dz (Sum.inr (Sum.inr (Sum.inl j)))

def dtp (dz : LVar h n → ℂ) : ℂ := dz (Sum.inr (Sum.inr (Sum.inr ())))

/-- The unknowns as polynomials. -/
noncomputable def XU (h : ℕ) {n : ℕ} (j : Fin n) : MvPolynomial (LVar h n) ℂ :=
  X (Sum.inr (Sum.inl j))

noncomputable def XV (h : ℕ) {n : ℕ} (j : Fin n) : MvPolynomial (LVar h n) ℂ :=
  X (Sum.inr (Sum.inr (Sum.inl j)))

noncomputable def XT (h n : ℕ) : MvPolynomial (LVar h n) ℂ :=
  X (Sum.inr (Sum.inr (Sum.inr ())))

/-- The matrix entry `a0 i j + ∑ l, Al l i j * x l` as a polynomial in the lifted unknowns. -/
noncomputable def hatA (a0 : Matrix (Fin n) (Fin n) ℂ)
    (Al : Fin (h + 2) → Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : MvPolynomial (LVar h n) ℂ :=
  C (a0 i j) + ∑ l, C (Al l i j) * X (Sum.inl l)

/-- The matrix `∑ l, dx l • Al l`. -/
def linA (Al : Fin (h + 2) → Matrix (Fin n) (Fin n) ℂ) (dx : Fin (h + 2) → ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => ∑ l, Al l i j * dx l

noncomputable def E1 (a0 : Matrix (Fin n) (Fin n) ℂ)
    (Al : Fin (h + 2) → Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : MvPolynomial (LVar h n) ℂ :=
  ∑ j, hatA a0 Al i j * XU h j

noncomputable def E2 (a0 : Matrix (Fin n) (Fin n) ℂ)
    (Al : Fin (h + 2) → Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℂ) (j : Fin n) :
    MvPolynomial (LVar h n) ℂ :=
  ∑ i, XV h i * hatA a0 Al i j - C (lam j) * XT h n

noncomputable def E3 (Al : Fin (h + 2) → Matrix (Fin n) (Fin n) ℂ)
    (vv : Fin h → Fin (h + 2) → ℂ) (k : Fin h) : MvPolynomial (LVar h n) ℂ :=
  ∑ l, C (vv k l) * ∑ i, XV h i * ∑ j, C (Al l i j) * XU h j

noncomputable def E4 (n : ℕ) (a : Fin (h + 2) → ℂ) : MvPolynomial (LVar h n) ℂ :=
  ∑ l, C (a l) * X (Sum.inl l) - 1

noncomputable def E5 (h : ℕ) (lam : Fin n → ℂ) : MvPolynomial (LVar h n) ℂ :=
  ∑ j, C (lam j) * XU h j - 1

noncomputable def E6 (h : ℕ) (mu : Fin n → ℂ) : MvPolynomial (LVar h n) ℂ :=
  ∑ j, C (mu j) * XV h j - 1

/-- The lifted system: as many equations as unknowns. -/
noncomputable def liftF (a0 : Matrix (Fin n) (Fin n) ℂ)
    (Al : Fin (h + 2) → Matrix (Fin n) (Fin n) ℂ) (a : Fin (h + 2) → ℂ)
    (vv : Fin h → Fin (h + 2) → ℂ) (lam mu : Fin n → ℂ) :
    LVar h n → MvPolynomial (LVar h n) ℂ :=
  Sum.elim (Fin.cons (E4 n a) (Fin.cons (E5 h lam) (E3 Al vv)))
    (Sum.elim (E1 a0 Al) (Sum.elim (E2 a0 Al lam) fun _ => E6 h mu))

variable (a0 : Matrix (Fin n) (Fin n) ℂ) (Al : Fin (h + 2) → Matrix (Fin n) (Fin n) ℂ)
  (a : Fin (h + 2) → ℂ) (vv : Fin h → Fin (h + 2) → ℂ) (lam mu : Fin n → ℂ)

theorem liftF_zero : liftF a0 Al a vv lam mu (Sum.inl 0) = E4 n a := by
  simp only [liftF, Sum.elim_inl, Fin.cons_zero]

theorem liftF_one : liftF a0 Al a vv lam mu (Sum.inl (Fin.succ 0)) = E5 h lam := by
  simp only [liftF, Sum.elim_inl, Fin.cons_succ, Fin.cons_zero]

theorem liftF_succ (k : Fin h) :
    liftF a0 Al a vv lam mu (Sum.inl k.succ.succ) = E3 Al vv k := by
  simp only [liftF, Sum.elim_inl, Fin.cons_succ]

theorem liftF_u (i : Fin n) : liftF a0 Al a vv lam mu (Sum.inr (Sum.inl i)) = E1 a0 Al i := rfl

theorem liftF_v (j : Fin n) :
    liftF a0 Al a vv lam mu (Sum.inr (Sum.inr (Sum.inl j))) = E2 a0 Al lam j := rfl

theorem liftF_t (s : Unit) :
    liftF a0 Al a vv lam mu (Sum.inr (Sum.inr (Sum.inr s))) = E6 h mu := rfl

section Rows

variable (x : Fin (h + 2) → ℂ) (u v : Fin n → ℂ) (t : ℂ) (dz : LVar h n → ℂ)

theorem eval_XU (j : Fin n) : eval (lpt x u v t) (XU h j) = u j := by
  simp [XU, lpt]

theorem eval_XV (j : Fin n) : eval (lpt x u v t) (XV h j) = v j := by
  simp [XV, lpt]

theorem eval_XT : eval (lpt x u v t) (XT h n) = t := by
  simp [XT, lpt]

theorem pd_XU (z : LVar h n → ℂ) (j : Fin n) : pd z dz (XU h j) = dup dz j := pd_X z dz _

theorem pd_XV (z : LVar h n → ℂ) (j : Fin n) : pd z dz (XV h j) = dvp dz j := pd_X z dz _

theorem pd_XT (z : LVar h n → ℂ) : pd z dz (XT h n) = dtp dz := pd_X z dz _

theorem eval_hatA (i j : Fin n) :
    eval (lpt x u v t) (hatA a0 Al i j) = a0 i j + ∑ l, Al l i j * x l := by
  simp [hatA, lpt]

theorem pd_hatA (z : LVar h n → ℂ) (i j : Fin n) :
    pd z dz (hatA a0 Al i j) = linA Al (dxp dz) i j := by
  simp only [hatA, pd_add, pd_C, pd_sum, pd_mul, pd_X, eval_C, zero_mul, add_zero, zero_add]
  rfl

variable {a0 Al x} {M : Matrix (Fin n) (Fin n) ℂ}
  (hM : ∀ i j, M i j = a0 i j + ∑ l, Al l i j * x l)

include hM

theorem eval_E1 (i : Fin n) : eval (lpt x u v t) (E1 a0 Al i) = (M *ᵥ u) i := by
  simp only [E1, map_sum, map_mul, eval_hatA, eval_XU, ← hM]
  rfl

theorem pd_E1 (i : Fin n) :
    pd (lpt x u v t) dz (E1 a0 Al i) = (M *ᵥ dup dz + linA Al (dxp dz) *ᵥ u) i := by
  simp only [E1, pd_sum, pd_mul, eval_hatA, pd_hatA, eval_XU, pd_XU, ← hM, sum_add_distrib]
  rfl

theorem eval_E2 (j : Fin n) :
    eval (lpt x u v t) (E2 a0 Al lam j) = (v ᵥ* M) j - lam j * t := by
  simp only [E2, map_sub, map_sum, map_mul, eval_C, eval_hatA, eval_XV, eval_XT, ← hM]
  rfl

theorem pd_E2 (j : Fin n) :
    pd (lpt x u v t) dz (E2 a0 Al lam j) =
      (v ᵥ* linA Al (dxp dz)) j + (dvp dz ᵥ* M) j - lam j * dtp dz := by
  simp only [E2, pd_sub, pd_sum, pd_mul, pd_C, eval_C, eval_hatA, pd_hatA, eval_XV, pd_XV,
    pd_XT, ← hM, zero_mul, add_zero, sum_add_distrib]
  rfl

omit hM

variable (Al x)

theorem eval_E3 (k : Fin h) :
    eval (lpt x u v t) (E3 Al vv k) = ∑ l, vv k l * (v ⬝ᵥ (Al l *ᵥ u)) := by
  simp only [E3, map_sum, map_mul, eval_C, eval_XU, eval_XV]
  rfl

theorem pd_E3 (k : Fin h) :
    pd (lpt x u v t) dz (E3 Al vv k) =
      ∑ l, vv k l * (v ⬝ᵥ (Al l *ᵥ dup dz) + dvp dz ⬝ᵥ (Al l *ᵥ u)) := by
  simp only [E3, pd_sum, pd_mul, pd_C, eval_C, map_sum, map_mul, eval_XU, eval_XV, pd_XU,
    pd_XV, zero_mul, add_zero, sum_add_distrib]
  rfl

theorem eval_E4 : eval (lpt x u v t) (E4 n a) = ∑ l, a l * x l - 1 := by
  simp [E4, lpt]

theorem pd_E4 (z : LVar h n → ℂ) : pd z dz (E4 n a) = ∑ l, a l * dxp dz l := by
  simp only [E4, pd_sub, pd_sum, pd_mul, pd_C, pd_X, pd_one, eval_C, zero_mul, add_zero,
    sub_zero]
  rfl

theorem eval_E5 : eval (lpt x u v t) (E5 h lam) = lam ⬝ᵥ u - 1 := by
  simp only [E5, map_sub, map_sum, map_mul, eval_C, eval_XU, map_one]
  rfl

theorem pd_E5 (z : LVar h n → ℂ) : pd z dz (E5 h lam) = lam ⬝ᵥ dup dz := by
  simp only [E5, pd_sub, pd_sum, pd_mul, pd_C, pd_XU, pd_one, eval_C, zero_mul, add_zero,
    sub_zero]
  rfl

theorem eval_E6 : eval (lpt x u v t) (E6 h mu) = mu ⬝ᵥ v - 1 := by
  simp only [E6, map_sub, map_sum, map_mul, eval_C, eval_XV, map_one]
  rfl

theorem pd_E6 (z : LVar h n → ℂ) : pd z dz (E6 h mu) = mu ⬝ᵥ dvp dz := by
  simp only [E6, pd_sub, pd_sum, pd_mul, pd_C, pd_XV, pd_one, eval_C, zero_mul, add_zero,
    sub_zero]
  rfl

end Rows

section Weights

variable (p q : ℕ)

/-- The weights of the unknowns. -/
def wt (h n p q : ℕ) : LVar h n → ℕ :=
  Sum.elim (fun _ => p) (Sum.elim (fun _ => q) (Sum.elim (fun _ => q) fun _ => p + q))

/-- The weighted degree bounds of the equations. -/
def Dg (h n p q : ℕ) : LVar h n → ℕ :=
  Sum.elim (Fin.cons p (Fin.cons q fun _ => 2 * q))
    (Sum.elim (fun _ => p + q) (Sum.elim (fun _ => p + q) fun _ => q))

theorem WD_XU (j : Fin n) : WD (wt h n p q) (XU h j) q := WD_X _ _

theorem WD_XV (j : Fin n) : WD (wt h n p q) (XV h j) q := WD_X _ _

theorem WD_XT : WD (wt h n p q) (XT h n) (p + q) := WD_X _ _

theorem WD_hatA (i j : Fin n) : WD (wt h n p q) (hatA a0 Al i j) p :=
  WD_add (WD_C _ _ _) (WD_sum fun l _ => WD_C_mul _ (WD_X (wt h n p q) (Sum.inl l)))

theorem WD_E1 (i : Fin n) : WD (wt h n p q) (E1 a0 Al i) (p + q) :=
  WD_sum fun j _ => WD_mul (WD_hatA a0 Al p q i j) (WD_XU p q j)

theorem WD_E2 (j : Fin n) : WD (wt h n p q) (E2 a0 Al lam j) (p + q) :=
  WD_sub (WD_sum fun i _ => WD_mono (WD_mul (WD_XV p q i) (WD_hatA a0 Al p q i j))
    (add_comm q p).le) (WD_C_mul _ (WD_XT p q))

theorem WD_E3 (k : Fin h) : WD (wt h n p q) (E3 Al vv k) (2 * q) :=
  WD_sum fun l _ => WD_C_mul _ (WD_sum fun i _ => WD_mono (WD_mul (WD_XV p q i)
    (WD_sum fun j _ => WD_C_mul _ (WD_XU p q j))) (two_mul q).ge)

theorem WD_E4 : WD (wt h n p q) (E4 n a) p :=
  WD_sub (WD_sum fun l _ => WD_C_mul _ (WD_X (wt h n p q) (Sum.inl l))) (WD_one _ _)

theorem WD_E5 : WD (wt h n p q) (E5 h lam) q :=
  WD_sub (WD_sum fun j _ => WD_C_mul _ (WD_XU p q j)) (WD_one _ _)

theorem WD_E6 : WD (wt h n p q) (E6 h mu) q :=
  WD_sub (WD_sum fun j _ => WD_C_mul _ (WD_XV p q j)) (WD_one _ _)

theorem WD_liftF (i : LVar h n) :
    WD (wt h n p q) (liftF a0 Al a vv lam mu i) (Dg h n p q i) := by
  rcases i with i | j | j | s
  · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => ?_) i) i
    · rw [liftF_zero]
      simp only [Dg, Sum.elim_inl, Fin.cons_zero]
      exact WD_E4 a p q
    · rw [liftF_one]
      simp only [Dg, Sum.elim_inl, Fin.cons_succ, Fin.cons_zero]
      exact WD_E5 lam p q
    · rw [liftF_succ]
      simp only [Dg, Sum.elim_inl, Fin.cons_succ]
      exact WD_E3 Al vv p q k
  · exact WD_E1 a0 Al p q j
  · exact WD_E2 a0 Al lam p q j
  · exact WD_E6 mu p q

theorem prod_wt : ∏ j : LVar h n, wt h n p q j = p ^ (h + 2) * (q ^ n * (q ^ n * (p + q))) := by
  simp [wt, Fintype.prod_sum_type]

theorem prod_Dg :
    ∏ j : LVar h n, Dg h n p q j =
      p * (q * (2 * q) ^ h) * ((p + q) ^ n * ((p + q) ^ n * q)) := by
  simp [Dg, Fintype.prod_sum_type, Fin.prod_univ_succ]

end Weights

end Lift

section Polar

variable {h n : ℕ}

/-- The polar system of `det A`: the determinant, an affine hyperplane, and `h` directional
derivatives of the determinant. -/
noncomputable def polarSys (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (h + 2)) ℂ))
    (a : Fin (h + 2) → ℂ) (vv : Fin h → Fin (h + 2) → ℂ) :
    Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ :=
  Fin.cons A.det (Fin.cons (∑ j, C (a j) * X j - 1)
    (fun k : Fin h => ∑ j, C (vv k j) * pderiv j A.det))

theorem polarSys_zero (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (h + 2)) ℂ))
    (a : Fin (h + 2) → ℂ) (vv : Fin h → Fin (h + 2) → ℂ) : polarSys A a vv 0 = A.det := by
  simp only [polarSys, Fin.cons_zero]

theorem polarSys_one (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (h + 2)) ℂ))
    (a : Fin (h + 2) → ℂ) (vv : Fin h → Fin (h + 2) → ℂ) :
    polarSys A a vv (Fin.succ 0) = ∑ j, C (a j) * X j - 1 := by
  simp only [polarSys, Fin.cons_succ, Fin.cons_zero]

theorem polarSys_succ (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (h + 2)) ℂ))
    (a : Fin (h + 2) → ℂ) (vv : Fin h → Fin (h + 2) → ℂ) (k : Fin h) :
    polarSys A a vv k.succ.succ = ∑ j, C (vv k j) * pderiv j A.det := by
  simp only [polarSys, Fin.cons_succ]

/-- The constant parts of the entries of a matrix of affine polynomials. -/
noncomputable def affC (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (h + 2)) ℂ)) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => (A i j).coeff 0

/-- The linear parts of the entries of a matrix of affine polynomials. -/
noncomputable def affL (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (h + 2)) ℂ))
    (l : Fin (h + 2)) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (A i j).coeff (Finsupp.single l 1)

/-- The lift of a simple polar point, with normalised kernel vectors, is a nondegenerate zero
of the lifted system. -/
theorem lift_nondeg (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (h + 2)) ℂ))
    (hA : ∀ i j, (A i j).totalDegree ≤ 1) (a : Fin (h + 2) → ℂ)
    (vv : Fin h → Fin (h + 2) → ℂ) (x : Fin (h + 2) → ℂ)
    (hx0 : ∀ i, eval x (polarSys A a vv i) = 0)
    (hx1 : ∀ dx : Fin (h + 2) → ℂ, (∀ i, pd x dx (polarSys A a vv i) = 0) → dx = 0)
    (lam mu u v : Fin n → ℂ) (c : ℂ) (hc : c ≠ 0)
    (hadj : (A.map (eval x)).adjugate = c • vecMulVec u v)
    (hMu : (A.map (eval x)) *ᵥ u = 0) (hvM : v ᵥ* (A.map (eval x)) = 0)
    (hlu : lam ⬝ᵥ u = 1) (hmv : mu ⬝ᵥ v = 1) :
    (∀ i, eval (lpt x u v 0) (liftF (affC A) (affL A) a vv lam mu i) = 0) ∧
      ∀ dz : LVar h n → ℂ,
        (∀ i, pd (lpt x u v 0) dz (liftF (affC A) (affL A) a vv lam mu i) = 0) → dz = 0 := by
  classical
  have hM : ∀ i j, (A.map (eval x)) i j = affC A i j + ∑ l, affL A l i j * x l :=
    fun i j => eval_affine (A i j) (hA i j) x
  have hAl : ∀ l i j, pderiv l (A i j) = C (affL A l i j) :=
    fun l i j => pderiv_affine (A i j) (hA i j) l
  have hu : u ≠ 0 := by
    rintro rfl
    simp at hlu
  have hv : v ≠ 0 := by
    rintro rfl
    simp at hmv
  have hadj0 : (A.map (eval x)).adjugate ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hu
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
    intro h0
    have h3 := congrFun (congrFun hadj i) j
    rw [h0] at h3
    simp only [Matrix.zero_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul] at h3
    exact mul_ne_zero hc (mul_ne_zero hi hj) h3.symm
  have hmapAl : ∀ l, (A.map (pderiv l)).map (eval x) = affL A l := by
    intro l
    ext i j
    simp only [Matrix.map_apply, hAl, eval_C]
  have hgrad : ∀ l, eval x (pderiv l A.det) = c * (v ⬝ᵥ (affL A l *ᵥ u)) := by
    intro l
    rw [eval_pderiv_det, hadj, hmapAl, Matrix.smul_mul, vecMulVec_mul, trace_smul,
      trace_vecMulVec, dotProduct_mulVec, dotProduct_comm, smul_eq_mul]
  have ha0 : ∑ l, a l * x l - 1 = 0 := by
    have h3 := hx0 (Fin.succ 0)
    rw [polarSys_one] at h3
    simpa using h3
  have hD0 : ∀ k, ∑ l, vv k l * (v ⬝ᵥ (affL A l *ᵥ u)) = 0 := by
    intro k
    have h3 := hx0 k.succ.succ
    rw [polarSys_succ] at h3
    simp only [map_sum, map_mul, eval_C, hgrad] at h3
    have h4 : c * ∑ l, vv k l * (v ⬝ᵥ (affL A l *ᵥ u)) = 0 := by
      rw [← h3, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    exact (mul_eq_zero.mp h4).resolve_left hc
  refine ⟨?_, ?_⟩
  · rintro (i | j | j | s)
    · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => ?_) i) i
      · rw [liftF_zero, eval_E4]
        exact ha0
      · rw [liftF_one, eval_E5, hlu, sub_self]
      · rw [liftF_succ, eval_E3]
        exact hD0 k
    · rw [liftF_u, eval_E1 u v 0 hM, hMu]
      rfl
    · rw [liftF_v, eval_E2 lam u v 0 hM, hvM]
      simp
    · rw [liftF_t, eval_E6, hmv, sub_self]
  · intro dz hdz
    have r1 : (A.map (eval x)) *ᵥ dup dz + linA (affL A) (dxp dz) *ᵥ u = 0 := by
      funext i
      have h3 := hdz (Sum.inr (Sum.inl i))
      rw [liftF_u, pd_E1 u v 0 dz hM] at h3
      exact h3
    have r2 : ∀ j, (v ᵥ* linA (affL A) (dxp dz)) j + (dvp dz ᵥ* (A.map (eval x))) j
        - lam j * dtp dz = 0 := by
      intro j
      have h3 := hdz (Sum.inr (Sum.inr (Sum.inl j)))
      rw [liftF_v, pd_E2 lam u v 0 dz hM] at h3
      exact h3
    have r3 : ∀ k, ∑ l, vv k l * (v ⬝ᵥ (affL A l *ᵥ dup dz) + dvp dz ⬝ᵥ (affL A l *ᵥ u))
        = 0 := by
      intro k
      have h3 := hdz (Sum.inl k.succ.succ)
      rw [liftF_succ, pd_E3] at h3
      exact h3
    have r4 : ∑ l, a l * dxp dz l = 0 := by
      have h3 := hdz (Sum.inl 0)
      rw [liftF_zero, pd_E4] at h3
      exact h3
    have r5 : lam ⬝ᵥ dup dz = 0 := by
      have h3 := hdz (Sum.inl (Fin.succ 0))
      rw [liftF_one, pd_E5] at h3
      exact h3
    have r6 : mu ⬝ᵥ dvp dz = 0 := by
      have h3 := hdz (Sum.inr (Sum.inr (Sum.inr ())))
      rw [liftF_t, pd_E6] at h3
      exact h3
    have hdA : A.map (pd x (dxp dz)) = linA (affL A) (dxp dz) := by
      ext i j
      simp only [Matrix.map_apply, pd, hAl, eval_C]
      rfl
    have hvdAu : v ⬝ᵥ (linA (affL A) (dxp dz) *ᵥ u) = 0 := by
      have h5 : v ⬝ᵥ ((A.map (eval x)) *ᵥ dup dz + linA (affL A) (dxp dz) *ᵥ u) = 0 := by
        rw [r1, dotProduct_zero]
      rw [dotProduct_add, dotProduct_mulVec, hvM, zero_dotProduct, zero_add] at h5
      exact h5
    have hdt : dtp dz = 0 := by
      have h6 : ∑ j, ((v ᵥ* linA (affL A) (dxp dz)) j + (dvp dz ᵥ* (A.map (eval x))) j
          - lam j * dtp dz) * u j = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [r2 j, zero_mul]
      have h7 : (v ᵥ* linA (affL A) (dxp dz)) ⬝ᵥ u + (dvp dz ᵥ* (A.map (eval x))) ⬝ᵥ u
          - dtp dz * (lam ⬝ᵥ u) = 0 := by
        rw [← h6]
        simp only [dotProduct]
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [← dotProduct_mulVec, hvdAu, ← dotProduct_mulVec, hMu, dotProduct_zero, hlu] at h7
      simpa using h7
    have hdv : dvp dz ᵥ* (A.map (eval x)) + v ᵥ* linA (affL A) (dxp dz) = 0 := by
      funext j
      have h3 := r2 j
      rw [hdt, mul_zero, sub_zero, add_comm] at h3
      exact h3
    have hpdG : pd x (dxp dz) A.det = 0 := by
      rw [pd_det, hadj, hdA, Matrix.smul_mul, vecMulVec_mul, trace_smul, trace_vecMulVec,
        dotProduct_comm, ← dotProduct_mulVec, hvdAu, smul_zero]
    obtain ⟨p1, p2, p3⟩ := pd_polar A (affL A) hAl x (dxp dz) hpdG
    rw [hdA] at p1 p2
    obtain ⟨κ, hκ⟩ := trace_dN_mul (A.map (eval x)) (A.map (eval x)).adjugate
      (A.adjugate.map (pd x (dxp dz))) (linA (affL A) (dxp dz)) u v (dup dz) (dvp dz) c hu hv
      hadj0 hMu hvM hadj p1 p2 r1 hdv
    have hdx : dxp dz = 0 := hx1 _ (by
      intro i
      refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun k => ?_) i) i
      · rw [polarSys_zero]
        exact hpdG
      · rw [polarSys_one]
        simp only [pd_sub, pd_sum, pd_mul, pd_C, pd_X, pd_one, eval_C, zero_mul, add_zero,
          sub_zero]
        exact r4
      · rw [polarSys_succ]
        simp only [pd_sum, pd_mul, pd_C, eval_C, zero_mul, add_zero, p3, hκ]
        have h8 : ∑ l, vv k l * (κ * (v ⬝ᵥ (affL A l *ᵥ u)) +
            c * (dvp dz ⬝ᵥ (affL A l *ᵥ u) + v ⬝ᵥ (affL A l *ᵥ dup dz))) =
            κ * ∑ l, vv k l * (v ⬝ᵥ (affL A l *ᵥ u)) +
            c * ∑ l, vv k l * (v ⬝ᵥ (affL A l *ᵥ dup dz) + dvp dz ⬝ᵥ (affL A l *ᵥ u)) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun l _ => by ring
        rw [h8, hD0 k, r3 k]
        ring)
    have hdA0 : linA (affL A) (dxp dz) = 0 := by
      ext i j
      simp [linA, hdx]
    rw [hdA0] at r1 hdv
    simp only [Matrix.zero_mulVec, add_zero, Matrix.vecMul_zero] at r1 hdv
    obtain ⟨τ1, h1⟩ := ker_span_of_adj (A.map (eval x)) hadj0 u hu hMu _ r1
    have hτ1 : τ1 = 0 := by
      rw [h1, dotProduct_smul, hlu] at r5
      simpa using r5
    obtain ⟨τ2, h2⟩ := leftKer_span_of_adj (A.map (eval x)) hadj0 v hv hvM _ hdv
    have hτ2 : τ2 = 0 := by
      rw [h2, dotProduct_smul, hmv] at r6
      simpa using r6
    funext i
    rcases i with l | j | j | s
    · exact congrFun hdx l
    · have h3 := congrFun h1 j
      rw [hτ1, zero_smul] at h3
      exact h3
    · have h3 := congrFun h2 j
      rw [hτ2, zero_smul] at h3
      exact h3
    · exact hdt

end Polar

/-- The weighted count of simple polar points of a determinant of affine forms, from the
weighted Bezout statement. -/
theorem polar_count_of
    (hB : ∀ (N : ℕ) (F : Fin N → MvPolynomial (Fin N) ℂ) (w D : Fin N → ℕ), (∀ i, ∀ s ∈ (F i).support, ∑ j, w j * s j ≤ D i) → ∀ S : Finset (Fin N → ℂ), (∀ x ∈ S, (∀ i, MvPolynomial.eval x (F i) = 0) ∧ (Matrix.of fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (F i))).det ≠ 0) → S.card * ∏ j, w j ≤ ∏ i, D i) :
    ∀ (h n : ℕ) (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (h + 2)) ℂ)), (∀ i j, (A i j).totalDegree ≤ 1) → ∀ (a : Fin (h + 2) → ℂ) (v : Fin h → Fin (h + 2) → ℂ) (S : Finset (Fin (h + 2) → ℂ)), (∀ x ∈ S, (∀ i, MvPolynomial.eval x ((Fin.cons A.det (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j A.det)) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i) = 0) ∧ (Matrix.of fun i j : Fin (h + 2) => MvPolynomial.eval x (MvPolynomial.pderiv j ((Fin.cons A.det (Fin.cons (∑ j, MvPolynomial.C (a j) * MvPolynomial.X j - 1) (fun k : Fin h => ∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j A.det)) : Fin (h + 2) → MvPolynomial (Fin (h + 2)) ℂ) i))).det ≠ 0) → ∀ p q : ℕ, S.card * p ^ (h + 1) * q ^ (2 * n) * (p + q) ≤ 2 ^ h * q ^ (h + 2) * (p + q) ^ (2 * n) := by
  intro h n A hA a vv S hS p q
  classical
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  have hS2 : ∀ x ∈ S, (∀ i, eval x (polarSys A a vv i) = 0) ∧
      (Matrix.of fun i j : Fin (h + 2) => eval x (pderiv j (polarSys A a vv i))).det ≠ 0 := hS
  have hS' : ∀ x ∈ S, (∀ i, eval x (polarSys A a vv i) = 0) ∧
      (∀ dx : Fin (h + 2) → ℂ, (∀ i, pd x dx (polarSys A a vv i) = 0) → dx = 0) ∧
      (A.map (eval x)).det = 0 ∧ (A.map (eval x)).adjugate ≠ 0 := by
    intro x hx
    obtain ⟨h0, h1⟩ := hS2 x hx
    refine ⟨h0, fun dx hdx => Matrix.eq_zero_of_mulVec_eq_zero h1 (funext fun i => hdx i),
      ?_, ?_⟩
    · have h2 := h0 0
      rw [polarSys_zero] at h2
      rw [← h2, RingHom.map_det]
      rfl
    · intro hadj
      apply h1
      refine Matrix.det_eq_zero_of_row_eq_zero 0 fun j => ?_
      rw [Matrix.of_apply, polarSys_zero, eval_pderiv_det, hadj, Matrix.zero_mul,
        Matrix.trace_zero]
  have hdata : ∀ x, ∃ u0 v0 : Fin n → ℂ, x ∈ S → u0 ≠ 0 ∧ v0 ≠ 0 ∧
      (A.map (eval x)) *ᵥ u0 = 0 ∧ v0 ᵥ* (A.map (eval x)) = 0 ∧
      (A.map (eval x)).adjugate = vecMulVec u0 v0 := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨-, -, hdet, hadj⟩ := hS' x hx
      obtain ⟨u0, v0, h3⟩ := adjugate_rank_one_of_det_zero _ hdet hadj
      exact ⟨u0, v0, fun _ => h3⟩
    · exact ⟨0, 0, fun h3 => absurd h3 hx⟩
  choose u0 v0 hd using hdata
  obtain ⟨lam, hlam⟩ := exists_dot_ne_zero S u0 fun x hx => (hd x hx).1
  obtain ⟨mu, hmu⟩ := exists_dot_ne_zero S v0 fun x hx => (hd x hx).2.1
  let lift : (Fin (h + 2) → ℂ) → LVar h n → ℂ := fun x =>
    lpt x ((lam ⬝ᵥ u0 x)⁻¹ • u0 x) ((mu ⬝ᵥ v0 x)⁻¹ • v0 x) 0
  have hinj : Function.Injective lift := by
    intro x1 x2 h12
    funext l
    exact congrFun h12 (Sum.inl l)
  have key := bezout_of_fin hB (liftF (affC A) (affL A) a vv lam mu) (wt h n p q) (Dg h n p q)
    (WD_liftF (affC A) (affL A) a vv lam mu p q) (S.image lift) (by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨h0, h1, -, -⟩ := hS' x hx
      obtain ⟨-, -, hMu, hvM, hadj⟩ := hd x hx
      have hl := hlam x hx
      have hm := hmu x hx
      exact lift_nondeg A hA a vv x h0 h1 lam mu _ _ ((lam ⬝ᵥ u0 x) * (mu ⬝ᵥ v0 x))
        (mul_ne_zero hl hm)
        (by
          rw [hadj]
          ext i j
          simp only [Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
          field_simp)
        (by rw [mulVec_smul, hMu, smul_zero])
        (by rw [smul_vecMul, hvM, smul_zero])
        (by rw [dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hl])
        (by rw [dotProduct_smul, smul_eq_mul, inv_mul_cancel₀ hm]))
  rw [Finset.card_image_of_injective _ hinj, prod_wt, prod_Dg] at key
  have hfin : p * (S.card * p ^ (h + 1) * q ^ (2 * n) * (p + q)) ≤
      p * (2 ^ h * q ^ (h + 2) * (p + q) ^ (2 * n)) := by
    calc p * (S.card * p ^ (h + 1) * q ^ (2 * n) * (p + q))
        = S.card * (p ^ (h + 2) * (q ^ n * (q ^ n * (p + q)))) := by ring
      _ ≤ p * (q * (2 * q) ^ h) * ((p + q) ^ n * ((p + q) ^ n * q)) := key
      _ = p * (2 ^ h * q ^ (h + 2) * (p + q) ^ (2 * n)) := by ring
  exact Nat.le_of_mul_le_mul_left hfin hp

end PEqualNP.Gct.Helpers
