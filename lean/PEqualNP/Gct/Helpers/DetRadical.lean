import PEqualNP.Defs
import PEqualNP.Gct.Helpers.DetHessian

/-! A matrix in the radical of the Hessian quadratic form of the determinant at a singular
matrix `M` is killed by the adjugate of `M` on both sides. Helper for L-gct-012. -/

namespace PEqualNP.Gct.Helpers

open Finset MvPolynomial

/-- The value of the second derivative of the determinant at a diagonal matrix, when a single
permutation `σ₀` can contribute. -/
theorem hess_det_diag_val {n : ℕ} (d : Fin n → ℂ) (a b : Fin n × Fin n)
    (σ₀ : Equiv.Perm (Fin n)) (h0 : σ₀ b.2 = b.1 ∧ a.2 ≠ b.2 ∧ σ₀ a.2 = a.1)
    (hfix : ∀ j, j ≠ a.2 → j ≠ b.2 → σ₀ j = j) :
    eval (fun p => Matrix.diagonal d p.1 p.2)
        (pderiv a (pderiv b (PEqualNP.Gct.detPoly ℂ n))) =
      ((Equiv.Perm.sign σ₀ : ℤ) : ℂ) * ∏ j ∈ (univ.erase b.2).erase a.2, d j := by
  rw [hess_det_sum, sum_eq_single σ₀]
  · simp only [h0, ne_eq, not_false_eq_true, and_self, ite_true]
    congr 1
    refine prod_congr rfl fun j hj => ?_
    have hja := (mem_erase.mp hj).1
    have hjb := (mem_erase.mp (mem_erase.mp hj).2).1
    simp [hfix j hja hjb]
  · intro σ _ hσ
    split_ifs with hc
    · obtain ⟨j, hj⟩ : ∃ j, σ j ≠ σ₀ j := by
        by_contra hh; push Not at hh; exact hσ (Equiv.ext hh)
      have hja : j ≠ a.2 := fun e => hj (by rw [e, hc.2.2, h0.2.2])
      have hjb : j ≠ b.2 := fun e => hj (by rw [e, hc.1, h0.1])
      rw [hfix j hja hjb] at hj
      rw [prod_eq_zero (i := j) (by simp [hja, hjb]) (by simp [hj]),
        mul_zero]
    · rw [mul_zero]
  · intro h; exact absurd (mem_univ _) h

theorem prod_erase_erase_ne_zero {n : ℕ} (d : Fin n → ℂ) (i : Fin n)
    (hd : ∀ j, j ≠ i → d j ≠ 0) (a b : Fin n × Fin n) (hi : i = a.2 ∨ i = b.2) :
    ∏ j ∈ (univ.erase b.2).erase a.2, d j ≠ 0 := by
  refine prod_ne_zero_iff.mpr fun j hj => hd j ?_
  have hja := (mem_erase.mp hj).1
  have hjb := (mem_erase.mp (mem_erase.mp hj).2).1
  rcases hi with e | e <;> rw [e] <;> assumption

/-- The diagonal case. -/
theorem adjugate_mul_radical_diag {n : ℕ} (hn : 2 ≤ n) (d : Fin n → ℂ)
    (hdet : ∏ i, d i = 0) (F : Matrix (Fin n) (Fin n) ℂ)
    (hF : ∀ a : Fin n × Fin n, ∑ b : Fin n × Fin n,
      eval (fun p => Matrix.diagonal d p.1 p.2)
        (pderiv a (pderiv b (PEqualNP.Gct.detPoly ℂ n))) * F b.1 b.2 = 0) :
    (Matrix.diagonal d).adjugate * F = 0 ∧ F * (Matrix.diagonal d).adjugate = 0 := by
  set H : Fin n × Fin n → Fin n × Fin n → ℂ := fun a b =>
    eval (fun p => Matrix.diagonal d p.1 p.2)
      (pderiv a (pderiv b (PEqualNP.Gct.detPoly ℂ n))) with hH
  have key : ∀ i, ∏ j ∈ univ.erase i, d j ≠ 0 → (∀ k, F i k = 0) ∧ (∀ k, F k i = 0) := by
    intro i hc
    have hz : d i = 0 := by
      rw [← mul_prod_erase univ d (mem_univ i)] at hdet
      exact (mul_eq_zero.mp hdet).resolve_right hc
    have hd : ∀ j, j ≠ i → d j ≠ 0 := fun j hj =>
      (prod_ne_zero_iff.mp hc) j (mem_erase.mpr ⟨hj, mem_univ _⟩)
    have hv := fun a b h => hess_det_diag_ne_zero d i hz a b h
    -- a row with a single possibly nonzero entry
    have row : ∀ a b₀, (∀ b, b ≠ b₀ → H a b ≠ 0 → False) → H a b₀ ≠ 0 → F b₀.1 b₀.2 = 0 := by
      intro a b₀ hb hne
      have := hF a
      rw [sum_eq_single b₀] at this
      · exact (mul_eq_zero.mp this).resolve_left hne
      · intro b _ hbb
        by_cases hz' : H a b = 0
        · simp only [hH] at hz'; rw [hz', zero_mul]
        · exact (hb b hbb hz').elim
      · intro h; exact absurd (mem_univ _) h
    have off1 : ∀ k, k ≠ i → F i k = 0 := by
      intro k hk
      refine row (k, i) (i, k) ?_ ?_
      · intro b hb hne
        obtain ⟨-, -, hc'⟩ := hv _ _ hne
        rcases hc' with ⟨e, -⟩ | ⟨e1, e2⟩
        · exact hk e
        · exact hb (Prod.ext e2 e1.symm)
      · simp only [hH]
        rw [hess_det_diag_val d (k, i) (i, k) (Equiv.swap i k)
          ⟨by simp, by simpa using hk.symm, by simp⟩
          (fun j h1 h2 => Equiv.swap_apply_of_ne_of_ne h1 h2)]
        exact mul_ne_zero (by simp [Equiv.Perm.sign_swap hk.symm])
          (prod_erase_erase_ne_zero d i hd _ _ (Or.inl rfl))
    have off2 : ∀ k, k ≠ i → F k i = 0 := by
      intro k hk
      refine row (i, k) (k, i) ?_ ?_
      · intro b hb hne
        obtain ⟨h2, hzz, hc'⟩ := hv _ _ hne
        rcases hc' with ⟨e, -⟩ | ⟨e1, e2⟩
        · exact hk e.symm
        · exact hb (Prod.ext e2 e1.symm)
      · simp only [hH]
        rw [hess_det_diag_val d (i, k) (k, i) (Equiv.swap i k)
          ⟨by simp, by simpa using hk, by simp⟩
          (fun j h1 h2 => Equiv.swap_apply_of_ne_of_ne h2 h1)]
        exact mul_ne_zero (by simp [Equiv.Perm.sign_swap hk.symm])
          (prod_erase_erase_ne_zero d i hd _ _ (Or.inr rfl))
    have dia : F i i = 0 := by
      have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
      obtain ⟨k, hk⟩ := exists_ne i
      refine row (k, k) (i, i) ?_ ?_
      · intro b hb hne
        obtain ⟨h2, hzz, hc'⟩ := hv _ _ hne
        simp only at h2 hzz hc'
        rcases hc' with ⟨-, e⟩ | ⟨e1, -⟩
        · rcases hzz with e' | e'
          · exact hk e'.symm
          · exact hb (Prod.ext (e.trans e'.symm) e'.symm)
        · exact h2 e1
      · simp only [hH]
        rw [hess_det_diag_val d (k, k) (i, i) 1 ⟨rfl, hk, rfl⟩ (fun j _ _ => rfl)]
        exact mul_ne_zero (by simp) (prod_erase_erase_ne_zero d i hd _ _ (Or.inr rfl))
    refine ⟨fun k => ?_, fun k => ?_⟩
    · by_cases e : k = i
      · rw [e]; exact dia
      · exact off1 k e
    · by_cases e : k = i
      · rw [e]; exact dia
      · exact off2 k e
  rw [Matrix.adjugate_diagonal]
  refine ⟨Matrix.ext fun i k => ?_, Matrix.ext fun i k => ?_⟩
  · rw [Matrix.diagonal_mul, Matrix.zero_apply]
    by_cases h : ∏ j ∈ univ.erase i, d j = 0
    · rw [h, zero_mul]
    · rw [(key i h).1 k, mul_zero]
  · rw [Matrix.mul_diagonal, Matrix.zero_apply]
    by_cases h : ∏ j ∈ univ.erase k, d j = 0
    · rw [h, mul_zero]
    · rw [(key k h).2 i, zero_mul]

/-- The radical condition transfers along `Y ↦ P * Y * Q` with `det P = det Q = 1`. -/
theorem radical_transfer {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) (hP : P.det = 1)
    (hQ : Q.det = 1) (Y E : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ a : Fin n × Fin n, ∑ b : Fin n × Fin n,
      eval (fun p => (P * Y * Q) p.1 p.2)
        (pderiv a (pderiv b (PEqualNP.Gct.detPoly ℂ n))) * (P * E * Q) b.1 b.2 = 0) :
    ∀ a : Fin n × Fin n, ∑ b : Fin n × Fin n,
      eval (fun p => Y p.1 p.2)
        (pderiv a (pderiv b (PEqualNP.Gct.detPoly ℂ n))) * E b.1 b.2 = 0 := by
  let φ : Fin n × Fin n → MvPolynomial (Fin n × Fin n) ℂ :=
    fun p => ∑ k, ∑ l, C (P p.1 k * Q l p.2) * MvPolynomial.X (k, l)
  have hφd : ∀ p q, pderiv q (φ p) = C (P p.1 q.1 * Q q.2 p.2) := by
    intro p q
    simp only [φ, map_sum, Derivation.leibniz, pderiv_C, pderiv_X,
      smul_eq_mul, Pi.single_apply]
    rw [sum_eq_single q.1, sum_eq_single q.2]
    · simp
    · intro l _ hl
      have : q ≠ (q.1, l) := fun e => hl (by rw [e])
      simp [Ne.symm this]
    · simp
    · intro k _ hk
      refine sum_eq_zero fun l _ => ?_
      have : q ≠ (k, l) := fun e => hk (by rw [e])
      simp [Ne.symm this]
    · simp
  have hbind : bind₁ φ (PEqualNP.Gct.detPoly ℂ n) = PEqualNP.Gct.detPoly ℂ n := by
    have hmat : (bind₁ φ).mapMatrix (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ) =
        P.map C * Matrix.mvPolynomialX (Fin n) (Fin n) ℂ * Q.map C := by
      refine Matrix.ext fun i j => ?_
      simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.mvPolynomialX_apply,
        bind₁_X_right, φ, Matrix.mul_apply, sum_mul]
      rw [sum_comm]
      refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
      simp only [map_mul]; ring
    have hPC : (P.map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ)).det = 1 := by
      have := RingHom.map_det (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) P
      rw [hP, map_one] at this; exact this.symm
    have hQC : (Q.map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ)).det = 1 := by
      have := RingHom.map_det (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) Q
      rw [hQ, map_one] at this; exact this.symm
    simp only [PEqualNP.Gct.detPoly]
    rw [AlgHom.map_det, hmat, Matrix.det_mul, Matrix.det_mul, hPC, hQC, one_mul, mul_one]
  set y : Fin n × Fin n → ℂ := fun p => Y p.1 p.2 with hy
  have hev : (fun p => eval y (φ p)) = fun p => (P * Y * Q) p.1 p.2 := by
    funext p
    simp only [φ, map_sum, map_mul, eval_C, eval_X, Matrix.mul_apply, hy, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  have hHess := hess_bind₁ φ (fun p q => P p.1 q.1 * Q q.2 p.2) hφd
    (PEqualNP.Gct.detPoly ℂ n) y
  rw [hbind, hev] at hHess
  set C' : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ :=
    Matrix.of fun p q => P p.1 q.1 * Q q.2 p.2 with hC'
  set H' := hess (PEqualNP.Gct.detPoly ℂ n) (fun p => (P * Y * Q) p.1 p.2) with hH'
  have hvec : C'.mulVec (fun b => E b.1 b.2) = fun q => (P * E * Q) q.1 q.2 := by
    funext q
    simp only [Matrix.mulVec, dotProduct, hC', Matrix.of_apply, Matrix.mul_apply,
      Fintype.sum_prod_type, sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  have hker : H'.mulVec (fun q => (P * E * Q) q.1 q.2) = 0 := by
    funext a; exact h a
  have hall : (hess (PEqualNP.Gct.detPoly ℂ n) y).mulVec (fun b => E b.1 b.2) = 0 := by
    rw [hHess, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hvec, hker,
      Matrix.mulVec_zero]
  intro a
  exact congrFun hall a

/-- A matrix in the radical of the Hessian of the determinant at a singular matrix `M` is
annihilated by the adjugate of `M` on both sides. The hypothesis `2 ≤ n` is needed: for
`n = 1` the Hessian vanishes while the adjugate is `1`. -/
theorem adjugate_mul_radical {n : ℕ} (hn : 2 ≤ n) (M E : Matrix (Fin n) (Fin n) ℂ)
    (hM : M.det = 0)
    (hE : ∀ a : Fin n × Fin n, ∑ b : Fin n × Fin n,
      MvPolynomial.eval (fun p => M p.1 p.2)
        (MvPolynomial.pderiv a (MvPolynomial.pderiv b (PEqualNP.Gct.detPoly ℂ n))) *
          E b.1 b.2 = 0) :
    M.adjugate * E = 0 ∧ E * M.adjugate = 0 := by
  obtain ⟨L, L', D, hLD⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal M
  set P := (L.map Matrix.TransvectionStruct.toMatrix).prod with hPdef
  set Q := (L'.map Matrix.TransvectionStruct.toMatrix).prod with hQdef
  have hP : P.det = 1 := Matrix.TransvectionStruct.det_toMatrix_prod L
  have hQ : Q.det = 1 := Matrix.TransvectionStruct.det_toMatrix_prod L'
  have hPa : P.adjugate.det = 1 := by rw [Matrix.det_adjugate, hP, one_pow]
  have hQa : Q.adjugate.det = 1 := by rw [Matrix.det_adjugate, hQ, one_pow]
  have hPP : P.adjugate * P = 1 := by rw [Matrix.adjugate_mul, hP, one_smul]
  have hQQ : Q * Q.adjugate = 1 := by rw [Matrix.mul_adjugate, hQ, one_smul]
  have hPP' : P * P.adjugate = 1 := by rw [Matrix.mul_adjugate, hP, one_smul]
  have hQQ' : Q.adjugate * Q = 1 := by rw [Matrix.adjugate_mul, hQ, one_smul]
  have hMD : P.adjugate * Matrix.diagonal D * Q.adjugate = M := by
    rw [← hLD, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul, Matrix.mul_assoc,
      hQQ, Matrix.mul_one]
  have hEE : P.adjugate * (P * E * Q) * Q.adjugate = E := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul, Matrix.mul_assoc,
      hQQ, Matrix.mul_one]
  have hrad := radical_transfer P.adjugate Q.adjugate hPa hQa (Matrix.diagonal D) (P * E * Q)
    (by rw [hMD, hEE]; exact hE)
  have hdet : ∏ i, D i = 0 := by
    rw [← Matrix.det_diagonal, ← hLD, Matrix.det_mul, Matrix.det_mul, hM]; ring
  obtain ⟨h1, h2⟩ := adjugate_mul_radical_diag hn D hdet (P * E * Q) hrad
  have hadj : (Matrix.diagonal D).adjugate = Q.adjugate * M.adjugate * P.adjugate := by
    rw [← hLD, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, Matrix.mul_assoc]
  rw [hadj] at h1 h2
  constructor
  · have : Q * (Q.adjugate * M.adjugate * P.adjugate * (P * E * Q)) * Q.adjugate =
        M.adjugate * E := by
      simp only [← Matrix.mul_assoc]
      rw [hQQ, Matrix.one_mul, Matrix.mul_assoc _ P.adjugate P, hPP, Matrix.mul_one,
        Matrix.mul_assoc _ Q Q.adjugate, hQQ, Matrix.mul_one]
    rw [← this, h1, Matrix.mul_zero, Matrix.zero_mul]
  · have : P.adjugate * (P * E * Q * (Q.adjugate * M.adjugate * P.adjugate)) * P =
        E * M.adjugate := by
      simp only [← Matrix.mul_assoc]
      rw [hPP, Matrix.one_mul, Matrix.mul_assoc _ Q Q.adjugate, hQQ, Matrix.mul_one,
        Matrix.mul_assoc _ P.adjugate P, hPP, Matrix.mul_one]
    rw [← this, h2, Matrix.mul_zero, Matrix.zero_mul]

end PEqualNP.Gct.Helpers
