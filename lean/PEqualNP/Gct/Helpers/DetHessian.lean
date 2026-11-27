import PEqualNP.Defs
import PEqualNP.Gct.Helpers.PermHessian
import PEqualNP.Gct.Helpers.ChainRule

/-! The Hessian of the determinant has rank at most `2n` at a singular matrix. Helper for
L-gct-012. -/

namespace PEqualNP.Gct.Helpers

open Finset MvPolynomial

/-- The value of the second derivative of the determinant, as a sum over permutations. -/
theorem hess_det_sum {n : ℕ} (x : Fin n × Fin n → ℂ) (a b : Fin n × Fin n) :
    eval x (pderiv a (pderiv b (PEqualNP.Gct.detPoly ℂ n))) =
      ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        (if σ b.2 = b.1 ∧ a.2 ≠ b.2 ∧ σ a.2 = a.1 then
          ∏ i ∈ (univ.erase b.2).erase a.2, x (σ i, i) else 0) := by
  simp only [PEqualNP.Gct.detPoly, Matrix.det_apply, Matrix.mvPolynomialX_apply, map_sum]
  refine sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, map_zsmul, map_zsmul, map_zsmul, zsmul_eq_mul, pderiv_perm_mon]
  congr 1
  by_cases hb : σ b.2 = b.1
  · rw [if_pos ⟨mem_univ _, hb⟩, pderiv_perm_mon]
    by_cases ha : a.2 ≠ b.2 ∧ σ a.2 = a.1
    · rw [if_pos ⟨mem_erase.mpr ⟨ha.1, mem_univ _⟩, ha.2⟩,
        if_pos (show σ b.2 = b.1 ∧ a.2 ≠ b.2 ∧ σ a.2 = a.1 from ⟨hb, ha.1, ha.2⟩), eval_prod]
      simp
    · rw [if_neg, map_zero, if_neg]
      · rintro ⟨_, h1, h2⟩; exact ha ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ha ⟨(mem_erase.mp h1).1, h2⟩
  · rw [if_neg (fun h => hb h.2), map_zero, map_zero, if_neg (fun h => hb h.1)]

/-- The zero pattern of the Hessian of the determinant at a diagonal matrix with a zero on the
diagonal at `z`. -/
theorem hess_det_diag_ne_zero {n : ℕ} (d : Fin n → ℂ) (z : Fin n) (hz : d z = 0)
    (a b : Fin n × Fin n)
    (h : eval (fun p => Matrix.diagonal d p.1 p.2)
      (pderiv a (pderiv b (PEqualNP.Gct.detPoly ℂ n))) ≠ 0) :
    a.2 ≠ b.2 ∧ (z = a.2 ∨ z = b.2) ∧
      ((a.1 = a.2 ∧ b.1 = b.2) ∨ (a.1 = b.2 ∧ b.1 = a.2)) := by
  rw [hess_det_sum] at h
  obtain ⟨σ, -, hσ⟩ := exists_ne_zero_of_sum_ne_zero h
  have hσ' := right_ne_zero_of_mul hσ
  split_ifs at hσ' with hc
  · obtain ⟨hb, h2, ha⟩ := hc
    have hfix : ∀ i, i ≠ a.2 → i ≠ b.2 → σ i = i ∧ d i ≠ 0 := by
      intro i hia hib
      have hi : i ∈ (univ.erase b.2).erase a.2 := by simp [hia, hib]
      have := (prod_ne_zero_iff.mp hσ') i hi
      by_cases e : σ i = i
      · refine ⟨e, ?_⟩
        simpa [Matrix.diagonal_apply, e] using this
      · exact absurd (by simp [Matrix.diagonal_apply, e]) this
    refine ⟨h2, ?_, ?_⟩
    · by_contra hz'
      push_neg at hz'
      exact (hfix z hz'.1 hz'.2).2 hz
    · have hb1 : b.1 = a.2 ∨ b.1 = b.2 := by
        by_contra hh; push_neg at hh
        have := (hfix b.1 hh.1 hh.2).1
        rw [← hb] at this
        exact hh.2 (by rw [← hb]; exact σ.injective this)
      have ha1 : a.1 = a.2 ∨ a.1 = b.2 := by
        by_contra hh; push_neg at hh
        have := (hfix a.1 hh.1 hh.2).1
        rw [← ha] at this
        exact hh.1 (by rw [← ha]; exact σ.injective this)
      have hne : a.1 ≠ b.1 := fun e => h2 (σ.injective (by rw [ha, hb, e]))
      rcases ha1 with ha1 | ha1 <;> rcases hb1 with hb1 | hb1
      · exact absurd (ha1.trans hb1.symm) hne
      · exact Or.inl ⟨ha1, hb1⟩
      · exact Or.inr ⟨ha1, hb1⟩
      · exact absurd (ha1.trans hb1.symm) hne
  · exact absurd rfl hσ'


theorem col_eq_single {ι : Type} [DecidableEq ι] (H : Matrix ι ι ℂ) (b a₀ : ι)
    (h : ∀ a, a ≠ a₀ → H a b = 0) : H.col b = H a₀ b • Pi.single a₀ 1 := by
  funext a
  by_cases e : a = a₀
  · subst e; simp [Matrix.col]
  · simp [Matrix.col, e, h a e]

/-- At a diagonal matrix with a zero on the diagonal, the Hessian of the determinant has rank at
most `2n`. -/
theorem rank_hess_det_diag {n : ℕ} (d : Fin n → ℂ) (z : Fin n) (hz : d z = 0) :
    (hess (PEqualNP.Gct.detPoly ℂ n) (fun p => Matrix.diagonal d p.1 p.2)).rank ≤ 2 * n := by
  set H := hess (PEqualNP.Gct.detPoly ℂ n) (fun p => Matrix.diagonal d p.1 p.2) with hH
  have hv : ∀ a b, H a b ≠ 0 → a.2 ≠ b.2 ∧ (z = a.2 ∨ z = b.2) ∧
      ((a.1 = a.2 ∧ b.1 = b.2) ∨ (a.1 = b.2 ∧ b.1 = a.2)) :=
    fun a b h => hess_det_diag_ne_zero d z hz a b h
  set A : Finset (Fin n × Fin n → ℂ) := univ.image fun k => Pi.single (k, z) 1 with hA
  set B : Finset (Fin n × Fin n → ℂ) := univ.image fun k => Pi.single (z, k) 1 with hB
  set S : Finset (Fin n × Fin n → ℂ) := insert (H.col (z, z)) (A ∪ B) with hS
  have memS : ∀ v ∈ S, v ∈ Submodule.span ℂ (S : Set (Fin n × Fin n → ℂ)) :=
    fun v hv => Submodule.subset_span hv
  have colmem : ∀ b, H.col b ∈ Submodule.span ℂ (S : Set (Fin n × Fin n → ℂ)) := by
    intro b
    obtain ⟨b1, b2⟩ := b
    by_cases hbz : (b1, b2) = (z, z)
    · rw [hbz]; exact memS _ (mem_insert_self _ _)
    by_cases hd : b1 = b2
    · subst hd
      have hb1 : b1 ≠ z := fun e => hbz (by rw [e])
      rw [col_eq_single H (b1, b1) (z, z)]
      · refine Submodule.smul_mem _ _ (memS _ ?_)
        exact mem_insert_of_mem (mem_union_left _ (mem_image.mpr ⟨z, mem_univ _, rfl⟩))
      · intro a ha
        by_contra hne
        obtain ⟨h2, hz', hc⟩ := hv a _ hne
        rcases hc with ⟨e1, -⟩ | ⟨e1, e2⟩
        · rcases hz' with e | e
          · exact ha (Prod.ext (by simp [e1, ← e]) (by simp [← e]))
          · exact hb1 e.symm
        · rcases hz' with e | e
          · exact hb1 (by simpa [← e] using e2)
          · exact hb1 e.symm
    · rw [col_eq_single H (b1, b2) (b2, b1)]
      · by_cases hzz : H (b2, b1) (b1, b2) = 0
        · rw [hzz, zero_smul]; exact Submodule.zero_mem _
        obtain ⟨-, hz', -⟩ := hv _ _ hzz
        refine Submodule.smul_mem _ _ (memS _ ?_)
        rcases hz' with e | e
        · simp only at e
          subst e
          exact mem_insert_of_mem (mem_union_left _ (mem_image.mpr ⟨b2, mem_univ _, rfl⟩))
        · simp only at e
          subst e
          exact mem_insert_of_mem (mem_union_right _ (mem_image.mpr ⟨b1, mem_univ _, rfl⟩))
      · intro a ha
        by_contra hne
        obtain ⟨-, -, hc⟩ := hv a _ hne
        rcases hc with ⟨-, e2⟩ | ⟨e1, e2⟩
        · exact hd (by simpa using e2)
        · exact ha (Prod.ext (by simpa using e1) (by simpa using e2.symm))
  have hcard : S.card ≤ 2 * n := by
    have hAc : A.card ≤ n := card_image_le.trans (by simp)
    have hBc : B.card ≤ n := card_image_le.trans (by simp)
    have hI : 1 ≤ (A ∩ B).card := by
      apply card_pos.mpr
      exact ⟨Pi.single (z, z) 1, mem_inter.mpr ⟨mem_image.mpr ⟨z, mem_univ _, rfl⟩,
        mem_image.mpr ⟨z, mem_univ _, rfl⟩⟩⟩
    have hU := card_union_add_card_inter A B
    have := card_insert_le (H.col (z, z)) (A ∪ B)
    rw [hS]
    omega
  rw [Matrix.rank_eq_finrank_span_cols]
  calc Module.finrank ℂ (Submodule.span ℂ (Set.range H.col))
      ≤ Module.finrank ℂ (Submodule.span ℂ (S : Set (Fin n × Fin n → ℂ))) :=
        Submodule.finrank_mono (Submodule.span_le.mpr (Set.range_subset_iff.mpr colmem))
    _ ≤ S.card := finrank_span_finset_le_card S
    _ ≤ 2 * n := hcard


/-- At every singular matrix the Hessian of the determinant has rank at most `2n`. -/
theorem rank_hess_det_singular {n : ℕ} (x : Fin n × Fin n → ℂ)
    (h0 : eval x (PEqualNP.Gct.detPoly ℂ n) = 0) :
    (hess (PEqualNP.Gct.detPoly ℂ n) x).rank ≤ 2 * n := by
  set Xm : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => x (i, j) with hXdef
  have hX : Xm.det = 0 := by
    rw [hXdef, ← Matrix.eval_det_mvPolynomialX]; exact h0
  obtain ⟨L, L', D, hLD⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal Xm
  set P := (L.map Matrix.TransvectionStruct.toMatrix).prod with hPdef
  set Q := (L'.map Matrix.TransvectionStruct.toMatrix).prod with hQdef
  have hP : P.det = 1 := Matrix.TransvectionStruct.det_toMatrix_prod L
  have hQ : Q.det = 1 := Matrix.TransvectionStruct.det_toMatrix_prod L'
  obtain ⟨z, -, hz⟩ : ∃ z ∈ univ, D z = 0 := by
    have : (Matrix.diagonal D).det = 0 := by
      rw [← hLD, Matrix.det_mul, Matrix.det_mul, hX]; ring
    rwa [Matrix.det_diagonal, prod_eq_zero_iff] at this
  let φ : Fin n × Fin n → MvPolynomial (Fin n × Fin n) ℂ :=
    fun p => ∑ k, ∑ l, C (P p.1 k * Q l p.2) * MvPolynomial.X (k, l)
  have hφd : ∀ p q, pderiv q (φ p) = C (P p.1 q.1 * Q q.2 p.2) := by
    intro p q
    simp only [φ, map_sum, Derivation.leibniz, pderiv_C, smul_zero, add_zero, pderiv_X,
      smul_eq_mul, Pi.single_apply]
    rw [sum_eq_single q.1, sum_eq_single q.2]
    · simp
    · intro l _ hl
      have : q ≠ (q.1, l) := fun e => hl (by rw [e])
      simp [this, Ne.symm this]
    · simp
    · intro k _ hk
      refine sum_eq_zero fun l _ => ?_
      have : q ≠ (k, l) := fun e => hk (by rw [e])
      simp [this, Ne.symm this]
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
  have hev : (fun p => eval x (φ p)) = fun p => Matrix.diagonal D p.1 p.2 := by
    funext p
    rw [← hLD]
    simp only [φ, map_sum, map_mul, eval_C, eval_X, Matrix.mul_apply, hXdef, Matrix.of_apply,
      sum_mul]
    rw [sum_comm]
    exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
  calc (hess (PEqualNP.Gct.detPoly ℂ n) x).rank
      = (hess (bind₁ φ (PEqualNP.Gct.detPoly ℂ n)) x).rank := by rw [hbind]
    _ ≤ (hess (PEqualNP.Gct.detPoly ℂ n) (fun p => eval x (φ p))).rank :=
        rank_hess_bind₁_le φ (fun p q => P p.1 q.1 * Q q.2 p.2) hφd _ x
    _ ≤ 2 * n := by rw [hev]; exact rank_hess_det_diag D z hz

end PEqualNP.Gct.Helpers
