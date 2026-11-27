import Mathlib
import PEqualNP.Defs
import PEqualNP.Gct.Helpers.Corank

/-! General tools for the polar lift (first part).

The directional derivative of a polynomial at a point, a weighted degree predicate on the support
of a polynomial, the transport of the weighted Bezout statement from `Fin N` to an arbitrary
finite index type (with "the derivative is injective" in place of a nonzero determinant), a
linear form avoiding finitely many nonzero vectors, the normal form of a polynomial of total
degree at most one, and the linear algebra of a corank-one matrix. -/

namespace PEqualNP.Gct.Helpers

open Finset Matrix MvPolynomial

section PointDeriv

variable {σ : Type*} [Fintype σ]

/-- The directional derivative of `P` at the point `z` along `dz`. -/
noncomputable def pd (z dz : σ → ℂ) (P : MvPolynomial σ ℂ) : ℂ :=
  ∑ j, eval z (pderiv j P) * dz j

theorem pd_add (z dz : σ → ℂ) (P Q : MvPolynomial σ ℂ) :
    pd z dz (P + Q) = pd z dz P + pd z dz Q := by
  simp only [pd, map_add, add_mul, sum_add_distrib]

theorem pd_sub (z dz : σ → ℂ) (P Q : MvPolynomial σ ℂ) :
    pd z dz (P - Q) = pd z dz P - pd z dz Q := by
  simp only [pd, map_sub, sub_mul, sum_sub_distrib]

theorem pd_zero (z dz : σ → ℂ) : pd z dz 0 = 0 := by
  simp [pd]

theorem pd_C (z dz : σ → ℂ) (c : ℂ) : pd z dz (C c) = 0 := by
  simp [pd]

theorem pd_one (z dz : σ → ℂ) : pd z dz 1 = 0 := by
  rw [← C_1]; exact pd_C z dz 1

theorem pd_X [DecidableEq σ] (z dz : σ → ℂ) (j : σ) : pd z dz (X j) = dz j := by
  unfold pd
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [pderiv_X, Pi.single_eq_of_ne (Ne.symm hb)]
    simp
  · simp

theorem pd_mul (z dz : σ → ℂ) (P Q : MvPolynomial σ ℂ) :
    pd z dz (P * Q) = eval z P * pd z dz Q + pd z dz P * eval z Q := by
  unfold pd
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Derivation.leibniz]
  simp only [smul_eq_mul, map_add, map_mul]
  ring

theorem pd_sum {ι : Type*} (z dz : σ → ℂ) (s : Finset ι) (f : ι → MvPolynomial σ ℂ) :
    pd z dz (∑ i ∈ s, f i) = ∑ i ∈ s, pd z dz (f i) := by
  unfold pd
  simp only [map_sum, Finset.sum_mul]
  exact Finset.sum_comm

/-- The directional derivative of a matrix product, entrywise. -/
theorem pd_matmul {n : ℕ} (z dz : σ → ℂ) (P Q : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ)) :
    (P * Q).map (pd z dz) =
      P.map (eval z) * Q.map (pd z dz) + P.map (pd z dz) * Q.map (eval z) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, pd_sum, pd_mul,
    sum_add_distrib]

end PointDeriv

section WeightedDegree

variable {σ : Type*} [Fintype σ]

/-- Every monomial of `P` has `w`-weighted degree at most `D`. -/
def WD (w : σ → ℕ) (P : MvPolynomial σ ℂ) (D : ℕ) : Prop :=
  ∀ s ∈ P.support, ∑ j, w j * s j ≤ D

theorem WD_mono {w : σ → ℕ} {P : MvPolynomial σ ℂ} {D D' : ℕ} (h : WD w P D) (hD : D ≤ D') :
    WD w P D' := fun s hs => (h s hs).trans hD

theorem WD_C (w : σ → ℕ) (c : ℂ) (D : ℕ) : WD w (C c) D := by
  classical
  intro s hs
  have h0 : s = 0 := by
    by_contra h
    rw [mem_support_iff, coeff_C] at hs
    exact hs (if_neg (Ne.symm h))
  subst h0
  simp

theorem WD_one (w : σ → ℕ) (D : ℕ) : WD w 1 D := by
  rw [← C_1]; exact WD_C w 1 D

theorem WD_X (w : σ → ℕ) (i : σ) : WD w (X i) (w i) := by
  classical
  intro s hs
  rw [support_X, Finset.mem_singleton] at hs
  subst hs
  simp [Finsupp.single_apply]

theorem WD_mul {w : σ → ℕ} {P Q : MvPolynomial σ ℂ} {D1 D2 : ℕ} (hP : WD w P D1)
    (hQ : WD w Q D2) : WD w (P * Q) (D1 + D2) := by
  classical
  intro s hs
  obtain ⟨s1, h1, s2, h2, rfl⟩ := Finset.mem_add.mp (support_mul P Q hs)
  simp only [Finsupp.coe_add, Pi.add_apply, mul_add, sum_add_distrib]
  exact add_le_add (hP s1 h1) (hQ s2 h2)

theorem WD_C_mul {w : σ → ℕ} {P : MvPolynomial σ ℂ} {D : ℕ} (c : ℂ) (hP : WD w P D) :
    WD w (C c * P) D := by
  have := WD_mul (WD_C w c 0) hP
  rwa [zero_add] at this

theorem WD_add {w : σ → ℕ} {P Q : MvPolynomial σ ℂ} {D : ℕ} (hP : WD w P D)
    (hQ : WD w Q D) : WD w (P + Q) D := by
  classical
  intro s hs
  rcases Finset.mem_union.mp (support_add hs) with h | h
  · exact hP s h
  · exact hQ s h

theorem WD_sub {w : σ → ℕ} {P Q : MvPolynomial σ ℂ} {D : ℕ} (hP : WD w P D)
    (hQ : WD w Q D) : WD w (P - Q) D := by
  classical
  intro s hs
  rcases Finset.mem_union.mp (support_sub _ P Q hs) with h | h
  · exact hP s h
  · exact hQ s h

theorem WD_sum {ι : Type*} {w : σ → ℕ} {t : Finset ι} {f : ι → MvPolynomial σ ℂ} {D : ℕ}
    (hf : ∀ i ∈ t, WD w (f i) D) : WD w (∑ i ∈ t, f i) D := by
  classical
  intro s hs
  obtain ⟨i, hi, hsi⟩ := Finset.mem_biUnion.mp (support_sum hs)
  exact hf i hi s hsi

end WeightedDegree

/-- The weighted Bezout statement over `Fin N` gives the same bound over any finite index type,
with nondegeneracy stated as injectivity of the derivative. -/
theorem bezout_of_fin
    (hB : ∀ (N : ℕ) (F : Fin N → MvPolynomial (Fin N) ℂ) (w D : Fin N → ℕ), (∀ i, ∀ s ∈ (F i).support, ∑ j, w j * s j ≤ D i) → ∀ S : Finset (Fin N → ℂ), (∀ x ∈ S, (∀ i, MvPolynomial.eval x (F i) = 0) ∧ (Matrix.of fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (F i))).det ≠ 0) → S.card * ∏ j, w j ≤ ∏ i, D i)
    {τ : Type} [Fintype τ] [DecidableEq τ] (F : τ → MvPolynomial τ ℂ) (w D : τ → ℕ)
    (hw : ∀ i, WD w (F i) (D i)) (S : Finset (τ → ℂ))
    (hS : ∀ z ∈ S, (∀ i, eval z (F i) = 0) ∧
      ∀ dz : τ → ℂ, (∀ i, pd z dz (F i) = 0) → dz = 0) :
    S.card * ∏ j, w j ≤ ∏ i, D i := by
  classical
  let e := Fintype.equivFin τ
  have h1 : ∀ i, ∀ s ∈ (rename e (F (e.symm i))).support,
      ∑ j, w (e.symm j) * s j ≤ D (e.symm i) := by
    intro i s hs
    rw [support_rename_of_injective e.injective, Finset.mem_image] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    refine le_trans (le_of_eq ?_) (hw (e.symm i) s' hs')
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Equiv.symm_apply_apply, Finsupp.mapDomain_apply_of_injective e.injective]
  have key := hB (Fintype.card τ) (fun i => rename e (F (e.symm i))) (fun j => w (e.symm j))
    (fun i => D (e.symm i)) h1 (S.image fun z => z ∘ e.symm) (by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨h0, h2⟩ := hS z hz
      have hcomp : (z ∘ e.symm) ∘ e = z := by
        funext t
        simp
      refine ⟨fun i => ?_, ?_⟩
      · rw [eval_rename, hcomp]
        exact h0 _
      · intro hdet
        obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
        apply hv
        have hve : v ∘ e = 0 := h2 (v ∘ e) fun t => by
          have h3 := congrFun hMv (e t)
          simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply,
            Equiv.symm_apply_apply] at h3
          rw [← Equiv.sum_comp e] at h3
          rw [← h3]
          unfold pd
          refine Finset.sum_congr rfl fun t' _ => ?_
          rw [pderiv_rename e.injective, eval_rename, hcomp]
          rfl
        funext j
        have h4 := congrFun hve (e.symm j)
        simpa using h4)
  rw [Finset.card_image_of_injective, Equiv.prod_comp e.symm w, Equiv.prod_comp e.symm D] at key
  · exact key
  · intro z1 z2 h
    funext t
    have h5 := congrFun h (e t)
    simpa using h5

/-- A linear form that does not vanish on any of finitely many nonzero vectors. -/
theorem exists_dot_ne_zero {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℂ)
    (hf : ∀ i ∈ s, f i ≠ 0) : ∃ lam : Fin n → ℂ, ∀ i ∈ s, lam ⬝ᵥ f i ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨lam, hlam⟩ := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hfa : f a ≠ 0 := hf a (Finset.mem_insert_self a s)
    obtain ⟨k, hk⟩ : ∃ k, f a k ≠ 0 := Function.ne_iff.mp hfa
    obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset
      ((insert a s).image fun i => -(lam ⬝ᵥ f i) / (f i k))
    refine ⟨lam + t • Pi.single k 1, fun i hi h0 => ?_⟩
    have hexp : (lam + t • Pi.single k 1) ⬝ᵥ f i = lam ⬝ᵥ f i + t * f i k := by
      rw [add_dotProduct, smul_dotProduct, single_one_dotProduct, smul_eq_mul]
    rw [hexp] at h0
    by_cases hik : f i k = 0
    · rw [hik, mul_zero, add_zero] at h0
      rcases Finset.mem_insert.mp hi with rfl | his
      · exact hk hik
      · exact hlam i his h0
    · apply ht
      refine Finset.mem_image.mpr ⟨i, hi, ?_⟩
      rw [div_eq_iff hik]
      linear_combination (-1 : ℂ) * h0

/-- A polynomial of total degree at most one is a constant plus a linear form. -/
theorem affine_normal_form {σ : Type*} [Fintype σ] [DecidableEq σ] (P : MvPolynomial σ ℂ)
    (hP : P.totalDegree ≤ 1) :
    P = C (P.coeff 0) + ∑ l, C (P.coeff (Finsupp.single l 1)) * X l := by
  ext m
  rw [MvPolynomial.coeff_add, coeff_C, MvPolynomial.coeff_sum]
  by_cases hm0 : m = 0
  · subst hm0
    rw [if_pos rfl, Finset.sum_eq_zero, add_zero]
    intro l _
    rw [coeff_C_mul, coeff_X', if_neg, mul_zero]
    intro h
    have h1 := DFunLike.congr_fun h l
    simp at h1
  by_cases hms : ∃ l, m = Finsupp.single l 1
  · obtain ⟨l, rfl⟩ := hms
    rw [if_neg (Ne.symm hm0), zero_add, Finset.sum_eq_single l]
    · rw [coeff_C_mul, coeff_X', if_pos rfl, mul_one]
    · intro b _ hb
      rw [coeff_C_mul, coeff_X', if_neg, mul_zero]
      intro h
      exact hb (Finsupp.single_left_injective one_ne_zero h)
    · simp
  · have hc : P.coeff m = 0 := by
      by_contra hc
      have hm := mem_support_iff.mpr hc
      have hsum : ∑ i, m i ≤ 1 := by
        have h1 := le_totalDegree hm
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at h1
        exact h1.trans hP
      obtain ⟨l, hl⟩ : ∃ l, m l ≠ 0 := by
        by_contra h
        push Not at h
        exact hm0 (Finsupp.ext h)
      apply hms
      refine ⟨l, ?_⟩
      ext i
      by_cases hil : i = l
      · subst hil
        have h2 := Finset.single_le_sum (f := fun i => m i) (fun i _ => Nat.zero_le _)
          (Finset.mem_univ i)
        rw [Finsupp.single_eq_same]
        omega
      · have h2 : m l + m i ≤ ∑ j, m j := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
          have h3 := Finset.single_le_sum (f := fun i => m i) (fun i _ => Nat.zero_le _)
            (Finset.mem_erase.mpr ⟨hil, Finset.mem_univ i⟩)
          omega
        have h4 : Finsupp.single l 1 i = 0 := by
          simp [Finsupp.single_apply, Ne.symm hil]
        rw [h4]
        omega
    rw [hc, if_neg (Ne.symm hm0), zero_add]
    symm
    apply Finset.sum_eq_zero
    intro l _
    rw [coeff_C_mul, coeff_X', if_neg (fun h => hms ⟨l, h.symm⟩), mul_zero]

/-- Evaluation of a polynomial of total degree at most one. -/
theorem eval_affine {σ : Type*} [Fintype σ] [DecidableEq σ] (P : MvPolynomial σ ℂ)
    (hP : P.totalDegree ≤ 1) (x : σ → ℂ) :
    eval x P = P.coeff 0 + ∑ l, P.coeff (Finsupp.single l 1) * x l := by
  conv_lhs => rw [affine_normal_form P hP]
  simp

/-- A partial derivative of a polynomial of total degree at most one is a constant. -/
theorem pderiv_affine {σ : Type*} [Fintype σ] [DecidableEq σ] (P : MvPolynomial σ ℂ)
    (hP : P.totalDegree ≤ 1) (l : σ) :
    pderiv l P = C (P.coeff (Finsupp.single l 1)) := by
  conv_lhs => rw [affine_normal_form P hP]
  rw [map_add, pderiv_C, zero_add, map_sum, Finset.sum_eq_single l]
  · rw [pderiv_C_mul, pderiv_X_self, mul_one]
  · intro b _ hb
    rw [pderiv_C_mul, pderiv_X, Pi.single_eq_of_ne hb, mul_zero]
  · simp

/-- If `adj M ≠ 0`, every kernel vector of `M` is a multiple of a fixed nonzero one. -/
theorem ker_span_of_adj {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hadj : M.adjugate ≠ 0)
    (u : Fin n → ℂ) (hu : u ≠ 0) (hMu : M *ᵥ u = 0) (y : Fin n → ℂ) (hy : M *ᵥ y = 0) :
    ∃ τ : ℂ, y = τ • u := by
  obtain ⟨g, hg⟩ := finrank_le_one_iff.mp (ker_finrank_le_one M hadj)
  obtain ⟨a, ha⟩ := hg ⟨u, by simpa using hMu⟩
  obtain ⟨b, hb⟩ := hg ⟨y, by simpa using hy⟩
  have ha' : a • (g : Fin n → ℂ) = u := congrArg Subtype.val ha
  have hb' : b • (g : Fin n → ℂ) = y := congrArg Subtype.val hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hu (by rw [← ha', zero_smul])
  refine ⟨b / a, ?_⟩
  rw [← ha', ← hb', smul_smul, div_mul_cancel₀ _ ha0]

/-- The left kernel version of `ker_span_of_adj`. -/
theorem leftKer_span_of_adj {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hadj : M.adjugate ≠ 0)
    (v : Fin n → ℂ) (hv : v ≠ 0) (hvM : v ᵥ* M = 0) (y : Fin n → ℂ) (hy : y ᵥ* M = 0) :
    ∃ τ : ℂ, y = τ • v := by
  have hadjT : Mᵀ.adjugate ≠ 0 := by
    intro h
    apply hadj
    have h1 := adjugate_transpose M
    rw [h] at h1
    exact transpose_eq_zero.mp h1
  exact ker_span_of_adj Mᵀ hadjT v hv (by rw [mulVec_transpose]; exact hvM) y
    (by rw [mulVec_transpose]; exact hy)

/-- The derivative of the adjugate at a corank-one point, up to one unknown scalar: if
`adj M = c u vᵀ`, `dN` satisfies the two differentiated adjugate identities, and `du`, `dv` are
the first-order variations of the kernel vectors, then
`dN = c du vᵀ + c u dvᵀ + κ u vᵀ`, stated through traces against an arbitrary matrix. -/
theorem trace_dN_mul {n : ℕ} (M N dN dA : Matrix (Fin n) (Fin n) ℂ) (u v du dv : Fin n → ℂ)
    (c : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) (hadj : M.adjugate ≠ 0)
    (hMu : M *ᵥ u = 0) (hvM : v ᵥ* M = 0) (hN : N = c • vecMulVec u v)
    (h1 : M * dN + dA * N = 0) (h2 : N * dA + dN * M = 0)
    (hdu : M *ᵥ du + dA *ᵥ u = 0) (hdv : dv ᵥ* M + v ᵥ* dA = 0) :
    ∃ κ : ℂ, ∀ B : Matrix (Fin n) (Fin n) ℂ, trace (dN * B) =
      κ * (v ⬝ᵥ (B *ᵥ u)) + c * (dv ⬝ᵥ (B *ᵥ u) + v ⬝ᵥ (B *ᵥ du)) := by
  have hz1 : ∀ w : Fin n → ℂ, vecMulVec (0 : Fin n → ℂ) w = 0 := fun w => by
    ext i j; simp [vecMulVec_apply]
  have hz2 : ∀ w : Fin n → ℂ, vecMulVec w (0 : Fin n → ℂ) = 0 := fun w => by
    ext i j; simp [vecMulVec_apply]
  have hn1 : ∀ a w : Fin n → ℂ, vecMulVec (-a) w = -vecMulVec a w := fun a w => by
    ext i j; simp [vecMulVec_apply]
  have hn2 : ∀ a w : Fin n → ℂ, vecMulVec a (-w) = -vecMulVec a w := fun a w => by
    ext i j; simp [vecMulVec_apply]
  have e1 : M *ᵥ du = -(dA *ᵥ u) := eq_neg_of_add_eq_zero_left hdu
  have e2 : dv ᵥ* M = -(v ᵥ* dA) := eq_neg_of_add_eq_zero_left hdv
  have e3 : M * dN = -(dA * N) := eq_neg_of_add_eq_zero_left h1
  have e4 : dN * M = -(N * dA) := eq_neg_of_add_eq_zero_right h2
  set R : Matrix (Fin n) (Fin n) ℂ := dN - c • vecMulVec du v - c • vecMulVec u dv with hR
  have hMR : M * R = 0 := by
    rw [hR, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, mul_vecMulVec,
      mul_vecMulVec, e3, hN, Matrix.mul_smul, mul_vecMulVec, e1, hMu, hn1, hz1]
    simp
  have hRM : R * M = 0 := by
    rw [hR, Matrix.sub_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, vecMulVec_mul,
      vecMulVec_mul, e4, hN, Matrix.smul_mul, vecMulVec_mul, e2, hvM, hn2, hz2]
    simp
  have hcol : ∀ j, M *ᵥ (fun i => R i j) = 0 := by
    intro j
    funext i
    simpa [Matrix.mul_apply, mulVec, dotProduct] using congrFun (congrFun hMR i) j
  choose τ hτ using fun j => ker_span_of_adj M hadj u hu hMu _ (hcol j)
  have hRij : ∀ i j, R i j = τ j * u i := fun i j => by
    have h3 := congrFun (hτ j) i
    simpa using h3
  obtain ⟨i0, hi0⟩ : ∃ i, u i ≠ 0 := Function.ne_iff.mp hu
  have hτM : τ ᵥ* M = 0 := by
    funext j
    have h3 := congrFun (congrFun hRM i0) j
    simp only [Matrix.mul_apply, hRij, Matrix.zero_apply] at h3
    have h4 : u i0 * (τ ᵥ* M) j = 0 := by
      rw [← h3]
      simp only [vecMul, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    exact (mul_eq_zero.mp h4).resolve_left hi0
  obtain ⟨κ, hκ⟩ := leftKer_span_of_adj M hadj v hv hvM τ hτM
  have hdN : dN = κ • vecMulVec u v + c • vecMulVec du v + c • vecMulVec u dv := by
    have h5 : R = κ • vecMulVec u v := by
      ext i j
      rw [hRij, hκ]
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, vecMulVec_apply]
      ring
    rw [← h5, hR]
    abel
  refine ⟨κ, fun B => ?_⟩
  have t1 : ∀ a b : Fin n → ℂ, trace (vecMulVec a b * B) = b ⬝ᵥ (B *ᵥ a) := fun a b => by
    rw [vecMulVec_mul, trace_vecMulVec, dotProduct_mulVec, dotProduct_comm]
  rw [hdN, Matrix.add_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul,
    trace_add, trace_add, trace_smul, trace_smul, trace_smul, t1, t1, t1]
  simp only [smul_eq_mul]
  ring

/-- The directional derivative of a determinant is the trace of the adjugate times the
entrywise directional derivative. -/
theorem pd_det {n d : ℕ} (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin d) ℂ))
    (x dx : Fin d → ℂ) :
    pd x dx A.det = trace ((A.map (eval x)).adjugate * A.map (pd x dx)) := by
  have hmap : A.map (pd x dx) =
      ∑ l, dx l • (A.map (pderiv l)).map (eval x) := by
    ext i j
    simp only [Matrix.map_apply, pd, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
  rw [hmap, Matrix.mul_sum, trace_sum]
  unfold pd
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [eval_pderiv_det, Matrix.mul_smul, trace_smul, smul_eq_mul, mul_comm]

/-- The differentiated adjugate identities at a point where the directional derivative of the
determinant vanishes, and the directional derivative of a partial derivative of the determinant
when the entries have constant partial derivatives. -/
theorem pd_polar {n d : ℕ} (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin d) ℂ))
    (Al : Fin d → Matrix (Fin n) (Fin n) ℂ) (hAl : ∀ l i j, pderiv l (A i j) = C (Al l i j))
    (x dx : Fin d → ℂ) (hG : pd x dx A.det = 0) :
    (A.map (eval x)) * A.adjugate.map (pd x dx) +
        A.map (pd x dx) * (A.map (eval x)).adjugate = 0 ∧
      (A.map (eval x)).adjugate * A.map (pd x dx) +
        A.adjugate.map (pd x dx) * (A.map (eval x)) = 0 ∧
      ∀ l, pd x dx (pderiv l A.det) = trace (A.adjugate.map (pd x dx) * Al l) := by
  have hadj : A.adjugate.map (eval x) = (A.map (eval x)).adjugate := by
    have h := RingHom.map_adjugate (MvPolynomial.eval x) A
    simp only [RingHom.mapMatrix_apply] at h
    exact h
  have hzero : ((A.det • (1 : Matrix (Fin n) (Fin n) (MvPolynomial (Fin d) ℂ))).map
      (pd x dx)) = 0 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Matrix.zero_apply]
    by_cases hij : i = j
    · rw [if_pos hij, mul_one]; exact hG
    · rw [if_neg hij, mul_zero]; exact pd_zero x dx
  refine ⟨?_, ?_, fun l => ?_⟩
  · have h1 := pd_matmul x dx A A.adjugate
    rw [mul_adjugate, hzero, hadj] at h1
    exact h1.symm
  · have h1 := pd_matmul x dx A.adjugate A
    rw [adjugate_mul, hzero, hadj] at h1
    exact h1.symm
  · have hmap : A.map (pderiv l) = (Al l).map C := by
      ext i j
      simp only [Matrix.map_apply, hAl]
    rw [derivation_det, hmap]
    simp only [trace, diag_apply, Matrix.mul_apply, Matrix.map_apply, pd_sum, pd_mul, pd_C,
      eval_C, mul_zero, zero_add]

end PEqualNP.Gct.Helpers
