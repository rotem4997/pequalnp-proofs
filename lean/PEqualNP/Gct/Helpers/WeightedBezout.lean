import PEqualNP.Gct.Helpers.ChainRule

/-! Weighted Bezout from the plain degree bound, by a power substitution. Helper for L-gct-039.

Give variable `j` the weight `w j`. Substituting `X j ^ (q * w j) + c` for `X j` turns a system
of weighted degrees `D i` into one of plain degrees `q * D i`, and every nondegenerate zero of
the old system into `∏ j, q * w j` nondegenerate zeros of the new one. The plain bound applied
to the new system, with `q` growing, gives the weighted bound. -/

namespace PEqualNP.Gct.Helpers

open MvPolynomial Finset

/-- The substitution `X j ↦ X j ^ e j + c`. -/
noncomputable def powShift {N : ℕ} (e : Fin N → ℕ) (c : ℂ) (j : Fin N) :
    MvPolynomial (Fin N) ℂ :=
  X j ^ e j + C c

theorem totalDegree_powShift_le {N : ℕ} (e : Fin N → ℕ) (c : ℂ) (j : Fin N) :
    (powShift e c j).totalDegree ≤ e j := by
  unfold powShift
  refine (totalDegree_add _ _).trans ?_
  rw [totalDegree_C, totalDegree_X_pow]
  simp

/-- The substitution turns weighted degree (weights `e`) into plain degree. -/
theorem totalDegree_bind₁_powShift_le {N : ℕ} (e : Fin N → ℕ) (c : ℂ)
    (p : MvPolynomial (Fin N) ℂ) (B : ℕ) (hB : ∀ s ∈ p.support, ∑ j, e j * s j ≤ B) :
    (bind₁ (powShift e c) p).totalDegree ≤ B := by
  have h : bind₁ (powShift e c) p =
      ∑ s ∈ p.support, C (p.coeff s) * ∏ j, powShift e c j ^ s j := by
    rw [bind₁, aeval_def, eval₂_eq']
    rfl
  rw [h]
  refine totalDegree_finsetSum_le fun s hs => ?_
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ((Finset.sum_le_sum fun j _ => ?_).trans (hB s hs))
  refine (totalDegree_pow _ _).trans ?_
  exact (Nat.mul_le_mul_left _ (totalDegree_powShift_le e c j)).trans (Nat.mul_comm _ _).le

theorem eval_bind₁_powShift {N : ℕ} (e : Fin N → ℕ) (c : ℂ) (z : Fin N → ℂ)
    (p : MvPolynomial (Fin N) ℂ) :
    eval z (bind₁ (powShift e c) p) = eval (fun j => z j ^ e j + c) p := by
  have h : eval z (bind₁ (powShift e c) p) = eval (fun j => eval z (powShift e c j)) p := by
    show eval₂Hom (RingHom.id ℂ) z _ = _
    rw [eval₂Hom_bind₁]
    rfl
  rw [h]
  simp [powShift]

theorem eval_pderiv_powShift {N : ℕ} (e : Fin N → ℕ) (c : ℂ) (z : Fin N → ℂ) (b k : Fin N) :
    eval z (pderiv b (powShift e c k)) = if k = b then (e k : ℂ) * z k ^ (e k - 1) else 0 := by
  unfold powShift
  rw [map_add, pderiv_C, add_zero, pderiv_pow, pderiv_X]
  by_cases h : k = b
  · subst h; simp
  · simp [h]

/-- The Jacobian of the substituted system is the old Jacobian at the image point times a
diagonal matrix. -/
theorem jac_bind₁_powShift {N : ℕ} (e : Fin N → ℕ) (c : ℂ)
    (F : Fin N → MvPolynomial (Fin N) ℂ) (z : Fin N → ℂ) :
    (Matrix.of fun i j => eval z (pderiv j (bind₁ (powShift e c) (F i)))) =
      (Matrix.of fun i j => eval (fun j => z j ^ e j + c) (pderiv j (F i))) *
        Matrix.diagonal (fun k => (e k : ℂ) * z k ^ (e k - 1)) := by
  ext i b
  rw [Matrix.mul_diagonal]
  simp only [Matrix.of_apply, pderiv_bind₁, map_sum, map_mul, eval_bind₁_powShift,
    eval_pderiv_powShift]
  simp

/-- One step: the plain bound applied to the substituted system. -/
theorem weighted_step
    (hA : ∀ (N : ℕ) (F : Fin N → MvPolynomial (Fin N) ℂ) (D : Fin N → ℕ), (∀ i, (F i).totalDegree ≤ D i) → ∀ S : Finset (Fin N → ℂ), (∀ x ∈ S, (∀ i, MvPolynomial.eval x (F i) = 0) ∧ (Matrix.of fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (F i))).det ≠ 0) → S.card ≤ ∏ i, (D i + 1))
    (N : ℕ) (F : Fin N → MvPolynomial (Fin N) ℂ) (w D : Fin N → ℕ)
    (hw : ∀ i, ∀ s ∈ (F i).support, ∑ j, w j * s j ≤ D i) (S : Finset (Fin N → ℂ))
    (hS : ∀ x ∈ S, (∀ i, MvPolynomial.eval x (F i) = 0) ∧
      (Matrix.of fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (F i))).det ≠ 0)
    (q : ℕ) (hq : 1 ≤ q) (hw1 : ∀ j, 1 ≤ w j) :
    S.card * ∏ j, (q * w j) ≤ ∏ i, (q * D i + 1) := by
  have hepos : ∀ j, 0 < q * w j := fun j => Nat.mul_pos hq (hw1 j)
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset (S.biUnion fun x => Finset.univ.image x)
  have hc' : ∀ x ∈ S, ∀ j, x j - c ≠ 0 := by
    intro x hx j h
    apply hc
    rw [Finset.mem_biUnion]
    exact ⟨x, hx, Finset.mem_image.2 ⟨j, Finset.mem_univ _, sub_eq_zero.1 h⟩⟩
  have hroot : ∀ (x : Fin N → ℂ) (j : Fin N), ∃ a : ℂ, a ^ (q * w j) = x j - c :=
    fun x j => IsAlgClosed.exists_pow_nat_eq _ (hepos j)
  choose α hα using hroot
  let ζ : Fin N → ℂ := fun j => Complex.exp (2 * Real.pi * Complex.I / ((q * w j : ℕ) : ℂ))
  have hζ : ∀ j, IsPrimitiveRoot (ζ j) (q * w j) :=
    fun j => Complex.isPrimitiveRoot_exp _ (hepos j).ne'
  let m : (Fin N → ℂ) × (∀ j : Fin N, Fin (q * w j)) → (Fin N → ℂ) :=
    fun p j => ζ j ^ (p.2 j : ℕ) * α p.1 j
  have hm : ∀ p, (fun j => m p j ^ (q * w j) + c) = p.1 := by
    intro p
    funext j
    show (ζ j ^ (p.2 j : ℕ) * α p.1 j) ^ (q * w j) + c = p.1 j
    rw [mul_pow, ← pow_mul, mul_comm (p.2 j : ℕ), pow_mul, (hζ j).pow_eq_one, one_pow, one_mul,
      hα]
    ring
  have hm0 : ∀ p, p.1 ∈ S → ∀ k, m p k ≠ 0 := by
    intro p hp k h0
    apply hc' p.1 hp k
    rw [← congrFun (hm p) k, h0, zero_pow (hepos k).ne']
    ring
  have hinj : Set.InjOn m
      (S ×ˢ (Finset.univ : Finset (∀ j : Fin N, Fin (q * w j))) : Finset _) := by
    rintro ⟨x, k⟩ hp ⟨x', k'⟩ _ h
    have h1 : (fun j => m (x, k) j ^ (q * w j) + c) = x := hm (x, k)
    have h2 : (fun j => m (x', k') j ^ (q * w j) + c) = x' := hm (x', k')
    rw [h] at h1
    have hx : x = x' := h1.symm.trans h2
    subst hx
    have hxS : x ∈ S := (Finset.mem_product.1 (Finset.mem_coe.1 hp)).1
    have hk : k = k' := by
      funext j
      have hj : ζ j ^ (k j : ℕ) * α x j = ζ j ^ (k' j : ℕ) * α x j := congrFun h j
      have hα0 : α x j ≠ 0 := by
        intro h0
        apply hc' x hxS j
        rw [← hα, h0, zero_pow (hepos j).ne']
      exact Fin.ext ((hζ j).pow_inj (k j).2 (k' j).2 (mul_right_cancel₀ hα0 hj))
    rw [hk]
  have hcard : ((S ×ˢ (Finset.univ : Finset (∀ j : Fin N, Fin (q * w j)))).image m).card =
      S.card * ∏ j, (q * w j) := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_product, Finset.card_univ, Fintype.card_pi]
    simp
  have hdeg : ∀ i, (bind₁ (powShift (fun j => q * w j) c) (F i)).totalDegree ≤ q * D i := by
    intro i
    apply totalDegree_bind₁_powShift_le
    intro s hs
    calc ∑ j, q * w j * s j = q * ∑ j, w j * s j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _
      _ ≤ q * D i := Nat.mul_le_mul_left _ (hw i s hs)
  have hzero : ∀ z ∈ (S ×ˢ (Finset.univ : Finset (∀ j : Fin N, Fin (q * w j)))).image m,
      (∀ i, eval z (bind₁ (powShift (fun j => q * w j) c) (F i)) = 0) ∧
        (Matrix.of fun i j =>
          eval z (pderiv j (bind₁ (powShift (fun j => q * w j) c) (F i)))).det ≠ 0 := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hz
    have hpS : p.1 ∈ S := (Finset.mem_product.1 hp).1
    obtain ⟨h0, hdet⟩ := hS p.1 hpS
    constructor
    · intro i
      rw [eval_bind₁_powShift, hm]
      exact h0 i
    · rw [jac_bind₁_powShift, Matrix.det_mul, Matrix.det_diagonal, hm]
      exact mul_ne_zero hdet (Finset.prod_ne_zero_iff.2 fun k _ =>
        mul_ne_zero (Nat.cast_ne_zero.2 (hepos k).ne') (pow_ne_zero _ (hm0 p hpS k)))
  have key := hA N (fun i => bind₁ (powShift (fun j => q * w j) c) (F i)) (fun i => q * D i)
    hdeg _ hzero
  rw [hcard] at key
  exact key

/-- Weighted Bezout from the plain degree bound on nondegenerate zeros. -/
theorem weighted_bezout_of
    (hA : ∀ (N : ℕ) (F : Fin N → MvPolynomial (Fin N) ℂ) (D : Fin N → ℕ), (∀ i, (F i).totalDegree ≤ D i) → ∀ S : Finset (Fin N → ℂ), (∀ x ∈ S, (∀ i, MvPolynomial.eval x (F i) = 0) ∧ (Matrix.of fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (F i))).det ≠ 0) → S.card ≤ ∏ i, (D i + 1)) :
    ∀ (N : ℕ) (F : Fin N → MvPolynomial (Fin N) ℂ) (w D : Fin N → ℕ), (∀ i, ∀ s ∈ (F i).support, ∑ j, w j * s j ≤ D i) → ∀ S : Finset (Fin N → ℂ), (∀ x ∈ S, (∀ i, MvPolynomial.eval x (F i) = 0) ∧ (Matrix.of fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (F i))).det ≠ 0) → S.card * ∏ j, w j ≤ ∏ i, D i := by
  intro N F w D hw S hS
  by_cases h0 : ∃ j, w j = 0
  · obtain ⟨j, hj⟩ := h0
    rw [Finset.prod_eq_zero (Finset.mem_univ j) hj]
    simp
  have hw1 : ∀ j, 1 ≤ w j := fun j => Nat.one_le_iff_ne_zero.2 fun h => h0 ⟨j, h⟩
  have hstep : ∀ q : ℕ, 1 ≤ q →
      ((S.card * ∏ j, w j : ℕ) : ℝ) ≤ ∏ i, ((D i : ℝ) + 1 / (q : ℝ)) := by
    intro q hq
    have h := weighted_step hA N F w D hw S hS q hq hw1
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    have e1 : (∏ i : Fin N, ((D i : ℝ) + 1 / (q : ℝ))) * (q : ℝ) ^ N =
        ∏ i : Fin N, ((q : ℝ) * D i + 1) := by
      have hpow : (q : ℝ) ^ N = ∏ _i : Fin N, (q : ℝ) := by simp
      rw [hpow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      field_simp
    have e2 : ∏ j : Fin N, (q * w j) = q ^ N * ∏ j, w j := by
      rw [Finset.prod_mul_distrib]
      simp
    rw [e2] at h
    have hc : ((S.card * (q ^ N * ∏ j, w j) : ℕ) : ℝ) ≤ ((∏ i, (q * D i + 1) : ℕ) : ℝ) := by
      exact_mod_cast h
    have h' : ((S.card * ∏ j, w j : ℕ) : ℝ) * (q : ℝ) ^ N ≤
        (∏ i, ((D i : ℝ) + 1 / (q : ℝ))) * (q : ℝ) ^ N := by
      rw [e1]
      push_cast at hc ⊢
      calc ((S.card : ℝ) * ∏ j, (w j : ℝ)) * (q : ℝ) ^ N
          =(S.card : ℝ) * ((q : ℝ) ^ N * ∏ j, (w j : ℝ)) := by ring
        _ ≤ _ := hc
    exact le_of_mul_le_mul_right h' (pow_pos hq0 N)
  have hlim : Filter.Tendsto (fun q : ℕ => ∏ i, ((D i : ℝ) + 1 / (q : ℝ))) Filter.atTop
      (nhds (∏ i, ((D i : ℝ) + 0))) :=
    tendsto_finsetProd _ fun i _ =>
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
  have hfin : ((S.card * ∏ j, w j : ℕ) : ℝ) ≤ ∏ i, ((D i : ℝ) + 0) :=
    ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨1, hstep⟩)
  simp only [add_zero] at hfin
  exact_mod_cast hfin

end PEqualNP.Gct.Helpers
