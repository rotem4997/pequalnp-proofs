import Mathlib.GroupTheory.Perm.DomMulAct
import PEqualNP.Defs

/-! Helper module (proofs only): the support criterion for `perm (J + t)` when `t` is a sum of
rank-one matrices (Binet-Cauchy for permanents).

For vectors `u_i, w_i ∈ ℂ^n` and scalars `c_i` (`i < d`), let
`A = ∏_j (1 + ∑_i u_i(j) X_i)` and `B = ∏_j (1 + ∑_i w_i(j) X_i)` in `ℂ[X_1, .., X_d]`, with
coefficients `a_α`, `b_α`. Then

  `perm (J + ∑_i c_i u_i w_iᵀ) = ∑_α (n - |α|)! * α! * a_α * b_α * c^α`.

The proof expands each column factor over a label `o : Option (Fin d)` (`none` for the entry `1`,
`some i` for the `i`-th rank-one term). A labelling `μ` of the columns has a type `typ μ`, the
number of columns with each label. The sum over permutations of the row weight of `μ ∘ σ⁻¹`
is, by the orbit count (the stabilizer of a labelling has `∏_o (count of o)!` elements), the
count `(n - |α|)! * α!` times the sum of the row weights of all labellings of the same type,
which is `a_α`. Summing the column weights over the labellings of type `α` gives `b_α`.

The corollary `level_of_disjoint`: if `a_α * b_α = 0` for every `α ≠ 0`, the permanent of
`J + ∑_i c_i u_i w_iᵀ` is `n!` for every `c`. -/

namespace PEqualNP.Gct.Helpers.Support

open Finset MvPolynomial

variable {n d : ℕ}

/-- The weight of a labelling: the product over the labelled positions of the labelled vector. -/
def wt (x : Fin d → Fin n → ℂ) (μ : Fin n → Option (Fin d)) : ℂ :=
  ∏ j, Option.elim (μ j) 1 (fun i => x i j)

/-- The number of positions with label `o`. -/
def cnt (μ : Fin n → Option (Fin d)) (o : Option (Fin d)) : ℕ :=
  Fintype.card {j // μ j = o}

/-- The type of a labelling: the number of positions carrying each label `i`. -/
noncomputable def typ (μ : Fin n → Option (Fin d)) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => cnt μ (some i)

@[simp] theorem typ_apply (μ : Fin n → Option (Fin d)) (i : Fin d) :
    typ μ i = cnt μ (some i) := rfl

/-- The exponent of a label. -/
noncomputable def sh (o : Option (Fin d)) : Fin d →₀ ℕ :=
  Option.elim o 0 fun i => Finsupp.single i 1

theorem sum_sh (μ : Fin n → Option (Fin d)) : ∑ j, sh (μ j) = typ μ := by
  ext i
  rw [Finsupp.finsetSum_apply, typ_apply, cnt, Fintype.card_subtype]
  have h : ∀ j, sh (μ j) i = if μ j = some i then 1 else 0 := by
    intro j
    rcases μ j with _ | k
    · simp [sh]
    · by_cases hk : k = i
      · subst hk; simp [sh]
      · simp [sh, hk]
  simp_rw [h]
  rw [Finset.sum_boole]
  simp

/-- The coefficients of `∏_j (1 + ∑_i x_i(j) X_i)` as sums of weights of labellings. -/
theorem coeff_prod (x : Fin d → Fin n → ℂ) (m : Fin d →₀ ℕ) :
    (∏ j : Fin n, (1 + ∑ i, C (x i j) * X i) : MvPolynomial (Fin d) ℂ).coeff m =
      ∑ μ : Fin n → Option (Fin d), if typ μ = m then wt x μ else 0 := by
  have h1 : ∀ j, (1 + ∑ i, C (x i j) * X i : MvPolynomial (Fin d) ℂ) =
      ∑ o : Option (Fin d), C (Option.elim o 1 fun i => x i j) * monomial (sh o) 1 := by
    intro j
    rw [Fintype.sum_option]
    simp [sh, X]
  simp_rw [h1]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, coeff_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, ← monomial_sum_one, sum_sh, C_mul_monomial, mul_one,
    coeff_monomial]
  rfl

theorem cnt_comp (μ : Fin n → Option (Fin d)) (σ : Equiv.Perm (Fin n)) (o : Option (Fin d)) :
    cnt (μ ∘ σ) o = cnt μ o := by
  unfold cnt
  exact Fintype.card_congr (σ.subtypeEquiv fun _ => Iff.rfl)

theorem sum_cnt (μ : Fin n → Option (Fin d)) : ∑ o, cnt μ o = n := by
  unfold cnt
  rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv μ), Fintype.card_fin]

theorem cnt_none (μ : Fin n → Option (Fin d)) : cnt μ none = n - ∑ i, typ μ i := by
  have h := sum_cnt μ
  rw [Fintype.sum_option] at h
  simp only [typ_apply]
  omega

theorem cnt_eq_of_typ (μ ν : Fin n → Option (Fin d)) (h : typ μ = typ ν) (o : Option (Fin d)) :
    cnt μ o = cnt ν o := by
  rcases o with _ | i
  · rw [cnt_none, cnt_none, h]
  · have := DFunLike.congr_fun h i
    simpa using this

/-- Two labellings with the same counts differ by a permutation. -/
theorem exists_perm (μ ν : Fin n → Option (Fin d)) (h : ∀ o, cnt ν o = cnt μ o) :
    ∃ σ : Equiv.Perm (Fin n), μ ∘ σ = ν := by
  let e : (Σ o, {j // ν j = o}) ≃ (Σ o, {j // μ j = o}) :=
    Equiv.sigmaCongrRight fun o => Fintype.equivOfCardEq (h o)
  refine ⟨(Equiv.sigmaFiberEquiv ν).symm.trans (e.trans (Equiv.sigmaFiberEquiv μ)), ?_⟩
  funext j
  simp only [Function.comp_apply, Equiv.trans_apply]
  exact (Fintype.equivOfCardEq (h (ν j)) ⟨j, rfl⟩).2

/-- The number of permutations carrying one labelling to another. -/
theorem card_perm_comp (μ ν : Fin n → Option (Fin d)) :
    (#{σ : Equiv.Perm (Fin n) | μ ∘ σ = ν} : ℕ) =
      if typ ν = typ μ then ∏ o, (cnt μ o).factorial else 0 := by
  split_ifs with h
  · obtain ⟨σ0, hσ0⟩ := exists_perm μ ν (cnt_eq_of_typ ν μ h)
    have hst : (#{g : Equiv.Perm (Fin n) | μ ∘ g = μ} : ℕ) = ∏ o, (cnt μ o).factorial := by
      rw [← Fintype.card_subtype]
      exact DomMulAct.stabilizer_card μ
    rw [← hst]
    refine Finset.card_nbij' (fun σ => σ * σ0⁻¹) (fun g => g * σ0) ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
      rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hσ, ← hσ0, Function.comp_assoc,
        ← Equiv.Perm.coe_mul, mul_inv_cancel, Equiv.Perm.coe_one, Function.comp_id]
    · intro g hg
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hg ⊢
      rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hg, hσ0]
    · intro σ _
      simp
    · intro g _
      simp
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro σ _ hσ
    apply h
    ext i
    simp only [typ_apply, ← hσ, cnt_comp]

/-- The orbit sum: the sum over permutations of the row weights of `μ ∘ σ⁻¹`. -/
theorem sum_perm_wt (x : Fin d → Fin n → ℂ) (μ : Fin n → Option (Fin d)) :
    ∑ σ : Equiv.Perm (Fin n), wt x (μ ∘ σ.symm) =
      ((∏ o, (cnt μ o).factorial : ℕ) : ℂ) *
        ∑ ν : Fin n → Option (Fin d), if typ ν = typ μ then wt x ν else 0 := by
  have h1 : ∑ σ : Equiv.Perm (Fin n), wt x (μ ∘ σ.symm) =
      ∑ σ : Equiv.Perm (Fin n), wt x (μ ∘ σ) :=
    Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ (fun σ => rfl)
  rw [h1]
  have h2 : ∀ σ : Equiv.Perm (Fin n), wt x (μ ∘ σ) =
      ∑ ν : Fin n → Option (Fin d), if μ ∘ σ = ν then wt x ν else 0 := by
    intro σ
    rw [Finset.sum_ite_eq]
    simp
  simp_rw [h2]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, card_perm_comp]
  split_ifs <;> simp

/-- The constant part of a labelled product. -/
theorem wt_const (c : Fin d → ℂ) (μ : Fin n → Option (Fin d)) :
    wt (fun i _ => c i) μ = ∏ i, c i ^ typ μ i := by
  unfold wt
  rw [← Finset.prod_fiberwise (s := Finset.univ) (g := μ)]
  rw [Fintype.prod_option]
  simp only [typ_apply, cnt, Fintype.card_subtype]
  have h : ∀ o : Option (Fin d), ∏ j ∈ ({j | μ j = o} : Finset (Fin n)),
      Option.elim (μ j) 1 (fun i => c i) = Option.elim o 1 (fun i => c i) ^ #{j | μ j = o} := by
    intro o
    rw [Finset.prod_congr rfl (fun j hj => by
      rw [(Finset.mem_filter.mp hj).2]), Finset.prod_const]
  simp only [h]
  simp

/-- The permanent expanded over labellings of the columns. -/
theorem eval_expand (u w : Fin d → Fin n → ℂ) (c : Fin d → ℂ) :
    MvPolynomial.eval (fun p : Fin n × Fin n => 1 + ∑ i, c i * u i p.1 * w i p.2)
        (PEqualNP.Gct.permPoly ℂ n) =
      ∑ μ : Fin n → Option (Fin d), (∏ i, c i ^ typ μ i) * wt w μ *
        ∑ σ : Equiv.Perm (Fin n), wt u (μ ∘ σ.symm) := by
  have hp : MvPolynomial.eval (fun p : Fin n × Fin n => 1 + ∑ i, c i * u i p.1 * w i p.2)
      (PEqualNP.Gct.permPoly ℂ n) =
      ∑ σ : Equiv.Perm (Fin n), ∏ j, (1 + ∑ i, c i * u i (σ j) * w i j) := by
    simp [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply]
  rw [hp]
  have h1 : ∀ σ : Equiv.Perm (Fin n), ∏ j, (1 + ∑ i, c i * u i (σ j) * w i j) =
      ∑ μ : Fin n → Option (Fin d),
        (∏ i, c i ^ typ μ i) * wt w μ * wt u (μ ∘ σ.symm) := by
    intro σ
    have h2 : ∀ j, (1 + ∑ i, c i * u i (σ j) * w i j) =
        ∑ o : Option (Fin d), Option.elim o 1 (fun i => c i * u i (σ j) * w i j) := by
      intro j
      rw [Fintype.sum_option]
      rfl
    simp_rw [h2]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun μ _ => ?_
    have h3 : ∀ j, Option.elim (μ j) 1 (fun i => c i * u i (σ j) * w i j) =
        Option.elim (μ j) 1 (fun i => c i) * Option.elim (μ j) 1 (fun i => u i (σ j)) *
          Option.elim (μ j) 1 (fun i => w i j) := by
      intro j
      rcases μ j with _ | i <;> simp
    simp_rw [h3]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← wt_const c μ]
    have h4 : ∏ j, Option.elim (μ j) 1 (fun i => u i (σ j)) = wt u (μ ∘ σ.symm) := by
      unfold wt
      exact Fintype.prod_equiv σ _ _ (fun j => by simp)
    rw [h4]
    unfold wt
    ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum]

/-- Regrouping a sum over labellings by type, over any set of types containing all of them. -/
theorem sum_by_typ (G : (Fin d →₀ ℕ) → ℂ) (F : (Fin n → Option (Fin d)) → ℂ)
    (S : Finset (Fin d →₀ ℕ)) (hS : ∀ μ : Fin n → Option (Fin d), typ μ ∈ S) :
    ∑ μ, G (typ μ) * F μ = ∑ m ∈ S, G m * ∑ μ, if typ μ = m then F μ else 0 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have h : ∀ m, G m * (if typ μ = m then F μ else 0) =
      if typ μ = m then G (typ μ) * F μ else 0 := by
    intro m
    split_ifs with hm
    · rw [hm]
    · simp
  simp_rw [h]
  rw [Finset.sum_ite_eq]
  simp [hS μ]

/-- The support criterion (Binet-Cauchy for permanents). -/
theorem support_criterion :
    ∀ (n d : ℕ) (u w : Fin d → Fin n → ℂ) (c : Fin d → ℂ),
      MvPolynomial.eval (fun p : Fin n × Fin n => 1 + ∑ i, c i * u i p.1 * w i p.2)
          (PEqualNP.Gct.permPoly ℂ n) =
        ∑ α ∈ (∏ j : Fin n, (1 + ∑ i, MvPolynomial.C (w i j) * MvPolynomial.X i) :
            MvPolynomial (Fin d) ℂ).support,
          ((n - ∑ i, α i).factorial : ℂ) * (∏ i, ((α i).factorial : ℂ)) *
            (∏ j : Fin n, (1 + ∑ i, MvPolynomial.C (u i j) * MvPolynomial.X i) :
              MvPolynomial (Fin d) ℂ).coeff α *
            (∏ j : Fin n, (1 + ∑ i, MvPolynomial.C (w i j) * MvPolynomial.X i) :
              MvPolynomial (Fin d) ℂ).coeff α *
            ∏ i, c i ^ α i := by
  intro n d u w c
  set A : MvPolynomial (Fin d) ℂ := ∏ j : Fin n, (1 + ∑ i, C (u i j) * X i) with hA
  set B : MvPolynomial (Fin d) ℂ := ∏ j : Fin n, (1 + ∑ i, C (w i j) * X i) with hB
  let G : (Fin d →₀ ℕ) → ℂ := fun m =>
    ((n - ∑ i, m i).factorial : ℂ) * (∏ i, ((m i).factorial : ℂ)) * A.coeff m * ∏ i, c i ^ m i
  have hN : ∀ μ : Fin n → Option (Fin d), ((∏ o, (cnt μ o).factorial : ℕ) : ℂ) =
      ((n - ∑ i, typ μ i).factorial : ℂ) * ∏ i, ((typ μ i).factorial : ℂ) := by
    intro μ
    rw [Fintype.prod_option, cnt_none]
    push_cast
    rfl
  rw [eval_expand]
  have h1 : ∀ μ : Fin n → Option (Fin d), (∏ i, c i ^ typ μ i) * wt w μ *
      ∑ σ : Equiv.Perm (Fin n), wt u (μ ∘ σ.symm) = G (typ μ) * wt w μ := by
    intro μ
    rw [sum_perm_wt, hN, ← coeff_prod u (typ μ)]
    simp only [G, ← hA]
    ring
  simp_rw [h1]
  have hsub : B.support ⊆ Finset.univ.image (typ (n := n) (d := d)) := by
    intro m hm
    rw [MvPolynomial.mem_support_iff, hB, coeff_prod] at hm
    by_contra h
    apply hm
    refine Finset.sum_eq_zero fun μ _ => ite_eq_right_iff.mpr fun hμ => ?_
    exact absurd (by rw [← hμ]; exact Finset.mem_image_of_mem _ (Finset.mem_univ μ)) h
  rw [sum_by_typ G (wt w) (Finset.univ.image (typ (n := n) (d := d)))
    (fun μ => Finset.mem_image_of_mem _ (Finset.mem_univ μ))]
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [hB, coeff_prod w m]
    simp only [G]
    ring
  · intro m _ hm
    rw [MvPolynomial.notMem_support_iff, hB, coeff_prod] at hm
    rw [hm, mul_zero]

theorem coeff_zero_prod (x : Fin d → Fin n → ℂ) :
    (∏ j : Fin n, (1 + ∑ i, C (x i j) * X i) : MvPolynomial (Fin d) ℂ).coeff 0 = 1 := by
  rw [← MvPolynomial.constantCoeff_eq, map_prod]
  simp

/-- The corollary: if the coefficients of `A` and `B` have disjoint supports away from `0`,
the permanent of `J + ∑_i c_i u_i w_iᵀ` is `n!` for every `c`. -/
theorem level_of_disjoint :
    ∀ (n d : ℕ) (u w : Fin d → Fin n → ℂ),
      (∀ α : Fin d →₀ ℕ, α ≠ 0 →
        (∏ j : Fin n, (1 + ∑ i, MvPolynomial.C (u i j) * MvPolynomial.X i) :
            MvPolynomial (Fin d) ℂ).coeff α *
          (∏ j : Fin n, (1 + ∑ i, MvPolynomial.C (w i j) * MvPolynomial.X i) :
            MvPolynomial (Fin d) ℂ).coeff α = 0) →
      ∀ c : Fin d → ℂ,
        MvPolynomial.eval (fun p : Fin n × Fin n => 1 + ∑ i, c i * u i p.1 * w i p.2)
            (PEqualNP.Gct.permPoly ℂ n) = (Nat.factorial n : ℂ) := by
  intro n d u w h c
  rw [support_criterion, Finset.sum_eq_single 0]
  · simp [coeff_zero_prod]
  · intro α _ hα
    have := h α hα
    calc _ = ((n - ∑ i, α i).factorial : ℂ) * (∏ i, ((α i).factorial : ℂ)) *
          ((∏ j : Fin n, (1 + ∑ i, C (u i j) * X i) : MvPolynomial (Fin d) ℂ).coeff α *
            (∏ j : Fin n, (1 + ∑ i, C (w i j) * X i) : MvPolynomial (Fin d) ℂ).coeff α) *
          ∏ i, c i ^ α i := by ring
      _ = 0 := by rw [this]; ring
  · intro h0
    rw [MvPolynomial.notMem_support_iff, coeff_zero_prod] at h0
    exact absurd h0 one_ne_zero

end PEqualNP.Gct.Helpers.Support
