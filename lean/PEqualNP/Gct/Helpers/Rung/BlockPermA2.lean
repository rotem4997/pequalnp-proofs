import Mathlib

/-!
# Helper module (proofs only): coefficient extraction and the root of unity product

* `coeff_sep`: in a polynomial ring in the variables `σ₀ ⊕ H`, the coefficient of a product
  over `h : H` of factors, each a sum of terms `(polynomial in σ₀) * X h ^ e`, is read off
  factor by factor.
* `prod_add_root_mul`: `∏ l < r, (y + ζ ^ l * x) = y ^ r + (-1) ^ (r + 1) * x ^ r` for a
  primitive `r`-th root of unity `ζ` in a domain.
-/

namespace PEqualNP.Gct.Rung.BPA

open MvPolynomial Finset

variable {R : Type*} [CommRing R] {σ₀ H : Type*}

theorem mapDomain_inl_eq (w : σ₀ →₀ ℕ) :
    (Finsupp.mapDomain Sum.inl w : σ₀ ⊕ H →₀ ℕ) = Finsupp.sumElim w 0 := by
  ext (i | i)
  · exact Finsupp.mapDomain_apply_of_injective Sum.inl_injective w i
  · rw [Finsupp.mapDomain_of_notMem_range]
    · simp
    · simp

theorem sumElim_inj (u w : σ₀ →₀ ℕ) (v n : H →₀ ℕ) :
    Finsupp.sumElim w n = Finsupp.sumElim u v ↔ w = u ∧ n = v := by
  constructor
  · intro h
    exact ⟨Finsupp.ext fun i => by simpa using DFunLike.congr_fun h (Sum.inl i),
      Finsupp.ext fun i => by simpa using DFunLike.congr_fun h (Sum.inr i)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem coeff_rename_inl_mul_monomial [DecidableEq σ₀] [DecidableEq H] (P : MvPolynomial σ₀ R)
    (u : σ₀ →₀ ℕ) (v n : H →₀ ℕ) :
    (rename Sum.inl P * monomial (Finsupp.sumElim 0 n) 1 : MvPolynomial (σ₀ ⊕ H) R).coeff
      (Finsupp.sumElim u v) = if n = v then P.coeff u else 0 := by
  refine MvPolynomial.induction_on' P ?_ ?_
  · intro w c
    rw [rename_monomial, monomial_mul_monomial, mapDomain_inl_eq, ← Finsupp.sumElim_add, add_zero,
      zero_add, mul_one, coeff_monomial, coeff_monomial]
    simp only [sumElim_inj]
    by_cases h1 : w = u <;> by_cases h2 : n = v <;> simp [h1, h2]
  · intro p q hp hq
    rw [map_add, add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    split_ifs <;> simp

theorem prod_X_inr_pow [DecidableEq σ₀] [Fintype H] [DecidableEq H] (m : H → ℕ) :
    (∏ h, X (Sum.inr h) ^ m h : MvPolynomial (σ₀ ⊕ H) R) =
      monomial (Finsupp.sumElim 0 (Finsupp.equivFunOnFinite.symm m)) 1 := by
  have h : (Finsupp.sumElim 0 (Finsupp.equivFunOnFinite.symm m) : σ₀ ⊕ H →₀ ℕ) =
      ∑ h, Finsupp.single (Sum.inr h) (m h) := by
    ext (i | i)
    · simp [Finsupp.finsetSum_apply]
    · simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [h, monomial_sum_one]
  refine prod_congr rfl fun h _ => ?_
  rw [X_pow_eq_monomial]

/-- Coefficient extraction, factor by factor. -/
theorem coeff_sep [DecidableEq σ₀] [Fintype H] [DecidableEq H] {ι : Type*} [DecidableEq ι]
    (S : H → Finset ι) (a : H → ι → MvPolynomial σ₀ R) (e : H → ι → ℕ)
    (A : MvPolynomial σ₀ R) (u : σ₀ →₀ ℕ) (v : H →₀ ℕ) :
    (rename Sum.inl A * ∏ h, ∑ x ∈ S h, rename Sum.inl (a h x) * X (Sum.inr h) ^ e h x :
      MvPolynomial (σ₀ ⊕ H) R).coeff (Finsupp.sumElim u v) =
      (A * ∏ h, ∑ x ∈ (S h).filter (fun x => e h x = v h), a h x).coeff u := by
  have hpi : Fintype.piFinset (fun h => (S h).filter fun x => e h x = v h) =
      (Fintype.piFinset S).filter (fun x => ∀ h, e h (x h) = v h) := by
    ext x
    simp [Fintype.mem_piFinset, forall_and]
  rw [Finset.prod_univ_sum, Finset.prod_univ_sum, Finset.mul_sum, Finset.mul_sum, coeff_sum,
    coeff_sum, hpi, Finset.sum_filter]
  refine sum_congr rfl fun x _ => ?_
  rw [Finset.prod_mul_distrib, ← map_prod, ← mul_assoc, ← map_mul, prod_X_inr_pow,
    coeff_rename_inl_mul_monomial]
  refine if_congr ?_ rfl rfl
  rw [DFunLike.ext_iff]
  rfl

theorem prod_add_root_mul {S : Type*} [CommRing S] [IsDomain S] {ζ : S} {r : ℕ} (hr : 0 < r)
    (hζ : IsPrimitiveRoot ζ r) (x y : S) :
    ∏ l ∈ range r, (y + ζ ^ l * x) = y ^ r + (-1) ^ (r + 1) * x ^ r := by
  classical
  have himg : (range r).image (fun l => ζ ^ l) = Polynomial.nthRootsFinset r (1 : S) := by
    apply Finset.eq_of_subset_of_card_le
    · intro μ hμ
      obtain ⟨l, _, rfl⟩ := mem_image.1 hμ
      rw [Polynomial.mem_nthRootsFinset hr, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one,
        one_pow]
    · rw [hζ.card_nthRootsFinset, card_image_of_injOn, card_range]
      intro i hi j hj h
      exact hζ.pow_inj (mem_range.1 hi) (mem_range.1 hj) h
  have key := hζ.pow_sub_pow_eq_prod_sub_mul y (-x) hr
  rw [← himg, prod_image] at key
  · calc ∏ l ∈ range r, (y + ζ ^ l * x) = ∏ l ∈ range r, (y - ζ ^ l * -x) :=
        prod_congr rfl fun l _ => by ring
      _ = y ^ r - (-x) ^ r := key.symm
      _ = _ := by
        rw [neg_pow]
        ring
  · intro i hi j hj h
    exact hζ.pow_inj (mem_range.1 hi) (mem_range.1 hj) h

end PEqualNP.Gct.Rung.BPA
