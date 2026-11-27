import Mathlib

/-!
# Helper module (proofs only): permanents with repeated rows as polynomial coefficients

For a matrix with rows indexed by `ρ` and columns by `κ` we write `pm M` for the sum over all
bijections `σ : κ ≃ ρ` of the products `∏ j, M (σ j) j` (the permanent when `ρ = κ`, and `0`
when the two types have different cardinalities).

The main result `pm_group`: if the row `i` only depends on its group `π i`, then `pm M` is
the number of permutations of the rows that preserve the groups, times the coefficient, in
the product over the columns `j` of the linear forms `∑ γ, W γ j * X γ`, of the monomial that
has each group variable to the power of the size of the group.
-/

namespace PEqualNP.Gct.Rung.BPA

open MvPolynomial Finset

variable {R : Type*} [CommRing R]
variable {ρ κ Γ : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype κ] [DecidableEq κ]
  [Fintype Γ] [DecidableEq Γ]

/-- The sum over all bijections from the columns to the rows of the product of the entries. -/
def pm (M : ρ → κ → R) : R := ∑ σ : κ ≃ ρ, ∏ j, M (σ j) j

theorem pm_eq_permanent {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n R) :
    pm (fun i j => M i j) = M.permanent := rfl

theorem pm_transpose (M : ρ → κ → R) : pm (fun j i => M i j) = pm M := by
  unfold pm
  refine Fintype.sum_equiv (Equiv.symmEquiv ρ κ) _ _ fun σ => ?_
  rw [← Equiv.prod_comp σ.symm]
  simp

theorem pm_reindex {ρ' κ' : Type*} [Fintype ρ'] [DecidableEq ρ'] [Fintype κ'] [DecidableEq κ']
    (e₁ : ρ' ≃ ρ) (e₂ : κ' ≃ κ) (M : ρ → κ → R) :
    pm (fun i j => M (e₁ i) (e₂ j)) = pm M := by
  unfold pm
  refine Fintype.sum_equiv (Equiv.equivCongr e₂ e₁) _ _ fun σ => ?_
  rw [← Equiv.prod_comp e₂]
  simp

/-- The number of permutations of the rows that preserve the groups. -/
def stab (π : ρ → Γ) : ℕ := (univ.filter fun τ : Equiv.Perm ρ => ∀ i, π (τ i) = π i).card

omit [Fintype Γ] in
theorem stab_pos (π : ρ → Γ) : 0 < stab π :=
  Finset.card_pos.2 ⟨1, by simp⟩

theorem stab_id : stab (id : ρ → ρ) = 1 := by
  unfold stab
  rw [Finset.card_eq_one]
  refine ⟨1, ?_⟩
  ext τ
  simp only [id, mem_filter, mem_univ, true_and, mem_singleton]
  exact ⟨fun h => Equiv.ext h, fun h => by simp [h]⟩

omit [DecidableEq ρ] [DecidableEq κ] [Fintype Γ] in
theorem exists_equiv_of_profile (π : ρ → Γ) (g : κ → Γ)
    (hp : (∑ j, Finsupp.single (g j) (1 : ℕ)) = ∑ i, Finsupp.single (π i) 1) :
    ∃ σ : κ ≃ ρ, ∀ j, π (σ j) = g j := by
  have hc : ∀ γ, Fintype.card {j // g j = γ} = Fintype.card {i // π i = γ} := by
    intro γ
    have := DFunLike.congr_fun hp γ
    simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finset.sum_boole,
      Nat.cast_id] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact this
  refine ⟨(Equiv.sigmaFiberEquiv g).symm.trans
    ((Equiv.sigmaCongrRight fun γ => Fintype.equivOfCardEq (hc γ)).trans
      (Equiv.sigmaFiberEquiv π)), fun j => ?_⟩
  exact ((Fintype.equivOfCardEq (hc (g j))) ⟨j, rfl⟩).2

omit [Fintype Γ] in
theorem card_fiber (π : ρ → Γ) (g : κ → Γ) :
    (univ.filter fun σ : κ ≃ ρ => ∀ j, π (σ j) = g j).card =
      if (∑ j, Finsupp.single (g j) (1 : ℕ)) = ∑ i, Finsupp.single (π i) 1 then stab π
      else 0 := by
  by_cases h : ∃ σ₀ : κ ≃ ρ, ∀ j, π (σ₀ j) = g j
  · obtain ⟨σ₀, h₀⟩ := h
    have prof : (∑ j, Finsupp.single (g j) (1 : ℕ)) = ∑ i, Finsupp.single (π i) 1 := by
      rw [← Equiv.sum_comp σ₀]
      simp [h₀]
    rw [ite_eq_left prof]
    unfold stab
    refine Finset.card_bij' (fun σ _ => σ₀.symm.trans σ) (fun τ _ => σ₀.trans τ) ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [mem_filter, mem_univ, true_and] at hσ ⊢
      intro i
      rw [Equiv.trans_apply, hσ, ← h₀]
      simp
    · intro τ hτ
      simp only [mem_filter, mem_univ, true_and] at hτ ⊢
      intro j
      rw [Equiv.trans_apply, hτ, h₀]
    · intro σ _
      ext j
      simp
    · intro τ _
      ext j
      simp
  · rw [ite_eq_right fun hp => h (exists_equiv_of_profile π g hp)]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro σ _ hσ
    exact h ⟨σ, hσ⟩

/-- Permanent with repeated rows as a coefficient. -/
theorem pm_group (π : ρ → Γ) (W : Γ → κ → R) :
    pm (fun i j => W (π i) j) =
      (stab π : R) * (∏ j, ∑ γ, C (W γ j) * X γ : MvPolynomial Γ R).coeff
        (∑ i, Finsupp.single (π i) 1) := by
  have hR : (∏ j, ∑ γ, C (W γ j) * X γ : MvPolynomial Γ R) =
      ∑ g : κ → Γ, monomial (∑ j, Finsupp.single (g j) 1) (∏ j, W (g j) j) := by
    rw [Finset.prod_univ_sum]
    simp only [Fintype.piFinset_univ]
    refine sum_congr rfl fun g _ => ?_
    rw [Finset.prod_mul_distrib, ← map_prod, monomial_sum_index]
    rfl
  rw [hR, coeff_sum]
  simp only [coeff_monomial]
  calc pm (fun i j => W (π i) j)
      = ∑ σ : κ ≃ ρ, ∑ g : κ → Γ, if (∀ j, π (σ j) = g j) then ∏ j, W (g j) j else 0 := by
        unfold pm
        refine sum_congr rfl fun σ _ => ?_
        rw [Finset.sum_eq_single (fun j => π (σ j))]
        · simp
        · intro g _ hg
          rw [ite_eq_right]
          intro h
          exact hg (funext fun j => (h j).symm)
        · simp
    _ = ∑ g : κ → Γ, ∑ σ : κ ≃ ρ, if (∀ j, π (σ j) = g j) then ∏ j, W (g j) j else 0 :=
        Finset.sum_comm
    _ = ∑ g : κ → Γ,
          ((univ.filter fun σ : κ ≃ ρ => ∀ j, π (σ j) = g j).card : R) * ∏ j, W (g j) j := by
        refine sum_congr rfl fun g _ => ?_
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    _ = _ := by
        rw [Finset.mul_sum]
        refine sum_congr rfl fun g _ => ?_
        rw [card_fiber]
        split_ifs <;> simp

end PEqualNP.Gct.Rung.BPA
