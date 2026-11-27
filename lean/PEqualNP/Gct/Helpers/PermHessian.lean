import PEqualNP.Defs
import PEqualNP.Gct.Helpers.PermCount
import PEqualNP.Gct.Helpers.HessKernel

/-! The Hessian of the permanent at the point of Mignon and Ressayre. Helper for L-gct-013. -/

namespace PEqualNP.Gct.Helpers

open Finset MvPolynomial

/-- Derivative of a product of variables. -/
theorem pderiv_prod_X {ι τ R : Type} [CommRing R] [DecidableEq ι] [DecidableEq τ] (s : Finset ι) (g : ι → τ)
    (b : τ) :
    pderiv b (∏ i ∈ s, (X (g i) : MvPolynomial τ R)) =
      ∑ i ∈ s, if g i = b then ∏ j ∈ s.erase i, (X (g j) : MvPolynomial τ R) else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, Derivation.leibniz, ih, sum_insert ha, erase_insert ha]
    rw [pderiv_X]
    have : ∀ i ∈ s, (if g i = b then ∏ j ∈ (insert a s).erase i, (X (g j) : MvPolynomial τ R)
        else 0) = X (g a) * (if g i = b then ∏ j ∈ s.erase i, X (g j) else 0) := by
      intro i hi
      have hne : a ≠ i := fun h => ha (h ▸ hi)
      split_ifs
      · rw [erase_insert_of_ne hne, prod_insert (fun h => ha (mem_of_mem_erase h))]
      · simp
    rw [sum_congr rfl this, ← mul_sum]
    simp only [smul_eq_mul, Pi.single_apply]
    split_ifs <;> simp [add_comm]


/-- The derivative of the monomial of a permutation. -/
theorem pderiv_perm_mon {m : ℕ} (σ : Equiv.Perm (Fin m)) (b : Fin m × Fin m) (t : Finset (Fin m)) :
    pderiv b (∏ i ∈ t, (X (σ i, i) : MvPolynomial (Fin m × Fin m) ℂ)) =
      if b.2 ∈ t ∧ σ b.2 = b.1 then ∏ j ∈ t.erase b.2, X (σ j, j) else 0 := by
  rw [pderiv_prod_X]
  by_cases h : b.2 ∈ t
  · rw [sum_eq_single b.2]
    · by_cases hb : σ b.2 = b.1
      · simp [h, hb]
      · have : ¬ ((σ b.2, b.2) = b) := fun e => hb (by rw [← e])
        simp [h, hb, this]
    · intro i _ hi
      have : ¬ ((σ i, i) = b) := fun e => hi (by rw [← e])
      simp [this]
    · intro h'; exact absurd h h'
  · rw [sum_eq_zero]
    · simp [h]
    · intro i hi
      have : ¬ ((σ i, i) = b) := fun e => h (by rw [← e]; exact hi)
      simp [this]

/-- The point of Mignon and Ressayre: all ones, with `1 - m` at `(0, 0)`. -/
noncomputable def mrPoint (n : ℕ) : Fin (n + 2) × Fin (n + 2) → ℂ :=
  fun p => if p = (0, 0) then 1 - ((n + 2 : ℕ) : ℂ) else 1

theorem eval_mon_mrPoint {n : ℕ} (σ : Equiv.Perm (Fin (n + 2))) (t : Finset (Fin (n + 2))) :
    eval (mrPoint n) (∏ i ∈ t, (X (σ i, i) : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ)) =
      if 0 ∈ t ∧ σ 0 = 0 then 1 - ((n + 2 : ℕ) : ℂ) else 1 := by
  rw [eval_prod]
  simp only [eval_X, mrPoint, Prod.ext_iff]
  by_cases h0 : σ 0 = 0
  · have : ∀ i ∈ t, (if σ i = 0 ∧ i = 0 then 1 - ((n + 2 : ℕ) : ℂ) else 1) =
        if 0 = i then 1 - ((n + 2 : ℕ) : ℂ) else 1 := by
      intro i _
      by_cases hi : i = 0
      · subst hi; simp [h0]
      · simp [hi, Ne.symm hi]
    rw [prod_congr rfl this, prod_ite_eq]
    simp [h0]
  · rw [prod_eq_one]
    · simp [h0]
    · intro i _
      by_cases hi : i = 0
      · subst hi; simp [h0]
      · simp [hi]

/-- The Hessian entry of the permanent at the point of Mignon and Ressayre, as a sum over
permutations. -/
theorem hess_perm_sum (n : ℕ) (a b : Fin (n + 2) × Fin (n + 2)) :
    eval (mrPoint n) (pderiv a (pderiv b (PEqualNP.Gct.permPoly ℂ (n + 2)))) =
      ∑ σ : Equiv.Perm (Fin (n + 2)),
        if σ b.2 = b.1 ∧ a.2 ≠ b.2 ∧ σ a.2 = a.1 then
          (if a.2 ≠ 0 ∧ b.2 ≠ 0 ∧ σ 0 = 0 then 1 - ((n + 2 : ℕ) : ℂ) else 1) else 0 := by
  simp only [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply, map_sum]
  refine sum_congr rfl fun σ _ => ?_
  rw [pderiv_perm_mon]
  by_cases hb : σ b.2 = b.1
  · rw [if_pos ⟨mem_univ _, hb⟩, pderiv_perm_mon]
    by_cases ha : a.2 ≠ b.2 ∧ σ a.2 = a.1
    · rw [if_pos ⟨mem_erase.mpr ⟨ha.1, mem_univ _⟩, ha.2⟩, eval_mon_mrPoint,
        if_pos (show σ b.2 = b.1 ∧ a.2 ≠ b.2 ∧ σ a.2 = a.1 from ⟨hb, ha.1, ha.2⟩)]
      congr 1
      simp only [mem_erase, mem_univ, and_true]
      apply propext
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨Ne.symm h1, Ne.symm h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨Ne.symm h1, Ne.symm h2⟩, h3⟩
    · rw [if_neg, map_zero, if_neg]
      · rintro ⟨_, h1, h2⟩; exact ha ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ha ⟨(mem_erase.mp h1).1, h2⟩
  · rw [if_neg (fun h => hb h.2), map_zero, map_zero, if_neg (fun h => hb h.1)]


theorem card_two {n : ℕ} (a b : Fin (n + 2) × Fin (n + 2)) (h2 : a.2 ≠ b.2) (h1 : a.1 ≠ b.1) :
    #{σ : Equiv.Perm (Fin (n + 2)) | σ b.2 = b.1 ∧ a.2 ≠ b.2 ∧ σ a.2 = a.1} = n.factorial := by
  let f : Fin (n + 2) → Fin (n + 2) := fun x => if x = b.2 then b.1 else a.1
  have hs : ({b.2, a.2} : Finset (Fin (n + 2))).card = 2 := card_pair (Ne.symm h2)
  have e : (univ.filter fun σ : Equiv.Perm (Fin (n + 2)) =>
      σ b.2 = b.1 ∧ a.2 ≠ b.2 ∧ σ a.2 = a.1) =
      univ.filter fun σ : Equiv.Perm (Fin (n + 2)) =>
        ∀ x ∈ ({b.2, a.2} : Finset (Fin (n + 2))), σ x = f x := by
    ext σ
    simp [f, h2]
  rw [e]
  convert card_perm_agree ({b.2, a.2} : Finset (Fin (n + 2))) f ?_ using 1
  · congr
  · rw [hs, Fintype.card_fin]; rfl
  · intro x hx y hy hxy
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all [f]

theorem card_three {n : ℕ} (a b : Fin (n + 2) × Fin (n + 2)) (h2 : a.2 ≠ b.2) (h1 : a.1 ≠ b.1)
    (ha1 : a.1 ≠ 0) (hb1 : b.1 ≠ 0) (ha2 : a.2 ≠ 0) (hb2 : b.2 ≠ 0) :
    #{σ : Equiv.Perm (Fin (n + 2)) |
      σ b.2 = b.1 ∧ a.2 ≠ b.2 ∧ σ a.2 = a.1 ∧ σ 0 = 0} = (n - 1).factorial := by
  let f : Fin (n + 2) → Fin (n + 2) :=
    fun x => if x = b.2 then b.1 else if x = a.2 then a.1 else 0
  have hs : ({b.2, a.2, 0} : Finset (Fin (n + 2))).card = 3 := by
    rw [card_insert_of_notMem, card_pair ha2]
    simp [Ne.symm h2, hb2]
  have e : (univ.filter fun σ : Equiv.Perm (Fin (n + 2)) =>
      σ b.2 = b.1 ∧ a.2 ≠ b.2 ∧ σ a.2 = a.1 ∧ σ 0 = 0) =
      univ.filter fun σ : Equiv.Perm (Fin (n + 2)) =>
        ∀ x ∈ ({b.2, a.2, 0} : Finset (Fin (n + 2))), σ x = f x := by
    ext σ
    simp [f, h2, Ne.symm ha2, Ne.symm hb2]
  rw [e]
  convert card_perm_agree ({b.2, a.2, 0} : Finset (Fin (n + 2))) f ?_ using 1
  · congr
  · rw [hs, Fintype.card_fin]; congr 1
  · intro x hx y hy hxy
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      simp_all [f, Ne.symm h2, Ne.symm ha2, Ne.symm hb2, Ne.symm ha1, Ne.symm hb1]


/-- The Hessian of the permanent at the point of Mignon and Ressayre, in closed form. -/
noncomputable def hessEntry (n : ℕ) (a b : Fin (n + 2) × Fin (n + 2)) : ℂ :=
  if a.2 ≠ b.2 ∧ a.1 ≠ b.1 then
    (n.factorial : ℂ) - ((n + 2 : ℕ) : ℂ) *
      (if a.1 ≠ 0 ∧ b.1 ≠ 0 ∧ a.2 ≠ 0 ∧ b.2 ≠ 0 then ((n - 1).factorial : ℂ) else 0)
  else 0

theorem hess_perm_entry (n : ℕ) (a b : Fin (n + 2) × Fin (n + 2)) :
    eval (mrPoint n) (pderiv a (pderiv b (PEqualNP.Gct.permPoly ℂ (n + 2)))) =
      hessEntry n a b := by
  rw [hess_perm_sum]
  have split : ∀ σ : Equiv.Perm (Fin (n + 2)),
      (if σ b.2 = b.1 ∧ a.2 ≠ b.2 ∧ σ a.2 = a.1 then
        (if a.2 ≠ 0 ∧ b.2 ≠ 0 ∧ σ 0 = 0 then 1 - ((n + 2 : ℕ) : ℂ) else 1) else 0) =
      (if σ b.2 = b.1 ∧ a.2 ≠ b.2 ∧ σ a.2 = a.1 then 1 else 0) +
      (if a.2 ≠ 0 ∧ b.2 ≠ 0 then
        (if σ b.2 = b.1 ∧ a.2 ≠ b.2 ∧ σ a.2 = a.1 ∧ σ 0 = 0 then -((n + 2 : ℕ) : ℂ) else 0)
        else 0) := by
    intro σ
    by_cases hC : σ b.2 = b.1 ∧ a.2 ≠ b.2 ∧ σ a.2 = a.1
    · by_cases hD : a.2 ≠ 0 ∧ b.2 ≠ 0
      · by_cases h0 : σ 0 = 0
        · simp only [hC, hD, h0, ne_eq, not_false_eq_true, and_self, if_true]; ring
        · simp [hC, hD, h0]
      · have : ¬ (a.2 ≠ 0 ∧ b.2 ≠ 0 ∧ σ 0 = 0) := fun h => hD ⟨h.1, h.2.1⟩
        simp only [hC, if_true, this, if_false, hD]; ring
    · have : ¬ (σ b.2 = b.1 ∧ a.2 ≠ b.2 ∧ σ a.2 = a.1 ∧ σ 0 = 0) :=
        fun h => hC ⟨h.1, h.2.1, h.2.2.1⟩
      simp [hC, this]
  rw [sum_congr rfl fun σ _ => split σ, sum_add_distrib, sum_boole]
  unfold hessEntry
  by_cases hab : a.2 ≠ b.2 ∧ a.1 ≠ b.1
  · rw [if_pos hab, card_two a b hab.1 hab.2]
    by_cases hD : a.2 ≠ 0 ∧ b.2 ≠ 0
    · simp only [hD, ne_eq, not_false_eq_true, and_self, if_true]
      rw [← sum_filter, sum_const, nsmul_eq_mul]
      by_cases h1 : a.1 ≠ 0 ∧ b.1 ≠ 0
      · rw [card_three a b hab.1 hab.2 h1.1 h1.2 hD.1 hD.2]
        simp only [h1, hD, ne_eq, not_false_eq_true, and_self, if_true]
        ring
      · have hz : (univ.filter fun σ : Equiv.Perm (Fin (n + 2)) =>
            σ b.2 = b.1 ∧ a.2 ≠ b.2 ∧ σ a.2 = a.1 ∧ σ 0 = 0) = ∅ := by
          rw [filter_eq_empty_iff]
          rintro σ - ⟨hb, -, ha, h0⟩
          apply h1
          refine ⟨fun e => hD.1 (σ.injective (by rw [ha, h0, e])),
            fun e => hD.2 (σ.injective (by rw [hb, h0, e]))⟩
        have : ¬ (a.1 ≠ 0 ∧ b.1 ≠ 0 ∧ a.2 ≠ 0 ∧ b.2 ≠ 0) := fun h => h1 ⟨h.1, h.2.1⟩
        rw [hz, card_empty, if_neg (fun h => h1 ⟨h.1, h.2.1⟩)]
        simp
    · have : ¬ (a.1 ≠ 0 ∧ b.1 ≠ 0 ∧ a.2 ≠ 0 ∧ b.2 ≠ 0) := fun h => hD ⟨h.2.2.1, h.2.2.2⟩
      simp [hD, this]
  · rw [if_neg hab]
    have hz : (univ.filter fun σ : Equiv.Perm (Fin (n + 2)) =>
        σ b.2 = b.1 ∧ a.2 ≠ b.2 ∧ σ a.2 = a.1) = ∅ := by
      rw [filter_eq_empty_iff]
      rintro σ - ⟨hb, h2, ha⟩
      exact hab ⟨h2, fun e => h2 (σ.injective (by rw [ha, hb, e]))⟩
    rw [hz]
    have hz' : ∀ σ : Equiv.Perm (Fin (n + 2)),
        ¬ (σ b.2 = b.1 ∧ a.2 ≠ b.2 ∧ σ a.2 = a.1 ∧ σ 0 = 0) := by
      rintro σ ⟨hb, h2, ha, -⟩
      exact hab ⟨h2, fun e => h2 (σ.injective (by rw [ha, hb, e]))⟩
    simp [hz']


/-- The permanent vanishes at the point of Mignon and Ressayre. -/
theorem perm_mrPoint (n : ℕ) : eval (mrPoint n) (PEqualNP.Gct.permPoly ℂ (n + 2)) = 0 := by
  simp only [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply, map_sum]
  have hσ : ∀ σ : Equiv.Perm (Fin (n + 2)),
      eval (mrPoint n) (∏ i, (X (σ i, i) : MvPolynomial (Fin (n + 2) × Fin (n + 2)) ℂ)) =
        1 + (if σ 0 = 0 then -((n + 2 : ℕ) : ℂ) else 0) := by
    intro σ
    rw [eval_mon_mrPoint]
    by_cases h : σ 0 = 0 <;> simp [h]; ring
  rw [sum_congr rfl fun σ _ => hσ σ, sum_add_distrib, ← sum_filter, sum_const, sum_const,
    card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, nsmul_eq_mul]
  have hc : #{σ : Equiv.Perm (Fin (n + 2)) | σ 0 = 0} = (n + 1).factorial := by
    have := card_perm_fix ({0} : Finset (Fin (n + 2)))
    rw [card_singleton, Fintype.card_fin] at this
    convert this using 2 <;> first | omega | (ext σ; simp)
  rw [hc, Nat.factorial_succ (n + 1)]
  push_cast
  ring

/-- The product of the closed-form Hessian with a vector, in the form of `hess_kernel`. -/
theorem hess_mulVec (n : ℕ) (v : Fin (n + 2) × Fin (n + 2) → ℂ) (i j : Fin (n + 2)) :
    (Matrix.of (hessEntry n)).mulVec v (i, j) =
      (n.factorial : ℂ) * (∑ k, ∑ l, if k ≠ i ∧ l ≠ j then v (k, l) else 0) -
        (if i ≠ 0 ∧ j ≠ 0 then
          (((n + 2 : ℕ) : ℂ) * ((n - 1).factorial : ℂ)) *
            (∑ k, ∑ l, if k ≠ i ∧ k ≠ 0 ∧ l ≠ j ∧ l ≠ 0 then v (k, l) else 0) else 0) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Fintype.sum_prod_type]
  have pt : ∀ k l, hessEntry n (i, j) (k, l) * v (k, l) =
      (n.factorial : ℂ) * (if k ≠ i ∧ l ≠ j then v (k, l) else 0) -
        (if i ≠ 0 ∧ j ≠ 0 then (((n + 2 : ℕ) : ℂ) * ((n - 1).factorial : ℂ)) *
          (if k ≠ i ∧ k ≠ 0 ∧ l ≠ j ∧ l ≠ 0 then v (k, l) else 0) else 0) := by
    intro k l
    unfold hessEntry
    dsimp only
    have e1 : (j ≠ l) = (l ≠ j) := propext ne_comm
    have e2 : (i ≠ k) = (k ≠ i) := propext ne_comm
    simp only [e1, e2]
    clear e1 e2
    split_ifs <;> first | (exfalso; tauto) | ring
  simp only [pt]
  by_cases hij : i ≠ 0 ∧ j ≠ 0
  · obtain ⟨hi, hj⟩ := hij
    simp only [hi, hj, ne_eq, not_false_eq_true, and_self, if_true, sum_sub_distrib, ← mul_sum]
  · simp only [hij, if_false, sub_zero, ← mul_sum]

end PEqualNP.Gct.Helpers
