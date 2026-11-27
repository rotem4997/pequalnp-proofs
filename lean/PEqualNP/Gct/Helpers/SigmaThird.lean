import PEqualNP.Defs
import PEqualNP.Gct.Helpers.PermHessian

/-! Helper for L-gct-062: the third partial derivatives of the permanent at the point of Mignon
and Ressayre, at three positions off the first row and column. -/

namespace PEqualNP.Gct.SigmaRed

open Finset MvPolynomial PEqualNP.Gct.Helpers

theorem ite_pos' {c : Prop} [Decidable c] (h : c) {α : Sort*} {t e : α} :
    (if c then t else e) = t := by simp [h]

theorem ite_neg' {c : Prop} [Decidable c] (h : ¬ c) {α : Sort*} {t e : α} :
    (if c then t else e) = e := by simp [h]

/-- The matching condition for three positions with pairwise distinct columns. -/
def Match3 {m : ℕ} (a b c : Fin m × Fin m) (σ : Equiv.Perm (Fin m)) : Prop :=
  σ c.2 = c.1 ∧ b.2 ≠ c.2 ∧ σ b.2 = b.1 ∧ a.2 ≠ b.2 ∧ a.2 ≠ c.2 ∧ σ a.2 = a.1

instance {m : ℕ} (a b c : Fin m × Fin m) : DecidablePred (Match3 a b c) := by
  intro σ; unfold Match3; infer_instance

theorem third_perm_sum (p : ℕ) (a b c : Fin (p + 2) × Fin (p + 2))
    (ha2 : a.2 ≠ 0) (hb2 : b.2 ≠ 0) (hc2 : c.2 ≠ 0) :
    eval (mrPoint p) (pderiv a (pderiv b (pderiv c (PEqualNP.Gct.permPoly ℂ (p + 2))))) =
      ∑ σ : Equiv.Perm (Fin (p + 2)),
        if Match3 a b c σ then (if σ 0 = 0 then 1 - ((p + 2 : ℕ) : ℂ) else 1) else 0 := by
  simp only [PEqualNP.Gct.permPoly, Matrix.permanent, Matrix.mvPolynomialX_apply, map_sum]
  refine sum_congr rfl fun σ _ => ?_
  rw [pderiv_perm_mon]
  by_cases hc : σ c.2 = c.1
  swap
  · rw [ite_neg' (fun h => hc h.2), map_zero, map_zero, map_zero, ite_neg' (fun h => hc h.1)]
  rw [ite_pos' ⟨mem_univ _, hc⟩, pderiv_perm_mon]
  by_cases hb : b.2 ≠ c.2 ∧ σ b.2 = b.1
  swap
  · rw [ite_neg', map_zero, map_zero, ite_neg']
    · rintro ⟨_, h1, h2, _⟩; exact hb ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact hb ⟨(mem_erase.mp h1).1, h2⟩
  rw [ite_pos' ⟨mem_erase.mpr ⟨hb.1, mem_univ _⟩, hb.2⟩, pderiv_perm_mon]
  by_cases ha : a.2 ≠ b.2 ∧ a.2 ≠ c.2 ∧ σ a.2 = a.1
  swap
  · rw [ite_neg', map_zero, ite_neg']
    · rintro ⟨_, _, _, h1, h2, h3⟩; exact ha ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2⟩
      have h1' := mem_erase.mp h1
      exact ha ⟨h1'.1, (mem_erase.mp h1'.2).1, h2⟩
  have hM : Match3 a b c σ := ⟨hc, hb.1, hb.2, ha.1, ha.2.1, ha.2.2⟩
  rw [ite_pos' ⟨mem_erase.mpr ⟨ha.1, mem_erase.mpr ⟨ha.2.1, mem_univ _⟩⟩, ha.2.2⟩,
    eval_mon_mrPoint, ite_pos' hM]
  have h0 : (0 : Fin (p + 2)) ∈ ((univ.erase c.2).erase b.2).erase a.2 := by
    simp [Ne.symm ha2, Ne.symm hb2, Ne.symm hc2]
  simp only [h0, true_and]

theorem card_match3 {m : ℕ} (a b c : Fin m × Fin m)
    (h2 : a.2 ≠ b.2 ∧ a.2 ≠ c.2 ∧ b.2 ≠ c.2) (h1 : a.1 ≠ b.1 ∧ a.1 ≠ c.1 ∧ b.1 ≠ c.1) :
    #{σ : Equiv.Perm (Fin m) | Match3 a b c σ} = (m - 3).factorial := by
  let f : Fin m → Fin m := fun x => if x = c.2 then c.1 else if x = b.2 then b.1 else a.1
  have hs : ({c.2, b.2, a.2} : Finset (Fin m)).card = 3 := by
    rw [card_insert_of_notMem, card_pair h2.1.symm]
    simp [Ne.symm h2.2.1, Ne.symm h2.2.2]
  have e : (univ.filter fun σ : Equiv.Perm (Fin m) => Match3 a b c σ) =
      univ.filter fun σ : Equiv.Perm (Fin m) =>
        ∀ x ∈ ({c.2, b.2, a.2} : Finset (Fin m)), σ x = f x := by
    ext σ
    simp [Match3, f, h2.1, h2.2.1, h2.2.2]
  rw [e]
  convert card_perm_agree ({c.2, b.2, a.2} : Finset (Fin m)) f ?_ using 1
  · congr
  · rw [hs, Fintype.card_fin]
  · intro x hx y hy hxy
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      simp_all [f, Ne.symm h2.1, Ne.symm h2.2.1, Ne.symm h2.2.2,
        Ne.symm h1.1, Ne.symm h1.2.1, Ne.symm h1.2.2]

theorem card_match3_zero {m : ℕ} (a b c : Fin (m + 1) × Fin (m + 1))
    (h2 : a.2 ≠ b.2 ∧ a.2 ≠ c.2 ∧ b.2 ≠ c.2) (h1 : a.1 ≠ b.1 ∧ a.1 ≠ c.1 ∧ b.1 ≠ c.1)
    (ha1 : a.1 ≠ 0) (ha2 : a.2 ≠ 0) (hb1 : b.1 ≠ 0) (hb2 : b.2 ≠ 0) (hc1 : c.1 ≠ 0)
    (hc2 : c.2 ≠ 0) :
    #{σ : Equiv.Perm (Fin (m + 1)) | Match3 a b c σ ∧ σ 0 = 0} = (m + 1 - 4).factorial := by
  let f : Fin (m + 1) → Fin (m + 1) :=
    fun x => if x = c.2 then c.1 else if x = b.2 then b.1 else if x = a.2 then a.1 else 0
  have hs : ({c.2, b.2, a.2, 0} : Finset (Fin (m + 1))).card = 4 := by
    rw [card_insert_of_notMem, card_insert_of_notMem, card_pair ha2]
    · simp [Ne.symm h2.1, hb2]
    · simp [Ne.symm h2.2.1, Ne.symm h2.2.2, hc2]
  have e : (univ.filter fun σ : Equiv.Perm (Fin (m + 1)) => Match3 a b c σ ∧ σ 0 = 0) =
      univ.filter fun σ : Equiv.Perm (Fin (m + 1)) =>
        ∀ x ∈ ({c.2, b.2, a.2, 0} : Finset (Fin (m + 1))), σ x = f x := by
    ext σ
    simp [Match3, f, h2.1, h2.2.1, h2.2.2, Ne.symm ha2, Ne.symm hb2, Ne.symm hc2]
    tauto
  rw [e]
  convert card_perm_agree ({c.2, b.2, a.2, 0} : Finset (Fin (m + 1))) f ?_ using 1
  · congr
  · rw [hs, Fintype.card_fin]
  · intro x hx y hy hxy
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp_all [f, Ne.symm h2.1, Ne.symm h2.2.1, Ne.symm h2.2.2,
        Ne.symm h1.1, Ne.symm h1.2.1, Ne.symm h1.2.2,
        Ne.symm ha1, Ne.symm hb1, Ne.symm hc1, Ne.symm ha2, Ne.symm hb2, Ne.symm hc2]

theorem third_perm_block (p : ℕ) (a b c : Fin (p + 2) × Fin (p + 2))
    (ha1 : a.1 ≠ 0) (ha2 : a.2 ≠ 0) (hb1 : b.1 ≠ 0) (hb2 : b.2 ≠ 0) (hc1 : c.1 ≠ 0) (hc2 : c.2 ≠ 0) :
    eval (mrPoint p) (pderiv a (pderiv b (pderiv c (PEqualNP.Gct.permPoly ℂ (p + 2))))) =
      if (a.1 ≠ b.1 ∧ a.1 ≠ c.1 ∧ b.1 ≠ c.1) ∧ (a.2 ≠ b.2 ∧ a.2 ≠ c.2 ∧ b.2 ≠ c.2) then
        ((p - 1).factorial : ℂ) - ((p + 2 : ℕ) : ℂ) * ((p - 2).factorial : ℂ) else 0 := by
  rw [third_perm_sum p a b c ha2 hb2 hc2]
  have split : ∀ σ : Equiv.Perm (Fin (p + 2)),
      (if Match3 a b c σ then (if σ 0 = 0 then 1 - ((p + 2 : ℕ) : ℂ) else 1) else 0) =
      (if Match3 a b c σ then 1 else 0) +
        (if Match3 a b c σ ∧ σ 0 = 0 then -((p + 2 : ℕ) : ℂ) else 0) := by
    intro σ
    by_cases hM : Match3 a b c σ
    · by_cases h0 : σ 0 = 0
      · simp only [hM, h0, and_self, ite_true]; ring
      · simp [hM, h0]
    · simp [hM]
  rw [sum_congr rfl fun σ _ => split σ, sum_add_distrib, sum_boole, ← sum_filter, sum_const,
    nsmul_eq_mul]
  by_cases hcond : (a.1 ≠ b.1 ∧ a.1 ≠ c.1 ∧ b.1 ≠ c.1) ∧ (a.2 ≠ b.2 ∧ a.2 ≠ c.2 ∧ b.2 ≠ c.2)
  · rw [ite_pos' hcond, card_match3 a b c hcond.2 hcond.1,
      card_match3_zero (m := p + 1) a b c hcond.2 hcond.1 ha1 ha2 hb1 hb2 hc1 hc2]
    have e1 : p + 2 - 3 = p - 1 := by omega
    have e2 : p + 1 + 1 - 4 = p - 2 := by omega
    rw [e1, e2]
    ring
  · rw [ite_neg' hcond]
    have hz : ∀ σ : Equiv.Perm (Fin (p + 2)), ¬ Match3 a b c σ := by
      rintro σ ⟨hc, hbc, hb, hab, hac, ha⟩
      apply hcond
      refine ⟨⟨?_, ?_, ?_⟩, hab, hac, hbc⟩
      · intro e; exact hab (σ.injective (by rw [ha, hb, e]))
      · intro e; exact hac (σ.injective (by rw [ha, hc, e]))
      · intro e; exact hbc (σ.injective (by rw [hb, hc, e]))
    simp [hz]

end PEqualNP.Gct.SigmaRed
