import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7850

open Finset

lemma sep_card (n : ℕ) (e : Sym2 (Fin n)) (he : ¬ e.IsDiag) :
    2 * (univ.filter (fun c : Fin n → Bool => ¬ (Sym2.map c e).IsDiag)).card
      = Fintype.card (Fin n → Bool) := by
  induction e with
  | _ a b =>
  have hab : a ≠ b := by simpa using he
  have key : ∀ c : Fin n → Bool, (Sym2.map c s(a, b)).IsDiag ↔ c a = c b := fun c => by simp
  have hb : ∀ c : Fin n → Bool, Function.update c a (!c a) b = c b :=
    fun c => Function.update_of_ne hab.symm _ _
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin n → Bool))) (fun c : Fin n → Bool => ¬ (Sym2.map c s(a, b)).IsDiag)
  have hbij : (univ.filter (fun c : Fin n → Bool => ¬ (Sym2.map c s(a, b)).IsDiag)).card
      = (univ.filter (fun c : Fin n → Bool => ¬ ¬ (Sym2.map c s(a, b)).IsDiag)).card := by
    refine Finset.card_nbij' (fun c => Function.update c a (!c a))
      (fun c => Function.update c a (!c a)) ?_ ?_ ?_ ?_
    · intro c hc
      have hc' : ¬ c a = c b := by simpa [key] using hc
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [key]; beta_reduce; rw [Function.update_self, hb]
      revert hc'; cases c a <;> cases c b <;> simp
    · intro c hc
      have hc' : c a = c b := by simpa [key] using hc
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [key]; beta_reduce; rw [Function.update_self, hb]
      revert hc'; cases c a <;> cases c b <;> simp
    · intro c _; simp
    · intro c _; simp
  rw [← Finset.card_univ, ← hsum, ← hbij]; ring

theorem main : ∀ (x1 : ℕ) (x2 : Finset (Sym2 (Fin x1))), (∀ x3 ∈ x2, ¬x3.IsDiag) → ∃ (x4 : Fin x1 → Bool), x2.card ≤ (2 : ℕ) * {x5 ∈ x2 | ¬(Sym2.map x4 x5).IsDiag}.card := by
  intro x1 x2 hx
  by_contra h
  push Not at h
  have h1 : ∑ c : Fin x1 → Bool, 2 * {x5 ∈ x2 | ¬(Sym2.map c x5).IsDiag}.card
      < ∑ _c : Fin x1 → Bool, x2.card :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun c _ => h c)
  have h2 : ∑ c : Fin x1 → Bool, 2 * {x5 ∈ x2 | ¬(Sym2.map c x5).IsDiag}.card
      = ∑ e ∈ x2, 2 * (univ.filter (fun c : Fin x1 → Bool => ¬ (Sym2.map c e).IsDiag)).card := by
    simp_rw [← Finset.mul_sum, Finset.card_filter]
    rw [Finset.sum_comm]
  rw [h2, Finset.sum_congr rfl (fun e he => sep_card x1 e (hx e he))] at h1
  simp only [Finset.sum_const, smul_eq_mul, Finset.card_univ] at h1
  rw [mul_comm] at h1
  exact lt_irrefl _ h1

end PEqualNP.Outside.L_meta_7850

theorem PEqualNP.Outside.L_meta_7850 : ∀ (x1 : ℕ) (x2 : Finset (Sym2 (Fin x1))), (∀ x3 ∈ x2, ¬x3.IsDiag) → ∃ (x4 : Fin x1 → Bool), x2.card ≤ (2 : ℕ) * {x5 ∈ x2 | ¬(Sym2.map x4 x5).IsDiag}.card :=
  PEqualNP.Outside.L_meta_7850.main
