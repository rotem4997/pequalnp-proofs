import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7598

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem main {n : ℕ} (E : Finset (Fin n × Fin n))
    (hE : ∀ x x' y y' : Fin n, x ≠ x' → y ≠ y' → ¬((x, y) ∈ E ∧ (x', y) ∈ E ∧ (x, y') ∈ E ∧ (x', y') ∈ E))
    (ha : (E.image Prod.fst).card ≤ 2256) :
    E.card ≤ 24 * ((E.image Prod.fst).card + (E.image Prod.snd).card - 1) := by
  classical
  let A := E.image Prod.fst
  let B := E.image Prod.snd
  let N : Fin n → Finset (Fin n) := fun y => (E.filter fun p => p.2 = y).image Prod.fst
  have hN : ∀ x y, x ∈ N y ↔ (x, y) ∈ E := by
    intro x y
    simp only [N, Finset.mem_image, Finset.mem_filter, Prod.exists]
    constructor
    · rintro ⟨a, b, ⟨h, rfl⟩, rfl⟩; exact h
    · intro h; exact ⟨x, y, ⟨h, rfl⟩, rfl⟩
  have hc : E.card = ∑ y ∈ B, (N y).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := B) (fun p hp => Finset.mem_coe.2 (Finset.mem_image_of_mem _ hp))]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.card_image_of_injOn]
    rintro ⟨a, b⟩ h1 ⟨c, d⟩ h2 h
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at h1 h2 h
    rw [h, h1.2, h2.2]
  have hd : ∑ y ∈ B, (N y).offDiag.card ≤ A.offDiag.card := by
    rw [← Finset.card_biUnion]
    · refine Finset.card_le_card fun p hp => ?_
      simp only [Finset.mem_biUnion, Finset.mem_offDiag] at hp ⊢
      obtain ⟨y, _, h1, h2, h3⟩ := hp
      exact ⟨Finset.mem_image.2 ⟨(p.1, y), (hN p.1 y).1 h1, rfl⟩, Finset.mem_image.2 ⟨(p.2, y), (hN p.2 y).1 h2, rfl⟩, h3⟩
    · intro y _ y' _ hne
      refine Finset.disjoint_left.2 fun p h1 h2 => ?_
      simp only [Finset.mem_offDiag, hN] at h1 h2
      exact hE p.1 p.2 y y' h1.2.2 hne ⟨h1.1, h1.2.1, h2.1, h2.2.1⟩
  have tang : ∀ y ∈ B, 94 * ((N y).card : ℤ) ≤ ((N y).offDiag.card : ℤ) + 47 * 48 := by
    intro y _
    rw [Finset.offDiag_card]
    generalize (N y).card = d
    have : d ≤ d * d := Nat.le_mul_self d
    push_cast [Nat.cast_sub this]
    rcases le_total d 47 with h | h
    · have h' : (d : ℤ) ≤ 47 := by exact_mod_cast h
      nlinarith
    · rcases Nat.lt_or_ge d 48 with h2 | h2
      · have : d = 47 := by omega
        subst this; norm_num
      · have h' : (48 : ℤ) ≤ d := by exact_mod_cast h2
        nlinarith
  have hs := Finset.sum_le_sum tang
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hs
  have hc' : (E.card : ℤ) = ∑ y ∈ B, ((N y).card : ℤ) := by rw [hc]; push_cast; rfl
  have hd' : (∑ y ∈ B, ((N y).offDiag.card : ℤ)) ≤ (A.offDiag.card : ℤ) := by exact_mod_cast hd
  rw [← hc'] at hs
  rw [Finset.offDiag_card] at hd'
  change A.card ≤ 2256 at ha
  change E.card ≤ 24 * (A.card + B.card - 1)
  rcases Nat.eq_zero_or_pos A.card with h0 | h0
  · have : E = ∅ := by
      have := Finset.card_eq_zero.1 h0
      exact Finset.image_eq_empty.1 this
    subst this
    simp
  · have h1 : A.card ≤ A.card * A.card := Nat.le_mul_self _
    push_cast [Nat.cast_sub h1] at hd'
    have h3 : (A.card : ℤ) ≤ 2256 := by exact_mod_cast ha
    have h4 : (1 : ℤ) ≤ A.card := by exact_mod_cast h0
    have : (E.card : ℤ) ≤ 24 * ((A.card : ℤ) + B.card - 1) := by nlinarith
    zify [show 1 ≤ A.card + B.card by omega]
    exact this

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_7598

theorem PEqualNP.Outside.L_meta_7598 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)), (∀ (x3 x4 x5 x6 : Fin x1), x3 ≠ x4 → x5 ≠ x6 → ¬((x3, x5) ∈ x2 ∧ (x4, x5) ∈ x2 ∧ (x3, x6) ∈ x2 ∧ (x4, x6) ∈ x2)) → Min.min (Finset.image Prod.fst x2).card (Finset.image Prod.snd x2).card ≤ (2256 : ℕ) → x2.card ≤ (24 : ℕ) * ((Finset.image Prod.fst x2).card + (Finset.image Prod.snd x2).card - (1 : ℕ)) := by
  intro n E hE hm
  classical
  rcases le_total (Finset.image Prod.fst E).card (Finset.image Prod.snd E).card with h | h
  · rw [min_eq_left h] at hm
    exact PEqualNP.Outside.L_meta_7598.main E (fun x x' y y' hx hy hh => hE x x' y y' hx hy hh) hm
  · rw [min_eq_right h] at hm
    have := PEqualNP.Outside.L_meta_7598.main (E.image Prod.swap) (by
      intro x x' y y' hx hy hh
      have e : ∀ a b : Fin n, (a, b) ∈ E.image Prod.swap ↔ (b, a) ∈ E := by
        intro a b
        simp only [Finset.mem_image, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
        constructor
        · rintro ⟨c, d, h1, rfl, rfl⟩; exact h1
        · intro h1; exact ⟨b, a, h1, rfl, rfl⟩
      rw [e, e, e, e] at hh
      exact hE y y' x x' hy hx ⟨hh.1, hh.2.2.1, hh.2.1, hh.2.2.2⟩) (by
      rw [Finset.image_image]; exact hm)
    rw [Finset.card_image_of_injective _ Prod.swap_injective, Finset.image_image, Finset.image_image] at this
    have e1 : (Prod.fst ∘ Prod.swap : Fin n × Fin n → Fin n) = Prod.snd := rfl
    have e2 : (Prod.snd ∘ Prod.swap : Fin n × Fin n → Fin n) = Prod.fst := rfl
    rw [e1, e2] at this
    omega
