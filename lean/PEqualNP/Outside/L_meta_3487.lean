import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3487

open Finset

theorem per_deg (d k : ℕ) (hk : k + d = d * d) : 174 * d ≤ k + 7656 := by
  rcases le_or_gt d 87 with h | h
  · nlinarith
  · nlinarith

theorem key {α β : Type*} [DecidableEq α] [DecidableEq β] (E : Finset (α × β))
    (h : ∀ (p p' : α) (l l' : β), p ≠ p' → l ≠ l' →
      ¬((p, l) ∈ E ∧ (p', l) ∈ E ∧ (p, l') ∈ E ∧ (p', l') ∈ E)) :
    174 * E.card + (E.image Prod.fst).card ≤
      (E.image Prod.fst).card * (E.image Prod.fst).card + 7656 * (E.image Prod.snd).card := by
  set P := E.image Prod.fst with hPdef
  set L := E.image Prod.snd with hLdef
  set F : β → Finset (α × β) := fun l => E.filter (fun x => x.2 = l) with hF
  have hE : E.card = ∑ l ∈ L, (F l).card := card_eq_sum_card_image Prod.snd E
  have hinj : ∑ l ∈ L, ((F l).offDiag).card ≤ P.offDiag.card := by
    rw [← card_sigma]
    apply card_le_card_of_injOn (fun z => (z.2.1.1, z.2.2.1))
    · rintro ⟨l, ⟨p, m⟩, ⟨q, n⟩⟩ hz
      simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_offDiag, hF, mem_filter] at hz
      obtain ⟨_, ⟨h1, hm⟩, ⟨h2, hn⟩, hne⟩ := hz
      subst hm
      subst hn
      simp only [mem_coe, mem_offDiag, hPdef, mem_image]
      refine ⟨⟨_, h1, rfl⟩, ⟨_, h2, rfl⟩, ?_⟩
      intro he
      apply hne
      rw [he]
    · rintro ⟨l, ⟨p, m⟩, ⟨q, n⟩⟩ hz ⟨l', ⟨p', m'⟩, ⟨q', n'⟩⟩ hz' heq
      simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_offDiag, hF, mem_filter] at hz hz'
      obtain ⟨_, ⟨h1, hm⟩, ⟨h2, hn⟩, hne⟩ := hz
      obtain ⟨_, ⟨h1', hm'⟩, ⟨h2', hn'⟩, hne'⟩ := hz'
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hp, hq⟩ := heq
      subst hp
      subst hq
      rw [hm] at h1
      rw [hn] at h2
      rw [hm'] at h1'
      rw [hn'] at h2'
      have hpq : p ≠ q := by
        intro he
        apply hne
        rw [he, hm, hn]
      by_cases hll : l = l'
      · subst hll
        rw [hm, hn, hm', hn']
      · exact absurd ⟨h1, h2, h1', h2'⟩ (h p q l l' hpq hll)
  have hdeg : ∀ l ∈ L, 174 * (F l).card ≤ ((F l).offDiag).card + 7656 := by
    intro l _
    apply per_deg
    rw [offDiag_card]
    exact Nat.sub_add_cancel (Nat.le_mul_self _)
  have hsum : 174 * E.card ≤ P.offDiag.card + 7656 * L.card := by
    rw [hE, mul_sum]
    calc ∑ l ∈ L, 174 * (F l).card ≤ ∑ l ∈ L, (((F l).offDiag).card + 7656) := sum_le_sum hdeg
      _ = ∑ l ∈ L, ((F l).offDiag).card + 7656 * L.card := by
        rw [sum_add_distrib, sum_const, smul_eq_mul, mul_comm]
      _ ≤ P.offDiag.card + 7656 * L.card := by omega
  have hP : P.offDiag.card + P.card = P.card * P.card := by
    rw [offDiag_card]
    exact Nat.sub_add_cancel (Nat.le_mul_self _)
  omega

theorem fin_bound (e a b : ℕ) (ha : a ≤ 7656) (h1 : 1 ≤ a)
    (hk : 174 * e + a ≤ a * a + 7656 * b) : e ≤ 44 * (a + b - 1) := by
  have h2 : 174 * e + 7656 ≤ 7656 * a + 7656 * b := by nlinarith
  omega

end PEqualNP.Outside.L_meta_3487

open PEqualNP.Outside.L_meta_3487 in
theorem PEqualNP.Outside.L_meta_3487 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)), (∀ (x3 x4 x5 x6 : Fin x1), x3 ≠ x4 → x5 ≠ x6 → ¬((x3, x5) ∈ x2 ∧ (x4, x5) ∈ x2 ∧ (x3, x6) ∈ x2 ∧ (x4, x6) ∈ x2)) → Min.min (Finset.image Prod.fst x2).card (Finset.image Prod.snd x2).card ≤ (7656 : ℕ) → x2.card ≤ (44 : ℕ) * ((Finset.image Prod.fst x2).card + (Finset.image Prod.snd x2).card - (1 : ℕ)) := by
  intro n E h hmin
  rcases E.eq_empty_or_nonempty with hE | hE
  · subst hE
    simp
  have ha1 : 1 ≤ (E.image Prod.fst).card := Finset.card_pos.2 (hE.image _)
  have hb1 : 1 ≤ (E.image Prod.snd).card := Finset.card_pos.2 (hE.image _)
  rcases min_le_iff.1 hmin with ha | hb
  · exact fin_bound _ _ _ ha ha1 (key E h)
  · set E' := E.image Prod.swap with hE'
    have hmem : ∀ x y : Fin n, (x, y) ∈ E' ↔ (y, x) ∈ E := by
      intro x y
      simp [hE']
    have hc : E'.card = E.card := Finset.card_image_of_injective _ Prod.swap_injective
    have hf : E'.image Prod.fst = E.image Prod.snd := by
      ext x
      simp [hE']
    have hs : E'.image Prod.snd = E.image Prod.fst := by
      ext x
      simp [hE']
    have h' : ∀ (p p' : Fin n) (l l' : Fin n), p ≠ p' → l ≠ l' →
        ¬((p, l) ∈ E' ∧ (p', l) ∈ E' ∧ (p, l') ∈ E' ∧ (p', l') ∈ E') := by
      intro p p' l l' hp hl hh
      rw [hmem, hmem, hmem, hmem] at hh
      obtain ⟨h1, h2, h3, h4⟩ := hh
      exact h l l' p p' hl hp ⟨h1, h3, h2, h4⟩
    have hk := key E' h'
    rw [hc, hf, hs] at hk
    have := fin_bound _ _ _ hb hb1 hk
    rw [Nat.add_comm (E.image Prod.fst).card]
    exact this
