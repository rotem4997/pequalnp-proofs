import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6258

lemma key (d : ℕ) : 94 * d ≤ (d * d - d) + 2256 := by
  have h : d ≤ d * d := Nat.le_mul_self d
  have h2 : d * d - d + d = d * d := Nat.sub_add_cancel h
  rcases le_or_gt d 47 with h1 | h1
  · interval_cases d <;> simp
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le (show 48 ≤ d from h1)
    nlinarith [h2, Nat.zero_le (e * e)]

lemma main {α β : Type*} [DecidableEq α] [DecidableEq β] (E : Finset (α × β))
    (h : ∀ a b c d, a ≠ b → c ≠ d → ¬((a, c) ∈ E ∧ (b, c) ∈ E ∧ (a, d) ∈ E ∧ (b, d) ∈ E))
    (hm : (E.image Prod.fst).card ≤ 2208) :
    E.card ≤ 24 * ((E.image Prod.fst).card + (E.image Prod.snd).card - 1) := by
  classical
  let S : β → Finset α := fun c => (E.filter (fun p => p.2 = c)).image Prod.fst
  have hS : ∀ c a, a ∈ S c ↔ (a, c) ∈ E := by
    intro c a
    simp only [S, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨a', c'⟩, ⟨hp, rfl⟩, rfl⟩
      exact hp
    · intro hp
      exact ⟨(a, c), ⟨hp, rfl⟩, rfl⟩
  have hcard : E.card = ∑ c ∈ E.image Prod.snd, (S c).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := E.image Prod.snd)
      (fun p hp => Finset.mem_image_of_mem _ hp)]
    apply Finset.sum_congr rfl
    intro c _
    symm
    apply Finset.card_image_of_injOn
    intro p hp q hq hpq
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hp hq
    exact Prod.ext hpq (hp.2.trans hq.2.symm)
  have hdisj : ∑ c ∈ E.image Prod.snd, (S c).offDiag.card ≤ (E.image Prod.fst).offDiag.card := by
    rw [← Finset.card_biUnion]
    · apply Finset.card_le_card
      rintro ⟨a, b⟩ hp
      simp only [Finset.mem_biUnion, Finset.mem_offDiag, hS] at hp
      obtain ⟨c, _, h1, h2, h3⟩ := hp
      rw [Finset.mem_offDiag]
      exact ⟨Finset.mem_image_of_mem Prod.fst h1, Finset.mem_image_of_mem Prod.fst h2, h3⟩
    · intro c _ c' _ hcc
      show Disjoint (S c).offDiag (S c').offDiag
      rw [Finset.disjoint_left]
      rintro ⟨a, b⟩ h1 h2
      simp only [Finset.mem_offDiag, hS] at h1 h2
      exact h a b c c' h1.2.2 hcc ⟨h1.1, h1.2.1, h2.1, h2.2.1⟩
  simp only [Finset.offDiag_card] at hdisj
  have hsum : 94 * E.card ≤ ∑ c ∈ E.image Prod.snd, ((S c).card * (S c).card - (S c).card)
      + 2256 * (E.image Prod.snd).card := by
    rw [hcard, Finset.mul_sum]
    calc ∑ c ∈ E.image Prod.snd, 94 * (S c).card
        ≤ ∑ c ∈ E.image Prod.snd, (((S c).card * (S c).card - (S c).card) + 2256) :=
          Finset.sum_le_sum (fun c _ => key _)
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_comm]
  rcases Nat.eq_zero_or_pos (E.image Prod.fst).card with h0 | h0
  · have : E = ∅ := by simpa using h0
    simp [this]
  · have h3 : (E.image Prod.fst).card * (E.image Prod.fst).card - (E.image Prod.fst).card
        ≤ 2208 * ((E.image Prod.fst).card - 1) := by
      obtain ⟨m, hm'⟩ : ∃ m, (E.image Prod.fst).card = m + 1 :=
        ⟨(E.image Prod.fst).card - 1, by omega⟩
      rw [hm'] at hm ⊢
      have h4 : (m + 1) * (m + 1) - (m + 1) = (m + 1) * m := by
        rw [Nat.sub_eq_iff_eq_add (by nlinarith)]
        ring
      rw [h4, Nat.add_sub_cancel]
      nlinarith
    omega

end PEqualNP.Outside.L_meta_6258

theorem PEqualNP.Outside.L_meta_6258 : ∀ {x1 : ℕ} (x2 : Finset (Fin x1 × Fin x1)), (∀ (x3 x4 x5 x6 : Fin x1), x3 ≠ x4 → x5 ≠ x6 → ¬((x3, x5) ∈ x2 ∧ (x4, x5) ∈ x2 ∧ (x3, x6) ∈ x2 ∧ (x4, x6) ∈ x2)) → (Finset.image Prod.fst x2).card ≤ (2208 : ℕ) ∨ (Finset.image Prod.snd x2).card ≤ (2208 : ℕ) → x2.card ≤ (24 : ℕ) * ((Finset.image Prod.fst x2).card + (Finset.image Prod.snd x2).card - (1 : ℕ)) := by
  intro n E h hor
  rcases hor with hm | hm
  · exact PEqualNP.Outside.L_meta_6258.main E h hm
  · have e1 : (E.image Prod.swap).image Prod.fst = E.image Prod.snd := by
      rw [Finset.image_image]; rfl
    have e2 : (E.image Prod.swap).image Prod.snd = E.image Prod.fst := by
      rw [Finset.image_image]; rfl
    have e3 : (E.image Prod.swap).card = E.card :=
      Finset.card_image_of_injective _ Prod.swap_injective
    have hmem : ∀ a b, (a, b) ∈ E.image Prod.swap ↔ (b, a) ∈ E := by
      intro a b
      simp [Finset.mem_image]
    have := PEqualNP.Outside.L_meta_6258.main (E.image Prod.swap)
      (by
        intro a b c d hab hcd
        simp only [hmem]
        intro hh
        exact h c d a b hcd hab ⟨hh.1, hh.2.2.1, hh.2.1, hh.2.2.2⟩)
      (by rw [e1]; exact hm)
    rw [e1, e2, e3] at this
    omega
