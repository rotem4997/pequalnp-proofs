import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8923
open PEqualNP.CircuitLowerBounds



theorem inc_card : (PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3).card = 52 := by
  decide +kernel

theorem inc_k22 : ∀ (p p' l l' : Fin 13), p ≠ p' → l ≠ l' →
    ¬((p, l) ∈ PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3 ∧
      (p, l') ∈ PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3 ∧
      (p', l) ∈ PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3 ∧
      (p', l') ∈ PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3) := by
  decide +kernel

theorem inc_row : ∀ p : Fin 13, (Finset.univ.filter fun l : Fin 13 =>
    (p, l) ∈ PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3).card ≤ 4 := by
  decide +kernel

theorem inc_col : ∀ l : Fin 13, (Finset.univ.filter fun p : Fin 13 =>
    (p, l) ∈ PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3).card ≤ 4 := by
  decide +kernel

theorem rect (A B : Finset (Fin 13))
    (h : A ×ˢ B ⊆ PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3) :
    5 * (A.card * B.card) ≤ 4 * (A.card + B.card) := by
  by_cases hA : A.card = 0
  · rw [hA]; omega
  by_cases hB : B.card = 0
  · rw [hB]; omega
  obtain ⟨p, hp⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hA)
  obtain ⟨l, hl⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hB)
  have hB4 : B.card ≤ 4 := le_trans (Finset.card_le_card (fun l' hl' =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, h (Finset.mem_product.2 ⟨hp, hl'⟩)⟩)) (inc_row p)
  have hA4 : A.card ≤ 4 := le_trans (Finset.card_le_card (fun p' hp' =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, h (Finset.mem_product.2 ⟨hp', hl⟩)⟩)) (inc_col l)
  have h1 : A.card ≤ 1 ∨ B.card ≤ 1 := by
    by_contra hc
    push_neg at hc
    obtain ⟨a, ha, a', ha', haa⟩ := Finset.one_lt_card.1 hc.1
    obtain ⟨b, hb, b', hb', hbb⟩ := Finset.one_lt_card.1 hc.2
    exact inc_k22 a a' b b' haa hbb ⟨h (Finset.mem_product.2 ⟨ha, hb⟩), h (Finset.mem_product.2 ⟨ha, hb'⟩),
      h (Finset.mem_product.2 ⟨ha', hb⟩), h (Finset.mem_product.2 ⟨ha', hb'⟩)⟩
  rcases h1 with h1 | h1
  · have : A.card = 1 := by omega
    rw [this]; omega
  · have : B.card = 1 := by omega
    rw [this]; omega

end PEqualNP.Outside.L_meta_8923

open PEqualNP.Outside.L_meta_8923 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_8923 : ∀ (x1 : Finset (Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ)))), (x1.biUnion fun (x2 : Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ))) => x2.1 ×ˢ x2.2) = PEqualNP.HeptadCover.incidences PEqualNP.HeptadCover.singerLines3 → (65 : ℕ) ≤ ∑ x3 ∈ x1, (x3.1.card + x3.2.card) := by
  intro F hF
  have h1 : 52 ≤ ∑ r ∈ F, (r.1.card * r.2.card) := by
    rw [← inc_card, ← hF]
    refine le_trans Finset.card_biUnion_le ?_
    apply Finset.sum_le_sum
    intro r _
    rw [Finset.card_product]
  have h2 : ∑ r ∈ F, 5 * (r.1.card * r.2.card) ≤ ∑ r ∈ F, 4 * (r.1.card + r.2.card) := by
    apply Finset.sum_le_sum
    intro r hr
    apply rect
    rw [← hF]
    exact Finset.subset_biUnion_of_mem (fun x : Finset (Fin 13) × Finset (Fin 13) => x.1 ×ˢ x.2) hr
  rw [← Finset.mul_sum, ← Finset.mul_sum] at h2
  omega
