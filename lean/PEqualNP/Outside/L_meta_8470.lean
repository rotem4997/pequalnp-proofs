import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8470

def inc (a b : ℕ) : Bool := [0, 5, 7, 17, 20].contains ((b + 21 - a) % 21)

def chk : Bool :=
  (List.range 21).all fun a => (List.range 21).all fun a' => (List.range 21).all fun b =>
    (List.range 21).all fun b' =>
      (a == a') || (b == b') || !(inc a b && inc a b' && inc a' b && inc a' b')

theorem chk_true : chk = true := by decide +kernel

theorem inc_iff (a b : ℕ) :
    inc a b = true ↔ (b + (21 : ℕ) - a) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)] := by
  simp [inc]

theorem c4 (a a' b b' : Fin 21) (ha : a ≠ a') (hb : b ≠ b')
    (h1 : inc a.val b.val = true) (h2 : inc a.val b'.val = true)
    (h3 : inc a'.val b.val = true) (h4 : inc a'.val b'.val = true) : False := by
  have h := chk_true
  simp only [chk, List.all_eq_true, List.mem_range] at h
  have h5 := h a.val a.isLt a'.val a'.isLt b.val b.isLt b'.val b'.isLt
  have ha' : a.val ≠ a'.val := Fin.val_ne_of_ne ha
  have hb' : b.val ≠ b'.val := Fin.val_ne_of_ne hb
  simp [h1, h2, h3, h4, ha', hb'] at h5

def edges : Finset (Fin 21 × Fin 21) := Finset.univ.filter (fun q => inc q.1.val q.2.val = true)

theorem edges_card : edges.card = 105 := by decide +kernel

theorem main : ∀ (x1 : Finset (Finset (Fin (21 : ℕ)) × Finset (Fin (21 : ℕ)))), (∀ x2 ∈ x1, x2.1.Nonempty ∧ x2.2.Nonempty ∧ ∀ x4 ∈ x2.1, ∀ x6 ∈ x2.2, (↑x6 + (21 : ℕ) - ↑x4) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) → (∀ (x3 x4 : Fin (21 : ℕ)), (↑x4 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)] → ∃ x6 ∈ x1, x3 ∈ x6.1 ∧ x4 ∈ x6.2) → (105 : ℕ) ≤ ∑ x4 ∈ x1, (x4.1.card + x4.2.card - (1 : ℕ)) := by
  intro S h1 h2
  have hsub : edges ⊆ S.biUnion (fun p => p.1 ×ˢ p.2) := by
    intro q hq
    have hq2 : inc q.1.val q.2.val = true := (Finset.mem_filter.mp hq).2
    obtain ⟨p, hp, ha, hb⟩ := h2 q.1 q.2 ((inc_iff _ _).mp hq2)
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_product.mpr ⟨ha, hb⟩⟩
  calc 105 = edges.card := edges_card.symm
    _ ≤ (S.biUnion fun p => p.1 ×ˢ p.2).card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ S, (p.1 ×ˢ p.2).card := Finset.card_biUnion_le
    _ ≤ ∑ p ∈ S, (p.1.card + p.2.card - 1) := by
      refine Finset.sum_le_sum (fun p hp => ?_)
      rw [Finset.card_product]
      obtain ⟨n1, n2, h3⟩ := h1 p hp
      have c1 := Finset.card_pos.mpr n1
      have c2 := Finset.card_pos.mpr n2
      by_cases hc : 1 < p.1.card ∧ 1 < p.2.card
      · exfalso
        obtain ⟨a, ha, a', ha', hne⟩ := Finset.one_lt_card.mp hc.1
        obtain ⟨b, hb, b', hb', hne'⟩ := Finset.one_lt_card.mp hc.2
        exact c4 a a' b b' hne hne' ((inc_iff _ _).mpr (h3 a ha b hb))
          ((inc_iff _ _).mpr (h3 a ha b' hb')) ((inc_iff _ _).mpr (h3 a' ha' b hb))
          ((inc_iff _ _).mpr (h3 a' ha' b' hb'))
      · have h4 : p.1.card = 1 ∨ p.2.card = 1 := by omega
        rcases h4 with h | h
        · rw [h]; omega
        · rw [h]; omega

end PEqualNP.Outside.L_meta_8470

theorem PEqualNP.Outside.L_meta_8470 : ∀ (x1 : Finset (Finset (Fin (21 : ℕ)) × Finset (Fin (21 : ℕ)))), (∀ x2 ∈ x1, x2.1.Nonempty ∧ x2.2.Nonempty ∧ ∀ x4 ∈ x2.1, ∀ x6 ∈ x2.2, (↑x6 + (21 : ℕ) - ↑x4) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) → (∀ (x3 x4 : Fin (21 : ℕ)), (↑x4 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)] → ∃ x6 ∈ x1, x3 ∈ x6.1 ∧ x4 ∈ x6.2) → (105 : ℕ) ≤ ∑ x4 ∈ x1, (x4.1.card + x4.2.card - (1 : ℕ)) := PEqualNP.Outside.L_meta_8470.main
