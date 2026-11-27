import Mathlib
import PEqualNP.Defs

-- If x5 is empty, take every point. If x4 lies on a line L, take the points of L on no line
-- of x5: they miss the point r where L meets a line of x5, so there are at most three, all
-- on L, and every other point lies on a line meeting L only in r or in itself. If the lines
-- of x5 pass through a point P, let M be the lines through P missing x4 and take the points
-- on no line of M; a finite check over P and the subsets of its pencil gives the bound.

namespace PEqualNP.Outside.L_meta_6824

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem l1 : ∀ L : Fin 13, ∃ p : Fin 13, p - L ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by decide +kernel

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem l2 : ∀ L l0 : Fin 13, ∃ r : Fin 13, r - L ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧ r - l0 ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by decide +kernel

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem l3 : ∀ L r q : Fin 13, r - L ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → ∃ l : Fin 13, q - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧
    ∀ p : Fin 13, p - L ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) → p = r ∨ p = q := by decide +kernel

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem l4 : ∀ L : Fin 13, (Finset.univ.filter (fun p : Fin 13 => p - L ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card = 4 := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem l5 : ∀ P : Fin 13, ∀ b0 b1 b2 b3 : Bool,
    (Finset.univ.filter (fun q : Fin 13 => ∀ l ∈ Finset.univ.filter (fun l : Fin 13 =>
      (l = P - 0 ∧ b0 = true) ∨ (l = P - 1 ∧ b1 = true) ∨ (l = P - 3 ∧ b2 = true) ∨ (l = P - 9 ∧ b3 = true)),
        ¬ q - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2 ∨
    (Finset.univ.filter (fun x9 : Fin 13 => ∀ x5 ∈ Finset.univ.filter (fun q : Fin 13 => ∀ l ∈ Finset.univ.filter (fun l : Fin 13 =>
      (l = P - 0 ∧ b0 = true) ∨ (l = P - 1 ∧ b1 = true) ∨ (l = P - 3 ∧ b2 = true) ∨ (l = P - 9 ∧ b3 = true)),
        ¬ q - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))), ¬ x5 - x9 ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2 ∨
    ((Finset.univ.filter (fun q : Fin 13 => ∀ l ∈ Finset.univ.filter (fun l : Fin 13 =>
      (l = P - 0 ∧ b0 = true) ∨ (l = P - 1 ∧ b1 = true) ∨ (l = P - 3 ∧ b2 = true) ∨ (l = P - 9 ∧ b3 = true)),
        ¬ q - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card = 3 ∧
      ∃ x9 : Fin 13, ∀ x10 ∈ Finset.univ.filter (fun q : Fin 13 => ∀ l ∈ Finset.univ.filter (fun l : Fin 13 =>
      (l = P - 0 ∧ b0 = true) ∨ (l = P - 1 ∧ b1 = true) ∨ (l = P - 3 ∧ b2 = true) ∨ (l = P - 9 ∧ b3 = true)),
        ¬ q - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))), x10 - x9 ∈ ({0, 1, 3, 9} : Finset (Fin 13))) := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem l6 : ∀ P l : Fin 13, P - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ↔ (l = P - 0 ∨ l = P - 1 ∨ l = P - 3 ∨ l = P - 9) := by
  decide +kernel

theorem hnc (S : Finset (Fin 13)) : Nat.card {x9 : Fin 13 // ∀ x5 ∈ S, ¬ x5 - x9 ∈ ({0, 1, 3, 9} : Finset (Fin 13))} =
    (Finset.univ.filter (fun x9 : Fin 13 => ∀ x5 ∈ S, ¬ x5 - x9 ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

end PEqualNP.Outside.L_meta_6824

open PEqualNP.Outside.L_meta_6824 in
theorem PEqualNP.Outside.L_meta_6824 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => x2 - x3 ∈ x1; have x3 : Finset (Fin (13 : ℕ)) → Fin (13 : ℕ) → Prop := fun (x3 : Finset (Fin (13 : ℕ))) (x4 : Fin (13 : ℕ)) => ∀ x5 ∈ x3, ¬x2 x5 x4; ∀ (x4 x5 : Finset (Fin (13 : ℕ))), (∀ x6 ∈ x4, ∀ x8 ∈ x5, ¬x2 x6 x8) → ((∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x4, x2 x8 x7) ∨ ∃ (x7 : Fin (13 : ℕ)), ∀ x8 ∈ x5, x2 x7 x8) → ∃ (x8 : Finset (Fin (13 : ℕ))), (∀ x9 ∉ x8, ∃ (x11 : Fin (13 : ℕ)), x3 x8 x11 ∧ x2 x9 x11) ∧ (x8.card ≤ (2 : ℕ) ∨ Nat.card { x9 : Fin (13 : ℕ) // x3 x8 x9 } ≤ (2 : ℕ) ∨ x8.card = (3 : ℕ) ∧ ∃ (x9 : Fin (13 : ℕ)), ∀ x10 ∈ x8, x2 x10 x9) ∧ x4 ⊆ x8 ∧ ∀ x9 ∈ x5, x3 x8 x9 := by
  dsimp only
  intro x4 x5 hdis hcase
  rcases Finset.eq_empty_or_nonempty x5 with h5 | ⟨l0, hl0⟩
  · subst h5
    refine ⟨Finset.univ, ?_, ?_, Finset.subset_univ _, by simp⟩
    · intro x9 hx
      exact absurd (Finset.mem_univ x9) hx
    · right; left
      rw [hnc]
      have he : (Finset.univ.filter fun x9 : Fin 13 =>
          ∀ x5 ∈ (Finset.univ : Finset (Fin 13)), ¬ x5 - x9 ∈ ({0, 1, 3, 9} : Finset (Fin 13))) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x9 _ h
        obtain ⟨p, hp⟩ := l1 x9
        exact h p (Finset.mem_univ _) hp
      rw [he]
      simp
  rcases hcase with ⟨L, hL⟩ | ⟨P, hP⟩
  · obtain ⟨r, hrL, hrl0⟩ := l2 L l0
    refine ⟨Finset.univ.filter (fun p : Fin 13 => p - L ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧ ∀ l ∈ x5, ¬ p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))),
      ?_, ?_, ?_, ?_⟩
    · intro q hq
      obtain ⟨l, hql, hl⟩ := l3 L r q hrL
      refine ⟨l, ?_, hql⟩
      intro p hp hpl
      have hp' := (Finset.mem_filter.1 hp).2
      rcases hl p hp'.1 hpl with rfl | rfl
      · exact hp'.2 l0 hl0 hrl0
      · exact hq hp
    · have hsub : Finset.univ.filter (fun p : Fin 13 => p - L ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧ ∀ l ∈ x5, ¬ p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))) ⊆
          (Finset.univ.filter (fun p : Fin 13 => p - L ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).erase r := by
        intro p hp
        have hp' := (Finset.mem_filter.1 hp).2
        refine Finset.mem_erase.2 ⟨?_, Finset.mem_filter.2 ⟨Finset.mem_univ _, hp'.1⟩⟩
        rintro rfl
        exact hp'.2 l0 hl0 hrl0
      have hc := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ r, hrL⟩ :
        r ∈ Finset.univ.filter (fun p : Fin 13 => p - L ∈ ({0, 1, 3, 9} : Finset (Fin 13)))), l4 L] at hc
      by_cases h2 : (Finset.univ.filter (fun p : Fin 13 => p - L ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧ ∀ l ∈ x5, ¬ p - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).card ≤ 2
      · exact Or.inl h2
      · exact Or.inr (Or.inr ⟨by omega, L, fun p hp => (Finset.mem_filter.1 hp).2.1⟩)
    · intro p hp
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hL p hp, fun l hl => hdis p hp l hl⟩
    · intro l hl p hp
      exact (Finset.mem_filter.1 hp).2.2 l hl
  · have hM : Finset.univ.filter (fun l : Fin 13 => P - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧ ∀ q ∈ x4, ¬ q - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))) ∈
        (Finset.univ.filter (fun l : Fin 13 => P - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)))).powerset := by
      rw [Finset.mem_powerset]
      intro l hl
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hl).2.1⟩
    refine ⟨Finset.univ.filter (fun q : Fin 13 => ∀ l ∈ Finset.univ.filter
      (fun l : Fin 13 => P - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧ ∀ q ∈ x4, ¬ q - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))), ¬ q - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))), ?_, ?_, ?_, ?_⟩
    · intro q hq
      rw [Finset.mem_filter] at hq
      push_neg at hq
      obtain ⟨l, hlM, hql⟩ := hq (Finset.mem_univ _)
      exact ⟨l, fun p hp hpl => (Finset.mem_filter.1 hp).2 l hlM hpl, hql⟩
    · rw [hnc]
      have hMe : Finset.univ.filter (fun l : Fin 13 => P - l ∈ ({0, 1, 3, 9} : Finset (Fin 13)) ∧ ∀ q ∈ x4, ¬ q - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))) =
          Finset.univ.filter (fun l : Fin 13 =>
            (l = P - 0 ∧ decide (∀ q ∈ x4, ¬ q - (P - 0) ∈ ({0, 1, 3, 9} : Finset (Fin 13))) = true) ∨
            (l = P - 1 ∧ decide (∀ q ∈ x4, ¬ q - (P - 1) ∈ ({0, 1, 3, 9} : Finset (Fin 13))) = true) ∨
            (l = P - 3 ∧ decide (∀ q ∈ x4, ¬ q - (P - 3) ∈ ({0, 1, 3, 9} : Finset (Fin 13))) = true) ∨
            (l = P - 9 ∧ decide (∀ q ∈ x4, ¬ q - (P - 9) ∈ ({0, 1, 3, 9} : Finset (Fin 13))) = true)) := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, l6 P l]
        constructor
        · rintro ⟨h | h | h | h, h2⟩ <;> subst h <;> simp_all
        · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩) <;> simp_all
      rw [hMe]
      exact l5 P _ _ _ _
    · intro q hq
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      intro l hl hql
      exact (Finset.mem_filter.1 hl).2.2 q hq hql
    · intro l hl p hp
      exact (Finset.mem_filter.1 hp).2 l
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hP l hl, fun q hq => hdis q hq l hl⟩)
