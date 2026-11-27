import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_6122 : ∀ (x1 x2 : ℕ) (x3 : ℕ → Set (Finset ℕ)), (∀ x4 < x1, x3 x4 = {{x4}}) → (∀ x5 < x2, ∃ x7 < x1 + x5, ∃ x8 < x1 + x5, x3 (x1 + x5) = Set.image2 (fun (x9 x10 : Finset ℕ) => x9 ∪ x10) (x3 x7) (x3 x8) ∨ x3 (x1 + x5) = x3 x7 ∨ x3 (x1 + x5) = {∅} ∨ x3 (x1 + x5) = x3 x7 ∪ x3 x8) → ∃ (x6 : ℕ → Set (Finset ℕ)), (∀ (x7 : ℕ) (x8 : Finset ℕ), x8 ∈ x6 x7 ↔ ∀ x9 ∈ x3 x7, ¬Disjoint x9 x8) ∧ (∀ x7 < x1, x6 x7 = {x9 : Finset ℕ | x7 ∈ x9}) ∧ ∀ x7 < x2, ∃ x9 < x1 + x7, ∃ x10 < x1 + x7, x6 (x1 + x7) ∈ [x6 x9 ∪ x6 x10, x6 x9 ∩ x6 x10, x6 x9, ∅] := by
  intro n m F hin hg
  refine ⟨fun w => {S : Finset ℕ | ∀ T ∈ F w, ¬ Disjoint T S}, fun w S => Iff.rfl, ?_, ?_⟩
  · intro w hw
    ext S
    simp only [Set.mem_setOf_eq, hin w hw, Set.mem_singleton_iff, forall_eq,
      Finset.disjoint_singleton_left, not_not]
  · intro j hj
    obtain ⟨a, ha, b, hb, h⟩ := hg j hj
    refine ⟨a, ha, b, hb, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases h with h | h | h | h
    · left
      ext S
      simp only [Set.mem_setOf_eq, Set.mem_union, h, Set.mem_image2]
      constructor
      · intro hS
        by_contra hc
        push_neg at hc
        obtain ⟨⟨A, hA, hAd⟩, ⟨B, hB, hBd⟩⟩ := hc
        exact hS (A ∪ B) ⟨A, hA, B, hB, rfl⟩ (Finset.disjoint_union_left.2 ⟨hAd, hBd⟩)
      · rintro (hS | hS) T ⟨A, hA, B, hB, rfl⟩ hd
        · exact hS A hA (Finset.disjoint_union_left.1 hd).1
        · exact hS B hB (Finset.disjoint_union_left.1 hd).2
    · right; right; left
      ext S
      simp only [Set.mem_setOf_eq, h]
    · right; right; right
      ext S
      simp only [Set.mem_setOf_eq, h, Set.mem_singleton_iff, forall_eq, Set.mem_empty_iff_false,
        iff_false, not_not]
      exact Finset.disjoint_empty_left S
    · right; left
      ext S
      simp only [Set.mem_setOf_eq, h, Set.mem_union, Set.mem_inter_iff]
      constructor
      · intro hS
        exact ⟨fun T hT => hS T (Or.inl hT), fun T hT => hS T (Or.inr hT)⟩
      · rintro ⟨h1, h2⟩ T (hT | hT)
        · exact h1 T hT
        · exact h2 T hT
