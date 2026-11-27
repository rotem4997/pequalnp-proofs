import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_6418 : ∀ (x1 x2 x3 : ℕ) (x4 : ℕ → Finset (Finset (Fin x1))) (x5 x6 : Type) (x7 : x5 → Fin x1 → Prop) (x8 : x6 → Fin x1 → Prop), (∀ (x9 : Fin x1), x4 ↑x9 = {{x9}}) → (∀ x10 < x2, ∃ (x12 : ℕ) (x13 : ℕ), x12 < x13 ∧ x13 < x1 + x10 ∧ (x4 (x1 + x10) = x4 x12 ∪ x4 x13 ∨ x4 (x1 + x10) = (x4 x12).biUnion fun (x14 : Finset (Fin x1)) => Finset.image (fun (x15 : Finset (Fin x1)) => x14 ∪ x15) (x4 x13))) → (∀ (x11 : x5), ∀ x12 ∈ x4 x3, ∃ x14 ∈ x12, x7 x11 x14) → (∀ (x12 : x6), ∃ x13 ∈ x4 x3, ∀ x14 ∈ x13, x8 x12 x14) → ∃ (x13 : ℕ → Set x5) (x14 : ℕ → Set x6), (∀ (x15 : Fin x1), x13 ↑x15 = {x16 : x5 | x7 x16 x15} ∧ x14 ↑x15 = {x16 : x6 | x8 x16 x15}) ∧ (∀ x15 < x2, ∃ (x17 : ℕ) (x18 : ℕ), x17 < x18 ∧ x18 < x1 + x15 ∧ x13 (x1 + x15) ×ˢ x14 (x1 + x15) ⊆ x13 x17 ×ˢ x14 x17 ∪ x13 x18 ×ˢ x14 x18) ∧ x13 x3 = Set.univ ∧ x14 x3 = Set.univ := by
  intro n m w0 F A B P Q hin hg hA hB
  classical
  refine ⟨fun w => {a : A | ∀ S ∈ F w, ∃ i ∈ S, P a i},
    fun w => {b : B | ∃ S ∈ F w, ∀ i ∈ S, Q b i}, ?_, ?_, ?_, ?_⟩
  · intro i
    constructor
    · ext a
      simp [hin i]
    · ext b
      simp [hin i]
  · intro j hj
    obtain ⟨p, q, hpq, hq, h⟩ := hg j hj
    refine ⟨p, q, hpq, hq, ?_⟩
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    simp only [Set.mem_setOf_eq] at ha hb
    rcases h with h | h
    · rw [h] at ha hb
      obtain ⟨S, hS, hSb⟩ := hb
      rcases Finset.mem_union.1 hS with hS | hS
      · left
        exact ⟨fun T hT => ha T (Finset.mem_union_left _ hT), S, hS, hSb⟩
      · right
        exact ⟨fun T hT => ha T (Finset.mem_union_right _ hT), S, hS, hSb⟩
    · rw [h] at ha hb
      obtain ⟨S, hS, hSb⟩ := hb
      obtain ⟨S1, hS1, hS'⟩ := Finset.mem_biUnion.1 hS
      obtain ⟨S2, hS2, rfl⟩ := Finset.mem_image.1 hS'
      by_cases hc : ∀ T ∈ F p, ∃ i ∈ T, P a i
      · left
        exact ⟨hc, S1, hS1, fun i hi => hSb i (Finset.mem_union_left _ hi)⟩
      · right
        push_neg at hc
        obtain ⟨T1, hT1, hno⟩ := hc
        refine ⟨fun T2 hT2 => ?_, S2, hS2, fun i hi => hSb i (Finset.mem_union_right _ hi)⟩
        obtain ⟨i, hi, hPi⟩ := ha (T1 ∪ T2)
          (Finset.mem_biUnion.2 ⟨T1, hT1, Finset.mem_image.2 ⟨T2, hT2, rfl⟩⟩)
        rcases Finset.mem_union.1 hi with h1 | h1
        · exact absurd hPi (hno i h1)
        · exact ⟨i, h1, hPi⟩
  · ext a
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact hA a
  · ext b
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact hB b
