import Mathlib
import PEqualNP.Defs

-- Every empty wire is replaced by the value of input 0. A nonempty wire keeps its value, so
-- each gate is still a union or an intersection of earlier wires. A rectangle gate of the new
-- list below the output cannot come from an empty wire, since input 0 is not below the output.
theorem PEqualNP.Outside.L_meta_4303 : ∀ (x1 x2 : Type) (x3 x4 x5 : ℕ) (x6 : ℕ → Set (x1 × x2)),   have x7 : (ℕ → Set (x1 × x2)) → x1 × x2 → Prop := fun (x7 : ℕ → Set (x1 × x2)) (x8 : x1 × x2) => ∃ x9 < x4, x7 (x3 + x9) ⊆ x7 x5 ∧ x8 ∈ x7 (x3 + x9) ∧ ∃ (x10 : ℕ) (x11 : ℕ), Max.max x10 x11 < x3 + x9 ∧ x7 (x3 + x9) = x7 x10 ∩ x7 x11 ∧ ∃ (x12 : Set x1) (x13 : Set x2), x7 x10 = x12 ×ˢ Set.univ ∧ x7 x11 = Set.univ ×ˢ x13;   (0 : ℕ) < x3 → (∀ x9 < x3, x6 x9 ≠ ∅) → x6 x5 ≠ ∅ → ¬x6 (0 : ℕ) ⊆ x6 x5 → (∀ x12 < x4, ∃ (x14 : ℕ) (x15 : ℕ), Max.max x14 x15 < x3 + x12 ∧ x6 (x3 + x12) ∈ [x6 x14 ∪ x6 x15, x6 x14, ∅, x6 x14 ∩ x6 x15]) → ∃ (x13 : ℕ → Set (x1 × x2)), (∀ x14 < x3, x13 x14 = x6 x14) ∧ x13 x5 = x6 x5 ∧ (∀ (x14 : ℕ), x13 x14 ≠ ∅) ∧ (∀ x14 < x4, ∃ (x16 : ℕ) (x17 : ℕ), Max.max x16 x17 < x3 + x14 ∧ (x13 (x3 + x14) = x13 x16 ∪ x13 x17 ∨ x13 (x3 + x14) = x13 x16 ∩ x13 x17)) ∧ ∀ (x14 : x1 × x2), x7 x13 x14 → x7 x6 x14 := by
  intro α β m k o s
  dsimp only
  intro hm hin ho hno hg
  classical
  have key : ∀ c : ℕ, ∃ c' : ℕ, c' ≤ c ∧ s c' = (if s c = ∅ then s 0 else s c) := by
    intro c
    by_cases hc : s c = ∅
    · exact ⟨0, Nat.zero_le _, by rw [if_pos hc]⟩
    · exact ⟨c, le_refl _, by rw [if_neg hc]⟩
  refine ⟨fun n => if s n = ∅ then s 0 else s n, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    dsimp only
    rw [if_neg (hin n hn)]
  · dsimp only
    rw [if_neg ho]
  · intro n
    dsimp only
    by_cases h : s n = ∅
    · rw [if_pos h]
      exact hin 0 hm
    · rw [if_neg h]
      exact h
  · intro i hi
    dsimp only
    obtain ⟨a, b, hab, hmem⟩ := hg i hi
    have hlt := max_lt_iff.mp hab
    have h0 : (if s 0 = ∅ then s 0 else s 0) = s 0 := by
      by_cases h : s 0 = ∅
      · rw [if_pos h]
      · rw [if_neg h]
    by_cases he : s (m + i) = ∅
    · refine ⟨0, 0, max_lt (by omega) (by omega), Or.inl ?_⟩
      rw [if_pos he, h0, Set.union_self]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h | h | h
      · by_cases ha : s a = ∅
        · have hb : s b ≠ ∅ := by
            intro hb
            apply he
            rw [h, ha, hb, Set.union_self]
          refine ⟨b, b, max_lt hlt.2 hlt.2, Or.inl ?_⟩
          rw [if_neg he, if_neg hb, Set.union_self, h, ha, Set.empty_union]
        · by_cases hb : s b = ∅
          · refine ⟨a, a, max_lt hlt.1 hlt.1, Or.inl ?_⟩
            rw [if_neg he, if_neg ha, Set.union_self, h, hb, Set.union_empty]
          · refine ⟨a, b, hab, Or.inl ?_⟩
            rw [if_neg he, if_neg ha, if_neg hb, h]
      · have ha : s a ≠ ∅ := by
          intro ha
          apply he
          rw [h, ha]
        refine ⟨a, a, max_lt hlt.1 hlt.1, Or.inl ?_⟩
        rw [if_neg he, if_neg ha, Set.union_self, h]
      · exact absurd h he
      · have ha : s a ≠ ∅ := by
          intro ha
          apply he
          rw [h, ha, Set.empty_inter]
        have hb : s b ≠ ∅ := by
          intro hb
          apply he
          rw [h, hb, Set.inter_empty]
        refine ⟨a, b, hab, Or.inr ?_⟩
        rw [if_neg he, if_neg ha, if_neg hb, h]
  · rintro p ⟨i, hi, hsub, hp, a, b, hab, hint, X, Y, hX, hY⟩
    dsimp only at hsub hp hint hX hY
    have hlt := max_lt_iff.mp hab
    by_cases he : s (m + i) = ∅
    · exfalso
      rw [if_pos he, if_neg ho] at hsub
      exact hno hsub
    · rw [if_neg he] at hsub hp hint
      rw [if_neg ho] at hsub
      obtain ⟨a', ha', ea⟩ := key a
      obtain ⟨b', hb', eb⟩ := key b
      refine ⟨i, hi, hsub, hp, a', b', max_lt (by omega) (by omega), ?_, X, Y, ?_, ?_⟩
      · rw [ea, eb]
        exact hint
      · rw [ea]
        exact hX
      · rw [eb]
        exact hY
