import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_7509 : ∀ (x1 x2 x3 : ℕ) (x4 : ℕ → Set ((Fin x1 → Bool) × (Fin x1 → Bool))),   let x5 : Type := (Fin x1 → Bool) × (Fin x1 → Bool);   x3 < x1 + x1 + x2 → (∀ (x7 : Fin x1), x4 ↑x7 = {x8 : x5 | x8.1 x7 = Bool.true} ∧ x4 (x1 + ↑x7) = {x8 : x5 | x8.2 x7 = Bool.true}) → (∀ x8 < x2, ∃ (x10 : ℕ) (x11 : ℕ), Max.max x10 x11 < x1 + x1 + x8 ∧ x4 (x1 + x1 + x8) ∈ [x4 x10 ∪ x4 x11, x4 x10, ∅, x4 x10 ∩ x4 x11]) → (∃ (x9 : x5), x9 ∈ x4 x3) → ∃ x10 ≤ x2, ∃ x11 < x1 + x1 + x10, ∃ (x12 : ℕ → Set x5), (∀ (x13 : Fin x1), x12 ↑x13 = {x14 : x5 | x14.1 x13 = Bool.true} ∧ x12 (x1 + ↑x13) = {x14 : x5 | x14.2 x13 = Bool.true}) ∧ (∀ x13 < x10, ∃ x15 < x1 + x1 + x13, ∃ x16 < x1 + x1 + x13, x12 (x1 + x1 + x13) = x12 x15 ∪ x12 x16 ∨ x12 (x1 + x1 + x13) = x12 x15 ∩ x12 x16) ∧ ∀ (x13 : x5), x13 ∈ x12 x11 ↔ x13 ∈ x4 x3 := by
  intro n m w0 W X hw0 hin hg hne
  classical
  have hn : 0 < n := by
    by_contra h0
    have hm : 0 < m := by omega
    obtain ⟨a, b, hab, _⟩ := hg 0 hm
    have := Nat.le_max_left a b
    omega
  obtain ⟨W', hW'⟩ : ∃ W' : ℕ → Set X, ∀ w, W' w = if n + n ≤ w ∧ W w = ∅ then W 0 else W w :=
    ⟨_, fun _ => rfl⟩
  have hlow : ∀ w, w < n + n → W' w = W w := fun w hw => by
    rw [hW', if_neg (by intro h; omega)]
  have hnz : ∀ w, W w ≠ ∅ → W' w = W w := fun w h => by
    rw [hW', if_neg (fun hh => h hh.2)]
  refine ⟨m, le_rfl, w0, hw0, W', ?_, ?_, ?_⟩
  · intro i
    rw [hlow _ (by omega), hlow _ (by omega)]
    exact hin i
  · intro j hj
    obtain ⟨a, b, hab, hk⟩ := hg j hj
    have ha : a < n + n + j := by have := Nat.le_max_left a b; omega
    have hb : b < n + n + j := by have := Nat.le_max_right a b; omega
    by_cases he : W (n + n + j) = ∅
    · refine ⟨0, by omega, 0, by omega, Or.inl ?_⟩
      rw [hW' (n + n + j), if_pos ⟨by omega, he⟩, hlow 0 (by omega), Set.union_self]
    · rw [hnz _ he]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with h | h | h | h
      · by_cases hae : W a = ∅
        · have hbe : W b ≠ ∅ := by
            intro hbe
            apply he
            rw [h, hae, hbe, Set.union_empty]
          refine ⟨b, hb, b, hb, Or.inl ?_⟩
          rw [hnz b hbe, h, hae, Set.empty_union, Set.union_self]
        · by_cases hbe : W b = ∅
          · refine ⟨a, ha, a, ha, Or.inl ?_⟩
            rw [hnz a hae, h, hbe, Set.union_empty, Set.union_self]
          · exact ⟨a, ha, b, hb, Or.inl (by rw [hnz a hae, hnz b hbe, h])⟩
      · have hae : W a ≠ ∅ := by rw [← h]; exact he
        exact ⟨a, ha, a, ha, Or.inl (by rw [hnz a hae, h, Set.union_self])⟩
      · exact absurd h he
      · have hae : W a ≠ ∅ := by
          intro hh
          apply he
          rw [h, hh, Set.empty_inter]
        have hbe : W b ≠ ∅ := by
          intro hh
          apply he
          rw [h, hh, Set.inter_empty]
        exact ⟨a, ha, b, hb, Or.inr (by rw [hnz a hae, hnz b hbe, h])⟩
  · intro p
    obtain ⟨q, hq⟩ := hne
    rw [hnz w0 (fun h => by rw [h] at hq; exact hq)]
