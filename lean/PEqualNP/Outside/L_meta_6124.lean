import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_6124 : ∀ (x1 : Type) (x2 x3 x4 : ℕ) (x5 : ℕ → Set x1) (x6 : Set x1), x4 < x2 + x3 → (∀ x8 < x2, ¬Disjoint (x5 x8) x6) → (∀ x9 < x3, ∃ x11 < x2 + x9, ∃ x12 < x2 + x9, x5 (x2 + x9) ∈ [x5 x11 ∪ x5 x12, x5 x11 ∩ x5 x12, x5 x11, ∅]) → Disjoint (x5 x4) x6 → ∀ x11 ∈ x5 x4, ∃ x13 < x3, ∃ x14 < x2 + x13, ∃ x15 < x2 + x13, x5 (x2 + x13) = x5 x14 ∩ x5 x15 ∧ ¬Disjoint (x5 x14) x6 ∧ ¬Disjoint (x5 x15) x6 ∧ Disjoint (x5 (x2 + x13)) x6 ∧ x11 ∈ x5 (x2 + x13) ∧ ∀ x16 < x2 + x13, x11 ∈ x5 x16 → ¬Disjoint (x5 x16) x6 := by
  intro α n s w A T hw hin hg hd e he
  classical
  have hex : ∃ k, e ∈ A k ∧ Disjoint (A k) T := ⟨w, he, hd⟩
  obtain ⟨k, hk, hmin, hkw⟩ : ∃ k, (e ∈ A k ∧ Disjoint (A k) T) ∧
      (∀ i < k, e ∈ A i → ¬ Disjoint (A i) T) ∧ k ≤ w :=
    ⟨Nat.find hex, Nat.find_spec hex,
      fun i hi hei hdi => Nat.find_min hex hi ⟨hei, hdi⟩, Nat.find_min' hex ⟨he, hd⟩⟩
  have hkn : n ≤ k := by
    by_contra h
    exact hin k (by omega) hk.2
  obtain ⟨j, rfl⟩ : ∃ j, k = n + j := ⟨k - n, by omega⟩
  have hj : j < s := by omega
  obtain ⟨a, ha, b, hb, hmem⟩ := hg j hj
  refine ⟨j, hj, a, ha, b, hb, ?_⟩
  have hk0 := hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h
  · exfalso
    rw [h] at hk
    rcases hk.1 with h1 | h1
    · exact hmin a ha h1 (hk.2.mono_left Set.subset_union_left)
    · exact hmin b hb h1 (hk.2.mono_left Set.subset_union_right)
  · rw [h] at hk
    exact ⟨h, hmin a ha hk.1.1, hmin b hb hk.1.2, hk0.2, hk0.1, hmin⟩
  · exfalso
    rw [h] at hk
    exact hmin a ha hk.1 hk.2
  · exfalso
    rw [h] at hk
    exact hk.1
