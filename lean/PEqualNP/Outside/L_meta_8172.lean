import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_8172 : ∀ (x1 x2 : List ℕ) (x3 : ℕ → ℕ → Bool) (x4 : ℕ) (x5 : List (ℕ × ℕ)),   have x6 : ℕ → Bool := fun (x6 : ℕ) => x5.any fun (x7 : ℕ × ℕ) => x3 x6 x7.1 && x3 x6 x7.2;   (∀ x7 ∈ x1, ∃ (x9 : Fin x4) (x10 : Fin x4), ∀ x11 ∈ x1 ++ x2, (x3 x11 ↑x9 && x3 x11 ↑x10) = Decidable.decide (x11 = x7)) → (∀ x8 ∈ x2, x6 x8 = Bool.false) → ∃ (x9 : List (ℕ × ℕ)), x9.length ≤ (List.filter (fun (x10 : ℕ) => !x6 x10) x1).length ∧ (∀ x10 ∈ x9, x10.1 < x4 ∧ x10.2 < x4) ∧ ∀ x10 ∈ x1 ++ x2, ((x5 ++ x9).any fun (x12 : ℕ × ℕ) => x3 x10 x12.1 && x3 x10 x12.2) = Decidable.decide (x10 ∈ x1) := by
  intro x1 x2 x3 x4 x5 x6 h1 h2
  have key : ∀ x7, ∃ p : ℕ × ℕ, x7 ∈ x1 → (p.1 < x4 ∧ p.2 < x4 ∧ ∀ x11 ∈ x1 ++ x2, (x3 x11 p.1 && x3 x11 p.2) = decide (x11 = x7)) := by
    intro x7
    by_cases hx : x7 ∈ x1
    · obtain ⟨a, b, hab⟩ := h1 x7 hx
      exact ⟨(a.val, b.val), fun _ => ⟨a.isLt, b.isLt, hab⟩⟩
    · exact ⟨(0, 0), fun h => absurd h hx⟩
  choose g hg using key
  refine ⟨(x1.filter (fun x10 => !x6 x10)).map g, by simp, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_map, List.mem_filter] at hp
    obtain ⟨a, ⟨ha, _⟩, rfl⟩ := hp
    exact ⟨(hg a ha).1, (hg a ha).2.1⟩
  · intro x10 hx10
    rw [List.any_append]
    by_cases hm : x10 ∈ x1
    · simp only [hm, decide_true]
      by_cases h6 : x6 x10 = true
      · have : (x5.any fun x12 => x3 x10 x12.1 && x3 x10 x12.2) = true := h6
        rw [this]; rfl
      · rw [Bool.or_eq_true]
        right
        rw [List.any_eq_true]
        refine ⟨g x10, ?_, ?_⟩
        · exact List.mem_map.mpr ⟨x10, List.mem_filter.mpr ⟨hm, by simpa using h6⟩, rfl⟩
        · rw [(hg x10 hm).2.2 x10 hx10]; simp
    · have hx2 : x10 ∈ x2 := by
        rcases List.mem_append.mp hx10 with h | h
        · exact absurd h hm
        · exact h
      have h6 : (x5.any fun x12 => x3 x10 x12.1 && x3 x10 x12.2) = false := h2 x10 hx2
      rw [h6, decide_eq_false hm, Bool.false_or, Bool.eq_false_iff]
      intro hc
      rw [List.any_eq_true] at hc
      obtain ⟨p, hp, hpv⟩ := hc
      simp only [List.mem_map, List.mem_filter] at hp
      obtain ⟨a, ⟨ha, _⟩, rfl⟩ := hp
      rw [(hg a ha).2.2 x10 hx10] at hpv
      simp at hpv
      exact hm (hpv ▸ ha)
