import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_7608 : ∀ (x1 : Type) (x2 x3 : List (Set x1)) (x4 : Set x1),   have x5 : ℕ → List (Set x1) := fun (x5 : ℕ) => x2 ++ List.take x5 x3;   x4 ∈ x2 ++ x3 → (∀ x7 ∈ x2, ¬x7 ⊆ x4) → (∀ (x8 : Fin x3.length), ∃ x9 ∈ x5 ↑x8, ∃ x10 ∈ x5 ↑x8, x3.get x8 = x9 ∪ x10 ∨ x3.get x8 = x9 ∩ x10) → ∀ x9 ∈ x4, ∃ (x11 : Fin x3.length), x3.get x11 ⊆ x4 ∧ x9 ∈ x3.get x11 ∧ ∃ x12 ∈ x5 ↑x11, ∃ x13 ∈ x5 ↑x11, ¬x12 ⊆ x4 ∧ ¬x13 ⊆ x4 ∧ x3.get x11 = x12 ∩ x13 := by
  intro x1 x2 x3 x4
  dsimp only
  intro h4 hgen hw p hp
  have key : ∀ n : ℕ, ∀ (h : n < x3.length), x3.get ⟨n, h⟩ ⊆ x4 → p ∈ x3.get ⟨n, h⟩ →
      ∃ (x11 : Fin x3.length), x3.get x11 ⊆ x4 ∧ p ∈ x3.get x11 ∧ ∃ x12 ∈ x2 ++ List.take (↑x11) x3, ∃ x13 ∈ x2 ++ List.take (↑x11) x3, ¬x12 ⊆ x4 ∧ ¬x13 ⊆ x4 ∧ x3.get x11 = x12 ∩ x13 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro h hsub hpm
      have down : ∀ a ∈ x2 ++ List.take n x3, a ⊆ x4 → p ∈ a →
          ∃ (x11 : Fin x3.length), x3.get x11 ⊆ x4 ∧ p ∈ x3.get x11 ∧ ∃ x12 ∈ x2 ++ List.take (↑x11) x3, ∃ x13 ∈ x2 ++ List.take (↑x11) x3, ¬x12 ⊆ x4 ∧ ¬x13 ⊆ x4 ∧ x3.get x11 = x12 ∩ x13 := by
        intro a ha has hpa
        rcases List.mem_append.1 ha with h2 | h3
        · exact absurd has (hgen a h2)
        · obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.1 h3
          have hj' : j < n ∧ j < x3.length := by simpa [List.length_take] using hj
          rw [List.getElem_take] at hje
          subst hje
          exact ih j hj'.1 hj'.2 has hpa
      obtain ⟨a, ha, b, hb, hab | hab⟩ := hw ⟨n, h⟩
      · rw [hab] at hpm hsub
        rcases hpm with hpa | hpb
        · exact down a ha (fun y hy => hsub (Or.inl hy)) hpa
        · exact down b hb (fun y hy => hsub (Or.inr hy)) hpb
      · by_cases h1 : a ⊆ x4
        · exact down a ha h1 (by rw [hab] at hpm; exact hpm.1)
        · by_cases h2 : b ⊆ x4
          · exact down b hb h2 (by rw [hab] at hpm; exact hpm.2)
          · exact ⟨⟨n, h⟩, hsub, hpm, a, ha, b, hb, h1, h2, hab⟩
  rcases List.mem_append.1 h4 with h | h
  · exact absurd (subset_refl x4) (hgen x4 h)
  · obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.1 h
    subst hje
    exact key j hj (subset_refl _) hp
