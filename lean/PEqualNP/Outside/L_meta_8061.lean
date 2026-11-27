import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8061

theorem aux (x1 x2 x3 : ℕ) (x4 x5 : ℕ → ℕ) (x6 x7 x8 : ℕ → Bool) (h1 : x3 < x1)
    (h2 : ∀ x10 < x2, x4 x10 < x1 + x10 ∧ x5 x10 < x1 + x10)
    (h3 : ∀ x11 < x1, x8 x11 = decide (x11 = x3))
    (h4 : ∀ x12 < x2, x8 (x1 + x12) = (x8 (x4 x12) && x6 x12 || x8 (x5 x12) && x7 x12)) :
    ∀ x14 < x1 + x2, x8 x14 = true ↔ Relation.ReflTransGen
      (fun (x13 x14 : ℕ) => ∃ x15 < x2, x14 = x1 + x15 ∧
        (x13 = x4 x15 ∧ x6 x15 = true ∨ x13 = x5 x15 ∧ x7 x15 = true)) x3 x14 := by
  intro n hn
  constructor
  · revert hn
    refine Nat.strong_induction_on n ?_
    intro n ih hn hx
    by_cases hlt : n < x1
    · rw [h3 n hlt] at hx
      have hn3 : n = x3 := of_decide_eq_true hx
      subst hn3
      exact Relation.ReflTransGen.refl
    · obtain ⟨k, rfl⟩ : ∃ k, n = x1 + k := ⟨n - x1, by omega⟩
      have hk : k < x2 := by omega
      rw [h4 k hk] at hx
      obtain ⟨ha, hb⟩ := h2 k hk
      simp only [Bool.or_eq_true, Bool.and_eq_true] at hx
      rcases hx with ⟨hx, h6⟩ | ⟨hx, h7⟩
      · exact Relation.ReflTransGen.tail (ih _ ha (by omega) hx) ⟨k, hk, rfl, Or.inl ⟨rfl, h6⟩⟩
      · exact Relation.ReflTransGen.tail (ih _ hb (by omega) hx) ⟨k, hk, rfl, Or.inr ⟨rfl, h7⟩⟩
  · intro h
    clear hn
    induction h with
    | refl => rw [h3 x3 h1]; simp
    | tail _ hbc ih =>
      obtain ⟨k, hk, rfl, hc⟩ := hbc
      rw [h4 k hk]
      rcases hc with ⟨rfl, h6⟩ | ⟨rfl, h7⟩
      · simp [ih, h6]
      · simp [ih, h7]

end PEqualNP.Outside.L_meta_8061

theorem PEqualNP.Outside.L_meta_8061 : ∀ (x1 x2 x3 : ℕ) (x4 x5 : ℕ → ℕ) (x6 x7 x8 : ℕ → Bool),   x3 < x1 →     (∀ x10 < x2, x4 x10 < x1 + x10 ∧ x5 x10 < x1 + x10) →       (∀ x11 < x1, x8 x11 = Decidable.decide (x11 = x3)) →         (∀ x12 < x2, x8 (x1 + x12) = (x8 (x4 x12) && x6 x12 || x8 (x5 x12) && x7 x12)) →           have x13 : ℕ → ℕ → Prop := fun (x13 x14 : ℕ) => ∃ x15 < x2, x14 = x1 + x15 ∧ (x13 = x4 x15 ∧ x6 x15 = Bool.true ∨ x13 = x5 x15 ∧ x7 x15 = Bool.true);           ∀ x14 < x1 + x2, x8 x14 = Bool.true ↔ Relation.ReflTransGen x13 x3 x14 := by
  intro x1 x2 x3 x4 x5 x6 x7 x8 h1 h2 h3 h4
  exact PEqualNP.Outside.L_meta_8061.aux x1 x2 x3 x4 x5 x6 x7 x8 h1 h2 h3 h4
