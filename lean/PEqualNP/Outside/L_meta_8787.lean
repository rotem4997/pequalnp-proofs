import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8787

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8787

theorem PEqualNP.Outside.L_meta_8787 : ∀ (x1 : List ℕ) (x2 : ℕ),   have x3 : (ℕ → Prop) → (ℕ → Prop) → ℕ → Prop := fun (x3 x4 : ℕ → Prop) (x5 : ℕ) => ∃ (x6 : ℕ), x3 x6 ∧ ∃ (x7 : ℕ), x4 x7 ∧ (x5 = x6 &&& x7 ∨ x5 = x6 ||| x7);   have x4 : List ℕ → ℕ → Prop := fun (x4 : List ℕ) => x3 (fun (x5 : ℕ) => x5 ∈ x4) fun (x5 : ℕ) => x5 ∈ x4;   (have x5 : ℕ → Prop := fun (x5 : ℕ) => x5 ∈ x1;     have x6 : ℕ → Prop := x3 x5 x5;     x3 x6 x6 x2 ∨ x3 x5 (x3 x5 x6) x2) →     ∃ (x6 : List ℕ), x6.length ≤ (2 : ℕ) ∧ (∀ (x7 : Fin x6.length), x4 (x1 ++ List.take (↑x7) x6) (x6.get x7)) ∧ x4 (x1 ++ x6) x2 := by
  intro A z
  intro op cl h
  have key : ∀ p q : ℕ, cl A p → cl (A ++ [p]) q → cl (A ++ [p, q]) z → ∃ (x6 : List ℕ), x6.length ≤ (2 : ℕ) ∧ (∀ (x7 : Fin x6.length), cl (A ++ List.take (↑x7) x6) (x6.get x7)) ∧ cl (A ++ x6) z := by
    intro p q h1 h2 h3
    refine ⟨[p, q], by simp, ?_, h3⟩
    rintro ⟨i, hi⟩
    have hi' : i < 2 := by simpa using hi
    interval_cases i
    · simpa using h1
    · simpa using h2
  have up : ∀ (P Q : ℕ → Prop) (P' Q' : ℕ → Prop) (n : ℕ), (∀ a, P a → P' a) → (∀ a, Q a → Q' a) → op P Q n → op P' Q' n := by
    rintro P Q P' Q' n hP hQ ⟨a, ha, b, hb, e⟩
    exact ⟨a, hP a ha, b, hQ b hb, e⟩
  rcases h with ⟨p, hp, q, hq, e⟩ | ⟨a, ha, r, ⟨b, hb, d, hd, e'⟩, e⟩
  · refine key p q hp (up _ _ _ _ _ ?_ ?_ hq) ⟨p, ?_, q, ?_, e⟩
    · intro a ha; exact List.mem_append_left _ ha
    · intro a ha; exact List.mem_append_left _ ha
    · simp
    · simp
  · refine key d r hd ⟨b, List.mem_append_left _ hb, d, by simp, e'⟩ ⟨a, List.mem_append_left _ ha, r, by simp, e⟩
