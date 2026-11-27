import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_6599 : ∀ (x1 x2 : Type) (x3 : Set x1) (x4 : x2) (x5 : x1 → x2) (x6 x7 : Set x1) (x8 x9 : Set x2), (∀ x10 ∈ x3, (x10 ∈ x6 ∧ x4 ∈ x8 ∨ x10 ∈ x7 ∧ x4 ∈ x9) ∧ (x10 ∈ x6 ∧ x5 x10 ∈ x8 ∨ x10 ∈ x7 ∧ x5 x10 ∈ x9)) → (∀ x11 ∈ x3, ¬(x11 ∈ x6 ∧ x4 ∈ x8 ∧ x5 x11 ∈ x8) ∧ ¬(x11 ∈ x7 ∧ x4 ∈ x9 ∧ x5 x11 ∈ x9)) → (∀ x12 ∈ x3, x12 ∈ x6 ∧ x12 ∈ x7 ∧ x4 ∈ x8 ∧ x4 ∉ x9 ∧ x5 x12 ∉ x8 ∧ x5 x12 ∈ x9) ∨ ∀ x12 ∈ x3, x12 ∈ x6 ∧ x12 ∈ x7 ∧ x4 ∈ x9 ∧ x4 ∉ x8 ∧ x5 x12 ∉ x9 ∧ x5 x12 ∈ x8 := by
  intro α β X c f A B P Q h1 h2
  by_cases hc : c ∈ P
  · left
    intro x hx
    have a := h1 x hx
    have b := h2 x hx
    tauto
  · right
    intro x hx
    have a := h1 x hx
    have b := h2 x hx
    tauto
