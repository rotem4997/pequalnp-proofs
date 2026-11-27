import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_4326 : have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : (Fin (42 : ℕ) → Bool) → Prop := fun (x2 : Fin (42 : ℕ) → Bool) => ∀ (x3 : Fin (42 : ℕ)), x2 x3 = Bool.true ↔ ∀ (x4 : Fin (42 : ℕ)), x2 x4 = Bool.true → ¬(x1 x3 x4 ∨ x1 x4 x3); ∀ (x3 : Fin (42 : ℕ) → Bool), x2 x3 ↔ (∀ (x4 x5 : Fin (42 : ℕ)), x3 x4 = Bool.true → x3 x5 = Bool.true → ¬x1 x4 x5) ∧ ∀ (x4 : Fin (42 : ℕ)), x3 x4 = Bool.false → ∃ (x6 : Fin (42 : ℕ)), x3 x6 = Bool.true ∧ (x1 x4 x6 ∨ x1 x6 x4) := by
  intro A M x
  constructor
  · intro h
    refine ⟨fun i j hi hj hij => ?_, fun i hi => ?_⟩
    · exact (h i).1 hi j hj (Or.inl hij)
    · by_contra hc
      push Not at hc
      have : x i = true := (h i).2 fun j hj hor => by
        rcases hor with hor | hor
        · exact (hc j hj).1 hor
        · exact (hc j hj).2 hor
      rw [hi] at this
      exact Bool.false_ne_true this
  · rintro ⟨h1, h2⟩ i
    constructor
    · intro hi j hj hor
      rcases hor with hor | hor
      · exact h1 i j hi hj hor
      · exact h1 j i hj hi hor
    · intro h
      by_contra hc
      obtain ⟨j, hj, hor⟩ := h2 i (by simpa using hc)
      exact h j hj hor
