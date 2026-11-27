import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8419

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_8419

theorem PEqualNP.Outside.L_meta_8419 : let x1 : Type := Fin (21 : ℕ); have x2 : x1 → Finset x1 := fun (x2 : x1) => {x3 : x1 | (↑x2 + (21 : ℕ) - ↑x3) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]}; have x3 : (Fin (42 : ℕ) → Bool) → Prop := fun (x3 : Fin (42 : ℕ) → Bool) => ∃ (x4 : Fin (42 : ℕ)) (x5 : Fin (42 : ℕ)), (↑x4 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x5 ∧ (↑x5 + (21 : ℕ) - ↑x4) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true; ∀ (x4 : Fin (42 : ℕ) → Bool), x3 x4 → (∀ (x6 : Fin (42 : ℕ) → Bool), (∀ (x7 : Fin (42 : ℕ)), x6 x7 = Bool.true → x4 x7 = Bool.true) → x3 x6 → x6 = x4) → ∃ (x7 : x1) (x8 : x1), x7 ∈ x2 x8 ∧ List.ofFn x4 = PEqualNP.GenericRejection.incidenceInput {x7} {x8} := by
  intro X S F x hx hmin
  obtain ⟨a, b, ⟨ha, hb, hab⟩, hxa, hxb⟩ := hx
  have hxe : (fun i => decide (i = a ∨ i = b)) = x := hmin _ (by
    intro i hi
    simp only [decide_eq_true_eq] at hi
    rcases hi with rfl | rfl
    · exact hxa
    · exact hxb) ⟨a, b, ⟨ha, hb, hab⟩, by simp, by simp⟩
  refine ⟨⟨a, ha⟩, ⟨(b : ℕ) - 21, by have := b.isLt; omega⟩, ?_, ?_⟩
  · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    have e : ((b : ℕ) - 21 + 21 - (a : ℕ)) % 21 = ((b : ℕ) + 21 - (a : ℕ)) % 21 := by omega
    rw [e]; exact hab
  · unfold PEqualNP.GenericRejection.incidenceInput
    rw [← List.ofFn_fin_append, ← hxe]
    congr 1
    funext i
    refine Fin.addCases (m := 21) (n := 21) (motive := fun i => decide (i = a ∨ i = b) = Fin.append (fun p : Fin 21 => decide (p ∈ ({(⟨a, ha⟩ : Fin 21)} : Finset (Fin 21)))) (fun l : Fin 21 => decide (l ∈ ({(⟨(b : ℕ) - 21, by have := b.isLt; omega⟩ : Fin 21)} : Finset (Fin 21)))) i) (fun p => ?_) (fun l => ?_) i
    · rw [Fin.append_left]
      congr 1
      apply propext
      rw [Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · exact Fin.ext (by have := congrArg Fin.val h; simpa using this)
        · have := congrArg Fin.val h
          simp only [Fin.val_castAdd] at this
          have := p.isLt
          omega
      · rintro rfl
        exact Or.inl (Fin.ext rfl)
    · rw [Fin.append_right]
      congr 1
      apply propext
      rw [Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · have := congrArg Fin.val h
          simp only [Fin.val_natAdd] at this
          omega
        · have := congrArg Fin.val h
          simp only [Fin.val_natAdd] at this
          exact Fin.ext (by simp only; omega)
      · rintro rfl
        exact Or.inr (Fin.ext (by simp only [Fin.val_natAdd]; omega))
