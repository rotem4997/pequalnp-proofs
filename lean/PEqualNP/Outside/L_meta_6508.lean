import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6508

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


theorem aux : True := trivial

end PEqualNP.Outside.L_meta_6508

theorem PEqualNP.Outside.L_meta_6508 : ∀ (x1 : Type) (x2 : List (Bool → Set x1)),   have x3 : Bool → (Bool → Set x1) → (Bool → Set x1) → Bool → Set x1 := fun (x3 : Bool) (x4 x5 : Bool → Set x1) (x6 : Bool) => if x6 = x3 then x4 x6 ∪ x5 x6 else x4 x6 ∩ x5 x6;   have x4 : List (Bool → Set x1) → Prop := fun (x4 : List (Bool → Set x1)) =>     ∀ (x5 : Fin x4.length),       have x6 : List (Bool → Set x1) := x2 ++ List.take (↑x5) x4;       ∃ x7 ∈ x6, ∃ x8 ∈ x6, ∃ (x9 : Bool), ∀ (x10 : Bool), x4.get x5 x10 ⊆ if x10 = x9 then x7 x10 ∪ x8 x10 else x7 x10 ∩ x8 x10;   ∀ (x5 : List (Bool → Set x1)), x4 x5 → ∀ x7 ∈ x2 ++ x5, ∀ x9 ∈ x2 ++ x5, ∀ x11 ∈ x2 ++ x5, ∀ x13 ∈ x2 ++ x5, ∀ x15 ∈ x2 ++ x5, ∃ (x17 : List (Bool → Set x1)), x17.length = x5.length + (4 : ℕ) ∧ x4 x17 ∧ x3 Bool.true x15 (x3 Bool.false x13 (x3 Bool.true (x3 Bool.true x7 x9) x11)) ∈ x2 ++ x17 := by
  intro α B D W xs hxs a ha b hb c hc d hd e he
  have key : ∀ ys : List (Bool → Set α), W ys → ∀ p ∈ B ++ ys, ∀ q ∈ B ++ ys, ∀ t : Bool, W (ys ++ [D t p q]) := by
    intro ys hy p hp q hq t i
    have hi : (i : ℕ) < (ys ++ [D t p q]).length := i.isLt
    simp only [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_or_ge i ys.length with h | h
    · have := hy ⟨i, h⟩
      simp only [List.get_eq_getElem] at this ⊢
      rw [List.take_append_of_le_length (by omega), List.getElem_append_left h]
      exact this
    · have hh : (i : ℕ) = ys.length := by omega
      simp only [List.get_eq_getElem]
      have e1 : (ys ++ [D t p q])[(i : ℕ)]'i.isLt = D t p q := by
        rw [List.getElem_append_right (by omega)]; simp
      rw [e1, List.take_append_of_le_length (by omega), hh, List.take_length]
      refine ⟨p, hp, q, hq, t, fun x => ?_⟩
      simp [D]
  have m : ∀ (ys : List (Bool → Set α)) (z w : Bool → Set α), w ∈ B ++ ys → w ∈ B ++ (ys ++ [z]) := by
    intro ys z w hw
    rw [← List.append_assoc]; exact List.mem_append_left _ hw
  have l : ∀ (ys : List (Bool → Set α)) (z : Bool → Set α), z ∈ B ++ (ys ++ [z]) := by
    intro ys z; simp
  have w1 := key xs hxs a ha b hb true
  have w2 := key _ w1 _ (l xs (D true a b)) c (m _ _ _ hc) true
  have w3 := key _ w2 d (m _ _ _ (m _ _ _ hd)) _ (l _ (D true (D true a b) c)) false
  have w4 := key _ w3 e (m _ _ _ (m _ _ _ (m _ _ _ he))) _ (l _ (D false d (D true (D true a b) c))) true
  exact ⟨_, by simp, w4, l _ _⟩
