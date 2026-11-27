import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7521_aux

def V (x1 x2 : List ℕ) : Prop :=
  ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2,
    x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5

theorem V_snoc (B P : List ℕ) (g a b : ℕ) (hV : V B P) (ha : a ∈ B ++ P) (hb : b ∈ B ++ P)
    (hg : g = a &&& b ∨ g = a ||| b) : V B (P ++ [g]) := by
  intro i
  rcases Nat.lt_or_ge i.1 P.length with h | h
  · obtain ⟨u, hu, v, hv, e⟩ := hV ⟨i.1, h⟩
    refine ⟨u, ?_, v, ?_, ?_⟩
    · rw [List.take_append_of_le_length (Nat.le_of_lt h)]; exact hu
    · rw [List.take_append_of_le_length (Nat.le_of_lt h)]; exact hv
    · simpa [List.get_eq_getElem, List.getElem_append_left h] using e
  · have hi : i.1 = P.length := by
      have := i.2
      simp at this
      omega
    refine ⟨a, ?_, b, ?_, ?_⟩
    · rw [hi]; simpa using ha
    · rw [hi]; simpa using hb
    · rw [List.get_eq_getElem, List.getElem_append_right h]
      simpa using hg

theorem gen (f : Finset ℕ → Bool × ℕ × ℕ → Finset ℕ)
    (H : ∀ S x, (∀ y ∈ f S x, y ∈ S) ∨ ∃ a ∈ S, ∃ b ∈ S, ∃ g : ℕ,
      (g = a &&& b ∨ g = a ||| b) ∧ ∀ y ∈ f S x, y = g ∨ y ∈ S)
    (B : List ℕ) (ops : List (Bool × ℕ × ℕ)) :
    ∀ (S : Finset ℕ) (P : List ℕ), V B P → (∀ s ∈ S, s ∈ B ++ P) →
      ∃ Q : List ℕ, Q.length ≤ ops.length ∧ V B (P ++ Q) ∧
        ∀ y ∈ List.foldl f S ops, y ∈ B ++ (P ++ Q) := by
  induction ops with
  | nil =>
    intro S P hV hS
    exact ⟨[], by simp, by simpa using hV, by simpa using hS⟩
  | cons x xs ih =>
    intro S P hV hS
    rcases H S x with h | ⟨a, ha, b, hb, g, hg, h⟩
    · obtain ⟨Q, hl, hv, hm⟩ := ih (f S x) P hV (fun s hs => hS s (h s hs))
      exact ⟨Q, by simp; omega, hv, hm⟩
    · obtain ⟨Q, hl, hv, hm⟩ := ih (f S x) (P ++ [g])
        (V_snoc B P g a b hV (hS a ha) (hS b hb) hg)
        (fun s hs => by
          rcases h s hs with e | e
          · simp [e]
          · have := hS s e
            simp at this ⊢
            tauto)
      exact ⟨g :: Q, by simp; omega, by simpa using hv, by simpa using hm⟩

theorem V_nil (B : List ℕ) : V B [] := by
  intro i
  exact absurd i.2 (by simp)

theorem gen0 (f : Finset ℕ → Bool × ℕ × ℕ → Finset ℕ)
    (H : ∀ S x, (∀ y ∈ f S x, y ∈ S) ∨ ∃ a ∈ S, ∃ b ∈ S, ∃ g : ℕ,
      (g = a &&& b ∨ g = a ||| b) ∧ ∀ y ∈ f S x, y = g ∨ y ∈ S)
    (B : List ℕ) (ops : List (Bool × ℕ × ℕ)) (S : Finset ℕ) (hS : ∀ s ∈ S, s ∈ B) :
      ∃ Q : List ℕ, Q.length ≤ ops.length ∧ V B Q ∧
        ∀ y ∈ List.foldl f S ops, y ∈ B ++ Q := by
  obtain ⟨Q, hl, hv, hm⟩ := gen f H B ops S [] (V_nil _) (by simpa using hS)
  exact ⟨Q, hl, by simpa using hv, by simpa using hm⟩

theorem main (x2 : Finset ℕ) (x3 : List (Bool × ℕ × ℕ)) :
    ∃ (x4 : List ℕ), x4.length ≤ x3.length ∧ V x2.toList x4 ∧
      ∀ x5 ∈ List.foldl
        (fun (x6 : Finset ℕ) (x7 : Bool × ℕ × ℕ) =>
          have x8 : ℕ := x7.2.1;
          have x9 : ℕ := x7.2.2;
          if x8 ∈ x6 ∧ x9 ∈ x6 ∧ x8 ≠ x9 then Insert.insert (if x7.1 = Bool.true then x8 ||| x9 else x8 &&& x9) (if x2.card = (8 : ℕ) then (x6.erase x8).erase x9 else x6) else x6)
        x2 x3, x5 ∈ x2.toList ++ x4 := by
  refine gen0 _ ?_ x2.toList x3 x2 (by simp)
  intro S x
  beta_reduce
  try dsimp only
  by_cases h : x.2.1 ∈ S ∧ x.2.2 ∈ S ∧ x.2.1 ≠ x.2.2
  · right
    rw [if_pos h]
    refine ⟨x.2.1, h.1, x.2.2, h.2.1, (if x.1 = Bool.true then x.2.1 ||| x.2.2 else x.2.1 &&& x.2.2), ?_, ?_⟩
    · split_ifs <;> simp
    · intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with e | e
      · exact Or.inl e
      · right
        split_ifs at e
        · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase e)
        · exact e
  · left
    rw [if_neg h]
    exact fun y hy => hy

end PEqualNP.Outside.L_meta_7521_aux

theorem PEqualNP.Outside.L_meta_7521 : have x1 : List ℕ → List ℕ → Prop := fun (x1 x2 : List ℕ) => ∀ (x3 : Fin x2.length), ∃ x4 ∈ x1 ++ List.take (↑x3) x2, ∃ x5 ∈ x1 ++ List.take (↑x3) x2, x2.get x3 = x4 &&& x5 ∨ x2.get x3 = x4 ||| x5; ∀ (x2 : Finset ℕ) (x3 : List (Bool × ℕ × ℕ)),   ∃ (x4 : List ℕ),     x4.length ≤ x3.length ∧       x1 x2.toList x4 ∧         ∀           x5 ∈             List.foldl               (fun (x6 : Finset ℕ) (x7 : Bool × ℕ × ℕ) =>                 have x8 : ℕ := x7.2.1;                 have x9 : ℕ := x7.2.2;                 if x8 ∈ x6 ∧ x9 ∈ x6 ∧ x8 ≠ x9 then Insert.insert (if x7.1 = Bool.true then x8 ||| x9 else x8 &&& x9) (if x2.card = (8 : ℕ) then (x6.erase x8).erase x9 else x6) else x6)               x2 x3,           x5 ∈ x2.toList ++ x4 := by
  exact PEqualNP.Outside.L_meta_7521_aux.main
