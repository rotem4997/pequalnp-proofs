import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card

namespace PEqualNP.Outside.L_meta_4779_aux

def Ind (E : List (ℕ × ℕ)) (x : Fin 14 → Bool) : Prop :=
  ¬∃ (i : Fin 14) (j : Fin 14), ((i : ℕ), (j : ℕ)) ∈ E ∧ x i = true ∧ x j = true

theorem falses_lt (x : Fin 14 → Bool) (v : Fin 14) (hv : x v = false) :
    (Finset.univ.filter (fun i => Function.update x v true i = false)).card <
      (Finset.univ.filter (fun i => x i = false)).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨v, by simp [hv], by simp⟩
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    by_cases h : i = v
    · subst h; simp at hi
    · rwa [Function.update_of_ne h] at hi

theorem ext (E : List (ℕ × ℕ)) (f : (Fin 14 → Bool) → Bool) (h07 : ((0 : ℕ), (7 : ℕ)) ∈ E)
    (hmono : ∀ (a b : Fin 14 → Bool), (∀ i, a i = true → b i = true) → f a = true → f b = true)
    (hH : ∀ (x : Fin 14 → Bool), Ind E x →
      (∀ (v : Fin 14), x v = false → ∃ (i : Fin 14) (j : Fin 14), ((i : ℕ), (j : ℕ)) ∈ E ∧
        Function.update x v true i = true ∧ Function.update x v true j = true) →
      x 0 = false ∨ x 7 = false → f x ≠ true) :
    ∀ (n : ℕ) (x : Fin 14 → Bool), (Finset.univ.filter (fun i => x i = false)).card ≤ n →
      Ind E x → f x = true → False := by
  intro n
  induction n with
  | zero =>
    intro x hc hi hf
    by_cases hm : ∀ (v : Fin 14), x v = false → ∃ (i : Fin 14) (j : Fin 14), ((i : ℕ), (j : ℕ)) ∈ E ∧
        Function.update x v true i = true ∧ Function.update x v true j = true
    · refine hH x hi hm ?_ hf
      by_contra h0
      simp only [not_or, Bool.not_eq_false] at h0
      exact hi ⟨0, 7, h07, h0.1, h0.2⟩
    · push_neg at hm
      obtain ⟨v, hv, _⟩ := hm
      have : v ∈ Finset.univ.filter (fun i => x i = false) := by simp [hv]
      have := Finset.card_pos.2 ⟨v, this⟩
      omega
  | succ n ih =>
    intro x hc hi hf
    by_cases hm : ∀ (v : Fin 14), x v = false → ∃ (i : Fin 14) (j : Fin 14), ((i : ℕ), (j : ℕ)) ∈ E ∧
        Function.update x v true i = true ∧ Function.update x v true j = true
    · refine hH x hi hm ?_ hf
      by_contra h0
      simp only [not_or, Bool.not_eq_false] at h0
      exact hi ⟨0, 7, h07, h0.1, h0.2⟩
    · push_neg at hm
      obtain ⟨v, hv, hnone⟩ := hm
      have hlt := falses_lt x v hv
      refine ih (Function.update x v true) (by omega) ?_ ?_
      · rintro ⟨i, j, hij, hi', hj'⟩
        exact hnone i j hij hi' hj'
      · refine hmono x _ ?_ hf
        intro i hxi
        by_cases h : i = v
        · subst h; simp
        · rw [Function.update_of_ne h]; exact hxi

end PEqualNP.Outside.L_meta_4779_aux

theorem PEqualNP.Outside.L_meta_4779 : ∀ (x1 : List (ℕ × ℕ)) (x2 : (Fin (14 : ℕ) → Bool) → Bool), ((0 : ℕ), (7 : ℕ)) ∈ x1 → (∀ (x4 x5 : Fin (14 : ℕ) → Bool), (∀ (x6 : Fin (14 : ℕ)), x4 x6 = Bool.true → x5 x6 = Bool.true) → x2 x4 = Bool.true → x2 x5 = Bool.true) → (∀ (x5 : Fin (14 : ℕ) → Bool), (¬∃ (x6 : Fin (14 : ℕ)) (x7 : Fin (14 : ℕ)), (↑x6, ↑x7) ∈ x1 ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → (∀ (x7 : Fin (14 : ℕ)), x5 x7 = Bool.false → ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)), (↑x9, ↑x10) ∈ x1 ∧ Function.update x5 x7 Bool.true x9 = Bool.true ∧ Function.update x5 x7 Bool.true x10 = Bool.true) → x5 (0 : Fin (14 : ℕ)) = Bool.false ∨ x5 (7 : Fin (14 : ℕ)) = Bool.false → x2 x5 ≠ Bool.true) → ∀ (x6 : Fin (14 : ℕ) → Bool), x2 x6 = Bool.true → ∃ (x8 : Fin (14 : ℕ)) (x9 : Fin (14 : ℕ)), (↑x8, ↑x9) ∈ x1 ∧ x6 x8 = Bool.true ∧ x6 x9 = Bool.true := by
  intro E f h07 hmono hH x hx
  by_contra hne
  exact PEqualNP.Outside.L_meta_4779_aux.ext E f h07 hmono hH _ x le_rfl hne hx
