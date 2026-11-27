import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7623

def stepF (l : List ℕ) (n : ℕ) : List ℕ :=
  l ++ [if n < (4096 : ℕ) then l.getD (n % (64 : ℕ)) (0 : ℕ) &&& l.getD (n / (64 : ℕ) % (64 : ℕ)) (0 : ℕ)
    else l.getD (n % (64 : ℕ)) (0 : ℕ) ||| l.getD (n / (64 : ℕ) % (64 : ℕ)) (0 : ℕ)]

def Rel (a b : ℕ) (l l' : List ℕ) : Prop :=
  l.length = l'.length ∧ ∀ i : ℕ, (l.getD i 0).testBit a = true → (l'.getD i 0).testBit b = true

theorem getD_snoc (l : List ℕ) (v i : ℕ) :
    (l ++ [v]).getD i 0 = if i < l.length then l.getD i 0 else if i = l.length then v else 0 := by
  by_cases h : i < l.length
  · rw [if_pos h, List.getD_append _ _ _ _ h]
  · rw [if_neg h, List.getD_append_right _ _ _ _ (by omega)]
    rcases Nat.exists_eq_add_of_le (show l.length ≤ i by omega) with ⟨k, rfl⟩
    cases k with
    | zero => simp
    | succ k => simp

theorem step (a b n : ℕ) (l l' : List ℕ) (h : Rel a b l l') : Rel a b (stepF l n) (stepF l' n) := by
  obtain ⟨hlen, H⟩ := h
  refine ⟨by simp [stepF, hlen], ?_⟩
  intro i hi
  unfold stepF at hi ⊢
  rw [getD_snoc] at hi ⊢
  rw [← hlen]
  by_cases h1 : i < l.length
  · rw [if_pos h1] at hi ⊢
    exact H i hi
  · rw [if_neg h1] at hi ⊢
    by_cases h2 : i = l.length
    · rw [if_pos h2] at hi ⊢
      have Ha := H (n % 64)
      have Hb := H (n / 64 % 64)
      split_ifs at hi ⊢ <;> simp only [Nat.testBit_land, Nat.testBit_lor, Bool.and_eq_true, Bool.or_eq_true] at hi ⊢
      · exact ⟨Ha hi.1, Hb hi.2⟩
      · rcases hi with hi | hi
        · exact Or.inl (Ha hi)
        · exact Or.inr (Hb hi)
    · rw [if_neg h2] at hi
      simp at hi

theorem main (a b : ℕ) (xs : List ℕ) : ∀ (l l' : List ℕ), Rel a b l l' →
    Rel a b (xs.foldl stepF l) (xs.foldl stepF l') := by
  induction xs with
  | nil => intro l l' h; exact h
  | cons x xs ih => intro l l' h; exact ih _ _ (step a b x l l' h)

end PEqualNP.Outside.L_meta_7623

theorem PEqualNP.Outside.L_meta_7623 : have x1 : List ℕ → ℕ → List ℕ := fun (x1 : List ℕ) (x2 : ℕ) => x1 ++ [if x2 < (4096 : ℕ) then x1.getD (x2 % (64 : ℕ)) (0 : ℕ) &&& x1.getD (x2 / (64 : ℕ) % (64 : ℕ)) (0 : ℕ) else x1.getD (x2 % (64 : ℕ)) (0 : ℕ) ||| x1.getD (x2 / (64 : ℕ) % (64 : ℕ)) (0 : ℕ)]; ∀ (x2 x3 : List ℕ) (x4 : List (Fin (8192 : ℕ))) (x5 x6 : ℕ), x2.length = x3.length → (∀ (x8 : ℕ), (x2.getD x8 (0 : ℕ)).testBit x5 = Bool.true → (x3.getD x8 (0 : ℕ)).testBit x6 = Bool.true) → ∀ (x9 : ℕ), ((List.foldl x1 x2 (List.map Fin.val x4)).getD x9 (0 : ℕ)).testBit x5 = Bool.true → ((List.foldl x1 x3 (List.map Fin.val x4)).getD x9 (0 : ℕ)).testBit x6 = Bool.true := by
  intro x1 x2 x3 x4 x5 x6 hlen H x9 hx
  exact (PEqualNP.Outside.L_meta_7623.main x5 x6 (List.map Fin.val x4) x2 x3 ⟨hlen, H⟩).2 x9 hx
