import PEqualNP.Defs
import Mathlib.Data.List.GetD

theorem PEqualNP.Outside.L_meta_9242 :
    ∀ (x1 : List (Bool × ℕ × ℕ)) (x2 x3 : List ℕ) (x4 x5 : ℕ), x2.length = x3.length → (∀ (x7 : ℕ), (x2.getD x7 (0 : ℕ)).testBit x4 = Bool.true → (x3.getD x7 (0 : ℕ)).testBit x5 = Bool.true) → ∀ (x8 : ℕ), ((List.foldl (fun (x9 : List ℕ) (x10 : Bool × ℕ × ℕ) => x9 ++ [if x10.1 = Bool.true then x9.getD x10.2.1 (0 : ℕ) ||| x9.getD x10.2.2 (0 : ℕ) else x9.getD x10.2.1 (0 : ℕ) &&& x9.getD x10.2.2 (0 : ℕ)]) x2 x1).getD x8 (0 : ℕ)).testBit x4 = Bool.true → ((List.foldl (fun (x10 : List ℕ) (x11 : Bool × ℕ × ℕ) => x10 ++ [if x11.1 = Bool.true then x10.getD x11.2.1 (0 : ℕ) ||| x10.getD x11.2.2 (0 : ℕ) else x10.getD x11.2.1 (0 : ℕ) &&& x10.getD x11.2.2 (0 : ℕ)]) x3 x1).getD x8 (0 : ℕ)).testBit x5 = Bool.true := by
  intro gs
  induction gs with
  | nil =>
    intro a b r s _ h k hk
    exact h k hk
  | cons g gs ih =>
    intro a b r s hl h
    simp only [List.foldl_cons]
    apply ih _ _ r s (by simp [hl])
    intro k hk
    by_cases hlt : k < a.length
    · rw [List.getD_append _ _ _ _ hlt] at hk
      rw [List.getD_append _ _ _ _ (by omega)]
      exact h k hk
    · by_cases heq : k = a.length
      · subst heq
        rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero] at hk
        rw [hl, List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
        by_cases hg : g.1 = true
        · rw [if_pos hg] at hk ⊢
          rw [Nat.testBit_or, Bool.or_eq_true] at hk ⊢
          rcases hk with hk | hk
          · exact Or.inl (h _ hk)
          · exact Or.inr (h _ hk)
        · rw [if_neg hg] at hk ⊢
          rw [Nat.testBit_and, Bool.and_eq_true] at hk ⊢
          exact ⟨h _ hk.1, h _ hk.2⟩
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hk
        simp at hk
