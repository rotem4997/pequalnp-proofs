import Mathlib

/-!
# Few NOT gates: the bound function

Step 1 of the few-NOT build: the recursive bound `fewNotBound m q s b K`, its two unfolding
equations, the two facts about a maximum taken by a right fold over `List.range r`, and two
sanity values.
-/

namespace PEqualNP.MetaComplexity.FewNot

/-- The bound with `s` NOT gates left, `b` points already fixed and window size `K`, for a
family of `m` sets where each point lies in `q + 1` sets of size `q + 1`. -/
def fewNotBound (m q s b K : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ)
    (fun b' K' : ℕ => (if b' = 0 then m else m - (b' * q + 1)) * min K' q)
    (fun _ (g : ℕ → ℕ → ℕ) (b' K' : ℕ) =>
      (List.range (min K' (q + 1) + 1)).foldr
        (fun (j acc : ℕ) => max acc (min (g (b' + j) (K' - j)) (g b' j))) 0)
    s b K

/-- Unfolding at zero NOT gates. -/
theorem fn_G_zero (m q b K : ℕ) :
    fewNotBound m q 0 b K = (if b = 0 then m else m - (b * q + 1)) * min K q := rfl

/-- Unfolding at `s + 1` NOT gates. -/
theorem fn_G_succ (m q s b K : ℕ) :
    fewNotBound m q (s + 1) b K =
      (List.range (min K (q + 1) + 1)).foldr
        (fun (j acc : ℕ) => max acc (min (fewNotBound m q s (b + j) (K - j))
          (fewNotBound m q s b j))) 0 := rfl

/-- Each term is at most the right-fold maximum. -/
theorem fn_le_foldr_max {f : ℕ → ℕ} {r j : ℕ} (hj : j ∈ List.range r) :
    f j ≤ (List.range r).foldr (fun (j acc : ℕ) => max acc (f j)) 0 := by
  suffices H : ∀ l : List ℕ, j ∈ l → f j ≤ l.foldr (fun (j acc : ℕ) => max acc (f j)) 0 from
    H _ hj
  intro l hl
  induction l with
  | nil => simp at hl
  | cons a l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp hl with h | h
    · subst h; exact le_max_right _ _
    · exact le_trans (ih h) (le_max_left _ _)

/-- The right-fold maximum is at most any common upper bound of the terms. -/
theorem fn_foldr_max_le {f : ℕ → ℕ} {r c : ℕ} (h : ∀ j ∈ List.range r, f j ≤ c) :
    (List.range r).foldr (fun (j acc : ℕ) => max acc (f j)) 0 ≤ c := by
  suffices H : ∀ l : List ℕ, (∀ j ∈ l, f j ≤ c) →
      l.foldr (fun (j acc : ℕ) => max acc (f j)) 0 ≤ c from H _ h
  intro l hl
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (ih fun j hj => hl j (List.mem_cons_of_mem a hj)) (hl a List.mem_cons_self)

/-- Sanity value, one NOT gate, the family of 73 sets. -/
theorem fn_val_one : fewNotBound 73 8 1 0 73 = 292 := by decide

/-- Sanity value, two NOT gates, the family of 73 sets. -/
theorem fn_val_two : fewNotBound 73 8 2 0 73 = 112 := by decide

end PEqualNP.MetaComplexity.FewNot
