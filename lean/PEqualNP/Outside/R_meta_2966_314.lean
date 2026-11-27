import Mathlib
import PEqualNP.Defs

set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2966_314
  (binary : let f := (fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
      (3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any
      (fun e => x e.1 && x e.2))
    ∀ (n : ℕ) (op : Fin n → Bool) (left right : Fin n → ℕ × Bool) (out : ℕ × Bool) (value : (Fin 9 → Bool) → ℕ → Bool),
    n ≤ 12 → (∀ j, (left j).1 < 10 + j.val ∧ (right j).1 < 10 + j.val) → out.1 < 10 + n →
    (∀ x (i : Fin 9), value x i.val = x i) →
    (∀ x, value x 9 = false) →
    (∀ x j, let pin := fun s : ℕ × Bool => value x s.1 ^^ s.2
      value x (10 + j.val) =
        if op j = true then pin (left j) && pin (right j) else pin (left j) || pin (right j)) →
    ∃ x, (value x out.1 ^^ out.2) ≠ f x)
  (freeOnly : let f := (fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
      (3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any
      (fun e => x e.1 && x e.2))
    ∀ (n : ℕ) (op : Fin n → Bool) (left right : Fin n → ℕ × Bool) (out : ℕ) (value : (Fin 9 → Bool) → ℕ → Bool),
    13 ≤ n → n ≤ 14 → (∀ j, (left j).1 < 10 + j.val ∧ (right j).1 < 10 + j.val) → out < 10 + n →
    (∀ j, ((left j).2 = true → (left j).1 = 0 ∨ (left j).1 = 9) ∧
      ((right j).2 = true → (right j).1 = 0 ∨ (right j).1 = 9)) →
    (∀ x (i : Fin 9), value x i.val = x i) →
    (∀ x, value x 9 = false) →
    (∀ x j, let pin := fun s : ℕ × Bool => value x s.1 ^^ s.2
      value x (10 + j.val) =
        if op j = true then pin (left j) && pin (right j) else pin (left j) || pin (right j)) →
    ∃ x, value x out ≠ f x)
  (oneExtra : let f := (fun x : Fin 9 → Bool => ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
      (3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any
      (fun e => x e.1 && x e.2))
    ∀ (extra : Fin 23) (op : Fin 13 → Bool) (left right : Fin 13 → ℕ × Bool) (out : ℕ) (value : (Fin 9 → Bool) → ℕ → Bool),
    extra.val ≠ 0 → extra.val ≠ 9 → (∀ j, (left j).1 < 10 + j.val ∧ (right j).1 < 10 + j.val) → out < 23 →
    (∀ j, ((left j).2 = true → (left j).1 = 0 ∨ (left j).1 = 9 ∨ (left j).1 = extra.val) ∧
      ((right j).2 = true → (right j).1 = 0 ∨ (right j).1 = 9 ∨ (right j).1 = extra.val)) →
    (∀ x (i : Fin 9), value x i.val = x i) →
    (∀ x, value x 9 = false) →
    (∀ x j, let pin := fun s : ℕ × Bool => value x s.1 ^^ s.2
      value x (10 + j.val) =
        if op j = true then pin (left j) && pin (right j) else pin (left j) || pin (right j)) →
    ∃ x, value x out ≠ f x) :
  ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : ℕ × Bool) (x6 : Finset ℕ) (x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   x6.card ≤ (3 : ℕ) →     x1 + x6.card ≤ (14 : ℕ) →       (∀ (x10 : Fin x1), (x3 x10).1 < (10 : ℕ) + ↑x10 ∧ (x4 x10).1 < (10 : ℕ) + ↑x10) →         x5.1 < (10 : ℕ) + x1 →           x5.2 = Bool.false →             (have x13 : ℕ × Bool → Prop := fun (x13 : ℕ × Bool) => x13.2 = Bool.true → x13.1 = (0 : ℕ) ∨ x13.1 = (9 : ℕ) ∨ x13.1 ∈ x6;               x13 x5 ∧ ∀ (x14 : Fin x1), x13 (x3 x14) ∧ x13 (x4 x14)) →               (∀ (x14 : Fin (9 : ℕ) → Bool) (x15 : Fin (9 : ℕ)), x7 x14 ↑x15 = x14 x15) →                 (∀ (x15 : Fin (9 : ℕ) → Bool), x7 x15 (9 : ℕ) = Bool.false) →                   (∀ (x16 : Fin (9 : ℕ) → Bool) (x17 : Fin x1),                       have x18 : ℕ × Bool → Bool := fun (x18 : ℕ × Bool) => x7 x16 x18.1 ^^ x18.2;                       x7 x16 ((10 : ℕ) + ↑x17) = if x2 x17 = Bool.true then x18 (x3 x17) && x18 (x4 x17) else x18 (x3 x17) || x18 (x4 x17)) →                     ∃ (x17 : Fin (9 : ℕ) → Bool), (x7 x17 x5.1 ^^ x5.2) ≠ (x17 (0 : Fin (9 : ℕ)) && x17 (1 : Fin (9 : ℕ)) || x17 (1 : Fin (9 : ℕ)) && x17 (2 : Fin (9 : ℕ)) || x17 (2 : Fin (9 : ℕ)) && x17 (3 : Fin (9 : ℕ)) || x17 (3 : Fin (9 : ℕ)) && x17 (4 : Fin (9 : ℕ)) || x17 (4 : Fin (9 : ℕ)) && x17 (0 : Fin (9 : ℕ)) || x17 (0 : Fin (9 : ℕ)) && x17 (5 : Fin (9 : ℕ)) || x17 (1 : Fin (9 : ℕ)) && x17 (6 : Fin (9 : ℕ)) || x17 (2 : Fin (9 : ℕ)) && x17 (7 : Fin (9 : ℕ)) || x17 (3 : Fin (9 : ℕ)) && x17 (8 : Fin (9 : ℕ)) || x17 (5 : Fin (9 : ℕ)) && x17 (7 : Fin (9 : ℕ)) || x17 (6 : Fin (9 : ℕ)) && x17 (8 : Fin (9 : ℕ)) || x17 (8 : Fin (9 : ℕ)) && x17 (5 : Fin (9 : ℕ))) := by
  intro n op left right out paid value paidSmall budget read outBound outPositive allowed onInputs zeroWire onGates
  by_cases small : n ≤ 12
  · obtain ⟨x, witness⟩ :=
      binary n op left right out value small read outBound onInputs zeroWire onGates
    exact ⟨x, by simpa only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] using witness⟩
  have nlower : 13 ≤ n := by omega
  have nupper : n ≤ 14 := by omega
  have cost : paid.card ≤ 1 := by omega
  have noExtra (ok : ∀ j, ((left j).2 = true → (left j).1 = 0 ∨ (left j).1 = 9) ∧
      ((right j).2 = true → (right j).1 = 0 ∨ (right j).1 = 9)) := by
    exact freeOnly n op left right out.1 value nlower nupper read outBound ok onInputs zeroWire onGates
  by_cases empty : paid = ∅
  · obtain ⟨x, witness⟩ := noExtra (fun j => by
      have h := allowed.2 j
      simpa [empty] using h)
    exact ⟨x, by simpa only [outPositive, Bool.xor_false, List.any_cons, List.any_nil,
      Bool.or_false, Bool.or_assoc] using witness⟩
  have one : paid.card = 1 := by
    have positive := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr empty)
    omega
  have hn : n = 13 := by omega
  subst n
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp one
  by_cases within : k < 23 ∧ k ≠ 0 ∧ k ≠ 9
  · let extra : Fin 23 := ⟨k, within.1⟩
    have ok : ∀ j,
        ((left j).2 = true → (left j).1 = 0 ∨ (left j).1 = 9 ∨ (left j).1 = extra.val) ∧
        ((right j).2 = true → (right j).1 = 0 ∨ (right j).1 = 9 ∨ (right j).1 = extra.val) := by
      intro j
      have h := allowed.2 j
      simpa [hk, extra] using h
    obtain ⟨x, witness⟩ :=
      oneExtra extra op left right out.1 value within.2.1 within.2.2
        read outBound ok onInputs zeroWire onGates
    exact ⟨x, by simpa only [outPositive, Bool.xor_false, List.any_cons, List.any_nil,
      Bool.or_false, Bool.or_assoc] using witness⟩
  · have exclude (s : ℕ × Bool) (lt : s.1 < 23)
        (ok : s.2 = true → s.1 = 0 ∨ s.1 = 9 ∨ s.1 ∈ paid) :
        s.2 = true → s.1 = 0 ∨ s.1 = 9 := by
      intro sign
      rcases ok sign with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      rw [hk, Finset.mem_singleton] at h
      by_contra! fail
      exact within ⟨h ▸ lt, fun e => fail.1 (h.trans e), fun e => fail.2 (h.trans e)⟩
    obtain ⟨x, witness⟩ := noExtra (fun j =>
      ⟨exclude (left j) (by have := (read j).1; omega) (allowed.2 j).1,
        exclude (right j) (by have := (read j).2; omega) (allowed.2 j).2⟩)
    exact ⟨x, by simpa only [outPositive, Bool.xor_false, List.any_cons, List.any_nil,
      Bool.or_false, Bool.or_assoc] using witness⟩
