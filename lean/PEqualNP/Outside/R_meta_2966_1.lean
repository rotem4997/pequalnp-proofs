import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2966_1
    (reservedOnly : ∀ (n : ℕ) (op : Fin n → Bool) (left right : Fin n → ℕ × Bool)
      (out : ℕ × Bool) (value : (Fin 9 → Bool) → ℕ → Bool),
      (∀ j : Fin n, (left j).1 < 10 + j.val ∧ (right j).1 < 10 + j.val) →
      out.1 < 10 + n → out.2 = false →
      n ≤ 14 →
      (let signed := fun i : ℕ × Bool => i.2 = true → i.1 = 0 ∨ i.1 = 9
       signed out ∧ ∀ j, signed (left j) ∧ signed (right j)) →
      (∀ (x : Fin 9 → Bool) (i : Fin 9), value x i.val = x i) →
      (∀ x : Fin 9 → Bool, value x 9 = false) →
      (∀ (x : Fin 9 → Bool) (j : Fin n),
        let read := fun i : ℕ × Bool => value x i.1 ^^ i.2
        value x (10 + j.val) =
          if op j = true then read (left j) && read (right j)
          else read (left j) || read (right j)) →
      (∀ r ∈ ([3,6,12,13,17,24,33,42,50,66,69,104,116,132,133,138,160,200,201,208,261,264,265,276,288,320,321,385,402] : List ℕ),
        let x : Fin 9 → Bool := fun i => r.testBit i.val
        (value x out.1 ^^ out.2) = decide (r ∈ ([3,6,12,13,17,24,33,66,132,133,160,264,265,288,320,321] : List ℕ))) →
      False)
    (additional : ∀ (n : ℕ) (op : Fin n → Bool) (left right : Fin n → ℕ × Bool)
      (out : ℕ × Bool) (value : (Fin 9 → Bool) → ℕ → Bool),
      (∀ j : Fin n, (left j).1 < 10 + j.val ∧ (right j).1 < 10 + j.val) →
      out.1 < 10 + n → out.2 = false →
      ∀ S : Finset ℕ, S.Nonempty → S.card ≤ 3 → n + S.card ≤ 14 →
      (let signed := fun i : ℕ × Bool => i.2 = true → i.1 = 0 ∨ i.1 = 9 ∨ i.1 ∈ S
       signed out ∧ ∀ j, signed (left j) ∧ signed (right j)) →
      (∀ (x : Fin 9 → Bool) (i : Fin 9), value x i.val = x i) →
      (∀ x : Fin 9 → Bool, value x 9 = false) →
      (∀ (x : Fin 9 → Bool) (j : Fin n),
        let read := fun i : ℕ × Bool => value x i.1 ^^ i.2
        value x (10 + j.val) =
          if op j = true then read (left j) && read (right j)
          else read (left j) || read (right j)) →
      (∀ x : Fin 9 → Bool, (value x out.1 ^^ out.2) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
         x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
         x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) → False) :
    ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : ℕ × Bool) (x6 : Finset ℕ) (x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   x6.card ≤ (3 : ℕ) →     x1 + x6.card ≤ (14 : ℕ) →       (∀ (x10 : Fin x1), (x3 x10).1 < (10 : ℕ) + ↑x10 ∧ (x4 x10).1 < (10 : ℕ) + ↑x10) →         x5.1 < (10 : ℕ) + x1 →           x5.2 = Bool.false →             (have x13 : ℕ × Bool → Prop := fun (x13 : ℕ × Bool) => x13.2 = Bool.true → x13.1 = (0 : ℕ) ∨ x13.1 = (9 : ℕ) ∨ x13.1 ∈ x6;               x13 x5 ∧ ∀ (x14 : Fin x1), x13 (x3 x14) ∧ x13 (x4 x14)) →               (∀ (x14 : Fin (9 : ℕ) → Bool) (x15 : Fin (9 : ℕ)), x7 x14 ↑x15 = x14 x15) →                 (∀ (x15 : Fin (9 : ℕ) → Bool), x7 x15 (9 : ℕ) = Bool.false) →                   (∀ (x16 : Fin (9 : ℕ) → Bool) (x17 : Fin x1),                       have x18 : ℕ × Bool → Bool := fun (x18 : ℕ × Bool) => x7 x16 x18.1 ^^ x18.2;                       x7 x16 ((10 : ℕ) + ↑x17) = if x2 x17 = Bool.true then x18 (x3 x17) && x18 (x4 x17) else x18 (x3 x17) || x18 (x4 x17)) →                     ∃ (x17 : Fin (9 : ℕ) → Bool), (x7 x17 x5.1 ^^ x5.2) ≠ (x17 (0 : Fin (9 : ℕ)) && x17 (1 : Fin (9 : ℕ)) || x17 (1 : Fin (9 : ℕ)) && x17 (2 : Fin (9 : ℕ)) || x17 (2 : Fin (9 : ℕ)) && x17 (3 : Fin (9 : ℕ)) || x17 (3 : Fin (9 : ℕ)) && x17 (4 : Fin (9 : ℕ)) || x17 (4 : Fin (9 : ℕ)) && x17 (0 : Fin (9 : ℕ)) || x17 (0 : Fin (9 : ℕ)) && x17 (5 : Fin (9 : ℕ)) || x17 (1 : Fin (9 : ℕ)) && x17 (6 : Fin (9 : ℕ)) || x17 (2 : Fin (9 : ℕ)) && x17 (7 : Fin (9 : ℕ)) || x17 (3 : Fin (9 : ℕ)) && x17 (8 : Fin (9 : ℕ)) || x17 (5 : Fin (9 : ℕ)) && x17 (7 : Fin (9 : ℕ)) || x17 (6 : Fin (9 : ℕ)) && x17 (8 : Fin (9 : ℕ)) || x17 (8 : Fin (9 : ℕ)) && x17 (5 : Fin (9 : ℕ))) := by
  intro n op left right out S value hCard hSize hEarlier hOut hPol hSigned hInput hZero hTrace
  by_contra! hAll
  by_cases hS : S.Nonempty
  · exact additional n op left right out value hEarlier hOut hPol S hS hCard hSize
      hSigned hInput hZero hTrace hAll
  · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    refine reservedOnly n op left right out value hEarlier hOut hPol (by omega)
      (by simpa [hempty] using hSigned) hInput hZero hTrace ?_
    intro r hr
    dsimp only
    rw [hAll]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
