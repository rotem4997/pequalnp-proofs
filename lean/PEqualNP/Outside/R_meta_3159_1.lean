import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3159_1
  (noPaid : ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x6 : Finset ℕ) (x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   (0 : ℕ) < x1 →     x6.card ≤ (3 : ℕ) →       x1 + x6.card ≤ (14 : ℕ) →         x6.card ≤ (1 : ℕ) → x6.card = (0 : ℕ) →           (∀ (x12 : Fin x1), (x3 x12).1 < (10 : ℕ) + ↑x12 ∧ (x4 x12).1 < (10 : ℕ) + ↑x12) →             (∀ (x13 : Fin (9 : ℕ)), ∃ (x14 : Fin x1), (x3 x14).1 = ↑x13 ∨ (x4 x14).1 = ↑x13) →               (∀ (x14 : ℕ), x14 ∈ x6 ↔ x14 ≠ (0 : ℕ) ∧ x14 ≠ (9 : ℕ) ∧ (Bool.false = Bool.true ∧ x14 = (9 : ℕ) + x1 ∨ ∃ (x15 : Fin x1), x3 x15 = (x14, Bool.true) ∨ x4 x15 = (x14, Bool.true))) →                 (∀ (x15 : Fin (9 : ℕ) → Bool) (x16 : Fin (9 : ℕ)), x7 x15 ↑x16 = x15 x16) →                   (∀ (x16 : Fin (9 : ℕ) → Bool), x7 x16 (9 : ℕ) = Bool.false) →                     (∀ (x17 : Fin (9 : ℕ) → Bool) (x18 : Fin x1),                         have x19 : ℕ × Bool → Bool := fun (x19 : ℕ × Bool) => x7 x17 x19.1 ^^ x19.2;                         x7 x17 ((10 : ℕ) + ↑x18) = if x2 x18 = Bool.true then x19 (x3 x18) && x19 (x4 x18) else x19 (x3 x18) || x19 (x4 x18)) →                       ∃ (x18 : Fin (9 : ℕ) → Bool), (x7 x18 ((9 : ℕ) + x1) ^^ Bool.false) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x19 : ℕ) => x18 (Fin.ofNat (9 : ℕ) (x19 / (10 : ℕ))) && x18 (Fin.ofNat (9 : ℕ) (x19 % (10 : ℕ))))
  (onePaid : ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x6 : Finset ℕ) (x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   (0 : ℕ) < x1 →     x6.card ≤ (3 : ℕ) →       x1 + x6.card ≤ (14 : ℕ) →         x6.card ≤ (1 : ℕ) → x6.card = (1 : ℕ) →           (∀ (x12 : Fin x1), (x3 x12).1 < (10 : ℕ) + ↑x12 ∧ (x4 x12).1 < (10 : ℕ) + ↑x12) →             (∀ (x13 : Fin (9 : ℕ)), ∃ (x14 : Fin x1), (x3 x14).1 = ↑x13 ∨ (x4 x14).1 = ↑x13) →               (∀ (x14 : ℕ), x14 ∈ x6 ↔ x14 ≠ (0 : ℕ) ∧ x14 ≠ (9 : ℕ) ∧ (Bool.false = Bool.true ∧ x14 = (9 : ℕ) + x1 ∨ ∃ (x15 : Fin x1), x3 x15 = (x14, Bool.true) ∨ x4 x15 = (x14, Bool.true))) →                 (∀ (x15 : Fin (9 : ℕ) → Bool) (x16 : Fin (9 : ℕ)), x7 x15 ↑x16 = x15 x16) →                   (∀ (x16 : Fin (9 : ℕ) → Bool), x7 x16 (9 : ℕ) = Bool.false) →                     (∀ (x17 : Fin (9 : ℕ) → Bool) (x18 : Fin x1),                         have x19 : ℕ × Bool → Bool := fun (x19 : ℕ × Bool) => x7 x17 x19.1 ^^ x19.2;                         x7 x17 ((10 : ℕ) + ↑x18) = if x2 x18 = Bool.true then x19 (x3 x18) && x19 (x4 x18) else x19 (x3 x18) || x19 (x4 x18)) →                       ∃ (x18 : Fin (9 : ℕ) → Bool), (x7 x18 ((9 : ℕ) + x1) ^^ Bool.false) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x19 : ℕ) => x18 (Fin.ofNat (9 : ℕ) (x19 / (10 : ℕ))) && x18 (Fin.ofNat (9 : ℕ) (x19 % (10 : ℕ)))) :
  ∀ (x1 : ℕ) (x2 : Fin x1 → Bool) (x3 x4 : Fin x1 → ℕ × Bool) (x5 : Bool) (x6 : Finset ℕ) (x7 : (Fin (9 : ℕ) → Bool) → ℕ → Bool),   (0 : ℕ) < x1 →     x6.card ≤ (3 : ℕ) →       x1 + x6.card ≤ (14 : ℕ) →         x6.card ≤ (1 : ℕ) →           (∀ (x12 : Fin x1), (x3 x12).1 < (10 : ℕ) + ↑x12 ∧ (x4 x12).1 < (10 : ℕ) + ↑x12) →             (∀ (x13 : Fin (9 : ℕ)), ∃ (x14 : Fin x1), (x3 x14).1 = ↑x13 ∨ (x4 x14).1 = ↑x13) →               (∀ (x14 : ℕ), x14 ∈ x6 ↔ x14 ≠ (0 : ℕ) ∧ x14 ≠ (9 : ℕ) ∧ (x5 = Bool.true ∧ x14 = (9 : ℕ) + x1 ∨ ∃ (x15 : Fin x1), x3 x15 = (x14, Bool.true) ∨ x4 x15 = (x14, Bool.true))) →                 (∀ (x15 : Fin (9 : ℕ) → Bool) (x16 : Fin (9 : ℕ)), x7 x15 ↑x16 = x15 x16) →                   (∀ (x16 : Fin (9 : ℕ) → Bool), x7 x16 (9 : ℕ) = Bool.false) →                     (∀ (x17 : Fin (9 : ℕ) → Bool) (x18 : Fin x1),                         have x19 : ℕ × Bool → Bool := fun (x19 : ℕ × Bool) => x7 x17 x19.1 ^^ x19.2;                         x7 x17 ((10 : ℕ) + ↑x18) = if x2 x18 = Bool.true then x19 (x3 x18) && x19 (x4 x18) else x19 (x3 x18) || x19 (x4 x18)) →                       ∃ (x18 : Fin (9 : ℕ) → Bool), (x7 x18 ((9 : ℕ) + x1) ^^ x5) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x19 : ℕ) => x18 (Fin.ofNat (9 : ℕ) (x19 / (10 : ℕ))) && x18 (Fin.ofNat (9 : ℕ) (x19 % (10 : ℕ))) := by
  intro n op l r phase paid w hn hthree budget hcard back every charged raw zero step
  cases phase with
  | false =>
    have choices : paid.card = 0 ∨ paid.card = 1 := by omega
    rcases choices with card | card
    · exact noPaid n op l r paid w hn hthree budget hcard card back every charged raw zero step
    · exact onePaid n op l r paid w hn hthree budget hcard card back every charged raw zero step
  | true =>
    classical
    have outPaid : 9+n ∈ paid :=
      (charged _).2 ⟨by omega, by omega, Or.inl ⟨rfl,rfl⟩⟩
    have clean (j : Fin n) (p : Nat × Bool) (hp : p = l j ∨ p = r j)
        (neg : p.2 = true) : p.1 = 0 ∨ p.1 = 9 := by
      by_cases h0 : p.1 = 0
      · exact Or.inl h0
      by_cases h9 : p.1 = 9
      · exact Or.inr h9
      have pp : p = (p.1,true) := Prod.ext rfl neg
      have member : p.1 ∈ paid := (charged _).2 ⟨h0,h9,Or.inr ⟨j,by
        rcases hp with h | h
        · exact Or.inl (h.symm.trans pp)
        · exact Or.inr (h.symm.trans pp)⟩⟩
      have eq : p.1 = 9+n := (Finset.card_le_one.mp hcard) _ member _ outPaid
      have earlier : p.1 < 10+j.val := by
        rcases hp with rfl | rfl
        · exact (back j).1
        · exact (back j).2
      have hj := j.isLt
      omega
    let off : Fin 9 → Bool := fun i => decide (i = 0)
    let on : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
    have inputMono (j : Fin 9) : off j = true → on j = true := by
      simp only [off,on,decide_eq_true_eq]
      exact Or.inl
    have equalZero : off 0 = on 0 := by decide
    have mono (i : Nat) : i < 10+n → w off i = true → w on i = true := by
      induction i using Nat.strong_induction_on with
      | ind i ih =>
        intro limit value
        by_cases hi : i < 9
        · rw [raw off ⟨i,hi⟩] at value
          rw [raw on ⟨i,hi⟩]
          exact inputMono ⟨i,hi⟩ value
        by_cases h9 : i = 9
        · subst i
          simp only [zero] at value
          contradiction
        let j : Fin n := ⟨i-10, by omega⟩
        have ji : i = 10+j.val := by dsimp [j]; omega
        have pinMono (p : Nat × Bool) (hp : p = l j ∨ p = r j) :
            (w off p.1 ^^ p.2) = true → (w on p.1 ^^ p.2) = true := by
          have earlier : p.1 < i := by
            rw [ji]
            rcases hp with rfl | rfl
            · exact (back j).1
            · exact (back j).2
          cases sign : p.2 with
          | false =>
            simpa only [sign, Bool.xor_false] using ih p.1 earlier (earlier.trans limit)
          | true =>
            have eq : w off p.1 = w on p.1 := by
              rcases clean j p hp sign with h | h
              · rw [h]
                exact (raw off ⟨0,by decide⟩).trans
                  (equalZero.trans (raw on ⟨0,by decide⟩).symm)
              · rw [h,zero,zero]
            rw [eq]
            exact id
        rw [ji,step] at value ⊢
        dsimp only at value ⊢
        cases hop : op j with
        | false =>
          simp only [hop, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true] at value ⊢
          exact value.elim
            (fun h => Or.inl (pinMono (l j) (Or.inl rfl) h))
            (fun h => Or.inr (pinMono (r j) (Or.inr rfl) h))
        | true =>
          simp only [hop, ↓reduceIte, Bool.and_eq_true] at value ⊢
          exact ⟨pinMono (l j) (Or.inl rfl) value.1,
            pinMono (r j) (Or.inr rfl) value.2⟩
    have offTarget : ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
        (fun e => off (Fin.ofNat 9 (e / 10)) && off (Fin.ofNat 9 (e % 10))) = false := by decide
    have onTarget : ([1,12,23,34,40,5,16,27,38,57,68,85] : List Nat).any
        (fun e => on (Fin.ofNat 9 (e / 10)) && on (Fin.ofNat 9 (e % 10))) = true := by decide
    cases value : w off (9+n) with
    | false =>
      refine ⟨off, ?_⟩
      rw [value,offTarget]
      decide
    | true =>
      refine ⟨on, ?_⟩
      rw [mono (9+n) (by omega) value,onTarget]
      decide
