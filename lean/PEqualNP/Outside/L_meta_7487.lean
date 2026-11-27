import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7487

def nbB (x y : Fin 13) : Bool := x == y || x == y + 1 || x == y + 3 || x == y + 9

theorem nb_iff : ∀ x y : Fin 13, (∃ x4 ∈ ({(0 : Fin 13), 1, 3, 9} : Finset (Fin 13)), x = y + x4) ↔ nbB x y = true := by
  decide

def inp (x4 : ℕ × ℕ) (x5 x6 : Fin 13) (x7 : Bool) : Fin (13 + 13) → Bool :=
  have x8 : ℕ → ℕ → Fin 13 → Bool := fun (x8 x9 : ℕ) (x10 : Fin 13) => if x7 = true then x9.testBit ↑(-(x5 * x10 + x6)) else x8.testBit ↑(x5 * x10 + x6)
  Fin.append (x8 x4.1 x4.2) (x8 x4.2 x4.1)

def selB (x11 : Fin 26 → Bool) (s : Bool) (v : Fin 13) (w : Fin 13) : Bool :=
  (if s = true then nbB v w else nbB w v) && x11 (if s = true then Fin.natAdd 13 w else Fin.castAdd 13 w)

def checkB (x11 : Fin 26 → Bool) : Bool :=
  ((List.finRange 13).all fun a => (List.finRange 13).all fun b => !(nbB a b && x11 (Fin.castAdd 13 a) && x11 (Fin.natAdd 13 b))) &&
  ([true, false].all fun s => (List.finRange 13).all fun v =>
     decide (((List.finRange 13).filter (selB x11 s v)).length ≤ 2))

def okP (p : ℕ × ℕ) : Bool :=
  [(1 : Fin 13), 3, 9].all fun m => (List.finRange 13).all fun c => [true, false].all fun f => checkB (inp p m c f)

theorem ok0 : okP (7, 904) = true := by decide +kernel

theorem ok1 : okP (13, 2848) = true := by decide +kernel

theorem ok2 : okP (19, 708) = true := by decide +kernel

theorem ok3 : okP (21, 2720) = true := by decide +kernel

theorem ok4 : okP (25, 2656) = true := by decide +kernel

theorem ok5 : okP (37, 2440) = true := by decide +kernel

theorem ok6 : okP (41, 2370) = true := by decide +kernel

theorem ok7 : okP (133, 808) = true := by decide +kernel

theorem three (p : Fin 13 → Bool) (h : ((List.finRange 13).filter p).length ≤ 2) (a b c : Fin 13)
    (ha : p a = true) (hb : p b = true) (hc : p c = true) : a = b ∨ a = c ∨ b = c := by
  by_contra hne
  push_neg at hne
  obtain ⟨h1, h2, h3⟩ := hne
  have hsub : ({a, b, c} : Finset (Fin 13)) ⊆ ((List.finRange 13).filter p).toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and]
    rcases hx with rfl | rfl | rfl <;> assumption
  have hc3 : ({a, b, c} : Finset (Fin 13)).card = 3 := Finset.card_eq_three.mpr ⟨a, b, c, h1, h2, h3, rfl⟩
  have := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
  omega

theorem fromCheck (x11 : Fin 26 → Bool) (h : checkB x11 = true) :
    (¬∃ (x12 : Fin 13) (x13 : Fin 13), (∃ x4 ∈ ({(0 : Fin 13), 1, 3, 9} : Finset (Fin 13)), x12 = x13 + x4) ∧ x11 (Fin.castAdd 13 x12) = true ∧ x11 (Fin.natAdd 13 x13) = true) ∧
    ∀ (x12 : Bool) (x13 : Fin 13) (x15 x16 x17 : Fin 13),
      ((if x12 = true then (∃ x4 ∈ ({(0 : Fin 13), 1, 3, 9} : Finset (Fin 13)), x13 = x15 + x4) else (∃ x4 ∈ ({(0 : Fin 13), 1, 3, 9} : Finset (Fin 13)), x15 = x13 + x4)) ∧ x11 (if x12 = true then Fin.natAdd 13 x15 else Fin.castAdd 13 x15) = true) →
      ((if x12 = true then (∃ x4 ∈ ({(0 : Fin 13), 1, 3, 9} : Finset (Fin 13)), x13 = x16 + x4) else (∃ x4 ∈ ({(0 : Fin 13), 1, 3, 9} : Finset (Fin 13)), x16 = x13 + x4)) ∧ x11 (if x12 = true then Fin.natAdd 13 x16 else Fin.castAdd 13 x16) = true) →
      ((if x12 = true then (∃ x4 ∈ ({(0 : Fin 13), 1, 3, 9} : Finset (Fin 13)), x13 = x17 + x4) else (∃ x4 ∈ ({(0 : Fin 13), 1, 3, 9} : Finset (Fin 13)), x17 = x13 + x4)) ∧ x11 (if x12 = true then Fin.natAdd 13 x17 else Fin.castAdd 13 x17) = true) →
      x15 = x16 ∨ x15 = x17 ∨ x16 = x17 := by
  unfold checkB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have := List.all_eq_true.mp (List.all_eq_true.mp h1 a (List.mem_finRange a)) b (List.mem_finRange b)
    rw [nb_iff] at hab
    rw [hab, ha, hb] at this
    simp at this
  · intro s v a b c ha hb hc
    have hl := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h2 s (by cases s <;> simp)) v (List.mem_finRange v))
    have key : ∀ w, ((if s = true then (∃ x4 ∈ ({(0 : Fin 13), 1, 3, 9} : Finset (Fin 13)), v = w + x4) else (∃ x4 ∈ ({(0 : Fin 13), 1, 3, 9} : Finset (Fin 13)), w = v + x4)) ∧ x11 (if s = true then Fin.natAdd 13 w else Fin.castAdd 13 w) = true) → selB x11 s v w = true := by
      intro w ⟨hw1, hw2⟩
      unfold selB
      cases s
      · simp only [Bool.false_eq_true, ite_false] at hw1 hw2 ⊢
        rw [nb_iff] at hw1
        simp only [hw1, hw2, Bool.and_self]
      · simp only [ite_true] at hw1 hw2 ⊢
        rw [nb_iff] at hw1
        simp only [hw1, hw2, Bool.and_self]
    exact three _ hl a b c (key a ha) (key b hb) (key c hc)

end PEqualNP.Outside.L_meta_7487

theorem PEqualNP.Outside.L_meta_7487 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x4 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x4 : ℕ × ℕ) (x5 x6 : Fin (13 : ℕ)) (x7 : Bool) =>   have x8 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x8 x9 : ℕ) (x10 : Fin (13 : ℕ)) => if x7 = Bool.true then x9.testBit ↑(-(x5 * x10 + x6)) else x8.testBit ↑(x5 * x10 + x6);   Fin.append (x8 x4.1 x4.2) (x8 x4.2 x4.1); ∀ x5 ∈ x3,   ∀ x7 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))],     ∀ (x9 : Fin (13 : ℕ)) (x10 : Bool),       have x11 : Fin ((13 : ℕ) + (13 : ℕ)) → Bool := x4 x5 x7 x9 x10;       (¬∃ (x12 : Fin (13 : ℕ)) (x13 : Fin (13 : ℕ)), x2 x12 x13 ∧ x11 (Fin.castAdd (13 : ℕ) x12) = Bool.true ∧ x11 (Fin.natAdd (13 : ℕ) x13) = Bool.true) ∧         ∀ (x12 : Bool) (x13 : Fin (13 : ℕ)),           have x14 : Fin (13 : ℕ) → Prop := fun (x14 : Fin (13 : ℕ)) => (if x12 = Bool.true then x2 x13 x14 else x2 x14 x13) ∧ x11 (if x12 = Bool.true then Fin.natAdd (13 : ℕ) x14 else Fin.castAdd (13 : ℕ) x14) = Bool.true;           ∀ (x15 x16 x17 : Fin (13 : ℕ)), x14 x15 → x14 x16 → x14 x17 → x15 = x16 ∨ x15 = x17 ∨ x16 = x17 := by
  dsimp only
  intro x5 hx5 x7 hx7 x9 x10
  have hall : PEqualNP.Outside.L_meta_7487.okP x5 = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx5
    rcases hx5 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact PEqualNP.Outside.L_meta_7487.ok0
    · exact PEqualNP.Outside.L_meta_7487.ok1
    · exact PEqualNP.Outside.L_meta_7487.ok2
    · exact PEqualNP.Outside.L_meta_7487.ok3
    · exact PEqualNP.Outside.L_meta_7487.ok4
    · exact PEqualNP.Outside.L_meta_7487.ok5
    · exact PEqualNP.Outside.L_meta_7487.ok6
    · exact PEqualNP.Outside.L_meta_7487.ok7
  unfold PEqualNP.Outside.L_meta_7487.okP at hall
  have hc := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hall x7 hx7) x9 (List.mem_finRange x9)) x10 (by cases x10 <;> simp)
  exact PEqualNP.Outside.L_meta_7487.fromCheck _ hc
