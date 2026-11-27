import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18637_aux

def masks : List ℕ :=
  [7405575,23330829,5799955,22282261,21757977,21233693,3735587,19988517,3211303,19415081,7372867,24117317,7340103,23085129,23068749,22052945,5275731,22020181,19939425,19923045,18890857,6389891,6619269,6357127,6570121,6553741,6324419,6308041,21512457,21528849,4751635,21496089,17318185,20988233,21004625,17891877]

def D : Finset (Fin 13) := {0, 1, 3, 9}

def inD (x : Fin 13) : Bool :=
  x == 0 || x == 1 || x == 3 || x == 9

theorem inD_iff (x : Fin 13) : inD x = true ↔ x ∈ D := by
  revert x
  decide

def b2n (b : Bool) : ℕ :=
  if b then 1 else 0

def arc3 (a b : Fin 13) : Bool :=
  (List.finRange 13).all fun l =>
    decide (b2n (inD (0 - l)) + b2n (inD (a - l)) + b2n (inD (b - l)) ≤ 2)

def arc4 (a b c : Fin 13) : Bool :=
  (List.finRange 13).all fun l =>
    decide (b2n (inD (0 - l)) + b2n (inD (a - l)) + b2n (inD (b - l)) + b2n (inD (c - l)) ≤ 2)

def ok3 (a b : Fin 13) (k : ℕ) (t : Fin 13) : Bool :=
  (List.finRange 13).all (fun p => k.testBit (p - t).val == (p == 0 || p == a || p == b)) &&
  (List.finRange 13).all (fun l => k.testBit (13 + (l - t).val) == (!inD (0 - l) && !inD (a - l) && !inD (b - l)))

def ok4 (a b c : Fin 13) (k : ℕ) (t : Fin 13) : Bool :=
  (List.finRange 13).all (fun p => k.testBit (p - t).val == (p == 0 || p == a || p == b || p == c)) &&
  (List.finRange 13).all (fun l => k.testBit (13 + (l - t).val) == (!inD (0 - l) && !inD (a - l) && !inD (b - l) && !inD (c - l)))

def wit3 (a b : Fin 13) : ℕ × Fin 13 :=
  match (a.val, b.val) with
  | (1, 2) => (7405575, (0 : Fin 13))
  | (1, 4) => (5799955, (0 : Fin 13))
  | (1, 5) => (3735587, (0 : Fin 13))
  | (1, 6) => (7372867, (0 : Fin 13))
  | (1, 7) => (6389891, (0 : Fin 13))
  | (1, 8) => (19939425, (8 : Fin 13))
  | (1, 10) => (21757977, (10 : Fin 13))
  | (1, 11) => (23330829, (11 : Fin 13))
  | (1, 12) => (7405575, (12 : Fin 13))
  | (2, 3) => (23330829, (0 : Fin 13))
  | (2, 4) => (22282261, (0 : Fin 13))
  | (2, 5) => (19988517, (0 : Fin 13))
  | (2, 6) => (24117317, (0 : Fin 13))
  | (2, 7) => (6619269, (0 : Fin 13))
  | (2, 9) => (22052945, (9 : Fin 13))
  | (2, 10) => (19415081, (10 : Fin 13))
  | (2, 11) => (22282261, (11 : Fin 13))
  | (3, 4) => (21757977, (0 : Fin 13))
  | (3, 5) => (19415081, (0 : Fin 13))
  | (3, 6) => (23085129, (0 : Fin 13))
  | (3, 7) => (6570121, (0 : Fin 13))
  | (3, 8) => (21512457, (0 : Fin 13))
  | (3, 10) => (23085129, (10 : Fin 13))
  | (3, 11) => (19988517, (11 : Fin 13))
  | (3, 12) => (5799955, (12 : Fin 13))
  | (4, 6) => (22052945, (0 : Fin 13))
  | (4, 8) => (21528849, (0 : Fin 13))
  | (4, 9) => (21528849, (9 : Fin 13))
  | (4, 10) => (6570121, (10 : Fin 13))
  | (4, 11) => (24117317, (11 : Fin 13))
  | (4, 12) => (3735587, (12 : Fin 13))
  | (5, 6) => (19939425, (0 : Fin 13))
  | (5, 8) => (21512457, (5 : Fin 13))
  | (5, 9) => (21528849, (5 : Fin 13))
  | (5, 10) => (21512457, (10 : Fin 13))
  | (5, 11) => (6619269, (11 : Fin 13))
  | (5, 12) => (7372867, (12 : Fin 13))
  | (6, 7) => (6389891, (6 : Fin 13))
  | (6, 8) => (6619269, (6 : Fin 13))
  | (6, 9) => (6570121, (6 : Fin 13))
  | (6, 12) => (6389891, (12 : Fin 13))
  | (7, 8) => (7372867, (7 : Fin 13))
  | (7, 9) => (24117317, (7 : Fin 13))
  | (7, 10) => (23085129, (7 : Fin 13))
  | (7, 11) => (22052945, (7 : Fin 13))
  | (7, 12) => (19939425, (7 : Fin 13))
  | (8, 9) => (3735587, (8 : Fin 13))
  | (8, 10) => (19988517, (8 : Fin 13))
  | (8, 11) => (19415081, (8 : Fin 13))
  | (9, 10) => (5799955, (9 : Fin 13))
  | (9, 11) => (22282261, (9 : Fin 13))
  | (9, 12) => (21757977, (9 : Fin 13))
  | (10, 12) => (23330829, (10 : Fin 13))
  | (11, 12) => (7405575, (11 : Fin 13))
  | _ => (7405575, 0)

def wit4 (a b c : Fin 13) : ℕ × Fin 13 :=
  match (a.val, b.val, c.val) with
  | (1, 2, 5) => (3211303, (0 : Fin 13))
  | (1, 2, 6) => (7340103, (0 : Fin 13))
  | (1, 2, 7) => (6357127, (0 : Fin 13))
  | (1, 2, 11) => (21233693, (11 : Fin 13))
  | (1, 4, 6) => (5275731, (0 : Fin 13))
  | (1, 4, 8) => (4751635, (0 : Fin 13))
  | (1, 4, 11) => (23068749, (11 : Fin 13))
  | (1, 4, 12) => (3211303, (12 : Fin 13))
  | (1, 5, 10) => (21496089, (10 : Fin 13))
  | (1, 5, 11) => (6553741, (11 : Fin 13))
  | (1, 5, 12) => (7340103, (12 : Fin 13))
  | (1, 6, 7) => (6324419, (0 : Fin 13))
  | (1, 6, 12) => (6357127, (12 : Fin 13))
  | (1, 7, 8) => (6324419, (7 : Fin 13))
  | (1, 7, 10) => (6308041, (7 : Fin 13))
  | (1, 8, 10) => (19923045, (8 : Fin 13))
  | (1, 8, 11) => (18890857, (8 : Fin 13))
  | (1, 10, 12) => (21233693, (10 : Fin 13))
  | (2, 3, 4) => (21233693, (0 : Fin 13))
  | (2, 3, 6) => (23068749, (0 : Fin 13))
  | (2, 3, 7) => (6553741, (0 : Fin 13))
  | (2, 3, 10) => (18890857, (10 : Fin 13))
  | (2, 4, 6) => (22020181, (0 : Fin 13))
  | (2, 4, 9) => (21004625, (9 : Fin 13))
  | (2, 4, 11) => (22020181, (11 : Fin 13))
  | (2, 5, 6) => (19923045, (0 : Fin 13))
  | (2, 5, 9) => (17891877, (0 : Fin 13))
  | (2, 5, 10) => (17318185, (10 : Fin 13))
  | (2, 7, 10) => (20988233, (7 : Fin 13))
  | (2, 7, 11) => (21004625, (7 : Fin 13))
  | (2, 9, 10) => (5275731, (9 : Fin 13))
  | (2, 9, 11) => (22020181, (9 : Fin 13))
  | (3, 4, 8) => (21496089, (0 : Fin 13))
  | (3, 4, 10) => (6308041, (10 : Fin 13))
  | (3, 4, 11) => (19923045, (11 : Fin 13))
  | (3, 5, 6) => (18890857, (0 : Fin 13))
  | (3, 5, 8) => (17318185, (0 : Fin 13))
  | (3, 5, 10) => (20988233, (10 : Fin 13))
  | (3, 5, 12) => (5275731, (12 : Fin 13))
  | (3, 6, 7) => (6308041, (0 : Fin 13))
  | (3, 6, 8) => (20988233, (0 : Fin 13))
  | (3, 7, 11) => (17891877, (11 : Fin 13))
  | (3, 7, 12) => (4751635, (12 : Fin 13))
  | (3, 8, 11) => (17318185, (8 : Fin 13))
  | (3, 10, 12) => (23068749, (10 : Fin 13))
  | (3, 11, 12) => (3211303, (11 : Fin 13))
  | (4, 6, 8) => (21004625, (0 : Fin 13))
  | (4, 6, 9) => (17891877, (4 : Fin 13))
  | (4, 8, 10) => (17891877, (8 : Fin 13))
  | (4, 9, 10) => (4751635, (9 : Fin 13))
  | (4, 9, 12) => (21496089, (9 : Fin 13))
  | (4, 10, 12) => (6553741, (10 : Fin 13))
  | (4, 11, 12) => (7340103, (11 : Fin 13))
  | (5, 6, 9) => (4751635, (5 : Fin 13))
  | (5, 6, 12) => (6324419, (12 : Fin 13))
  | (5, 8, 9) => (21496089, (5 : Fin 13))
  | (5, 8, 10) => (17318185, (5 : Fin 13))
  | (5, 8, 11) => (20988233, (5 : Fin 13))
  | (5, 9, 11) => (21004625, (5 : Fin 13))
  | (5, 11, 12) => (6357127, (11 : Fin 13))
  | (6, 7, 8) => (6357127, (6 : Fin 13))
  | (6, 7, 12) => (6324419, (6 : Fin 13))
  | (6, 8, 9) => (6553741, (6 : Fin 13))
  | (6, 9, 12) => (6308041, (6 : Fin 13))
  | (7, 8, 9) => (7340103, (7 : Fin 13))
  | (7, 8, 11) => (5275731, (7 : Fin 13))
  | (7, 9, 10) => (23068749, (7 : Fin 13))
  | (7, 9, 11) => (22020181, (7 : Fin 13))
  | (7, 9, 12) => (19923045, (7 : Fin 13))
  | (7, 10, 12) => (18890857, (7 : Fin 13))
  | (8, 9, 10) => (3211303, (8 : Fin 13))
  | (9, 11, 12) => (21233693, (9 : Fin 13))
  | _ => (7405575, 0)

theorem check3 :
    ∀ a b : Fin 13, 0 < a → a < b → arc3 a b = true →
      (wit3 a b).1 ∈ masks ∧ ok3 a b (wit3 a b).1 (wit3 a b).2 = true := by
  decide +kernel

set_option maxHeartbeats 1000000 in
theorem check4 :
    ∀ a b c : Fin 13, 0 < a → a < b → b < c → arc4 a b c = true →
      (wit4 a b c).1 ∈ masks ∧ ok4 a b c (wit4 a b c).1 (wit4 a b c).2 = true := by
  decide +kernel

theorem sort3 {a b c : Fin 13} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ x y z : Fin 13, x < y ∧ y < z ∧ ({a, b, c} : Finset (Fin 13)) = {x, y, z} := by
  rcases lt_or_gt_of_ne hab with h1 | h1 <;>
  rcases lt_or_gt_of_ne hac with h2 | h2 <;>
  rcases lt_or_gt_of_ne hbc with h3 | h3
  · exact ⟨a, b, c, h1, h3, rfl⟩
  · exact ⟨a, c, b, h2, h3, by ext u; simp; tauto⟩
  · exact absurd (lt_trans h1 h3) (not_lt.mpr (le_of_lt h2))
  · exact ⟨c, a, b, h2, h1, by ext u; simp; tauto⟩
  · exact ⟨b, a, c, h1, h2, by ext u; simp; tauto⟩
  · exact absurd (lt_trans h3 h1) (not_lt.mpr (le_of_lt h2))
  · exact ⟨b, c, a, h3, h2, by ext u; simp; tauto⟩
  · exact ⟨c, b, a, h3, h1, by ext u; simp; tauto⟩

theorem card_filter_triple {a b : Fin 13} (ha : 0 < a) (hab : a < b) (l : Fin 13) :
    (({0, a, b} : Finset (Fin 13)).filter (fun i => i - l ∈ D)).card =
      b2n (inD (0 - l)) + b2n (inD (a - l)) + b2n (inD (b - l)) := by
  have h0a : (0 : Fin 13) ≠ a := ne_of_lt ha
  have h0b : (0 : Fin 13) ≠ b := ne_of_lt (lt_trans ha hab)
  have hab' : a ≠ b := ne_of_lt hab
  have h1 : ({0, a, b} : Finset (Fin 13)).filter (fun i => i - l ∈ D) =
      (if 0 - l ∈ D then {0} else ∅) ∪ (if a - l ∈ D then {a} else ∅) ∪ (if b - l ∈ D then {b} else ∅) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
    by_cases h0 : 0 - l ∈ D <;> by_cases ha' : a - l ∈ D <;> by_cases hb' : b - l ∈ D <;>
      simp [ha', hb'] <;> grind
  rw [h1]
  have hd1 : Disjoint (if 0 - l ∈ D then ({0} : Finset (Fin 13)) else ∅) (if a - l ∈ D then {a} else ∅) := by
    split_ifs <;> simp [h0a]
  have hd2 : Disjoint ((if 0 - l ∈ D then ({0} : Finset (Fin 13)) else ∅) ∪ (if a - l ∈ D then {a} else ∅))
      (if b - l ∈ D then {b} else ∅) := by
    split_ifs <;> simp [h0b, hab', h0b.symm, hab'.symm]
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
  simp only [b2n, inD_iff]
  split_ifs <;> simp

theorem card_filter_quad {a b c : Fin 13} (ha : 0 < a) (hab : a < b) (hbc : b < c) (l : Fin 13) :
    (({0, a, b, c} : Finset (Fin 13)).filter (fun i => i - l ∈ D)).card =
      b2n (inD (0 - l)) + b2n (inD (a - l)) + b2n (inD (b - l)) + b2n (inD (c - l)) := by
  have h0a : (0 : Fin 13) ≠ a := ne_of_lt ha
  have h0b : (0 : Fin 13) ≠ b := ne_of_lt (lt_trans ha hab)
  have h0c : (0 : Fin 13) ≠ c := ne_of_lt (lt_trans (lt_trans ha hab) hbc)
  have hab' : a ≠ b := ne_of_lt hab
  have hac' : a ≠ c := ne_of_lt (lt_trans hab hbc)
  have hbc' : b ≠ c := ne_of_lt hbc
  have h1 : ({0, a, b, c} : Finset (Fin 13)).filter (fun i => i - l ∈ D) =
      (if 0 - l ∈ D then {0} else ∅) ∪ (if a - l ∈ D then {a} else ∅) ∪
      (if b - l ∈ D then {b} else ∅) ∪ (if c - l ∈ D then {c} else ∅) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union]
    by_cases h0 : 0 - l ∈ D <;> by_cases ha' : a - l ∈ D <;>
      by_cases hb' : b - l ∈ D <;> by_cases hc' : c - l ∈ D <;>
      simp [ha', hb', hc'] <;> grind
  rw [h1]
  have hd1 : Disjoint (if 0 - l ∈ D then ({0} : Finset (Fin 13)) else ∅) (if a - l ∈ D then {a} else ∅) := by
    split_ifs <;> simp [h0a]
  have hd2 : Disjoint ((if 0 - l ∈ D then ({0} : Finset (Fin 13)) else ∅) ∪ (if a - l ∈ D then {a} else ∅))
      (if b - l ∈ D then {b} else ∅) := by
    split_ifs <;> simp [h0b, hab', h0b.symm, hab'.symm]
  have hd3 : Disjoint ((if 0 - l ∈ D then ({0} : Finset (Fin 13)) else ∅) ∪ (if a - l ∈ D then {a} else ∅) ∪
      (if b - l ∈ D then {b} else ∅)) (if c - l ∈ D then {c} else ∅) := by
    split_ifs <;> simp [h0c, hac', hbc', h0c.symm, hac'.symm, hbc'.symm]
  rw [Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1]
  simp only [b2n, inD_iff]
  split_ifs <;> simp

theorem locate_zero (Q : Finset (Fin 13)) (h0 : (0 : Fin 13) ∈ Q) (hcard : Q.card = 3 ∨ Q.card = 4)
    (harc : ∀ l : Fin 13, (Q.filter (fun i => i - l ∈ D)).card ≤ 2) :
    ∃ k ∈ masks, ∃ t : Fin 13,
      (∀ p : Fin 13, k.testBit (p - t).val = decide (p ∈ Q)) ∧
      ∀ l : Fin 13, k.testBit (13 + (l - t).val) = decide (∀ p ∈ Q, p - l ∉ D) := by
  have hQins : insert (0 : Fin 13) (Q.erase 0) = Q := Finset.insert_erase h0
  have h0n : (0 : Fin 13) ∉ Q.erase 0 := Finset.notMem_erase 0 Q
  have hce : (Q.erase 0).card = Q.card - 1 := Finset.card_erase_of_mem h0
  rcases hcard with hc3 | hc4
  · have hr2 : (Q.erase 0).card = 2 := by omega
    obtain ⟨u, v, huv, hR⟩ := Finset.card_eq_two.mp hr2
    have hpair : ∃ a b : Fin 13, a < b ∧ Q.erase 0 = {a, b} := by
      rcases lt_or_gt_of_ne huv with hlt | hgt
      · exact ⟨u, v, hlt, hR⟩
      · exact ⟨v, u, hgt, by rw [hR, Finset.pair_comm]⟩
    obtain ⟨a, b, hab, hRab⟩ := hpair
    have ha0 : a ≠ 0 := fun h => h0n (by rw [hRab, h]; simp)
    have ha : (0 : Fin 13) < a := Nat.pos_of_ne_zero (fun h => ha0 (Fin.ext h))
    have hQeq : Q = {0, a, b} := by rw [← hQins, hRab]
    subst hQeq
    have harc3 : arc3 a b = true := by
      unfold arc3
      rw [List.all_eq_true]
      intro l _
      rw [decide_eq_true_eq, ← card_filter_triple ha hab l]
      exact harc l
    obtain ⟨hmem, hok⟩ := check3 a b ha hab harc3
    refine ⟨(wit3 a b).1, hmem, (wit3 a b).2, ?_, ?_⟩
    · unfold ok3 at hok
      rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hok
      intro p
      have hp := hok.1 p (List.mem_finRange p)
      rw [beq_iff_eq] at hp
      rw [hp]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]
      tauto
    · unfold ok3 at hok
      rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hok
      intro l
      have hl := hok.2 l (List.mem_finRange l)
      rw [beq_iff_eq] at hl
      rw [hl]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩ p hp
        rcases hp with rfl | rfl | rfl
        · intro hd; exact absurd ((inD_iff _).mpr hd) (by rw [h1]; decide)
        · intro hd; exact absurd ((inD_iff _).mpr hd) (by rw [h2]; decide)
        · intro hd; exact absurd ((inD_iff _).mpr hd) (by rw [h3]; decide)
      · intro h
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · cases hd : inD (0 - l)
          · rfl
          · exact absurd ((inD_iff _).mp hd) (h 0 (Or.inl rfl))
        · cases hd : inD (a - l)
          · rfl
          · exact absurd ((inD_iff _).mp hd) (h a (Or.inr (Or.inl rfl)))
        · cases hd : inD (b - l)
          · rfl
          · exact absurd ((inD_iff _).mp hd) (h b (Or.inr (Or.inr rfl)))
  · have hr3 : (Q.erase 0).card = 3 := by omega
    obtain ⟨u, v, w, huv, huw, hvw, hR⟩ := Finset.card_eq_three.mp hr3
    obtain ⟨a, b, c, hab, hbc, hsort⟩ := sort3 huv huw hvw
    have hRabc : Q.erase 0 = {a, b, c} := hR.trans hsort
    have ha0 : a ≠ 0 := fun h => h0n (by rw [hRabc, h]; simp)
    have ha : (0 : Fin 13) < a := Nat.pos_of_ne_zero (fun h => ha0 (Fin.ext h))
    have hQeq : Q = {0, a, b, c} := by rw [← hQins, hRabc]
    subst hQeq
    have harc4 : arc4 a b c = true := by
      unfold arc4
      rw [List.all_eq_true]
      intro l _
      rw [decide_eq_true_eq, ← card_filter_quad ha hab hbc l]
      exact harc l
    obtain ⟨hmem, hok⟩ := check4 a b c ha hab hbc harc4
    refine ⟨(wit4 a b c).1, hmem, (wit4 a b c).2, ?_, ?_⟩
    · unfold ok4 at hok
      rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hok
      intro p
      have hp := hok.1 p (List.mem_finRange p)
      rw [beq_iff_eq] at hp
      rw [hp]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]
      tauto
    · unfold ok4 at hok
      rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hok
      intro l
      have hl := hok.2 l (List.mem_finRange l)
      rw [beq_iff_eq] at hl
      rw [hl]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ p hp
        rcases hp with rfl | rfl | rfl | rfl
        · intro hd; exact absurd ((inD_iff _).mpr hd) (by rw [h1]; decide)
        · intro hd; exact absurd ((inD_iff _).mpr hd) (by rw [h2]; decide)
        · intro hd; exact absurd ((inD_iff _).mpr hd) (by rw [h3]; decide)
        · intro hd; exact absurd ((inD_iff _).mpr hd) (by rw [h4]; decide)
      · intro h
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
        · cases hd : inD (0 - l)
          · rfl
          · exact absurd ((inD_iff _).mp hd) (h 0 (Or.inl rfl))
        · cases hd : inD (a - l)
          · rfl
          · exact absurd ((inD_iff _).mp hd) (h a (Or.inr (Or.inl rfl)))
        · cases hd : inD (b - l)
          · rfl
          · exact absurd ((inD_iff _).mp hd) (h b (Or.inr (Or.inr (Or.inl rfl))))
        · cases hd : inD (c - l)
          · rfl
          · exact absurd ((inD_iff _).mp hd) (h c (Or.inr (Or.inr (Or.inr rfl))))

theorem main_proof :
    ∀ Q : Finset (Fin 13), (Q.card = 3 ∨ Q.card = 4) →
      (∀ l : Fin 13, (Q.filter (fun i => i - l ∈ D)).card ≤ 2) →
      ∃ k ∈ masks, ∃ t : Fin 13,
        (∀ p : Fin 13, k.testBit (p - t).val = decide (p ∈ Q)) ∧
        ∀ l : Fin 13, k.testBit (13 + (l - t).val) = decide (∀ p ∈ Q, p - l ∉ D) := by
  intro Q hcard harc
  have hne : Q.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p0, hp0⟩ := hne
  let f : Fin 13 → Fin 13 := fun x => x - p0
  have hf : Function.Injective f := fun x y h => sub_left_inj.mp h
  let Q' : Finset (Fin 13) := Q.image f
  have h0 : (0 : Fin 13) ∈ Q' := Finset.mem_image.mpr ⟨p0, hp0, sub_self p0⟩
  have hcard' : Q'.card = 3 ∨ Q'.card = 4 := by
    rw [Finset.card_image_of_injective Q hf]
    exact hcard
  have hmem' : ∀ p : Fin 13, p - p0 ∈ Q' ↔ p ∈ Q := by
    intro p
    constructor
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨x, hx, hxp⟩
      have hxpeq : x = p := hf hxp
      rwa [← hxpeq]
    · intro hp
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have harc' : ∀ l : Fin 13, (Q'.filter (fun i => i - l ∈ D)).card ≤ 2 := by
    intro l
    have heq : Q'.filter (fun i => i - l ∈ D) = (Q.filter (fun i => i - (l + p0) ∈ D)).image f := by
      ext y
      simp only [Q', Finset.mem_filter, Finset.mem_image, f]
      constructor
      · rintro ⟨⟨x, hx, rfl⟩, hy⟩
        refine ⟨x, ⟨hx, ?_⟩, rfl⟩
        have hsub : x - (l + p0) = x - p0 - l := by abel
        rwa [hsub]
      · rintro ⟨x, ⟨hx, hxd⟩, rfl⟩
        refine ⟨⟨x, hx, rfl⟩, ?_⟩
        have hsub : x - p0 - l = x - (l + p0) := by abel
        rwa [hsub]
    rw [heq, Finset.card_image_of_injective _ hf]
    exact harc (l + p0)
  obtain ⟨k, hk, t', hp', hl'⟩ := locate_zero Q' h0 hcard' harc'
  refine ⟨k, hk, t' + p0, ?_, ?_⟩
  · intro p
    have hsub : p - (t' + p0) = (p - p0) - t' := by abel
    rw [hsub, hp' (p - p0)]
    exact decide_eq_decide.mpr (hmem' p)
  · intro l
    have hsub : l - (t' + p0) = (l - p0) - t' := by abel
    rw [hsub, hl' (l - p0)]
    apply decide_eq_decide.mpr
    constructor
    · intro h p hp
      have hsub2 : p - l = (p - p0) - (l - p0) := by abel
      rw [hsub2]
      exact h (p - p0) ((hmem' p).mpr hp)
    · intro h p' hp'
      rcases Finset.mem_image.mp hp' with ⟨p, hp, rfl⟩
      have hsub2 : p - p0 - (l - p0) = p - l := by abel
      rw [hsub2]
      exact h p hp

end PEqualNP.Outside.L_meta_18637_aux

theorem PEqualNP.Outside.L_meta_18637 : (have x1 : List ℕ :=   have x1 : List ℕ :=     have x1 : List ℕ :=       have x1 : List ℕ := [(21496089 : ℕ), (17318185 : ℕ), (20988233 : ℕ), (21004625 : ℕ), (17891877 : ℕ)];       (6308041 : ℕ) :: (21512457 : ℕ) :: (21528849 : ℕ) :: (4751635 : ℕ) :: x1;     have x2 : List ℕ := (6619269 : ℕ) :: (6357127 : ℕ) :: (6570121 : ℕ) :: (6553741 : ℕ) :: (6324419 : ℕ) :: x1;     (19939425 : ℕ) :: (19923045 : ℕ) :: (18890857 : ℕ) :: (6389891 : ℕ) :: x2;   have x2 : List ℕ :=     have x2 : List ℕ := (23085129 : ℕ) :: (23068749 : ℕ) :: (22052945 : ℕ) :: (5275731 : ℕ) :: (22020181 : ℕ) :: x1;     (19415081 : ℕ) :: (7372867 : ℕ) :: (24117317 : ℕ) :: (7340103 : ℕ) :: x2;   have x3 : List ℕ := (21757977 : ℕ) :: (21233693 : ℕ) :: (3735587 : ℕ) :: (19988517 : ℕ) :: (3211303 : ℕ) :: x2;   (7405575 : ℕ) :: (23330829 : ℕ) :: (5799955 : ℕ) :: (22282261 : ℕ) :: x3; have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (3 : ℕ) ∨ x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x2}.card ≤ (2 : ℕ)) → ∃ x6 ∈ x1, ∃ (x7 : Fin (13 : ℕ)), (∀ (x8 : Fin (13 : ℕ)), x6.testBit ↑(x8 - x7) = Decidable.decide (x8 ∈ x3)) ∧ ∀ (x8 : Fin (13 : ℕ)), x6.testBit ((13 : ℕ) + ↑(x8 - x7)) = Decidable.decide (∀ x9 ∈ x3, x9 - x8 ∉ x2)) := by
  exact PEqualNP.Outside.L_meta_18637_aux.main_proof
