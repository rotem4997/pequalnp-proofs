import PEqualNP.Defs

set_option maxRecDepth 32000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_6987_419
  (single_top :
    ∀ (L : List (ℕ × ℕ)),
      17 ≤ L.length → L.length ≤ 49 →
      (∀ p ∈ L, p.1 &&& p.2 ≠ p.1 ∧ p.2 &&& p.1 ≠ p.2 ∧ (p.1 ||| p.2) < 4503599627370495) →
      ∀ (a b : ℕ), a < 4503599627370495 → b < 4503599627370495 → (a ||| b) = 4503599627370495 →
      ∃ pm : ℕ, pm < 8192 ∧
        3 ≤ ((List.range 13).filter (fun p => pm.testBit p)).length ∧
        (∀ l < 13, ([l, (l + 1) % 13, (l + 3) % 13, (l + 9) % 13].filter (fun p => pm.testBit p)).length ≤ 2) ∧
        let R := L.foldl
          (fun (R : List ℕ) (p : ℕ × ℕ) =>
            if R.any (fun r => (p.1 &&& r) == p.1) && R.any (fun r => (p.2 &&& r) == p.2)
            then (p.1 ||| p.2) :: R else R)
          (((List.range 13).filter (fun p => !pm.testBit p)).map (fun p =>
              (1 <<< (4 * p)) ||| (1 <<< (4 * ((p + 12) % 13) + 1)) |||
              (1 <<< (4 * ((p + 10) % 13) + 2)) ||| (1 <<< (4 * ((p + 4) % 13) + 3))) ++
            ((List.range 13).filter (fun l =>
              pm.testBit l || pm.testBit ((l + 1) % 13) ||
              pm.testBit ((l + 3) % 13) || pm.testBit ((l + 9) % 13))).map (fun l => 15 <<< (4 * l)))
        ¬(R.any (fun r => (a &&& r) == a) = true ∧ R.any (fun r => (b &&& r) == b) = true))
  (multi_top :
    ∀ (L : List (ℕ × ℕ)),
      18 ≤ L.length → L.length ≤ 50 →
      (∀ p ∈ L, p.1 < 4503599627370496 ∧ p.2 < 4503599627370496 ∧
        p.1 &&& p.2 ≠ p.1 ∧ p.2 &&& p.1 ≠ p.2) →
      2 ≤ (L.filter (fun p => (p.1 ||| p.2) == 4503599627370495)).length →
      ∃ pm : ℕ, pm < 8192 ∧
        3 ≤ ((List.range 13).filter (fun p => pm.testBit p)).length ∧
        (∀ l < 13, ([l, (l + 1) % 13, (l + 3) % 13, (l + 9) % 13].filter (fun p => pm.testBit p)).length ≤ 2) ∧
        let R := L.foldl
          (fun (R : List ℕ) (p : ℕ × ℕ) =>
            if R.any (fun r => (p.1 &&& r) == p.1) && R.any (fun r => (p.2 &&& r) == p.2)
            then (p.1 ||| p.2) :: R else R)
          (((List.range 13).filter (fun p => !pm.testBit p)).map (fun p =>
              (1 <<< (4 * p)) ||| (1 <<< (4 * ((p + 12) % 13) + 1)) |||
              (1 <<< (4 * ((p + 10) % 13) + 2)) ||| (1 <<< (4 * ((p + 4) % 13) + 3))) ++
            ((List.range 13).filter (fun l =>
              pm.testBit l || pm.testBit ((l + 1) % 13) ||
              pm.testBit ((l + 3) % 13) || pm.testBit ((l + 9) % 13))).map (fun l => 15 <<< (4 * l)))
        4503599627370495 ∉ R) :
∀ (x1 : List (Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) × Finset (Fin (13 : ℕ) × Fin (4 : ℕ)))),   x1.length ≤ (50 : ℕ) →     ∃ (x3 : Fin (16 : ℕ)) (x4 : Fin (13 : ℕ)) (x5 : Fin (3 : ℕ)),       have x6 : Fin (13 : ℕ) × Fin (4 : ℕ) → Fin (26 : ℕ) → Bool := fun (x6 : Fin (13 : ℕ) × Fin (4 : ℕ)) (x7 : Fin (26 : ℕ)) => Decidable.decide (x7 = Fin.castAdd (13 : ℕ) (x6.1 + [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].getD ↑x6.2 (0 : Fin (13 : ℕ))) ∨ x7 = Fin.natAdd (13 : ℕ) x6.1);       let x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x7 x8 : Fin (13 : ℕ)) => x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ));       have x8 : Finset (Fin (13 : ℕ)) := {x8 : Fin (13 : ℕ) | ([(4544 : ℕ), (2464 : ℕ), (6464 : ℕ), (5440 : ℕ), (4416 : ℕ), (3332 : ℕ), (5264 : ℕ), (3204 : ℕ), (3076 : ℕ), (2336 : ℕ), (6400 : ℕ), (5376 : ℕ), (5136 : ℕ), (6164 : ℕ), (6148 : ℕ), (6160 : ℕ)].getD ↑x3 (0 : ℕ)).testBit ↑((x8 - x4) * [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].getD ↑x5 (0 : Fin (13 : ℕ))) = Bool.true};       have x9 : Fin (26 : ℕ) → Bool := fun (x9 : Fin (26 : ℕ)) => Decidable.decide ((∃ x10 ∈ x8, x9 = Fin.castAdd (13 : ℕ) x10) ∨ ∃ (x10 : Fin (13 : ℕ)), x9 = Fin.natAdd (13 : ℕ) x10 ∧ ∀ x11 ∈ x8, ¬x7 x11 x10);       ¬List.foldl (fun (x10 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) → Prop) (x11 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) × Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) (x12 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) => x10 x12 ∨ x12 ⊆ x11.1 ∪ x11.2 ∧ x10 x11.1 ∧ x10 x11.2) (fun (x10 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) => x10 = ∅ ∨ ∃ (x11 : Fin (26 : ℕ)), x9 x11 = Bool.false ∧ ∀ x12 ∈ x10, x6 x12 x11 = Bool.true) x1 Finset.univ := by
  classical
  intro x1 hx1
  let E := Fin 13 × Fin 4
  let full : ℕ := 4503599627370495
  let bound : ℕ := 4503599627370496
  let idx : E → ℕ := fun e => 4 * e.1.val + e.2.val
  let allE : List E :=
    (List.finRange 13).flatMap (fun l => (List.finRange 4).map (fun j => (l, j)))
  let enc : Finset E → ℕ := fun S =>
    allE.foldl (fun acc e => if e ∈ S then acc ||| (1 <<< idx e) else acc) 0
  let ptStar : ℕ → ℕ := fun p =>
    (1 <<< (4 * p)) ||| (1 <<< (4 * ((p + 12) % 13) + 1)) |||
    (1 <<< (4 * ((p + 10) % 13) + 2)) ||| (1 <<< (4 * ((p + 4) % 13) + 3))
  let lineStar : ℕ → ℕ := fun l => 15 <<< (4 * l)
  let initMasks : ℕ → List ℕ := fun pm =>
    ((List.range 13).filter (fun p => !pm.testBit p)).map ptStar ++
    ((List.range 13).filter (fun l =>
      pm.testBit l || pm.testBit ((l + 1) % 13) ||
      pm.testBit ((l + 3) % 13) || pm.testBit ((l + 9) % 13))).map lineStar
  let stepBM : List ℕ → ℕ × ℕ → List ℕ := fun R p =>
    if R.any (fun r => (p.1 &&& r) == p.1) && R.any (fun r => (p.2 &&& r) == p.2)
    then (p.1 ||| p.2) :: R else R
  let masks : List ℕ := [4544, 2464, 6464, 5440, 4416, 3332, 5264, 3204, 3076, 2336, 6400, 5376, 5136, 6164, 6148, 6160]
  let mults : List (Fin 13) := [1, 3, 9]
  let multsN : List ℕ := [1, 3, 9]
  let isArc : ℕ → Prop := fun pm =>
    pm < 8192 ∧
    3 ≤ ((List.range 13).filter (fun p => pm.testBit p)).length ∧
    ∀ l < 13, ([l, (l + 1) % 13, (l + 3) % 13, (l + 9) % 13].filter (fun p => pm.testBit p)).length ≤ 2
  have idx_lt : ∀ e : E, idx e < 52 := by
    intro e; dsimp [idx]; omega
  have idx_inj : ∀ e1 e2 : E, idx e1 = idx e2 → e1 = e2 := by
    intro e1 e2 h
    dsimp [idx] at h
    apply Prod.ext <;> apply Fin.ext <;> omega
  have mem_allE : ∀ e : E, e ∈ allE := by
    intro e
    dsimp [allE]
    rw [List.mem_flatMap]
    refine ⟨e.1, List.mem_finRange e.1, ?_⟩
    rw [List.mem_map]
    exact ⟨e.2, List.mem_finRange e.2, rfl⟩
  have testBit_one_shiftLeft : ∀ n k : ℕ, (1 <<< n).testBit k = decide (n = k) := by
    intro n k
    rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow]
  have testBit_fold : ∀ (es : List E) (S : Finset E) (init : ℕ) (k : ℕ),
      (es.foldl (fun acc e => if e ∈ S then acc ||| (1 <<< idx e) else acc) init).testBit k =
      (init.testBit k || es.any (fun e => decide (e ∈ S) && decide (idx e = k))) := by
    intro es S
    induction es with
    | nil => intro init k; simp
    | cons e es ih =>
      intro init k
      simp only [List.foldl_cons, List.any_cons]
      rw [ih]
      by_cases he : e ∈ S
      · simp only [he, ite_true, decide_true, Bool.true_and, Nat.testBit_or, testBit_one_shiftLeft]
        rw [Bool.or_assoc]
      · simp only [he, ite_false, decide_false, Bool.false_and, Bool.false_or]
  have testBit_enc : ∀ (S : Finset E) (k : ℕ),
      (enc S).testBit k = true ↔ ∃ e ∈ S, idx e = k := by
    intro S k
    dsimp [enc]
    rw [testBit_fold, Nat.zero_testBit, Bool.false_or, List.any_eq_true]
    constructor
    · rintro ⟨e, _, h⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨e, h.1, h.2⟩
    · rintro ⟨e, he, hk⟩
      refine ⟨e, mem_allE e, ?_⟩
      simp [he, hk]
  have enc_lt : ∀ S : Finset E, enc S < bound := by
    intro S
    have hpow : bound = 2 ^ 52 := by decide
    rw [hpow]
    have step_lt : ∀ (es : List E) (acc : ℕ), acc < 2 ^ 52 →
        es.foldl (fun acc e => if e ∈ S then acc ||| (1 <<< idx e) else acc) acc < 2 ^ 52 := by
      intro es
      induction es with
      | nil => intro acc h; exact h
      | cons e es ih =>
        intro acc h
        simp only [List.foldl_cons]
        apply ih
        split_ifs
        · rw [Nat.shiftLeft_eq, one_mul]
          exact Nat.or_lt_two_pow h (Nat.pow_lt_pow_right (by omega) (idx_lt e))
        · exact h
    exact step_lt allE 0 (by decide)
  have enc_empty : enc ∅ = 0 := by
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.zero_testBit]
    cases h : (enc ∅).testBit k
    · rfl
    · obtain ⟨e, he, _⟩ := (testBit_enc ∅ k).mp h
      exact absurd he (Finset.notMem_empty e)
  have enc_univ : enc Finset.univ = full := by
    apply Nat.eq_of_testBit_eq
    intro k
    have hfull : ∀ j, full.testBit j = decide (j < 52) := by
      intro j
      have hf : full = 2 ^ 52 - 1 := by decide
      rw [hf, Nat.testBit_two_pow_sub_one]
    rw [hfull]
    by_cases hk : k < 52
    · simp only [hk, decide_true]
      rw [testBit_enc]
      refine ⟨(⟨k / 4, by omega⟩, ⟨k % 4, by omega⟩), Finset.mem_univ _, ?_⟩
      dsimp [idx]; omega
    · simp only [hk, decide_false]
      cases h : (enc Finset.univ).testBit k
      · rfl
      · obtain ⟨e, _, he⟩ := (testBit_enc Finset.univ k).mp h
        have := idx_lt e; omega
  have enc_union : ∀ A B : Finset E, enc (A ∪ B) = enc A ||| enc B := by
    intro A B
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_or]
    cases h : (enc (A ∪ B)).testBit k
    · symm
      rw [Bool.or_eq_false_iff]
      constructor
      · cases ha : (enc A).testBit k
        · rfl
        · obtain ⟨e, he, hk⟩ := (testBit_enc A k).mp ha
          have hu := (testBit_enc (A ∪ B) k).mpr ⟨e, Finset.mem_union_left B he, hk⟩
          rw [h] at hu; cases hu
      · cases hb : (enc B).testBit k
        · rfl
        · obtain ⟨e, he, hk⟩ := (testBit_enc B k).mp hb
          have hu := (testBit_enc (A ∪ B) k).mpr ⟨e, Finset.mem_union_right A he, hk⟩
          rw [h] at hu; cases hu
    · symm
      rw [Bool.or_eq_true]
      obtain ⟨e, he, hk⟩ := (testBit_enc (A ∪ B) k).mp h
      rcases Finset.mem_union.mp he with hA | hB
      · exact Or.inl ((testBit_enc A k).mpr ⟨e, hA, hk⟩)
      · exact Or.inr ((testBit_enc B k).mpr ⟨e, hB, hk⟩)
  have enc_subset_iff : ∀ A B : Finset E, A ⊆ B ↔ (enc A &&& enc B) = enc A := by
    intro A B
    constructor
    · intro hAB
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_and]
      cases ha : (enc A).testBit k
      · simp
      · obtain ⟨e, he, hk⟩ := (testBit_enc A k).mp ha
        have hb := (testBit_enc B k).mpr ⟨e, hAB he, hk⟩
        simp [hb]
    · intro h e he
      have ha : (enc A).testBit (idx e) = true := (testBit_enc A (idx e)).mpr ⟨e, he, rfl⟩
      have h1 : ((enc A &&& enc B).testBit (idx e)) = (enc A).testBit (idx e) := congrArg (fun n => n.testBit (idx e)) h
      rw [Nat.testBit_and, ha, Bool.true_and] at h1
      obtain ⟨e', he', hi⟩ := (testBit_enc B (idx e)).mp h1
      rw [idx_inj e' e hi] at he'
      exact he'
  have full_and_lt : ∀ r : ℕ, r < bound → ((full &&& r) = full ↔ r = full) := by
    intro r hr
    have hpow : bound = 2 ^ 52 := by decide
    have hf : full = 2 ^ 52 - 1 := by decide
    have hand : full &&& r = r := by
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_and, hf, Nat.testBit_two_pow_sub_one]
      by_cases hk : k < 52
      · simp [hk]
      · simp only [hk, decide_false, Bool.false_and]
        symm
        rw [Nat.testBit_eq_false_of_lt]
        have hlt : 2 ^ 52 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
        omega
    rw [hand]
  have ptStar_lt : ∀ p < 13, ptStar p < full := by
    intro p hp
    have hf : full = 2 ^ 52 - 1 := by decide
    have hlt : ptStar p < 2 ^ 52 := by
      dsimp [ptStar]
      simp only [Nat.shiftLeft_eq, one_mul]
      refine @Nat.or_lt_two_pow _ _ 52 (@Nat.or_lt_two_pow _ _ 52 (@Nat.or_lt_two_pow _ _ 52 ?_ ?_) ?_) ?_
      · exact Nat.pow_lt_pow_right (by omega) (by omega)
      · exact Nat.pow_lt_pow_right (by omega) (by omega)
      · exact Nat.pow_lt_pow_right (by omega) (by omega)
      · exact Nat.pow_lt_pow_right (by omega) (by omega)
    have hne : ptStar p ≠ full := by
      intro heq
      have hb := congrArg (fun n => n.testBit (4 * ((p + 1) % 13))) heq
      rw [hf, Nat.testBit_two_pow_sub_one] at hb
      dsimp [ptStar] at hb
      simp only [Nat.testBit_or, testBit_one_shiftLeft] at hb
      have h1 : 4 * p ≠ 4 * ((p + 1) % 13) := by omega
      have h2 : 4 * ((p + 12) % 13) + 1 ≠ 4 * ((p + 1) % 13) := by omega
      have h3 : 4 * ((p + 10) % 13) + 2 ≠ 4 * ((p + 1) % 13) := by omega
      have h4 : 4 * ((p + 4) % 13) + 3 ≠ 4 * ((p + 1) % 13) := by omega
      have hlt52 : 4 * ((p + 1) % 13) < 52 := by omega
      simp [h1, h2, h3, h4, hlt52] at hb
    omega
  have lineStar_lt : ∀ l < 13, lineStar l < full := by
    intro l hl
    have hf : full = 2 ^ 52 - 1 := by decide
    have hlt : lineStar l < 2 ^ 52 := by
      dsimp [lineStar]
      rw [Nat.shiftLeft_eq]
      have h1 : 15 < 2 ^ 4 := by decide
      calc 15 * 2 ^ (4 * l) < 2 ^ 4 * 2 ^ (4 * l) :=
            Nat.mul_lt_mul_of_pos_right h1 (Nat.pow_pos (by omega))
        _ = 2 ^ (4 + 4 * l) := (Nat.pow_add 2 4 (4 * l)).symm
        _ ≤ 2 ^ 52 := Nat.pow_le_pow_right (by omega) (by omega)
    have hne : lineStar l ≠ full := by
      intro heq
      have hb := congrArg (fun n => n.testBit (4 * ((l + 1) % 13))) heq
      rw [hf, Nat.testBit_two_pow_sub_one] at hb
      dsimp [lineStar] at hb
      rw [Nat.testBit_shiftLeft] at hb
      have hlt52 : 4 * ((l + 1) % 13) < 52 := by omega
      simp only [hlt52, decide_true] at hb
      by_cases hge : 4 * l ≤ 4 * ((l + 1) % 13)
      · rw [decide_eq_true hge, Bool.true_and] at hb
        have hsub : 4 * ((l + 1) % 13) - 4 * l = 4 := by omega
        rw [hsub] at hb; cases hb
      · rw [decide_eq_false hge, Bool.false_and] at hb
        cases hb
    omega
  have initMasks_lt : ∀ pm r, r ∈ initMasks pm → r < full := by
    intro pm r hr
    dsimp [initMasks] at hr
    rw [List.mem_append] at hr
    rcases hr with hp | hl
    · rw [List.mem_map] at hp
      obtain ⟨p, hp, rfl⟩ := hp
      rw [List.mem_filter, List.mem_range] at hp
      exact ptStar_lt p hp.1
    · rw [List.mem_map] at hl
      obtain ⟨l, hl, rfl⟩ := hl
      rw [List.mem_filter, List.mem_range] at hl
      exact lineStar_lt l hl.1
  have stepBM_lt : ∀ (L : List (ℕ × ℕ)) (R : List ℕ),
      (∀ p ∈ L, p.1 < bound ∧ p.2 < bound) →
      (∀ r ∈ R, r < bound) →
      ∀ r ∈ L.foldl stepBM R, r < bound := by
    intro L
    induction L with
    | nil => intro R _ hR r hr; exact hR r hr
    | cons p L ih =>
      intro R hL hR r hr
      simp only [List.foldl_cons] at hr
      apply ih (stepBM R p) (fun q hq => hL q (List.mem_cons_of_mem p hq)) _ r hr
      intro s hs
      dsimp [stepBM] at hs
      split_ifs at hs
      · rw [List.mem_cons] at hs
        rcases hs with rfl | hs
        · have hp := hL p (List.mem_cons_self ..)
          have hpow : bound = 2 ^ 52 := by decide
          rw [hpow] at hp ⊢
          exact Nat.or_lt_two_pow hp.1 hp.2
        · exact hR s hs
      · exact hR s hs
  have stepBM_no_full : ∀ (L : List (ℕ × ℕ)) (R : List ℕ),
      (∀ p ∈ L, (p.1 ||| p.2) ≠ full) →
      full ∉ R →
      full ∉ L.foldl stepBM R := by
    intro L
    induction L with
    | nil => intro R _ hR; exact hR
    | cons p L ih =>
      intro R hL hR
      simp only [List.foldl_cons]
      apply ih (stepBM R p) (fun q hq => hL q (List.mem_cons_of_mem p hq))
      dsimp [stepBM]
      split_ifs
      · rw [List.mem_cons]; push Not
        exact ⟨Ne.symm (hL p (List.mem_cons_self ..)), hR⟩
      · exact hR
  let X : E → Fin 26 → Bool := fun e v =>
    decide (v = Fin.castAdd 13 (e.1 + ([0, 1, 3, 9] : List (Fin 13)).getD e.2.val 0) ∨
      v = Fin.natAdd 13 e.1)
  have ptStar_bit : ∀ (p : Fin 13) (e : E),
      (ptStar p.val).testBit (idx e) = X e (Fin.castAdd 13 p) := by
    intro p e
    rcases e with ⟨l, j⟩
    dsimp [ptStar, idx, X]
    simp only [Nat.testBit_or, testBit_one_shiftLeft]
    have hno2 : ¬(Fin.castAdd 13 p = Fin.natAdd 13 l) := by
      intro h; have h1 := congrArg Fin.val h; simp [Fin.val_castAdd] at h1; omega
    have hcast : ∀ q : Fin 13, (Fin.castAdd 13 p = Fin.castAdd 13 q) ↔ p.val = q.val := by
      intro q; constructor
      · intro h; exact congrArg Fin.val (Fin.castAdd_injective 13 _ h)
      · intro h; exact congrArg (Fin.castAdd 13) (Fin.ext h)
    have hp := p.isLt; have hl := l.isLt
    fin_cases j
    · simp only [List.getD_cons_zero, add_zero, hno2, or_false, hcast]
      have h2 : 4 * ((p.val + 12) % 13) + 1 ≠ 4 * l.val := by omega
      have h3 : 4 * ((p.val + 10) % 13) + 2 ≠ 4 * l.val := by omega
      have h4 : 4 * ((p.val + 4) % 13) + 3 ≠ 4 * l.val := by omega
      simp only [h2, h3, h4, decide_false, Bool.or_false]
      by_cases h : p.val = l.val
      · simp [h]
      · simp [h]
    · simp only [Fin.val_one, List.getD_cons_succ, List.getD_cons_zero, hno2, or_false, hcast, Fin.val_add]
      have h1 : 4 * p.val ≠ 4 * l.val + 1 := by omega
      have h3 : 4 * ((p.val + 10) % 13) + 2 ≠ 4 * l.val + 1 := by omega
      have h4 : 4 * ((p.val + 4) % 13) + 3 ≠ 4 * l.val + 1 := by omega
      simp only [h1, h3, h4, decide_false, Bool.false_or, Bool.or_false]
      by_cases h : p.val = (l.val + 1) % 13
      · simp [h]; omega
      · simp [h]; omega
    · simp only [List.getD_cons_succ, List.getD_cons_zero, hno2, or_false, hcast, Fin.val_add]
      have h1 : 4 * p.val ≠ 4 * l.val + 2 := by omega
      have h2 : 4 * ((p.val + 12) % 13) + 1 ≠ 4 * l.val + 2 := by omega
      have h4 : 4 * ((p.val + 4) % 13) + 3 ≠ 4 * l.val + 2 := by omega
      simp only [h1, h2, h4, decide_false, Bool.false_or, Bool.or_false]
      change decide (4 * ((p.val + 10) % 13) + 2 = 4 * l.val + 2) = decide (p.val = (l.val + 3) % 13)
      by_cases h : p.val = (l.val + 3) % 13
      · simp [h]; omega
      · simp [h]; omega
    · simp only [List.getD_cons_succ, List.getD_cons_zero, hno2, or_false, hcast, Fin.val_add]
      change (decide (4 * p.val = 4 * l.val + 3) || decide (4 * ((p.val + 12) % 13) + 1 = 4 * l.val + 3) ||
        decide (4 * ((p.val + 10) % 13) + 2 = 4 * l.val + 3) ||
        decide (4 * ((p.val + 4) % 13) + 3 = 4 * l.val + 3)) = decide (p.val = (l.val + 9) % 13)
      have h1 : 4 * p.val ≠ 4 * l.val + 3 := by omega
      have h2 : 4 * ((p.val + 12) % 13) + 1 ≠ 4 * l.val + 3 := by omega
      have h3 : 4 * ((p.val + 10) % 13) + 2 ≠ 4 * l.val + 3 := by omega
      simp only [h1, h2, h3, decide_false, Bool.false_or]
      by_cases h : p.val = (l.val + 9) % 13
      · simp [h]; omega
      · simp [h]; omega
  have lineStar_bit : ∀ (l : Fin 13) (e : E),
      (lineStar l.val).testBit (idx e) = X e (Fin.natAdd 13 l) := by
    intro l e
    rcases e with ⟨l', j⟩
    dsimp [lineStar, idx, X]
    rw [Nat.testBit_shiftLeft]
    have hno1 : ¬(Fin.natAdd 13 l = Fin.castAdd 13 (l' + ([0, 1, 3, 9] : List (Fin 13)).getD j.val 0)) := by
      intro h; have h1 := congrArg Fin.val h; simp [Fin.val_castAdd] at h1; omega
    have hnat : (Fin.natAdd 13 l = Fin.natAdd 13 l') ↔ l.val = l'.val := by
      constructor
      · intro h; exact congrArg Fin.val (Fin.natAdd_injective 13 _ h)
      · intro h; exact congrArg (Fin.natAdd 13) (Fin.ext h)
    simp only [hno1, false_or, hnat]
    have hl := l.isLt; have hl' := l'.isLt; have hj := j.isLt
    by_cases heq : l.val = l'.val
    · rw [heq]; simp only [decide_true]
      have hge : 4 * l'.val ≤ 4 * l'.val + j.val := by omega
      have hsub : 4 * l'.val + j.val - 4 * l'.val = j.val := by omega
      rw [decide_eq_true hge, Bool.true_and, hsub]
      fin_cases j <;> rfl
    · simp only [heq, decide_false]
      by_cases hge : 4 * l.val ≤ 4 * l'.val + j.val
      · rw [decide_eq_true hge, Bool.true_and]
        have h4 : 4 ≤ 4 * l'.val + j.val - 4 * l.val := by omega
        rw [Nat.testBit_eq_false_of_lt]
        have : 16 ≤ 2 ^ (4 * l'.val + j.val - 4 * l.val) :=
          le_trans (by decide : 16 ≤ 2 ^ 4) (Nat.pow_le_pow_right (by omega) h4)
        omega
      · rw [decide_eq_false hge, Bool.false_and]
  have ptStar_sub_iff : ∀ (p : Fin 13) (S : Finset E),
      ((enc S &&& ptStar p.val) = enc S) ↔ (∀ e ∈ S, X e (Fin.castAdd 13 p) = true) := by
    intro p S
    constructor
    · intro h e he
      have ha : (enc S).testBit (idx e) = true := (testBit_enc S (idx e)).mpr ⟨e, he, rfl⟩
      have h1 : (enc S &&& ptStar p.val).testBit (idx e) = (enc S).testBit (idx e) :=
        congrArg (fun n => n.testBit (idx e)) h
      rw [Nat.testBit_and, ha, Bool.true_and, ptStar_bit] at h1
      exact h1
    · intro h
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_and]
      cases ha : (enc S).testBit k
      · simp
      · obtain ⟨e, he, rfl⟩ := (testBit_enc S k).mp ha
        rw [ptStar_bit, h e he, Bool.true_and]
  have lineStar_sub_iff : ∀ (l : Fin 13) (S : Finset E),
      ((enc S &&& lineStar l.val) = enc S) ↔ (∀ e ∈ S, X e (Fin.natAdd 13 l) = true) := by
    intro l S
    constructor
    · intro h e he
      have ha : (enc S).testBit (idx e) = true := (testBit_enc S (idx e)).mpr ⟨e, he, rfl⟩
      have h1 : (enc S &&& lineStar l.val).testBit (idx e) = (enc S).testBit (idx e) :=
        congrArg (fun n => n.testBit (idx e)) h
      rw [Nat.testBit_and, ha, Bool.true_and, lineStar_bit] at h1
      exact h1
    · intro h
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_and]
      cases ha : (enc S).testBit k
      · simp
      · obtain ⟨e, he, rfl⟩ := (testBit_enc S k).mp ha
        rw [lineStar_bit, h e he, Bool.true_and]
  let st : (Finset E → Prop) → Finset E × Finset E → Finset E → Prop :=
    fun D p S => D S ∨ S ⊆ p.1 ∪ p.2 ∧ D p.1 ∧ D p.2
  let prune : List (ℕ × ℕ) → List (ℕ × ℕ) := fun L =>
    L.filter (fun p => decide (p.1 &&& p.2 ≠ p.1 ∧ p.2 &&& p.1 ≠ p.2))
  have foldl_equiv : ∀ (xs : List (Finset E × Finset E)) (D : Finset E → Prop) (R : List ℕ),
      (∀ S : Finset E, D S ↔ S = ∅ ∨ R.any (fun r => (enc S &&& r) == enc S) = true) →
      ∀ S : Finset E,
        xs.foldl st D S ↔
        S = ∅ ∨ ((prune (xs.map (fun p => (enc p.1, enc p.2)))).foldl stepBM R).any
          (fun r => (enc S &&& r) == enc S) = true := by
    intro xs
    induction xs with
    | nil =>
      intro D R hDR S
      exact hDR S
    | cons p xs ih =>
      intro D R hDR S
      simp only [List.foldl_cons, List.map_cons, prune, List.filter_cons]
      have hdown : ∀ A B : Finset E, A ⊆ B → D B → D A := by
        intro A B hAB hDB
        rw [hDR] at hDB ⊢
        rcases hDB with rfl | hR
        · exact Or.inl (Finset.subset_empty.mp hAB)
        · right
          rw [List.any_eq_true] at hR ⊢
          obtain ⟨r, hr, hBr⟩ := hR
          refine ⟨r, hr, ?_⟩
          simp only [beq_iff_eq] at hBr ⊢
          have hsub := (enc_subset_iff A B).mp hAB
          calc enc A &&& r = (enc A &&& enc B) &&& r := by rw [hsub]
            _ = enc A &&& (enc B &&& r) := Nat.and_assoc ..
            _ = enc A &&& enc B := by rw [hBr]
            _ = enc A := hsub
      by_cases hkeep : enc p.1 &&& enc p.2 ≠ enc p.1 ∧ enc p.2 &&& enc p.1 ≠ enc p.2
      · have hdec : decide (enc p.1 &&& enc p.2 ≠ enc p.1 ∧ enc p.2 &&& enc p.1 ≠ enc p.2) = true :=
          decide_eq_true hkeep
        simp only [hdec, ite_true, List.foldl_cons]
        apply ih (st D p) (stepBM R (enc p.1, enc p.2))
        intro T
        have hp1ne : p.1 ≠ ∅ := by
          intro h0; apply hkeep.1; rw [h0, enc_empty, Nat.zero_and]
        have hp2ne : p.2 ≠ ∅ := by
          intro h0; apply hkeep.2; rw [h0, enc_empty, Nat.zero_and]
        have hDp1 : D p.1 ↔ R.any (fun r => (enc p.1 &&& r) == enc p.1) = true :=
          (hDR p.1).trans (or_iff_right hp1ne)
        have hDp2 : D p.2 ↔ R.any (fun r => (enc p.2 &&& r) == enc p.2) = true :=
          (hDR p.2).trans (or_iff_right hp2ne)
        dsimp [st, stepBM]
        by_cases hfire : R.any (fun r => (enc p.1 &&& r) == enc p.1) = true ∧
            R.any (fun r => (enc p.2 &&& r) == enc p.2) = true
        · have hb : (R.any (fun r => (enc p.1 &&& r) == enc p.1) &&
              R.any (fun r => (enc p.2 &&& r) == enc p.2)) = true := by
            simp [hfire.1, hfire.2]
          rw [if_pos hb]
          rw [List.any_cons, Bool.or_eq_true, hDR T, hDp1, hDp2]
          simp only [hfire.1, hfire.2, and_self, and_true, beq_iff_eq, ← enc_union, ← enc_subset_iff]
          tauto
        · have hb : ¬((R.any (fun r => (enc p.1 &&& r) == enc p.1) &&
              R.any (fun r => (enc p.2 &&& r) == enc p.2)) = true) := by
            rw [Bool.and_eq_true]; exact hfire
          rw [if_neg hb]
          rw [hDR T, hDp1, hDp2]
          constructor
          · rintro (h | ⟨_, h1, h2⟩)
            · exact h
            · exact absurd ⟨h1, h2⟩ hfire
          · intro h; exact Or.inl h
      · simp only [hkeep, decide_false]
        apply ih (st D p) R
        intro T
        rw [← hDR T]
        dsimp [st]
        constructor
        · rintro (h | ⟨hsub, h1, h2⟩)
          · exact h
          · rw [not_and_or, not_not, not_not] at hkeep
            rcases hkeep with h12 | h21
            · have hle : p.1 ⊆ p.2 := (enc_subset_iff p.1 p.2).mpr h12
              exact hdown T p.2 (hsub.trans (Finset.union_subset hle (Finset.Subset.refl p.2))) h2
            · have hle : p.2 ⊆ p.1 := (enc_subset_iff p.2 p.1).mpr h21
              exact hdown T p.1 (hsub.trans (Finset.union_subset (Finset.Subset.refl p.1) hle)) h1
        · intro h; exact Or.inl h
  let mkSM : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℕ := fun a b c d =>
    1 ||| ([0, 2, 8, 512].getD a.val 0) ||| ([0, 4096, 4, 256].getD b.val 0) |||
    ([0, 1024, 2048, 64].getD c.val 0) ||| ([0, 16, 32, 128].getD d.val 0)
  have hmk_lt : ∀ a b c d : Fin 4, mkSM a b c d < 2 ^ 13 := by
    intro a b c d
    dsimp [mkSM]
    refine @Nat.or_lt_two_pow _ _ 13 (@Nat.or_lt_two_pow _ _ 13 (@Nat.or_lt_two_pow _ _ 13 (@Nat.or_lt_two_pow _ _ 13 (by decide) ?_) ?_) ?_) ?_
    · fin_cases a <;> decide
    · fin_cases b <;> decide
    · fin_cases c <;> decide
    · fin_cases d <;> decide
  have hmk_bits : ∀ a b c d : Fin 4,
      (mkSM a b c d).testBit 0 = true ∧
      (mkSM a b c d).testBit 1 = (a.val == 1) ∧
      (mkSM a b c d).testBit 2 = (b.val == 2) ∧
      (mkSM a b c d).testBit 3 = (a.val == 2) ∧
      (mkSM a b c d).testBit 4 = (d.val == 1) ∧
      (mkSM a b c d).testBit 5 = (d.val == 2) ∧
      (mkSM a b c d).testBit 6 = (c.val == 3) ∧
      (mkSM a b c d).testBit 7 = (d.val == 3) ∧
      (mkSM a b c d).testBit 8 = (b.val == 3) ∧
      (mkSM a b c d).testBit 9 = (a.val == 3) ∧
      (mkSM a b c d).testBit 10 = (c.val == 1) ∧
      (mkSM a b c d).testBit 11 = (c.val == 2) ∧
      (mkSM a b c d).testBit 12 = (b.val == 1) := by
    intro a b c d
    dsimp [mkSM]
    simp only [Nat.testBit_or]
    have ha : ∀ k : Fin 4,
        ([0, 2, 8, 512].getD k.val 0).testBit 1 = (k.val == 1) ∧
        ([0, 2, 8, 512].getD k.val 0).testBit 2 = false ∧
        ([0, 2, 8, 512].getD k.val 0).testBit 3 = (k.val == 2) ∧
        ([0, 2, 8, 512].getD k.val 0).testBit 4 = false ∧
        ([0, 2, 8, 512].getD k.val 0).testBit 5 = false ∧
        ([0, 2, 8, 512].getD k.val 0).testBit 6 = false ∧
        ([0, 2, 8, 512].getD k.val 0).testBit 7 = false ∧
        ([0, 2, 8, 512].getD k.val 0).testBit 8 = false ∧
        ([0, 2, 8, 512].getD k.val 0).testBit 9 = (k.val == 3) ∧
        ([0, 2, 8, 512].getD k.val 0).testBit 10 = false ∧
        ([0, 2, 8, 512].getD k.val 0).testBit 11 = false ∧
        ([0, 2, 8, 512].getD k.val 0).testBit 12 = false := by
      intro k; fin_cases k <;> decide
    have hb : ∀ k : Fin 4,
        ([0, 4096, 4, 256].getD k.val 0).testBit 1 = false ∧
        ([0, 4096, 4, 256].getD k.val 0).testBit 2 = (k.val == 2) ∧
        ([0, 4096, 4, 256].getD k.val 0).testBit 3 = false ∧
        ([0, 4096, 4, 256].getD k.val 0).testBit 4 = false ∧
        ([0, 4096, 4, 256].getD k.val 0).testBit 5 = false ∧
        ([0, 4096, 4, 256].getD k.val 0).testBit 6 = false ∧
        ([0, 4096, 4, 256].getD k.val 0).testBit 7 = false ∧
        ([0, 4096, 4, 256].getD k.val 0).testBit 8 = (k.val == 3) ∧
        ([0, 4096, 4, 256].getD k.val 0).testBit 9 = false ∧
        ([0, 4096, 4, 256].getD k.val 0).testBit 10 = false ∧
        ([0, 4096, 4, 256].getD k.val 0).testBit 11 = false ∧
        ([0, 4096, 4, 256].getD k.val 0).testBit 12 = (k.val == 1) := by
      intro k; fin_cases k <;> decide
    have hc : ∀ k : Fin 4,
        ([0, 1024, 2048, 64].getD k.val 0).testBit 1 = false ∧
        ([0, 1024, 2048, 64].getD k.val 0).testBit 2 = false ∧
        ([0, 1024, 2048, 64].getD k.val 0).testBit 3 = false ∧
        ([0, 1024, 2048, 64].getD k.val 0).testBit 4 = false ∧
        ([0, 1024, 2048, 64].getD k.val 0).testBit 5 = false ∧
        ([0, 1024, 2048, 64].getD k.val 0).testBit 6 = (k.val == 3) ∧
        ([0, 1024, 2048, 64].getD k.val 0).testBit 7 = false ∧
        ([0, 1024, 2048, 64].getD k.val 0).testBit 8 = false ∧
        ([0, 1024, 2048, 64].getD k.val 0).testBit 9 = false ∧
        ([0, 1024, 2048, 64].getD k.val 0).testBit 10 = (k.val == 1) ∧
        ([0, 1024, 2048, 64].getD k.val 0).testBit 11 = (k.val == 2) ∧
        ([0, 1024, 2048, 64].getD k.val 0).testBit 12 = false := by
      intro k; fin_cases k <;> decide
    have hd : ∀ k : Fin 4,
        ([0, 16, 32, 128].getD k.val 0).testBit 1 = false ∧
        ([0, 16, 32, 128].getD k.val 0).testBit 2 = false ∧
        ([0, 16, 32, 128].getD k.val 0).testBit 3 = false ∧
        ([0, 16, 32, 128].getD k.val 0).testBit 4 = (k.val == 1) ∧
        ([0, 16, 32, 128].getD k.val 0).testBit 5 = (k.val == 2) ∧
        ([0, 16, 32, 128].getD k.val 0).testBit 6 = false ∧
        ([0, 16, 32, 128].getD k.val 0).testBit 7 = (k.val == 3) ∧
        ([0, 16, 32, 128].getD k.val 0).testBit 8 = false ∧
        ([0, 16, 32, 128].getD k.val 0).testBit 9 = false ∧
        ([0, 16, 32, 128].getD k.val 0).testBit 10 = false ∧
        ([0, 16, 32, 128].getD k.val 0).testBit 11 = false ∧
        ([0, 16, 32, 128].getD k.val 0).testBit 12 = false := by
      intro k; fin_cases k <;> decide
    have ha' := ha a; have hb' := hb b; have hc' := hc c; have hd' := hd d
    simp only [ha', hb', hc', hd', Bool.false_or, Bool.or_false]
    simp only [show (1 : ℕ).testBit 0 = true by decide,
      show (1 : ℕ).testBit 1 = false by decide, show (1 : ℕ).testBit 2 = false by decide,
      show (1 : ℕ).testBit 3 = false by decide, show (1 : ℕ).testBit 4 = false by decide,
      show (1 : ℕ).testBit 5 = false by decide, show (1 : ℕ).testBit 6 = false by decide,
      show (1 : ℕ).testBit 7 = false by decide, show (1 : ℕ).testBit 8 = false by decide,
      show (1 : ℕ).testBit 9 = false by decide, show (1 : ℕ).testBit 10 = false by decide,
      show (1 : ℕ).testBit 11 = false by decide, show (1 : ℕ).testBit 12 = false by decide,
      Bool.true_or, Bool.false_or, and_self]
  let genMaskN : ℕ → ℕ → ℕ → ℕ := fun x3 x4 x5 =>
    (List.range 13).foldl (fun acc p =>
      if (masks.getD x3 0).testBit (((p + 13 - x4) * multsN.getD x5 0) % 13)
      then acc ||| (1 <<< p) else acc) 0
  let arcTbl : List ℕ :=
    [0, 0, 0, 0, 0, 328, 448, 357, 0, 171, 471, 595, 0, 613, 182, 458,
     0, 318, 588, 164, 332, 201, 0, 8, 367, 15, 238, 0, 437, 0, 143, 125,
     0, 444, 190, 477, 596, 0, 151, 243, 438, 132, 0, 245, 177, 138, 99, 0,
     0, 371, 433, 612, 175, 19, 136, 0, 590, 0, 237, 512, 495, 263, 0, 262,
     0, 552, 321, 440, 396, 0, 282, 280, 335, 57, 204, 0, 591, 513, 0, 146,
     370, 58, 18, 0, 293, 0, 0, 0, 0, 0, 0, 0, 241, 0, 0, 0,
     373, 0, 61, 244, 0, 0, 0, 0, 296, 0, 0, 0, 21, 0, 0, 0,
     167, 59, 0, 128, 84, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0,
     0, 405, 605, 337, 366, 289, 252, 0, 184, 93, 0, 28, 375, 0, 26, 298,
     549, 0, 510, 56, 54, 0, 0, 0, 55, 0, 0, 0, 0, 0, 0, 0,
     341, 302, 0, 210, 17, 0, 0, 0, 0, 0, 0, 0, 63, 0, 0, 0,
     457, 291, 121, 0, 0, 0, 0, 0, 145, 0, 0, 0, 261, 0, 0, 0,
     0, 359, 386, 159, 557, 47, 0, 45, 432, 0, 239, 120, 316, 7, 74, 0,
     393, 279, 0, 81, 0, 0, 0, 0, 290, 0, 0, 0, 277, 0, 0, 0,
     601, 251, 34, 0, 518, 0, 0, 0, 126, 0, 0, 0, 0, 0, 0, 0,
     345, 0, 306, 3, 46, 0, 0, 0, 0, 0, 0, 0, 199, 0, 0, 0]
  let isArcBool : ℕ → Bool := fun m =>
    Nat.ble 3 ((List.range 13).filter (fun p => m.testBit p)).length &&
    (List.range 13).all (fun l =>
      Nat.ble ([l, (l + 1) % 13, (l + 3) % 13, (l + 9) % 13].filter (fun p => m.testBit p)).length 2)
  have hcover : ∀ a b c d : Fin 4,
      isArcBool (mkSM a b c d) = true →
      let code := arcTbl.getD (64 * a.val + 16 * b.val + 4 * c.val + d.val) 0
      code < 624 ∧ genMaskN (code / 39) ((code % 39) / 3) (code % 3) = mkSM a b c d := by
    have hall : (List.finRange 4).all (fun a =>
      (List.finRange 4).all (fun b =>
        (List.finRange 4).all (fun c =>
          (List.finRange 4).all (fun d =>
            let m := mkSM a b c d
            let code := arcTbl.getD (64 * a.val + 16 * b.val + 4 * c.val + d.val) 0
            !isArcBool m || (Nat.blt code 624 && (genMaskN (code / 39) ((code % 39) / 3) (code % 3) == m)))))) = true := by
      decide +kernel
    intro a b c d ha
    rw [List.all_eq_true] at hall
    have h1 := hall a (List.mem_finRange a); rw [List.all_eq_true] at h1
    have h2 := h1 b (List.mem_finRange b); rw [List.all_eq_true] at h2
    have h3 := h2 c (List.mem_finRange c); rw [List.all_eq_true] at h3
    have h4 := h3 d (List.mem_finRange d)
    simp only [ha, Bool.not_true, Bool.false_or, Bool.and_eq_true, Nat.blt_eq, beq_iff_eq] at h4
    exact h4
  have arc_to_triple : ∀ pm : ℕ, isArc pm →
      ∃ (x3 : Fin 16) (x4 : Fin 13) (x5 : Fin 3),
        ∀ p : Fin 13, pm.testBit p.val =
          (masks.getD x3.val 0).testBit (((p - x4) * mults.getD x5.val 0).val) := by
    intro pm harc
    obtain ⟨hpm_lt, hpm_cnt, hpm_line⟩ := harc
    have hex0 : ∃ p0 < 13, pm.testBit p0 = true := by
      have hne : ((List.range 13).filter (fun p => pm.testBit p)) ≠ [] := by
        intro hemp; rw [hemp] at hpm_cnt; simp at hpm_cnt
      obtain ⟨p0, hp0⟩ := List.exists_mem_of_ne_nil _ hne
      rw [List.mem_filter, List.mem_range] at hp0
      exact ⟨p0, hp0.1, hp0.2⟩
    obtain ⟨p0, hp0_lt, hp0_bit⟩ := hex0
    let sm : ℕ := (List.range 13).foldl (fun acc p =>
      if pm.testBit ((p + p0) % 13) then acc ||| (1 <<< p) else acc) 0
    have sm_testBit_aux : ∀ (ks : List ℕ) (init k : ℕ),
        (ks.foldl (fun acc p => if pm.testBit ((p + p0) % 13) then acc ||| (1 <<< p) else acc) init).testBit k =
        (init.testBit k || ks.any (fun p => pm.testBit ((p + p0) % 13) && decide (p = k))) := by
      intro ks
      induction ks with
      | nil => intro init k; simp
      | cons a ks ih =>
        intro init k
        simp only [List.foldl_cons, List.any_cons]
        rw [ih]
        cases h : pm.testBit ((a + p0) % 13)
        · simp
        · simp only [ite_true, Bool.true_and, Nat.testBit_or, testBit_one_shiftLeft]
          rw [Bool.or_assoc]
    have sm_bit : ∀ k : ℕ, sm.testBit k = (decide (k < 13) && pm.testBit ((k + p0) % 13)) := by
      intro k
      dsimp [sm]
      rw [sm_testBit_aux, Nat.zero_testBit, Bool.false_or]
      by_cases hk : k < 13
      · simp only [hk, decide_true, Bool.true_and]
        cases hb : pm.testBit ((k + p0) % 13)
        · rw [Bool.eq_false_iff]; intro h
          rw [List.any_eq_true] at h
          obtain ⟨a, _, ha⟩ := h
          simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
          have ha2 : a = k := ha.2
          subst ha2; rw [hb] at ha; cases ha.1
        · rw [List.any_eq_true]
          exact ⟨k, List.mem_range.mpr hk, by simp [hb]⟩
      · simp only [hk, decide_false, Bool.false_and]
        rw [Bool.eq_false_iff]; intro h
        rw [List.any_eq_true] at h
        obtain ⟨a, ha_mem, ha⟩ := h
        rw [List.mem_range] at ha_mem
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
        omega
    have sm_zero : sm.testBit 0 = true := by
      rw [sm_bit 0]; simp [Nat.mod_eq_of_lt hp0_lt, hp0_bit]
    have mod13_comm : ∀ a b c : ℕ, ((a + b) % 13 + c) % 13 = ((a + c) % 13 + b) % 13 := by
      intro a b c
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      rw [Nat.add_mod ((a + c) % 13), Nat.mod_mod, ← Nat.add_mod]
      congr 1; omega
    have filter_len4 : ∀ (a b c d : ℕ) (f : ℕ → Bool),
        ([a, b, c, d].filter f).length =
        (if f a then 1 else 0) + (if f b then 1 else 0) + (if f c then 1 else 0) + (if f d then 1 else 0) := by
      intro a b c d f
      cases h1 : f a <;> cases h2 : f b <;> cases h3 : f c <;> cases h4 : f d <;> simp [h1, h2, h3, h4]
    have filter_len3 : ∀ (a b c : ℕ) (f : ℕ → Bool),
        ([a, b, c].filter f).length =
        (if f a then 1 else 0) + (if f b then 1 else 0) + (if f c then 1 else 0) := by
      intro a b c f
      cases h1 : f a <;> cases h2 : f b <;> cases h3 : f c <;> simp [h1, h2, h3]
    have sm_line : ∀ l < 13,
        ([l, (l + 1) % 13, (l + 3) % 13, (l + 9) % 13].filter (fun p => sm.testBit p)).length ≤ 2 := by
      intro l hl
      have hl' := hpm_line ((l + p0) % 13) (Nat.mod_lt _ (by omega))
      have h0 : sm.testBit l = pm.testBit ((l + p0) % 13) := by
        rw [sm_bit]; simp [hl]
      have h1 : sm.testBit ((l + 1) % 13) = pm.testBit (((l + p0) % 13 + 1) % 13) := by
        rw [sm_bit, decide_eq_true (Nat.mod_lt _ (by omega)), Bool.true_and, mod13_comm l 1 p0]
      have h3 : sm.testBit ((l + 3) % 13) = pm.testBit (((l + p0) % 13 + 3) % 13) := by
        rw [sm_bit, decide_eq_true (Nat.mod_lt _ (by omega)), Bool.true_and, mod13_comm l 3 p0]
      have h9 : sm.testBit ((l + 9) % 13) = pm.testBit (((l + p0) % 13 + 9) % 13) := by
        rw [sm_bit, decide_eq_true (Nat.mod_lt _ (by omega)), Bool.true_and, mod13_comm l 9 p0]
      rw [filter_len4] at hl' ⊢
      rw [h0, h1, h3, h9]
      exact hl'
    have sm_cnt : 3 ≤ ((List.range 13).filter (fun p => sm.testBit p)).length := by
      have hcard_sm : ((List.range 13).filter (fun p => sm.testBit p)).length =
          (Finset.univ.filter (fun p : Fin 13 => sm.testBit p.val)).card := by
        have hnd : ((List.range 13).filter (fun p => sm.testBit p)).Nodup :=
          List.Nodup.filter _ List.nodup_range
        have hbij : (Finset.univ.filter (fun p : Fin 13 => sm.testBit p.val)).card =
            (((List.range 13).filter (fun p => sm.testBit p)).toFinset).card := by
          apply Finset.card_bij (fun (p : Fin 13) _ => p.val)
          · intro p hp
            rw [Finset.mem_filter] at hp
            rw [List.mem_toFinset, List.mem_filter, List.mem_range]
            exact ⟨p.isLt, hp.2⟩
          · intro a _ b _ h; exact Fin.ext h
          · intro n hn
            rw [List.mem_toFinset, List.mem_filter, List.mem_range] at hn
            exact ⟨⟨n, hn.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn.2⟩, rfl⟩
        rw [hbij, List.toFinset_card_of_nodup hnd]
      have hcard_pm : ((List.range 13).filter (fun p => pm.testBit p)).length =
          (Finset.univ.filter (fun p : Fin 13 => pm.testBit p.val)).card := by
        have hnd : ((List.range 13).filter (fun p => pm.testBit p)).Nodup :=
          List.Nodup.filter _ List.nodup_range
        have hbij : (Finset.univ.filter (fun p : Fin 13 => pm.testBit p.val)).card =
            (((List.range 13).filter (fun p => pm.testBit p)).toFinset).card := by
          apply Finset.card_bij (fun (p : Fin 13) _ => p.val)
          · intro p hp
            rw [Finset.mem_filter] at hp
            rw [List.mem_toFinset, List.mem_filter, List.mem_range]
            exact ⟨p.isLt, hp.2⟩
          · intro a _ b _ h; exact Fin.ext h
          · intro n hn
            rw [List.mem_toFinset, List.mem_filter, List.mem_range] at hn
            exact ⟨⟨n, hn.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn.2⟩, rfl⟩
        rw [hbij, List.toFinset_card_of_nodup hnd]
      rw [hcard_sm]; rw [hcard_pm] at hpm_cnt
      have heq : (Finset.univ.filter (fun p : Fin 13 => sm.testBit p.val)).card =
          (Finset.univ.filter (fun p : Fin 13 => pm.testBit p.val)).card := by
        let p0f : Fin 13 := ⟨p0, hp0_lt⟩
        apply Finset.card_bij (fun p _ => p + p0f)
        · intro p hp
          rw [Finset.mem_filter] at hp ⊢
          refine ⟨Finset.mem_univ _, ?_⟩
          have hb := sm_bit p.val
          simp only [p.isLt, decide_true, Bool.true_and] at hb
          rw [Fin.val_add]
          change pm.testBit ((p.val + p0) % 13) = true
          rw [← hb]; exact hp.2
        · intro a _ b _ h; exact add_right_cancel h
        · intro q hq
          rw [Finset.mem_filter] at hq
          refine ⟨q - p0f, ?_, sub_add_cancel q p0f⟩
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have hb := sm_bit (q - p0f).val
          simp only [(q - p0f).isLt, decide_true, Bool.true_and] at hb
          rw [hb]
          have hval : ((q - p0f).val + p0) % 13 = q.val := by
            have h := congrArg Fin.val (sub_add_cancel q p0f)
            rw [Fin.val_add] at h
            exact h
          rw [hval]; exact hq.2
      omega
    have pick_one : ∀ (a b c : ℕ),
        ([a, b, c].filter (fun p => sm.testBit p)).length ≤ 1 →
        ∃ (c_idx : Fin 4),
          sm.testBit a = (c_idx.val == 1) ∧
          sm.testBit b = (c_idx.val == 2) ∧
          sm.testBit c = (c_idx.val == 3) := by
      intro a b c hle
      cases ha : sm.testBit a <;> cases hb : sm.testBit b <;> cases hc : sm.testBit c
      · exact ⟨0, by decide⟩
      · exact ⟨3, by decide⟩
      · exact ⟨2, by decide⟩
      · simp [ha, hb, hc] at hle
      · exact ⟨1, by decide⟩
      · simp [ha, hb, hc] at hle
      · simp [ha, hb, hc] at hle
      · simp [ha, hb, hc] at hle
    have hl0 : ([1, 3, 9].filter (fun p => sm.testBit p)).length ≤ 1 := by
      have h := sm_line 0 (by omega)
      rw [filter_len4] at h; rw [filter_len3]
      have h0 : sm.testBit 0 = true := sm_zero
      change (if sm.testBit 0 = true then 1 else 0) + (if sm.testBit 1 = true then 1 else 0) +
        (if sm.testBit 3 = true then 1 else 0) + (if sm.testBit 9 = true then 1 else 0) ≤ 2 at h
      rw [h0] at h; simp only [ite_true] at h; omega
    have hl12 : ([12, 2, 8].filter (fun p => sm.testBit p)).length ≤ 1 := by
      have h := sm_line 12 (by omega)
      rw [filter_len4] at h; rw [filter_len3]
      have h0 : sm.testBit 0 = true := sm_zero
      change (if sm.testBit 12 = true then 1 else 0) + (if sm.testBit 0 = true then 1 else 0) +
        (if sm.testBit 2 = true then 1 else 0) + (if sm.testBit 8 = true then 1 else 0) ≤ 2 at h
      rw [h0] at h; simp only [ite_true] at h; omega
    have hl10 : ([10, 11, 6].filter (fun p => sm.testBit p)).length ≤ 1 := by
      have h := sm_line 10 (by omega)
      rw [filter_len4] at h; rw [filter_len3]
      have h0 : sm.testBit 0 = true := sm_zero
      change (if sm.testBit 10 = true then 1 else 0) + (if sm.testBit 11 = true then 1 else 0) +
        (if sm.testBit 0 = true then 1 else 0) + (if sm.testBit 6 = true then 1 else 0) ≤ 2 at h
      rw [h0] at h; simp only [ite_true] at h; omega
    have hl4 : ([4, 5, 7].filter (fun p => sm.testBit p)).length ≤ 1 := by
      have h := sm_line 4 (by omega)
      rw [filter_len4] at h; rw [filter_len3]
      have h0 : sm.testBit 0 = true := sm_zero
      change (if sm.testBit 4 = true then 1 else 0) + (if sm.testBit 5 = true then 1 else 0) +
        (if sm.testBit 7 = true then 1 else 0) + (if sm.testBit 0 = true then 1 else 0) ≤ 2 at h
      rw [h0] at h; simp only [ite_true] at h; omega
    obtain ⟨c0, h1, h3, h9⟩ := pick_one 1 3 9 hl0
    obtain ⟨c1, h12, h2, h8⟩ := pick_one 12 2 8 hl12
    obtain ⟨c2, h10, h11, h6⟩ := pick_one 10 11 6 hl10
    obtain ⟨c3, h4, h5, h7⟩ := pick_one 4 5 7 hl4
    have hsm_eq : sm = mkSM c0 c1 c2 c3 := by
      have hb := hmk_bits c0 c1 c2 c3
      apply Nat.eq_of_testBit_eq
      intro k
      by_cases hk : k < 13
      · have hk_eq : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨
            k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 := by omega
        rcases hk_eq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rw [sm_zero, hb.1]
        · rw [h1, hb.2.1]
        · rw [h2, hb.2.2.1]
        · rw [h3, hb.2.2.2.1]
        · rw [h4, hb.2.2.2.2.1]
        · rw [h5, hb.2.2.2.2.2.1]
        · rw [h6, hb.2.2.2.2.2.2.1]
        · rw [h7, hb.2.2.2.2.2.2.2.1]
        · rw [h8, hb.2.2.2.2.2.2.2.2.1]
        · rw [h9, hb.2.2.2.2.2.2.2.2.2.1]
        · rw [h10, hb.2.2.2.2.2.2.2.2.2.2.1]
        · rw [h11, hb.2.2.2.2.2.2.2.2.2.2.2.1]
        · rw [h12, hb.2.2.2.2.2.2.2.2.2.2.2.2]
      · rw [sm_bit]; simp only [hk, decide_false, Bool.false_and]
        symm
        have hlt := hmk_lt c0 c1 c2 c3
        rw [Nat.testBit_eq_false_of_lt]
        have hpow : 2 ^ 13 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
        omega
    have hisArc_sm : isArcBool (mkSM c0 c1 c2 c3) = true := by
      rw [← hsm_eq]
      dsimp [isArcBool]
      rw [Bool.and_eq_true, Nat.ble_eq, List.all_eq_true]
      refine ⟨sm_cnt, fun l hl => ?_⟩
      rw [List.mem_range] at hl
      rw [Nat.ble_eq]
      exact sm_line l hl
    have hhit := hcover c0 c1 c2 c3 hisArc_sm
    let code := arcTbl.getD (64 * c0.val + 16 * c1.val + 4 * c2.val + c3.val) 0
    have hcode_lt : code < 624 := hhit.1
    have hcode_eq : genMaskN (code / 39) ((code % 39) / 3) (code % 3) = mkSM c0 c1 c2 c3 := hhit.2
    let x3 : Fin 16 := ⟨code / 39, by omega⟩
    let x4 : Fin 13 := ⟨(code % 39) / 3, by omega⟩
    let x5 : Fin 3 := ⟨code % 3, by omega⟩
    have genMask_bit : ∀ (p : Fin 13),
        (genMaskN x3.val x4.val x5.val).testBit p.val =
          (masks.getD x3.val 0).testBit (((p - x4) * mults.getD x5.val 0).val) := by
      intro p
      have haux : ∀ (ks : List ℕ) (init k : ℕ),
          (ks.foldl (fun acc q =>
            if (masks.getD x3.val 0).testBit (((q + 13 - x4.val) * multsN.getD x5.val 0) % 13)
            then acc ||| (1 <<< q) else acc) init).testBit k =
          (init.testBit k || ks.any (fun q =>
            (masks.getD x3.val 0).testBit (((q + 13 - x4.val) * multsN.getD x5.val 0) % 13) && decide (q = k))) := by
        intro ks
        induction ks with
        | nil => intro init k; simp
        | cons a ks ih =>
          intro init k
          simp only [List.foldl_cons, List.any_cons]
          rw [ih]
          cases h : (masks.getD x3.val 0).testBit (((a + 13 - x4.val) * multsN.getD x5.val 0) % 13)
          · simp
          · simp only [ite_true, Bool.true_and, Nat.testBit_or, testBit_one_shiftLeft]
            rw [Bool.or_assoc]
      dsimp [genMaskN]
      rw [haux, Nat.zero_testBit, Bool.false_or]
      have hidx : ((p.val + 13 - x4.val) * multsN.getD x5.val 0) % 13 =
          ((p - x4) * mults.getD x5.val 0).val := by
        have hm : multsN.getD x5.val 0 = (mults.getD x5.val 0).val := by
          have hall : ∀ k : Fin 3, multsN.getD k.val 0 = (mults.getD k.val 0).val := by decide
          exact hall x5
        have hp_lt := p.isLt
        have hx4_lt := x4.isLt
        rw [hm]
        simp only [Fin.val_mul, Fin.val_sub]
        rw [Nat.mul_mod, Nat.mul_mod ((13 - x4.val + p.val) % 13)]
        congr 2
        rw [Nat.mod_mod]
        congr 1; omega
      rw [← hidx]
      cases hb : (masks.getD x3.val 0).testBit (((p.val + 13 - x4.val) * multsN.getD x5.val 0) % 13)
      · rw [Bool.eq_false_iff]; intro h
        rw [List.any_eq_true] at h
        obtain ⟨a, _, ha⟩ := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ha
        have ha2 : a = p.val := ha.2
        subst ha2; rw [hb] at ha; cases ha.1
      · rw [List.any_eq_true]
        exact ⟨p.val, List.mem_range.mpr p.isLt, by simp only [hb, decide_true, Bool.and_self]⟩
    let p0f : Fin 13 := ⟨p0, hp0_lt⟩
    refine ⟨x3, x4 + p0f, x5, ?_⟩
    intro p
    have hshift : (p - (x4 + p0f)) = (p - p0f) - x4 := by rw [add_comm x4 p0f, sub_add_eq_sub_sub]
    rw [hshift, ← genMask_bit, hcode_eq, ← hsm_eq, sm_bit]
    simp only [(p - p0f).isLt, decide_true, Bool.true_and]
    have hval : ((p - p0f).val + p0) % 13 = p.val := by
      have h := congrArg Fin.val (sub_add_cancel p p0f)
      rw [Fin.val_add] at h
      exact h
    rw [hval]
  have arc_init_equiv : ∀ (pm : ℕ) (x3 : Fin 16) (x4 : Fin 13) (x5 : Fin 3),
      (∀ p : Fin 13, pm.testBit p.val =
        (masks.getD x3.val 0).testBit (((p - x4) * mults.getD x5.val 0).val)) →
      let x7 : Fin 13 → Fin 13 → Prop := fun a b => a = b ∨ a = b + 1 ∨ a = b + 3 ∨ a = b + 9
      let x8 : Finset (Fin 13) :=
        {a : Fin 13 | (masks.getD x3.val 0).testBit (((a - x4) * mults.getD x5.val 0).val) = true}
      let x9 : Fin 26 → Bool := fun v =>
        decide ((∃ a ∈ x8, v = Fin.castAdd 13 a) ∨
          ∃ l : Fin 13, v = Fin.natAdd 13 l ∧ ∀ a ∈ x8, ¬x7 a l)
      ∀ S : Finset E,
        (S = ∅ ∨ ∃ v : Fin 26, x9 v = false ∧ ∀ e ∈ S, X e v = true) ↔
        (S = ∅ ∨ (initMasks pm).any (fun r => (enc S &&& r) == enc S) = true) := by
    intro pm x3 x4 x5 hpm x7 x8 x9 S
    have hx8_mem : ∀ p : Fin 13, p ∈ x8 ↔ pm.testBit p.val = true := by
      intro p
      dsimp [x8]
      rw [Finset.mem_filter]
      simp [hpm p]
    have hx9_pt : ∀ p : Fin 13, x9 (Fin.castAdd 13 p) = false ↔ pm.testBit p.val = false := by
      intro p
      dsimp [x9]
      rw [decide_eq_false_iff_not, not_or]
      constructor
      · rintro ⟨h1, _⟩
        cases hb : pm.testBit p.val
        · rfl
        · exfalso; exact h1 ⟨p, (hx8_mem p).mpr hb, rfl⟩
      · intro hbf
        refine ⟨?_, ?_⟩
        · rintro ⟨a, ha, heq⟩
          have hpa : p = a := Fin.castAdd_injective 13 _ heq
          subst hpa
          have := (hx8_mem p).mp ha
          rw [hbf] at this; cases this
        · rintro ⟨l, heq, _⟩
          have h1 := congrArg Fin.val heq
          simp [Fin.val_castAdd] at h1
          omega
    have hx9_line : ∀ l : Fin 13, x9 (Fin.natAdd 13 l) = false ↔
        (pm.testBit l.val || pm.testBit ((l.val + 1) % 13) ||
         pm.testBit ((l.val + 3) % 13) || pm.testBit ((l.val + 9) % 13)) = true := by
      intro l
      dsimp [x9]
      rw [decide_eq_false_iff_not, not_or]
      have hno1 : ¬∃ a ∈ x8, Fin.natAdd 13 l = Fin.castAdd 13 a := by
        rintro ⟨a, _, heq⟩
        have h1 := congrArg Fin.val heq
        simp [Fin.val_castAdd] at h1
        omega
      have h2_iff : (¬∃ l' : Fin 13, Fin.natAdd 13 l = Fin.natAdd 13 l' ∧ ∀ a ∈ x8, ¬x7 a l') ↔
          ∃ a ∈ x8, x7 a l := by
        constructor
        · intro h
          by_contra hnone
          push Not at hnone
          exact h ⟨l, rfl, hnone⟩
        · rintro ⟨a, ha, hax⟩ ⟨l', heq, hall⟩
          have hll : l = l' := Fin.natAdd_injective 13 _ heq
          subst hll
          exact hall a ha hax
      rw [and_iff_right hno1, h2_iff]
      simp only [Bool.or_eq_true]
      constructor
      · rintro ⟨a, ha, hax⟩
        have hab := (hx8_mem a).mp ha
        dsimp [x7] at hax
        rcases hax with rfl | rfl | rfl | rfl
        · left; left; left; exact hab
        · left; left; right; simpa [Fin.val_add] using hab
        · left; right; simpa [Fin.val_add] using hab
        · right; simpa [Fin.val_add] using hab
      · intro hor
        rcases hor with ((h0 | h1) | h3) | h9
        · exact ⟨l, (hx8_mem l).mpr h0, Or.inl rfl⟩
        · refine ⟨l + 1, (hx8_mem (l + 1)).mpr ?_, Or.inr (Or.inl rfl)⟩
          simpa [Fin.val_add] using h1
        · refine ⟨l + 3, (hx8_mem (l + 3)).mpr ?_, Or.inr (Or.inr (Or.inl rfl))⟩
          simpa [Fin.val_add] using h3
        · refine ⟨l + 9, (hx8_mem (l + 9)).mpr ?_, Or.inr (Or.inr (Or.inr rfl))⟩
          simpa [Fin.val_add] using h9
    apply or_congr_right
    rw [List.any_eq_true]
    constructor
    · rintro ⟨v, hv, hS⟩
      by_cases hlt : v.val < 13
      · let p : Fin 13 := ⟨v.val, hlt⟩
        have hveq : v = Fin.castAdd 13 p := Fin.ext (by simp [p])
        rw [hveq] at hv hS
        have hp_false := (hx9_pt p).mp hv
        refine ⟨ptStar p.val, ?_, ?_⟩
        · dsimp [initMasks]
          rw [List.mem_append]; left
          rw [List.mem_map]
          refine ⟨p.val, ?_, rfl⟩
          rw [List.mem_filter, List.mem_range]
          exact ⟨p.isLt, by simp [hp_false]⟩
        · simp only [beq_iff_eq]
          exact (ptStar_sub_iff p S).mpr hS
      · let l : Fin 13 := ⟨v.val - 13, by omega⟩
        have hveq : v = Fin.natAdd 13 l := Fin.ext (by simp [l]; omega)
        rw [hveq] at hv hS
        have hl_true := (hx9_line l).mp hv
        refine ⟨lineStar l.val, ?_, ?_⟩
        · dsimp [initMasks]
          rw [List.mem_append]; right
          rw [List.mem_map]
          refine ⟨l.val, ?_, rfl⟩
          rw [List.mem_filter, List.mem_range]
          exact ⟨l.isLt, hl_true⟩
        · simp only [beq_iff_eq]
          exact (lineStar_sub_iff l S).mpr hS
    · rintro ⟨r, hr, hsub⟩
      simp only [beq_iff_eq] at hsub
      dsimp [initMasks] at hr
      rw [List.mem_append] at hr
      rcases hr with hp | hl
      · rw [List.mem_map] at hp
        obtain ⟨p, hp, rfl⟩ := hp
        rw [List.mem_filter, List.mem_range] at hp
        let pf : Fin 13 := ⟨p, hp.1⟩
        refine ⟨Fin.castAdd 13 pf, (hx9_pt pf).mpr (by simpa [pf] using hp.2), ?_⟩
        exact (ptStar_sub_iff pf S).mp hsub
      · rw [List.mem_map] at hl
        obtain ⟨l, hl, rfl⟩ := hl
        rw [List.mem_filter, List.mem_range] at hl
        let lf : Fin 13 := ⟨l, hl.1⟩
        refine ⟨Fin.natAdd 13 lf, (hx9_line lf).mpr hl.2, ?_⟩
        exact (lineStar_sub_iff lf S).mp hsub
  have finish_from_arc : ∀ pm : ℕ, isArc pm →
      full ∉ (prune (x1.map (fun p => (enc p.1, enc p.2)))).foldl stepBM (initMasks pm) →
      ∃ (x3 : Fin 16) (x4 : Fin 13) (x5 : Fin 3),
        have x6 : Fin (13 : ℕ) × Fin (4 : ℕ) → Fin (26 : ℕ) → Bool := fun (x6 : Fin (13 : ℕ) × Fin (4 : ℕ)) (x7 : Fin (26 : ℕ)) => Decidable.decide (x7 = Fin.castAdd (13 : ℕ) (x6.1 + [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].getD ↑x6.2 (0 : Fin (13 : ℕ))) ∨ x7 = Fin.natAdd (13 : ℕ) x6.1);
        let x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x7 x8 : Fin (13 : ℕ)) => x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ));
        have x8 : Finset (Fin (13 : ℕ)) := {x8 : Fin (13 : ℕ) | ([(4544 : ℕ), (2464 : ℕ), (6464 : ℕ), (5440 : ℕ), (4416 : ℕ), (3332 : ℕ), (5264 : ℕ), (3204 : ℕ), (3076 : ℕ), (2336 : ℕ), (6400 : ℕ), (5376 : ℕ), (5136 : ℕ), (6164 : ℕ), (6148 : ℕ), (6160 : ℕ)].getD ↑x3 (0 : ℕ)).testBit ↑((x8 - x4) * [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].getD ↑x5 (0 : Fin (13 : ℕ))) = Bool.true};
        have x9 : Fin (26 : ℕ) → Bool := fun (x9 : Fin (26 : ℕ)) => Decidable.decide ((∃ x10 ∈ x8, x9 = Fin.castAdd (13 : ℕ) x10) ∨ ∃ (x10 : Fin (13 : ℕ)), x9 = Fin.natAdd (13 : ℕ) x10 ∧ ∀ x11 ∈ x8, ¬x7 x11 x10);
        ¬List.foldl (fun (x10 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) → Prop) (x11 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) × Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) (x12 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) => x10 x12 ∨ x12 ⊆ x11.1 ∪ x11.2 ∧ x10 x11.1 ∧ x10 x11.2) (fun (x10 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) => x10 = ∅ ∨ ∃ (x11 : Fin (26 : ℕ)), x9 x11 = Bool.false ∧ ∀ x12 ∈ x10, x6 x12 x11 = Bool.true) x1 Finset.univ := by
    intro pm harc hnot
    obtain ⟨x3, x4, x5, hpm⟩ := arc_to_triple pm harc
    refine ⟨x3, x4, x5, ?_⟩
    dsimp only
    intro hreach
    have heq := (foldl_equiv x1 _ (initMasks pm) (arc_init_equiv pm x3 x4 x5 hpm) Finset.univ).mp hreach
    rcases heq with hemp | hany
    · have : ((0 : Fin 13), (0 : Fin 4)) ∈ (∅ : Finset E) := hemp ▸ Finset.mem_univ _
      exact Finset.notMem_empty _ this
    · rw [List.any_eq_true] at hany
      obtain ⟨r, hr_mem, hr_eq⟩ := hany
      simp only [beq_iff_eq, enc_univ] at hr_eq
      have hr_lt : r < bound := by
        apply stepBM_lt (prune (x1.map (fun p => (enc p.1, enc p.2)))) (initMasks pm)
        · intro q hq
          dsimp [prune] at hq
          rw [List.mem_filter, List.mem_map] at hq
          obtain ⟨⟨p, _, rfl⟩, _⟩ := hq
          exact ⟨enc_lt p.1, enc_lt p.2⟩
        · intro s hs
          have := initMasks_lt pm s hs
          omega
        · exact hr_mem
      have hrf : r = full := (full_and_lt r hr_lt).mp hr_eq
      subst hrf
      exact hnot hr_mem
  have base18 : ∀ (G : List (ℕ × ℕ)), G.length ≤ 17 → full ∉ G.foldl stepBM (initMasks 4544) := by
    let W : List E := [(0,0),(0,1),(1,1),(0,2),(1,2),(2,2),(0,3),(1,3),(2,3),
      (3,2),(4,2),(5,1),(6,0),(7,0),(8,0),(9,2),(10,3),(11,1),(12,0)]
    let popW : ℕ → ℕ := fun n => (W.filter (fun e => n.testBit (idx e))).length
    let orAll : List ℕ → ℕ := fun T => T.foldl (· ||| ·) 0
    have pop_full : popW full = 19 := by
      have hf : full = 2 ^ 52 - 1 := by decide
      have hbit : ∀ e : E, full.testBit (idx e) = true := by
        intro e; rw [hf, Nat.testBit_two_pow_sub_one]; exact decide_eq_true (idx_lt e)
      dsimp [popW]
      simp only [hbit]
      rfl
    have pop_init : ∀ r ∈ initMasks 4544, popW r ≤ 1 := by
      have hpt : ∀ p : Fin 13, !(4544 : ℕ).testBit p.val = true →
          (W.filter (fun e => X e (Fin.castAdd 13 p))).length ≤ 1 := by
        have hall : (List.finRange 13).all (fun p =>
            (4544 : ℕ).testBit p.val || Nat.ble (W.filter (fun e => X e (Fin.castAdd 13 p))).length 1) = true := by
          decide +kernel
        intro p hp
        rw [List.all_eq_true] at hall
        have h1 := hall p (List.mem_finRange p)
        cases hbit : (4544 : ℕ).testBit p.val
        · rw [hbit, Bool.false_or, Nat.ble_eq] at h1
          exact h1
        · rw [hbit] at hp; cases hp
      have hln : ∀ l : Fin 13,
          ((4544 : ℕ).testBit l.val || (4544 : ℕ).testBit ((l.val + 1) % 13) ||
           (4544 : ℕ).testBit ((l.val + 3) % 13) || (4544 : ℕ).testBit ((l.val + 9) % 13)) = true →
          (W.filter (fun e => X e (Fin.natAdd 13 l))).length ≤ 1 := by
        have hall : (List.finRange 13).all (fun l =>
            !((4544 : ℕ).testBit l.val || (4544 : ℕ).testBit ((l.val + 1) % 13) ||
              (4544 : ℕ).testBit ((l.val + 3) % 13) || (4544 : ℕ).testBit ((l.val + 9) % 13)) ||
            Nat.ble (W.filter (fun e => X e (Fin.natAdd 13 l))).length 1) = true := by
          decide +kernel
        intro l hl
        rw [List.all_eq_true] at hall
        have h1 := hall l (List.mem_finRange l)
        simp only [hl, Bool.not_true, Bool.false_or, Nat.ble_eq] at h1
        exact h1
      intro r hr
      dsimp [initMasks] at hr
      rw [List.mem_append] at hr
      rcases hr with hp | hl
      · rw [List.mem_map] at hp
        obtain ⟨p, hp, rfl⟩ := hp
        rw [List.mem_filter, List.mem_range] at hp
        dsimp [popW]
        have hfun : (fun e : E => (ptStar p).testBit (idx e)) = (fun e : E => X e (Fin.castAdd 13 ⟨p, hp.1⟩)) := by
          funext e; exact ptStar_bit ⟨p, hp.1⟩ e
        rw [hfun]
        exact hpt ⟨p, hp.1⟩ hp.2
      · rw [List.mem_map] at hl
        obtain ⟨l, hl, rfl⟩ := hl
        rw [List.mem_filter, List.mem_range] at hl
        dsimp [popW]
        have hfun : (fun e : E => (lineStar l).testBit (idx e)) = (fun e : E => X e (Fin.natAdd 13 ⟨l, hl.1⟩)) := by
          funext e; exact lineStar_bit ⟨l, hl.1⟩ e
        rw [hfun]
        exact hln ⟨l, hl.1⟩ hl.2
    have filter_or_le : ∀ (ks : List E) (f g : E → Bool),
        (ks.filter (fun i => f i || g i)).length ≤ (ks.filter f).length + (ks.filter g).length := by
      intro ks f g
      induction ks with
      | nil => simp
      | cons k ks ih =>
        simp only [List.filter_cons]
        cases f k <;> cases g k <;> simp <;> omega
    have filter_mono : ∀ (ks : List E) (f g : E → Bool),
        (∀ i, f i = true → g i = true) →
        (ks.filter f).length ≤ (ks.filter g).length := by
      intro ks f g hfg
      induction ks with
      | nil => simp
      | cons k ks ih =>
        simp only [List.filter_cons]
        cases hf : f k
        · cases g k <;> simp <;> omega
        · rw [hfg k hf]; simp; omega
    have pop_or_le : ∀ a b : ℕ, popW (a ||| b) ≤ popW a + popW b := by
      intro a b
      dsimp [popW]
      have hbit : (fun e : E => (a ||| b).testBit (idx e)) =
          (fun e : E => a.testBit (idx e) || b.testBit (idx e)) := by
        funext e; exact Nat.testBit_or a b (idx e)
      rw [hbit]
      exact filter_or_le W _ _
    have orAll_bit : ∀ (T : List ℕ) (init k : ℕ),
        (T.foldl (· ||| ·) init).testBit k = (init.testBit k || T.any (fun r => r.testBit k)) := by
      intro T
      induction T with
      | nil => intro init k; simp
      | cons r T ih =>
        intro init k
        simp only [List.foldl_cons, List.any_cons]
        rw [ih, Nat.testBit_or, Bool.or_assoc]
    have orAll_pop_le : ∀ T : List ℕ, (∀ r ∈ T, r ∈ initMasks 4544) →
        popW (orAll T) ≤ T.length := by
      intro T
      induction T with
      | nil => intro _; dsimp [orAll, popW]; simp [Nat.zero_testBit]
      | cons r T ih =>
        intro hT
        have hstep : orAll (r :: T) = r ||| orAll T := by
          apply Nat.eq_of_testBit_eq; intro k
          dsimp [orAll]
          rw [orAll_bit T (0 ||| r) k, Nat.testBit_or 0 r, Nat.testBit_or r, orAll_bit T 0 k]
          simp [Nat.zero_testBit]
        rw [hstep]
        have h1 := pop_or_le r (orAll T)
        have h2 := pop_init r (hT r (List.mem_cons_self ..))
        have h3 := ih (fun s hs => hT s (List.mem_cons_of_mem r hs))
        simp only [List.length_cons]
        omega
    have countBM : ∀ (G : List (ℕ × ℕ)) (T : List ℕ),
        (∀ r ∈ T, r ∈ G.foldl stepBM (initMasks 4544)) →
        popW (orAll T) ≤ G.length + T.length := by
      intro G
      induction G using List.reverseRecOn with
      | nil =>
        intro T hT
        simpa using orAll_pop_le T hT
      | append_singleton G p ih =>
        intro T hT
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at hT
        let R := G.foldl stepBM (initMasks 4544)
        by_cases hall : ∀ r ∈ T, r ∈ R
        · have hc := ih T hall
          simp only [List.length_append, List.length_singleton]; omega
        · push Not at hall
          obtain ⟨r0, hr0T, hr0bad⟩ := hall
          have hstep_r0 := hT r0 hr0T
          dsimp [stepBM] at hstep_r0
          by_cases hfire : (R.any (fun r => (p.1 &&& r) == p.1) && R.any (fun r => (p.2 &&& r) == p.2)) = true
          · rw [Bool.and_eq_true, List.any_eq_true, List.any_eq_true] at hfire
            obtain ⟨⟨s1, hs1R, hs1⟩, ⟨s2, hs2R, hs2⟩⟩ := hfire
            simp only [beq_iff_eq] at hs1 hs2
            let T' : List ℕ := s1 :: s2 :: T.filter (fun r => decide (r ∈ R))
            have hT'R : ∀ r ∈ T', r ∈ R := by
              intro r hr
              simp only [T', List.mem_cons, List.mem_filter, decide_eq_true_eq] at hr
              rcases hr with rfl | rfl | ⟨_, h⟩
              · exact hs1R
              · exact hs2R
              · exact h
            have hfilt_lt : (T.filter (fun r => decide (r ∈ R))).length < T.length := by
              have hle : ∀ (M : List ℕ), r0 ∈ M → (M.filter (fun r => decide (r ∈ R))).length < M.length := by
                intro M
                induction M with
                | nil => intro h; exact absurd h List.not_mem_nil
                | cons a M ihM =>
                  intro h
                  simp only [List.filter_cons, List.length_cons]
                  rcases List.mem_cons.mp h with rfl | hmem
                  · have hf : decide (r0 ∈ R) = false := decide_eq_false hr0bad
                    rw [hf]; simp only [Bool.false_eq_true, ite_false]
                    have hfl := List.length_filter_le (fun r => decide (r ∈ R)) M
                    omega
                  · have hrec := ihM hmem
                    by_cases ha : a ∈ R
                    · have ht : decide (a ∈ R) = true := decide_eq_true ha
                      rw [ht]; simp only [ite_true, List.length_cons]; omega
                    · have hf : decide (a ∈ R) = false := decide_eq_false ha
                      rw [hf]; simp only [Bool.false_eq_true, ite_false]; omega
              exact hle T hr0T
            have hT'len : T'.length ≤ T.length + 1 := by
              have : T'.length = (T.filter (fun r => decide (r ∈ R))).length + 2 := rfl
              omega
            have hbits : ∀ e : E, (orAll T).testBit (idx e) = true → (orAll T').testBit (idx e) = true := by
              intro e hi
              dsimp [orAll] at hi ⊢
              rw [orAll_bit, Nat.zero_testBit, Bool.false_or, List.any_eq_true] at hi ⊢
              obtain ⟨r, hrT, hri⟩ := hi
              by_cases hrR : r ∈ R
              · exact ⟨r, by simp [T', hrT, hrR], hri⟩
              · have hrm := hT r hrT
                dsimp [stepBM] at hrm
                split_ifs at hrm
                · rw [List.mem_cons] at hrm
                  rcases hrm with rfl | hrm
                  · rw [Nat.testBit_or, Bool.or_eq_true] at hri
                    rcases hri with hp1 | hp2
                    · refine ⟨s1, by simp [T'], ?_⟩
                      have := congrArg (fun n => n.testBit (idx e)) hs1
                      rw [Nat.testBit_and, hp1, Bool.true_and] at this
                      exact this
                    · refine ⟨s2, by simp [T'], ?_⟩
                      have := congrArg (fun n => n.testBit (idx e)) hs2
                      rw [Nat.testBit_and, hp2, Bool.true_and] at this
                      exact this
                  · exact absurd hrm hrR
                · exact absurd hrm hrR
            have hmono : popW (orAll T) ≤ popW (orAll T') :=
              filter_mono W _ _ hbits
            have hc := ih T' hT'R
            simp only [List.length_append, List.length_singleton]
            omega
          · rw [ite_eq_right_iff.mpr (fun hh => absurd hh hfire)] at hstep_r0
            exact absurd hstep_r0 hr0bad
    intro G hG hfull
    have hc := countBM G [full] (by intro r hr; rw [List.mem_singleton] at hr; subst hr; exact hfull)
    have hor1 : orAll [full] = full := by
      dsimp [orAll]; simp
    rw [hor1, pop_full] at hc
    simp only [List.length_singleton] at hc
    omega
  have arc_4544 : isArc 4544 := by decide +kernel
  let L : List (ℕ × ℕ) := prune (x1.map (fun p => (enc p.1, enc p.2)))
  have hL_len : L.length ≤ 50 := by
    have h1 : L.length ≤ (x1.map (fun p => (enc p.1, enc p.2))).length :=
      List.length_filter_le _ _
    simp only [List.length_map] at h1
    omega
  have hL_props : ∀ p ∈ L, p.1 < bound ∧ p.2 < bound ∧ p.1 &&& p.2 ≠ p.1 ∧ p.2 &&& p.1 ≠ p.2 := by
    intro p hp
    dsimp [L, prune] at hp
    rw [List.mem_filter, List.mem_map] at hp
    obtain ⟨⟨q, _, rfl⟩, hcond⟩ := hp
    simp only [decide_eq_true_eq] at hcond
    exact ⟨enc_lt q.1, enc_lt q.2, hcond.1, hcond.2⟩
  let tops := L.filter (fun p => (p.1 ||| p.2) == full)
  by_cases htop0 : tops.length = 0
  · apply finish_from_arc 4544 arc_4544
    apply stepBM_no_full L (initMasks 4544)
    · intro p hp heq
      have hmem : p ∈ tops := by
        dsimp [tops]; rw [List.mem_filter]; exact ⟨hp, by simp [heq]⟩
      have hne : tops ≠ [] := List.ne_nil_of_mem hmem
      have hpos : 0 < tops.length := List.length_pos_of_ne_nil hne
      omega
    · intro hf
      have := initMasks_lt 4544 full hf
      omega
  · by_cases htop2 : 2 ≤ tops.length
    · by_cases hlen18 : 18 ≤ L.length
      · obtain ⟨pm, hpm_lt, hpm_cnt, hpm_line, hnot⟩ :=
          multi_top L hlen18 hL_len hL_props htop2
        exact finish_from_arc pm ⟨hpm_lt, hpm_cnt, hpm_line⟩ hnot
      · exact finish_from_arc 4544 arc_4544 (base18 L (by omega))
    · have htop1 : tops.length = 1 := by omega
      have split_one : ∀ (M : List (ℕ × ℕ)),
          (M.filter (fun p => (p.1 ||| p.2) == full)).length = 1 →
          ∃ (L1 L2 : List (ℕ × ℕ)) (a b : ℕ),
            M = L1 ++ (a, b) :: L2 ∧
            (a ||| b) = full ∧
            (∀ p ∈ L1, (p.1 ||| p.2) ≠ full) ∧
            (∀ p ∈ L2, (p.1 ||| p.2) ≠ full) := by
        intro M
        induction M with
        | nil => intro h; simp at h
        | cons p M ih =>
          intro h
          simp only [List.filter_cons] at h
          by_cases hp : ((p.1 ||| p.2) == full) = true
          · rw [if_pos hp, List.length_cons] at h
            have h0 : (M.filter (fun q => (q.1 ||| q.2) == full)).length = 0 := by omega
            refine ⟨[], M, p.1, p.2, rfl, by simpa [beq_iff_eq] using hp, (fun q hq => absurd hq List.not_mem_nil), ?_⟩
            intro q hq hqeq
            have hmem : q ∈ M.filter (fun r => (r.1 ||| r.2) == full) :=
              List.mem_filter.mpr ⟨hq, by simp [hqeq]⟩
            have := List.length_pos_of_ne_nil (List.ne_nil_of_mem hmem)
            omega
          · rw [if_neg hp] at h
            obtain ⟨L1, L2, a, b, hM, hab, hL1, hL2⟩ := ih h
            refine ⟨p :: L1, L2, a, b, by simp [hM], hab, ?_, hL2⟩
            intro q hq
            rcases List.mem_cons.mp hq with rfl | hq'
            · intro heq; apply hp; simp [heq]
            · exact hL1 q hq'
      obtain ⟨L1, L2, a, b, hL_split, hab_or, hL1_ne, hL2_ne⟩ := split_one L htop1
      by_cases hL1_17 : 17 ≤ L1.length
      · have hL1_le : L1.length ≤ 49 := by
          have : L.length = L1.length + 1 + L2.length := by
            rw [hL_split, List.length_append, List.length_cons]; omega
          omega
        have hL1_props : ∀ p ∈ L1,
            p.1 &&& p.2 ≠ p.1 ∧ p.2 &&& p.1 ≠ p.2 ∧ (p.1 ||| p.2) < full := by
          intro p hp
          have hpL : p ∈ L := by rw [hL_split]; exact List.mem_append_left _ hp
          have hbase := hL_props p hpL
          have hor_lt : p.1 ||| p.2 < bound := by
            have hpow : bound = 2 ^ 52 := by decide
            rw [hpow] at hbase ⊢
            exact Nat.or_lt_two_pow hbase.1 hbase.2.1
          have hne := hL1_ne p hp
          refine ⟨hbase.2.2.1, hbase.2.2.2, ?_⟩
          have : bound = full + 1 := by decide
          omega
        have habL : (a, b) ∈ L := by rw [hL_split]; simp
        have hab_p := hL_props (a, b) habL
        have ha_lt : a < full := by
          have hne : a ≠ full := by
            intro heq
            apply hab_p.2.2.2
            have hf : full = 2 ^ 52 - 1 := by decide
            have hpow : bound = 2 ^ 52 := by decide
            apply Nat.eq_of_testBit_eq; intro k
            rw [heq, Nat.testBit_and, hf, Nat.testBit_two_pow_sub_one]
            by_cases hk : k < 52
            · simp [hk]
            · simp only [hk, decide_false, Bool.and_false]
              symm
              rw [Nat.testBit_eq_false_of_lt]
              have hle : 2 ^ 52 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
              omega
          have : bound = full + 1 := by decide
          have := hab_p.1; omega
        have hb_lt : b < full := by
          have hne : b ≠ full := by
            intro heq
            apply hab_p.2.2.1
            have hf : full = 2 ^ 52 - 1 := by decide
            have hpow : bound = 2 ^ 52 := by decide
            apply Nat.eq_of_testBit_eq; intro k
            rw [heq, Nat.testBit_and, hf, Nat.testBit_two_pow_sub_one]
            by_cases hk : k < 52
            · simp [hk]
            · simp only [hk, decide_false, Bool.and_false]
              symm
              rw [Nat.testBit_eq_false_of_lt]
              have hle : 2 ^ 52 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
              omega
          have : bound = full + 1 := by decide
          have := hab_p.2.1; omega
        obtain ⟨pm, hpm_lt, hpm_cnt, hpm_line, hnotab⟩ :=
          single_top L1 hL1_17 hL1_le hL1_props a b ha_lt hb_lt hab_or
        apply finish_from_arc pm ⟨hpm_lt, hpm_cnt, hpm_line⟩
        change full ∉ L.foldl stepBM (initMasks pm)
        rw [hL_split, List.foldl_append, List.foldl_cons]
        apply stepBM_no_full L2 _ hL2_ne
        let R1 := L1.foldl stepBM (initMasks pm)
        have hR1_no : full ∉ R1 := by
          apply stepBM_no_full L1 (initMasks pm) hL1_ne
          intro hf; have := initMasks_lt pm full hf; omega
        dsimp [stepBM]
        have hfire_false : ¬((R1.any (fun r => (a &&& r) == a) && R1.any (fun r => (b &&& r) == b)) = true) := by
          rw [Bool.and_eq_true]; exact hnotab
        rw [if_neg hfire_false]
        exact hR1_no
      · apply finish_from_arc 4544 arc_4544
        change full ∉ L.foldl stepBM (initMasks 4544)
        rw [hL_split, List.foldl_append, List.foldl_cons]
        apply stepBM_no_full L2 _ hL2_ne
        have h17 : (L1 ++ [(a, b)]).length ≤ 17 := by
          simp only [List.length_append, List.length_singleton]; omega
        have hbase := base18 (L1 ++ [(a, b)]) h17
        simpa only [List.foldl_append, List.foldl_cons, List.foldl_nil] using hbase
