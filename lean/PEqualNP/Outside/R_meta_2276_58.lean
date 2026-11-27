import PEqualNP.Defs

-- Twenty edges, thirty-seven maximal independent sets, and the excluded edge.
-- A witness with at most twenty-four gates would satisfy the encoding on these rows.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2276_58
    (encode : ∀ (rows : List Nat) (g : Nat → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ r ∈ rows, r < 2 ^ 14) → PEqualNP.MetaComplexity.Monotone2 C → C.size ≤ 24 →
      (∀ r ∈ rows, C.eval (List.ofFn (fun i : Fin 14 => r.testBit i.val)) = g r) →
      PEqualNP.Defs.LratEncoding.FormulaSat (PEqualNP.Defs.LratEncoding.enc 14 24 g rows))
    (noSmallModel :
      let pos : List Nat := [257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112]
      let neg : List Nat := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256, 129]
      ¬ PEqualNP.Defs.LratEncoding.FormulaSat
        (PEqualNP.Defs.LratEncoding.enc 14 24 (fun r => decide (r ∈ pos)) (pos ++ neg))) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))]; have x2 : (Fin (14 : ℕ) → Bool) → Prop := fun (x2 : Fin (14 : ℕ) → Bool) => ∃ (x3 : Fin (14 : ℕ)) (x4 : Fin (14 : ℕ)), (↑x3, ↑x4) ∈ x1 ∧ x2 x3 = Bool.true ∧ x2 x4 = Bool.true; have x3 : (Fin (14 : ℕ) → Bool) → Prop := fun (x3 : Fin (14 : ℕ) → Bool) => (x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.true → ¬x2 (Function.update x3 x4 Bool.false)) ∨ ¬x2 x3 ∧ ∀ (x4 : Fin (14 : ℕ)), x3 x4 = Bool.false → x2 (Function.update x3 x4 Bool.true); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x6 : Fin (14 : ℕ) → Bool), x3 x6 → x6 (0 : Fin (14 : ℕ)) = Bool.false ∨ x6 (7 : Fin (14 : ℕ)) = Bool.false → (x4.eval (List.ofFn x6) = Bool.true ↔ x2 x6)) → x4.eval (List.ofFn fun (x7 : Fin (14 : ℕ)) => Decidable.decide (x7 = (0 : Fin (14 : ℕ)) ∨ x7 = (7 : Fin (14 : ℕ)))) = Bool.false → (25 : ℕ) ≤ x4.size := by
  let edges : List (Nat × Nat) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
  let E := fun x : Fin 14 → Bool => ∃ a b : Fin 14, (a.val, b.val) ∈ edges ∧ x a = true ∧ x b = true
  let B := fun x : Fin 14 → Bool =>
    (E x ∧ ∀ i : Fin 14, x i = true → ¬E (Function.update x i false)) ∨
    (¬E x ∧ ∀ i : Fin 14, x i = false → E (Function.update x i true))
  change ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin 14 → Bool, B x → (x 0 = false ∨ x 7 = false) →
      (C.eval (List.ofFn x) = true ↔ E x)) →
    C.eval (List.ofFn (fun i : Fin 14 => decide (i = 0 ∨ i = 7))) = false → 25 ≤ C.size
  intro C hmono onBoundary hpair
  by_contra hsmall
  have hsize : C.size ≤ 24 := by omega
  let evalRow := fun x : Fin 14 → Bool => C.eval (List.ofFn x)
  have special : evalRow (fun i : Fin 14 => decide (i = 0 ∨ i = 7)) = false := hpair
  let pos : List Nat := [257, 1025, 130, 514, 8194, 260, 4100, 8196, 136, 2056, 4104, 1040, 2064, 8208, 544, 1056, 4128, 320, 576, 2112]
  let neg : List Nat := [127, 244, 314, 432, 541, 660, 792, 1102, 1220, 1290, 1548, 2087, 2212, 2338, 2565, 3078, 3716, 4179, 4304, 4370, 4625, 5008, 5186, 6147, 7426, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656, 12353, 13504, 14849, 16256, 129]
  let rows := pos ++ neg
  let bits := fun (m : Nat) (i : Fin 14) => m.testBit i.val

  have rowValue (m : Nat) (hm : m ∈ rows) :
      evalRow (bits m) = decide (m ∈ pos) := by
    by_cases h129 : m = 129
    · subst m
      have matchBits : bits 129 = (fun i : Fin 14 => decide (i = 0 ∨ i = 7)) := by
        funext i
        exact (by decide : ∀ j : Fin 14, bits 129 j = decide (j = 0 ∨ j = 7)) i
      rw [matchBits, special]
      decide
    · let es : List (Fin 14 × Fin 14) := [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]
      let fast := fun x : Fin 14 → Bool => es.any (fun p => x p.1 && x p.2) = true
      have es_iff : ∀ a b : Fin 14, (a,b) ∈ es ↔ (a.val,b.val) ∈ edges := by decide +kernel
      have agrees (x : Fin 14 → Bool) : fast x ↔ E x := by
        change (es.any (fun p => x p.1 && x p.2) = true) ↔ _
        rw [List.any_eq_true]
        constructor
        · rintro ⟨⟨a, b⟩, hab, hx⟩
          exact ⟨a, b, (es_iff a b).mp hab, (Bool.and_eq_true_iff.mp hx).1, (Bool.and_eq_true_iff.mp hx).2⟩
        · rintro ⟨a, b, hab, ha, hb⟩
          exact ⟨(a,b), (es_iff a b).mpr hab, Bool.and_eq_true_iff.mpr ⟨ha,hb⟩⟩
      let boundary := fun x : Fin 14 → Bool =>
        (fast x ∧ ∀ i : Fin 14, x i = true → ¬fast (Function.update x i false)) ∨
        (¬fast x ∧ ∀ i : Fin 14, x i = false → fast (Function.update x i true))
      have table : ∀ n ∈ rows, n ≠ 129 →
          boundary (bits n) ∧ ((bits n) 0 = false ∨ (bits n) 7 = false) ∧
            (fast (bits n) ↔ n ∈ pos) := by decide +kernel
      obtain ⟨hb, hc, hv⟩ := table m hm h129
      have bd : B (bits m) := by
        simpa only [boundary, B, agrees] using hb
      have result := (onBoundary (bits m) bd hc).trans ((agrees _).symm.trans hv)
      exact Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using result)

  apply noSmallModel
  exact encode rows (fun r => decide (r ∈ pos)) C (by decide +kernel) hmono hsize rowValue
