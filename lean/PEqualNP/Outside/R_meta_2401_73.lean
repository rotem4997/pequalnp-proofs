import PEqualNP.Defs

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_2401_73
    (classify : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => ∃ x4 ∈ x1, x2 = x3 + x4; have x3 : List (ℕ × ℕ) := [((7 : ℕ), (904 : ℕ)), ((13 : ℕ), (2848 : ℕ)), ((19 : ℕ), (708 : ℕ)), ((21 : ℕ), (2720 : ℕ)), ((25 : ℕ), (2656 : ℕ)), ((37 : ℕ), (2440 : ℕ)), ((41 : ℕ), (2370 : ℕ)), ((133 : ℕ), (808 : ℕ))]; have x4 : ℕ × ℕ → Fin (13 : ℕ) → Fin (13 : ℕ) → Bool → Fin ((13 : ℕ) + (13 : ℕ)) → Bool := fun (x4 : ℕ × ℕ) (x5 x6 : Fin (13 : ℕ)) (x7 : Bool) =>   have x8 : ℕ → ℕ → Fin (13 : ℕ) → Bool := fun (x8 x9 : ℕ) (x10 : Fin (13 : ℕ)) => if x7 = Bool.true then x9.testBit ↑(-(x5 * x10 + x6)) else x8.testBit ↑(x5 * x10 + x6);   Fin.append (x8 x4.1 x4.2) (x8 x4.2 x4.1); ∀ (x5 : Finset (Fin (13 : ℕ))),   let x6 : Fin (13 : ℕ) → Prop := fun (x6 : Fin (13 : ℕ)) => ∀ x7 ∈ x5, ¬x2 x7 x6;   (∀ x7 ∉ x5, ∃ (x9 : Fin (13 : ℕ)), x6 x9 ∧ x2 x7 x9) → ((¬∃ (x8 : Fin (13 : ℕ)), ∀ x9 ∈ x5, x2 x9 x8) ∧ ¬∃ (x8 : Fin (13 : ℕ)), ∀ (x9 : Fin (13 : ℕ)), x6 x9 → x2 x8 x9) → ∃ x9 ∈ x3, ∃ x10 ∈ [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))], ∃ (x11 : Fin (13 : ℕ)) (x12 : Bool), (fun (x13 : Fin ((13 : ℕ) + (13 : ℕ))) => Decidable.decide ((∃ x14 ∈ x5, x13 = Fin.castAdd (13 : ℕ) x14) ∨ ∃ (x14 : Fin (13 : ℕ)), x13 = Fin.natAdd (13 : ℕ) x14 ∧ x6 x14)) = x4 x9 x10 x11 x12)
    (search : ∃ (q : Fin 4) (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.Monotone2 C ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack 27 C ∧ C.size ≤ 62 ∧
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let I := fun (p l : Fin 13) => ∃ d ∈ D, p = l + d
      let j : Fin 26 := if q.val = 1 then 1 else if q.val = 3 then 14 else 13
      let useAnd := decide (q.val = 0)
      let aug := fun (x : Fin 26 → Bool) =>
        Fin.lastCases (if useAnd = true then x 0 && x j else x 0 || x j) x
      let reps : List (ℕ × ℕ) := [(7, 904), (13, 2848), (19, 708), (21, 2720), (25, 2656), (37, 2440), (41, 2370), (133, 808)]
      let row := fun (z : ℕ × ℕ) (m t : Fin 13) (dual : Bool) =>
        let bit := fun (a b : ℕ) (i : Fin 13) =>
          if dual = true then b.testBit (-(m * i + t)).val else a.testBit (m * i + t).val
        Fin.append (bit z.1 z.2) (bit z.2 z.1)
      (∀ p l : Fin 13, I p l → PEqualNP.MetaComplexity.circuitFun 27 C
        (aug (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l))) = true) ∧
      ∀ z ∈ reps, ∀ m ∈ ([1, 3, 9] : List (Fin 13)), ∀ t : Fin 13, ∀ dual : Bool,
        PEqualNP.MetaComplexity.circuitFun 27 C (aug (row z m t dual)) = false) :
    ∃ (x1 : Fin (4 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 ∧     PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x2 ∧       x2.size ≤ (62 : ℕ) ∧         have x3 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x4 x5 : Fin (13 : ℕ)) => ∃ x6 ∈ x3, x4 = x5 + x6;         have x5 : Fin (26 : ℕ) := if ↑x1 = (1 : ℕ) then (1 : Fin (26 : ℕ)) else if ↑x1 = (3 : ℕ) then (14 : Fin (26 : ℕ)) else (13 : Fin (26 : ℕ));         have x6 : Bool := Decidable.decide (↑x1 = (0 : ℕ));         have x7 : (Fin (26 : ℕ) → Bool) → Fin (27 : ℕ) → Bool := fun (x7 : Fin (26 : ℕ) → Bool) (x8 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (if x6 = Bool.true then x7 (0 : Fin (26 : ℕ)) && x7 x5 else x7 (0 : Fin (26 : ℕ)) || x7 x5) x7 x8;         (∀ (x8 x9 : Fin (13 : ℕ)), x4 x8 x9 → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x2 (x7 fun (x11 : Fin (26 : ℕ)) => Decidable.decide (x11 = Fin.castAdd (13 : ℕ) x8 ∨ x11 = Fin.natAdd (13 : ℕ) x9)) = Bool.true) ∧           ∀ (x8 : Finset (Fin (13 : ℕ))),             have x9 : Fin (13 : ℕ) → Prop := fun (x9 : Fin (13 : ℕ)) => ∀ x10 ∈ x8, ¬x4 x10 x9;             (∀ x10 ∉ x8, ∃ (x12 : Fin (13 : ℕ)), x9 x12 ∧ x4 x10 x12) → ((¬∃ (x11 : Fin (13 : ℕ)), ∀ x12 ∈ x8, x4 x12 x11) ∧ ¬∃ (x11 : Fin (13 : ℕ)), ∀ (x12 : Fin (13 : ℕ)), x9 x12 → x4 x11 x12) → ∀ (x12 : Fin (26 : ℕ) → Bool), (∀ (x13 : Fin (26 : ℕ)), x12 x13 = Bool.true ↔ (∃ x14 ∈ x8, x13 = Fin.castAdd (13 : ℕ) x14) ∨ ∃ (x14 : Fin (13 : ℕ)), x13 = Fin.natAdd (13 : ℕ) x14 ∧ x9 x14) → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x2 (x7 x12) = Bool.false := by
  obtain ⟨q, C, mono, back, size, positive, negative⟩ := search
  let j : Fin 26 := if q.val = 1 then 1 else if q.val = 3 then 14 else 13
  let useAnd := decide (q.val = 0)
  let aug : (Fin 26 → Bool) → Fin 27 → Bool := fun x =>
    Fin.lastCases (if useAnd = true then x 0 && x j else x 0 || x j) x
  let reps : List (ℕ × ℕ) := [(7, 904), (13, 2848), (19, 708), (21, 2720), (25, 2656), (37, 2440), (41, 2370), (133, 808)]
  let row : (ℕ × ℕ) → Fin 13 → Fin 13 → Bool → Fin 26 → Bool := fun z m t dual =>
    let bit := fun (a b : ℕ) (i : Fin 13) =>
      if dual = true then b.testBit (-(m * i + t)).val else a.testBit (m * i + t).val
    Fin.append (bit z.1 z.2) (bit z.2 z.1)
  have rejects : ∀ z ∈ reps, ∀ m ∈ ([1, 3, 9] : List (Fin 13)), ∀ t : Fin 13, ∀ dual : Bool,
      PEqualNP.MetaComplexity.circuitFun 27 C (aug (row z m t dual)) = false := negative
  refine ⟨q, C, mono, back, size, positive, ?_⟩
  intro P miss closed generic x pattern
  obtain ⟨z, hz, m, hm, t, dual, represented⟩ := classify P closed generic
  have same : x = (fun k => decide ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨
      ∃ l : Fin 13, k = Fin.natAdd 13 l ∧ miss l)) := by
    funext k
    apply Bool.eq_iff_iff.mpr
    exact (pattern k).trans decide_eq_true_iff.symm
  change PEqualNP.MetaComplexity.circuitFun 27 C (aug x) = false
  rw [same, represented]
  exact rejects z hz m hm t dual
