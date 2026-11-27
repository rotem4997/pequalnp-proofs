import PEqualNP.Defs

-- The first seven lines carry the synthesis problem. Each of the six remaining
-- lines can be appended as four incident point inputs joined by three OR gates,
-- one AND with its line input and one OR with the preceding output.
theorem PEqualNP.Outside.R_meta_2401_347
  (hlocal :
    let offsets : Finset (Fin 13) := {0, 1, 3, 9}
    let I := fun p l : Fin 13 => ∃ d ∈ offsets, p = l + d
    let feed : (Fin 26 → Bool) → Fin 27 → Bool := fun x => Fin.lastCases (x 0 || x 1) x
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 27 C ∧
      C.size ≤ 32 ∧ C.output < 27 + C.size ∧
      (∀ p l : Fin 13, l.val < 7 → I p l →
        PEqualNP.MetaComplexity.circuitFun 27 C (feed fun i =>
          decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) ∧
      ∀ x : Fin 26 → Bool,
        (∀ p l : Fin 13, I p l → x (Fin.castAdd 13 p) = true → x (Fin.natAdd 13 l) ≠ true) →
        (¬ ∃ l : Fin 13, ∀ p, x (Fin.castAdd 13 p) = true → I p l) →
        (¬ ∃ p : Fin 13, ∀ l, x (Fin.natAdd 13 l) = true → I p l) →
        PEqualNP.MetaComplexity.circuitFun 27 C (feed x) = false)
  (hfinish :
    let offsets : Finset (Fin 13) := {0, 1, 3, 9}
    let I := fun p l : Fin 13 => ∃ d ∈ offsets, p = l + d
    let feed : (Fin 26 → Bool) → Fin 27 → Bool := fun x => Fin.lastCases (x 0 || x 1) x
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack 27 C →
      C.output < 27 + C.size →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 27 D ∧
        D.size ≤ C.size + 30 ∧
        ∀ x : Fin 26 → Bool, PEqualNP.MetaComplexity.circuitFun 27 D (feed x) = true ↔
          PEqualNP.MetaComplexity.circuitFun 27 C (feed x) = true ∨ ∃ p l : Fin 13,
            7 ≤ l.val ∧ I p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) :
    ∃ (x1 : Fin (4 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x2 ∧     PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x2 ∧       x2.size ≤ (62 : ℕ) ∧         have x3 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x4 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x4 x5 : Fin (13 : ℕ)) => ∃ x6 ∈ x3, x4 = x5 + x6;         have x5 : Fin (26 : ℕ) := if ↑x1 = (1 : ℕ) then (1 : Fin (26 : ℕ)) else if ↑x1 = (3 : ℕ) then (14 : Fin (26 : ℕ)) else (13 : Fin (26 : ℕ));         have x6 : Bool := Decidable.decide (↑x1 = (0 : ℕ));         have x7 : (Fin (26 : ℕ) → Bool) → Fin (27 : ℕ) → Bool := fun (x7 : Fin (26 : ℕ) → Bool) (x8 : Fin ((26 : ℕ) + (1 : ℕ))) => Fin.lastCases (if x6 = Bool.true then x7 (0 : Fin (26 : ℕ)) && x7 x5 else x7 (0 : Fin (26 : ℕ)) || x7 x5) x7 x8;         (∀ (x8 x9 : Fin (13 : ℕ)), x4 x8 x9 → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x2 (x7 fun (x11 : Fin (26 : ℕ)) => Decidable.decide (x11 = Fin.castAdd (13 : ℕ) x8 ∨ x11 = Fin.natAdd (13 : ℕ) x9)) = Bool.true) ∧           ∀ (x8 : Finset (Fin (13 : ℕ))),             have x9 : Fin (13 : ℕ) → Prop := fun (x9 : Fin (13 : ℕ)) => ∀ x10 ∈ x8, ¬x4 x10 x9;             (∀ x10 ∉ x8, ∃ (x12 : Fin (13 : ℕ)), x9 x12 ∧ x4 x10 x12) → ((¬∃ (x11 : Fin (13 : ℕ)), ∀ x12 ∈ x8, x4 x12 x11) ∧ ¬∃ (x11 : Fin (13 : ℕ)), ∀ (x12 : Fin (13 : ℕ)), x9 x12 → x4 x11 x12) → ∀ (x12 : Fin (26 : ℕ) → Bool), (∀ (x13 : Fin (26 : ℕ)), x12 x13 = Bool.true ↔ (∃ x14 ∈ x8, x13 = Fin.castAdd (13 : ℕ) x14) ∨ ∃ (x14 : Fin (13 : ℕ)), x13 = Fin.natAdd (13 : ℕ) x14 ∧ x9 x14) → PEqualNP.MetaComplexity.circuitFun (27 : ℕ) x2 (x7 x12) = Bool.false := by
  let I := fun p l : Fin 13 => ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + d
  let feed : (Fin 26 → Bool) → Fin 27 → Bool := fun x => Fin.lastCases (x 0 || x 1) x
  obtain ⟨C, hC, hbC, hsC, validOutput, hpC, hnC⟩ := hlocal
  obtain ⟨D, hD, hbD, hsD, evalD⟩ := hfinish C hC hbC validOutput
  refine ⟨1, D, hD, hbD, by omega, ?_⟩
  constructor
  · intro p l hI
    let x := fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)
    change PEqualNP.MetaComplexity.circuitFun 27 D (feed x) = true
    apply (evalD x).mpr
    by_cases hl : l.val < 7
    · exact Or.inl (hpC p l hl hI)
    · exact Or.inr ⟨p, l, by omega, hI, by simp [x], by simp [x]⟩
  · intro A missed _ generic x hx
    let miss := fun l : Fin 13 => ∀ p ∈ A, ¬ I p l
    have disjointWires (p l : Fin 13) : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
      intro h
      have e := congrArg Fin.val h
      change p.val = 13 + l.val at e
      omega
    have points (p : Fin 13) : x (Fin.castAdd 13 p) = true ↔ p ∈ A := by
      rw [hx]
      constructor
      · rintro (⟨q, hq, e⟩ | ⟨l, e, _⟩)
        · have eqv : p = q := Fin.ext (congrArg (fun i : Fin 26 => i.val) e)
          exact eqv ▸ hq
        · exact ((disjointWires p l) e).elim
      · intro hp
        exact Or.inl ⟨p, hp, rfl⟩
    have lines (l : Fin 13) : x (Fin.natAdd 13 l) = true ↔ miss l := by
      rw [hx]
      constructor
      · rintro (⟨p, _, e⟩ | ⟨k, e, hk⟩)
        · exact ((disjointWires p l) e.symm).elim
        · have ev := congrArg Fin.val e
          change 13 + l.val = 13 + k.val at ev
          have eqv : l = k := Fin.ext (by omega)
          exact eqv ▸ hk
      · intro hl
        exact Or.inr ⟨l, rfl, hl⟩
    have noEdge (p l : Fin 13) (hi : I p l) (hp : x (Fin.castAdd 13 p) = true)
        (hl : x (Fin.natAdd 13 l) = true) : False :=
      (lines l).mp hl p ((points p).mp hp) hi
    have notLine : ¬ ∃ l : Fin 13, ∀ p, x (Fin.castAdd 13 p) = true → I p l := by
      rintro ⟨l, h⟩
      exact generic.1 ⟨l, fun p hp => h p ((points p).mpr hp)⟩
    have notPencil : ¬ ∃ p : Fin 13, ∀ l, x (Fin.natAdd 13 l) = true → I p l := by
      rintro ⟨p, h⟩
      exact generic.2 ⟨p, fun l hl => h l ((lines l).mpr hl)⟩
    have hneg := hnC x noEdge notLine notPencil
    have outside : ¬ ∃ p l : Fin 13, 7 ≤ l.val ∧ I p l ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
      rintro ⟨p, l, _, hi, hp, hl⟩
      exact noEdge p l hi hp hl
    change PEqualNP.MetaComplexity.circuitFun 27 D (feed x) = false
    cases result : PEqualNP.MetaComplexity.circuitFun 27 D (feed x) with
    | false => rfl
    | true =>
      rcases (evalD x).mp result with holds | hit
      · rw [hneg] at holds
        contradiction
      · exact (outside hit).elim
