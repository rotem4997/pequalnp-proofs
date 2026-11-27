import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A first-gate cut: constant and copy circuits cannot accept every incident pair,
-- so a size-at-most-63 monotone circuit that does so has a first AND or a first OR.
theorem PEqualNP.Outside.R_meta_4071_1
    (hAND :
      let I := fun (p l : Fin 13) => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let EL := fun (P : Finset (Fin 13)) => Finset.univ.filter (fun l => ∀ p ∈ P, ¬ I p l)
      let EP := fun (L : Finset (Fin 13)) => Finset.univ.filter (fun p => ∀ l ∈ L, ¬ I p l)
      let CP := fun (P : Finset (Fin 13)) => ∀ l : Fin 13, {p ∈ P | I p l}.card ≤ 2
      let CL := fun (L : Finset (Fin 13)) => ∀ p : Fin 13, {l ∈ L | I p l}.card ≤ 2
      let row := fun (P L : Finset (Fin 13)) (i : Fin 26) =>
        Fin.addCases (motive := fun _ => Bool)
          (fun p : Fin 13 => decide (p ∈ P)) (fun l : Fin 13 => decide (l ∈ L)) i
      ∀ C : Circuit, Monotone2 C → C.size ≤ 63 →
        (∀ g : Gate, ∀ M : List Gate, C.gates = g :: M → g.op = GateOp.and) →
        (∀ p l : Fin 13, I p l →
          circuitFun 26 C (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) →
        (∃ P : Finset (Fin 13), P.card = 4 ∧ CP P ∧ circuitFun 26 C (row P (EL P)) = true) ∨
        (∃ L : Finset (Fin 13), L.card = 4 ∧ CL L ∧ circuitFun 26 C (row (EP L) L) = true))
    (hOR :
      let I := fun (p l : Fin 13) => p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9
      let EL := fun (P : Finset (Fin 13)) => Finset.univ.filter (fun l => ∀ p ∈ P, ¬ I p l)
      let EP := fun (L : Finset (Fin 13)) => Finset.univ.filter (fun p => ∀ l ∈ L, ¬ I p l)
      let CP := fun (P : Finset (Fin 13)) => ∀ l : Fin 13, {p ∈ P | I p l}.card ≤ 2
      let CL := fun (L : Finset (Fin 13)) => ∀ p : Fin 13, {l ∈ L | I p l}.card ≤ 2
      let row := fun (P L : Finset (Fin 13)) (i : Fin 26) =>
        Fin.addCases (motive := fun _ => Bool)
          (fun p : Fin 13 => decide (p ∈ P)) (fun l : Fin 13 => decide (l ∈ L)) i
      ∀ C : Circuit, Monotone2 C → C.size ≤ 63 →
        (∀ g : Gate, ∀ M : List Gate, C.gates = g :: M → g.op = GateOp.or) →
        (∀ p l : Fin 13, I p l →
          circuitFun 26 C (fun i => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) = true) →
        (∃ P : Finset (Fin 13), P.card = 4 ∧ CP P ∧ circuitFun 26 C (row P (EL P)) = true) ∨
        (∃ L : Finset (Fin 13), L.card = 4 ∧ CL L ∧ circuitFun 26 C (row (EP L) L) = true)) :
    let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x2 : Finset (Fin (13 : ℕ))) => {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x2, ¬x1 x4 x3}; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x3 : Finset (Fin (13 : ℕ))) => {x4 : Fin (13 : ℕ) | ∀ x5 ∈ x3, ¬x1 x4 x5}; have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x1 x6 x5}.card ≤ (2 : ℕ); have x5 : Finset (Fin (13 : ℕ)) → Prop := fun (x5 : Finset (Fin (13 : ℕ))) => ∀ (x6 : Fin (13 : ℕ)), (Finset.filter (x1 x6) x5).card ≤ (2 : ℕ); have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => Fin.addCases (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x6)) (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x7)) x8; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x7.size ≤ (63 : ℕ) → (∀ (x10 x11 : Fin (13 : ℕ)), x1 x10 x11 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 fun (x13 : Fin (26 : ℕ)) => Decidable.decide (x13 = Fin.castAdd (13 : ℕ) x10 ∨ x13 = Fin.natAdd (13 : ℕ) x11)) = Bool.true) → (∃ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) ∧ x4 x11 ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x6 x11 (x2 x11)) = Bool.true) ∨ ∃ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) ∧ x5 x11 ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x6 (x3 x11) x11) = Bool.true := by
  dsimp only
  intro C hmono hsz hacc
  cases hgs : C.gates with
  | nil =>
    exfalso
    have hw (x : Fin 26 → Bool) :
        circuitFun 26 C x = (List.ofFn x).getD C.output false := by
      change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn x)).getD C.output false = (List.ofFn x).getD C.output false
      rw [hgs, List.foldl_nil]
    have b00 := hacc (0 : Fin 13) 0 (Or.inl rfl)
    have b11 := hacc (1 : Fin 13) 1 (Or.inl rfl)
    rw [hw] at b00 b11
    by_cases ho : C.output < 26
    · have hget (x : Fin 26 → Bool) :
          (List.ofFn x).getD C.output false = x ⟨C.output, ho⟩ := by
        have hlen : C.output < (List.ofFn x).length := by
          simpa using ho
        rw [List.getD_eq_getElem (l := List.ofFn x) (n := C.output) false hlen]
        exact List.getElem_ofFn (f := x) hlen
      rw [hget] at b00 b11
      -- flag (0,0) is true only at wires 0 and 13; flag (1,1) only at 1 and 14
      have f00 : (fun i : Fin 26 =>
          decide (i = Fin.castAdd 13 (0 : Fin 13) ∨ i = Fin.natAdd 13 (0 : Fin 13)))
            ⟨C.output, ho⟩ = true := b00
      have f11 : (fun i : Fin 26 =>
          decide (i = Fin.castAdd 13 (1 : Fin 13) ∨ i = Fin.natAdd 13 (1 : Fin 13)))
            ⟨C.output, ho⟩ = true := b11
      have e00 : C.output = 0 ∨ C.output = 13 := by
        have := of_decide_eq_true f00
        rcases this with h | h
        · have : C.output = (Fin.castAdd 13 (0 : Fin 13)).val := Fin.val_eq_of_eq h
          exact Or.inl (by simpa using this)
        · have : C.output = (Fin.natAdd 13 (0 : Fin 13)).val := Fin.val_eq_of_eq h
          exact Or.inr (by simpa using this)
      have e11 : C.output = 1 ∨ C.output = 14 := by
        have := of_decide_eq_true f11
        rcases this with h | h
        · have : C.output = (Fin.castAdd 13 (1 : Fin 13)).val := Fin.val_eq_of_eq h
          exact Or.inl (by simpa using this)
        · have : C.output = (Fin.natAdd 13 (1 : Fin 13)).val := Fin.val_eq_of_eq h
          exact Or.inr (by simpa using this)
      omega
    · have hdef (x : Fin 26 → Bool) :
          (List.ofFn x).getD C.output false = false :=
        List.getD_eq_default _ _ (by simp; omega)
      rw [hdef] at b00
      exact Bool.false_ne_true b00
  | cons g M =>
    have hin : g ∈ C.gates := by simp [hgs]
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
      have := (hmono g hin).1
      simpa using this
    rcases hop with hand | hor
    · apply hAND C hmono hsz ?_ hacc
      intro g' M' hg'
      have : g' = g := by
        rw [hgs] at hg'; cases hg'; rfl
      simp [this, hand]
    · apply hOR C hmono hsz ?_ hacc
      intro g' M' hg'
      have : g' = g := by
        rw [hgs] at hg'; cases hg'; rfl
      simp [this, hor]

