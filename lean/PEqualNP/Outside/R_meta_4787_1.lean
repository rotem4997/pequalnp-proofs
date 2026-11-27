import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4787_1
    (normalize :
      ∀ C : Circuit, Monotone2 C →
        ∃ D : Circuit, Monotone2 D ∧ D.size = C.size ∧
          (∀ i : Fin D.gates.length, (D.gates.get i).inputs.length = 2 ∧
            ∀ j ∈ (D.gates.get i).inputs, j < 28 + i.val) ∧
          ∀ x : Fin 26 → Bool,
            D.wires (List.ofFn x ++ [true, false]) = C.wires (List.ofFn x ++ [true, false]))
    (boundForBinaryBackwards : let x1 : Type := Fin (13 : ℕ); have x2 : Finset x1 := {(0 : x1), (1 : x1), (3 : x1), (9 : x1)}; let x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => ∃ x5 ∈ x2, x3 = x4 + x5; let x4 : Finset x1 → x1 → Prop := fun (x4 : Finset x1) (x5 : x1) => ∀ x6 ∈ x4, ¬x3 x6 x5; let x5 : Type := Fin (26 : ℕ) → Bool; have x6 : x1 → x1 → x5 := fun (x6 x7 : x1) (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x6 ∨ x8 = Fin.natAdd (13 : ℕ) x7); have x7 : Finset x1 → x5 := fun (x7 : Finset x1) (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x7, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x4 x7 x9); have x8 : Finset x1 → Prop := fun (x8 : Finset x1) => (∀ x9 ∉ x8, ∃ (x11 : x1), x4 x8 x11 ∧ x3 x9 x11) ∧ ((∃ (x9 : x1), ∀ x10 ∈ x8, x3 x10 x9) ∨ ∃ (x9 : x1), ∀ (x10 : x1), x4 x8 x10 → x3 x9 x10); ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x9 →     x9.size ≤ (60 : ℕ) → (∀ i : Fin x9.gates.length,
          (x9.gates.get i).inputs.length = 2 ∧
          ∀ j ∈ (x9.gates.get i).inputs, j < 28 + i.val) →       have x12 : ℕ → x5 → Bool := fun (x12 : ℕ) (x13 : x5) => (x9.wires (List.ofFn x13 ++ [Bool.true, Bool.false])).getD x12 Bool.false;       have x13 : (x5 → Bool) → Prop := fun (x13 : x5 → Bool) => ∀ (x14 x15 : x1), x3 x14 x15 → x13 (x6 x14 x15) = Bool.true;       ∀ (x14 x15 : Fin (28 + x9.size)), x14 ≠ x15 → (x13 fun (x16 : x5) => x12 x14 x16 || x12 x15 x16) → ¬x13 (x12 x14) → ¬x13 (x12 x15) → (∀ (x19 : Finset x1), x8 x19 → ¬(x12 x14 (x7 x19) || x12 x15 (x7 x19)) = Bool.true) → False) :
    let x1 : Type := Fin (13 : ℕ); have x2 : Finset x1 := {(0 : x1), (1 : x1), (3 : x1), (9 : x1)}; let x3 : x1 → x1 → Prop := fun (x3 x4 : x1) => ∃ x5 ∈ x2, x3 = x4 + x5; let x4 : Finset x1 → x1 → Prop := fun (x4 : Finset x1) (x5 : x1) => ∀ x6 ∈ x4, ¬x3 x6 x5; let x5 : Type := Fin (26 : ℕ) → Bool; have x6 : x1 → x1 → x5 := fun (x6 x7 : x1) (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = Fin.castAdd (13 : ℕ) x6 ∨ x8 = Fin.natAdd (13 : ℕ) x7); have x7 : Finset x1 → x5 := fun (x7 : Finset x1) (x8 : Fin (26 : ℕ)) => Decidable.decide ((∃ x9 ∈ x7, x8 = Fin.castAdd (13 : ℕ) x9) ∨ ∃ (x9 : Fin (13 : ℕ)), x8 = Fin.natAdd (13 : ℕ) x9 ∧ x4 x7 x9); have x8 : Finset x1 → Prop := fun (x8 : Finset x1) => (∀ x9 ∉ x8, ∃ (x11 : x1), x4 x8 x11 ∧ x3 x9 x11) ∧ ((∃ (x9 : x1), ∀ x10 ∈ x8, x3 x10 x9) ∨ ∃ (x9 : x1), ∀ (x10 : x1), x4 x8 x10 → x3 x9 x10); ∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.Monotone2 x9 →     x9.size ≤ (60 : ℕ) →       have x12 : ℕ → x5 → Bool := fun (x12 : ℕ) (x13 : x5) => (x9.wires (List.ofFn x13 ++ [Bool.true, Bool.false])).getD x12 Bool.false;       have x13 : (x5 → Bool) → Prop := fun (x13 : x5 → Bool) => ∀ (x14 x15 : x1), x3 x14 x15 → x13 (x6 x14 x15) = Bool.true;       ∀ (x14 x15 : ℕ), (x13 fun (x16 : x5) => x12 x14 x16 || x12 x15 x16) → ¬x13 (x12 x14) → ¬x13 (x12 x15) → (∀ (x19 : Finset x1), x8 x19 → ¬(x12 x14 (x7 x19) || x12 x15 (x7 x19)) = Bool.true) → False := by
  intro F diff incident avoids Input pos neg degenerate C hMono hSize value covers a b
    hUnion hLeft hRight hReject
  obtain ⟨D, hDMono, hDSize, hShape, hWires⟩ := normalize C hMono
  have hBudget : D.size ≤ 60 := hDSize.le.trans hSize
  have fold_length (gs : List Gate) (w : List Bool) :
      (gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w).length =
        w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have size_wires (x : Input) : (C.wires (List.ofFn x ++ [true, false])).length = 28 + C.size := by
    change (C.gates.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)])
      (List.ofFn x ++ [true, false])).length = 28 + C.gates.length
    rw [fold_length]
    simp
  have beyond (i : ℕ) (hi : 28 + C.size ≤ i) (x : Input) : value i x = false := by
    change (C.wires (List.ofFn x ++ [true, false])).getD i false = false
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rwa [size_wires])]
    rfl
  have ha : a < 28 + C.size := by
    by_contra! h
    apply hRight
    intro p l hi
    simpa only [beyond a h, Bool.false_or] using hUnion p l hi
  have hb : b < 28 + C.size := by
    by_contra! h
    apply hLeft
    intro p l hi
    simpa only [beyond b h, Bool.or_false] using hUnion p l hi
  have hab : a ≠ b := by
    intro he
    subst b
    apply hLeft
    intro p l hi
    simpa only [Bool.or_self] using hUnion p l hi
  let a' : Fin (28 + D.size) := ⟨a, by simpa only [hDSize] using ha⟩
  let b' : Fin (28 + D.size) := ⟨b, by simpa only [hDSize] using hb⟩
  have hne : a' ≠ b' := fun h => hab (congrArg Fin.val h)
  apply boundForBinaryBackwards D hDMono hBudget hShape a' b' hne
  · simpa only [a', b', hWires] using hUnion
  · simpa only [a', hWires] using hLeft
  · simpa only [b', hWires] using hRight
  · simpa only [a', b', hWires] using hReject
