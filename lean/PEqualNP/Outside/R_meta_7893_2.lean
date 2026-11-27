import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_7893_2
    (h16 : ∀ (x1 : Circuit) (x2 : ℕ), PEqualNP.TopForm.IsAO2 10 x1 → x1.size = 16 →
      (10 ≤ x2 ∧ x2 < 10 + x1.size ∧ ∀ (x5 : ℕ) (x6 : Gate), 10 + x5 ≤ x2 → x1.gates[x5]? = some x6 → 0 ∉ x6.inputs) →
      let x6 : ℕ → Fin 10 → Bool := fun x6 x7 => x6.testBit ↑x7
      let x7 : ℕ → Bool := fun x7 => (x1.wires (List.ofFn (Function.update (x6 x7) 0 false))).getD x2 false
      let x8 : ℕ → Bool := fun x8 => circuitFun 10 x1 (Function.update (x6 x8) 0 (x6 x8 0 || x7 x8))
      (∀ x9 ∈ ([50, 104, 116, 138, 208, 276, 402, 548, 554, 770] : List ℕ), x7 x9 = false) →
      ¬((∀ x10 ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640] : List ℕ), x8 x10 = true) ∧
        ∀ x10 ∈ ([50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] : List ℕ), x8 x10 = false))
    (h17 : ∀ (x1 : Circuit) (x2 : ℕ), PEqualNP.TopForm.IsAO2 10 x1 → x1.size = 17 →
      (10 ≤ x2 ∧ x2 < 10 + x1.size ∧ ∀ (x5 : ℕ) (x6 : Gate), 10 + x5 ≤ x2 → x1.gates[x5]? = some x6 → 0 ∉ x6.inputs) →
      let x6 : ℕ → Fin 10 → Bool := fun x6 x7 => x6.testBit ↑x7
      let x7 : ℕ → Bool := fun x7 => (x1.wires (List.ofFn (Function.update (x6 x7) 0 false))).getD x2 false
      let x8 : ℕ → Bool := fun x8 => circuitFun 10 x1 (Function.update (x6 x8) 0 (x6 x8 0 || x7 x8))
      (∀ x9 ∈ ([50, 104, 116, 138, 208, 276, 402, 548, 554, 770] : List ℕ), x7 x9 = false) →
      ¬((∀ x10 ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640] : List ℕ), x8 x10 = true) ∧
        ∀ x10 ∈ ([50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] : List ℕ), x8 x10 = false))
    (h18 : ∀ (x1 : Circuit) (x2 : ℕ), PEqualNP.TopForm.IsAO2 10 x1 → x1.size = 18 →
      (10 ≤ x2 ∧ x2 < 10 + x1.size ∧ ∀ (x5 : ℕ) (x6 : Gate), 10 + x5 ≤ x2 → x1.gates[x5]? = some x6 → 0 ∉ x6.inputs) →
      let x6 : ℕ → Fin 10 → Bool := fun x6 x7 => x6.testBit ↑x7
      let x7 : ℕ → Bool := fun x7 => (x1.wires (List.ofFn (Function.update (x6 x7) 0 false))).getD x2 false
      let x8 : ℕ → Bool := fun x8 => circuitFun 10 x1 (Function.update (x6 x8) 0 (x6 x8 0 || x7 x8))
      (∀ x9 ∈ ([50, 104, 116, 138, 208, 276, 402, 548, 554, 770] : List ℕ), x7 x9 = false) →
      ¬((∀ x10 ∈ ([3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640] : List ℕ), x8 x10 = true) ∧
        ∀ x10 ∈ ([50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773] : List ℕ), x8 x10 = false)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.TopForm.IsAO2 (10 : ℕ) x1 → (16 : ℕ) ≤ x1.size ∧ x1.size ≤ (18 : ℕ) → (x2 ≠ (0 : ℕ) ∧ x2 < (10 : ℕ) + x1.size ∧ ∀ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate), (10 : ℕ) + x5 ≤ x2 → x1.gates[x5]? = Option.some x6 → (0 : ℕ) ∉ x6.inputs) → have x6 : ℕ → Fin (10 : ℕ) → Bool := fun (x6 : ℕ) (x7 : Fin (10 : ℕ)) => x6.testBit ↑x7; have x7 : ℕ → Bool := fun (x7 : ℕ) => (x1.wires (List.ofFn (Function.update (x6 x7) (0 : Fin (10 : ℕ)) Bool.false))).getD x2 Bool.false; have x8 : ℕ → Bool := fun (x8 : ℕ) => PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x1 (Function.update (x6 x8) (0 : Fin (10 : ℕ)) (x6 x8 (0 : Fin (10 : ℕ)) || x7 x8)); (∀ x9 ∈ [(50 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (208 : ℕ), (276 : ℕ), (402 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ)], x7 x9 = Bool.false) → ¬((∀ x10 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ), (528 : ℕ), (576 : ℕ), (640 : ℕ)], x8 x10 = Bool.true) ∧ ∀ x10 ∈ [(50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ), (521 : ℕ), (548 : ℕ), (554 : ℕ), (770 : ℕ), (773 : ℕ)], x8 x10 = Bool.false) := by
  intro x1 x2 hAO hSize hW x6 x7 x8 hZero
  by_cases hlt : x2 < 10
  · exfalso
    have hWiresPrefix : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
        (gs.foldl (fun w' g => w' ++ [g.op.eval (g.inputs.map fun k => w'.getD k false)]) w).getD i false = w.getD i false := by
      intro gs
      induction gs with
      | nil => intro w i _; rfl
      | cons g gs ih =>
        intro w i hi
        simp only [List.foldl_cons]
        rw [ih _ _ (by simp; omega)]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        simp [List.getElem?_append_left hi]
    have hBit : ∀ n : ℕ, x7 n = n.testBit x2 := by
      intro n
      dsimp [x7, Circuit.wires]
      rw [hWiresPrefix _ _ _ (by simp [hlt])]
      rw [List.getD_eq_getElem?_getD]
      simp only [List.getElem?_ofFn, hlt, ↓reduceDIte, Option.getD_some]
      have hne : (⟨x2, hlt⟩ : Fin 10) ≠ 0 := by
        intro h
        exact hW.1 (Fin.ext_iff.mp h)
      simp [Function.update_of_ne hne, x6]
    have hFalse : ∀ b : Fin 9,
        ∃ n ∈ ([50, 104, 116, 138, 208, 276, 402, 548, 554, 770] : List ℕ), n.testBit (b.1 + 1) = true := by
      decide
    rcases hFalse ⟨x2 - 1, by have := hW.1; omega⟩ with ⟨n, hn, htrue⟩
    have hEq : (x2 - 1) + 1 = x2 := Nat.sub_add_cancel (Nat.pos_of_ne_zero hW.1)
    rw [hEq] at htrue
    have := hZero n hn
    rw [hBit n, htrue] at this
    cases this
  · have hge : 10 ≤ x2 := Nat.le_of_not_lt hlt
    have hW' : 10 ≤ x2 ∧ x2 < 10 + x1.size ∧ ∀ x5 x6, 10 + x5 ≤ x2 → x1.gates[x5]? = some x6 → 0 ∉ x6.inputs :=
      ⟨hge, hW.2.1, hW.2.2⟩
    rcases hSize with ⟨h1, h2⟩
    have hCases : x1.size = 16 ∨ x1.size = 17 ∨ x1.size = 18 := by omega
    rcases hCases with hs | hs | hs
    · exact h16 x1 x2 hAO hs hW' hZero
    · exact h17 x1 x2 hAO hs hW' hZero
    · exact h18 x1 x2 hAO hs hW' hZero
