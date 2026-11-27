import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7426_1
    (restrictPin : ∀ (j : Fin 10) (f : Bool → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
      let run := fun x : Fin 10 → Bool => C.eval (List.ofFn x ++ [f (x j)])
      let pin : (Fin 9 → Bool) → Fin 10 → Bool := fun y => Fin.cases false y
      PEqualNP.MetaComplexity.FanInTwo C →
      (∃ a b : Fin 10 → Bool, (∀ i, i ≠ 0 → a i = b i) ∧ run a ≠ run b) →
      (∃ y z : Fin 9 → Bool, run (pin y) ≠ run (pin z)) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.FanInTwo D ∧ D.size < C.size ∧
          ∀ y : Fin 9 → Bool, D.eval (List.ofFn y ++ [f (pin y j)]) = run (pin y))
    (nineLower : ∀ (j : Fin 10) (f : Bool → Bool), j.val ∈ [0, 2, 3] →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
        D.size ≤ 15 → ∃ y : Fin 9 → Bool,
          let x : Fin 10 → Bool := Fin.cases false y
          D.eval (List.ofFn y ++ [f (x j)]) ≠ decide (∃ a b : Fin 10,
            x a = true ∧ x b = true ∧
            (([50, 69, 138, 276, 521, 385, 770, 548, 104, 208] : List ℕ).getD a.val 0).testBit b.val = true)) :
    ∀ (x1 : Fin (10 : ℕ)) (x2 : Bool → Bool), ↑x1 ∈ [(0 : ℕ), (2 : ℕ), (3 : ℕ)] → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (16 : ℕ) → (∀ x7 ∈ x4.gates, ∀ x9 ∈ x7.inputs, x9 ≤ (27 : ℕ)) → x4.output ≤ (27 : ℕ) → ∃ (x9 : Fin (10 : ℕ) → Bool), (x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ))) = Bool.false ∧ x4.eval (List.ofFn x9 ++ [x2 (x9 x1)]) ≠ (fun (x10 : Fin (10 : ℕ) → Bool) => Decidable.decide (∃ (x11 : Fin (10 : ℕ)) (x12 : Fin (10 : ℕ)), x10 x11 = Bool.true ∧ x10 x12 = Bool.true ∧ ([(50 : ℕ), (69 : ℕ), (138 : ℕ), (276 : ℕ), (521 : ℕ), (385 : ℕ), (770 : ℕ), (548 : ℕ), (104 : ℕ), (208 : ℕ)].getD ↑x11 (0 : ℕ)).testBit ↑x12 = Bool.true)) x9 := by
  intro j f hj C hfan hsize _ _
  let edge := fun x : Fin 10 → Bool => decide (∃ a b : Fin 10,
    x a = true ∧ x b = true ∧
    (([50, 69, 138, 276, 521, 385, 770, 548, 104, 208] : List ℕ).getD a.val 0).testBit b.val = true)
  let run := fun x : Fin 10 → Bool => C.eval (List.ofFn x ++ [f (x j)])
  let pin : (Fin 9 → Bool) → Fin 10 → Bool := fun y => Fin.cases false y
  change ∃ x : Fin 10 → Bool, (x 0 && x 1) = false ∧ run x ≠ edge x
  by_contra! correct
  let a := fun i : Fin 10 => decide (i = 4)
  let b := fun i : Fin 10 => decide (i = 4 ∨ i = 0)
  have distinguish : ∃ u v : Fin 10 → Bool,
      (∀ i, i ≠ 0 → u i = v i) ∧ run u ≠ run v := by
    refine ⟨a, b, ?_, ?_⟩
    · intro i hi
      simp [a, b, hi]
    · rw [correct a (by rfl), correct b (by rfl)]
      dsimp only [edge, a, b]
      decide
  have varies : ∃ y z : Fin 9 → Bool, run (pin y) ≠ run (pin z) := by
    let y := fun _ : Fin 9 => false
    let z := fun i : Fin 9 => decide (i = 0 ∨ i = 1)
    refine ⟨y, z, ?_⟩
    rw [correct (pin y) (by rfl), correct (pin z) (by rfl)]
    dsimp only [edge, pin, y, z]
    decide
  obtain ⟨D, hD, smaller, same⟩ := restrictPin j f C hfan distinguish varies
  obtain ⟨y, mismatch⟩ := nineLower j f hj D hD (by omega)
  exact mismatch ((same y).trans (correct (pin y) (by rfl)))
