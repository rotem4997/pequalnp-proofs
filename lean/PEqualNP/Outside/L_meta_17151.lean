import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_17151 : (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x2 x3 : Fin (13 : ℕ)) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x2)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 = x3); have x3 : Finset (Fin (13 : ℕ)) → List Bool := fun (x3 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (x4 ∈ x3)) ++ List.ofFn fun (x4 : Fin (13 : ℕ)) => Decidable.decide (∀ x5 ∈ x3, x5 - x4 ∉ x1); have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => x4.card = (4 : ℕ) ∧ ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ); ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 : Fin (13 : ℕ)) (x7 : Bool), PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x9 : Fin x5.gates.length), ∀ x10 ∈ (x5.gates.get x9).inputs, x10 < (27 : ℕ) + ↑x9) → (∀ (x10 x11 : Fin (13 : ℕ)), x10 - x11 ∈ x1 → x10 ≠ (0 : Fin (13 : ℕ)) ∨ x11 ≠ x6 → x5.eval (x2 x10 x11 ++ [x7]) = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), x4 x11 → x5.eval (x3 x11 ++ [x7]) = Bool.false) → x5.gates = [] → (63 : ℕ) ≤ x5.size) := by
  dsimp only
  intro C x6 x7 _ _ hPos hNeg hNil
  exfalso
  have heval : ∀ l : List Bool, C.eval l = l.getD C.output false := by
    intro l
    simp [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, hNil]
  have h1 := hPos 1 1 (by decide) (Or.inl (by decide))
  have h2 := hPos 2 2 (by decide) (Or.inl (by decide))
  have hq := hNeg {0, 1, 2, 5} (by decide +kernel)
  rw [heval] at h1 h2 hq
  by_cases hlt : C.output < 27
  · have key : ∀ (b : Bool) (o : Fin 27),
      ¬ (((List.ofFn fun (i : Fin 13) => decide (i = 1)) ++
          (List.ofFn fun (i : Fin 13) => decide (i = 1)) ++ [b]).getD o.val false = true ∧
         ((List.ofFn fun (i : Fin 13) => decide (i = 2)) ++
          (List.ofFn fun (i : Fin 13) => decide (i = 2)) ++ [b]).getD o.val false = true ∧
         ((List.ofFn fun (i : Fin 13) => decide (i ∈ ({0, 1, 2, 5} : Finset (Fin 13)))) ++
          (List.ofFn fun (i : Fin 13) => decide (∀ p ∈ ({0, 1, 2, 5} : Finset (Fin 13)),
            p - i ∉ ({0, 1, 3, 9} : Finset (Fin 13)))) ++ [b]).getD o.val false = false) := by
      decide +kernel
    exact key x7 ⟨C.output, hlt⟩ ⟨h1, h2, hq⟩
  · have hlen : ((List.ofFn fun (i : Fin 13) => decide (i = 1)) ++
        (List.ofFn fun (i : Fin 13) => decide (i = 1)) ++ [x7]).length ≤ C.output := by
      simp
      omega
    have hfalse : ((List.ofFn fun (i : Fin 13) => decide (i = 1)) ++
        (List.ofFn fun (i : Fin 13) => decide (i = 1)) ++ [x7]).getD C.output false = false := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]
      rfl
    rw [hfalse] at h1
    cases h1
