import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_17197 : (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : (List Bool → Bool) → Prop := fun (x2 : List Bool → Bool) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2 ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → List ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : List ℕ) => x2 fun (x5 : List Bool) => x3.eval (x5 ++ [x4.any fun (x6 : ℕ) => x5.getD x6 Bool.false]); have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x5 : Fin x4.gates.length), ∀ x6 ∈ (x4.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5; have x5 : List (List ℕ) := [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (2 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)], [(0 : ℕ), (15 : ℕ)], [(0 : ℕ), (17 : ℕ)], [(0 : ℕ), (20 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(13 : ℕ), (15 : ℕ)]]; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), ∀ x7 ∈ x5, PEqualNP.MetaComplexity.Monotone2 x6 → x4 x6 → x3 x6 x7 → x6.gates = [] → (63 : ℕ) ≤ x6.size) := by
  intro d tests admissible earlier menus c aux inMenu mono reads accepted empty
  let pair := fun a : Fin 13 =>
    (List.ofFn (fun i : Fin 13 => decide (i = a))) ++ List.ofFn (fun i : Fin 13 => decide (i = a))
  have blanks : ∀ v ∈ menus,
      (v.any fun j => (pair 8).getD j false) = false ∧
      (v.any fun j => (pair 9).getD j false) = false := by decide +kernel
  obtain ⟨b8,b9⟩ := blanks aux inMenu
  have p8 : c.eval (pair 8 ++ [aux.any fun j => (pair 8).getD j false]) = true :=
    accepted.1 8 8 (by decide)
  have p9 : c.eval (pair 9 ++ [aux.any fun j => (pair 9).getD j false]) = true :=
    accepted.1 9 9 (by decide)
  rw [b8] at p8
  rw [b9] at p9
  simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
    empty, List.foldl_nil] at p8 p9
  by_cases h : c.output < 27
  · have clash : ∀ j : Fin 27,
        (pair 8 ++ [false]).getD j.val false = true →
        (pair 9 ++ [false]).getD j.val false = true → False := by decide +kernel
    exact False.elim (clash ⟨c.output,h⟩ p8 p9)
  · have hl : (pair 8 ++ [false]).length ≤ c.output := by change 27 ≤ c.output; omega
    simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_none hl,Option.getD_none] at p8
    contradiction
