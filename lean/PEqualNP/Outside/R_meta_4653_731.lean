import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4653_731
    (normalize :
      let count (D : Circuit) :=
        ({j : Fin D.gates.length | (D.gates.get j).op = GateOp.or} : Set _).ncard
      let critical (n : ℕ) (E : Fin n → Fin n → Prop) (D : Circuit) :=
        ∀ j : Fin D.gates.length, (D.gates.get j).op = GateOp.or →
          ∀ w ∈ (D.gates.get j).inputs, ∃ p l, E p l ∧
            let xs := List.ofFn (fun z : Fin n => decide (z = p ∨ z = l))
            ({D with gates := D.gates.set j.val ⟨GateOp.and, [w]⟩} : Circuit).eval xs = false ∧
            let pre := ({D with gates := D.gates.take j.val} : Circuit).wires xs
            pre.getD w false = false ∧ ∃ k ∈ (D.gates.get j).inputs, pre.getD k false = true
      let binary (n : ℕ) (D : Circuit) :=
        ∀ j : Fin D.gates.length, (D.gates.get j).op = GateOp.or →
          ∃ a b, (D.gates.get j).inputs = [a, b] ∧ a ≠ b ∧ a < n + j.val ∧ b < n + j.val
      ∀ (n : ℕ) (E : Fin n → Fin n → Prop) (C : Circuit), Monotone2 C → critical n E C →
        ∃ D, Monotone2 D ∧ count D ≤ count C ∧ critical n E D ∧ binary n D ∧
          ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x))
    (bound :
      let count (D : Circuit) :=
        ({j : Fin D.gates.length | (D.gates.get j).op = GateOp.or} : Set _).ncard
      let binary (n : ℕ) (D : Circuit) :=
        ∀ j : Fin D.gates.length, (D.gates.get j).op = GateOp.or →
          ∃ a b, (D.gates.get j).inputs = [a, b] ∧ a ≠ b ∧ a < n + j.val ∧ b < n + j.val
      let E (p l : Fin 42) := p.val < 21 ∧ 21 ≤ l.val ∧
        (l.val + 21 - p.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      ∀ C, Monotone2 C → binary 42 C →
        (∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.or →
          ∀ w ∈ (C.gates.get j).inputs, ∃ p l, E p l ∧
            ({C with gates := C.gates.set j.val ⟨GateOp.and, [w]⟩} : Circuit).eval
              (List.ofFn (fun z : Fin 42 => decide (z = p ∨ z = l))) = false) →
        (∀ x : Fin 42 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ p l, E p l ∧ x p = true ∧ x l = true) → 104 ≤ count C) :
    have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => {x3 : Fin x2.gates.length | (x2.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard; have x3 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → PEqualNP.CircuitLowerBounds.Circuit := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ) => { gates := x3.gates.set x4 { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5] : PEqualNP.CircuitLowerBounds.Gate }, output := x3.output : PEqualNP.CircuitLowerBounds.Circuit }; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x5 : Fin (42 : ℕ) → Bool), x4.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin (42 : ℕ)) (x7 : Fin (42 : ℕ)), x1 x6 x7 ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true; have x5 : Fin (42 : ℕ) → Fin (42 : ℕ) → Fin (42 : ℕ) → Bool := fun (x5 x6 x7 : Fin (42 : ℕ)) => Decidable.decide (x7 = x5 ∨ x7 = x6); have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) =>   ∀ (x7 : Fin x6.gates.length),     (x6.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or →       ∀ x9 ∈ (x6.gates.get x7).inputs,         ∃ (x11 : Fin (42 : ℕ)) (x12 : Fin (42 : ℕ)),           x1 x11 x12 ∧             (x3 x6 (↑x7) x9).eval (List.ofFn (x5 x11 x12)) = Bool.false ∧               have x13 : List Bool := { gates := List.take (↑x7) x6.gates, output := x6.output : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn (x5 x11 x12));               x13.getD x9 Bool.false = Bool.false ∧ ∃ x14 ∈ (x6.gates.get x7).inputs, x13.getD x14 Bool.false = Bool.true; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x4 x7 → x6 x7 → (104 : ℕ) ≤ x2 x7 := by
  intro E count bypass computes row critical C legal correct pins
  obtain ⟨D, legalD, costD, pinsD, binaryD, same⟩ := normalize 42 E C legal pins
  have computesD : ∀ x : Fin 42 → Bool, D.eval (List.ofFn x) = true ↔
      ∃ p l, E p l ∧ x p = true ∧ x l = true := by
    intro x
    rw [same]
    exact correct x
  apply (bound D legalD binaryD ?_ computesD).trans costD
  intro j hj w hw
  obtain ⟨p, l, hpl, loss, _⟩ := pinsD j hj w hw
  exact ⟨p, l, hpl, loss⟩
