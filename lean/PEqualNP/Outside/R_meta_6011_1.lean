import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- The circuit is empty or its last gate is one of the two allowed kinds, and past the end of the
-- gate list `gateAt` reads the default OR gate. So the gate at index `size - 1` is an AND in one
-- case and an OR in the other, and the step is asked once for each of the two cases.
theorem PEqualNP.Outside.R_meta_6011_1
    (lastAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           (∀ x8 ∈ x1.gates, x2 ∉ x8.inputs ∧ x3 ∉ x8.inputs) →             have x9 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};             have x10 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x10 x11 : Fin (13 : ℕ)) => (List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 = x10)) ++ List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 = x11);             have x11 : Finset (Fin (13 : ℕ)) → List Bool := fun (x11 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 ∈ x11)) ++ List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (∀ x13 ∈ x11, x13 - x12 ∉ x9);             have x12 : Finset (Fin (13 : ℕ)) → Prop := fun (x12 : Finset (Fin (13 : ℕ))) => x12.card = (4 : ℕ) ∧ ∀ (x13 : Fin (13 : ℕ)), {x14 ∈ x12 | x14 - x13 ∈ x9}.card ≤ (2 : ℕ);             have x13 : ℕ → List Bool → Bool := fun (x13 : ℕ) (x14 : List Bool) => (x1.wires x14).getD x13 Bool.false;             (∀ (x14 x15 : Fin (13 : ℕ)), x14 - x15 ∈ x9 → x13 x2 (x10 x14 x15) = Bool.true ∨ x13 x3 (x10 x14 x15) = Bool.true) → (∀ (x15 : Finset (Fin (13 : ℕ))), x12 x15 → x13 x2 (x11 x15) = Bool.false ∧ x13 x3 (x11 x15) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 - x17 ∈ x9 ∧ x13 x2 (x10 x16 x17) = Bool.true ∧ x13 x3 (x10 x16 x17) = Bool.false) → (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 - x18 ∈ x9 ∧ x13 x3 (x10 x17 x18) = Bool.true ∧ x13 x2 (x10 x17 x18) = Bool.false) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (63 : ℕ) ≤ x1.size)
    (lastOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           (∀ x8 ∈ x1.gates, x2 ∉ x8.inputs ∧ x3 ∉ x8.inputs) →             have x9 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};             have x10 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x10 x11 : Fin (13 : ℕ)) => (List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 = x10)) ++ List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 = x11);             have x11 : Finset (Fin (13 : ℕ)) → List Bool := fun (x11 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 ∈ x11)) ++ List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (∀ x13 ∈ x11, x13 - x12 ∉ x9);             have x12 : Finset (Fin (13 : ℕ)) → Prop := fun (x12 : Finset (Fin (13 : ℕ))) => x12.card = (4 : ℕ) ∧ ∀ (x13 : Fin (13 : ℕ)), {x14 ∈ x12 | x14 - x13 ∈ x9}.card ≤ (2 : ℕ);             have x13 : ℕ → List Bool → Bool := fun (x13 : ℕ) (x14 : List Bool) => (x1.wires x14).getD x13 Bool.false;             (∀ (x14 x15 : Fin (13 : ℕ)), x14 - x15 ∈ x9 → x13 x2 (x10 x14 x15) = Bool.true ∨ x13 x3 (x10 x14 x15) = Bool.true) → (∀ (x15 : Finset (Fin (13 : ℕ))), x12 x15 → x13 x2 (x11 x15) = Bool.false ∧ x13 x3 (x11 x15) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 - x17 ∈ x9 ∧ x13 x2 (x10 x16 x17) = Bool.true ∧ x13 x3 (x10 x16 x17) = Bool.false) → (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 - x18 ∈ x9 ∧ x13 x3 (x10 x17 x18) = Bool.true ∧ x13 x2 (x10 x17 x18) = Bool.false) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or → (63 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x1 →       x2 < (26 : ℕ) + x1.size →         x3 < (26 : ℕ) + x1.size →           (∀ x8 ∈ x1.gates, x2 ∉ x8.inputs ∧ x3 ∉ x8.inputs) →             have x9 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};             have x10 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x10 x11 : Fin (13 : ℕ)) => (List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 = x10)) ++ List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 = x11);             have x11 : Finset (Fin (13 : ℕ)) → List Bool := fun (x11 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (x12 ∈ x11)) ++ List.ofFn fun (x12 : Fin (13 : ℕ)) => Decidable.decide (∀ x13 ∈ x11, x13 - x12 ∉ x9);             have x12 : Finset (Fin (13 : ℕ)) → Prop := fun (x12 : Finset (Fin (13 : ℕ))) => x12.card = (4 : ℕ) ∧ ∀ (x13 : Fin (13 : ℕ)), {x14 ∈ x12 | x14 - x13 ∈ x9}.card ≤ (2 : ℕ);             have x13 : ℕ → List Bool → Bool := fun (x13 : ℕ) (x14 : List Bool) => (x1.wires x14).getD x13 Bool.false;             (∀ (x14 x15 : Fin (13 : ℕ)), x14 - x15 ∈ x9 → x13 x2 (x10 x14 x15) = Bool.true ∨ x13 x3 (x10 x14 x15) = Bool.true) → (∀ (x15 : Finset (Fin (13 : ℕ))), x12 x15 → x13 x2 (x11 x15) = Bool.false ∧ x13 x3 (x11 x15) = Bool.false) → (∃ (x16 : Fin (13 : ℕ)) (x17 : Fin (13 : ℕ)), x16 - x17 ∈ x9 ∧ x13 x2 (x10 x16 x17) = Bool.true ∧ x13 x3 (x10 x16 x17) = Bool.false) → (∃ (x17 : Fin (13 : ℕ)) (x18 : Fin (13 : ℕ)), x17 - x18 ∈ x9 ∧ x13 x3 (x10 x17 x18) = Bool.true ∧ x13 x2 (x10 x17 x18) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  intros x1 x2 x3 h1 h2 h3 h4 h5 L1 L2 L3 L4 L5 h6 h7 h8 h9
  have hop : ∀ g ∈ x1.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa using (h1 g hg).1
  have hsz : x1.size = x1.gates.length := rfl
  have hcase : (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op =
      GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = GateOp.or := by
    rcases Nat.eq_zero_or_pos x1.size with hz | hpos
    · right
      have hg : PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))
          = Gate.mk GateOp.or [] := by
        show List.getD x1.gates (x1.size - (1 : ℕ)) (Gate.mk GateOp.or []) = _
        apply List.getD_eq_default
        omega
      rw [hg]
    · have hj : x1.size - (1 : ℕ) < x1.gates.length := by rw [← hsz]; omega
      have hg : PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))
          = x1.gates[x1.size - (1 : ℕ)] :=
        List.getD_eq_getElem _ _ hj
      rw [hg]
      exact hop _ (List.getElem_mem hj)
  rcases hcase with hand | har
  · exact lastAnd x1 x2 x3 h1 h2 h3 h4 h5 h6 h7 h8 h9 hand
  · exact lastOr x1 x2 x3 h1 h2 h3 h4 h5 h6 h7 h8 h9 har
