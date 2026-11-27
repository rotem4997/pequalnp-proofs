import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- The circuit is empty or its last gate is one of the two allowed kinds, and past the end of the
-- gate list `gateAt` reads the default OR gate. So the gate at index `size - 1` is an AND in one
-- case and an OR in the other, and the step is asked once for each of the two cases.
theorem PEqualNP.Outside.R_meta_5256_1
    (lastAnd :
      have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 → (∀ (x6 : Bool) (x7 : List Bool), x2 x6 x7 → x3.eval x7 = x6) → (2 : ℕ) ≤ x3.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) → (∀ x8 < x3.size, ∀ x10 ≤ (26 : ℕ) + x8, ∃ (x12 : Bool) (x13 : List Bool), x2 x12 x13 ∧ (x3.wires x13).getD ((26 : ℕ) + x8) Bool.false = x12 ∧ (if x10 = (26 : ℕ) + x8 then Bool.false else (x3.wires x13).getD x10 Bool.false) = !x12) → (∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x9 x10) → (PEqualNP.MetaComplexity.NestedCover.gateAt x3 (x3.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (64 : ℕ) ≤ x3.size)
    (lastOr :
      have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 → (∀ (x6 : Bool) (x7 : List Bool), x2 x6 x7 → x3.eval x7 = x6) → (2 : ℕ) ≤ x3.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) → (∀ x8 < x3.size, ∀ x10 ≤ (26 : ℕ) + x8, ∃ (x12 : Bool) (x13 : List Bool), x2 x12 x13 ∧ (x3.wires x13).getD ((26 : ℕ) + x8) Bool.false = x12 ∧ (if x10 = (26 : ℕ) + x8 then Bool.false else (x3.wires x13).getD x10 Bool.false) = !x12) → (∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x9 x10) → (PEqualNP.MetaComplexity.NestedCover.gateAt x3 (x3.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or → (64 : ℕ) ≤ x3.size) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 → (∀ (x6 : Bool) (x7 : List Bool), x2 x6 x7 → x3.eval x7 = x6) → (2 : ℕ) ≤ x3.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) → (∀ x8 < x3.size, ∀ x10 ≤ (26 : ℕ) + x8, ∃ (x12 : Bool) (x13 : List Bool), x2 x12 x13 ∧ (x3.wires x13).getD ((26 : ℕ) + x8) Bool.false = x12 ∧ (if x10 = (26 : ℕ) + x8 then Bool.false else (x3.wires x13).getD x10 Bool.false) = !x12) → (∃ (x9 : ℕ) (x10 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x9 x10) → (64 : ℕ) ≤ x3.size := by
  intros L1 L2 x3 h1 h2 h3 h4 h5 h6
  have hop : ∀ g ∈ x3.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa using (h1 g hg).1
  have hsz : x3.size = x3.gates.length := rfl
  have hcase : (PEqualNP.MetaComplexity.NestedCover.gateAt x3 (x3.size - (1 : ℕ))).op =
      GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt x3 (x3.size - (1 : ℕ))).op = GateOp.or := by
    rcases Nat.eq_zero_or_pos x3.size with hz | hpos
    · right
      have hg : PEqualNP.MetaComplexity.NestedCover.gateAt x3 (x3.size - (1 : ℕ))
          = Gate.mk GateOp.or [] := by
        show List.getD x3.gates (x3.size - (1 : ℕ)) (Gate.mk GateOp.or []) = _
        apply List.getD_eq_default
        omega
      rw [hg]
    · have hj : x3.size - (1 : ℕ) < x3.gates.length := by rw [← hsz]; omega
      have hg : PEqualNP.MetaComplexity.NestedCover.gateAt x3 (x3.size - (1 : ℕ))
          = x3.gates[x3.size - (1 : ℕ)] :=
        List.getD_eq_getElem _ _ hj
      rw [hg]
      exact hop _ (List.getElem_mem hj)
  rcases hcase with hand | har
  · exact lastAnd x3 h1 h2 h3 h4 h5 h6 hand
  · exact lastOr x3 h1 h2 h3 h4 h5 h6 har
