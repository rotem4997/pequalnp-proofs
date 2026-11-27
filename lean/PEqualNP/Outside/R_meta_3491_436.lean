import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3491_436
    (norm : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x10 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) ∧ x9.size ≤ x5.size ∧ ∀ x10 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ) (x15 : Finset ℕ) (x16 : Finset ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x10).inputs = [x13, x14] ∧ x13 ∈ x16 ∧ x14 ∈ x15 ∧ (∀ x17 ∈ x15, x17 < x1 ∨ ∃ x19 < x9.gates.length, x17 = x1 + x2 + x19 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x19).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x19).inputs, x20 ∈ x15) ∧ ∀ x17 ∈ x16, x1 ≤ x17 ∧ x17 < x1 + x2 ∨ ∃ x19 < x9.gates.length, x17 = x1 + x2 + x19 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x19).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x19).inputs, x20 ∈ x16)
    (count : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : Finset ℕ), (∀ (x8 x9 : Fin x1) (x10 x11 : Fin x2), x8 ≠ x9 → x10 ≠ x11 → ¬(x3 x8 x10 ∧ x3 x8 x11 ∧ x3 x9 x10 ∧ x3 x9 x11)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x10 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) → (∀ x11 ∈ x6, x11 < x1 ∨ ∃ x13 < x5.gates.length, x11 = x1 + x2 + x13 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x14 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x13).inputs, x14 ∈ x6) → (∀ x12 ∈ x7, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x5.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x14).inputs, x15 ∈ x7) → (∀ x13 < x5.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x13).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x16 : ℕ) (x17 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x13).inputs = [x16, x17] ∧ x16 ∈ x7 ∧ x17 ∈ x6) → ∃ (x14 : Finset (Fin (x1 + x2))), (∀ (x15 : Fin x1) (x16 : Fin x2), x3 x15 x16 → Fin.castAdd x2 x15 ∈ x14 ∨ Fin.natAdd x1 x16 ∈ x14) ∧ (PEqualNP.ReadTwo.incid x3).card + x14.card ≤ x5.size + (1 : ℕ)) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : Finset (Fin (x1 + x2))), (∀ (x10 : Fin x1) (x11 : Fin x2), x3 x10 x11 → Fin.castAdd x2 x10 ∈ x9 ∨ Fin.natAdd x1 x11 ∈ x9) ∧ (PEqualNP.ReadTwo.incid x3).card + x9.card ≤ x5.size + (1 : ℕ) := by
  classical
  intro x1 x2 x3 x4 x5 hC hA hF
  obtain ⟨D, hDA, hDF, hDs, hDt⟩ := norm x1 x2 x3 x5 hC hA hF
  let Pw : Finset ℕ := (Finset.range (x1 + x2 + D.gates.length)).filter (fun w => ∃ S : Finset ℕ, w ∈ S ∧ ∀ x17 ∈ S, x17 < x1 ∨ ∃ x19 < D.gates.length, x17 = x1 + x2 + x19 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D x19).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D x19).inputs, x20 ∈ S)
  let Lw : Finset ℕ := (Finset.range (x1 + x2 + D.gates.length)).filter (fun w => ∃ S : Finset ℕ, w ∈ S ∧ ∀ x17 ∈ S, x1 ≤ x17 ∧ x17 < x1 + x2 ∨ ∃ x19 < D.gates.length, x17 = x1 + x2 + x19 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D x19).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D x19).inputs, x20 ∈ S)
  have hP : ∀ x11 ∈ Pw, x11 < x1 ∨ ∃ x13 < D.gates.length, x11 = x1 + x2 + x13 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x14 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D x13).inputs, x14 ∈ Pw := by
    intro w hw
    obtain ⟨-, S, hwS, hS⟩ := Finset.mem_filter.mp hw
    rcases hS w hwS with h | ⟨j, hj, hwj, hop, hinp⟩
    · exact Or.inl h
    · refine Or.inr ⟨j, hj, hwj, hop, ?_⟩
      intro u hu
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, S, hinp u hu, hS⟩
      rcases hS u (hinp u hu) with h' | ⟨j', hj', huj, -⟩
      · omega
      · omega
  have hL : ∀ x12 ∈ Lw, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < D.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D x14).inputs, x15 ∈ Lw := by
    intro w hw
    obtain ⟨-, S, hwS, hS⟩ := Finset.mem_filter.mp hw
    rcases hS w hwS with h | ⟨j, hj, hwj, hop, hinp⟩
    · exact Or.inl h
    · refine Or.inr ⟨j, hj, hwj, hop, ?_⟩
      intro u hu
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, S, hinp u hu, hS⟩
      rcases hS u (hinp u hu) with h' | ⟨j', hj', huj, -⟩
      · omega
      · omega
  have hAnd : ∀ x13 < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D x13).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x16 : ℕ) (x17 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt D x13).inputs = [x16, x17] ∧ x16 ∈ Lw ∧ x17 ∈ Pw := by
    intro j hj hand
    obtain ⟨a, b, Pj, Lj, hinp, ha, hb, hPj, hLj⟩ := hDt j hj hand
    refine ⟨a, b, hinp, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, Lj, ha, hLj⟩
      rcases hLj a ha with h' | ⟨j', hj', huj, -⟩
      · omega
      · omega
    · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, Pj, hb, hPj⟩
      rcases hPj b hb with h' | ⟨j', hj', huj, -⟩
      · omega
      · omega
  obtain ⟨T, hT, hbd⟩ := count x1 x2 x3 D Pw Lw hC hDA hDF hP hL hAnd
  exact ⟨T, hT, le_trans hbd (by omega)⟩
