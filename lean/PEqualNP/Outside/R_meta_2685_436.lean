import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2685_436
    (cover : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : ℕ) (x10 : Fin x9 → Finset (Fin x1)) (x11 : Fin x9 → Finset (Fin x2)), (∀ (x12 : Fin x9), (x10 x12).Nonempty ∧ (x11 x12).Nonempty) ∧ (∀ (x12 : Fin x9), ∀ x13 ∈ x10 x12, ∀ x15 ∈ x11 x12, x3 x13 x15) ∧ (∀ (x12 : Fin x1) (x13 : Fin x2), x3 x12 x13 → ∃ (x15 : Fin x9), x12 ∈ x10 x15 ∧ x13 ∈ x11 x15) ∧ ∑ x12 : Fin x9, ((x10 x12).card + (x11 x12).card) ≤ x5.size + (1 : ℕ))
    (compile : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 x6 : ℕ) (x7 : Fin x6 → Finset (Fin x1)) (x8 : Fin x6 → Finset (Fin x2)), ((∀ (x9 : Fin x6), (x7 x9).Nonempty ∧ (x8 x9).Nonempty) ∧ (∀ (x9 : Fin x6), ∀ x10 ∈ x7 x9, ∀ x12 ∈ x8 x9, x3 x10 x12) ∧ ∀ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 → ∃ (x12 : Fin x6), x9 ∈ x7 x12 ∧ x10 ∈ x8 x12) → ∑ x10 : Fin x6, ((x7 x10).card + (x8 x10).card) ≤ x5 + (1 : ℕ) → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2) x11 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x11 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x11.size ≤ x5 ∧ ∀ x12 < x11.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x11 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ) (x17 : Finset ℕ) (x18 : Finset ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x11 x12).inputs = [x15, x16] ∧ x15 ∈ x18 ∧ x16 ∈ x17 ∧ (∀ x19 ∈ x17, x19 < x1 ∨ ∃ x21 < x11.gates.length, x19 = x1 + x2 + x21 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x11 x21).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x11 x21).inputs, x22 ∈ x17) ∧ ∀ x19 ∈ x18, x1 ≤ x19 ∧ x19 < x1 + x2 ∨ ∃ x21 < x11.gates.length, x19 = x1 + x2 + x21 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x11 x21).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x11 x21).inputs, x22 ∈ x18) :
    ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (P L : Finset ℕ), PEqualNP.TopForm.IsAO2 (Np + Nl) D ∧ (∀ y : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D y = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ y (Fin.castAdd Nl p) = true ∧ y (Fin.natAdd Np l) = true)) ∧ D.size ≤ C.size ∧ (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ L) ∧ ∀ i < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) := by
  classical
  intro x1 x2 x3 x4 x5 hC hA hF
  obtain ⟨k, A, B, hne, hin, hcov, hcost⟩ := cover x1 x2 x3 x5 hC hA hF
  obtain ⟨D, hDA, hDF, hDs, hDt⟩ := compile x1 x2 x3 x5.size k A B ⟨hne, hin, hcov⟩ hcost
  refine ⟨D, (Finset.range (x1 + x2 + D.gates.length)).filter (fun w => ∃ S : Finset ℕ, w ∈ S ∧ ∀ x17 ∈ S, x17 < x1 ∨ ∃ x19 < D.gates.length, x17 = x1 + x2 + x19 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D x19).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D x19).inputs, x20 ∈ S), (Finset.range (x1 + x2 + D.gates.length)).filter (fun w => ∃ S : Finset ℕ, w ∈ S ∧ ∀ x17 ∈ S, x1 ≤ x17 ∧ x17 < x1 + x2 ∨ ∃ x19 < D.gates.length, x17 = x1 + x2 + x19 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D x19).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D x19).inputs, x20 ∈ S), hDA, hDF, hDs, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨-, S, hwS, hS⟩ := Finset.mem_filter.mp hw
    rcases hS w hwS with h | ⟨j, hj, hwj, hop, hinp⟩
    · exact Or.inl h
    · refine Or.inr ⟨j, hj, hwj, hop, ?_⟩
      intro u hu
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, S, hinp u hu, hS⟩
      rcases hS u (hinp u hu) with h' | ⟨j', hj', huj, -⟩
      · omega
      · omega
  · intro w hw
    obtain ⟨-, S, hwS, hS⟩ := Finset.mem_filter.mp hw
    rcases hS w hwS with h | ⟨j, hj, hwj, hop, hinp⟩
    · exact Or.inl h
    · refine Or.inr ⟨j, hj, hwj, hop, ?_⟩
      intro u hu
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, S, hinp u hu, hS⟩
      rcases hS u (hinp u hu) with h' | ⟨j', hj', huj, -⟩
      · omega
      · omega
  · intro j hj hand
    obtain ⟨a, b, Pj, Lj, hinp, ha, hb, hPj, hLj⟩ := hDt j hj hand
    refine ⟨a, b, hinp, Or.inr ⟨?_, ?_⟩⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, Lj, ha, hLj⟩
      rcases hLj a ha with h' | ⟨j', hj', huj, -⟩
      · omega
      · omega
    · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, Pj, hb, hPj⟩
      rcases hPj b hb with h' | ⟨j', hj', huj, -⟩
      · omega
      · omega
