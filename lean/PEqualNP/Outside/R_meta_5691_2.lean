import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5691_2
    (costBound : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m))
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ i k : Fin n, ∀ j l : Fin m, i ≠ k → j ≠ l →
        ¬ ((i,j) ∈ E ∧ (i,l) ∈ E ∧ (k,j) ∈ E ∧ (k,l) ∈ E)) →
      PEqualNP.TopForm.IsAO2 (n+m) C →
      (∀ z : Fin (n+m) → Bool, PEqualNP.MetaComplexity.circuitFun (n+m) C z =
        decide (∃ i j, (i,j) ∈ E ∧ z (Fin.castAdd m i) = true ∧ z (Fin.natAdd n j) = true)) →
      ∃ L : Finset (Fin n), ∃ R : Finset (Fin m),
        (∀ e ∈ E, e.1 ∈ L ∨ e.2 ∈ R) ∧ E.card + L.card + R.card ≤ C.size + 1)
    (compileStars : ∀ (n m : ℕ) (A B : Finset (Fin n × Fin m)),
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit, ∃ S : Bool → Finset ℕ,
        PEqualNP.TopForm.IsAO2 (n+m) D ∧
        (∀ z : Fin (n+m) → Bool, PEqualNP.MetaComplexity.circuitFun (n+m) D z =
          decide (∃ i j, (i,j) ∈ A ∪ B ∧ z (Fin.castAdd m i) = true ∧ z (Fin.natAdd n j) = true)) ∧
        D.size ≤ A.card + B.card + (A.image Prod.fst).card + (B.image Prod.snd).card - 1 ∧
        (let g := PEqualNP.MetaComplexity.NestedCover.gateAt D
         ∀ side, ∀ w ∈ S side,
           (if side then n ≤ w ∧ w < n+m else w < n) ∨
           ∃ j < D.gates.length, w = n+m+j ∧
             (g j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (g j).inputs, u ∈ S side) ∧
        (let g := PEqualNP.MetaComplexity.NestedCover.gateAt D
         ∀ j < D.gates.length, (g j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
           ∃ a ∈ S true, ∃ b ∈ S false, (g j).inputs = [a,b])) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x10 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) ∧ x9.size ≤ x5.size ∧ ∀ x10 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ) (x15 : Finset ℕ) (x16 : Finset ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x10).inputs = [x13, x14] ∧ x13 ∈ x16 ∧ x14 ∈ x15 ∧ (∀ x17 ∈ x15, x17 < x1 ∨ ∃ x19 < x9.gates.length, x17 = x1 + x2 + x19 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x19).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x19).inputs, x20 ∈ x15) ∧ ∀ x17 ∈ x16, x1 ≤ x17 ∧ x17 < x1 + x2 ∨ ∃ x19 < x9.gates.length, x17 = x1 + x2 + x19 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x19).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x19).inputs, x20 ∈ x16 := by
  classical
  intro n m relation inst C noSquare legal computes
  let E : Finset (Fin n × Fin m) := Finset.univ.filter fun e => relation e.1 e.2
  have square : ∀ i k : Fin n, ∀ j l : Fin m, i ≠ k → j ≠ l →
      ¬ ((i,j) ∈ E ∧ (i,l) ∈ E ∧ (k,j) ∈ E ∧ (k,l) ∈ E) := by
    simpa [E] using noSquare
  have evalC (z : Fin (n+m) → Bool) : PEqualNP.MetaComplexity.circuitFun (n+m) C z =
      decide (∃ i j, (i,j) ∈ E ∧ z (Fin.castAdd m i) = true ∧ z (Fin.natAdd n j) = true) := by
    simpa [E] using computes z
  obtain ⟨L,R,covers,cost⟩ := costBound n m E C square legal evalC
  let A := E.filter fun e => e.1 ∈ L
  let B := E \ A
  have partition : A ∪ B = E := by
    ext e
    simp only [A,B,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter]
    tauto
  have sub : A ⊆ E := Finset.filter_subset _ _
  have count : A.card + B.card = E.card := by
    have h := Finset.card_sdiff_of_subset sub
    have le := Finset.card_le_card sub
    change A.card + (E \ A).card = E.card
    omega
  have left : A.image Prod.fst ⊆ L := by
    intro i hi
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp he).2
  have right : B.image Prod.snd ⊆ R := by
    intro j hj
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨inside,outside⟩ := Finset.mem_sdiff.mp he
    exact (covers e inside).resolve_left fun hl => outside (Finset.mem_filter.mpr ⟨inside,hl⟩)
  obtain ⟨D,S,model,evaluates,size,closed,gates⟩ := compileStars n m A B
  refine ⟨D,model,?_,?_,?_⟩
  · intro z
    simpa [partition,E] using evaluates z
  · have hl := Finset.card_le_card left
    have hr := Finset.card_le_card right
    omega
  · intro j hj op
    obtain ⟨a,ha,b,hb,wires⟩ := gates j hj op
    exact ⟨a,b,S false,S true,wires,ha,hb,by simpa using closed false,by simpa using closed true⟩
