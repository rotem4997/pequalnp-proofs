import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

-- A line-degree bound on each color gives a numerical condition for the two-level form.
theorem PEqualNP.Outside.R_meta_3503_634
    (normalize :
    ∀ (n m : ℕ) (I : Fin n → Fin m → Prop) [DecidableRel I] (C : Circuit),
      (∀ p q l s, p ≠ q → l ≠ s → ¬ (I p l ∧ I p s ∧ I q l ∧ I q s)) →
      IsAO2 (n+m) C →
      (∀ x, circuitFun (n+m) C x = decide (∃ p l, I p l ∧
        x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)) →
      ∃ D : Circuit, IsAO2 (n+m) D ∧ D.size ≤ C.size ∧
        (∀ x, circuitFun (n+m) D x = circuitFun (n+m) C x) ∧
        ∀ w < n+m+D.size, (D.lineDegrees (n+m) (Finset.range n)).getD w 0 ≤ 1 ∧
          (D.lineDegrees (n+m) (Finset.Ico n (n+m))).getD w 0 ≤ 1)
    (colors :
    ∀ (n m : ℕ) (C : Circuit), IsAO2 (n+m) C →
      (∀ w < n+m+C.size, (C.lineDegrees (n+m) (Finset.range n)).getD w 0 ≤ 1 ∧
        (C.lineDegrees (n+m) (Finset.Ico n (n+m))).getD w 0 ≤ 1) →
      ∃ P L : Finset ℕ,
        (∀ w ∈ P, w < n ∨ ∃ i < C.size, w = n+m+i ∧ (gateAt C i).op = .or ∧
          ∀ u ∈ (gateAt C i).inputs, u ∈ P) ∧
        (∀ w ∈ L, n ≤ w ∧ w < n+m ∨ ∃ i < C.size, w = n+m+i ∧ (gateAt C i).op = .or ∧
          ∀ u ∈ (gateAt C i).inputs, u ∈ L) ∧
        (∀ i < C.size, (gateAt C i).op = .and → ∃ a b,
          (gateAt C i).inputs = [a,b] ∧ (a ∈ P ∧ b ∈ L ∨ a ∈ L ∧ b ∈ P))) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ x5.size ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ (x15 ∈ x10 ∧ x16 ∈ x11 ∨ x15 ∈ x11 ∧ x16 ∈ x10) := by
  intro n m I inst C c4 shape computes
  obtain ⟨D, dShape, dSize, dEval, bounds⟩ := normalize n m I C c4 shape computes
  obtain ⟨P, L, points, lines, products⟩ := colors n m D dShape bounds
  exact ⟨D, P, L, dShape, fun x => (dEval x).trans (computes x), dSize, points, lines, products⟩
