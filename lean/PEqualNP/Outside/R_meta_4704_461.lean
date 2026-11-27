import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.ReadK PEqualNP.GenericRejection

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_4704_461
    (cleaning : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2))
      (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      (200 : ℕ) ≤ x1 →
      x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →
      (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →
      PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →
      ¬ PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) →
      x4.output < x2 + x2 + x4.size →
      PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →
      (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 →
        PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 →
        x4.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = Bool.false) →
      (∀ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x14 →
        x14.output < x2 + x2 + x14.size →
        (∀ (x17 x18 : Finset (Fin x2)),
          x14.eval (PEqualNP.GenericRejection.incidenceInput x17 x18) =
            x4.eval (PEqualNP.GenericRejection.incidenceInput x17 x18)) →
        x4.size ≤ x14.size) →
      ∃ x5 : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 (x2 + x2) x5 ∧ x5.size ≤ x4.size ∧
        x5.output < x2 + x2 + x5.size ∧
        PEqualNP.GenericRejection.RightOnIncidentPairs x3 x5 ∧
        (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 →
          PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 →
          x5.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = Bool.false) ∧
        (∀ (i : ℕ), i < x5.size →
          ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 i).inputs,
            w < x2 + x2 ∨ ∃ j < x5.size,
              w = x2 + x2 + j ∧
                (PEqualNP.MetaComplexity.NestedCover.gateAt x5 j).op
                  = PEqualNP.CircuitLowerBounds.GateOp.or))
    (counting : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2))
      (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      (200 : ℕ) ≤ x1 →
      x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →
      (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →
      PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →
      x4.output < x2 + x2 + x4.size →
      PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →
      (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 →
        PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 →
        x4.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = Bool.false) →
      (∀ (i : ℕ), i < x4.size →
        ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x4 i).inputs,
          w < x2 + x2 ∨ ∃ j < x4.size,
            w = x2 + x2 + j ∧
              (PEqualNP.MetaComplexity.NestedCover.gateAt x4 j).op
                = PEqualNP.CircuitLowerBounds.GateOp.or) →
      x2 * (x1 + 1) ≤ x4.size)
    (bridge : ∀ (x1 x2 x5 : ℕ),
      (200 : ℕ) ≤ x1 →
      x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → x2 * (x1 + 1) ≤ x5 →
      x2 * x1 ≤ (100 : ℕ) * x5) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2))
      (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 →
      x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →
      (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →
      (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →
      PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →
      ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) →
      x4.output < x2 + x2 + x4.size →
      PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →
      (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 →
        PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 →
        x4.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = Bool.false) →
      (∀ (x14 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x2 + x2) x14 →
        x14.output < x2 + x2 + x14.size →
        (∀ (x17 x18 : Finset (Fin x2)),
          x14.eval (PEqualNP.GenericRejection.incidenceInput x17 x18) =
            x4.eval (PEqualNP.GenericRejection.incidenceInput x17 x18)) →
        x4.size ≤ x14.size) →
      x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro x1 x2 x3 x4 hq hN hcard huniq hao hnr2 hout hright hfalse hmin
  obtain ⟨x5, hao5, hsize5, hout5, hright5, hfalse5, hclean5⟩ :=
    cleaning x1 x2 x3 x4 hq hN hcard huniq hao hnr2 hout hright hfalse hmin
  have hcount := counting x1 x2 x3 x5 hq hN hcard huniq hao5 hout5 hright5 hfalse5 hclean5
  have hsq := bridge x1 x2 x5.size hq hN hcount
  omega
