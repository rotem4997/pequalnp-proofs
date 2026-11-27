import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2008_733
    (hCanonical :
      let Cross (n : ℕ) (C : Circuit) (g : Gate) :=
        g.op = GateOp.and ∧
        ((∀ w ∈ g.inputs, ∃ x : Fin n → Bool,
          (C.wires (List.ofFn x ++ List.replicate n false)).getD w false ≠
            (C.wires (List.ofFn x ++ List.replicate n true)).getD w false) ∨
         ∀ w ∈ g.inputs, ∃ x : Fin n → Bool,
          (C.wires (List.replicate n false ++ List.ofFn x)).getD w false ≠
            (C.wires (List.replicate n true ++ List.ofFn x)).getD w false)
      ∀ (n : ℕ) (C : Circuit) (T : Finset ℕ),
        (∀ j g, C.gates[j]? = some g → Cross n C g → j ∈ T) →
        ∃ U : Finset ℕ, U ⊆ T ∧ U ⊆ Finset.range C.size ∧
          ∀ j g, C.gates[j]? = some g → (j ∈ U ↔ Cross n C g))
    (hLower :
      let Cross (n : ℕ) (C : Circuit) (g : Gate) :=
        g.op = GateOp.and ∧
        ((∀ w ∈ g.inputs, ∃ x : Fin n → Bool,
          (C.wires (List.ofFn x ++ List.replicate n false)).getD w false ≠
            (C.wires (List.ofFn x ++ List.replicate n true)).getD w false) ∨
         ∀ w ∈ g.inputs, ∃ x : Fin n → Bool,
          (C.wires (List.replicate n false ++ List.ofFn x)).getD w false ≠
            (C.wires (List.replicate n true ++ List.ofFn x)).getD w false)
      ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → ∀ U : Finset ℕ, U ⊆ Finset.range x5.size →
        (∀ j g, x5.gates[j]? = some g → (j ∈ U ↔ Cross x2 x5 g)) →
        100 * U.card < x2 * x1 → x2 * x1 ≤ 100 * x5.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → x5.output < x2 + x2 + x5.size → (∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x12]? = Option.some x13 → ∃ (x15 : ℕ) (x16 : ℕ), x13.inputs = [x15, x16] ∧ x15 < x16 ∧ x16 < x2 + x2 + x12) → (∀ (x13 x14 : Fin x2), x3 x13 x14 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x16 : Fin (x2 + x2)) => Decidable.decide (x16 = Fin.castAdd x2 x13 ∨ x16 = Fin.natAdd x2 x14)) = Bool.true) → (∀ (x14 : Fin (x2 + x2) → Bool), Fintype.card { x15 : Fin x2 // x14 (Fin.natAdd x2 x15) = Bool.true } ≤ x1 → (¬∃ (x16 : Fin x2) (x17 : Fin x2), x3 x16 x17 ∧ x14 (Fin.castAdd x2 x16) = Bool.true ∧ x14 (Fin.natAdd x2 x17) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x14 = Bool.false) → ∀ (x15 : Finset ℕ), (∀ (x16 : ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x16]? = Option.some x17 → x17.op = PEqualNP.CircuitLowerBounds.GateOp.and → x16 ∉ x15 → ¬((∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.false)).getD x21 Bool.false ≠ (x5.wires (List.ofFn x23 ++ List.replicate x2 Bool.true)).getD x21 Bool.false) ∨ ∀ x21 ∈ x17.inputs, ∃ (x23 : Fin x2 → Bool), (x5.wires (List.replicate x2 Bool.false ++ List.ofFn x23)).getD x21 Bool.false ≠ (x5.wires (List.replicate x2 Bool.true ++ List.ofFn x23)).getD x21 Bool.false)) → (100 : ℕ) * x15.card < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q n R inst C hq hn hDegree hUnique hMono hOutput hSorted hAccept hReject T hTags hBudget
  obtain ⟨U, hSub, hRange, hExact⟩ := hCanonical n C T (by
    intro j g hget hCross
    by_contra hOutside
    exact hTags j g hget hCross.1 hOutside hCross.2)
  have hCard : U.card ≤ T.card := Finset.card_le_card hSub
  have hSmall : 100 * U.card < n * q :=
    (Nat.mul_le_mul_left 100 hCard).trans_lt hBudget
  exact hLower q n R C hq hn hDegree hUnique hMono hOutput hSorted hAccept hReject
    U hRange hExact hSmall
