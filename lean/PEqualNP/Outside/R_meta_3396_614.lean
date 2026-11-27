import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.FactorSubst

-- Count the output as one use. A live gate contributes two further operand positions.
-- Distinct wires pay for the incident vertices and live gates. Extra occurrences of
-- those same wires measure sharing in the underlying circuit, including repeated inputs.
theorem PEqualNP.Outside.R_meta_3396_614
    (distinctWires : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit),
      IsAO2 (n+m) C →
      (∀ x, circuitFun (n+m) C x = decide (∃ p l, (p,l) ∈ E ∧
        x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)) →
      let S := liveGates (n+m) C
      let R := C.output :: S.toList.flatMap (fun j => (gateAt C j).inputs)
      (E.image Prod.fst).card + (E.image Prod.snd).card + S.card ≤ R.toFinset.card)
    (repeatedWires : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)) (C : Circuit),
      (∀ p q l s, p ≠ q → l ≠ s → ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) →
      IsAO2 (n+m) C →
      (∀ x, circuitFun (n+m) C x = decide (∃ p l, (p,l) ∈ E ∧
        x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)) →
      M ⊆ E → (∀ e ∈ M, ∀ d ∈ M, e.1 = d.1 → e = d) →
      (∀ e ∈ M, ∀ d ∈ M, e.2 = d.2 → e = d) →
      (∀ e ∈ E, ¬ ((∀ d ∈ E, d.1 = e.1 → d = e) ∨ (∀ d ∈ E, d.2 = e.2 → d = e))) →
      let S := liveGates (n+m) C
      let R := C.output :: S.toList.flatMap (fun j => (gateAt C j).inputs)
      E.card + M.card ≤ (E.image Prod.fst).card + (E.image Prod.snd).card +
        (R.length - R.toFinset.card)) :
∀ (x1 x2 : ℕ) (x3 x4 : Finset (Fin x1 × Fin x2)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬((x6, x8) ∈ x3 ∧ (x6, x9) ∈ x3 ∧ (x7, x8) ∈ x3 ∧ (x7, x9) ∈ x3)) →     PEqualNP.TopForm.IsAO2 (x1 + x2) x5 →       (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) →         x4 ⊆ x3 →           (∀ x10 ∈ x4, ∀ x12 ∈ x4, x10.1 = x12.1 → x10 = x12) →             (∀ x11 ∈ x4, ∀ x13 ∈ x4, x11.2 = x13.2 → x11 = x13) →               have x12 : Fin x1 × Fin x2 → Prop := fun (x12 : Fin x1 × Fin x2) => (∀ x13 ∈ x3, x13.1 = x12.1 → x13 = x12) ∨ ∀ x13 ∈ x3, x13.2 = x12.2 → x13 = x12;               (∀ x13 ∈ x3, ¬x12 x13) → x3.card + x4.card ≤ x5.size + (1 : ℕ) := by
  classical
  intro n m E M C square ao val sub rows cols leaf hleaf
  let S := liveGates (n+m) C
  let R := C.output :: S.toList.flatMap (fun j => (gateAt C j).inputs)
  have hDistinct := distinctWires n m E C ao val
  have hRepeat := repeatedWires n m E M C square ao val sub rows cols hleaf
  change (E.image Prod.fst).card + (E.image Prod.snd).card + S.card ≤ R.toFinset.card at hDistinct
  change E.card + M.card ≤ (E.image Prod.fst).card + (E.image Prod.snd).card + (R.length - R.toFinset.card) at hRepeat
  have subset : S ⊆ Finset.range C.gates.length := Finset.filter_subset _ _
  have bounded : S.card ≤ C.size := by
    change S.card ≤ C.gates.length
    simpa only [Finset.card_range] using Finset.card_le_card subset
  have two (j : ℕ) (hj : j ∈ S.toList) : (gateAt C j).inputs.length = 2 := by
    have lt := Finset.mem_range.mp (subset (Finset.mem_toList.mp hj))
    apply ao.2.2
    change C.gates.getD j ⟨GateOp.or, []⟩ ∈ C.gates
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem lt]
  have lengths : ∀ l : List ℕ, (∀ j ∈ l, (gateAt C j).inputs.length = 2) →
      (l.flatMap (fun j => (gateAt C j).inputs)).length = 2*l.length := by
    intro l
    induction l with
    | nil => simp
    | cons j l ih =>
      intro hall
      have head := hall j (by simp)
      have tail := ih (fun i hi => hall i (by simp [hi]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons, head, tail]
      omega
  have count : R.length = 2*S.card + 1 := by
    simp [R, lengths S.toList two]
  have card_le : R.toFinset.card ≤ R.length := List.toFinset_card_le R
  omega
