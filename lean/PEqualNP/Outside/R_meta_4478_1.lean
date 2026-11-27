import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- Separate the monotone-circuit matching lower bound from König's cover extraction.
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_4478_1
    (matchingBound : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit),
      let hit : Fin (n + m) → Fin n × Fin m → Prop := fun v e =>
        Fin.castAdd m e.1 = v ∨ Fin.natAdd n e.2 = v
      (∀ p q l k, p ≠ q → l ≠ k →
        ¬ ((p, l) ∈ E ∧ (p, k) ∈ E ∧ (q, l) ∈ E ∧ (q, k) ∈ E)) →
      IsAO2 (n + m) C →
      (∀ z, circuitFun (n + m) C z =
        decide (∃ e ∈ E, z (Fin.castAdd m e.1) = true ∧ z (Fin.natAdd n e.2) = true)) →
      (∀ v, (E.filter (hit v)).card ≠ 1) →
      ∃ M : Finset (Fin n × Fin m), M ⊆ E ∧
        (∀ e ∈ M, ∀ f ∈ M, e ≠ f → e.1 ≠ f.1 ∧ e.2 ≠ f.2) ∧
        (∀ N : Finset (Fin n × Fin m), N ⊆ E →
          (∀ e ∈ N, ∀ f ∈ N, e ≠ f → e.1 ≠ f.1 ∧ e.2 ≠ f.2) →
          N.card ≤ M.card) ∧
        2 * E.card - M.card ≤ C.size + 1)
    (konig : ∀ (n m : ℕ) (E M : Finset (Fin n × Fin m)), M ⊆ E →
      (∀ e ∈ M, ∀ f ∈ M, e ≠ f → e.1 ≠ f.1 ∧ e.2 ≠ f.2) →
      (∀ N : Finset (Fin n × Fin m), N ⊆ E →
        (∀ e ∈ N, ∀ f ∈ N, e ≠ f → e.1 ≠ f.1 ∧ e.2 ≠ f.2) →
        N.card ≤ M.card) →
      ∃ T : Finset (Fin (n + m)),
        (∀ e ∈ E, Fin.castAdd m e.1 ∈ T ∨ Fin.natAdd n e.2 ∈ T) ∧
        T.card ≤ E.card - M.card) :
    ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),
      let x5 : Fin (x1 + x2) → Fin x1 × Fin x2 → Prop := fun (x5 : Fin (x1 + x2)) (x6 : Fin x1 × Fin x2) => Fin.castAdd x2 x6.1 = x5 ∨ Fin.natAdd x1 x6.2 = x5;
      have x6 : Finset (Fin x1 × Fin x2) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : Finset (Fin x1 × Fin x2)) (x7 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧ ∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x8 = Decidable.decide (∃ x9 ∈ x6, x8 (Fin.castAdd x2 x9.1) = Bool.true ∧ x8 (Fin.natAdd x1 x9.2) = Bool.true);
      (∀ (x7 x8 : Fin x1) (x9 x10 : Fin x2), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x3 ∧ (x7, x10) ∈ x3 ∧ (x8, x9) ∈ x3 ∧ (x8, x10) ∈ x3)) → x6 x3 x4 → (∀ (x9 : Fin (x1 + x2)), (Finset.filter (x5 x9) x3).card ≠ (1 : ℕ)) → ∃ (x10 : Finset (Fin (x1 + x2))), (∀ x11 ∈ x3, Fin.castAdd x2 x11.1 ∈ x10 ∨ Fin.natAdd x1 x11.2 ∈ x10) ∧ x3.card + x10.card ≤ x4.size + (1 : ℕ) := by
  intro n m E C
  let hit : Fin (n + m) → Fin n × Fin m → Prop := fun v e =>
    Fin.castAdd m e.1 = v ∨ Fin.natAdd n e.2 = v
  let computes : Finset (Fin n × Fin m) → Circuit → Prop := fun F D =>
    IsAO2 (n + m) D ∧ ∀ z, circuitFun (n + m) D z =
      decide (∃ e ∈ F, z (Fin.castAdd m e.1) = true ∧ z (Fin.natAdd n e.2) = true)
  change (∀ p q l k, p ≠ q → l ≠ k →
      ¬ ((p, l) ∈ E ∧ (p, k) ∈ E ∧ (q, l) ∈ E ∧ (q, k) ∈ E)) →
    computes E C → (∀ v, (E.filter (hit v)).card ≠ 1) →
    ∃ T : Finset (Fin (n + m)),
      (∀ e ∈ E, Fin.castAdd m e.1 ∈ T ∨ Fin.natAdd n e.2 ∈ T) ∧
      E.card + T.card ≤ C.size + 1
  intro hfree hc hno
  obtain ⟨hao, hcorrect⟩ := hc
  obtain ⟨M, hsub, hmatch, hmax, hbound⟩ :=
    matchingBound n m E C hfree hao hcorrect hno
  obtain ⟨T, hcover, hsize⟩ := konig n m E M hsub hmatch hmax
  refine ⟨T, hcover, ?_⟩
  have hcard : M.card ≤ E.card := Finset.card_le_card hsub
  omega
