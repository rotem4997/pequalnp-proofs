import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4895_1
    (hbudget : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m))
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ (p q : Fin n) (l k : Fin m), p ≠ q → l ≠ k →
        ¬((p,l) ∈ E ∧ (p,k) ∈ E ∧ (q,l) ∈ E ∧ (q,k) ∈ E)) →
      PEqualNP.TopForm.IsAO2 (n + m) C →
      (∀ z, PEqualNP.MetaComplexity.circuitFun (n + m) C z =
        decide (∃ p l, (p,l) ∈ E ∧ z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) →
      ∃ (A : Finset (Fin n)) (B : Finset (Fin m)),
        (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) ∧ E.card + A.card + B.card - 1 ≤ C.size)
    (hstar : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m))
      (A : Finset (Fin n)) (B : Finset (Fin m)),
      (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 (n + m) D ∧
        D.size ≤ E.card + A.card + B.card - 1 ∧
        (∀ z, PEqualNP.MetaComplexity.circuitFun (n + m) D z =
          decide (∃ p l, (p,l) ∈ E ∧ z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true)) ∧
        PEqualNP.ReadK.IsReadK (n + m) D 1) : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x10 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) ∧ x9.size ≤ x5.size ∧ PEqualNP.ReadK.IsReadK (x1 + x2) x9 (1 : ℕ) := by
  intro n m I dec C noFour ao eval
  let E := Finset.univ.filter (fun e : Fin n × Fin m => I e.1 e.2)
  have mem (p : Fin n) (l : Fin m) : (p,l) ∈ E ↔ I p l := by simp [E]
  have agrees (z : Fin (n + m) → Bool) :
      PEqualNP.MetaComplexity.circuitFun (n + m) C z =
        decide (∃ p l, (p,l) ∈ E ∧ z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true) := by
    simpa only [mem] using eval z
  obtain ⟨A, B, cover, budget⟩ := hbudget n m E C (by simpa only [mem] using noFour) ao agrees
  obtain ⟨D, dao, size, deval, read⟩ := hstar n m E A B cover
  exact ⟨D, dao, fun z => by simpa only [mem] using deval z, size.trans budget, read⟩
