import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_3688_653
    (trim : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n)) (C : Circuit),
      let computes := fun (D : Circuit) =>
        ∀ z, circuitFun (n + n) D z = decide (∃ p l, (p,l) ∈ E ∧
          z (Fin.castAdd n p) = true ∧ z (Fin.natAdd n l) = true)
      n < E.card → (∀ p, (p, σ p) ∈ E) → IsAO2 (n + n) C → computes C →
      ∃ D : Circuit, IsAO2 (n + n) D ∧ computes D ∧ D.size ≤ C.size ∧
        D.output + 1 = n + n + D.size ∧
        (D.gates.flatMap Gate.inputs).toFinset = Finset.range (n + n + D.size - 1))
    (account : ∀ (m : ℕ) (D : Circuit), IsAO2 m D →
      0 < m + D.size →
      (D.gates.flatMap Gate.inputs).toFinset = Finset.range (m + D.size - 1) →
      m + ((D.gates.flatMap Gate.inputs).length - (D.gates.flatMap Gate.inputs).toFinset.card) = D.size + 1)
    (charge : ∀ (n : ℕ) (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n)) (D : Circuit),
      let computes := fun (D : Circuit) =>
        ∀ z, circuitFun (n + n) D z = decide (∃ p l, (p,l) ∈ E ∧
          z (Fin.castAdd n p) = true ∧ z (Fin.natAdd n l) = true)
      n < E.card →
      (∀ p q l s, p ≠ q → l ≠ s →
        ¬ ((p,l) ∈ E ∧ (p,s) ∈ E ∧ (q,l) ∈ E ∧ (q,s) ∈ E)) →
      (∀ p, (p, σ p) ∈ E) → IsAO2 (n + n) D → computes D →
      D.output + 1 = n + n + D.size →
      (D.gates.flatMap Gate.inputs).toFinset = Finset.range (n + n + D.size - 1) →
      E.card - n ≤ (D.gates.flatMap Gate.inputs).length - (D.gates.flatMap Gate.inputs).toFinset.card) :
    ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)) (x3 : Equiv.Perm (Fin x1)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x1 < x2.card → (2 : ℕ) * x1 ≤ x4.size + (1 : ℕ) → (∀ (x7 x8 x9 x10 : Fin x1), x7 ≠ x8 → x9 ≠ x10 → ¬((x7, x9) ∈ x2 ∧ (x7, x10) ∈ x2 ∧ (x8, x9) ∈ x2 ∧ (x8, x10) ∈ x2)) → (∀ (x8 : Fin x1), (x8, x3 x8) ∈ x2) → PEqualNP.TopForm.IsAO2 (x1 + x1) x4 → (∀ (x10 : Fin (x1 + x1) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x1) x4 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x1), (x11, x12) ∈ x2 ∧ x10 (Fin.castAdd x1 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) → x2.card + x1 ≤ x4.size + (1 : ℕ) := by
  intro n E σ C hextra _ hrect hmatch hAO heval
  obtain ⟨D, hAO', heval', hsize, hlast, hcover⟩ := trim n E σ C hextra hmatch hAO heval
  have hcount := account (n + n) D hAO' (by omega) hcover
  have hcharge := charge n E σ D hextra hrect hmatch hAO' heval' hlast hcover
  omega
