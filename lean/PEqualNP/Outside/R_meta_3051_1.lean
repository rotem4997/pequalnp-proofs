import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK PEqualNP.TopForm

-- Normalize the gate list. Count the incident pairs with a short proof tree
-- that either reads the line once or reads both endpoints twice.
theorem PEqualNP.Outside.R_meta_3051_1
    (normalize : ∀ (n : ℕ) (C : Circuit), Monotone2 C →
      circuitFun n C (fun _ => false) = false →
      ∃ D : Circuit, IsAO2 n D ∧ D.size ≤ C.size ∧ circuitFun n D = circuitFun n C)
    (manyTraces : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      let traces := Fintype.card {e : Fin N × Fin N //
        let v := (readVectors C (N+N) [e.1.val,N+e.2.val] 2).getD C.output []
        I e.1 e.2 ∧ ([2,2] ∈ v ∨ [1,1] ∈ v ∨ [2,1] ∈ v)}
      300 ≤ q → (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsAO2 (N+N) C →
      (∀ z : Fin (N+N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N+N) C z = false) →
      N*q ≤ 2*traces → N*q ≤ 100*C.size)
    (fewTraces : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      let traces := Fintype.card {e : Fin N × Fin N //
        let v := (readVectors C (N+N) [e.1.val,N+e.2.val] 2).getD C.output []
        I e.1 e.2 ∧ ([2,2] ∈ v ∨ [1,1] ∈ v ∨ [2,1] ∈ v)}
      300 ≤ q → N = q^2 + q + 1 →
      (∀ l, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) → IsAO2 (N+N) C →
      (∀ p l, I p l → circuitFun (N+N) C
        (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true) →
      (∀ z : Fin (N+N) → Bool, Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N+N) C z = false) →
      2*traces < N*q → N*q ≤ 100*C.size) :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (300 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro q N I _ C large shape degree join mono accepts rejects
  have zero : circuitFun (N+N) C (fun _ => false) = false := by
    apply rejects
    · simp
    · simp
  obtain ⟨D, basis, budget, same⟩ := normalize (N+N) C mono zero
  have dAccept (p l : Fin N) (incident : I p l) : circuitFun (N+N) D
      (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true := by
    rw [same]
    exact accepts p l incident
  have dReject (z : Fin (N+N) → Bool)
      (small : Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q)
      (absent : ¬ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
      circuitFun (N+N) D z = false := by
    rw [same]
    exact rejects z small absent
  let count := Fintype.card {e : Fin N × Fin N //
        let v := (readVectors D (N+N) [e.1.val,N+e.2.val] 2).getD D.output []
        I e.1 e.2 ∧ ([2,2] ∈ v ∨ [1,1] ∈ v ∨ [2,1] ∈ v)}
  have bound : N*q ≤ 100*D.size := by
    by_cases enough : N*q ≤ 2*count
    · exact manyTraces q N I D large join basis dReject enough
    · exact fewTraces q N I D large shape degree join basis dAccept dReject (Nat.lt_of_not_ge enough)
  exact bound.trans (Nat.mul_le_mul_left 100 budget)
