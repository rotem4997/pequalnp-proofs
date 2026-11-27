import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK PEqualNP.TopForm PEqualNP.GenericRejection

theorem PEqualNP.Outside.R_meta_3682_2
    (h1 : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      1 ≤ q → RightOnIncidentPairs S C →
      (∀ X Y : Finset (Fin n), Y.card ≤ q → IsFalseInput S X Y →
        C.eval (incidenceInput X Y) = false) →
      (∀ T : Finset (Fin (n+n)),
      ((List.finRange n).countP (fun l => decide (Fin.natAdd n l ∈ T))) ≤ q →
      (IsPrimeImplicant (n+n) C T ↔ ∃ p l : Fin n, p ∈ S l ∧
        T = {Fin.castAdd n p, Fin.natAdd n l})))
    (h2 : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      200 ≤ q → n = q ^ 2 + q + 1 → (∀ l, (S l).card = q+1) →
      (∀ p r : Fin n, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      IsAO2 (n+n) C → ¬IsReadK (n+n) C 2 → C.output < n+n+C.size →
      (∀ T : Finset (Fin (n+n)),
      ((List.finRange n).countP (fun l => decide (Fin.natAdd n l ∈ T))) ≤ q →
      (IsPrimeImplicant (n+n) C T ↔ ∃ p l : Fin n, p ∈ S l ∧
        T = {Fin.castAdd n p, Fin.natAdd n l})) → n*q ≤ 100*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → x4.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q n S C hq hn hcard hplane hao hread hout hit reject
  exact h2 q n S C hq hn hcard hplane hao hread hout
    (h1 q n S C (by omega) hit reject)
