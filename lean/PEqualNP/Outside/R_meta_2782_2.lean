import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2782_2
    (smallTests :
      ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
        0 < q → n = q ^ 2 + q + 1 →
        (∀ l, (S l).card = q + 1) →
        (∀ p r : Fin n, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
        IsAO2 (n + n) C → C.output < n + n + C.size →
        RightOnIncidentPairs S C →
        (∀ (X Y : Finset (Fin n)), X.card + Y.card ≤ 3 → IsFalseInput S X Y →
          C.eval (incidenceInput X Y) = false) →
        n + n + n ≤ C.size + 1)
    (large :
      ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
        300 ≤ q → n = q ^ 2 + q + 1 →
        (∀ l, (S l).card = q + 1) →
        (∀ p r : Fin n, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
        IsAO2 (n + n) C → C.output < n + n + C.size →
        RightOnIncidentPairs S C →
        (∀ (X Y : Finset (Fin n)), Y.card ≤ q → IsFalseInput S X Y →
          C.eval (incidenceInput X Y) = false) →
        n * q ≤ 100 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset ℕ), (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), (x3 x8).card = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x9 ∈ x3 x12 ∧ x10 ∈ x3 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → x4.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = Bool.false) → (∀ x14 < x4.size, x14 ∉ x5 → (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x18 : Finset (Fin x2) → Bool) (x19 : Finset (Fin x2) → Bool), ∀ (x20 x21 : Finset (Fin x2)), PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput x20 x21) (x2 + x2 + x14) = (x18 x20 && x19 x21)) → (100 : ℕ) * x5.card < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q n S C marked hq hn hline hjoin hC houtput htrue hfalse _ _
  by_cases hlarge : 300 ≤ q
  · exact large q n S C hlarge hn hline hjoin hC houtput htrue hfalse
  have branchSize := smallTests q n S C (by omega) hn hline hjoin hC houtput htrue
    (fun X Y hXY bad => hfalse X Y (by omega) bad)
  have hn100 : 100 ≤ n := by omega
  calc
    n * q ≤ n * 299 := Nat.mul_le_mul_left n (by omega)
    _ ≤ 100 * C.size := by
      rw [Nat.mul_comm n 299]
      omega
