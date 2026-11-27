import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.GenericRejection PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_3258_271
    (linear : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      2 ≤ q → n = q^2+q+1 → (∀ l, (S l).card = q+1) →
      (∀ p r : Fin n, p ≠ r → ∃! l : Fin n, p ∈ S l ∧ r ∈ S l) →
      IsAO2 (n+n) C → RightOnIncidentPairs S C →
      (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      3*n ≤ C.size+1)
    (large : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      300 ≤ q → n = q^2+q+1 → (∀ l, (S l).card = q+1) →
      (∀ p r : Fin n, p ≠ r → ∃! l : Fin n, p ∈ S l ∧ r ∈ S l) →
      IsAO2 (n+n) C → C.output < n+n+C.size → RightOnIncidentPairs S C →
      (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      (∃ j < C.size, (gateAt C j).op = .or ∧ ∃ K : Finset (Fin n), 100 < K.card ∧
        let A (l : Fin n) : Finset (Fin n) :=
          {p : Fin n | wireValue C (incidenceInput {p} {l}) (n+n+j) = true}
        Set.InjOn A (K : Set (Fin n)) ∧ ∀ l ∈ K, 1 < (A l).card ∧ A l ⊆ S l ∧
          wireValue C (incidenceInput (S l)ᶜ {l}) (n+n+j) = false) →
      n*q ≤ 100*C.size) :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) →           PEqualNP.TopForm.IsAO2 (x2 + x2) x4 →             x4.output < x2 + x2 + x4.size →               PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 →                 (∀ (x12 x13 : Finset (Fin x2)), x13.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) →                   (∃ x13 < x4.size,                       (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧                         ∃ (x14 : Finset (Fin x2)),                           (100 : ℕ) < x14.card ∧                             have x15 : Fin x2 → Finset (Fin x2) := fun (x15 : Fin x2) => {x16 : Fin x2 | PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput {x16} {x15}) (x2 + x2 + x13) = Bool.true};                             Set.InjOn x15 ↑x14 ∧ ∀ x16 ∈ x14, (1 : ℕ) < (x15 x16).card ∧ x15 x16 ⊆ x3 x16 ∧ PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput (x3 x16)ᶜ {x16}) (x2 + x2 + x13) = Bool.false) →                     x2 * x1 ≤ (100 : ℕ) * x4.size
 := by
  intro q n S C order size counts join model output yes no wide
  by_cases big : 300 ≤ q
  · exact large q n S C big size counts join model output yes no wide
  have bound := linear q n S C (by omega) size counts join model yes no
  have population : 100 ≤ n := by omega
  calc
    n*q ≤ n*299 := Nat.mul_le_mul_left _ (by omega)
    _ ≤ 100*C.size := by omega
