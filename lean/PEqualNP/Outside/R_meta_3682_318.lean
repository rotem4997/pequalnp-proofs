import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.TopForm PEqualNP.ReadK

theorem PEqualNP.Outside.R_meta_3682_318
    (readTwo : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      200 ≤ q → n = q^2+q+1 → (∀ l, (S l).card = q+1) →
      (∀ p r : Fin n, p ≠ r → ∃! l : Fin n, p ∈ S l ∧ r ∈ S l) →
      IsAO2 (n+n) C → IsReadK (n+n) C 2 → C.output < n+n+C.size →
      RightOnIncidentPairs S C →
      (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      n*q ≤ 100*C.size)
    (minimal : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      200 ≤ q → n = q^2+q+1 → (∀ l, (S l).card = q+1) →
      (∀ p r : Fin n, p ≠ r → ∃! l : Fin n, p ∈ S l ∧ r ∈ S l) →
      IsAO2 (n+n) C → ¬ IsReadK (n+n) C 2 → C.output < n+n+C.size →
      RightOnIncidentPairs S C →
      (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      (∀ D : Circuit, IsAO2 (n+n) D → D.output < n+n+D.size →
        (∀ X Y : Finset (Fin n), D.eval (incidenceInput X Y) = C.eval (incidenceInput X Y)) →
        C.size ≤ D.size) →
      n*q ≤ 100*C.size) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → ¬PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → x4.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  classical
  intro q n S C hq hn sizes join basis _ output accepts rejects
  let valid (k : ℕ) := ∃ D : Circuit, D.size = k ∧ IsAO2 (n+n) D ∧
    D.output < n+n+D.size ∧ ∀ X Y : Finset (Fin n),
      D.eval (incidenceInput X Y) = C.eval (incidenceInput X Y)
  have existsValid : ∃ k, valid k := ⟨C.size, C, rfl, basis, output, fun _ _ => rfl⟩
  obtain ⟨D, Dsize, Dbasis, Doutput, eq⟩ := Nat.find_spec existsValid
  have minSize (B : Circuit) (Bbasis : IsAO2 (n+n) B) (Boutput : B.output < n+n+B.size)
      (Beq : ∀ X Y : Finset (Fin n),
        B.eval (incidenceInput X Y) = D.eval (incidenceInput X Y)) : D.size ≤ B.size := by
    rw [Dsize]
    apply Nat.find_min' existsValid
    exact ⟨B, rfl, Bbasis, Boutput, fun X Y => (Beq X Y).trans (eq X Y)⟩
  have comparison : D.size ≤ C.size :=
    minSize C basis output (fun X Y => (eq X Y).symm)
  have Dyes : RightOnIncidentPairs S D := fun l p on => (eq {p} {l}).trans (accepts l p on)
  have Dno (X Y : Finset (Fin n)) (few : Y.card ≤ q) (bad : IsFalseInput S X Y) :
      D.eval (incidenceInput X Y) = false := (eq X Y).trans (rejects X Y few bad)
  have lower : n*q ≤ 100*D.size := by
    by_cases reads : IsReadK (n+n) D 2
    · exact readTwo q n S D hq hn sizes join Dbasis reads Doutput Dyes Dno
    · exact minimal q n S D hq hn sizes join Dbasis reads Doutput Dyes Dno minSize
  exact lower.trans (Nat.mul_le_mul_left 100 comparison)
