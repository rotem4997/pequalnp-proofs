import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.TopForm

-- Removing the final AND saves one gate. Each sparse line set has one upstream
-- wire that is correct on every point set; the wire may depend on the lines.
theorem PEqualNP.Outside.R_meta_3469_521
    (normalize : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit) (j a b : ℕ),
      IsAO2 (n+n) C → C.output = n+n+j → C.gates[j]? = some ⟨.and,[a,b]⟩ →
      RightOnIncidentPairs S C →
      (∀ X Y, Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) →
      ∃ D : Circuit, IsAO2 (n+n) D ∧ D.size+1 ≤ C.size ∧
        RightOnIncidentPairs S ⟨D.gates,a⟩ ∧ RightOnIncidentPairs S ⟨D.gates,b⟩ ∧
        ∀ Y : Finset (Fin n), Y.card ≤ q → ∃ w ∈ [a,b], ∀ X : Finset (Fin n),
          wireValue D (incidenceInput X Y) w = incidenceFun S X Y)
    (count : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (D : Circuit) (a b : ℕ),
      200 ≤ q → n = q^2+q+1 → (∀ l, (S l).card = q+1) →
      (∀ p r : Fin n, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      IsAO2 (n+n) D → RightOnIncidentPairs S ⟨D.gates,a⟩ → RightOnIncidentPairs S ⟨D.gates,b⟩ →
      (∀ Y : Finset (Fin n), Y.card ≤ q → ∃ w ∈ [a,b], ∀ X : Finset (Fin n),
        wireValue D (incidenceInput X Y) w = incidenceFun S X Y) → n*q ≤ 100*(D.size+1)) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ (x12 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x4.output - (x2 + x2)]? = Option.some x12 ∧ x12.op = PEqualNP.CircuitLowerBounds.GateOp.and) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x14 x15 : Finset (Fin x2)), x15.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x14 x15 → x4.eval (PEqualNP.GenericRejection.incidenceInput x14 x15) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q n S C hq hn lineCard uniqueLine ao before _H gate pairs sound
  obtain ⟨g, hg, hand⟩ := gate
  obtain ⟨a,b,inputs⟩ := List.length_eq_two.mp (ao.2.2 g (List.mem_of_getElem? hg))
  have detail : g = ⟨.and,[a,b]⟩ := by cases g; simp_all
  have same : C.output = n+n+(C.output-(n+n)) := by omega
  obtain ⟨D, hao, saved, ha, hb, exactSlices⟩ :=
    normalize q n S C _ a b ao same (hg.trans (congrArg some detail)) pairs sound
  have h := count q n S D a b hq hn lineCard uniqueLine hao ha hb exactSlices
  omega
