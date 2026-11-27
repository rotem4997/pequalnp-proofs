import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_2782_419
    (hInputs : ∀ (n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      (∀ l, (S l).Nonempty) → (∀ p, ∃ l, p ∈ S l) →
      IsAO2 (n+n) C → RightOnIncidentPairs S C →
      (∀ X Y : Finset (Fin n), X.card + Y.card = 1 → C.eval (incidenceInput X Y) = false) →
      n + n ≤ C.size + 1)
    (hLarge : ∀ (q n : ℕ) (S : Fin n → Finset (Fin n)) (C : Circuit),
      200 ≤ q → n = q^2 + q + 1 → (∀ l, (S l).card = q+1) →
      (∀ p r : Fin n, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      IsAO2 (n+n) C → C.output < n+n+C.size → RightOnIncidentPairs S C →
      (∀ (X Y : Finset (Fin n)), Y.card ≤ q → IsFalseInput S X Y →
        C.eval (incidenceInput X Y) = false) →
      n*q ≤ 100*C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : Finset ℕ), (100 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), (x3 x8).card = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x9 ∈ x3 x12 ∧ x10 ∈ x3 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → x4.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = Bool.false) → (∀ x14 < x4.size, x14 ∉ x5 → (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x14).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x18 : Finset (Fin x2) → Bool) (x19 : Finset (Fin x2) → Bool), ∀ (x20 x21 : Finset (Fin x2)), PEqualNP.CircuitLowerBounds.wireValue x4 (PEqualNP.GenericRejection.incidenceInput x20 x21) (x2 + x2 + x14) = (x18 x20 && x19 x21)) → (100 : ℕ) * x5.card < x2 * x1 → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  intro q n S C T hq hn degree join model output accepts rejects _ _
  by_cases high : 200 ≤ q
  · exact hLarge q n S C high hn degree join model output accepts rejects
  have hn100 : 100 ≤ n := by omega
  have line_meets (l : Fin n) : (S l).Nonempty :=
    Finset.card_pos.mp (by rw [degree]; omega)
  have point_meets (p : Fin n) : ∃ l, p ∈ S l := by
    obtain ⟨r, hr⟩ : ∃ r : Fin n, p ≠ r := by
      by_cases hp : p.val = 0
      · refine ⟨⟨1, by omega⟩, ?_⟩
        intro he
        have hv : p.val = 1 := congrArg Fin.val he
        omega
      · exact ⟨⟨0, by omega⟩, fun he => hp (congrArg Fin.val he)⟩
    obtain ⟨l, ⟨hp, _⟩, _⟩ := join p r hr
    exact ⟨l, hp⟩
  have singles (X Y : Finset (Fin n)) (one : X.card + Y.card = 1) :
      C.eval (incidenceInput X Y) = false := by
    apply rejects X Y (by omega)
    by_cases hx : X = ∅
    · subst X
      intro l hl
      simp
    · have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hx)
      have hy : Y = ∅ := Finset.card_eq_zero.mp (by omega)
      subst Y
      intro l hl
      simp at hl
  have bound := hInputs n S C line_meets point_meets model accepts singles
  have hcap : q ≤ 199 := by omega
  have mult := Nat.mul_le_mul_left n hcap
  omega
