import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3376_1
  (h1 :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (0 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x12.card + x13.card ≤ (3 : ℕ) → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 + x2 + x2 ≤ x4.size + (1 : ℕ))
  (h2 :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (0 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ g : PEqualNP.CircuitLowerBounds.Gate, x4.gates[x4.output - (x2 + x2)]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.and) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x12.card + x13.card ≤ (3 : ℕ) → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 + x2 + x2 ≤ x4.size + (1 : ℕ))
  (h3 :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (0 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x2 + x2 ≤ x4.output → x4.output < x2 + x2 + x4.size → (∃ g : PEqualNP.CircuitLowerBounds.Gate, x4.gates[x4.output - (x2 + x2)]? = Option.some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x12.card + x13.card ≤ (3 : ℕ) → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 + x2 + x2 ≤ x4.size + (1 : ℕ)) :
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (0 : ℕ) < x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x12 x13 : Finset (Fin x2)), x12.card + x13.card ≤ (3 : ℕ) → PEqualNP.GenericRejection.IsFalseInput x3 x12 x13 → x4.eval (PEqualNP.GenericRejection.incidenceInput x12 x13) = Bool.false) → x2 + x2 + x2 ≤ x4.size + (1 : ℕ) := by
  intro x1 x2 x3 x4 hq hx2 hcard huniq hao hlt hright hfalse
  rcases lt_or_ge x4.output (x2 + x2) with hout_lt | hout_ge
  · exact h1 x1 x2 x3 x4 hq hx2 hcard huniq hao hout_lt hright hfalse
  · have hidx : x4.output - (x2 + x2) < x4.gates.length := by
      change x4.output - (x2 + x2) < x4.size
      omega
    obtain ⟨g, hg⟩ : ∃ g, x4.gates[x4.output - (x2 + x2)]? = Option.some g :=
      ⟨x4.gates[x4.output - (x2 + x2)], getElem?_pos x4.gates _ hidx⟩
    rcases hao.1 g (List.mem_of_getElem? hg) with hop | hop
    · exact h2 x1 x2 x3 x4 hq hx2 hcard huniq hao hout_ge hlt ⟨g, hg, hop⟩ hright hfalse
    · exact h3 x1 x2 x3 x4 hq hx2 hcard huniq hao hout_ge hlt ⟨g, hg, hop⟩ hright hfalse
