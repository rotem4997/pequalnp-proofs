import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection PEqualNP.HeptadCover PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_17854_53
    (shape : let low := fun C : Circuit => HasLineDegree 26 (Finset.Ico 13 26) C 2 ∨ HasLineDegree 26 (Finset.range 13) C 2;∀ C : Circuit, Monotone2 C → ComputesIncidence singerLines3 C → low C → (gateAt C (C.size-1)).op = GateOp.and → (∃ D : Circuit, Monotone2 D ∧ ComputesIncidence singerLines3 D ∧ low D ∧ D.size < C.size ∧ D.output + 1 = 26 + D.size) ∨ (∃ a b : ℕ, C.output + 1 = 26 + C.size ∧ C.gates.getLast? = some (⟨GateOp.and,[a,b]⟩ : Gate) ∧ a < C.output ∧ b < C.output ∧ a ≠ b))
    (thin : let low := fun C : Circuit => HasLineDegree 26 (Finset.Ico 13 26) C 2 ∨ HasLineDegree 26 (Finset.range 13) C 2;∀ C : Circuit, Monotone2 C → ComputesIncidence singerLines3 C → low C → C.output + 1 = 26 + C.size → 63 ≤ C.size)
    (explicit : let low := fun C : Circuit => HasLineDegree 26 (Finset.Ico 13 26) C 2 ∨ HasLineDegree 26 (Finset.range 13) C 2;∀ C : Circuit, Monotone2 C → ComputesIncidence singerLines3 C → low C → (∃ a b : ℕ, C.output + 1 = 26 + C.size ∧ C.gates.getLast? = some (⟨GateOp.and,[a,b]⟩ : Gate) ∧ a < C.output ∧ b < C.output ∧ a ≠ b) → 64 ≤ C.size) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x1 → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (2 : ℕ) ∨ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x1 (2 : ℕ) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (64 : ℕ) ≤ x1.size) := by
  intro C hm hc hd hl
  rcases shape C hm hc hd hl with ⟨D,hDm,hDc,hDd,hsize,htail⟩ | hp
  · have hD := thin D hDm hDc hDd htail
    omega
  · exact explicit C hm hc hd hp
