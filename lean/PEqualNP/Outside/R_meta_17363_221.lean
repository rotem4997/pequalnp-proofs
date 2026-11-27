import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17363_221
    (h1 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool) (x3 : Fin (13 : ℕ)), PEqualNP.MetaComplexity.Monotone2 x1 → (∃ (x2 : Fin x1.gates.length), (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x5 x6 : Fin (13 : ℕ)), (if x2 = Bool.true then x5 ≠ x3 else x6 ≠ x3) → x5 ∈ PEqualNP.HeptadCover.singerLines3 x6 → x1.eval (PEqualNP.GenericRejection.incidenceInput {x5} {x6}) = Bool.true) → (∀ (x6 x7 : Finset (Fin (13 : ℕ))), (if x2 = Bool.true then x3 ∉ x6 else x3 ∉ x7) → x1.eval (PEqualNP.GenericRejection.incidenceInput x6 x7) = Bool.true → PEqualNP.GenericRejection.incidenceFun PEqualNP.HeptadCover.singerLines3 x6 x7 = Bool.true) → (59 : ℕ) ≤ x1.size)
    (h2 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool) (x3 : Fin (13 : ℕ)), PEqualNP.MetaComplexity.Monotone2 x1 → (¬(∃ (x2 : Fin x1.gates.length), (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.and)) → (∀ (x5 x6 : Fin (13 : ℕ)), (if x2 = Bool.true then x5 ≠ x3 else x6 ≠ x3) → x5 ∈ PEqualNP.HeptadCover.singerLines3 x6 → x1.eval (PEqualNP.GenericRejection.incidenceInput {x5} {x6}) = Bool.true) → (∀ (x6 x7 : Finset (Fin (13 : ℕ))), (if x2 = Bool.true then x3 ∉ x6 else x3 ∉ x7) → x1.eval (PEqualNP.GenericRejection.incidenceInput x6 x7) = Bool.true → PEqualNP.GenericRejection.incidenceFun PEqualNP.HeptadCover.singerLines3 x6 x7 = Bool.true) → (59 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool) (x3 : Fin (13 : ℕ)), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x5 x6 : Fin (13 : ℕ)), (if x2 = Bool.true then x5 ≠ x3 else x6 ≠ x3) → x5 ∈ PEqualNP.HeptadCover.singerLines3 x6 → x1.eval (PEqualNP.GenericRejection.incidenceInput {x5} {x6}) = Bool.true) → (∀ (x6 x7 : Finset (Fin (13 : ℕ))), (if x2 = Bool.true then x3 ∉ x6 else x3 ∉ x7) → x1.eval (PEqualNP.GenericRejection.incidenceInput x6 x7) = Bool.true → PEqualNP.GenericRejection.incidenceFun PEqualNP.HeptadCover.singerLines3 x6 x7 = Bool.true) → (59 : ℕ) ≤ x1.size := by
  intro x1
  by_cases h : (∃ (x2 : Fin x1.gates.length), (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.and)
  · intros
    apply h1 <;> assumption
  · intros
    apply h2 <;> assumption
