import PEqualNP.MetaComplexity.Helpers.LogicRows

/-- A map correct on CNF codes and sending non-codes to YES sends the complement of SAT to YES and SAT to NO. -/
theorem PEqualNP.MetaComplexity.L352 : ∀ r : List Bool → ℕ × PEqualNP.CircuitLowerBounds.Circuit, Function.Injective PEqualNP.Search.encodeCNF → (∀ φ : PEqualNP.Search.CNF, (¬ PEqualNP.Search.Satisfiable φ → PEqualNP.MetaComplexity.LgpYes (r (PEqualNP.Search.encodeCNF φ)).1 (r (PEqualNP.Search.encodeCNF φ)).2) ∧ (PEqualNP.Search.Satisfiable φ → PEqualNP.MetaComplexity.LgpNo (r (PEqualNP.Search.encodeCNF φ)).1 (r (PEqualNP.Search.encodeCNF φ)).2)) → (∀ x : List Bool, x ∉ Set.range PEqualNP.Search.encodeCNF → PEqualNP.MetaComplexity.LgpYes (r x).1 (r x).2) → ∀ x : List Bool, (x ∉ PEqualNP.Search.SAT → PEqualNP.MetaComplexity.LgpYes (r x).1 (r x).2) ∧ (x ∈ PEqualNP.Search.SAT → PEqualNP.MetaComplexity.LgpNo (r x).1 (r x).2) :=
  PEqualNP.MetaComplexity.Helpers.LogicRows.glue
