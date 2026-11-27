import PEqualNP.MetaComplexity.Helpers.LgpB.Iff

theorem PEqualNP.MetaComplexity.L665 : (∃ r : List Bool → ℕ × PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) PEqualNP.MetaComplexity.encodeLgp r ∧ ∀ x : List Bool, (x ∉ PEqualNP.Search.SAT → PEqualNP.MetaComplexity.LgpYes (r x).1 (r x).2) ∧ (x ∈ PEqualNP.Search.SAT → PEqualNP.MetaComplexity.LgpNo (r x).1 (r x).2)) → (PEqualNP.MetaComplexity.LgpInP ↔ PEqualNP.Library.P = PEqualNP.Library.NP) :=
  PEqualNP.MetaComplexity.LgpB.iff_of_reduction
