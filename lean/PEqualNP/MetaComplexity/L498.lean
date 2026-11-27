import PEqualNP.MetaComplexity.Helpers.MachineShell

/-- The outer shell of the reduction: a polynomial-time map on CNF codes extends to every bit
string, agreeing on codes and sending every other string to the instance with no inputs, no
gates and output wire 0. -/
theorem PEqualNP.MetaComplexity.L498 : ∀ R : PEqualNP.Search.CNF → ℕ × PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.Library.ComputableInPolyTime PEqualNP.Search.encodeCNF PEqualNP.MetaComplexity.encodeLgp R → ∃ r : List Bool → ℕ × PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) PEqualNP.MetaComplexity.encodeLgp r ∧ (∀ φ : PEqualNP.Search.CNF, r (PEqualNP.Search.encodeCNF φ) = R φ) ∧ ∀ x : List Bool, (∀ φ : PEqualNP.Search.CNF, PEqualNP.Search.encodeCNF φ ≠ x) → r x = (0, PEqualNP.CircuitLowerBounds.Circuit.mk [] 0) :=
  PEqualNP.MetaComplexity.Helpers.MachineShell.shell
