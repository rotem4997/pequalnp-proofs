import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.UndecidableUnary

open PEqualNP.MetaComplexity.Helpers.UndecUnary in
/-- P/poly contains a language that no machine decides: the strings whose length lies in a
suitable set of natural numbers. Every such language has constant-size circuits, and there are
more of them than machines. -/
theorem PEqualNP.MetaComplexity.L006 : ∃ L : Language Bool, L ∈ PEqualNP.CircuitLowerBounds.PPoly ∧ ∀ t : ℕ → ℕ, L ∉ PEqualNP.Library.DTIME t := by
  obtain ⟨A, hA⟩ := exists_lenLang_not_decided
  exact ⟨lenLang A, lenLang_mem_PPoly A, hA⟩
