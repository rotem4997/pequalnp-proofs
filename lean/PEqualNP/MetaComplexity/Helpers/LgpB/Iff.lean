import PEqualNP.MetaComplexity.Helpers.LgpB.LgpInP
import PEqualNP.MetaComplexity.L114
import PEqualNP.Library.L018
import PEqualNP.Library.L031

/-- If P equals NP then the last-gate problem is in P: non-minimality inside the promise is an
existential block (a smaller fan-in-two circuit) over a universal block (all inputs, of length
the unary number of inputs), and both blocks collapse under P = NP. -/
theorem PEqualNP.MetaComplexity.LgpB.l109 : PEqualNP.Library.P = PEqualNP.Library.NP → PEqualNP.MetaComplexity.LgpInP :=
  PEqualNP.MetaComplexity.LgpB.LgpInP.l109

namespace PEqualNP.MetaComplexity.LgpB

/-- A polynomial-time reduction sending strings outside SAT to minimal circuits and strings in
SAT to circuits one gate above minimum makes the last-gate problem in P exactly when P = NP. -/
theorem iff_of_reduction : (∃ r : List Bool → ℕ × PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) PEqualNP.MetaComplexity.encodeLgp r ∧ ∀ x : List Bool, (x ∉ PEqualNP.Search.SAT → PEqualNP.MetaComplexity.LgpYes (r x).1 (r x).2) ∧ (x ∈ PEqualNP.Search.SAT → PEqualNP.MetaComplexity.LgpNo (r x).1 (r x).2)) → (PEqualNP.MetaComplexity.LgpInP ↔ PEqualNP.Library.P = PEqualNP.Library.NP) :=
  fun h => ⟨fun hl => (PEqualNP.Library.L018 _ PEqualNP.Library.L031).1
      (PEqualNP.MetaComplexity.L114 h hl),
    PEqualNP.MetaComplexity.LgpB.l109⟩

end PEqualNP.MetaComplexity.LgpB
