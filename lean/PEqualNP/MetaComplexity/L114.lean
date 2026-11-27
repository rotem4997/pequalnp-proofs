import Mathlib
import PEqualNP.Defs.MetaComplexityLgp
import PEqualNP.Defs.Search
import PEqualNP.Library.L007
import PEqualNP.Library.L008

/-- A polynomial-time reduction of the complement of SAT into the last-gate promise problem,
together with a polynomial-time test for the last-gate problem on its promise, puts SAT in P. -/
theorem PEqualNP.MetaComplexity.L114 : (∃ r : List Bool → ℕ × PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) PEqualNP.MetaComplexity.encodeLgp r ∧ ∀ x : List Bool, (x ∉ PEqualNP.Search.SAT → PEqualNP.MetaComplexity.LgpYes (r x).1 (r x).2) ∧ (x ∈ PEqualNP.Search.SAT → PEqualNP.MetaComplexity.LgpNo (r x).1 (r x).2)) → PEqualNP.MetaComplexity.LgpInP → PEqualNP.Search.SAT ∈ PEqualNP.Library.P := by
  rintro ⟨r, hr, hYN⟩ ⟨f, hf, hcorr⟩
  have hc : PEqualNP.Search.SATᶜ ∈ PEqualNP.Library.P := by
    refine ⟨fun x => f (r x), fun x => ?_,
      PEqualNP.Library.L007 _ _ _ _ _ _ _ _ _ r f hr hf⟩
    constructor
    · intro hx
      exact (hcorr (r x)).1 ((hYN x).1 hx)
    · intro hx hmem
      have h2 := (hcorr (r x)).2 ((hYN x).2 hmem)
      have hx' : f (r x) = true := hx
      rw [h2] at hx'
      exact Bool.false_ne_true hx'
  have := PEqualNP.Library.L008 _ hc
  rwa [compl_compl] at this
