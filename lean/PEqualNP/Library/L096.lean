import PEqualNP.Library.Universal.UnaryPad

/-- For a polynomial-time decidable relation `R`, the language of the strings `1 ^ t 0 x` with a witness `w` of length at most `t` and `(x, w) ∈ R` is in NP. -/
theorem PEqualNP.Library.L096 : ∀ R : Set (List Bool × List Bool), PEqualNP.Library.DecidableInPolyTime PEqualNP.Library.encodePair R → ({y : List Bool | ∃ (t : ℕ) (x w : List Bool), y = List.replicate t true ++ false :: x ∧ w.length ≤ t ∧ (x, w) ∈ R} : Language Bool) ∈ PEqualNP.Library.NP :=
  fun R hR => PEqualNP.Library.Universal.unaryPad_NP R hR
