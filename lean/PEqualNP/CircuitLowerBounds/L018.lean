import PEqualNP.CircuitLowerBounds.Helpers.ThrCount

/-- Some language has no depth-two threshold circuits of polynomial size (counting, with
Chow's theorem bounding the number of threshold functions). -/
theorem PEqualNP.CircuitLowerBounds.L018 :
    ∃ L : Language Bool, ∀ p : Polynomial ℕ,
      L ∉ PEqualNP.CircuitLowerBounds.THRTHR (fun n => p.eval n) :=
  PEqualNP.CircuitLowerBounds.Helpers.exists_not_thrthr
