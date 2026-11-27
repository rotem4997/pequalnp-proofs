import PEqualNP.Library.Helpers.OracleLift

/-- Every language in P is in P^A, for every oracle `A`. -/
theorem PEqualNP.Library.L057 :
    ∀ A : Language Bool, PEqualNP.Library.P ⊆ PEqualNP.Library.OracleP A :=
  PEqualNP.Library.Helpers.P_subset_OracleP
