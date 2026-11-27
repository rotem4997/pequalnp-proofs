import PEqualNP.Library.Helpers.OracleEmpty

/-- With the empty oracle, `NP^A` is `NP`. -/
theorem PEqualNP.Library.L085 :
    PEqualNP.Library.OracleNP (∅ : Set (List Bool)) = PEqualNP.Library.NP :=
  PEqualNP.Library.Helpers.OracleEmpty.oracleNP_empty
