import PEqualNP.Library.Helpers.OracleEmpty

/-- With the empty oracle, `P^A` is `P`. -/
theorem PEqualNP.Library.L084 :
    PEqualNP.Library.OracleP (∅ : Set (List Bool)) = PEqualNP.Library.P :=
  PEqualNP.Library.Helpers.OracleEmpty.oracleP_empty
