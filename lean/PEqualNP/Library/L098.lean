import PEqualNP.MetaComplexity.Helpers.Machines.Lookup

/-- The bit of a string at an index written in binary, least significant bit first (false when
out of range), is computed in polynomial time. -/
theorem PEqualNP.Library.L098 : PEqualNP.Library.ComputableInPolyTime PEqualNP.Library.encodePair Computability.encodeBool (fun p : List Bool × List Bool => p.1.getD (List.foldr (fun (b : Bool) (a : ℕ) => 2 * a + (if b = true then 1 else 0)) 0 p.2) false) :=
  PEqualNP.MetaComplexity.Helpers.Machines.cpt_lookup
