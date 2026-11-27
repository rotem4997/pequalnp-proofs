import PEqualNP.MetaComplexity.Helpers.MachinePrint

/-- The cover circuit in block layout, printed as a circuit code from n and the owner tuples
in unary, is computable in polynomial time. -/
theorem PEqualNP.MetaComplexity.L508 : PEqualNP.Library.ComputableInPolyTime (fun p : List ℕ × List (List ℕ) => PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false]) p.1 ++ (PEqualNP.CircuitLowerBounds.encodeList (PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false]))) p.2) PEqualNP.MetaComplexity.encodeLgp (fun p : List ℕ × List (List ℕ) => (p.1.headD 0, PEqualNP.MetaComplexity.coverCircuitB (p.1.headD 0) (p.2.map (fun l : List ℕ => (l.headD 0, l.tail))))) :=
  PEqualNP.MetaComplexity.Helpers.MachinePrint.printer
