import PEqualNP.MetaComplexity.Helpers.MachinePoly

/-- Any fixed list of polynomials with natural coefficients is computable in polynomial time on
tuples of unary numbers (entries past the end of the tuple read 0). -/
theorem PEqualNP.MetaComplexity.L507 : ∀ (s : ℕ) (P : List (MvPolynomial (Fin s) ℕ)), PEqualNP.Library.ComputableInPolyTime (PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false])) (PEqualNP.CircuitLowerBounds.encodeList (fun a : ℕ => List.replicate a true ++ [false])) (fun t : List ℕ => P.map (fun q : MvPolynomial (Fin s) ℕ => MvPolynomial.eval (fun i : Fin s => t.getD i.val 0) q)) :=
  PEqualNP.MetaComplexity.Helpers.MachinePoly.l507
