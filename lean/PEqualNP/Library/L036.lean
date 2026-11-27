import PEqualNP.Library.SearchHelpers.SearchToDecision

/-- Search reduces to decision for SAT (Levin 1973): if SAT is in P, some polynomial-time
function finds a satisfying assignment of every satisfiable formula whose variables are all
below the length of its code, as the list of the values of the variables. -/
theorem PEqualNP.Library.L036 : PEqualNP.Search.SAT ∈ PEqualNP.Library.P → ∃ f : List Bool → List Bool, PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f ∧ ∀ φ : PEqualNP.Search.CNF, (∀ c ∈ φ, ∀ l ∈ c, l.1 < (PEqualNP.Search.encodeCNF φ).length) → PEqualNP.Search.Satisfiable φ → PEqualNP.Search.CNF.eval (fun i : ℕ => (f (PEqualNP.Search.encodeCNF φ)).getD i false) φ = true := by
  rintro ⟨d, hd, hc⟩
  exact PEqualNP.Library.SearchHelpers.S2D.search_of_decider d hd hc
