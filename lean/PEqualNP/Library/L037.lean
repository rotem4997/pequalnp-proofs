import PEqualNP.Library.Helpers.OutputLength

/-- No polynomial-time function outputs satisfying assignments indexed by variable number. -/
theorem PEqualNP.Library.L037 : ¬ ∃ f : List Bool → List Bool,
    PEqualNP.Library.ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x) f ∧
      ∀ φ : PEqualNP.Search.CNF, PEqualNP.Search.Satisfiable φ →
        PEqualNP.Search.CNF.eval
          (fun i : ℕ => (f (PEqualNP.Search.encodeCNF φ)).getD i false) φ = true :=
  PEqualNP.Library.Helpers.no_indexed_assignment
