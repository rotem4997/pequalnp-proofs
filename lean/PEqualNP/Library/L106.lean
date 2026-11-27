import PEqualNP.Search.Helpers.CP.TriDag

/-- Cutting planes refutations give triangle dags: for any CNF, any split of its variables and
any cutting planes refutation over the integers, the falsified sets of its lines form a
triangle dag solving the search problem with at most as many nodes (Hrubes and Pudlak 2017;
Sokolov 2017). -/
theorem PEqualNP.Library.L106 : ∀ (V : Type) [Fintype V] [DecidableEq V] (side : V → Bool)
    (F : Set (PEqualNP.ProofComplexity.Clause V)) (π : List (PEqualNP.Search.CPLine V)),
    PEqualNP.Search.IsCPRefutation F π →
    ∃ ρ : List (Set (V → Bool)), PEqualNP.Search.IsTriDagFor side F ρ ∧ ρ.length ≤ π.length :=
  fun _ _ _ side _ π h =>
    ⟨π.map fun e => {a | ¬ PEqualNP.Search.CPLine.Holds a e},
      PEqualNP.Search.Helpers.CP.triDagFor_of_refutation side h, by simp⟩
