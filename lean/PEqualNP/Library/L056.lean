import PEqualNP.Library.SearchHelpers.ResLin

/-- Res(lin) simulates resolution with at most four lines per line. -/
theorem PEqualNP.Library.L056 : ∀ (n : ℕ) (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
    (π : List (PEqualNP.ProofComplexity.Clause (Fin n))),
    PEqualNP.ProofComplexity.IsRefutation F π →
    ∃ π' : List (PEqualNP.Search.LinClause n), PEqualNP.Search.IsResLinRefutation F π' ∧
      π'.length ≤ 4 * π.length := by
  rintro n F π ⟨hd, he⟩
  obtain ⟨π', hd', hlen, hmem⟩ := PEqualNP.Library.SearchHelpers.resLin_simulates F π hd
  refine ⟨π', ⟨hd', ?_⟩, hlen⟩
  have := hmem ∅ he
  simpa [PEqualNP.Library.SearchHelpers.lin] using this
