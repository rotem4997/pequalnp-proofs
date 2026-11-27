import PEqualNP.ProofComplexity.Helpers.SmallPhpLin

/-- Every Res(+) refutation of PHP 2 1 has at least two lines. -/
theorem PEqualNP.ProofComplexity.L016 :
    ∀ π : List (PEqualNP.ProofComplexity.LinClause (Fin 2 × Fin 1)),
      PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.PHP 2 1) π →
        1 < π.length :=
  PEqualNP.ProofComplexity.Helpers.php21_len
