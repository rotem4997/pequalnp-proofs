import PEqualNP.Library.Helpers.TreeComplete
import PEqualNP.ProofComplexity.L021

/-- The bit pigeonhole formula with `2 ^ l + 1` pigeons and `2 ^ l` holes has a tree-like
Res(lin) refutation over the integers: the witness that L-lib-103 is not vacuous. -/
theorem PEqualNP.Library.L104 : ∀ l : ℕ, Nonempty (PEqualNP.Search.ResLinQTree (PEqualNP.ProofComplexity.BPHP (2 ^ l + 1) l) []) :=
  fun l => PEqualNP.Library.Helpers.TreeComplete.complete _
    (PEqualNP.ProofComplexity.L021 (2 ^ l + 1) l (Nat.lt_succ_self _))
