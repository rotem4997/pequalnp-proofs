import PEqualNP.Defs
import PEqualNP.Gct.L065
import PEqualNP.Gct.Helpers.FermatIterated

/-- Iterated Fermat lemma: a linear subspace `W` of `ℂ^M` on which all the power sums
`∑ x_i^j`, `2 ≤ j ≤ k`, vanish has `k * dim W ≤ M`. For `k = 2` this is the bound for totally
isotropic subspaces, for `k = 3` the sharp Fermat lemma L-gct-061. From Kneser for codes
(L-gct-065) applied along the chain `(W + ℂ1)^a W`, after polarization and a split along the
stabilizer of `(W + ℂ1)^(k-2) W`. -/
theorem PEqualNP.Gct.L067 : ∀ (M k : ℕ) (W : Submodule ℂ (Fin M → ℂ)), 2 ≤ k → (∀ j : ℕ, 2 ≤ j → j ≤ k → ∀ x ∈ W, ∑ i, x i ^ j = 0) → k * Module.finrank ℂ W ≤ M :=
  PEqualNP.Gct.Helpers.FermatIter.fermat_iter_of_kneser PEqualNP.Gct.L065
