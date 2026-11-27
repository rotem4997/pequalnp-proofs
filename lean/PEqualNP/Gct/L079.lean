import Mathlib
import PEqualNP.Defs
import PEqualNP.Gct.Helpers.ProdSigma
import PEqualNP.Gct.Helpers.ProdSigmaChain

/-- Product-type linear spaces through Sigma_m inside the permanent hypersurface have dimension
at most 2m - 2. Rests on the chain inequality `PEqualNP.Gct.Helpers.ProdSigmaChain.chain`. -/
theorem PEqualNP.Gct.L079 : ∀ (m : ℕ) (U : Fin m → Submodule ℂ (Fin m → ℂ)), 2 ≤ m → (∀ i : Fin m, (fun j : Fin m => if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then (1 : ℂ) - (m : ℂ) else 1) ∈ U i) → (∀ x : Fin m × Fin m → ℂ, (∀ i : Fin m, (fun j : Fin m => x (i, j)) ∈ U i) → MvPolynomial.eval x (PEqualNP.Gct.permPoly ℂ m) = 0) → ∑ i : Fin m, Module.finrank ℂ (U i) ≤ 2 * m - 2 := by
  intro m U hm hSig hperm
  exact PEqualNP.Gct.Helpers.ProdSigma.main
    (fun n q hn V hI => PEqualNP.Gct.Helpers.ProdSigmaChain.chain n q hn V hI) m U hm hSig hperm
