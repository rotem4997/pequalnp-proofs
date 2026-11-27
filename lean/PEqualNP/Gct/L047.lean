import PEqualNP.Gct.Helpers.ParamTrans
import PEqualNP.Gct.Helpers.PolarSard

/-- Generic polar directions of a smooth form give independent gradients: for a smooth form `G`
in `h + 2` variables there are `h` directions such that at every nonzero common zero of `G` and
its polar derivatives the gradients of these `h + 1` forms are linearly independent. -/
theorem PEqualNP.Gct.L047 :
    ∀ (h r : ℕ) (G : MvPolynomial (Fin (h + 2)) ℂ), 2 ≤ r → G.IsHomogeneous r → (∀ x : Fin (h + 2) → ℂ, (∀ i, MvPolynomial.eval x (MvPolynomial.pderiv i G) = 0) → x = 0) → ∃ v : Fin h → Fin (h + 2) → ℂ, ∀ x : Fin (h + 2) → ℂ, x ≠ 0 → MvPolynomial.eval x G = 0 → (∀ k, MvPolynomial.eval x (∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j G) = 0) → LinearIndependent ℂ (Fin.cons (fun j => MvPolynomial.eval x (MvPolynomial.pderiv j G)) (fun k j => MvPolynomial.eval x (MvPolynomial.pderiv j (∑ l, MvPolynomial.C (v k l) * MvPolynomial.pderiv l G))) : Fin (h + 1) → Fin (h + 2) → ℂ) :=
  PEqualNP.Gct.Helpers.h4_of
    (fun E P _ _ _ _ _ _ _ _ μ _ f hf hs =>
      PEqualNP.Gct.Helpers.param_transversality E P μ f hf hs)
