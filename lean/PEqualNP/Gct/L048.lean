import PEqualNP.Defs
import PEqualNP.Gct.Helpers.ChartA

/-! L-gct-048, chart choice for L-gct-034. Let `G` be a form in `h + 2` variables and
`D_{v_1} G, .., D_{v_h} G` its polar derivatives. If the `h + 1` gradients of
`G, D_{v_1} G, .., D_{v_h} G` are linearly independent at every nonzero common zero, then some
covector `a` vanishes at no nonzero common zero. Proof: by the inverse function theorem the cone
of common zeros is locally a line near each of its nonzero points, so by compactness of the unit
sphere it is a finite union of lines, and a covector off finitely many hyperplanes exists. -/

open MvPolynomial PEqualNP.Gct.Helpers PEqualNP.Gct.Helpers.ChartA

theorem PEqualNP.Gct.L048 : ∀ (h r : ℕ) (G : MvPolynomial (Fin (h + 2)) ℂ) (v : Fin h → Fin (h + 2) → ℂ), G.IsHomogeneous r → (∀ x : Fin (h + 2) → ℂ, x ≠ 0 → MvPolynomial.eval x G = 0 → (∀ k, MvPolynomial.eval x (∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j G) = 0) → LinearIndependent ℂ (Fin.cons (fun j => MvPolynomial.eval x (MvPolynomial.pderiv j G)) (fun k j => MvPolynomial.eval x (MvPolynomial.pderiv j (∑ l, MvPolynomial.C (v k l) * MvPolynomial.pderiv l G))) : Fin (h + 1) → Fin (h + 2) → ℂ)) → ∃ a : Fin (h + 2) → ℂ, ∀ x : Fin (h + 2) → ℂ, MvPolynomial.eval x G = 0 → ∑ j, a j * x j = 0 → (∀ k : Fin h, MvPolynomial.eval x (∑ j, MvPolynomial.C (v k j) * MvPolynomial.pderiv j G) = 0) → x = 0 := by
  intro h r G v hG hind
  exact chart_choice G hG v hind
