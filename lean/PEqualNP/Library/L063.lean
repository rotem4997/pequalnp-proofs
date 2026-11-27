import Mathlib
import PEqualNP.Library.Helpers.QueryEvasion

/-- Query evasion on the Boolean cube (Lemma 4.3 of Aaronson and Wigderson 2009,
"Algebrization"): for any finite set `Y` of points of `F ^ n`, all but at most `|Y|` cube points
`w` admit a polynomial of individual degree at most two vanishing on `Y` whose restriction to the
cube is the indicator of `w`. -/
theorem PEqualNP.Library.L063 : ∀ (F : Type) [Field F] (n : ℕ) (Y : Finset (Fin n → F)), ∃ G : Finset (Fin n → Bool), 2 ^ n ≤ G.card + Y.card ∧ ∀ w ∈ G, ∃ p : MvPolynomial (Fin n) F, (∀ i : Fin n, MvPolynomial.degreeOf i p ≤ 2) ∧ (∀ y ∈ Y, MvPolynomial.eval y p = 0) ∧ ∀ z : Fin n → Bool, MvPolynomial.eval (fun i => if z i then (1 : F) else 0) p = if z = w then 1 else 0 :=
  fun F _ n Y => PEqualNP.Library.Helpers.QueryEvasion.main F n Y
