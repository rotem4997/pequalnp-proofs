import PEqualNP.Library.L063
import PEqualNP.Library.Helpers.QueryEvasionUnion

/-- Query evasion across finitely many fields (union bound over L-lib-063):
one Boolean point is good for every field at once. Aaronson and Wigderson 2009, Theorem 5.3. -/
theorem PEqualNP.Library.L064 : ∀ (n k : ℕ) (Fs : Fin k → Type) [inst : ∀ j, Field (Fs j)] (Y : ∀ j, Finset (Fin n → Fs j)), ∑ j, (Y j).card < 2 ^ n → ∃ w : Fin n → Bool, ∀ j, ∃ p : MvPolynomial (Fin n) (Fs j), (∀ i : Fin n, MvPolynomial.degreeOf i p ≤ 2) ∧ (∀ y ∈ Y j, MvPolynomial.eval y p = 0) ∧ ∀ z : Fin n → Bool, MvPolynomial.eval (fun i => if z i then (1 : Fs j) else 0) p = if z = w then 1 else 0 :=
  PEqualNP.Library.Helpers.QueryEvasionUnion.of_single PEqualNP.Library.L063
