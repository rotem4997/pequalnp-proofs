import PEqualNP.Defs
import PEqualNP.Gct.Helpers.FermatFromKneser

/-! L-gct-066: Kneser's theorem for codes over `ℂ` (the statement of L-gct-065) implies the sharp
Fermat lemma (the statement of L-gct-061): a linear space in `ℂ^M` on which both power sums
`p2` and `p3` vanish has dimension at most `M/3`. Proof notes: Gct/FermatProof.md. -/

theorem PEqualNP.Gct.L066 :
    (∀ (n : ℕ) (S T St : Submodule ℂ (Fin n → ℂ)), S ≠ ⊥ → T ≠ ⊥ → (∀ x, x ∈ St ↔ ∀ v ∈ S * T, x * v ∈ S * T) → Module.finrank ℂ S + Module.finrank ℂ T ≤ Module.finrank ℂ (S * T) + Module.finrank ℂ St) → (∀ (M : ℕ) (W : Submodule ℂ (Fin M → ℂ)), (∀ x ∈ W, ∑ i, x i ^ 2 = 0) → (∀ x ∈ W, ∑ i, x i ^ 3 = 0) → 3 * Module.finrank ℂ W ≤ M) :=
  fun hK => PEqualNP.Gct.Helpers.fermat_of_kneser hK
