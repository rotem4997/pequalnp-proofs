import PEqualNP.Defs
import PEqualNP.Gct.L065
import PEqualNP.Gct.L066

/-! L-gct-061 (sharp Fermat lemma): a complex linear space in `ℂ^M` on which both power sums
`x_1^2 + ... + x_M^2` and `x_1^3 + ... + x_M^3` vanish has dimension at most `M/3`.
It is L-gct-066 (Kneser implies Fermat) applied to L-gct-065 (Kneser for codes over `ℂ`). -/

theorem PEqualNP.Gct.L061 :
    ∀ (M : ℕ) (W : Submodule ℂ (Fin M → ℂ)), (∀ x ∈ W, ∑ i, x i ^ 2 = 0) → (∀ x ∈ W, ∑ i, x i ^ 3 = 0) → 3 * Module.finrank ℂ W ≤ M :=
  PEqualNP.Gct.L066 PEqualNP.Gct.L065
