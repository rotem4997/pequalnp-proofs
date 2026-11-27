import PEqualNP.Gct.Helpers.Kneser.SubalgFinite
import PEqualNP.Gct.Helpers.Kneser.ETransform
import PEqualNP.Gct.Helpers.Kneser.Assembly

/-- Kneser for codes over the complex numbers (Mirandola and Zemor 2015, Theorem 3.3): for nonzero
subspaces `S`, `T` of `ℂ^n` with coordinatewise product `S * T` and stabilizer `St` of the
product, `dim S + dim T ≤ dim (S * T) + dim St`. From the finiteness of the set of subalgebras
of `ℂ^n`, the e-transform lemma, and a covering argument with a reduction to full support. -/
theorem PEqualNP.Gct.L065 : ∀ (n : ℕ) (S T St : Submodule ℂ (Fin n → ℂ)), S ≠ ⊥ → T ≠ ⊥ → (∀ x, x ∈ St ↔ ∀ v ∈ S * T, x * v ∈ S * T) → Module.finrank ℂ S + Module.finrank ℂ T ≤ Module.finrank ℂ (S * T) + Module.finrank ℂ St :=
  PEqualNP.Gct.Helpers.Kneser.kneser_of PEqualNP.Gct.Helpers.Kneser.finite_subalgebra
    PEqualNP.Gct.Helpers.Kneser.etransform
