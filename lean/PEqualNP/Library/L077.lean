import PEqualNP.Library.Helpers.AlgCollapseFacts
import PEqualNP.Library.Helpers.AlgCollapse

/-- Algebrizing collapse from the verifier enumeration (mirrors L-lib-072): a padded oracle `A`
and its multilinear extension `E` over every finite field have NP^E inside P^A. -/
theorem PEqualNP.Library.L077 : (∃ (g : ℕ → Language Bool → Set (List Bool × List Bool)) (r : ℕ → Polynomial ℕ), (∀ (A : Language Bool) (R : Set (List Bool × List Bool)), PEqualNP.Library.OracleDecidableInPolyTime A PEqualNP.Library.encodePair R → ∃ i : ℕ, g i A = R) ∧ ∀ (i : ℕ) (A A' : Language Bool) (x w : List Bool), (∀ y : List Bool, y.length ≤ (r i).eval (x.length + w.length) → (y ∈ A ↔ y ∈ A')) → ((x, w) ∈ g i A ↔ (x, w) ∈ g i A')) → ∀ codes : PEqualNP.Library.FieldCodes, PEqualNP.Library.FieldCodes.Injective codes → ∃ (A : Language Bool) (E : PEqualNP.Library.AlgExtension), PEqualNP.Library.IsMultiquadraticExtension A E ∧ PEqualNP.Library.OracleNP (PEqualNP.Library.extOracle codes E) ⊆ PEqualNP.Library.OracleP A :=
  PEqualNP.Library.Helpers.AlgCollapse.of_enum PEqualNP.Library.Helpers.AlgCollapseFacts.mlext_ext
    PEqualNP.Library.Helpers.AlgCollapseFacts.extOracle_mlext_congr
