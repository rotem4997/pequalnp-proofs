import PEqualNP.Library.Helpers.AlgEncode
import PEqualNP.Library.Helpers.AlgDiagonal

/-- Algebrization diagonal (Aaronson and Wigderson 2009, Theorem 5.3, combinatorial form): from
an enumeration of oracle polynomial-time deciders with local answers, every injective naming of
field elements admits an oracle `A` and a degree-2 extension `E` with NP^A not inside P^E. -/
theorem PEqualNP.Library.L070 : (∃ (g : ℕ → Language Bool → Language Bool) (q : ℕ → Polynomial ℕ), (∀ (A L : Language Bool), L ∈ PEqualNP.Library.OracleP A → ∃ i : ℕ, g i A = L) ∧ ∀ (i : ℕ) (A : Language Bool) (x : List Bool), ∃ Q : Finset (List Bool), Q.card ≤ (q i).eval x.length ∧ ∀ A' : Language Bool, (∀ y ∈ Q, y ∈ A ↔ y ∈ A') → (x ∈ g i A ↔ x ∈ g i A')) → ∀ codes : PEqualNP.Library.FieldCodes, PEqualNP.Library.FieldCodes.Injective codes → ∃ (A : Language Bool) (E : PEqualNP.Library.AlgExtension), PEqualNP.Library.IsMultiquadraticExtension A E ∧ ¬ PEqualNP.Library.OracleNP A ⊆ PEqualNP.Library.OracleP (PEqualNP.Library.extOracle codes E) :=
  PEqualNP.Library.Helpers.AlgDiagonal.of_enum PEqualNP.Library.Helpers.AlgEncode.prefix_unique
