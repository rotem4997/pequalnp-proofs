import PEqualNP.Library.L071
import PEqualNP.Library.L077

/-- Algebrization blocks proofs of P != NP (Aaronson and Wigderson, ACM Trans. Comput. Theory
1(1), 2009): for every injective naming of field elements there are an oracle `A` and an
extension `E` of `A` of degree at most 2 per variable over every finite field with NP^E inside
P^A. Here by a padded oracle, with no PSPACE-complete set. -/
theorem PEqualNP.Library.L076 : ∀ codes : PEqualNP.Library.FieldCodes, PEqualNP.Library.FieldCodes.Injective codes → ∃ (A : Language Bool) (E : PEqualNP.Library.AlgExtension), PEqualNP.Library.IsMultiquadraticExtension A E ∧ PEqualNP.Library.OracleNP (PEqualNP.Library.extOracle codes E) ⊆ PEqualNP.Library.OracleP A :=
  PEqualNP.Library.L077 PEqualNP.Library.L071
