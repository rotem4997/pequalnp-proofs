import PEqualNP.Library.L058
import PEqualNP.Library.L070

/-- The algebrization barrier (Aaronson and Wigderson, ACM Trans. Comput. Theory 1(1), 2009,
Theorem 5.3): for every injective naming of field elements there are an oracle `A` and an
extension `E` of `A` of degree at most 2 per variable over every finite field with NP^A not
inside P^E. So no algebrizing technique proves P = NP. -/
theorem PEqualNP.Library.L065 : ∀ codes : PEqualNP.Library.FieldCodes, PEqualNP.Library.FieldCodes.Injective codes → ∃ (A : Language Bool) (E : PEqualNP.Library.AlgExtension), PEqualNP.Library.IsMultiquadraticExtension A E ∧ ¬ PEqualNP.Library.OracleNP A ⊆ PEqualNP.Library.OracleP (PEqualNP.Library.extOracle codes E) :=
  PEqualNP.Library.L070 PEqualNP.Library.L058
