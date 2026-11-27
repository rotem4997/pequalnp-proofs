import PEqualNP.Library.L058
import PEqualNP.Library.Helpers.BGSSeparation

/-- Baker, Gill and Solovay (SIAM J. Comput. 4(4), 1975), Theorem 3: some oracle separates P
from NP. The enumeration `L-lib-058`, the diagonal `L-lib-059` and the verifier `L-lib-060`. -/
theorem PEqualNP.Library.L062 :
    ∃ B : Language Bool, PEqualNP.Library.OracleP B ≠ PEqualNP.Library.OracleNP B :=
  PEqualNP.Library.Helpers.BGS.separation_of_enum PEqualNP.Library.L058
