import PEqualNP.Library.L071
import PEqualNP.Library.L072

/-- Baker, Gill and Solovay (SIAM J. Comput. 4(4), 1975), Theorem 1: some oracle makes NP equal
to P. Here by a padded oracle defined by recursion on length (`L-lib-072`) on the countable family
of oracle verifiers (`L-lib-071`), with no universal machine. -/
theorem PEqualNP.Library.L061 :
    ∃ A : Language Bool, PEqualNP.Library.OracleP A = PEqualNP.Library.OracleNP A :=
  PEqualNP.Library.L072 PEqualNP.Library.L071
