import PEqualNP.Library.L020
import PEqualNP.Library.L031
import PEqualNP.Library.SearchHelpers.KSatNP
import PEqualNP.Library.SearchHelpers.KSatHard

/-- 3-SAT is NP-complete (Karp 1972). It is in NP by a width filter into SAT, and SAT, which is
NP-complete (L-lib-031), reduces to it clause by clause with fresh variables; completeness then
transfers along the reduction (L-lib-020). -/
theorem PEqualNP.Library.L032 : PEqualNP.Library.NPComplete (PEqualNP.Search.KSAT 3) :=
  PEqualNP.Library.L020 PEqualNP.Search.SAT (PEqualNP.Search.KSAT 3) PEqualNP.Library.L031
    PEqualNP.Library.SearchHelpers.KSat.ksat3_in_NP
    PEqualNP.Library.SearchHelpers.KSat.sat_reduces_ksat3
