import PEqualNP.Library.SearchHelpers.TableauSound
import PEqualNP.Library.SearchHelpers.TableauComplete
import PEqualNP.Library.SearchHelpers.TableauStepCPT
import PEqualNP.Library.SearchHelpers.TableauEdgeCPT
import PEqualNP.Library.SearchHelpers.TableauAssembly

/-- SAT is NP-complete (Cook 1971, Levin 1973). SAT is in NP (L-lib-029). For hardness, an NP
verifier compiles to a micro-instruction code; the input is mapped to the encoding of the tableau
formula of that code, which is satisfiable exactly when some witness makes the code accept, and
whose encoding is written in polynomial time. -/
theorem PEqualNP.Library.L031 : PEqualNP.Library.NPComplete PEqualNP.Search.SAT :=
  PEqualNP.Library.SearchHelpers.Tab.npComplete_SAT_of
    (fun c zs m T hz h => PEqualNP.Library.SearchHelpers.Tab.accepts_of_sat c zs m T hz h)
    (fun c zs m T hz w hw h => PEqualNP.Library.SearchHelpers.Tab.sat_of_accepts c zs m T hz w hw h)
    (fun c p q => PEqualNP.Library.SearchHelpers.Tab.cpt_tableau_of c p q
      (PEqualNP.Library.SearchHelpers.Tab.cpt_stepPart c p q))
