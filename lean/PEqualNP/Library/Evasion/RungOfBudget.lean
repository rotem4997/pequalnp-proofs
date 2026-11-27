import PEqualNP.Library.Evasion.RungPlan
import PEqualNP.Library.Evasion.NoCollapseFinal
import PEqualNP.Library.Evasion.MConstr
import PEqualNP.Library.Evasion.MGuard
import PEqualNP.Library.Evasion.MTrans
import PEqualNP.Library.Evasion.MED
import PEqualNP.Library.Evasion.MPadExp
import PEqualNP.Library.Evasion.MRoot

namespace PEqualNP.Library.Evasion

/-- The rung from the one remaining machine piece, the budgeted verifier run. -/
theorem rung_of_budget (hB : StmtBudget) : StmtRung :=
  rung_of_machine_pieces rootDom padExp clk padClock constrComp constrAff hB lenGuard fixLead
    notTime toPairBody ed noScaledCollapse

end PEqualNP.Library.Evasion
