import PEqualNP.Library.Evasion.NoCollapse
import PEqualNP.Library.Evasion.Pure
import PEqualNP.Library.Evasion.Clock
import PEqualNP.Library.Evasion.Patch

namespace PEqualNP.Library.Evasion

/-- The padding form of the time hierarchy, with every piece proved. -/
theorem noScaledCollapse : StmtNoScaledCollapse :=
  noScaledCollapse_of_pieces t5b t5d t5e clk dtimeoO

end PEqualNP.Library.Evasion
