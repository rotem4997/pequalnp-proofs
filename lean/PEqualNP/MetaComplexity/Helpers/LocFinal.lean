import PEqualNP.MetaComplexity.Helpers.LocAssemble
import PEqualNP.MetaComplexity.Helpers.LocLast

/-!
# The row of `L-meta-115`

All sixteen pieces of `LocPlan` are proved; this module applies the assembly.
-/

namespace PEqualNP.MetaComplexity.Loc.Final

open PEqualNP.MetaComplexity.Loc

/-- The monotone lower bound on graphs with long threads. -/
theorem row : RowStmt :=
  Assemble.row_of_last (Last.PLast_proof Wires.ToolProp_proof Wires.ToolU_proof)
    (Last.PFC_proof Removal.ToolRemoval_proof Wires.ToolLower_proof Clean.ToolSnoc_proof
      Wires.ToolLemma1a_proof Assemble.payPair Removal.ToolLive_proof
      Removal.ToolNoAlias_proof Assemble.cons)

end PEqualNP.MetaComplexity.Loc.Final
