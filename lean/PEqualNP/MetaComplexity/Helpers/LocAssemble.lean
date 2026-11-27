import PEqualNP.MetaComplexity.Helpers.LocRemoval
import PEqualNP.MetaComplexity.Helpers.LocClean
import PEqualNP.MetaComplexity.Helpers.LocWires
import PEqualNP.MetaComplexity.Helpers.LocRes
import PEqualNP.MetaComplexity.Helpers.LocStruct
import PEqualNP.MetaComplexity.Helpers.LocFree
import PEqualNP.MetaComplexity.Helpers.LocFan
import PEqualNP.MetaComplexity.Helpers.LocCellA
import PEqualNP.MetaComplexity.Helpers.LocReadOne

/-!
# The row of `L-meta-115` from its last two pieces

Every piece of `LocPlan` except `PLast` and `PFC` is proved in the `Loc*` modules; this module
feeds them to the assembly, so the row follows from those two.
-/

namespace PEqualNP.MetaComplexity.Loc.Assemble

open PEqualNP.MetaComplexity.Loc

theorem pay0 : ToolPay0 :=
  Free.ToolPay0_proof Clean.ToolRestrict_proof Res.ToolRes0_proof Res.ToolDrop0_proof

theorem pay1 : ToolPay1 :=
  Free.ToolPay1_proof Clean.ToolRestrict_proof Res.ToolRes1_proof Res.ToolDrop1_proof

theorem payPair : ToolPayPair :=
  Free.ToolPayPair_proof Clean.ToolRestrict_proof Clean.ToolLeast_proof Res.ToolResPair_proof
    Res.ToolDropPair_proof

theorem cons : ToolCons := Fan.ToolCons_proof Wires.ToolLemma1a_proof Wires.ToolMono_proof

/-- The row from the last cell and the pair step. -/
theorem row_of_last (hLast : PLast) (hFC : PFC) : RowStmt :=
  loc_of_pieces Struct.PClosure_proof Struct.PStructure_proof Free.PBase_proof
    (Free.PS1_proof Clean.ToolLeast_proof Removal.ToolRemoval_proof Clean.ToolRestrict_proof
      Res.ToolResA_proof)
    (Free.PLeafLow_proof Clean.ToolLeast_proof Removal.ToolRemoval_proof
      Clean.ToolRestrict_proof Res.ToolRes0_proof Res.ToolRes1_proof)
    (Free.PTwin_proof Clean.ToolLeast_proof Removal.ToolRemoval_proof Clean.ToolRestrict_proof
      Res.ToolRes0_proof)
    Clean.ToolLeast_proof
    (Fan.PFanLow_proof Removal.ToolRemoval_proof Removal.ToolLive_proof pay0)
    (Fan.PFanTwo_proof Removal.ToolRemoval_proof Removal.ToolLive_proof
      Removal.ToolNoAlias_proof pay0 pay1)
    (CellA.PCellA_proof Removal.ToolRemoval_proof Removal.ToolNoAlias_proof
      Removal.ToolLive_proof pay0 pay1 Wires.ToolProp_proof Wires.ToolMono_proof)
    (Fan.PReadFew_proof Removal.ToolRemoval_proof Removal.ToolLive_proof pay1)
    (ReadOne.PReadOneAnd_proof Wires.ToolProp_proof Wires.ToolMono_proof cons pay1
      Removal.ToolRemoval_proof Removal.ToolLive_proof Removal.ToolNoAlias_proof)
    (ReadOne.PReadOneOr_proof Wires.ToolProp_proof Wires.ToolMono_proof cons pay1
      Removal.ToolRemoval_proof Removal.ToolLive_proof Removal.ToolNoAlias_proof)
    (Fan.PReadTwo_proof Removal.ToolRemoval_proof Removal.ToolLive_proof
      Removal.ToolNoAlias_proof Wires.ToolMono_proof pay1)
    hLast hFC

end PEqualNP.MetaComplexity.Loc.Assemble
