import PEqualNP.Gct.Helpers.Rung.AssemblyRestriction
import PEqualNP.Gct.Helpers.Rung.Arith
import PEqualNP.Gct.Helpers.Rung.Avoidance
import PEqualNP.Gct.Helpers.Rung.LemmaE
import PEqualNP.Gct.Helpers.Rung.RowSpaceExists
import PEqualNP.Gct.Helpers.Rung.RowSystem
import PEqualNP.Gct.Helpers.Rung.BoundedZeros
import PEqualNP.Gct.Helpers.Rung.FewRows
import PEqualNP.Gct.Helpers.Rung.GoodSubspace
import PEqualNP.Gct.L053

/-!
# The rung, with one step left as a hypothesis

Every step of the chain to the statement of L-gct-057 except the block-sum permanent identity
(`BlockPerm`), which stays a hypothesis here.
-/

namespace PEqualNP.Gct.Rung

/-- The block-sum permanent identity gives the statement of L-gct-057. -/
theorem stmt057_of_blockPerm (h : BlockPerm) : Stmt057 :=
  assemblyRestriction (rowSpaceExists avoidance lemmaE) (fewRows rowSystem boundedZeros)
    goodSubspace h arith PEqualNP.Gct.L053

end PEqualNP.Gct.Rung
