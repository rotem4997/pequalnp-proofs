import PEqualNP.Gct.Helpers.FactZ
import PEqualNP.Gct.Helpers.Rung.Statements

/-!
`BoundedZeros` (Fact Z) of the superquadratic rung, from `PEqualNP.Gct.Helpers.factz`.
-/

namespace PEqualNP.Gct.Rung

/-- Fact Z: `k` forms of degree `t` in `l` variables with only the trivial common zero bound the
finite zero sets of every system with those top forms, uniformly in the lower order terms. -/
theorem boundedZeros : BoundedZeros :=
  fun l k t g hgh hg => PEqualNP.Gct.Helpers.factz l k t g hgh hg

end PEqualNP.Gct.Rung
