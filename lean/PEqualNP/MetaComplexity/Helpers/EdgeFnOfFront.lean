import PEqualNP.MetaComplexity.Helpers.EdgeFnGraphPlan
import PEqualNP.MetaComplexity.Helpers.EdgeFnExt
import PEqualNP.MetaComplexity.Helpers.EdgeFnExch
import PEqualNP.MetaComplexity.Helpers.EdgeFnLift
import PEqualNP.MetaComplexity.Helpers.EdgeFnXMove
import PEqualNP.MetaComplexity.Helpers.EdgeFnAnd
import PEqualNP.MetaComplexity.Helpers.EdgeFnWin
import PEqualNP.MetaComplexity.Helpers.EdgeFnTwo

/-!
The class-form lower bound from the one remaining piece, the frontier gate.
-/

namespace PEqualNP.MetaComplexity.EdgeFn

/-- The main lemma from the frontier piece alone. -/
theorem ml_of_front (hFront : StmtFront) : StmtML :=
  stmtML stmtAnd (stmtExt stmtLift stmtXMove hFront stmtWin (stmtTwo stmtExch stmtWin))

/-- The class-form lower bound from the frontier piece alone. -/
theorem lb_of_front (hFront : StmtFront) : StmtLB := lb_of_ml (ml_of_front hFront)

end PEqualNP.MetaComplexity.EdgeFn
