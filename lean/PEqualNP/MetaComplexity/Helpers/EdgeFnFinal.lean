import PEqualNP.MetaComplexity.Helpers.EdgeFnOfFront
import PEqualNP.MetaComplexity.Helpers.EdgeFnFront

/-!
The class-form lower bound with every piece proved: for a graph in the class (T) (every cycle of
length at least 7, no walk shorter than 7 between two distinct vertices of degree at least 3)
with extra OR-variables no edge meets, every circuit over AND, OR, NOT (fan-in two, every gate
counted) for the edge function has `|A| + |E| + k ≤ size + 1` for every `k` below all covers.
-/

namespace PEqualNP.MetaComplexity.EdgeFn

/-- The main lemma, all pieces proved. -/
theorem stmtML_final : StmtML := ml_of_front stmtFront

/-- The class-form lower bound, all pieces proved. -/
theorem stmtLB_final : StmtLB := lb_of_front stmtFront

end PEqualNP.MetaComplexity.EdgeFn
