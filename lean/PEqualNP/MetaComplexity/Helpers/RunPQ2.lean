import PEqualNP.MetaComplexity.Helpers.RunAsm6

/-!
# Run-of-four assembly, the q2 side (`AsmPQ2`), stage 1: two readers of `x_q2`

Paper: the run-of-four argument in direct form, section 5, (P-Q2), outcomes (q-a), (q-b).
Conjecture until the checker accepts. Stage 1 only: if two distinct gates read `x_q2` in the
least list, `Least.two_readers` gives Drop 3 at false or Drop 4 at true, i.e. one of the first
two outcomes of `AsmPQ2`. The single reader case is the open remainder (proved in the later files of this family).
-/

namespace PEqualNP.MetaComplexity.Helpers.RunAsm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers PEqualNP.MetaComplexity.Helpers.Forest
open PEqualNP.MetaComplexity.Loc PEqualNP.MetaComplexity.EdgeFn

/-- Two distinct readers of `x_q2` in a least list of a run of four give outcome (q-a) or (q-b). -/
theorem pq2_two_readers (n : ℕ) (G : SimpleGraph (Fin (n + 1))) (q0 q1 q2 q3 q4 q5 : Fin (n + 1))
    (gs : List Gate) (o : ℕ) (r : r4Run G q0 q1 q2 q3 q4 q5) (L : Least (n + 1) (F G ∅) gs o)
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p (q2 : ℕ)) (hq : Reads gs q (q2 : ℕ)) :
    Drop (F G ∅) q2 false 3 gs.length ∨ Drop (F G ∅) q2 true 4 gs.length := by
  obtain ⟨hD, -⟩ := r4_stmtG3 n G ∅ q0 q1 q2 q3 q4 q5 (fun i _ _ h => Finset.notMem_empty i h) r
  have hnc := hD.nc q2 (by simp)
  rcases L.two_readers q2 hnc p q hpq hp hq with ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨-, h4⟩
  · exact Or.inl h3
  · exact Or.inl (h4.mono (by norm_num) le_rfl)
  · exact Or.inr h4

end PEqualNP.MetaComplexity.Helpers.RunAsm
