import PEqualNP.Defs.Expanders
import Mathlib

/-!
# Helpers: the permutation model of a bounded-degree bipartite graph (for L-pcx-043)

`b` permutations of `Fin (n+1)` give a bipartite graph with `n+1` pigeons and `n` holes:
pigeon `i` is joined to hole `j` when some permutation sends `i` to `j` (the extra point
`Fin.last n` is dropped). Every pigeon then has at most `b` holes and every hole at most `b`
pigeons. L-pcx-043 shows by counting that some choice of `b = 8` permutations is a boundary
expander.

The interface statements of the counting proof are recorded here as `Prop` definitions so
that the parts can be proved separately and assembled.
-/

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.Expanders

/-- The bipartite graph of `b` permutations of `Fin (n+1)`, the point `Fin.last n` dropped. -/
def permGraph {n b : ℕ} (σ : Fin b → Equiv.Perm (Fin (n + 1))) : BipGraph (n + 1) n :=
  fun i => Finset.univ.filter (fun j : Fin n => ∃ k, σ k i = j.castSucc)

/-- The permutation count (an upper bound suffices): the permutations of a finite type that
map `T` into `Y`. -/
def PermCountStmt : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (T Y : Finset α),
    (Finset.univ.filter (fun σ : Equiv.Perm α => ∀ x ∈ T, σ x ∈ Y)).card ≤
      Y.card.descFactorial T.card * (Fintype.card α - T.card).factorial

/-- The union bound is below one: for some `s₀ ≥ 5`, for all large `n`, the expected number of
left sets of size `1 ≤ t ≤ n / s₀` whose 8 images all lie in one set of `5 t` points is
below one. -/
def ArithStmt : Prop :=
  ∃ s₀ n₀ : ℕ, 5 ≤ s₀ ∧ ∀ n : ℕ, n₀ ≤ n →
    ∑ t ∈ Finset.Icc 1 (n / s₀),
      ((n + 1).choose t : ℝ) * ((n + 1).choose (5 * t) : ℝ) *
        (((5 * t).descFactorial t : ℝ) / ((n + 1).descFactorial t : ℝ)) ^ 8 < 1

end PEqualNP.ProofComplexity.Helpers
