import PEqualNP.Defs.ProofComplexity

/-!
# Definitions of the proof complexity program: restriction of a CNF by a partial assignment

A partial assignment `ρ : V → Option Bool` sets the variables `v` with `ρ v = some b` and
leaves the variables with `ρ v = none` free. Restricting a clause by `ρ`: if `ρ` makes some
literal of the clause true, the clause is satisfied and disappears; otherwise the literals on
set variables (all false under `ρ`) are removed and the literals on free variables remain.
Variable names do not change: the restricted formula is a set of clauses on the same type `V`
in which set variables no longer occur.

Instance in use: setting every pigeonhole variable outside the edges of a bipartite graph to
false turns the pigeonhole formula into the graph pigeonhole formula of that graph.
-/

namespace PEqualNP.ProofComplexity

/-- The restriction of the clause `C` by the partial assignment `ρ`: `none` when `ρ` makes some
literal of `C` true, otherwise the literals of `C` on the variables `ρ` leaves free. -/
def restrictClause {V : Type} [DecidableEq V] (ρ : V → Option Bool) (C : Clause V) :
    Option (Clause V) :=
  if ∃ l ∈ C, ρ l.1 = some l.2 then none else some (C.filter fun l => ρ l.1 = none)

/-- The restriction of the CNF formula `F` by `ρ`: the restrictions of its clauses that `ρ`
does not satisfy. -/
def restrictCNF {V : Type} [DecidableEq V] (F : Set (Clause V)) (ρ : V → Option Bool) :
    Set (Clause V) :=
  {C' | ∃ C ∈ F, restrictClause ρ C = some C'}

end PEqualNP.ProofComplexity
