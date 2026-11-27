import PEqualNP.Defs.ProofComplexity

/-!
# Definitions of the P = NP algorithm search: clause learning by unit propagation

A model of the unsatisfiable runs of CDCL solvers that is independent of decisions, restarts
and deletion: the solver learns a sequence of clauses, each of which is RUP (reverse unit
propagation) with respect to the input and the clauses learned before it: assuming every
literal of the clause false, unit propagation falsifies some known clause. Every learning
scheme in use (any cut of the implication graph, first UIP, decision learning, clause
minimization) learns RUP clauses (Beame, Kautz and Sabharwal 2004). A run ends in an
unsatisfiability proof when it learns the empty clause.
-/

namespace PEqualNP.Search

open PEqualNP.ProofComplexity

/-- The complementary literal. -/
def negLit {V : Type} (l : Literal V) : Literal V := (l.1, !l.2)

/-- `UPForces Γ A l`: unit propagation over the clauses `Γ`, from the literals `A` assumed
true, makes `l` true: `l` is assumed, or some clause of `Γ` contains `l` and every other
literal of it is already made false. -/
inductive UPForces {V : Type} (Γ : Set (Clause V)) (A : Set (Literal V)) : Literal V → Prop
  | hyp {l : Literal V} : l ∈ A → UPForces Γ A l
  | unit {D : Clause V} {l : Literal V} : D ∈ Γ → l ∈ D →
      (∀ l' ∈ D, l' ≠ l → UPForces Γ A (negLit l')) → UPForces Γ A l

/-- `C` is RUP over `Γ`: assuming every literal of `C` false, unit propagation over `Γ` makes
every literal of some clause of `Γ` false. -/
def IsRUP {V : Type} (Γ : Set (Clause V)) (C : Clause V) : Prop :=
  ∃ D ∈ Γ, ∀ l ∈ D, UPForces Γ (negLit '' (↑C : Set (Literal V))) (negLit l)

/-- `IsRUPRun F ρ`: the clauses `ρ`, NEWEST FIRST, are learned in turn, each RUP over `F`
and the clauses learned before it. Its length is the number of learned clauses. -/
inductive IsRUPRun {V : Type} (F : Set (Clause V)) : List (Clause V) → Prop
  | nil : IsRUPRun F []
  | learn {ρ : List (Clause V)} {C : Clause V} :
      IsRUPRun F ρ → IsRUP (F ∪ {D | D ∈ ρ}) C → IsRUPRun F (C :: ρ)

end PEqualNP.Search
