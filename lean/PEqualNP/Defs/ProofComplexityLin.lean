import PEqualNP.Defs.ProofComplexity
import Mathlib.Algebra.Ring.Parity

/-!
# Definitions of the proof complexity program: resolution over linear equations

The system Res(⊕) of Itsykson and Sokolov (MFCS 2014; Ann. Pure Appl. Logic 171(1), 2020):
resolution whose lines are disjunctions of linear equations over the field with two elements.
It is the weakest standard fragment of bounded-depth Frege with parity gates. The ruling is in
`ProofComplexity/README.md`.
-/

namespace PEqualNP.ProofComplexity

/-- A linear equation over the two-element field: `(f, b)` says that the sum of the variables
in `f` is `b`, that is, the number of variables of `f` set to true is odd exactly when `b` is
true. -/
abbrev LinEq (V : Type) : Type := Finset V × Bool

/-- A linear clause: a finite set of linear equations, read as their disjunction. -/
abbrev LinClause (V : Type) : Type := Finset (LinEq V)

/-- The assignment `a` satisfies the equation `q`. -/
def LinEqSat {V : Type} (a : V → Bool) (q : LinEq V) : Prop :=
  Odd (q.1.filter (fun v => a v = true)).card ↔ q.2 = true

/-- The assignment `a` satisfies the linear clause `C`: it satisfies some equation of `C`. -/
def LinClauseSat {V : Type} (a : V → Bool) (C : LinClause V) : Prop :=
  ∃ q ∈ C, LinEqSat a q

/-- A clause as a linear clause: the literal `(v, s)` becomes the equation `v = s`. -/
def linOfClause {V : Type} [DecidableEq V] (C : Clause V) : LinClause V :=
  C.image (fun l => (({l.1} : Finset V), l.2))

/-- The resolution rule of Res(⊕): `R` is obtained from `C` and `D` by resolving on a linear
form `f`, where `C` holds the equation `f = 0` and `D` holds `f = 1`. -/
def IsLinResolvent {V : Type} [DecidableEq V] (C D R : LinClause V) : Prop :=
  ∃ f : Finset V, (f, false) ∈ C ∧ (f, true) ∈ D ∧ R = C.erase (f, false) ∪ D.erase (f, true)

/-- `IsLinDerivation F π`: the list `π`, NEWEST LINE FIRST, is a Res(⊕) derivation from the
linear clauses `F`. Each line is a clause of `F`, a resolvent of two lines after it in the
list, or a weakening of one line after it: any linear clause satisfied by every assignment
that satisfies that line. The number of lines is `π.length`. -/
inductive IsLinDerivation {V : Type} [DecidableEq V] (F : Set (LinClause V)) :
    List (LinClause V) → Prop
  | nil : IsLinDerivation F []
  | ax {π : List (LinClause V)} {C : LinClause V} :
      IsLinDerivation F π → C ∈ F → IsLinDerivation F (C :: π)
  | res {π : List (LinClause V)} {C D R : LinClause V} :
      IsLinDerivation F π → C ∈ π → D ∈ π → IsLinResolvent C D R → IsLinDerivation F (R :: π)
  | weak {π : List (LinClause V)} {C D : LinClause V} :
      IsLinDerivation F π → C ∈ π → (∀ a : V → Bool, LinClauseSat a C → LinClauseSat a D) →
      IsLinDerivation F (D :: π)

/-- A Res(⊕) refutation of the CNF formula `F`: a Res(⊕) derivation from the clauses of `F`,
read as linear clauses, that contains the empty linear clause. -/
def IsLinRefutation {V : Type} [DecidableEq V] (F : Set (Clause V)) (π : List (LinClause V)) :
    Prop :=
  IsLinDerivation ((fun C => linOfClause C) '' F) π ∧ (∅ : LinClause V) ∈ π

end PEqualNP.ProofComplexity
