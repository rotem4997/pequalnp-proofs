import PEqualNP.Defs.ProofComplexityLin

/-!
# Definitions of the proof complexity program: Res(k, ⊕)

Resolution whose lines are disjunctions of conjunctions of at most `k` linear equations over
the field with two elements: the system that extends Res(⊕) (the case `k = 1`) the way the
`k`-DNF resolution Res(k) of Krajicek (Fund. Math. 170, 2001) extends resolution. Rules: cut on
a term, and-introduction, and weakening.

The weakening relation is a parameter of the derivation predicate, because the choice matters.
With FULL semantic weakening (`LinKSemWeak`) the system is trivial once `k` reaches the clause
width: the line whose terms say "clause `i` is false" is a tautology, and one cut against each
axiom empties it. The system we study uses `IsLinKWeakening`: term by term, a term of the
premise implies one term of the conclusion, or implies the disjunction of the one-equation
terms of the conclusion. At `k = 1` this is exactly the semantic weakening of Res(⊕). The
ruling is in `ProofComplexity/README.md`.
-/

namespace PEqualNP.ProofComplexity

/-- A term: a finite set of linear equations, read as their conjunction. The empty term is
true. -/
abbrev LinTerm (V : Type) : Type := Finset (LinEq V)

/-- A line of Res(k, ⊕): a finite set of terms, read as their disjunction. The empty line is
false. -/
abbrev LinKLine (V : Type) : Type := Finset (LinTerm V)

/-- The assignment `a` satisfies the term `T`: it satisfies every equation of `T`. -/
def LinTermSat {V : Type} (a : V → Bool) (T : LinTerm V) : Prop :=
  ∀ q ∈ T, LinEqSat a q

/-- The assignment `a` satisfies the line `L`: it satisfies some term of `L`. -/
def LinKLineSat {V : Type} (a : V → Bool) (L : LinKLine V) : Prop :=
  ∃ T ∈ L, LinTermSat a T

/-- The complementary equation: `f = b` becomes `f = b + 1`. -/
def negLinEq {V : Type} (q : LinEq V) : LinEq V := (q.1, !q.2)

/-- A clause as a line: one one-equation term `{v = s}` for each literal `(v, s)`. -/
def linKOfClause {V : Type} [DecidableEq V] (C : Clause V) : LinKLine V :=
  (linOfClause C).image (fun q => ({q} : LinTerm V))

/-- The cut rule: `C` holds the term `T`, `D` holds the one-equation term of the complement of
every equation of `T`, and `R` is the rest of `C` together with the rest of `D`. -/
def IsLinKCut {V : Type} [DecidableEq V] (C D R : LinKLine V) : Prop :=
  ∃ T : LinTerm V, T ∈ C ∧ (∀ e ∈ T, ({negLinEq e} : LinTerm V) ∈ D) ∧
    R = C.erase T ∪ (D \ T.image (fun e => ({negLinEq e} : LinTerm V)))

/-- And-introduction: from `C` holding `T₁` and `D` holding `T₂`, the rest of both together
with the term `T₁ ∪ T₂`. -/
def IsLinKAndIntro {V : Type} [DecidableEq V] (C D R : LinKLine V) : Prop :=
  ∃ T₁ T₂ : LinTerm V, T₁ ∈ C ∧ T₂ ∈ D ∧ R = (C.erase T₁ ∪ D.erase T₂) ∪ {T₁ ∪ T₂}

/-- Termwise weakening: every term of `L` implies a single term of `M`, or implies the
disjunction of the one-equation terms of `M`. -/
def IsLinKWeakening {V : Type} (L M : LinKLine V) : Prop :=
  ∀ T ∈ L, (∃ S ∈ M, ∀ a : V → Bool, LinTermSat a T → LinTermSat a S) ∨
    (∀ a : V → Bool, LinTermSat a T → ∃ q : LinEq V, ({q} : LinTerm V) ∈ M ∧ LinEqSat a q)

/-- Full semantic weakening: every assignment satisfying `L` satisfies `M`. Named only to
state that it makes the system trivial. -/
def LinKSemWeak {V : Type} (L M : LinKLine V) : Prop :=
  ∀ a : V → Bool, LinKLineSat a L → LinKLineSat a M

/-- `IsLinKDerivation k W F π`: the list `π`, NEWEST LINE FIRST, is a derivation from the lines
`F` in which every term of every line has at most `k` equations. Each line is a line of `F`,
or follows from two lines after it in the list by cut or by and-introduction, or from one line
after it by the weakening relation `W`. The number of lines is `π.length`. -/
inductive IsLinKDerivation {V : Type} [DecidableEq V] (k : ℕ)
    (W : LinKLine V → LinKLine V → Prop) (F : Set (LinKLine V)) : List (LinKLine V) → Prop
  | nil : IsLinKDerivation k W F []
  | ax {π : List (LinKLine V)} {C : LinKLine V} :
      IsLinKDerivation k W F π → C ∈ F → (∀ T ∈ C, T.card ≤ k) →
      IsLinKDerivation k W F (C :: π)
  | cut {π : List (LinKLine V)} {C D R : LinKLine V} :
      IsLinKDerivation k W F π → C ∈ π → D ∈ π → IsLinKCut C D R → (∀ T ∈ R, T.card ≤ k) →
      IsLinKDerivation k W F (R :: π)
  | andIntro {π : List (LinKLine V)} {C D R : LinKLine V} :
      IsLinKDerivation k W F π → C ∈ π → D ∈ π → IsLinKAndIntro C D R →
      (∀ T ∈ R, T.card ≤ k) → IsLinKDerivation k W F (R :: π)
  | weak {π : List (LinKLine V)} {C D : LinKLine V} :
      IsLinKDerivation k W F π → C ∈ π → W C D → (∀ T ∈ D, T.card ≤ k) →
      IsLinKDerivation k W F (D :: π)

/-- A Res(k, ⊕) refutation of the CNF formula `F`, with termwise weakening: a derivation from
the clauses of `F`, read as lines, that contains the empty line. -/
def IsLinKRefutation {V : Type} [DecidableEq V] (k : ℕ) (F : Set (Clause V))
    (π : List (LinKLine V)) : Prop :=
  IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' F) π ∧ (∅ : LinKLine V) ∈ π

end PEqualNP.ProofComplexity
