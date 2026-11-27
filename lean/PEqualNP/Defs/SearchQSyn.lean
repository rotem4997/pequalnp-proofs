import PEqualNP.Defs.SearchQ

/-!
# Definitions of the P = NP algorithm search: Res(lin) over the integers with syntactic rules

The system R(lin) of Raz and Tzameret (Ann. Pure Appl. Logic 155, 2008) with only syntactic
rules. The semantic one-line weakening of `IsResLinQDerivation` makes every tautology one step
from any axiom, and over the integers some counting principles are short tautologies (the
refutation of L-alg-004), so size lower bounds for pigeonhole-type formulas are false there.
Here a line may only grow by adding equations, the equations `0 = c` with `c ≠ 0` may be
dropped, and the Boolean axioms `x = 0 ∨ x = 1` are given.
-/

namespace PEqualNP.Search

/-- `IsResLinQSynDerivation F π`: the list `π` of lines is an R(lin) derivation from the
clauses `F` with syntactic rules, NEWEST LINE FIRST. Rules: an axiom (exactly the equations of
the literals of a clause of `F`); the Boolean axiom `v = 0 ∨ v = 1`; resolution as in
`IsResLinQDerivation` (an integer combination of the first equations of two earlier lines,
followed by the rest of both); weakening (any line containing every equation of an earlier
line); simplification (an earlier line with its equations of the form `0 = c`, `c ≠ 0`,
removed). -/
inductive IsResLinQSynDerivation {V : Type} [Fintype V] [DecidableEq V]
    (F : Set (PEqualNP.ProofComplexity.Clause V)) : List (QLine V) → Prop
  | nil : IsResLinQSynDerivation F []
  | ax {π : List (QLine V)} {L : QLine V} (C : PEqualNP.ProofComplexity.Clause V) :
      IsResLinQSynDerivation F π → C ∈ F → (∀ e, e ∈ L ↔ ∃ l ∈ C, e = litQEq l) →
      IsResLinQSynDerivation F (L :: π)
  | bool {π : List (QLine V)} (v : V) :
      IsResLinQSynDerivation F π →
      IsResLinQSynDerivation F ([litQEq (v, false), litQEq (v, true)] :: π)
  | res {π : List (QLine V)} {e e' : QEq V} {C D : QLine V} (α β : ℤ) :
      IsResLinQSynDerivation F π → (e :: C) ∈ π → (e' :: D) ∈ π →
      IsResLinQSynDerivation F (((α • e.1 + β • e'.1, α * e.2 + β * e'.2) :: (C ++ D)) :: π)
  | weaken {π : List (QLine V)} {C D : QLine V} :
      IsResLinQSynDerivation F π → C ∈ π → (∀ e ∈ C, e ∈ D) →
      IsResLinQSynDerivation F (D :: π)
  | simp {π : List (QLine V)} {C : QLine V} :
      IsResLinQSynDerivation F π → C ∈ π →
      IsResLinQSynDerivation F (C.filter (fun e => ¬ (e.1 = 0 ∧ e.2 ≠ 0)) :: π)

/-- A syntactic R(lin) refutation: a derivation containing the empty line. -/
def IsResLinQSynRefutation {V : Type} [Fintype V] [DecidableEq V]
    (F : Set (PEqualNP.ProofComplexity.Clause V)) (π : List (QLine V)) : Prop :=
  IsResLinQSynDerivation F π ∧ ([] : QLine V) ∈ π

end PEqualNP.Search
