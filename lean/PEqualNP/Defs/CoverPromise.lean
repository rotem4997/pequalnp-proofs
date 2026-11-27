import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Lattice.Fold
import PEqualNP.Defs.Search

/-!
# Definitions of the promise vertex cover reduction

The objects of the reduction from CNF satisfiability to promise vertex cover, stated over the
CNF formulas of `Defs/Search.lean`.

* The textbook graph of a CNF formula: two literal vertices for every variable that occurs,
  joined by an edge; a vertex for every occurrence of a literal in a clause, with a clique on
  the occurrences of each clause; and each occurrence joined to its literal.
* A vertex cover: a finite set of vertices meeting every edge.
* The reduction: append a fresh positive literal `y` to every clause and add the unit clause
  `¬y`; the graph is the textbook graph of the new formula.
* The cover: the one read off the all-true assignment (the literal "true" of every variable,
  and every occurrence except the first true one in its clause).
-/

namespace PEqualNP.MetaComplexity.CoverPromise

open PEqualNP.Search

/-- The vertices: a literal `(x, b)`, or an occurrence `(i, j)`, the `j`-th literal of the
`i`-th clause (both counted from `0`). Only finitely many of them carry edges in the graphs below;
the others are isolated and play no role for vertex covers. -/
abbrev Vertex : Type := Literal ⊕ (ℕ × ℕ)

/-- The variables that occur in a formula. -/
def vars (ψ : CNF) : Finset ℕ :=
  (ψ.flatMap (List.map Prod.fst)).toFinset

/-- The `i`-th clause of a formula, the empty clause past its end. -/
def clauseAt (ψ : CNF) (i : ℕ) : Clause :=
  ψ.getD i []

/-- Adjacency of the textbook graph of a formula `ψ`: the two literals of an occurring
variable; two distinct occurrences of the same clause; an occurrence and its literal. -/
def satAdj (ψ : CNF) : Vertex → Vertex → Prop
  | .inl a, .inl b => a.1 = b.1 ∧ a.2 ≠ b.2 ∧ a.1 ∈ vars ψ
  | .inr (i, j), .inr (k, l) =>
      i = k ∧ j ≠ l ∧ j < (clauseAt ψ i).length ∧ l < (clauseAt ψ i).length
  | .inr (i, j), .inl a => (clauseAt ψ i)[j]? = some a
  | .inl a, .inr (i, j) => (clauseAt ψ i)[j]? = some a

/-- The textbook graph of a formula `ψ` (reduction from CNF satisfiability to vertex
cover). -/
def satGraph (ψ : CNF) : SimpleGraph Vertex where
  Adj := satAdj ψ
  symm := ⟨by
    rintro (⟨x, a⟩ | ⟨i, j⟩) (⟨y, b⟩ | ⟨k, l⟩) h <;> simp only [satAdj] at h ⊢
    · exact ⟨h.1.symm, h.2.1.symm, h.1 ▸ h.2.2⟩
    · exact h
    · exact h
    · obtain ⟨rfl, h1, h2, h3⟩ := h
      exact ⟨rfl, Ne.symm h1, h3, h2⟩⟩
  loopless := ⟨by
    rintro (⟨x, a⟩ | ⟨i, j⟩) h <;> simp [satAdj] at h⟩

/-- A vertex cover: a finite set of vertices meeting every edge. -/
def IsVertexCover {V : Type} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S

/-- The cover read off an assignment `σ`: the literal `(x, σ x)` of every occurring
variable, and every occurrence except the first one that is true under `σ` in its clause
(`List.findIdx` is the length of the clause when no literal of it is true). -/
def coverOf (ψ : CNF) (σ : Assignment) : Finset Vertex :=
  ((vars ψ).image fun x => (x, σ x)).disjSum
    ((Finset.range ψ.length).biUnion fun i =>
      ((Finset.range (clauseAt ψ i).length).filter
        (fun j => j ≠ (clauseAt ψ i).findIdx (Literal.eval σ))).image fun j => (i, j))

/-- A variable that does not occur in `φ`: one more than the largest that does. -/
def fresh (φ : CNF) : ℕ :=
  (vars φ).sup id + 1

/-- `φ' = {C ∨ y : C ∈ φ} ∪ {¬y}` with `y = fresh φ`. -/
def cvcFormula (φ : CNF) : CNF :=
  φ.map (fun C => C ++ [(fresh φ, true)]) ++ [[(fresh φ, false)]]

/-- The graph of the reduction: the textbook graph of `φ'`. -/
def cvcGraph (φ : CNF) : SimpleGraph Vertex :=
  satGraph (cvcFormula φ)

/-- The cover of the reduction: the cover of the textbook graph of `φ'` read off the
assignment "every variable true" (which falsifies exactly the clause `¬y` of `φ'`). -/
def cvcCover (φ : CNF) : Finset Vertex :=
  coverOf (cvcFormula φ) (fun _ => true)

end PEqualNP.MetaComplexity.CoverPromise
