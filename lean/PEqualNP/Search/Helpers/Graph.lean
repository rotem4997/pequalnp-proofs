import PEqualNP.Defs

/-!
# Helpers: graphs with numbered edges, for Tseitin formulas

Used by the refutation of `L-alg-002`. Vertices are `Fin m`, edges are `Fin n` (the edges are
the variables of the Tseitin formula), and each edge has two different ends.
-/

namespace PEqualNP.Search.Helpers

/-- A loopless multigraph with vertices `Fin m` and numbered edges `Fin n`. -/
structure EdgeGraph (m n : ℕ) where
  ends : Fin n → Fin m × Fin m
  loopless : ∀ e, (ends e).1 ≠ (ends e).2

variable {m n : ℕ}

/-- The edges at vertex `v`. -/
def EdgeGraph.incident (G : EdgeGraph m n) (v : Fin m) : Finset (Fin n) :=
  Finset.univ.filter fun e => (G.ends e).1 = v ∨ (G.ends e).2 = v

/-- `u` and `w` are joined by an edge outside `S`. -/
def EdgeGraph.Adj (G : EdgeGraph m n) (S : Finset (Fin n)) (u w : Fin m) : Prop :=
  ∃ e, e ∉ S ∧ (G.ends e = (u, w) ∨ G.ends e = (w, u))

/-- `w` is reachable from `u` in the graph with the edges of `S` deleted. -/
def EdgeGraph.Reach (G : EdgeGraph m n) (S : Finset (Fin n)) : Fin m → Fin m → Prop :=
  Relation.ReflTransGen (G.Adj S)

open Classical in
/-- The component of `v`, after deleting the edges of `S`, has more than half the vertices. -/
def EdgeGraph.BigComp (G : EdgeGraph m n) (S : Finset (Fin n)) (v : Fin m) : Prop :=
  m < 2 * (Finset.univ.filter fun u => G.Reach S v u).card

end PEqualNP.Search.Helpers
