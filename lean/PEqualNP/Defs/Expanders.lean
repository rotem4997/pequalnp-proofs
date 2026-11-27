import PEqualNP.Defs.ProofComplexity

/-!
# Bipartite graphs, boundary expansion, and pigeonhole formulas on a graph

Needed by the proof complexity chain to L-pcx-017 (Res(+) lower bounds for the pigeonhole
formula through polynomial calculus degree on an expander). The pinned Mathlib has no
bipartite expanders.

* A bipartite graph with left vertices `Fin m` (pigeons) and right vertices `Fin N` (holes) is
  the neighbourhood of each left vertex, `BipGraph m N := Fin m → Finset (Fin N)`.
* The unique neighbours of a left set `T`: the right vertices with exactly one neighbour in `T`.
  `G` is an `(s, δ)` boundary expander when every left set of at most `s` vertices has at least
  `δ` times as many unique neighbours as it has vertices.
* The variables of a pigeonhole formula on `G` are its edges, `GEdge G`, so that the number of
  variables is the number of edges (on the complete graph it would be quadratic).
* `graphPHP G`: for each pigeon, "it sits in some neighbouring hole"; for each hole and two
  different neighbouring pigeons, "not both". This is exactly what restricting `PHP` to the
  edges of `G` gives. `funGraphPHP G` adds, for each pigeon and two different neighbouring
  holes, "not both" (the functional version).
-/

namespace PEqualNP.Expanders

open PEqualNP.ProofComplexity

/-- A bipartite graph with left vertices `Fin m` and right vertices `Fin N`, given by the
neighbourhood of each left vertex. -/
abbrev BipGraph (m N : ℕ) : Type := Fin m → Finset (Fin N)

/-- The left neighbours of the right vertex `j`. -/
def rightNbrs {m N : ℕ} (G : BipGraph m N) (j : Fin N) : Finset (Fin m) :=
  Finset.univ.filter (fun i => j ∈ G i)

/-- Every left vertex has at most `b` neighbours. -/
def LeftDegLe {m N : ℕ} (G : BipGraph m N) (b : ℕ) : Prop :=
  ∀ i, (G i).card ≤ b

/-- Every right vertex has at most `b` neighbours. -/
def RightDegLe {m N : ℕ} (G : BipGraph m N) (b : ℕ) : Prop :=
  ∀ j, (rightNbrs G j).card ≤ b

/-- The unique neighbours of the left set `T`: right vertices with exactly one neighbour in `T`. -/
def uniqueNbrs {m N : ℕ} (G : BipGraph m N) (T : Finset (Fin m)) : Finset (Fin N) :=
  Finset.univ.filter (fun j => (T.filter (fun i => j ∈ G i)).card = 1)

/-- `G` is an `(s, δ)` boundary expander: every left set of at most `s` vertices has at least
`δ` times its size in unique neighbours. -/
def IsBdryExpander {m N : ℕ} (G : BipGraph m N) (s δ : ℕ) : Prop :=
  ∀ T : Finset (Fin m), T.card ≤ s → δ * T.card ≤ (uniqueNbrs G T).card

/-- The edges of `G`: pairs (pigeon, hole) with the hole a neighbour of the pigeon. -/
abbrev GEdge {m N : ℕ} (G : BipGraph m N) : Type := {e : Fin m × Fin N // e.2 ∈ G e.1}

/-- The pigeonhole formula on `G`, variables the edges: each pigeon sits in a neighbouring hole,
and no hole holds two different pigeons. -/
def graphPHP {m N : ℕ} (G : BipGraph m N) : Set (Clause (GEdge G)) :=
  {C | ∃ i : Fin m, C = Finset.univ.filter (fun l : Literal (GEdge G) => l.1.1.1 = i ∧ l.2 = true)} ∪
  {C | ∃ (e e' : GEdge G), e.1.2 = e'.1.2 ∧ e.1.1 ≠ e'.1.1 ∧ C = {(e, false), (e', false)}}

/-- The functional pigeonhole formula on `G`: `graphPHP G` and, for each pigeon, not two
different holes. -/
def funGraphPHP {m N : ℕ} (G : BipGraph m N) : Set (Clause (GEdge G)) :=
  graphPHP G ∪
  {C | ∃ (e e' : GEdge G), e.1.1 = e'.1.1 ∧ e.1.2 ≠ e'.1.2 ∧ C = {(e, false), (e', false)}}

end PEqualNP.Expanders
