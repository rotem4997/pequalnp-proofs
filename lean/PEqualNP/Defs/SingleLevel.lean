import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Dedup
import PEqualNP.Defs.CircuitLowerBounds
import PEqualNP.Defs.MetaComplexity
import PEqualNP.Defs.MetaComplexityMinimal

/-!
# Single-level circuits for the selector family `f_H`, for the meta-complexity program

The graph. A graph on the vertices `Fin v` is a list of edges (ordered pairs). The order of the
list indexes the selector inputs. `WF` says the list is a simple graph: no loop, no edge listed
twice in either orientation.

Covers. A vertex cover is a set of vertices meeting every edge; the cover number `vc` is the
least size of a vertex cover.

The excess `ex`: the largest value of `|F| - |V(F)|` over sub-lists `F` of the edge list, where
`V(F)` is the set of vertices the edges of `F` touch (truncated subtraction; the empty sub-list
gives `0`).

The input layout of `fH E` on a graph with `v` vertices and edge list `E` (`m = E.length`):
wire `0` is `x_0`; wire `1 + u` is the vertex variable `x_u` (`u < v`); wire `1 + v + i` is the
selector `z_i` of the edge `E[i]` (`i < m`). So `n = 1 + v + m` inputs.

The selector function: `f_H = OR over edges e = uv of (z_e AND (x_0 OR x_u OR x_v))`.

The class: fan-in two AND/OR/NOT circuits (`FanInTwo`) with no NOT gate, in which every wire has
AND depth at most `1`. Only an AND gate reading at least two wires counts as a level. `IsLeastSL`
says a circuit of the class computes `f` and has no more gates than any circuit of the class
computing `f`.

Circuits, their size and the function they compute are those of
`PEqualNP.Defs.CircuitLowerBounds`, `PEqualNP.Defs.MetaComplexity` and
`PEqualNP.Defs.MetaComplexityMinimal`.
-/

namespace PEqualNP.MetaComplexity.SingleLevel

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-! ## The graph side -/

/-- A graph on the vertices `Fin v`, given by its list of edges. The order of the list
fixes the order of the selector inputs. -/
abbrev Edges (v : ℕ) := List (Fin v × Fin v)

/-- Two ordered pairs name the same undirected edge. -/
def SameEdge {v : ℕ} (e f : Fin v × Fin v) : Prop :=
  (e.1 = f.1 ∧ e.2 = f.2) ∨ (e.1 = f.2 ∧ e.2 = f.1)

instance {v : ℕ} (e f : Fin v × Fin v) : Decidable (SameEdge e f) := by
  unfold SameEdge; infer_instance

/-- The edge list is a simple graph: no loop, no edge listed twice in either
orientation. -/
def WF {v : ℕ} (E : Edges v) : Prop :=
  (∀ e ∈ E, e.1 ≠ e.2) ∧ E.Pairwise (fun e f => ¬ SameEdge e f)

instance {v : ℕ} (E : Edges v) : Decidable (WF E) := by unfold WF; infer_instance

/-- `T` is a vertex cover: every edge has an end in `T`. -/
def IsCover {v : ℕ} (E : Edges v) (T : Finset (Fin v)) : Prop :=
  ∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T

instance {v : ℕ} (E : Edges v) (T : Finset (Fin v)) : Decidable (IsCover E T) := by
  unfold IsCover; infer_instance

/-- The vertex cover number: the least size of a vertex cover (the set of all vertices
is one, so the set below is nonempty). -/
noncomputable def vc {v : ℕ} (E : Edges v) : ℕ :=
  sInf {k | ∃ T : Finset (Fin v), IsCover E T ∧ T.card = k}

/-- The vertices touched by a list of edges, as a list without repetition. -/
def verts {v : ℕ} (F : Edges v) : List (Fin v) :=
  (F.flatMap fun e => [e.1, e.2]).dedup

/-- The excess, in a component-free form: the largest value of `|F| - |V(F)|` over
sub-lists `F` of the edge list (truncated subtraction; the empty sub-list gives `0`). -/
def ex {v : ℕ} (E : Edges v) : ℕ :=
  (E.sublists.map fun F => F.length - (verts F).length).foldr max 0

/-! ## The function -/

/-- The input wire of `x_0`. -/
def x0 {v m : ℕ} : Fin (1 + v + m) := ⟨0, by omega⟩

/-- The input wire of the vertex variable `x_u`. -/
def xv {v m : ℕ} (u : Fin v) : Fin (1 + v + m) := ⟨1 + u.val, by omega⟩

/-- The input wire of the selector `z_i` of edge number `i`. -/
def zs {v m : ℕ} (i : Fin m) : Fin (1 + v + m) := ⟨1 + v + i.val, by omega⟩

/-- The selector family: `f_H = OR over edges e = uv of (z_e AND (x_0 OR x_u OR x_v))`,
on `1 + v + m` inputs in the layout of the module docstring. -/
def fH {v : ℕ} (E : Edges v) (y : Fin (1 + v + E.length) → Bool) : Bool :=
  (List.finRange E.length).any fun i =>
    y (zs i) && (y x0 || y (xv (E.get i).1) || y (xv (E.get i).2))

/-! ## The circuit class -/

/-- The AND level a gate adds: `1` for an AND gate reading at least two wires, else `0`.
An AND gate reading no wire (the constant `true`) or one wire (a copy) adds no level; an AND
gate reading one wire twice (`[j, j]`) does. -/
def andLevel (g : Gate) : ℕ :=
  match g.op, g.inputs with
  | GateOp.and, _ :: _ :: _ => 1
  | _, _ => 0

/-- The AND depth of every wire on `n` inputs: the largest number of (two-input) AND
gates on a path ending at the wire. Inputs `0`; a gate: the largest AND depth among the wires
it reads (a wire that does not exist counts `0`), plus its `andLevel`. Same fold as
`Circuit.depths`. -/
def andDepths (C : Circuit) (n : ℕ) : List ℕ :=
  C.gates.foldl
    (fun d g => d ++ [(g.inputs.map fun i => d.getD i 0).foldr max 0 + andLevel g])
    (List.replicate n 0)

/-- The gate is not a NOT gate. -/
def notNot (g : Gate) : Bool :=
  match g.op with
  | GateOp.not => false
  | _ => true

/-- The class: fan-in two AND/OR/NOT (`FanInTwo`), no NOT gate, and every wire (dead
gates included) has AND depth at most `1`: no path passes through two two-input AND gates. -/
def IsSingleLevel (n : ℕ) (C : Circuit) : Prop :=
  FanInTwo C ∧ (∀ g ∈ C.gates, notNot g = true) ∧ ∀ d ∈ andDepths C n, d ≤ 1

/-- `C` is a least circuit of `f` inside the class. -/
def IsLeastSL (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit) : Prop :=
  IsSingleLevel n C ∧ circuitFun n C = f ∧
    ∀ D : Circuit, IsSingleLevel n D → circuitFun n D = f → C.size ≤ D.size

end PEqualNP.MetaComplexity.SingleLevel
