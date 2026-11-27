import PEqualNP.Defs.LineDegree
import PEqualNP.Defs.MetaComplexityLgpMono
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Relation

/-!
# Definitions for the degree-two chain (L-meta-649), helper

Everything the cards D2-03 to D2-18 of the builder sheet
(the builder sheet, section 0) speak of, in Lean.

DESIGN. The circuit is read as an abstract fan-in-two DAG `Dag N` with THE SAME WIRE INDEXING as
the root circuit on `N + N` inputs: wire `p < N` is the point input `x_p`, wire `N + l` is the
line input `y_l`, gate `j` is wire `N + N + j`. A gate is `and a b`, `or a b` or a constant
`cst v`. Value and line-degree are defined by recursion on the wire index with the root's guard
(a read of a wire that is not below the gate reads `false` and has degree `0`), so no
well-formedness proof is carried in the structure; `Dag.WF` says every read is below the gate.

* `ofCircuit` translates a root circuit gate by gate (one DAG gate per root gate, same index):
  `AND []` is `cst true`, `OR []` is `cst false`, a copy is `or a a`, a read of a missing wire
  becomes `cst false` (or the valid half of an OR). Size is equal, every wire keeps its value,
  no degree grows (cards D2-03a to D2-03d).
* `toCircuit` translates back (same values and degrees, card D2-03r), so the checked test lemma
  L-meta-629 applies to a DAG.
* Nothing is ever re-indexed. Gates outside the cone of the output stay and are paid by `size`;
  the classes X, M, T are filters of the cone (a `Finset` of wire indices). Cleaning (D2-04,
  D2-09) replaces a gate in place; the form (D2-15, D2-16) appends gates.

All sets are `Finset`s; decidability is classical where it is not structural.
-/

namespace PEqualNP.MetaComplexity.Deg2

open PEqualNP.CircuitLowerBounds

/-! ## The DAG -/

/-- A gate of the DAG: AND or OR of two wires (by index), or a constant. -/
inductive G where
  | and (a b : ℕ)
  | or (a b : ℕ)
  | cst (v : Bool)
  deriving DecidableEq, Repr

/-- The wires a gate reads. -/
def G.kids : G → List ℕ
  | .and a b => [a, b]
  | .or a b => [a, b]
  | .cst _ => []

/-- A fan-in-two AND/OR DAG on `N` points and `N` lines: gate `j` is wire `N + N + j`. -/
structure Dag (N : ℕ) where
  /-- The gates in order. -/
  gates : List G
  /-- The output wire. -/
  out : ℕ

namespace Dag

variable {N : ℕ}

/-- The number of gates (constants included). -/
def size (D : Dag N) : ℕ := D.gates.length

/-- The gate producing wire `i`, if `i` is a gate wire. -/
def gateAt (D : Dag N) (i : ℕ) : Option G :=
  if N + N ≤ i then D.gates[i - (N + N)]? else none

/-- The value of wire `i` on input `x`. A read of a wire not below the gate reads `false`. -/
def val (D : Dag N) (x : Fin (N + N) → Bool) (i : ℕ) : Bool :=
  if h : i < N + N then x ⟨i, h⟩ else
  match D.gates[i - (N + N)]? with
  | some (.and a b) =>
      (if _ : a < i then D.val x a else false) && (if _ : b < i then D.val x b else false)
  | some (.or a b) =>
      (if _ : a < i then D.val x a else false) || (if _ : b < i then D.val x b else false)
  | some (.cst v) => v
  | none => false
termination_by i

/-- The line-degree of wire `i`: a line input `1`, a point input `0`, AND the sum, OR the
maximum, a constant `0`, a read of a wire not below the gate `0`. -/
def deg (D : Dag N) (i : ℕ) : ℕ :=
  if i < N + N then (if N ≤ i then 1 else 0) else
  match D.gates[i - (N + N)]? with
  | some (.and a b) =>
      (if _ : a < i then D.deg a else 0) + (if _ : b < i then D.deg b else 0)
  | some (.or a b) =>
      max (if _ : a < i then D.deg a else 0) (if _ : b < i then D.deg b else 0)
  | some (.cst _) => 0
  | none => 0
termination_by i

/-- The function computed: the value of the output wire. -/
def fn (D : Dag N) (x : Fin (N + N) → Bool) : Bool := D.val x D.out

/-- `c` is a wire read by gate `i` (and below it). -/
def Kid (D : Dag N) (i c : ℕ) : Prop := ∃ g, D.gateAt i = some g ∧ c ∈ g.kids ∧ c < i

/-- Every read is of a wire below the gate. -/
def WF (D : Dag N) : Prop := ∀ i g, D.gateAt i = some g → ∀ c ∈ g.kids, c < i

/-- Downward reachability (reflexive). -/
def Reach (D : Dag N) : ℕ → ℕ → Prop := Relation.ReflTransGen D.Kid

/-- Gate `i` is an AND gate. -/
def IsAnd (D : Dag N) (i : ℕ) : Prop := ∃ a b, D.gateAt i = some (.and a b)

/-- Gate `i` is an OR gate. -/
def IsOr (D : Dag N) (i : ℕ) : Prop := ∃ a b, D.gateAt i = some (.or a b)

open Classical in
/-- The GATE wires reachable from some wire of `S`. -/
noncomputable def coneOf (D : Dag N) (S : Finset ℕ) : Finset ℕ :=
  (Finset.range (N + N + D.size)).filter (fun i => N + N ≤ i ∧ ∃ r ∈ S, D.Reach r i)

/-- The gates in the cone of the output. -/
noncomputable def cone (D : Dag N) : Finset ℕ := D.coneOf {D.out}

/-- X: gates of the cone of degree 0 (x-only, constants included). -/
noncomputable def X (D : Dag N) : Finset ℕ := D.cone.filter (fun i => D.deg i = 0)
/-- M: gates of the cone of degree 1. -/
noncomputable def M (D : Dag N) : Finset ℕ := D.cone.filter (fun i => D.deg i = 1)
/-- T: gates of the cone of degree 2. -/
noncomputable def T (D : Dag N) : Finset ℕ := D.cone.filter (fun i => D.deg i = 2)

open Classical in
/-- AND gates of M. -/
noncomputable def AndM (D : Dag N) : Finset ℕ := D.M.filter D.IsAnd
open Classical in
/-- OR gates of M. -/
noncomputable def OrM (D : Dag N) : Finset ℕ := D.M.filter D.IsOr
open Classical in
/-- OR gates of T. -/
noncomputable def Tor (D : Dag N) : Finset ℕ := D.T.filter D.IsOr
open Classical in
/-- AND gates of T with a child of degree 0 (the other then has degree 2). -/
noncomputable def Tandf (D : Dag N) : Finset ℕ :=
  D.T.filter (fun i => ∃ a b, D.gateAt i = some (.and a b) ∧ (D.deg a = 0 ∨ D.deg b = 0))
open Classical in
/-- AND gates of T with two children of degree 1. -/
noncomputable def Tmix (D : Dag N) : Finset ℕ :=
  D.T.filter (fun i => ∃ a b, D.gateAt i = some (.and a b) ∧ D.deg a = 1 ∧ D.deg b = 1)

end Dag

/-! ## Translations to and from root circuits -/

/-- One root gate as a DAG gate at wire `i` (reads at `i` or above are missing). -/
def trGate (i : ℕ) (g : Gate) : G :=
  match g.op, g.inputs with
  | .and, [] => .cst true
  | .or, [] => .cst false
  | .and, [a] => if a < i then .or a a else .cst false
  | .or, [a] => if a < i then .or a a else .cst false
  | .and, [a, b] => if a < i ∧ b < i then .and a b else .cst false
  | .or, [a, b] =>
      if a < i ∧ b < i then .or a b else if a < i then .or a a
      else if b < i then .or b b else .cst false
  | _, _ => .cst false

/-- The DAG of a root circuit on `N + N` inputs: gate `j` translated at wire `N + N + j`. -/
def ofCircuit (N : ℕ) (C : Circuit) : Dag N :=
  { gates := C.gates.mapIdx (fun j g => trGate (N + N + j) g), out := C.output }

/-- A DAG gate as a root gate. -/
def G.toGate : G → Gate
  | .and a b => ⟨.and, [a, b]⟩
  | .or a b => ⟨.or, [a, b]⟩
  | .cst v => if v then ⟨.and, []⟩ else ⟨.or, []⟩

/-- The root circuit of a DAG. -/
def Dag.toCircuit {N : ℕ} (D : Dag N) : Circuit := ⟨D.gates.map G.toGate, D.out⟩

/-! ## The graph, the inputs, the function -/

/-- No two distinct points on two distinct common lines (section 0.2: A1 and A2 at once). -/
def NoRect {N : ℕ} (I : Fin N → Fin N → Prop) : Prop :=
  ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')

/-- The marked inputs: the lines, positions `N` to `N + N - 1`. -/
def lineMarks (N : ℕ) : Finset ℕ := Finset.Ico N (N + N)

/-- The edge function (section 0.4). -/
def edgeFun (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] :
    (Fin (N + N) → Bool) → Bool :=
  fun z => decide (∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)

/-- The incident pairs, in the form of the statement of L-meta-649. -/
def edges (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)

/-- `f` is true exactly at the inputs carrying an incident pair (no decidability needed). -/
def Computes {N : ℕ} (I : Fin N → Fin N → Prop) (f : (Fin (N + N) → Bool) → Bool) : Prop :=
  ∀ z, f z = true ↔ ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true

/-- The input `[P; S]`: exactly the points of `P` and the lines of `S` on. -/
def inp {N : ℕ} (P S : Finset (Fin N)) : Fin (N + N) → Bool :=
  Fin.addCases (motive := fun _ => Bool) (fun p => decide (p ∈ P)) (fun l => decide (l ∈ S))

/-- `e_p`: point `p` alone. -/
def pt {N : ℕ} (p : Fin N) : Fin (N + N) → Bool := inp {p} ∅

/-- `e_p + e_w`. -/
def ep {N : ℕ} (p w : Fin N) : Fin (N + N) → Bool := inp {p} {w}

open Classical in
/-- The test input `z_S`: the lines of `S` and every point on no line of `S`. -/
noncomputable def testInput {N : ℕ} (I : Fin N → Fin N → Prop) (S : Finset (Fin N)) :
    Fin (N + N) → Bool :=
  inp (Finset.univ.filter (fun p => ∀ l ∈ S, ¬ I p l)) S

open Classical in
/-- The points on line `l`. -/
noncomputable def ptsOn {N : ℕ} (I : Fin N → Fin N → Prop) (l : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun p => I p l)

open Classical in
/-- The lines through point `p`. -/
noncomputable def pencil {N : ℕ} (I : Fin N → Fin N → Prop) (p : Fin N) : Finset (Fin N) :=
  Finset.univ.filter (fun l => I p l)

/-- `r` is p-honest: false at `e_p`, and true at `e_p + e_u` only for `u` through `p`. -/
def IsHonest {N : ℕ} (I : Fin N → Fin N → Prop) (r : (Fin (N + N) → Bool) → Bool)
    (p : Fin N) : Prop :=
  r (pt p) = false ∧ ∀ u, r (ep p u) = true → I p u

namespace Dag

variable {N : ℕ}

/-! ## Alive and dead sets -/

/-- `L(f)`: the points `p` with `f(e_p) = 1`. -/
def alive (D : Dag N) (f : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun p => D.val (pt p) f = true)

open Classical in
/-- `Dead_d(f)`: the sets of at most `d` lines at whose test input `f` is false. -/
noncomputable def deadSets (I : Fin N → Fin N → Prop) (D : Dag N) (d : ℕ) (f : ℕ) :
    Finset (Finset (Fin N)) :=
  (Finset.univ : Finset (Finset (Fin N))).filter
    (fun S => S.card ≤ d ∧ D.val (testInput I S) f = false)

/-! ## V*, pinned ORs, markers, labelled wires -/

/-- `VReach D v u`: the line input `y_u` is reached from `v` through OR gates of degree 1 only
(no labelled wire). `V*(y_u) = {u}`; an AND gate or an x-only wire reaches nothing. -/
inductive VReach (D : Dag N) : ℕ → Fin N → Prop
  | leaf (u : Fin N) : VReach D (N + u.val) u
  | step {v c : ℕ} {u : Fin N} : D.IsOr v → D.deg v = 1 → D.Kid v c → VReach D c u →
      VReach D v u

open Classical in
/-- `V*(v)`. -/
noncomputable def Vstar (D : Dag N) (v : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun u => D.VReach v u)

/-- An OR gate of degree 1 is pinned to `p`: at least two lines in `V*`, all through `p`. -/
def PinnedTo (I : Fin N → Fin N → Prop) (D : Dag N) (v : ℕ) (p : Fin N) : Prop :=
  D.IsOr v ∧ D.deg v = 1 ∧ 2 ≤ (D.Vstar v).card ∧ D.Vstar v ⊆ pencil I p

open Classical in
/-- Pinned := pairs `(p, u)` with an OR of M pinned to `p` and `u` in its `V*`. -/
noncomputable def pinned (I : Fin N → Fin N → Prop) (D : Dag N) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => ∃ v ∈ D.OrM, PinnedTo I D v e.1 ∧ e.2 ∈ D.Vstar v)

/-- A marker of line `w`: a wire of degree 1 with `V* = {w}` (the leaf `y_w` included). -/
def IsMarker (D : Dag N) (r : ℕ) (w : Fin N) : Prop := D.deg r = 1 ∧ D.Vstar r = {w}

/-- `e = AND(f, v)` (either order) with label `f` of degree 0 and `v` of degree 1: the labelled
wire `e -> v`. -/
def LabAnd (D : Dag N) (e f v : ℕ) : Prop :=
  (D.gateAt e = some (.and f v) ∨ D.gateAt e = some (.and v f)) ∧ D.deg f = 0 ∧ D.deg v = 1

open Classical in
/-- Served := pairs `(p, w)` with an AND `e = AND(f, v)` of M, `V*(v) = {w}`, `p` alive in `f`
and on `w`, and at most two alive points of `f` on `w`. -/
noncomputable def served (I : Fin N → Fin N → Prop) (D : Dag N) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => ∃ g ∈ D.AndM, ∃ f v, D.LabAnd g f v ∧ D.Vstar v = {e.2} ∧
    e.1 ∈ D.alive f ∧ I e.1 e.2 ∧ (D.alive f ∩ ptsOn I e.2).card ≤ 2)

open Classical in
/-- `F_d` over the gate set `Gs`: incident pairs `(p, l)` with an x-only gate `f` of `Gs` having
a dead set, `p` alive in `f`, and at least `d + 1` alive points of `f` on `l`. -/
noncomputable def fSet (I : Fin N → Fin N → Prop) (D : Dag N) (Gs : Finset ℕ) (d : ℕ) :
    Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => I e.1 e.2 ∧ ∃ f ∈ Gs, D.deg f = 0 ∧ D.deadSets I d f ≠ ∅ ∧
    e.1 ∈ D.alive f ∧ d + 1 ≤ (D.alive f ∩ ptsOn I e.2).card)

/-- Every label of a labelled wire at a gate of `Gs` has a dead set of at most two lines. -/
def Cleaned (I : Fin N → Fin N → Prop) (D : Dag N) (Gs : Finset ℕ) : Prop :=
  ∀ e ∈ Gs, ∀ f v, D.LabAnd e f v → D.deadSets I 2 f ≠ ∅

/-! ## Paths -/

/-- `π` is a downward path of wires from `a` to `b`. -/
def IsPath (D : Dag N) (π : List ℕ) (a b : ℕ) : Prop :=
  π.head? = some a ∧ π.getLast? = some b ∧
    ∀ k, k + 1 < π.length → D.Kid (π.getD k 0) (π.getD (k + 1) 0)

/-- Every label of a labelled wire on `π` is true at `x`. -/
def LabelsAlive (D : Dag N) (π : List ℕ) (x : Fin (N + N) → Bool) : Prop :=
  ∀ k f, k + 1 < π.length → D.LabAnd (π.getD k 0) f (π.getD (k + 1) 0) → D.val x f = true

/-! ## The top part: items and contexts (D2-15) -/

/-- The top-down pass from the output through T: an OR of T passes to each child of degree at
least 1; an AND of T with a label `f` (degree 0) passes to its degree-2 child when `ok f`.
`Top D (fun _ => True)` is reachability by the pass; `Top D (fun f => D.val x f = true)` is
"the context is true at `x`". -/
inductive Top (D : Dag N) (ok : ℕ → Prop) : ℕ → Prop
  | root : Top D ok D.out
  | orStep {h c : ℕ} : Top D ok h → h ∈ D.Tor → D.Kid h c → 1 ≤ D.deg c → Top D ok c
  | andStep {h f c : ℕ} : Top D ok h → h ∈ D.Tandf →
      (D.gateAt h = some (.and f c) ∨ D.gateAt h = some (.and c f)) →
      D.deg f = 0 → D.deg c = 2 → f < h → c < h → ok f → Top D ok c

/-- An item: a wire reached by the pass that is of degree at most 1 or a gate of T_mix. -/
def IsItem (D : Dag N) (b : ℕ) : Prop :=
  D.Top (fun _ => True) b ∧ (D.deg b ≤ 1 ∨ b ∈ D.Tmix)

open Classical in
/-- The context `psi_b` (an x-only monotone function). -/
noncomputable def ctx (D : Dag N) (b : ℕ) : (Fin (N + N) → Bool) → Bool :=
  fun x => decide (D.Top (fun f => D.val x f = true) b)

/-- The factors of an item: itself if of degree at most 1, its two children if in T_mix. -/
def IsFactor (D : Dag N) (b r : ℕ) : Prop :=
  (D.deg b ≤ 1 ∧ r = b) ∨ (b ∈ D.Tmix ∧ D.Kid b r)

open Classical in
/-- Marker edges (section 0.6, intrinsic): incident `(p, w)` with an item `b` whose context is
true at `e_p`, every factor true at `e_p + e_w`, and some factor a marker of `w`. -/
noncomputable def markerEdges (I : Fin N → Fin N → Prop) (D : Dag N) :
    Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => I e.1 e.2 ∧ ∃ b, D.IsItem b ∧ D.ctx b (pt e.1) = true ∧
    (∀ r, D.IsFactor b r → D.val (ep e.1 e.2) r = true) ∧ ∃ r, D.IsFactor b r ∧ D.IsMarker r e.2)

/-! ## Sound partial forms (D2-09 to D2-14, D2-16) -/

/-- The gates in the union of the cones of the roots `R w`, `w ∈ W`: `M'' ∪ X''`, of card `s''`. -/
noncomputable def rootCone (D : Dag N) (W : Finset (Fin N)) (R : Fin N → ℕ) : Finset ℕ :=
  D.coneOf (W.image R)

/-- A sound partial form: a well-formed DAG `D`, lines `W`, roots `R w` of degree at most 1,
with `OR_{w ∈ W} (y_w AND R w)` at most the edge function. -/
def SoundPartialForm (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N))
    (R : Fin N → ℕ) : Prop :=
  D.WF ∧ (∀ w ∈ W, D.deg (R w) ≤ 1) ∧
    ∀ z, (∃ w ∈ W, z (Fin.natAdd N w) = true ∧ D.val z (R w) = true) →
      ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true

open Classical in
/-- Counted edges `E'`. -/
noncomputable def countedEdges (D : Dag N) (W : Finset (Fin N)) (R : Fin N → ℕ) :
    Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => e.2 ∈ W ∧ D.val (ep e.1 e.2) (R e.2) = true)

open Classical in
/-- `E0`: `w ∈ W` and `D_w^0(e_p) = 1` (the root at the input with no line). -/
noncomputable def e0Set (D : Dag N) (W : Finset (Fin N)) (R : Fin N → ℕ) :
    Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => e.2 ∈ W ∧ D.val (pt e.1) (R e.2) = true)

/-- `f <= sum_w` as functions. -/
def LeSum (I : Fin N → Fin N → Prop) (D : Dag N) (f : ℕ) (w : Fin N) : Prop :=
  ∀ z, D.val z f = true → ∃ p, I p w ∧ z (Fin.castAdd N p) = true

open Classical in
/-- `E1`: counted edges `(p, w)` with an x-only gate `f` of the form, `f <= sum_w`, `p` alive,
at least two alive points. -/
noncomputable def e1Set (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N))
    (R : Fin N → ℕ) : Finset (Fin N × Fin N) :=
  (D.countedEdges W R).filter (fun e => ∃ f ∈ D.rootCone W R, D.deg f = 0 ∧
    D.LeSum I f e.2 ∧ e.1 ∈ D.alive f ∧ 2 ≤ (D.alive f).card)

/-- A path for the counted edge `(p, w)`: from `R w` to `y_w`, every wire true at `e_p + e_w`
and false at `e_p` (the path D2-11 builds when `(p, w)` is not in `E0`). -/
def EdgePath (D : Dag N) (R : Fin N → ℕ) (p w : Fin N) (π : List ℕ) : Prop :=
  D.IsPath π (R w) (N + w.val) ∧ ∀ v ∈ π, D.val (ep p w) v = true ∧ D.val (pt p) v = false

/-- Position `k` of `π` is a p-gate: `π[k] = AND(f, π[k+1])` with `L(f) = {p}`. -/
def PGateAt (D : Dag N) (p : Fin N) (π : List ℕ) (k : ℕ) : Prop :=
  k + 1 < π.length ∧ ∃ f, D.LabAnd (π.getD k 0) f (π.getD (k + 1) 0) ∧ D.alive f = {p}

/-- The p-gate with child `g'` is BETA: a root of a line off `p` reaches `g'` by a path whose
labels are all true at `e_p`. -/
def IsBeta (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N)) (R : Fin N → ℕ)
    (p : Fin N) (g' : ℕ) : Prop :=
  ∃ u ∈ W, ¬ I p u ∧ ∃ π, D.IsPath π (R u) g' ∧ D.LabelsAlive π (pt p)

open Classical in
/-- Counted edges with a path whose FIRST p-gate is alpha (not beta). -/
noncomputable def alphaEdges (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N))
    (R : Fin N → ℕ) : Finset (Fin N × Fin N) :=
  (D.countedEdges W R).filter (fun e => ∃ π, D.EdgePath R e.1 e.2 π ∧ ∃ k,
    D.PGateAt e.1 π k ∧ (∀ k' < k, ¬ D.PGateAt e.1 π k') ∧
    ¬ D.IsBeta I W R e.1 (π.getD (k + 1) 0))

open Classical in
/-- Counted edges with a path whose LAST p-gate is beta. -/
noncomputable def betaEdges (I : Fin N → Fin N → Prop) (D : Dag N) (W : Finset (Fin N))
    (R : Fin N → ℕ) : Finset (Fin N × Fin N) :=
  (D.countedEdges W R).filter (fun e => ∃ π, D.EdgePath R e.1 e.2 π ∧ ∃ k,
    D.PGateAt e.1 π k ∧ (∀ k', k < k' → ¬ D.PGateAt e.1 π k') ∧
    D.IsBeta I W R e.1 (π.getD (k + 1) 0))

end Dag

end PEqualNP.MetaComplexity.Deg2
