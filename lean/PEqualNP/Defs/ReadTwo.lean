import PEqualNP.Defs.TopForm
import PEqualNP.Defs.ReadK

/-!
# Root definitions for the read-2 chain (A0 to A13)

Section A of the read-2 assembly desk file of the full-basis route, built over the root names
`Circuit`, `Circuit.wires`, `GateOp`, `circuitFun`, `NestedCover.gateAt`, `TopForm.IsAO2`,
`ReadK.readsAtMost`, `ReadK.IsReadK`. Inputs are wires `0 .. n - 1`, gate `j` is wire `n + j`.

Every definition here is a definition, not a result: none was printed, and each is to be read by
a second reader for saying what its sentence says (MINDSET 0i (e)).

Decidability. `gateOpDecEq` is a local instance (so `nOr`, `nAnd`, `isAnd`, `isOr` are
computable); `open Classical` supplies the rest. The definitions marked `noncomputable` use a
classical decision (a `Finset.filter` or `decide` on a predicate with no instance).

TRANSPOSE. The triple `(lw, pw, fun l p => I p l)`: "X at TRANSP" means X with these arguments.

CAVEATS (comments only).
* `ptv` and `ptl` follow the FIRST TWO reads of an AND gate (`in0`, `in1`): with three reads the
  third is ignored, with one read the second is taken as wire `0`. So a skeleton is a proof tree
  only for gates of exactly two reads; every statement using `ptv`, `tree2` or `Has2` carries
  `IsAO2`.
* The "leaf gate" in `ptl` is a WIRE number: the operand wire the leaf hangs from (an input of
  its nearest AND, or the output), not a gate index.
* `hasTy` is not total: a tight leaf whose shadow has two or more points (an `xBig` leaf, or its
  transpose) has none of the four types.
* T1's graft is `Sk.subst` (a chosen leaf replaced by a skeleton); `Sk` has no cut constructor.
* `Exs` and `Epp` contain every incidence with NO read-2 tree at all (the condition "no tree with
  a big tight x-leaf" holds vacuously): statements about them carry `Has2`.
* The five B2 classes (`clX`, `clXs`, `clP`, `clL`, `clO`) do not cover every case on their face
  (bottom lines empty, one bottom line other than `l`, or no source point): a statement that they
  partition the cases must prove those away.
* `tB1.dual` and `tB2.dual` (and `tDIRECT.dual`) equal `tB1`, `tB2`, `tDIRECT` up to the child
  swaps `fitsShape` allows, so `ALLTEMPLATES` has more templates than shapes: fine for "fits some
  template", wrong for a count by the list length.
* `dom2 n C u m` is vacuous when `u` is not an input wire: statements state `u < n` beside it.
* `fpl` is meant with `N = M` (the plane): statements using it carry `N = M` as a hypothesis.

RULINGS ALREADY APPLIED (the author's): `fitsShape` (shape up to child swaps, typed leaves);
`Sk.subst` by leaf position in `ptl` order; `yTight`/`yBig` as `xTight`/`xBig` at TRANSP; the
wire-0 default of `in0`/`in1` under `IsAO2`; `[DecidableRel I]` on `fpl`; `hasDirect` at the root
only; `ALLTEMPLATES` with DIRECT and closed under dual.
-/

namespace PEqualNP.ReadTwo

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Classical

attribute [local instance] gateOpDecEq

/-! ## A0. Wires and paths -/

/-- The value of wire `w` of `C` on the input `x` (`false` past the last wire). -/
def wval {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

/-- The first input wire of gate `j` (`0` if it has none). -/
def in0 (C : Circuit) (j : ℕ) : ℕ := ((gateAt C j).inputs).getD 0 0

/-- The second input wire of gate `j` (`0` if it has none). -/
def in1 (C : Circuit) (j : ℕ) : ℕ := ((gateAt C j).inputs).getD 1 0

/-- Gate `j` exists and is an AND gate. -/
def isAnd (C : Circuit) (j : ℕ) : Prop := j < C.gates.length ∧ (gateAt C j).op = GateOp.and

/-- Gate `j` exists and is an OR gate. -/
def isOr (C : Circuit) (j : ℕ) : Prop := j < C.gates.length ∧ (gateAt C j).op = GateOp.or

/-- Gate `j` is an AND gate reading the wires `a` and `b`, in either order. -/
def andOn (C : Circuit) (j a b : ℕ) : Prop :=
  isAnd C j ∧ ((in0 C j = a ∧ in1 C j = b) ∨ (in0 C j = b ∧ in1 C j = a))

/-- An OR-only upward path from wire `a` to wire `b` (`b = a` allowed): each step goes from a
wire to an OR gate reading it, at a higher wire number. -/
def orp (C : Circuit) (n : ℕ) : ℕ → ℕ → Prop :=
  Relation.ReflTransGen
    (fun a b => a < b ∧ ∃ j, b = n + j ∧ isOr C j ∧ a ∈ (gateAt C j).inputs)

/-- The number of OR gates. -/
def nOr (C : Circuit) : ℕ := (C.gates.filter (fun g => decide (g.op = GateOp.or))).length

/-- The number of AND gates. -/
def nAnd (C : Circuit) : ℕ := (C.gates.filter (fun g => decide (g.op = GateOp.and))).length

/-- The input on `n` wires with exactly the wires of `W` true. -/
def indW (n : ℕ) (W : Finset ℕ) : Fin n → Bool := fun k => decide (k.val ∈ W)

/-! ## A1. Layout -/

/-- Points `pw` and lines `lw` are distinct input wires. -/
def Layout {N M : ℕ} (n : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ) : Prop :=
  Function.Injective pw ∧ Function.Injective lw ∧ (∀ p l, pw p ≠ lw l) ∧ (∀ p, pw p < n) ∧
    (∀ l, lw l < n)

/-- No two points on two common lines (its own transpose). -/
def Lin {N M : ℕ} (I : Fin N → Fin M → Prop) : Prop :=
  ∀ p p' l l', p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p' l ∧ I p l' ∧ I p' l')

/-- The incidences, as a finite set of pairs. -/
noncomputable def incid {N M : ℕ} (I : Fin N → Fin M → Prop) : Finset (Fin N × Fin M) :=
  Finset.univ.filter (fun e => I e.1 e.2)

/-! ## A2. Soundness on two points and two lines -/

/-- The circuit rejects every input of at most two points and at most two lines with no
incidence among them. -/
def Snd22 {N M : ℕ} (n : ℕ) (C : Circuit) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) : Prop :=
  ∀ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 2 → Y.card ≤ 2 →
    (∀ p ∈ P, ∀ l ∈ Y, ¬ I p l) →
    circuitFun n C (indW n (P.image pw ∪ Y.image lw)) = false

/-! ## A3. OR-shadow -/

/-- The inputs `a` (read through `f`) with an OR-only path to the wire `u`. -/
def sh {K : ℕ} (C : Circuit) (n : ℕ) (f : Fin K → ℕ) (u : ℕ) : Set (Fin K) :=
  {a | orp C n (f a) u}

/-! ## A4. Skeleton proof trees -/

/-- A skeleton: a leaf carrying its variable, or an AND gate number with two subtrees. -/
inductive Sk
  | lf (v : ℕ)
  | nd (j : ℕ) (s t : Sk)

/-- `ptv C n top s`: the skeleton `s` is valid hanging from the wire `top`. A leaf: its variable
is an input with an OR path to `top`. A node `j`: an AND gate with an OR path to `top`, its first
input carrying the left subtree and its second the right. -/
def ptv (C : Circuit) (n : ℕ) : ℕ → Sk → Prop
  | top, .lf v => v < n ∧ orp C n v top
  | top, .nd j s t => isAnd C j ∧ orp C n (n + j) top ∧ ptv C n (in0 C j) s ∧ ptv C n (in1 C j) t

/-- The leaves of a skeleton hanging from `top`, as (leaf gate, leaf variable): the leaf gate is
the wire the leaf hangs from. -/
def ptl (C : Circuit) : ℕ → Sk → List (ℕ × ℕ)
  | top, .lf v => [(top, v)]
  | _, .nd j s t => ptl C (in0 C j) s ++ ptl C (in1 C j) t

/-! ## A5. Read-2 trees of an incidence -/

/-- A valid skeleton of the output with at least one AND, every leaf the point `p` or the line
`l`, each read once or twice. -/
def tree2 {N M : ℕ} (n : ℕ) (C : Circuit) (pw : Fin N → ℕ) (lw : Fin M → ℕ) (p : Fin N)
    (l : Fin M) (s : Sk) : Prop :=
  ptv C n C.output s ∧ (∃ j s1 s2, s = Sk.nd j s1 s2) ∧
  (∀ gv ∈ ptl C C.output s, gv.2 = pw p ∨ gv.2 = lw l) ∧
  ((ptl C C.output s).filter (·.2 = pw p)).length ∈ ({1, 2} : Finset ℕ) ∧
  ((ptl C C.output s).filter (·.2 = lw l)).length ∈ ({1, 2} : Finset ℕ)

/-- Every incidence has a read-2 tree. -/
def Has2 {N M : ℕ} (n : ℕ) (C : Circuit) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) : Prop :=
  ∀ p l, I p l → ∃ s, tree2 n C pw lw p l s

/-! ## A6. Leaf types and tight leaves -/

/-- Leaf types: p-private x-leaf, non-tight x-leaf, l-private y-leaf, non-tight y-leaf. -/
inductive Ty
  | P
  | x
  | W
  | y
  deriving DecidableEq

/-- An x-leaf (variable `p`) whose shadow points all lie on `l`. -/
def xTight {N M : ℕ} (C : Circuit) (n : ℕ) (pw : Fin N → ℕ) (I : Fin N → Fin M → Prop)
    (p : Fin N) (l : Fin M) (gv : ℕ × ℕ) : Prop :=
  gv.2 = pw p ∧ sh C n pw gv.1 ⊆ {p' | I p' l}

/-- A tight x-leaf with at least two shadow points. -/
def xBig {N M : ℕ} (C : Circuit) (n : ℕ) (pw : Fin N → ℕ) (I : Fin N → Fin M → Prop)
    (p : Fin N) (l : Fin M) (gv : ℕ × ℕ) : Prop :=
  xTight C n pw I p l gv ∧ 2 ≤ (sh C n pw gv.1).ncard

/-- `yTight` is `xTight` at TRANSP, at the incidence `(l, p)`. -/
def yTight {N M : ℕ} (C : Circuit) (n : ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (p : Fin N) (l : Fin M) (gv : ℕ × ℕ) : Prop :=
  xTight C n lw (fun l p => I p l) l p gv

/-- `yBig` is `xBig` at TRANSP, at the incidence `(l, p)`. -/
def yBig {N M : ℕ} (C : Circuit) (n : ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (p : Fin N) (l : Fin M) (gv : ℕ × ℕ) : Prop :=
  xBig C n lw (fun l p => I p l) l p gv

/-- The type of a leaf `gv` of a tree of `(p, l)`. -/
def hasTy {N M : ℕ} (C : Circuit) (n : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (p : Fin N) (l : Fin M) (gv : ℕ × ℕ) : Ty → Prop
  | .P => gv.2 = pw p ∧ sh C n pw gv.1 = {p}
  | .x => gv.2 = pw p ∧ ∃ p' ∈ sh C n pw gv.1, ¬ I p' l
  | .W => gv.2 = lw l ∧ sh C n lw gv.1 = {l}
  | .y => gv.2 = lw l ∧ ∃ l' ∈ sh C n lw gv.1, ¬ I p l'

/-! ## Substitution on skeletons (for the graft of T1) -/

/-- The number of leaves of a skeleton. -/
def Sk.nleaves : Sk → ℕ
  | .lf _ => 1
  | .nd _ s t => s.nleaves + t.nleaves

/-- `s.subst k r`: the skeleton `s` with its leaf number `k` (from `0`, in the order of `ptl`,
left subtree first) replaced by `r`; `s` itself when `k` is not below `s.nleaves`. -/
def Sk.subst : Sk → ℕ → Sk → Sk
  | .lf v, k, r => if k = 0 then r else .lf v
  | .nd j s t, k, r =>
      if k < s.nleaves then .nd j (s.subst k r) t else .nd j s (t.subst (k - s.nleaves) r)

/-! ## A7. The doubly private incidences -/

/-- The incidences with no read-2 tree having a big tight x-leaf. -/
noncomputable def Exs {N M : ℕ} (n : ℕ) (C : Circuit) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) : Finset (Fin N × Fin M) :=
  (incid I).filter (fun e =>
    ¬ ∃ s, tree2 n C pw lw e.1 e.2 s ∧ ∃ gv ∈ ptl C C.output s, xBig C n pw I e.1 e.2 gv)

/-- `Exs` at TRANSP, pulled back by `Prod.swap`. -/
noncomputable def Eys {N M : ℕ} (n : ℕ) (C : Circuit) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) : Finset (Fin N × Fin M) :=
  (Exs n C lw pw (fun l p => I p l)).image Prod.swap

/-- The doubly private incidences. -/
noncomputable def Epp {N M : ℕ} (n : ℕ) (C : Circuit) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) : Finset (Fin N × Fin M) :=
  Exs n C pw lw I ∩ Eys n C pw lw I

/-! ## A8. Typed shape templates -/

/-- A template: a leaf with a set of allowed types, or a node with two subtemplates. -/
inductive Tm
  | lt (A : Finset Ty)
  | nd (s t : Tm)

/-- The skeleton hanging from `top` matches the template at `(p, l)`: the same shape up to
swapping the two children of any node, every leaf of an allowed type. -/
def fitsShape {N M : ℕ} (C : Circuit) (n : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (p : Fin N) (l : Fin M) : ℕ → Tm → Sk → Prop
  | top, .lt A, .lf v => ∃ τ ∈ A, hasTy C n pw lw I p l (top, v) τ
  | _, .nd a b, .nd j s t =>
      (fitsShape C n pw lw I p l (in0 C j) a s ∧ fitsShape C n pw lw I p l (in1 C j) b t) ∨
      (fitsShape C n pw lw I p l (in0 C j) b s ∧ fitsShape C n pw lw I p l (in1 C j) a t)
  | _, _, _ => False

/-- Leaf sets. -/
abbrev X : Tm := Tm.lt {.P, .x}
abbrev Y : Tm := Tm.lt {.W, .y}
abbrev P : Tm := Tm.lt {.P}
abbrev W : Tm := Tm.lt {.W}
abbrev xx : Tm := Tm.lt {.x}
abbrev yy : Tm := Tm.lt {.y}

/-- The caterpillar `(a, b, {c, d})`, `a` at the top. -/
def cat (a b c d : Tm) : Tm := .nd a (.nd b (.nd c d))

def tDIRECT : Tm := Tm.nd P W
def tS1 : Tm := Tm.nd (.nd P X) W
def tS2 : Tm := Tm.nd P (.nd xx W)
def tB1 : Tm := Tm.nd (.nd X X) (.nd Y Y)
def tB2 : Tm := Tm.nd (.nd P yy) (.nd xx W)

/-- The 16 counted caterpillar patterns (with their duals). -/
def tC1 : Tm := cat P xx W Y
def tC2 : Tm := cat X P W Y
def tC3 : Tm := cat P W xx Y

/-- The six residual patterns. -/
def tWPWx : Tm := cat W P W xx
def tWxyP : Tm := cat W xx yy P
def tyPWx : Tm := cat yy P W xx
def tPWPy : Tm := cat P W P yy
def tPyxW : Tm := cat P yy xx W
def txWPy : Tm := cat xx W P yy

/-- The dual leaf type: `P <-> W`, `x <-> y`. -/
def Ty.dual : Ty → Ty
  | .P => .W
  | .x => .y
  | .W => .P
  | .y => .x

/-- The dual template: every leaf set through `Ty.dual`. -/
def Tm.dual : Tm → Tm
  | .lt A => .lt (A.image Ty.dual)
  | .nd s t => .nd s.dual t.dual

/-- DIRECT (the author's ruling): the AND at the ROOT of the skeleton of the output is the lowest
common AND of the two leaves, and its two children are exactly the OR paths of the two private
leaves (one `P` leaf, one `W` leaf, in either order). Not "some subtree matches `tDIRECT`": the
match is at `C.output` and at the whole skeleton `s`. -/
def hasDirect {N M : ℕ} (C : Circuit) (n : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (p : Fin N) (l : Fin M) (s : Sk) : Prop :=
  fitsShape C n pw lw I p l C.output tDIRECT s

/-- The shape list of one step's coverage (T26): DIRECT, S1, S2, B1, B2, the caterpillar groups
C1 to C3 (with their leaf-type sets, the 16 counted caterpillar patterns: 2 + 4 + 2 with duals),
the six residual patterns, and the duals of tS1, tS2, tB1, tC1, tC2, tC3 (the author's exact list,
20 templates). It is CLOSED UNDER DUAL up to the swaps `fitsShape` allows: tDIRECT and tB2 are
self-dual, the six residual are three dual pairs (`tWPWx`/`tPWPy`, `tWxyP`/`tPyxW`,
`tyPWx`/`txWPy`), and the dual of a listed dual is the original up to `Finset` equality of its
leaf sets. Trees outside `Epp` are handled by the RT steps, not by a template. -/
def ALLTEMPLATES : List Tm :=
  [tDIRECT, tS1, tS2, tB1, tB2, tC1, tC2, tC3, tWPWx, tWxyP, tyPWx, tPWPy, tPyxW, txWPy,
    tS1.dual, tS2.dual, tB1.dual, tC1.dual, tC2.dual, tC3.dual]

/-! ## A9. Squared points, junk, readers, sources, bottoms -/

/-- Squared points of `u`: an AND OR-below `u` with `a` in both inputs' shadows. -/
def dsq {K : ℕ} (C : Circuit) (n : ℕ) (f : Fin K → ℕ) (u : ℕ) : Set (Fin K) :=
  {a | ∃ j, isAnd C j ∧ orp C n (n + j) u ∧ orp C n (f a) (in0 C j) ∧ orp C n (f a) (in1 C j)}

/-- Junk-pair lines of `u` (semantic): `u` is true on `{p1, w1}` with `p1` off `w1`. -/
def jpr {N M : ℕ} (C : Circuit) (n : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (u : ℕ) : Set (Fin M) :=
  {w1 | ∃ p1, ¬ I p1 w1 ∧ wval C (indW n {pw p1, lw w1}) u = true}

/-- Junk lines of `v` relative to the point `p`: shadow lines of `v` missing `p`. -/
def jl {N M : ℕ} (C : Circuit) (n : ℕ) (lw : Fin M → ℕ) (I : Fin N → Fin M → Prop)
    (p : Fin N) (v : ℕ) : Set (Fin M) :=
  {m | m ∈ sh C n lw v ∧ ¬ I p m}

/-- Junk points of `u` relative to the line `l`: shadow points of `u` off `l`. -/
def jp {N M : ℕ} (C : Circuit) (n : ℕ) (pw : Fin N → ℕ) (I : Fin N → Fin M → Prop)
    (l : Fin M) (u : ℕ) : Set (Fin N) :=
  {z | z ∈ sh C n pw u ∧ ¬ I z l}

/-- A reader of `p`: an AND `j` on `a` and `m` whose slot `a` fixes `p`. -/
def reader {N : ℕ} (C : Circuit) (n : ℕ) (pw : Fin N → ℕ) (p : Fin N) (j a m : ℕ) : Prop :=
  andOn C j a m ∧ sh C n pw a = {p}

/-- A source of `p`: a reader whose other slot `v` has a junk line. -/
def source {N M : ℕ} (C : Circuit) (n : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (p : Fin N) (j a v : ℕ) : Prop :=
  reader C n pw p j a v ∧ (jl C n lw I p v).Nonempty

/-- A bottom of `l`: an AND `j` on `u` and `b`, slot `b` fixing `l`, slot `u` with a junk point. -/
def bottom {N M : ℕ} (C : Circuit) (n : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (l : Fin M) (j u b : ℕ) : Prop :=
  andOn C j u b ∧ sh C n lw b = {l} ∧ (jp C n pw I l u).Nonempty

/-! ## A10. The junk star -/

/-- At `g = AND(c, cb)` with an OR path to the output: for every source of `p` OR-below `c` and
every bottom of a line `l'` missing `p` OR-below `cb`, every junk line of the source passes
through every junk point of the bottom. -/
def junkStar {N M : ℕ} (C : Circuit) (n : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (g c cb : ℕ) : Prop :=
  andOn C g c cb ∧ orp C n (n + g) C.output ∧
  ∀ p l' h1 a v h2 u b, source C n pw lw I p h1 a v → orp C n (n + h1) c →
    bottom C n pw lw I l' h2 u b → orp C n (n + h2) cb → ¬ I p l' →
    ∀ m ∈ jl C n lw I p v, ∀ z ∈ jp C n pw I l' u, I z m

/-! ## A11. The B2 classes -/

/-- The lines with a bottom OR-below `cb`. -/
def bLines {N M : ℕ} (C : Circuit) (n : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (cb : ℕ) : Set (Fin M) :=
  {l' | ∃ h u b, bottom C n pw lw I l' h u b ∧ orp C n (n + h) cb}

/-- The points with a source OR-below `c`. -/
def aPoints {N M : ℕ} (C : Circuit) (n : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (c : ℕ) : Set (Fin N) :=
  {p' | ∃ h a v, source C n pw lw I p' h a v ∧ orp C n (n + h) c}

/-- Class X: `p` misses a line of `bLines cb`. -/
def clX {N M : ℕ} (C : Circuit) (n : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (p : Fin N) (_l : Fin M) (_c cb : ℕ) : Prop :=
  ∃ l' ∈ bLines C n pw lw I cb, ¬ I p l'

/-- Class X*: a point of `aPoints c` is off `l`. -/
def clXs {N M : ℕ} (C : Circuit) (n : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (_p : Fin N) (l : Fin M) (c _cb : ℕ) : Prop :=
  ∃ p' ∈ aPoints C n pw lw I c, ¬ I p' l

/-- Class P: neither X nor X*, at least two bottom lines. -/
def clP {N M : ℕ} (C : Circuit) (n : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (p : Fin N) (l : Fin M) (c cb : ℕ) : Prop :=
  ¬ clX C n pw lw I p l c cb ∧ ¬ clXs C n pw lw I p l c cb ∧
    2 ≤ (bLines C n pw lw I cb).ncard

/-- Class L: neither X nor X*, the bottom lines are `{l}`, at least two source points. -/
def clL {N M : ℕ} (C : Circuit) (n : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (p : Fin N) (l : Fin M) (c cb : ℕ) : Prop :=
  ¬ clX C n pw lw I p l c cb ∧ ¬ clXs C n pw lw I p l c cb ∧
    bLines C n pw lw I cb = {l} ∧ 2 ≤ (aPoints C n pw lw I c).ncard

/-- Class O: neither X nor X*, the bottom lines are `{l}`, the source points `{p}`. -/
def clO {N M : ℕ} (C : Circuit) (n : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (p : Fin N) (l : Fin M) (c cb : ℕ) : Prop :=
  ¬ clX C n pw lw I p l c cb ∧ ¬ clXs C n pw lw I p l c cb ∧
    bLines C n pw lw I cb = {l} ∧ aPoints C n pw lw I c = {p}

/-! ## A12. Dirt and domination -/

/-- `S` is dirty off the line `l`: for every point `p'` off `l`, `S` is true on some input of at
most one point and two lines, with `p'` and the point off both lines. -/
def dOff {N M : ℕ} (C : Circuit) (n : ℕ) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (S : ℕ) (l : Fin M) : Prop :=
  ∀ p', ¬ I p' l → ∃ (P : Finset (Fin N)) (Y : Finset (Fin M)), P.card ≤ 1 ∧ Y.card ≤ 2 ∧
    (∀ a ∈ insert p' P, ∀ m ∈ Y, ¬ I a m) ∧ wval C (indW n (P.image pw ∪ Y.image lw)) S = true

/-- The output is true wherever the input `u` and the wire `m` are true. -/
def dom2 (n : ℕ) (C : Circuit) (u m : ℕ) : Prop :=
  ∀ z : Fin n → Bool, (∃ h : u < n, z ⟨u, h⟩ = true) → wval C z m = true →
    circuitFun n C z = true

/-! ## A13. The incidence function -/

/-- The incidence function on `N + M` inputs: some incident pair has both its point input
(`Fin.castAdd`) and its line input (`Fin.natAdd`) true. -/
def fpl {M : ℕ} (N : ℕ) (I : Fin N → Fin M → Prop) [DecidableRel I] (z : Fin (N + M) → Bool) :
    Bool :=
  decide (∃ p l, I p l ∧ z (Fin.castAdd M p) = true ∧ z (Fin.natAdd N l) = true)

end PEqualNP.ReadTwo
