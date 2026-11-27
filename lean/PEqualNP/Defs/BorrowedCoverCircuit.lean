import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import PEqualNP.Defs.NestedCoverCircuit

/-!
# Borrowed cover circuits of a graph function

The setting is that of `PEqualNP.Defs.NestedCoverCircuit`: inputs `Fin n`, wire `i < n` is
`x_i`, gate number `j` is wire `n + j`, a graph `K` on `Fin n` and a set `A` of inputs give the
graph function `F_(K,A)`. A nested cover circuit is a circuit together with data (`NCCData`)
labelling every gate with its role; this module adds one local departure from it.

The object (section 2 of the borrowed cover note of the last-gate route). A BORROWING in nested
data is a quintuple `(s, t, q, r, m)` of distinct vertices (the note calls `m` "n"; here `n` is
the number of inputs) with
* (b1) `s -> t` is a tie;
* (b2) `t` is a root (no tie out of `t`) and the vertices owned by `t` are exactly `s` and `q`;
* (b3) `m` is in the cover, `m != t`, and `m` owns `ms` and `mr`;
* (b4) `rq` is an edge of `K` (so `s t q r m` is a 5-cycle);
* (b5) the leaf `lam_m(s)` is the root of `Z_s`, and some OR gate `a` of `O_m` has exactly the
  two operands `lam_m(s)` and `lam_m(r)` (in either order);
* (b6) every leaf `lam_t'(t)`, `t'` owning `t't`, is the input `x_t`.
A BORROWED COVER CIRCUIT is the circuit of nested data with a set of borrowings with pairwise
distinct `s`, in which for each borrowing the term of `s` is `B_s = AND(a, root of O_s)` in place
of `AND(root of Z_s, root of O_s)`; every other gate is as in a nested cover circuit.

The formal reading. As for nested cover circuits, the module does not generate the circuit: it
says when a given circuit IS one. The data is `BCCData n`: nested data `base` and, for each
vertex `s`, an optional borrowing `borrow s` (keyed by `s`, so the `s` are distinct by
construction) recording `t, q, r, m` and the gate index of `a`. `BValid` is `Valid` of
`NestedCoverCircuit` verbatim, except that the condition `TermOK` on the term of a borrowed `s`
is replaced by `BorrowedTermOK` (the term reads the wire of `a` in place of the root of `Z_s`),
plus the condition `IsBorrowing` on every recorded borrowing. Nothing else changes: the tree
`Z_s` is still checked as an OR tree with root `zroot s` (its root is simply no longer read by
`B_s`; the tree conditions count reads inside the tree only).

Relation to `IsNestedCoverCircuit`. With no borrowing (`borrow s = none` for all `s`), `BValid`
is exactly `Valid` on `base`; so every nested cover circuit is a borrowed cover circuit, and a
circuit is nested iff it has a borrowed labelling with no borrowing. That a labelling with at
least one borrowing is never nested (the borrowed term is an AND gate not below `F`) is Lemma B of
the note, on paper only; it is NOT part of the definition.

* `Borrow n`: the record `t, q, r, m, gate` of one borrowing (the `s` is the key).
* `BCCData n`: `base : NCCData n` and `borrow : Fin n → Option (Borrow n)`.
* `IsBorrowing n K C d s b`: conditions (b1) to (b6) for `(s, b.t, b.q, b.r, b.m)` and the gate
  `b.gate` of `C`, against nested data `d`.
* `BorrowedTermOK n C d s b`: the gate at `bw s` has role `B` of `s` and is
  `AND(a, root of O_s)` in either order, `a` the wire `n + b.gate`.
* `BValid n K A C d`: `d` labels `C` as a borrowed cover circuit of `(K, A)`.
* `NoBorrowing d`: no vertex carries a borrowing.
* `IsBorrowedCoverCircuit n K A C`: some `d` with `BValid`.

Caveats a statement must respect.
* All caveats of `NestedCoverCircuit` hold here (`A` disjoint from the edge vertices, the empty
  case, `ReadsBack` imposing acyclicity, vertex numbers in `role` compared with `t.val`).
* The note works under (G1) no triangle and no 4-cycle and (G2) no cycle inside a minimum cover.
  Nothing here enforces them. The consequences the note draws from them (`q` outside the cover,
  two borrowings never share `t`, the borrowed gate list is acyclic, the circuit computes
  `F_(K,A)` with `|A| + |E| + |T| - 1` gates) are theorems of the note on paper, not part of the
  definition; `q` outside the cover in particular is NOT required.
* "Distinct" is `[s, t, q, r, m].Nodup`; `m != t` is part of it.
* The degenerate case of the note (`t` owns only `s`) is NOT a borrowing here ((b2) asks for the
  two owned vertices `s` and `q`, with `q != s` by distinctness).
* `IsBorrowedCoverCircuit` includes the nested ones. A statement about the circuits that are
  borrowed and not nested must say so (for example
  `IsBorrowedCoverCircuit n K A C ∧ ¬ IsNestedCoverCircuit n K A C`).
-/

namespace PEqualNP.MetaComplexity.BorrowedCover

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

/-- One borrowing `(s, t, q, r, m)` with the gate `a` of `O_m`; the vertex `s` is the key under
which it is stored in `BCCData`. -/
structure Borrow (n : ℕ) where
  /-- The receiver `t`: `s -> t`, and `t` owns exactly `s` and `q`. -/
  t : Fin n
  /-- The other vertex `q` owned by `t`. -/
  q : Fin n
  /-- The borrowed vertex `r`, owned by `m` and adjacent to `q`. -/
  r : Fin n
  /-- The cover vertex `m` (called `n` in the note) owning `ms` and `mr`. -/
  m : Fin n
  /-- The gate number of `a = OR(lam_m(s), lam_m(r))`, a gate of `O_m`; its wire is
  `n + gate`. -/
  gate : ℕ
  deriving DecidableEq

/-- The data of a borrowed cover circuit: nested data and, for each `s`, an optional
borrowing. -/
structure BCCData (n : ℕ) where
  /-- The nested data underneath. -/
  base : NCCData n
  /-- `borrow s = some b`: the term of `s` is borrowed, along `(s, b.t, b.q, b.r, b.m)`. -/
  borrow : Fin n → Option (Borrow n)

/-- Conditions (b1) to (b6): `(s, b.t, b.q, b.r, b.m)` with the gate `b.gate` of `C` is a
borrowing in the nested data `d`. -/
def IsBorrowing (n : ℕ) (K : SimpleGraph (Fin n)) (C : Circuit) (d : NCCData n) (s : Fin n)
    (b : Borrow n) : Prop :=
  [s, b.t, b.q, b.r, b.m].Nodup ∧
    -- (b1)
    d.tie s = some b.t ∧
    -- (b2)
    b.t ∈ d.cover ∧ d.tie b.t = none ∧ (∀ v, d.owns b.t v = true ↔ (v = s ∨ v = b.q)) ∧
    -- (b3)
    b.m ∈ d.cover ∧ d.owns b.m s = true ∧ d.owns b.m b.r = true ∧
    -- (b4)
    K.Adj b.r b.q ∧
    -- (b5)
    d.lam b.m s = d.zroot s ∧ b.gate < C.gates.length ∧ d.role b.gate = (Kind.o, b.m.val) ∧
    (gateAt C b.gate).op = GateOp.or ∧
    ((gateAt C b.gate).inputs = [d.lam b.m s, d.lam b.m b.r] ∨
      (gateAt C b.gate).inputs = [d.lam b.m b.r, d.lam b.m s]) ∧
    -- (b6)
    ∀ t', d.owns t' b.t = true → d.lam t' b.t = b.t.val

/-- The borrowed term of `s`: the gate at wire `bw s` has role `B` of `s` and is the AND of the
wire of `a` (wire `n + b.gate`) and the root of `O_s`, in either order. -/
def BorrowedTermOK (n : ℕ) (C : Circuit) (d : NCCData n) (s : Fin n) (b : Borrow n) : Prop :=
  ∃ j < C.gates.length, d.bw s = n + j ∧ d.role j = (Kind.b, s.val) ∧
    (gateAt C j).op = GateOp.and ∧
    ((gateAt C j).inputs = [n + b.gate, d.oroot s] ∨ (gateAt C j).inputs = [d.oroot s, n + b.gate])

/-- The data `d` labels `C` as a borrowed cover circuit of `(K, A)`: `Valid` of the nested
module on `d.base`, with the term condition of each borrowed `s` replaced by `BorrowedTermOK`,
and every recorded borrowing satisfying `IsBorrowing`. -/
def BValid (n : ℕ) (K : SimpleGraph (Fin n)) (A : Finset (Fin n)) (C : Circuit)
    (d : BCCData n) : Prop :=
  ReadsBack n C ∧ IsMinCover K d.base.cover ∧ OwnerOK K d.base ∧ TieOK d.base ∧
    RolesOK n C d.base ∧
    (∀ t ∈ d.base.cover,
      ((d.borrow t).isNone = true → TermOK n C d.base t) ∧
      (∀ b ∈ d.borrow t, BorrowedTermOK n C d.base t b) ∧
      IsOrTree n C (gatesOf d.base C Kind.z t.val) (zLeaves d.base t) (d.base.zroot t) ∧
      IsOrTree n C (gatesOf d.base C Kind.o t.val) (oLeaves d.base t) (d.base.oroot t) ∧
      ∀ r, d.base.owns t r = true → LamOK n C d.base t r) ∧
    IsOrTree n C (topGates d.base C) (topLeaves d.base A) C.output ∧
    ∀ s, ∀ b ∈ d.borrow s, IsBorrowing n K C d.base s b

/-- No vertex carries a borrowing. -/
def NoBorrowing {n : ℕ} (d : BCCData n) : Prop :=
  ∀ s, d.borrow s = none

/-- `C` is a borrowed cover circuit of `(K, A)` on `n` inputs (section 2 of the note). Nested
cover circuits are the case with no borrowing. -/
def IsBorrowedCoverCircuit (n : ℕ) (K : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (C : Circuit) : Prop :=
  ∃ d : BCCData n, BValid n K A C d

/-! ## Decidability, so that small rows can be checked by `decide` -/

attribute [local instance] gateOpDecEq

instance (n : ℕ) (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (C : Circuit) (d : NCCData n)
    (s : Fin n) (b : Borrow n) : Decidable (IsBorrowing n K C d s b) := by
  unfold IsBorrowing; infer_instance

instance (n : ℕ) (C : Circuit) (d : NCCData n) (s : Fin n) (b : Borrow n) :
    Decidable (BorrowedTermOK n C d s b) := by
  unfold BorrowedTermOK; infer_instance

instance (n : ℕ) (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (A : Finset (Fin n))
    (C : Circuit) (d : BCCData n) : Decidable (BValid n K A C d) := by
  unfold BValid; infer_instance

end PEqualNP.MetaComplexity.BorrowedCover
