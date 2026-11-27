import PEqualNP.MetaComplexity.Helpers.ReadersExport
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Plan module for the lower bound on the edge function (pieces specific to the lifting proof)

Statements only: every `Stmt*` below is a `Prop`, none is proved here. A builder proves
`theorem x : StmtX` in a file of its own. The plan, the paper proofs of the pieces and the list of
what is expected from the shared model and graph layers are in `notes/fullproof/plan.md`.

Nothing of the shared layers is defined here. The objects are the checked ones: clean gate lists
(`CleanL`, `vl` of `Parity3.lean`, `Parity4.lean`), readers and least lists (`Readers.Reads`,
`Readers.Least`, `Readers.Drop`, `Readers.PairFunnel` of `Readers.lean`), supports (`suppsFrom`,
`inputSupps` of `Support.lean`). New here, all specific to the proof: the redirect-and-delete move,
the tail potential, the semantic hypotheses on a set `D` of inputs, the frontier configuration.
-/

namespace PEqualNP.MetaComplexity.EdgeFn

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.Helpers.Readers

/-! ## The move: delete one gate and let its readers read an earlier wire -/

/-- The wire renaming when gate `p` is deleted and replaced by the earlier wire `a`. -/
def rd (N p a w : ℕ) : ℕ := if w < N + p then w else if w = N + p then a else w - 1

/-- The gate list with gate `p` deleted and every later read renamed by `rd`. -/
def rdel (N p a : ℕ) (gs : List Gate) : List Gate :=
  gs.take p ++ (gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (rd N p a)⟩

/-- Piece C1. The move keeps cleanness, removes one gate, keeps every earlier wire at every
input, and at an input where gate `p` agrees with wire `a` keeps every wire up to renaming. -/
def StmtRD : Prop :=
  ∀ (N : ℕ) (gs : List Gate) (p a : ℕ), CleanL N gs → p < gs.length → a < N + p →
    CleanL N (rdel N p a gs) ∧ (rdel N p a gs).length + 1 = gs.length ∧
    (∀ (x : Fin N → Bool) (w : ℕ), w < N + p → vl (rdel N p a gs) x w = vl gs x w) ∧
    (∀ x : Fin N → Bool, vl gs x (N + p) = vl gs x a →
      ∀ w : ℕ, vl (rdel N p a gs) x (rd N p a w) = vl gs x w)

/-! ## The tail potential -/

/-- Gate `j` is a NOT gate, or an OR gate whose wire is pointwise below `F`. -/
def TailOK (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (j : ℕ) : Prop :=
  ∃ g, gs[j]? = some g ∧ (g.op = GateOp.not ∨
    (g.op = GateOp.or ∧ ∀ x : Fin N → Bool, vl gs x (N + j) = true → F x = true))

/-- The last `t` gates are all tail gates. -/
def TailGE (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (t : ℕ) : Prop :=
  t ≤ gs.length ∧ ∀ j, gs.length ≤ j + t → j < gs.length → TailOK N F gs j

/-- Piece C3, the lift (FULL-PROOF 4.1 as a move on a least list). An OR gate at `p` reading
`l` and `h`, with `h` below `F`: deleting it, redirecting to `l` and adding `or [out, h]` on top
gives a least list again; if gate `p` is not a tail gate, the tail grows by one. -/
def StmtLift : Prop :=
  ∀ (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (o p l h : ℕ) (g : Gate),
    Least N F gs o → (∃ x y : Fin N → Bool, F x ≠ F y) →
    gs[p]? = some g → g.op = GateOp.or → (g.inputs = [l, h] ∨ g.inputs = [h, l]) →
    (∀ x : Fin N → Bool, vl gs x h = true → F x = true) →
    Least N F (rdel N p l gs ++ [⟨GateOp.or, [rd N p l o, h]⟩]) (N + (gs.length - 1)) ∧
    (¬ TailOK N F gs p → ∀ t, TailGE N F gs t →
      TailGE N F (rdel N p l gs ++ [⟨GateOp.or, [rd N p l o, h]⟩]) (t + 1))

/-- Piece C4, the exchange as an explicit move (replaces FULL-PROOF 4.4(b)). Two AND gates at
`p < p'` read `h` (other operands `l`, `q`), and `F` is true wherever `h` is false: deleting both,
redirecting to `l` and `q`, and adding `not [h]` and `or [out, that]` gives a least list again,
and the tail grows by two. The statement is symmetric in the roles of the two gates. -/
def StmtXMove : Prop :=
  ∀ (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (o p p' l q h : ℕ) (g g' : Gate),
    Least N F gs o → (∃ x y : Fin N → Bool, F x ≠ F y) → p < p' →
    gs[p]? = some g → g.op = GateOp.and → (g.inputs = [l, h] ∨ g.inputs = [h, l]) →
    gs[p']? = some g' → g'.op = GateOp.and → (g'.inputs = [q, h] ∨ g'.inputs = [h, q]) →
    (∀ x : Fin N → Bool, vl gs x h = false → F x = true) →
    ∃ (gs' : List Gate) (o' : ℕ), Least N F gs' o' ∧
      ∀ t, TailGE N F gs t → TailGE N F gs' (t + 2)

/-- Piece C5, the exchange with the strict count (FULL-PROOF 4.3 on clean lists). `T` is a set
of positions each of which reads `h`, or reads an OR gate or a NOT gate that reads `h`. -/
def StmtExch : Prop :=
  ∀ (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (o h : ℕ) (T : Finset ℕ),
    CleanL N gs → (∀ x : Fin N → Bool, vl gs x o = F x) → (∃ x y : Fin N → Bool, F x ≠ F y) →
    (∀ x : Fin N → Bool, vl gs x h = false → F x = true) →
    (∀ t ∈ T, Reads gs t h ∨ ∃ (r : ℕ) (g : Gate), gs[r]? = some g ∧
      (g.op = GateOp.or ∨ g.op = GateOp.not) ∧ Reads gs r h ∧ Reads gs t (N + r)) →
    ∃ (gs' : List Gate) (o' : ℕ), CleanL N gs' ∧ (∀ x : Fin N → Bool, vl gs' x o' = F x) ∧
      gs'.length + T.card ≤ gs.length + 2

/-! ## The semantic hypotheses on the set `D` of inputs -/

/-- The input `x` with every input of `D` set to false. -/
def zeroOn {N : ℕ} (D : Finset (Fin N)) (x : Fin N → Bool) : Fin N → Bool :=
  fun i => if i ∈ D then false else x i

/-- What the circuit part uses of the function `F` and the set `D` (H1 to H5 of the plan). -/
structure DeepHyp {N : ℕ} (F : (Fin N → Bool) → Bool) (D : Finset (Fin N)) : Prop where
  /-- H1: both restrictions at an input of `D` are not constant. -/
  nc : ∀ y ∈ D, ∀ b : Bool, ∃ x x' : Fin N → Bool,
    F (Function.update x y b) ≠ F (Function.update x' y b)
  /-- H2: no pair funnel between two inputs of `D`. -/
  nf : ∀ y ∈ D, ∀ y' ∈ D, y ≠ y' → ¬ PairFunnel F y y'
  /-- H3, the window: where `F` is false with `D` switched off, the inputs of `D` can be reset
  so that `F` is false with `y` off and true with `y` on. -/
  win : ∀ y ∈ D, ∀ x : Fin N → Bool, F (zeroOn D x) = false →
    ∃ x' : Fin N → Bool, (∀ i, i ∉ D → x' i = x i) ∧ x' y = false ∧ F x' = false ∧
      F (Function.update x' y true) = true
  /-- H4: switching `D` off can only lower `F`. -/
  mono : ∀ x : Fin N → Bool, F (zeroOn D x) = true → F x = true
  /-- H5: `F` is false at the all-false input. -/
  zero : F (fun _ => false) = false

/-- The wire `l` is a literal of the input `y`: the input wire itself, or a gate `not [y]`. -/
def IsLit (N : ℕ) (gs : List Gate) (y : Fin N) (l : ℕ) : Prop :=
  l = (y : ℕ) ∨ ∃ pn, l = N + pn ∧ gs[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩

/-- No input of `D` is in the support of wire `h`. -/
def DFree {N : ℕ} (D : Finset (Fin N)) (gs : List Gate) (h : ℕ) : Prop :=
  ∀ y ∈ D, y ∉ (suppsFrom gs (inputSupps N)).getD h ∅

/-- P1 fails: every input of `D`, and every NOT gate on one, has at most one reading position. -/
def OneReader {N : ℕ} (D : Finset (Fin N)) (gs : List Gate) : Prop :=
  (∀ y ∈ D, ∀ p q : ℕ, Reads gs p (y : ℕ) → Reads gs q (y : ℕ) → p = q) ∧
  (∀ y ∈ D, ∀ pn : ℕ, gs[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩ →
    ∀ p q : ℕ, Reads gs p (N + pn) → Reads gs q (N + pn) → p = q)

/-- The frontier configuration: gate `p` is binary, reads a literal `l` of `y ∈ D` and a wire
`h` whose support avoids `D`. -/
def Front {N : ℕ} (D : Finset (Fin N)) (gs : List Gate) (p : ℕ) (g : Gate) (y : Fin N)
    (l h : ℕ) : Prop :=
  gs[p]? = some g ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    (g.inputs = [l, h] ∨ g.inputs = [h, l]) ∧ y ∈ D ∧ IsLit N gs y l ∧ DFree D gs h

/-- Piece C8 (FULL-PROOF 3.2 and 3.4). In a least list where P1 fails there is a frontier gate,
and it is not the output. -/
def StmtFront : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (gs : List Gate)
    (o : ℕ), DeepHyp F D → D.Nonempty → Least (n + 1) F gs o → OneReader D gs →
    ∃ (p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ), Front D gs p g y l h ∧ o ≠ n + 1 + p

/-- Piece C9 (FULL-PROOF 3.3). At a frontier gate: an OR partner is below `F`; the negation of
an AND partner is below `F`, and an AND partner is a gate wire. -/
def StmtWin : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (gs : List Gate)
    (o p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ),
    DeepHyp F D → Least (n + 1) F gs o → OneReader D gs → Front D gs p g y l h →
    (g.op = GateOp.or → ∀ x : Fin (n + 1) → Bool, vl gs x h = true → F x = true) ∧
    (g.op = GateOp.and →
      (∀ x : Fin (n + 1) → Bool, vl gs x h = false → F x = true) ∧ n + 1 ≤ h)

/-- Piece C7 (FULL-PROOF 4.4 (a), (c) and the shape of the round rule). At an AND frontier gate
whose partner `h` has another reader: there is exactly one other reader, and it is an AND gate
reading `h` and a different wire. -/
def StmtTwo : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (gs : List Gate)
    (o p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ),
    DeepHyp F D → Least (n + 1) F gs o → OneReader D gs → Front D gs p g y l h →
    g.op = GateOp.and → (∃ r, r ≠ p ∧ Reads gs r h) →
    ∃ (r : ℕ) (g' : Gate) (q : ℕ), r ≠ p ∧ gs[r]? = some g' ∧ g'.op = GateOp.and ∧
      (g'.inputs = [q, h] ∨ g'.inputs = [h, q]) ∧
      ∀ t, Reads gs t h → t = p ∨ t = r

/-- Piece C6 (FULL-PROOF 3.5). An AND gate reading a literal of `y` and a gate wire that
nothing else reads pays: three gates at `y := false` for the literal `y`, four at `y := true`
for the literal NOT `y`. -/
def StmtAnd : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o p ph l : ℕ) (g : Gate)
    (y : Fin (n + 1)),
    Least (n + 1) F gs o →
    (∀ b : Bool, ∃ x x' : Fin (n + 1) → Bool,
      F (Function.update x y b) ≠ F (Function.update x' y b)) →
    Dep F y → gs[p]? = some g → g.op = GateOp.and →
    (g.inputs = [l, n + 1 + ph] ∨ g.inputs = [n + 1 + ph, l]) → IsLit (n + 1) gs y l →
    ph < gs.length → (∀ t, Reads gs t (n + 1 + ph) → t = p) →
    o ≠ n + 1 + p → o ≠ n + 1 + ph →
    (l = (y : ℕ) → Drop F y false 3 gs.length) ∧
    (l ≠ (y : ℕ) → Drop F y true 4 gs.length)

/-- Piece C10a (FULL-PROOF 5.1, extremal form). Some least list has an input of `D` with two
readers, or a NOT gate on one with two readers, or an AND frontier gate that is the only reader
of its partner. -/
def StmtExt : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (s : ℕ),
    DeepHyp F D → D.Nonempty → HasCircuitSize (n + 1) F s →
    ∃ (gs : List Gate) (o : ℕ), Least (n + 1) F gs o ∧ gs.length ≤ s ∧
      (¬ OneReader D gs ∨
        ∃ (p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ), Front D gs p g y l h ∧
          g.op = GateOp.and ∧ n + 1 ≤ h ∧ o ≠ n + 1 + p ∧ ∀ t, Reads gs t h → t = p)

/-- Piece C10b, the circuit theorem (FULL-PROOF 5.1 with only `r_0 ≤ 3`, `r_1 ≤ 4`). Some input
of `D` pays three gates at false or four at true. Root names only, apart from `DeepHyp`. -/
def StmtML : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (s : ℕ),
    DeepHyp F D → D.Nonempty → HasCircuitSize (n + 1) F s →
    ∃ y ∈ D,
      (∃ s' : ℕ, s' + 3 ≤ s ∧
        HasCircuitSize (n + 1) (fun x => F (Function.update x y false)) s') ∨
      (∃ s' : ℕ, s' + 4 ≤ s ∧
        HasCircuitSize (n + 1) (fun x => F (Function.update x y true)) s')

/-! ## The final statement, on root names only (a draft: the route's row statement decides) -/

/-- The lower bound. `G` is a graph on the inputs in which every cycle has length at least 7
and no walk shorter than 7 joins two distinct vertices of degree at least 3; `A` is a set of
inputs that no edge meets; `k` is at most the size of every vertex cover. Then every fan-in two
circuit for "some input of `A` is true or both ends of some edge are true" has at least
`|A| + |E| + k - 1` gates. -/
def StmtLB : Prop :=
  ∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)),
    (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 7 ≤ c.length) →
    (∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard →
      ∀ p : G.Walk u v, 7 ≤ p.length) →
    (∀ i j : Fin n, G.Adj i j → i ∉ A) →
    (A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) →
    (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) →
    HasCircuitSize n
      (fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨
        ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) s →
    A.card + G.edgeSet.ncard + k ≤ s + 1

end PEqualNP.MetaComplexity.EdgeFn
