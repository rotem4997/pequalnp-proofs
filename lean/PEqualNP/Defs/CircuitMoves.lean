import Mathlib.Data.Fintype.Pi
import PEqualNP.Defs.CircuitLowerBounds
import PEqualNP.Defs.NestedCoverCircuit

/-!
# Two moves on circuits: LIFT and JUNK DROP, on top of gate erasure

The setting is the circuit model of `PEqualNP.Defs.CircuitLowerBounds`: on `n` inputs, wire
`i < n` is the input `x_i` and gate number `j` (from `0`) is wire `n + j`; a read of a wire that
does not exist yet gives `false`.

The objects (item D3 of the meta-2 desk hand-over and the flattening note of the last-gate route).

* ERASING gate `m` with redirect `p`: gate `m` (wire `n + m`) is removed; in every LATER gate, and
  in the output index, a read of wire `n + m` becomes a read of `p`, and a read of a wire above
  `n + m` goes down by one (it is the same gate, one place earlier). Earlier gates are untouched.
* LIFT at `(m, h)`: gate `m` is `OR(p, h)` (either operand order), `h` is a gate whose function is
  at most the output function of the circuit on every input of length `n`. The readers of `m`
  read `p`, `m` is erased, and a new LAST gate `OR(old output, h)` is the output.
* JUNK DROP at gate `j`: gate `j` is `AND(u, w)` (either operand order) where `w` is an OR gate
  `OR(q, r)` (either operand order); gate `j` becomes `AND(u, q)` (the operand `w` is replaced by
  `q` in its own position). Nothing else changes; gate `w` stays (it may become unread).

Names.
* `eraseRedirect n m p i`: the new index of a read of wire `i` when gate `m` is erased.
* `eraseGate n C m p`: the circuit with gate `m` erased and its readers sent to `p`.
* `WireBelowOutput n C w`: on every input of length `n`, wire `w` true implies the output
  true (the function of `w` is at most the function of `C`, the paper's "below F").
* `liftAt n C m p h`: the lifted circuit, `eraseGate n C m p` plus the gate `OR(output, h)`.
* `Lift n C C'`, `JunkDrop n C C'`: the two moves, as relations, each decidable.
* `gateDecEq`, `circuitDecEq`: decidable equality of gates and circuits (not global instances,
  following the pattern of `gateOpDecEq`).

Caveats a statement must respect.
* `p` is an index of the NEW circuit; it names the same wire in both circuits exactly when
  `p < n + m`. `Lift` requires `p < n + m` and `h < n + m` (they are operands of gate `m`, so
  they exist before it); `eraseGate` on its own accepts any `p`, and with `p >= n + m` the
  redirected reads point wherever `p` points in the new circuit. With `m` past the last gate
  `eraseGate` returns `C` unchanged.
* The moves are SYNTACTIC. `Lift` carries the paper's side condition (`h` below the output
  function), and keeps the function on NOT-free circuits (Lemma 3 of the flattening note), not
  in general (that argument is on paper, not checked here). `JunkDrop` carries NO side
  condition: it narrows `AND(u, OR(q, r))` to `AND(u, q)`, which keeps the function
  only when what is dropped is junk (Lemma 2 of the note). A statement "by steps that keep the
  function" must add `C'.eval = C.eval` on inputs of length `n` itself.
* Both moves keep the number of gates. `Lift` does not require `m` to differ from the output (the
  note claims no lift there; with `m` the output the lift rebuilds an equivalent gate), nor
  `p` to differ from `h`, nor fan-in two elsewhere in the circuit.
* Operands of the moved gates must exist when read: `Lift` asks `p, h < n + m` and `n <= h`
  (`h` is a gate), `JunkDrop` asks `u < n + j`, `n <= w < n + j` and `q, r < w`.
* The output of the lifted circuit is its last gate; the output of the input circuit may be any
  wire.
-/

namespace PEqualNP.CircuitMoves

open PEqualNP.CircuitLowerBounds

/-- The new index of a read of wire `i` when gate `m` (wire `n + m`) is erased with redirect
`p`: wire `n + m` becomes `p`, a wire above it goes down by one, a wire below it stays. -/
def eraseRedirect (n m p i : ℕ) : ℕ :=
  if i = n + m then p else if n + m < i then i - 1 else i

/-- Gate `m` of `C` on `n` inputs erased: the gates before it as they were, the gates after it
with every read renamed by `eraseRedirect n m p`, the output renamed likewise. If `C` has no
gate `m`, `C` itself. -/
def eraseGate (n : ℕ) (C : Circuit) (m p : ℕ) : Circuit :=
  if m < C.gates.length then
    { gates := C.gates.take m ++
        (C.gates.drop (m + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩)
      output := eraseRedirect n m p C.output }
  else C

/-- On every input of length `n`, if wire `w` of `C` is true then the output of `C` is true. -/
def WireBelowOutput (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD w false = true → C.eval (List.ofFn x) = true

/-- The lift of `C` at gate `m = OR(p, h)`: gate `m` erased with its readers sent to `p`, then a
new last gate `OR(output, h)`, which is the new output. -/
def liftAt (n : ℕ) (C : Circuit) (m p h : ℕ) : Circuit :=
  { gates := (eraseGate n C m p).gates ++ [⟨GateOp.or, [(eraseGate n C m p).output, h]⟩]
    output := n + (eraseGate n C m p).gates.length }

/-- Equality of gates is decidable. Not a global instance. -/
@[instance_reducible]
def gateDecEq : DecidableEq Gate := fun a b =>
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  decidable_of_iff (a.op = b.op ∧ a.inputs = b.inputs)
    (by cases a; cases b; simp)

/-- Equality of circuits is decidable. Not a global instance. -/
@[instance_reducible]
def circuitDecEq : DecidableEq Circuit := fun a b =>
  letI := gateDecEq
  decidable_of_iff (a.gates = b.gates ∧ a.output = b.output)
    (by cases a; cases b; simp)

attribute [local instance] gateDecEq circuitDecEq

/-- LIFT: `C'` is a lift of `C` on `n` inputs. Some gate `m` is `OR(p, h)` or `OR(h, p)` with
`p, h` earlier wires, `h` a gate whose function is at most that of `C`, and `C'` is
`liftAt n C m p h`. -/
def Lift (n : ℕ) (C C' : Circuit) : Prop :=
  ∃ m < C.gates.length, ∃ p < n + m, ∃ h < n + m, n ≤ h ∧
    (C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩) ∧
    WireBelowOutput n C h ∧ C' = liftAt n C m p h

/-- JUNK DROP: `C'` is `C` with one gate `AND(u, OR(q, r))` replaced by `AND(u, q)`. Gate `j` is
`AND(u, w)` or `AND(w, u)`, wire `w` is an earlier gate `OR(q, r)` or `OR(r, q)`, and `C'` has
`w` replaced by `q` in gate `j`, everything else equal. -/
def JunkDrop (n : ℕ) (C C' : Circuit) : Prop :=
  ∃ j < C.gates.length, ∃ u < n + j, ∃ w < n + j, n ≤ w ∧ ∃ q < w, ∃ r < w,
    (C.gates[w - n]? = some ⟨GateOp.or, [q, r]⟩ ∨ C.gates[w - n]? = some ⟨GateOp.or, [r, q]⟩) ∧
    ((C.gates[j]? = some ⟨GateOp.and, [u, w]⟩ ∧
        C' = { gates := C.gates.set j ⟨GateOp.and, [u, q]⟩, output := C.output }) ∨
      (C.gates[j]? = some ⟨GateOp.and, [w, u]⟩ ∧
        C' = { gates := C.gates.set j ⟨GateOp.and, [q, u]⟩, output := C.output }))

instance (n : ℕ) (C : Circuit) (w : ℕ) : Decidable (WireBelowOutput n C w) := by
  unfold WireBelowOutput; infer_instance

instance (n : ℕ) (C C' : Circuit) : Decidable (Lift n C C') := by
  unfold Lift; infer_instance

instance (n : ℕ) (C C' : Circuit) : Decidable (JunkDrop n C C') := by
  unfold JunkDrop; infer_instance

end PEqualNP.CircuitMoves
