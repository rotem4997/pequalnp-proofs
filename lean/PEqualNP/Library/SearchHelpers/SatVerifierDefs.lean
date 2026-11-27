import PEqualNP.Library.Universal.LazyDefs
import PEqualNP.Library.SearchHelpers.Encoding

/-!
# String functions for a verifier of SAT

Helper module (proofs only, no statement may use it). It defines a total verifier `SV` on pairs
(input, witness) of bit strings as a composition of small named total functions on bit strings.
`SatVerifier.lean` proves that `SV` characterizes SAT with witnesses no longer than the input.
No machine appears here.

Strings are read in pairs of bits, as in `PEqualNP.Search.encodeLiteral`: `[true, d]` is a digit,
`[false, b]` is a terminator. An item is a run of digit pairs closed by one terminator pair.

The witness is any bit string. It is read as a sequence of items, and the assignment it denotes
makes the variable `i` true exactly when `vcode i` (the digits of `i` and the pair
`[false, true]`) is one of the first `w.length` items of `w`. Every string denotes an
assignment, so the witness needs no well-formedness test.

## Primitives and the toolbox item that computes each

* `headI`: a finite-state transducer (states: at a pair boundary, inside a digit pair, inside
  the terminator pair, done; one output symbol per input symbol at most). The first item of a
  string, with its terminator pair.
* `dropI`: a finite-state transducer (same states; copies after the first item). The string
  without its first item. `headI s ++ dropI s = s`, and `dropI` shortens a nonempty string.
* `polB`: the second symbol of a string as a decision bit (a finite-state test).
* `isEnd`: test of the fixed prefix `[false, false]` (a finite-state test).
* `wfB`: a finite-state acceptor with the nine states `WS` and the transition `wfD`; the
  string is accepted when the run from `WS.a` ends in `WS.a`. `wfB_eq_fstRun` writes it as a
  transducer that writes nothing while reading and one symbol at the end.
* `memStep`: `unpairB` twice, `dropI`, `headI`, equality of two strings as a decision bit,
  `bflag`, append, `pairB` twice. One step of the search for an item on the packed state
  `pairB item (pairB rest flag)`. Output at most 3 symbols longer than the input.
* `memB c w`: the bounded iteration `memStep^[w.length]` on `pairB c (pairB w [])`, then
  non-emptiness of the flag component.
* `litB it w`: `List.tail` twice, `memB`, `polB`, Boolean connectives. The value of the literal
  item `it` under the assignment denoted by `w`.
* `stW`, `stR`, `stC`, `stB`: components by `unpairB`.
* `evStep`: the components, `dropI`, `headI`, `isEnd`, `litB`, emptiness of a string, `bflag`,
  append, a constant, `pairB` three times, and one `sel`. One step of the evaluation on the
  packed state `pairB witness (pairB rest (pairB clauseFlag badFlag))`: it consumes one item of
  the rest. Output at most 5 symbols longer than the input.
* `evalB x w`: the bounded iteration `evStep^[x.length]` on `pairB w (pairB x (pairB [] []))`,
  then emptiness of the bad flag.
* `SV`: `wfB` and `evalB`, with a Boolean conjunction.
-/

namespace PEqualNP.Library.SearchHelpers.SatV

open PEqualNP.Search PEqualNP.Library.Universal

/-! ### Items -/

/-- The first item of a string: digit pairs up to and including the first terminator pair. -/
def headI : List Bool → List Bool
  | [] => []
  | [a] => [a]
  | true :: d :: r => true :: d :: headI r
  | false :: d :: _ => [false, d]

/-- The string without its first item. -/
def dropI : List Bool → List Bool
  | [] => []
  | [_] => []
  | true :: _ :: r => dropI r
  | false :: _ :: r => r

/-- The second symbol as a decision bit: the polarity of a literal item. -/
def polB : List Bool → Bool
  | _ :: b :: _ => b
  | _ => false

/-- The string starts with the end-of-clause pair. -/
def isEnd : List Bool → Bool
  | false :: false :: _ => true
  | _ => false

/-- The code of a variable as an item: its binary digits as digit pairs, then `[false, true]`.
A literal `(i, b)` is encoded as `true :: b :: vcode i`. -/
def vcode (i : ℕ) : List Bool := (i.bits.flatMap fun d => [true, d]) ++ [false, true]

/-! ### Well-formedness: a finite-state acceptor -/

/-- States of the acceptor. `a`: at a pair boundary with no clause open. `b`: at a pair boundary
after a literal. `c`: at a pair boundary inside a literal whose digits so far are canonical.
`d`: the same, the last digit being `false`. `abT`, `abF`, `cT`, `cF`: inside a pair whose first
symbol was `true` or `false`, coming from `a` or `b`, or from `c` or `d`. `dead`: rejected. -/
inductive WS : Type
  | a | b | c | d | abT | abF | cT | cF | dead
  deriving DecidableEq

instance : Fintype WS :=
  ⟨{.a, .b, .c, .d, .abT, .abF, .cT, .cF, .dead}, fun q => by cases q <;> simp⟩

/-- Transition of the acceptor. -/
def wfD : WS → Bool → WS
  | .a, true => .abT
  | .a, false => .abF
  | .b, true => .abT
  | .b, false => .abF
  | .abT, _ => .c
  | .abF, false => .a
  | .abF, true => .dead
  | .c, true => .cT
  | .c, false => .cF
  | .d, true => .cT
  | .d, false => .dead
  | .cT, true => .c
  | .cT, false => .d
  | .cF, true => .b
  | .cF, false => .dead
  | .dead, _ => .dead

/-- The string is the encoding of a CNF formula. -/
def wfB (x : List Bool) : Bool := decide (x.foldl wfD .a = .a)

/-! ### Membership of an item in the witness -/

/-- One step of the search for an item on the packed state `pairB item (pairB rest flag)`:
compare the first item of the rest with the item, record an equality in the flag, and drop the
first item of the rest. -/
def memStep (s : List Bool) : List Bool :=
  pairB (unpairB s).1 (pairB (dropI (unpairB (unpairB s).2).1)
    ((unpairB (unpairB s).2).2 ++
      bflag (decide (headI (unpairB (unpairB s).2).1 = (unpairB s).1))))

/-- The item `c` is one of the first `w.length` items of `w`. -/
def memB (c w : List Bool) : Bool :=
  !(unpairB (unpairB (memStep^[w.length] (pairB c (pairB w [])))).2).2.isEmpty

/-- The value of the literal item `it` under the assignment denoted by `w`: the variable is
listed in `w` exactly when the polarity is `true`. -/
def litB (it w : List Bool) : Bool :=
  (memB it.tail.tail w && polB it) || (!memB it.tail.tail w && !polB it)

/-! ### Evaluation -/

/-- The witness of a packed state. -/
def stW (s : List Bool) : List Bool := (unpairB s).1

/-- The rest of the input of a packed state. -/
def stR (s : List Bool) : List Bool := (unpairB (unpairB s).2).1

/-- The clause flag of a packed state: nonempty when a literal of the open clause is true. -/
def stC (s : List Bool) : List Bool := (unpairB (unpairB (unpairB s).2).2).1

/-- The bad flag of a packed state: nonempty when a closed clause was false. -/
def stB (s : List Bool) : List Bool := (unpairB (unpairB (unpairB s).2).2).2

/-- One step of the evaluation on the packed state
`pairB witness (pairB rest (pairB clauseFlag badFlag))`. When the rest starts with the
end-of-clause pair, the bad flag records an empty clause flag and the clause flag is emptied;
otherwise the first item is read as a literal and its value is recorded in the clause flag. The
item is dropped from the rest. -/
def evStep (s : List Bool) : List Bool :=
  pairB (stW s) (pairB (dropI (stR s))
    (sel (bflag (isEnd (stR s)))
      (pairB (stC s ++ bflag (litB (headI (stR s)) (stW s))) (stB s))
      (pairB [] (stB s ++ bflag (stC s).isEmpty))))

/-- No clause of `x` is false under the assignment denoted by `w` (on a well-formed `x`). -/
def evalB (x w : List Bool) : Bool :=
  (stB (evStep^[x.length] (pairB w (pairB x (pairB [] []))))).isEmpty

/-- The verifier: `x` encodes a CNF formula that the assignment denoted by `w` satisfies. -/
def SV (p : List Bool × List Bool) : Bool := wfB p.1 && evalB p.1 p.2

end PEqualNP.Library.SearchHelpers.SatV
