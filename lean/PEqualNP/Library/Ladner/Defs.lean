import PEqualNP.Library.Universal.LazyDefs

/-!
# String functions for the delayed diagonal language

Helper module (proofs only, no statement may use it). Everything here is a total function on
bit strings, built from the primitives of the interpreter toolbox, so that polynomial-time
computability comes from combinators.

The construction takes a code string `cA` and a polynomial `q` (a verifier for an NP-complete
language, as given by `np_code`). The language `Acq cA q` is the verifier language. The delayed
diagonal language is

  `LL cA q = {y | psi y ∈ Acq cA q ∧ (|psi y| + 2) ^ stage (|psi y|) ≤ |y|}`,

where `psi y` is the first component of `y` as a self-delimiting pair and `stage` is a slowly
growing stage function. The stage function is the number of `true` symbols in a history string
`Hs n` of length `n`, which grows by one symbol per step: `Hs (n + 1) = Hs n ++ [Wb (Hs n)]`.
The bit `Wb h` says that the candidate string read off the `|h|`-th string of the enumeration
witnesses, within a budget of `|h|`, that the decider number `stage |h|` (a code string read
off the enumeration, clocked by `(|z| + 2) ^ stage`) differs from the language on it.

## Primitives

* `ones h`: the `true` symbols of `h` (a filter).
* `dropU cnt arg`: `arg` without its first `|cnt|` symbols (iterated `List.tail`).
* `leFlag a b`: the flag string of the length comparison `|a| ≤ |b|`.
* `tpStep`, `tpw zz k N`: the capped power, a string of length `min (|zz| ^ |k|) (|N| + 1)`,
  by iterating a capped unary multiplication on the packed state `pairB rest (pairB acc zz)`,
  where `|rest| + |acc|` stays equal to the cap.
-/

namespace PEqualNP.Library.Ladner

open PEqualNP.Library.Universal

/-- The `true` symbols of a string: the number of `true` symbols, in unary. -/
def ones (h : List Bool) : List Bool := h.filter id

/-- Drop as many symbols as the first argument has. -/
def dropU (cnt arg : List Bool) : List Bool := List.tail^[cnt.length] arg

/-- The flag string of a length comparison. -/
def leFlag (a b : List Bool) : List Bool := if a.length ≤ b.length then [true] else []

/-- The total of the capped power state. -/
def tpTot (s : List Bool) : List Bool := (unpairB s).1 ++ (unpairB (unpairB s).2).1

/-- The next accumulator of the capped power state. -/
def tpAcc (s : List Bool) : List Bool :=
  sel (leFlag (mulU (unpairB (unpairB s).2).1 (unpairB (unpairB s).2).2) (tpTot s)) (tpTot s)
    (mulU (unpairB (unpairB s).2).1 (unpairB (unpairB s).2).2)

/-- One step of the capped power on the packed state `pairB rest (pairB acc zz)`. -/
def tpStep (s : List Bool) : List Bool :=
  pairB (dropU (tpAcc s) (tpTot s)) (pairB (tpAcc s) (unpairB (unpairB s).2).2)

/-- The capped power: a string of length `min (|zz| ^ |k|) (|N| + 1)`. -/
def tpw (zz k N : List Bool) : List Bool :=
  (unpairB (unpairB (tpStep^[k.length] (pairB N (pairB [true] zz)))).2).1

/-- The first component of a string read as a self-delimiting pair. -/
def psi (z : List Bool) : List Bool := (unpairB z).1

/-- The candidate string of a history: the first component of the `|h|`-th string. -/
def cz (h : List Bool) : List Bool := (unpairB (succB^[h.length] [])).1

/-- The code string of the requirement with the given unary number. -/
def rq (st : List Bool) : List Bool := (unpairB (succB^[st.length] [])).1

/-- The base of the powers: two more symbols than the string. -/
def base (z : List Bool) : List Bool := true :: true :: z

/-- The clock of the current decider on the candidate, capped by the budget. -/
def clk (h : List Bool) : List Bool := tpw (base (cz h)) (ones h) h

/-- The number of `true` symbols among the first `|u|` symbols of `h`, in unary. -/
def stg (u h : List Bool) : List Bool := dropU (ones (dropU u h)) (ones h)

/-- The padding demanded of `z`, capped by the length of `z`, with stages read off `h`. -/
def padOf (z h : List Bool) : List Bool := tpw (base (psi z)) (stg (psi z) h) z

/-- The query to the interpreter for the verifier `cA` clocked by `q`. -/
def qry (cA : List Bool) (q : Polynomial ℕ) (x : List Bool) : List Bool :=
  pairB cA (pairB x (un (q.eval x.length)))

/-- The witness bit of a history: within the budget, the current decider differs from the
language on the candidate string. -/
def Wb (cA : List Bool) (q : Polynomial ℕ) (h : List Bool) : Bool :=
  decide ((psi (cz h)).length ≤ h.length) &&
    (decide ((clk h).length ≤ h.length) &&
      (decide ((qry cA q (psi (cz h)) ++ [true, true]).length ≤
          (lgU (mulU h [true])).length) &&
        (V (pairB (rq (ones h)) (pairB (cz h) (clk h)), []) !=
          (!(srch (qry cA q (psi (cz h))) h).isEmpty &&
            decide ((padOf (cz h) h).length ≤ (cz h).length)))))

/-- One step of the history. -/
def hstep (cA : List Bool) (q : Polynomial ℕ) (h : List Bool) : List Bool := h ++ [Wb cA q h]

/-- The history of length `n`. -/
def Hs (cA : List Bool) (q : Polynomial ℕ) (n : ℕ) : List Bool := (hstep cA q)^[n] []

/-- The stage function. -/
def stage (cA : List Bool) (q : Polynomial ℕ) (n : ℕ) : ℕ := (ones (Hs cA q n)).length

/-- The verifier language of `cA` clocked by `q`. -/
def Acq (cA : List Bool) (q : Polynomial ℕ) : Language Bool :=
  {x | ∃ w : List Bool, V (qry cA q x, w) = true}

/-- The padding condition. -/
def Gp (cA : List Bool) (q : Polynomial ℕ) (y : List Bool) : Prop :=
  ((psi y).length + 2) ^ stage cA q (psi y).length ≤ y.length

/-- The delayed diagonal language. -/
def LL (cA : List Bool) (q : Polynomial ℕ) : Language Bool :=
  {y | psi y ∈ Acq cA q ∧ Gp cA q y}

/-- The enumeration of clocked deciders. -/
def Dd (i : ℕ) (z : List Bool) : Bool :=
  V (pairB (rq (un i)) (pairB z (un ((z.length + 2) ^ i))), [])

end PEqualNP.Library.Ladner
