import PEqualNP.MetaComplexity.Helpers.MachineOwnCnf

/-!
# Helper module (proofs only): the renaming by earliest occurrence, and its machine body

`renF` is the function of row L-meta-500 (the new variable of a literal is the index, among the
items of the formula, of the earliest literal item with the same variable). The machine writes
the output item by item: for item `it` of the input code, `bodyR` gives the end pair for an end
item and, for a literal, its sign and the binary code of the count `cntR` (the number of item
indices `p` with no earlier or equal item carrying the same variable code).
-/

namespace PEqualNP.MetaComplexity.MachineRen

open PEqualNP.Search PEqualNP.Library PEqualNP.Library.Universal
  PEqualNP.Library.SearchHelpers.SatV PEqualNP.MetaComplexity.MachineOwn

/-- The function of the row. -/
def renF (φ : CNF) : CNF :=
  φ.map (fun c : Clause => c.map (fun l : Literal =>
    ((φ.flatMap (fun c' : Clause => c'.map some ++ [none])).findIdx
      (fun o : Option Literal => o.any (fun l' : Literal => l'.1 == l.1)), l.2)))

/-- The flags of the items `p' ≤ p` whose variable code is `t`. -/
def innerR (L : List (Option Literal)) (t : List Bool) (p : ℕ) : List Bool :=
  (List.range (p + 1)).flatMap (fun p' => bflag (decide ((itemAt L p').tail.tail = t)))

/-- In unary: the number of `p < M` with no item `p' ≤ p` of variable code `t`. -/
def cntR (M : ℕ) (L : List (Option Literal)) (t : List Bool) : List Bool :=
  (List.range M).flatMap (fun p => bflag (decide (innerR L t p = [])))

/-- The output written for one input item. -/
def bodyR (M : ℕ) (L : List (Option Literal)) (it : List Bool) : List Bool :=
  sel it [] (sel (bflag (isEnd it))
    (true :: sel (signF it) [false] [true] ++ vcode (cntR M L it.tail.tail).length) [false, false])

end PEqualNP.MetaComplexity.MachineRen
