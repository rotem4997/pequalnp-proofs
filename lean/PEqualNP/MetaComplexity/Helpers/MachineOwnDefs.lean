import PEqualNP.Defs

/-!
# Helper module (proofs only): the function of row L-meta-499, with its parts named

The names follow the statement: `offO` (item index of the first item of a clause), `posO`,
`XO` (the slot vertices), `litO`, `wO`, `fO` (first positive literal, or the width), `innerO`
(the slot triples of one subdivided edge), `blkO` (the lists written for the item `(i, j)`),
`tailO` (the lists of the two hub edges and their owners) and `ownO`, the whole list.
`ownO` unfolds to the function of the statement (checked by `rfl` in `MachineOwn.lean`).
-/

namespace PEqualNP.MetaComplexity.MachineOwn

open PEqualNP.Search

def offO (ψ : CNF) (i : ℕ) : ℕ := ((ψ.take i).map (fun c : Clause => c.length + 1)).sum

def posO (E : ℕ) (ψ : CNF) (i j : ℕ) : ℕ := 2 * (E + 1) + offO ψ i + j

def XO (E k u v t : ℕ) : ℕ := 3 * (E + 1) + 2 * k * (u * (3 * (E + 1)) + v) + t - 1

def litO (ψ : CNF) (i j : ℕ) : Literal := (ψ.getD i []).getD j (0, false)

def wO (ψ : CNF) (i : ℕ) : ℕ := (ψ.getD i []).length

def fO (ψ : CNF) (i : ℕ) : ℕ := (ψ.getD i []).findIdx (fun l : Literal => l.2)

def innerO (E k u v : ℕ) (inT : Bool) : List (List ℕ) :=
  ((List.range (2 * k)).filter (fun s : ℕ => decide ((s + 1) % 2 = 0 ↔ inT = true))).map
    (fun s : ℕ => [XO E k u v (s + 1), if s = 0 then u else XO E k u v s,
      if s + 1 = 2 * k then v else XO E k u v (s + 2)])

/-- Part A of the block of item `(i, j)`. -/
def blkA (E k : ℕ) (ψ : CNF) (i j : ℕ) : List (List ℕ) :=
  if j < wO ψ i then innerO E k (2 * (litO ψ i j).1 + (if (litO ψ i j).2 then 1 else 0))
    (posO E ψ i j) (litO ψ i j).2 else innerO E k (2 * E + 1) (posO E ψ i j) true

/-- Part B: the subdivided clause edges to the later items of the clause. -/
def blkB (E k : ℕ) (ψ : CNF) (i j : ℕ) : List (List ℕ) :=
  ((List.range (wO ψ i + 1)).filter (fun l : ℕ => decide (j < l))).flatMap
    (fun l : ℕ => innerO E k (posO E ψ i j) (posO E ψ i l) (decide (j ≠ fO ψ i)))

/-- Part C: the variable edge, at the first occurrence. -/
def blkC (E k : ℕ) (ψ : CNF) (i j : ℕ) : List (List ℕ) :=
  if j < wO ψ i ∧ (litO ψ i j).1 = offO ψ i + j then
    innerO E k (2 * (litO ψ i j).1) (2 * (litO ψ i j).1 + 1) false else []

/-- Part D: the owner list of the clause vertex. -/
def blkD (E k : ℕ) (ψ : CNF) (i j : ℕ) : List (List ℕ) :=
  if j ≠ fO ψ i then [posO E ψ i j :: ((if j < wO ψ i ∧ (litO ψ i j).2 = false then
    [XO E k (2 * (litO ψ i j).1) (posO E ψ i j) (2 * k)] else []) ++
    (if fO ψ i < j then [XO E k (posO E ψ i (fO ψ i)) (posO E ψ i j) (2 * k)] else []) ++
    ((List.range (wO ψ i + 1)).filter (fun l : ℕ => decide (j < l))).map
      (fun l : ℕ => XO E k (posO E ψ i j) (posO E ψ i l) 1))] else []

/-- The positive occurrences of variable `v`, as slot vertices next to `2 v + 1`. -/
def occO (E k : ℕ) (ψ : CNF) (v : ℕ) : List ℕ :=
  (List.range ψ.length).flatMap (fun i' : ℕ => ((List.range (wO ψ i')).filter
    (fun j' : ℕ => decide ((litO ψ i' j').1 = v ∧ (litO ψ i' j').2 = true))).map
      (fun j' : ℕ => XO E k (2 * v + 1) (posO E ψ i' j') 1))

/-- Part E: the owner list of the positive variable vertex, at the first occurrence. -/
def blkE (E k : ℕ) (ψ : CNF) (i j : ℕ) : List (List ℕ) :=
  if j < wO ψ i ∧ (litO ψ i j).1 = offO ψ i + j then
    [(2 * (litO ψ i j).1 + 1) :: XO E k (2 * (litO ψ i j).1) (2 * (litO ψ i j).1 + 1) (2 * k) ::
      occO E k ψ (litO ψ i j).1] else []

def blkO (E k : ℕ) (ψ : CNF) (i j : ℕ) : List (List ℕ) :=
  blkA E k ψ i j ++ blkB E k ψ i j ++ blkC E k ψ i j ++ blkD E k ψ i j ++ blkE E k ψ i j

def tailO (E k : ℕ) (ψ : CNF) : List (List ℕ) :=
  innerO E k (2 * E) (2 * E + 1) false ++ innerO E k (2 * E) (3 * E + 2) false ++
    [(2 * E + 1) :: XO E k (2 * E) (2 * E + 1) (2 * k) ::
      (List.range ψ.length).map (fun i : ℕ => XO E k (2 * E + 1) (posO E ψ i (wO ψ i)) 1)] ++
    [[3 * E + 2, XO E k (2 * E) (3 * E + 2) (2 * k)]]

def ownO (E k : ℕ) (ψ : CNF) : List (List ℕ) :=
  (List.range ψ.length).flatMap (fun i : ℕ =>
    (List.range (wO ψ i + 1)).flatMap (fun j : ℕ => blkO E k ψ i j)) ++
    innerO E k (2 * E) (2 * E + 1) false ++ innerO E k (2 * E) (3 * E + 2) false ++
    [(2 * E + 1) :: XO E k (2 * E) (2 * E + 1) (2 * k) ::
      (List.range ψ.length).map (fun i : ℕ => XO E k (2 * E + 1) (posO E ψ i (wO ψ i)) 1)] ++
    [[3 * E + 2, XO E k (2 * E) (3 * E + 2) (2 * k)]]

theorem ownO_eq (E k : ℕ) (ψ : CNF) : ownO E k ψ = (List.range ψ.length).flatMap (fun i : ℕ =>
    (List.range (wO ψ i + 1)).flatMap (fun j : ℕ => blkO E k ψ i j)) ++ tailO E k ψ := by
  simp only [ownO, tailO, List.append_assoc]

end PEqualNP.MetaComplexity.MachineOwn
