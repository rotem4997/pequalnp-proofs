import PEqualNP.Defs.HeptadCover
import Mathlib.Data.Rat.Defs

/-!
# Generic maximal false inputs and the generic rejection rate `rho` of a circuit

A plane (projective or not) is given as data, with the conventions of `Defs/PencilGate.lean`:
`n` points `Fin n` and `m` lines, a family `S : Fin m → Finset (Fin n)`; point `p` is ON line
`l` iff `p ∈ S l`. The INCIDENCE FUNCTION has `n + m` variables, POINTS FIRST (as in
`Defs/LowMerge.lean`): point `p` is input `p`, line `l` is input `n + l`. An input is a pair
`(X, Y)` of a point set and a line set, encoded as the list `incidenceInput X Y` of `n + m`
bits; `F(X, Y)` is true iff some point of `X` lies on some line of `Y`. A circuit is a root
circuit (`PEqualNP.CircuitLowerBounds.Circuit`) on these `n + m` inputs.

* A FALSE INPUT: no point of `X` lies on a line of `Y`, i.e. every line of `Y` misses `X`.
* MAXIMAL FALSE: false, and adding any one point outside `X`, or any one line outside `Y`, makes
  it true. (Equivalently, a lemma not built in: `Y` is the set of lines missing `X` and `X` is
  the set of points on no line of `Y`.)
* GENERIC (the reading of the concept file, "both sides at least q"): `|X| ≥ q`, `|Y| ≥ q`, `X`
  lies in no line (no line contains every point of `X`), `Y` lies in no pencil (no point lies on
  every line of `Y`).
* NARROW GENERIC (the second reading, of the threshold leg): generic, and `|X|` and `|Y|` both in
  `{q + 1, q + 2}`.
* `rho S q C`: the fraction of generic maximal false inputs at which `C` outputs `false`, in `ℚ`.
  `rhoNarrow S q C` is the same over the narrow set.

Names.
* `incidenceInput X Y : List Bool`: the input with exactly the points of `X` and lines of `Y` on.
* `incidenceFun S X Y : Bool`: the incidence function.
* `IsFalseInput S X Y`, `IsMaximalFalse S X Y`, `InNoLine S X`, `InNoPencil S Y`,
  `IsGeneric S q X Y`, `IsGenericNarrow S q X Y`: the predicates above, all decidable.
* `zeroSet S Y`: the points on no line of `Y` (`missLines S X` of `Defs/HeptadCover.lean` is
  the dual: the lines missing `X`).
* `genericInputs S q`, `narrowInputs S q : Finset (Finset (Fin n) × Finset (Fin m))`: the
  generic, resp. narrow generic, maximal false inputs.
* `rejectionRate C G : ℚ`: the fraction of the inputs in `G` at which `C` outputs `false`.
* `rho S q C := rejectionRate C (genericInputs S q)`, `rhoNarrow S q C` likewise.
* `RightOnIncidentPairs S C`: `C` outputs `true` on every input with exactly one point and one
  line on, the point on the line.
* `ComputesIncidence S C`: `C` computes the incidence function on every input.

Caveats a statement must respect.
* EMPTY SET CONVENTION: when there is no generic input, `rho = 0 / 0 = 0` (division in `ℚ`).
  This is a junk value: then every circuit, correct or not, has `rho = 0`. At order 2 (Fano)
  the generic set is EMPTY (script, all `2^7` point sets): a triangle meets all seven lines.
  At order 3 it has 468 members, the 234 triangles with their 4 missing lines and the 234
  quadrangles with their 3 missing lines (script; the sanity file states it). The narrow set is
  EMPTY at order 3 (the shapes are (3,4) and (4,3), not in `{4, 5}`) and, by the threshold
  leg's census, at every order `q ≥ 8`. A statement "rho = 1" or "rho > 0" must assume the set
  is nonempty, or it is false for the trivial reason.
* `q` is a free parameter: nothing ties it to the plane `S`. For `PG(2, q)` pass its order.
  `S` is arbitrary data; nothing here assumes a projective plane.
* The notion is for MONOTONE circuits right on the incident pairs (`IsMonotoneCircuit`,
  `RightOnIncidentPairs`); neither is built into `rho`, which evaluates any circuit. A circuit
  that computes the incidence function has `rho = 1` when the set is nonempty (a lemma).
* `rho` reads the circuit only on the generic maximal false inputs (`Circuit.eval` on
  `incidenceInput`); it says nothing about other inputs. "OR of all lines" is right on the
  incident pairs and has `rho = 0`.
* `genericInputs` is defined as a filter over ALL pairs `(X, Y)` (`2^(n+m)` of them); a
  computation should go through the lemma that it is the image of the closed generic point sets
  `X ↦ (X, missLines S X)`.
* The empty line set lies in a pencil whenever `n ≥ 1` (every point is on all of its lines), and
  the empty point set lies in a line whenever `m ≥ 1`.
-/

namespace PEqualNP.GenericRejection

open PEqualNP.CircuitLowerBounds PEqualNP.HeptadCover

variable {n m : ℕ}

/-- The input with exactly the points of `X` and the lines of `Y` on, points first: bit `p` is
`p ∈ X`, bit `n + l` is `l ∈ Y`. -/
def incidenceInput (X : Finset (Fin n)) (Y : Finset (Fin m)) : List Bool :=
  List.ofFn (fun p : Fin n => decide (p ∈ X)) ++ List.ofFn (fun l : Fin m => decide (l ∈ Y))

/-- The incidence function: true iff some point of `X` lies on some line of `Y`. -/
def incidenceFun (S : Fin m → Finset (Fin n)) (X : Finset (Fin n)) (Y : Finset (Fin m)) :
    Bool :=
  decide (∃ p ∈ X, ∃ l ∈ Y, p ∈ S l)

/-- A FALSE INPUT: every line of `Y` misses `X`. -/
def IsFalseInput (S : Fin m → Finset (Fin n)) (X : Finset (Fin n)) (Y : Finset (Fin m)) :
    Prop :=
  ∀ l ∈ Y, Disjoint (S l) X

instance (S : Fin m → Finset (Fin n)) (X : Finset (Fin n)) (Y : Finset (Fin m)) :
    Decidable (IsFalseInput S X Y) :=
  inferInstanceAs (Decidable (∀ l ∈ Y, _))

/-- MAXIMAL FALSE: false, and adding any point outside `X`, or any line outside `Y`, breaks
falseness. -/
def IsMaximalFalse (S : Fin m → Finset (Fin n)) (X : Finset (Fin n)) (Y : Finset (Fin m)) :
    Prop :=
  IsFalseInput S X Y ∧ (∀ p : Fin n, p ∉ X → ¬ IsFalseInput S (insert p X) Y) ∧
    ∀ l : Fin m, l ∉ Y → ¬ IsFalseInput S X (insert l Y)

instance (S : Fin m → Finset (Fin n)) (X : Finset (Fin n)) (Y : Finset (Fin m)) :
    Decidable (IsMaximalFalse S X Y) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- `X` lies in NO LINE: no line contains every point of `X`. -/
def InNoLine (S : Fin m → Finset (Fin n)) (X : Finset (Fin n)) : Prop :=
  ∀ l : Fin m, ¬ X ⊆ S l

instance (S : Fin m → Finset (Fin n)) (X : Finset (Fin n)) : Decidable (InNoLine S X) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- `Y` lies in NO PENCIL: no point lies on every line of `Y`. -/
def InNoPencil (S : Fin m → Finset (Fin n)) (Y : Finset (Fin m)) : Prop :=
  ∀ p : Fin n, ¬ ∀ l ∈ Y, p ∈ S l

instance (S : Fin m → Finset (Fin n)) (Y : Finset (Fin m)) : Decidable (InNoPencil S Y) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- GENERIC (both sides at least `q`): `|X| ≥ q`, `|Y| ≥ q`, `X` in no line, `Y` in no
pencil. -/
def IsGeneric (S : Fin m → Finset (Fin n)) (q : ℕ) (X : Finset (Fin n)) (Y : Finset (Fin m)) :
    Prop :=
  q ≤ X.card ∧ q ≤ Y.card ∧ InNoLine S X ∧ InNoPencil S Y

instance (S : Fin m → Finset (Fin n)) (q : ℕ) (X : Finset (Fin n)) (Y : Finset (Fin m)) :
    Decidable (IsGeneric S q X Y) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- NARROW GENERIC: generic, and both sizes in `{q + 1, q + 2}`. -/
def IsGenericNarrow (S : Fin m → Finset (Fin n)) (q : ℕ) (X : Finset (Fin n))
    (Y : Finset (Fin m)) : Prop :=
  IsGeneric S q X Y ∧ X.card ∈ ({q + 1, q + 2} : Finset ℕ) ∧ Y.card ∈ ({q + 1, q + 2} : Finset ℕ)

instance (S : Fin m → Finset (Fin n)) (q : ℕ) (X : Finset (Fin n)) (Y : Finset (Fin m)) :
    Decidable (IsGenericNarrow S q X Y) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The points on no line of `Y`. -/
def zeroSet (S : Fin m → Finset (Fin n)) (Y : Finset (Fin m)) : Finset (Fin n) :=
  Finset.univ.filter fun p => ∀ l ∈ Y, p ∉ S l

/-- The generic maximal false inputs. -/
def genericInputs (S : Fin m → Finset (Fin n)) (q : ℕ) :
    Finset (Finset (Fin n) × Finset (Fin m)) :=
  Finset.univ.filter fun XY => IsMaximalFalse S XY.1 XY.2 ∧ IsGeneric S q XY.1 XY.2

/-- The narrow generic maximal false inputs. -/
def narrowInputs (S : Fin m → Finset (Fin n)) (q : ℕ) :
    Finset (Finset (Fin n) × Finset (Fin m)) :=
  Finset.univ.filter fun XY => IsMaximalFalse S XY.1 XY.2 ∧ IsGenericNarrow S q XY.1 XY.2

/-- The fraction of the inputs of `G` at which `C` outputs `false` (`0` when `G` is empty). -/
def rejectionRate (C : Circuit) (G : Finset (Finset (Fin n) × Finset (Fin m))) : ℚ :=
  ((G.filter fun XY => C.eval (incidenceInput XY.1 XY.2) = false).card : ℚ) / G.card

/-- The GENERIC REJECTION RATE: the fraction of generic maximal false inputs at which `C`
outputs `false` (`0` when there is none). -/
def rho (S : Fin m → Finset (Fin n)) (q : ℕ) (C : Circuit) : ℚ :=
  rejectionRate C (genericInputs S q)

/-- The same over the narrow generic set. -/
def rhoNarrow (S : Fin m → Finset (Fin n)) (q : ℕ) (C : Circuit) : ℚ :=
  rejectionRate C (narrowInputs S q)

/-- `C` is RIGHT ON THE INCIDENT PAIRS: true on the input with only point `p` and line `l` on,
whenever `p` is on `l`. -/
def RightOnIncidentPairs (S : Fin m → Finset (Fin n)) (C : Circuit) : Prop :=
  ∀ l : Fin m, ∀ p ∈ S l, C.eval (incidenceInput {p} {l}) = true

/-- `C` computes the incidence function on every input. -/
def ComputesIncidence (S : Fin m → Finset (Fin n)) (C : Circuit) : Prop :=
  ∀ (X : Finset (Fin n)) (Y : Finset (Fin m)), C.eval (incidenceInput X Y) = incidenceFun S X Y

/-! ## The star circuit and the OR of all lines -/

/-- The STAR circuit: for each point `p` an OR gate over the lines through `p` (wire
`n + m + p`), then an AND gate of point `p` with it (wire `n + m + n + p`), then the OR of
those `n` AND gates (wire `n + m + n + n`, the output). -/
def starGates (S : Fin m → Finset (Fin n)) : List Gate :=
  List.ofFn (fun p : Fin n => (⟨GateOp.or, ((List.finRange m).filter
      (fun l => decide (p ∈ S l))).map (fun l => n + l.val)⟩ : Gate)) ++
    (List.ofFn (fun p : Fin n => (⟨GateOp.and, [p.val, n + m + p.val]⟩ : Gate)) ++
      [⟨GateOp.or, List.ofFn (fun p : Fin n => n + m + n + p.val)⟩])

def star (S : Fin m → Finset (Fin n)) : Circuit :=
  ⟨starGates S, n + m + n + n⟩

/-- The OR of all line inputs. -/
def orLines (n m : ℕ) : Circuit :=
  ⟨[⟨GateOp.or, List.ofFn (fun l : Fin m => n + l.val)⟩], n + m⟩

end PEqualNP.GenericRejection
