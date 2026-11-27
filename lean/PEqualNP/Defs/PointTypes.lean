import PEqualNP.Defs.GenericRejection

/-!
# One-point negatives, semantic frames, point types and their number `t`

A new notion, defined on a SEMANTIC frame (the views are functions, not gates). Every definition here is a definition, not a result: none was
printed, and each is to be read by a second reader for saying what its sentence says
(MINDSET 0i (e)).

Conventions (those of `Defs/GenericRejection.lean`). A plane is data `S : Fin m → Finset (Fin n)`,
`n` points and `m` lines, point `p` ON line `l` iff `p ∈ S l`. An input is a pair `(X, Y)` of a
point set and a line set. A function of the incidence variables is an `IFun n m`, a map
`Finset (Fin n) → Finset (Fin m) → Bool`; a root circuit on the `n + m` inputs (points first)
gives one by `circuitIFun`, through `incidenceInput`.

* `IsFrame C V`: the family `V : Fin g → IFun n m` is a SEMANTIC FRAME of `C`: for every input,
  `C` is true iff every `V j` is true (`C` = AND of the `V j` as functions; no gate structure).
* `IsOnePointNeg S k p T`: the input `({p}, T)` is a ONE-POINT NEGATIVE at `p` of level `k`:
  `T` has at most `k` lines and no line of `T` passes through `p` (`IsFalseInput S {p} T`).
  Nothing else is on: the input is exactly `({p}, T)`.
* `ptype S k V p : Finset (Fin g)`: the TYPE of `p`, the set of `j` such that `V j` is false at
  SOME one-point negative at `p` of level `k`.
* `numTypes S k V : ℕ`: `t`, the number of distinct types over all points (the card of the image
  of `ptype` over `Finset.univ`).

Caveats (comments only).
* `IsFrame` does not ask `C` or any `V j` to be monotone, nor `C` to be the incidence function;
  statements that need either state it. Under `IsFrame`, each `V j ≥ C` pointwise (a lemma).
* `ptype` and `numTypes` do not use `C` at all: they read only `V`, `S` and `k`. A statement
  about a frame of `C` carries `IsFrame C V` beside them.
* The level `k` is free; `k = 0` allows only `T = ∅`. Since `T = ∅` is a one-point negative at
  every level, `C {p} ∅ = false` already makes the type of `p` nonempty for a frame.
* With `n = 0` (no points) `numTypes = 0`.
* The 2.3 text calls the type "the set of views non-constant at p", a SYNTACTIC notion of the
  coated circuit; it then uses only that a view in no type is true at every one-point negative.
  This file takes the SEMANTIC reading the brief names (false at some one-point negative). For
  a view constant at `p` in the 2.3 sense, `V j` is true at every one-point negative at `p`, so
  2.3's type CONTAINS this file's type; they need not be equal.
-/

namespace PEqualNP.PointTypes

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection

variable {n m : ℕ}

/-- A function of the incidence variables: a point set and a line set give a bit. -/
abbrev IFun (n m : ℕ) : Type := Finset (Fin n) → Finset (Fin m) → Bool

/-- The function a root circuit on the `n + m` inputs (points first) computes. -/
def circuitIFun (C : Circuit) : IFun n m := fun X Y => C.eval (incidenceInput X Y)

/-- `V` is a SEMANTIC FRAME of `C`: on every input, `C` is true iff every `V j` is true. -/
def IsFrame {g : ℕ} (C : IFun n m) (V : Fin g → IFun n m) : Prop :=
  ∀ (X : Finset (Fin n)) (Y : Finset (Fin m)), C X Y = true ↔ ∀ j, V j X Y = true

/-- The input `({p}, T)` is a ONE-POINT NEGATIVE at `p` of level `k`: at most `k` lines, none
through `p`. -/
def IsOnePointNeg (S : Fin m → Finset (Fin n)) (k : ℕ) (p : Fin n) (T : Finset (Fin m)) :
    Prop :=
  T.card ≤ k ∧ IsFalseInput S {p} T

instance (S : Fin m → Finset (Fin n)) (k : ℕ) (p : Fin n) (T : Finset (Fin m)) :
    Decidable (IsOnePointNeg S k p T) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The TYPE of `p`: the views false at some one-point negative at `p` of level `k`. -/
def ptype {g : ℕ} (S : Fin m → Finset (Fin n)) (k : ℕ) (V : Fin g → IFun n m) (p : Fin n) :
    Finset (Fin g) :=
  Finset.univ.filter fun j => ∃ T : Finset (Fin m), IsOnePointNeg S k p T ∧ V j {p} T = false

/-- `t`: the number of distinct types over all points. -/
def numTypes {g : ℕ} (S : Fin m → Finset (Fin n)) (k : ℕ) (V : Fin g → IFun n m) : ℕ :=
  (Finset.univ.image (ptype S k V)).card

end PEqualNP.PointTypes
