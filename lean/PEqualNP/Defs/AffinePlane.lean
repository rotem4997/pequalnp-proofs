import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# The affine plane over a finite field, as a set system

For a finite field `F` with `q = Fintype.card F` elements, the affine plane `F × F` has
`q ^ 2` points and `q ^ 2 + q` lines:

* the non-vertical line of slope `a` and intercept `b`, the points `(x, a * x + b)`
  (`q ^ 2` lines, one per pair `(a, b)`);
* the vertical line at `c`, the points `(c, y)` (`q` lines, one per `c`).

The points at infinity (the projective completion) are left out. Each line has `q` points and
two distinct lines share at most one point.

This module encodes the lines as a family `Fin (q ^ 2 + q) → Finset (Fin (q ^ 2))`, the shape of
the set systems in the rows on Boolean sums (`S : Fin m → Finset (Fin n)`), so a statement on
such a family applies to the plane with no conversion.

Names:
* `AffinePlane.Line F`: the type `(F × F) ⊕ F` of lines; `Sum.inl (a, b)` is the line
  `y = a * x + b`, `Sum.inr c` is the line `x = c`.
* `AffinePlane.lineSet F l`: the points of the line `l`, a `Finset (F × F)`.
* `AffinePlane.pointEquiv F : F × F ≃ Fin (Fintype.card F ^ 2)`: the fixed point encoding.
* `AffinePlane.lineEquiv F : Line F ≃ Fin (Fintype.card F ^ 2 + Fintype.card F)`: the fixed
  line encoding.
* `AffinePlane.affineLines F : Fin (Fintype.card F ^ 2 + Fintype.card F) →
  Finset (Fin (Fintype.card F ^ 2))`: the family of lines, through the two encodings.

Conventions of the encodings (noncomputable):
* `e = Fintype.equivFin F : F ≃ Fin q`, a fixed but unspecified enumeration of `F`.
* The point `(x, y)` is the index `e y + q * e x` (Mathlib's `finProdFinEquiv` on `(e x, e y)`,
  then the cast `q * q = q ^ 2`).
* The non-vertical line `(a, b)` has index `pointEquiv F (a, b)`, below `q ^ 2`; the vertical
  line `c` has index `q ^ 2 + e c` (Mathlib's `finSumFinEquiv`).

Caveats a statement must respect:
* The enumeration `e` is not computable, so `decide` does not see through `affineLines`, even
  for `ZMod 2`; concrete facts come from the general theorems.
* A statement should only use properties that do not depend on the choice of `e` (sizes,
  intersections, incidences), since `e` is fixed but unspecified.
* The number of points is written `Fintype.card F ^ 2`, the number of lines
  `Fintype.card F ^ 2 + Fintype.card F`; the field is a parameter, `q` is never a free number.
* No points at infinity: the projective plane of order `q` has `q ^ 2 + q + 1` points and
  lines, this family has `q ^ 2` points and `q ^ 2 + q` lines.
-/

namespace PEqualNP.AffinePlane

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- The lines of the affine plane over `F`: `Sum.inl (a, b)` is the line `y = a * x + b`,
`Sum.inr c` is the vertical line `x = c`. -/
abbrev Line : Type _ := (F × F) ⊕ F

/-- The points of a non-vertical line `y = a * x + b`. -/
def slopeLine (ab : F × F) : Finset (F × F) :=
  Finset.univ.filter (fun p => p.2 = ab.1 * p.1 + ab.2)

/-- The points of a vertical line `x = c`. -/
def verticalLine (c : F) : Finset (F × F) :=
  Finset.univ.filter (fun p => p.1 = c)

/-- The points of the line `l`. -/
def lineSet (l : Line F) : Finset (F × F) :=
  Sum.elim (slopeLine F) (verticalLine F) l

/-- The fixed encoding of the points: `(x, y)` goes to `e y + q * e x` with
`e = Fintype.equivFin F` and `q = Fintype.card F`. -/
noncomputable def pointEquiv : F × F ≃ Fin (Fintype.card F ^ 2) :=
  ((Equiv.prodCongr (Fintype.equivFin F) (Fintype.equivFin F)).trans finProdFinEquiv).trans
    (finCongr (sq (Fintype.card F)).symm)

/-- The fixed encoding of the lines: the line `(a, b)` goes to `pointEquiv F (a, b)`, the
vertical line `c` goes to `q ^ 2 + e c`. -/
noncomputable def lineEquiv : Line F ≃ Fin (Fintype.card F ^ 2 + Fintype.card F) :=
  (Equiv.sumCongr (pointEquiv F) (Fintype.equivFin F)).trans finSumFinEquiv

/-- The affine lines of `F × F` as a set system on `Fintype.card F ^ 2` points:
line number `i` is the set of the codes of its points. -/
noncomputable def affineLines :
    Fin (Fintype.card F ^ 2 + Fintype.card F) → Finset (Fin (Fintype.card F ^ 2)) :=
  fun i => (lineSet F ((lineEquiv F).symm i)).map (pointEquiv F).toEmbedding

end PEqualNP.AffinePlane
