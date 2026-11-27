import PEqualNP.Defs.PencilGate
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.ENat.Lattice

/-!
# Quadrangles, supports and the heptad cover number of an incidence structure

An incidence structure is given as data, with the conventions of `Defs/PencilGate.lean`: `n`
points `Fin n` and `m` lines, a family `S : Fin m → Finset (Fin n)` of point sets; point `p` is
ON line `l` iff `p ∈ S l`. The VARIABLES are the `n` points and the `m` lines, as the sum type
`Fin n ⊕ Fin m` (points are `Sum.inl p`, lines are `Sum.inr l`). A set of variables is a
`Finset (Fin n ⊕ Fin m)`; a set of point-line pairs is a `Finset (Fin n × Fin m)`.

* `IsQuadrangle S Q`: `Q` is a set of four points, no three on a common line (every line meets
  `Q` in at most two points).
* `quadrangles S`: the finset of all quadrangles.
* `missLines S Q`: the lines meeting `Q` in no point (`M(Q)`).
* `supp S Q`: the SUPPORT of `Q`, the variables `Q ∪ M(Q)` (`H_Q`).
* `incidences S`: the incident pairs `(p, l)`, `p ∈ S l`.
* `PairIn V pl`: both ends of the pair `pl = (p, l)` are in `V`.
* `IsFree R V`: no pair of `R` lies inside `V` (`R` is a set of FORBIDDEN pairs). This is the
  reading of the route file `depth3-order3-split.md`, section 0 ("sets of variables, each
  containing no pair of R"), and the reading under which its tables were computed.
* `IsCompatible S R V`: every INCIDENT pair inside `V` lies in `R` (`R` is a set of ALLOWED
  pairs). By definition this is `IsFree (incidences S \ R) V`.
* `HasCover S R k`: at most `k` `R`-free sets of variables such that every support lies inside
  one of them.
* `kappa S R : ℕ∞`: the HEPTAD COVER NUMBER, the least `k` with `HasCover S R k`, `⊤` if none.
* `singerLines3`: the plane of order 3 as data, line `l` is `{0, 1, 3, 9} + l` mod 13.

Caveats a statement must respect:
* `kappa` is in the FORBIDDEN reading. The route's `kappa(R)` for `R ⊆ INC` is `kappa S R`; the
  "compatible" reading with allowed set `R` is `kappa S (incidences S \ R)`. The two differ:
  at order 3 the least 2-matching has `kappa = 3` in the forbidden reading and `234` in the
  allowed reading (script). Monotone in the forbidden reading: `R ⊆ R'` gives
  `kappa S R ≤ kappa S R'`.
* FINITENESS. `kappa S R < ⊤` iff every support is `R`-free: if so, the set of all supports is a
  cover with `(quadrangles S).card` members; if not, no `R`-free set contains that support. A
  support never contains an incident pair (its lines miss its points), so for `R ⊆ incidences S`
  the number is always finite; it can be `⊤` only when `R` holds a NON-incident pair `(p, l)`
  with `p ∈ Q` and `l ∈ M(Q)` for some quadrangle `Q`.
* If `S` has no quadrangle, every support condition is vacuous and `kappa S R = 0`.
* `S` is arbitrary data: nothing assumes a projective plane. "No three on a line" is read as
  `(Q ∩ S l).card ≤ 2` for every `l`; when `S` has repeated lines this is the same condition.
* A cover is a FINSET of sets, so `HasCover S R k` says AT MOST `k` sets, and is monotone in `k`.
-/

namespace PEqualNP.HeptadCover

variable {n m : ℕ}

/-- `Q` is a QUADRANGLE: four points, no three on a common line. -/
def IsQuadrangle (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) : Prop :=
  Q.card = 4 ∧ ∀ l : Fin m, (Q ∩ S l).card ≤ 2

instance (S : Fin m → Finset (Fin n)) : DecidablePred (IsQuadrangle S) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- All quadrangles of `S`. -/
def quadrangles (S : Fin m → Finset (Fin n)) : Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard 4).filter fun Q => ∀ l : Fin m, (Q ∩ S l).card ≤ 2

/-- `M(Q)`: the lines meeting `Q` in no point. -/
def missLines (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter fun l => Disjoint (S l) Q

/-- The SUPPORT of `Q`: the points of `Q` and the lines of `M(Q)`, as variables. -/
def supp (S : Fin m → Finset (Fin n)) (Q : Finset (Fin n)) : Finset (Fin n ⊕ Fin m) :=
  Q.disjSum (missLines S Q)

/-- The incident pairs `(p, l)` with `p` on `l`. -/
def incidences (S : Fin m → Finset (Fin n)) : Finset (Fin n × Fin m) :=
  Finset.univ.filter fun pl => pl.1 ∈ S pl.2

/-- Both ends of the pair `pl = (p, l)` lie in the set of variables `V`. -/
def PairIn (V : Finset (Fin n ⊕ Fin m)) (pl : Fin n × Fin m) : Prop :=
  Sum.inl pl.1 ∈ V ∧ Sum.inr pl.2 ∈ V

instance (V : Finset (Fin n ⊕ Fin m)) : DecidablePred (PairIn V) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- `V` is `R`-FREE: no pair of `R` (the forbidden pairs) lies inside `V`. -/
def IsFree (R : Finset (Fin n × Fin m)) (V : Finset (Fin n ⊕ Fin m)) : Prop :=
  ∀ pl ∈ R, ¬ PairIn V pl

instance (R : Finset (Fin n × Fin m)) : DecidablePred (IsFree R) :=
  fun _ => inferInstanceAs (Decidable (∀ _ ∈ R, _))

/-- `V` is `R`-COMPATIBLE: every incident pair inside `V` lies in `R` (the allowed pairs). -/
def IsCompatible (S : Fin m → Finset (Fin n)) (R : Finset (Fin n × Fin m))
    (V : Finset (Fin n ⊕ Fin m)) : Prop :=
  IsFree (incidences S \ R) V

instance (S : Fin m → Finset (Fin n)) (R : Finset (Fin n × Fin m)) :
    DecidablePred (IsCompatible S R) :=
  fun V => inferInstanceAs (Decidable (IsFree (incidences S \ R) V))

/-- At most `k` `R`-free sets of variables such that every support lies inside one of them. -/
def HasCover (S : Fin m → Finset (Fin n)) (R : Finset (Fin n × Fin m)) (k : ℕ) : Prop :=
  ∃ F : Finset (Finset (Fin n ⊕ Fin m)), F.card ≤ k ∧ (∀ V ∈ F, IsFree R V) ∧
    ∀ Q ∈ quadrangles S, ∃ V ∈ F, supp S Q ⊆ V

/-- The HEPTAD COVER NUMBER `kappa(R)` (forbidden reading): the least `k` with
`HasCover S R k`, `⊤` if there is none. -/
noncomputable def kappa (S : Fin m → Finset (Fin n)) (R : Finset (Fin n × Fin m)) : ℕ∞ :=
  sInf ((fun k : ℕ => (k : ℕ∞)) '' {k | HasCover S R k})

/-- The plane of order 3 as data: points `Fin 13`, line `l` is `{0, 1, 3, 9} + l` mod 13. -/
def singerLines3 (l : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter fun p : Fin 13 => (p.val + 13 - l.val) % 13 ∈ ({0, 1, 3, 9} : Finset ℕ)

end PEqualNP.HeptadCover
