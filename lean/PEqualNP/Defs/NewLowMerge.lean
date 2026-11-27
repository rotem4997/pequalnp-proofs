import Mathlib.Logic.Relation
import PEqualNP.Defs.LowMerge

/-!
# Classes before a wire and new low merges at a line

The setting is that of `PEqualNP.Defs.LowMerge`: the root circuit model on the edge function of a
bipartite graph, `P` points then `L` lines (point `p` is input `p`, line `w` is input `P + w`),
incidence `inc : Fin P → Fin L → Bool`, wires numbered as in `Circuit.wires`.

Fix a line `w` and a wire index `g`. Take the points as vertices and, for every wire `j < g`
that is LOW for `w`, its ALIVE SET at `w` as a hyperedge. The CLASSES BEFORE `g` at `w` are the
connected components of this hypergraph (a point in no such alive set is alone). The wire `g` is
a NEW LOW MERGE at `w` when `g` is low for `w` and its alive set at `w` meets at least two classes
before `g` (the paper "the merge identity", section "Definitions": a gate low for `w` that joins
two or more classes when it appears, the classes following the order of the wires).

The classes are computed by a LABEL FOLD along the wires, the same labelling as the class labels
of the helper files of the checked inequality row (`lab` in the low-merge proof helpers): start
with label `p.val` on point `p`; at each wire `j`, if `j` is low for `w`, every point whose label
is a label of the alive set of `j` gets the largest such label. Two points are in the same class
before `g` exactly when their labels after the wires below `g` agree.

Names.
* `classStep P L inc C w lab j`: the labels after wire `j`, from the labels `lab` before it.
* `classLabel P L inc C g w : Fin P → ℕ`: the class labels before wire `g` (after wires `0` to
  `g - 1`).
* `SameClass P L inc C g w p q`: `p` and `q` have the same label before `g` (decidable).
* `AliveLinked P L inc C g w p q`: some wire `j < g` low for `w` has both `p` and `q` in its
  alive set at `w`. The connected components of the hypergraph are the classes of
  `Relation.EqvGen (AliveLinked P L inc C g w)`; `SameClass` agrees with that closure (a lemma,
  proved in the scratch file of this module, not built in).
* `classesMet P L inc C g w : Finset ℕ`: the labels of the classes before `g` met by the alive
  set of `g` at `w`.
* `IsNewLowMerge P L inc C g w`: `g` is low for `w` and `classesMet` has at least two elements.
  Decidable (instance below).

Caveats a statement must respect.
* The vertex set is ALL points (`Fin P`), not only the points of `w`. This changes nothing about
  the classes of points of `w`: the alive set of a wire low for `w` lies among the points of `w`
  (a lemma of the root, not built in), so a point off `w` is in no hyperedge and stays alone, and
  the alive set of a low `g` meets only classes of points of `w`.
* Every wire below `g` contributes, inputs included (as in the thinker's text: every wire `j`
  earlier than `g`). A point input on `w` has a one-point alive set and joins nothing; a line
  input other than `y_w` is low with an empty alive set; `y_w` is not low. So counting inputs or
  not gives the same classes.
* `g` itself need not be a gate, an OR gate or of fan-in two: the definition is semantic (low,
  alive set, classes). That an input wire is never a new low merge, and that a new low merge
  which is an OR of two earlier wires is a low merge (`PEqualNP.LowMerge.IsLowMerge`), are
  lemmas, not built in.
* AND/OR-only is NOT built in (`PEqualNP.CircuitLowerBounds.IsMonotoneCircuit` is the
  hypothesis), as for `IsLow`.
* The label values themselves carry no meaning beyond equality; only `SameClass` and the
  number of labels (`classesMet`) are meant to be stated on.
* Wires at or above the end of the circuit read `false`: they are low with an empty alive set,
  never new low merges.
-/

namespace PEqualNP.LowMerge

open PEqualNP.CircuitLowerBounds

/-- One step of the label fold: the labels after wire `j` from the labels `lab` before it. If
`j` is low for `w`, every point whose label is a label of the alive set of `j` at `w` gets the
largest label of that alive set; otherwise nothing changes. -/
def classStep (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (w : Fin L)
    (lab : Fin P → ℕ) (j : ℕ) : Fin P → ℕ :=
  fun p =>
    if IsLow P L inc C j w ∧ lab p ∈ (aliveSet P L C j w).image lab then
      ((aliveSet P L C j w).image lab).sup id
    else lab p

/-- The class labels before wire `g` at line `w`: the fold of `classStep` along the wires
`0, 1, ..., g - 1`, starting from label `p.val` on point `p`. -/
def classLabel (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ) (w : Fin L) :
    Fin P → ℕ :=
  (List.range g).foldl (classStep P L inc C w) (fun p => p.val)

/-- `p` and `q` are in the same class before wire `g` at line `w`. -/
def SameClass (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ) (w : Fin L)
    (p q : Fin P) : Prop :=
  classLabel P L inc C g w p = classLabel P L inc C g w q

/-- The hyperedge relation before `g`: some wire `j < g` low for `w` has both `p` and `q` in its
alive set at `w`. Its equivalence closure has the classes before `g` as its classes. -/
def AliveLinked (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ) (w : Fin L)
    (p q : Fin P) : Prop :=
  ∃ j < g, IsLow P L inc C j w ∧ p ∈ aliveSet P L C j w ∧ q ∈ aliveSet P L C j w

/-- The labels of the classes before `g` that the alive set of `g` at `w` meets. -/
def classesMet (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ) (w : Fin L) :
    Finset ℕ :=
  (aliveSet P L C g w).image (classLabel P L inc C g w)

/-- NEW LOW MERGE: wire `g` is low for line `w` and its alive set at `w` meets at least two
classes before `g`. -/
def IsNewLowMerge (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ) (w : Fin L) :
    Prop :=
  IsLow P L inc C g w ∧ 2 ≤ (classesMet P L inc C g w).card

instance (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ) (w : Fin L)
    (p q : Fin P) : Decidable (SameClass P L inc C g w p q) := by
  unfold SameClass; infer_instance

instance (P L : ℕ) (inc : Fin P → Fin L → Bool) (C : Circuit) (g : ℕ) (w : Fin L) :
    Decidable (IsNewLowMerge P L inc C g w) := by
  unfold IsNewLowMerge; infer_instance

end PEqualNP.LowMerge
