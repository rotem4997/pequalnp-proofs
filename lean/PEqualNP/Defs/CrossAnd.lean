import PEqualNP.Defs.SyntacticMultilinear
import PEqualNP.Defs.EdgeOwnership
import PEqualNP.Defs.MetaComplexity

/-!
# Cross AND gates and the cross-AND profile of an edge function

A circuit of the root model on the inputs `Fin n`, a marked side `M : Finset (Fin n)` of the
inputs (for an incidence structure, the line inputs). The SUPPORT of a wire is the set of inputs it
can be reached from (`PEqualNP.SyntacticMultilinear.support`; a read of a wire at or past the
gate's own wire reads `false` and has empty support, `operandSupport`).

* `IsCrossAnd n M C j`: gate `j` is an AND gate reading exactly two wires `a, b`, and the supports
  of `a` and `b` (as read by gate `j`) EITHER both meet `M` OR both meet the complement of `M`.
  So an AND whose two sides are "pure" (one side's support inside `M`, the other's inside the
  complement) is NOT a cross AND; an AND with a side reaching nothing is not one either.
* `crossCount n M C`: the number of cross AND gates of `C`.
* `CrossProfileLE n K M s k`: some AND/OR circuit of fan-in at most two computing the edge function
  of the graph `K` (`graphFun K ∅`) has at most `s` gates and at most `k` cross AND gates. The
  profile `k_K(s)` is the least such `k`.

Caveats a statement must respect.
* `IsCrossAnd` looks only at AND gates of fan-in exactly two; an AND of another fan-in is never a
  cross AND. `CrossProfileLE` asks for `FanInTwo` (at most two) and `AndOrOnly`, and counts every
  gate in `s`, unused ones included.
* Supports are syntactic: an input reached through the wiring counts even if the gate's function
  does not depend on it.
* The marked side is a parameter: for the incidence function of a plane, `M` is the line inputs.
-/

namespace PEqualNP.CrossAnd

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.SyntacticMultilinear

attribute [local instance] gateOpDecEq

/-- Gate `j` is a CROSS AND for the marked side `M`: an AND gate reading exactly two wires whose
supports, as read by the gate, both meet `M` or both meet the complement of `M`. -/
def IsCrossAnd (n : ℕ) (M : Finset (Fin n)) (C : Circuit) (j : ℕ) : Prop :=
  (gateAt C j).op = GateOp.and ∧ (gateAt C j).inputs.length = 2 ∧
    (((operandSupport n C j ((gateAt C j).inputs.getD 0 0) ∩ M).Nonempty ∧
        (operandSupport n C j ((gateAt C j).inputs.getD 1 0) ∩ M).Nonempty) ∨
      ((operandSupport n C j ((gateAt C j).inputs.getD 0 0) \ M).Nonempty ∧
        (operandSupport n C j ((gateAt C j).inputs.getD 1 0) \ M).Nonempty))

instance (n : ℕ) (M : Finset (Fin n)) (C : Circuit) (j : ℕ) : Decidable (IsCrossAnd n M C j) := by
  unfold IsCrossAnd; infer_instance

/-- The number of cross AND gates of `C`. -/
def crossCount (n : ℕ) (M : Finset (Fin n)) (C : Circuit) : ℕ :=
  ((Finset.range C.gates.length).filter (fun j => IsCrossAnd n M C j)).card

/-- The cross-AND profile as a predicate: the edge function of `K` has an AND/OR circuit of
fan-in at most two with at most `s` gates and at most `k` cross AND gates. -/
def CrossProfileLE (n : ℕ) (K : SimpleGraph (Fin n)) [DecidableRel K.Adj] (M : Finset (Fin n))
    (s k : ℕ) : Prop :=
  ∃ C : Circuit, PEqualNP.EdgeOwnership.AndOrOnly C ∧ PEqualNP.MetaComplexity.FanInTwo C ∧
    (∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun K ∅ x) ∧
    C.gates.length ≤ s ∧ crossCount n M C ≤ k

end PEqualNP.CrossAnd
