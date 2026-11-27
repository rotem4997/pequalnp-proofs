import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.Lift

/-!
# L-meta-2604: the implicant lift

In a circuit, an OR gate `j` reading `[u, t]`, where wire `t` implies the output, may drop its
input `t` if a new last gate ORs the old output with `t`: the function is unchanged. Proof: the
two wire lists agree below gate `j`; if `t` reads `false` gate `j` has the same value in both
and so does everything after it, and the new gate ORs in `false`; if `t` reads `true` both
sides are `true` (the new gate by its input `t`, the old circuit by the hypothesis).
-/

namespace PEqualNP.MetaComplexity

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.Lift

theorem L2604 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (j u t : ℕ),
  PEqualNP.MetaComplexity.Monotone2 C →
  j < C.gates.length →
  C.gates[j]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u, t] } →
  t < n + j →
  (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD t false = true →
      PEqualNP.MetaComplexity.circuitFun n C x = true) →
  PEqualNP.MetaComplexity.circuitFun n
    { gates := C.gates.set j { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u] } ++
        [{ op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [C.output, t] }],
      output := n + C.gates.length } =
  PEqualNP.MetaComplexity.circuitFun n C := by
  intro n C j u t _ hj hg ht himp
  funext x
  have hgj : C.gates[j] = { op := GateOp.or, inputs := [u, t] } := by
    rw [List.getElem?_eq_some_iff] at hg
    exact hg.2
  have hsplit : C.gates = C.gates.take j ++
      ({ op := GateOp.or, inputs := [u, t] } : Gate) :: C.gates.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.drop_eq_getElem_cons hj, hgj]
  have hset : C.gates.set j ({ op := GateOp.or, inputs := [u] } : Gate) = C.gates.take j ++
      ({ op := GateOp.or, inputs := [u] } : Gate) :: C.gates.drop (j + 1) := by
    rw [List.set_eq_take_append_cons_drop, if_pos hj]
  have himpx := himp x
  unfold circuitFun Circuit.eval at himpx ⊢
  simp only [wires_eq] at himpx ⊢
  -- names
  set A := C.gates.take j with hA
  set B := C.gates.drop (j + 1) with hB
  set w0 := List.ofFn x with hw0
  set wA := A.foldl step w0 with hwA
  have hlenA : wA.length = n + j := by
    rw [hwA, foldl_step_length, hw0, List.length_ofFn, hA, List.length_take]
    omega
  have htA : t < wA.length := by omega
  -- the old wire list
  have hW : C.gates.foldl step w0 =
      B.foldl step (step wA { op := GateOp.or, inputs := [u, t] }) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  -- the new wire list before the last gate
  set W' := (A ++ ({ op := GateOp.or, inputs := [u] } : Gate) :: B).foldl step w0 with hW'
  have hW'eq : W' = B.foldl step (step wA { op := GateOp.or, inputs := [u] }) := by
    rw [hW', List.foldl_append, List.foldl_cons]
  have hlenW' : W'.length = n + C.gates.length := by
    have : (A ++ ({ op := GateOp.or, inputs := [u] } : Gate) :: B).length = C.gates.length := by
      conv_rhs => rw [hsplit]
      simp
    rw [hW', foldl_step_length, this, hw0, List.length_ofFn]
  have hW't : W'.getD t false = wA.getD t false := by
    rw [hW'eq, foldl_step_getD _ _ t (by simp [step]; omega)]
    exact getD_append_left _ _ t htA
  have hWt : (C.gates.foldl step w0).getD t false = wA.getD t false := by
    rw [hW, foldl_step_getD _ _ t (by simp [step]; omega)]
    exact getD_append_left _ _ t htA
  -- the new circuit's value
  have hLHS : ((C.gates.set j ({ op := GateOp.or, inputs := [u] } : Gate) ++
      [({ op := GateOp.or, inputs := [C.output, t] } : Gate)]).foldl step w0).getD
        (n + C.gates.length) false = (W'.getD C.output false || W'.getD t false) := by
    rw [hset, List.foldl_append, ← hW']
    simp only [List.foldl_cons, List.foldl_nil]
    rw [← hlenW']
    unfold step
    rw [getD_append_singleton_last]
    simp [GateOp.eval]
  rw [hLHS, hW't]
  cases hval : wA.getD t false with
  | true =>
    rw [← hWt] at hval
    rw [himpx hval]
    simp
  | false =>
    have hstep : step wA ({ op := GateOp.or, inputs := [u] } : Gate) =
        step wA { op := GateOp.or, inputs := [u, t] } := by
      unfold step
      rw [List.getD_eq_getElem?_getD] at hval
      simp [GateOp.eval, hval]
    rw [hW'eq, hstep, ← hW]
    simp

end PEqualNP.MetaComplexity
