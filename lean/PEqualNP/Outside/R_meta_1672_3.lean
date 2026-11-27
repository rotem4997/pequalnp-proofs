import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Restrict input four when it has three effective readers. Otherwise only
-- the sparse-reader search remains. The restriction is the checked minor.
-- Of the permitted operations, only NOT is false on two true operands.
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_1672_3 :
  (let readers := fun C : Circuit => C.gates.countP fun g =>
      (g.inputs.head? == some 4) || (g.op.eval [true, true] && g.inputs.contains 4)
    ∀ C : Circuit, FanInTwo C → 3 ≤ readers C →
      (∃ x : Fin 8 → Bool, circuitFun 9 C (Fin.insertNth (4 : Fin 9) false x) = false) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + 3 ≤ C.size ∧
        circuitFun 8 D = (fun x => circuitFun 9 C (Fin.insertNth (4 : Fin 9) false x))) →
  (let readers := fun C : Circuit => C.gates.countP fun g =>
      (g.inputs.head? == some 4) || (g.op.eval [true, true] && g.inputs.contains 4)
    ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y 6)) →
      circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      readers C ≤ 2 → 16 ≤ C.size) →
  (¬ PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12) →
  ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y 6)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro eliminate sparse minor C fan firstGate correct
  let readers := fun C : Circuit => C.gates.countP fun g =>
    (g.inputs.head? == some 4) || (g.op.eval [true, true] && g.inputs.contains 4)
  change (∀ C : Circuit, FanInTwo C → 3 ≤ readers C →
      (∃ x : Fin 8 → Bool, circuitFun 9 C (Fin.insertNth (4 : Fin 9) false x) = false) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + 3 ≤ C.size ∧
        circuitFun 8 D = (fun x => circuitFun 9 C (Fin.insertNth (4 : Fin 9) false x))) at eliminate
  change (∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y 6)) →
      circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      readers C ≤ 2 → 16 ≤ C.size) at sparse
  have restriction (x : Fin 8 → Bool) :
      circuitFun 9 C (Fin.insertNth (4 : Fin 9) false x) = (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) x := by
    let ins : Fin 9 → Bool := Fin.insertNth (4 : Fin 9) false x
    have hi (j : Fin 8) : ins ((4 : Fin 9).succAbove j) = x j :=
      Fin.insertNth_apply_succAbove (α := fun _ : Fin 9 => Bool) (4 : Fin 9) false x j
    have h0 : ins 0 = x 0 := hi 0
    have h1 : ins 1 = x 1 := hi 1
    have h2 : ins 2 = x 2 := hi 2
    have h3 : ins 3 = x 3 := hi 3
    have h4 : ins 4 = false :=
      Fin.insertNth_apply_same (α := fun _ : Fin 9 => Bool) (4 : Fin 9) false x
    have h5 : ins 5 = x 4 := hi 4
    have h6 : ins 6 = x 5 := hi 5
    have h7 : ins 7 = x 6 := hi 6
    have h8 : ins 8 = x 7 := hi 7
    calc
      _ = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) ins := congrFun correct ins
      _ = _ := by
        simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8,
          Bool.false_and, Bool.and_false, Bool.or_false]
  by_cases many : 3 ≤ readers C
  · by_contra tooSmall
    have notTrue : circuitFun 9 C (Fin.insertNth (4 : Fin 9) false (fun _ => false)) = false :=
      restriction (fun _ => false)
    obtain ⟨D, fanD, saving, evalD⟩ := eliminate C fan many ⟨_, notTrue⟩
    apply minor
    refine ⟨D, fanD, by omega, ?_⟩
    intro x
    exact (congrFun evalD x).trans (restriction x)
  · exact sparse C fan firstGate correct (by omega)
