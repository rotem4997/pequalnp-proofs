import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CircuitMoves PEqualNP.EdgeOwnership

-- A replacement wire can be any earlier wire, including one unrelated to the gate.
-- When it is an operand, the failed test has a prescribed sign.
set_option maxHeartbeats 1800000 in
theorem PEqualNP.Outside.R_meta_2247_631
  (rewire : ∀ n (C : Circuit), Monotone2 C → ReadsBack n C →
    ∀ j < C.size, ∀ a < n + j, let D := eraseGate n C j a
    Monotone2 D ∧ ReadsBack n D ∧ D.size < C.size ∧
    ∀ x : List Bool, x.length = n → a ∈ (gateAt C j).inputs →
      D.eval x ≠ C.eval x → C.eval x = !((gateAt C j).op.eval []))
  (critical :
    let d : Finset (Fin 13) := {0,1,3,9}
    let rows := fun (sign : Bool) (x : List Bool) => if sign then
      ∃ i l : Fin 13, i-l ∈ d ∧ x = (List.ofFn (fun a : Fin 13 => decide (a=i))) ++ List.ofFn (fun a : Fin 13 => decide (a=l))
      else ∃ Q : Finset (Fin 13), Q.card=4 ∧ (∀ l : Fin 13, (Q.filter (fun i => i-l ∈ d)).card ≤ 2) ∧
        x = (List.ofFn (fun a : Fin 13 => decide (a∈Q))) ++ List.ofFn (fun l : Fin 13 => decide (∀ i∈Q, i-l ∉ d))
    let valid := fun C : PEqualNP.CircuitLowerBounds.Circuit => PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C ∧
      ∀ s x, rows s x → C.eval x=s
    let smaller := fun C : PEqualNP.CircuitLowerBounds.Circuit => ∃ D, valid D ∧ D.size < C.size
    ∀ C, valid C → C.size < 64 →
      (∃ i j, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ InCone 26 C i j) →
      (∀ j < C.size, ∀ a < 26+j, ∃ s w, rows s w ∧ (eraseGate 26 C j a).eval w ≠ s ∧
        (a ∈ (gateAt C j).inputs → s = !((gateAt C j).op.eval []))) → smaller C) :
    have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : Bool → List Bool → Prop := fun (x2 : Bool) (x3 : List Bool) => if x2 = Bool.true then ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 = (List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x5) else ∃ (x4 : Finset (Fin (13 : ℕ))), x4.card = (4 : ℕ) ∧ (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) ∧ x3 = (List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (x5 ∈ x4)) ++ List.ofFn fun (x5 : Fin (13 : ℕ)) => Decidable.decide (∀ x6 ∈ x4, x6 - x5 ∉ x1); have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x3 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 ∧ ∀ (x4 : Bool) (x5 : List Bool), x2 x4 x5 → x3.eval x5 = x4; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x3 x5 ∧ x5.size < x4.size; have x5 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x5 : PEqualNP.CircuitLowerBounds.Circuit) =>   ∀ x6 < x5.gates.length,     have x8 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x5 x6;     have x9 : Bool := !x8.op.eval [];     ∀ x10 ∈ x8.inputs, ∃ (x12 : List Bool), x2 x9 x12 ∧ (x5.wires x12).getD x10 Bool.false = !x9 ∧ (x5.wires x12).getD ((26 : ℕ) + x6) Bool.false = x9; ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x3 x6 → x5 x6 → x6.size < (64 : ℕ) → (∃ (x10 : ℕ) (x11 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x11).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x6 x10 x11) → x4 x6 := by
  let d : Finset (Fin 13) := {0,1,3,9}
  let rows := fun (sign : Bool) (x : List Bool) => if sign then
    ∃ i l : Fin 13, i-l ∈ d ∧ x = (List.ofFn (fun a : Fin 13 => decide (a=i))) ++ List.ofFn (fun a : Fin 13 => decide (a=l))
    else ∃ Q : Finset (Fin 13), Q.card=4 ∧ (∀ l : Fin 13, (Q.filter (fun i => i-l ∈ d)).card ≤ 2) ∧
      x = (List.ofFn (fun a : Fin 13 => decide (a∈Q))) ++ List.ofFn (fun l : Fin 13 => decide (∀ i∈Q, i-l ∉ d))
  let valid := fun C : PEqualNP.CircuitLowerBounds.Circuit => PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 26 C ∧
    ∀ s x, rows s x → C.eval x=s
  let smaller := fun C : PEqualNP.CircuitLowerBounds.Circuit => ∃ D, valid D ∧ D.size < C.size
  let essential := fun C : PEqualNP.CircuitLowerBounds.Circuit => ∀ j < C.gates.length,
    let g := PEqualNP.MetaComplexity.NestedCover.gateAt C j
    let s := !(g.op.eval [])
    ∀ a∈g.inputs, ∃ x, rows s x ∧ (C.wires x).getD a false = !s ∧ (C.wires x).getD (26+j) false = s

  change ∀ C, valid C → essential C → C.size < 64 →
    (∃ i j, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧ InCone 26 C i j) → smaller C
  intro C validC _ budget nested
  classical
  by_contra noSmaller
  apply noSmaller
  apply critical C validC budget nested
  intro j hj a ha
  obtain ⟨mono,back,fit⟩ := validC
  obtain ⟨monoD, backD, shorter, direction⟩ := rewire 26 C mono back j hj a ha
  have failure : ∃ s w, rows s w ∧ (eraseGate 26 C j a).eval w ≠ s := by
    by_contra! none
    exact noSmaller ⟨_,⟨monoD,backD,none⟩,shorter⟩
  obtain ⟨s,w,hw,failed⟩ := failure
  refine ⟨s,w,hw,failed,?_⟩
  intro operand
  have len : w.length = 26 := by
    cases s with
    | true =>
      obtain ⟨i,l,_,rfl⟩ := hw
      simp
    | false =>
      obtain ⟨Q,_,_,rfl⟩ := hw
      simp
  have prior := fit s w hw
  exact prior.symm.trans (direction w len operand (by simpa only [prior] using failed))
