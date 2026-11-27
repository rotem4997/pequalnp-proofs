import Mathlib
import PEqualNP.Defs

-- For the first child, suppose the circuit has at most 14 gates. Remove its
-- first gate and give the remaining circuit a fresh input z for that wire.
-- Its output H agrees with the target when z is set to x0 AND x2.
-- If H is independent of z, replace z by x0. This gives a circuit of size
-- at most 13 for the target. Restricting the essential input x4 to false
-- saves a gate and leaves the eight-input function of L-meta-1007, which
-- requires at least 13 gates.
-- If H depends on z, setting z to false saves a gate. The result agrees
-- with the target whenever x2 or x0 is false. It still depends on x0
-- because with only x4 set, toggling x0 toggles the output. Setting x0 to false
-- saves a second gate. The remaining function, up to renaming the eight
-- inputs, is the one in L-meta-1664. It requires 12 gates and at most
-- 11 remain. Both gate eliminations have nonconstant restricted outputs.
--
-- For the three exact-size children the recursor counts each NOT gate,
-- including any whose output is unused.
theorem PEqualNP.Outside.R_meta_1668_2
    (lower : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 2)) →
      PEqualNP.MetaComplexity.circuitFun 9 C =
        (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4)
         || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7)
         || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      15 ≤ C.size)
    (zeroNot : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 2)) →
      C.size = 15 →
      C.gates.countP (fun g =>
            PEqualNP.CircuitLowerBounds.GateOp.rec (motive := fun _ => Bool)
              false false true (fun _ => false) false g.op) = 0 →
      PEqualNP.MetaComplexity.circuitFun 9 C ≠
        (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4)
          || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7)
          || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (oneNot : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 2)) →
      C.size = 15 →
      C.gates.countP (fun g =>
            PEqualNP.CircuitLowerBounds.GateOp.rec (motive := fun _ => Bool)
              false false true (fun _ => false) false g.op) = 1 →
      PEqualNP.MetaComplexity.circuitFun 9 C ≠
        (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4)
          || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7)
          || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (moreNot : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 2)) →
      C.size = 15 →
      2 ≤ C.gates.countP (fun g =>
            PEqualNP.CircuitLowerBounds.GateOp.rec (motive := fun _ => Bool)
              false false true (fun _ => false) false g.op) →
      PEqualNP.MetaComplexity.circuitFun 9 C ≠
        (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4)
          || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7)
          || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 2)) →
      PEqualNP.MetaComplexity.circuitFun 9 C =
        (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4)
         || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7)
         || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      16 ≤ C.size := by
  intro C hf first answer
  have bound := lower C hf first answer
  by_contra! small
  have sz : C.size = 15 := by omega
  let n := C.gates.countP (fun g =>
    PEqualNP.CircuitLowerBounds.GateOp.rec (motive := fun _ => Bool)
      false false true (fun _ => false) false g.op)
  by_cases h0 : n = 0
  · exact (zeroNot C hf first sz h0) answer
  by_cases h1 : n = 1
  · exact (oneNot C hf first sz h1) answer
  have hn : 2 ≤ n := by omega
  exact (moreNot C hf first sz hn) answer
