import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2938_1
    (zeroNot :
      ∀ (pins : List (Fin 11)), pins.length = 2 →
        ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
            C.gates.countP (fun g =>
              PEqualNP.CircuitLowerBounds.GateOp.rec (motive := fun _ => Bool)
                false false true (fun _ => false) false g.op) = 0 →
              ∃ (x : Fin 9 → Bool),
                let w : List Bool := List.ofFn x ++ [x 0 && x 2];
                C.eval (w ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
                  (pins.map fun i => w.getD i.val false)]) ≠
                  (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
                   x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
                   x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (oneNot :
      ∀ (pins : List (Fin 11)), pins.length = 2 →
        ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
            C.gates.countP (fun g =>
              PEqualNP.CircuitLowerBounds.GateOp.rec (motive := fun _ => Bool)
                false false true (fun _ => false) false g.op) = 1 →
              ∃ (x : Fin 9 → Bool),
                let w : List Bool := List.ofFn x ++ [x 0 && x 2];
                C.eval (w ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
                  (pins.map fun i => w.getD i.val false)]) ≠
                  (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
                   x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
                   x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5))
    (twoOrMore :
      ∀ (pins : List (Fin 11)), pins.length = 2 →
        ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
            2 ≤ C.gates.countP (fun g =>
              PEqualNP.CircuitLowerBounds.GateOp.rec (motive := fun _ => Bool)
                false false true (fun _ => false) false g.op) →
              ∃ (x : Fin 9 → Bool),
                let w : List Bool := List.ofFn x ++ [x 0 && x 2];
                C.eval (w ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
                  (pins.map fun i => w.getD i.val false)]) ≠
                  (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
                   x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
                   x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) :
    ∀ (pins : List (Fin 11)), pins.length = 2 →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ 13 →
          ∃ (x : Fin 9 → Bool),
            let w : List Bool := List.ofFn x ++ [x 0 && x 2];
            C.eval (w ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
              (pins.map fun i => w.getD i.val false)]) ≠
              (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
               x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
               x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
  intro pins hp C hfan hsize
  let n := C.gates.countP (fun g =>
    PEqualNP.CircuitLowerBounds.GateOp.rec (motive := fun _ => Bool)
      false false true (fun _ => false) false g.op)
  by_cases hzero : n = 0
  · exact zeroNot pins hp C hfan hsize (by simpa [n] using hzero)
  by_cases hone : n = 1
  · exact oneNot pins hp C hfan hsize (by simpa [n] using hone)
  · have htwo : 2 ≤ n := by omega
    exact twoOrMore pins hp C hfan hsize (by simpa [n] using htwo)
