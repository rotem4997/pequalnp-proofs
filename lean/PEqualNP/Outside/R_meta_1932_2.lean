import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1932_2
    (zeroNot : ∀ (pins : List ℕ), pins.length ≤ 2 →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
      D.size ≤ 13 →
      D.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op) = 0 →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 && x 2]
        D.eval (w ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
          (pins.map fun i => w.getD i false)]) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
           (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
           (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (oneNot : ∀ (pins : List ℕ), pins.length ≤ 2 →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
      D.size ≤ 13 →
      D.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op) = 1 →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 && x 2]
        D.eval (w ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
          (pins.map fun i => w.getD i false)]) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
           (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
           (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (twoNot : ∀ (pins : List ℕ), pins.length ≤ 2 →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
      D.size ≤ 13 →
      D.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op) = 2 →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 && x 2]
        D.eval (w ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
          (pins.map fun i => w.getD i false)]) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
           (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
           (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
    (moreNot : ∀ (pins : List ℕ), pins.length ≤ 2 →
      ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D →
      D.size ≤ 13 →
      3 ≤ D.gates.countP (fun g => PEqualNP.CircuitLowerBounds.GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op) →
      ∃ x : Fin 9 → Bool,
        let w := List.ofFn x ++ [x 0 && x 2]
        D.eval (w ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
          (pins.map fun i => w.getD i false)]) ≠
          ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
           (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
           (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    ∀ (x1 : List ℕ),   x1.length ≤ (2 : ℕ) →     ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),       PEqualNP.MetaComplexity.FanInTwo x3 →         x3.size ≤ (13 : ℕ) →           ∃ (x6 : Fin (9 : ℕ) → Bool),             have x7 : List Bool := List.ofFn x6 ++ [x6 (0 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ))];             x3.eval (x7 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x8 : ℕ) => x7.getD x8 Bool.false) x1)]) ≠ (x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) := by
  intro pins hlen D hfan hsize
  let n := D.gates.countP (fun g =>
    PEqualNP.CircuitLowerBounds.GateOp.rec (motive := fun _ => Bool)
      false false true (fun _ => false) false g.op)
  by_cases h0 : n = 0
  · exact zeroNot pins hlen D hfan hsize h0
  by_cases h1 : n = 1
  · exact oneNot pins hlen D hfan hsize h1
  by_cases h2 : n = 2
  · exact twoNot pins hlen D hfan hsize h2
  exact moreNot pins hlen D hfan hsize (show 3 ≤ n by omega)
