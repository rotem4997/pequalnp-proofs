import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A unique reader of the two opposite literals can retain only one polarity.
-- The first child removes the inverter and the extra wire. The second searches
-- nine-input circuits with one reader, allowing either polarity at input zero.
theorem PEqualNP.Outside.R_meta_2309_1
    (contract : ∀ C : Circuit,
      let tail := (C.gates.drop 1).map (fun g => Gate.mk g.op (ite (g.op.eval [false] = true) (g.inputs.take 1) g.inputs))
      FanInTwo C →
      (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = !(x 0)) →
      (tail.filter (fun g => [0,9].any fun j => g.inputs.contains j)).length ≤ 1 →
      ∃ (D : Circuit) (b : Bool), FanInTwo D ∧ D.size < C.size ∧
        (D.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1 ∧
        ∀ x : Fin 9 → Bool, circuitFun 9 C x =
          circuitFun 9 D (fun i => if i = 0 then b != x 0 else x i))
    (exclude : ∀ (D : Circuit) (b : Bool), FanInTwo D → D.size ≤ 14 →
      (D.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1 →
      ∃ x : Fin 9 → Bool,
        circuitFun 9 D (fun i => if i = 0 then b != x 0 else x i) ≠
        ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
         (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
         (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   have x3 : List PEqualNP.CircuitLowerBounds.Gate := List.map (fun (x3 : PEqualNP.CircuitLowerBounds.Gate) => { op := x3.op, inputs := if x3.op.eval [Bool.false] = Bool.true then List.take (1 : ℕ) x3.inputs else x3.inputs : PEqualNP.CircuitLowerBounds.Gate }) (List.drop (1 : ℕ) x2.gates);   have x4 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => [(0 : ℕ), (9 : ℕ)].any fun (x5 : ℕ) => x4.inputs.contains x5;   have x5 : ℕ := (List.filter x4 x3).length;   PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x7 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x7)).getD (9 : ℕ) Bool.false = !x7 (0 : Fin (9 : ℕ))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → x2.size ≤ (15 : ℕ) → x5 ≤ (1 : ℕ) → False := by
  dsimp only
  intro C hfan hfirst hfun hsize hfew
  obtain ⟨D, b, hD, hlen, hone, heq⟩ := contract C hfan hfirst hfew
  obtain ⟨x, hx⟩ := exclude D b hD (by omega) hone
  exact hx ((heq x).symm.trans (congrFun hfun x))
