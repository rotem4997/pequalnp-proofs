import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18994_556
    (hRawNot : ∀ (x1 x2 : List PEqualNP.CircuitLowerBounds.Gate) (x3 x4 : ℕ),
      PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →
      PEqualNP.MetaComplexity.FanInTwo { gates := x2, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →
      List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x8 : ℕ) => Bool.false) Bool.false x7.op) x1 = (0 : ℕ) →
      List.countP (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x9 : ℕ) => Bool.false) Bool.false x8.op) x2 = (0 : ℕ) →
      x1.length ≤ (3 : ℕ) →
      x1.length + x2.length = (17 : ℕ) →
      x3 < (10 : ℕ) →
      x4 < (28 : ℕ) →
      ∃ (x13 : Fin (10 : ℕ) → Bool), { gates := x1 ++ { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x3] : PEqualNP.CircuitLowerBounds.Gate } :: x2, output := x4 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x13) ≠ (x13 (0 : Fin (10 : ℕ)) && x13 (1 : Fin (10 : ℕ)) || x13 (1 : Fin (10 : ℕ)) && x13 (2 : Fin (10 : ℕ)) || x13 (2 : Fin (10 : ℕ)) && x13 (3 : Fin (10 : ℕ)) || x13 (3 : Fin (10 : ℕ)) && x13 (4 : Fin (10 : ℕ)) || x13 (4 : Fin (10 : ℕ)) && x13 (0 : Fin (10 : ℕ)) || x13 (0 : Fin (10 : ℕ)) && x13 (5 : Fin (10 : ℕ)) || x13 (1 : Fin (10 : ℕ)) && x13 (6 : Fin (10 : ℕ)) || x13 (2 : Fin (10 : ℕ)) && x13 (7 : Fin (10 : ℕ)) || x13 (3 : Fin (10 : ℕ)) && x13 (8 : Fin (10 : ℕ)) || x13 (4 : Fin (10 : ℕ)) && x13 (9 : Fin (10 : ℕ)) || x13 (5 : Fin (10 : ℕ)) && x13 (7 : Fin (10 : ℕ)) || x13 (7 : Fin (10 : ℕ)) && x13 (9 : Fin (10 : ℕ)) || x13 (9 : Fin (10 : ℕ)) && x13 (6 : Fin (10 : ℕ)) || x13 (6 : Fin (10 : ℕ)) && x13 (8 : Fin (10 : ℕ)) || x13 (8 : Fin (10 : ℕ)) && x13 (5 : Fin (10 : ℕ))))
    (hHighFanout : ∀ (x1 x2 : List PEqualNP.CircuitLowerBounds.Gate) (x3 x4 : ℕ),
      PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →
      PEqualNP.MetaComplexity.FanInTwo { gates := x2, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →
      List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x8 : ℕ) => Bool.false) Bool.false x7.op) x1 = (0 : ℕ) →
      List.countP (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x9 : ℕ) => Bool.false) Bool.false x8.op) x2 = (0 : ℕ) →
      x1.length ≤ (3 : ℕ) →
      x1.length + x2.length = (17 : ℕ) →
      (10 : ℕ) ≤ x3 →
      x3 < (10 : ℕ) + x1.length →
      x4 < (28 : ℕ) →
      (∃ (v : Fin (10 : ℕ)), (3 : ℕ) ≤ List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (v.val ∈ g.inputs)) (x1 ++ x2)) →
      ∃ (x13 : Fin (10 : ℕ) → Bool), { gates := x1 ++ { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x3] : PEqualNP.CircuitLowerBounds.Gate } :: x2, output := x4 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x13) ≠ (x13 (0 : Fin (10 : ℕ)) && x13 (1 : Fin (10 : ℕ)) || x13 (1 : Fin (10 : ℕ)) && x13 (2 : Fin (10 : ℕ)) || x13 (2 : Fin (10 : ℕ)) && x13 (3 : Fin (10 : ℕ)) || x13 (3 : Fin (10 : ℕ)) && x13 (4 : Fin (10 : ℕ)) || x13 (4 : Fin (10 : ℕ)) && x13 (0 : Fin (10 : ℕ)) || x13 (0 : Fin (10 : ℕ)) && x13 (5 : Fin (10 : ℕ)) || x13 (1 : Fin (10 : ℕ)) && x13 (6 : Fin (10 : ℕ)) || x13 (2 : Fin (10 : ℕ)) && x13 (7 : Fin (10 : ℕ)) || x13 (3 : Fin (10 : ℕ)) && x13 (8 : Fin (10 : ℕ)) || x13 (4 : Fin (10 : ℕ)) && x13 (9 : Fin (10 : ℕ)) || x13 (5 : Fin (10 : ℕ)) && x13 (7 : Fin (10 : ℕ)) || x13 (7 : Fin (10 : ℕ)) && x13 (9 : Fin (10 : ℕ)) || x13 (9 : Fin (10 : ℕ)) && x13 (6 : Fin (10 : ℕ)) || x13 (6 : Fin (10 : ℕ)) && x13 (8 : Fin (10 : ℕ)) || x13 (8 : Fin (10 : ℕ)) && x13 (5 : Fin (10 : ℕ))))
    (hGateNotBounded : ∀ (x1 x2 : List PEqualNP.CircuitLowerBounds.Gate) (x3 x4 : ℕ),
      PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →
      PEqualNP.MetaComplexity.FanInTwo { gates := x2, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →
      List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x8 : ℕ) => Bool.false) Bool.false x7.op) x1 = (0 : ℕ) →
      List.countP (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x9 : ℕ) => Bool.false) Bool.false x8.op) x2 = (0 : ℕ) →
      x1.length ≤ (3 : ℕ) →
      x1.length + x2.length = (17 : ℕ) →
      (10 : ℕ) ≤ x3 →
      x3 < (10 : ℕ) + x1.length →
      x4 < (28 : ℕ) →
      (∀ (v : Fin (10 : ℕ)), List.countP (fun (g : PEqualNP.CircuitLowerBounds.Gate) => Decidable.decide (v.val ∈ g.inputs)) (x1 ++ x2) ≤ (2 : ℕ)) →
      ∃ (x13 : Fin (10 : ℕ) → Bool), { gates := x1 ++ { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x3] : PEqualNP.CircuitLowerBounds.Gate } :: x2, output := x4 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x13) ≠ (x13 (0 : Fin (10 : ℕ)) && x13 (1 : Fin (10 : ℕ)) || x13 (1 : Fin (10 : ℕ)) && x13 (2 : Fin (10 : ℕ)) || x13 (2 : Fin (10 : ℕ)) && x13 (3 : Fin (10 : ℕ)) || x13 (3 : Fin (10 : ℕ)) && x13 (4 : Fin (10 : ℕ)) || x13 (4 : Fin (10 : ℕ)) && x13 (0 : Fin (10 : ℕ)) || x13 (0 : Fin (10 : ℕ)) && x13 (5 : Fin (10 : ℕ)) || x13 (1 : Fin (10 : ℕ)) && x13 (6 : Fin (10 : ℕ)) || x13 (2 : Fin (10 : ℕ)) && x13 (7 : Fin (10 : ℕ)) || x13 (3 : Fin (10 : ℕ)) && x13 (8 : Fin (10 : ℕ)) || x13 (4 : Fin (10 : ℕ)) && x13 (9 : Fin (10 : ℕ)) || x13 (5 : Fin (10 : ℕ)) && x13 (7 : Fin (10 : ℕ)) || x13 (7 : Fin (10 : ℕ)) && x13 (9 : Fin (10 : ℕ)) || x13 (9 : Fin (10 : ℕ)) && x13 (6 : Fin (10 : ℕ)) || x13 (6 : Fin (10 : ℕ)) && x13 (8 : Fin (10 : ℕ)) || x13 (8 : Fin (10 : ℕ)) && x13 (5 : Fin (10 : ℕ)))) :
    (∀ (x1 x2 : List PEqualNP.CircuitLowerBounds.Gate) (x3 x4 : ℕ), PEqualNP.MetaComplexity.FanInTwo { gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } → PEqualNP.MetaComplexity.FanInTwo { gates := x2, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } → List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x8 : ℕ) => Bool.false) Bool.false x7.op) x1 = (0 : ℕ) → List.countP (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.false Bool.false Bool.true (fun (x9 : ℕ) => Bool.false) Bool.false x8.op) x2 = (0 : ℕ) → x1.length ≤ (3 : ℕ) → x1.length + x2.length = (17 : ℕ) → x3 < (10 : ℕ) + x1.length → x4 < (28 : ℕ) → ∃ (x13 : Fin (10 : ℕ) → Bool), { gates := x1 ++ { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x3] : PEqualNP.CircuitLowerBounds.Gate } :: x2, output := x4 : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x13) ≠ (x13 (0 : Fin (10 : ℕ)) && x13 (1 : Fin (10 : ℕ)) || x13 (1 : Fin (10 : ℕ)) && x13 (2 : Fin (10 : ℕ)) || x13 (2 : Fin (10 : ℕ)) && x13 (3 : Fin (10 : ℕ)) || x13 (3 : Fin (10 : ℕ)) && x13 (4 : Fin (10 : ℕ)) || x13 (4 : Fin (10 : ℕ)) && x13 (0 : Fin (10 : ℕ)) || x13 (0 : Fin (10 : ℕ)) && x13 (5 : Fin (10 : ℕ)) || x13 (1 : Fin (10 : ℕ)) && x13 (6 : Fin (10 : ℕ)) || x13 (2 : Fin (10 : ℕ)) && x13 (7 : Fin (10 : ℕ)) || x13 (3 : Fin (10 : ℕ)) && x13 (8 : Fin (10 : ℕ)) || x13 (4 : Fin (10 : ℕ)) && x13 (9 : Fin (10 : ℕ)) || x13 (5 : Fin (10 : ℕ)) && x13 (7 : Fin (10 : ℕ)) || x13 (7 : Fin (10 : ℕ)) && x13 (9 : Fin (10 : ℕ)) || x13 (9 : Fin (10 : ℕ)) && x13 (6 : Fin (10 : ℕ)) || x13 (6 : Fin (10 : ℕ)) && x13 (8 : Fin (10 : ℕ)) || x13 (8 : Fin (10 : ℕ)) && x13 (5 : Fin (10 : ℕ)))) := by
  intro x1 x2 x3 x4 hf1 hf2 hc1 hc2 hle hsum hx3 hx4
  by_cases hraw : x3 < 10
  · exact hRawNot x1 x2 x3 x4 hf1 hf2 hc1 hc2 hle hsum hraw hx4
  · have hge : 10 ≤ x3 := Nat.le_of_not_lt hraw
    by_cases hfan : ∃ v : Fin 10, 3 ≤ List.countP (fun g : PEqualNP.CircuitLowerBounds.Gate => Decidable.decide (v.val ∈ g.inputs)) (x1 ++ x2)
    · exact hHighFanout x1 x2 x3 x4 hf1 hf2 hc1 hc2 hle hsum hge hx3 hx4 hfan
    · apply hGateNotBounded x1 x2 x3 x4 hf1 hf2 hc1 hc2 hle hsum hge hx3 hx4
      intro v
      by_contra hgt
      exact hfan ⟨v, by omega⟩
