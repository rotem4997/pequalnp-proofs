import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3338_1
    (h1 : let t := fun (x : Fin 8 → Bool) =>
      let n := PEqualNP.MetaComplexity.tableIndex x
      ([18369897887404062920, 18446740762289764600, 18446744073709551560,
        18446744073709551608] : List Nat).getD (n / 64) 0 |>.testBit (n % 64)
    ∀ k, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x => t x || x 0 || x 3) k → 10 ≤ k)
    (h2 : let args := fun (b : Bool) (x : Fin 8 → Bool) =>
      [x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3, x 1 || b]
    let used := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
      if g.op.eval [false,false] then g.inputs.take 1 else g.inputs
    ∀ (p s : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (o : Nat),
    let c : PEqualNP.CircuitLowerBounds.Circuit := ⟨p ++ g :: s, o⟩
    PEqualNP.MetaComplexity.FanInTwo c → g.op = .or → (used g).any (fun j => decide (j = 6)) = true →
    PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x => c.eval (args true x))
      (max 1 (p.length + s.length - ((p.filter (fun g => (used g).contains 9)).length +
      (s.filter (fun g => (used g).contains 9 || (used g).contains (10 + p.length))).length))))
    (h3 : let t := fun (x : Fin 8 → Bool) =>
      let n := PEqualNP.MetaComplexity.tableIndex x
      ([18369897887404062920, 18446740762289764600, 18446744073709551560,
        18446744073709551608] : List Nat).getD (n / 64) 0 |>.testBit (n % 64)
    let args := fun (b : Bool) (x : Fin 8 → Bool) =>
      [x 1, x 0, x 4, x 7, x 5, x 2, b, x 6, x 3, x 1 || b]
    let used := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
      if g.op.eval [false,false] then g.inputs.take 1 else g.inputs
    ∀ (p s : List PEqualNP.CircuitLowerBounds.Gate) (g : PEqualNP.CircuitLowerBounds.Gate) (o : Nat),
    let c : PEqualNP.CircuitLowerBounds.Circuit := ⟨p ++ g :: s, o⟩
    PEqualNP.MetaComplexity.FanInTwo c → p.length + s.length ≤ 13 →
    (∀ h ∈ p ++ s, (used h).any (fun j => decide (j = 6)) = false) →
    (used g).any (fun j => decide (j = 6)) = true → g.op = .or →
    10 ≤ p.length + s.length - ((p.filter (fun g => (used g).contains 9)).length +
      (s.filter (fun g => (used g).contains 9 || (used g).contains (10 + p.length))).length) →
    ¬ ((∀ x, c.eval (args false x) = t x) ∧ (∀ x, c.eval (args true x) = (t x || x 0 || x 3)))) :
have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => Decidable.decide (x2 = (6 : ℕ)); have x2 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x2 : Bool) (x3 : Fin (8 : ℕ) → Bool) => [x3 (1 : Fin (8 : ℕ)), x3 (0 : Fin (8 : ℕ)), x3 (4 : Fin (8 : ℕ)), x3 (7 : Fin (8 : ℕ)), x3 (5 : Fin (8 : ℕ)), x3 (2 : Fin (8 : ℕ)), x2, x3 (6 : Fin (8 : ℕ)), x3 (3 : Fin (8 : ℕ)), x3 (1 : Fin (8 : ℕ)) || x2]; have x3 : (Fin (8 : ℕ) → Bool) → Bool := fun (x3 : Fin (8 : ℕ) → Bool) =>   have x4 : ℕ := PEqualNP.MetaComplexity.tableIndex x3;   ([(18369897887404062920 : ℕ), (18446740762289764600 : ℕ), (18446744073709551560 : ℕ), (18446744073709551608 : ℕ)].getD (x4 / (64 : ℕ)) (0 : ℕ)).testBit (x4 % (64 : ℕ)); ∀ (x4 x5 : List PEqualNP.CircuitLowerBounds.Gate) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : ℕ),   have x8 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x4 ++ x6 :: x5, output := x7 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x8 →     x4.length + x5.length ≤ (13 : ℕ) →       (∀ x11 ∈ x4 ++ x5, x1 x11 = Bool.false) →         x1 x6 = Bool.true →           x6.op = PEqualNP.CircuitLowerBounds.GateOp.or →             (have x14 : Fin (8 : ℕ) → Bool := fun (x14 : Fin (8 : ℕ)) => Decidable.decide (x14 = (1 : Fin (8 : ℕ)) ∨ x14 = (3 : Fin (8 : ℕ)));               have x15 : Bool → Bool := fun (x15 : Bool) => x6.op.eval (List.map (fun (x16 : ℕ) => ({ gates := x4, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (x2 x15 x14)).getD x16 Bool.false) x6.inputs);               x15 Bool.true ≠ x15 Bool.false) →               (∀ (x15 : Fin (8 : ℕ) → Bool), x8.eval (x2 Bool.false x15) = x3 x15) → ∃ (x16 : Fin (8 : ℕ) → Bool), x8.eval (x2 Bool.true x16) ≠ (x3 x16 || x16 (0 : Fin (8 : ℕ)) || x16 (3 : Fin (8 : ℕ))) := by
  classical
  dsimp only at h1 h2 h3 ⊢
  intro p s g o hfan hsize hnone hraw hor _ hzero
  by_contra! hone
  have high := h2 p s g o hfan hor hraw
  have same := funext hone
  rw [same] at high
  have bound := h1 _ high
  exact h3 p s g o hfan hsize hnone hraw hor (by omega) ⟨hzero, hone⟩
