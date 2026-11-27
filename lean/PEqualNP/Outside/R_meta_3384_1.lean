import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3384_1
    (h1 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 6 (fun (x : Fin 6 → Bool) => (x 0 && x 1) || (x 0 && x 3) || (x 1 && x 4) ||
      (x 2 && x 4) || (x 3 && x 5) || (x 2 && x 5)) 7)
    (h2 : let row := fun (x : Fin 6 → Bool) => [x 0,x 1,false,x 2,x 3,x 4,x 5]
    ∀ c : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo c → c.size = 11 →
    (PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x => c.eval (row x)) 7 ∨
      let val := fun (j : Fin 11) (x : Fin 6 → Bool) => (c.wires (row x)).getD (7 + j.val) false
      ∃ t : Fin 8 → Fin 11, (∀ i j, i ≠ j → ∃ x, val (t i) x ≠ val (t j) x) ∧
        ∀ i (r : Fin 8), ∃ x, val (t i) x ≠ (false :: true :: List.ofFn x).getD r.val false))
    (h3 : let target : (Fin (7 : ℕ) → Bool) → Bool := fun (x1 : Fin (7 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ))); let row := fun (x : Fin 6 → Bool) => [x 0,x 1,false,x 2,x 3,x 4,x 5]; ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 →
    (let val := fun (j : Fin 11) (x : Fin 6 → Bool) => (x2.wires (row x)).getD (7 + j.val) false
      ∃ t : Fin 8 → Fin 11, (∀ i j, i ≠ j → ∃ x, val (t i) x ≠ val (t j) x) ∧
        ∀ i (r : Fin 8), ∃ x, val (t i) x ≠ (false :: true :: List.ofFn x).getD r.val false) → x2.size = (11 : ℕ) → PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = target → List.Forall₂ (fun (x9 x10 : PEqualNP.CircuitLowerBounds.Gate) => x9.op = x10.op ∧ List.Forall₂ (fun (x11 x12 : ℕ) => x12 = x11 + (1 : ℕ) ∨ x12 = (0 : ℕ) ∧ (x11 = x4 ∨ x11 = x5)) x9.inputs x10.inputs) x2.gates x3.gates → (∀ (x10 : Fin (7 : ℕ) → Bool), (x3.wires (Bool.true :: List.ofFn x10)).getD (x2.output + (1 : ℕ)) Bool.false = (target x10 || x10 (0 : Fin (7 : ℕ)) || x10 (3 : Fin (7 : ℕ)))) → (List.filter (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.op.eval [Bool.true, Bool.false] && x11.inputs.contains (2 : ℕ)) x2.gates).length ≥ (2 : ℕ)) :
have x1 : (Fin (7 : ℕ) → Bool) → Bool := fun (x1 : Fin (7 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (4 : ℕ), (15 : ℕ), (26 : ℕ), (35 : ℕ), (46 : ℕ), (36 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (7 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (7 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (11 : ℕ) → PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = x1 → List.Forall₂ (fun (x9 x10 : PEqualNP.CircuitLowerBounds.Gate) => x9.op = x10.op ∧ List.Forall₂ (fun (x11 x12 : ℕ) => x12 = x11 + (1 : ℕ) ∨ x12 = (0 : ℕ) ∧ (x11 = x4 ∨ x11 = x5)) x9.inputs x10.inputs) x2.gates x3.gates → (∀ (x10 : Fin (7 : ℕ) → Bool), (x3.wires (Bool.true :: List.ofFn x10)).getD (x2.output + (1 : ℕ)) Bool.false = (x1 x10 || x10 (0 : Fin (7 : ℕ)) || x10 (3 : Fin (7 : ℕ)))) → (List.filter (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => x11.op.eval [Bool.true, Bool.false] && x11.inputs.contains (2 : ℕ)) x2.gates).length ≥ (2 : ℕ) := by
  classical
  dsimp only at h2 h3 ⊢
  intro c d a b hfan hsize hfun hmap hhigh
  rcases h2 c hfan hsize with small | rank
  · exfalso
    apply h1
    convert small using 1
    funext x
    have e := congrFun hfun (fun i => ([x 0,x 1,false,x 2,x 3,x 4,x 5] : List Bool).getD i.val false)
    change c.eval (List.ofFn _) = _ at e
    rw [show List.ofFn (fun i : Fin 7 => ([x 0,x 1,false,x 2,x 3,x 4,x 5] : List Bool).getD i.val false) =
      [x 0,x 1,false,x 2,x 3,x 4,x 5] by rfl] at e
    rw [e]
    change _ = ((x 0 && x 1) || ((x 1 && false) || ((x 0 && x 3) || ((x 1 && x 4) ||
      ((false && x 5) || ((x 2 && x 4) || ((x 3 && x 5) || ((x 2 && x 5) || false))))))))
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
      cases h4 : x 4 <;> cases h5 : x 5 <;> rfl
  · exact h3 c d a b hfan rank hsize hfun hmap hhigh
