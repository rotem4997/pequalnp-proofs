import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4207_791
    (hasMask :
      let f (z : Fin 9 → Bool) : Bool :=
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
          (fun k => z (Fin.ofNat 9 (k / 10)) && z (Fin.ofNat 9 (k % 10)))
      let r (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin 9) : Finset (Fin C.size) :=
        {i | v.val ∈ (C.gates.get i).inputs}
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.IsMinimalCircuit 9 C → C.size = 15 →
        PEqualNP.MetaComplexity.circuitFun 9 C = f →
        (∀ i : Fin C.size, let g := C.gates.get i
            (∀ w ∈ g.inputs, w < 9 + i.val) ∧ g.inputs.Nodup ∧
            (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1 ∨
              g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 2)) →
        (∀ v ∈ ([4, 6, 7] : List (Fin 9)), (r C v).Nonempty ∧ (r C v).card ≤ 2 ∧
           ∀ i ∈ r C v, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
        (r C 4).card = 2 →
        ∃ x y : Fin 9 → Bool, C.output ≠ 4 ∧ (∀ i ≠ 4, x i = y i) ∧
          PEqualNP.MetaComplexity.circuitFun 9 C x ≠ PEqualNP.MetaComplexity.circuitFun 9 C y ∧
          (∀ i : Fin C.size, let g := C.gates.get i
          (4 : ℕ) ∈ g.inputs → g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          ∃ j ∈ g.inputs, j ≠ 4 ∧ j < 9 + i.val ∧
            (C.wires (List.ofFn x)).getD j false = true))
    (agreeWhenMasked :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x y : Fin 9 → Bool),
        C.output ≠ 4 → (∀ i ≠ 4, x i = y i) →
        (∀ i : Fin C.size, let g := C.gates.get i
          (4 : ℕ) ∈ g.inputs → g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          ∃ j ∈ g.inputs, j ≠ 4 ∧ j < 9 + i.val ∧
            (C.wires (List.ofFn x)).getD j false = true) →
        PEqualNP.MetaComplexity.circuitFun 9 C x = PEqualNP.MetaComplexity.circuitFun 9 C y) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 →     x3.size = (15 : ℕ) →       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 →         (∀ (x7 : Fin x3.size),             have x8 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x7;             (∀ x9 ∈ x8.inputs, x9 < (9 : ℕ) + ↑x7) ∧ x8.inputs.Nodup ∧ (x8.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x8.inputs.length = (1 : ℕ) ∨ x8.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x8.inputs.length = (2 : ℕ))) →           (∀ x8 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x8).Nonempty ∧ (x2 x3 x8).card ≤ (2 : ℕ) ∧ ∀ x10 ∈ x2 x3 x8, (x3.gates.get x10).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (x2 x3 (4 : Fin (9 : ℕ))).card = (2 : ℕ) → False := by
  intro f readers C minimal size computes normalized lowDegree double
  have eqGraph : f = fun z : Fin 9 → Bool =>
      ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
        (fun k => z (Fin.ofNat 9 (k / 10)) && z (Fin.ofNat 9 (k % 10))) := by
    funext z
    simp only [f, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] <;> rfl
  obtain ⟨x, y, output, same, differs, mask⟩ :=
    hasMask C minimal size (computes.trans eqGraph) normalized lowDegree double
  exact differs (agreeWhenMasked C x y output same mask)
