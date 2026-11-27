import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2116_271
    (mask : let f := (fun x : Fin 9 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
        x 5 && x 7 || x 6 && x 8 || x 8 && x 5);
      ∀ (C : Circuit), circuitFun 9 C = f → ∀ (v : Fin 9) (i : Fin C.size) (w : ℕ),
        v ∈ ([4,6,7] : List (Fin 9)) → w < 9+i.val → w ≠ v.val →
        (C.gates.get i).op = GateOp.or →
        ((C.gates.get i).inputs = [v.val,w] ∨ (C.gates.get i).inputs = [w,v.val]) →
        (∀ k : Fin C.size, k ≠ i → v.val ∉ (C.gates.get k).inputs) →
        PEqualNP.TopForm.orIn 9 C w = ∅ ∧
        ∀ x : Fin 9 → Bool, x v = false → f x = false → f (Function.update x v true) = true →
          (C.wires (List.ofFn x)).getD w false = false)
    (search : let f := (fun x : Fin 9 → Bool =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
        x 5 && x 7 || x 6 && x 8 || x 8 && x 5);
      ∀ (C : Circuit), IsMinimalCircuit 9 C → C.size ≤ 15 → circuitFun 9 C = f →
        (∀ i : Fin C.size, (∀ p ∈ (C.gates.get i).inputs, p < 9+i.val) ∧
          (C.gates.get i).inputs.Nodup ∧
          ((C.gates.get i).op = GateOp.not ∧ (C.gates.get i).inputs.length = 1 ∨
           (C.gates.get i).op ≠ GateOp.not ∧ (C.gates.get i).inputs.length = 2)) →
        (∀ v ∈ ([4,6,7] : List (Fin 9)), ∃ (i : Fin C.size) (w : ℕ),
          (C.gates.get i).op = GateOp.or ∧
          ((C.gates.get i).inputs = [v.val,w] ∨ (C.gates.get i).inputs = [w,v.val]) ∧
          (∀ k : Fin C.size, k ≠ i → v.val ∉ (C.gates.get k).inputs) ∧
          PEqualNP.TopForm.orIn 9 C w = ∅ ∧
          ∀ x : Fin 9 → Bool, x v = false → f x = false → f (Function.update x v true) = true →
            (C.wires (List.ofFn x)).getD w false = false) → False) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x4 x6).card = (1 : ℕ) ∧ ∀ x8 ∈ x2 x4 x6, (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → False := by
  dsimp only
  intro C model unique
  obtain ⟨minimal, budget, computes, shape, _⟩ := model
  apply search C minimal budget computes shape
  intro v hv
  obtain ⟨cardinality, ops⟩ := unique v hv
  let readers : Finset (Fin C.size) := Finset.univ.filter fun i => v.val ∈ (C.gates.get i).inputs
  change readers.card = 1 at cardinality
  obtain ⟨i, eqlist⟩ := Finset.card_eq_one.mp cardinality
  have hit (k : Fin C.size) : v.val ∈ (C.gates.get k).inputs ↔ k = i := by
    have equal : k ∈ readers ↔ k = i := by rw [eqlist, Finset.mem_singleton]
    simpa [readers] using equal
  have atI : v.val ∈ (C.gates.get i).inputs := (hit i).mpr rfl
  have isOR : (C.gates.get i).op = .or := ops i (by
    change i ∈ readers
    rw [eqlist]
    exact Finset.mem_singleton_self i)
  have pins2 : (C.gates.get i).inputs.length = 2 := by
    rcases (shape i).2.2 with hn | ha
    · rw [isOR] at hn
      cases hn.1
    · exact ha.2
  have only (k : Fin C.size) (hne : k ≠ i) : v.val ∉ (C.gates.get k).inputs :=
    fun h => hne ((hit k).mp h)
  obtain ⟨a,b,pins⟩ := List.length_eq_two.mp pins2
  have ab : a ≠ b := by simpa [pins] using (shape i).2.1
  have own : v.val = a ∨ v.val = b := by simpa [pins] using atI
  have give (w : ℕ) (hw : w ∈ (C.gates.get i).inputs) (diff : w ≠ v.val)
      (form : (C.gates.get i).inputs = [v.val,w] ∨ (C.gates.get i).inputs = [w,v.val]) :=
    mask C computes v i w hv ((shape i).1 w hw) diff isOR form only
  rcases own with ea | eb
  · subst a
    have bmem : b ∈ (C.gates.get i).inputs := by simp [pins]
    exact ⟨i,b,isOR,Or.inl pins,only,give b bmem (Ne.symm ab) (Or.inl pins)⟩
  · subst b
    have amem : a ∈ (C.gates.get i).inputs := by simp [pins]
    exact ⟨i,a,isOR,Or.inr pins,only,give a amem ab (Or.inr pins)⟩
