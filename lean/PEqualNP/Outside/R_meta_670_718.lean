import PEqualNP.Defs

-- Split clean minimum representatives by the actual readers of inputs 4, 6, and 7.
-- The normalization child is supported by restriction lower bounds; its proof remains a child.
theorem PEqualNP.Outside.R_meta_670_718 :
  (let f : (Fin 9 → Bool) → Bool := (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
    let r : (C : PEqualNP.CircuitLowerBounds.Circuit) → Fin 9 → Finset (Fin C.size) :=
      fun C v => Finset.univ.filter (fun i : Fin C.size => (v : ℕ) ∈ (C.gates.get i).inputs)
    let P : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C =>
      PEqualNP.MetaComplexity.IsMinimalCircuit 9 C ∧ C.size ≤ 15 ∧
      PEqualNP.MetaComplexity.circuitFun 9 C = f ∧
      (∀ i : Fin C.size, let g := C.gates.get i
        (∀ w ∈ g.inputs, w < 9 + (i : ℕ)) ∧ g.inputs.Nodup ∧
        ((g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1) ∨
         (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 2))) ∧
      ∀ v : Fin 9, v ∈ ([4, 6, 7] : List (Fin 9)) →
        (r C v).Nonempty ∧ (r C v).card ≤ 2 ∧
        ((r C v).card = 2 → ∀ i ∈ r C v, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or)
    PEqualNP.MetaComplexity.HasCircuitSize 9 f 15 → ∃ C, P C) →
  (let f : (Fin 9 → Bool) → Bool := (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
    let r : (C : PEqualNP.CircuitLowerBounds.Circuit) → Fin 9 → Finset (Fin C.size) :=
      fun C v => Finset.univ.filter (fun i : Fin C.size => (v : ℕ) ∈ (C.gates.get i).inputs)
    let P : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C =>
      PEqualNP.MetaComplexity.IsMinimalCircuit 9 C ∧ C.size ≤ 15 ∧
      PEqualNP.MetaComplexity.circuitFun 9 C = f ∧
      (∀ i : Fin C.size, let g := C.gates.get i
        (∀ w ∈ g.inputs, w < 9 + (i : ℕ)) ∧ g.inputs.Nodup ∧
        ((g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1) ∨
         (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 2))) ∧
      ∀ v : Fin 9, v ∈ ([4, 6, 7] : List (Fin 9)) →
        (r C v).Nonempty ∧ (r C v).card ≤ 2 ∧
        ((r C v).card = 2 → ∀ i ∈ r C v, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or)
    ∀ C, P C →
      (∃ v : Fin 9, v ∈ ([4, 6, 7] : List (Fin 9)) ∧
        ∃ i ∈ r C v, (C.gates.get i).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) → False) →
  (let f : (Fin 9 → Bool) → Bool := (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
    let r : (C : PEqualNP.CircuitLowerBounds.Circuit) → Fin 9 → Finset (Fin C.size) :=
      fun C v => Finset.univ.filter (fun i : Fin C.size => (v : ℕ) ∈ (C.gates.get i).inputs)
    let P : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C =>
      PEqualNP.MetaComplexity.IsMinimalCircuit 9 C ∧ C.size ≤ 15 ∧
      PEqualNP.MetaComplexity.circuitFun 9 C = f ∧
      (∀ i : Fin C.size, let g := C.gates.get i
        (∀ w ∈ g.inputs, w < 9 + (i : ℕ)) ∧ g.inputs.Nodup ∧
        ((g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1) ∨
         (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 2))) ∧
      ∀ v : Fin 9, v ∈ ([4, 6, 7] : List (Fin 9)) →
        (r C v).Nonempty ∧ (r C v).card ≤ 2 ∧
        ((r C v).card = 2 → ∀ i ∈ r C v, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or)
    ∀ C, P C →
      (∀ v : Fin 9, v ∈ ([4, 6, 7] : List (Fin 9)) →
        ∀ i ∈ r C v, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
      (∃ v : Fin 9, v ∈ ([4, 6, 7] : List (Fin 9)) ∧ (r C v).card = 2) → False) →
  (let f : (Fin 9 → Bool) → Bool := (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5))
    let r : (C : PEqualNP.CircuitLowerBounds.Circuit) → Fin 9 → Finset (Fin C.size) :=
      fun C v => Finset.univ.filter (fun i : Fin C.size => (v : ℕ) ∈ (C.gates.get i).inputs)
    let P : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun C =>
      PEqualNP.MetaComplexity.IsMinimalCircuit 9 C ∧ C.size ≤ 15 ∧
      PEqualNP.MetaComplexity.circuitFun 9 C = f ∧
      (∀ i : Fin C.size, let g := C.gates.get i
        (∀ w ∈ g.inputs, w < 9 + (i : ℕ)) ∧ g.inputs.Nodup ∧
        ((g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1) ∨
         (g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 2))) ∧
      ∀ v : Fin 9, v ∈ ([4, 6, 7] : List (Fin 9)) →
        (r C v).Nonempty ∧ (r C v).card ≤ 2 ∧
        ((r C v).card = 2 → ∀ i ∈ r C v, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or)
    ∀ C, P C →
      (∀ v : Fin 9, v ∈ ([4, 6, 7] : List (Fin 9)) →
        (r C v).card = 1 ∧ ∀ i ∈ r C v,
          (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or) → False) →
  ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15 := by
  classical
  intro hnormal hnonor hdouble hsingle h
  obtain ⟨C, hC⟩ := hnormal h
  let r : Fin 9 → Finset (Fin C.size) := fun v =>
    Finset.univ.filter (fun i : Fin C.size => (v : ℕ) ∈ (C.gates.get i).inputs)
  have hp : ∀ v : Fin 9, v ∈ ([4, 6, 7] : List (Fin 9)) →
      (r v).Nonempty ∧ (r v).card ≤ 2 ∧
      ((r v).card = 2 → ∀ i ∈ r v,
        (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or) := hC.2.2.2.2
  by_cases hbad : ∃ v : Fin 9, v ∈ ([4, 6, 7] : List (Fin 9)) ∧
      ∃ i ∈ r v, (C.gates.get i).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or
  · exact hnonor C hC hbad
  have hor : ∀ v : Fin 9, v ∈ ([4, 6, 7] : List (Fin 9)) →
      ∀ i ∈ r v, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro v hv i hi
    by_contra hnot
    exact hbad ⟨v, hv, i, hi, hnot⟩
  by_cases htwo : ∃ v : Fin 9, v ∈ ([4, 6, 7] : List (Fin 9)) ∧ (r v).card = 2
  · exact hdouble C hC hor htwo
  apply hsingle C hC
  intro v hv
  refine ⟨?_, hor v hv⟩
  have hpos := Finset.card_pos.mpr (hp v hv).1
  have hle := (hp v hv).2.1
  have hne : (r v).card ≠ 2 := fun he => htwo ⟨v, hv, he⟩
  change (r v).card = 1
  omega
