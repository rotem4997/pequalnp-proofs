import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4217_1
    (factor : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (k : ℕ),
      PEqualNP.TopForm.IsAO2 n C →
      (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and →
      let branch := fun b : Fin 2 =>
        PEqualNP.MetaComplexity.circuitFun n (PEqualNP.CircuitMoves.eraseGate n C k (PEqualNP.TopForm.opnd C k b))
      PEqualNP.MetaComplexity.circuitFun n C = fun x => branch 0 x && branch 1 x)
    (separate : ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      let val := fun (w : ℕ) (u v : Fin 14) =>
        PEqualNP.CleanedNonEdge.wireVal 14 C w (PEqualNP.EdgeOwnership.pairInput u v)
      let op := PEqualNP.TopForm.opnd C
      let isAnd := fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
        PEqualNP.CircuitLowerBounds.GateOp.and
      let atWire := fun w j => 14 + j = w ∨ PEqualNP.EdgeOwnership.InCone 14 C j (w - 14)
      let quiet := fun w => val w 0 0 = false ∧ val w 7 7 = false
      let start := fun j => isAnd j ∧ quiet (14 + j) ∧
        ∃ b : Fin 2, val (op j b) 0 0 = true ∧ val (op j (1-b)) 7 7 = true
      C.size ≤ 27 → PEqualNP.TopForm.IsAO2 14 C →
      (∀ g ∈ C.gates, g.inputs.Nodup) →
      ∀ k, isAnd k → atWire C.output k → val (14+k) 0 7 = true →
        (∀ b, quiet (op k b)) →
        (let branch := fun b : Fin 2 =>
          PEqualNP.MetaComplexity.circuitFun 14 (PEqualNP.CircuitMoves.eraseGate 14 C k (op k b))
         (fun x => branch 0 x && branch 1 x) =
           PEqualNP.ReadTwo.fpl 7 (fun p l : Fin 7 => p ∈ PEqualNP.CircuitLowerBounds.fanoLines l)) →
        (∀ b, ∃ j, atWire (op k b) j ∧ start j) →
        ∃ j, (atWire (op k 0) j ∧ start j) ∧ (atWire (op k 1) j ∧ start j)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),
    have x2 : ℕ → Fin (14 : ℕ) → Fin (14 : ℕ) → Bool := fun (x2 : ℕ) (x3 x4 : Fin (14 : ℕ)) => PEqualNP.CleanedNonEdge.wireVal (14 : ℕ) x1 x2 (PEqualNP.EdgeOwnership.pairInput x3 x4);
    have x3 : ℕ → ℕ → Prop := fun (x3 x4 : ℕ) => ((14 : ℕ) + x4 = x3 ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x4 (x3 - (14 : ℕ))) ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x2 ((14 : ℕ) + x4) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 ((14 : ℕ) + x4) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false ∧ ∃ (x5 : Fin (2 : ℕ)), x2 (PEqualNP.TopForm.opnd x1 x4 x5) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.true ∧ x2 (PEqualNP.TopForm.opnd x1 x4 ((1 : Fin (2 : ℕ)) - x5)) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true;
    x1.size ≤ (27 : ℕ) → PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → (∀ x6 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x6).inputs.Nodup) → (PEqualNP.MetaComplexity.circuitFun (14 : ℕ) x1 = fun (x7 : Fin (14 : ℕ) → Bool) => Decidable.decide (∃ (x8 : Fin (7 : ℕ)) (x9 : Fin (7 : ℕ)), x8 ∈ PEqualNP.CircuitLowerBounds.fanoLines x9 ∧ x7 (Fin.castAdd (7 : ℕ) x8) = Bool.true ∧ x7 (Fin.natAdd (7 : ℕ) x9) = Bool.true)) → ∀ (x8 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and → (14 : ℕ) + x8 = x1.output ∨ PEqualNP.EdgeOwnership.InCone (14 : ℕ) x1 x8 (x1.output - (14 : ℕ)) → x2 ((14 : ℕ) + x8) (0 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.true → (∀ (x12 : Fin (2 : ℕ)), x2 (PEqualNP.TopForm.opnd x1 x8 x12) (0 : Fin (14 : ℕ)) (0 : Fin (14 : ℕ)) = Bool.false ∧ x2 (PEqualNP.TopForm.opnd x1 x8 x12) (7 : Fin (14 : ℕ)) (7 : Fin (14 : ℕ)) = Bool.false) → (¬∃ (x13 : ℕ), x3 (PEqualNP.TopForm.opnd x1 x8 (0 : Fin (2 : ℕ))) x13 ∧ x3 (PEqualNP.TopForm.opnd x1 x8 (1 : Fin (2 : ℕ))) x13) → ¬∃ (x14 : ℕ) (x15 : ℕ), x3 (PEqualNP.TopForm.opnd x1 x8 (0 : Fin (2 : ℕ))) x14 ∧ x3 (PEqualNP.TopForm.opnd x1 x8 (1 : Fin (2 : ℕ))) x15 := by
  intro C
  dsimp only
  intro size shape distinct computes k hand live pair singles disjoint witnesses
  obtain ⟨left, right, hl, hr⟩ := witnesses
  have pins : ∀ g ∈ C.gates, g.inputs.Nodup := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] :=
      List.getD_eq_getElem _ _ hj
    exact hgate ▸ distinct j hj
  have common := separate C size shape pins k hand live pair singles
    ((factor 14 C k shape hand).symm.trans computes)
  apply disjoint
  simp only [and_assoc] at common ⊢
  apply common
  intro b
  fin_cases b
  · exact ⟨left, hl⟩
  · exact ⟨right, hr⟩
