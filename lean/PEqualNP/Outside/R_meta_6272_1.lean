import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- The circuit is empty or its last gate is one of the two allowed kinds, and past the end of the
-- gate list `gateAt` reads the default OR gate. So the gate at index `size - 1` is an AND in one
-- case and an OR in the other, and the step is asked once for each of the two cases.
theorem PEqualNP.Outside.R_meta_6272_1
    (lastAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Finset (Fin (13 : ℕ))), (∀ (x5 : Fin (13 : ℕ)), (x3 ∩ PEqualNP.HeptadCover.singerLines3 x5).card ≤ (2 : ℕ)) → x4.card ≤ (3 : ℕ) → (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x4 | x7 ∈ PEqualNP.HeptadCover.singerLines3 x8}.card ≤ (2 : ℕ)) → x1.eval (PEqualNP.GenericRejection.incidenceInput x3 x4) = PEqualNP.GenericRejection.incidenceFun PEqualNP.HeptadCover.singerLines3 x3 x4) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (39 : ℕ) ≤ x1.size)
    (lastOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Finset (Fin (13 : ℕ))), (∀ (x5 : Fin (13 : ℕ)), (x3 ∩ PEqualNP.HeptadCover.singerLines3 x5).card ≤ (2 : ℕ)) → x4.card ≤ (3 : ℕ) → (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x4 | x7 ∈ PEqualNP.HeptadCover.singerLines3 x8}.card ≤ (2 : ℕ)) → x1.eval (PEqualNP.GenericRejection.incidenceInput x3 x4) = PEqualNP.GenericRejection.incidenceFun PEqualNP.HeptadCover.singerLines3 x3 x4) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or → (39 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ (x3 x4 : Finset (Fin (13 : ℕ))), (∀ (x5 : Fin (13 : ℕ)), (x3 ∩ PEqualNP.HeptadCover.singerLines3 x5).card ≤ (2 : ℕ)) → x4.card ≤ (3 : ℕ) → (∀ (x7 : Fin (13 : ℕ)), {x8 ∈ x4 | x7 ∈ PEqualNP.HeptadCover.singerLines3 x8}.card ≤ (2 : ℕ)) → x1.eval (PEqualNP.GenericRejection.incidenceInput x3 x4) = PEqualNP.GenericRejection.incidenceFun PEqualNP.HeptadCover.singerLines3 x3 x4) → (39 : ℕ) ≤ x1.size := by
  intros x1 h1 h2
  have hop : ∀ g ∈ x1.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa using (h1 g hg).1
  have hsz : x1.size = x1.gates.length := rfl
  have hcase : (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op =
      GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = GateOp.or := by
    rcases Nat.eq_zero_or_pos x1.size with hz | hpos
    · right
      have hg : PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))
          = Gate.mk GateOp.or [] := by
        show List.getD x1.gates (x1.size - (1 : ℕ)) (Gate.mk GateOp.or []) = _
        apply List.getD_eq_default
        omega
      rw [hg]
    · have hj : x1.size - (1 : ℕ) < x1.gates.length := by rw [← hsz]; omega
      have hg : PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))
          = x1.gates[x1.size - (1 : ℕ)] :=
        List.getD_eq_getElem _ _ hj
      rw [hg]
      exact hop _ (List.getElem_mem hj)
  rcases hcase with hand | har
  · exact lastAnd x1 h1 h2 hand
  · exact lastOr x1 h1 h2 har
