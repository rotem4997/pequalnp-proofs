import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- The circuit is empty or its last gate is one of the two allowed kinds, and past the end of the
-- gate list `gateAt` reads the default OR gate. So the gate at index `size - 1` is an AND in one
-- case and an OR in the other, and the step is asked once for each of the two cases.
theorem PEqualNP.Outside.R_meta_7267_1
    (lastAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), ∀ x4 ∈ [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)]], PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x1 → x2 < (27 : ℕ) + x1.size → x3 < (27 : ℕ) + x1.size → (∀ (x10 x11 : Fin (13 : ℕ)), x10 ∈ PEqualNP.HeptadCover.singerLines3 x11 → (x1.wires (PEqualNP.GenericRejection.incidenceInput {x10} {x11} ++ [x4.any fun (x13 : ℕ) => (PEqualNP.GenericRejection.incidenceInput {x10} {x11}).getD x13 Bool.false])).getD x2 Bool.false = Bool.true ∧ (x1.wires (PEqualNP.GenericRejection.incidenceInput {x10} {x11} ++ [x4.any fun (x13 : ℕ) => (PEqualNP.GenericRejection.incidenceInput {x10} {x11}).getD x13 Bool.false])).getD x3 Bool.false = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x11 → (x1.wires (PEqualNP.GenericRejection.incidenceInput x11 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x11) ++ [x4.any fun (x13 : ℕ) => (PEqualNP.GenericRejection.incidenceInput x11 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x11)).getD x13 Bool.false])).getD x2 Bool.false = Bool.false ∨ (x1.wires (PEqualNP.GenericRejection.incidenceInput x11 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x11) ++ [x4.any fun (x13 : ℕ) => (PEqualNP.GenericRejection.incidenceInput x11 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x11)).getD x13 Bool.false])).getD x3 Bool.false = Bool.false) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (62 : ℕ) ≤ x1.size)
    (lastOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), ∀ x4 ∈ [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)]], PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x1 → x2 < (27 : ℕ) + x1.size → x3 < (27 : ℕ) + x1.size → (∀ (x10 x11 : Fin (13 : ℕ)), x10 ∈ PEqualNP.HeptadCover.singerLines3 x11 → (x1.wires (PEqualNP.GenericRejection.incidenceInput {x10} {x11} ++ [x4.any fun (x13 : ℕ) => (PEqualNP.GenericRejection.incidenceInput {x10} {x11}).getD x13 Bool.false])).getD x2 Bool.false = Bool.true ∧ (x1.wires (PEqualNP.GenericRejection.incidenceInput {x10} {x11} ++ [x4.any fun (x13 : ℕ) => (PEqualNP.GenericRejection.incidenceInput {x10} {x11}).getD x13 Bool.false])).getD x3 Bool.false = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x11 → (x1.wires (PEqualNP.GenericRejection.incidenceInput x11 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x11) ++ [x4.any fun (x13 : ℕ) => (PEqualNP.GenericRejection.incidenceInput x11 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x11)).getD x13 Bool.false])).getD x2 Bool.false = Bool.false ∨ (x1.wires (PEqualNP.GenericRejection.incidenceInput x11 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x11) ++ [x4.any fun (x13 : ℕ) => (PEqualNP.GenericRejection.incidenceInput x11 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x11)).getD x13 Bool.false])).getD x3 Bool.false = Bool.false) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or → (62 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ), ∀ x4 ∈ [[], [(0 : ℕ)], [(13 : ℕ)], [(0 : ℕ), (1 : ℕ)], [(13 : ℕ), (14 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)]], PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x1 → x2 < (27 : ℕ) + x1.size → x3 < (27 : ℕ) + x1.size → (∀ (x10 x11 : Fin (13 : ℕ)), x10 ∈ PEqualNP.HeptadCover.singerLines3 x11 → (x1.wires (PEqualNP.GenericRejection.incidenceInput {x10} {x11} ++ [x4.any fun (x13 : ℕ) => (PEqualNP.GenericRejection.incidenceInput {x10} {x11}).getD x13 Bool.false])).getD x2 Bool.false = Bool.true ∧ (x1.wires (PEqualNP.GenericRejection.incidenceInput {x10} {x11} ++ [x4.any fun (x13 : ℕ) => (PEqualNP.GenericRejection.incidenceInput {x10} {x11}).getD x13 Bool.false])).getD x3 Bool.false = Bool.true) → (∀ (x11 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x11 → (x1.wires (PEqualNP.GenericRejection.incidenceInput x11 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x11) ++ [x4.any fun (x13 : ℕ) => (PEqualNP.GenericRejection.incidenceInput x11 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x11)).getD x13 Bool.false])).getD x2 Bool.false = Bool.false ∨ (x1.wires (PEqualNP.GenericRejection.incidenceInput x11 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x11) ++ [x4.any fun (x13 : ℕ) => (PEqualNP.GenericRejection.incidenceInput x11 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x11)).getD x13 Bool.false])).getD x3 Bool.false = Bool.false) → (62 : ℕ) ≤ x1.size  := by
  intros x1 x2 x3 x4 hx hmono hrb hlt2 hlt3 hq hquad
  have hop : ∀ g ∈ x1.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa using (hmono g hg).1
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
  · exact lastAnd x1 x2 x3 x4 hx hmono hrb hlt2 hlt3 hq hquad hand
  · exact lastOr x1 x2 x3 x4 hx hmono hrb hlt2 hlt3 hq hquad har
