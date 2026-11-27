import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- The circuit is empty or its last gate is one of the two allowed kinds, and past the end of the
-- gate list `gateAt` reads the default OR gate. So the gate at index `size - 1` is an AND in one
-- case and an OR in the other, and the step is asked once for each of the two cases.
theorem PEqualNP.Outside.R_meta_6043_1
    (lastAnd :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   ∀ x2 ∈ [[(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)]],     PEqualNP.MetaComplexity.Monotone2 x1 →       PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x1 →         have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) =>           have x8 : List Bool := (List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x6)) ++ List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x7);           x1.eval (x8 ++ [x2.any fun (x9 : ℕ) => x8.getD x9 Bool.false]);         (∀ (x7 x8 : Fin (13 : ℕ)), x7 ∈ PEqualNP.HeptadCover.singerLines3 x8 → x6 {x7} {x8} = Bool.true) → (∀ (x8 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x8 → x6 x8 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x8) = Bool.false) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.and → (63 : ℕ) ≤ x1.size)
    (lastOr :
      ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   ∀ x2 ∈ [[(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)]],     PEqualNP.MetaComplexity.Monotone2 x1 →       PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x1 →         have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) =>           have x8 : List Bool := (List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x6)) ++ List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x7);           x1.eval (x8 ++ [x2.any fun (x9 : ℕ) => x8.getD x9 Bool.false]);         (∀ (x7 x8 : Fin (13 : ℕ)), x7 ∈ PEqualNP.HeptadCover.singerLines3 x8 → x6 {x7} {x8} = Bool.true) → (∀ (x8 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x8 → x6 x8 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x8) = Bool.false) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or → (63 : ℕ) ≤ x1.size) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   ∀ x2 ∈ [[(0 : ℕ), (13 : ℕ)], [(0 : ℕ), (14 : ℕ)]],     PEqualNP.MetaComplexity.Monotone2 x1 →       PEqualNP.MetaComplexity.NestedCover.ReadsBack (27 : ℕ) x1 →         have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) =>           have x8 : List Bool := (List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x6)) ++ List.ofFn fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 ∈ x7);           x1.eval (x8 ++ [x2.any fun (x9 : ℕ) => x8.getD x9 Bool.false]);         (∀ (x7 x8 : Fin (13 : ℕ)), x7 ∈ PEqualNP.HeptadCover.singerLines3 x8 → x6 {x7} {x8} = Bool.true) → (∀ (x8 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x8 → x6 x8 (PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x8) = Bool.false) → (63 : ℕ) ≤ x1.size  := by
  intros x1 x2 hx hmono hrb h6 hq hquad
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
  · exact lastAnd x1 x2 hx hmono hrb hq hquad hand
  · exact lastOr x1 x2 hx hmono hrb hq hquad har
