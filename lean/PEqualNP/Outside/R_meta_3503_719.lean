import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

-- Handle empty incidence graphs directly by an empty circuit reading wire m + n.
-- For nonempty C4-free bipartite incidence, construct the corresponding C4-free SimpleGraph,
-- pick a minimum bipartite vertex cover (A, B), normalize to a least TopForm circuit,
-- apply the TopForm lower bound |E| + |A| + |B| - 1 <= C.size, and build the two-level star cover.
theorem PEqualNP.Outside.R_meta_3503_719
    (hTopForm : ∀ (k : ℕ) (G : SimpleGraph (Fin k)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → G.edgeFinset.Nonempty → IsAO2 k C →
      circuitFun k C = graphFun G ∅ →
      ∃ C' : Circuit, IsLeastAO G C' ∧ TopForm G C' ∧ C'.size ≤ C.size)
    (hSize : ∀ (m n : ℕ) (I : Fin m → Fin n → Prop) [DecidableRel I]
      (G : SimpleGraph (Fin (m + n))) [DecidableRel G.Adj] (C : Circuit)
      (A : Finset (Fin m)) (B : Finset (Fin n)),
      (∀ a b : Fin (m + n), G.Adj a b ↔
        (∃ p l, I p l ∧ a = Fin.castAdd n p ∧ b = Fin.natAdd m l) ∨
        (∃ p l, I p l ∧ b = Fin.castAdd n p ∧ a = Fin.natAdd m l)) →
      NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C →
      (∀ p l, I p l → p ∈ A ∨ l ∈ B) →
      (∀ (A' : Finset (Fin m)) (B' : Finset (Fin n)),
        (∀ p l, I p l → p ∈ A' ∨ l ∈ B') → A.card + B.card ≤ A'.card + B'.card) →
      Fintype.card { pl : Fin m × Fin n // I pl.1 pl.2 } + A.card + B.card ≤
        C.size + 1)
    (hBuild : ∀ (m n : ℕ) (I : Fin m → Fin n → Prop) [DecidableRel I]
      (A : Finset (Fin m)) (B : Finset (Fin n)),
      (∃ p l, I p l) → (∀ p l, I p l → p ∈ A ∨ l ∈ B) →
      ∃ (D : Circuit) (P Q : Finset ℕ),
        IsAO2 (m + n) D ∧
        D.size + 1 ≤
          Fintype.card { pl : Fin m × Fin n // I pl.1 pl.2 } + A.card + B.card ∧
        (∀ z : Fin (m + n) → Bool, circuitFun (m + n) D z =
          decide (∃ p l, I p l ∧ z (Fin.castAdd n p) = true ∧ z (Fin.natAdd m l) = true)) ∧
        (∀ w ∈ P, w < m ∨ ∃ j < D.gates.length, w = m + n + j ∧
          (gateAt D j).op = GateOp.or ∧ ∀ u ∈ (gateAt D j).inputs, u ∈ P) ∧
        (∀ w ∈ Q, (m ≤ w ∧ w < m + n) ∨ ∃ j < D.gates.length, w = m + n + j ∧
          (gateAt D j).op = GateOp.or ∧ ∀ u ∈ (gateAt D j).inputs, u ∈ Q) ∧
        (∀ j < D.gates.length, (gateAt D j).op = GateOp.and →
          ∃ u v : ℕ, (gateAt D j).inputs = [u, v] ∧ ((u ∈ P ∧ v ∈ Q) ∨ (u ∈ Q ∧ v ∈ P)))) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Finset ℕ) (x11 : Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x12 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x12 = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x1 x14) = Bool.true)) ∧ x9.size ≤ x5.size ∧ (∀ x12 ∈ x10, x12 < x1 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x10) ∧ (∀ x12 ∈ x11, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x9.gates.length, x12 = x1 + x2 + x14 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x14).inputs, x15 ∈ x11) ∧ ∀ x12 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x15 : ℕ) (x16 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x12).inputs = [x15, x16] ∧ (x15 ∈ x10 ∧ x16 ∈ x11 ∨ x15 ∈ x11 ∧ x16 ∈ x10) := by
  classical
  intro m n I _ C hC4 hAO hEval
  by_cases hHasEdge : ∃ p l, I p l
  · let G : SimpleGraph (Fin (m + n)) :=
      SimpleGraph.fromRel fun a b =>
        ∃ (p : Fin m) (l : Fin n), I p l ∧ a = Fin.castAdd n p ∧ b = Fin.natAdd m l
    have hAdjIff : ∀ a b : Fin (m + n), G.Adj a b ↔
        (∃ p l, I p l ∧ a = Fin.castAdd n p ∧ b = Fin.natAdd m l) ∨
        (∃ p l, I p l ∧ b = Fin.castAdd n p ∧ a = Fin.natAdd m l) := by
      intro a b
      constructor
      · intro hab
        exact hab.2
      · intro h
        refine ⟨?_, h⟩
        intro heq
        rcases h with ⟨p, l, _, ha, hb⟩ | ⟨p, l, _, hb, ha⟩
        · have hv := congrArg Fin.val (ha.symm.trans (heq.trans hb))
          rw [Fin.val_castAdd, Fin.val_natAdd] at hv
          have hp := p.isLt
          omega
        · have hv := congrArg Fin.val (hb.symm.trans (heq.symm.trans ha))
          rw [Fin.val_castAdd, Fin.val_natAdd] at hv
          have hp := p.isLt
          omega
    have hNoC4 : NoFourCycle G := by
      intro a b hab
      by_contra hgt
      have hpair := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card)
      rcases hpair with ⟨w1, hw1, w2, hw2, hne⟩
      have h1 := (Finset.mem_filter.mp hw1).2
      have h2 := (Finset.mem_filter.mp hw2).2
      have ha1 := (hAdjIff a w1).mp h1.1
      have hb1 := (hAdjIff b w1).mp h1.2
      have ha2 := (hAdjIff a w2).mp h2.1
      have hb2 := (hAdjIff b w2).mp h2.2
      rcases ha1 with ⟨p1, l1, hI1, ha_p1, hw1_l1⟩ | ⟨p1, l1, hI1, hw1_p1, ha_l1⟩
      · rcases hb1 with ⟨q1, l1', hIb1, hb_q1, hw1_l1'⟩ | ⟨q1, l1', _, hw1_q1, _⟩
        · have hl1 : l1' = l1 := Fin.ext (by
            have hv := congrArg Fin.val (hw1_l1'.symm.trans hw1_l1)
            rw [Fin.val_natAdd, Fin.val_natAdd] at hv; omega)
          rw [hl1] at hIb1
          rcases ha2 with ⟨p2, l2, hI2, ha_p2, hw2_l2⟩ | ⟨_, _, _, _, ha_l2⟩
          · have hp2 : p2 = p1 := Fin.ext (by
              have hv := congrArg Fin.val (ha_p2.symm.trans ha_p1)
              rw [Fin.val_castAdd, Fin.val_castAdd] at hv; omega)
            rw [hp2] at hI2
            rcases hb2 with ⟨q2, l2', hIb2, hb_q2, hw2_l2'⟩ | ⟨q2, _, _, hw2_q2, _⟩
            · have hq2 : q2 = q1 := Fin.ext (by
                have hv := congrArg Fin.val (hb_q2.symm.trans hb_q1)
                rw [Fin.val_castAdd, Fin.val_castAdd] at hv; omega)
              have hl2 : l2' = l2 := Fin.ext (by
                have hv := congrArg Fin.val (hw2_l2'.symm.trans hw2_l2)
                rw [Fin.val_natAdd, Fin.val_natAdd] at hv; omega)
              rw [hq2, hl2] at hIb2
              have hpq : p1 ≠ q1 := by
                intro heq; apply hab; rw [ha_p1, hb_q1, heq]
              have hll : l1 ≠ l2 := by
                intro heq; apply hne; rw [hw1_l1, hw2_l2, heq]
              exact hC4 p1 q1 l1 l2 hpq hll ⟨hI1, hI2, hIb1, hIb2⟩
            · have hv := congrArg Fin.val (hw2_q2.symm.trans hw2_l2)
              rw [Fin.val_castAdd, Fin.val_natAdd] at hv; have := q2.isLt; omega
          · have hv := congrArg Fin.val (ha_p1.symm.trans ha_l2)
            rw [Fin.val_castAdd, Fin.val_natAdd] at hv; have := p1.isLt; omega
        · have hv := congrArg Fin.val (hw1_q1.symm.trans hw1_l1)
          rw [Fin.val_castAdd, Fin.val_natAdd] at hv; have := q1.isLt; omega
      · rcases hb1 with ⟨_, _, _, _, hw1_l1'⟩ | ⟨p1', l1', hIb1, hw1_p1', hb_l1'⟩
        · have hv := congrArg Fin.val (hw1_p1.symm.trans hw1_l1')
          rw [Fin.val_castAdd, Fin.val_natAdd] at hv; have := p1.isLt; omega
        · have hp1 : p1' = p1 := Fin.ext (by
            have hv := congrArg Fin.val (hw1_p1'.symm.trans hw1_p1)
            rw [Fin.val_castAdd, Fin.val_castAdd] at hv; omega)
          rw [hp1] at hIb1
          rcases ha2 with ⟨p2, _, _, ha_p2, _⟩ | ⟨p2, l2, hI2, hw2_p2, ha_l2⟩
          · have hv := congrArg Fin.val (ha_p2.symm.trans ha_l1)
            rw [Fin.val_castAdd, Fin.val_natAdd] at hv; have := p2.isLt; omega
          · have hl2 : l2 = l1 := Fin.ext (by
              have hv := congrArg Fin.val (ha_l2.symm.trans ha_l1)
              rw [Fin.val_natAdd, Fin.val_natAdd] at hv; omega)
            rw [hl2] at hI2
            rcases hb2 with ⟨_, _, _, _, hw2_l2'⟩ | ⟨p2', l2', hIb2, hw2_p2', hb_l2'⟩
            · have hv := congrArg Fin.val (hw2_p2.symm.trans hw2_l2')
              rw [Fin.val_castAdd, Fin.val_natAdd] at hv; have := p2.isLt; omega
            · have hp2 : p2' = p2 := Fin.ext (by
                have hv := congrArg Fin.val (hw2_p2'.symm.trans hw2_p2)
                rw [Fin.val_castAdd, Fin.val_castAdd] at hv; omega)
              have hl2' : l2' = l1' := Fin.ext (by
                have hv := congrArg Fin.val (hb_l2'.symm.trans hb_l1')
                rw [Fin.val_natAdd, Fin.val_natAdd] at hv; omega)
              rw [hp2, hl2'] at hIb2
              have hpp : p1 ≠ p2 := by
                intro heq; apply hne; rw [hw1_p1, hw2_p2, heq]
              have hll : l1 ≠ l1' := by
                intro heq; apply hab; rw [ha_l1, hb_l1', heq]
              exact hC4 p1 p2 l1 l1' hpp hll ⟨hI1, hIb1, hI2, hIb2⟩
    have hNonempty : G.edgeFinset.Nonempty := by
      rcases hHasEdge with ⟨p, l, hpl⟩
      refine ⟨s(Fin.castAdd n p, Fin.natAdd m l), ?_⟩
      exact SimpleGraph.mem_edgeFinset.mpr (G.mem_edgeSet.mpr ((hAdjIff _ _).mpr (Or.inl ⟨p, l, hpl, rfl, rfl⟩)))
    have hFunEq : circuitFun (m + n) C = graphFun G ∅ := by
      funext z
      rw [hEval z]
      change decide (∃ p l, I p l ∧ z (Fin.castAdd n p) = true ∧ z (Fin.natAdd m l) = true) =
        (decide (∃ a ∈ (∅ : Finset (Fin (m + n))), z a = true) ||
          decide (∃ u v, G.Adj u v ∧ z u = true ∧ z v = true))
      have hEmptyF : decide (∃ a ∈ (∅ : Finset (Fin (m + n))), z a = true) = false := by
        rw [decide_eq_false_iff_not]
        intro h
        rcases h with ⟨a, ha, _⟩
        exact Finset.notMem_empty a ha
      rw [hEmptyF, Bool.false_or]
      apply decide_eq_decide.mpr
      constructor
      · intro h
        rcases h with ⟨p, l, hpl, hp, hl⟩
        exact ⟨Fin.castAdd n p, Fin.natAdd m l, (hAdjIff _ _).mpr (Or.inl ⟨p, l, hpl, rfl, rfl⟩), hp, hl⟩
      · intro h
        rcases h with ⟨u, v, huv, hu, hv⟩
        rcases (hAdjIff u v).mp huv with ⟨p, l, hpl, rfl, rfl⟩ | ⟨p, l, hpl, rfl, rfl⟩
        · exact ⟨p, l, hpl, hu, hv⟩
        · exact ⟨p, l, hpl, hv, hu⟩
    have hNorm := hTopForm (m + n) G C hNoC4 hNonempty hAO hFunEq
    rcases hNorm with ⟨C', hLeast, hTop, hC'le⟩
    let covers : Finset (Finset (Fin m) × Finset (Fin n)) :=
      Finset.univ.filter (fun ab => ∀ p l, I p l → p ∈ ab.1 ∨ l ∈ ab.2)
    have hCovNe : covers.Nonempty := by
      refine ⟨(Finset.univ, ∅), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      intro p _ _
      exact Or.inl (Finset.mem_univ p)
    have hMin := Finset.exists_min_image covers (fun ab => ab.1.card + ab.2.card) hCovNe
    rcases hMin with ⟨ab, habMem, habMin⟩
    have habCov : ∀ p l, I p l → p ∈ ab.1 ∨ l ∈ ab.2 := (Finset.mem_filter.mp habMem).2
    have hMinProp : ∀ (A' : Finset (Fin m)) (B' : Finset (Fin n)),
        (∀ p l, I p l → p ∈ A' ∨ l ∈ B') → ab.1.card + ab.2.card ≤ A'.card + B'.card := by
      intro A' B' hAB'
      exact habMin (A', B') (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAB'⟩)
    have hLB := hSize m n I G C' ab.1 ab.2 hAdjIff hNoC4 hNonempty hLeast hTop habCov hMinProp
    have hBuilt := hBuild m n I ab.1 ab.2 hHasEdge habCov
    rcases hBuilt with ⟨D, P, Q, hDAO, hDsz, hDEval, hP, hQ, hAnd⟩
    refine ⟨D, P, Q, hDAO, hDEval, ?_, hP, hQ, hAnd⟩
    omega
  · refine ⟨⟨[], m + n⟩, ∅, ∅, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro g hg; cases hg
      · intro j hj; cases hj
      · intro g hg; cases hg
    · intro z
      have hLhs : circuitFun (m + n) ⟨[], m + n⟩ z = false := by
        change (List.ofFn z).getD (m + n) false = false
        rw [List.getD_eq_default _ _ (by rw [List.length_ofFn])]
      have hRhs : decide (∃ p l, I p l ∧ z (Fin.castAdd n p) = true ∧ z (Fin.natAdd m l) = true) = false := by
        rw [decide_eq_false_iff_not]
        intro h
        rcases h with ⟨p, l, hpl, _, _⟩
        exact hHasEdge ⟨p, l, hpl⟩
      rw [hLhs, hRhs]
    · exact Nat.zero_le _
    · intro w hw; exact absurd hw (Finset.notMem_empty w)
    · intro w hw; exact absurd hw (Finset.notMem_empty w)
    · intro j hj; cases hj
