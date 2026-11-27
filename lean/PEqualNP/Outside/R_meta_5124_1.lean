import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_5124_1
    (essential : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → G.support.ncard ≤ C.size + 1)
    (core : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty → ∀ (C : Circuit) (H : SimpleGraph (Fin n)),
      IsLeastAO G C → TopForm G C → H ≤ G.deleteEdges (starEdges G C : Set (Sym2 (Fin n))) →
      (∀ v : Fin n, (H.neighborSet v).ncard = 0 ∨ 3 ≤ (H.neighborSet v).ncard) →
      (∀ u v : Fin n, s(u,v) ∈ H.edgeSet → ∀ w < n + C.gates.length,
        v ∈ orIn n C w →
          (2 ≤ (orIn n C w).card → ∃ z ∈ orIn n C w, ¬ G.Adj u z) ∧
          (3 ≤ (orIn n C w).card → 2 ≤ ((orIn n C w).filter fun z => ¬ G.Adj u z).card)) →
      H.edgeSet.ncard ≤ c * (C.size + 1)) :
  ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → ∀ x10 ⊆ PEqualNP.TopForm.Ustar x3 x7, (∀ (x12 x13 : Fin x2), s(x12, x13) ∈ x10 → ∀ x15 < x2 + x7.gates.length, x13 ∈ PEqualNP.TopForm.orIn x2 x7 x15 → ((2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 x15).card → ∃ x19 ∈ PEqualNP.TopForm.orIn x2 x7 x15, ¬x3.Adj x12 x19) ∧ ((3 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 x15).card → (2 : ℕ) ≤ {x19 ∈ PEqualNP.TopForm.orIn x2 x7 x15 | ¬x3.Adj x12 x19}.card)) → x10.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨c, hCore⟩ := core
  refine ⟨c + 2, ?_⟩
  intro n G _ hGirth hEdge C hLeast hTop S hSU hGuard
  classical
  have edgeCount (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
      F.edgeSet.ncard = F.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset,Set.ncard_coe_finset]
  have peel (p : ℕ) : ∀ (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      F.support.ncard = p →
      ∃ H : SimpleGraph (Fin n), H ≤ F ∧
        (∀ v : Fin n, (H.neighborSet v).ncard = 0 ∨ 3 ≤ (H.neighborSet v).ncard) ∧
        F.edgeSet.ncard ≤ H.edgeSet.ncard + 2 * p := by
    induction p using Nat.strong_induction_on with
    | ind p smaller =>
      intro F _ hF
      by_cases h : ∀ v : Fin n, (F.neighborSet v).ncard = 0 ∨ 3 ≤ (F.neighborSet v).ncard
      · exact ⟨F,le_rfl,h,by omega⟩
      · push Not at h
        obtain ⟨v,hv0,hv2⟩ := h
        have hDeg := F.ncard_neighborSet v
        have hvPos : 0 < F.degree v := by omega
        have hv : v ∈ F.support := by
          by_contra hn
          have hz : F.neighborSet v = ∅ := by
            apply Set.eq_empty_iff_forall_notMem.mpr
            intro w hw
            exact hn ⟨w,hw⟩
          exact hv0 (by rw [hz,Set.ncard_empty])
        have hPpos : 0 < F.support.ncard := by
          rw [← Set.fintypeCard_eq_ncard]
          exact Fintype.card_pos_iff.mpr ⟨⟨v,hv⟩⟩
        let R := F.deleteIncidenceSet v
        have hDrop : R.support.ncard ≤ F.support.ncard - 1 := by
          simpa only [Set.fintypeCard_eq_ncard] using F.card_support_deleteIncidenceSet hv
        obtain ⟨H,hHR,hMin,hH⟩ := smaller R.support.ncard (by omega) R rfl
        refine ⟨H,hHR.trans (F.deleteIncidenceSet_le v),hMin,?_⟩
        have hRemoved : R.edgeFinset.card = F.edgeFinset.card - F.degree v :=
          F.card_edgeFinset_deleteIncidenceSet v
        have hLe : F.degree v ≤ F.edgeFinset.card := by
          rw [← F.card_incidenceFinset_eq_degree v]
          exact Finset.card_le_card (F.incidenceFinset_subset v)
        rw [edgeCount R] at hH
        rw [edgeCount F]
        omega
  have hSG : S ⊆ G.edgeFinset := fun e he => (Finset.mem_sdiff.mp (hSU he)).1
  let D := G.deleteEdges ((G.edgeFinset \ S : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))
  have hDEdges : D.edgeFinset = S := by
    change (G.deleteEdges ((G.edgeFinset \ S : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))).edgeFinset = S
    rw [SimpleGraph.edgeFinset_deleteEdges]
    ext e
    simp only [Finset.mem_sdiff]
    constructor
    · rintro ⟨heG, hNot⟩
      by_contra heS
      exact hNot ⟨heG, heS⟩
    · intro heS
      exact ⟨hSG heS, fun h => h.2 heS⟩
  obtain ⟨H, hHD, hMin, hPeel⟩ := peel D.support.ncard D rfl
  have hDSupport : D.support ⊆ G.support := by
    intro v hv
    obtain ⟨w, hw⟩ := hv
    exact ⟨w, (G.deleteEdges_le _) hw⟩
  have hHSub : H ≤ G.deleteEdges (starEdges G C : Set (Sym2 (Fin n))) := by
    apply SimpleGraph.edgeFinset_subset_edgeFinset.mp
    rw [SimpleGraph.edgeFinset_deleteEdges]
    intro e he
    have hd := SimpleGraph.edgeFinset_mono hHD he
    rw [hDEdges] at hd
    exact hSU hd
  have hHGuard : ∀ u v : Fin n, s(u,v) ∈ H.edgeSet → ∀ w < n + C.gates.length,
      v ∈ orIn n C w →
        (2 ≤ (orIn n C w).card → ∃ z ∈ orIn n C w, ¬ G.Adj u z) ∧
        (3 ≤ (orIn n C w).card → 2 ≤ ((orIn n C w).filter fun z => ¬ G.Adj u z).card) := by
    intro u v huv
    have hH : s(u,v) ∈ H.edgeFinset := by simpa using huv
    have hD := SimpleGraph.edgeFinset_mono hHD hH
    rw [hDEdges] at hD
    exact hGuard u v hD
  have hBound := hCore n G hGirth hEdge C H hLeast hTop hHSub hMin hHGuard
  have hSupport := (Set.ncard_le_ncard hDSupport).trans (essential n G C hLeast)
  have hCount : D.edgeSet.ncard = S.card := by rw [edgeCount D, hDEdges]
  rw [hCount] at hPeel
  rw [Nat.add_mul]
  omega
