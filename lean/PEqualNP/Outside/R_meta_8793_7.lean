import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

-- A cut of the two-or-more-junk case of the order-3 plane bound.
-- ledger: the checked L_meta_7862 (the ledger inequality and the cover bound).
-- core: what is left. A circuit with at most 63 gates is assumed, and three facts that follow
-- from the ledger on this plane are handed over as hypotheses: the ledger with 52 edges, the
-- count 52 <= 4 * tops + uncovered (a vertex covers at most 4 edges), and their consequence
-- 4 * (junk + 2 * centreless + other ORs) + 4 <= 5 * uncovered. So a counterexample needs many
-- uncovered edges for each junk gate; bounding the uncovered edges closes the case.
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_8793_7
    (ledger : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → (∃ u v : Fin n, G.Adj u v) → IsLeastAO G C → TopForm G C →
      G.edgeSet.ncard + (tops G C \ centreless G C).card + 2 * (centreless G C).card +
          (junk G C).card + (orN G C \ lam G C).card ≤ C.size + (Ustar G C).card + 1 ∧
        ∀ K : Finset (Fin n), NestedCover.IsMinCover (G.deleteEdges ↑(Ustar G C)) K →
          K.card ≤ (tops G C \ centreless G C).card)
    (core : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit),
      G = SimpleGraph.fromRel (fun a b : Fin 26 => a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) →
      IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card → C.size ≤ 63 →
      52 + (tops G C \ centreless G C).card + 2 * (centreless G C).card + (junk G C).card +
          (orN G C \ lam G C).card ≤ C.size + (Ustar G C).card + 1 →
      52 ≤ 4 * (tops G C \ centreless G C).card + (Ustar G C).card →
      4 * ((junk G C).card + 2 * (centreless G C).card + (orN G C \ lam G C).card) + 4 ≤
          5 * (Ustar G C).card → False) :
    ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), (x1 = SimpleGraph.fromRel fun (x4 x5 : Fin (26 : ℕ)) => ↑x4 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.TopForm x1 x3 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x3).card → (64 : ℕ) ≤ x3.size := by
  intro G inst C hG hL hT hJ
  have four : ∀ a w1 : Fin 26, ((a.val < 13 ∧ 13 ≤ w1.val ∧ (a.val + w1.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∨ (w1.val < 13 ∧ 13 ≤ a.val ∧ (w1.val + a.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ))) → ∀ b : Fin 26, a ≠ b → ((b.val < 13 ∧ 13 ≤ w1.val ∧ (b.val + w1.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∨ (w1.val < 13 ∧ 13 ≤ b.val ∧ (w1.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ))) →
      ∀ w2 : Fin 26, ((a.val < 13 ∧ 13 ≤ w2.val ∧ (a.val + w2.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∨ (w2.val < 13 ∧ 13 ≤ a.val ∧ (w2.val + a.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ))) → ((b.val < 13 ∧ 13 ≤ w2.val ∧ (b.val + w2.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∨ (w2.val < 13 ∧ 13 ≤ b.val ∧ (w2.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ))) → w1 = w2 := by
    decide +kernel
  have hpairs : ((Finset.univ : Finset (Fin 26 × Fin 26)).filter
      fun q : Fin 26 × Fin 26 => (q.1.val < 13 ∧ 13 ≤ q.2.val ∧ (q.1.val + q.2.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ))).card = 52 := by
    decide +kernel
  have hdeg : ∀ v : Fin 26, ((Finset.univ : Finset (Fin 26)).filter fun w : Fin 26 => ((v.val < 13 ∧ 13 ≤ w.val ∧ (v.val + w.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∨ (w.val < 13 ∧ 13 ≤ v.val ∧ (w.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)))).card ≤ 4 := by
    decide +kernel
  have adj : ∀ u v : Fin 26, G.Adj u v ↔ ((u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∨ (v.val < 13 ∧ 13 ≤ u.val ∧ (v.val + u.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ))) := by
    intro u v
    rw [hG, SimpleGraph.fromRel_adj]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rintro rfl
      rcases h with h | h <;> omega
  have hno : NoFourCycle G := by
    intro a b hab
    rw [Finset.card_le_one]
    intro w1 h1 w2 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact four a w1 ((adj a w1).1 h1.1) b hab ((adj b w1).1 h1.2) w2 ((adj a w2).1 h2.1)
      ((adj b w2).1 h2.2)
  have hedge : ∃ u v : Fin 26, G.Adj u v := ⟨0, 13, (adj 0 13).2 (Or.inl (by decide))⟩
  obtain ⟨hledger, hcover⟩ := ledger 26 G C hno hedge hL hT
  -- at least 52 edges
  have hE : 52 ≤ G.edgeFinset.card := by
    rw [← hpairs]
    refine Finset.card_le_card_of_injOn (fun q : Fin 26 × Fin 26 => s(q.1, q.2)) ?_ ?_
    · intro q hq
      have hq' : (q.1.val < 13 ∧ 13 ≤ q.2.val ∧ (q.1.val + q.2.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) := by
        simpa using hq
      simp only [Finset.mem_coe]
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact (adj q.1 q.2).2 (Or.inl hq')
    · intro q hq q' hq' heq
      have h1 : (q.1.val < 13 ∧ 13 ≤ q.2.val ∧ (q.1.val + q.2.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) := by
        simpa using hq
      have h2 : (q'.1.val < 13 ∧ 13 ≤ q'.2.val ∧ (q'.1.val + q'.2.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) := by
        simpa using hq'
      have heq' : s(q.1, q.2) = s(q'.1, q'.2) := heq
      rw [Sym2.eq_iff] at heq'
      rcases heq' with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Prod.ext e1 e2
      · exfalso
        have := congrArg Fin.val e1
        omega
  have hE' : 52 ≤ G.edgeSet.ncard := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    exact hE
  -- a least vertex cover of the covered part exists
  have hex : ∃ K : Finset (Fin 26), NestedCover.IsMinCover (G.deleteEdges ↑(Ustar G C)) K := by
    classical
    have hcov : ((Finset.univ : Finset (Finset (Fin 26))).filter fun T : Finset (Fin 26) =>
        (G.deleteEdges ↑(Ustar G C)).IsVertexCover (↑T : Set (Fin 26))).Nonempty := by
      exact ⟨Finset.univ, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun v w _ =>
        Or.inl (Finset.mem_coe.2 (Finset.mem_univ v))⟩⟩
    obtain ⟨K, hK, hmin⟩ := Finset.exists_min_image _ (fun T : Finset (Fin 26) => T.card) hcov
    exact ⟨K, (Finset.mem_filter.1 hK).2, fun T' hT' =>
      hmin T' (Finset.mem_filter.2 ⟨Finset.mem_univ _, hT'⟩)⟩
  obtain ⟨K, hK⟩ := hex
  have hK2 := hcover K hK
  -- every edge outside the uncovered set meets K, and a vertex lies on at most 4 edges
  have hsub : G.edgeFinset \ Ustar G C ⊆
      K.biUnion (fun v : Fin 26 => (((Finset.univ : Finset (Fin 26)).filter fun w : Fin 26 => ((v.val < 13 ∧ 13 ≤ w.val ∧ (v.val + w.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∨ (w.val < 13 ∧ 13 ≤ v.val ∧ (w.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ))))).image (fun w : Fin 26 => s(v, w))) := by
    intro e
    refine Sym2.ind (fun v w => ?_) e
    intro he
    rw [Finset.mem_sdiff] at he
    obtain ⟨heE, heU⟩ := he
    have hvw : G.Adj v w := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at heE
      exact heE
    have hH : (G.deleteEdges ↑(Ustar G C)).Adj v w := by
      rw [SimpleGraph.deleteEdges_adj]
      exact ⟨hvw, fun h => heU (Finset.mem_coe.1 h)⟩
    rw [Finset.mem_biUnion]
    rcases hK.1 hH with hv | hw
    · exact ⟨v, Finset.mem_coe.1 hv, Finset.mem_image.2
        ⟨w, Finset.mem_filter.2 ⟨Finset.mem_univ _, (adj v w).1 hvw⟩, rfl⟩⟩
    · exact ⟨w, Finset.mem_coe.1 hw, Finset.mem_image.2
        ⟨v, Finset.mem_filter.2 ⟨Finset.mem_univ _, (adj w v).1 hvw.symm⟩, Sym2.eq_swap⟩⟩
  have hc1 : (G.edgeFinset \ Ustar G C).card ≤ 4 * K.card := by
    refine (Finset.card_le_card hsub).trans ?_
    refine Finset.card_biUnion_le.trans ?_
    refine (Finset.sum_le_sum (fun v _ => Finset.card_image_le.trans (hdeg v))).trans ?_
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hc2 : G.edgeFinset.card ≤ (G.edgeFinset \ Ustar G C).card + (Ustar G C).card :=
    Finset.card_le_card_sdiff_add_card
  by_contra hlt
  have hs : C.size ≤ 63 := by omega
  exact core G C hG hL hT hJ hs (by omega) (by omega) (by omega)
