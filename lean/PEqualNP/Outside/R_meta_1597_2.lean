import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1597_2 :
    (∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit),
       G = PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
       PEqualNP.TopForm.IsLeastAO G D → PEqualNP.TopForm.TopForm G D →
       let T : Finset ℕ := PEqualNP.TopForm.tops G D
       let C0 : Finset ℕ := PEqualNP.TopForm.centreless G D
       let J : Finset ℕ := PEqualNP.TopForm.junk G D
       let U : Finset (Sym2 (Fin 11)) := PEqualNP.TopForm.Ustar G D
       (∀ a ∈ T,
         let S : Fin 2 → Finset (Fin 11) := PEqualNP.TopForm.side D a
         (∀ u ∈ S 0, ∀ v ∈ S 1, G.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1)) →
       (∀ u v : Fin 11, s(u, v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ h ∈ J, PEqualNP.EdgeOwnership.gateVal 11 D a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches 11 D (PEqualNP.TopForm.opnd D a b) h ∧ PEqualNP.EdgeOwnership.gateVal 11 D h (PEqualNP.EdgeOwnership.pairInput u v) = true) →
       15 + (T \ C0).card + 2 * C0.card + J.card + (PEqualNP.TopForm.orN G D \ PEqualNP.TopForm.lam G D).card ≤ D.size + U.card →
       (∀ K : Finset (Fin 11), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K → K.card ≤ (T \ C0).card) →
       3 ≤ J.card → 22 ≤ D.size) →
    (∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit) (g1 g2 : ℕ),
       G = PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
       PEqualNP.TopForm.IsLeastAO G D → PEqualNP.TopForm.TopForm G D →
       let T : Finset ℕ := PEqualNP.TopForm.tops G D
       let C0 : Finset ℕ := PEqualNP.TopForm.centreless G D
       let U : Finset (Sym2 (Fin 11)) := PEqualNP.TopForm.Ustar G D
       (∀ a ∈ T,
         let S : Fin 2 → Finset (Fin 11) := PEqualNP.TopForm.side D a
         (∀ u ∈ S 0, ∀ v ∈ S 1, G.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1)) →
       (∀ u v : Fin 11, s(u, v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ h : ℕ, (h = g1 ∨ h = g2) ∧ PEqualNP.EdgeOwnership.gateVal 11 D a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches 11 D (PEqualNP.TopForm.opnd D a b) h ∧ PEqualNP.EdgeOwnership.gateVal 11 D h (PEqualNP.EdgeOwnership.pairInput u v) = true) →
       17 + (T \ C0).card + 2 * C0.card + (PEqualNP.TopForm.orN G D \ PEqualNP.TopForm.lam G D).card ≤ D.size + U.card →
       (∀ K : Finset (Fin 11), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K → K.card ≤ (T \ C0).card) →
       PEqualNP.TopForm.junk G D = {g1, g2} → PEqualNP.EdgeOwnership.InCone 11 D g1 g2 → 22 ≤ D.size) →
    (∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit) (g1 g2 : ℕ),
       G = PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
       PEqualNP.TopForm.IsLeastAO G D → PEqualNP.TopForm.TopForm G D →
       let T : Finset ℕ := PEqualNP.TopForm.tops G D
       let C0 : Finset ℕ := PEqualNP.TopForm.centreless G D
       let U : Finset (Sym2 (Fin 11)) := PEqualNP.TopForm.Ustar G D
       let ic : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone 11 D
       (∀ a ∈ T,
         let S : Fin 2 → Finset (Fin 11) := PEqualNP.TopForm.side D a
         (∀ u ∈ S 0, ∀ v ∈ S 1, G.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1)) →
       (∀ u v : Fin 11, s(u, v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ h : ℕ, (h = g1 ∨ h = g2) ∧ PEqualNP.EdgeOwnership.gateVal 11 D a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches 11 D (PEqualNP.TopForm.opnd D a b) h ∧ PEqualNP.EdgeOwnership.gateVal 11 D h (PEqualNP.EdgeOwnership.pairInput u v) = true) →
       17 + (T \ C0).card + 2 * C0.card + (PEqualNP.TopForm.orN G D \ PEqualNP.TopForm.lam G D).card ≤ D.size + U.card →
       (∀ K : Finset (Fin 11), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K → K.card ≤ (T \ C0).card) →
       g1 < g2 → PEqualNP.TopForm.junk G D = {g1, g2} → ¬ ic g1 g2 → ¬ ic g2 g1 → (∃ a ∈ T, ic g1 a ∧ ic g2 a) → 22 ≤ D.size) →
    (∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (D : PEqualNP.CircuitLowerBounds.Circuit) (g1 g2 : ℕ),
       G = PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
       PEqualNP.TopForm.IsLeastAO G D → PEqualNP.TopForm.TopForm G D →
       let T : Finset ℕ := PEqualNP.TopForm.tops G D
       let C0 : Finset ℕ := PEqualNP.TopForm.centreless G D
       let U : Finset (Sym2 (Fin 11)) := PEqualNP.TopForm.Ustar G D
       let ic : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone 11 D
       (∀ a ∈ T,
         let S : Fin 2 → Finset (Fin 11) := PEqualNP.TopForm.side D a
         (∀ u ∈ S 0, ∀ v ∈ S 1, G.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1)) →
       (∀ u v : Fin 11, s(u, v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ h : ℕ, (h = g1 ∨ h = g2) ∧ PEqualNP.EdgeOwnership.gateVal 11 D a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches 11 D (PEqualNP.TopForm.opnd D a b) h ∧ PEqualNP.EdgeOwnership.gateVal 11 D h (PEqualNP.EdgeOwnership.pairInput u v) = true) →
       17 + (T \ C0).card + 2 * C0.card + (PEqualNP.TopForm.orN G D \ PEqualNP.TopForm.lam G D).card ≤ D.size + U.card →
       (∀ K : Finset (Fin 11), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑U) K → K.card ≤ (T \ C0).card) →
       g1 < g2 → PEqualNP.TopForm.junk G D = {g1, g2} → ¬ ic g1 g2 → ¬ ic g2 g1 → (∀ a ∈ T, ic g1 a → ¬ ic g2 a) → 22 ≤ D.size) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → (∀ a ∈ PEqualNP.TopForm.tops G C, Disjoint (PEqualNP.TopForm.side (n := n) C a 0) (PEqualNP.TopForm.side (n := n) C a 1) ∧ (∀ u ∈ PEqualNP.TopForm.side (n := n) C a 0, ∀ v ∈ PEqualNP.TopForm.side (n := n) C a 1, G.Adj u v) ∧ ((PEqualNP.TopForm.side (n := n) C a 0).card ≤ 1 ∨ (PEqualNP.TopForm.side (n := n) C a 1).card ≤ 1)) ∧ ∀ u v : Fin n, s(u, v) ∈ PEqualNP.TopForm.Ustar G C → ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2, ∃ h ∈ PEqualNP.TopForm.junk G C, PEqualNP.EdgeOwnership.gateVal n C a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a b) h ∧ PEqualNP.EdgeOwnership.gateVal n C h (PEqualNP.EdgeOwnership.pairInput u v) = true) → (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C → G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card + 2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤ C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧ ∀ K : Finset (Fin n), PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K → K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO (PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D → PEqualNP.TopForm.TopForm (PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D → 2 ≤ (PEqualNP.TopForm.junk (PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]) D).card → 22 ≤ D.size := by
  intro c1 c2 c3 c4 h1 h2 D hL hT hj2
  set G0 := PEqualNP.EdgeOwnership.edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
  change 2 ≤ (PEqualNP.TopForm.junk G0 D).card at hj2
  have hnf : PEqualNP.TopForm.NoFourCycle G0 := by decide
  have hne : G0.edgeFinset.Nonempty := by decide
  have hecard : G0.edgeFinset.card = 16 := by decide
  obtain ⟨hstar0, hoff⟩ := h1 11 G0 D hnf hne hL hT
  obtain ⟨hcnt, hcov⟩ := h2 11 G0 D hnf hne hL hT
  rw [hecard] at hcnt
  have hstar : ∀ a ∈ PEqualNP.TopForm.tops G0 D,
      let S : Fin 2 → Finset (Fin 11) := PEqualNP.TopForm.side D a
      (∀ u ∈ S 0, ∀ v ∈ S 1, G0.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1) := by
    intro a ha
    exact (hstar0 a ha).2
  by_cases hj3 : 3 ≤ (PEqualNP.TopForm.junk G0 D).card
  · have hcnt1 : 15 + (PEqualNP.TopForm.tops G0 D \ PEqualNP.TopForm.centreless G0 D).card +
        2 * (PEqualNP.TopForm.centreless G0 D).card + (PEqualNP.TopForm.junk G0 D).card +
        (PEqualNP.TopForm.orN G0 D \ PEqualNP.TopForm.lam G0 D).card ≤
        D.size + (PEqualNP.TopForm.Ustar G0 D).card := by omega
    exact c1 G0 D rfl hL hT hstar hoff hcnt1 hcov hj3
  · have hj_eq2 : (PEqualNP.TopForm.junk G0 D).card = 2 := by omega
    have hcnt2 : 17 + (PEqualNP.TopForm.tops G0 D \ PEqualNP.TopForm.centreless G0 D).card +
        2 * (PEqualNP.TopForm.centreless G0 D).card +
        (PEqualNP.TopForm.orN G0 D \ PEqualNP.TopForm.lam G0 D).card ≤
        D.size + (PEqualNP.TopForm.Ustar G0 D).card := by omega
    obtain ⟨x1, x2, hne12, hjset0⟩ := Finset.card_eq_two.mp hj_eq2
    have hord : ∃ g1 g2 : ℕ, g1 < g2 ∧ PEqualNP.TopForm.junk G0 D = {g1, g2} := by
      rcases lt_or_gt_of_ne hne12 with hlt | hlt
      · exact ⟨x1, x2, hlt, hjset0⟩
      · rw [Finset.pair_comm] at hjset0
        exact ⟨x2, x1, hlt, hjset0⟩
    obtain ⟨g1, g2, hlt12, hjset⟩ := hord
    have hoffPair : ∀ (a0 b0 : ℕ), PEqualNP.TopForm.junk G0 D = {a0, b0} →
        ∀ u v : Fin 11, s(u, v) ∈ PEqualNP.TopForm.Ustar G0 D →
          ∃ a ∈ PEqualNP.TopForm.tops G0 D, ∃ b : Fin 2, ∃ h : ℕ, (h = a0 ∨ h = b0) ∧
            PEqualNP.EdgeOwnership.gateVal 11 D a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧
            PEqualNP.CleanedNonEdge.OrReaches 11 D (PEqualNP.TopForm.opnd D a b) h ∧
            PEqualNP.EdgeOwnership.gateVal 11 D h (PEqualNP.EdgeOwnership.pairInput u v) = true := by
      intro a0 b0 hjs u v huv
      obtain ⟨a, ha, b, h, hh, hv1, hor, hv2⟩ := hoff u v huv
      rw [hjs] at hh
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      exact ⟨a, ha, b, h, hh, hv1, hor, hv2⟩
    by_cases hc12 : PEqualNP.EdgeOwnership.InCone 11 D g1 g2
    · exact c2 G0 D g1 g2 rfl hL hT hstar (hoffPair g1 g2 hjset) hcnt2 hcov hjset hc12
    · by_cases hc21 : PEqualNP.EdgeOwnership.InCone 11 D g2 g1
      · have hjset' : PEqualNP.TopForm.junk G0 D = {g2, g1} := by rw [Finset.pair_comm]; exact hjset
        exact c2 G0 D g2 g1 rfl hL hT hstar (hoffPair g2 g1 hjset') hcnt2 hcov hjset' hc21
      · by_cases hsh : ∃ a ∈ PEqualNP.TopForm.tops G0 D, PEqualNP.EdgeOwnership.InCone 11 D g1 a ∧ PEqualNP.EdgeOwnership.InCone 11 D g2 a
        · exact c3 G0 D g1 g2 rfl hL hT hstar (hoffPair g1 g2 hjset) hcnt2 hcov hlt12 hjset hc12 hc21 hsh
        · refine c4 G0 D g1 g2 rfl hL hT hstar (hoffPair g1 g2 hjset) hcnt2 hcov hlt12 hjset hc12 hc21 ?_
          intro a ha hg1
          exact fun hg2 => hsh ⟨a, ha, hg1, hg2⟩
