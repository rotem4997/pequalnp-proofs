import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Data.Fintype.Powerset
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

-- Prove the exact residual vertex-cover bounds on G11 inside the reduction
-- (7 <= K.card + U.card for all U, and 8 <= K.card + U.card when 4 <= U.card),
-- discharging U.card <= 1 directly and splitting into U.card = 2, U.card = 3, and 4 <= U.card.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2258_47 :
    (∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (D : Circuit),
      G = edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
        (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
      IsLeastAO G D → TopForm G D →
      (∀ a ∈ tops G D, let S : Fin 2 → Finset (Fin 11) := side D a
        (∀ u ∈ S 0, ∀ v ∈ S 1, G.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1)) →
      (∀ u v : Fin 11, s(u, v) ∈ Ustar G D → ∃ a ∈ tops G D, ∃ b : Fin 2, ∃ h ∈ junk G D,
        gateVal 11 D a (pairInput u v) = true ∧ OrReaches 11 D (opnd D a b) h ∧
        gateVal 11 D h (pairInput u v) = true) →
      15 + (tops G D \ centreless G D).card + 2 * (centreless G D).card + (junk G D).card +
        (orN G D \ lam G D).card ≤ D.size + (Ustar G D).card →
      (Ustar G D).card = 2 → 5 ≤ (tops G D \ centreless G D).card → 3 ≤ (junk G D).card →
      22 ≤ D.size) →
    (∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (D : Circuit),
      G = edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
        (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
      IsLeastAO G D → TopForm G D →
      (∀ a ∈ tops G D, let S : Fin 2 → Finset (Fin 11) := side D a
        (∀ u ∈ S 0, ∀ v ∈ S 1, G.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1)) →
      (∀ u v : Fin 11, s(u, v) ∈ Ustar G D → ∃ a ∈ tops G D, ∃ b : Fin 2, ∃ h ∈ junk G D,
        gateVal 11 D a (pairInput u v) = true ∧ OrReaches 11 D (opnd D a b) h ∧
        gateVal 11 D h (pairInput u v) = true) →
      15 + (tops G D \ centreless G D).card + 2 * (centreless G D).card + (junk G D).card +
        (orN G D \ lam G D).card ≤ D.size + (Ustar G D).card →
      (Ustar G D).card = 3 → 4 ≤ (tops G D \ centreless G D).card → 3 ≤ (junk G D).card →
      22 ≤ D.size) →
    (∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (D : Circuit),
      G = edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
        (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
      IsLeastAO G D → TopForm G D →
      let T := tops G D
      let V := centreless G D
      let J := junk G D
      let U := Ustar G D
      (∀ a ∈ T, let S : Fin 2 → Finset (Fin 11) := side D a
        (∀ u ∈ S 0, ∀ v ∈ S 1, G.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1)) →
      (∀ u v : Fin 11, s(u, v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ h ∈ J,
        gateVal 11 D a (pairInput u v) = true ∧ OrReaches 11 D (opnd D a b) h ∧
        gateVal 11 D h (pairInput u v) = true) →
      15 + (T \ V).card + 2 * V.card + J.card + (orN G D \ lam G D).card ≤ D.size + U.card →
      (∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K → K.card ≤ (T \ V).card) →
      4 ≤ U.card → 8 ≤ (T \ V).card + U.card → 3 ≤ J.card → 22 ≤ D.size) →
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x7 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x8 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x9 : Finset ℕ := PEqualNP.TopForm.junk x1 x3;         have x10 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         (∀ x11 ∈ x7,             have x13 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x11;             (∀ x14 ∈ x13 (0 : Fin (2 : ℕ)), ∀ x16 ∈ x13 (1 : Fin (2 : ℕ)), x1.Adj x14 x16) ∧ ((x13 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x13 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x12 x13 : Fin (11 : ℕ)), s(x12, x13) ∈ x10 → ∃ x15 ∈ x7, ∃ (x16 : Fin (2 : ℕ)), ∃ x17 ∈ x9, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x15 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x15 x16) x17 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true) → (15 : ℕ) + (x7 \ x8).card + (2 : ℕ) * x8.card + x9.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x10.card → (∀ (x14 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x10) x14 → x14.card ≤ (x7 \ x8).card) → (3 : ℕ) ≤ x9.card → (22 : ℕ) ≤ x3.size := by
  intro hTwo hThree hFour G _ D hG hLeast hTop
  dsimp only
  intro hStars hOff hCount hCoverBound hJunk
  let rawPairs : List (ℕ × ℕ) :=
    [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
     (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
  let edgePairs : Finset (Fin 11 × Fin 11) :=
    {(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
     (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)}
  have hPairsAdj : ∀ p ∈ edgePairs, (edgeGraph 11 rawPairs).Adj p.1 p.2 := by decide
  have hPairsLt : ∀ p ∈ edgePairs, p.1 < p.2 := by decide
  have hCheckAll : ∀ K : Finset (Fin 11),
      7 ≤ K.card + (edgePairs.filter (fun p => p.1 ∉ K ∧ p.2 ∉ K)).card ∧
      (K.card ≤ 3 → 8 ≤ K.card + (edgePairs.filter (fun p => p.1 ∉ K ∧ p.2 ∉ K)).card) := by
    decide
  classical
  let U := Ustar G D
  let H := G.deleteEdges (↑U : Set (Sym2 (Fin 11)))
  let covers : Finset (Finset (Fin 11)) :=
    Finset.univ.filter (fun K : Finset (Fin 11) => H.IsVertexCover (↑K : Set (Fin 11)))
  have hCovers : covers.Nonempty := by
    refine ⟨(Finset.univ : Finset (Fin 11)), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    intro u _ _
    exact Or.inl (Finset.mem_univ u)
  exact Exists.elim (Finset.exists_min_image covers Finset.card hCovers) fun K hK_rest => by
    have hKMin : IsMinCover H K :=
      ⟨(Finset.mem_filter.mp hK_rest.1).2, fun A hA =>
        hK_rest.2 A (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩)⟩
    have hKT : K.card ≤ (tops G D \ centreless G D).card := hCoverBound K hKMin
    let missed : Finset (Fin 11 × Fin 11) := edgePairs.filter (fun p => p.1 ∉ K ∧ p.2 ∉ K)
    let toSym : Fin 11 × Fin 11 → Sym2 (Fin 11) := fun p => s(p.1, p.2)
    have hSubU : missed.image toSym ⊆ U := by
      intro e he
      exact Exists.elim (Finset.mem_image.mp he) fun p hp => by
        rw [← hp.2]
        have hp_mem := (Finset.mem_filter.mp hp.1).1
        have hp_not := (Finset.mem_filter.mp hp.1).2
        have hadjG : G.Adj p.1 p.2 := by rw [hG]; exact hPairsAdj p hp_mem
        by_contra hnotU
        have hadjH : H.Adj p.1 p.2 := SimpleGraph.deleteEdges_adj.mpr ⟨hadjG, hnotU⟩
        exact (hKMin.1 hadjH).elim hp_not.1 hp_not.2
    have hInjSym : Set.InjOn toSym ↑missed := by
      intro p1 h1 p2 h2 heq
      have lt1 := hPairsLt p1 (Finset.mem_filter.mp h1).1
      have lt2 := hPairsLt p2 (Finset.mem_filter.mp h2).1
      exact (Sym2.eq_iff.mp heq).elim
        (fun h => Prod.ext h.1 h.2)
        (fun h => absurd (lt_trans (h.1 ▸ lt1) (h.2 ▸ lt2)) (lt_irrefl _))
    have hMissedLeU : missed.card ≤ U.card := by
      rw [← Finset.card_image_of_injOn hInjSym]
      exact Finset.card_le_card hSubU
    have hChk := hCheckAll K
    rw [Finset.filter_congr_decidable] at hChk
    have h7 : 7 ≤ K.card + U.card := by
      have h7m : 7 ≤ K.card + missed.card := hChk.1
      omega
    change 15 + (tops G D \ centreless G D).card + 2 * (centreless G D).card + (junk G D).card +
      (orN G D \ lam G D).card ≤ D.size + U.card at hCount
    change 3 ≤ (junk G D).card at hJunk
    by_cases hle1 : U.card ≤ 1
    · omega
    · by_cases heq2 : U.card = 2
      · exact hTwo G D hG hLeast hTop hStars hOff hCount heq2 (by omega) hJunk
      · by_cases heq3 : U.card = 3
        · exact hThree G D hG hLeast hTop hStars hOff hCount heq3 (by omega) hJunk
        · have hge4 : 4 ≤ U.card := by omega
          have h8 : 8 ≤ (tops G D \ centreless G D).card + U.card := by
            by_cases hk3 : K.card ≤ 3
            · have h8m : 8 ≤ K.card + missed.card := hChk.2 hk3
              omega
            · omega
          exact hFour G D hG hLeast hTop hStars hOff hCount hCoverBound hge4 h8 hJunk
