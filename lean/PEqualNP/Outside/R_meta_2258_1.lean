import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

-- The graph bound and the path from a junk AND to a top rule out at most two uncovered edges.
-- For larger uncovered sets, charge the remaining cover vertices together with those edges.
theorem PEqualNP.Outside.R_meta_2258_1
    (hGraph :
      let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6),
        (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
      ∀ (U : Finset (Sym2 (Fin 11))) (K : Finset (Fin 11)),
        (G.deleteEdges ↑U).IsVertexCover (↑K : Set (Fin 11)) → 7 ≤ K.card + U.card)
    (hTrace :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit),
        (∀ g ∈ D.gates, g.inputs.length = 2) →
        ∀ a ∈ tops G D, ∀ b : Fin 2, ∀ h ∈ junk G D,
          OrReaches n D (opnd D a b) h →
            a ∈ centreless G D ∨ (orN G D \ lam G D).Nonempty)
    (hCharge :
      ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (D : Circuit),
        G = edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6),
          (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
        IsLeastAO G D → TopForm G D →
        let U := Ustar G D
        let J := junk G D
        let V := centreless G D
        let T := tops G D
        let R := orN G D \ lam G D
        (∀ a ∈ T, let S : Fin 2 → Finset (Fin 11) := side D a
          (∀ u ∈ S 0, ∀ v ∈ S 1, G.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1)) →
        (∀ u v : Fin 11, s(u, v) ∈ U → ∃ a ∈ T, ∃ b : Fin 2, ∃ h ∈ J,
          gateVal 11 D a (pairInput u v) = true ∧ OrReaches 11 D (opnd D a b) h ∧
          gateVal 11 D h (pairInput u v) = true) →
        3 ≤ U.card → 3 ≤ J.card → D.size ≤ 21 →
        ∃ K A : Finset (Fin 11),
          IsMinCover (G.deleteEdges ↑U) K ∧
          (∀ u v : Fin 11, s(u, v) ∈ U → u ∈ K ∪ A ∨ v ∈ K ∪ A) ∧
          A.card + U.card ≤ 2 * V.card + J.card + R.card)
    : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x7 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x8 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x9 : Finset ℕ := PEqualNP.TopForm.junk x1 x3;         have x10 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         (∀ x11 ∈ x7,             have x13 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x11;             (∀ x14 ∈ x13 (0 : Fin (2 : ℕ)), ∀ x16 ∈ x13 (1 : Fin (2 : ℕ)), x1.Adj x14 x16) ∧ ((x13 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x13 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x12 x13 : Fin (11 : ℕ)), s(x12, x13) ∈ x10 → ∃ x15 ∈ x7, ∃ (x16 : Fin (2 : ℕ)), ∃ x17 ∈ x9, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x15 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x15 x16) x17 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x12 x13) = Bool.true) → (15 : ℕ) + (x7 \ x8).card + (2 : ℕ) * x8.card + x9.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x10.card → (∀ (x14 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x10) x14 → x14.card ≤ (x7 \ x8).card) → (3 : ℕ) ≤ x9.card → (22 : ℕ) ≤ x3.size := by
  intro G _ D hG hLeast hTop
  dsimp only
  intro hStars hOff hCount hCoverBound hJunk
  by_contra hShort
  have hSize : D.size ≤ 21 := by omega
  let U := Ustar G D
  let V := centreless G D
  let T := tops G D
  let J := junk G D
  let R := orN G D \ lam G D
  change 15 + (T \ V).card + 2 * V.card + J.card + R.card ≤ D.size + U.card at hCount
  change 3 ≤ J.card at hJunk
  have hResidual (W : Finset (Sym2 (Fin 11))) (K : Finset (Fin 11))
      (hK : (G.deleteEdges ↑W).IsVertexCover (↑K : Set (Fin 11))) : 7 ≤ K.card + W.card := by
    rw [hG] at hK
    exact hGraph W K hK
  classical
  let H := G.deleteEdges (↑U : Set (Sym2 (Fin 11)))
  by_cases hLarge : 3 ≤ U.card
  · obtain ⟨K, A, hKMin, hA, hACharge⟩ := hCharge G D hG hLeast hTop hStars hOff hLarge hJunk hSize
    have hKT : K.card ≤ (T \ V).card := hCoverBound K hKMin
    change A.card + U.card ≤ 2 * V.card + J.card + R.card at hACharge
    have hFull : G.IsVertexCover (↑(K ∪ A) : Set (Fin 11)) := by
      intro u v hadj
      by_cases hDel : s(u, v) ∈ U
      · exact hA u v hDel
      · have he : H.Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨hadj, hDel⟩
        exact (hKMin.1 he).imp (Finset.mem_union_left _) (Finset.mem_union_left _)
    have hFullDeleted : (G.deleteEdges (↑(∅ : Finset (Sym2 (Fin 11))) : Set (Sym2 (Fin 11)))).IsVertexCover
        (↑(K ∪ A) : Set (Fin 11)) := by
      intro u v hadj
      exact hFull (SimpleGraph.deleteEdges_adj.mp hadj).1
    have hFullBound := hResidual ∅ (K ∪ A) hFullDeleted
    have hUnion := Finset.card_union_le K A
    rw [Finset.card_empty, Nat.add_zero] at hFullBound
    omega
  · let covers : Finset (Finset (Fin 11)) :=
      Finset.univ.filter (fun (K : Finset (Fin 11)) => H.IsVertexCover (↑K : Set (Fin 11)))
    have hCovers : covers.Nonempty := by
      refine ⟨(Finset.univ : Finset (Fin 11)), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      intro u v _
      exact Or.inl (Finset.mem_univ u)
    obtain ⟨K, hK, hMin⟩ := Finset.exists_min_image covers Finset.card hCovers
    have hKMin : IsMinCover H K :=
      ⟨(Finset.mem_filter.mp hK).2, fun A hA =>
        hMin A (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩)⟩
    have hKT : K.card ≤ (T \ V).card := hCoverBound K hKMin
    have hKBound := hResidual U K hKMin.1
    have hUNonempty : U.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨e, he⟩ := hUNonempty
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨a, ha, b, h, hh, _, hr, _⟩ := hOff u v he
      rcases hTrace 11 G D hLeast.1.2.2 a ha b h hh hr with haV | hR
      · have hV : 0 < V.card := Finset.card_pos.mpr ⟨a, haV⟩
        omega
      · have hR' : 0 < R.card := Finset.card_pos.mpr hR
        omega
