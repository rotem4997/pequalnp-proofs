import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

-- Cover edges outside Ustar and inside Ustar separately, then combine the covers.
theorem PEqualNP.Outside.R_meta_8105_1
    (topCover : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit), NoFourCycle G → IsLeastAO G C → TopForm G C →
      ∃ S : Finset (Fin n),
        (∀ u v, G.Adj u v → s(u,v) ∉ Ustar G C → u ∈ S ∨ v ∈ S) ∧
        S.card ≤ (tops G C \ centreless G C).card)
    (residualCover : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit), NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C →
      TopForm G C → (Ustar G C).Nonempty → 2 ≤ (junk G C).card →
      ∃ T : Finset (Fin n),
        (∀ u v, G.Adj u v → s(u,v) ∈ Ustar G C → u ∈ T ∨ v ∈ T) ∧
        T.card + (Ustar G C).card ≤
          2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (PEqualNP.TopForm.Ustar x2 x4).Nonempty → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x4).card → ∃ (x11 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x11 ∧ x11.card + (PEqualNP.TopForm.Ustar x2 x4).card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card := by
  classical
  intro n G inst C noFour edges least top uncovered manyJunk
  obtain ⟨S, coversS, costS⟩ := topCover n G C noFour least top
  obtain ⟨T, coversT, costT⟩ := residualCover n G C noFour edges least top uncovered manyJunk
  refine ⟨S ∪ T, ?_, ?_⟩
  · intro u v adj
    by_cases h : s(u,v) ∈ Ustar G C
    · rcases coversT u v adj h with hu | hv
      · exact Or.inl (Finset.mem_union_right S hu)
      · exact Or.inr (Finset.mem_union_right S hv)
    · rcases coversS u v adj h with hu | hv
      · exact Or.inl (Finset.mem_union_left T hu)
      · exact Or.inr (Finset.mem_union_left T hv)
  · have unionBound := Finset.card_union_le S T
    omega
