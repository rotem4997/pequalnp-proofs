import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.CoverPromise
open PEqualNP.TopForm PEqualNP.EdgeOwnership

-- A lone junk AND which rejects singletons leaves two bicliques. Their centres
-- give a residual cover of size at most two in the absence of a 4-cycle.
theorem PEqualNP.Outside.R_meta_4185_7
    (analyze : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      (∃ S : Finset (Fin n), S.card ≤ (tops G C \ centreless G C).card ∧
        ∀ e ∈ starEdges G C, ∃ v ∈ S, v ∈ e) ∧
      (junk G C = ∅ → Ustar G C = ∅) ∧
      (∀ g : ℕ, junk G C = {g} → (∀ v : Fin n, gateVal n C g (pairInput v v) = false) →
        ∃ K : Finset (Fin n), K.card ≤ 2 ∧ ∀ e ∈ Ustar G C, ∃ v ∈ K, v ∈ e))
    (remaining : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      NoFourCycle G → IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      (Ustar G C).Nonempty → (junk G C).Nonempty →
      let b := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
      (∀ g : ℕ, junk G C = {g} → (∀ v : Fin n, gateVal n C g (pairInput v v) = false) →
        b < (Ustar G C).card + 2) →
      ∃ K : Finset (Fin n), IsVertexCover G K ∧
        K.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card + b) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → ∃ (x9 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x9 ∧ x9.card + (PEqualNP.TopForm.Ustar x2 x4).card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card := by
  classical
  intro n G _ C four _ least top
  obtain ⟨⟨S, hS, starCover⟩, noJunk, smallCover⟩ := analyze n G C four least top
  let U := Ustar G C
  let b := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
  have finish (K : Finset (Fin n)) (covers : ∀ e ∈ U, ∃ v ∈ K, v ∈ e)
      (cost : K.card + U.card ≤ b) :
      ∃ T : Finset (Fin n), IsVertexCover G T ∧
        T.card + U.card ≤ (tops G C \ centreless G C).card + b := by
    refine ⟨S ∪ K, ?_, ?_⟩
    · intro u v he
      have covered : ∃ w ∈ S ∪ K, w ∈ s(u,v) := by
        by_cases h : s(u,v) ∈ starEdges G C
        · obtain ⟨w,hw,he⟩ := starCover _ h
          exact ⟨w,Finset.mem_union_left _ hw,he⟩
        · obtain ⟨w,hw,he⟩ := covers _ (Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr he,h⟩)
          exact ⟨w,Finset.mem_union_right _ hw,he⟩
      obtain ⟨w,hw,he⟩ := covered
      rcases Sym2.mem_iff.mp he with rfl | rfl
      · exact Or.inl hw
      · exact Or.inr hw
    · have unionBound := Finset.card_union_le S K
      omega
  have dest : ∃ T : Finset (Fin n), IsVertexCover G T ∧
      T.card + U.card ≤ (tops G C \ centreless G C).card + b := by
    by_cases none : U = ∅
    · apply finish ∅
      · intro e he
        rw [none] at he
        exact (Finset.notMem_empty e he).elim
      · simp only [none, Finset.card_empty, Nat.zero_add, Nat.zero_le]
    have occupied : (junk G C).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr (fun empty => none (noJunk empty))
    by_cases fits : ∃ g : ℕ, junk G C = {g} ∧
        (∀ v : Fin n, gateVal n C g (pairInput v v) = false) ∧ U.card + 2 ≤ b
    · obtain ⟨g,unique,single,budget⟩ := fits
      obtain ⟨K,hK,hC⟩ := smallCover g unique single
      exact finish K hC (by omega)
    · refine remaining n G C four least top (Finset.nonempty_iff_ne_empty.mpr none) occupied ?_
      intro g unique single
      exact lt_of_not_ge (fun budget => fits ⟨g,unique,single,budget⟩)
  obtain ⟨T, cover, hT⟩ := dest
  refine ⟨T, cover, ?_⟩
  dsimp only [U,b] at hT
  omega
