import PEqualNP.ProofComplexity.Helpers.LiftClassPlan

namespace PEqualNP.ProofComplexity.LiftClass

open PEqualNP.ProofComplexity

theorem stmtJunta : StmtJunta := by
  intro V _ c L
  classical
  constructor
  · intro x y hxy
    have key : ∀ q ∈ L, (LinEqSat (emb c x) q ↔ LinEqSat (emb c y) q) := by
      intro q hq
      unfold LinEqSat
      have : q.1.filter (fun u => emb c x u = true) = q.1.filter (fun u => emb c y u = true) := by
        apply Finset.filter_congr
        intro u hu
        have hb : u.1 ∈ lineBlocks L :=
          Finset.mem_biUnion.2 ⟨q, hq, Finset.mem_image.2 ⟨u, hu, rfl⟩⟩
        simp only [emb, hxy u.1 hb]
      rw [this]
    have hiff : LinClauseSat (emb c x) L ↔ LinClauseSat (emb c y) L := by
      constructor
      · rintro ⟨q, hq, h⟩; exact ⟨q, hq, (key q hq).1 h⟩
      · rintro ⟨q, hq, h⟩; exact ⟨q, hq, (key q hq).2 h⟩
    show ¬ LinClauseSat (emb c x) L ↔ ¬ LinClauseSat (emb c y) L
    rw [hiff]
  · have hsub : lineBlocks L ⊆ lineLocalBlocks L ∪
        (L.filter (fun q => 2 ≤ (eqBlocks q).card)).biUnion eqBlocks := by
      intro v hv
      obtain ⟨q, hq, hvq⟩ := Finset.mem_biUnion.1 hv
      have hpos : 0 < (eqBlocks q).card := Finset.card_pos.2 ⟨v, hvq⟩
      by_cases h1 : (eqBlocks q).card = 1
      · exact Finset.mem_union_left _
          (Finset.mem_biUnion.2 ⟨q, Finset.mem_filter.2 ⟨hq, h1⟩, hvq⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_biUnion.2 ⟨q, Finset.mem_filter.2 ⟨hq, by omega⟩, hvq⟩)
    calc (lineBlocks L).card
        ≤ (lineLocalBlocks L ∪
          (L.filter (fun q => 2 ≤ (eqBlocks q).card)).biUnion eqBlocks).card :=
          Finset.card_le_card hsub
      _ ≤ (lineLocalBlocks L).card +
          ((L.filter (fun q => 2 ≤ (eqBlocks q).card)).biUnion eqBlocks).card :=
          Finset.card_union_le _ _
      _ ≤ (lineLocalBlocks L).card + lineCrossInc L :=
          Nat.add_le_add_left Finset.card_biUnion_le _

end PEqualNP.ProofComplexity.LiftClass
