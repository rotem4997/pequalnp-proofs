import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3446

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.Core

private abbrev adj7b (u v : Fin 7) : Bool :=
  (u == 0 && (v == 2 || v == 3)) || ((u == 2 || u == 3) && v == 0) ||
  (u == 1 && v == 4) || (u == 4 && v == 1) ||
  (u == 5 && v == 6) || (u == 6 && v == 5)

private abbrev G7 : SimpleGraph (Fin 7) where
  Adj u v := adj7b u v = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

private def s7 : Fin 7 → Bool := fun i => i == 2 || i == 3 || i == 4 || i == 6

private def C7 : Circuit :=
  ⟨[
    ⟨.or, [0, 4]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.and, [8, 9]⟩,
    ⟨.and, [7, 10]⟩,
    ⟨.and, [1, 4]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.and, [13, 7]⟩,
    ⟨.and, [13, 8]⟩,
    ⟨.and, [13, 9]⟩,
    ⟨.and, [13, 10]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [18, 13]⟩,
    ⟨.or, [19, 14]⟩,
    ⟨.or, [20, 15]⟩,
    ⟨.or, [21, 16]⟩,
    ⟨.or, [22, 17]⟩
  ], 23⟩

private def T7 : Finset (Fin 7) := {0, 1, 5}
private def T7' : Finset (Fin 7) := {1, 5}

private lemma minCover_G7 : IsMinCover G7 T7 := by
  refine ⟨?_, ?_⟩
  · intro u v huv
    rw [Finset.mem_coe, Finset.mem_coe]
    revert u v huv
    decide
  · intro S hS
    have h02 : (0 : Fin 7) ∈ S ∨ (2 : Fin 7) ∈ S := hS (by decide : G7.Adj 0 2)
    have h14 : (1 : Fin 7) ∈ S ∨ (4 : Fin 7) ∈ S := hS (by decide : G7.Adj 1 4)
    have h56 : (5 : Fin 7) ∈ S ∨ (6 : Fin 7) ∈ S := hS (by decide : G7.Adj 5 6)
    have hcard : T7.card = 3 := by decide
    rw [hcard]
    rcases h02 with h0 | h2 <;> rcases h14 with h1 | h4 <;> rcases h56 with h5 | h6
    · exact le_trans (by decide : ({0, 1, 5} : Finset (Fin 7)).card = 3).ge (Finset.card_le_card (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption))
    · exact le_trans (by decide : ({0, 1, 6} : Finset (Fin 7)).card = 3).ge (Finset.card_le_card (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption))
    · exact le_trans (by decide : ({0, 4, 5} : Finset (Fin 7)).card = 3).ge (Finset.card_le_card (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption))
    · exact le_trans (by decide : ({0, 4, 6} : Finset (Fin 7)).card = 3).ge (Finset.card_le_card (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption))
    · exact le_trans (by decide : ({2, 1, 5} : Finset (Fin 7)).card = 3).ge (Finset.card_le_card (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption))
    · exact le_trans (by decide : ({2, 1, 6} : Finset (Fin 7)).card = 3).ge (Finset.card_le_card (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption))
    · exact le_trans (by decide : ({2, 4, 5} : Finset (Fin 7)).card = 3).ge (Finset.card_le_card (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption))
    · exact le_trans (by decide : ({2, 4, 6} : Finset (Fin 7)).card = 3).ge (Finset.card_le_card (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption))

private lemma D7_eq : (maximalCores G7 C7).biUnion (gammaE G7 C7) = {s(0, 2), s(0, 3)} := by
  decide +kernel

private lemma minCover_G7' : IsMinCover (G7.deleteEdges (((maximalCores G7 C7).biUnion (gammaE G7 C7) : Finset (Sym2 (Fin 7))) : Set (Sym2 (Fin 7)))) T7' := by
  rw [D7_eq]
  refine ⟨?_, ?_⟩
  · intro u v huv
    rw [SimpleGraph.deleteEdges_adj, Finset.mem_coe] at huv
    revert u v huv
    decide
  · intro S hS
    have h14 : (1 : Fin 7) ∈ S ∨ (4 : Fin 7) ∈ S := hS (by rw [SimpleGraph.deleteEdges_adj, Finset.mem_coe]; decide)
    have h56 : (5 : Fin 7) ∈ S ∨ (6 : Fin 7) ∈ S := hS (by rw [SimpleGraph.deleteEdges_adj, Finset.mem_coe]; decide)
    have hcard : T7'.card = 2 := by decide
    rw [hcard]
    rcases h14 with h1 | h4 <;> rcases h56 with h5 | h6
    · exact le_trans (by decide : ({1, 5} : Finset (Fin 7)).card = 2).ge (Finset.card_le_card (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption))
    · exact le_trans (by decide : ({1, 6} : Finset (Fin 7)).card = 2).ge (Finset.card_le_card (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption))
    · exact le_trans (by decide : ({4, 5} : Finset (Fin 7)).card = 2).ge (Finset.card_le_card (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption))
    · exact le_trans (by decide : ({4, 6} : Finset (Fin 7)).card = 2).ge (Finset.card_le_card (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption))

private lemma main_proof : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → PEqualNP.MetaComplexity.NestedCover.IsMinCover G T → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤ (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers n C w).filter (fun k => PEqualNP.Core.InOutputCone n C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C))).card + (PEqualNP.Core.maximalCores G C).card + T'.card) := by
  intro H
  have h := H 7 G7 C7 s7 T7 T7'
    (by decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    (by funext x; revert x; decide +kernel)
    (by decide +kernel)
    (by decide +kernel)
    minCover_G7
    minCover_G7'
  have hbad : ¬ (((maximalCores G7 C7).biUnion (gammaE G7 C7)).card + T7.card ≤ (((maximalCores G7 C7).biUnion (coneSet 7 C7)).filter (fun w => w ∈ maximalCores G7 C7 ∨ ((readers 7 C7 w).filter (fun k => InOutputCone 7 C7 k)) ⊆ (maximalCores G7 C7).biUnion (coneSet 7 C7))).card + (maximalCores G7 C7).card + T7'.card) := by
    decide +kernel
  exact hbad h

end PEqualNP.Outside.L_meta_3446

theorem PEqualNP.Outside.L_meta_3446 : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → PEqualNP.MetaComplexity.NestedCover.IsMinCover G T → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T.card ≤ (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers n C w).filter (fun k => PEqualNP.Core.InOutputCone n C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C))).card + (PEqualNP.Core.maximalCores G C).card + T'.card) := by
  exact PEqualNP.Outside.L_meta_3446.main_proof
