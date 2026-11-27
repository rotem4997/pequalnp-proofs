import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3444

open PEqualNP.CircuitLowerBounds

abbrev gP : SimpleGraph (Fin 5) := SimpleGraph.fromRel (fun a b : Fin 5 => a.val + 1 = b.val)

def cx : Circuit :=
  { gates := [{ op := GateOp.and, inputs := [0, 1] }, { op := GateOp.and, inputs := [1, 2] },
      { op := GateOp.or, inputs := [2, 4] }, { op := GateOp.and, inputs := [3, 7] },
      { op := GateOp.or, inputs := [5, 8] }, { op := GateOp.and, inputs := [2, 9] },
      { op := GateOp.or, inputs := [6, 10] }, { op := GateOp.or, inputs := [9, 11] }],
    output := 12 }

def sx : Fin 5 → Bool := fun i => decide (i.val % 2 = 0)

def tx : Finset (Fin 5) := {1, 3}

theorem hD : (PEqualNP.Core.maximalCores gP cx).biUnion (PEqualNP.TopForm.gammaE gP cx) = {s(2, 3)} := by
  decide

theorem hcover : PEqualNP.MetaComplexity.NestedCover.IsMinCover
    (gP.deleteEdges (((PEqualNP.Core.maximalCores gP cx).biUnion
      (PEqualNP.TopForm.gammaE gP cx) : Finset (Sym2 (Fin 5))) : Set (Sym2 (Fin 5)))) tx := by
  rw [hD]
  refine ⟨?_, ?_⟩
  · intro v w hvw
    rw [SimpleGraph.deleteEdges_adj, SimpleGraph.fromRel_adj] at hvw
    obtain ⟨⟨hne, hr⟩, hs⟩ := hvw
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hs
    fin_cases v <;> fin_cases w <;> simp_all [tx, Sym2.eq_swap]
  · intro T hT
    have h01 : (gP.deleteEdges (({s(2, 3)} : Finset (Sym2 (Fin 5))) : Set (Sym2 (Fin 5)))).Adj 0 1 := by
      rw [SimpleGraph.deleteEdges_adj, SimpleGraph.fromRel_adj]
      simp
    have h34 : (gP.deleteEdges (({s(2, 3)} : Finset (Sym2 (Fin 5))) : Set (Sym2 (Fin 5)))).Adj 3 4 := by
      rw [SimpleGraph.deleteEdges_adj, SimpleGraph.fromRel_adj]
      simp
    have ha := hT h01
    have hb := hT h34
    simp only [Finset.mem_coe] at ha hb
    have htx : tx.card = 2 := by decide
    rw [htx]
    obtain ⟨a, haT, ha2⟩ : ∃ a ∈ T, a.val ≤ 1 := by
      rcases ha with h | h
      · exact ⟨0, h, by decide⟩
      · exact ⟨1, h, by decide⟩
    obtain ⟨b, hbT, hb2⟩ : ∃ b ∈ T, 3 ≤ b.val := by
      rcases hb with h | h
      · exact ⟨3, h, by decide⟩
      · exact ⟨4, h, by decide⟩
    have hab : a ≠ b := by
      intro e
      rw [e] at ha2
      omega
    have hsub : ({a, b} : Finset (Fin 5)) ⊆ T := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact haT
      · exact hbT
    have := Finset.card_le_card hsub
    rw [Finset.card_pair hab] at this
    exact this

end PEqualNP.Outside.L_meta_3444

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
open PEqualNP.Outside.L_meta_3444 in
theorem PEqualNP.Outside.L_meta_3444 : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).filter (fun w => w ∈ PEqualNP.Core.maximalCores G C ∨ ((PEqualNP.TopForm.readers n C w).filter (fun k => PEqualNP.Core.InOutputCone n C k)) ⊆ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C))).card + (G.edgeFinset \ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T'.card + (PEqualNP.Core.maximalCores G C).card ≤ C.size + 1) := by
  intro h
  have key := @h 5 gP inferInstance cx sx tx (by decide) (by decide) (by decide)
    (by funext x; revert x; decide) (by decide) (by decide) hcover
  revert key
  decide

