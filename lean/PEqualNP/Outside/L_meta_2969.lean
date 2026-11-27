import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2969

open PEqualNP.CircuitLowerBounds

-- two copies of the core (x0 AND x1) AND (x0 OR x1); the second copy is unread
def cx : Circuit :=
  { gates := [{ op := GateOp.and, inputs := [0, 1] }, { op := GateOp.or, inputs := [0, 1] },
      { op := GateOp.and, inputs := [2, 3] }, { op := GateOp.and, inputs := [2, 3] }],
    output := 4 }

def sx : Fin 2 → Bool := fun i => decide (i = 0)

theorem hD : (PEqualNP.Core.maximalCores (⊤ : SimpleGraph (Fin 2)) cx).biUnion
    (PEqualNP.TopForm.gammaE (⊤ : SimpleGraph (Fin 2)) cx) = {s(0, 1)} := by decide

theorem hcover : PEqualNP.MetaComplexity.NestedCover.IsMinCover
    ((⊤ : SimpleGraph (Fin 2)).deleteEdges
      (((PEqualNP.Core.maximalCores (⊤ : SimpleGraph (Fin 2)) cx).biUnion
        (PEqualNP.TopForm.gammaE (⊤ : SimpleGraph (Fin 2)) cx) : Finset (Sym2 (Fin 2))) :
          Set (Sym2 (Fin 2)))) ∅ := by
  rw [hD]
  refine ⟨?_, fun T _ => by simp⟩
  intro v w hvw
  exfalso
  rw [SimpleGraph.deleteEdges_adj] at hvw
  obtain ⟨h1, h2⟩ := hvw
  apply h2
  simp only [Finset.coe_singleton, Set.mem_singleton_iff]
  have hne : v ≠ w := h1
  fin_cases v <;> fin_cases w <;> simp_all [Sym2.eq_swap]

end PEqualNP.Outside.L_meta_2969

open PEqualNP.Outside.L_meta_2969 in
theorem PEqualNP.Outside.L_meta_2969 : ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (T' : Finset (Fin n)), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges (((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C) : Finset (Sym2 (Fin n))) : Set (Sym2 (Fin n)))) T' → ((PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.Core.coneSet n C)).card + (G.edgeFinset \ (PEqualNP.Core.maximalCores G C).biUnion (PEqualNP.TopForm.gammaE G C)).card + T'.card + (PEqualNP.Core.maximalCores G C).card ≤ C.size + 1) := by
  intro h
  have key := h 2 (⊤ : SimpleGraph (Fin 2)) cx sx ∅
    (by decide) (by decide) (by decide) (by funext x; revert x; decide) (by decide) hcover
  revert key
  decide
