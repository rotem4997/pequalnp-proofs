import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import PEqualNP.Defs

-- Use a cover bound for circuits with an unsound AND gate.
-- The wire inequality only uses binary fan-in and backwards references.
theorem PEqualNP.Outside.R_meta_17625_1
    (hCover :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
        G.IsBipartite →
        ¬G.IsAcyclic →
        PEqualNP.TopForm.NoFourCycle G →
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        (∃ j < C.size,
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
            PEqualNP.CircuitLowerBounds.GateOp.and ∧
          ¬PEqualNP.TopForm.BelowF G C j) →
        ∃ V : Finset (Fin n),
          (∀ u v, G.Adj u v → u ∈ V ∨ v ∈ V) ∧
          G.edgeFinset.card + V.card ≤ C.size + 1)
    (hWireBudget :
      ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.TopForm.IsAO2 n C →
        0 < C.size →
        let refs := C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs
        let inputRefs := refs.toFinset.filter (fun w => w < n)
        C.size + 1 ≤ inputRefs.card + (refs.length - refs.toFinset.card)) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x2.IsBipartite →     ¬x2.IsAcyclic →       PEqualNP.TopForm.NoFourCycle x2 →         PEqualNP.TopForm.IsLeastAO x2 x4 →           PEqualNP.TopForm.TopForm x2 x4 →             (∃ x10 < x4.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.BelowF x2 x4 x10 ∧ ∃ (x11 : Fin x1 × Fin x1) (x12 : Fin x1 × Fin x1), s(x11.1, x11.2) ≠ s(x12.1, x12.2) ∧ ∀ x13 ∈ [x11, x12], x2.Adj x13.1 x13.2 ∧ PEqualNP.ReadK.readsAtMost x4 x1 [↑x13.1, ↑x13.2] (1 : ℕ) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x10 (PEqualNP.EdgeOwnership.pairInput x13.1 x13.2) = Bool.true) →               ∀ (x11 : Finset (Fin x1)) (x12 : ↥x11 → Fin x1),                 Function.Injective x12 →                   (∀ (x14 : ↥x11), x12 x14 ∉ x11 ∧ x2.Adj (↑x14) (x12 x14)) →                     have x15 : List ℕ := List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates;                     have x16 : Finset ℕ := {x16 ∈ x15.toFinset | x16 < x1};                     x2.edgeFinset.card + x11.card - x16.card ≤ x15.length - x15.toFinset.card := by
  classical
  intro n G _ C hBipartite hCyclic hC4 hLeast hTop hWitness M mate hMate hEdges
  obtain ⟨j, hj, hAnd, hDirty, _⟩ := hWitness
  obtain ⟨V, hCoverHits, hCoverCost⟩ :=
    hCover n G C hBipartite hCyclic hC4 hLeast hTop ⟨j, hj, hAnd, hDirty⟩
  -- Pick the left endpoint if it is in the cover, and otherwise its
  -- matched endpoint. The two endpoint families have disjoint ranges.
  let pick (a : ↥M) : Fin n := if (a : Fin n) ∈ V then a else mate a
  have hPickMem (a : ↥M) : pick a ∈ V := by
    by_cases ha : (a : Fin n) ∈ V
    · simpa [pick, ha] using ha
    · simpa [pick, ha] using (hCoverHits a (mate a) (hEdges a).2).resolve_left ha
  have hPickInj : Function.Injective pick := by
    intro a b hab
    by_cases ha : (a : Fin n) ∈ V <;> by_cases hb : (b : Fin n) ∈ V
    · exact Subtype.ext (by simpa [pick, ha, hb] using hab)
    · have he : (a : Fin n) = mate b := by simpa [pick, ha, hb] using hab
      exact False.elim ((hEdges b).1 (he ▸ a.property))
    · have he : mate a = (b : Fin n) := by simpa [pick, ha, hb] using hab
      exact False.elim ((hEdges a).1 (he.symm ▸ b.property))
    · exact hMate (by simpa [pick, ha, hb] using hab)
  have hMatchingCost : M.card ≤ V.card := by
    simpa using Fintype.card_le_of_injective
      (fun a => (⟨pick a, hPickMem a⟩ : ↥V))
      (fun a b hab => hPickInj (congrArg Subtype.val hab))
  let refs := C.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs
  let inputRefs := refs.toFinset.filter (fun w => w < n)
  have hWires : C.size + 1 ≤ inputRefs.card + (refs.length - refs.toFinset.card) :=
    hWireBudget n C hLeast.1 (Nat.zero_lt_of_lt hj)
  change G.edgeFinset.card + M.card - inputRefs.card ≤ refs.length - refs.toFinset.card
  omega
