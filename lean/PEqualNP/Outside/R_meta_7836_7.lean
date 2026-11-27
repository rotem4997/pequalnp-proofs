import Mathlib
import PEqualNP.Defs

-- Cut of L-meta-7836 along the witness of the accepted L-meta-8197: the first hypothesis is the statement of
-- the accepted L-meta-8197 (proved), the second is the step restricted to edges without that witness.
theorem PEqualNP.Outside.R_meta_7836_7
    (shallow : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → ∀ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x6 → PEqualNP.TopForm.TopForm x3 x6 → ∀ x9 ⊆ PEqualNP.TopForm.Ustar x3 x6, (∀ x11 ∈ x9, ∃ (x13 : Fin x2) (x14 : Fin x2), x11 = s(x13, x14) ∧ ∃ x15 ∈ PEqualNP.TopForm.tops x3 x6, ∀ (x16 : Fin (2 : ℕ)), x13 ∈ PEqualNP.TopForm.side x6 x15 x16 ∨ x14 ∈ PEqualNP.TopForm.side x6 x15 x16 ∨ ∃ x17 ∈ PEqualNP.TopForm.junk x3 x6, PEqualNP.CleanedNonEdge.OrReaches x2 x6 (PEqualNP.TopForm.opnd x6 x15 x16) x17 ∧ ((∀ (x18 : Fin (2 : ℕ)), x13 ∈ PEqualNP.TopForm.side x6 x17 x18 ∨ x14 ∈ PEqualNP.TopForm.side x6 x17 x18) ∨ ∃ (x18 : Fin (2 : ℕ)), x13 ∈ PEqualNP.TopForm.side x6 x15 ((1 : Fin (2 : ℕ)) - x16) ∧ (x13 ∈ PEqualNP.TopForm.side x6 x17 x18 ∨ x14 ∈ PEqualNP.TopForm.side x6 x17 x18) ∧ ∃ x19 ∈ PEqualNP.TopForm.junk x3 x6, PEqualNP.CleanedNonEdge.OrReaches x2 x6 (PEqualNP.TopForm.opnd x6 x17 ((1 : Fin (2 : ℕ)) - x18)) x19 ∧ ∀ (x20 : Fin (2 : ℕ)), x13 ∈ PEqualNP.TopForm.side x6 x19 x20 ∨ x14 ∈ PEqualNP.TopForm.side x6 x19 x20)) → x9.card ≤ x1 * (x6.size + (1 : ℕ)))
    (deep : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : SimpleGraph (Fin x2)), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → x8 ≤ x3.deleteEdges ↑(PEqualNP.TopForm.starEdges x3 x7) → (∀ (x12 : Fin x2), (x8.neighborSet x12).ncard = (0 : ℕ) ∨ (2 : ℕ) + (4 : ℕ) * List.count (↑x12) (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x7.gates) < (x8.neighborSet x12).ncard) → ∀ x9 ⊆ PEqualNP.TopForm.Ustar x3 x7, (∀ x10 ∈ x9, x10 ∈ x8.edgeSet) → (∀ x10 ∈ x9, ¬(∃ (y1 : Fin x2) (y2 : Fin x2), x10 = s(y1, y2) ∧ ∃ y3 ∈ PEqualNP.TopForm.tops x3 x7, ∀ (y4 : Fin (2 : ℕ)), y1 ∈ PEqualNP.TopForm.side x7 y3 y4 ∨ y2 ∈ PEqualNP.TopForm.side x7 y3 y4 ∨ ∃ y5 ∈ PEqualNP.TopForm.junk x3 x7, PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 y3 y4) y5 ∧ ((∀ (y6 : Fin (2 : ℕ)), y1 ∈ PEqualNP.TopForm.side x7 y5 y6 ∨ y2 ∈ PEqualNP.TopForm.side x7 y5 y6) ∨ ∃ (y6 : Fin (2 : ℕ)), y1 ∈ PEqualNP.TopForm.side x7 y3 ((1 : Fin (2 : ℕ)) - y4) ∧ (y1 ∈ PEqualNP.TopForm.side x7 y5 y6 ∨ y2 ∈ PEqualNP.TopForm.side x7 y5 y6) ∧ ∃ y7 ∈ PEqualNP.TopForm.junk x3 x7, PEqualNP.CleanedNonEdge.OrReaches x2 x7 (PEqualNP.TopForm.opnd x7 y5 ((1 : Fin (2 : ℕ)) - y6)) y7 ∧ ∀ (y8 : Fin (2 : ℕ)), y1 ∈ PEqualNP.TopForm.side x7 y7 y8 ∨ y2 ∈ PEqualNP.TopForm.side x7 y7 y8))) → x9.card ≤ x1 * (x7.size + (1 : ℕ))) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : SimpleGraph (Fin x2)), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → x8 ≤ x3.deleteEdges ↑(PEqualNP.TopForm.starEdges x3 x7) → (∀ (x12 : Fin x2), (x8.neighborSet x12).ncard = (0 : ℕ) ∨ (2 : ℕ) + (4 : ℕ) * List.count (↑x12) (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x7.gates) < (x8.neighborSet x12).ncard) → x8.edgeSet.ncard ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  obtain ⟨cA, hA⟩ := shallow
  obtain ⟨cB, hB⟩ := deep
  refine ⟨cA + cB, ?_⟩
  intro n G inst hg hne C H hL hT hH hdeg
  set F := (PEqualNP.TopForm.Ustar G C).filter (fun e => e ∈ H.edgeSet) with hF
  have hsub : H.edgeSet ⊆ (↑F : Set (Sym2 (Fin n))) := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have hadj : H.Adj u v := he
      have h2 := hH hadj
      rw [SimpleGraph.deleteEdges_adj] at h2
      rw [Finset.mem_coe, hF, Finset.mem_filter]
      refine ⟨?_, he⟩
      unfold PEqualNP.TopForm.Ustar
      rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset]
      exact ⟨h2.1, fun h => h2.2 (Finset.mem_coe.mpr h)⟩
  have hle : H.edgeSet.ncard ≤ F.card := by
    rw [← Set.ncard_coe_finset F]
    exact Set.ncard_le_ncard hsub (Finset.finite_toSet F)
  let P : Sym2 (Fin n) → Prop := fun e => ∃ (y1 : Fin n) (y2 : Fin n), e = s(y1, y2) ∧ ∃ y3 ∈ PEqualNP.TopForm.tops G C, ∀ (y4 : Fin (2 : ℕ)), y1 ∈ PEqualNP.TopForm.side C y3 y4 ∨ y2 ∈ PEqualNP.TopForm.side C y3 y4 ∨ ∃ y5 ∈ PEqualNP.TopForm.junk G C, PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C y3 y4) y5 ∧ ((∀ (y6 : Fin (2 : ℕ)), y1 ∈ PEqualNP.TopForm.side C y5 y6 ∨ y2 ∈ PEqualNP.TopForm.side C y5 y6) ∨ ∃ (y6 : Fin (2 : ℕ)), y1 ∈ PEqualNP.TopForm.side C y3 ((1 : Fin (2 : ℕ)) - y4) ∧ (y1 ∈ PEqualNP.TopForm.side C y5 y6 ∨ y2 ∈ PEqualNP.TopForm.side C y5 y6) ∧ ∃ y7 ∈ PEqualNP.TopForm.junk G C, PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C y5 ((1 : Fin (2 : ℕ)) - y6)) y7 ∧ ∀ (y8 : Fin (2 : ℕ)), y1 ∈ PEqualNP.TopForm.side C y7 y8 ∨ y2 ∈ PEqualNP.TopForm.side C y7 y8)
  have hsplit := Finset.card_filter_add_card_filter_not (s := F) P
  have h1 : (F.filter P).card ≤ cA * (C.size + 1) :=
    hA n G hg C hL hT (F.filter P) (fun e he => (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1) (fun e he => (Finset.mem_filter.mp he).2)
  have h2 : (F.filter (fun e => ¬ P e)).card ≤ cB * (C.size + 1) :=
    hB n G hg hne C H hL hT hH hdeg (F.filter (fun e => ¬ P e)) (fun e he => (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1) (fun e he => (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2) (fun e he => (Finset.mem_filter.mp he).2)
  refine le_trans hle ?_
  rw [← hsplit]
  nlinarith
