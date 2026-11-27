import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2076_389
    (stars : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
        ({e : Sym2 (Fin n) | ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2,
        (∃ u v : Fin n, u ≠ v ∧
          u ∈ PEqualNP.TopForm.side C a b ∧ v ∈ PEqualNP.TopForm.side C a b) ∧
        ∃ p ∈ PEqualNP.TopForm.side (n := n) C a b, ∃ q : Fin n,
          e = s(p, q) ∧
          PEqualNP.CircuitLowerBounds.Circuit.eval
            ⟨C.gates, PEqualNP.TopForm.opnd C a (1 - b)⟩
            (List.ofFn (fun v : Fin n => decide (v = q))) = true} : Set (Sym2 (Fin n))).ncard ≤ 3 * (C.size + 1))
    (remaining : ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) →
      G.edgeFinset.Nonempty →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (H : SimpleGraph (Fin n)),
        PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
        H ≤ G.deleteEdges ↑(PEqualNP.TopForm.starEdges G C) →
        (∀ v : Fin n, (H.neighborSet v).ncard = 0 ∨ 3 ≤ (H.neighborSet v).ncard) →
        (H.edgeSet \ ({e : Sym2 (Fin n) | ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2,
        (∃ u v : Fin n, u ≠ v ∧
          u ∈ PEqualNP.TopForm.side C a b ∧ v ∈ PEqualNP.TopForm.side C a b) ∧
        ∃ p ∈ PEqualNP.TopForm.side (n := n) C a b, ∃ q : Fin n,
          e = s(p, q) ∧
          PEqualNP.CircuitLowerBounds.Circuit.eval
            ⟨C.gates, PEqualNP.TopForm.opnd C a (1 - b)⟩
            (List.ofFn (fun v : Fin n => decide (v = q))) = true} : Set (Sym2 (Fin n)))).ncard ≤ c * (C.size + 1)) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : SimpleGraph (Fin x2)), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → x8 ≤ x3.deleteEdges ↑(PEqualNP.TopForm.starEdges x3 x7) → (∀ (x12 : Fin x2), (x8.neighborSet x12).ncard = (0 : ℕ) ∨ (3 : ℕ) ≤ (x8.neighborSet x12).ncard) → x8.edgeSet.ncard ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨c, hr⟩ := remaining
  refine ⟨c + 3, ?_⟩
  intro n G _ hg he C H hleast htop hsub hdegree
  rw [Nat.add_mul]
  have hJ := stars n G hg he C hleast htop
  have hRest := hr n G hg he C H hleast htop hsub hdegree
  exact (Set.ncard_le_ncard_sdiff_add_ncard H.edgeSet _ (Set.toFinite _)).trans
    (Nat.add_le_add hRest hJ)
