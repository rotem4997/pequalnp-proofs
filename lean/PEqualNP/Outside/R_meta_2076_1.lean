import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2076_1
    (h1 : ∃ (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → (5 : ℕ) ≤ w.length) →
      G.edgeFinset.Nonempty →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (H : SimpleGraph (Fin n)),
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        H ≤ G.deleteEdges ↑(PEqualNP.TopForm.starEdges G C) →
        (∀ (v : Fin n), (H.neighborSet v).ncard = (0 : ℕ) ∨ (3 : ℕ) ≤ (H.neighborSet v).ncard) →
        {e ∈ H.edgeSet | ∃ a ∈ PEqualNP.TopForm.tops G C, ∃ b : Fin 2, ∃ u v : Fin n,
          e = s(u, v) ∧ PEqualNP.EdgeOwnership.gateVal n C a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧
          (u ∈ PEqualNP.TopForm.side (n := n) C a (1 - b) ∨
           v ∈ PEqualNP.TopForm.side (n := n) C a (1 - b))}.ncard ≤ c * (C.size + (1 : ℕ)))
    (h2 : ∃ (c : ℕ), ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → (5 : ℕ) ≤ w.length) →
      G.edgeFinset.Nonempty →
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (H : SimpleGraph (Fin n)),
        PEqualNP.TopForm.IsLeastAO G C →
        PEqualNP.TopForm.TopForm G C →
        H ≤ G.deleteEdges ↑(PEqualNP.TopForm.starEdges G C) →
        (∀ (v : Fin n), (H.neighborSet v).ncard = (0 : ℕ) ∨ (3 : ℕ) ≤ (H.neighborSet v).ncard) →
        {e ∈ H.edgeSet | ∀ a ∈ PEqualNP.TopForm.tops G C, ∀ u v : Fin n,
          e = s(u, v) → PEqualNP.EdgeOwnership.gateVal n C a (PEqualNP.EdgeOwnership.pairInput u v) = true →
          u ∉ PEqualNP.TopForm.side (n := n) C a 0 ∧ v ∉ PEqualNP.TopForm.side (n := n) C a 0 ∧
          u ∉ PEqualNP.TopForm.side (n := n) C a 1 ∧ v ∉ PEqualNP.TopForm.side (n := n) C a 1}.ncard ≤
          c * (C.size + (1 : ℕ))) :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj],
      (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) →
      x3.edgeFinset.Nonempty →
      ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : SimpleGraph (Fin x2)),
        PEqualNP.TopForm.IsLeastAO x3 x7 →
        PEqualNP.TopForm.TopForm x3 x7 →
        x8 ≤ x3.deleteEdges ↑(PEqualNP.TopForm.starEdges x3 x7) →
        (∀ (x12 : Fin x2), (x8.neighborSet x12).ncard = (0 : ℕ) ∨ (3 : ℕ) ≤ (x8.neighborSet x12).ncard) →
        x8.edgeSet.ncard ≤ x1 * (x7.size + (1 : ℕ)) := by
  obtain ⟨c1, hc1⟩ := h1
  obtain ⟨c2, hc2⟩ := h2
  refine ⟨c1 + c2, fun x2 x3 _ hcyc hne x7 x8 hleast htop hsub hdeg => ?_⟩
  have hb1 := hc1 x2 x3 hcyc hne x7 x8 hleast htop hsub hdeg
  have hb2 := hc2 x2 x3 hcyc hne x7 x8 hleast htop hsub hdeg
  have hunion : x8.edgeSet ⊆
      {e ∈ x8.edgeSet | ∃ a ∈ PEqualNP.TopForm.tops x3 x7, ∃ b : Fin 2, ∃ u v : Fin x2,
        e = s(u, v) ∧ PEqualNP.EdgeOwnership.gateVal x2 x7 a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧
        (u ∈ PEqualNP.TopForm.side (n := x2) x7 a (1 - b) ∨
         v ∈ PEqualNP.TopForm.side (n := x2) x7 a (1 - b))} ∪
      {e ∈ x8.edgeSet | ∀ a ∈ PEqualNP.TopForm.tops x3 x7, ∀ u v : Fin x2,
        e = s(u, v) → PEqualNP.EdgeOwnership.gateVal x2 x7 a (PEqualNP.EdgeOwnership.pairInput u v) = true →
        u ∉ PEqualNP.TopForm.side (n := x2) x7 a 0 ∧ v ∉ PEqualNP.TopForm.side (n := x2) x7 a 0 ∧
        u ∉ PEqualNP.TopForm.side (n := x2) x7 a 1 ∧ v ∉ PEqualNP.TopForm.side (n := x2) x7 a 1} := by
    intro e he
    by_cases hp : ∃ a ∈ PEqualNP.TopForm.tops x3 x7, ∃ b : Fin 2, ∃ u v : Fin x2,
        e = s(u, v) ∧ PEqualNP.EdgeOwnership.gateVal x2 x7 a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧
        (u ∈ PEqualNP.TopForm.side (n := x2) x7 a (1 - b) ∨
         v ∈ PEqualNP.TopForm.side (n := x2) x7 a (1 - b))
    · exact Or.inl ⟨he, hp⟩
    · refine Or.inr ⟨he, fun a ha u v huv hval => ?_⟩
      have hnot : ∀ b : Fin 2, ¬ (u ∈ PEqualNP.TopForm.side (n := x2) x7 a (1 - b) ∨
          v ∈ PEqualNP.TopForm.side (n := x2) x7 a (1 - b)) := by
        intro b hb
        exact hp ⟨a, ha, b, u, v, huv, hval, hb⟩
      have h0 := hnot 1
      have h1' := hnot 0
      simp only [Fin.reduceSub, not_or] at h0 h1'
      exact ⟨h0.1, h0.2, h1'.1, h1'.2⟩
  have hcard : x8.edgeSet.ncard ≤
      ({e ∈ x8.edgeSet | ∃ a ∈ PEqualNP.TopForm.tops x3 x7, ∃ b : Fin 2, ∃ u v : Fin x2,
        e = s(u, v) ∧ PEqualNP.EdgeOwnership.gateVal x2 x7 a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧
        (u ∈ PEqualNP.TopForm.side (n := x2) x7 a (1 - b) ∨
         v ∈ PEqualNP.TopForm.side (n := x2) x7 a (1 - b))} ∪
      {e ∈ x8.edgeSet | ∀ a ∈ PEqualNP.TopForm.tops x3 x7, ∀ u v : Fin x2,
        e = s(u, v) → PEqualNP.EdgeOwnership.gateVal x2 x7 a (PEqualNP.EdgeOwnership.pairInput u v) = true →
        u ∉ PEqualNP.TopForm.side (n := x2) x7 a 0 ∧ v ∉ PEqualNP.TopForm.side (n := x2) x7 a 0 ∧
        u ∉ PEqualNP.TopForm.side (n := x2) x7 a 1 ∧ v ∉ PEqualNP.TopForm.side (n := x2) x7 a 1}).ncard :=
    Set.ncard_le_ncard hunion (Set.toFinite _)
  have hle : x8.edgeSet.ncard ≤
      {e ∈ x8.edgeSet | ∃ a ∈ PEqualNP.TopForm.tops x3 x7, ∃ b : Fin 2, ∃ u v : Fin x2,
        e = s(u, v) ∧ PEqualNP.EdgeOwnership.gateVal x2 x7 a (PEqualNP.EdgeOwnership.pairInput u v) = true ∧
        (u ∈ PEqualNP.TopForm.side (n := x2) x7 a (1 - b) ∨
         v ∈ PEqualNP.TopForm.side (n := x2) x7 a (1 - b))}.ncard +
      {e ∈ x8.edgeSet | ∀ a ∈ PEqualNP.TopForm.tops x3 x7, ∀ u v : Fin x2,
        e = s(u, v) → PEqualNP.EdgeOwnership.gateVal x2 x7 a (PEqualNP.EdgeOwnership.pairInput u v) = true →
        u ∉ PEqualNP.TopForm.side (n := x2) x7 a 0 ∧ v ∉ PEqualNP.TopForm.side (n := x2) x7 a 0 ∧
        u ∉ PEqualNP.TopForm.side (n := x2) x7 a 1 ∧ v ∉ PEqualNP.TopForm.side (n := x2) x7 a 1}.ncard :=
    le_trans hcard (Set.ncard_union_le _ _)
  calc
    x8.edgeSet.ncard ≤ c1 * (x7.size + (1 : ℕ)) + c2 * (x7.size + (1 : ℕ)) := le_trans hle (Nat.add_le_add hb1 hb2)
    _ = (c1 + c2) * (x7.size + (1 : ℕ)) := (Nat.add_mul c1 c2 (x7.size + 1)).symm
