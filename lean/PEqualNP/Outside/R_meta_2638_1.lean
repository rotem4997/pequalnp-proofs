import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2638_1
    (strip : ∀ (n s : ℕ) (H : SimpleGraph (Fin n)) (A : Finset (Fin n)) (f : (Fin n → Bool) → Bool),
      (∀ a b, H.Adj a b → a ∉ A) → (∃ a b, H.Adj a b) →
      (∀ x, f x = true ↔ (∃ i ∈ A, x i = true) ∨ ∃ a b, H.Adj a b ∧ x a = true ∧ x b = true) →
      HasCircuitSize n f s →
      ∃ t, t + A.card ≤ s ∧ ∃ g, HasCircuitSize n g t ∧
        ∀ x, g x = true ↔ ∃ a b, H.Adj a b ∧ x a = true ∧ x b = true)
    (tableBound : ∀ (n m : ℕ) (H : SimpleGraph (Fin n)) (X Y : Fin m → Fin n → Fin n → Prop)
      (lab : Fin m → Fin n), (∀ a b v w, H.Adj a b → (v = w ∨ H.Adj v w) →
        (∃! i, X i a b ∧ Y i v w) ∧
        (∀ i, X i a b → Y i v w → (lab i = a ∨ lab i = b) ∧
          ¬ ((H.Adj v (lab i) ∨ H.Adj w (lab i)) ∧ lab i ≠ v ∧ lab i ≠ w))) →
      ∃ T : Finset (Fin n), (∀ a b, H.Adj a b → a ∈ T ∨ b ∈ T) ∧
        H.edgeSet.ncard + T.card ≤ m)
    (constructTable : ∀ (n t : ℕ) (G H : SimpleGraph (Fin n)) (z : Fin n) (g : (Fin n → Bool) → Bool),
      (∀ v, (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3) →
      (G.neighborSet z).ncard = 3 →
      (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      H = G.deleteEdges (G.incidenceSet z) →
      (∀ x, g x = true ↔ ∃ a b, H.Adj a b ∧ x a = true ∧ x b = true) →
      HasCircuitSize n g t →
      ∃ (X Y : Fin (t + 1) → Fin n → Fin n → Prop) (lab : Fin (t + 1) → Fin n),
        ∀ a b v w, H.Adj a b → (v = w ∨ H.Adj v w) →
        (∃! i, X i a b ∧ Y i v w) ∧
        (∀ i, X i a b → Y i v w → (lab i = a ∨ lab i = b) ∧
          ¬ ((H.Adj v (lab i) ∨ H.Adj w (lab i)) ∧ lab i ≠ v ∧ lab i ≠ w)))
    : ∀ (x1 x2 x3 : ℕ) (x4 : SimpleGraph (Fin x1)) (x5 : Finset (Fin x1)) (x6 : Fin x1) (x7 : (Fin x1 → Bool) → Bool), (∀ x8 ∉ x5, (x4.neighborSet x8).ncard = (3 : ℕ)) → (∀ (x9 : Fin x1) (x10 : x4.Walk x9 x9), x10.IsCycle → (7 : ℕ) ≤ x10.length) → (∀ (x10 x11 : Fin x1), x4.Adj x10 x11 → x10 ∉ x5) → (∃ (x11 : Fin x1) (x12 : Fin x1), x4.Adj x11 x12) → x6 ∉ x5 → (∀ (x13 : Fin x1 → Bool), x7 x13 = Bool.true ↔ (∃ x14 ∈ x5, x13 x14 = Bool.true) ∨ ∃ (x14 : Fin x1) (x15 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x14 x15 ∧ x13 x14 = Bool.true ∧ x13 x15 = Bool.true) → (∀ (x14 : Finset (Fin x1)), (∀ (x15 x16 : Fin x1), (x4.deleteEdges (x4.incidenceSet x6)).Adj x15 x16 → x15 ∈ x14 ∨ x16 ∈ x14) → x2 ≤ x14.card) → PEqualNP.MetaComplexity.HasCircuitSize x1 x7 x3 → x5.card + (x4.deleteEdges (x4.incidenceSet x6)).edgeSet.ncard + x2 ≤ x3 + (1 : ℕ) := by
  classical
  intro n k s G A z f degree girth markedIsolated hasEdge zUnmarked spec minCover size
  let H := G.deleteEdges (G.incidenceSet z)
  have degrees (v : Fin n) : (G.neighborSet v).ncard = 0 ∨ (G.neighborSet v).ncard = 3 := by
    by_cases hv : v ∈ A
    · left
      have empty : G.neighborSet v = ∅ := Set.eq_empty_iff_forall_notMem.mpr
        (fun w hw => markedIsolated v w hw hv)
      simp [empty]
    · exact Or.inr (degree v hv)
  have residualEdge : ∃ i j, H.Adj i j := by
    obtain ⟨i, j, hij⟩ := hasEdge
    have survivor : ∃ u, u ≠ z ∧ u ∉ A := by
      by_cases h : i = z
      · exact ⟨j, fun h' => hij.ne (h.trans h'.symm), markedIsolated j i hij.symm⟩
      · exact ⟨i, h, markedIsolated i j hij⟩
    obtain ⟨u, huz, hua⟩ := survivor
    by_contra hno
    have hsub : G.neighborSet u ⊆ ({z} : Set (Fin n)) := by
      intro w hw
      by_contra h
      have hwz : w ≠ z := by simpa only [Set.mem_singleton_iff] using h
      exact hno ⟨u, w, SimpleGraph.deleteIncidenceSet_adj.mpr ⟨hw, huz, hwz⟩⟩
    have hle := Set.ncard_le_ncard hsub
    simp [degree u hua] at hle
  have isolated : ∀ a b, H.Adj a b → a ∉ A :=
    fun a b h => markedIsolated a b (SimpleGraph.deleteIncidenceSet_adj.mp h).1
  obtain ⟨t, budget, g, small, pure⟩ := strip n s H A f isolated residualEdge spec size
  obtain ⟨X, Y, lab, partition⟩ := constructTable n t G H z g degrees (degree z zUnmarked)
    girth rfl pure small
  obtain ⟨T, covers, count⟩ := tableBound n (t + 1) H X Y lab partition
  have coverLower := minCover T covers
  change A.card + H.edgeSet.ncard + k ≤ s + 1
  omega
