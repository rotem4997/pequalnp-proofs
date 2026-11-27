import Mathlib
import PEqualNP.Defs

-- Split the lower bound into the usual cover form of the charging lemma
-- and the graph fact that, in this cubic bipartite setting, every vertex
-- cover is at least half the vertices that are not isolated OR-inputs.
theorem PEqualNP.Outside.R_meta_5114_1
    (hCover : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
        (f : (Fin n → Bool) → Bool) (k : ℕ),
      G.Colorable (2 : ℕ) →
      (∀ v ∉ A, (G.neighborSet v).ncard = (3 : ℕ)) →
      (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → (7 : ℕ) ≤ w.length) →
      (∀ i j : Fin n, G.Adj i j → i ∉ A) →
      (∃ i j : Fin n, G.Adj i j) →
      (∀ x : Fin n → Bool,
        f x = Bool.true ↔ (∃ a ∈ A, x a = Bool.true) ∨
          ∃ i j : Fin n, G.Adj i j ∧ x i = Bool.true ∧ x j = Bool.true) →
      (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) →
      ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n f s →
        A.card + G.edgeSet.ncard + k ≤ s + (1 : ℕ))
    (hHalf : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)),
      G.Colorable (2 : ℕ) →
      (∀ v ∉ A, (G.neighborSet v).ncard = (3 : ℕ)) →
      (∀ i j : Fin n, G.Adj i j → i ∉ A) →
      (∃ i j : Fin n, G.Adj i j) →
      ∀ T : Finset (Fin n),
        (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) →
        (Finset.univ \ A).card / (2 : ℕ) ≤ T.card) :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), x2.Colorable (2 : ℕ) → (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) → ∀ (x11 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x11 → x3.card + x2.edgeSet.ncard + (Finset.univ \ x3).card / (2 : ℕ) ≤ x11 + (1 : ℕ) := by
  intro n G A f hcol hdeg hgirth hA hedge hf s hs
  exact hCover n G A f ((Finset.univ \ A).card / (2 : ℕ))
    hcol hdeg hgirth hA hedge hf
    (hHalf n G A hcol hdeg hA hedge) s hs
