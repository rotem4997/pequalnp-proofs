import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

-- The block masks encode the sixteen edges, three triangles and four induced pentagons.
-- Disjoint blocks certify additive cover costs of one, two and three, respectively.
-- A seven-vertex cover handles large budgets without using either child.
theorem PEqualNP.Outside.R_meta_2384_421
  (pack : let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
    let blocks : List ℕ := [513, 1025, 18, 258, 36, 1028, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768, 274, 200, 800, 1573, 1809, 1729, 1332]
    ∀ K : Finset (Fin 11), ∃ (P : List ℕ) (X : Finset (Fin 11)),
      P.Pairwise (fun a b => a &&& b = 0) ∧ (∀ a ∈ P, a ∈ blocks ∧ ∀ v ∈ K, a.testBit v.val = false) ∧
      G.IsVertexCover (↑(K ∪ X)) ∧ X.card ≤ (P.map (fun a => (a.bitIndices.length + 1) / 2)).sum)
  (charge : let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
    let blocks : List ℕ := [513, 1025, 18, 258, 36, 1028, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768, 274, 200, 800, 1573, 1809, 1729, 1332]
    ∀ D : Circuit, D.size ≤ 21 → IsLeastAO G D → TopForm G D → 2 ≤ (junk G D).card →
      let U := Ustar G D
      let B := 2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card
      U.card ≤ B → B < 2 * U.card → B - U.card < 7 →
      ∃ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K ∧
        ∀ P : List ℕ, P.Pairwise (fun a b => a &&& b = 0) → (∀ a ∈ P, a ∈ blocks ∧ ∀ v ∈ K, a.testBit v.val = false) → (P.map (fun a => (a.bitIndices.length + 1) / 2)).sum ≤ B - U.card) :
  let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →           have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           x7.card ≤ x8 → x8 < (2 : ℕ) * x7.card → ∃ (x11 : Finset (Fin (11 : ℕ))) (x12 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x7) x11 ∧ x1.IsVertexCover ↑(x11 ∪ x12) ∧ x12.card ≤ x8 - x7.card := by
  dsimp only
  intro D hsize least top hj
  let G := edgeGraph 11 [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
  let U := Ustar G D
  let B := 2 * (centreless G D).card + (junk G D).card + (orN G D \ lam G D).card
  change U.card ≤ B → B < 2 * U.card → _
  intro lo hi
  by_cases large : 7 ≤ B - U.card
  · classical
    let H := G.deleteEdges (↑U)
    let Q (m : ℕ) := ∃ K : Finset (Fin 11), H.IsVertexCover (↑K) ∧ K.card = m
    have ex : ∃ m, Q m := ⟨_, Finset.univ, by simp [H], rfl⟩
    obtain ⟨K, hc, hk⟩ := Nat.find_spec ex
    have hm : IsMinCover H K := ⟨hc, fun T ht => hk.trans_le (Nat.find_min' ex ⟨T, ht, rfl⟩)⟩
    let X : Finset (Fin 11) := {0, 1, 3, 5, 7, 8, 10}
    have hx : G.IsVertexCover (↑X) := by
      change ∀ u v : Fin 11, G.Adj u v → u ∈ X ∨ v ∈ X
      dsimp [G, X]
      decide +kernel
    refine ⟨K, X, hm, ?_, ?_⟩
    · intro u v huv
      exact (hx huv).imp (Finset.mem_union_right K) (Finset.mem_union_right K)
    · have seven : X.card = 7 := by decide
      change X.card ≤ B - U.card
      omega
  · obtain ⟨K, hm, bound⟩ := charge D hsize least top hj lo hi (Nat.lt_of_not_ge large)
    obtain ⟨P, X, hP, hK, hc, hx⟩ := pack K
    exact ⟨K, X, hm, hc, hx.trans (bound P hP hK)⟩
