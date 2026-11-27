import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_2384_471
    (geometry : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
    NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
    let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
    let U := Ustar G C
    let H := G.deleteEdges (↑U)
    B ≤ 3 → (∃ u v : Fin n, s(u,v) ∈ U) →
    3 ≤ B ∧ ∃ q : Fin n, ∀ u v : Fin n, s(u,v) ∈ U → ∃ w : Fin n, (w=u ∨ w=v) ∧ H.Adj q w ∧
        ∀ x : Fin n → Bool, x w = true → graphFun G ∅ x = false →
        ∃ S : Finset (Fin n), (S.card ≤ 1 ∨ ∃ c, ∀ z ∈ S, H.Adj z c) ∧
        (∀ i j : Fin n, s(i,j) ∈ U → i ∈ S ∨ j ∈ S) ∧ ∀ z ∈ S, x z = false)
    (finite : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
    ∀ U : Finset (Sym2 (Fin 11)), U ⊆ G.edgeFinset → 2 ≤ U.card → U.card ≤ 3 →
    let H := G.deleteEdges (↑U)
    (∃ q : Fin 11, ∀ u v : Fin 11, s(u,v) ∈ U → ∃ w : Fin 11, (w=u ∨ w=v) ∧ H.Adj q w ∧
        ∀ x : Fin 11 → Bool, x w = true → graphFun G ∅ x = false →
        ∃ S : Finset (Fin 11), (S.card ≤ 1 ∨ ∃ c, ∀ z ∈ S, H.Adj z c) ∧
        (∀ i j : Fin 11, s(i,j) ∈ U → i ∈ S ∨ j ∈ S) ∧ ∀ z ∈ S, x z = false) →
    ∃ K X : Finset (Fin 11), IsMinCover H K ∧ G.IsVertexCover ↑(K ∪ X) ∧ X.card ≤ 3-U.card)
    (large : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
    ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
    let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
    let U := Ustar G C
    4 ≤ B → U.card ≤ B → B < 2 * U.card →
    ∃ K X : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K ∧ G.IsVertexCover ↑(K ∪ X) ∧ X.card ≤ B-U.card) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →           have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           x7.card ≤ x8 → x8 < (2 : ℕ) * x7.card → ∃ (x11 : Finset (Fin (11 : ℕ))) (x12 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x7) x11 ∧ x1.IsVertexCover ↑(x11 ∪ x12) ∧ x12.card ≤ x8 - x7.card := by
  intro G C hsize hl ht hj U B uB bU
  change U.card ≤ B at uB
  change B < 2 * U.card at bU
  by_cases big : 4 ≤ B
  · exact large C hsize hl ht hj big uB bU
  have hf : NoFourCycle G := by dsimp [G]; decide +kernel
  have he : G.edgeFinset.Nonempty := by
    exact ⟨s((0 : Fin 11),(9 : Fin 11)), SimpleGraph.mem_edgeFinset.mpr (by decide)⟩
  have hU : U.Nonempty := Finset.card_pos.mp (by omega)
  have e : ∃ u v : Fin 11, s(u,v) ∈ U := by
    obtain ⟨s,hs⟩ := hU
    induction s using Sym2.inductionOn with
    | _ i j => exact ⟨i,j,hs⟩
  obtain ⟨three,sup⟩ := geometry 11 G C hf he hl ht hj (show B ≤ 3 by omega) e
  change 3 ≤ B at three
  obtain ⟨K,X,m,c,hx⟩ := finite U Finset.sdiff_subset (by omega) (by omega) sup
  exact ⟨K,X,m,c,show X.card ≤ B-U.card by omega⟩
