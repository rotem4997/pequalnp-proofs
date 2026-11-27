import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

-- A minimum cover of the residual graph can be chosen inside an original
-- seven-vertex cover except at the seventeen deletion masks in the first premise.
-- The other premises charge vertices dropped from a seven-cover and exclude the
-- exceptional masks for a short circuit. Edge zero is the first pair in es.
theorem PEqualNP.Outside.R_meta_2384_1
  (ordinary : let es : List (ℕ × ℕ) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  let G := edgeGraph 11 es
  let code := fun (U : Finset (Sym2 (Fin 11))) => BitVec.ofNat 16 (tableIndex fun i : Fin 16 =>
    let e := es.getD i.val (0,0)
    decide (s(Fin.ofNat 11 e.1, Fin.ofNat 11 e.2) ∈ U))
  ∀ U : Finset (Sym2 (Fin 11)), code U ∉ ([36608,44800,44864,44992,48960,52992,53120,53184,57216,61184,61248,61312,61376,65280,65344,65408,65472] : List (BitVec 16)) →
    ∃ K T : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K ∧ G.IsVertexCover (↑T) ∧ K ⊆ T ∧ T.card = 7)
  (charge : let es : List (ℕ × ℕ) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  let G := edgeGraph 11 es
  ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
    let U := Ustar G C
    let B := 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
    U.card ≤ B → B < 2*U.card →
    ∀ T X : Finset (Fin 11), T.card = 7 → G.IsVertexCover (↑T) → X ⊆ T →
      (G.deleteEdges ↑U).IsVertexCover (↑(T \ X)) → X.card ≤ B-U.card)
  (rare : let es : List (ℕ × ℕ) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  let G := edgeGraph 11 es
  let code := fun (U : Finset (Sym2 (Fin 11))) => BitVec.ofNat 16 (tableIndex fun i : Fin 16 =>
    let e := es.getD i.val (0,0)
    decide (s(Fin.ofNat 11 e.1, Fin.ofNat 11 e.2) ∈ U))
  ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
    let U := Ustar G C
    let B := 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
    U.card ≤ B → B < 2*U.card →
    code U ∉ ([36608,44800,44864,44992,48960,52992,53120,53184,57216,61184,61248,61312,61376,65280,65344,65408,65472] : List (BitVec 16)))
  : let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   x2.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x2 →       PEqualNP.TopForm.TopForm x1 x2 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →           have x7 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;           have x8 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card;           x7.card ≤ x8 → x8 < (2 : ℕ) * x7.card → ∃ (x11 : Finset (Fin (11 : ℕ))) (x12 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x7) x11 ∧ x1.IsVertexCover ↑(x11 ∪ x12) ∧ x12.card ≤ x8 - x7.card := by
  let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  dsimp only
  intro C short least top hj hlo hhi
  obtain ⟨K,T,hk,ht,hkt,hs⟩ := ordinary (Ustar G C) (rare C short least top hj hlo hhi)
  let X := T \ K
  have xt : X ⊆ T := Finset.sdiff_subset
  have back : T \ X = K := by
    ext i
    simp only [X, Finset.mem_sdiff]
    constructor
    · rintro ⟨hi,h⟩
      by_contra hk'
      exact h ⟨hi,hk'⟩
    · intro hi
      exact ⟨hkt hi, fun h => h.2 hi⟩
  have joined : K ∪ X = T := by
    ext i
    simp only [X, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (h | h)
      · exact hkt h
      · exact h.1
    · intro h
      by_cases hK : i∈K
      · exact Or.inl hK
      · exact Or.inr ⟨h,hK⟩
  have bd := charge C short least top hj hlo hhi T X hs ht xt (by rw [back]; exact hk.1)
  exact ⟨K,X,hk, by rw [joined]; exact ht,bd⟩
