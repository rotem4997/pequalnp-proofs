import Mathlib.Data.Finset.Powerset
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

set_option maxRecDepth 12000 in
set_option maxHeartbeats 7500000 in
theorem PEqualNP.Outside.R_meta_4131_1
    (equalCharge :
      let es : List (ℕ × ℕ) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      let G := edgeGraph 11 es
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
        let U := Ustar G C
        let B := 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        0 < U.card → B = U.card →
        ∀ p ∈ ([(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(5,9),(6,7)] : List (Fin 11 × Fin 11)),
          s(p.1,p.2) ∉ U)
    (middleCharge :
      let es : List (ℕ × ℕ) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      let G := edgeGraph 11 es
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
        let U := Ustar G C
        let B := 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        ∀ d : ℕ, 1 ≤ d → d ≤ 5 → B = U.card + d → B < 2*U.card →
          ([2,3,5,8,12] : List ℕ).getD (d-1) 0 ≤ U.card →
          ∀ T K : Finset (Fin 11), T.card = 7 → G.IsVertexCover ↑T → K ⊆ T →
            K.card + d = 6 → (G.deleteEdges ↑U).IsVertexCover ↑K → False)
    (allEdges :
      let es : List (ℕ × ℕ) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      let G := edgeGraph 11 es
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
        (Ustar G C).card = 16 →
        2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card = 22 → False) :
    have es : List (ℕ × ℕ) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
      (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
    let G : SimpleGraph (Fin 11) := edgeGraph 11 es
    ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
      have U : Finset (Sym2 (Fin 11)) := Ustar G C
      have B : ℕ := 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
      U.card ≤ B → B < 2*U.card → ∀ T X : Finset (Fin 11), T.card = 7 → G.IsVertexCover ↑T →
        X ⊆ T → (G.deleteEdges ↑U).IsVertexCover ↑(T \ X) → X.card ≤ B - U.card := by
  intro es G C size least top junkCount U B hlo hhi T X hT coverT hX coverCut
  let d := B - U.card
  change X.card ≤ d
  by_contra! fail
  have xle : X.card ≤ 7 := (Finset.card_le_card hX).trans_eq hT
  have d6 : d ≤ 6 := by omega
  have budget : B = U.card + d := by dsimp [d]; omega
  obtain ⟨Y, hYX, hY⟩ := Finset.exists_subset_card_eq (show d + 1 ≤ X.card by omega)
  let K := T \ Y
  have Ysub : Y ⊆ T := hYX.trans hX
  have Ksub : K ⊆ T := Finset.sdiff_subset
  have Kcard : K.card + d = 6 := by
    have sum : K.card + Y.card = T.card := Finset.card_sdiff_add_card_eq_card Ysub
    omega
  have cutSub : T \ X ⊆ K := by
    intro v hv
    have h := Finset.mem_sdiff.mp hv
    exact Finset.mem_sdiff.mpr ⟨h.1, fun hvY => h.2 (hYX hvY)⟩
  have cutK : (G.deleteEdges ↑U).IsVertexCover ↑K := by
    intro a b h
    exact (coverCut h).imp (fun mem => cutSub mem) (fun mem => cutSub mem)
  let single : List (Fin 11 × Fin 11) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),
    (3,6),(3,7),(4,8),(5,9),(6,7)]
  by_cases zero : d = 0
  · have six : K.card = 6 := by omega
    have anyPair : ∀ K : Finset (Fin 11), K.card = 6 →
        single.any (fun p => decide (p.1 ∉ K ∧ p.2 ∉ K)) = true := by decide +kernel
    obtain ⟨p, hp, hm⟩ := List.any_eq_true.mp (anyPair K six)
    have miss : p.1 ∉ K ∧ p.2 ∉ K := of_decide_eq_true hm
    have isEdge : ∀ p ∈ single, G.Adj p.1 p.2 := by decide +kernel
    have upos : 0 < U.card := by omega
    have beq : B = U.card := by omega
    have out : s(p.1,p.2) ∉ U := equalCharge C size least top junkCount upos beq p hp
    have edge : (G.deleteEdges ↑U).Adj p.1 p.2 := SimpleGraph.deleteEdges_adj.mpr ⟨isEdge p hp, out⟩
    exact (cutK edge).elim miss.1 miss.2
  let ordered : Finset (Fin 11 × Fin 11) := {(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
    (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)}
  let missing (K : Finset (Fin 11)) := ordered.filter fun p => p.1 ∉ K ∧ p.2 ∉ K
  let minimum (k : ℕ) := ([16,12,8,5,3,2,1] : List ℕ).getD k 0
  have cardinalLower : ∀ K : Finset (Fin 11), minimum K.card ≤ (missing K).card := by decide +kernel
  have orderedEdges : ∀ p ∈ ordered, p.1 < p.2 ∧ G.Adj p.1 p.2 := by decide +kernel
  let make (p : Fin 11 × Fin 11) : Sym2 (Fin 11) := s(p.1,p.2)
  have inject : Set.InjOn make ↑(missing K) := by
    intro a ha b hb equal
    have aord := (orderedEdges a (Finset.mem_filter.mp ha).1).1
    have bord := (orderedEdges b (Finset.mem_filter.mp hb).1).1
    rcases Sym2.eq_iff.mp equal with ⟨e₁,e₂⟩ | ⟨e₁,e₂⟩
    · exact Prod.ext e₁ e₂
    · exact (not_lt_of_gt (e₁ ▸ e₂ ▸ aord) bord).elim
  have subset : (missing K).image make ⊆ U := by
    intro e he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨listed, left, right⟩ := Finset.mem_filter.mp hp
    by_contra h
    have adj : (G.deleteEdges ↑U).Adj p.1 p.2 := SimpleGraph.deleteEdges_adj.mpr ⟨(orderedEdges p listed).2, h⟩
    exact (cutK adj).elim left right
  have threshold : minimum K.card ≤ U.card := by
    have lower := cardinalLower K
    rw [← Finset.card_image_of_injOn inject] at lower
    exact lower.trans (Finset.card_le_card subset)
  by_cases six : d = 6
  · have card0 : K.card = 0 := by omega
    have ulo : 16 ≤ U.card := by simpa [card0, minimum] using threshold
    have edgeNumber : G.edgeFinset.card = 16 := by decide +kernel
    have usub : U ⊆ G.edgeFinset := Finset.sdiff_subset
    have uhi : U.card ≤ 16 := (Finset.card_le_card usub).trans_eq edgeNumber
    have ueq : U.card = 16 := by omega
    have beq : B = 22 := by omega
    exact allEdges C size least top junkCount ueq beq
  have mid : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 := by omega
  have Kc : K.card = 6 - d := by omega
  rw [Kc] at threshold
  have count : ([2,3,5,8,12] : List ℕ).getD (d - 1) 0 ≤ U.card := by
    rcases mid with h | h | h | h | h <;> simpa [h, minimum] using threshold
  exact middleCharge C size least top junkCount d (by omega) (by omega) budget hhi count T K hT coverT Ksub Kcard cutK
