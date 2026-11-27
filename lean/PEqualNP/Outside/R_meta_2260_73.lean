import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

-- An earliest true junk gate has a true raw input on each side.
-- This turns the circuit traces on missing edges into tests on four finite
-- sets. A small circuit can fail the original count only in the indicated
-- range for the missing edges and the OR gates outside Lambda.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16000 in
theorem PEqualNP.Outside.R_meta_2260_73
    (raw : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C → ∀ x : Fin n → Bool,
      (∃ j ∈ junk G C, gateVal n C j x = true) →
      ∃ j ∈ junk G C, ∀ b : Fin 2, ∃ w ∈ side C j b, x w = true)
    (count : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (g h : ℕ),
      G = edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
         (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      junk G C = {g, h} → InCone 11 C g h →
      let U := Ustar G C
      let Z := centreless G C
      let p := 2 * Z.card + (orN G C \ lam G C).card
      3 + p ≤ 2 * U.card →
      (tops G C \ Z).card + p ≤ 4 + U.card →
      (∀ u v : Fin 11, s(u, v) ∈ U →
        ∃ j ∈ junk G C, ∀ b : Fin 2, u ∈ side C j b ∨ v ∈ side C j b) →
      22 ≤ C.size) :
    ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit) (g h : ℕ),
      G = edgeGraph 11
        [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
         (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      let tops' := tops G C
      let Z := centreless G C
      let U := Ustar G C
      (∀ j ∈ tops',
        let S := side C j
        (∀ u ∈ S 0, ∀ v ∈ S 1, G.Adj u v) ∧ ((S 0).card ≤ 1 ∨ (S 1).card ≤ 1)) →
      (∀ u v : Fin 11, s(u, v) ∈ U →
        ∃ j ∈ tops', ∃ (b : Fin 2) (k : ℕ), (k = g ∨ k = h) ∧
          gateVal 11 C j (pairInput u v) = true ∧
          PEqualNP.CleanedNonEdge.OrReaches 11 C (opnd C j b) k ∧
          gateVal 11 C k (pairInput u v) = true) →
      17 + (tops' \ Z).card + 2 * Z.card + (orN G C \ lam G C).card ≤ C.size + U.card →
      (∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K → K.card ≤ (tops' \ Z).card) →
      junk G C = {g, h} → InCone 11 C g h → 22 ≤ C.size := by
  classical
  intro G inst C g h hG least form
  dsimp only
  intro _ trace account cover junkPair nested
  let U := Ustar G C
  let Z := centreless G C
  let T := tops G C \ Z
  let p := 2 * Z.card + (orN G C \ lam G C).card
  change 17 + T.card + 2 * Z.card + (orN G C \ lam G C).card ≤ C.size + U.card at account
  have lowerCount : 17 + T.card + p ≤ C.size + U.card := by dsimp [p]; omega
  by_contra! short
  have low : T.card + p ≤ 4 + U.card := by omega
  let J := G.deleteEdges (U : Set (Sym2 (Fin 11)))
  have hasCover : ∃ k : ℕ, ∃ K : Finset (Fin 11), J.IsVertexCover (K : Set (Fin 11)) ∧ K.card = k :=
    ⟨11, Finset.univ, by simp, by simp⟩
  obtain ⟨K, hK, hk⟩ := Nat.find_spec hasCover
  have hmin : IsMinCover J K := by
    refine ⟨hK, fun S hs => ?_⟩
    exact hk ▸ Nat.find_min' hasCover ⟨S, hs, rfl⟩
  have hKt : K.card ≤ T.card := cover K hmin
  have contains (e : Sym2 (Fin 11)) : ∃ v, v ∈ e :=
    Sym2.ind (fun i j => ⟨i, Sym2.mem_mk_left i j⟩) e
  choose pick hp using contains
  let S := K ∪ U.image pick
  have full : G.IsVertexCover (S : Set (Fin 11)) := by
    intro i j hij
    by_cases hu : s(i, j) ∈ U
    · have hi := Finset.mem_image_of_mem pick hu
      rcases Sym2.mem_iff.mp (hp s(i, j)) with heq | heq
      · exact Or.inl (Finset.mem_union_right K (heq ▸ hi))
      · exact Or.inr (Finset.mem_union_right K (heq ▸ hi))
    · rcases hK (SimpleGraph.deleteEdges_adj.mpr ⟨hij, hu⟩) with hi | hj
      · exact Or.inl (Finset.mem_union_left _ hi)
      · exact Or.inr (Finset.mem_union_left _ hj)
  have hseven : 7 ≤ S.card := by
    let edges : List (Fin 11 × Fin 11) :=
      [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
       (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]
    have witness : ∀ W : Finset (Fin 11), W.card < 7 →
        ∃ e ∈ edges, e.1 ∉ W ∧ e.2 ∉ W ∧ e.1 ≠ e.2 := by decide +kernel
    by_contra! hsmall
    obtain ⟨e, he, h₁, h₂, hne⟩ := witness S hsmall
    have adj : G.Adj e.1 e.2 := by
      rw [hG]
      refine ⟨hne, Or.inl ?_⟩
      change (e.1.val, e.2.val) ∈ edges.map (fun v => (v.1.val, v.2.val))
      exact List.mem_map_of_mem he
    exact (full adj).elim h₁ h₂
  have hScard : S.card ≤ K.card + U.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_image_le _)
  have expensive : 3 + p ≤ 2 * U.card := by omega
  have masks (u v : Fin 11) (huv : s(u, v) ∈ U) :
      ∃ j ∈ junk G C, ∀ b : Fin 2, u ∈ side C j b ∨ v ∈ side C j b := by
    obtain ⟨a, _, b, j, hj, _, _, hval⟩ := trace u v huv
    have hjunk : j ∈ junk G C := by
      rw [junkPair]
      rcases hj with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    obtain ⟨k, hk', sides⟩ := raw 11 G C least form (pairInput u v) ⟨j, hjunk, hval⟩
    refine ⟨k, hk', fun b => ?_⟩
    obtain ⟨w, hw, htrue⟩ := sides b
    have eq : w = u ∨ w = v := of_decide_eq_true htrue
    exact eq.elim (fun h => Or.inl (h ▸ hw)) (fun h => Or.inr (h ▸ hw))
  have enough := count G C g h hG least form junkPair nested expensive low masks
  omega
