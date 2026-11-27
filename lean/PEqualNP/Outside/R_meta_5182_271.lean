import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

-- Forcing a cover away from the four distinguished vertices leaves a singleton
-- and three disjoint pairs. Each contributes an explicit loss when its edges
-- to the four vertices disappear. A single deleted internal edge is mandatory.
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 8000 in
theorem PEqualNP.Outside.R_meta_5182_271
    (profile : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (U : Finset (Sym2 (Fin 11))),
  let S : Finset (Fin 11) := {3,8,9,10}
  let M : Finset (Fin 11 × Fin 11) := {(1,4),(2,5),(6,7)}
  (∀ p ∈ M, G.Adj p.1 p.2) →
  let H := G.deleteEdges (U : Set (Sym2 (Fin 11)))
  let N := (Finset.univ \ S).filter fun v => ∃ a ∈ S, H.Adj a v
  let blind (v : Fin 11) := ∀ a ∈ S, G.Adj a v → s(a,v) ∈ U
  N.card + (M.filter fun p => H.Adj p.1 p.2 ∧ p.1 ∉ N ∧ p.2 ∉ N).card +
    (if blind 0 then 1 else 0) + (M.filter fun p => blind p.1 ∨ blind p.2).card +
    (M.filter fun p => blind p.1 ∧ blind p.2 ∧ s(p.1,p.2) ∈ U).card = 7)
    (positive : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
  NoFourCycle G → G.edgeFinset.Nonempty → IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
  ∀ u v : Fin n, s(u,v) ∈ Ustar G C →
    1 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card)
    (charge : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit),
      G = edgeGraph 11 ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97].map
        fun e : ℕ => (e / 11,e % 11)) →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C → C.size < 22 →
      (∃ i j, junk G C = {i,j} ∧ InCone 11 C i j) →
      let U := Ustar G C
      let S : Finset (Fin 11) := {3,8,9,10}
      let M : Finset (Fin 11 × Fin 11) := {(1,4),(2,5),(6,7)}
      let blind (v : Fin 11) := ∀ a ∈ S, G.Adj a v → s(a,v) ∈ U
      let p := 2 * (centreless G C).card + (orN G C \ lam G C).card
      s(8,9) ∈ U → 1 ≤ p → 3 ≤ U.card →
      (4 ≤ U.card ∨ ∃ v ∈ Finset.univ \ S, blind v) →
      U.card + (if blind 0 then 1 else 0) + (M.filter fun q => blind q.1 ∨ blind q.2).card +
        (M.filter fun q => blind q.1 ∧ blind q.2 ∧ s(q.1,q.2) ∈ U).card ≤ 2 + p) :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x3.size < (22 : ℕ) →           (∃ (x8 : ℕ) (x9 : ℕ), PEqualNP.TopForm.junk x1 x3 = {x8, x9} ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x8 x9) →             have x9 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             let x10 : SimpleGraph (Fin (11 : ℕ)) := x1.deleteEdges ↑x9;             have x11 : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};             have x12 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};             ∀ x13 ⊆ x11,               x13 = ∅ →                 (∀ x16 ∈ x11 \ x13, ∀ x18 ∈ x11 \ x13, ¬x10.Adj x16 x18) →                   have x17 : Finset (Fin (11 : ℕ)) := {x17 ∈ Finset.univ \ x11 | ∃ x18 ∈ x11 \ x13, x10.Adj x18 x17};                   have x18 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {x18 ∈ x12 | x10.Adj x18.1 x18.2 ∧ x18.1 ∉ x17 ∧ x18.2 ∉ x17};                   (5 : ℕ) + x9.card ≤ x13.card + x17.card + x18.card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card := by
  classical
  intro G inst C hG least form size nested U H S M T subset empty independent
  subst T
  intro N P
  rw [Finset.card_empty, Nat.zero_add]
  have indep : ∀ a ∈ S, ∀ b ∈ S, ¬H.Adj a b := by
    simpa only [Finset.sdiff_empty] using independent
  have active : G.Adj (8 : Fin 11) 9 := by rw [hG]; decide +kernel
  have marked : s(8,9) ∈ U := by
    by_contra kept
    exact indep 8 (by decide) 9 (by decide) (SimpleGraph.deleteEdges_adj.mpr ⟨active,kept⟩)
  have nonempty : G.edgeFinset.Nonempty := ⟨s(8,9),SimpleGraph.mem_edgeFinset.mpr active⟩
  have nofour : NoFourCycle G := by
    let es : List (ℕ × ℕ) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
      (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
    have checked : NoFourCycle (edgeGraph 11 es) := by decide +kernel
    have carry (A B : SimpleGraph (Fin 11)) [da : DecidableRel A.Adj] [db : DecidableRel B.Adj]
        (eq : A = B) (h : @NoFourCycle 11 A da) : @NoFourCycle 11 B db := by
      subst B
      have same : db = da := Subsingleton.elim _ _
      subst db
      exact h
    exact carry (edgeGraph 11 es) G hG.symm checked
  have pos := positive 11 G C nofour nonempty least form 8 9 marked
  let V : Finset (Fin 11) := {0,1,2,4,5,6,7}
  have complement : Finset.univ \ S = V := by decide +kernel
  have nform : N = (Finset.univ \ S).filter (fun v => ∃ i ∈ S, H.Adj i v) := by
    dsimp only [N]; rw [Finset.sdiff_empty]
  have nV : N ⊆ V := by
    rw [nform,← complement]; exact Finset.filter_subset _ _
  have vcard : V.card = 7 := by decide +kernel
  let blind (v : Fin 11) := ∀ a ∈ S, G.Adj a v → s(a,v) ∈ U
  have visible (v : Fin 11) (hv : v ∈ V) (hb : ¬blind v) : v ∈ N := by
    rw [nform]
    refine Finset.mem_filter.mpr ⟨complement.symm ▸ hv,?_⟩
    by_contra! none
    apply hb
    intro i hi a
    by_contra kept
    exact none i hi (SimpleGraph.deleteEdges_adj.mpr ⟨a,kept⟩)
  by_cases three : 3 ≤ U.card
  · by_cases damage : 4 ≤ U.card ∨ ∃ v ∈ Finset.univ \ S, blind v
    · have matching : ∀ q ∈ M, G.Adj q.1 q.2 := by rw [hG]; decide +kernel
      have exactProfile := profile G U matching
      have balance := charge G C hG least form size nested marked pos three damage
      have exactCount : N.card + P.card + (if blind 0 then 1 else 0) +
        (M.filter fun q => blind q.1 ∨ blind q.2).card +
        (M.filter fun q => blind q.1 ∧ blind q.2 ∧ s(q.1,q.2) ∈ U).card = 7 := by
          dsimp only [P]
          rw [nform]
          exact exactProfile
      change U.card + (if blind 0 then 1 else 0) + (M.filter fun q => blind q.1 ∨ blind q.2).card +
        (M.filter fun q => blind q.1 ∧ blind q.2 ∧ s(q.1,q.2) ∈ U).card ≤
        2 + (2 * (centreless G C).card + (orN G C \ lam G C).card) at balance
      omega
    · have complete : V ⊆ N := by
        intro v hv
        exact visible v hv (fun h => damage (Or.inr ⟨v,complement.symm ▸ hv,h⟩))
      have total := Finset.card_le_card complete
      have atMost : ¬4 ≤ U.card := fun h => damage (Or.inl h)
      omega
  · let w (v : Fin 11) : Fin 11 :=
      if v = 0 then 9 else if v = 1 then 8 else if v = 2 then 10
      else if v = 4 then 8 else if v = 5 then 8 else 3
    let e (v : Fin 11) := s(w v,v)
    have spokes : ∀ v ∈ V, w v ∈ S ∧ G.Adj (w v) v ∧ e v ≠ s(8,9) := by
      rw [hG]; decide +kernel
    have unique : ∀ a ∈ V, ∀ b ∈ V, e a = e b → a = b := by decide +kernel
    have imageSmall : (V \ N).image e ⊆ U.erase s(8,9) := by
      intro t ht
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨hin,hout⟩ := Finset.mem_sdiff.mp hv
      obtain ⟨hw,adj,diff⟩ := spokes v hin
      apply Finset.mem_erase.mpr
      refine ⟨diff,?_⟩
      by_contra kept
      exact hout (visible v hin (fun h => kept (h (w v) hw adj)))
    have injective : Set.InjOn e (↑(V \ N) : Set (Fin 11)) := by
      intro a ha b hb eq
      exact unique a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1 eq
    have count := Finset.card_le_card imageSmall
    rw [Finset.card_image_of_injOn injective] at count
    have erased := Finset.card_erase_add_one marked
    have split := Finset.card_sdiff_add_card_eq_card nV
    omega

-- The following is the complete proof script for the first child.
--   classical
--   intro G inst U S M hM H N blind
--   let V : Finset (Fin 11) := {0,1,2,4,5,6,7}
--   have complement : Finset.univ \ S = V := by decide +kernel
--   have outside (v : Fin 11) (hv : v ∈ V) : v ∉ S :=
--     (Finset.mem_sdiff.mp (complement.symm ▸ hv)).2
--   have visible (v : Fin 11) (hv : v ∉ S) : v ∈ N ↔ ¬blind v := by
--     constructor
--     · intro h hb
--       obtain ⟨i, hi, adj⟩ := (Finset.mem_filter.mp h).2
--       obtain ⟨old, kept⟩ := SimpleGraph.deleteEdges_adj.mp adj
--       exact kept (hb i hi old)
--     · intro h
--       refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩, ?_⟩
--       by_contra! none
--       apply h
--       intro i hi old
--       by_contra kept
--       exact none i hi (SimpleGraph.deleteEdges_adj.mpr ⟨old,kept⟩)
--   have nv : N = V.filter (fun v => ¬blind v) := by
--     ext v
--     constructor
--     · intro h
--       have hv := complement ▸ (Finset.mem_filter.mp h).1
--       exact Finset.mem_filter.mpr ⟨hv,(visible v (outside v hv)).mp h⟩
--     · intro h
--       obtain ⟨hv,hb⟩ := Finset.mem_filter.mp h
--       exact (visible v (outside v hv)).mpr hb
--   have ends : ∀ p ∈ M, p.1 ∈ V ∧ p.2 ∈ V := by decide +kernel
--   have pm : (M.filter fun p => H.Adj p.1 p.2 ∧ p.1 ∉ N ∧ p.2 ∉ N) =
--       M.filter (fun p => s(p.1,p.2) ∉ U ∧ blind p.1 ∧ blind p.2) := by
--     apply Finset.filter_congr
--     intro p hp
--     obtain ⟨hu,hv⟩ := ends p hp
--     simp [H, hM p hp, visible p.1 (outside _ hu), visible p.2 (outside _ hv)]
--   have vertices (f : Fin 11 → ℕ) : (∑ i ∈ V, f i) =
--       f 0 + (f 1 + (f 2 + (f 4 + (f 5 + (f 6 + f 7))))) := by
--     dsimp only [V]
--     repeat rw [Finset.sum_insert (by decide)]
--     rw [Finset.sum_singleton]
--   have pairs (f : Fin 11 × Fin 11 → ℕ) : (∑ i ∈ M, f i) =
--       f (1,4) + (f (2,5) + f (6,7)) := by
--     dsimp only [M]
--     repeat rw [Finset.sum_insert (by decide)]
--     rw [Finset.sum_singleton]
--   have one : (if ¬blind 0 then 1 else 0) + (if blind 0 then 1 else 0) = 1 := by
--     by_cases h : blind 0 <;> simp [h]
--   have two (u v : Fin 11) : (if ¬blind u then 1 else 0) + (if ¬blind v then 1 else 0) +
--       (if s(u,v) ∉ U ∧ blind u ∧ blind v then 1 else 0) +
--       (if blind u ∨ blind v then 1 else 0) +
--       (if blind u ∧ blind v ∧ s(u,v) ∈ U then 1 else 0) = 2 := by
--     by_cases hu : blind u <;> by_cases hv : blind v <;> by_cases he : s(u,v) ∈ U <;> simp [*]
--   rw [pm,nv]
--   simp only [Finset.card_filter,vertices,pairs]
--   have first := two 1 4
--   have second := two 2 5
--   have third := two 6 7
--   omega

-- The second child uses two published proofs from this repository.
-- L_meta_1490 by willakone, commit 54c3478931cf7a9745722fe4fab89d93e7094a9a.
-- L_meta_2695 by Hemmurs, commit 5f1698b278b697840dda9a85de5fecd6cf90b943.
-- The following is the complete deduction from those two proofs.
--   classical
--   intro n G inst C nofour nonempty least form u v miss
--   obtain ⟨a,ha,b,j,hj,_,reached,_⟩ :=
--     (PEqualNP.Outside.L_meta_1490 n G C nofour nonempty least form).2 u v miss
--   rcases PEqualNP.Outside.L_meta_2695 n G C least.1.2.2 a ha b j hj reached with centered | outside
--   · have h : 0 < (centreless G C).card := Finset.card_pos.mpr ⟨a,centered⟩
--     omega
--   · have h := Finset.card_pos.mpr outside
--     omega

-- Independent count for three deleted edges, with edge positions numbered from zero.
-- theorem three_deletions :
--     let E : List (ℕ × ℕ) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
--       (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
--     let S : List ℕ := [3,8,9,10]
--     let V : List ℕ := [0,1,2,4,5,6,7]
--     let orders := (List.range 15).flatMap fun i =>
--       ((List.range 15).filter fun j => i < j).map fun j => (i,j)
--     let lost (p : ℕ × ℕ) := V.filter fun v => !(E.zipIdx.any fun q =>
--       q.2 != 15 && q.2 != p.1 && q.2 != p.2 &&
--         ((q.1.1 == v && S.contains q.1.2) || (q.1.2 == v && S.contains q.1.1)))
--     orders.length = 105 ∧ (orders.filter fun p => (lost p).isEmpty).length = 73 ∧
--       (orders.filter fun p => (lost p).length = 1).length = 31 ∧
--       (orders.filter fun p => 2 ≤ (lost p).length) = [(3,5)] := by
--   decide +kernel
