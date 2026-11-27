import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership

-- The finite graph profile supplies the gate allowance for each number of residual edges.
-- Below this allowance it suffices to exhibit a surviving edge outside sets of one size.
theorem PEqualNP.Outside.R_meta_2704_2
    (profile : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj], G = edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] →
      ∀ (U : Finset (Sym2 (Fin 11))), U ⊆ G.edgeFinset → ∀ T : Finset (Fin 11),
      (∀ u v, (G.deleteEdges ↑U).Adj u v → u ∈ T ∨ v ∈ T) →
      5 + U.card ≤ T.card + [0,0,2,4,5,7,8,9,11,12,13,14,16,17,18,19,21].getD U.card 0)
    (escape : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit),
      G = edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] → IsLeastAO G C → PEqualNP.TopForm.TopForm G C → C.size < 22 →
      (∃ i j, junk G C = {i,j} ∧ InCone 11 C i j) →
      let r := (Ustar G C).card
      let k := 2 * (centreless G C).card + (orN G C \ lam G C).card
      k < [0,0,2,4,5,7,8,9,11,12,13,14,16,17,18,19,21].getD r 0 → ∀ T : Finset (Fin 11), T.card = min 11 (4+r-k) →
      ∃ u v : Fin 11, u ∉ T ∧ v ∉ T ∧ G.Adj u v ∧ s(u,v) ∈ starEdges G C) :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x3.size < (22 : ℕ) →           (∃ (x8 : ℕ) (x9 : ℕ), PEqualNP.TopForm.junk x1 x3 = {x8, x9} ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x8 x9) →             have x9 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             let x10 : SimpleGraph (Fin (11 : ℕ)) := x1.deleteEdges ↑x9;             have x11 : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};             have x12 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};             ∀ x13 ⊆ x11,               (∀ x15 ∈ x11 \ x13, ∀ x17 ∈ x11 \ x13, ¬x10.Adj x15 x17) →                 have x16 : Finset (Fin (11 : ℕ)) := {x16 ∈ Finset.univ \ x11 | ∃ x17 ∈ x11 \ x13, x10.Adj x17 x16};                 have x17 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {x17 ∈ x12 | x10.Adj x17.1 x17.2 ∧ x17.1 ∉ x16 ∧ x17.2 ∉ x16};                 (5 : ℕ) + x9.card ≤ x13.card + x16.card + x17.card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card := by
  intro G inst C graph least top short nested U H S M B sub valid F P
  classical
  let K := (B ∪ F) ∪ P.image Prod.fst
  have shape0 : ∀ u v, (edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]).Adj u v →
      u ∈ S ∨ v ∈ S ∨ (u,v) ∈ M ∨ (v,u) ∈ M := by decide +kernel
  have shape : ∀ u v, H.Adj u v → u ∈ S ∨ v ∈ S ∨ (u,v) ∈ M ∨ (v,u) ∈ M := by
    intro u v h
    apply shape0
    rw [← graph]
    exact (SimpleGraph.deleteEdges_adj.mp h).1
  have forced {u v : Fin 11} (adj : H.Adj u v) (us : u ∈ S) (ub : u ∉ B) (vb : v ∉ B) : v ∈ F := by
    have um := Finset.mem_sdiff.mpr ⟨us,ub⟩
    have vs : v ∉ S := fun vs => valid u um v (Finset.mem_sdiff.mpr ⟨vs,vb⟩) adj
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,vs⟩,u,um,adj⟩
  have covers : ∀ u v, H.Adj u v → u ∈ K ∨ v ∈ K := by
    intro u v adj
    by_contra! neither
    have ub : u ∉ B := fun hu => neither.1 (Finset.mem_union_left _ (Finset.mem_union_left _ hu))
    have vb : v ∉ B := fun hv => neither.2 (Finset.mem_union_left _ (Finset.mem_union_left _ hv))
    have uf : u ∉ F := fun hu => neither.1 (Finset.mem_union_left _ (Finset.mem_union_right _ hu))
    have vf : v ∉ F := fun hv => neither.2 (Finset.mem_union_left _ (Finset.mem_union_right _ hv))
    rcases shape u v adj with us|vs|m|m
    · exact vf (forced adj us ub vb)
    · exact uf (forced adj.symm vs vb ub)
    · have h : (u,v) ∈ P := Finset.mem_filter.mpr ⟨m,adj,uf,vf⟩
      exact neither.1 (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,h,rfl⟩))
    · have h : (v,u) ∈ P := Finset.mem_filter.mpr ⟨m,adj.symm,vf,uf⟩
      exact neither.2 (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_,h,rfl⟩))
  have size : K.card ≤ B.card + F.card + P.card :=
    (Finset.card_union_le ..).trans (Nat.add_le_add (Finset.card_union_le ..) Finset.card_image_le)
  let k := 2*(centreless G C).card+(orN G C \ lam G C).card
  let b := [0,0,2,4,5,7,8,9,11,12,13,14,16,17,18,19,21].getD U.card 0
  have enough := profile G graph U Finset.sdiff_subset K covers
  change 5+U.card ≤ K.card+b at enough
  by_contra fail
  have miss : B.card+F.card+P.card+k < 5+U.card := by dsimp [k]; omega
  have lo : k < b := by omega
  have upper : K.card ≤ min 11 (4+U.card-k) := by
    have bound := Finset.card_le_univ K
    simp at bound
    omega
  obtain ⟨T,hKT,_,ht⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ K) upper
    (show min 11 (4+U.card-k) ≤ (Finset.univ : Finset (Fin 11)).card by simp)
  obtain ⟨u,v,ut,vt,adj,star⟩ := escape G C graph least top short nested lo T ht
  have survives : H.Adj u v := SimpleGraph.deleteEdges_adj.mpr ⟨adj,fun hu => (Finset.mem_sdiff.mp hu).2 star⟩
  exact (covers u v survives).elim (fun h => ut (hKT h)) (fun h => vt (hKT h))
