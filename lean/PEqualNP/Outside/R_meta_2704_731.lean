import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_2704_731
    (twoEdges : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit),
      G = edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] →
      IsLeastAO G C → TopForm G C → C.size < 22 →
      (∃ i j, junk G C = {i,j} ∧ InCone 11 C i j) →
      (Ustar G C).card = 2 → 2 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card)
    (threeEdges : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit),
      G = edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] →
      IsLeastAO G C → TopForm G C → C.size < 22 →
      (∃ i j, junk G C = {i,j} ∧ InCone 11 C i j) →
      (Ustar G C).card = 3 → 4 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card)
    (replace : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit),
      G = edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] →
      IsLeastAO G C → TopForm G C → C.size < 22 →
      (∃ i j, junk G C = {i,j} ∧ InCone 11 C i j) →
      let U := Ustar G C
      4 ≤ U.card → ∀ T : Finset (Fin 11),
      (∀ u v, (G.deleteEdges ↑U).Adj u v → u ∈ T ∨ v ∈ T) →
      T.card + (2 * (centreless G C).card + (orN G C \ lam G C).card) < 5 + U.card →
      ∃ D : Circuit, IsAO2 11 D ∧ circuitFun 11 D = graphFun G ∅ ∧ D.size < C.size) :
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
  have endpoint (e : Sym2 (Fin 11)) : ∃ v, v ∈ e := by
    induction e using Sym2.ind with
    | _ u v => exact ⟨u, Sym2.mem_mk_left u v⟩
  let chooseVertex (e : Sym2 (Fin 11)) := Classical.choose (endpoint e)
  let Kfull := K ∪ U.image chooseVertex
  have coversFull (u v : Fin 11) (adj : G.Adj u v) : u ∈ Kfull ∨ v ∈ Kfull := by
    by_cases gone : s(u,v) ∈ U
    · have memPick : chooseVertex s(u,v) ∈ Kfull :=
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, gone, rfl⟩)
      rcases Sym2.mem_iff.mp (Classical.choose_spec (endpoint s(u,v))) with eq | eq
      · exact Or.inl (eq ▸ memPick)
      · exact Or.inr (eq ▸ memPick)
    · have left := covers u v (SimpleGraph.deleteEdges_adj.mpr ⟨adj, gone⟩)
      exact left.imp (Finset.mem_union_left _) (Finset.mem_union_left _)
  have fullCard : Kfull.card ≤ K.card + U.card :=
    (Finset.card_union_le ..).trans (Nat.add_le_add_left Finset.card_image_le _)
  let w (v : Fin 11) : ℕ := if v ∈ Kfull then 1 else 0
  have edgeWeight {u v : Fin 11} (adj : G.Adj u v) : 1 ≤ w u + w v := by
    rcases coversFull u v adj with hu | hv
    · simp [w, hu]
    · simp [w, hv]
  have pattern : ∀ u v, (edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]).Adj u v → 1 ≤ w u + w v := by
    intro u v adj
    apply edgeWeight
    rwa [graph]
  have triA : 2 ≤ w 1 + w 4 + w 8 := by
    have e14 := pattern 1 4 (by decide)
    have e18 := pattern 1 8 (by decide)
    have e48 := pattern 4 8 (by decide)
    omega
  have triB : 2 ≤ w 3 + w 6 + w 7 := by
    have e36 := pattern 3 6 (by decide)
    have e37 := pattern 3 7 (by decide)
    have e67 := pattern 6 7 (by decide)
    omega
  have pentagon : 3 ≤ w 0 + w 2 + w 5 + w 9 + w 10 := by
    have e09 := pattern 0 9 (by decide)
    have e0ten := pattern 0 10 (by decide)
    have e25 := pattern 2 5 (by decide)
    have e2ten := pattern 2 10 (by decide)
    have e59 := pattern 5 9 (by decide)
    omega
  have total : Kfull.card = ∑ i : Fin 11, w i := by
    exact Finset.card_eq_sum_ite (Finset.subset_univ Kfull)
  have expanded : (∑ i : Fin 11, w i) =
      w 0 + w 1 + w 2 + w 3 + w 4 + w 5 + w 6 + w 7 + w 8 + w 9 + w 10 := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, add_assoc]
    rfl
  let k := 2 * (centreless G C).card + (orN G C \ lam G C).card
  suffices charge : 5 + U.card ≤ B.card + F.card + P.card + k by
    dsimp only [k] at charge
    omega
  have lowerCover : 7 ≤ K.card + U.card := by omega
  by_cases small : U.card ≤ 1
  · omega
  by_cases htwo : U.card = 2
  · have hk : 2 ≤ k := twoEdges G C graph least top short nested htwo
    omega
  by_cases hthree : U.card = 3
  · have hk : 4 ≤ k := threeEdges G C graph least top short nested hthree
    omega
  have four : 4 ≤ U.card := by omega
  by_contra fail
  have failK : K.card + k < 5 + U.card := by omega
  obtain ⟨D, hAO, heval, hless⟩ :=
    replace G C graph least top short nested four K covers failK
  exact (Nat.not_lt_of_ge (least.2.2 D hAO heval)) hless
