import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 3200000 in
theorem PEqualNP.Outside.R_meta_5968_743
    (profile :
      let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ U ⊆ G.edgeFinset, ∀ K : Finset (Fin 11),
      (G.deleteEdges (U : Set (Sym2 (Fin 11)))).IsVertexCover (K : Set (Fin 11)) →
      let loss := fun m : ℕ => ((U.filter (fun e => ∀ p : Fin 11, p ∈ e → m.testBit (p + (0 : Fin 11)).val = true)).card + 1) / 2
      7 ≤ K.card + (loss 274 + loss 200 + loss 1573) ∧ 16 ≤ 4 * K.card + U.card)
    (small :
      let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ (C : Circuit) (a b : ℕ), IsLeastAO G C → TopForm G C → C.size < 22 →
      junk G C = {a,b} → let U := Ustar G C
      U.card ≤ 2 → ∀ K : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) K →
      5 + U.card ≤ K.card + 2 * (centreless G C).card + (orN G C \ lam G C).card)
    (hard :
      let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ (C : Circuit) (a b : ℕ),
      let w := wmax G C
      let e := gammaE G C
      let A := fun j : ℕ => (e j).filter (fun h => ∃ z ∈ w j, z ∈ h)
      let I := e a ∩ e b
      let good := ∀ x, gateVal 11 C a x = true → gateVal 11 C b x = true → graphFun G ∅ x = true
      let U := Ustar G C
      let H := 2 * (centreless G C).card + (orN G C \ lam G C).card
      let loss := fun m : ℕ => ((U.filter (fun e => ∀ p : Fin 11, p ∈ e → m.testBit (p + (0 : Fin 11)).val = true)).card + 1) / 2
      IsLeastAO G C → TopForm G C → C.size < 22 → junk G C = {a,b} →
      3 ≤ U.card → 4 * H ≤ 5 * U.card → 2 + H < U.card + (loss 274 + loss 200 + loss 1573) →
      (A a).card ≤ 7 ∧ (A b).card ≤ 7 ∧ (good → I.card ≤ 8) ∧
        (good ∨ (w a ∩ w b).Nonempty) →
      (∀ h ∈ U, h ∈ A a ∨ h ∈ A b ∨ good ∧ h ∈ I) →
      ∃ K, IsMinCover (G.deleteEdges ↑U) K ∧ 5 + U.card ≤ K.card + H) :
(∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         x3.size < (22 : ℕ) →           PEqualNP.TopForm.junk x1 x3 = {x4, x5} →             have x11 : ℕ → Finset (Sym2 (Fin (11 : ℕ))) := fun (x11 : ℕ) => {x12 ∈ PEqualNP.TopForm.gammaE x1 x3 x11 | ∃ x13 ∈ PEqualNP.TopForm.wmax x1 x3 x11, x13 ∈ x12};             have x12 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.gammaE x1 x3 x4 ∩ PEqualNP.TopForm.gammaE x1 x3 x5;             have x13 : Prop := ∀ (x13 : Fin (11 : ℕ) → Bool), PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x4 x13 = Bool.true → PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x5 x13 = Bool.true → PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ x13 = Bool.true;             have x14 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             (x11 x4).card ≤ (7 : ℕ) ∧ (x11 x5).card ≤ (7 : ℕ) ∧ (x13 → x12.card ≤ (8 : ℕ)) ∧ (x13 ∨ (PEqualNP.TopForm.wmax x1 x3 x4 ∩ PEqualNP.TopForm.wmax x1 x3 x5).Nonempty) → (∀ x16 ∈ x14, x16 ∈ x11 x4 ∨ x16 ∈ x11 x5 ∨ x13 ∧ x16 ∈ x12) → ∃ (x17 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x14) x17 ∧ (5 : ℕ) + x14.card ≤ x17.card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card) := by
  have arith : ∀ u k h d : ℕ, ¬ u ≤ 2 → 7 ≤ k + d → 16 ≤ 4 * k + u →
      ¬ 5 + u ≤ k + h → 3 ≤ u ∧ 4 * h ≤ 5 * u ∧ 2 + h < u + d := by
    clear profile small hard
    intro u k h d hu h₁ h₂ hn
    omega
  let P := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  let instP : DecidableRel P.Adj := inferInstanceAs (DecidableRel (edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]).Adj)
  intro G inst C a b graph
  subst G
  have heq : inst = instP := Subsingleton.elim _ _
  subst inst
  intro hL hT hsz hj
  intro stars shared safe rest hp hcover
  let U := Ustar P C
  let H := 2 * (centreless P C).card + (orN P C \ lam P C).card
  let loss := fun m : ℕ => ((U.filter (fun e => ∀ p : Fin 11, p ∈ e → m.testBit (p + (0 : Fin 11)).val = true)).card + 1) / 2
  classical
  have hx : ∃ n : ℕ, ∃ S : Finset (Fin 11),
      (P.deleteEdges ↑U).IsVertexCover (S : Set (Fin 11)) ∧ S.card = n :=
    ⟨11,Finset.univ,fun _ _ _ => Or.inl (Finset.mem_coe.mpr (Finset.mem_univ _)),Finset.card_fin 11⟩
  obtain ⟨K,hK,hn⟩ := Nat.find_spec hx
  have hmin : IsMinCover (P.deleteEdges ↑U) K :=
    ⟨hK,fun T ht => hn.symm ▸ Nat.find_min' hx ⟨T,ht,rfl⟩⟩
  by_cases hs : U.card ≤ 2
  · exact ⟨K,hmin,small C a b hL hT hsz hj hs K hmin⟩
  have hpairs : 7 ≤ K.card + (loss 274 + loss 200 + loss 1573) ∧ 16 ≤ 4 * K.card + U.card :=
    profile U Finset.sdiff_subset K hK
  by_cases good : 5 + U.card ≤ K.card + H
  · exact ⟨K,hmin,good.trans (Nat.add_assoc _ _ _).symm.le⟩
  · obtain ⟨h1,h2,h3⟩ := arith _ _ _ _ hs hpairs.1 hpairs.2 good
    obtain ⟨T,hm,ineq⟩ := hard C a b hL hT hsz hj h1 h2 h3 hp hcover
    refine ⟨T,hm,?_⟩
    exact ineq.trans (Nat.add_assoc _ _ _).symm.le