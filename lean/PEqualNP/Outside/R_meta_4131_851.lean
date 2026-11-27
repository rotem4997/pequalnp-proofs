import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm

set_option maxRecDepth 30000 in
set_option maxHeartbeats 8500000 in
theorem PEqualNP.Outside.R_meta_4131_851
    (small :
      let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
        let U := Ustar G C
        let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        ∀ d : ℕ, (d ≤ 2) → B = U.card+d → B < 2*U.card →
          ([1,2,3,5,8,12,16] : List ℕ).getD d 0 ≤ U.card →
          ∀ S : Finset (Fin 11), S.card = d+5 →
          (∃ I ⊆ S, I.card = 4 ∧ ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) →
          ∃ u ∈ S, ∃ v ∈ S, G.Adj u v ∧ s(u,v) ∉ U)
    (three :
      let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
        let U := Ustar G C
        let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        ∀ d : ℕ, (d = 3) → B = U.card+d → B < 2*U.card →
          ([1,2,3,5,8,12,16] : List ℕ).getD d 0 ≤ U.card →
          ∀ S : Finset (Fin 11), S.card = d+5 →
          (∃ I ⊆ S, I.card = 4 ∧ ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) →
          ∃ u ∈ S, ∃ v ∈ S, G.Adj u v ∧ s(u,v) ∉ U)
    (fourCase :
      let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
        let U := Ustar G C
        let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        ∀ d : ℕ, (d = 4) → B = U.card+d → B < 2*U.card →
          ([1,2,3,5,8,12,16] : List ℕ).getD d 0 ≤ U.card →
          ∀ S : Finset (Fin 11), S.card = d+5 →
          (∃ I ⊆ S, I.card = 4 ∧ ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) →
          ∃ u ∈ S, ∃ v ∈ S, G.Adj u v ∧ s(u,v) ∉ U)
    (large :
      let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card →
        let U := Ustar G C
        let B := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
        ∀ d : ℕ, (5 ≤ d ∧ d ≤ 6) → B = U.card+d → B < 2*U.card →
          ([1,2,3,5,8,12,16] : List ℕ).getD d 0 ≤ U.card →
          ∀ S : Finset (Fin 11), S.card = d+5 →
          (∃ I ⊆ S, I.card = 4 ∧ ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v) →
          ∃ u ∈ S, ∃ v ∈ S, G.Adj u v ∧ s(u,v) ∉ U) :
    have x1 : List (ℕ × ℕ) := [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; let x2 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) x1; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x3.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x2 x3 →       PEqualNP.TopForm.TopForm x2 x3 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x2 x3).card →           have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x2 x3;           have x9 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x3).card + (PEqualNP.TopForm.junk x2 x3).card + (PEqualNP.TopForm.orN x2 x3 \ PEqualNP.TopForm.lam x2 x3).card;           x8.card ≤ x9 → x9 < (2 : ℕ) * x8.card → ∀ (x12 x13 : Finset (Fin (11 : ℕ))), x12.card = (7 : ℕ) → x2.IsVertexCover ↑x12 → x13 ⊆ x12 → (x2.deleteEdges ↑x8).IsVertexCover ↑(x12 \ x13) → x13.card ≤ x9 - x8.card := by
  intro E G C short least top dirty U B low high T X seven cover sub residual
  let d := B - U.card
  change X.card ≤ d
  by_contra! tooSmall
  have bound := Finset.card_le_card sub
  have dmax : d ≤ 6 := by omega
  have budget : B = U.card + d := by dsimp [d]; omega
  obtain ⟨Y, hYX, hY⟩ := Finset.exists_subset_card_eq (show d + 1 ≤ X.card by omega)
  let I := (Finset.univ : Finset (Fin 11)) \ T
  let S := (Finset.univ : Finset (Fin 11)) \ (T \ Y)
  have iy : Y ⊆ T := hYX.trans sub
  have four : I.card = 4 := by
    rw [show I = Finset.univ \ T from rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ _), seven]
    rfl
  have card : S.card = d + 5 := by
    have hsplit := Finset.card_sdiff_add_card_eq_card iy
    have hcard : S.card = 11 - (T \ Y).card := by
      rw [show S = Finset.univ \ (T \ Y) from rfl,
        Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      rfl
    omega
  have IS : I ⊆ S := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,fun h => (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp h).1⟩
  have independent : ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v := by
    intro u hu v hv edge
    exact (cover edge).elim (Finset.mem_sdiff.mp hu).2 (Finset.mem_sdiff.mp hv).2
  have disjoint : ∀ u ∈ S, ∀ v ∈ S, ¬ (G.deleteEdges ↑U).Adj u v := by
    intro u hu v hv edge
    rcases residual edge with a | b
    · obtain ⟨atT,notX⟩ := Finset.mem_sdiff.mp a
      exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_sdiff.mpr ⟨atT, fun h => notX (hYX h)⟩)
    · obtain ⟨atT,notX⟩ := Finset.mem_sdiff.mp b
      exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_sdiff.mpr ⟨atT, fun h => notX (hYX h)⟩)

  let encoded : List ℕ := [9,10,20,24,37,42,54,55,72,74,88,89,103,106,121,137]
  let source (i : Fin 16) : Fin 11 := Fin.ofNat 11 (encoded.getD i.val 0 / 16)
  let target (i : Fin 16) : Fin 11 := Fin.ofNat 11 (encoded.getD i.val 0 % 16)
  let edgeOf (i : Fin 16) := s(source i,target i)
  let inside (A : Finset (Fin 11)) : Finset (Fin 16) :=
    Finset.univ.filter fun i => source i ∈ A ∧ target i ∈ A
  have listed : ∀ i, G.Adj (source i) (target i) := by decide +kernel
  have unique : ∀ i j, edgeOf i = edgeOf j → i = j := by decide +kernel
  have minCards (t : Fin 7) : ∀ A : Finset (Fin 11), A.card = 5+t.val →
      ([1,2,3,5,8,12,16] : List ℕ).getD t.val 0 ≤ (inside A).card := by
    fin_cases t <;> decide +kernel
  have covered : (inside S).image edgeOf ⊆ U := by
    intro e he
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
    have both : source i ∈ S ∧ target i ∈ S := (Finset.mem_filter.mp hi).2
    by_contra missing
    exact disjoint _ both.1 _ both.2 (SimpleGraph.deleteEdges_adj.mpr ⟨listed i,missing⟩)
  have edgeFloor : ([1,2,3,5,8,12,16] : List ℕ).getD d 0 ≤ U.card := by
    have count := Finset.card_le_card covered
    rw [Finset.card_image_of_injective _ (fun _ _ h => unique _ _ h)] at count
    exact (minCards ⟨d,by omega⟩ S (by change S.card = 5+d; omega)).trans count
  have base : ∃ A ⊆ S, A.card = 4 ∧ ∀ u ∈ A, ∀ v ∈ A, ¬ G.Adj u v :=
    ⟨I,IS,four,independent⟩
  have missing : ∃ u ∈ S, ∃ v ∈ S, G.Adj u v ∧ s(u,v) ∉ U := by
    by_cases low : d ≤ 2
    · exact small C short least top dirty d low budget high edgeFloor S card base
    by_cases mid : d = 3
    · exact three C short least top dirty d mid budget high edgeFloor S card base
    by_cases next : d = 4
    · exact fourCase C short least top dirty d next budget high edgeFloor S card base
    · exact large C short least top dirty d ⟨by omega,dmax⟩ budget high edgeFloor S card base
  obtain ⟨u,hu,v,hv,edge,notCovered⟩ := missing
  exact disjoint u hu v hv (SimpleGraph.deleteEdges_adj.mpr ⟨edge,notCovered⟩)
