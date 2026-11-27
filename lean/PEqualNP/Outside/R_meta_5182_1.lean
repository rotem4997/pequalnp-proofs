import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_5182_1
    (uncovered_routing : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      ((Ustar G C).Nonempty → 0 < 2 * (centreless G C).card + (orN G C \ lam G C).card) ∧
      (∀ u v, s(u, v) ∈ Ustar G C → ∃ j ∈ junk G C,
        ∀ b : Fin 2, u ∈ side C j b ∨ v ∈ side C j b))
    (large_uncovered : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj] (C : Circuit),
      G = edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
        (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] →
      IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      (∃ i j, junk G C = {i, j} ∧ InCone 11 C i j) →
      let U := Ustar G C
      let charge := 2 * (centreless G C).card + (orN G C \ lam G C).card
      s((8 : Fin 11), 9) ∈ U → 3 ≤ U.card → charge + 4 ≤ 2 * U.card →
      (∀ u v, s(u, v) ∈ U → ∃ j ∈ junk G C, ∀ b : Fin 2, u ∈ side C j b ∨ v ∈ side C j b) →
      22 ≤ C.size) :
  ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit),
  x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ)
    [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)),
      ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)),
      ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)),
      ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →
  PEqualNP.TopForm.IsLeastAO x1 x3 →
  PEqualNP.TopForm.TopForm x1 x3 →
  x3.size < (22 : ℕ) →
  (∃ (x8 : ℕ) (x9 : ℕ), PEqualNP.TopForm.junk x1 x3 = {x8, x9} ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x8 x9) →
  have x9 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;
  let x10 : SimpleGraph (Fin (11 : ℕ)) := x1.deleteEdges ↑x9;
  have x11 : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};
  have x12 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};
  ∀ x13 ⊆ x11,
    x13 = ∅ →
      (∀ x16 ∈ x11 \ x13, ∀ x18 ∈ x11 \ x13, ¬x10.Adj x16 x18) →
        have x17 : Finset (Fin (11 : ℕ)) := {x17 ∈ Finset.univ \ x11 | ∃ x18 ∈ x11 \ x13, x10.Adj x18 x17};
        have x18 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {x18 ∈ x12 | x10.Adj x18.1 x18.2 ∧ x18.1 ∉ x17 ∧ x18.2 ∉ x17};
        (5 : ℕ) + x9.card ≤ x13.card + x17.card + x18.card + (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card := by
  intro G inst C hG hleast htop hsize hjunk U H X M S hsub hS hind N R
  let Y : Finset (Fin 11) := Finset.univ \ X
  -- Match each outside vertex to a specific incident edge crossing X.
  let w (v : Fin 11) : Fin 11 :=
    if v = 0 then 9 else if v = 2 then 10 else if v = 6 ∨ v = 7 then 3 else 8
  have witness (v : Fin 11) (hv : v ∈ Y) : w v ∈ X ∧ G.Adj (w v) v := by
    rw [hG]
    have fixed : ∀ a : Fin 11, a ∈ Y → w a ∈ X ∧
        (PEqualNP.EdgeOwnership.edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
          (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]).Adj (w a) a := by
      decide +kernel
    exact fixed v hv
  let f (v : Fin 11) : Sym2 (Fin 11) := s(w v, v)
  let missing := (Y \ N).image f
  have hN (v : Fin 11) : v ∈ N ↔ v ∈ Y ∧ ∃ a ∈ X, H.Adj a v := by
    change v ∈ Y.filter (fun v => ∃ a ∈ X \ S, H.Adj a v) ↔ _
    simp -congrConsts [hS]
  have hg89 : G.Adj 8 9 := by rw [hG]; decide
  -- The edge inside X is different from every matched edge.
  have h89 : s((8 : Fin 11), 9) ∈ U := by
    by_contra hnot
    have hk : H.Adj 8 9 := SimpleGraph.deleteEdges_adj.mpr ⟨hg89, hnot⟩
    have h8 : (8 : Fin 11) ∈ X \ S := by rw [hS]; decide
    have h9 : (9 : Fin 11) ∈ X \ S := by rw [hS]; decide
    exact hind 8 h8 9 h9 hk
  have imageInj : Set.InjOn f (↑(Y \ N) : Set (Fin 11)) := by
    intro a ha b hb heq
    have haY : a ∈ Y := (Finset.mem_sdiff.mp (Finset.mem_coe.mp ha)).1
    have hbY : b ∈ Y := (Finset.mem_sdiff.mp (Finset.mem_coe.mp hb)).1
    rcases Sym2.eq_iff.mp heq with ⟨_, eq⟩ | ⟨eq, _⟩
    · exact eq
    · exact ((Finset.mem_sdiff.mp hbY).2 (eq ▸ (witness a haY).1)).elim
  have hnot89 : s((8 : Fin 11), 9) ∉ missing := by
    intro hm
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hm
    have hvY := (Finset.mem_sdiff.mp hv).1
    have hvX := (Finset.mem_sdiff.mp hvY).2
    rcases Sym2.eq_iff.mp heq with ⟨_, eq⟩ | ⟨_, eq⟩
    · exact hvX (eq.symm ▸ (show (9 : Fin 11) ∈ X by decide))
    · exact hvX (eq.symm ▸ (show (8 : Fin 11) ∈ X by decide))
  have hmissing : insert s((8 : Fin 11), 9) missing ⊆ U := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | hm
    · exact h89
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hm
      obtain ⟨hvY, hvN⟩ := Finset.mem_sdiff.mp hv
      by_contra hf
      obtain ⟨hw, hedge⟩ := witness v hvY
      exact hvN ((hN v).mpr ⟨hvY, w v, hw, SimpleGraph.deleteEdges_adj.mpr ⟨hedge, hf⟩⟩)
  have countMissing := Finset.card_le_card hmissing
  rw [Finset.card_insert_of_notMem hnot89, Finset.card_image_of_injOn imageInj,
    Finset.card_sdiff_of_subset (fun v hv => ((hN v).mp hv).1)] at countMissing
  have hY : Y.card = 7 := by decide
  have graphBudget : 8 ≤ N.card + U.card := by omega
  by_contra failBound
  have impossibleCount := Nat.lt_of_not_ge failBound
  let charge := 2 * (centreless G C).card + (orN G C \ lam G C).card
  obtain ⟨chargePositive, routed⟩ := uncovered_routing 11 G C hleast htop
  have chargePos : 0 < charge := chargePositive ⟨_, h89⟩
  have chargeSmall : charge + 4 ≤ 2 * U.card := by
    change 2 * (centreless G C).card + (orN G C \ lam G C).card + 4 ≤ 2 * U.card
    omega
  have many : 3 ≤ U.card := by omega
  exact (Nat.not_le_of_lt hsize) (large_uncovered G C hG hleast htop hjunk h89 many chargeSmall routed)
