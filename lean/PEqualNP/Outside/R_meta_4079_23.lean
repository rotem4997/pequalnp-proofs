import PEqualNP.Defs

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.R_meta_4079_23
    (joint : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)];
      ∀ C : Circuit, IsLeastAO G C → TopForm G C → (junk G C).card = 2 →
      let U := Ustar G C
      let D := (junk G C).biUnion fun g => (gammaE G C g).filter fun e => ¬Disjoint e.toFinset (wmax G C g)
      let O := (orN G C \ lam G C).card
      (U \ D).card ≤ 2 + O)
    (guarded : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)];
      ∀ C : Circuit, C.size ≤ 21 → IsLeastAO G C → TopForm G C → (junk G C).card = 2 →
      let U := Ustar G C
      let D := (junk G C).biUnion fun g => (gammaE G C g).filter fun e => ¬Disjoint e.toFinset (wmax G C g)
      let O := (orN G C \ lam G C).card
      let T := 2 * (centreless G C).card
      (∀ u v, s(u,v) ∈ U → ∃ g ∈ junk G C, gateVal 11 C g (pairInput u v) = true) →
      3 ≤ U.card → T + 2 + O < 2 * U.card →
      (U ∩ D).card ≤ T + (2 + O - (U \ D).card)) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (21 : ℕ) → PEqualNP.TopForm.IsLeastAO x1 x2 → PEqualNP.TopForm.TopForm x1 x2 → (PEqualNP.TopForm.junk x1 x2).card = (2 : ℕ) → (∀ (x7 x8 : Fin (11 : ℕ)), s(x7, x8) ∈ PEqualNP.TopForm.Ustar x1 x2 → ∃ x10 ∈ PEqualNP.TopForm.junk x1 x2, PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x2 x10 (PEqualNP.EdgeOwnership.pairInput x7 x8) = Bool.true) → (3 : ℕ) ≤ (PEqualNP.TopForm.Ustar x1 x2).card → (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card → (PEqualNP.TopForm.Ustar x1 x2).card ≤ (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card := by
  intro G C size least top two fires lo hi
  let U := Ustar G C
  let D := (junk G C).biUnion fun g => (gammaE G C g).filter fun e => ¬Disjoint e.toFinset (wmax G C g)
  let O := (orN G C \ lam G C).card
  let T := 2 * (centreless G C).card
  change T + (junk G C).card + O < 2 * U.card at hi
  have hi2 : T + 2 + O < 2 * U.card := (congrArg (fun k : Nat => T + k + O) two) ▸ hi
  have hJ : (U \ D).card ≤ 2 + O := joint C least top two
  have hG : (U ∩ D).card ≤ T + (2 + O - (U \ D).card) :=
    guarded C size least top two fires lo hi2
  have parts := Finset.card_sdiff_add_card_inter U D
  change U.card ≤ T + (junk G C).card + O
  omega
