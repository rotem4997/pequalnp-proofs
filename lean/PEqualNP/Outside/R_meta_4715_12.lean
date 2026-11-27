import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.BitIndices
import PEqualNP.Defs

open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_4715_12
    (certify : let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
    let blocks : List Nat := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768,274,200,800,1573,1809,1729,1332]
    ∀ b ∈ blocks, let vertices := Finset.univ.filter (fun v : Fin 11 => b.testBit v.val)
      ∀ S ∈ vertices.powerset, (∀ u ∈ vertices, ∀ v ∈ vertices, G.Adj u v → u ∈ S ∨ v ∈ S) →
        (b.bitIndices.length + 1) / 2 ≤ S.card)
    (hard : let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ), (274 : ℕ), (200 : ℕ), (800 : ℕ), (1573 : ℕ), (1809 : ℕ), (1729 : ℕ), (1332 : ℕ)]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x3.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x3).card →           have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;           have x9 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.junk x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card;           x8.card ≤ x9 → x9 < (2 : ℕ) * x8.card → x9 - x8.card < (7 : ℕ) → (∀ X : Finset (Fin 11), (∀ u v : Fin 11, s(u, v) ∈ x8 → u ∈ X ∨ v ∈ X) → x9 - x8.card < X.card) → ∃ (x13 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x8) x13 ∧ ∀ (x14 : List ℕ), List.Pairwise (fun (x15 x16 : ℕ) => x15 &&& x16 = (0 : ℕ)) x14 → (∀ x16 ∈ x14, x16 ∈ x2 ∧ ∀ x18 ∈ x13, x16.testBit ↑x18 = Bool.false) → (List.map (fun (x17 : ℕ) => (x17.bitIndices.length + (1 : ℕ)) / (2 : ℕ)) x14).sum ≤ x9 - x8.card) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; have x2 : List ℕ := [(513 : ℕ), (1025 : ℕ), (18 : ℕ), (258 : ℕ), (36 : ℕ), (1028 : ℕ), (72 : ℕ), (136 : ℕ), (272 : ℕ), (1040 : ℕ), (288 : ℕ), (544 : ℕ), (192 : ℕ), (1088 : ℕ), (640 : ℕ), (768 : ℕ), (274 : ℕ), (200 : ℕ), (800 : ℕ), (1573 : ℕ), (1809 : ℕ), (1729 : ℕ), (1332 : ℕ)]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x3.size ≤ (21 : ℕ) →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x3).card →           have x8 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;           have x9 : ℕ := (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x3).card + (PEqualNP.TopForm.junk x1 x3).card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card;           x8.card ≤ x9 → x9 < (2 : ℕ) * x8.card → x9 - x8.card < (7 : ℕ) → ∃ (x13 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x8) x13 ∧ ∀ (x14 : List ℕ), List.Pairwise (fun (x15 x16 : ℕ) => x15 &&& x16 = (0 : ℕ)) x14 → (∀ x16 ∈ x14, x16 ∈ x2 ∧ ∀ x18 ∈ x13, x16.testBit ↑x18 = Bool.false) → (List.map (fun (x17 : ℕ) => (x17.bitIndices.length + (1 : ℕ)) / (2 : ℕ)) x14).sum ≤ x9 - x8.card := by
  have pack :
      ∀ (P : List Nat) (X : Finset (Fin 11)),
        List.Pairwise (fun a b => a &&& b = 0) P →
        (∀ b ∈ P,
          (b.bitIndices.length + 1) / 2 ≤ (X.filter fun v => b.testBit v.val).card) →
        (P.map fun b => (b.bitIndices.length + 1) / 2).sum ≤ X.card := by
    intro P
    induction P with
    | nil =>
        intro X _ _
        simp
    | cons b bs ih =>
        intro X hpair hweight
        rw [List.pairwise_cons] at hpair
        rcases hpair with ⟨hhead, htail⟩
        let A : Finset (Fin 11) := X.filter fun v => b.testBit v.val
        have hAsub : A ⊆ X := Finset.filter_subset _ _
        have hheadWeight : (b.bitIndices.length + 1) / 2 ≤ A.card := by
          exact hweight b (by simp)
        have hmaskDisjoint : ∀ c ∈ bs,
            Disjoint A (X.filter fun v => c.testBit v.val) := by
          intro c hc
          apply Finset.disjoint_left.mpr
          intro v hvA hvC
          have hb : b.testBit v.val = true := (Finset.mem_filter.mp hvA).2
          have hcbit : c.testBit v.val = true := (Finset.mem_filter.mp hvC).2
          have hbits : (b &&& c).testBit v.val = true := by
            simp [Nat.testBit_and, hb, hcbit]
          rw [hhead c hc] at hbits
          simp at hbits
        have hfilterEq (c : ℕ) (hc : c ∈ bs) :
            (X \ A).filter (fun v => c.testBit v.val) =
              X.filter (fun v => c.testBit v.val) := by
          ext v
          constructor
          · intro hv
            have hmem := Finset.mem_filter.mp hv
            exact Finset.mem_filter.mpr
              ⟨(Finset.mem_sdiff.mp hmem.1).1, hmem.2⟩
          · intro hv
            have hmem := Finset.mem_filter.mp hv
            have hrem : v ∈ X \ A := by
              refine Finset.mem_sdiff.mpr ⟨hmem.1, ?_⟩
              intro hvA
              exact Finset.disjoint_left.mp (hmaskDisjoint c hc) hvA hv
            exact Finset.mem_filter.mpr ⟨hrem, hmem.2⟩
        have hweightTail : ∀ c ∈ bs,
            (c.bitIndices.length + 1) / 2 ≤
              ((X \ A).filter fun v => c.testBit v.val).card := by
          intro c hc
          have h := hweight c (by simp [hc])
          rw [hfilterEq c hc]
          exact h
        have htailBound := ih (X \ A) htail hweightTail
        have hcard : (X \ A).card + A.card = X.card :=
          Finset.card_sdiff_add_card_eq_card hAsub
        simp only [List.map_cons, List.sum_cons]
        omega


  dsimp only
  let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  let blocks : List Nat := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768,274,200,800,1573,1809,1729,1332]
  intro C hsize hleast htop hjunk
  let U := Ustar G C
  let B := 2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
  change U.card ≤ B → B < 2 * U.card → B - U.card < 7 → _
  intro hlow hhigh hbudget
  classical
  by_cases cheap : ∃ X : Finset (Fin 11),
      (∀ u v : Fin 11, s(u,v) ∈ U → u ∈ X ∨ v ∈ X) ∧ X.card ≤ B - U.card
  · obtain ⟨X, covers, size⟩ := cheap
    let H := G.deleteEdges (↑U)
    let Q (k : Nat) := ∃ K : Finset (Fin 11), H.IsVertexCover (↑K) ∧ K.card = k
    have ex : ∃ k, Q k := ⟨_, Finset.univ, by simp [H], rfl⟩
    obtain ⟨K, hk, card⟩ := Nat.find_spec ex
    have least : IsMinCover H K := ⟨hk, fun T ht => card.trans_le (Nat.find_min' ex ⟨T,ht,rfl⟩)⟩
    refine ⟨K, least, ?_⟩
    intro P hp good
    have charge (b : Nat) (hb : b ∈ P) :
        (b.bitIndices.length + 1) / 2 ≤ (X.filter (fun v : Fin 11 => b.testBit v.val)).card := by
      obtain ⟨inblocks, avoids⟩ := good b hb
      let V := Finset.univ.filter (fun v : Fin 11 => b.testBit v.val)
      let S := X.filter (fun v : Fin 11 => b.testBit v.val)
      have sub : S ⊆ V := fun v hv => Finset.mem_filter.mpr ⟨Finset.mem_univ v,(Finset.mem_filter.mp hv).2⟩
      apply certify b inblocks S (Finset.mem_powerset.mpr sub)
      intro u hu v hv edge
      have au := (Finset.mem_filter.mp hu).2
      have av := (Finset.mem_filter.mp hv).2
      have du : u ∉ K := fun mem => Bool.noConfusion ((avoids u mem).symm.trans au)
      have dv : v ∉ K := fun mem => Bool.noConfusion ((avoids v mem).symm.trans av)
      have gone : s(u,v) ∈ U := by
        by_contra keep
        exact (hk (SimpleGraph.deleteEdges_adj.mpr ⟨edge,keep⟩)).elim du dv
      exact (covers u v gone).imp (fun xu => Finset.mem_filter.mpr ⟨xu,au⟩)
        (fun xv => Finset.mem_filter.mpr ⟨xv,av⟩)
    exact (pack P X hp charge).trans size
  · exact hard C hsize hleast htop hjunk hlow hhigh hbudget
      (fun X hX => Nat.lt_of_not_ge (fun le => cheap ⟨X,hX,le⟩))
