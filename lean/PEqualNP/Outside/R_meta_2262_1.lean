import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

-- For monotone gates, maximal independent sets suffice to test whether a gate
-- implies the edge function. Retain the joint ancestor condition in the finite
-- synthesis problem so it treats only the shared-top case.
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_2262_1
    (maximal :
      let G := edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
      let N : List ℕ := [15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546]
      ∀ (C : Circuit) (j : ℕ), AndOrOnly C →
        (∀ r ∈ N, gateVal 11 C j (fun i => r.testBit i.val) = false) →
        BelowF G C j)
    (exclude :
      let N : List ℕ := [15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546]
      let P : List ℕ := [513, 1025, 18, 258, 36, 1028, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768]
      let a := fun (C : Circuit) j => (gateAt C j).op = GateOp.and
      let k := fun (C : Circuit) j =>
        ∀ r ∈ N, gateVal 11 C j (fun i => r.testBit i.val) = false
      let c := InCone 11
      ∀ (C : Circuit) (p q : ℕ),
        IsAO2 11 C → C.size ≤ 21 → p < q → q < C.size → a C p → a C q →
        (∀ i < C.size, a C i → (k C i ↔ i ≠ p ∧ i ≠ q)) →
        (∀ i < C.size, a C i → k C i → ∀ j < C.size, a C j → ¬ c C i j) →
        ¬ c C p q → ¬ c C q p →
        (∃ j < C.size, a C j ∧ k C j ∧ c C p j ∧ c C q j) →
        (∀ r ∈ P, circuitFun 11 C (fun i => r.testBit i.val) = true) →
        (∀ r ∈ N, circuitFun 11 C (fun i => r.testBit i.val) = false) →
        False) :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x9 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x10 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         have x12 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3;         (∀ x13 ∈ x9,             have x15 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x13;             (∀ x16 ∈ x15 (0 : Fin (2 : ℕ)), ∀ x18 ∈ x15 (1 : Fin (2 : ℕ)), x1.Adj x16 x18) ∧ ((x15 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x15 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x14 x15 : Fin (11 : ℕ)), s(x14, x15) ∈ x11 → ∃ x17 ∈ x9, ∃ (x18 : Fin (2 : ℕ)) (x19 : ℕ), (x19 = x4 ∨ x19 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x17 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x17 x18) x19 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x19 (PEqualNP.EdgeOwnership.pairInput x14 x15) = Bool.true) → (17 : ℕ) + (x9 \ x10).card + (2 : ℕ) * x10.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x11.card → (∀ (x16 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x16 → x16.card ≤ (x9 \ x10).card) → x4 < x5 → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → ¬x12 x4 x5 → ¬x12 x5 x4 → (∃ x21 ∈ x9, x12 x4 x21 ∧ x12 x5 x21) → (22 : ℕ) ≤ x3.size := by
  intro G inst C p q eqG least top T Z U Anc stars routed budget cover ltPQ junkEq noPQ noQP shared
  by_contra! short
  let E : List (ℕ × ℕ) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  let H := edgeGraph 11 E
  let N : List ℕ := [15, 29, 43, 57, 71, 85, 99, 113, 135, 149, 163, 177, 269, 325, 389, 526, 540, 582, 596, 1066, 1186, 1288, 1408, 1546]
  let P : List ℕ := [513, 1025, 18, 258, 36, 1028, 72, 136, 272, 1040, 288, 544, 192, 1088, 640, 768]
  let input (r : ℕ) : Fin 11 → Bool := fun i => r.testBit i.val
  let sample (r : ℕ) := E.any fun e => r.testBit e.1 && r.testBit e.2
  have graphTrue (D : SimpleGraph (Fin 11)) [DecidableRel D.Adj] (x : Fin 11 → Bool) :
      graphFun D ∅ x = true ↔ ∃ u v, D.Adj u v ∧ x u = true ∧ x v = true := by
    change (decide (∃ a ∈ (∅ : Finset (Fin 11)), x a = true) ||
      decide (∃ u v, D.Adj u v ∧ x u = true ∧ x v = true)) = true ↔ _
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
  change G = H at eqG
  have same (x : Fin 11 → Bool) : graphFun G ∅ x = graphFun H ∅ x := by
    apply Bool.eq_iff_iff.mpr
    rw [graphTrue G x, graphTrue H x, eqG]
  have sampleCorrect (r : ℕ) : sample r = graphFun H ∅ (input r) := by
    apply Bool.eq_iff_iff.mpr
    rw [graphTrue H]
    change E.any _ = true ↔ _
    rw [List.any_eq_true]
    constructor
    · rintro ⟨⟨u,v⟩, he, hv⟩
      have valid : E.all (fun e => decide (e.1 < 11 ∧ e.2 < 11 ∧ e.1 ≠ e.2)) = true := by
        decide +kernel
      obtain ⟨hu, hv', ne⟩ := of_decide_eq_true (List.all_eq_true.mp valid _ he)
      have adj : H.Adj ⟨u,hu⟩ ⟨v,hv'⟩ := ⟨fun e => ne (congrArg Fin.val e), Or.inl he⟩
      obtain ⟨onU,onV⟩ := Bool.and_eq_true_iff.mp hv
      exact ⟨⟨u,hu⟩, ⟨v,hv'⟩, adj, onU, onV⟩
    · rintro ⟨u,v,he,hu,hv⟩
      rcases he.2 with e | e
      · exact ⟨(u.val,v.val), e, Bool.and_eq_true_iff.mpr ⟨hu,hv⟩⟩
      · exact ⟨(v.val,u.val), e, Bool.and_eq_true_iff.mpr ⟨hv,hu⟩⟩
  have listedNeg : N.all (fun r => !sample r) = true := by decide +kernel
  have listedPos : P.all sample = true := by decide +kernel
  have seenNeg (r : ℕ) (hr : r ∈ N) : graphFun G ∅ (input r) = false := by
    have ok := List.all_eq_true.mp listedNeg r hr
    have bit : sample r = false := by
      cases h : sample r with
      | false => rfl
      | true => rw [h] at ok; contradiction
    exact (same _).trans ((sampleCorrect r).symm.trans bit)
  have seenPos (r : ℕ) (hr : r ∈ P) : graphFun G ∅ (input r) = true := by
    rw [same, ← sampleCorrect]
    exact List.all_eq_true.mp listedPos r hr
  have sound (j : ℕ) (quiet : ∀ r ∈ N, gateVal 11 C j (input r) = false) :
      BelowF G C j := by
    intro x hx
    exact (same x).trans (maximal C j least.1.1 quiet x hx)
  have info (j : ℕ) (hj : j ∈ junk G C) :
      j < C.size ∧ (gateAt C j).op = GateOp.and ∧ IsDirty 11 G C j := by
    unfold junk gatesWhere at hj
    rw [Finset.mem_filter, Finset.mem_range] at hj
    exact hj
  have jp : p ∈ junk G C := by rw [junkEq]; simp
  have jq : q ∈ junk G C := by rw [junkEq]; simp
  have below (j : ℕ) (hj : j < C.size) (op : (gateAt C j).op = GateOp.and)
      (np : j ≠ p) (nq : j ≠ q) : BelowF G C j := by
    intro x hx
    cases hf : graphFun G ∅ x with
    | true => rfl
    | false =>
      have mem : j ∈ junk G C := by
        unfold junk gatesWhere
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, op, hj, x, hx, hf⟩
      rw [junkEq] at mem
      simp only [Finset.mem_insert, Finset.mem_singleton] at mem
      exact (mem.elim np nq).elim
  have criterion (j : ℕ) (hj : j < C.size) (op : (gateAt C j).op = GateOp.and) :
      (∀ r ∈ N, gateVal 11 C j (input r) = false) ↔ j ≠ p ∧ j ≠ q := by
    constructor
    · intro quiet
      have b := sound j quiet
      have impossible (z : ℕ) (hz : z ∈ junk G C) : j ≠ z := by
        rintro rfl
        obtain ⟨_, x, hx, hf⟩ := (info j hz).2.2
        rw [b x hx] at hf
        contradiction
      exact ⟨impossible p jp, impossible q jq⟩
    · rintro ⟨np, nq⟩ r hr
      cases h : gateVal 11 C j (input r) with
      | false => rfl
      | true =>
        have contradictionBool := (below j hj op np nq _ h).symm.trans (seenNeg r hr)
        contradiction
  refine exclude C p q least.1 (by omega) ltPQ (info q jq).1 (info p jp).2.1 (info q jq).2.1
    criterion ?_ noPQ noQP ?_ ?_ ?_
  · intro i hi ai quiet j hj aj
    exact top i hi j hj ai (sound i quiet) aj
  · obtain ⟨j, hj, hp, hq⟩ := shared
    change j ∈ tops G C at hj
    unfold tops gatesWhere at hj
    have peel (f : ℕ → Prop) (d : DecidablePred f) (S : Finset ℕ) (z : ℕ)
        (h : z ∈ @Finset.filter ℕ f d S) : z ∈ S ∧ f z := by
      letI : DecidablePred f := d
      exact Finset.mem_filter.mp h
    obtain ⟨valid, op, clean⟩ := peel _ _ _ _ hj
    refine ⟨j, Finset.mem_range.mp valid, op, ?_, hp, hq⟩
    intro r hr
    cases h : gateVal 11 C j (input r) with
    | false => rfl
    | true =>
      have contradictionBool := (clean _ h).symm.trans (seenNeg r hr)
      contradiction
  · intro r hr
    exact (congrFun least.2.1 (input r)).trans (seenPos r hr)
  · intro r hr
    exact (congrFun least.2.1 (input r)).trans (seenNeg r hr)
