import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxRecDepth 6000 in
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_5020_451
    (slots : ∀ (n : ℕ) (C : Circuit) (A : Finset (Fin n)), IsMinimalCircuit n C →
      (∀ a ∈ A, ∃ x y : Fin n → Bool, (∀ j, j ≠ a → x j = y j) ∧
        circuitFun n C x ≠ circuitFun n C y) →
      A.card + ∑ v ∈ Aᶜ, (C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length ≤ C.size + 1)
    (dense : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
      (∀ T : Finset (Fin n), G.IsVertexCover (T : Set (Fin n)) → k ≤ T.card) →
      IsMinimalCircuit n C → circuitFun n C = NestedCover.graphFun G A →
      let readers := fun (v : Fin n) => C.gates.filter fun g =>
        (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      let L := Aᶜ.filter fun v => (readers v).length = 2
      (∀ v ∉ A, 2 ≤ (readers v).length) →
      (∃ v ∉ A, (readers v).length = 2 ∧ ∃ g ∈ readers v, g.op ≠ GateOp.or) →
      5 * (Aᶜ : Finset (Fin n)).card < 6 * L.card →
      ¬ (∃ c : Fin n → Fin 2, ∀ u ∈ L, ∀ v ∈ L, G.Adj u v → c u ≠ c v) →
      A.card + G.edgeSet.ncard + k ≤ C.size + 1) :
    ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool) (x6 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x7 ∉ x4, (x3.neighborSet x7).ncard = (3 : ℕ)) →     (∀ (x8 : Fin x1) (x9 : x3.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) →       (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → x9 ∉ x4) →         (∃ (x10 : Fin x1) (x11 : Fin x1), x3.Adj x10 x11) →           (∀ (x11 : Finset (Fin x1)), (∀ (x12 x13 : Fin x1), x3.Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) → x2 ≤ x11.card) →             (∀ (x12 : Fin x1 → Bool), x5 x12 = Bool.true ↔ (∃ x13 ∈ x4, x12 x13 = Bool.true) ∨ ∃ (x13 : Fin x1) (x14 : Fin x1), x3.Adj x13 x14 ∧ x12 x13 = Bool.true ∧ x12 x14 = Bool.true) →               PEqualNP.MetaComplexity.FanInTwo x6 →                 PEqualNP.MetaComplexity.circuitFun x1 x6 = x5 →                   (∀ (x15 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x15 → x6.size ≤ x15) →                     (∀ x16 ∉ x4, (2 : ℕ) ≤ (List.filter (fun (x18 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x18.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x18.inputs).contains ↑x16) x6.gates).length) →                       (∃ x17 ∉ x4,                           have x18 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x18 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x18.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x18.inputs).contains ↑x17) x6.gates;                           x18.length = (2 : ℕ) ∧ ∃ x19 ∈ x18, x19.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) →                         x4.card + x3.edgeSet.ncard + x2 ≤ x6.size + (1 : ℕ) := by
  have independentLarge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (V : Finset (Fin n)) (bounded : ∀ v ∈ V, (G.neighborSet v).ncard ≤ 3)
      (girth : ∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) :
      ∃ I ⊆ V, V.card ≤ 3 * I.card ∧ ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v := by
    classical
    have noTriangle {u v w : Fin n} (uv : G.Adj u v) (vw : G.Adj v w) (wu : G.Adj w u) : False := by
      let p : G.Walk u u := .cons uv (.cons vw (.cons wu .nil))
      have cyclic : p.IsCycle := by
        apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
        refine ⟨?_, by change 3 ≤ 3; omega⟩
        apply (SimpleGraph.Walk.isPath_def _).mpr
        simp [p, List.nodup_cons, uv.ne.symm, vw.ne, wu.ne]
      have bad := girth u p cyclic
      change 7 ≤ 3 at bad
      omega
    let Indep (J : Finset (Fin n)) := ∀ u ∈ J, ∀ v ∈ J, ¬ G.Adj u v
    let candidates := V.powerset.filter Indep
    have existsCandidate : candidates.Nonempty :=
      ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), by simp [Indep]⟩⟩
    obtain ⟨I, hI, maximal⟩ := Finset.exists_max_image candidates Finset.card existsCandidate
    obtain ⟨isub, independent⟩ := Finset.mem_filter.mp hI
    have subsetV := Finset.mem_powerset.mp isub
    refine ⟨I, subsetV, ?_, independent⟩
    have maxI (J : Finset (Fin n)) (js : J ⊆ V) (ji : Indep J) : J.card ≤ I.card :=
      maximal J (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr js,ji⟩)
    let U := V \ I
    let neighbors (v : Fin n) := I.filter fun z => G.Adj v z
    have member (v z : Fin n) : z ∈ neighbors v ↔ z ∈ I ∧ G.Adj v z := Finset.mem_filter
    have nearNonempty (v : Fin n) (hv : v ∈ U) : (neighbors v).Nonempty := by
      obtain ⟨vV,vI⟩ := Finset.mem_sdiff.mp hv
      by_contra notNear
      have none : ∀ z ∈ I, ¬G.Adj v z := by
        intro z h edge
        exact notNear ⟨z,(member _ _).mpr ⟨h,edge⟩⟩
      have ins : Indep (insert v I) := by
        intro x hx y hy
        rcases Finset.mem_insert.mp hx with hx' | hx' <;>
          rcases Finset.mem_insert.mp hy with hy' | hy'
        · rw [hx', hy']
          exact G.loopless.irrefl _
        · rw [hx']
          exact none _ hy'
        · rw [hy']
          exact fun h => none _ hx' h.symm
        · exact independent _ hx' _ hy'
      have b := maxI (insert v I) (Finset.insert_subset_iff.mpr ⟨vV,subsetV⟩) ins
      rw [Finset.card_insert_of_notMem vI] at b
      omega
    let lone := U.filter fun v => (neighbors v).card = 1
    let other := U \ lone
    have loneSub : lone ⊆ U := Finset.filter_subset _ _
    let pick (v : Fin n) := if hv : v ∈ U then (neighbors v).min' (nearNonempty v hv) else v
    have hasPick (v : Fin n) (hv : v ∈ U) : pick v ∈ neighbors v := by
      dsimp only [pick]
      rw [dite_eq_left hv]
      exact Finset.min'_mem _ _
    have onlyPick (v : Fin n) (hv : v ∈ lone) {i : Fin n} (hi : i ∈ I) (ad : G.Adj v i) :
        i = pick v := by
      obtain ⟨vU,count⟩ := Finset.mem_filter.mp hv
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp count
      have first := (member v i).mpr ⟨hi,ad⟩
      have second := hasPick v vU
      rw [ha, Finset.mem_singleton] at first second
      exact first.trans second.symm
    have loneCount : lone.card ≤ I.card := by
      apply Finset.card_le_card_of_injOn pick
      · intro v hv
        exact ((member _ _).mp (hasPick v (loneSub hv))).1
      · intro u hu v hv same
        by_contra distinct
        have uU := loneSub hu
        have vU := loneSub hv
        obtain ⟨uV,uI⟩ := Finset.mem_sdiff.mp uU
        obtain ⟨vV,vI⟩ := Finset.mem_sdiff.mp vU
        let i := pick u
        have inear := (member _ _).mp (hasPick u uU)
        have ineav := (member _ _).mp (hasPick v vU)
        have ux : G.Adj u i := inear.2
        have vx : G.Adj v i := by
          change G.Adj v (pick u)
          rw [same]
          exact ineav.2
        have uv : ¬ G.Adj u v := fun e => noTriangle e vx ux.symm
        let rest := I.erase i
        have ur (r : Fin n) (hr : r ∈ rest) : ¬ G.Adj u r :=
          fun e => (Finset.mem_erase.mp hr).1 (onlyPick u hu (Finset.mem_erase.mp hr).2 e)
        have vr (r : Fin n) (hr : r ∈ rest) : ¬ G.Adj v r :=
          fun e => (Finset.mem_erase.mp hr).1 ((onlyPick v hv (Finset.mem_erase.mp hr).2 e).trans same.symm)
        let J := insert u (insert v rest)
        have js : J ⊆ V :=
          Finset.insert_subset_iff.mpr ⟨uV,Finset.insert_subset_iff.mpr
            ⟨vV,(Finset.erase_subset _ _).trans subsetV⟩⟩
        have ji : Indep J := by
          intro a ha b hb
          simp only [J, Finset.mem_insert] at ha hb
          rcases ha with (rfl | rfl | ha) <;> rcases hb with (rfl | rfl | hb)
          · exact G.loopless.irrefl _
          · exact uv
          · exact ur _ hb
          · exact fun e => uv e.symm
          · exact G.loopless.irrefl _
          · exact vr _ hb
          · exact fun e => ur _ ha e.symm
          · exact fun e => vr _ ha e.symm
          · exact independent _ (Finset.mem_erase.mp ha).2 _ (Finset.mem_erase.mp hb).2
        have vr' : v ∉ rest := fun h => vI (Finset.mem_erase.mp h).2
        have ur' : u ∉ insert v rest := by
          simp only [Finset.mem_insert, not_or]
          exact ⟨distinct,fun h => uI (Finset.mem_erase.mp h).2⟩
        have b := maxI J js ji
        change (insert u (insert v (I.erase i))).card ≤ I.card at b
        rw [Finset.card_insert_of_notMem ur', Finset.card_insert_of_notMem vr',
          Finset.card_erase_of_mem inear.1] at b
        have positive : 0 < I.card := Finset.card_pos.mpr ⟨_,inear.1⟩
        omega
    have little (v : Fin n) (hv : v ∈ lone) : 1 ≤ (neighbors v).card :=
      (Finset.mem_filter.mp hv).2.ge
    have more (v : Fin n) (hv : v ∈ other) : 2 ≤ (neighbors v).card := by
      obtain ⟨vU,notLone⟩ := Finset.mem_sdiff.mp hv
      have z := Finset.card_pos.mpr (nearNonempty v vU)
      have ne : (neighbors v).card ≠ 1 := fun e => notLone (Finset.mem_filter.mpr ⟨vU,e⟩)
      omega
    have lowerL := Finset.sum_le_sum little
    have lowerO := Finset.sum_le_sum more
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at lowerL lowerO
    have split := Finset.sum_sdiff loneSub (f := fun v => (neighbors v).card)
    change (∑ v ∈ other, (neighbors v).card) + _ = _ at split
    have countEdges :
        (∑ v ∈ U, (neighbors v).card) ≤ 3 * I.card := by
      calc
        (∑ v ∈ U, (neighbors v).card) = ∑ v ∈ U, ∑ i ∈ I, if G.Adj v i then 1 else 0 := by
          simp [neighbors]
        _ = ∑ i ∈ I, ∑ v ∈ U, if G.Adj v i then 1 else 0 := Finset.sum_comm
        _ = ∑ i ∈ I, (U.filter fun v => G.Adj v i).card := by simp
        _ ≤ ∑ _i ∈ I, 3 := by
          apply Finset.sum_le_sum
          intro i hi
          have contained : (U.filter fun v => G.Adj v i) ⊆ G.neighborFinset i := by
            intro v hv
            exact (G.mem_neighborFinset i v).mpr (Finset.mem_filter.mp hv).2.symm
          have budget := Finset.card_le_card contained
          rw [G.card_neighborFinset_eq_degree, ← G.ncard_neighborSet i] at budget
          exact budget.trans (bounded i (subsetV hi))
        _ = 3 * I.card := by simp [Nat.mul_comm]
    have cu := Finset.card_sdiff_add_card_eq_card subsetV
    have co := Finset.card_sdiff_add_card_eq_card loneSub
    change U.card + I.card = V.card at cu
    change other.card + lone.card = U.card at co
    omega
  have edgeCount {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
      (∑ v : Fin n, G.degree v) = 2 * G.edgeSet.ncard := by
    classical
    have counts (v : Fin n) : (G.edgeFinset.filter fun e => v ∈ e).card = G.degree v := by
      rw [← G.incidenceFinset_eq_filter, G.card_incidenceFinset_eq_degree]
    have num (e : Sym2 (Fin n)) (he : e ∈ G.edgeFinset) :
        (Finset.univ.filter fun v => v ∈ e).card = 2 := by
      induction e using Sym2.inductionOn with
      | _ a b =>
        have adj : G.Adj a b := (SimpleGraph.mem_edgeSet G).mp (SimpleGraph.mem_edgeFinset.mp he)
        have eq : (Finset.univ.filter fun v => v ∈ s(a,b)) = {a,b} := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_iff,
            Finset.mem_insert, Finset.mem_singleton]
        rw [eq,Finset.card_pair adj.ne]
    calc
      (∑ v : Fin n, G.degree v) =
          ∑ v : Fin n, ∑ e ∈ G.edgeFinset, if v ∈ e then (1 : ℕ) else 0 := by
        apply Finset.sum_congr rfl
        intro v _
        rw [Finset.sum_boole]
        exact (counts v).symm
      _ = ∑ e ∈ G.edgeFinset, ∑ v : Fin n, if v ∈ e then (1 : ℕ) else 0 := Finset.sum_comm
      _ = ∑ _e ∈ G.edgeFinset, 2 := by
        apply Finset.sum_congr rfl
        intro e he
        rw [Finset.sum_boole]
        exact num e he
      _ = 2 * G.edgeSet.ncard := by
        have equal : G.edgeFinset.card = G.edgeSet.ncard := by
          rw [← Set.ncard_coe_finset,SimpleGraph.coe_edgeFinset]
        simp only [Finset.sum_const, smul_eq_mul]
        rw [equal,Nat.mul_comm]
  -- The larger color class gives the count used in R_meta_2636_73.
  have colorClass {n : ℕ} (G : SimpleGraph (Fin n)) (L : Finset (Fin n))
      (hc : ∃ c : Fin n → Fin 2, ∀ u ∈ L, ∀ v ∈ L, G.Adj u v → c u ≠ c v) :
      ∃ I ⊆ L, L.card ≤ 2 * I.card ∧ ∀ u ∈ I, ∀ v ∈ I, ¬G.Adj u v := by
    classical
    obtain ⟨c,distinct⟩ := hc
    let X := L.filter fun v => c v = 0
    let Y := L.filter fun v => ¬c v = 0
    have cards : X.card + Y.card = L.card := Finset.card_filter_add_card_filter_not _
    by_cases large : Y.card ≤ X.card
    · refine ⟨X, Finset.filter_subset _ _, by omega, ?_⟩
      intro u hu v hv edge
      obtain ⟨ul,uc⟩ := Finset.mem_filter.mp hu
      obtain ⟨vl,vc⟩ := Finset.mem_filter.mp hv
      exact distinct u ul v vl edge (uc.trans vc.symm)
    · refine ⟨Y, Finset.filter_subset _ _, by omega, ?_⟩
      intro u hu v hv edge
      obtain ⟨ul,uc⟩ := Finset.mem_filter.mp hu
      obtain ⟨vl,vc⟩ := Finset.mem_filter.mp hv
      apply distinct u ul v vl edge
      have onlyOne : ∀ a : Fin 2, a ≠ 0 → a = 1 := by decide
      exact (onlyOne _ uc).trans (onlyOne _ vc).symm
  classical
  intro n k G A f C degree girth isolated edge minCover spec fan computes minimum twice nonOr
  let U := Aᶜ
  let readers (v : Fin n) := (C.gates.filter fun g =>
    (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length
  let L := U.filter fun v => readers v = 2
  have minC : IsMinimalCircuit n C := by
    refine ⟨fan,fun D hf hsame => minimum _ ?_⟩
    exact ⟨D,hf,le_rfl,fun x => congrFun (hsame.trans computes) x⟩
  let colored := ∃ c : Fin n → Fin 2, ∀ u ∈ L, ∀ v ∈ L, G.Adj u v → c u ≠ c v
  by_cases tight : (5 * U.card < 6 * L.card) ∧ ¬colored
  · have rep : circuitFun n C = NestedCover.graphFun G A := by
      rw [computes]
      funext x
      apply Bool.eq_iff_iff.mpr
      change f x = true ↔
        (decide (∃ a ∈ A, x a = true) || decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) = true
      simpa only [Bool.or_eq_true, decide_eq_true_eq] using spec x
    exact dense n k G A C degree girth isolated edge (fun T hT => minCover T (fun u v e => hT e))
      minC rep twice nonOr tight.1 tight.2
  have lU : L ⊆ U := Finset.filter_subset _ _
  have sufficient : ∃ I ⊆ U, 2 * L.card ≤ U.card + 2 * I.card ∧
      ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v := by
    by_cases high : 5 * U.card < 6 * L.card
    · by_cases properColor : colored
      · obtain ⟨I,iL,half,independent⟩ := colorClass G L properColor
        have lSize := Finset.card_le_card lU
        exact ⟨I,iL.trans lU,by omega,independent⟩
      · exact (tight ⟨high,properColor⟩).elim
    · obtain ⟨I,iU,large,independent⟩ := independentLarge G U
        (fun v hv => (degree v (Finset.mem_compl.mp hv)).le) girth
      exact ⟨I,iU,by omega,independent⟩
  obtain ⟨I,iU,large,independent⟩ := sufficient
  let cover := U \ I
  have covers : ∀ u v, G.Adj u v → u ∈ cover ∨ v ∈ cover := by
    intro u v e
    have hu : u ∈ U := Finset.mem_compl.mpr (isolated u v e)
    have hv : v ∈ U := Finset.mem_compl.mpr (isolated v u e.symm)
    by_cases ui : u ∈ I
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨hv,fun vi => independent u ui v vi e⟩)
    · exact Or.inl (Finset.mem_sdiff.mpr ⟨hu,ui⟩)
  have tau := minCover cover covers
  have hI := Finset.card_sdiff_add_card_eq_card iU
  change cover.card + I.card = U.card at hI
  have slotsBudget := slots n C A minC (by
    intro a ha
    let z : Fin n → Bool := fun _ => false
    let y : Fin n → Bool := fun i => decide (i=a)
    refine ⟨z,y,fun i hi => by simp [z,y,hi],?_⟩
    rw [computes]
    have fz : f z = false := Bool.eq_false_iff.mpr (fun h => by
      have contradiction := (spec z).mp h
      simp [z] at contradiction)
    have fy : f y = true := (spec y).2 (Or.inl ⟨a,ha,by simp [y]⟩)
    rw [fz,fy]
    decide)
  change A.card + ∑ v ∈ U, readers v ≤ C.size + 1 at slotsBudget
  have few (v : Fin n) (hv : v ∈ L) : 2 ≤ readers v := (Finset.mem_filter.mp hv).2.ge
  have more (v : Fin n) (hv : v ∈ U \ L) : 3 ≤ readers v := by
    obtain ⟨vu,vl⟩ := Finset.mem_sdiff.mp hv
    have h := twice v (Finset.mem_compl.mp vu)
    change 2 ≤ readers v at h
    have ne : readers v ≠ 2 := fun eq => vl (Finset.mem_filter.mpr ⟨vu,eq⟩)
    omega
  have low := Finset.sum_le_sum few
  have upper := Finset.sum_le_sum more
  simp only [Finset.sum_const, smul_eq_mul] at low upper
  have splitSum := Finset.sum_sdiff lU (f := readers)
  have splitCard := Finset.card_sdiff_add_card_eq_card lU
  have dA (v : Fin n) (hv : v ∈ A) : G.degree v = 0 :=
    (G.degree_eq_zero v).2 (fun j h => isolated v j h hv)
  have dU (v : Fin n) (hv : v ∈ U) : G.degree v = 3 := by
    rw [← G.ncard_neighborSet]
    exact degree v (Finset.mem_compl.mp hv)
  have balance := edgeCount G
  rw [← A.sum_add_sum_compl, Finset.sum_congr rfl dA, Finset.sum_congr rfl dU] at balance
  simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul] at balance
  change U.card * 3 = 2 * G.edgeSet.ncard at balance
  omega
