import Mathlib
import PEqualNP.Defs

open scoped BigOperators
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_5022_487
    (strip : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      let read := fun (D : Circuit) (v : Fin n) =>
        D.gates.filter (fun g => (g.inputs.take (cond (g.op.eval [false]) 1 2)).contains v.val)
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
        IsMinimalCircuit n C → circuitFun n C = graphFun G A →
        ∃ D : Circuit, IsMinimalCircuit n D ∧ circuitFun n D = graphFun G ∅ ∧
          D.size + A.card = C.size ∧ ∀ v ∉ A, (read D v).map Gate.op = (read C v).map Gate.op)
    (slots : ∀ (n : ℕ) (C : Circuit),
      let r := fun (v : Fin n) => (C.gates.filter (fun g =>
        (g.inputs.take (cond (g.op.eval [false]) 1 2)).contains v.val)).length
      IsMinimalCircuit n C → (∃ x y, circuitFun n C x ≠ circuitFun n C y) →
        (∑ v : Fin n, r v) ≤ C.size + 1)
    (excess : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit),
      let R := fun (v : Fin n) => C.gates.filter (fun g =>
        (g.inputs.take (cond (g.op.eval [false]) 1 2)).contains v.val)
      let U := (Finset.univ : Finset (Fin n)) \ A
      let H := U.filter (fun v => 3 ≤ (R v).length)
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
        (∀ v (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) → (∀ u v, G.Adj u v → u ∉ A) →
        (∀ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) → k ≤ T.card) →
        IsMinimalCircuit n C → circuitFun n C = graphFun G ∅ →
        (∀ v ∉ A, 2 ≤ (R v).length ∧ ((R v).length = 2 → ∀ g ∈ R v, g.op = .or)) →
        (∃ v ∉ A, (R v).length = 2) →
        U.card + 2 * H.card < 2*k → ¬(PEqualNP.Library.Peel.delVerts G H).IsBipartite →
        (∑ v : Fin n, (R v).length) < G.edgeSet.ncard + k → G.edgeSet.ncard + k ≤ C.size + 1) :
  ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool) (x6 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x7 ∉ x4, (x3.neighborSet x7).ncard = (3 : ℕ)) →     (∀ (x8 : Fin x1) (x9 : x3.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) →       (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → x9 ∉ x4) →         (∃ (x10 : Fin x1) (x11 : Fin x1), x3.Adj x10 x11) →           (∀ (x11 : Finset (Fin x1)), (∀ (x12 x13 : Fin x1), x3.Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) → x2 ≤ x11.card) →             (∀ (x12 : Fin x1 → Bool), x5 x12 = Bool.true ↔ (∃ x13 ∈ x4, x12 x13 = Bool.true) ∨ ∃ (x13 : Fin x1) (x14 : Fin x1), x3.Adj x13 x14 ∧ x12 x13 = Bool.true ∧ x12 x14 = Bool.true) →               PEqualNP.MetaComplexity.FanInTwo x6 →                 PEqualNP.MetaComplexity.circuitFun x1 x6 = x5 →                   (∀ (x15 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x15 → x6.size ≤ x15) →                     (∀ x16 ∉ x4, (2 : ℕ) ≤ (List.filter (fun (x18 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x18.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x18.inputs).contains ↑x16) x6.gates).length) →                       (∀ x17 ∉ x4,                           have x19 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x19 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x19.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x19.inputs).contains ↑x17) x6.gates;                           x19.length = (2 : ℕ) → ∀ x21 ∈ x19, x21.op = PEqualNP.CircuitLowerBounds.GateOp.or) →                         (∃ x18 ∉ x4, (List.filter (fun (x19 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x19.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x19.inputs).contains ↑x18) x6.gates).length = (2 : ℕ)) → x4.card + x3.edgeSet.ncard + x2 ≤ x6.size + (1 : ℕ) := by
  intro n k G A f C cubic girth apart nonempty cover spec fan computes min two only existsTwo
  classical
  have hgraph : f = graphFun G A := by
    funext x
    apply Bool.eq_iff_iff.mpr
    have exactSpec := spec x
    change f x = true ↔ (decide (∃ a ∈ A, x a = true) ||
      decide (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)) = true
    simpa only [Bool.or_eq_true,decide_eq_true_eq] using exactSpec
  have minimum : IsMinimalCircuit n C := by
    refine ⟨fan,?_⟩
    intro E efan efun
    exact min E.size ⟨E,efan,le_rfl,fun x => congrFun (efun.trans computes) x⟩
  obtain ⟨D,dmin,dfun,size,same⟩ := strip n G A C apart nonempty minimum (computes.trans hgraph)
  let read (E : Circuit) (v : Fin n) :=
    E.gates.filter (fun g => (g.inputs.take (cond (g.op.eval [false]) 1 2)).contains v.val)
  have sameOp (v : Fin n) (hv : v ∉ A) : (read D v).map Gate.op = (read C v).map Gate.op := same v hv
  have sameCount (v : Fin n) (hv : v ∉ A) : (read D v).length = (read C v).length := by
    simpa only [List.length_map] using congrArg List.length (sameOp v hv)
  have preserved (v : Fin n) (hv : v ∉ A) :
      2 ≤ (read D v).length ∧ ((read D v).length = 2 → ∀ g ∈ read D v, g.op = .or) := by
    refine ⟨(sameCount v hv).symm ▸ two v hv,?_⟩
    intro htwo g hg
    have old : (read C v).length = 2 := (sameCount v hv).symm.trans htwo
    have op : g.op ∈ (read D v).map Gate.op := List.mem_map_of_mem hg
    rw [sameOp v hv] at op
    obtain ⟨h,hh,eq⟩ := List.mem_map.mp op
    exact eq.symm.trans (only v hv old h hh)
  have oneTwo : ∃ v ∉ A, (read D v).length = 2 := by
    obtain ⟨v,hv,eq⟩ := existsTwo
    exact ⟨v,hv,(sameCount v hv).trans eq⟩
  have outputsUnequal : ∃ x y, circuitFun n D x ≠ circuitFun n D y := by
    have positive : graphFun G ∅ (fun _ => true) = true := by
      change (decide (∃ a ∈ (∅ : Finset (Fin n)), (true : Bool) = true) ||
        decide (∃ u v, G.Adj u v ∧ (true : Bool) = true ∧ (true : Bool) = true)) = true
      simp only [Bool.or_eq_true,decide_eq_true_eq,and_true]
      exact Or.inr nonempty
    have negative : graphFun G ∅ (fun _ => false) = false := by
      change (decide (∃ a ∈ (∅ : Finset (Fin n)), (false : Bool) = true) ||
        decide (∃ u v, G.Adj u v ∧ (false : Bool) = true ∧ (false : Bool) = true)) = false
      simp
    refine ⟨fun _ => true, fun _ => false, ?_⟩
    rw [dfun,positive,negative]
    decide
  have lower : G.edgeSet.ncard + k ≤ D.size + 1 := by
    by_cases enough : G.edgeSet.ncard + k ≤ ∑ v : Fin n, (read D v).length
    · exact enough.trans (slots n D dmin outputsUnequal)
    · let live := (Finset.univ : Finset (Fin n)) \ A
      let heavy := live.filter (fun v => 3 ≤ (read D v).length)
      have deg_indicator (v : Fin n) : G.degree v = if v ∈ live then 3 else 0 := by
        by_cases marked : v ∈ A
        · have empty : G.neighborSet v = ∅ := by
            ext u
            simp only [SimpleGraph.mem_neighborSet,Set.mem_empty_iff_false,iff_false]
            exact fun adj => apart v u adj marked
          rw [← G.ncard_neighborSet v,empty]
          simp [live,marked]
        · rw [← G.ncard_neighborSet v,cubic v marked]
          simp [live,marked]
      have deg_sum : (∑ v : Fin n, G.degree v) = 3*live.card := by
        calc
          (∑ v : Fin n, G.degree v) = ∑ v : Fin n, if v ∈ live then 3 else 0 :=
            Finset.sum_congr rfl (fun v _ => deg_indicator v)
          _ = ∑ _v ∈ live, (3 : ℕ) := by
            rw [← Finset.sum_filter]
            congr 1
            ext v
            simp
          _ = 3*live.card := by simp [Nat.mul_comm]
      have edgeNum : G.edgeFinset.card = G.edgeSet.ncard := by
        rw [Set.ncard_eq_toFinset_card']
        rfl
      have incidence := G.sum_degrees_eq_twice_card_edges
      rw [deg_sum,edgeNum] at incidence
      have readWeight : 2*live.card + heavy.card ≤ ∑ v : Fin n, (read D v).length := by
        have heavy_sum : (∑ v ∈ live, if 3 ≤ (read D v).length then 1 else 0) = heavy.card := by
          rw [← Finset.sum_filter]
          simp [heavy]
        calc
          2*live.card + heavy.card = (∑ v ∈ live, (2 + (if 3 ≤ (read D v).length then 1 else 0))) := by
            rw [Finset.sum_add_distrib,heavy_sum]
            simp [Nat.mul_comm]
          _ ≤ ∑ v ∈ live, (read D v).length := by
            apply Finset.sum_le_sum
            intro v hv
            have vA : v ∉ A := (Finset.mem_sdiff.mp hv).2
            have r := (preserved v vA).1
            split <;> omega
          _ ≤ ∑ v : Fin n, (read D v).length :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intro v _ _; omega)
      have gap : (∑ v : Fin n, (read D v).length) < G.edgeSet.ncard + k := Nat.lt_of_not_ge enough
      have necessary : live.card + 2*heavy.card < 2*k := by omega
      have oddPart : ¬(PEqualNP.Library.Peel.delVerts G heavy).IsBipartite := by
        intro bip
        obtain ⟨left,right,part⟩ := SimpleGraph.isBipartite_iff_exists_isBipartiteWith.mp bip
        let L := live.filter (fun v => v ∈ left)
        let R := live.filter (fun v => v ∈ right)
        have apartSides : Disjoint L R := by
          apply Finset.disjoint_left.mpr
          intro v inL inR
          exact Set.disjoint_left.mp part.disjoint (Finset.mem_filter.mp inL).2 (Finset.mem_filter.mp inR).2
        have inside : L ∪ R ⊆ live := by
          intro v hv
          rcases Finset.mem_union.mp hv with inL | inR
          · exact (Finset.mem_filter.mp inL).1
          · exact (Finset.mem_filter.mp inR).1
        have sideCards := Finset.card_le_card inside
        rw [Finset.card_union_of_disjoint apartSides] at sideCards
        have twoCovers (u v : Fin n) (adj : G.Adj u v) :
            (u ∈ heavy ∪ L ∨ v ∈ heavy ∪ L) ∧ (u ∈ heavy ∪ R ∨ v ∈ heavy ∪ R) := by
          by_cases hu : u ∈ heavy
          · exact ⟨Or.inl (Finset.mem_union_left _ hu),Or.inl (Finset.mem_union_left _ hu)⟩
          by_cases hv : v ∈ heavy
          · exact ⟨Or.inr (Finset.mem_union_left _ hv),Or.inr (Finset.mem_union_left _ hv)⟩
          have huLive : u ∈ live := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,apart u v adj⟩
          have hvLive : v ∈ live := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,apart v u adj.symm⟩
          have adjLow : (PEqualNP.Library.Peel.delVerts G heavy).Adj u v := ⟨adj,hu,hv⟩
          rcases part.mem_of_adj adjLow with ⟨uLeft,vRight⟩ | ⟨uRight,vLeft⟩
          · exact ⟨Or.inl (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨huLive,uLeft⟩)),
              Or.inr (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvLive,vRight⟩))⟩
          · exact ⟨Or.inr (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvLive,vLeft⟩)),
              Or.inl (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨huLive,uRight⟩))⟩
        have lbound := (cover (heavy ∪ L) (fun u v h => (twoCovers u v h).1)).trans (Finset.card_union_le _ _)
        have rbound := (cover (heavy ∪ R) (fun u v h => (twoCovers u v h).2)).trans (Finset.card_union_le _ _)
        omega
      exact excess n k G A D cubic girth apart cover dmin dfun preserved oneTwo necessary oddPart gap
  omega
