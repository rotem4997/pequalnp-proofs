import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The vertices with two effective readers supply a cheap vertex cover when their
-- induced graph is bipartite and every ordinary vertex has at least two readers.
theorem PEqualNP.Outside.R_meta_2636_73
    (slots : ∀ (n : ℕ) (C : Circuit) (A : Finset (Fin n)), IsMinimalCircuit n C →
      (∀ a ∈ A, ∃ x y : Fin n → Bool, (∀ j, j ≠ a → x j = y j) ∧
        circuitFun n C x ≠ circuitFun n C y) →
      A.card + ∑ v ∈ Aᶜ, (C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length ≤ C.size + 1)
    (star : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A T : Finset (Fin n)),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) → (∀ u v, G.Adj u v → u ∉ A) →
      (∃ u v, G.Adj u v) → (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) →
      ∃ z ∉ A, ∃ t : ℕ, t+5 ≤ A.card + G.edgeSet.ncard + T.card ∧
        HasCircuitSize n (fun x => NestedCover.graphFun G A (Function.update x z false)) t)
    (one : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
      IsMinimalCircuit n C → circuitFun n C = NestedCover.graphFun G A →
      (∀ T : Finset (Fin n), G.IsVertexCover (T : Set (Fin n)) →
        C.size + 1 < A.card + G.edgeSet.ncard + T.card) →
      (∃ v ∉ A, (C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length ≤ 1) →
      ∃ z ∉ A, ∃ t : ℕ, t+4 ≤ C.size ∧ HasCircuitSize n
        (fun x => circuitFun n C (Function.update x z false)) t)
    (odd : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) →
      (∀ v (w : G.Walk v v), w.IsCycle → 7 ≤ w.length) →
      (∀ u v, G.Adj u v → u ∉ A) → (∃ u v, G.Adj u v) →
      IsMinimalCircuit n C → circuitFun n C = NestedCover.graphFun G A →
      (∀ T : Finset (Fin n), G.IsVertexCover (T : Set (Fin n)) →
        C.size + 1 < A.card + G.edgeSet.ncard + T.card) →
      (∀ v ∉ A, 2 ≤ (C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length) →
      ¬(G.induce {v : Fin n | v ∉ A ∧ (C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length = 2}).Colorable 2 →
      ∃ z ∉ A, ∃ t : ℕ, t+4 ≤ C.size ∧ HasCircuitSize n
        (fun x => circuitFun n C (Function.update x z false)) t) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool), (∀ x5 ∉ x3, (x2.neighborSet x5).ncard = (3 : ℕ)) → (∀ (x6 : Fin x1) (x7 : x2.Walk x6 x6), x7.IsCycle → (7 : ℕ) ≤ x7.length) → (∀ (x7 x8 : Fin x1), x2.Adj x7 x8 → x7 ∉ x3) → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → (∀ (x9 : Fin x1 → Bool), x4 x9 = Bool.true ↔ (∃ x10 ∈ x3, x9 x10 = Bool.true) ∨ ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ x9 x10 = Bool.true ∧ x9 x11 = Bool.true) → ∀ (x10 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x10 → ∃ x12 ∉ x3, ∃ (x13 : ℕ), x13 + (4 : ℕ) ≤ x10 ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x14 : Fin x1 → Bool) => x4 (Function.update x14 x12 Bool.false)) x13 := by
  classical
  let readers {n : ℕ} (C : Circuit) (v : Fin n) : ℕ := (C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val).length
  -- A larger color class of L supplies an independent set with twice its size at least |L|.
  have colorClass {n : ℕ} (G : SimpleGraph (Fin n)) (L : Finset (Fin n))
      (hc : (G.induce (L : Set (Fin n))).Colorable 2) :
      ∃ I ⊆ L, L.card ≤ 2 * I.card ∧ ∀ u ∈ I, ∀ v ∈ I, ¬G.Adj u v := by
    classical
    obtain ⟨color⟩ := hc
    let c (v : Fin n) : Fin 2 := if h : v ∈ L then color ⟨v,h⟩ else 0
    have distinct (u v : Fin n) (hu : u ∈ L) (hv : v ∈ L) (e : G.Adj u v) : c u ≠ c v := by
      simpa only [c, dite_eq_left hu, dite_eq_left hv] using
        color.valid (show (G.induce (L : Set (Fin n))).Adj ⟨u,hu⟩ ⟨v,hv⟩ from e)
    let X := L.filter fun v => c v = 0
    let Y := L.filter fun v => ¬c v = 0
    have cards : X.card + Y.card = L.card := Finset.card_filter_add_card_filter_not _
    by_cases large : Y.card ≤ X.card
    · refine ⟨X, Finset.filter_subset _ _, by omega, ?_⟩
      intro u hu v hv edge
      obtain ⟨ul,uc⟩ := Finset.mem_filter.mp hu
      obtain ⟨vl,vc⟩ := Finset.mem_filter.mp hv
      exact distinct u v ul vl edge (uc.trans vc.symm)
    · refine ⟨Y, Finset.filter_subset _ _, by omega, ?_⟩
      intro u hu v hv edge
      obtain ⟨ul,uc⟩ := Finset.mem_filter.mp hu
      obtain ⟨vl,vc⟩ := Finset.mem_filter.mp hv
      apply distinct u v ul vl edge
      have onlyOne : ∀ a : Fin 2, a ≠ 0 → a = 1 := by decide
      exact (onlyOne _ uc).trans (onlyOne _ vc).symm

  have coverBudget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (C : Circuit)
      (degree : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
      (isolated : ∀ u v, G.Adj u v → u ∉ A)
      (hC : IsMinimalCircuit n C) (he : circuitFun n C = NestedCover.graphFun G A)
      (twice : ∀ v ∉ A, 2 ≤ readers C v)
      (hc : (G.induce {v : Fin n | v ∉ A ∧ readers C v = 2}).Colorable 2) :
      ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
        A.card + G.edgeFinset.card + T.card ≤ C.size + 1 := by
    classical
    let U := Aᶜ
    let L := U.filter fun v => readers C v = 2
    have lsub : L ⊆ U := Finset.filter_subset _ _
    have asSet : (L : Set (Fin n)) = {v : Fin n | v ∉ A ∧ readers C v = 2} := by
      ext v
      simp [L,U]
    obtain ⟨I, iL, half, indep⟩ := colorClass G L (asSet ▸ hc)
    have iU := iL.trans lsub
    refine ⟨U \ I, ?_, ?_⟩
    · intro u v e
      have uU : u ∈ U := Finset.mem_compl.mpr (isolated u v e)
      have vU : v ∈ U := Finset.mem_compl.mpr (isolated v u e.symm)
      by_cases ui : u ∈ I
      · exact Or.inr (Finset.mem_sdiff.mpr ⟨vU, fun vi => indep u ui v vi e⟩)
      · exact Or.inl (Finset.mem_sdiff.mpr ⟨uU,ui⟩)
    · have budget := slots n C A hC (by
        intro a ha
        let z : Fin n → Bool := fun _ => false
        let y : Fin n → Bool := fun i => decide (i = a)
        refine ⟨z,y,fun i hi => by simp [z,y,hi],?_⟩
        rw [he]
        have hz : NestedCover.graphFun G A z = false := by
          change (decide (∃ a ∈ A, z a = true) || decide (∃ i j, G.Adj i j ∧ z i = true ∧ z j = true)) = false
          simp [z]
        have hy : NestedCover.graphFun G A y = true := by
          change (decide (∃ a ∈ A, y a = true) || decide (∃ i j, G.Adj i j ∧ y i = true ∧ y j = true)) = true
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          exact Or.inl ⟨a,ha,by simp [y]⟩
        rw [hz,hy]
        decide)
      have small (v : Fin n) (hv : v ∈ L) : 2 ≤ readers C v :=
        (Finset.mem_filter.mp hv).2.ge
      have big (v : Fin n) (hv : v ∈ U \ L) : 3 ≤ readers C v := by
        obtain ⟨vu,vl⟩ := Finset.mem_sdiff.mp hv
        have h := twice v (Finset.mem_compl.mp vu)
        have h' : readers C v ≠ 2 := fun eq => vl (Finset.mem_filter.mpr ⟨vu,eq⟩)
        omega
      have lo := Finset.sum_le_sum small
      have hi := Finset.sum_le_sum big
      simp only [Finset.sum_const, smul_eq_mul] at lo hi
      have splitSum := Finset.sum_sdiff lsub (f := readers C)
      have hL := Finset.card_sdiff_add_card_eq_card lsub
      have hI := Finset.card_sdiff_add_card_eq_card iU
      have dA (a : Fin n) (ha : a ∈ A) : G.degree a = 0 :=
        (G.degree_eq_zero a).mpr (fun j h => isolated a j h ha)
      have dU (a : Fin n) (ha : a ∈ Aᶜ) : G.degree a = 3 := by
        rw [← G.ncard_neighborSet]
        exact degree a (Finset.mem_compl.mp ha)
      have handshake := G.sum_degrees_eq_twice_card_edges
      rw [← A.sum_add_sum_compl, Finset.sum_congr rfl dA, Finset.sum_congr rfl dU] at handshake
      simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul] at handshake
      change A.card + ∑ a ∈ U, readers C a ≤ C.size + 1 at budget
      change U.card * 3 = 2 * G.edgeFinset.card at handshake
      omega
  intro n G A f deg girth isolated edges spec s has
  let available (k : ℕ) := HasCircuitSize n f k
  have nonempty : ∃ k, available k := ⟨s,has⟩
  obtain ⟨C,fan,cap,eval⟩ := Nat.find_spec nonempty
  have correct : circuitFun n C = f := funext eval
  have minC : IsMinimalCircuit n C := by
    refine ⟨fan, fun D good same => cap.trans ?_⟩
    exact Nat.find_min' nonempty (show HasCircuitSize n f D.size from
      ⟨D,good,le_rfl,fun x => congrFun (same.trans correct) x⟩)
  have Cs : C.size ≤ s := cap.trans (Nat.find_min' nonempty has)
  have rep : circuitFun n C = NestedCover.graphFun G A := by
    rw [correct]
    funext x
    apply Bool.eq_iff_iff.mpr
    change (f x = true) ↔
      (decide (∃ a ∈ A, x a = true) || decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) = true
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using spec x
  suffices h : ∃ z ∉ A, ∃ t : ℕ, t+4 ≤ C.size ∧ HasCircuitSize n
      (fun x => circuitFun n C (Function.update x z false)) t by
    obtain ⟨z,za,t,ht,build⟩ := h
    exact ⟨z,za,t,ht.trans Cs, by simpa only [correct] using build⟩
  have card_eq : G.edgeFinset.card = G.edgeSet.ncard := by
    rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
  by_cases better : (∀ T : Finset (Fin n), G.IsVertexCover (T : Set (Fin n)) →
        C.size + 1 < A.card + G.edgeSet.ncard + T.card)
  · by_cases single : ∃ v ∉ A, readers C v ≤ 1
    · exact one n G A C deg girth isolated edges minC rep better single
    have twice (v : Fin n) (hv : v ∉ A) : 2 ≤ readers C v := by
      by_contra! h
      exact single ⟨v,hv,by omega⟩
    apply odd n G A C deg girth isolated edges minC rep better twice
    intro color
    obtain ⟨T,cover,budget⟩ := coverBudget G A C deg isolated minC rep twice color
    have strictBound := better T (fun {u v} e => cover u v e)
    rw [card_eq] at budget
    omega
  · push_neg at better
    obtain ⟨T,cover,budget⟩ := better
    obtain ⟨z,hz,t,ht,build⟩ := star n G A T deg isolated edges (fun _ _ e => cover e)
    exact ⟨z,hz,t,by omega,by rw [rep]; exact build⟩
