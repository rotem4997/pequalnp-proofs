import Mathlib
import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- The four-cycle argument uses the walk construction from L_meta_1733.
theorem PEqualNP.Outside.R_meta_4011_214
  (separate : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
    FanInTwo C → circuitFun n C = graphFun G A → (∀ a b, G.Adj a b → a∉A) →
    PEqualNP.TopForm.NoFourCycle G → ∀ v∉A, ∀ T : Finset (Fin n), v∉T →
    Disjoint A T → (∀ a∈T, ∀ b∈T, ¬G.Adj a b) → T.card < (G.neighborFinset v).card →
    ∃ g ∈ C.gates, v.val ∈ g.inputs.take (bif g.op.eval [false] then 1 else 2) ∧
      (g.op ≠ .or ∨ ∀ t∈T, t.val∉g.inputs))
  (residual : ∀ (n : Nat) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
    (∀ v∉A, (G.neighborSet v).ncard=3) → (∀ v : Fin n, ∀ w : G.Walk v v, w.IsCycle → 7≤w.length) →
    (∀ a b, G.Adj a b → a∉A) → (∃ a b, G.Adj a b) → IsMinimalCircuit n C → circuitFun n C=graphFun G A →
    (∀ v∉A, let R := C.gates.filter fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
      R.length≤3 ∧ (R.length=3 → ∀ g∈R, g.op=.or) ∧
        ∀ T : Finset (Fin n), v∉T → Disjoint A T → T.card≤2 → (∀ a∈T, ∀ b∈T, ¬G.Adj a b) →
          ∃ g∈R, g.op≠.or ∨ ∀ t∈T, t.val∉g.inputs) →
    (∀ K : Finset (Fin n), Disjoint A K → (∀ a b, G.Adj a b → a∈K ∨ b∈K) →
      C.size+1<A.card+G.edgeFinset.card+K.card) →
    ∃ v∉A, ∃ k, k+4≤C.size ∧ HasCircuitSize n (fun x => circuitFun n C (Function.update x v false)) k) :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x4, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x4) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 →             PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4 →               (∀ x12 ∉ x4,                   have x14 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x14.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x14.inputs).contains ↑x12) x5.gates;                   x14.length ≤ (3 : ℕ) ∧ (x14.length = (3 : ℕ) → ∀ x16 ∈ x14, x16.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                 (∀ (x13 : Finset (Fin x1)), Disjoint x4 x13 → (∀ (x15 x16 : Fin x1), x2.Adj x15 x16 → x15 ∈ x13 ∨ x16 ∈ x13) → x5.size + (1 : ℕ) < x4.card + x2.edgeFinset.card + x13.card) → ∃ x14 ∉ x4, ∃ (x15 : ℕ), x15 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => PEqualNP.MetaComplexity.circuitFun x1 x5 (Function.update x16 x14 Bool.false)) x15 := by
  intro n G inst A C cubic girth active edge minimal correct readers below
  have four : PEqualNP.TopForm.NoFourCycle G := by
    intro a b hab
    by_contra hc
    rw [not_le] at hc
    obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.mp hc
    rw [Finset.mem_filter] at hw1 hw2
    obtain ⟨-, ha1, hb1⟩ := hw1
    obtain ⟨-, ha2, hb2⟩ := hw2
    have e1 := G.ne_of_adj ha1
    have e2 := G.ne_of_adj hb1
    have e3 := G.ne_of_adj ha2
    have e4 := G.ne_of_adj hb2
    have hcyc : (SimpleGraph.Walk.cons ha1 (SimpleGraph.Walk.cons hb1.symm
        (SimpleGraph.Walk.cons hb2 (SimpleGraph.Walk.cons ha2.symm SimpleGraph.Walk.nil)))).IsCycle := by
      rw [SimpleGraph.Walk.cons_isCycle_iff]
      refine ⟨?_, ?_⟩
      · simp [SimpleGraph.Walk.cons_isPath_iff, e1, e2, e3, e4, hab, hne, Ne.symm e1, Ne.symm e2,
          Ne.symm e3, Ne.symm e4, Ne.symm hab, Ne.symm hne]
      · simp [Sym2.eq_iff, e1, e2, e3, e4, hab, hne, Ne.symm e1, Ne.symm e2,
          Ne.symm e3, Ne.symm e4, Ne.symm hab, Ne.symm hne]
    have h5 := girth a _ hcyc
    simp at h5
  apply residual n G A C cubic girth active edge minimal correct _ below
  intro v hv R
  obtain ⟨bound,three⟩ := readers v hv
  refine ⟨bound,three,?_⟩
  intro T vT clean two independent
  have small : T.card < (G.neighborFinset v).card := by
    change T.card < (G.neighborSet v).toFinset.card
    rw [← Set.ncard_eq_toFinset_card',cubic v hv]
    omega
  obtain ⟨gate,mem,pin,avoids⟩ := separate n G A C minimal.1 correct active four v hv T vT clean independent small
  exact ⟨gate,List.mem_filter.mpr ⟨mem,List.contains_iff_mem.mpr pin⟩,avoids⟩
