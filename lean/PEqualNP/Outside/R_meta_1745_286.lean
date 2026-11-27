import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_1745_286
    (unmaskable :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (A : Finset (Fin n)) (C : Circuit),
      let R := fun (v : Fin n) => C.gates.filter
        (fun g => ((g.inputs.take (bif g.op.eval [false] then 1 else 2))).contains v.val)
      (∀ v, G.degree v = if v ∈ A then 0 else 3) → 7 ≤ G.egirth →
      FanInTwo C → circuitFun n C = graphFun G A →
      ∀ v ∉ A, ∀ P Z : Finset (Fin n), (P ∪ Z).card ≤ 2 → v ∉ P ∪ Z →
        G.IsIndepSet (P : Set (Fin n)) → Disjoint A P → Disjoint P Z →
        ¬ ∀ g ∈ R v, ∃ i : Fin n, i.val ∈ g.inputs ∧
          ((i ∈ P ∧ g.op = .or) ∨ (i ∈ Z ∧ g.op = .and)))
    (residual :
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (A : Finset (Fin n)) (C : Circuit),
      let R := fun (v : Fin n) => C.gates.filter
        (fun g => ((g.inputs.take (bif g.op.eval [false] then 1 else 2))).contains v.val)
      (∀ v, G.degree v = if v ∈ A then 0 else 3) → 7 ≤ G.egirth →
      G ≠ ⊥ → IsMinimalCircuit n C → circuitFun n C = graphFun G A →
      (∀ v ∉ A, (R v).length ≤ 3 ∧ ((R v).length = 3 → ∀ g ∈ R v, g.op = .or)) →
      (∀ v ∉ A, ∀ P Z : Finset (Fin n), (P ∪ Z).card ≤ 2 → v ∉ P ∪ Z →
        G.IsIndepSet (P : Set (Fin n)) → Disjoint A P → Disjoint P Z →
        ¬ ∀ g ∈ R v, ∃ i : Fin n, i.val ∈ g.inputs ∧
          ((i ∈ P ∧ g.op = .or) ∨ (i ∈ Z ∧ g.op = .and))) →
      ∃ v ∉ A, ∃ s, s+4 ≤ C.size ∧ HasCircuitSize n (fun x => graphFun G A (Function.update x v false)) s) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     ∃ x15 ∉ x3, ∃ (x16 : ℕ), x16 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x4 (Function.update x17 x15 Bool.false)) x16 := by
  classical
  intro n G A f C deg girth noMarked edges spec fan total min reads
  letI : DecidableRel G.Adj := Classical.decRel _
  have reg (v : Fin n) : G.degree v = if v ∈ A then 0 else 3 := by
    by_cases m : v ∈ A
    · rw [if_pos m]
      apply (G.degree_eq_zero v).mpr
      intro w h
      exact noMarked v w h m
    · rw [if_neg m,← G.ncard_neighborSet]
      exact deg v m
  have large : 7 ≤ G.egirth := SimpleGraph.le_egirth.mpr
    (fun v w cycle => by exact_mod_cast girth v w cycle)
  have nonempty : G ≠ ⊥ := by
    obtain ⟨u,v,edge⟩ := edges
    exact fun empty => (SimpleGraph.eq_bot_iff_forall_not_adj.mp empty) u v edge
  have eq : f = graphFun G A := by
    funext x
    have law : graphFun G A x = true ↔
        (∃ a ∈ A, x a = true) ∨ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
      change (decide (∃ a ∈ A, x a = true) || decide (∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)) = true ↔
        (∃ a ∈ A, x a = true) ∨ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true
      simp only [Bool.or_eq_true,decide_eq_true_eq]
    exact Bool.eq_iff_iff.mpr ((spec x).trans law.symm)
  have optimal : IsMinimalCircuit n C := by
    refine ⟨fan,?_⟩
    intro D hd same
    exact min D.size ⟨D,hd,le_rfl,fun x => congrFun (same.trans total) x⟩
  have result := residual n G A C reg large nonempty optimal (total.trans eq) reads
    (unmaskable n G A C reg large fan (total.trans eq))
  rw [eq]
  exact result
