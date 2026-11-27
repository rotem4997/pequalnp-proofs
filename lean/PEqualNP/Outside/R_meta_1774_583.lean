import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm Relation

-- Select the first AND gate owning two disjoint edges.
-- Its nonedge witness cannot propagate to the output through OR gates alone.
theorem PEqualNP.Outside.R_meta_1774_583
    (invariant : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      let readOR (a b : ℕ) := ∃ k < C.size, a = n+k ∧ (gateAt C k).op = .or ∧
        b < n+k ∧ b ∈ (gateAt C k).inputs
      let bad (C : Circuit) (j : ℕ) := ∃ u v p q : Fin n, G.Adj u v ∧ G.Adj p q ∧
        Owns n C j u v ∧ Owns n C j p q ∧ u ≠ p ∧ u ≠ q ∧ v ≠ p ∧ v ≠ q
      NoFourCycle G → Monotone2 C → circuitFun n C = graphFun G ∅ →
      ∀ j : ℕ, bad C j →
        (∃ a b : Fin n, ¬ G.Adj a b ∧ gateVal n C j (pairInput a b) = true) ∧
        ¬ ReflTransGen readOR C.output (n+j))
    (repair : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      let readOR (a b : ℕ) := ∃ k < C.size, a = n+k ∧ (gateAt C k).op = .or ∧
        b < n+k ∧ b ∈ (gateAt C k).inputs
      let bad (C : Circuit) (j : ℕ) := ∃ u v p q : Fin n, G.Adj u v ∧ G.Adj p q ∧
        Owns n C j u v ∧ Owns n C j p q ∧ u ≠ p ∧ u ≠ q ∧ v ≠ p ∧ v ≠ q
      let useful (C : Circuit) := ∀ j < C.size, (gateAt C j).op = .and →
        ∃ u v : Fin n, G.Adj u v ∧ Owns n C j u v
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → NoFourCycle G →
      IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ → useful C →
      ∀ j, bad C j → (∀ i < j, ¬ bad C i) →
        ¬ ReflTransGen readOR C.output (n+j) →
        ∃ D : Circuit, Monotone2 D ∧ circuitFun n D = circuitFun n C ∧ D.size ≤ C.size ∧ useful D ∧
          {i | bad D i}.ncard < {i | bad C i}.ncard) :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ x7 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11;       have x7 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => {x8 : ℕ | ∃ (x9 : Fin x1) (x10 : Fin x1) (x11 : Fin x1) (x12 : Fin x1), x2.Adj x9 x10 ∧ x2.Adj x11 x12 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x9 x10 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x11 x12 ∧ x9 ≠ x11 ∧ x9 ≠ x12 ∧ x10 ≠ x11 ∧ x10 ≠ x12}.ncard;       ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x8 → PEqualNP.MetaComplexity.circuitFun x1 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x6 x8 → (0 : ℕ) < x7 x8 → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ PEqualNP.MetaComplexity.circuitFun x1 x13 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x13.size ≤ x8.size ∧ x6 x13 ∧ x7 x13 < x7 x8 := by
  intro n G inst triangle square useful cost C minimum correct usable positive
  classical
  let bad (j : ℕ) := ∃ u v p q : Fin n, G.Adj u v ∧ G.Adj p q ∧
    Owns n C j u v ∧ Owns n C j p q ∧ u ≠ p ∧ u ≠ q ∧ v ≠ p ∧ v ≠ q
  have badExists : ∃ j, bad j := by
    by_contra none
    have noBad : {j | bad j} = ∅ := by
      ext j
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun bj => none ⟨j,bj⟩
    change 0 < {j | bad j}.ncard at positive
    rw [noBad,Set.ncard_empty] at positive
    omega
  let j := Nat.find badExists
  have hj : bad j := Nat.find_spec badExists
  have first (i : ℕ) (hi : i < j) : ¬ bad i := fun own =>
    (not_le_of_gt hi) (Nat.find_min' badExists own)
  have masked := invariant n G C square minimum.1 correct j hj
  obtain ⟨D,mono,agree,size,owns,fewer⟩ := repair n G C triangle square minimum correct usable
    j hj first masked.2
  exact ⟨D,mono,agree.trans correct,size,owns,fewer⟩
