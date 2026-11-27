import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open scoped BigOperators

theorem PEqualNP.Outside.R_meta_2662_731
    (cutHalf : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (T : Finset (Sym2 (Fin n))), T ⊆ G.edgeFinset →
        ∃ (U : Finset (Sym2 (Fin n))) (c : Fin n → Bool), U ⊆ T ∧ T.card ≤ 2 * U.card ∧
          ∀ u v : Fin n, s(u, v) ∈ U → c u ≠ c v)
    (bipartiteBound : ∃ r k : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        (∀ v, G.degree v = 0 ∨ 3 ≤ G.degree v) →
        (∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → 5 ≤ w.length) →
        ∀ C : Circuit, IsMinimalMonoCircuit n C → circuitFun n C = graphFun G ∅ →
        ∀ T ⊆ G.edgeFinset,
          (∃ c : Fin n → Bool, ∀ u v : Fin n, s(u, v) ∈ T → c u ≠ c v) →
          (∀ u v : Fin n, s(u, v) ∈ T → ∀ j : ℕ, Owns n C j u v →
            let hit (a b : Fin n) := gateVal n C j (pairInput a b) = true
            let support (p : Fin n × Fin n) := ({p.1, p.2} : Finset (Fin n)) \ {u, v}
            hit u u ∨ hit v v ∨
              ∃ F : Finset (Fin n × Fin n), F.card = r + 3 ∧
                (∀ p ∈ F, hit p.1 p.2 ∧ ¬ G.Adj p.1 p.2) ∧
                (∀ p ∈ F, ∀ q ∈ F, p ≠ q → Disjoint (support p) (support q))) →
          T.card ≤ k * (C.size + 1)) :
    ∃ (x1 : ℕ) (x2 : ℕ),   ∀ (x3 : ℕ) (x4 : SimpleGraph (Fin x3)) [x5 : DecidableRel x4.Adj],     (∀ (x6 : Fin x3), x4.degree x6 = (0 : ℕ) ∨ (3 : ℕ) ≤ x4.degree x6) →       (∀ (x7 : Fin x3) (x8 : x4.Walk x7 x7), x8.IsCycle → (5 : ℕ) ≤ x8.length) →         ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.IsMinimalMonoCircuit x3 x8 →             PEqualNP.MetaComplexity.circuitFun x3 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x4 ∅ →               ∀ x11 ⊆ x4.edgeFinset,                 (∀ x13 ∈ x11,                     ∀ (x15 x16 : Fin x3),                       x13 = s(x15, x16) →                         ∀ (x18 : Fin x8.gates.length),                           PEqualNP.EdgeOwnership.Owns x3 x8 (↑x18) x15 x16 →                             have x20 : Fin x3 → Fin x3 → Prop := fun (x20 x21 : Fin x3) => PEqualNP.EdgeOwnership.gateVal x3 x8 (↑x18) (PEqualNP.EdgeOwnership.pairInput x20 x21) = Bool.true;                             have x21 : Fin x3 × Fin x3 → Finset (Fin x3) := fun (x21 : Fin x3 × Fin x3) => {x21.1, x21.2} \ {x15, x16};                             x20 x15 x15 ∨ x20 x16 x16 ∨ ∃ (x22 : Finset (Fin x3 × Fin x3)), x22.card = x1 + (3 : ℕ) ∧ (∀ x23 ∈ x22, x20 x23.1 x23.2 ∧ ¬x4.Adj x23.1 x23.2) ∧ ∀ x23 ∈ x22, ∀ x25 ∈ x22, x23 ≠ x25 → Disjoint (x21 x23) (x21 x25)) →                   x11.card ≤ x2 * (x8.size + (1 : ℕ)) := by
  obtain ⟨r, k, count⟩ := bipartiteBound
  refine ⟨r, 2 * k, ?_⟩
  intro n G inst degree girth C least computes T sub witnesses
  obtain ⟨U, c, subset, half, crossing⟩ := cutHalf n G T sub
  have countU := count n G degree girth C least computes U (subset.trans sub)
    ⟨c, crossing⟩ (by
      intro u v edge j owns
      exact witnesses _ (subset edge) u v rfl ⟨j, owns.1⟩ owns)
  exact half.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 2 countU)
