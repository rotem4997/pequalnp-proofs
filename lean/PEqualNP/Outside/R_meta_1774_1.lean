import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1774_1
    (hNonEdge : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.NoFourCycle G → PEqualNP.MetaComplexity.Monotone2 C →
      ∀ (j : ℕ) (u v p q : Fin n), G.Adj u v → G.Adj p q →
        u ≠ p → u ≠ q → v ≠ p → v ≠ q →
        PEqualNP.EdgeOwnership.Owns n C j u v → PEqualNP.EdgeOwnership.Owns n C j p q →
        ∃ a b : Fin n, ¬ G.Adj a b ∧
          PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput a b) = true)
    (hSound : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      PEqualNP.TopForm.NoFourCycle G →
      ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C →
        PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ →
        ∀ j < C.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          ∀ a b : Fin n,
            PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput a b) = true →
            G.Adj a b) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj],   (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) →     PEqualNP.TopForm.NoFourCycle x2 →       have x6 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x6 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ x7 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11;       have x7 : PEqualNP.CircuitLowerBounds.Circuit → ℕ := fun (x7 : PEqualNP.CircuitLowerBounds.Circuit) => {x8 : ℕ | ∃ (x9 : Fin x1) (x10 : Fin x1) (x11 : Fin x1) (x12 : Fin x1), x2.Adj x9 x10 ∧ x2.Adj x11 x12 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x9 x10 ∧ PEqualNP.EdgeOwnership.Owns x1 x7 x8 x11 x12 ∧ x9 ≠ x11 ∧ x9 ≠ x12 ∧ x10 ≠ x11 ∧ x10 ≠ x12}.ncard;       ∀ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x8 → PEqualNP.MetaComplexity.circuitFun x1 x8 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x6 x8 → (0 : ℕ) < x7 x8 → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x13 ∧ PEqualNP.MetaComplexity.circuitFun x1 x13 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ x13.size ≤ x8.size ∧ x6 x13 ∧ x7 x13 < x7 x8 := by
  intro n G _ htri hfour useful cost C hmin hfun _ hpos
  exfalso
  have hempty : {x8 : ℕ | ∃ (x9 x10 x11 x12 : Fin n), G.Adj x9 x10 ∧ G.Adj x11 x12 ∧
      PEqualNP.EdgeOwnership.Owns n C x8 x9 x10 ∧ PEqualNP.EdgeOwnership.Owns n C x8 x11 x12 ∧
      x9 ≠ x11 ∧ x9 ≠ x12 ∧ x10 ≠ x11 ∧ x10 ≠ x12} = ∅ := by
    ext j
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨u, v, p, q, huv, hpq, ho1, ho2, h1, h2, h3, h4⟩
    obtain ⟨a, b, hab, hval⟩ := hNonEdge n G C hfour hmin.1 j u v p q huv hpq h1 h2 h3 h4 ho1 ho2
    exact hab (hSound n G htri hfour C hmin hfun j ho1.1 ho1.2.1 a b hval)
  have hzero : cost C = 0 := by
    show Set.ncard _ = 0
    rw [hempty, Set.ncard_empty]
  omega
