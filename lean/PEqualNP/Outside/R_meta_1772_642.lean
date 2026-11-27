import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_1772_642
    (star : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n)),
      CoverPromise.IsVertexCover G T → ∃ C : Circuit, Monotone2 C ∧
        circuitFun n C = graphFun G ∅ ∧ C.size ≤ G.edgeSet.ncard + T.card - 1 ∧
        ∀ j < C.size, (gateAt C j).op = GateOp.and → ∃ u v, G.Adj u v ∧ Owns n C j u v)
    (below : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (D : Circuit),
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → NoFourCycle G →
      IsMinimalMonoCircuit n D → circuitFun n D = graphFun G ∅ →
      (∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T →
        D.size < G.edgeSet.ncard + T.card - 1) →
      ∃ C : Circuit, Monotone2 C ∧ circuitFun n C = graphFun G ∅ ∧ C.size ≤ D.size ∧
        ∀ j < C.size, (gateAt C j).op = GateOp.and → ∃ u v, G.Adj u v ∧ Owns n C j u v) :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj], (∀ (x4 x5 x6 : Fin x1), x2.Adj x4 x5 → x2.Adj x5 x6 → ¬x2.Adj x6 x4) → PEqualNP.TopForm.NoFourCycle x2 → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalMonoCircuit x1 x6 ∧ PEqualNP.MetaComplexity.circuitFun x1 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ ∧ ∀ x7 < x6.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x6 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11 ∧ PEqualNP.EdgeOwnership.Owns x1 x6 x7 x10 x11 := by
  intro n G _ tri four
  classical
  let f := graphFun G ∅
  let feasible (k : ℕ) := ∃ C : Circuit, Monotone2 C ∧ circuitFun n C = f ∧ C.size = k
  have existsSize : ∃ k, feasible k := by
    obtain ⟨C, h, eq, _, _⟩ := star n G Finset.univ (fun _ _ _ => Or.inl (Finset.mem_univ _))
    exact ⟨_, C, h, eq, rfl⟩
  obtain ⟨D, mono, computes, size⟩ := Nat.find_spec existsSize
  have least (C : Circuit) (h : Monotone2 C) (eq : circuitFun n C = f) : D.size ≤ C.size := by
    rw [size]
    exact Nat.find_min' existsSize (show feasible C.size from ⟨C,h,eq,rfl⟩)
  have minimal : IsMinimalMonoCircuit n D := ⟨mono, fun C h eq => least C h (eq.trans computes)⟩
  have finish (C : Circuit) (h : Monotone2 C) (eq : circuitFun n C = f) (le : C.size ≤ D.size)
      (owns : ∀ j < C.size, (gateAt C j).op = GateOp.and → ∃ u v, G.Adj u v ∧ Owns n C j u v) :
      IsMinimalMonoCircuit n C ∧ circuitFun n C = f ∧
        ∀ j < C.size, (gateAt C j).op = GateOp.and → ∃ u v, G.Adj u v ∧ Owns n C j u v :=
    ⟨⟨h, fun B hb same => le.trans (least B hb (same.trans eq))⟩, eq, owns⟩
  by_cases cheap : ∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T →
      D.size < G.edgeSet.ncard + T.card - 1
  · obtain ⟨C,h,eq,le,owns⟩ := below n G D tri four minimal computes cheap
    exact ⟨C, finish C h eq le owns⟩
  · push_neg at cheap
    obtain ⟨T,cover,le⟩ := cheap
    obtain ⟨C,h,eq,cost,owns⟩ := star n G T cover
    exact ⟨C, finish C h eq (cost.trans le) owns⟩
