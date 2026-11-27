import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.A5387

theorem PEqualNP.MetaComplexity.L5387 : (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) → (∀ k < C.gates.length, ∃ x : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n C k x = true) → ∀ h < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C h).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.TopForm.BelowF G C h ↔ ∀ k < C.gates.length, PEqualNP.EdgeOwnership.InCone n C h k → (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.or)) → ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) → (∀ k < C.gates.length, ∃ x : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n C k x = true) → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t : Fin n, PEqualNP.EdgeOwnership.gateVal n C k (fun r => decide (r = t)) = false) → ∀ (u v : Fin n) (o : ℕ), G.Adj u v → C.output = n + o → PEqualNP.Core.ReadTwiceAt n C o u v → ∃ Y < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C Y).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬ PEqualNP.TopForm.BelowF G C Y ∧ PEqualNP.EdgeOwnership.gateVal n C Y (PEqualNP.EdgeOwnership.pairInput u v) = true ∧ ((u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C Y 0) ∧ v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C Y 1)) ∨ (v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C Y 0) ∧ u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C Y 1))) := by
  intro H n G _ C hC hF hcone hlift handlow hlive hone u v o huv hout hread
  have hval : ∀ x : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C C.output x =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x := fun x => congrFun hF x
  have htrue : PEqualNP.CleanedNonEdge.wireVal n C C.output (PEqualNP.EdgeOwnership.pairInput u v)
      = true := by
    rw [hval]
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨u, v, huv, by simp [PEqualNP.EdgeOwnership.pairInput],
      by simp [PEqualNP.EdgeOwnership.pairInput]⟩
  have ho : o < C.gates.length := by
    by_contra h
    have h2 : PEqualNP.CleanedNonEdge.wireVal n C C.output (PEqualNP.EdgeOwnership.pairInput u v)
        = false := by
      unfold PEqualNP.CleanedNonEdge.wireVal
      rw [PEqualNP.MetaComplexity.ReadTwoBridge.wires_eq]
      apply PEqualNP.MetaComplexity.ReadTwoBridge.foldl_snoc_beyond
        (fun ins (g : PEqualNP.CircuitLowerBounds.Gate) => g.op.eval ins) false
      rw [List.length_ofFn, hout]
      omega
    rw [h2] at htrue
    exact Bool.false_ne_true htrue
  have hlt : C.output < n + C.gates.length := by omega
  have hunit : ∀ t : Fin n, t ∉ PEqualNP.TopForm.orIn n C C.output := by
    intro t ht
    have h1 := PEqualNP.MetaComplexity.Helpers.A5387.orIn_val hC t _ hlt ht
      (fun r => decide (r = t)) (by simp)
    rw [hval] at h1
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Bool.or_eq_true,
      decide_eq_true_eq] at h1
    rcases h1 with ⟨a, ha, _⟩ | ⟨a, b, hab, rfl, h⟩
    · exact absurd ha (Finset.notMem_empty a)
    · exact G.ne_of_adj hab h.symm
  rcases PEqualNP.MetaComplexity.Helpers.A5387.descent hC u v _ hlt htrue with
    h | h | ⟨X, hX, hr, hop, hv⟩
  · exact (hunit u h).elim
  · exact (hunit v h).elim
  obtain ⟨Y, hY, hY2, hY3, hY4, hY5⟩ :=
    PEqualNP.MetaComplexity.Helpers.A5387.sep_below hC hone u v X hX hop hv
  rw [hout] at hr
  have hcX : PEqualNP.EdgeOwnership.InCone n C Y X := by
    rcases hY5 with rfl | hY5
    · exfalso
      have h1 := PEqualNP.MetaComplexity.Helpers.A5387.read_one hC u v (G.ne_of_adj huv) Y o ho hY
        hY2 hr hY4
      unfold PEqualNP.Core.ReadTwiceAt at hread
      rw [hread] at h1
      exact Bool.false_ne_true h1
    · exact hY5
  refine ⟨Y, hY, hY2, fun hb => ?_, hY3, hY4⟩
  have h1 := (H n G C hC hF hcone hlift handlow hlive Y hY hY2).1 hb X hX hcX
  rw [hop] at h1
  exact PEqualNP.CircuitLowerBounds.GateOp.noConfusion h1
