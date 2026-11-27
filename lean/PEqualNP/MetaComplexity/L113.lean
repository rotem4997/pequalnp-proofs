import Mathlib
import PEqualNP.MetaComplexity.L204
import PEqualNP.MetaComplexity.Helpers.NotFreeCor

/-- Under girth at least nine and distance at least nine between vertices of degree at least
three, the edge function has a smallest fan-in-two circuit with no NOT gate. -/
theorem PEqualNP.MetaComplexity.L113 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 9 ≤ p.length) → (∀ (u v : Fin n), u ≠ v → 3 ≤ G.degree u → 3 ≤ G.degree v → ∀ p : G.Walk u v, 9 ≤ p.length) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.circuitFun n C = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ (∀ g ∈ D.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧ D.size ≤ C.size := by
  intro n G _ hcyc hdist C hC hfun
  by_cases hE : ∃ i j : Fin n, G.Adj i j
  · -- a least vertex cover
    have hne : ((Finset.univ : Finset (Fin n)).powerset.filter
        (fun T => ∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T)).Nonempty :=
      ⟨Finset.univ, by simp⟩
    obtain ⟨T, hTmem, hTmin⟩ := Finset.exists_min_image _ Finset.card hne
    have hTcov : ∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T := (Finset.mem_filter.1 hTmem).2
    have hmin : ∀ T' : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T' ∨ j ∈ T') →
        T.card ≤ T'.card := fun T' hT' =>
      hTmin T' (Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.subset_univ _), hT'⟩)
    have hnb : ∀ u : Fin n, (G.neighborSet u).ncard = G.degree u := by
      intro u
      rw [Set.ncard_eq_toFinset_card']
      rfl
    have hsize : PEqualNP.MetaComplexity.HasCircuitSize n
        (fun x : Fin n → Bool => @decide ((∃ a ∈ (∅ : Finset (Fin n)), x a = true) ∨
          ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _))
        C.size := by
      refine ⟨C, hC, le_rfl, fun x => ?_⟩
      have := congrFun hfun x
      simp only [PEqualNP.MetaComplexity.circuitFun] at this
      rw [this]
      simp
    have hlb := PEqualNP.MetaComplexity.L204 n T.card C.size G ∅
      (fun v c hc => le_trans (by norm_num) (hcyc v c hc))
      (fun u v huv hu hv p => le_trans (by norm_num)
        (hdist u v huv (by rwa [hnb] at hu) (by rwa [hnb] at hv) p))
      (fun i j _ => Finset.notMem_empty i) (Or.inr hE) hmin hsize
    obtain ⟨D, hD, hDnot, hDfun, hDsize⟩ := PEqualNP.MetaComplexity.Helpers.NotFreeCor.nfc_edge_upper_mono n G T hE hTcov
    refine ⟨D, hD, hDnot, hDfun.trans hfun.symm, ?_⟩
    have hec : G.edgeSet.ncard = G.edgeFinset.card := by
      rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
    rw [hec] at hlb
    simp only [Finset.card_empty] at hlb
    omega
  · refine ⟨⟨[], n⟩, by simp [PEqualNP.MetaComplexity.FanInTwo], by simp, ?_, by
      simp [PEqualNP.CircuitLowerBounds.Circuit.size]⟩
    rw [hfun]
    funext x
    simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_nil]
    have : ¬ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true :=
      fun ⟨i, j, h, _⟩ => hE ⟨i, j, h⟩
    simp [this]
