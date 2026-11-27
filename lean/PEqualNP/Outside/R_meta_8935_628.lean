import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_8935_628
    (lower : ∀ (N : ℕ) (H : SimpleGraph (Fin N)) [DecidableRel H.Adj] (D : Circuit),
      H.IsBipartite → NoFourCycle H →
      (∀ X : Finset (Fin N), X.card ≤ 2 → (H.induce (↑X : Set (Fin N))ᶜ).Connected) →
      (∃ M : H.Subgraph, M.IsPerfectMatching) →
      (2 * H.edgeFinset.card - 3 * N)^3 ≤ N^2 →
      IsAO2 N D → circuitFun N D = graphFun H ∅ →
      H.edgeFinset.card + N/2 ≤ D.size + 1 + Nat.sqrt N)
    (amplify : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.IsBipartite → ¬G.IsAcyclic → NoFourCycle G → IsLeastAO G C →
      ∃ (m N : ℕ) (H : SimpleGraph (Fin N)) (_ : DecidableRel H.Adj) (D : Circuit),
        N < m^2 ∧ H.IsBipartite ∧ NoFourCycle H ∧
        (∀ X : Finset (Fin N), X.card ≤ 2 → (H.induce (↑X : Set (Fin N))ᶜ).Connected) ∧
        (∃ M : H.Subgraph, M.IsPerfectMatching) ∧
        (2 * H.edgeFinset.card - 3 * N)^3 ≤ N^2 ∧
        IsAO2 N D ∧ circuitFun N D = graphFun H ∅ ∧
        m*(G.edgeFinset.card + G.vertexCoverNum.toNat) + (D.size+1) ≤
        H.edgeFinset.card + N/2 + m*(C.size+1))
    : (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), x2.IsBipartite → ¬x2.IsAcyclic → PEqualNP.TopForm.NoFourCycle x2 → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (∃ x10 < x4.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ¬PEqualNP.TopForm.BelowF x2 x4 x10 ∧ ∃ (x11 : Fin x1) (x12 : Fin x1) (x13 : Fin x1) (x14 : Fin x1), x2.Adj x11 x12 ∧ x2.Adj x13 x14 ∧ s(x11, x12) ≠ s(x13, x14) ∧ PEqualNP.ReadK.readsAtMost x4 x1 [↑x11, ↑x12] (1 : ℕ) = Bool.false ∧ PEqualNP.ReadK.readsAtMost x4 x1 [↑x13, ↑x14] (1 : ℕ) = Bool.false ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x10 (PEqualNP.EdgeOwnership.pairInput x11 x12) = Bool.true ∧ PEqualNP.EdgeOwnership.gateVal x1 x4 x10 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true) → ∃ (x11 : Finset (Fin x1)), x2.IsVertexCover ↑x11 ∧ x2.edgeFinset.card + x11.card ≤ x4.size + (1 : ℕ)) := by
  classical
  intro n G dec C bip cyc sq least _ _
  obtain ⟨m, N, H, decH, D, order, color, linear, conn, matching, density, ao, func, cost⟩ :=
    amplify n G C bip cyc sq least
  let _ : DecidableRel H.Adj := decH
  have error : Nat.sqrt N < m := Nat.sqrt_lt.mpr (by simpa [pow_two] using order)
  have bound := lower N H D color linear conn matching density ao func
  have base : G.edgeFinset.card + G.vertexCoverNum.toNat ≤ C.size+1 := by
    by_contra! high
    have gap := Nat.mul_le_mul_left m (Nat.succ_le_of_lt high)
    rw [Nat.mul_succ] at gap
    omega
  obtain ⟨S, eqn, cover⟩ := G.vertexCoverNum_exists
  refine ⟨S.toFinset, by simpa using cover, ?_⟩
  rw [← eqn, Set.encard_eq_coe_toFinset_card] at base
  simpa using base
