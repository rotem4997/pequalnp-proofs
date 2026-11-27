import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

-- Four vertices meet every edge except three disjoint pairs.
-- Fixing the cover on those four leaves forced vertices and one choice per remaining pair.
theorem PEqualNP.Outside.R_meta_2260_1
    (coverCost : ∀ (H : SimpleGraph (Fin (11 : ℕ))) [inst : DecidableRel H.Adj],
      let S : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};
      have M : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};
      (∀ (u v : Fin (11 : ℕ)), H.Adj u v → u ∈ S ∨ v ∈ S ∨ (u, v) ∈ M ∨ (v, u) ∈ M) →
      ∀ (K : Finset (Fin (11 : ℕ))),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover H K →
      ∃ B ⊆ S,
      (∀ v ∈ S \ B, ∀ w ∈ S \ B, ¬H.Adj v w) ∧
      let forced : Finset (Fin (11 : ℕ)) := {v ∈ Finset.univ \ S | ∃ a ∈ S \ B, H.Adj a v};
      have pairs : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {e ∈ M | H.Adj e.1 e.2 ∧ e.1 ∉ forced ∧ e.2 ∉ forced};
      K.card = B.card + forced.card + pairs.card)
    (gateCharge : ∀ (G : SimpleGraph (Fin (11 : ℕ))) [inst : DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
      G = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →
      PEqualNP.TopForm.IsLeastAO G C →
      PEqualNP.TopForm.TopForm G C →
      C.size < (22 : ℕ) →
      (∃ (i : ℕ) (j : ℕ), PEqualNP.TopForm.junk G C = {i, j} ∧ PEqualNP.EdgeOwnership.InCone (11 : ℕ) C i j) →
      let U : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar G C;
      let H : SimpleGraph (Fin (11 : ℕ)) := G.deleteEdges ↑U;
      let S : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};
      have M : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};
      ∀ B ⊆ S,
      (∀ u ∈ S \ B, ∀ w ∈ S \ B, ¬H.Adj u w) →
      let forced : Finset (Fin (11 : ℕ)) := {v ∈ Finset.univ \ S | ∃ w ∈ S \ B, H.Adj w v};
      have pairs : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {e ∈ M | H.Adj e.1 e.2 ∧ e.1 ∉ forced ∧ e.2 ∉ forced};
      (5 : ℕ) + U.card ≤ B.card + forced.card + pairs.card + (2 : ℕ) * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card) :
    ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         have x9 : Finset ℕ := PEqualNP.TopForm.tops x1 x3;         have x10 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;         have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;         (∀ x12 ∈ x9,             have x14 : Fin (2 : ℕ) → Finset (Fin (11 : ℕ)) := PEqualNP.TopForm.side x3 x12;             (∀ x15 ∈ x14 (0 : Fin (2 : ℕ)), ∀ x17 ∈ x14 (1 : Fin (2 : ℕ)), x1.Adj x15 x17) ∧ ((x14 (0 : Fin (2 : ℕ))).card ≤ (1 : ℕ) ∨ (x14 (1 : Fin (2 : ℕ))).card ≤ (1 : ℕ))) →           (∀ (x13 x14 : Fin (11 : ℕ)), s(x13, x14) ∈ x11 → ∃ x16 ∈ x9, ∃ (x17 : Fin (2 : ℕ)) (x18 : ℕ), (x18 = x4 ∨ x18 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x16 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x16 x17) x18 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x18 (PEqualNP.EdgeOwnership.pairInput x13 x14) = Bool.true) → (17 : ℕ) + (x9 \ x10).card + (2 : ℕ) * x10.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card ≤ x3.size + x11.card → (∀ (x15 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x11) x15 → x15.card ≤ (x9 \ x10).card) → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 → (22 : ℕ) ≤ x3.size := by
  intro G inst C i j hg hleast htop tops0 centre0 eqEdges hside hsource hcount hcovered hj hcone
  classical
  let U := Ustar G C
  let H := G.deleteEdges (U : Set _)
  let S := ({3, 8, 9, 10} : Finset (Fin 11))
  let M := ({(1, 4), (2, 5), (6, 7)} : Finset (Fin 11 × Fin 11))
  have graphShape : ∀ u v, (PEqualNP.EdgeOwnership.edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]).Adj u v →
      u ∈ S ∨ v ∈ S ∨ (u,v) ∈ M ∨ (v,u) ∈ M := by decide +kernel
  have shape : ∀ u v, H.Adj u v → u ∈ S ∨ v ∈ S ∨ (u,v) ∈ M ∨ (v,u) ∈ M := by
    intro u v huv
    apply graphShape u v
    rw [← hg]
    exact (SimpleGraph.deleteEdges_adj.mp huv).1
  let P := fun k : ℕ => ∃ K : Finset (Fin 11), H.IsVertexCover (K : Set _) ∧ K.card = k
  have ex : ∃ k, P k := ⟨11, Finset.univ, by simp [SimpleGraph.IsVertexCover], by simp⟩
  obtain ⟨K, covers, hk⟩ := Nat.find_spec ex
  have hmin : IsMinCover H K := by
    refine ⟨covers, ?_⟩
    intro A ha
    rw [hk]
    exact Nat.find_min' ex (show P A.card from ⟨A, ha, rfl⟩)
  obtain ⟨B, hB, valid, cost⟩ := coverCost H shape K hmin
  by_contra short
  have small : C.size < 22 := by omega
  have charge := gateCharge G C hg hleast htop small ⟨i,j,hj,hcone⟩ B hB valid
  have bound := hcovered K hmin
  change 17 + (tops G C \ centreless G C).card + 2 * (centreless G C).card +
    (orN G C \ lam G C).card ≤ C.size + U.card at hcount
  let F := (Finset.univ \ S).filter (fun v => ∃ a ∈ S \ B, H.Adj a v)
  let L := M.filter (fun e => H.Adj e.1 e.2 ∧ e.1 ∉ F ∧ e.2 ∉ F)
  change K.card = B.card + F.card + L.card at cost
  change (5 + U.card) ≤ B.card + F.card + L.card + 2 * (centreless G C).card +
    (orN G C \ lam G C).card at charge
  change K.card ≤ (tops G C \ centreless G C).card at bound
  omega