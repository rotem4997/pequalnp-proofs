import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_4007_317
    (residualCover : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit) (i j : ℕ),
      G = PEqualNP.EdgeOwnership.edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] →
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      PEqualNP.TopForm.junk G C = {i,j} → PEqualNP.EdgeOwnership.InCone 11 C i j →
      C.size < 22 →
      let U := PEqualNP.TopForm.Ustar G C
      let Z := PEqualNP.TopForm.centreless G C
      let cost := 2 * Z.card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card
      3 + cost ≤ 2 * U.card →
      (PEqualNP.TopForm.tops G C \ Z).card + cost ≤ 4 + U.card →
      (∀ u v : Fin 11, s(u,v) ∈ U → ∃ k ∈ PEqualNP.TopForm.junk G C,
        ∀ b : Fin 2, u ∈ PEqualNP.TopForm.side C k b ∨ v ∈ PEqualNP.TopForm.side C k b) →
      ∃ K : Finset (Fin 11), (G.deleteEdges (U : Set (Sym2 (Fin 11)))).IsVertexCover (K : Set (Fin 11)) ∧
        K.card + U.card ≤ 7)
    (smallCharge : ∀ (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj]
      (C : PEqualNP.CircuitLowerBounds.Circuit) (i j : ℕ),
      G = PEqualNP.EdgeOwnership.edgeGraph 11 [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)] →
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      PEqualNP.TopForm.junk G C = {i,j} → PEqualNP.EdgeOwnership.InCone 11 C i j →
      C.size < 22 →
      let u := (PEqualNP.TopForm.Ustar G C).card
      2 ≤ u → u ≤ 3 →
      2 * u ≤ 2 + (2 * (PEqualNP.TopForm.centreless G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card)) :
    (∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] →     PEqualNP.TopForm.IsLeastAO x1 x3 →       PEqualNP.TopForm.TopForm x1 x3 →         PEqualNP.TopForm.junk x1 x3 = {x4, x5} →           PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 →             have x11 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;             have x12 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;             have x13 : ℕ := (2 : ℕ) * x12.card + (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card;             (3 : ℕ) + x13 ≤ (2 : ℕ) * x11.card → (PEqualNP.TopForm.tops x1 x3 \ x12).card + x13 ≤ (4 : ℕ) + x11.card → (∀ (x16 x17 : Fin (11 : ℕ)), s(x16, x17) ∈ x11 → ∃ x19 ∈ PEqualNP.TopForm.junk x1 x3, ∀ (x20 : Fin (2 : ℕ)), x16 ∈ PEqualNP.TopForm.side x3 x19 x20 ∨ x17 ∈ PEqualNP.TopForm.side x3 x19 x20) → (22 : ℕ) ≤ x3.size) := by
  intro G inst C i j graph least top junk cone
  dsimp only
  intro cap budget trace
  by_contra! small
  obtain ⟨K, cover, coverBound⟩ := residualCover G C i j graph least top junk cone small cap budget trace
  let U := PEqualNP.TopForm.Ustar G C
  let Z := PEqualNP.TopForm.centreless G C
  let cost := 2 * Z.card + (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card
  change 3 + cost ≤ 2 * U.card at cap
  change K.card + U.card ≤ 7 at coverBound
  have upper : U.card ≤ 3 := by
    by_contra! large
    have few : K.card ≤ 3 := by omega
    let edges : List (Fin 11 × Fin 11) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
    let missing (S : Finset (Fin 11)) : Finset (Sym2 (Fin 11)) :=
      ((edges.filter fun p => decide (p.1 ∉ S ∧ p.2 ∉ S)).map fun p => s(p.1,p.2)).toFinset
    have checked : ∀ S : Finset (Fin 11), S.card ≤ 3 → 8 ≤ S.card + (missing S).card := by
      dsimp [missing, edges]
      decide +kernel
    have listed : ∀ p ∈ edges, G.Adj p.1 p.2 := by
      rw [graph]
      dsimp [edges]
      decide +kernel
    have contained : missing K ⊆ U := by
      intro e he
      simp only [missing, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq] at he
      obtain ⟨p, ⟨hp, hleft, hright⟩, rfl⟩ := he
      by_contra omitted
      have adj := SimpleGraph.deleteEdges_adj.mpr ⟨listed p hp, omitted⟩
      exact (cover adj).elim hleft hright
    have edgesBound := Finset.card_le_card contained
    have tooMany := checked K few
    omega
  have lower : 2 ≤ U.card := by omega
  have charge := smallCharge G C i j graph least top junk cone small lower upper
  change 2 * U.card ≤ 2 + cost at charge
  omega
