import PEqualNP.Search.Helpers.Hierarchy.Draft

/-!
# Width of Gaussian refutations of Tseitin parity systems

`tseitinXorWidth`: the statement `TseitinXorWidth` of the draft, as written there. If deleting
any `2 * k` edges of `G` leaves a component with more than half of the vertices, and the
component of the charged vertex in `G` itself has more than half of the vertices, the Tseitin
parity system of `G` has no refutation by adding equations with every line on at most `k`
variables.

The proof. Every derived line is the sum of the vertex equations over a set `U` of vertices:
its variables are the edge boundary of `U` and its right side is "the charged vertex is in
`U`". The invariant carried through a derivation is that `U` can be taken with at most half
of the vertices. For a sum of two lines, with sets `U`, `U'` and boundaries `S`, `S'`, delete
`S ∪ S'` (at most `2 * k` edges): the large component left does not cross either boundary, so
it lies inside or outside each of `U`, `U'`, and it is too large to lie inside; so it misses
the symmetric difference of `U` and `U'`, which therefore has fewer than half of the vertices.
A refutation would be a set with empty boundary containing the charged vertex, so containing
its whole component, which has more than half of the vertices.
-/

namespace PEqualNP.Search.Helpers.HierarchyDraft

open PEqualNP.Search.Helpers

namespace TsW

variable {m n : ℕ}

/-- The edge boundary of a set of vertices: the edges with exactly one end in the set. -/
def bd (G : EdgeGraph m n) (U : Finset (Fin m)) : Finset (Fin n) :=
  Finset.univ.filter fun e => ¬ ((G.ends e).1 ∈ U ↔ (G.ends e).2 ∈ U)

theorem mem_bd (G : EdgeGraph m n) (U : Finset (Fin m)) (e : Fin n) :
    e ∈ bd G U ↔ ¬ ((G.ends e).1 ∈ U ↔ (G.ends e).2 ∈ U) := by
  simp [bd]

/-- The boundary of the empty set is empty. -/
theorem bd_empty (G : EdgeGraph m n) : bd G ∅ = ∅ := by
  ext e
  simp [mem_bd]

/-- The boundary of one vertex is the set of its edges (edges have two different ends). -/
theorem bd_singleton (G : EdgeGraph m n) (v : Fin m) : bd G {v} = G.incident v := by
  ext e
  have hl := G.loopless e
  simp only [mem_bd, Finset.mem_singleton, EdgeGraph.incident, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro h
    by_contra hc
    rw [not_or] at hc
    exact h ⟨fun h1 => absurd h1 hc.1, fun h2 => absurd h2 hc.2⟩
  · rintro (h | h) hiff
    · exact hl (h.trans (hiff.mp h).symm)
    · exact hl ((hiff.mpr h).trans h.symm)

/-- The boundary of a symmetric difference is the symmetric difference of the boundaries. -/
theorem bd_symmDiff (G : EdgeGraph m n) (U U' : Finset (Fin m)) :
    bd G (symmDiff U U') = symmDiff (bd G U) (bd G U') := by
  ext e
  simp only [mem_bd, Finset.mem_symmDiff]
  tauto

/-- A path that avoids a set of edges containing the boundary of `U` stays on one side. -/
theorem reach_side (G : EdgeGraph m n) {T : Finset (Fin n)} {U : Finset (Fin m)}
    (hT : bd G U ⊆ T) {v u : Fin m} (h : G.Reach T v u) : v ∈ U ↔ u ∈ U := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hadj ih =>
    refine ih.trans ?_
    obtain ⟨e, he, hends⟩ := hadj
    have hnb : e ∉ bd G U := fun hb => he (hT hb)
    rw [mem_bd, not_not] at hnb
    rcases hends with h | h
    · rw [h] at hnb
      exact hnb
    · rw [h] at hnb
      exact hnb.symm

open Classical in
/-- A set with at most half of the vertices misses every large component of the graph with
its boundary (or more) deleted. -/
theorem small_misses (G : EdgeGraph m n) {T : Finset (Fin n)} {U : Finset (Fin m)}
    (hT : bd G U ⊆ T) (hU : 2 * U.card ≤ m) {v : Fin m} (hv : G.BigComp T v)
    {u : Fin m} (hu : G.Reach T v u) : u ∉ U := by
  intro huU
  have hvU : v ∈ U := (reach_side G hT hu).mpr huU
  unfold EdgeGraph.BigComp at hv
  have hsub : (Finset.univ.filter fun u => G.Reach T v u) ⊆ U := by
    intro w hw
    exact (reach_side G hT (Finset.mem_filter.mp hw).2).mp hvU
  have := Finset.card_le_card hsub
  omega

open Classical in
/-- The invariant of a derivation: the line is the sum of the vertex equations over a set of
at most half of the vertices, and has at most `k` variables. -/
theorem derivable_invariant (G : EdgeGraph m n) (v0 : Fin m) (k : ℕ) (hm : 2 ≤ m)
    (hbig : ∀ S : Finset (Fin n), S.card ≤ 2 * k → ∃ v, G.BigComp S v)
    {e : PEqualNP.ProofComplexity.LinEq (Fin n)} (h : XorDerivable (tseitinXor G v0) k e) :
    ∃ U : Finset (Fin m), e.1 = bd G U ∧ e.2 = decide (v0 ∈ U) ∧ 2 * U.card ≤ m ∧
      e.1.card ≤ k := by
  induction h with
  | ax he hw =>
    obtain ⟨v, rfl⟩ := he
    refine ⟨{v}, (bd_singleton G v).symm, ?_, by simpa using hm, hw⟩
    by_cases hv : v = v0
    · simp [hv]
    · have hv' : ¬ v0 = v := fun h => hv h.symm
      simp [hv, hv']
  | zero => exact ⟨∅, (bd_empty G).symm, by simp, by simp, by simp⟩
  | @add e e' _ _ hw ih ih' =>
    obtain ⟨U, hS, hb, hU, hk⟩ := ih
    obtain ⟨U', hS', hb', hU', hk'⟩ := ih'
    refine ⟨symmDiff U U', ?_, ?_, ?_, hw⟩
    · show symmDiff e.1 e'.1 = _
      rw [bd_symmDiff, hS, hS']
    · show xor e.2 e'.2 = _
      rw [hb, hb']
      by_cases h1 : v0 ∈ U <;> by_cases h2 : v0 ∈ U' <;> simp [Finset.mem_symmDiff, h1, h2]
    · have hcard : (e.1 ∪ e'.1).card ≤ 2 * k := by
        have := Finset.card_union_le e.1 e'.1
        omega
      obtain ⟨v, hv⟩ := hbig _ hcard
      have hT : bd G U ⊆ e.1 ∪ e'.1 := hS ▸ Finset.subset_union_left
      have hT' : bd G U' ⊆ e.1 ∪ e'.1 := hS' ▸ Finset.subset_union_right
      have hv2 := hv
      unfold EdgeGraph.BigComp at hv2
      have hdis : Disjoint (Finset.univ.filter fun u => G.Reach (e.1 ∪ e'.1) v u)
          (symmDiff U U') := by
        rw [Finset.disjoint_left]
        intro u hu hmem
        have hr := (Finset.mem_filter.mp hu).2
        have h1 := small_misses G hT hU hv hr
        have h2 := small_misses G hT' hU' hv hr
        rw [Finset.mem_symmDiff] at hmem
        tauto
      have hle := Finset.card_le_univ
        ((Finset.univ.filter fun u => G.Reach (e.1 ∪ e'.1) v u) ∪ symmDiff U U')
      rw [Finset.card_union_of_disjoint hdis, Fintype.card_fin] at hle
      omega

end TsW

/-- The statement `TseitinXorWidth` of the draft, as written there: if deleting any `2 * k`
edges leaves a component with more than half of the vertices, and the charged vertex is in
such a component of the whole graph, the Tseitin parity system has no refutation by adding
equations with every line on at most `k` variables. -/
theorem tseitinXorWidth : TseitinXorWidth := by
  intro m n G v0 k hm hbig h0 href
  obtain ⟨U, hS, hb, hU, -⟩ := TsW.derivable_invariant G v0 k hm hbig href
  have hT : TsW.bd G U ⊆ ∅ := by
    rw [← hS]
  have hv0 : v0 ∈ U := by
    have : true = decide (v0 ∈ U) := hb
    simpa using this.symm
  exact TsW.small_misses G hT hU h0 Relation.ReflTransGen.refl hv0

end PEqualNP.Search.Helpers.HierarchyDraft
