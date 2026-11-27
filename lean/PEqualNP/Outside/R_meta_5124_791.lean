import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5124_791
  (highDegree : ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → ∀ x10 ⊆ PEqualNP.TopForm.Ustar x3 x7, (∀ (x12 x13 : Fin x2), s(x12, x13) ∈ x10 → ∀ x15 < x2 + x7.gates.length, x13 ∈ PEqualNP.TopForm.orIn x2 x7 x15 → ((2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 x15).card → ∃ x19 ∈ PEqualNP.TopForm.orIn x2 x7 x15, ¬x3.Adj x12 x19) ∧ ((3 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 x15).card → (2 : ℕ) ≤ {x19 ∈ PEqualNP.TopForm.orIn x2 x7 x15 | ¬x3.Adj x12 x19}.card)) → (∀ e ∈ x10, ∀ v ∈ e, 4 ≤ x3.degree v) → x10.card ≤ x1 * (x7.size + (1 : ℕ)))
  (lowDegree : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ x, C.eval (List.ofFn x) = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x) →
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
    ∀ edges : Finset (Sym2 (Fin n)),
    (∀ e ∈ edges, ∃ u v, G.Adj u v ∧ G.degree u ≤ 3 ∧ e = s(u, v)) →
    edges.card ≤ 3 * (2 * C.size + 1)) :
  ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → ∀ x10 ⊆ PEqualNP.TopForm.Ustar x3 x7, (∀ (x12 x13 : Fin x2), s(x12, x13) ∈ x10 → ∀ x15 < x2 + x7.gates.length, x13 ∈ PEqualNP.TopForm.orIn x2 x7 x15 → ((2 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 x15).card → ∃ x19 ∈ PEqualNP.TopForm.orIn x2 x7 x15, ¬x3.Adj x12 x19) ∧ ((3 : ℕ) ≤ (PEqualNP.TopForm.orIn x2 x7 x15).card → (2 : ℕ) ≤ {x19 ∈ PEqualNP.TopForm.orIn x2 x7 x15 | ¬x3.Adj x12 x19}.card)) → x10.card ≤ x1 * (x7.size + (1 : ℕ)) := by
  classical
  obtain ⟨bound, highBound⟩ := highDegree
  refine ⟨bound + 6, ?_⟩
  intro n G inst girth nonempty C least top edges subset sideCondition
  let high (e : Sym2 (Fin n)) : Prop := ∀ v ∈ e, 4 ≤ G.degree v
  have parts := Finset.card_filter_add_card_filter_not (s := edges) high
  have hb : (edges.filter high).card ≤ bound * (C.size + 1) := by
    apply highBound n G girth nonempty C least top
    · exact (Finset.filter_subset _ _).trans subset
    · intro u v huv
      exact sideCondition u v (Finset.mem_filter.mp huv).1
    · intro e he
      exact (Finset.mem_filter.mp he).2
  have lb : (edges.filter (fun e => ¬ high e)).card ≤ 3 * (2 * C.size + 1) := by
    apply lowDegree n G C
    · intro x
      exact congrFun least.2.1 x
    · intro g hg
      exact (least.1.2.2 g hg).le
    · intro e he
      have heG := (Finset.mem_sdiff.mp (subset (Finset.mem_filter.mp he).1)).1
      have notHigh := (Finset.mem_filter.mp he).2
      induction e using Sym2.inductionOn with
      | hf u v =>
        have adj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp heG
        by_cases hu : G.degree u ≤ 3
        · exact ⟨u, v, adj, hu, rfl⟩
        · have hv : G.degree v ≤ 3 := by
            by_contra h
            apply notHigh
            intro w hw
            rcases Sym2.mem_iff.mp hw with rfl | rfl <;> omega
          exact ⟨v, u, adj.symm, hv, Sym2.eq_swap⟩
  rw [Nat.add_mul]
  omega
