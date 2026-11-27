import PEqualNP.MetaComplexity.Helpers.OneNotEval

/-!
# One NOT gate: splitting around the NOT gate

S-SPLIT (step 6 of the build plan): a gate list of
AND, OR and NOT gates with at most one NOT gate (stated by indices, since `GateOp` has no
decidable equality) is NOT-free, or is (AND/OR gates) ++ one NOT gate :: (AND/OR gates).
-/

namespace PEqualNP.MetaComplexity.OneNot

open PEqualNP.CircuitLowerBounds

/-- S-SPLIT. -/
theorem on1_split : ∀ gates : List PEqualNP.CircuitLowerBounds.Gate,
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) →
    (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not →
        (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∨
    ∃ (pre post : List PEqualNP.CircuitLowerBounds.Gate) (ins : List ℕ),
      gates = pre ++ ({ op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := ins } :
        PEqualNP.CircuitLowerBounds.Gate) :: post ∧
      (∀ g ∈ pre, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ g ∈ post, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) := by
  intro gates hops huniq
  by_cases hex : ∃ g ∈ gates, g.op = GateOp.not
  · right
    obtain ⟨g, hg, hop⟩ := hex
    obtain ⟨s, t, rfl⟩ := List.append_of_mem hg
    -- the NOT gate sits at index `s.length`
    have hslot : ((s ++ g :: t).get ⟨s.length, by simp⟩).op = GateOp.not := by
      simp [hop]
    have nf : ∀ g' ∈ s ++ g :: t, g'.op ≠ GateOp.not → (g'.op = GateOp.and ∨
        g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 := by
      intro g' hg' hne
      obtain ⟨h1 | h1 | h1, h2⟩ := hops g' hg'
      · exact ⟨Or.inl h1, h2⟩
      · exact ⟨Or.inr h1, h2⟩
      · exact absurd h1 hne
    refine ⟨s, t, g.inputs, ?_, ?_, ?_⟩
    · cases g with
      | mk op ins => simp only at hop; subst hop; rfl
    · intro g' hg'
      apply nf g' (by simp [hg'])
      intro hn
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg'
      have := huniq ⟨i, by simp; omega⟩ ⟨s.length, by simp⟩
        (by simp [List.getElem_append_left hi, hn]) hslot
      simp only [Fin.mk.injEq] at this; omega
    · intro g' hg'
      apply nf g' (by simp [hg'])
      intro hn
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg'
      have := huniq ⟨s.length + 1 + i, by simp; omega⟩ ⟨s.length, by simp⟩
        (by
          simp only [List.get_eq_getElem]
          rw [List.getElem_append_right (by omega)]
          simp only [show s.length + 1 + i - s.length = i + 1 by omega,
            List.getElem_cons_succ]
          exact hn) hslot
      simp only [Fin.mk.injEq] at this; omega
  · left
    intro g hg
    obtain ⟨h1 | h1 | h1, h2⟩ := hops g hg
    · exact ⟨Or.inl h1, h2⟩
    · exact ⟨Or.inr h1, h2⟩
    · exact absurd ⟨g, hg, h1⟩ hex

end PEqualNP.MetaComplexity.OneNot
