import PEqualNP.CircuitLowerBounds.Helpers.AndChain

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitLowerBounds.Helpers in
/-- Every unary language is in P/poly: at each length the circuit is either the AND of all
inputs or the constant `false`. -/
theorem PEqualNP.CircuitLowerBounds.L003 : ∀ L : Language Bool,
    (∀ x ∈ L, ∀ b ∈ x, b = true) → L ∈ PEqualNP.CircuitLowerBounds.PPoly := by
  intro L hL
  refine ⟨Polynomial.X + 1, fun n => ?_⟩
  by_cases h : List.replicate n true ∈ L
  · refine ⟨⟨andChain n n, n + n⟩, fun g hg => ?_, ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := andChain_gates n n g hg
      exact ⟨by rw [h1]; exact Or.inl rfl, h2⟩
    · simp [Circuit.size, andChain_length]
    · intro x hx
      subst hx
      rw [andChain_eval]
      constructor
      · intro hall
        have : x = List.replicate x.length true := by
          rw [List.eq_replicate_iff]
          exact ⟨rfl, fun b hb => by simpa using List.all_eq_true.mp hall b hb⟩
        rw [this]; exact h
      · intro hx
        exact List.all_eq_true.mpr fun b hb => by simpa using hL x hx b hb
  · refine ⟨⟨[⟨GateOp.or, []⟩], n⟩, fun g hg => ?_, ?_, ?_⟩
    · simp at hg; subst hg; exact ⟨Or.inr (Or.inl rfl), by simp⟩
    · simp [Circuit.size]
    · intro x hx
      subst hx
      have he : (Circuit.mk [⟨GateOp.or, []⟩] x.length).eval x = false := by
        simp [Circuit.eval, Circuit.wires, GateOp.eval]
      rw [he]
      constructor
      · intro hf; cases hf
      · intro hx
        exfalso; apply h
        have : x = List.replicate x.length true := by
          rw [List.eq_replicate_iff]
          exact ⟨rfl, hL x hx⟩
        rw [← this]; exact hx
