import PEqualNP.Defs

/-- A machine has at most one output on each input. -/
theorem PEqualNP.Library.L005 : ∀ (tm : Turing.FinTM2) (l : List (tm.Γ tm.k₀))
    (o₁ o₂ : List (tm.Γ tm.k₁)), Nonempty (Turing.TM2Outputs tm l (some o₁)) →
    Nonempty (Turing.TM2Outputs tm l (some o₂)) → o₁ = o₂ := by
  rintro tm l o₁ o₂ ⟨h₁⟩ ⟨h₂⟩
  -- a halted configuration has no successor, so nothing is reached after it
  have key : ∀ (o o' : List (tm.Γ tm.k₁)) (n m : ℕ), n ≤ m →
      (flip bind tm.step)^[n] (some (Turing.initList tm l)) = some (Turing.haltList tm o) →
      (flip bind tm.step)^[m] (some (Turing.initList tm l)) = some (Turing.haltList tm o') →
      o = o' := by
    intro o o' n m hnm hn hm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [Nat.add_comm, Function.iterate_add_apply, hn] at hm
    cases d with
    | zero =>
      have h := congrArg (fun c : tm.Cfg => c.stk tm.k₁) (Option.some.inj hm)
      simpa [Turing.haltList] using h
    | succ d =>
      exfalso
      rw [Function.iterate_succ_apply] at hm
      have hnone : flip bind tm.step (some (Turing.haltList tm o)) = none := rfl
      rw [hnone] at hm
      have : ∀ k : ℕ, (flip bind tm.step)^[k] none = none := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih => rw [Function.iterate_succ_apply]; exact ih
      rw [this] at hm
      cases hm
  have e₁ := h₁.evals_in_steps
  have e₂ := h₂.evals_in_steps
  rcases Nat.le_total h₁.steps h₂.steps with h | h
  · exact key _ _ _ _ h e₁ e₂
  · exact (key _ _ _ _ h e₂ e₁).symm
