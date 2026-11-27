import PEqualNP.Defs

/-- `SIZE` and `HasCircuitSize` agree: a language is in `SIZE s` exactly when, at every length
`n`, its slice as a Boolean function has a circuit with at most `s n` gates. -/
theorem PEqualNP.MetaComplexity.L019 : ∀ (s : ℕ → ℕ) (L : Language Bool),
    L ∈ PEqualNP.CircuitLowerBounds.SIZE s ↔
    ∀ n : ℕ, ∃ f : (Fin n → Bool) → Bool, (∀ x : Fin n → Bool, f x = true ↔ List.ofFn x ∈ L) ∧
      PEqualNP.MetaComplexity.HasCircuitSize n f (s n) := by
  intro s L
  constructor
  · intro h n
    obtain ⟨C, hg, hs, hd⟩ := h n
    exact ⟨fun x => C.eval (List.ofFn x), fun x => hd (List.ofFn x) (by simp),
      C, hg, hs, fun _ => rfl⟩
  · intro h n
    obtain ⟨f, hf, C, hg, hs, hev⟩ := h n
    refine ⟨C, hg, hs, ?_⟩
    intro x hx
    subst hx
    have e : List.ofFn (fun i : Fin x.length => x[i]) = x := List.ofFn_getElem
    have := hf (fun i : Fin x.length => x[i])
    rw [← hev, e] at this
    exact this
