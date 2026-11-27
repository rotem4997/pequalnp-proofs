import PEqualNP.MetaComplexity.Helpers.Elim

/-- Gate elimination: if `f` on `n + 1` inputs depends on its last input and stays
non-constant when that input is fixed to `b`, a circuit of size `s + 1` for `f` gives a
circuit of size `s` for the restriction. -/
theorem PEqualNP.MetaComplexity.L014 : ∀ (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool)
    (s : ℕ),
    (∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x) →
    (∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b)) →
    PEqualNP.MetaComplexity.HasCircuitSize (n + 1) f (s + 1) →
    PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s :=
  PEqualNP.MetaComplexity.Helpers.gate_elim
