import PEqualNP.MetaComplexity.Helpers.Hardwire

/-- Hardwiring inputs: fixing the last `k` inputs of a function on `n + k` inputs to constants
costs at most one more gate. -/
theorem PEqualNP.MetaComplexity.L018 : ∀ (n k : ℕ) (f : (Fin (n + k) → Bool) → Bool)
    (c : Fin k → Bool) (s : ℕ), PEqualNP.MetaComplexity.HasCircuitSize (n + k) f s →
    PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => f (Fin.append y c)) (s + 1) :=
  PEqualNP.MetaComplexity.Helpers.hardwire
