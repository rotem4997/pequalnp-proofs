import PEqualNP.MetaComplexity.Helpers.RigidAnd

/-- For a non-constant `g` on `k` inputs, the function `(x AND y) OR g` on two fresh inputs
`x, y` placed first has a circuit with at most `s + 2` gates exactly when `g` has one with at
most `s`: a rigid AND term costs exactly two gates. -/
theorem PEqualNP.MetaComplexity.L153 : ∀ (k s : ℕ) (g : (Fin k → Bool) → Bool), (∃ y y' : Fin k → Bool, g y ≠ g y') → (PEqualNP.MetaComplexity.HasCircuitSize (2 + k) (fun x : Fin (2 + k) → Bool => (x (Fin.castAdd k 0) && x (Fin.castAdd k 1)) || g (fun j : Fin k => x (Fin.natAdd 2 j))) (s + 2) ↔ PEqualNP.MetaComplexity.HasCircuitSize k g s) :=
  fun k s g hnc => PEqualNP.MetaComplexity.Helpers.RigidAnd.rigid_and k s g hnc
