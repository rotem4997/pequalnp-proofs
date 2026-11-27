import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.Threshold

/-!
# L-meta-12318: the representing threshold, rebuilt, conditional on the sharp conversion

The proof is `Threshold.threshold`.
-/

theorem PEqualNP.MetaComplexity.L12318 : (∀ (k l s : ℕ) (A : Fin (2 ^ k) → Fin (2 ^ l) → Bool), PEqualNP.MetaComplexity.HasCircuitSize (k + l) (PEqualNP.Represents.adjFun A) s → PEqualNP.Represents.RepSizeAtMost A (2 * s + 2 * 2 ^ k + k * 2 ^ ((k + 1) / 2) + 2 * 2 ^ l + l * 2 ^ ((l + 1) / 2))) → ∀ (A : (k : ℕ) → Fin (2 ^ k) → Fin (2 ^ k) → Bool) (d K : ℕ), 0 < d → (∀ k, K ≤ k → ¬ PEqualNP.Represents.RepSizeAtMost (A k) (4 * 2 ^ k + 2 ^ k / d)) → {x : List Bool | Even x.length ∧ PEqualNP.Represents.adjFun (k := x.length / 2) (l := x.length / 2) (A (x.length / 2)) (fun i => x.getD i false) = true} ∈ PEqualNP.Library.NP → ¬ PEqualNP.Library.NP ⊆ PEqualNP.CircuitLowerBounds.PPoly :=
  fun hB => PEqualNP.MetaComplexity.Threshold.threshold hB
