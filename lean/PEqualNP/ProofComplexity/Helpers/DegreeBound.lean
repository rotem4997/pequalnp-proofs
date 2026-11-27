import PEqualNP.Defs
import PEqualNP.ProofComplexity.Helpers.MomentReduction
import PEqualNP.ProofComplexity.Helpers.MomentExt

/-!
# Helpers: the polynomial calculus degree bound for functional pigeonhole over the
two-element field, assembled from the reduction to matching moments and the extension
theorem.
-/

namespace PEqualNP.ProofComplexity.Helpers

open PEqualNP.ProofComplexity

theorem momentExt_of_holes (m N k : ℕ) (h : 2 * (k + 1) ≤ N + 1) :
    PEqualNP.ProofComplexity.MomentExt m N k := by
  intro z hz
  have toM : ∀ T : Finset (Fin m × Fin N), IsPartialMatching T → MomentExt.IsMatching T :=
    fun T hT p hp q hq =>
      ⟨fun e => hT p hp q hq (Or.inl e), fun e => hT p hp q hq (Or.inr e)⟩
  have ofM : ∀ T : Finset (Fin m × Fin N), MomentExt.IsMatching T → IsPartialMatching T :=
    fun T hT a ha b hb e => e.elim (hT a ha b hb).1 (hT a ha b hb).2
  have hz' : MomentExt.Consistent k z :=
    fun T hT hc i hi => hz T (ofM T hT) hc i hi
  obtain ⟨z', hz'c, hag⟩ := MomentExt.consistent_extend_fin m N k (by omega) z hz'
  exact ⟨z', fun T hT hc i hi => hz'c T (toM T hT) hc i hi, fun T _ hc => hag T hc⟩

theorem funPHP_no_pc_refutation (m N B : ℕ) (hN : 1 ≤ N) (hB : 2 * B ≤ N + 1) :
    ¬ PCRefutable (funPHPSystem m N) B :=
  no_pc_refutation_of_momentExt m N B hN
    (fun k hk => momentExt_of_holes m N k (by omega))

end PEqualNP.ProofComplexity.Helpers
