import PEqualNP.Defs
import PEqualNP.ProofComplexity.Helpers.MomentExt

namespace PEqualNP.ProofComplexity

/-- L-pcx-029: moment extension holds at level `k` with at least `2 * k + 1` holes. -/
theorem L029 : ∀ m N k : ℕ, 2 * (k + 1) ≤ N + 1 → PEqualNP.ProofComplexity.MomentExt m N k := by
  intro m N k h z hz
  have toM : ∀ T : Finset (Fin m × Fin N), IsPartialMatching T → Helpers.MomentExt.IsMatching T :=
    fun T hT p hp q hq =>
      ⟨fun e => hT p hp q hq (Or.inl e), fun e => hT p hp q hq (Or.inr e)⟩
  have ofM : ∀ T : Finset (Fin m × Fin N), Helpers.MomentExt.IsMatching T → IsPartialMatching T :=
    fun T hT a ha b hb e => e.elim (hT a ha b hb).1 (hT a ha b hb).2
  have hz' : Helpers.MomentExt.Consistent k z :=
    fun T hT hc i hi => hz T (ofM T hT) hc i hi
  obtain ⟨z', hz'c, hag⟩ := Helpers.MomentExt.consistent_extend_fin m N k (by omega) z hz'
  exact ⟨z', fun T hT hc i hi => hz'c T (toM T hT) hc i hi, fun T _ hc => hag T hc⟩

end PEqualNP.ProofComplexity
