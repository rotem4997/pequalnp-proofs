import PEqualNP.Library.Helpers.OracleCopy

/-!
# L-lib-067: every oracle is in P relative to itself

The oracle machine `Helpers.OracleCopy.ocM` copies its input onto the query stack, asks the
oracle once and writes the answer, in `n + 3` steps on an input of length `n`.
-/

namespace PEqualNP.Library

open Classical in
theorem L067 : ∀ A : Language Bool, A ∈ PEqualNP.Library.OracleP A := by
  intro A
  refine ⟨Polynomial.X + 3, fun x => decide (x ∈ A), Helpers.OracleCopy.ocM,
    Equiv.refl Bool, Equiv.refl Bool, fun x => by simp only [decide_eq_true_eq]; exact Iff.rfl,
    fun x => ?_⟩
  obtain ⟨r⟩ := Helpers.OracleCopy.oc_run A x
  exact ⟨⟨r.toEvalsTo, by
    have := r.steps_le_m
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_ofNat]
    exact this⟩⟩

end PEqualNP.Library
