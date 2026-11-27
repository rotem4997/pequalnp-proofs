import PEqualNP.Library.L003
import PEqualNP.Library.L073

/-- P is contained in P/poly: a language decided in time `p n` has circuits of size
`c * (p n + n + 1) ^ 3` (L-lib-073), and that bound is itself a polynomial in `n`. -/
theorem PEqualNP.CircuitLowerBounds.L006 :
    PEqualNP.Library.P ⊆ PEqualNP.CircuitLowerBounds.PPoly := by
  intro L hL
  obtain ⟨p, hp⟩ := (PEqualNP.Library.L003 L).mp hL
  obtain ⟨c, hc⟩ := PEqualNP.Library.L073 _ L hp
  refine ⟨Polynomial.C c * (p + Polynomial.X + 1) ^ 3, ?_⟩
  have e : (fun n : ℕ => Polynomial.eval n (Polynomial.C c * (p + Polynomial.X + 1) ^ 3)) =
      fun n : ℕ => c * (Polynomial.eval n p + n + 1) ^ 3 := by
    funext n
    simp
  rw [e]
  exact hc
