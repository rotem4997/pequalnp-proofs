import PEqualNP.Defs
import PEqualNP.Gct.Helpers.DetHessian

/-! Hessian rank at zeros of a polynomial with a determinantal expression. Helper for
L-gct-014. -/

namespace PEqualNP.Gct.Helpers

open Finset MvPolynomial

theorem eq_single_of_degree_le_one {τ : Type} (s : τ →₀ ℕ) (a : τ)
    (hs : (s.sum fun _ e => e) ≤ 1) (ha : s a ≠ 0) : s = Finsupp.single a 1 := by
  classical
  have hle : ∀ x, s x ≤ s.sum fun _ e => e := fun x => by
    by_cases hx : x ∈ s.support
    · exact Finset.single_le_sum (f := fun x => s x) (fun _ _ => Nat.zero_le _) hx
    · rw [Finsupp.notMem_support_iff.mp hx]; exact Nat.zero_le _
  ext x
  by_cases hx : x = a
  · subst hx; have := hle x; simp; omega
  · rw [Finsupp.single_apply, if_neg (Ne.symm hx)]
    by_contra hne
    have h2 : s a + s x ≤ s.sum fun _ e => e := by
      have hsub : ({a, x} : Finset τ) ⊆ s.support := by
        intro y hy
        simp only [mem_insert, mem_singleton] at hy
        rcases hy with rfl | rfl <;> simpa
      have := Finset.sum_le_sum_of_subset (f := fun y => s y) hsub
      rw [sum_pair (Ne.symm hx)] at this
      exact this
    omega

/-- A polynomial of total degree at most one has constant partial derivatives. -/
theorem pderiv_of_totalDegree_le_one {τ : Type} (q : MvPolynomial τ ℂ) (hq : q.totalDegree ≤ 1)
    (a : τ) : pderiv a q = C (q.coeff (Finsupp.single a 1)) := by
  classical
  conv_lhs => rw [q.as_sum]
  rw [map_sum]
  simp only [pderiv_monomial]
  by_cases hmem : Finsupp.single a 1 ∈ q.support
  · rw [sum_eq_single (Finsupp.single a 1)]
    · simp
    · intro s hs hne
      have : s a = 0 := by
        by_contra h
        exact hne (eq_single_of_degree_le_one s a ((le_totalDegree hs).trans hq) h)
      simp [this]
    · intro h; exact absurd hmem h
  · rw [sum_eq_zero, Finsupp.notMem_support_iff.mp (by simpa using hmem), map_zero]
    intro s hs
    have : s a = 0 := by
      by_contra h
      exact hmem (eq_single_of_degree_le_one s a ((le_totalDegree hs).trans hq) h ▸ hs)
    simp [this]


/-- At a zero of a polynomial with a determinantal expression of size `n`, its Hessian has rank
at most `2n`. -/
theorem rank_hess_detExpr {k n : ℕ} (p : MvPolynomial (Fin k) ℂ) (y : Fin k → ℂ)
    (hp : PEqualNP.Gct.HasDetExpression p n) (h0 : eval y p = 0) :
    (hess p y).rank ≤ 2 * n := by
  obtain ⟨A, hA, rfl⟩ := hp
  let φ : Fin n × Fin n → MvPolynomial (Fin k) ℂ := fun q => A q.1 q.2
  have hbind : bind₁ φ (PEqualNP.Gct.detPoly ℂ n) = A.det := by
    simp only [PEqualNP.Gct.detPoly]
    rw [AlgHom.map_det]
    congr 1
    refine Matrix.ext fun i j => ?_
    simp [φ]
  have hc : ∀ q a, pderiv a (φ q) = C ((A q.1 q.2).coeff (Finsupp.single a 1)) :=
    fun q a => pderiv_of_totalDegree_le_one _ (hA q.1 q.2) a
  have hev : eval (fun q => eval y (φ q)) (PEqualNP.Gct.detPoly ℂ n) = 0 := by
    have : eval y (bind₁ φ (PEqualNP.Gct.detPoly ℂ n)) =
        eval (fun q => eval y (φ q)) (PEqualNP.Gct.detPoly ℂ n) := by
      show eval₂Hom (RingHom.id ℂ) y _ = _
      rw [eval₂Hom_bind₁]
      rfl
    rw [← this, hbind, h0]
  rw [← hbind]
  exact (rank_hess_bind₁_le φ _ hc _ y).trans (rank_hess_det_singular _ hev)

end PEqualNP.Gct.Helpers
