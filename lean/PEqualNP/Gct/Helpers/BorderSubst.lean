import Mathlib
import PEqualNP.Defs
import PEqualNP.Gct.L003

/-! Border determinantal expressions are preserved by affine substitutions. Helper for
L-gct-023. -/

namespace PEqualNP.Gct.Helpers

open MvPolynomial

/-- Substituting polynomials of total degree at most one does not raise the total degree. -/
theorem totalDegree_bind₁_le_of_affine {σ τ R : Type} [CommRing R] (g : σ → MvPolynomial τ R)
    (hg : ∀ i, (g i).totalDegree ≤ 1) (a : MvPolynomial σ R) :
    (bind₁ g a).totalDegree ≤ a.totalDegree := by
  conv_lhs => rw [a.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hs)
  rw [Finsupp.sum]
  refine Finset.sum_le_sum fun i _ => ?_
  refine (totalDegree_pow _ _).trans ?_
  exact (Nat.mul_le_mul_left _ (hg i)).trans (by simp)

/-- A determinantal expression is carried along an affine substitution. -/
theorem hasDetExpression_bind₁ {σ τ R : Type} [CommRing R] (g : σ → MvPolynomial τ R)
    (hg : ∀ i, (g i).totalDegree ≤ 1) {q : MvPolynomial σ R} {n : ℕ}
    (h : PEqualNP.Gct.HasDetExpression q n) :
    PEqualNP.Gct.HasDetExpression (bind₁ g q) n := by
  obtain ⟨A, hA, hdet⟩ := h
  refine ⟨A.map (bind₁ g), fun i j => ?_, ?_⟩
  · exact (totalDegree_bind₁_le_of_affine g hg _).trans (hA i j)
  · rw [← hdet, AlgHom.map_det]
    rfl

/-- The coefficients of a substituted polynomial are a fixed finite linear combination of the
coefficients of the polynomial, once its support lies in a fixed finite set. -/
theorem coeff_bind₁_eq_sum {σ τ : Type} (g : σ → MvPolynomial τ ℂ) (S : Finset (σ →₀ ℕ))
    (q : MvPolynomial σ ℂ) (hS : ∀ s, s ∉ S → q.coeff s = 0) (t : τ →₀ ℕ) :
    (bind₁ g q).coeff t = ∑ s ∈ S, q.coeff s * (bind₁ g (monomial s 1)).coeff t := by
  classical
  have hsub : q.support ⊆ S := fun s hs => by
    by_contra h
    exact (mem_support_iff.mp hs) (hS s h)
  conv_lhs => rw [q.as_sum]
  rw [map_sum, coeff_sum]
  refine (Finset.sum_subset hsub ?_).trans ?_
  · intro s _ hs
    rw [notMem_support_iff.mp hs]
    simp
  · refine Finset.sum_congr rfl fun s _ => ?_
    have hm : monomial s (q.coeff s) = C (q.coeff s) * monomial s 1 := by
      rw [C_mul_monomial, mul_one]
    rw [hm, map_mul, bind₁_C_right, coeff_C_mul]

/-- A border determinantal expression is carried along an affine substitution, when the
polynomial has finitely many variables. -/
theorem hasBorderDetExpression_bind₁ (σ τ : Type) [Finite σ] (p : MvPolynomial σ ℂ)
    (g : σ → MvPolynomial τ ℂ) (n : ℕ) (hg : ∀ i, (g i).totalDegree ≤ 1)
    (h : PEqualNP.Gct.HasBorderDetExpression p n) :
    PEqualNP.Gct.HasBorderDetExpression (bind₁ g p) n := by
  classical
  obtain ⟨q, hq, hlim⟩ := h
  have hfin : {s : σ →₀ ℕ | s ≤ Finsupp.equivFunOnFinite.symm (fun _ => n)}.Finite :=
    Set.finite_Iic _
  have hqS : ∀ k s, s ∉ hfin.toFinset → (q k).coeff s = 0 := by
    intro k s hs
    by_contra hne
    apply hs
    have hmem : s ∈ (q k).support := mem_support_iff.mpr hne
    have hdeg := (le_totalDegree hmem).trans (PEqualNP.Gct.L003 σ ℂ (q k) n (hq k))
    rw [Set.Finite.mem_toFinset]
    intro i
    by_cases hi : i ∈ s.support
    · exact (Finset.single_le_sum (f := fun j => s j) (fun _ _ => Nat.zero_le _) hi).trans hdeg
    · simp [Finsupp.notMem_support_iff.mp hi]
  have hpS : ∀ s, s ∉ hfin.toFinset → p.coeff s = 0 := fun s hs =>
    tendsto_nhds_unique (hlim s) (by simp [hqS _ s hs])
  refine ⟨fun k => bind₁ g (q k), fun k => hasDetExpression_bind₁ g hg (hq k), fun t => ?_⟩
  rw [coeff_bind₁_eq_sum g _ p hpS]
  simp only [coeff_bind₁_eq_sum g _ _ (hqS _)]
  exact tendsto_finsetSum _ fun s _ => (hlim s).mul_const _

end PEqualNP.Gct.Helpers
