import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.CommRing
import PEqualNP.Search.Helpers.Hierarchy.WallClosure

/-!
# The sum-of-squares wall for parity systems, steps P2 and P3: the functional

The functional `pE F d` on real polynomials: on a monomial with exponent vector `a` it is the
value (`Wall.val`) of the set `oddSupp a` of variables with odd exponent. It is defined on all
polynomials, with no truncation. Proved here: its value on a product, that it kills every
multiple of `X v * X v - 1` (in every degree), and that it kills `q * xorPoly e` for an
equation `e` of the system when the product has total degree at most `2 * D ≤ d`.

Known mathematics (Grigoriev 2001; Schoenebeck 2008). Nothing here is a result of the fleet
until the checker accepts it.
-/

namespace PEqualNP.Search.Helpers.HierarchyDraft.Wall

open MvPolynomial

variable {V : Type} [DecidableEq V]

/-! ## Odd supports of exponent vectors -/

/-- The set of variables with odd exponent. -/
def oddSupp (a : V →₀ ℕ) : Finset V := a.support.filter (fun v => Odd (a v))

theorem mem_oddSupp {a : V →₀ ℕ} {v : V} : v ∈ oddSupp a ↔ Odd (a v) := by
  simp only [oddSupp, Finset.mem_filter, Finsupp.mem_support_iff]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun h0 => ?_, h⟩
    rw [h0] at h
    exact absurd h (by decide)

theorem oddSupp_add (a b : V →₀ ℕ) : oddSupp (a + b) = symmDiff (oddSupp a) (oddSupp b) := by
  ext v
  simp only [mem_oddSupp, Finset.mem_symmDiff, Finsupp.add_apply, Nat.odd_add,
    ← Nat.not_odd_iff_even]
  tauto

theorem oddSupp_zero : oddSupp (0 : V →₀ ℕ) = ∅ := by
  ext v
  simp [mem_oddSupp]

theorem oddSupp_single_two (v : V) : oddSupp (Finsupp.single v 2) = ∅ := by
  ext w
  have h : ¬ Odd ((Finsupp.single v 2 : V →₀ ℕ) w) := by
    rw [Finsupp.single_apply]
    split_ifs <;> decide
  simp [mem_oddSupp, h]

theorem card_oddSupp_le (a : V →₀ ℕ) : (oddSupp a).card ≤ a.sum fun _ e => e := by
  calc (oddSupp a).card ≤ a.support.card := Finset.card_filter_le _ _
    _ = ∑ _v ∈ a.support, 1 := by simp
    _ ≤ ∑ v ∈ a.support, a v :=
        Finset.sum_le_sum (fun v hv => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv))
    _ = a.sum fun _ e => e := rfl

theorem card_symmDiff_le (A B : Finset V) : (symmDiff A B).card ≤ A.card + B.card := by
  have h : symmDiff A B ⊆ A ∪ B := by
    intro x hx
    rw [Finset.mem_symmDiff] at hx
    rw [Finset.mem_union]
    tauto
  exact (Finset.card_le_card h).trans (Finset.card_union_le A B)

/-- The exponent vector of the product of the variables of `T`. -/
noncomputable def chi (T : Finset V) : V →₀ ℕ := ∑ v ∈ T, Finsupp.single v 1

theorem chi_apply (T : Finset V) (w : V) : chi T w = if w ∈ T then 1 else 0 := by
  simp [chi, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem oddSupp_chi (T : Finset V) : oddSupp (chi T) = T := by
  ext w
  rw [mem_oddSupp, chi_apply]
  split_ifs with h <;> simp [h]

theorem chi_degree (T : Finset V) : ((chi T).sum fun _ e => e) = T.card := by
  have hs : (chi T).support ⊆ T := by
    intro v hv
    rw [Finsupp.mem_support_iff, chi_apply] at hv
    by_contra h
    exact hv (if_neg h)
  rw [Finsupp.sum_of_support_subset _ hs _ (fun _ _ => rfl)]
  simp [chi_apply]

theorem chi_ne_zero {T : Finset V} (hT : T.Nonempty) : chi T ≠ 0 := by
  obtain ⟨v, hv⟩ := hT
  intro h
  have h1 := chi_apply T v
  rw [h, if_pos hv] at h1
  simp at h1

theorem prod_X_eq (T : Finset V) :
    (∏ v ∈ T, (X v : MvPolynomial V ℝ)) = monomial (chi T) 1 :=
  (monomial_sum_one T (fun v => Finsupp.single v 1)).symm

/-! ## The functional -/

/-- The functional of the wall: on the monomial of exponent vector `a`, the value of the odd
support of `a`. -/
noncomputable def pE (F : Set (PEqualNP.ProofComplexity.LinEq V)) (d : ℕ) :
    MvPolynomial V ℝ →ₗ[ℝ] ℝ :=
  (basisMonomials V ℝ).constr ℝ (fun a => val F d (oddSupp a))

variable {F : Set (PEqualNP.ProofComplexity.LinEq V)} {d : ℕ}

theorem pE_monomial (a : V →₀ ℕ) (c : ℝ) :
    pE F d (monomial a c) = c * val F d (oddSupp a) := by
  have h : (monomial a c : MvPolynomial V ℝ) = c • (basisMonomials V ℝ) a := by
    simp only [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, pE, Module.Basis.constr_basis, smul_eq_mul]

theorem pE_one (hF : ¬ XorRefutable F d) : pE F d 1 = 1 := by
  have h : (1 : MvPolynomial V ℝ) = monomial 0 1 := rfl
  rw [h, pE_monomial, oddSupp_zero, val_empty hF, mul_one]

/-- The functional on a product, one monomial of the left factor at a time. -/
theorem pE_mul (q p : MvPolynomial V ℝ) :
    pE F d (q * p) = ∑ a ∈ q.support, q.coeff a * pE F d (monomial a 1 * p) := by
  conv_lhs => rw [q.as_sum]
  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have h : (monomial a (q.coeff a) : MvPolynomial V ℝ) * p = q.coeff a • (monomial a 1 * p) := by
    rw [← smul_mul_assoc, smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, smul_eq_mul]

/-- The functional on a product of two polynomials, as a double sum over monomials. -/
theorem pE_mul_mul (q p : MvPolynomial V ℝ) :
    pE F d (q * p) = ∑ a ∈ q.support, ∑ b ∈ p.support,
      q.coeff a * p.coeff b * val F d (symmDiff (oddSupp a) (oddSupp b)) := by
  rw [pE_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [mul_comm (monomial a 1) p, pE_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [monomial_mul_monomial, pE_monomial, oddSupp_add, symmDiff_comm]
  ring

/-! ## The linear constraints -/

/-- The functional kills every multiple of a sign axiom, in every degree. -/
theorem pE_mul_sign (v : V) (q : MvPolynomial V ℝ) :
    pE F d (q * (X v * X v - 1)) = 0 := by
  rw [pE_mul]
  refine Finset.sum_eq_zero (fun a _ => ?_)
  have h : (monomial a 1 : MvPolynomial V ℝ) * (X v * X v - 1)
      = monomial (a + Finsupp.single v 2) 1 - monomial a 1 := by
    rw [mul_sub, mul_one, ← pow_two, X_pow_eq_monomial, monomial_mul_monomial, mul_one]
  have h2 : symmDiff (oddSupp a) (∅ : Finset V) = oddSupp a := symmDiff_bot _
  rw [h, map_sub, pE_monomial, pE_monomial, oddSupp_add, oddSupp_single_two, h2]
  simp

theorem xorPoly_eq (T : Finset V) (b : Bool) :
    xorPoly (T, b) = monomial (chi T) 1 - monomial 0 (sgn b) := by
  rw [xorPoly, prod_X_eq, C_apply]
  rfl

theorem coeff_chi_xorPoly {T : Finset V} (hT : T.Nonempty) (b : Bool) :
    (xorPoly (T, b)).coeff (chi T) = 1 := by
  classical
  rw [xorPoly_eq, coeff_sub, coeff_monomial, coeff_monomial, if_pos rfl,
    if_neg (chi_ne_zero hT).symm, sub_zero]

theorem xorPoly_ne_zero {T : Finset V} (hT : T.Nonempty) (b : Bool) : xorPoly (T, b) ≠ 0 := by
  intro h
  have h1 := coeff_chi_xorPoly hT b
  rw [h] at h1
  simp at h1

theorem card_le_totalDegree_xorPoly {T : Finset V} (hT : T.Nonempty) (b : Bool) :
    T.card ≤ (xorPoly (T, b)).totalDegree := by
  have hmem : chi T ∈ (xorPoly (T, b)).support := by
    rw [mem_support_iff, coeff_chi_xorPoly hT b]
    exact one_ne_zero
  have h := le_totalDegree hmem
  rwa [chi_degree] at h

/-- The functional kills `q * xorPoly e` for an equation `e` of the system, when the product
has total degree at most `2 * D ≤ d`. -/
theorem pE_mul_xorPoly (hF : ¬ XorRefutable F d) {D : ℕ} (hD : 2 * D ≤ d)
    {e : PEqualNP.ProofComplexity.LinEq V} (he : e ∈ F) (q : MvPolynomial V ℝ)
    (hdeg : (q * xorPoly e).totalDegree ≤ 2 * D) : pE F d (q * xorPoly e) = 0 := by
  obtain ⟨T, b⟩ := e
  by_cases hq : q = 0
  · rw [hq, zero_mul, map_zero]
  by_cases hT : T = ∅
  · subst hT
    cases b with
    | false =>
      have h0 : xorPoly ((∅ : Finset V), false) = 0 := by simp [xorPoly]
      rw [h0, mul_zero, map_zero]
    | true => exact absurd (XorDerivable.ax he (by simp)) hF
  have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
  have hdeg' : q.totalDegree + T.card ≤ d := by
    have h1 := totalDegree_mul_of_isDomain hq (xorPoly_ne_zero hTne b)
    have h2 := card_le_totalDegree_xorPoly hTne b
    omega
  have hTd : XorDerivable F d (T, b) := XorDerivable.ax he (by simp only; omega)
  rw [pE_mul]
  refine Finset.sum_eq_zero (fun a ha => ?_)
  have ha1 := le_totalDegree ha
  have ha2 := card_oddSupp_le a
  have ha3 := card_symmDiff_le (oddSupp a) T
  have h : (monomial a 1 : MvPolynomial V ℝ) * xorPoly (T, b)
      = monomial (a + chi T) 1 - monomial a (sgn b) := by
    rw [xorPoly_eq, mul_sub, monomial_mul_monomial, monomial_mul_monomial, mul_one, one_mul, add_zero]
  rw [h, map_sub, pE_monomial, pE_monomial, oddSupp_add, oddSupp_chi,
    val_symmDiff hF hTd (by omega) (by omega)]
  simp

end PEqualNP.Search.Helpers.HierarchyDraft.Wall
