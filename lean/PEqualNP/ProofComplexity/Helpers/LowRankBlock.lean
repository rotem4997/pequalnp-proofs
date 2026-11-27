import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Helpers: low rank block products (Lemma 7.6 of arXiv:2609.23015)

For affine polynomials `g 1, ..., g s` over `ZMod 2` whose span has dimension
`r ≤ h (k + 1)`, there are coefficient polynomials `c u i` of degree at most `k`
such that each `g i * ∏ u, (1 + ∑ i', c u i' * g i')` has degree at most
`h (k + 1) + 1` and vanishes on the Boolean cube.

Proof: take a basis `F` of the span, split it into `h` blocks of size `k + 1`, and
use the telescoping identity `∏ a < n, (1 + G a) = 1 + ∑ a < n, G a * ∏ b < a, (1 + G b)`.
-/

namespace PEqualNP.ProofComplexity.Helpers.LowRankBlock

open MvPolynomial

/-- Telescoping over any commutative ring. -/
theorem prod_one_add_telescope {R : Type*} [CommRing R] (G : ℕ → R) (n : ℕ) :
    ∏ a ∈ Finset.range n, (1 + G a) =
      1 + ∑ a ∈ Finset.range n, G a * ∏ b ∈ Finset.range a, (1 + G b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ, ih]
    ring

theorem totalDegree_prod_one_add_le {σ : Type} (G : ℕ → MvPolynomial σ (ZMod 2))
    (hG : ∀ a, (G a).totalDegree ≤ 1) (n : ℕ) :
    (∏ a ∈ Finset.range n, (1 + G a)).totalDegree ≤ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ]
    refine (totalDegree_mul _ _).trans ?_
    have h1 : (1 + G n).totalDegree ≤ 1 := by
      refine (totalDegree_add _ _).trans ?_
      simp [hG n]
    omega

theorem zmod_two_eq_one_of_ne_zero {y : ZMod 2} (hy : y ≠ 0) : y = 1 := by
  revert y
  decide

theorem zmod_two_one_add_one : (1 : ZMod 2) + 1 = 0 := by
  decide

theorem low_rank : ∀ (σ : Type) (s h k : ℕ) (g : Fin s → MvPolynomial σ (ZMod 2)), (∀ i, (g i).totalDegree ≤ 1) → 1 ≤ h → 1 ≤ k → Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range g)) ≤ h * (k + 1) → ∃ c : Fin h → Fin s → MvPolynomial σ (ZMod 2), (∀ u i, (c u i).totalDegree ≤ k) ∧ ∀ i : Fin s, (g i * ∏ u : Fin h, (1 + ∑ i' : Fin s, c u i' * g i')).totalDegree ≤ h * (k + 1) + 1 ∧ ∀ x : σ → ZMod 2, MvPolynomial.eval x (g i * ∏ u : Fin h, (1 + ∑ i' : Fin s, c u i' * g i')) = 0 := by
  intro σ s h k g hg _ _ hr
  set V := Submodule.span (ZMod 2) (Set.range g) with hV
  have : Module.Finite (ZMod 2) V := Module.Finite.span_of_finite (ZMod 2) (Set.finite_range g)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set r := Module.finrank (ZMod 2) V with hrdef
  let b : Module.Basis (Fin r) (ZMod 2) V := Module.finBasis (ZMod 2) V
  -- degree bound on the span
  have hVdeg : V ≤ restrictTotalDegree σ (ZMod 2) 1 := by
    rw [hV, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (mem_restrictTotalDegree _ _ _).2 (hg i)
  -- block entries
  let G : ℕ → ℕ → MvPolynomial σ (ZMod 2) := fun u a =>
    if hl : u * (k + 1) + a < r then (b ⟨_, hl⟩ : MvPolynomial σ (ZMod 2)) else 0
  have hGV : ∀ u a, G u a ∈ V := by
    intro u a
    simp only [G]
    split_ifs
    · exact (b _).2
    · exact V.zero_mem
  have hGdeg : ∀ u a, (G u a).totalDegree ≤ 1 := fun u a =>
    (mem_restrictTotalDegree _ _ _).1 (hVdeg (hGV u a))
  have hμ : ∀ u a, ∃ μ : Fin s → ZMod 2, ∑ i, μ i • g i = G u a := fun u a =>
    (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).1 (hGV u a)
  choose μ hμ using hμ
  let P : ℕ → ℕ → MvPolynomial σ (ZMod 2) := fun u n =>
    ∏ a ∈ Finset.range n, (1 + G u a)
  refine ⟨fun u i => ∑ a ∈ Finset.range (k + 1), μ u a i • P u a, ?_, ?_⟩
  · intro u i
    refine (totalDegree_finsetSum _ _).trans ?_
    refine Finset.sup_le fun a ha => ?_
    refine (totalDegree_smul_le _ _).trans ?_
    have : (P u a).totalDegree ≤ a := totalDegree_prod_one_add_le (G u) (hGdeg u) a
    have := Finset.mem_range.1 ha
    omega
  have hfac : ∀ u : Fin h,
      1 + ∑ i' : Fin s, (∑ a ∈ Finset.range (k + 1), μ u a i' • P u a) * g i' = P u (k + 1) := by
    intro u
    rw [show P u (k + 1) = _ from prod_one_add_telescope (G u) (k + 1)]
    congr 1
    simp_rw [Finset.sum_mul, smul_mul_assoc]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hμ u a, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, mul_comm]
  simp_rw [hfac]
  intro i
  refine ⟨?_, ?_⟩
  · refine (totalDegree_mul _ _).trans ?_
    have h1 : (∏ u : Fin h, P u (k + 1)).totalDegree ≤ h * (k + 1) := by
      refine (totalDegree_finsetProd _ _).trans ?_
      refine (Finset.sum_le_sum fun (u : Fin h) _ =>
        totalDegree_prod_one_add_le (G u) (hGdeg u) (k + 1)).trans ?_
      simp
    have := hg i
    omega
  · intro x
    rw [map_mul, map_prod]
    by_cases hall : ∀ (u : Fin h) a, a < k + 1 → eval x (G u a) = 0
    · -- every basis vector vanishes at x, so g i does
      have hF : ∀ j : Fin r, eval x (b j : MvPolynomial σ (ZMod 2)) = 0 := by
        intro j
        have hj : (j : ℕ) / (k + 1) < h := by
          rw [Nat.div_lt_iff_lt_mul (by omega)]
          exact lt_of_lt_of_le j.2 hr
        have ha : (j : ℕ) % (k + 1) < k + 1 := Nat.mod_lt _ (by omega)
        have := hall ⟨_, hj⟩ _ ha
        have hidx : (j : ℕ) / (k + 1) * (k + 1) + (j : ℕ) % (k + 1) = j := by
          rw [mul_comm]; exact Nat.div_add_mod _ _
        simp only [G] at this
        rw [dite_eq_left (by rw [hidx]; exact j.2)] at this
        convert this using 4
        exact Fin.ext hidx.symm
      have hgi : g i ∈ V := Submodule.subset_span ⟨i, rfl⟩
      have hsum := b.sum_repr ⟨g i, hgi⟩
      have hsum' : g i = ∑ j, (b.repr ⟨g i, hgi⟩ j) • (b j : MvPolynomial σ (ZMod 2)) := by
        have := congrArg Subtype.val hsum
        rw [Submodule.coe_sum] at this
        simpa using this.symm
      rw [hsum', map_sum]
      simp [hF]
    · push Not at hall
      obtain ⟨u, a, ha, hne⟩ := hall
      have h1 : eval x (G u a) = 1 := by
        exact zmod_two_eq_one_of_ne_zero hne
      apply mul_eq_zero_of_right
      refine Finset.prod_eq_zero (Finset.mem_univ u) ?_
      simp only [P]
      rw [map_prod]
      refine Finset.prod_eq_zero (Finset.mem_range.2 ha) ?_
      rw [map_add, map_one, h1]
      exact zmod_two_one_add_one

end PEqualNP.ProofComplexity.Helpers.LowRankBlock
