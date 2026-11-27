import PEqualNP.Search.Helpers.Hierarchy.WallFunctional

/-!
# The sum-of-squares wall for parity systems, step P5 and the wall

A parity system with no Gaussian refutation of width `d` has a pseudo-expectation of degree
`2 * D` for every `D` with `2 * D ≤ d` (`sosWallDual_of`), hence no sum-of-squares refutation
of that degree (`sosWall_of`). Both are proved from one hypothesis, `Wall.KernelPSD`: a real
kernel with entries in `{0, 1, -1}`, symmetric, with unit diagonal and multiplicative along
its nonzero entries is positive semidefinite. That statement mentions no polynomial; it is
proved elsewhere and is an explicit hypothesis here.

Known mathematics (Grigoriev 2001; Schoenebeck 2008). Nothing here is a result of the fleet
until the checker accepts it.
-/

namespace PEqualNP.Search.Helpers.HierarchyDraft

namespace Wall

open MvPolynomial

/-- Positivity of sign kernels that are multiplicative along their nonzero entries (a direct
sum of rank one blocks). An explicit hypothesis of this file. -/
def KernelPSD : Prop :=
  ∀ (ι : Type) [Fintype ι] (K : ι → ι → ℝ) (c : ι → ℝ),
    (∀ i j, K i j = 0 ∨ K i j = 1 ∨ K i j = -1) → (∀ i j, K i j = K j i) → (∀ i, K i i = 1) →
    (∀ i j k, K i j ≠ 0 → K j k ≠ 0 → K i k = K i j * K j k) →
    0 ≤ ∑ i, ∑ j, c i * c j * K i j

variable {V : Type} [DecidableEq V] {F : Set (PEqualNP.ProofComplexity.LinEq V)} {d : ℕ}

/-- Positivity: the functional is nonnegative on the square of a polynomial of total degree at
most `D`, when `2 * D ≤ d`. -/
theorem pE_mul_self_nonneg (hkernel : KernelPSD) (hF : ¬ XorRefutable F d) {D : ℕ}
    (hD : 2 * D ≤ d) (r : MvPolynomial V ℝ) (hr : r.totalDegree ≤ D) :
    0 ≤ pE F d (r * r) := by
  have hcard : ∀ a ∈ r.support, (oddSupp a).card ≤ D := fun a ha =>
    (card_oddSupp_le a).trans ((le_totalDegree ha).trans hr)
  have hw : ∀ a ∈ r.support, ∀ b ∈ r.support,
      (symmDiff (oddSupp a) (oddSupp b)).card ≤ d := by
    intro a ha b hb
    have h1 := card_symmDiff_le (oddSupp a) (oddSupp b)
    have h2 := hcard a ha
    have h3 := hcard b hb
    omega
  have h := hkernel {a // a ∈ r.support}
    (fun i j => val F d (symmDiff (oddSupp i.1) (oddSupp j.1))) (fun i => r.coeff i.1)
    (fun i j => val_trichotomy F d _)
    (fun i j => congrArg (val F d) (symmDiff_comm _ _))
    (fun i => by
      have e : symmDiff (oddSupp i.1) (oddSupp i.1) = (∅ : Finset V) := symmDiff_self _
      simp only [e]
      exact val_empty hF)
    (fun i j k hij hjk => val_symmDiff_mul hF hij hjk (hw i.1 i.2 k.1 k.2))
  rw [pE_mul_mul, ← Finset.sum_coe_sort r.support]
  refine le_of_le_of_eq h (Finset.sum_congr rfl (fun i _ => ?_))
  exact Finset.sum_coe_sort r.support
    (fun b => r.coeff i.1 * r.coeff b * val F d (symmDiff (oddSupp i.1) (oddSupp b)))

/-- The functional of the wall is a pseudo-expectation. -/
theorem isPseudoExpectation_pE (hkernel : KernelPSD) (hF : ¬ XorRefutable F d) {D : ℕ}
    (hD : 2 * D ≤ d) : IsPseudoExpectation (xorSystem F) D (pE F d) := by
  refine ⟨pE_one hF, ?_, fun r hr => pE_mul_self_nonneg hkernel hF hD r hr⟩
  rintro p (⟨v, rfl⟩ | ⟨e, he, rfl⟩) q hq
  · exact pE_mul_sign v q
  · exact pE_mul_xorPoly hF hD he q hq

end Wall

/-- The dual form of the wall, from positivity of sign kernels: a parity system with no
Gaussian refutation of width `d` has a pseudo-expectation of degree `2 * D` when `2 * D ≤ d`. -/
theorem sosWallDual_of (hkernel : Wall.KernelPSD) : SoSWallDual := by
  intro V _ F d D hD hF
  exact ⟨Wall.pE F d, Wall.isPseudoExpectation_pE hkernel hF hD⟩

/-- The wall, from positivity of sign kernels: a parity system with no Gaussian refutation of
width `d` has no sum-of-squares refutation of degree `2 * D` when `2 * D ≤ d`. -/
theorem sosWall_of (hkernel : Wall.KernelPSD) : SoSWall := by
  intro V _ F d D hD hF
  exact not_sosRefutable_of_pseudoExpectation (Wall.isPseudoExpectation_pE hkernel hF hD)

end PEqualNP.Search.Helpers.HierarchyDraft
