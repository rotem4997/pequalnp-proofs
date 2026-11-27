import Mathlib
import PEqualNP.Gct.Helpers.S2Height

namespace PEqualNP.Gct.Helpers.S3Plan

open MvPolynomial

/-- Row polynomial `1 + sum_k l_k(i,j) X_k`. -/
noncomputable def A3 {d q : ℕ} (l : Fin d → Fin 3 × Fin q → ℂ) (i : Fin 3) (j : Fin q) :
    MvPolynomial (Fin d) ℂ :=
  1 + ∑ k, C (l k (i, j)) * X k

/-- Column product. -/
noncomputable def g3 {d q : ℕ} (l : Fin d → Fin 3 × Fin q → ℂ) (j : Fin q) :
    MvPolynomial (Fin d) ℂ :=
  A3 l 0 j * A3 l 1 j * A3 l 2 j

/-- The target row L-gct-157. -/
def Target : Prop := ∀ (q : ℕ) (L : Submodule ℂ (Fin 3 × Fin q → ℂ)), 1 ≤ q → (∀ t ∈ L, (∀ i : Fin 3, ∑ j, t (i, j) = 0) ∧ (∑ j, ∑ l, if j = l then 0 else (t (0, j) * t (1, l) + t (0, j) * t (2, l) + t (1, j) * t (2, l))) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else t (0, j) * t (1, l) * t (2, m)) = 0) → Module.finrank ℂ L + 1 ≤ q

/-- S1: the literal hypotheses give `F(eps J + t) = q eps^3` on L. -/
def S1 : Prop := ∀ (q : ℕ) (L : Submodule ℂ (Fin 3 × Fin q → ℂ)),
  (∀ t ∈ L, (∀ i : Fin 3, ∑ j, t (i, j) = 0) ∧ (∑ j, ∑ l, if j = l then 0 else (t (0, j) * t (1, l) + t (0, j) * t (2, l) + t (1, j) * t (2, l))) = 0 ∧ (∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else t (0, j) * t (1, l) * t (2, m)) = 0) →
  ∀ t ∈ L, ∀ ε : ℂ, ∑ j, (ε + t (0, j)) * (ε + t (1, j)) * (ε + t (2, j)) = (q : ℂ) * ε ^ 3

/-- S2: the identity on points becomes an identity in every commutative C-algebra. -/
def S2 : Prop := ∀ (d q : ℕ) (l : Fin d → Fin 3 × Fin q → ℂ),
  (∀ (ε : ℂ) (u : Fin d → ℂ), ∑ j, (ε + ∑ k, u k * l k (0, j)) * (ε + ∑ k, u k * l k (1, j)) *
      (ε + ∑ k, u k * l k (2, j)) = (q : ℂ) * ε ^ 3) →
  ∀ (S : Type) [CommRing S] [Algebra ℂ S] (ε : S) (u : Fin d → S),
    ∑ j, (ε + ∑ k, algebraMap ℂ S (l k (0, j)) * u k) * (ε + ∑ k, algebraMap ℂ S (l k (1, j)) * u k) *
      (ε + ∑ k, algebraMap ℂ S (l k (2, j)) * u k) = (q : S) * ε ^ 3

/-- S3 (generic G-c): a family with constant terms 1 summing to the constant q. -/
def S3 : Prop := ∀ (d q : ℕ) (g : Fin q → MvPolynomial (Fin d) ℂ), 1 ≤ q →
  (∀ j, constantCoeff (g j) = 1) → ∑ j, g j = C (q : ℂ) →
  ∃ s : Finset (MvPolynomial (Fin d) ℂ),
    Ideal.span (s : Set (MvPolynomial (Fin d) ℂ)) = Ideal.span (Set.range fun j => g j - 1) ∧
    s.card + 1 ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range g))

/-- S4: at a point of the fibre in a field, the functional two-point identity. -/
def S4 : Prop := ∀ (d q : ℕ) (l : Fin d → Fin 3 × Fin q → ℂ) (K : Type) [Field K] [Algebra ℂ K]
  (π : MvPolynomial (Fin d) ℂ →ₐ[ℂ] K),
  (∀ (ε : ℂ) (u : Fin d → ℂ), ∑ j, (ε + ∑ k, u k * l k (0, j)) * (ε + ∑ k, u k * l k (1, j)) *
      (ε + ∑ k, u k * l k (2, j)) = (q : ℂ) * ε ^ 3) →
  (∀ j, π (g3 l j) = 1) →
  (∀ i j, π (A3 l i j) ≠ 0) ∧
  ∀ φ : K →ₗ[ℂ] ℂ, ∑ ij : Fin 3 × Fin q,
    algebraMap ℂ K (φ (π (A3 l ij.1 ij.2))) * (π (A3 l ij.1 ij.2))⁻¹ = algebraMap ℂ K (3 * q * φ 1)

/-- S5: a prime strictly below m0 makes some row entry nonconstant. -/
def S5 : Prop := ∀ (d q : ℕ) (l : Fin d → Fin 3 × Fin q → ℂ) (K : Type) [Field K] [Algebra ℂ K]
  (π : MvPolynomial (Fin d) ℂ →ₐ[ℂ] K) (P : Ideal (MvPolynomial (Fin d) ℂ)),
  LinearIndependent ℂ l → (∀ p, π p = 0 ↔ p ∈ P) → P ≤ PEqualNP.Gct.Helpers.S2Height.m0 ℂ d →
  (∃ k, X k ∉ P) → ∃ i j, π (A3 l i j) ∉ Set.range (algebraMap ℂ K)

/-- S6 (Lemma T, any number of rows, no second functional). -/
def S6 : Prop := ∀ (K : Type) [Field K] [Algebra ℂ K] (O : ValuationSubring K),
  (∀ r : ℂ, algebraMap ℂ K r ∈ O) → ∀ (ι : Type) [Fintype ι] (e : ι → K), (∀ i, e i ≠ 0) →
  (∃ i, e i ∉ O) → ∀ c : ℂ,
  ∃ φ : K →ₗ[ℂ] ℂ, ∑ i, algebraMap ℂ K (φ (e i)) * (e i)⁻¹ ≠ algebraMap ℂ K (c * φ 1)

/-- S7: a column of product one with a non-unit entry has an entry outside O. -/
def S7 : Prop := ∀ (K : Type) [Field K] (O : ValuationSubring K) (a b c : K),
  a * b * c = 1 → (a ∈ O.nonunits ∨ b ∈ O.nonunits ∨ c ∈ O.nonunits) → (a ∉ O ∨ b ∉ O ∨ c ∉ O)

/-- S8: m0 is minimal over the fibre ideal. -/
def S8 : Prop := ∀ (d q : ℕ) (l : Fin d → Fin 3 × Fin q → ℂ), LinearIndependent ℂ l →
  (∀ (ε : ℂ) (u : Fin d → ℂ), ∑ j, (ε + ∑ k, u k * l k (0, j)) * (ε + ∑ k, u k * l k (1, j)) *
      (ε + ∑ k, u k * l k (2, j)) = (q : ℂ) * ε ^ 3) →
  PEqualNP.Gct.Helpers.S2Height.m0 ℂ d ∈ (Ideal.span (Set.range fun j => g3 l j - 1)).minimalPrimes

/-- S9: the general-p lemma H_p, for the record (hypothesis F = q eps^p on V). -/
def HpRow : Prop := ∀ (p q : ℕ) (L : Submodule ℂ (Fin p × Fin q → ℂ)), 1 ≤ q →
  (∀ t ∈ L, ∀ ε : ℂ, ∑ j, ∏ i, (ε + t (i, j)) = (q : ℂ) * ε ^ p) →
  Module.finrank ℂ L + 1 ≤ q

/-- The general-p Lemma T identity form: S4 for p rows. -/
noncomputable def Ap {p d q : ℕ} (l : Fin d → Fin p × Fin q → ℂ) (i : Fin p) (j : Fin q) :
    MvPolynomial (Fin d) ℂ :=
  1 + ∑ k, C (l k (i, j)) * X k

def S4p : Prop := ∀ (p d q : ℕ) (l : Fin d → Fin p × Fin q → ℂ) (K : Type) [Field K] [Algebra ℂ K]
  (π : MvPolynomial (Fin d) ℂ →ₐ[ℂ] K),
  (∀ (ε : ℂ) (u : Fin d → ℂ), ∑ j, ∏ i, (ε + ∑ k, u k * l k (i, j)) = (q : ℂ) * ε ^ p) →
  (∀ j, π (∏ i, Ap l i j) = 1) →
  ∀ φ : K →ₗ[ℂ] ℂ, ∑ ij : Fin p × Fin q,
    algebraMap ℂ K (φ (π (Ap l ij.1 ij.2))) * (π (Ap l ij.1 ij.2))⁻¹ = algebraMap ℂ K (p * q * φ 1)


end PEqualNP.Gct.Helpers.S3Plan
