import PEqualNP.ProofComplexity.Helpers.General

/-!
# Plan statements for L-pcx-042 (degree to size, Res(⊕), characteristic two, affine inputs)

Scratch file of the planning leg. Nothing here is proved except two small glue facts
(`pcClosure` is a submodule; it is `DegClosed`). Every `example : Prop` is a STATEMENT to be
proved by a later leg, written on our definitions. Source of the mathematics: the unrefereed
preprint arXiv:2610.00837 (Sections 3 to 6, with p = 2, r = 1), re-derived for our rules.

Conventions.
* `C` is the degree-`D` closure. All lemmas before the simulation use only the abstract
  property `DegClosed C D`, so they are formula-independent.
* A family of multipliers is a `Set` of polynomials. `errKer C M k` is the space of `f` of
  degree at most `k` with `m * f ∈ C` for every `m ∈ M`; `errRank C M k` is its codimension
  in the space of polynomials of degree at most `k` (the rank of `f ↦ ([m * f])_m`).
* For a polynomial `P` and inputs `G`, the source's `Z_P(k)` is `errKer C (zMul P G) k` and
  `c_P(k)` is `errRank C (zMul P G) k`.
* `polyLE k` is ALL polynomials of total degree at most `k` (not only multilinear ones);
  `numMono n k` is the number of MULTILINEAR monomials of degree at most `k`.
-/

namespace PEqualNP.ProofComplexity.DegSizePlan

open MvPolynomial Module PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers

section Abstract

variable {σ : Type}

/-- The degree-`D` polynomial calculus closure of `A`, as a submodule. -/
def pcClosure (A : Set (MvPolynomial σ (ZMod 2))) (D : ℕ) :
    Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) where
  carrier := {p | PCDerivable A D p}
  add_mem' := fun hp hq => PCDerivable.add hp hq
  zero_mem' := PCDerivable.zero
  smul_mem' := by
    intro c p hp
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · simpa using (PCDerivable.zero : PCDerivable A D 0)
    · simpa using hp

theorem mem_pcClosure {A : Set (MvPolynomial σ (ZMod 2))} {D : ℕ}
    {p : MvPolynomial σ (ZMod 2)} : p ∈ pcClosure A D ↔ PCDerivable A D p := Iff.rfl

/-- The only properties of the closure used by the linear algebra: closed under
multiplication by a variable below the degree cap, and it holds the Boolean axioms. -/
structure DegClosed (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D : ℕ) : Prop where
  two_le : 2 ≤ D
  mulX : ∀ (v : σ) (f : MvPolynomial σ (ZMod 2)), f ∈ C → f.totalDegree + 1 ≤ D → X v * f ∈ C
  bool : ∀ v : σ, X v * X v + X v ∈ C

/-- The closure of a system that holds the Boolean axioms is `DegClosed`. -/
theorem degClosed_pcClosure (A : Set (MvPolynomial σ (ZMod 2))) (D : ℕ) (hD : 2 ≤ D)
    (hA : ∀ v : σ, X v * X v + X v ∈ A) : DegClosed (pcClosure A D) D where
  two_le := hD
  mulX := fun v f hf hdeg => PCDerivable.mulX v hf
    ((totalDegree_mul _ _).trans (by rw [totalDegree_X]; omega))
  bool := fun v => PCDerivable.ax (hA v) (by
    refine (totalDegree_add _ _).trans (max_le ((totalDegree_mul _ _).trans ?_) ?_)
    · rw [totalDegree_X]; omega
    · rw [totalDegree_X]; omega)

/-- All polynomials of total degree at most `k`. -/
noncomputable abbrev polyLE (σ : Type) (k : ℕ) : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  restrictTotalDegree σ (ZMod 2) k

/-- The `f` of degree at most `k` with `m * f ∈ C` for every multiplier `m ∈ M`. -/
noncomputable def errKer (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (M : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  polyLE σ k ⊓ ⨅ m ∈ M, C.comap (LinearMap.mulLeft (ZMod 2) m)

theorem mem_errKer {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))}
    {M : Set (MvPolynomial σ (ZMod 2))} {k : ℕ} {f : MvPolynomial σ (ZMod 2)} :
    f ∈ errKer C M k ↔ f.totalDegree ≤ k ∧ ∀ m ∈ M, m * f ∈ C := by
  simp [errKer, polyLE, mem_restrictTotalDegree]

/-- The codimension of `errKer C M k` among the polynomials of degree at most `k`. -/
noncomputable def errRank (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (M : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) : ℕ :=
  finrank (ZMod 2) (polyLE σ k) - finrank (ZMod 2) (errKer C M k)

/-- The multipliers `P * g`, `g ∈ G`: the source's error witnesses of the approximator `P`. -/
noncomputable def zMul (P : MvPolynomial σ (ZMod 2)) (G : Set (MvPolynomial σ (ZMod 2))) :
    Set (MvPolynomial σ (ZMod 2)) := (fun g => P * g) '' G

/-- The number of multilinear monomials of degree at most `k` in `n` variables. -/
def numMono (n k : ℕ) : ℕ := ∑ j ∈ Finset.range (k + 1), n.choose j

/-- The codimension of the low-degree part of the closure: the source's `h_K`. -/
noncomputable def hCodim (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (K : ℕ) : ℕ :=
  finrank (ZMod 2) (polyLE σ K) - finrank (ZMod 2) ↥(C ⊓ polyLE σ K)

/-- The gain per factor: the source's `η` at `p = 2`, `d = 1`. -/
noncomputable def eta (n K : ℕ) : ℝ := (numMono n (K - 1) : ℝ) / (2 * numMono n K)

/-! ## Lemma A (absorption), formula-independent, small -/

example : Prop :=
  ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D : ℕ), DegClosed C D →
    ∀ f g : MvPolynomial σ (ZMod 2), f ∈ C → g.totalDegree + f.totalDegree ≤ D → g * f ∈ C

/-- Lemma A', small: an affine polynomial is idempotent modulo the closure. -/
example : Prop :=
  ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D : ℕ), DegClosed C D →
    ∀ g : MvPolynomial σ (ZMod 2), g.totalDegree ≤ 1 → g * g + g ∈ C

/-! ## Lemma 4.1 (monotone normalised rank) -/

/-- Lemma 4.1, abstract form (pure commutative algebra and counting). `Z` is any space that
is closed under multiplication by a variable below degree `K` and holds the Boolean
multiples of degree at most `K`. Cross-multiplied, so it needs neither `K ≤ card σ` nor
division. -/
example : Prop :=
  ∀ (σ : Type) [Fintype σ] (Z : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (K : ℕ),
    (∀ (v : σ) (f : MvPolynomial σ (ZMod 2)), f ∈ Z → f.totalDegree + 1 ≤ K → X v * f ∈ Z) →
    (∀ (v : σ) (u : σ →₀ ℕ), (u.sum fun _ e => e) + 2 ≤ K →
      (X v * X v + X v) * monomial u (1 : ZMod 2) ∈ Z) →
    ∀ k k' : ℕ, k ≤ k' → k' ≤ K →
      (finrank (ZMod 2) (polyLE σ k') - finrank (ZMod 2) ↥(Z ⊓ polyLE σ k')) *
          numMono (Fintype.card σ) k
        ≤ (finrank (ZMod 2) (polyLE σ k) - finrank (ZMod 2) ↥(Z ⊓ polyLE σ k)) *
          numMono (Fintype.card σ) k'

/-- Lemma 4.1 as used: for an approximator `P` of degree at most `a` and affine inputs `G`,
with `a + K + 1 ≤ D`. -/
example : Prop :=
  ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D a K : ℕ)
    (P : MvPolynomial σ (ZMod 2)) (G : Set (MvPolynomial σ (ZMod 2))),
    DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ 1) → a + K + 1 ≤ D →
    ∀ k k' : ℕ, k ≤ k' → k' ≤ K →
      errRank C (zMul P G) k' * numMono (Fintype.card σ) k
        ≤ errRank C (zMul P G) k * numMono (Fintype.card σ) k'

/-! ## Rank retention (Lemmas 3.1 to 3.3 and Corollary 3.5 at p = 2) -/

/-- Lemmas 3.1 to 3.3 in matrix form, pure linear algebra. `E` is ANY field of
characteristic two with an `ι`-family `lam` that is linearly independent over `ZMod 2`
(a function field is not needed: a finite field of `2 ^ card ι` elements does). If the
kernel of `∑ lam i • M i` is inside the kernel of `∑ lam i ^ 2 • M i`, then some
combination with coefficients in `ZMod 2` keeps half of the rank of the stacked matrix. -/
example : Prop :=
  ∀ (ι r n : Type) [Fintype ι] [Fintype r] [Fintype n] [DecidableEq n]
    (E : Type) [Field E] [Algebra (ZMod 2) E] (lam : ι → E)
    (M : ι → Matrix r n (ZMod 2)),
    LinearIndependent (ZMod 2) lam →
    (∀ u : n → E, (∑ i, lam i • (M i).map (algebraMap (ZMod 2) E)).mulVec u = 0 →
      (∑ i, lam i ^ 2 • (M i).map (algebraMap (ZMod 2) E)).mulVec u = 0) →
    ∃ c : ι → ZMod 2,
      (Matrix.of fun (p : ι × r) (j : n) => M p.1 p.2 j).rank ≤ 2 * (∑ i, c i • M i).rank

/-- Corollary 3.5 at `p = 2`, affine `G`: rank retention for the multiplication maps. With
`H` of degree at most `b` and `b + k + 2 ≤ D`, some sum `q` of a subset of `G` has: the rank
of `f ↦ ([h * q * f])_h` on degree at most `k` is at least half the rank of
`f ↦ ([h * g * f])_{h, g}`. -/
example : Prop :=
  ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D b k : ℕ)
    (H : Set (MvPolynomial σ (ZMod 2))) (G : Finset (MvPolynomial σ (ZMod 2))),
    DegClosed C D → (∀ h ∈ H, h.totalDegree ≤ b) → (∀ g ∈ G, g.totalDegree ≤ 1) →
    b + k + 2 ≤ D →
    ∃ J : Finset (MvPolynomial σ (ZMod 2)), J ⊆ G ∧
      errRank C (Set.image2 (fun h g => h * g) H ↑G) k
        ≤ 2 * errRank C ((fun h => h * ∑ g ∈ J, g) '' H) k

/-! ## Lemma 4.2 (approximation gain) -/

/-- Lemma 4.2 at `p = 2`: one more affine factor removes half of the rank one degree
lower. -/
example : Prop :=
  ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D a K : ℕ)
    (P : MvPolynomial σ (ZMod 2)) (G : Finset (MvPolynomial σ (ZMod 2))),
    DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ 1) → 1 ≤ K →
    a + K + 2 ≤ D →
    ∃ q ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2))),
      2 * errRank C (zMul (P * (1 + q)) ↑G) K + errRank C (zMul P ↑G) (K - 1)
        ≤ 2 * errRank C (zMul P ↑G) K

/-! ## Theorem 4.3 (the approximators and the common multiplier) -/

/-- Theorem 4.3 (a): `t` greedy factors bring the rank below `h_K * (1 - η) ^ t`. -/
example : Prop :=
  ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t : ℕ)
    (G : Finset (MvPolynomial σ (ZMod 2))),
    DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ 1) → 1 ≤ K → K + t + 1 ≤ D →
    ∃ qs : Fin t → MvPolynomial σ (ZMod 2),
      (∀ j, qs j ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2)))) ∧
      (errRank C (zMul (∏ j, (1 + qs j)) ↑G) K : ℝ)
        ≤ hCodim C K * (1 - eta (Fintype.card σ) K) ^ t

/-- Theorem 4.3 (b): the common multiplier. `S` indexes the lines, `G ν` are the affine
inputs of line `ν`. -/
example : Prop :=
  ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t : ℕ)
    (ι : Type) (S : Finset ι) (G : ι → Finset (MvPolynomial σ (ZMod 2))),
    DegClosed C D → (1 : MvPolynomial σ (ZMod 2)) ∉ C →
    (∀ ν ∈ S, ∀ g ∈ G ν, g.totalDegree ≤ 1) → 1 ≤ K → K + t + 1 ≤ D →
    (S.card : ℝ) * (1 - eta (Fintype.card σ) K) ^ t < 1 →
    ∃ (f : MvPolynomial σ (ZMod 2)) (qs : ι → Fin t → MvPolynomial σ (ZMod 2)),
      f.totalDegree ≤ K ∧ f ∉ C ∧
      (∀ ν ∈ S, ∀ j, qs ν j ∈ Submodule.span (ZMod 2) (↑(G ν) : Set (MvPolynomial σ (ZMod 2)))) ∧
      ∀ ν ∈ S, ∀ g ∈ G ν, (∏ j, (1 + qs ν j)) * g * f ∈ C

end Abstract

/-! ## Proposition 5.1 (the simulation), on OUR rules -/

/-- The transfer step (formula-independent; reuses `pcDerivable_prod_absorb`): if `f * P` is
in the closure for `P = ∏ (1 + qs j)` with every `qs j` in the span of `G`, and `g * R * f`
is in the closure for every `g ∈ G`, then `R * f` is, in budget `K + t + deg R ≤ D`. -/
example : Prop :=
  ∀ (σ : Type) (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t r : ℕ)
    (G : Set (MvPolynomial σ (ZMod 2))) (qs : Fin t → MvPolynomial σ (ZMod 2))
    (f R : MvPolynomial σ (ZMod 2)),
    DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ 1) →
    (∀ j, qs j ∈ Submodule.span (ZMod 2) G) → f.totalDegree ≤ K → R.totalDegree ≤ r →
    K + t + r ≤ D →
    (∏ j, (1 + qs j)) * f ∈ C → (∀ g ∈ G, g * R * f ∈ C) → R * f ∈ C

/-- Proposition 5.1 on our rules (axioms of a CNF of width at most `w`, resolution on a
linear form, SEMANTIC weakening of one line). Budget `K + max (2 * t + 2) (t + w) ≤ D`:
axiom `K + t + w`, weakening `K + 2 * t` and `K + t + 1`, resolution `K + 2 * t + 1` and
`K + t + 2`. -/
example : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinClause V))
    (w D K t : ℕ) (f : MvPolynomial V (ZMod 2))
    (qs : LinClause V → Fin t → MvPolynomial V (ZMod 2)),
    (∀ A ∈ F, A.card ≤ w) → IsLinDerivation ((fun A => linOfClause A) '' F) π →
    K + max (2 * t + 2) (t + w) ≤ D → f.totalDegree ≤ K →
    (∀ L ∈ π, ∀ j, qs L j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑L : Set (LinEq V)))) →
    (∀ L ∈ π, ∀ q ∈ L, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * eqPoly q * f)) →
    ∀ L ∈ π, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * f)

/-- Its consequence for a refutation: the common multiplier is in the closure. -/
example : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinClause V))
    (w D K t : ℕ) (f : MvPolynomial V (ZMod 2))
    (qs : LinClause V → Fin t → MvPolynomial V (ZMod 2)),
    (∀ A ∈ F, A.card ≤ w) → IsLinRefutation F π →
    K + max (2 * t + 2) (t + w) ≤ D → f.totalDegree ≤ K →
    (∀ L ∈ π, ∀ j, qs L j ∈ Submodule.span (ZMod 2) ((fun q => eqPoly q) '' (↑L : Set (LinEq V)))) →
    (∀ L ∈ π, ∀ q ∈ L, PCDerivable (cnfSystem F) D ((∏ j, (1 + qs L j)) * eqPoly q * f)) →
    PCDerivable (cnfSystem F) D f

/-! ## The size criterion before arithmetic, and the two side facts -/

/-- Assembly of Theorem 4.3 and Proposition 5.1: the size bound with `η` explicit. -/
example : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (π : List (LinClause V))
    (w D K t : ℕ),
    (∀ A ∈ F, A.card ≤ w) → IsLinRefutation F π → ¬ PCRefutable (cnfSystem F) D →
    1 ≤ K → K + max (2 * t + 2) (t + w) ≤ D →
    1 ≤ (π.length : ℝ) * (1 - eta (Fintype.card V) K) ^ t

/-- Completeness in degree `max (card V) w` (small to medium; reuses `vanish_derivable`):
needed only to know `D < card V`, so that `K ≤ card V` in the binomial estimate. -/
example : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (Clause V)) (w D : ℕ),
    (∀ A ∈ F, A.card ≤ w) → ¬ Satisfiable F → w ≤ D → Fintype.card V ≤ D →
    PCRefutable (cnfSystem F) D

/-- The binomial estimate: `η ≥ K / (2 (n + 1))` for `1 ≤ K ≤ n + 1`. -/
example : Prop :=
  ∀ n K : ℕ, 1 ≤ K → K ≤ n + 1 → (K : ℝ) / (2 * (n + 1)) ≤ eta n K

/-! ## The final theorem -/

/-- The target as recorded (L-pcx-042). The chain above gives it with room to spare. -/
example : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V)) (π : List (PEqualNP.ProofComplexity.LinClause V)) (w D : ℕ), (∀ C ∈ F, C.card ≤ w) → 32 * w ≤ D → 32 ≤ D → ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem F) D → PEqualNP.ProofComplexity.IsLinRefutation F π → Real.exp ((D : ℝ) ^ 2 / (1024 * (Fintype.card V : ℝ))) ≤ (π.length : ℝ)

/-- The stronger form that the same chain gives on our rules (width up to `D / 2`, constant
`256` in place of `1024`). -/
example : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (F : Set (PEqualNP.ProofComplexity.Clause V)) (π : List (PEqualNP.ProofComplexity.LinClause V)) (w D : ℕ), (∀ C ∈ F, C.card ≤ w) → 2 * w ≤ D → 32 ≤ D → ¬ PEqualNP.ProofComplexity.PCRefutable (PEqualNP.ProofComplexity.cnfSystem F) D → PEqualNP.ProofComplexity.IsLinRefutation F π → Real.exp ((D : ℝ) ^ 2 / (256 * (Fintype.card V : ℝ))) ≤ (π.length : ℝ)

end PEqualNP.ProofComplexity.DegSizePlan
