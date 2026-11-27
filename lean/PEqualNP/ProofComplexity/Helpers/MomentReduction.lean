import PEqualNP.ProofComplexity.Helpers.PCToolkit

/-!
# Helpers: reduction of the polynomial calculus degree bound for the functional pigeonhole
principle to a statement about moments of partial matchings

The file reduces the statement "the functional pigeonhole system has no polynomial calculus
refutation of degree `B` over `ZMod 2`" to a purely combinatorial statement, `MomentExt`,
about families of values in `ZMod 2` indexed by partial matchings.

* `staticSpan F k`: the linear span of the monomial multiples of the polynomials of `F` of
  total degree at most `k` (the static, Nullstellensatz style, closure in degree `k`).
* `pcDerivable_mem_staticSpan`: if `staticSpan F (k + 1)` meets the polynomials of degree at
  most `k` inside `staticSpan F k` for every `k < B`, every line derivable in degree `B` is in
  `staticSpan F B`.
* `IsPartialMatching`, `MomentConsistent`, `MomentExt`: the combinatorial notions.
* `momentFunctional z`: the linear functional attached to a family `z`; it vanishes on
  `staticSpan (funPHPSystem m N) k` when `z` is `k`-consistent
  (`momentFunctional_staticSpan`).
* `momentConsistent_of_dual`, `dual_eq_momentFunctional`: conversely, every linear functional
  that vanishes on the static span of degree `k` agrees, on polynomials of degree at most
  `k`, with the functional of a `k`-consistent family.
* `staticSpan_funPHP_inter`: the extension property `MomentExt m N k` gives the intersection
  property at level `k`.
* `no_pc_refutation_of_momentExt`: the reduction.
* `momentExt_zero`, `not_momentExt_zero_of_no_holes`, `not_momentExt_two_one_one`: sanity
  checks on `MomentExt`.
-/

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial

/-! ### The static span and the passage from derivations to the static span -/

section Static

variable {σ : Type}

/-- The static span of degree `k`: the linear span of the products `monomial a 1 * f` with
`f` in `F` whose total degree is at most `k`. -/
noncomputable def staticSpan (F : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) :
    Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  Submodule.span (ZMod 2)
    {q | ∃ (a : σ →₀ ℕ) (f : MvPolynomial σ (ZMod 2)),
      f ∈ F ∧ (monomial a 1 * f).totalDegree ≤ k ∧ q = monomial a 1 * f}

theorem monomial_one_mul_X (a : σ →₀ ℕ) (v : σ) :
    monomial a (1 : ZMod 2) * X v = monomial (a + Finsupp.single v 1) 1 := by
  rw [X, monomial_mul_monomial, mul_one]

/-- The total degree of a monomial with coefficient one is the degree of its exponent. -/
theorem totalDegree_monomial_one (a : σ →₀ ℕ) :
    (monomial a (1 : ZMod 2)).totalDegree = a.degree := by
  rw [totalDegree_monomial _ one_ne_zero]
  rfl

/-- A variable times a member of the static span of degree `k` is in the static span of
degree `k + 1`. -/
theorem X_mul_mem_staticSpan {F : Set (MvPolynomial σ (ZMod 2))} {k : ℕ} (j : σ)
    {g : MvPolynomial σ (ZMod 2)} (hg : g ∈ staticSpan F k) :
    X j * g ∈ staticSpan F (k + 1) := by
  induction hg using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨a, f, hf, hdeg, rfl⟩ := hq
    have heq : X j * (monomial a 1 * f) =
        monomial (a + Finsupp.single j 1) (1 : ZMod 2) * f := by
      rw [← monomial_one_mul_X]
      ring
    refine Submodule.subset_span ⟨a + Finsupp.single j 1, f, hf, ?_, heq⟩
    rw [← heq]
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_X]
    omega
  | zero => simp
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ _ hx

/-- From the dynamic calculus to the static span. If, for every `k < B`, the members of the
static span of degree `k + 1` that have degree at most `k` are in the static span of degree
`k`, then every line derivable in degree `B` is in the static span of degree `B`. -/
theorem pcDerivable_mem_staticSpan {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (hint : ∀ k < B, ∀ p, p ∈ staticSpan F (k + 1) → p.totalDegree ≤ k → p ∈ staticSpan F k)
    {p : MvPolynomial σ (ZMod 2)} (h : PCDerivable F B p) : p ∈ staticSpan F B := by
  induction h with
  | @ax p hp hdeg =>
    exact Submodule.subset_span ⟨0, p, hp, by simpa using hdeg, by simp⟩
  | zero => exact Submodule.zero_mem _
  | add _ _ ih1 ih2 => exact Submodule.add_mem _ ih1 ih2
  | @mulX j p _ hdeg ih =>
    by_cases hp0 : p = 0
    · subst hp0
      simp
    have hXp : (X j * p).totalDegree = 1 + p.totalDegree := by
      rw [totalDegree_mul_of_isDomain (X_ne_zero j) hp0, totalDegree_X]
    obtain ⟨k, rfl⟩ : ∃ k, B = k + 1 := ⟨B - 1, by omega⟩
    exact X_mul_mem_staticSpan j (hint k (Nat.lt_succ_self k) p ih (by omega))

/-- Under the intersection property, a constant in the static span of degree `B` is in the
static span of degree `0`. -/
theorem one_mem_staticSpan_zero {F : Set (MvPolynomial σ (ZMod 2))} {B : ℕ}
    (hint : ∀ k < B, ∀ p, p ∈ staticSpan F (k + 1) → p.totalDegree ≤ k → p ∈ staticSpan F k)
    (h : (1 : MvPolynomial σ (ZMod 2)) ∈ staticSpan F B) :
    (1 : MvPolynomial σ (ZMod 2)) ∈ staticSpan F 0 := by
  induction B with
  | zero => exact h
  | succ k ih =>
    exact ih (fun k' hk' => hint k' (by omega)) (hint k (by omega) 1 h (by simp))

/-- Two linear functionals that agree on the monomials of degree at most `k` agree on the
polynomials of total degree at most `k`. -/
theorem dual_eq_of_monomial_eq {k : ℕ}
    (f g : MvPolynomial σ (ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (h : ∀ a : σ →₀ ℕ, a.degree ≤ k → f (monomial a 1) = g (monomial a 1))
    (p : MvPolynomial σ (ZMod 2)) (hp : p.totalDegree ≤ k) : f p = g p := by
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hm : monomial a (p.coeff a) = p.coeff a • monomial a (1 : ZMod 2) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul, map_smul, h a ((le_totalDegree ha).trans hp)]

theorem support_add_single_one [DecidableEq σ] (a : σ →₀ ℕ) (v : σ) :
    (a + Finsupp.single v 1).support = insert v a.support := by
  ext u
  by_cases h : v = u
  · subst h
    simp
  · simp [Ne.symm h]

theorem card_support_le_degree (a : σ →₀ ℕ) : a.support.card ≤ a.degree := by
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun v hv => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)

end Static

/-! ### Partial matchings, consistent moment families, the extension property -/

section Matching

variable {m N : ℕ}

/-- A partial matching: a finite set of pairs (row, column) in which different pairs have
different rows and different columns. -/
def IsPartialMatching (T : Finset (Fin m × Fin N)) : Prop :=
  ∀ a ∈ T, ∀ b ∈ T, (a.1 = b.1 ∨ a.2 = b.2) → a = b

/-- A family `z` of values in `ZMod 2` is `k`-consistent if, for every partial matching `T`
with fewer than `k` pairs and every row `i` not used by `T`, the value at `T` is the sum,
over the columns `j` not used by `T`, of the values at `insert (i, j) T`. Only the values of
`z` at partial matchings with at most `k` pairs matter. -/
def MomentConsistent (m N k : ℕ) (z : Finset (Fin m × Fin N) → ZMod 2) : Prop :=
  ∀ T : Finset (Fin m × Fin N), IsPartialMatching T → T.card < k →
    ∀ i : Fin m, (∀ a ∈ T, a.1 ≠ i) →
      z T = ∑ j ∈ Finset.univ.filter (fun j : Fin N => ∀ a ∈ T, a.2 ≠ j), z (insert (i, j) T)

/-- The extension property at level `k`: every `k`-consistent family agrees, on the partial
matchings with at most `k` pairs, with a `(k + 1)`-consistent family. -/
def MomentExt (m N k : ℕ) : Prop :=
  ∀ z : Finset (Fin m × Fin N) → ZMod 2, MomentConsistent m N k z →
    ∃ z' : Finset (Fin m × Fin N) → ZMod 2, MomentConsistent m N (k + 1) z' ∧
      ∀ T : Finset (Fin m × Fin N), IsPartialMatching T → T.card ≤ k → z' T = z T

theorem isPartialMatching_empty : IsPartialMatching (∅ : Finset (Fin m × Fin N)) := by
  intro a ha
  simp at ha

theorem IsPartialMatching.mono {S T : Finset (Fin m × Fin N)} (hT : IsPartialMatching T)
    (hST : S ⊆ T) : IsPartialMatching S :=
  fun a ha b hb h => hT a (hST ha) b (hST hb) h

/-- Adding a pair in an unused row keeps a partial matching exactly when the column is
unused. -/
theorem isPartialMatching_insert_iff {S : Finset (Fin m × Fin N)} (hS : IsPartialMatching S)
    {i : Fin m} (hrow : ∀ a ∈ S, a.1 ≠ i) (j : Fin N) :
    IsPartialMatching (insert (i, j) S) ↔ ∀ a ∈ S, a.2 ≠ j := by
  constructor
  · intro h a ha haj
    have := h a (Finset.mem_insert_of_mem ha) (i, j) (Finset.mem_insert_self _ _) (Or.inr haj)
    exact hrow a ha (by rw [this])
  · intro hcol a ha b hb hab
    rcases Finset.mem_insert.mp ha with rfl | ha' <;> rcases Finset.mem_insert.mp hb with rfl | hb'
    · rfl
    · rcases hab with h | h
      · exact absurd h.symm (hrow b hb')
      · exact absurd h.symm (hcol b hb')
    · rcases hab with h | h
      · exact absurd h (hrow a ha')
      · exact absurd h (hcol a ha')
    · exact hS a ha' b hb' hab

/-- Adding a second pair in a used row destroys a partial matching. -/
theorem not_isPartialMatching_insert {S : Finset (Fin m × Fin N)} {i : Fin m} {j j0 : Fin N}
    (h0 : (i, j0) ∈ S) (hj : j ≠ j0) : ¬ IsPartialMatching (insert (i, j) S) := by
  intro h
  have := h (i, j) (Finset.mem_insert_self _ _) (i, j0) (Finset.mem_insert_of_mem h0)
    (Or.inl rfl)
  exact hj (congrArg Prod.snd this)

open Classical in
/-- The weight of a set of pairs under a family `z`: the value of `z` at a partial matching,
and zero at a set that is not a partial matching. -/
noncomputable def momentWeight (z : Finset (Fin m × Fin N) → ZMod 2)
    (S : Finset (Fin m × Fin N)) : ZMod 2 :=
  if IsPartialMatching S then z S else 0

theorem momentWeight_of_not {z : Finset (Fin m × Fin N) → ZMod 2}
    {S : Finset (Fin m × Fin N)} (h : ¬ IsPartialMatching S) : momentWeight z S = 0 :=
  ite_eq_right h

theorem momentWeight_of_matching {z : Finset (Fin m × Fin N) → ZMod 2}
    {S : Finset (Fin m × Fin N)} (h : IsPartialMatching S) : momentWeight z S = z S :=
  ite_eq_left h

/-- The row identity for weights: for a `k`-consistent family, the weights of the sets
`insert (i, j) S` over all columns `j` sum to the weight of `S`, as soon as `S` has fewer
than `k` pairs when it is a partial matching. -/
theorem momentWeight_row_sum {z : Finset (Fin m × Fin N) → ZMod 2} {k : ℕ}
    (hz : MomentConsistent m N k z) (S : Finset (Fin m × Fin N))
    (hS : IsPartialMatching S → S.card < k) (i : Fin m) :
    ∑ j : Fin N, momentWeight z (insert (i, j) S) = momentWeight z S := by
  by_cases hM : IsPartialMatching S
  · by_cases hrow : ∀ a ∈ S, a.1 ≠ i
    · rw [momentWeight_of_matching hM, hz S hM (hS hM) i hrow, Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hc : ∀ a ∈ S, a.2 ≠ j
      · rw [ite_eq_left hc,
          momentWeight_of_matching ((isPartialMatching_insert_iff hM hrow j).mpr hc)]
      · rw [ite_eq_right hc, momentWeight_of_not
          (fun h => hc ((isPartialMatching_insert_iff hM hrow j).mp h))]
    · push Not at hrow
      obtain ⟨⟨i', j0⟩, ha, hi⟩ := hrow
      simp only at hi
      subst hi
      rw [Finset.sum_eq_single j0]
      · rw [Finset.insert_eq_of_mem ha]
      · intro j _ hj
        exact momentWeight_of_not (not_isPartialMatching_insert ha hj)
      · intro h
        exact absurd (Finset.mem_univ _) h
  · rw [momentWeight_of_not hM]
    refine Finset.sum_eq_zero fun j _ => ?_
    exact momentWeight_of_not fun h => hM (h.mono (Finset.subset_insert _ _))

/-! ### The functional of a moment family -/

/-- The linear functional of a family `z`: a monomial goes to the weight of its support. -/
noncomputable def momentFunctional (z : Finset (Fin m × Fin N) → ZMod 2) :
    MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  (basisMonomials (Fin m × Fin N) (ZMod 2)).constr (ZMod 2)
    fun a => momentWeight z a.support

theorem momentFunctional_monomial (z : Finset (Fin m × Fin N) → ZMod 2)
    (a : Fin m × Fin N →₀ ℕ) :
    momentFunctional z (monomial a 1) = momentWeight z a.support := by
  have h := (basisMonomials (Fin m × Fin N) (ZMod 2)).constr_basis (ZMod 2)
    (fun a => momentWeight z a.support) a
  rw [coe_basisMonomials] at h
  exact h

/-- The row axiom of pigeon `i`. -/
theorem rowAxiom_totalDegree_le (i : Fin m) :
    ((∑ j : Fin N, X (i, j)) + 1 : MvPolynomial (Fin m × Fin N) (ZMod 2)).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans (max_le ?_ (by simp))
  refine totalDegree_finsetSum_le fun j _ => ?_
  rw [totalDegree_X]

theorem one_le_rowAxiom_totalDegree (hN : 1 ≤ N) (i : Fin m) :
    1 ≤ ((∑ j : Fin N, X (i, j)) + 1 : MvPolynomial (Fin m × Fin N) (ZMod 2)).totalDegree := by
  by_contra hlt
  have h0 : ((∑ j : Fin N, X (i, j)) + 1 :
      MvPolynomial (Fin m × Fin N) (ZMod 2)).totalDegree = 0 := by omega
  rw [totalDegree_eq_zero_iff_eq_C] at h0
  have e0 := congrArg (eval (fun _ : Fin m × Fin N => (0 : ZMod 2))) h0
  have e1 := congrArg
    (eval (fun v : Fin m × Fin N => if v = (i, (⟨0, hN⟩ : Fin N)) then (1 : ZMod 2) else 0)) h0
  simp only [map_add, map_sum, eval_X, map_one, eval_C, Finset.sum_const_zero, zero_add] at e0 e1
  rw [← e0] at e1
  simp [Prod.mk.injEq] at e1

theorem monomial_one_mul_rowAxiom (a : Fin m × Fin N →₀ ℕ) (i : Fin m) :
    monomial a (1 : ZMod 2) * ((∑ j : Fin N, X (i, j)) + 1) =
      (∑ j : Fin N, monomial (a + Finsupp.single (i, j) 1) 1) + monomial a 1 := by
  rw [mul_add, mul_one, Finset.mul_sum]
  simp only [monomial_one_mul_X]

/-- The functional of a `k`-consistent family vanishes on the static span of degree `k` of
the functional pigeonhole system. -/
theorem momentFunctional_staticSpan (hN : 1 ≤ N) {z : Finset (Fin m × Fin N) → ZMod 2}
    {k : ℕ} (hz : MomentConsistent m N k z) {p : MvPolynomial (Fin m × Fin N) (ZMod 2)}
    (hp : p ∈ staticSpan (funPHPSystem m N) k) : momentFunctional z p = 0 := by
  induction hp using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]
  | mem q hq =>
    obtain ⟨a, f, hf, hdeg, rfl⟩ := hq
    rcases hf with ⟨v, rfl⟩ | ⟨i, j, j', hne, rfl⟩ | ⟨i, i', j, hne, rfl⟩ | ⟨i, rfl⟩
    · rw [mul_add, ← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, map_add,
        momentFunctional_monomial, momentFunctional_monomial, support_add_single_one,
        support_add_single_one, Finset.insert_idem v a.support]
      exact CharTwo.add_self_eq_zero _
    · rw [← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, momentFunctional_monomial,
        support_add_single_one, support_add_single_one]
      refine momentWeight_of_not fun h => hne ?_
      have := h (i, j) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) (i, j')
        (Finset.mem_insert_self _ _) (Or.inl rfl)
      exact congrArg Prod.snd this
    · rw [← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, momentFunctional_monomial,
        support_add_single_one, support_add_single_one]
      refine momentWeight_of_not fun h => hne ?_
      have := h (i, j) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) (i', j)
        (Finset.mem_insert_self _ _) (Or.inr rfl)
      exact congrArg Prod.fst this
    · have hrow := one_le_rowAxiom_totalDegree (m := m) hN i
      have hne0 :
          ((∑ j : Fin N, X (i, j)) + 1 : MvPolynomial (Fin m × Fin N) (ZMod 2)) ≠ 0 := by
        intro h0
        rw [h0, totalDegree_zero] at hrow
        omega
      have hmon : monomial a (1 : ZMod 2) ≠ 0 := by
        rw [Ne, monomial_eq_zero]
        exact one_ne_zero
      rw [totalDegree_mul_of_isDomain hmon hne0, totalDegree_monomial_one] at hdeg
      have hcard := card_support_le_degree a
      rw [monomial_one_mul_rowAxiom, map_add, map_sum, momentFunctional_monomial]
      simp only [momentFunctional_monomial, support_add_single_one]
      rw [momentWeight_row_sum hz a.support (fun _ => by omega) i]
      exact CharTwo.add_self_eq_zero _

/-! ### From a functional that vanishes on the static span to a consistent family -/

/-- The exponent of the multilinear monomial of a set of variables. -/
noncomputable def indMon (T : Finset (Fin m × Fin N)) : Fin m × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => if v ∈ T then 1 else 0

theorem indMon_apply (T : Finset (Fin m × Fin N)) (v : Fin m × Fin N) :
    indMon T v = if v ∈ T then 1 else 0 := rfl

theorem indMon_support (T : Finset (Fin m × Fin N)) : (indMon T).support = T := by
  ext v
  simp [indMon_apply]

theorem indMon_degree (T : Finset (Fin m × Fin N)) : (indMon T).degree = T.card := by
  rw [Finsupp.degree_eq_sum]
  simp [indMon_apply]

theorem indMon_insert {T : Finset (Fin m × Fin N)} {v : Fin m × Fin N} (hv : v ∉ T) :
    indMon (insert v T) = indMon T + Finsupp.single v 1 := by
  ext u
  by_cases h : u = v
  · subst h
    simp [indMon_apply, hv]
  · simp [indMon_apply, h]

theorem eq_indMon_support {a : Fin m × Fin N →₀ ℕ} (h : ∀ v, a v ≤ 1) :
    a = indMon a.support := by
  ext v
  have := h v
  by_cases h0 : a v = 0
  · simp [indMon_apply, h0]
  · simp [indMon_apply, h0]
    omega

/-- A functional that vanishes on the static span of degree `k` does not see multiplicities:
on a monomial of degree at most `k` it has the value of the multilinear monomial with the
same support. -/
theorem dual_monomial_eq_indMon {k : ℕ}
    {φ : MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2}
    (hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0) :
    ∀ (n : ℕ) (a : Fin m × Fin N →₀ ℕ), a.degree = n → a.degree ≤ k →
      φ (monomial a 1) = φ (monomial (indMon a.support) 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a han hak
    by_cases h : ∀ v, a v ≤ 1
    · rw [← eq_indMon_support h]
    push Not at h
    obtain ⟨v, hv⟩ := h
    have hle : Finsupp.single v 2 ≤ a := by
      intro u
      by_cases huv : v = u
      · subst huv
        rw [Finsupp.single_eq_same]
        omega
      · simp [huv]
    obtain ⟨b, hb⟩ : ∃ b, a = b + Finsupp.single v 2 :=
      ⟨a - Finsupp.single v 2, (tsub_add_cancel_of_le hle).symm⟩
    set c := b + Finsupp.single v 1 with hc
    have hac : a = c + Finsupp.single v 1 := by
      rw [hb, hc, add_assoc, ← Finsupp.single_add]
    have hdeg : a.degree = c.degree + 1 := by
      rw [hac, map_add, Finsupp.degree_single]
    have hq : monomial b (1 : ZMod 2) * (X v * X v + X v) = monomial a 1 + monomial c 1 := by
      rw [mul_add, ← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, ← hc, ← hac]
    have hmem : monomial a (1 : ZMod 2) + monomial c 1 ∈ staticSpan (funPHPSystem m N) k := by
      refine Submodule.subset_span ⟨b, _, Or.inl ⟨v, rfl⟩, ?_, hq.symm⟩
      rw [hq]
      refine (totalDegree_add _ _).trans (max_le ?_ ?_)
      · rw [totalDegree_monomial_one]
        exact hak
      · rw [totalDegree_monomial_one]
        omega
    have h0 := hφ _ hmem
    rw [map_add, CharTwo.add_eq_zero] at h0
    have hsupp : a.support = c.support := by
      rw [hac, support_add_single_one, Finset.insert_eq_of_mem]
      rw [Finsupp.mem_support_iff, hc]
      simp
    rw [h0, hsupp]
    exact ih c.degree (by omega) c rfl (by omega)

/-- A functional that vanishes on the static span of degree `k` vanishes on the monomials of
degree at most `k` whose support is not a partial matching. -/
theorem dual_monomial_eq_zero {k : ℕ}
    {φ : MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2}
    (hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0)
    (a : Fin m × Fin N →₀ ℕ) (hak : a.degree ≤ k) (hM : ¬ IsPartialMatching a.support) :
    φ (monomial a 1) = 0 := by
  unfold IsPartialMatching at hM
  push Not at hM
  obtain ⟨u, hu, v, hv, huv, hne⟩ := hM
  have hle : Finsupp.single u 1 + Finsupp.single v 1 ≤ a := by
    intro w
    have h1 := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hu)
    have h2 := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hv)
    by_cases hwu : u = w
    · subst hwu
      simpa [Finsupp.single_apply, Ne.symm hne] using h1
    · by_cases hwv : v = w
      · subst hwv
        simpa [Finsupp.single_apply, hne] using h2
      · simp [hwu, hwv]
  obtain ⟨b, hb⟩ : ∃ b, a = b + (Finsupp.single u 1 + Finsupp.single v 1) :=
    ⟨a - (Finsupp.single u 1 + Finsupp.single v 1), (tsub_add_cancel_of_le hle).symm⟩
  have hq : monomial b (1 : ZMod 2) * (X u * X v) = monomial a 1 := by
    rw [← mul_assoc, monomial_one_mul_X, monomial_one_mul_X, hb, add_assoc]
  have hF : (X u * X v : MvPolynomial (Fin m × Fin N) (ZMod 2)) ∈ funPHPSystem m N := by
    obtain ⟨i, j⟩ := u
    obtain ⟨i', j'⟩ := v
    rcases huv with h | h
    · simp only at h
      subst h
      exact Or.inr (Or.inl ⟨i, j, j', fun h => hne (by rw [h]), rfl⟩)
    · simp only at h
      subst h
      exact Or.inr (Or.inr (Or.inl ⟨i, i', j, fun h => hne (by rw [h]), rfl⟩))
  refine hφ _ (Submodule.subset_span ⟨b, _, hF, ?_, hq.symm⟩)
  rw [hq, totalDegree_monomial_one]
  exact hak

/-- The values of a functional that vanishes on the static span of degree `k`, at the
multilinear monomials, form a `k`-consistent family. -/
theorem momentConsistent_of_dual {k : ℕ}
    {φ : MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2}
    (hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0) :
    MomentConsistent m N k fun T => φ (monomial (indMon T) 1) := by
  intro T hT hcard i hrow
  have hnot : ∀ j : Fin N, (i, j) ∉ T := fun j hj => hrow _ hj rfl
  have hmem : monomial (indMon T) (1 : ZMod 2) * ((∑ j : Fin N, X (i, j)) + 1) ∈
      staticSpan (funPHPSystem m N) k := by
    refine Submodule.subset_span ⟨indMon T, _, Or.inr (Or.inr (Or.inr ⟨i, rfl⟩)), ?_, rfl⟩
    refine (totalDegree_mul _ _).trans ?_
    have h1 := rowAxiom_totalDegree_le (N := N) i
    rw [totalDegree_monomial_one, indMon_degree]
    omega
  have h0 := hφ _ hmem
  rw [monomial_one_mul_rowAxiom, map_add, CharTwo.add_eq_zero, map_sum] at h0
  show φ (monomial (indMon T) 1) = _
  rw [← h0, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← indMon_insert (hnot j)]
  by_cases hc : ∀ a ∈ T, a.2 ≠ j
  · rw [ite_eq_left hc]
  · rw [ite_eq_right hc]
    refine dual_monomial_eq_zero hφ _ ?_ ?_
    · rw [indMon_degree, Finset.card_insert_of_notMem (hnot j)]
      omega
    · rw [indMon_support]
      exact fun h => hc ((isPartialMatching_insert_iff hT hrow j).mp h)

/-- A functional that vanishes on the static span of degree `k` agrees with the functional
of its family of values on the polynomials of degree at most `k`. -/
theorem dual_eq_momentFunctional {k : ℕ}
    {φ : MvPolynomial (Fin m × Fin N) (ZMod 2) →ₗ[ZMod 2] ZMod 2}
    (hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0)
    (p : MvPolynomial (Fin m × Fin N) (ZMod 2)) (hp : p.totalDegree ≤ k) :
    φ p = momentFunctional (fun T => φ (monomial (indMon T) 1)) p := by
  refine dual_eq_of_monomial_eq _ _ (fun a ha => ?_) p hp
  rw [momentFunctional_monomial]
  by_cases hM : IsPartialMatching a.support
  · rw [momentWeight_of_matching hM]
    exact dual_monomial_eq_indMon hφ _ a rfl ha
  · rw [momentWeight_of_not hM]
    exact dual_monomial_eq_zero hφ a ha hM

/-! ### The intersection property and the reduction -/

/-- The extension property at level `k` gives the intersection property at level `k`: a
member of the static span of degree `k + 1` of total degree at most `k` is in the static span
of degree `k`. -/
theorem staticSpan_funPHP_inter (hN : 1 ≤ N) {k : ℕ} (hext : MomentExt m N k)
    (p : MvPolynomial (Fin m × Fin N) (ZMod 2))
    (hp : p ∈ staticSpan (funPHPSystem m N) (k + 1)) (hdeg : p.totalDegree ≤ k) :
    p ∈ staticSpan (funPHPSystem m N) k := by
  by_contra hnot
  obtain ⟨φ, hφp, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hφ : ∀ q ∈ staticSpan (funPHPSystem m N) k, φ q = 0 := by
    intro q hq
    have : φ q ∈ (staticSpan (funPHPSystem m N) k).map φ := Submodule.mem_map_of_mem hq
    rw [hmap] at this
    exact (Submodule.mem_bot _).mp this
  obtain ⟨z', hz', hagree⟩ := hext _ (momentConsistent_of_dual hφ)
  apply hφp
  rw [dual_eq_momentFunctional hφ p hdeg, ← momentFunctional_staticSpan hN hz' hp]
  refine dual_eq_of_monomial_eq _ _ (fun a ha => ?_) p hdeg
  rw [momentFunctional_monomial, momentFunctional_monomial]
  by_cases hM : IsPartialMatching a.support
  · rw [momentWeight_of_matching hM, momentWeight_of_matching hM]
    exact (hagree _ hM ((card_support_le_degree a).trans ha)).symm
  · rw [momentWeight_of_not hM, momentWeight_of_not hM]

/-- The reduction. If the extension property for moment families holds at every level below
`B`, the functional pigeonhole system with at least one hole has no polynomial calculus
refutation of degree `B` over `ZMod 2`. -/
theorem no_pc_refutation_of_momentExt :
    ∀ m N B : ℕ, 1 ≤ N → (∀ k < B, MomentExt m N k) →
      ¬ PCRefutable (funPHPSystem m N) B := by
  intro m N B hN hext href
  have hint : ∀ k < B, ∀ p, p ∈ staticSpan (funPHPSystem m N) (k + 1) → p.totalDegree ≤ k →
      p ∈ staticSpan (funPHPSystem m N) k :=
    fun k hk p => staticSpan_funPHP_inter hN (hext k hk) p
  have h0 := one_mem_staticSpan_zero hint (pcDerivable_mem_staticSpan hint href)
  have hz : MomentConsistent m N 0 fun _ => 1 := by
    intro T _ hcard
    omega
  have hval := momentFunctional_staticSpan hN hz h0
  have h1 : (1 : MvPolynomial (Fin m × Fin N) (ZMod 2)) = monomial 0 1 := rfl
  rw [h1, momentFunctional_monomial, Finsupp.support_zero,
    momentWeight_of_matching isPartialMatching_empty] at hval
  exact one_ne_zero hval

/-! ### Sanity checks on the extension property -/

/-- At level `0` the extension property holds as soon as there is a hole: put the value of
the empty matching on the pairs of column `0`. -/
theorem momentExt_zero (m N : ℕ) (hN : 1 ≤ N) : MomentExt m N 0 := by
  intro z _
  refine ⟨fun T => if T = ∅ then z ∅ else
    if ∃ i : Fin m, T = {(i, (⟨0, hN⟩ : Fin N))} then z ∅ else 0, ?_, ?_⟩
  · intro T _ hcard i _
    have hT : T = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hT
    simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, Finset.filter_true,
      ite_true, insert_empty_eq, Finset.singleton_ne_empty, ite_false]
    rw [Finset.sum_eq_single (⟨0, hN⟩ : Fin N)]
    · rw [ite_eq_left ⟨i, rfl⟩]
    · intro j _ hj
      refine ite_eq_right ?_
      rintro ⟨i', h⟩
      rw [Finset.singleton_inj] at h
      exact hj (congrArg Prod.snd h)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro T _ hcard
    have hT : T = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hT
    simp

/-- Without holes and with at least one pigeon the extension property fails at level `0`:
the row identity forces the value of the empty matching to be zero. -/
theorem not_momentExt_zero_of_no_holes (m : ℕ) (hm : 1 ≤ m) : ¬ MomentExt m 0 0 := by
  intro h
  obtain ⟨z', hz', hagree⟩ := h (fun _ => 1) (fun T _ hcard => by omega)
  have h1 := hz' ∅ isPartialMatching_empty (by simp) ⟨0, hm⟩ (by simp)
  rw [hagree ∅ isPartialMatching_empty (by simp)] at h1
  simp at h1

/-- With two pigeons and one hole the extension property fails at level `1`. -/
theorem not_momentExt_two_one_one : ¬ MomentExt 2 1 1 := by
  intro h
  have hz : MomentConsistent 2 1 1 fun _ => 1 := by
    intro T _ hcard i _
    have hT : T = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hT
    simp
  obtain ⟨z', hz', hagree⟩ := h _ hz
  have hM : IsPartialMatching ({((0 : Fin 2), (0 : Fin 1))} : Finset (Fin 2 × Fin 1)) := by
    intro a ha b hb _
    rw [Finset.mem_singleton] at ha hb
    rw [ha, hb]
  have h1 := hz' {((0 : Fin 2), (0 : Fin 1))} hM (by simp) 1 (by simp)
  rw [hagree _ hM (by simp)] at h1
  have hempty : (Finset.univ.filter fun j : Fin 1 =>
      ∀ a ∈ ({((0 : Fin 2), (0 : Fin 1))} : Finset (Fin 2 × Fin 1)), a.2 ≠ j) = ∅ := by
    decide
  rw [hempty, Finset.sum_empty] at h1
  exact one_ne_zero h1

end Matching

end PEqualNP.ProofComplexity.Helpers
