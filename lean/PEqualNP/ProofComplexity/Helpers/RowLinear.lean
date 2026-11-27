import Mathlib

/-!
# Helpers: the row-linear space and a common kernel of affine restrictions

This file checks the counting core of Section 6 of K. Braun, "An exponential lower bound for
the bit pigeonhole principle in resolution over parities" (arXiv:2609.23015, unrefereed),
namely the dimension count behind its Lemma 6.4 (with the dimension half of its Lemma 6.3 and
the lower bound half of its Lemma 5.4).

Variables are `b (i, t)` for a row (pigeon) `i : Fin m` and a bit `t : Fin l`, over `ZMod 2`.

* `rowLinear m l k` is the span of the monomials of degree at most `k` that use at most one
  variable of each row, each to the power one. `le_finrank_rowLinear` bounds its dimension
  from below by `m.choose k * l ^ k`.
* `exists_ne_zero_forall_eq_zero` is the linear pigeonhole: finitely many linear maps whose
  ranges have total dimension below that of the source have a common nonzero kernel vector.
* An affine substitution `φ` into `d` variables (each `φ x` of total degree at most one) sends
  polynomials of degree at most `k` to polynomials of degree at most `k`
  (`totalDegree_aeval_le`), and those form a space of dimension at most `(d + k).choose k`
  (`finrank_restrictTotalDegree_le`). Nothing is multilinearised: the target is the full
  polynomial ring in `d` variables.
* `mul_choose_lt` is the numeric inequality.
* `exists_rowLinear_aeval_eq_zero` combines these: at most `M` affine substitutions, each into
  at most `m * l - 3 * l * (k + 1) - 1` variables, kill a common nonzero row-linear polynomial,
  as polynomials.

* `exists_cofactors` is the ideal membership with degree control: for an affine substitution
  `ψ` of the ring into itself and `f` of degree at most `k`, the difference `f - f ∘ ψ` is a
  combination of the `X x - ψ x` with cofactors of degree at most `k - 1`.
  `exists_rowLinear_eq_sum_mul` adds this to the common kernel statement.

What is not in this file: the passage from a flat given by affine equations of rank `r` to an
affine parametrisation by `m * l - r` variables such that every `X x - ψ x` is a constant
combination of the given equations (Lemma 6.1 of the paper, Gaussian elimination).
-/

namespace PEqualNP.ProofComplexity.Helpers

open MvPolynomial Module

/-! ### The row-linear space and its dimension -/

/-- Exponent vectors of degree at most `k` whose exponents in each row sum to at most one. -/
def rowLinearSet (m l k : ℕ) : Set ((Fin m × Fin l) →₀ ℕ) :=
  {u | (u.sum fun _ e => e) ≤ k ∧ ∀ i, ∑ t, u (i, t) ≤ 1}

/-- The row-linear space: the span of the monomials of degree at most `k` with at most one
variable from each row. -/
noncomputable def rowLinear (m l k : ℕ) : Submodule (ZMod 2) (MvPolynomial (Fin m × Fin l) (ZMod 2)) :=
  restrictSupport (ZMod 2) (rowLinearSet m l k)

theorem rowLinearSet_finite (m l k : ℕ) : (rowLinearSet m l k).Finite := by
  have h : {u : (Fin m × Fin l) →₀ ℕ | ∀ a, u a ≤ 1}.Finite :=
    (Set.Finite.pi' fun _ ↦ Set.finite_le_nat _).preimage DFunLike.coe_injective.injOn
  refine h.subset fun u hu a => ?_
  refine le_trans ?_ (hu.2 a.1)
  exact Finset.single_le_sum (f := fun t => u (a.1, t)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ a.2)

theorem rowLinear_le_restrictTotalDegree (m l k : ℕ) :
    rowLinear m l k ≤ restrictTotalDegree (Fin m × Fin l) (ZMod 2) k :=
  restrictSupport_mono (ZMod 2) fun _ hu => hu.1

theorem totalDegree_le_of_mem_rowLinear {m l k : ℕ}
    {f : MvPolynomial (Fin m × Fin l) (ZMod 2)} (hf : f ∈ rowLinear m l k) :
    f.totalDegree ≤ k :=
  (mem_restrictTotalDegree _ _ _).1 (rowLinear_le_restrictTotalDegree m l k hf)

/-- The exponent vector choosing the bit `c i` in each row `i` of `S`. -/
noncomputable def rowMonomial {m l : ℕ} (S : Finset (Fin m)) (c : S → Fin l) :
    (Fin m × Fin l) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    fun x => if h : x.1 ∈ S then (if c ⟨x.1, h⟩ = x.2 then 1 else 0) else 0

theorem rowMonomial_apply {m l : ℕ} (S : Finset (Fin m)) (c : S → Fin l) (x : Fin m × Fin l) :
    rowMonomial S c x = if h : x.1 ∈ S then (if c ⟨x.1, h⟩ = x.2 then 1 else 0) else 0 :=
  rfl

theorem rowMonomial_row_sum {m l : ℕ} (S : Finset (Fin m)) (c : S → Fin l) (i : Fin m) :
    ∑ t, rowMonomial S c (i, t) = if i ∈ S then 1 else 0 := by
  by_cases h : i ∈ S
  · simp only [rowMonomial_apply, h, dite_true, ite_true]
    exact (Finset.sum_ite_eq Finset.univ (c ⟨i, h⟩) (fun _ => 1)).trans (by simp)
  · simp [rowMonomial_apply, h]

theorem rowMonomial_mem {m l k : ℕ} (S : Finset (Fin m)) (hS : S.card = k) (c : S → Fin l) :
    rowMonomial S c ∈ rowLinearSet m l k := by
  refine ⟨?_, fun i => ?_⟩
  · rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type]
    simp [rowMonomial_row_sum, hS]
  · rw [rowMonomial_row_sum]
    split_ifs <;> simp

theorem rowMonomial_injective {m l : ℕ} {S S' : Finset (Fin m)} {c : S → Fin l}
    {c' : S' → Fin l} (h : rowMonomial S c = rowMonomial S' c') : S = S' ∧ HEq c c' := by
  have hS : S = S' := by
    ext i
    have := congrArg (fun u : (Fin m × Fin l) →₀ ℕ => ∑ t, u (i, t)) h
    simp only [rowMonomial_row_sum] at this
    by_cases h1 : i ∈ S <;> by_cases h2 : i ∈ S' <;> simp_all
  subst hS
  refine ⟨rfl, heq_of_eq (funext fun i => ?_)⟩
  by_contra hne
  have hne' : ¬ c' i = c i := fun h' => hne h'.symm
  have := DFunLike.congr_fun h (i.1, c i)
  simp [rowMonomial_apply, hne'] at this

/-- The lower bound half of Lemma 5.4 of arXiv:2609.23015: the row-linear space has dimension
at least `m.choose k * l ^ k`. -/
theorem le_finrank_rowLinear (m l k : ℕ) :
    m.choose k * l ^ k ≤ finrank (ZMod 2) (rowLinear m l k) := by
  classical
  have hfin : Finite (rowLinearSet m l k) := (rowLinearSet_finite m l k).to_subtype
  have hrank : finrank (ZMod 2) (rowLinear m l k) = Nat.card (rowLinearSet m l k) :=
    Module.finrank_eq_nat_card_basis (basisRestrictSupport (ZMod 2) (rowLinearSet m l k))
  rw [hrank]
  let g : (Σ S : {S : Finset (Fin m) // S.card = k}, (S.1 → Fin l)) → rowLinearSet m l k :=
    fun p => ⟨rowMonomial p.1.1 p.2, rowMonomial_mem p.1.1 p.1.2 p.2⟩
  have hg : Function.Injective g := by
    rintro ⟨⟨S, hS⟩, c⟩ ⟨⟨S', hS'⟩, c'⟩ h
    obtain ⟨rfl, hc⟩ := rowMonomial_injective (congrArg Subtype.val h)
    obtain rfl := eq_of_heq hc
    rfl
  have hcard : Nat.card (Σ S : {S : Finset (Fin m) // S.card = k}, (S.1 → Fin l))
      = m.choose k * l ^ k := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    have : ∀ S : {S : Finset (Fin m) // S.card = k}, Fintype.card (S.1 → Fin l) = l ^ k := by
      intro S
      simp [S.2]
    rw [Finset.sum_congr rfl fun S _ => this S]
    simp
  rw [← hcard]
  exact Nat.card_le_card_of_injective g hg

/-! ### The linear pigeonhole -/

/-- Finitely many linear maps out of `V` whose ranges have total dimension less than that of
`V` vanish together at some nonzero vector. -/
theorem exists_ne_zero_forall_eq_zero {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype ι] {W : ι → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V →ₗ[K] W i) (D : ι → ℕ)
    (hD : ∀ i, finrank K (LinearMap.range (f i)) ≤ D i) (h : ∑ i, D i < finrank K V) :
    ∃ v, v ≠ 0 ∧ ∀ i, f i v = 0 := by
  have hV : Module.Finite K V := Module.finite_of_finrank_pos (lt_of_le_of_lt (Nat.zero_le _) h)
  by_contra hcon
  push Not at hcon
  let F : V →ₗ[K] (∀ i, LinearMap.range (f i)) := LinearMap.pi fun i => (f i).rangeRestrict
  have hF : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hv0
    obtain ⟨i, hi⟩ := hcon v hv0
    exact hi (congrArg Subtype.val (congrFun hv i))
  have h1 := LinearMap.finrank_le_finrank_of_injective hF
  rw [Module.finrank_pi_fintype] at h1
  exact absurd (lt_of_le_of_lt (h1.trans (Finset.sum_le_sum fun i _ => hD i)) h) (lt_irrefl _)

/-! ### Affine substitutions and the dimension of their target -/

/-- An affine substitution does not raise the total degree. -/
theorem totalDegree_aeval_le {σ τ K : Type*} [Field K]
    (φ : σ → MvPolynomial τ K) (hφ : ∀ x, (φ x).totalDegree ≤ 1) (f : MvPolynomial σ K) :
    (aeval φ f).totalDegree ≤ f.totalDegree := by
  rw [aeval_def, eval₂_eq]
  refine totalDegree_finsetSum_le fun u hu => ?_
  refine (totalDegree_mul _ _).trans ?_
  rw [algebraMap_eq, totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (le_totalDegree hu)
  refine (totalDegree_pow _ _).trans ?_
  exact (Nat.mul_le_mul_left _ (hφ i)).trans (le_of_eq (mul_one _))

/-- There are at most `(d + k).choose k` exponent vectors of degree at most `k` in `d`
variables. -/
theorem card_degree_le (d k : ℕ) :
    Nat.card {u : Fin d →₀ ℕ | (u.sum fun _ e => e) ≤ k} ≤ (d + k).choose k := by
  classical
  let g : {u : Fin d →₀ ℕ | (u.sum fun _ e => e) ≤ k} → Sym (Option (Fin d)) k := fun u =>
    ⟨(Finsupp.toMultiset u.1).map some
        + Multiset.replicate (k - (u.1.sum fun _ e => e)) none, by
      have h : (u.1.sum fun _ e => e) ≤ k := u.2
      have e : (u.1.sum fun _ => id) = u.1.sum fun _ e => e := rfl
      simp only [Multiset.card_add, Multiset.card_map, Multiset.card_replicate,
        Finsupp.card_toMultiset, e]
      omega⟩
  have hg : Function.Injective g := by
    rintro ⟨u, hu⟩ ⟨v, hv⟩ h
    apply Subtype.ext
    ext x
    have h1 := congrArg (fun s : Sym (Option (Fin d)) k => Multiset.count (some x) s.1) h
    simpa [g, Multiset.count_map_eq_count' some _ (Option.some_injective _),
      Multiset.count_replicate] using h1
  have h2 := Nat.card_le_card_of_injective g hg
  have h3 : Nat.card (Sym (Option (Fin d)) k) = (d + k).choose k := by
    rw [Nat.card_eq_fintype_card, Sym.card_sym_eq_multichoose, Nat.multichoose_eq]
    simp
  exact h3 ▸ h2

/-- The dimension half of Lemma 6.3 of arXiv:2609.23015: polynomials of degree at most `k` in
`d` variables form a space of dimension at most `(d + k).choose k`. -/
theorem finrank_restrictTotalDegree_le (K : Type*) [Field K] (d k : ℕ) :
    finrank K (restrictTotalDegree (Fin d) K k) ≤ (d + k).choose k := by
  have h : finrank K (restrictTotalDegree (Fin d) K k)
      = Nat.card {u : Fin d →₀ ℕ | (u.sum fun _ e => e) ≤ k} :=
    Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)
  rw [h]
  exact card_degree_le d k

/-- The restriction of an affine substitution to the row-linear space has a range of dimension
at most `(d + k).choose k`. -/
theorem finrank_range_aeval_rowLinear_le {m l k d : ℕ}
    (φ : Fin m × Fin l → MvPolynomial (Fin d) (ZMod 2)) (hφ : ∀ x, (φ x).totalDegree ≤ 1) :
    finrank (ZMod 2)
      (LinearMap.range ((aeval φ).toLinearMap ∘ₗ (rowLinear m l k).subtype))
      ≤ (d + k).choose k := by
  refine le_trans (Submodule.finrank_mono ?_) (finrank_restrictTotalDegree_le (ZMod 2) d k)
  rintro _ ⟨f, rfl⟩
  rw [mem_restrictTotalDegree]
  exact (totalDegree_aeval_le φ hφ f.1).trans (totalDegree_le_of_mem_rowLinear f.2)

/-! ### Ideal membership with degree control -/

/-- For a monomial of degree `n` and an affine substitution `ψ` of the ring into itself, the
difference between the monomial and its image is a combination of the `X x - ψ x` with
cofactors that vanish or have degree below `n`. -/
theorem exists_cofactors_monomial {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]
    (ψ : σ → MvPolynomial σ K) (hψ : ∀ x, (ψ x).totalDegree ≤ 1) :
    ∀ (n : ℕ) (s : σ →₀ ℕ) (c : K), (s.sum fun _ e => e) = n →
      ∃ a : σ → MvPolynomial σ K,
        monomial s c - aeval ψ (monomial s c) = ∑ x, a x * (X x - ψ x) ∧
        ∀ x, a x = 0 ∨ (a x).totalDegree + 1 ≤ n := by
  intro n
  induction n with
  | zero =>
    intro s c hs
    have hs0 : s = 0 := by
      ext y
      by_contra hy
      have hmem : y ∈ s.support := Finsupp.mem_support_iff.2 hy
      have h1 : s y ≤ ∑ i ∈ s.support, s i :=
        Finset.single_le_sum (f := fun i => s i) (fun _ _ => Nat.zero_le _) hmem
      have h2 : ∑ i ∈ s.support, s i = 0 := hs
      exact hy (by simpa using Nat.le_zero.1 (h2 ▸ h1))
    subst hs0
    refine ⟨fun _ => 0, ?_, fun _ => Or.inl rfl⟩
    have : (monomial (0 : σ →₀ ℕ) c : MvPolynomial σ K) = C c := rfl
    simp [this]
  | succ n ih =>
    intro s c hs
    obtain ⟨x, hx⟩ : ∃ x, s x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have : s = 0 := Finsupp.ext hcon
      subst this
      simp at hs
    set s' : σ →₀ ℕ := s - Finsupp.single x 1 with hs'
    have hsplit : s = s' + Finsupp.single x 1 := by
      ext y
      by_cases hy : y = x
      · subst hy
        simp only [hs', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
          Finsupp.single_eq_same]
        omega
      · simp [hs', Ne.symm hy]
    have hsum : (s'.sum fun _ e => e) = n := by
      have h1 : (s.sum fun _ e => e) = (s'.sum fun _ e => e) + 1 := by
        conv_lhs => rw [hsplit]
        rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
        simp
      omega
    obtain ⟨a, ha, hdeg⟩ := ih s' c hsum
    set p : MvPolynomial σ K := monomial s' c with hp
    have hmon : monomial s c = p * X x := by
      rw [hsplit, monomial_add_single, pow_one]
    have hpdeg : p.totalDegree ≤ n := by
      have := totalDegree_monomial_le s' c
      exact this.trans (le_of_eq hsum)
    refine ⟨fun y => ψ x * a y + if y = x then p else 0, ?_, fun y => Or.inr ?_⟩
    · have e1 : ∑ y, (ψ x * a y + if y = x then p else 0) * (X y - ψ y)
          = ψ x * ∑ y, a y * (X y - ψ y) + p * (X x - ψ x) := by
        simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, ite_mul,
          zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [e1, ← ha, hmon, map_mul, aeval_X]
      ring
    · show (ψ x * a y + if y = x then p else 0).totalDegree + 1 ≤ n + 1
      have h1 : (ψ x * a y).totalDegree ≤ n := by
        rcases hdeg y with h0 | h0
        · simp [h0]
        · have := totalDegree_mul (ψ x) (a y)
          have := hψ x
          omega
      have h2 : (if y = x then p else 0 : MvPolynomial σ K).totalDegree ≤ n := by
        split_ifs
        · exact hpdeg
        · simp
      have := totalDegree_add (ψ x * a y) (if y = x then p else 0)
      have := max_le h1 h2
      omega

/-- The ideal membership half of Lemma 6.3 of arXiv:2609.23015, for an affine substitution `ψ`
of the ring into itself: if `f` has degree at most `k`, then `f - f ∘ ψ` is a combination of
the `X x - ψ x` with cofactors of degree at most `k - 1`. In particular, if `ψ` kills `f`
then `f` itself is such a combination. -/
theorem exists_cofactors {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]
    (ψ : σ → MvPolynomial σ K) (hψ : ∀ x, (ψ x).totalDegree ≤ 1)
    (f : MvPolynomial σ K) (k : ℕ) (hf : f.totalDegree ≤ k) :
    ∃ a : σ → MvPolynomial σ K,
      f - aeval ψ f = ∑ x, a x * (X x - ψ x) ∧ ∀ x, (a x).totalDegree ≤ k - 1 := by
  choose A hA1 hA2 using fun (u : σ →₀ ℕ) (c : K) =>
    exists_cofactors_monomial ψ hψ _ u c rfl
  refine ⟨fun x => ∑ u ∈ f.support, A u (f.coeff u) x, ?_, fun x => ?_⟩
  · conv_lhs => rw [← support_sum_monomial_coeff f]
    rw [map_sum, ← Finset.sum_sub_distrib]
    simp_rw [hA1, Finset.sum_mul]
    exact Finset.sum_comm
  · refine totalDegree_finsetSum_le fun u hu => ?_
    rcases hA2 u (f.coeff u) x with h0 | h0
    · simp [h0]
    · have h1 : (u.sum fun _ e => e) ≤ f.totalDegree := le_totalDegree hu
      omega

/-! ### The numeric inequality -/

/-- The integer form of the ratio estimate in the proof of Lemma 6.4 of arXiv:2609.23015. -/
theorem choose_mul_pow_le {m l k d : ℕ} (hkm : k ≤ m)
    (hd : d + 3 * l * (k + 1) + 1 ≤ m * l) :
    (d + k).choose k * m ^ k ≤ m.choose k * l ^ k * (m - k) ^ k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkm
  have hsub : k + j - k = j := by omega
  rw [hsub]
  have hkl : k ≤ l * k := by
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp at hd
    · exact Nat.le_mul_of_pos_left k hl
  have h1 : d + k + l * k ≤ j * l := by nlinarith
  have key : (d + k) * (k + j) ≤ l * (j + 1) * j := by
    nlinarith [Nat.mul_le_mul_right (k + j) h1]
  have hA : (d + k).choose k * k.factorial ≤ (d + k) ^ k := by
    have := Nat.descFactorial_le_pow (d + k) k
    rw [Nat.descFactorial_eq_factorial_mul_choose] at this
    rwa [mul_comm]
  have hB : (j + 1) ^ k ≤ k.factorial * (k + j).choose k := by
    have := Nat.pow_sub_le_descFactorial (k + j) k
    rw [Nat.descFactorial_eq_factorial_mul_choose] at this
    have e : k + j + 1 - k = j + 1 := by omega
    rwa [e] at this
  have hpos : 0 < (j + 1) ^ k := by positivity
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc (j + 1) ^ k * ((d + k).choose k * (k + j) ^ k)
      ≤ (k.factorial * (k + j).choose k) * ((d + k).choose k * (k + j) ^ k) :=
        Nat.mul_le_mul_right _ hB
    _ = ((d + k).choose k * k.factorial) * ((k + j) ^ k * (k + j).choose k) := by ring
    _ ≤ (d + k) ^ k * ((k + j) ^ k * (k + j).choose k) := Nat.mul_le_mul_right _ hA
    _ = ((d + k) * (k + j)) ^ k * (k + j).choose k := by rw [mul_pow]; ring
    _ ≤ (l * (j + 1) * j) ^ k * (k + j).choose k :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left key k)
    _ = (j + 1) ^ k * ((k + j).choose k * l ^ k * j ^ k) := by rw [mul_pow, mul_pow]; ring

/-- The numeric inequality of Lemma 6.4 of arXiv:2609.23015: `M` restriction targets together
have dimension below that of the row-linear space. -/
theorem mul_choose_lt {m l k M d : ℕ} (hl : 1 ≤ l) (hkm : k ≤ m)
    (hlog : (m : ℝ) * Real.log (4 * M) ≤ (k : ℝ) ^ 2)
    (hd : d + 3 * l * (k + 1) + 1 ≤ m * l) :
    M * (d + k).choose k < m.choose k * l ^ k := by
  have hBpos : 0 < m.choose k * l ^ k :=
    Nat.mul_pos (Nat.choose_pos hkm) (by positivity)
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simpa using hBpos
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp at hd
    · exact h
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hN := choose_mul_pow_le hkm hd
  have hNR : ((d + k).choose k : ℝ) * (m : ℝ) ^ k
      ≤ (m.choose k : ℝ) * (l : ℝ) ^ k * ((m : ℝ) - k) ^ k := by
    have := (Nat.cast_le (α := ℝ)).2 hN
    push_cast [Nat.cast_sub hkm] at this
    exact this
  -- `(m - k) ^ k * (4 M) ≤ m ^ k`
  have hjm : (0 : ℝ) ≤ (m : ℝ) - k := by
    have : (k : ℝ) ≤ m := by exact_mod_cast hkm
    linarith
  have h1 : ((m : ℝ) - k) / m ≤ Real.exp (-(k / m)) := by
    have := Real.add_one_le_exp (-((k : ℝ) / m))
    have e : ((m : ℝ) - k) / m = -((k : ℝ) / m) + 1 := by field_simp; ring
    rw [e]; exact this
  have h2 : (((m : ℝ) - k) / m) ^ k ≤ Real.exp (-((k : ℝ) ^ 2 / m)) := by
    refine (pow_le_pow_left₀ (div_nonneg hjm hmR.le) h1 k).trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h3 : (4 * M : ℝ) ≤ Real.exp ((k : ℝ) ^ 2 / m) := by
    have hpos : (0 : ℝ) < 4 * M := by positivity
    rw [← Real.exp_log hpos]
    apply Real.exp_le_exp.2
    rw [le_div_iff₀ hmR]
    linarith
  have h4 : ((m : ℝ) - k) ^ k * (4 * M) ≤ (m : ℝ) ^ k := by
    have h5 : (((m : ℝ) - k) / m) ^ k * (4 * M) ≤ 1 := by
      calc (((m : ℝ) - k) / m) ^ k * (4 * M)
          ≤ Real.exp (-((k : ℝ) ^ 2 / m)) * Real.exp ((k : ℝ) ^ 2 / m) :=
            mul_le_mul h2 h3 (by positivity) (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    rw [div_pow, div_mul_eq_mul_div, div_le_one (by positivity)] at h5
    exact h5
  have hBR : (0 : ℝ) ≤ (m.choose k : ℝ) * (l : ℝ) ^ k := by positivity
  have h6 : (4 * M * (d + k).choose k : ℝ) * (m : ℝ) ^ k
      ≤ ((m.choose k : ℝ) * (l : ℝ) ^ k) * (m : ℝ) ^ k := by
    calc (4 * M * (d + k).choose k : ℝ) * (m : ℝ) ^ k
        = (4 * M) * (((d + k).choose k : ℝ) * (m : ℝ) ^ k) := by ring
      _ ≤ (4 * M) * ((m.choose k : ℝ) * (l : ℝ) ^ k * ((m : ℝ) - k) ^ k) :=
          mul_le_mul_of_nonneg_left hNR (by positivity)
      _ = ((m.choose k : ℝ) * (l : ℝ) ^ k) * (((m : ℝ) - k) ^ k * (4 * M)) := by ring
      _ ≤ ((m.choose k : ℝ) * (l : ℝ) ^ k) * (m : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left h4 hBR
  have h7 : (4 * M * (d + k).choose k : ℝ) ≤ (m.choose k : ℝ) * (l : ℝ) ^ k :=
    le_of_mul_le_mul_right h6 (by positivity)
  have h8 : 4 * M * (d + k).choose k ≤ m.choose k * l ^ k := by exact_mod_cast h7
  have h9 : 4 * (M * (d + k).choose k) ≤ m.choose k * l ^ k := by rw [← mul_assoc]; exact h8
  omega

/-! ### The common kernel -/

/-- The counting core of Lemma 6.4 of arXiv:2609.23015. Let `k ≤ m`, `1 ≤ l` and
`m * log (4 M) ≤ k ^ 2`. Given `M` affine substitutions of the `m * l` bit variables, the
`j`-th into `d j` variables with `d j + 3 * l * (k + 1) + 1 ≤ m * l`, some nonzero row-linear
polynomial of degree at most `k` is sent to the zero polynomial by all of them. -/
theorem exists_rowLinear_aeval_eq_zero {m l k M : ℕ} (hl : 1 ≤ l) (hkm : k ≤ m)
    (hlog : (m : ℝ) * Real.log (4 * M) ≤ (k : ℝ) ^ 2)
    (d : Fin M → ℕ) (hd : ∀ j, d j + 3 * l * (k + 1) + 1 ≤ m * l)
    (φ : ∀ j, Fin m × Fin l → MvPolynomial (Fin (d j)) (ZMod 2))
    (hφ : ∀ j x, (φ j x).totalDegree ≤ 1) :
    ∃ f : MvPolynomial (Fin m × Fin l) (ZMod 2),
      f ∈ rowLinear m l k ∧ f ≠ 0 ∧ ∀ j, aeval (φ j) f = 0 := by
  have hsum : ∑ j, (d j + k).choose k < finrank (ZMod 2) (rowLinear m l k) := by
    refine lt_of_lt_of_le ?_ (le_finrank_rowLinear m l k)
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simpa using Nat.mul_pos (Nat.choose_pos hkm) (pow_pos hl k)
    · -- compare every summand with the largest admissible number of free variables
      obtain ⟨d0, hd0, hmax⟩ : ∃ d0, d0 + 3 * l * (k + 1) + 1 ≤ m * l ∧ ∀ j, d j ≤ d0 := by
        refine ⟨m * l - (3 * l * (k + 1) + 1), ?_, fun j => ?_⟩
        · have := hd ⟨0, hM⟩
          omega
        · have := hd j
          omega
      refine lt_of_le_of_lt ?_ (mul_choose_lt (M := M) hl hkm hlog hd0)
      calc ∑ j, (d j + k).choose k ≤ ∑ _j : Fin M, (d0 + k).choose k :=
            Finset.sum_le_sum fun j _ => Nat.choose_le_choose k (by have := hmax j; omega)
        _ = M * (d0 + k).choose k := by simp
  obtain ⟨v, hv, hzero⟩ := exists_ne_zero_forall_eq_zero
    (fun j => (aeval (φ j)).toLinearMap ∘ₗ (rowLinear m l k).subtype)
    (fun j => (d j + k).choose k)
    (fun j => finrank_range_aeval_rowLinear_le (φ j) (hφ j)) hsum
  exact ⟨v.1, v.2, fun h => hv (Subtype.ext h), fun j => hzero j⟩

/-- Lemma 6.4 of arXiv:2609.23015 for flats given by an affine parametrisation. In addition to
`exists_rowLinear_aeval_eq_zero`, let `ι j` name, for each of the `d j` parameters, a bit
variable. Then the common kernel element `f` is, for every `j`, a combination of the
polynomials `X x - (φ j x read in the variables ι j)` with cofactors of degree at most
`k - 1`. -/
theorem exists_rowLinear_eq_sum_mul {m l k M : ℕ} (hl : 1 ≤ l) (hkm : k ≤ m)
    (hlog : (m : ℝ) * Real.log (4 * M) ≤ (k : ℝ) ^ 2)
    (d : Fin M → ℕ) (hd : ∀ j, d j + 3 * l * (k + 1) + 1 ≤ m * l)
    (φ : ∀ j, Fin m × Fin l → MvPolynomial (Fin (d j)) (ZMod 2))
    (hφ : ∀ j x, (φ j x).totalDegree ≤ 1)
    (ι : ∀ j, Fin (d j) → Fin m × Fin l) :
    ∃ f : MvPolynomial (Fin m × Fin l) (ZMod 2),
      f ∈ rowLinear m l k ∧ f ≠ 0 ∧ ∀ j,
        ∃ a : Fin m × Fin l → MvPolynomial (Fin m × Fin l) (ZMod 2),
          f = ∑ x, a x * (X x - rename (ι j) (φ j x)) ∧ ∀ x, (a x).totalDegree ≤ k - 1 := by
  obtain ⟨f, hf, hf0, hzero⟩ := exists_rowLinear_aeval_eq_zero hl hkm hlog d hd φ hφ
  refine ⟨f, hf, hf0, fun j => ?_⟩
  have hcomp : aeval (fun x => rename (ι j) (φ j x))
      = ((rename (ι j)).comp (aeval (φ j)) :
          MvPolynomial (Fin m × Fin l) (ZMod 2) →ₐ[ZMod 2] _) := by
    apply algHom_ext
    intro x
    simp
  have hker : aeval (fun x => rename (ι j) (φ j x)) f = 0 := by
    rw [hcomp, AlgHom.comp_apply, hzero j, map_zero]
  obtain ⟨a, ha, hdeg⟩ := exists_cofactors (fun x => rename (ι j) (φ j x))
    (fun x => (totalDegree_rename_le _ _).trans (hφ j x)) f k
    (totalDegree_le_of_mem_rowLinear hf)
  rw [hker, sub_zero] at ha
  exact ⟨a, ha, hdeg⟩

end PEqualNP.ProofComplexity.Helpers
