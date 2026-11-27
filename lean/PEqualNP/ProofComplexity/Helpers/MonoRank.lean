import Mathlib

/-!
# Monotonicity of a normalised rank for subspaces closed under variable multiplication

Source of the statement: arXiv:2610.00837 (unrefereed), Lemma 4.1. The proofs here are ours.

Let `Z` be a linear subspace of the polynomial ring in finitely many variables over a field,
and let `c k` be the dimension of the image of the polynomials of total degree at most `k` in
the quotient by `Z` (equivalently the codimension of `Z ∩ V_k` in `V_k`). Suppose that, up to a
degree bound `K`,

* multiplying a member of `Z` of degree below `K` by a variable stays in `Z`, and
* every multiple `x^d * (X i ^ 2 - X i)` of a Boolean axiom of degree at most `K` lies in `Z`.

Then `c (k + 1) * N k ≤ c k * N (k + 1)` whenever `k + 1 ≤ K`, where `N k` counts the
multilinear monomials of degree at most `k`. So `c k / N k` is nonincreasing on `0 .. K`.

Three parts.

* Part A (sets only): in a down-closed family of subsets of a finite type, the slice sizes
  `b j` satisfy `(j + 1) * b (j + 1) ≤ (n - j) * b j` (from the local LYM inequality of
  Mathlib), hence `b j / choose n j` is nonincreasing, hence so are the ratios of partial sums.
* Part B (monomial order): for any monomial order and any subspace `Z`, the monomials that are
  not leading monomials of nonzero members of `Z` are linearly independent modulo `Z`, and
  every polynomial is congruent modulo `Z` to a combination of such monomials that are no
  larger than its own leading monomial. With the degree lexicographic order this gives a basis
  of the image of `V_k`, the same monomials for every `k`, cut off by degree. Under the two
  closure hypotheses these monomials are multilinear and closed under removing a variable up
  to degree `K`.
* Part C: the combination.

The second hypothesis cannot be dropped: for `Z = 0` in one variable, `c = 1, 2, 3` while
`N = 1, 2, 2`, and `3 * 2 > 2 * 2`.
-/

namespace PEqualNP.ProofComplexity.Helpers
namespace MonoRank

open Finset MvPolynomial
open scoped FinsetFamily MonomialOrder

/-! ## Part A: down-closed set families -/

section Combinatorial

variable {σ : Type*} [DecidableEq σ] [Fintype σ]

/-- Double counting between consecutive slices of a down-closed family. -/
theorem slice_succ_mul_le (𝒜 : Finset (Finset σ)) (h : IsLowerSet (𝒜 : Set (Finset σ)))
    (j : ℕ) :
    (j + 1) * #(𝒜 # (j + 1)) ≤ (Fintype.card σ - j) * #(𝒜 # j) := by
  rcases Nat.lt_or_ge (Fintype.card σ) (j + 1) with hj | hj
  · have h0 : 𝒜 # (j + 1) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro s hs
      have h1 := (Finset.mem_slice.1 hs).2
      have h2 := Finset.card_le_univ s
      omega
    simp [h0]
  · have h1 := Finset.local_lubell_yamamoto_meshalkin_inequality_mul
      (Finset.sized_slice (𝒜 := 𝒜) (r := j + 1))
    have hsub : ∂ (𝒜 # (j + 1)) ⊆ 𝒜 # j := by
      intro t ht
      obtain ⟨s, hs, a, ha, rfl⟩ := Finset.mem_shadow_iff.1 ht
      rw [Finset.mem_slice] at hs ⊢
      refine ⟨h (Finset.erase_subset a s) (Finset.mem_coe.2 hs.1), ?_⟩
      rw [Finset.card_erase_of_mem ha, hs.2]
      rfl
    have h2 := Finset.card_le_card hsub
    have h3 : Fintype.card σ - (j + 1) + 1 = Fintype.card σ - j := by omega
    rw [h3] at h1
    calc (j + 1) * #(𝒜 # (j + 1)) = #(𝒜 # (j + 1)) * (j + 1) := Nat.mul_comm _ _
      _ ≤ #(∂ (𝒜 # (j + 1))) * (Fintype.card σ - j) := h1
      _ ≤ #(𝒜 # j) * (Fintype.card σ - j) := Nat.mul_le_mul_right _ h2
      _ = (Fintype.card σ - j) * #(𝒜 # j) := Nat.mul_comm _ _

/-- The slice densities `b j / choose n j` of a down-closed family are nonincreasing. -/
theorem slice_succ_mul_choose_le (𝒜 : Finset (Finset σ))
    (h : IsLowerSet (𝒜 : Set (Finset σ))) (j : ℕ) :
    #(𝒜 # (j + 1)) * (Fintype.card σ).choose j
      ≤ #(𝒜 # j) * (Fintype.card σ).choose (j + 1) := by
  have h1 := slice_succ_mul_le 𝒜 h j
  have h2 := Nat.choose_succ_right_eq (Fintype.card σ) j
  refine Nat.le_of_mul_le_mul_left (?_ : (j + 1) * _ ≤ (j + 1) * _) (Nat.succ_pos j)
  calc (j + 1) * (#(𝒜 # (j + 1)) * (Fintype.card σ).choose j)
      = ((j + 1) * #(𝒜 # (j + 1))) * (Fintype.card σ).choose j := by ring
    _ ≤ ((Fintype.card σ - j) * #(𝒜 # j)) * (Fintype.card σ).choose j :=
        Nat.mul_le_mul_right _ h1
    _ = #(𝒜 # j) * ((Fintype.card σ).choose j * (Fintype.card σ - j)) := by ring
    _ = #(𝒜 # j) * ((Fintype.card σ).choose (j + 1) * (j + 1)) := by rw [h2]
    _ = (j + 1) * (#(𝒜 # j) * (Fintype.card σ).choose (j + 1)) := by ring

omit [DecidableEq σ] [Fintype σ] in
/-- Mediant step: if `b j / c j` is nonincreasing on `0 .. k + 1` (with `c` positive on
`0 .. k`), then the ratio of partial sums does not increase from `k` to `k + 1`. -/
theorem mediant_partial_sums (b c : ℕ → ℕ) (k : ℕ) (hc : ∀ j ≤ k, 0 < c j)
    (h : ∀ j ≤ k, b (j + 1) * c j ≤ b j * c (j + 1)) :
    (∑ j ∈ range (k + 2), b j) * (∑ j ∈ range (k + 1), c j)
      ≤ (∑ j ∈ range (k + 1), b j) * (∑ j ∈ range (k + 2), c j) := by
  have key : ∀ l, l ≤ k + 1 → ∀ j ≤ l, b l * c j ≤ b j * c l := by
    intro l
    induction l with
    | zero =>
      intro _ j hj
      obtain rfl : j = 0 := by omega
      exact le_rfl
    | succ l ih =>
      intro hl j hj
      rcases Nat.eq_or_lt_of_le hj with rfl | hj'
      · exact le_rfl
      have i1 := ih (by omega) j (by omega)
      have i2 := h l (by omega)
      have hp := hc l (by omega)
      refine Nat.le_of_mul_le_mul_left (?_ : c l * _ ≤ c l * _) hp
      calc c l * (b (l + 1) * c j) = (b (l + 1) * c l) * c j := by ring
        _ ≤ (b l * c (l + 1)) * c j := Nat.mul_le_mul_right _ i2
        _ = (b l * c j) * c (l + 1) := by ring
        _ ≤ (b j * c l) * c (l + 1) := Nat.mul_le_mul_right _ i1
        _ = c l * (b j * c (l + 1)) := by ring
  rw [Finset.sum_range_succ b (k + 1), Finset.sum_range_succ c (k + 1)]
  have h1 : b (k + 1) * ∑ j ∈ range (k + 1), c j ≤ (∑ j ∈ range (k + 1), b j) * c (k + 1) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_le_sum fun j hj =>
      key (k + 1) le_rfl j (by have := Finset.mem_range.1 hj; omega)
  rw [add_mul, mul_add]
  exact Nat.add_le_add_left h1 _

/-- For a down-closed family, the number of members of size at most `k`, divided by the number
of all sets of size at most `k`, does not increase with `k` (cross-multiplied form). -/
theorem downClosed_partial_sums (𝒜 : Finset (Finset σ))
    (h : IsLowerSet (𝒜 : Set (Finset σ))) (k : ℕ) :
    (∑ j ∈ range (k + 2), #(𝒜 # j)) * (∑ j ∈ range (k + 1), (Fintype.card σ).choose j)
      ≤ (∑ j ∈ range (k + 1), #(𝒜 # j))
          * (∑ j ∈ range (k + 2), (Fintype.card σ).choose j) := by
  rcases Nat.lt_or_ge (Fintype.card σ) (k + 1) with hk | hk
  · have h0 : #(𝒜 # (k + 1)) = 0 := by
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_of_forall_notMem
      intro s hs
      have h1 := (Finset.mem_slice.1 hs).2
      have h2 := Finset.card_le_univ s
      omega
    rw [Finset.sum_range_succ (fun j => #(𝒜 # j)) (k + 1), h0, add_zero]
    exact Nat.mul_le_mul_left _
      (Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega)))
  · exact mediant_partial_sums (fun j => #(𝒜 # j)) (fun j => (Fintype.card σ).choose j) k
      (fun j hj => Nat.choose_pos (by omega)) (fun j _ => slice_succ_mul_choose_le 𝒜 h j)

omit [Fintype σ] in
/-- The partial sums of slice sizes count the members of size at most `k`. -/
theorem sum_slice_eq_card_filter (𝒜 : Finset (Finset σ)) (k : ℕ) :
    ∑ j ∈ range (k + 1), #(𝒜 # j) = #(𝒜.filter (fun s => #s ≤ k)) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Finset.card) (t := range (k + 1))
    (fun s hs => Finset.mem_range.2 (by have := (Finset.mem_filter.1 hs).2; omega))]
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 1
  ext s
  have := Finset.mem_range.1 hj
  simp only [Finset.mem_slice, Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, by omega⟩, h2⟩
  · rintro ⟨⟨h1, _⟩, h2⟩
    exact ⟨h1, h2⟩

omit [Fintype σ] in
/-- A family closed under removing one element is down-closed. -/
theorem isLowerSet_of_erase (𝒜 : Finset (Finset σ))
    (h : ∀ s ∈ 𝒜, ∀ a ∈ s, s.erase a ∈ 𝒜) : IsLowerSet (𝒜 : Set (Finset σ)) := by
  intro s t hts hs
  have key : ∀ u : Finset σ, u ⊆ s → s \ u ∈ 𝒜 := by
    intro u
    induction u using Finset.induction_on with
    | empty => intro _; simpa using hs
    | insert a u ha ih =>
      intro hu
      rw [Finset.sdiff_insert]
      refine h _ (ih ((Finset.subset_insert a u).trans hu)) a ?_
      exact Finset.mem_sdiff.2 ⟨hu (Finset.mem_insert_self a u), ha⟩
  have h1 := key (s \ t) Finset.sdiff_subset
  rw [Finset.sdiff_sdiff_eq_self hts] at h1
  exact Finset.mem_coe.2 h1

end Combinatorial

/-! ## Part B: standard monomials -/

section Algebraic

variable {σ : Type*} {F : Type*} [Field F]

/-- The exponents that occur as leading exponents of nonzero members of `Z`. -/
def leadSet (m : MonomialOrder σ) (Z : Submodule F (MvPolynomial σ F)) : Set (σ →₀ ℕ) :=
  {d | ∃ q ∈ Z, q ≠ 0 ∧ m.degree q = d}

/-- Two polynomials with the same leading exponent and the same leading coefficient: the
difference is zero or has a strictly smaller leading exponent. -/
theorem degree_sub_lt_of_lead_eq (m : MonomialOrder σ) {f g : MvPolynomial σ F}
    (hd : m.degree f = m.degree g) (hc : m.leadingCoeff f = m.leadingCoeff g)
    (hne : f - g ≠ 0) : m.degree (f - g) ≺[m] m.degree f := by
  apply lt_of_le_of_ne
  · have h1 := m.degree_sub_le (f := f) (g := g)
    rw [← hd, sup_idem] at h1
    exact h1
  · intro h'
    have h'' : m.degree (f - g) = m.degree f := m.toSyn.injective h'
    have h2 := m.degree_mem_support hne
    rw [h'', mem_support_iff, coeff_sub] at h2
    apply h2
    have h3 : g.coeff (m.degree f) = m.leadingCoeff g := by rw [hd]; rfl
    rw [h3, ← hc]
    exact sub_self _

/-- The monomials outside the leading set are linearly independent modulo `Z`. -/
theorem linearIndependent_std (m : MonomialOrder σ) (Z : Submodule F (MvPolynomial σ F)) :
    LinearIndependent F
      (fun d : ((leadSet m Z)ᶜ : Set (σ →₀ ℕ)) => Z.mkQ (monomial (d : σ →₀ ℕ) (1 : F))) := by
  have hli : LinearIndependent F
      (fun d : ((leadSet m Z)ᶜ : Set (σ →₀ ℕ)) => monomial (d : σ →₀ ℕ) (1 : F)) := by
    have := (MvPolynomial.basisMonomials σ F).linearIndependent.comp
      (fun d : ((leadSet m Z)ᶜ : Set (σ →₀ ℕ)) => (d : σ →₀ ℕ)) Subtype.val_injective
    simpa [Function.comp_def] using this
  refine hli.map ?_
  rw [Submodule.ker_mkQ, Submodule.disjoint_def]
  intro p hp hZ
  by_contra hne
  have hsupp : p ∈ restrictSupport F ((leadSet m Z)ᶜ : Set (σ →₀ ℕ)) := by
    rw [restrictSupport_eq_span, Set.image_eq_range]
    exact hp
  have h1 : m.degree p ∈ ((leadSet m Z)ᶜ : Set (σ →₀ ℕ)) :=
    ((mem_restrictSupport_iff F).1 hsupp) (Finset.mem_coe.2 (m.degree_mem_support hne))
  exact h1 ⟨p, hZ, hne, rfl⟩

/-- Reduction: modulo `Z` every polynomial is a combination of monomials outside the leading
set that are no larger than its own leading monomial. -/
theorem mkQ_mem_span_std (m : MonomialOrder σ) (Z : Submodule F (MvPolynomial σ F))
    (p : MvPolynomial σ F) :
    Z.mkQ p ∈ Submodule.span F ((fun d : σ →₀ ℕ => Z.mkQ (monomial d (1 : F))) ''
      {d | d ∉ leadSet m Z ∧ d ≼[m] m.degree p}) := by
  suffices H : ∀ a : m.syn, ∀ p : MvPolynomial σ F, m.toSyn (m.degree p) = a →
      Z.mkQ p ∈ Submodule.span F ((fun d : σ →₀ ℕ => Z.mkQ (monomial d (1 : F))) ''
        {d | d ∉ leadSet m Z ∧ d ≼[m] m.degree p}) from H _ p rfl
  intro a
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    intro p hpa
    by_cases hp : p = 0
    · rw [hp, map_zero]
      exact Submodule.zero_mem _
    have hc : m.leadingCoeff p ≠ 0 := m.leadingCoeff_ne_zero_iff.2 hp
    -- a polynomial `g` with the leading data of `p` whose class is already in the span
    obtain ⟨g, hgd, hgc, hgmem⟩ : ∃ g : MvPolynomial σ F, m.degree g = m.degree p ∧
        m.leadingCoeff g = m.leadingCoeff p ∧
        Z.mkQ g ∈ Submodule.span F ((fun d : σ →₀ ℕ => Z.mkQ (monomial d (1 : F))) ''
          {d | d ∉ leadSet m Z ∧ d ≼[m] m.degree p}) := by
      by_cases hd : m.degree p ∈ leadSet m Z
      · obtain ⟨q, hqZ, hq0, hqd⟩ := hd
        have hcq : m.leadingCoeff q ≠ 0 := m.leadingCoeff_ne_zero_iff.2 hq0
        have hr : m.leadingCoeff p / m.leadingCoeff q ≠ 0 := div_ne_zero hc hcq
        have hdeg : m.degree ((m.leadingCoeff p / m.leadingCoeff q) • q) = m.degree p := by
          rw [m.degree_smul_of_isRegular (IsRegular.of_ne_zero hr), hqd]
        refine ⟨(m.leadingCoeff p / m.leadingCoeff q) • q, hdeg, ?_, ?_⟩
        · show ((m.leadingCoeff p / m.leadingCoeff q) • q).coeff
            (m.degree ((m.leadingCoeff p / m.leadingCoeff q) • q)) = _
          rw [hdeg, coeff_smul, smul_eq_mul, ← hqd]
          exact div_mul_cancel₀ _ hcq
        · have : Z.mkQ ((m.leadingCoeff p / m.leadingCoeff q) • q) = 0 := by
            rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
            exact Z.smul_mem _ hqZ
          rw [this]
          exact Submodule.zero_mem _
      · classical
        refine ⟨monomial (m.degree p) (m.leadingCoeff p), ?_, ?_, ?_⟩
        · rw [m.degree_monomial, if_neg hc]
        · exact m.leadingCoeff_monomial _
        · have : monomial (m.degree p) (m.leadingCoeff p)
              = m.leadingCoeff p • monomial (m.degree p) (1 : F) := by
            rw [smul_monomial, smul_eq_mul, mul_one]
          rw [this, map_smul]
          exact Submodule.smul_mem _ _
            (Submodule.subset_span ⟨m.degree p, ⟨hd, le_rfl⟩, rfl⟩)
    have hsplit : Z.mkQ p = Z.mkQ (p - g) + Z.mkQ g := by
      rw [← map_add, sub_add_cancel]
    rw [hsplit]
    refine Submodule.add_mem _ ?_ hgmem
    by_cases hpg : p - g = 0
    · rw [hpg, map_zero]
      exact Submodule.zero_mem _
    have hlt : m.degree (p - g) ≺[m] m.degree p :=
      degree_sub_lt_of_lead_eq m hgd.symm hgc.symm hpg
    have h1 := ih (m.toSyn (m.degree (p - g))) (hpa ▸ hlt) (p - g) rfl
    refine Submodule.span_mono (Set.image_mono ?_) h1
    rintro d ⟨hd1, hd2⟩
    exact ⟨hd1, hd2.trans hlt.le⟩

/-- The rank used below is the dimension of `V / (Z ∩ V)`: the image of a subspace `V` in the
quotient by `Z` has the dimension of `V` modulo the part of `Z` inside `V`. -/
theorem finrank_quotient_comap_eq_finrank_map (Z V : Submodule F (MvPolynomial σ F)) :
    Module.finrank F (V ⧸ Z.comap V.subtype) = Module.finrank F (V.map Z.mkQ) := by
  have h1 : LinearMap.ker (Z.mkQ ∘ₗ V.subtype) = Z.comap V.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have h2 : LinearMap.range (Z.mkQ ∘ₗ V.subtype) = V.map Z.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  exact ((Submodule.quotEquivOfEq _ _ h1.symm).trans
    ((Z.mkQ ∘ₗ V.subtype).quotKerEquivRange.trans (LinearEquiv.ofEq _ _ h2))).finrank_eq

section DegLex

variable [LinearOrder σ] [WellFoundedGT σ]

/-- With the degree lexicographic order, the image of the polynomials of total degree at most
`k` in the quotient by `Z` is spanned by the standard monomials of degree at most `k`. -/
theorem map_restrictTotalDegree_eq_span (Z : Submodule F (MvPolynomial σ F)) (k : ℕ) :
    (restrictTotalDegree σ F k).map Z.mkQ
      = Submodule.span F (Set.range
          (fun d : {d : σ →₀ ℕ // d ∉ leadSet MonomialOrder.degLex Z ∧ d.degree ≤ k} =>
            Z.mkQ (monomial (d : σ →₀ ℕ) (1 : F)))) := by
  apply le_antisymm
  · rintro _ ⟨p, hp, rfl⟩
    have hp' : p.totalDegree ≤ k := (mem_restrictTotalDegree σ k p).1 hp
    refine Submodule.span_mono ?_ (mkQ_mem_span_std MonomialOrder.degLex Z p)
    rintro _ ⟨d, ⟨hd1, hd2⟩, rfl⟩
    have h1 : d.degree ≤ (MonomialOrder.degLex.degree p).degree :=
      Finsupp.DegLex.monotone_degree hd2
    rw [degree_degLexDegree] at h1
    exact ⟨⟨d, hd1, h1.trans hp'⟩, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨⟨d, hd1, hd2⟩, rfl⟩
    refine ⟨monomial d 1, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_restrictTotalDegree, totalDegree_monomial _ one_ne_zero]
    exact hd2

/-- The dimension of the image of `V_k` modulo `Z` is the number of standard monomials of
degree at most `k`. No hypothesis on `Z` is needed. -/
theorem finrank_map_restrictTotalDegree (Z : Submodule F (MvPolynomial σ F)) (k : ℕ) :
    Module.finrank F ((restrictTotalDegree σ F k).map Z.mkQ)
      = Set.ncard {d : σ →₀ ℕ | d ∉ leadSet MonomialOrder.degLex Z ∧ d.degree ≤ k} := by
  have hli : LinearIndependent F
      (fun d : {d : σ →₀ ℕ // d ∉ leadSet MonomialOrder.degLex Z ∧ d.degree ≤ k} =>
        Z.mkQ (monomial (d : σ →₀ ℕ) (1 : F))) := by
    have := (linearIndependent_std MonomialOrder.degLex Z).comp
      (fun d : {d : σ →₀ ℕ // d ∉ leadSet MonomialOrder.degLex Z ∧ d.degree ≤ k} =>
        (⟨d.1, d.2.1⟩ : ((leadSet MonomialOrder.degLex Z)ᶜ : Set (σ →₀ ℕ))))
      (by intro a b hab; simp only [Subtype.mk.injEq] at hab; exact Subtype.ext hab)
    simpa [Function.comp_def] using this
  rw [map_restrictTotalDegree_eq_span, Module.finrank_eq_nat_card_basis (Module.Basis.span hli)]
  rfl

/-- The multilinear exponent vector of a set of variables. -/
noncomputable def ind (s : Finset σ) : σ →₀ ℕ := ∑ i ∈ s, Finsupp.single i 1

omit [WellFoundedGT σ] in
theorem ind_apply (s : Finset σ) (i : σ) : ind s i = if i ∈ s then 1 else 0 := by
  classical
  simp [ind, Finsupp.single_apply]

omit [WellFoundedGT σ] in
theorem ind_degree (s : Finset σ) : (ind s).degree = #s := by
  simp [ind]

omit [WellFoundedGT σ] in
theorem ind_injective : Function.Injective (ind : Finset σ → σ →₀ ℕ) := by
  intro s t h
  ext i
  have h1 := DFunLike.congr_fun h i
  rw [ind_apply, ind_apply] at h1
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp_all

omit [WellFoundedGT σ] in
theorem ind_support_of_le_one (d : σ →₀ ℕ) (h : ∀ i, d i ≤ 1) : ind d.support = d := by
  ext i
  rw [ind_apply]
  have := h i
  by_cases hi : i ∈ d.support
  · rw [if_pos hi]
    have := Finsupp.mem_support_iff.1 hi
    omega
  · rw [if_neg hi]
    exact (Finsupp.notMem_support_iff.1 hi).symm

variable (Z : Submodule F (MvPolynomial σ F)) (K : ℕ)

/-- Standard monomials of degree at most `K` are multilinear when `Z` contains the monomial
multiples of the Boolean axioms up to degree `K`. -/
theorem std_le_one
    (hB : ∀ (d : σ →₀ ℕ) (i : σ), d.degree + 2 ≤ K →
      monomial d (1 : F) * (X i ^ 2 - X i) ∈ Z)
    (d : σ →₀ ℕ) (hd : d ∉ leadSet MonomialOrder.degLex Z) (hK : d.degree ≤ K) (i : σ) :
    d i ≤ 1 := by
  classical
  by_contra hi
  apply hd
  set e : σ →₀ ℕ := d - Finsupp.single i 2 with he
  have hde : d = e + Finsupp.single i 2 := by
    ext j
    by_cases hj : j = i
    · subst hj; simp [he]; omega
    · simp [he, Finsupp.single_apply, Ne.symm hj]
  have hdeg : e.degree + 2 = d.degree := by
    rw [hde, map_add, Finsupp.degree_single]
  have hq : monomial e (1 : F) * (X i ^ 2 - X i)
      = monomial (e + Finsupp.single i 2) (1 : F) - monomial (e + Finsupp.single i 1) (1 : F) := by
    rw [mul_sub, X_pow_eq_monomial, monomial_mul, X, monomial_mul, mul_one]
  have hlt : MonomialOrder.degLex.degree (monomial (e + Finsupp.single i 1) (1 : F))
      ≺[MonomialOrder.degLex]
      MonomialOrder.degLex.degree (monomial (e + Finsupp.single i 2) (1 : F)) := by
    rw [MonomialOrder.degree_monomial, MonomialOrder.degree_monomial, if_neg one_ne_zero,
      if_neg one_ne_zero]
    apply MonomialOrder.degLex.toSyn_strictMono
    apply lt_of_le_of_ne
    · exact add_le_add le_rfl (Finsupp.single_le_single.2 (show (1 : ℕ) ≤ 2 by omega))
    · intro h
      have := DFunLike.congr_fun h i
      simp at this
  refine ⟨monomial e (1 : F) * (X i ^ 2 - X i), hB e i (by omega), ?_, ?_⟩
  · rw [hq]
    intro h0
    rw [sub_eq_zero] at h0
    rw [h0] at hlt
    exact lt_irrefl _ hlt
  · rw [hq, MonomialOrder.degree_sub_of_lt hlt, MonomialOrder.degree_monomial,
      if_neg one_ne_zero, ← hde]

/-- Standard monomials of degree at most `K` stay standard after removing one variable, when
`Z` is closed under multiplication by variables below degree `K`. -/
theorem std_sub_single
    (hX : ∀ p ∈ Z, p.totalDegree < K → ∀ i : σ, X i * p ∈ Z)
    (d : σ →₀ ℕ) (hd : d ∉ leadSet MonomialOrder.degLex Z) (hK : d.degree ≤ K) (i : σ)
    (hi : 1 ≤ d i) : d - Finsupp.single i 1 ∉ leadSet MonomialOrder.degLex Z := by
  classical
  rintro ⟨q, hqZ, hq0, hqd⟩
  apply hd
  have hde : d = Finsupp.single i 1 + (d - Finsupp.single i 1) := by
    ext j
    by_cases hj : j = i
    · subst hj; simp; omega
    · simp [Finsupp.single_apply, Ne.symm hj]
  have hdeg : 1 + (d - Finsupp.single i 1).degree = d.degree := by
    conv_rhs => rw [hde, map_add, Finsupp.degree_single]
  have hqt : q.totalDegree < K := by
    rw [← degree_degLexDegree, hqd]
    omega
  have hXne : (X i : MvPolynomial σ F) ≠ 0 := X_ne_zero i
  refine ⟨X i * q, hX q hqZ hqt i, mul_ne_zero hXne hq0, ?_⟩
  rw [MonomialOrder.degree_mul hXne hq0, MonomialOrder.degree_X, hqd, ← hde]

end DegLex

end Algebraic

/-! ## Part C: the combined statement -/

section Combined

variable {σ : Type*} [Fintype σ] {F : Type*} [Field F]

/-- **Standard monomial basis.** Under the two closure hypotheses up to degree `K`, there is
one down-closed family of sets of variables such that, for every `k ≤ K`, the dimension of the
image of the degree at most `k` polynomials modulo `Z` is the number of members of the family
of size at most `k`. -/
theorem exists_downClosed_family [DecidableEq σ] (Z : Submodule F (MvPolynomial σ F)) (K : ℕ)
    (hX : ∀ p ∈ Z, p.totalDegree < K → ∀ i : σ, X i * p ∈ Z)
    (hB : ∀ (d : σ →₀ ℕ) (i : σ), d.degree + 2 ≤ K →
      monomial d (1 : F) * (X i ^ 2 - X i) ∈ Z) :
    ∃ 𝒜 : Finset (Finset σ), IsLowerSet (𝒜 : Set (Finset σ)) ∧ ∀ k ≤ K,
      Module.finrank F ((restrictTotalDegree σ F k).map Z.mkQ)
        = ∑ j ∈ range (k + 1), #(𝒜 # j) := by
  classical
  letI : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  set L := leadSet (F := F) MonomialOrder.degLex Z with hL
  refine ⟨Finset.univ.filter (fun s => ind s ∉ L ∧ #s ≤ K), ?_, ?_⟩
  · apply isLowerSet_of_erase
    intro s hs a ha
    rw [Finset.mem_filter] at hs ⊢
    obtain ⟨-, hs1, hs2⟩ := hs
    refine ⟨Finset.mem_univ _, ?_, (Finset.card_erase_le).trans hs2⟩
    have h1 : ind (s.erase a) = ind s - Finsupp.single a 1 := by
      ext j
      rw [Finsupp.tsub_apply, ind_apply, ind_apply, Finsupp.single_apply]
      by_cases hj : a = j
      · subst hj; simp [ha]
      · simp [hj, Ne.symm hj]
    rw [h1]
    exact std_sub_single Z K hX (ind s) hs1 (by rw [ind_degree]; exact hs2) a
      (by rw [ind_apply, if_pos ha])
  · intro k hk
    rw [finrank_map_restrictTotalDegree, sum_slice_eq_card_filter, ← Set.ncard_coe_finset,
      ← Set.ncard_image_of_injective _ ind_injective]
    congr 1
    ext d
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hd1, hd2⟩
      have h1 : ind d.support = d :=
        ind_support_of_le_one d (std_le_one Z K hB d hd1 (hd2.trans hk))
      have h2 : #d.support = d.degree := by rw [← ind_degree, h1]
      refine ⟨d.support, ⟨⟨?_, ?_⟩, ?_⟩, h1⟩
      · rw [h1]; exact hd1
      · omega
      · omega
    · rintro ⟨s, ⟨⟨hs1, _⟩, hs3⟩, rfl⟩
      exact ⟨hs1, by rw [ind_degree]; exact hs3⟩

/-- **Monotonicity of the normalised rank.** With `c k` the dimension of the image of the
degree at most `k` polynomials modulo `Z` and `N k` the number of multilinear monomials of
degree at most `k`: `c (k + 1) * N k ≤ c k * N (k + 1)` for `k + 1 ≤ K`. -/
theorem rank_ratio_monotone (Z : Submodule F (MvPolynomial σ F)) (K : ℕ)
    (hX : ∀ p ∈ Z, p.totalDegree < K → ∀ i : σ, X i * p ∈ Z)
    (hB : ∀ (d : σ →₀ ℕ) (i : σ), d.degree + 2 ≤ K →
      monomial d (1 : F) * (X i ^ 2 - X i) ∈ Z)
    (k : ℕ) (hk : k + 1 ≤ K) :
    Module.finrank F ((restrictTotalDegree σ F (k + 1)).map Z.mkQ)
        * (∑ j ∈ range (k + 1), (Fintype.card σ).choose j)
      ≤ Module.finrank F ((restrictTotalDegree σ F k).map Z.mkQ)
        * (∑ j ∈ range (k + 2), (Fintype.card σ).choose j) := by
  classical
  obtain ⟨𝒜, h𝒜, hc⟩ := exists_downClosed_family Z K hX hB
  rw [hc (k + 1) hk, hc k (by omega)]
  exact downClosed_partial_sums 𝒜 h𝒜 k

end Combined

end MonoRank
end PEqualNP.ProofComplexity.Helpers
