import PEqualNP.ProofComplexity.Helpers.DegSizePlan
import PEqualNP.ProofComplexity.Helpers.MonoRank
import PEqualNP.ProofComplexity.Helpers.RankRetention

/-!
# Two links of L-pcx-042: monotone normalised rank and rank retention, on `errRank`

Both statements are copied from `Helpers/DegSizePlan.lean`.

* `monoRank_used` (Lemma 4.1 as used) is `MonoRank.rank_ratio_monotone` applied to the space
  `annih C (zMul P G)` of all `f` with `m * f ∈ C` for every multiplier `m`, iterated from
  one step to `k ≤ k'`.
* `rankRetention_used` (Corollary 3.5 at `p = 2`, affine inputs) is
  `rank_retention_closure` applied to the inputs indexed by the subtype of `G` and the
  multipliers indexed by the subtype of `H`.

Glue proved here: absorption (`absorb`, Lemma A of the plan), the finite dimension of the
polynomials of bounded degree in finitely many variables, the identification of `errRank`
with the rank of any linear map on `polyLE σ k` whose kernel is `errKer` (`errRank_eq_range`),
and the normal form of a polynomial of degree at most one (`exists_affine`).
-/

namespace PEqualNP.ProofComplexity.DegSizeRank

open MvPolynomial Module PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.DegSizePlan

section Glue

variable {σ : Type}

/-- A nonzero exponent vector is a variable plus an exponent vector of degree one less. -/
theorem exists_single_add (d : σ →₀ ℕ) (hd : d ≠ 0) :
    ∃ (i : σ) (e : σ →₀ ℕ), d = Finsupp.single i 1 + e ∧ e.degree + 1 = d.degree := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
    by_contra h
    push Not at h
    exact hd (Finsupp.ext h)
  have hde : d = Finsupp.single i 1 + (d - Finsupp.single i 1) := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp
      omega
    · simp [Ne.symm hj]
  refine ⟨i, d - Finsupp.single i 1, hde, ?_⟩
  have h := congrArg Finsupp.degree hde
  rw [map_add, Finsupp.degree_single] at h
  omega

theorem totalDegree_monomial_one (d : σ →₀ ℕ) :
    (monomial d (1 : ZMod 2)).totalDegree = d.degree := by
  rw [totalDegree_monomial _ one_ne_zero]
  rfl

theorem bool_totalDegree_le (v : σ) :
    (X v * X v + X v : MvPolynomial σ (ZMod 2)).totalDegree ≤ 2 := by
  refine (totalDegree_add _ _).trans (max_le ((totalDegree_mul _ _).trans ?_) ?_)
  · rw [totalDegree_X]
  · rw [totalDegree_X]
    omega

/-- Absorption for one monomial. -/
theorem monomial_mul_mem {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ}
    (hC : DegClosed C D) :
    ∀ (n : ℕ) (d : σ →₀ ℕ), d.degree = n → ∀ f ∈ C, n + f.totalDegree ≤ D →
      monomial d (1 : ZMod 2) * f ∈ C := by
  intro n
  induction n with
  | zero =>
    intro d hd f hf _
    have h0 : d = 0 := by
      by_contra hne
      obtain ⟨i, e, -, he⟩ := exists_single_add d hne
      omega
    subst h0
    simpa using hf
  | succ n ih =>
    intro d hd f hf hdeg
    have hne : d ≠ 0 := by
      rintro rfl
      simp at hd
    obtain ⟨i, e, hde, he⟩ := exists_single_add d hne
    have h1 := ih e (by omega) f hf (by omega)
    have h2 : (monomial e (1 : ZMod 2) * f).totalDegree + 1 ≤ D := by
      have h3 := totalDegree_mul (monomial e (1 : ZMod 2)) f
      have h4 := totalDegree_monomial_one e
      omega
    have h5 := hC.mulX i _ h1 h2
    have e5 : monomial d (1 : ZMod 2) * f = X i * (monomial e 1 * f) := by
      rw [hde, ← mul_assoc]
      congr 1
      rw [X, monomial_mul_monomial, mul_one]
    rw [e5]
    exact h5

/-- Lemma A (absorption): a member of the closure may be multiplied by any polynomial within
the degree budget. -/
theorem absorb {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ} (hC : DegClosed C D)
    (f g : MvPolynomial σ (ZMod 2)) (hf : f ∈ C) (hdeg : g.totalDegree + f.totalDegree ≤ D) :
    g * f ∈ C := by
  have e : g * f = ∑ v ∈ g.support, g.coeff v • (monomial v (1 : ZMod 2) * f) := by
    conv_lhs => rw [g.as_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← smul_mul_assoc, smul_monomial, smul_eq_mul, mul_one]
  rw [e]
  refine C.sum_mem fun v hv => C.smul_mem _ (monomial_mul_mem hC _ v rfl f hf ?_)
  have h1 : v.degree ≤ g.totalDegree := le_totalDegree hv
  omega

/-- Polynomials of bounded degree in finitely many variables form a finite dimensional
space. -/
instance finite_restrictTotalDegree [Finite σ] (k : ℕ) :
    Module.Finite (ZMod 2) ↥(restrictTotalDegree σ (ZMod 2) k) := by
  have hfin : Finite ↥{u : σ →₀ ℕ | (u.sum fun _ e => e) ≤ k} :=
    Set.Finite.to_subtype ((Finsupp.finite_of_degree_le k).subset fun u hu => hu)
  exact Module.Finite.of_basis
    (basisRestrictSupport (ZMod 2) {u : σ →₀ ℕ | (u.sum fun _ e => e) ≤ k})

/-- `errRank` is the rank of any linear map on the polynomials of degree at most `k` whose
kernel is `errKer`. In particular the truncated subtraction in `errRank` loses nothing. -/
theorem errRank_eq_range [Finite σ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (M : Set (MvPolynomial σ (ZMod 2)))
    (k : ℕ) (L : ↥(polyLE σ k) →ₗ[ZMod 2] W)
    (hL : ∀ f : ↥(polyLE σ k), L f = 0 ↔ ∀ m ∈ M, m * (f : MvPolynomial σ (ZMod 2)) ∈ C) :
    finrank (ZMod 2) ↥(LinearMap.range L) = errRank C M k := by
  have hle : errKer C M k ≤ polyLE σ k := inf_le_left
  have hker : LinearMap.ker L = (errKer C M k).comap (polyLE σ k).subtype := by
    ext f
    rw [LinearMap.mem_ker, hL, Submodule.mem_comap, mem_errKer]
    exact ⟨fun h => ⟨(mem_restrictTotalDegree σ k _).1 f.2, h⟩, fun h => h.2⟩
  have r := LinearMap.finrank_range_add_finrank_ker L
  rw [hker, (Submodule.comapSubtypeEquivOfLe hle).finrank_eq] at r
  unfold errRank
  omega

/-- The space of all `f` with `m * f ∈ C` for every multiplier `m ∈ M`. -/
noncomputable def annih (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (M : Set (MvPolynomial σ (ZMod 2))) : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)) :=
  ⨅ m ∈ M, C.comap (LinearMap.mulLeft (ZMod 2) m)

theorem mem_annih {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))}
    {M : Set (MvPolynomial σ (ZMod 2))} {f : MvPolynomial σ (ZMod 2)} :
    f ∈ annih C M ↔ ∀ m ∈ M, m * f ∈ C := by
  simp [annih]

/-- `errRank` is the dimension of the image of the degree at most `k` polynomials modulo
`annih C M`. -/
theorem errRank_eq_map [Finite σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
    (M : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) :
    errRank C M k = finrank (ZMod 2) ↥((polyLE σ k).map (annih C M).mkQ) := by
  rw [← errRank_eq_range C M k ((annih C M).mkQ ∘ₗ (polyLE σ k).subtype)
    (fun f => by simp [mem_annih]), LinearMap.range_comp, Submodule.range_subtype]

/-- From one step to any `k ≤ k'`. -/
theorem iterate_ratio (c N : ℕ → ℕ) (K : ℕ) (hpos : ∀ j, 0 < N j)
    (step : ∀ j, j + 1 ≤ K → c (j + 1) * N j ≤ c j * N (j + 1)) (k : ℕ) :
    ∀ t, k + t ≤ K → c (k + t) * N k ≤ c k * N (k + t) := by
  intro t
  induction t with
  | zero => intro _; exact le_rfl
  | succ t ih =>
    intro hK
    have h1 := ih (by omega)
    have h2 := step (k + t) (by omega)
    have h3 : c (k + t + 1) * N k * N (k + t) ≤ c k * N (k + t + 1) * N (k + t) := by
      calc c (k + t + 1) * N k * N (k + t) = c (k + t + 1) * N (k + t) * N k := by ring
        _ ≤ c (k + t) * N (k + t + 1) * N k := Nat.mul_le_mul_right _ h2
        _ = c (k + t) * N k * N (k + t + 1) := by ring
        _ ≤ c k * N (k + t) * N (k + t + 1) := Nat.mul_le_mul_right _ h1
        _ = c k * N (k + t + 1) * N (k + t) := by ring
    exact Nat.le_of_mul_le_mul_right h3 (hpos (k + t))

/-- A polynomial of degree at most one over the two-element field is `affine a B`. -/
theorem exists_affine [Fintype σ] (g : MvPolynomial σ (ZMod 2)) (hg : g.totalDegree ≤ 1) :
    ∃ (a : ZMod 2) (B : σ → ZMod 2), g = affine a B := by
  classical
  refine ⟨g.coeff 0, fun j => g.coeff (Finsupp.single j 1), ?_⟩
  ext d
  by_cases hd : 1 < d.degree
  · rw [coeff_eq_zero_of_totalDegree_lt (lt_of_le_of_lt hg hd),
      coeff_eq_zero_of_totalDegree_lt (lt_of_le_of_lt (affine_totalDegree_le _ _) hd)]
  · by_cases h0 : d = 0
    · subst h0
      simp [affine, coeff_C_mul]
    · obtain ⟨i, e, hde, he⟩ := exists_single_add d h0
      have he0 : e = 0 := by
        by_contra hne
        obtain ⟨_, _, -, he'⟩ := exists_single_add e hne
        omega
      subst he0
      rw [add_zero] at hde
      subst hde
      have h0' : ¬ ((0 : σ →₀ ℕ) = Finsupp.single i 1) := fun h => h0 h.symm
      simp [affine, coeff_C_mul, coeff_X, Finsupp.single_left_inj, h0']

end Glue

/-- Lemma 4.1 as used: for an approximator `P` of degree at most `a` and affine inputs `G`,
with `a + K + 1 ≤ D`, the normalised rank is nonincreasing in the degree up to `K`. -/
theorem monoRank_used :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D a K : ℕ)
      (P : MvPolynomial σ (ZMod 2)) (G : Set (MvPolynomial σ (ZMod 2))),
      DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ 1) → a + K + 1 ≤ D →
      ∀ k k' : ℕ, k ≤ k' → k' ≤ K →
        errRank C (zMul P G) k' * numMono (Fintype.card σ) k
          ≤ errRank C (zMul P G) k * numMono (Fintype.card σ) k' := by
  intro σ _ C D a K P G hC hP hG hD
  have hmdeg : ∀ m ∈ zMul P G, m.totalDegree ≤ a + 1 := by
    rintro _ ⟨g, hg, rfl⟩
    show (P * g).totalDegree ≤ a + 1
    have h1 := totalDegree_mul P g
    have h2 := hG g hg
    omega
  have hX : ∀ p ∈ annih C (zMul P G), p.totalDegree < K → ∀ i : σ,
      X i * p ∈ annih C (zMul P G) := by
    intro p hp hdeg i
    rw [mem_annih] at hp ⊢
    intro m hm
    have h1 := hC.mulX i (m * p) (hp m hm) (by
      have h2 := totalDegree_mul m p
      have h3 := hmdeg m hm
      omega)
    have e : m * (X i * p) = X i * (m * p) := by ring
    rw [e]
    exact h1
  have hB : ∀ (d : σ →₀ ℕ) (i : σ), d.degree + 2 ≤ K →
      monomial d (1 : ZMod 2) * (X i ^ 2 - X i) ∈ annih C (zMul P G) := by
    intro d i hd
    rw [mem_annih]
    intro m hm
    have e : m * (monomial d (1 : ZMod 2) * (X i ^ 2 - X i))
        = (m * monomial d 1) * (X i * X i + X i) := by
      rw [CharTwo.sub_eq_add]
      ring
    rw [e]
    refine absorb hC _ _ (hC.bool i) ?_
    have h1 := totalDegree_mul m (monomial d (1 : ZMod 2))
    have h2 := totalDegree_monomial_one d
    have h3 := bool_totalDegree_le i
    have h4 := hmdeg m hm
    omega
  have step : ∀ j, j + 1 ≤ K →
      errRank C (zMul P G) (j + 1) * numMono (Fintype.card σ) j
        ≤ errRank C (zMul P G) j * numMono (Fintype.card σ) (j + 1) := by
    intro j hj
    rw [errRank_eq_map, errRank_eq_map]
    exact MonoRank.rank_ratio_monotone (annih C (zMul P G)) K hX hB j hj
  have hpos : ∀ j, 0 < numMono (Fintype.card σ) j := by
    intro j
    unfold numMono
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨0, by simp, by simp⟩
  intro k k' hkk' hk'
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hkk'
  exact iterate_ratio (fun j => errRank C (zMul P G) j) (fun j => numMono (Fintype.card σ) j)
    K hpos step k t hk'

/-- Corollary 3.5 at `p = 2`, affine `G`: rank retention for the multiplication maps. -/
theorem rankRetention_used :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D b k : ℕ)
      (H : Set (MvPolynomial σ (ZMod 2))) (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (∀ h ∈ H, h.totalDegree ≤ b) → (∀ g ∈ G, g.totalDegree ≤ 1) →
      b + k + 2 ≤ D →
      ∃ J : Finset (MvPolynomial σ (ZMod 2)), J ⊆ G ∧
        errRank C (Set.image2 (fun h g => h * g) H ↑G) k
          ≤ 2 * errRank C ((fun h => h * ∑ g ∈ J, g) '' H) k := by
  classical
  intro σ _ C D b k H G hC hH hG hD
  have haff : ∀ i : ↥G, ∃ (a : ZMod 2) (B : σ → ZMod 2),
      (i : MvPolynomial σ (ZMod 2)) = affine a B := fun i => exists_affine _ (hG i i.2)
  choose a B hab using haff
  let hfun : ↥H → MvPolynomial σ (ZMod 2) := fun α => α
  obtain ⟨c, hc⟩ := rank_retention_closure (ι := ↥G) (τ := ↥H) C (polyLE σ k) D k b
    (fun p hp hdeg j => hC.mulX j p hp (by omega))
    (fun p hp j => absorb hC _ _ (hC.bool j) (by
      have h1 := bool_totalDegree_le (σ := σ) j
      omega))
    (fun f hf => (mem_restrictTotalDegree σ k f).1 hf)
    a B hfun (fun α => hH α α.2) hD
  set J : Finset (MvPolynomial σ (ZMod 2)) :=
    (Finset.univ.filter fun i : ↥G => c i = 1).map (Function.Embedding.subtype _) with hJdef
  have hJ : J ⊆ G := by
    intro g hg
    rw [hJdef, Finset.mem_map] at hg
    obtain ⟨i, -, rfl⟩ := hg
    exact i.2
  have hcomb : comb (fun i => affine (a i) (B i)) c = ∑ g ∈ J, g := by
    rw [hJdef, Finset.sum_map, Finset.sum_filter]
    unfold comb
    refine Finset.sum_congr rfl fun i _ => ?_
    show c i • affine (a i) (B i) = if c i = 1 then (i : MvPolynomial σ (ZMod 2)) else 0
    rw [← hab i]
    have hci : c i = 0 ∨ c i = 1 := by
      generalize c i = x
      revert x
      decide
    rcases hci with h | h
    · simp [h]
    · simp [h]
  have e1 : finrank (ZMod 2) ↥(LinearMap.range
        (LinearMap.pi fun i => mulMap C (polyLE σ k) hfun (affine (a i) (B i))))
      = errRank C (Set.image2 (fun h g => h * g) H ↑G) k := by
    refine errRank_eq_range C _ k _ fun f => ?_
    constructor
    · intro hz m hm
      obtain ⟨h, hh, g, hg, rfl⟩ := hm
      have hz' : mulMap C (polyLE σ k) hfun (affine (a ⟨g, hg⟩) (B ⟨g, hg⟩)) f = 0 :=
        congrFun hz ⟨g, hg⟩
      have h1 := (mulMap_apply_eq_zero C (polyLE σ k) hfun _ f).1 hz' ⟨h, hh⟩
      rw [← hab ⟨g, hg⟩] at h1
      have e : h * g * (f : MvPolynomial σ (ZMod 2)) = (f : MvPolynomial σ (ZMod 2)) * g * h := by
        ring
      rw [e]
      exact h1
    · intro hz
      funext i
      show mulMap C (polyLE σ k) hfun (affine (a i) (B i)) f = 0
      rw [mulMap_apply_eq_zero]
      intro α
      rw [← hab i]
      have h1 := hz ((α : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)))
        (Set.mem_image2_of_mem α.2 (Finset.mem_coe.2 i.2))
      have e : (f : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)) * hfun α
          = (α : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)) * f := by
        show (f : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)) * α = _
        ring
      rw [e]
      exact h1
  have e2 : finrank (ZMod 2) ↥(LinearMap.range
        (mulMap C (polyLE σ k) hfun (comb (fun i => affine (a i) (B i)) c)))
      = errRank C ((fun h => h * ∑ g ∈ J, g) '' H) k := by
    refine errRank_eq_range C _ k _ fun f => ?_
    rw [mulMap_apply_eq_zero, hcomb]
    constructor
    · rintro hz _ ⟨h, hh, rfl⟩
      have h1 := hz ⟨h, hh⟩
      have e : h * (∑ g ∈ J, g) * (f : MvPolynomial σ (ZMod 2))
          = (f : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * h := by ring
      rw [e]
      exact h1
    · intro hz α
      have h1 := hz ((α : MvPolynomial σ (ZMod 2)) * ∑ g ∈ J, g) ⟨α, α.2, rfl⟩
      have e : (f : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * hfun α
          = (α : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * f := by
        show (f : MvPolynomial σ (ZMod 2)) * (∑ g ∈ J, g) * α = _
        ring
      rw [e]
      exact h1
  rw [e1, e2] at hc
  exact ⟨J, hJ, hc⟩

end PEqualNP.ProofComplexity.DegSizeRank
