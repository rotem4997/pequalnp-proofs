import PEqualNP.ProofComplexity.Helpers.DegSizeRank
import PEqualNP.ProofComplexity.Helpers.DegSizeGain

/-!
# The counting core of degree to size, for inputs of degree at most `k`

`DegSizeRank` and `DegSizeGain` prove the abstract counting core of L-pcx-042 for inputs `G`
of degree at most one. This file proves the same chain for inputs of degree at most `k`
(the input polynomial of a conjunction of at most `k` parity equations is a product of at
most `k` affine polynomials). Nothing here depends on a proof system: only `DegClosed C D`.

* `idem_k`: every polynomial `g` of degree at most `k` is idempotent modulo the closure,
  `g * g + g ∈ C`, in budget `2 * k ≤ D`.
* `monoRank_mul`: Lemma 4.1 for ANY family of multipliers of degree at most `b`, in budget
  `b + K ≤ D`; `monoRank_used_k` is its instance for `zMul P G`, budget `a + K + k ≤ D`.
* `rankRetention_used_k`: rank retention, budget `b + l + 2 * k ≤ D`.
* `eta_k`, `gain_k`: one more factor `1 + q` removes half of the rank `k` levels lower,
  budget `a + K + 2 * k ≤ D`.
* `greedy_k`, `common_k`: the greedy approximators and the common multiplier, budget
  `K + t * k + k ≤ D`.

At `k = 1` every statement is the original one with the original budget; the last section
derives the originals (`stmt41_of_k`, `stmt35_of_k`, `gain_of_k`, `greedy_of_k`,
`common_of_k`) from the degree `k` versions as the check.

The linear algebra (`RankRetention` up to `rank_retention_mul`, `MonoRank`, and the three
dimension counts of `DegSizeGain`) is reused unchanged.
-/

namespace PEqualNP.ProofComplexity.DegSizeGainK

open MvPolynomial Module PEqualNP.ProofComplexity PEqualNP.ProofComplexity.Helpers
  PEqualNP.ProofComplexity.DegSizePlan

/-- The gain per factor for inputs of degree at most `k`: multiplication by `q` of degree at
most `k` maps level `K - k` into level `K`. -/
noncomputable def eta_k (n K k : ℕ) : ℝ := (numMono n (K - k) : ℝ) / (2 * numMono n K)

theorem eta_k_one (n K : ℕ) : eta_k n K 1 = eta n K := rfl

/-! ## Degrees and idempotence -/

section Poly

variable {σ : Type}

theorem deg_one_add_le_k {k : ℕ} {q : MvPolynomial σ (ZMod 2)} (hq : q.totalDegree ≤ k) :
    (1 + q).totalDegree ≤ k :=
  (totalDegree_add _ _).trans (max_le (by simp) hq)

theorem deg_idem_le_k {k : ℕ} {q : MvPolynomial σ (ZMod 2)} (hq : q.totalDegree ≤ k) :
    (q * q + q).totalDegree ≤ 2 * k :=
  (totalDegree_add _ _).trans (max_le ((DegSizeGain.deg_mul_le hq hq).trans (by omega))
    (by omega))

theorem deg_le_of_mem_span {k : ℕ} {G : Set (MvPolynomial σ (ZMod 2))}
    (hG : ∀ g ∈ G, g.totalDegree ≤ k) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q.totalDegree ≤ k :=
  DegSizeGain.mem_polyLE.mp
    (Submodule.span_le.mpr (fun g hg => DegSizeGain.mem_polyLE.mpr (hG g hg)) hq)

theorem deg_prod_le_k {k t : ℕ} (qs : Fin t → MvPolynomial σ (ZMod 2))
    (h : ∀ j, (qs j).totalDegree ≤ k) : (∏ j, (1 + qs j)).totalDegree ≤ t * k := by
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ j : Fin t, (1 + qs j).totalDegree ≤ ∑ _j : Fin t, k :=
        Finset.sum_le_sum (fun j _ => deg_one_add_le_k (h j))
    _ = t * k := by simp

variable {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ}

/-- A monomial of degree `n` is idempotent modulo the closure, in budget `2 * n ≤ D`. -/
theorem idem_monomial_one (hC : DegClosed C D) :
    ∀ (n : ℕ) (u : σ →₀ ℕ), (u.sum fun _ e => e) = n → 2 * n ≤ D →
      monomial u (1 : ZMod 2) * monomial u 1 + monomial u 1 ∈ C := by
  intro n
  induction n with
  | zero =>
    intro u hu _
    have h0 : u = 0 := DegSizeGain.eq_zero_of_sum_eq_zero u hu
    subst h0
    have hm : (monomial (0 : σ →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
    rw [hm, one_mul, CharTwo.add_self_eq_zero]
    exact C.zero_mem
  | succ n ih =>
    intro u hu hD
    have h0 : u ≠ 0 := by rintro rfl; simp at hu
    obtain ⟨v, u', rfl, hs⟩ := DegSizeGain.exists_single_add u h0
    have hm' := ih u' (by omega) (by omega)
    have hmd : (monomial u' (1 : ZMod 2)).totalDegree ≤ n := by
      have h2 : (monomial u' (1 : ZMod 2)).totalDegree ≤ (u'.sum fun _ e => e) :=
        totalDegree_monomial_le u' 1
      omega
    have e0 : monomial (Finsupp.single v 1 + u') (1 : ZMod 2) = X v * monomial u' 1 := by
      rw [monomial_single_add, pow_one]
    rw [e0]
    generalize monomial u' (1 : ZMod 2) = m at hm' hmd ⊢
    have e : X v * m * (X v * m) + X v * m
        = (m * m) * (X v * X v + X v) + X v * (m * m + m) := by
      linear_combination (-1 : MvPolynomial σ (ZMod 2)) *
        CharTwo.add_self_eq_zero (X v * (m * m))
    rw [e]
    refine C.add_mem ?_ (hC.mulX v _ hm' ?_)
    · refine DegSizeGain.absorb hC (hC.bool v) ?_
      have h1 := DegSizeGain.deg_mul_le hmd hmd
      have h2 := DegSizeRank.bool_totalDegree_le v
      omega
    · have h1 := deg_idem_le_k hmd
      omega

theorem idem_monomial_k (hC : DegClosed C D) {k : ℕ} (u : σ →₀ ℕ) (c : ZMod 2)
    (hu : (u.sum fun _ e => e) ≤ k) (hD : 2 * k ≤ D) :
    monomial u c * monomial u c + monomial u c ∈ C := by
  have hc : c = 0 ∨ c = 1 := by revert c; decide
  rcases hc with rfl | rfl
  · simp
  · exact idem_monomial_one hC _ u rfl (by omega)

/-- Idempotence modulo the closure for EVERY polynomial of degree at most `k`, in budget
`2 * k ≤ D`: over the two-element field squaring is additive, so it reduces to monomials,
and a monomial reduces to the Boolean axioms one variable at a time. -/
theorem idem_k (hC : DegClosed C D) {k : ℕ} (g : MvPolynomial σ (ZMod 2))
    (hg : g.totalDegree ≤ k) (hD : 2 * k ≤ D) : g * g + g ∈ C := by
  classical
  have key : ∀ (s : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → ZMod 2),
      (∀ u ∈ s, (u.sum fun _ e => e) ≤ k) →
      (∑ u ∈ s, monomial u (c u)) * (∑ u ∈ s, monomial u (c u))
        + ∑ u ∈ s, monomial u (c u) ∈ C := by
    intro s c
    induction s using Finset.induction_on with
    | empty => intro _; simp
    | insert a s ha ih =>
      intro hs
      rw [Finset.sum_insert ha]
      have e : ∀ m r : MvPolynomial σ (ZMod 2),
          (m + r) * (m + r) + (m + r) = (m * m + m) + (r * r + r) := by
        intro m r
        linear_combination CharTwo.add_self_eq_zero (m * r)
      rw [e]
      exact C.add_mem (idem_monomial_k hC a (c a) (hs a (Finset.mem_insert_self a s)) hD)
        (ih (fun u hu => hs u (Finset.mem_insert_of_mem hu)))
  have h := key g.support (fun u => g.coeff u)
    (fun u hu => (le_totalDegree hu).trans hg)
  rwa [support_sum_monomial_coeff] at h

/-- The base case of the greedy induction, inputs of degree at most `k`. -/
theorem errRank_one_le_k [Fintype σ] (hC : DegClosed C D) {k : ℕ}
    {G : Set (MvPolynomial σ (ZMod 2))} (hG : ∀ g ∈ G, g.totalDegree ≤ k) {K : ℕ}
    (hD : K + k ≤ D) : errRank C (zMul 1 G) K ≤ hCodim C K := by
  have hle : C ⊓ polyLE σ K ≤ errKer C (zMul 1 G) K := by
    intro f hf
    have hfC : f ∈ C := hf.1
    have hfE : f.totalDegree ≤ K := DegSizeGain.mem_polyLE.mp hf.2
    rw [DegSizeGain.mem_errKer_zMul]
    refine ⟨hfE, fun g hg => ?_⟩
    rw [one_mul]
    have h1 := hG g hg
    exact DegSizeGain.absorb hC hfC (by omega)
  have h2 := Submodule.finrank_mono hle
  unfold errRank hCodim
  omega

end Poly

/-! ## Lemma 4.1 as used -/

/-- Lemma 4.1 for any family `M` of multipliers of degree at most `b`, in budget
`b + K ≤ D`: the normalised rank is nonincreasing in the level up to `K`. -/
theorem monoRank_mul :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D b K : ℕ)
      (M : Set (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (∀ m ∈ M, m.totalDegree ≤ b) → b + K ≤ D →
      ∀ l l' : ℕ, l ≤ l' → l' ≤ K →
        errRank C M l' * numMono (Fintype.card σ) l
          ≤ errRank C M l * numMono (Fintype.card σ) l' := by
  intro σ _ C D b K M hC hmdeg hD
  have hX : ∀ p ∈ DegSizeRank.annih C M, p.totalDegree < K → ∀ i : σ,
      X i * p ∈ DegSizeRank.annih C M := by
    intro p hp hdeg i
    rw [DegSizeRank.mem_annih] at hp ⊢
    intro m hm
    have h1 := hC.mulX i (m * p) (hp m hm) (by
      have h2 := totalDegree_mul m p
      have h3 := hmdeg m hm
      omega)
    have e : m * (X i * p) = X i * (m * p) := by ring
    rw [e]
    exact h1
  have hB : ∀ (d : σ →₀ ℕ) (i : σ), d.degree + 2 ≤ K →
      monomial d (1 : ZMod 2) * (X i ^ 2 - X i) ∈ DegSizeRank.annih C M := by
    intro d i hd
    rw [DegSizeRank.mem_annih]
    intro m hm
    have e : m * (monomial d (1 : ZMod 2) * (X i ^ 2 - X i))
        = (m * monomial d 1) * (X i * X i + X i) := by
      rw [CharTwo.sub_eq_add]
      ring
    rw [e]
    refine DegSizeRank.absorb hC _ _ (hC.bool i) ?_
    have h1 := totalDegree_mul m (monomial d (1 : ZMod 2))
    have h2 := DegSizeRank.totalDegree_monomial_one d
    have h3 := DegSizeRank.bool_totalDegree_le i
    have h4 := hmdeg m hm
    omega
  have step : ∀ j, j + 1 ≤ K →
      errRank C M (j + 1) * numMono (Fintype.card σ) j
        ≤ errRank C M j * numMono (Fintype.card σ) (j + 1) := by
    intro j hj
    rw [DegSizeRank.errRank_eq_map, DegSizeRank.errRank_eq_map]
    exact MonoRank.rank_ratio_monotone (DegSizeRank.annih C M) K hX hB j hj
  intro l l' hll' hl'
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hll'
  exact DegSizeRank.iterate_ratio (fun j => errRank C M j)
    (fun j => numMono (Fintype.card σ) j) K (fun j => DegSizeGain.numMono_pos _ j) step l t hl'

/-- Lemma 4.1 as used: for an approximator `P` of degree at most `a` and inputs `G` of
degree at most `k`, with `a + K + k ≤ D`. -/
theorem monoRank_used_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
      (D a K k : ℕ) (P : MvPolynomial σ (ZMod 2)) (G : Set (MvPolynomial σ (ZMod 2))),
      DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ k) → a + K + k ≤ D →
      ∀ l l' : ℕ, l ≤ l' → l' ≤ K →
        errRank C (zMul P G) l' * numMono (Fintype.card σ) l
          ≤ errRank C (zMul P G) l * numMono (Fintype.card σ) l' := by
  intro σ _ C D a K k P G hC hP hG hD
  refine monoRank_mul σ C D (a + k) K (zMul P G) hC ?_ (by omega)
  rintro _ ⟨g, hg, rfl⟩
  exact DegSizeGain.deg_mul_le hP (hG g hg)

/-! ## Rank retention -/

/-- Rank retention for inputs of degree at most `k`: with `H` of degree at most `b` and
`b + l + 2 * k ≤ D`, some sum `q` of a subset of `G` keeps half of the rank at level `l`. -/
theorem rankRetention_used_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
      (D b l k : ℕ) (H : Set (MvPolynomial σ (ZMod 2)))
      (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (∀ h ∈ H, h.totalDegree ≤ b) → (∀ g ∈ G, g.totalDegree ≤ k) →
      b + l + 2 * k ≤ D →
      ∃ J : Finset (MvPolynomial σ (ZMod 2)), J ⊆ G ∧
        errRank C (Set.image2 (fun h g => h * g) H ↑G) l
          ≤ 2 * errRank C ((fun h => h * ∑ g ∈ J, g) '' H) l := by
  classical
  intro σ _ C D b l k H G hC hH hG hD
  let gfun : ↥G → MvPolynomial σ (ZMod 2) := fun i => i
  let hfun : ↥H → MvPolynomial σ (ZMod 2) := fun α => α
  have hcd : ∀ c : ↥G → ZMod 2, (comb gfun c).totalDegree ≤ k := by
    intro c
    refine DegSizeGain.mem_polyLE.mp ?_
    unfold comb
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (DegSizeGain.mem_polyLE.mpr (hG i i.2))
  have hmul : ∀ (c c' : ↥G → ZMod 2) (α : ↥H), ∀ f ∈ polyLE σ l,
      f * comb gfun c * hfun α ∈ C → f * comb gfun c * comb gfun c' * hfun α ∈ C := by
    intro c c' α f hf hmem
    have e : f * comb gfun c * comb gfun c' * hfun α
        = comb gfun c' * (f * comb gfun c * hfun α) := by ring
    rw [e]
    refine DegSizeGain.absorb hC hmem ?_
    have h1 : (f * comb gfun c * hfun α).totalDegree ≤ l + k + b := DegSizeGain.deg_mul_le
      (DegSizeGain.deg_mul_le (DegSizeGain.mem_polyLE.mp hf) (hcd c)) (hH α α.2)
    have h2 := hcd c'
    omega
  have hidem : ∀ (c : ↥G → ZMod 2) (α : ↥H), ∀ f ∈ polyLE σ l,
      f * (comb gfun c * comb gfun c + comb gfun c) * hfun α ∈ C := by
    intro c α f hf
    have e : f * (comb gfun c * comb gfun c + comb gfun c) * hfun α
        = (f * hfun α) * (comb gfun c * comb gfun c + comb gfun c) := by ring
    rw [e]
    refine DegSizeGain.absorb hC (idem_k hC _ (hcd c) (by omega)) ?_
    have h1 : (f * hfun α).totalDegree ≤ l + b :=
      DegSizeGain.deg_mul_le (DegSizeGain.mem_polyLE.mp hf) (hH α α.2)
    have h2 := deg_idem_le_k (hcd c)
    omega
  obtain ⟨c, hc⟩ := rank_retention_mul (ι := ↥G) (τ := ↥H) C (polyLE σ l) gfun hfun
    hmul hidem
  set J : Finset (MvPolynomial σ (ZMod 2)) :=
    (Finset.univ.filter fun i : ↥G => c i = 1).map (Function.Embedding.subtype _) with hJdef
  have hJ : J ⊆ G := by
    intro g hg
    rw [hJdef, Finset.mem_map] at hg
    obtain ⟨i, -, rfl⟩ := hg
    exact i.2
  have hcomb : comb gfun c = ∑ g ∈ J, g := by
    rw [hJdef, Finset.sum_map, Finset.sum_filter]
    unfold comb
    refine Finset.sum_congr rfl fun i _ => ?_
    show c i • (i : MvPolynomial σ (ZMod 2)) = if c i = 1 then (i : MvPolynomial σ (ZMod 2)) else 0
    have hci : c i = 0 ∨ c i = 1 := by
      generalize c i = x
      revert x
      decide
    rcases hci with h | h
    · simp [h]
    · simp [h]
  have e1 : finrank (ZMod 2) ↥(LinearMap.range
        (LinearMap.pi fun i => mulMap C (polyLE σ l) hfun (gfun i)))
      = errRank C (Set.image2 (fun h g => h * g) H ↑G) l := by
    refine DegSizeRank.errRank_eq_range C _ l _ fun f => ?_
    constructor
    · intro hz m hm
      obtain ⟨h, hh, g, hg, rfl⟩ := hm
      have hz' : mulMap C (polyLE σ l) hfun (gfun ⟨g, hg⟩) f = 0 := congrFun hz ⟨g, hg⟩
      have h1 := (mulMap_apply_eq_zero C (polyLE σ l) hfun _ f).1 hz' ⟨h, hh⟩
      have e : h * g * (f : MvPolynomial σ (ZMod 2)) = (f : MvPolynomial σ (ZMod 2)) * g * h := by
        ring
      rw [e]
      exact h1
    · intro hz
      funext i
      show mulMap C (polyLE σ l) hfun (gfun i) f = 0
      rw [mulMap_apply_eq_zero]
      intro α
      have h1 := hz ((α : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)))
        (Set.mem_image2_of_mem α.2 (Finset.mem_coe.2 i.2))
      have e : (f : MvPolynomial σ (ZMod 2)) * gfun i * hfun α
          = (α : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)) * f := by
        show (f : MvPolynomial σ (ZMod 2)) * (i : MvPolynomial σ (ZMod 2)) * α = _
        ring
      rw [e]
      exact h1
  have e2 : finrank (ZMod 2) ↥(LinearMap.range
        (mulMap C (polyLE σ l) hfun (comb gfun c)))
      = errRank C ((fun h => h * ∑ g ∈ J, g) '' H) l := by
    refine DegSizeRank.errRank_eq_range C _ l _ fun f => ?_
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

/-! ## Approximation gain -/

/-- The gain for inputs of degree at most `k`: one more factor `1 + q`, `q` a sum of a
subset of `G`, removes half of the rank `k` levels lower. Budget `a + K + 2 * k ≤ D`. -/
theorem gain_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
      (D a K k : ℕ) (P : MvPolynomial σ (ZMod 2)) (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ k) → k ≤ K →
      a + K + 2 * k ≤ D →
      ∃ q ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2))),
        2 * errRank C (zMul (P * (1 + q)) ↑G) K + errRank C (zMul P ↑G) (K - k)
          ≤ 2 * errRank C (zMul P ↑G) K := by
  intro σ _ C D a K k P G hC hP hG hK hD
  have hG' : ∀ g ∈ (↑G : Set (MvPolynomial σ (ZMod 2))), g.totalDegree ≤ k :=
    fun g hg => hG g (Finset.mem_coe.mp hg)
  obtain ⟨J, hJ, hrr⟩ := rankRetention_used_k σ C D a (K - k) k {P} G hC
    (by intro h hh; rw [Set.mem_singleton_iff.mp hh]; exact hP) hG (by omega)
  obtain ⟨q, hqdef⟩ : ∃ q, q = ∑ g ∈ J, g := ⟨_, rfl⟩
  rw [← hqdef, Set.image_singleton, Set.image2_singleton_left] at hrr
  have hrr' : errRank C (zMul P ↑G) (K - k) ≤ 2 * errRank C {P * q} (K - k) := hrr
  have hqs : q ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2))) := by
    rw [hqdef]
    exact Submodule.sum_mem _ (fun g hg => Submodule.subset_span (Finset.mem_coe.mpr (hJ hg)))
  have hq1 : q.totalDegree ≤ k := deg_le_of_mem_span hG' hqs
  have hidem : q * q + q ∈ C := idem_k hC q hq1 (by omega)
  have hidem2 := deg_idem_le_k hq1
  refine ⟨q, hqs, ?_⟩
  -- the kernel of the old approximator `k` levels lower, seen through `f ↦ q * f`
  have hi : polyLE σ (K - k) ⊓ (errKer C (zMul P ↑G) K).comap (LinearMap.mulLeft (ZMod 2) q)
      ≤ errKer C {P * q} (K - k) := by
    intro f hf
    have hfd : f.totalDegree ≤ K - k := DegSizeGain.mem_polyLE.mp hf.1
    have hfW : q * f ∈ errKer C (zMul P ↑G) K := hf.2
    rw [DegSizeGain.mem_errKer_zMul] at hfW
    rw [mem_errKer]
    refine ⟨hfd, ?_⟩
    intro m hm
    rw [Set.mem_singleton_iff.mp hm]
    have hsum : P * q * (q * f) ∈ C := by
      have e : ∑ g ∈ J, P * g * (q * f) = P * q * (q * f) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, ← hqdef]
      rw [← e]
      exact C.sum_mem (fun g hg => hfW.2 g (Finset.mem_coe.mpr (hJ hg)))
    have hid : (P * f) * (q * q + q) ∈ C := by
      have hd1 := DegSizeGain.deg_mul_le hP hfd
      exact DegSizeGain.absorb hC hidem (by omega)
    have e : P * q * (q * f) + (P * f) * (q * q + q) = P * q * f := by
      linear_combination CharTwo.add_self_eq_zero (P * q * (q * f))
    rw [← e]
    exact C.add_mem hsum hid
  -- the new kernel holds the old one and the multiples `q * f`
  have hii : (polyLE σ (K - k)).map (LinearMap.mulLeft (ZMod 2) q) ⊔ errKer C (zMul P ↑G) K
      ≤ errKer C (zMul (P * (1 + q)) ↑G) K := by
    refine sup_le ?_ ?_
    · rintro _ ⟨f, hfA, rfl⟩
      have hfd : f.totalDegree ≤ K - k := DegSizeGain.mem_polyLE.mp hfA
      change q * f ∈ errKer C (zMul (P * (1 + q)) ↑G) K
      rw [DegSizeGain.mem_errKer_zMul]
      have hd0 := DegSizeGain.deg_mul_le hq1 hfd
      refine ⟨by omega, ?_⟩
      intro g hg
      have hd1 := DegSizeGain.deg_mul_le (DegSizeGain.deg_mul_le hP (hG' g hg)) hfd
      have e : P * (1 + q) * g * (q * f) = (P * g * f) * (q * q + q) := by ring
      rw [e]
      exact DegSizeGain.absorb hC hidem (by omega)
    · intro f hf
      rw [DegSizeGain.mem_errKer_zMul] at hf ⊢
      refine ⟨hf.1, ?_⟩
      intro g hg
      have hd1 := DegSizeGain.deg_mul_le (DegSizeGain.deg_mul_le hP (hG' g hg)) hf.1
      have hd2 := deg_one_add_le_k hq1
      have e : P * (1 + q) * g * f = (1 + q) * (P * g * f) := by ring
      rw [e]
      exact DegSizeGain.absorb hC (hf.2 g hg) (by omega)
  have key := DegSizeGain.finrank_add_le (LinearMap.mulLeft (ZMod 2) q) (polyLE σ (K - k))
    (errKer C (zMul P ↑G) K)
  have k1 := Submodule.finrank_mono hi
  have k2 := Submodule.finrank_mono hii
  have k3 : finrank (ZMod 2) ↥(errKer C {P * q} (K - k)) ≤ finrank (ZMod 2) (polyLE σ (K - k)) :=
    Submodule.finrank_mono (DegSizeGain.errKer_le _ _)
  have k4 : finrank (ZMod 2) ↥(errKer C (zMul (P * (1 + q)) ↑G) K)
      ≤ finrank (ZMod 2) (polyLE σ K) := Submodule.finrank_mono (DegSizeGain.errKer_le _ _)
  have k5 : finrank (ZMod 2) ↥(errKer C (zMul P ↑G) K) ≤ finrank (ZMod 2) (polyLE σ K) :=
    Submodule.finrank_mono (DegSizeGain.errKer_le _ _)
  unfold errRank at hrr' ⊢
  omega

/-! ## The greedy approximators -/

theorem greedy_arith_k {c c' c1 h n K k t : ℕ} (h1 : 2 * c' + c1 ≤ 2 * c)
    (h2 : c * numMono n (K - k) ≤ c1 * numMono n K)
    (hb : (c : ℝ) ≤ h * (1 - eta_k n K k) ^ t) :
    (c' : ℝ) ≤ h * (1 - eta_k n K k) ^ (t + 1) := by
  have hN : (0 : ℝ) < numMono n K := by exact_mod_cast DegSizeGain.numMono_pos n K
  have hN1 : (numMono n (K - k) : ℝ) ≤ numMono n K := by
    exact_mod_cast DegSizeGain.numMono_mono n (Nat.sub_le K k)
  have h1' : (2 : ℝ) * c' + c1 ≤ 2 * c := by exact_mod_cast h1
  have h2' : (c : ℝ) * numMono n (K - k) ≤ c1 * numMono n K := by exact_mod_cast h2
  have hx : 0 ≤ 1 - eta_k n K k := by
    have hle : eta_k n K k ≤ 1 := by
      unfold eta_k
      exact (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have he : (c : ℝ) * eta_k n K k ≤ c1 / 2 := by
    unfold eta_k
    have e1 : (c : ℝ) * (numMono n (K - k) / (2 * numMono n K))
        = (c * numMono n (K - k)) / (2 * numMono n K) := by ring
    have e2 : (c1 : ℝ) / 2 = (c1 * numMono n K) / (2 * numMono n K) := by field_simp
    rw [e1, e2]
    gcongr
  calc (c' : ℝ) ≤ c * (1 - eta_k n K k) := by linarith
    _ ≤ (h * (1 - eta_k n K k) ^ t) * (1 - eta_k n K k) := mul_le_mul_of_nonneg_right hb hx
    _ = h * (1 - eta_k n K k) ^ (t + 1) := by ring

/-- The greedy approximators for inputs of degree at most `k`: `t` factors bring the rank
below `h_K * (1 - eta_k) ^ t`. Budget `K + t * k + k ≤ D`. -/
theorem greedy_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
      (D K t k : ℕ) (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ k) → k ≤ K → K + t * k + k ≤ D →
      ∃ qs : Fin t → MvPolynomial σ (ZMod 2),
        (∀ j, qs j ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2)))) ∧
        (errRank C (zMul (∏ j, (1 + qs j)) ↑G) K : ℝ)
          ≤ hCodim C K * (1 - eta_k (Fintype.card σ) K k) ^ t := by
  intro σ _ C D K t k G hC hG hK
  have hG' : ∀ g ∈ (↑G : Set (MvPolynomial σ (ZMod 2))), g.totalDegree ≤ k :=
    fun g hg => hG g (Finset.mem_coe.mp hg)
  induction t with
  | zero =>
    intro hD
    refine ⟨fun _ => 0, fun j => j.elim0, ?_⟩
    rw [Fin.prod_univ_zero, pow_zero, mul_one]
    exact_mod_cast errRank_one_le_k hC hG' (by omega)
  | succ t ih =>
    intro hD
    have et : (t + 1) * k = t * k + k := by ring
    rw [et] at hD
    obtain ⟨qs, hqs, hb⟩ := ih (by omega)
    have hP : (∏ j, (1 + qs j)).totalDegree ≤ t * k :=
      deg_prod_le_k qs (fun j => deg_le_of_mem_span hG' (hqs j))
    obtain ⟨q, hq, hgain⟩ := gain_k σ C D (t * k) K k _ G hC hP hG hK (by omega)
    have h41' := monoRank_used_k σ C D (t * k) K k _ (↑G) hC hP hG' (by omega) (K - k) K
      (by omega) le_rfl
    refine ⟨Fin.snoc (α := fun _ => MvPolynomial σ (ZMod 2)) qs q, ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [Fin.snoc_last]; exact hq
      · rw [Fin.snoc_castSucc]; exact hqs i
    · rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact greedy_arith_k hgain h41' hb

/-! ## The common multiplier -/

/-- The common multiplier for inputs of degree at most `k`. `S` indexes the lines, `G ν` are
the inputs of line `ν`. Budget `K + t * k + k ≤ D`. -/
theorem common_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2)))
      (D K t k : ℕ) (ι : Type) (S : Finset ι) (G : ι → Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (1 : MvPolynomial σ (ZMod 2)) ∉ C →
      (∀ ν ∈ S, ∀ g ∈ G ν, g.totalDegree ≤ k) → k ≤ K → K + t * k + k ≤ D →
      (S.card : ℝ) * (1 - eta_k (Fintype.card σ) K k) ^ t < 1 →
      ∃ (f : MvPolynomial σ (ZMod 2)) (qs : ι → Fin t → MvPolynomial σ (ZMod 2)),
        f.totalDegree ≤ K ∧ f ∉ C ∧
        (∀ ν ∈ S, ∀ j,
          qs ν j ∈ Submodule.span (ZMod 2) (↑(G ν) : Set (MvPolynomial σ (ZMod 2)))) ∧
        ∀ ν ∈ S, ∀ g ∈ G ν, (∏ j, (1 + qs ν j)) * g * f ∈ C := by
  classical
  intro σ _ C D K t k ι S G hC h1 hG hK hD hlt
  have hg : ∀ ν, ∃ qs : Fin t → MvPolynomial σ (ZMod 2), ν ∈ S →
      ((∀ j, qs j ∈ Submodule.span (ZMod 2) (↑(G ν) : Set (MvPolynomial σ (ZMod 2)))) ∧
        (errRank C (zMul (∏ j, (1 + qs j)) ↑(G ν)) K : ℝ)
          ≤ hCodim C K * (1 - eta_k (Fintype.card σ) K k) ^ t) := by
    intro ν
    by_cases hν : ν ∈ S
    · obtain ⟨qs, h⟩ := greedy_k σ C D K t k (G ν) hC (hG ν hν) hK hD
      exact ⟨qs, fun _ => h⟩
    · exact ⟨fun _ => 0, fun h => absurd h hν⟩
  choose qs hqs using hg
  have : FiniteDimensional (ZMod 2) ↥(C ⊓ polyLE σ K) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have hCE : finrank (ZMod 2) ↥(C ⊓ polyLE σ K) ≤ finrank (ZMod 2) (polyLE σ K) :=
    Submodule.finrank_mono inf_le_right
  -- the closure is proper, so its low-degree part has positive codimension
  have hpos : 0 < hCodim C K := by
    by_contra h0
    have hle : finrank (ZMod 2) (polyLE σ K) ≤ finrank (ZMod 2) ↥(C ⊓ polyLE σ K) := by
      unfold hCodim at h0
      omega
    have heq := Submodule.eq_of_le_of_finrank_le
      (inf_le_right : C ⊓ polyLE σ K ≤ polyLE σ K) hle
    have hone : (1 : MvPolynomial σ (ZMod 2)) ∈ C ⊓ polyLE σ K := by
      rw [heq]
      exact DegSizeGain.mem_polyLE.mpr (by simp)
    exact h1 hone.1
  -- the ranks of all lines together stay below that codimension
  have hsum : ∑ ν ∈ S, errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K < hCodim C K := by
    have hR : ((∑ ν ∈ S, errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K : ℕ) : ℝ)
        < (hCodim C K : ℝ) := by
      push_cast
      calc ∑ ν ∈ S, (errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K : ℝ)
          ≤ ∑ _ν ∈ S, ((hCodim C K : ℝ) * (1 - eta_k (Fintype.card σ) K k) ^ t) :=
            Finset.sum_le_sum (fun ν hν => (hqs ν hν).2)
        _ = (hCodim C K : ℝ) * ((S.card : ℝ) * (1 - eta_k (Fintype.card σ) K k) ^ t) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ < (hCodim C K : ℝ) * 1 := mul_lt_mul_of_pos_left hlt (by exact_mod_cast hpos)
        _ = (hCodim C K : ℝ) := mul_one _
    exact_mod_cast hR
  have hcod : finrank (ZMod 2) (polyLE σ K)
      ≤ finrank (ZMod 2)
          ↥(polyLE σ K ⊓ ⨅ ν ∈ S, errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K)
        + ∑ ν ∈ S, errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K :=
    DegSizeGain.codim_iInf (polyLE σ K)
      (fun ν => errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K)
      (fun ν => DegSizeGain.errKer_le _ _) S
  have hnot : ¬ (polyLE σ K ⊓ ⨅ ν ∈ S, errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K)
      ≤ C ⊓ polyLE σ K := by
    intro hle
    have hm := Submodule.finrank_mono hle
    unfold hCodim at hsum
    omega
  obtain ⟨f, hfI, hfC⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hfE : f ∈ polyLE σ K := hfI.1
  refine ⟨f, qs, DegSizeGain.mem_polyLE.mp hfE, fun hc => hfC ⟨hc, hfE⟩,
    fun ν hν => (hqs ν hν).1, ?_⟩
  intro ν hν g hg
  have hfW : f ∈ errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K := by
    exact (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hfI.2 ν) hν
  exact (DegSizeGain.mem_errKer_zMul.mp hfW).2 g (Finset.mem_coe.mpr hg)

/-! ## The check at `k = 1`: the originals follow, with their own budgets -/

/-- `DegSizeGain.Stmt41` (the statement of `DegSizeRank.monoRank_used`) is `monoRank_used_k`
at `k = 1`. -/
theorem stmt41_of_k : DegSizeGain.Stmt41 := by
  intro σ _ C D a K P G hC hP hG hD
  exact monoRank_used_k σ C D a K 1 P G hC hP hG hD

/-- `DegSizeGain.Stmt35` (the statement of `DegSizeRank.rankRetention_used`) is
`rankRetention_used_k` at `k = 1`. -/
theorem stmt35_of_k : DegSizeGain.Stmt35 := by
  intro σ _ C D b l H G hC hH hG hD
  exact rankRetention_used_k σ C D b l 1 H G hC hH hG (by omega)

/-- The conclusion of `DegSizeGain.gain` is `gain_k` at `k = 1`. -/
theorem gain_of_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D a K : ℕ)
      (P : MvPolynomial σ (ZMod 2)) (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ 1) → 1 ≤ K →
      a + K + 2 ≤ D →
      ∃ q ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2))),
        2 * errRank C (zMul (P * (1 + q)) ↑G) K + errRank C (zMul P ↑G) (K - 1)
          ≤ 2 * errRank C (zMul P ↑G) K := by
  intro σ _ C D a K P G hC hP hG hK hD
  exact gain_k σ C D a K 1 P G hC hP hG hK (by omega)

/-- The conclusion of `DegSizeGain.greedy` is `greedy_k` at `k = 1`. -/
theorem greedy_of_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t : ℕ)
      (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ 1) → 1 ≤ K → K + t + 1 ≤ D →
      ∃ qs : Fin t → MvPolynomial σ (ZMod 2),
        (∀ j, qs j ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2)))) ∧
        (errRank C (zMul (∏ j, (1 + qs j)) ↑G) K : ℝ)
          ≤ hCodim C K * (1 - eta (Fintype.card σ) K) ^ t := by
  intro σ _ C D K t G hC hG hK hD
  exact greedy_k σ C D K t 1 G hC hG hK (by omega)

/-- The conclusion of `DegSizeGain.common` is `common_k` at `k = 1`. -/
theorem common_of_k :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t : ℕ)
      (ι : Type) (S : Finset ι) (G : ι → Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (1 : MvPolynomial σ (ZMod 2)) ∉ C →
      (∀ ν ∈ S, ∀ g ∈ G ν, g.totalDegree ≤ 1) → 1 ≤ K → K + t + 1 ≤ D →
      (S.card : ℝ) * (1 - eta (Fintype.card σ) K) ^ t < 1 →
      ∃ (f : MvPolynomial σ (ZMod 2)) (qs : ι → Fin t → MvPolynomial σ (ZMod 2)),
        f.totalDegree ≤ K ∧ f ∉ C ∧
        (∀ ν ∈ S, ∀ j,
          qs ν j ∈ Submodule.span (ZMod 2) (↑(G ν) : Set (MvPolynomial σ (ZMod 2)))) ∧
        ∀ ν ∈ S, ∀ g ∈ G ν, (∏ j, (1 + qs ν j)) * g * f ∈ C := by
  intro σ _ C D K t ι S G hC h1 hG hK hD hlt
  exact common_k σ C D K t 1 ι S G hC h1 hG hK (by omega) hlt

end PEqualNP.ProofComplexity.DegSizeGainK
