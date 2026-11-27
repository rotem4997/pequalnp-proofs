import PEqualNP.ProofComplexity.Helpers.DegSizePlan

/-!
# Approximation gain, greedy approximators and the common multiplier (links of L-pcx-042)

Three links of the degree to size chain for Res(⊕), on the statements of `DegSizePlan`:

* `gain` (Lemma 4.2 at `p = 2`): one more affine factor removes half of the rank one degree
  lower;
* `greedy` (Theorem 4.3 (a)): `t` greedy factors bring the rank below `h_K * (1 - η) ^ t`;
* `common` (Theorem 4.3 (b)): the common multiplier.

Two upstream links are taken as explicit hypotheses, each quantified exactly as its
statement in `DegSizePlan`: `Stmt41` (Lemma 4.1 as used) and `Stmt35` (Corollary 3.5 at
`p = 2`, affine inputs). Absorption (Lemma A) and idempotence of affine polynomials
(Lemma A') are proved here locally.

Source of the mathematics: the unrefereed preprint arXiv:2610.00837, Section 4, re-derived.
-/

namespace PEqualNP.ProofComplexity.DegSizeGain

open MvPolynomial Module PEqualNP.ProofComplexity PEqualNP.ProofComplexity.DegSizePlan

/-- Lemma 4.1 as used, verbatim from `DegSizePlan`. -/
def Stmt41 : Prop :=
  ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D a K : ℕ)
    (P : MvPolynomial σ (ZMod 2)) (G : Set (MvPolynomial σ (ZMod 2))),
    DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ 1) → a + K + 1 ≤ D →
    ∀ k k' : ℕ, k ≤ k' → k' ≤ K →
      errRank C (zMul P G) k' * numMono (Fintype.card σ) k
        ≤ errRank C (zMul P G) k * numMono (Fintype.card σ) k'

/-- Corollary 3.5 at `p = 2`, affine `G`, verbatim from `DegSizePlan`. -/
def Stmt35 : Prop :=
  ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D b k : ℕ)
    (H : Set (MvPolynomial σ (ZMod 2))) (G : Finset (MvPolynomial σ (ZMod 2))),
    DegClosed C D → (∀ h ∈ H, h.totalDegree ≤ b) → (∀ g ∈ G, g.totalDegree ≤ 1) →
    b + k + 2 ≤ D →
    ∃ J : Finset (MvPolynomial σ (ZMod 2)), J ⊆ G ∧
      errRank C (Set.image2 (fun h g => h * g) H ↑G) k
        ≤ 2 * errRank C ((fun h => h * ∑ g ∈ J, g) '' H) k

/-! ## Pure linear algebra -/

section LinearAlgebra

variable {V V' : Type*} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup V']
  [Module (ZMod 2) V']

/-- Rank and nullity of a linear map restricted to a finite-dimensional subspace. -/
theorem finrank_eq_map_add_inf_ker (g : V →ₗ[ZMod 2] V') (S : Submodule (ZMod 2) V)
    [FiniteDimensional (ZMod 2) S] :
    finrank (ZMod 2) S
      = finrank (ZMod 2) ↥(S.map g) + finrank (ZMod 2) ↥(S ⊓ LinearMap.ker g) := by
  have h := (g ∘ₗ S.subtype).finrank_range_add_finrank_ker
  rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.ker_comp] at h
  have e : finrank (ZMod 2) ↥((LinearMap.ker g).comap S.subtype)
      = finrank (ZMod 2) ↥(S ⊓ LinearMap.ker g) := by
    rw [← Submodule.map_comap_subtype]
    exact (Submodule.equivMapOfInjective S.subtype S.injective_subtype _).finrank_eq
  omega

/-- The dimension count behind the gain: the image of `A` under `f` adds to `W` at least
what `A` has outside the preimage of `W`. -/
theorem finrank_add_le (f : V →ₗ[ZMod 2] V) (A W : Submodule (ZMod 2) V)
    [FiniteDimensional (ZMod 2) A] [FiniteDimensional (ZMod 2) W] :
    finrank (ZMod 2) A + finrank (ZMod 2) W
      ≤ finrank (ZMod 2) ↥(A ⊓ W.comap f) + finrank (ZMod 2) ↥(A.map f ⊔ W) := by
  have h1 := finrank_eq_map_add_inf_ker (W.mkQ ∘ₗ f) A
  have h2 := finrank_eq_map_add_inf_ker W.mkQ (A.map f ⊔ W)
  rw [LinearMap.ker_comp, Submodule.ker_mkQ] at h1
  rw [Submodule.ker_mkQ, inf_eq_right.mpr le_sup_right] at h2
  have h3 : finrank (ZMod 2) ↥(A.map (W.mkQ ∘ₗ f))
      ≤ finrank (ZMod 2) ↥((A.map f ⊔ W).map W.mkQ) := by
    rw [Submodule.map_comp]
    exact Submodule.finrank_mono (Submodule.map_mono le_sup_left)
  omega

/-- Codimension is subadditive over a finite intersection. -/
theorem codim_iInf {ι : Type} (E : Submodule (ZMod 2) V) [FiniteDimensional (ZMod 2) E]
    (W : ι → Submodule (ZMod 2) V) (hW : ∀ ν, W ν ≤ E) (S : Finset ι) :
    finrank (ZMod 2) E
      ≤ finrank (ZMod 2) ↥(E ⊓ ⨅ ν ∈ S, W ν)
        + ∑ ν ∈ S, (finrank (ZMod 2) E - finrank (ZMod 2) (W ν)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h0 : (⨅ ν ∈ (∅ : Finset ι), W ν) = ⊤ := by simp
    rw [h0, inf_top_eq]
    exact Nat.le_add_right _ _
  | insert a s ha ih =>
    rw [Finset.iInf_insert, Finset.sum_insert ha, inf_left_comm]
    have : FiniteDimensional (ZMod 2) ↥(W a) := Submodule.finiteDimensional_of_le (hW a)
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (W a) (E ⊓ ⨅ ν ∈ s, W ν)
    have h2 : finrank (ZMod 2) ↥(W a ⊔ (E ⊓ ⨅ ν ∈ s, W ν)) ≤ finrank (ZMod 2) E :=
      Submodule.finrank_mono (sup_le (hW a) inf_le_left)
    have h3 : finrank (ZMod 2) (W a) ≤ finrank (ZMod 2) E := Submodule.finrank_mono (hW a)
    omega

end LinearAlgebra

/-! ## Degrees, absorption (Lemma A) and idempotence (Lemma A') -/

section Poly

variable {σ : Type}

theorem mem_polyLE {k : ℕ} {f : MvPolynomial σ (ZMod 2)} :
    f ∈ polyLE σ k ↔ f.totalDegree ≤ k := by
  simp [polyLE, mem_restrictTotalDegree]

theorem deg_mul_le {p q : MvPolynomial σ (ZMod 2)} {a b : ℕ} (hp : p.totalDegree ≤ a)
    (hq : q.totalDegree ≤ b) : (p * q).totalDegree ≤ a + b :=
  (totalDegree_mul p q).trans (add_le_add hp hq)

theorem deg_one_add_le {q : MvPolynomial σ (ZMod 2)} (hq : q.totalDegree ≤ 1) :
    (1 + q).totalDegree ≤ 1 :=
  (totalDegree_add _ _).trans (max_le (by simp) hq)

theorem deg_idem_le {q : MvPolynomial σ (ZMod 2)} (hq : q.totalDegree ≤ 1) :
    (q * q + q).totalDegree ≤ 2 :=
  (totalDegree_add _ _).trans (max_le (deg_mul_le hq hq) (by omega))

theorem deg_le_one_of_mem_span {G : Set (MvPolynomial σ (ZMod 2))}
    (hG : ∀ g ∈ G, g.totalDegree ≤ 1) {q : MvPolynomial σ (ZMod 2)}
    (hq : q ∈ Submodule.span (ZMod 2) G) : q.totalDegree ≤ 1 :=
  mem_polyLE.mp (Submodule.span_le.mpr (fun g hg => mem_polyLE.mpr (hG g hg)) hq)

theorem deg_prod_le {t : ℕ} (qs : Fin t → MvPolynomial σ (ZMod 2))
    (h : ∀ j, (qs j).totalDegree ≤ 1) : (∏ j, (1 + qs j)).totalDegree ≤ t := by
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ j : Fin t, (1 + qs j).totalDegree ≤ ∑ _j : Fin t, 1 :=
        Finset.sum_le_sum (fun j _ => deg_one_add_le (h j))
    _ = t := by simp

theorem eq_zero_of_sum_eq_zero (u : σ →₀ ℕ) (h : (u.sum fun _ e => e) = 0) : u = 0 := by
  rw [Finsupp.sum] at h
  ext i
  simp only [Finsupp.coe_zero, Pi.zero_apply]
  by_contra hi
  exact hi ((Finset.sum_eq_zero_iff.mp h) i (Finsupp.mem_support_iff.mpr hi))

theorem exists_single_add (u : σ →₀ ℕ) (h : u ≠ 0) :
    ∃ (v : σ) (u' : σ →₀ ℕ), u = Finsupp.single v 1 + u' ∧
      (u.sum fun _ e => e) = 1 + (u'.sum fun _ e => e) := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, u v ≠ 0 := by
    by_contra hcon
    refine h (Finsupp.ext (fun a => ?_))
    by_contra ha
    exact hcon ⟨a, ha⟩
  have hu : u = Finsupp.single v 1 + (u - Finsupp.single v 1) := by
    ext i
    rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    split_ifs with hvi
    · subst hvi; omega
    · omega
  refine ⟨v, u - Finsupp.single v 1, hu, ?_⟩
  conv_lhs => rw [hu]
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]

variable {C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))} {D : ℕ}

theorem absorb_monomial (hC : DegClosed C D) :
    ∀ (n : ℕ) (u : σ →₀ ℕ) (c : ZMod 2) (f : MvPolynomial σ (ZMod 2)),
      (u.sum fun _ e => e) = n → f ∈ C → n + f.totalDegree ≤ D → monomial u c * f ∈ C := by
  intro n
  induction n with
  | zero =>
    intro u c f hu hf _
    have h0 : u = 0 := eq_zero_of_sum_eq_zero u hu
    subst h0
    have hm : monomial (0 : σ →₀ ℕ) c = MvPolynomial.C c := rfl
    rw [hm, C_mul']
    exact C.smul_mem c hf
  | succ n ih =>
    intro u c f hu hf hd
    have h0 : u ≠ 0 := by rintro rfl; simp at hu
    obtain ⟨v, u', rfl, hs⟩ := exists_single_add u h0
    rw [monomial_single_add, pow_one, mul_assoc]
    have hm := ih u' c f (by omega) hf (by omega)
    refine hC.mulX v _ hm ?_
    have h1 := totalDegree_mul (monomial u' c) f
    have h2 : (monomial u' c).totalDegree ≤ (u'.sum fun _ e => e) := totalDegree_monomial_le u' c
    omega

/-- Lemma A (absorption). -/
theorem absorb (hC : DegClosed C D) {f g : MvPolynomial σ (ZMod 2)} (hf : f ∈ C)
    (h : g.totalDegree + f.totalDegree ≤ D) : g * f ∈ C := by
  have e : g * f = ∑ u ∈ g.support, monomial u (g.coeff u) * f := by
    rw [← Finset.sum_mul, support_sum_monomial_coeff]
  rw [e]
  refine C.sum_mem fun u hu => ?_
  have h1 : (u.sum fun _ e => e) ≤ g.totalDegree := le_totalDegree hu
  exact absorb_monomial hC _ u _ f rfl hf (by omega)

theorem idem_monomial (hC : DegClosed C D) (u : σ →₀ ℕ) (c : ZMod 2)
    (hu : (u.sum fun _ e => e) ≤ 1) :
    monomial u c * monomial u c + monomial u c ∈ C := by
  have hc : c = 0 ∨ c = 1 := by revert c; decide
  rcases hc with rfl | rfl
  · simp
  · by_cases h0 : u = 0
    · subst h0
      have hm : (monomial (0 : σ →₀ ℕ) (1 : ZMod 2)) = 1 := rfl
      rw [hm, one_mul, CharTwo.add_self_eq_zero]
      exact C.zero_mem
    · obtain ⟨v, u', rfl, hs⟩ := exists_single_add u h0
      have hu' : u' = 0 := eq_zero_of_sum_eq_zero u' (by omega)
      subst hu'
      rw [add_zero]
      exact hC.bool v

/-- Lemma A' (an affine polynomial is idempotent modulo the closure). -/
theorem affine_idem (hC : DegClosed C D) (g : MvPolynomial σ (ZMod 2))
    (hg : g.totalDegree ≤ 1) : g * g + g ∈ C := by
  classical
  have key : ∀ (s : Finset (σ →₀ ℕ)) (c : (σ →₀ ℕ) → ZMod 2),
      (∀ u ∈ s, (u.sum fun _ e => e) ≤ 1) →
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
      exact C.add_mem (idem_monomial hC a (c a) (hs a (Finset.mem_insert_self a s)))
        (ih (fun u hu => hs u (Finset.mem_insert_of_mem hu)))
  have h := key g.support (fun u => g.coeff u)
    (fun u hu => (le_totalDegree hu).trans hg)
  rwa [support_sum_monomial_coeff] at h

/-! ## Facts on `errKer`, `errRank`, `numMono` -/

theorem errKer_le (M : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) :
    errKer C M k ≤ polyLE σ k := by
  unfold errKer
  exact inf_le_left

instance errKer_finite [Fintype σ] (M : Set (MvPolynomial σ (ZMod 2))) (k : ℕ) :
    FiniteDimensional (ZMod 2) ↥(errKer C M k) :=
  Submodule.finiteDimensional_of_le (errKer_le M k)

theorem mem_errKer_zMul {P : MvPolynomial σ (ZMod 2)} {G : Set (MvPolynomial σ (ZMod 2))}
    {k : ℕ} {f : MvPolynomial σ (ZMod 2)} :
    f ∈ errKer C (zMul P G) k ↔ f.totalDegree ≤ k ∧ ∀ g ∈ G, P * g * f ∈ C := by
  rw [mem_errKer]
  simp [zMul]

theorem numMono_pos (n k : ℕ) : 0 < numMono n k := by
  unfold numMono
  have h : ∑ j ∈ Finset.range 1, n.choose j ≤ ∑ j ∈ Finset.range (k + 1), n.choose j :=
    Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
  have h1 : ∑ j ∈ Finset.range 1, n.choose j = 1 := by simp
  omega

theorem numMono_mono (n : ℕ) {k k' : ℕ} (h : k ≤ k') : numMono n k ≤ numMono n k' := by
  unfold numMono
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

/-- The base case of the greedy induction: the trivial approximator `1` has rank at most
the codimension of the closure. -/
theorem errRank_one_le [Fintype σ] (hC : DegClosed C D) {G : Set (MvPolynomial σ (ZMod 2))}
    (hG : ∀ g ∈ G, g.totalDegree ≤ 1) {K : ℕ} (hD : K + 1 ≤ D) :
    errRank C (zMul 1 G) K ≤ hCodim C K := by
  have hle : C ⊓ polyLE σ K ≤ errKer C (zMul 1 G) K := by
    intro f hf
    have hfC : f ∈ C := hf.1
    have hfE : f.totalDegree ≤ K := mem_polyLE.mp hf.2
    rw [mem_errKer_zMul]
    refine ⟨hfE, fun g hg => ?_⟩
    rw [one_mul]
    have h1 := hG g hg
    exact absorb hC hfC (by omega)
  have h2 := Submodule.finrank_mono hle
  unfold errRank hCodim
  omega

end Poly

/-! ## Lemma 4.2 (approximation gain) -/

/-- Lemma 4.2 at `p = 2`, from rank retention. -/
theorem gain (h35 : Stmt35) :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D a K : ℕ)
      (P : MvPolynomial σ (ZMod 2)) (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → P.totalDegree ≤ a → (∀ g ∈ G, g.totalDegree ≤ 1) → 1 ≤ K →
      a + K + 2 ≤ D →
      ∃ q ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2))),
        2 * errRank C (zMul (P * (1 + q)) ↑G) K + errRank C (zMul P ↑G) (K - 1)
          ≤ 2 * errRank C (zMul P ↑G) K := by
  intro σ _ C D a K P G hC hP hG hK hD
  have hG' : ∀ g ∈ (↑G : Set (MvPolynomial σ (ZMod 2))), g.totalDegree ≤ 1 :=
    fun g hg => hG g (Finset.mem_coe.mp hg)
  obtain ⟨J, hJ, hrr⟩ := h35 σ C D a (K - 1) {P} G hC
    (by intro h hh; rw [Set.mem_singleton_iff.mp hh]; exact hP) hG (by omega)
  obtain ⟨q, hqdef⟩ : ∃ q, q = ∑ g ∈ J, g := ⟨_, rfl⟩
  rw [← hqdef, Set.image_singleton, Set.image2_singleton_left] at hrr
  have hrr' : errRank C (zMul P ↑G) (K - 1) ≤ 2 * errRank C {P * q} (K - 1) := hrr
  have hqs : q ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2))) := by
    rw [hqdef]
    exact Submodule.sum_mem _ (fun g hg => Submodule.subset_span (Finset.mem_coe.mpr (hJ hg)))
  have hq1 : q.totalDegree ≤ 1 := deg_le_one_of_mem_span hG' hqs
  have hidem : q * q + q ∈ C := affine_idem hC q hq1
  have hidem2 := deg_idem_le hq1
  refine ⟨q, hqs, ?_⟩
  -- the kernel of the old approximator one level lower, seen through `f ↦ q * f`
  have hi : polyLE σ (K - 1) ⊓ (errKer C (zMul P ↑G) K).comap (LinearMap.mulLeft (ZMod 2) q)
      ≤ errKer C {P * q} (K - 1) := by
    intro f hf
    have hfd : f.totalDegree ≤ K - 1 := mem_polyLE.mp hf.1
    have hfW : q * f ∈ errKer C (zMul P ↑G) K := hf.2
    rw [mem_errKer_zMul] at hfW
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
      have hd1 := deg_mul_le hP hfd
      exact absorb hC hidem (by omega)
    have e : P * q * (q * f) + (P * f) * (q * q + q) = P * q * f := by
      linear_combination CharTwo.add_self_eq_zero (P * q * (q * f))
    rw [← e]
    exact C.add_mem hsum hid
  -- the new kernel holds the old one and the multiples `q * f`
  have hii : (polyLE σ (K - 1)).map (LinearMap.mulLeft (ZMod 2) q) ⊔ errKer C (zMul P ↑G) K
      ≤ errKer C (zMul (P * (1 + q)) ↑G) K := by
    refine sup_le ?_ ?_
    · rintro _ ⟨f, hfA, rfl⟩
      have hfd : f.totalDegree ≤ K - 1 := mem_polyLE.mp hfA
      change q * f ∈ errKer C (zMul (P * (1 + q)) ↑G) K
      rw [mem_errKer_zMul]
      have hd0 := deg_mul_le hq1 hfd
      refine ⟨by omega, ?_⟩
      intro g hg
      have hd1 := deg_mul_le (deg_mul_le hP (hG' g hg)) hfd
      have e : P * (1 + q) * g * (q * f) = (P * g * f) * (q * q + q) := by ring
      rw [e]
      exact absorb hC hidem (by omega)
    · intro f hf
      rw [mem_errKer_zMul] at hf ⊢
      refine ⟨hf.1, ?_⟩
      intro g hg
      have hd1 := deg_mul_le (deg_mul_le hP (hG' g hg)) hf.1
      have hd2 := deg_one_add_le hq1
      have e : P * (1 + q) * g * f = (1 + q) * (P * g * f) := by ring
      rw [e]
      exact absorb hC (hf.2 g hg) (by omega)
  have key := finrank_add_le (LinearMap.mulLeft (ZMod 2) q) (polyLE σ (K - 1))
    (errKer C (zMul P ↑G) K)
  have k1 := Submodule.finrank_mono hi
  have k2 := Submodule.finrank_mono hii
  have k3 : finrank (ZMod 2) ↥(errKer C {P * q} (K - 1)) ≤ finrank (ZMod 2) (polyLE σ (K - 1)) :=
    Submodule.finrank_mono (errKer_le _ _)
  have k4 : finrank (ZMod 2) ↥(errKer C (zMul (P * (1 + q)) ↑G) K)
      ≤ finrank (ZMod 2) (polyLE σ K) := Submodule.finrank_mono (errKer_le _ _)
  have k5 : finrank (ZMod 2) ↥(errKer C (zMul P ↑G) K) ≤ finrank (ZMod 2) (polyLE σ K) :=
    Submodule.finrank_mono (errKer_le _ _)
  unfold errRank at hrr' ⊢
  omega

/-! ## Theorem 4.3 (a): the greedy approximators -/

theorem greedy_arith {c c' c1 h n K t : ℕ} (h1 : 2 * c' + c1 ≤ 2 * c)
    (h2 : c * numMono n (K - 1) ≤ c1 * numMono n K)
    (hb : (c : ℝ) ≤ h * (1 - eta n K) ^ t) :
    (c' : ℝ) ≤ h * (1 - eta n K) ^ (t + 1) := by
  have hN : (0 : ℝ) < numMono n K := by exact_mod_cast numMono_pos n K
  have hN1 : (numMono n (K - 1) : ℝ) ≤ numMono n K := by
    exact_mod_cast numMono_mono n (Nat.sub_le K 1)
  have h1' : (2 : ℝ) * c' + c1 ≤ 2 * c := by exact_mod_cast h1
  have h2' : (c : ℝ) * numMono n (K - 1) ≤ c1 * numMono n K := by exact_mod_cast h2
  have hx : 0 ≤ 1 - eta n K := by
    have hle : eta n K ≤ 1 := by
      unfold eta
      exact (div_le_one (by positivity)).mpr (by linarith)
    linarith
  have he : (c : ℝ) * eta n K ≤ c1 / 2 := by
    unfold eta
    have e1 : (c : ℝ) * (numMono n (K - 1) / (2 * numMono n K))
        = (c * numMono n (K - 1)) / (2 * numMono n K) := by ring
    have e2 : (c1 : ℝ) / 2 = (c1 * numMono n K) / (2 * numMono n K) := by field_simp
    rw [e1, e2]
    gcongr
  calc (c' : ℝ) ≤ c * (1 - eta n K) := by linarith
    _ ≤ (h * (1 - eta n K) ^ t) * (1 - eta n K) := mul_le_mul_of_nonneg_right hb hx
    _ = h * (1 - eta n K) ^ (t + 1) := by ring

/-- Theorem 4.3 (a), from Lemma 4.1 as used and rank retention. -/
theorem greedy (h41 : Stmt41) (h35 : Stmt35) :
    ∀ (σ : Type) [Fintype σ] (C : Submodule (ZMod 2) (MvPolynomial σ (ZMod 2))) (D K t : ℕ)
      (G : Finset (MvPolynomial σ (ZMod 2))),
      DegClosed C D → (∀ g ∈ G, g.totalDegree ≤ 1) → 1 ≤ K → K + t + 1 ≤ D →
      ∃ qs : Fin t → MvPolynomial σ (ZMod 2),
        (∀ j, qs j ∈ Submodule.span (ZMod 2) (↑G : Set (MvPolynomial σ (ZMod 2)))) ∧
        (errRank C (zMul (∏ j, (1 + qs j)) ↑G) K : ℝ)
          ≤ hCodim C K * (1 - eta (Fintype.card σ) K) ^ t := by
  intro σ _ C D K t G hC hG hK
  have hG' : ∀ g ∈ (↑G : Set (MvPolynomial σ (ZMod 2))), g.totalDegree ≤ 1 :=
    fun g hg => hG g (Finset.mem_coe.mp hg)
  induction t with
  | zero =>
    intro hD
    refine ⟨fun _ => 0, fun j => j.elim0, ?_⟩
    rw [Fin.prod_univ_zero, pow_zero, mul_one]
    exact_mod_cast errRank_one_le hC hG' (by omega)
  | succ t ih =>
    intro hD
    obtain ⟨qs, hqs, hb⟩ := ih (by omega)
    have hP : (∏ j, (1 + qs j)).totalDegree ≤ t :=
      deg_prod_le qs (fun j => deg_le_one_of_mem_span hG' (hqs j))
    obtain ⟨q, hq, hgain⟩ := gain h35 σ C D t K _ G hC hP hG hK (by omega)
    have h41' := h41 σ C D t K _ (↑G) hC hP hG' (by omega) (K - 1) K (by omega) le_rfl
    refine ⟨Fin.snoc (α := fun _ => MvPolynomial σ (ZMod 2)) qs q, ?_, ?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [Fin.snoc_last]; exact hq
      · rw [Fin.snoc_castSucc]; exact hqs i
    · rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact greedy_arith hgain h41' hb

/-! ## Theorem 4.3 (b): the common multiplier -/

/-- Theorem 4.3 (b), from Lemma 4.1 as used and rank retention. -/
theorem common (h41 : Stmt41) (h35 : Stmt35) :
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
  classical
  intro σ _ C D K t ι S G hC h1 hG hK hD hlt
  have hg : ∀ ν, ∃ qs : Fin t → MvPolynomial σ (ZMod 2), ν ∈ S →
      ((∀ j, qs j ∈ Submodule.span (ZMod 2) (↑(G ν) : Set (MvPolynomial σ (ZMod 2)))) ∧
        (errRank C (zMul (∏ j, (1 + qs j)) ↑(G ν)) K : ℝ)
          ≤ hCodim C K * (1 - eta (Fintype.card σ) K) ^ t) := by
    intro ν
    by_cases hν : ν ∈ S
    · obtain ⟨qs, h⟩ := greedy h41 h35 σ C D K t (G ν) hC (hG ν hν) hK hD
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
      exact mem_polyLE.mpr (by simp)
    exact h1 hone.1
  -- the ranks of all lines together stay below that codimension
  have hsum : ∑ ν ∈ S, errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K < hCodim C K := by
    have hR : ((∑ ν ∈ S, errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K : ℕ) : ℝ)
        < (hCodim C K : ℝ) := by
      push_cast
      calc ∑ ν ∈ S, (errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K : ℝ)
          ≤ ∑ _ν ∈ S, ((hCodim C K : ℝ) * (1 - eta (Fintype.card σ) K) ^ t) :=
            Finset.sum_le_sum (fun ν hν => (hqs ν hν).2)
        _ = (hCodim C K : ℝ) * ((S.card : ℝ) * (1 - eta (Fintype.card σ) K) ^ t) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
        _ < (hCodim C K : ℝ) * 1 := mul_lt_mul_of_pos_left hlt (by exact_mod_cast hpos)
        _ = (hCodim C K : ℝ) := mul_one _
    exact_mod_cast hR
  have hcod : finrank (ZMod 2) (polyLE σ K)
      ≤ finrank (ZMod 2)
          ↥(polyLE σ K ⊓ ⨅ ν ∈ S, errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K)
        + ∑ ν ∈ S, errRank C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K :=
    codim_iInf (polyLE σ K) (fun ν => errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K)
      (fun ν => errKer_le _ _) S
  have hnot : ¬ (polyLE σ K ⊓ ⨅ ν ∈ S, errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K)
      ≤ C ⊓ polyLE σ K := by
    intro hle
    have hm := Submodule.finrank_mono hle
    unfold hCodim at hsum
    omega
  obtain ⟨f, hfI, hfC⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hfE : f ∈ polyLE σ K := hfI.1
  refine ⟨f, qs, mem_polyLE.mp hfE, fun hc => hfC ⟨hc, hfE⟩, fun ν hν => (hqs ν hν).1, ?_⟩
  intro ν hν g hg
  have hfW : f ∈ errKer C (zMul (∏ j, (1 + qs ν j)) ↑(G ν)) K := by
    exact (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hfI.2 ν) hν
  exact (mem_errKer_zMul.mp hfW).2 g (Finset.mem_coe.mpr hg)

end PEqualNP.ProofComplexity.DegSizeGain
