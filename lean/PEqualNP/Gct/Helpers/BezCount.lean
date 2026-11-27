import Mathlib
import PEqualNP.Gct.Helpers.BezFinite

/-!
Helpers for L-gct-042 (count lemma B), the dimension lower bound, with no regular sequence.

Main result `bez_finrank_ge`: if the top forms of `f_1, .., f_n` in `C[x_1, .., x_n]` have only the
trivial common zero, then `dim_C C[x] / (f) >= prod_i totalDegree f_i`.

Route (elementary, no Koszul complex, no Cohen-Macaulay theory):

1. `bez_filtered_gen`: every polynomial `P` of degree at most `T` is a `C`-combination of
   `f^a * x^b` with `sum_i d_i a_i <= T` and `|b| <= D0` (graded Nakayama along the top forms).
2. Hence `C[x]` is a finite module over `A = C[f_1, .., f_n]`, so the `f_i` are algebraically
   independent (transcendence degree).
3. Nakayama (determinant trick) over `A` with the ideal `(f_1, .., f_n)` of `A`: lifts
   `u_1, .., u_s` of a basis of `C[x]/(f)` give `r in A`, `r - 1 in (f)A`, `r * C[x] <= sum A u_l`.
   Algebraic independence gives `r != 0`.
4. Degree bookkeeping: `r * P` for `deg P <= T` lies in the span of `f^a * u_l` with
   `sum_i d_i a_i <= T + E`, so `#{|b| <= T} <= s * #{a : sum d_i a_i <= T + E}`.
5. `prod d * #{a : sum d_i a_i <= T} <= #{|b| <= T + sum d}` and a growth comparison give
   `prod d <= s`.
-/

namespace PEqualNP.Gct.Helpers

open MvPolynomial
open scoped Pointwise

section Count

variable {n : ℕ}

/-- The box `{0..T}^n`. -/
def bezBox (n T : ℕ) : Finset (Fin n → ℕ) := Fintype.piFinset fun _ => Finset.range (T + 1)

/-- Exponents of weighted degree at most `T`. -/
def bezWt (d : Fin n → ℕ) (T : ℕ) : Finset (Fin n → ℕ) :=
  (bezBox n T).filter fun a => ∑ i, d i * a i ≤ T

/-- Exponents of degree at most `T`. -/
def bezSimplex (n T : ℕ) : Finset (Fin n → ℕ) := bezWt (fun _ : Fin n => 1) T

theorem mem_bezWt {d : Fin n → ℕ} (hd : ∀ i, 1 ≤ d i) {T : ℕ} {a : Fin n → ℕ} :
    a ∈ bezWt d T ↔ ∑ i, d i * a i ≤ T := by
  unfold bezWt bezBox
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h => h.2, fun h => ⟨fun i => ?_, h⟩⟩
  rw [Finset.mem_range]
  have h1 : d i * a i ≤ ∑ j, d j * a j :=
    Finset.single_le_sum (f := fun j => d j * a j) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have h2 : a i ≤ d i * a i := Nat.le_mul_of_pos_left _ (hd i)
  omega

theorem mem_bezSimplex {T : ℕ} {a : Fin n → ℕ} : a ∈ bezSimplex n T ↔ ∑ i, a i ≤ T := by
  unfold bezSimplex
  rw [mem_bezWt (fun _ => le_rfl)]
  simp

theorem bezWt_mono {d : Fin n → ℕ} (hd : ∀ i, 1 ≤ d i) {T T' : ℕ} (h : T ≤ T') :
    bezWt d T ⊆ bezWt d T' := fun a ha => by
  rw [mem_bezWt hd] at ha ⊢
  omega

theorem bezWt_add {d : Fin n → ℕ} (hd : ∀ i, 1 ≤ d i) {a b : Fin n → ℕ} {T T' : ℕ}
    (ha : a ∈ bezWt d T) (hb : b ∈ bezWt d T') : a + b ∈ bezWt d (T + T') := by
  rw [mem_bezWt hd] at ha hb ⊢
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  omega

theorem bezSimplex_card_le (T : ℕ) : (bezSimplex n T).card ≤ (T + 1) ^ n := by
  calc (bezSimplex n T).card ≤ (bezBox n T).card := Finset.card_filter_le _ _
    _ = (T + 1) ^ n := by simp [bezBox, Fintype.card_piFinset]

theorem bezSimplex_card_pos : 1 ≤ (bezSimplex n 0).card :=
  Finset.card_pos.mpr ⟨0, mem_bezSimplex.mpr (by simp)⟩

/-- The injection `(a, r) ↦ (d_i a_i + r_i)`, `0 ≤ r_i < d_i`. -/
theorem bez_card_wt_mul {d : Fin n → ℕ} (hd : ∀ i, 1 ≤ d i) (T : ℕ) :
    (bezWt d T).card * ∏ i, d i ≤ (bezSimplex n (T + ∑ i, d i)).card := by
  classical
  have hcard : (bezWt d T ×ˢ Fintype.piFinset fun i => Finset.range (d i)).card =
      (bezWt d T).card * ∏ i, d i := by
    simp [Finset.card_product, Fintype.card_piFinset]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun p => fun i => d i * p.1 i + p.2 i) ?_ ?_
  · intro p hp
    simp only [Finset.coe_product, Finset.mem_coe, Finset.mem_product, Fintype.mem_piFinset,
      Set.mem_prod] at hp
    simp only [Finset.mem_coe]
    rw [mem_bezSimplex, Finset.sum_add_distrib]
    have h1 := (mem_bezWt hd).mp hp.1
    have h2 : ∑ i, p.2 i ≤ ∑ i, d i :=
      Finset.sum_le_sum fun i _ => (Finset.mem_range.mp (hp.2 i)).le
    omega
  · intro p hp q hq hpq
    simp only [Finset.coe_product, Finset.mem_coe, Finset.mem_product, Fintype.mem_piFinset,
      Set.mem_prod] at hp hq
    have key : ∀ i, p.1 i = q.1 i ∧ p.2 i = q.2 i := by
      intro i
      have e := congrFun hpq i
      dsimp only at e
      have hp2 := Finset.mem_range.mp (hp.2 i)
      have hq2 := Finset.mem_range.mp (hq.2 i)
      have hdi : 0 < d i := hd i
      have e1 : (d i * p.1 i + p.2 i) / d i = p.1 i := by
        rw [Nat.mul_add_div hdi, Nat.div_eq_of_lt hp2, add_zero]
      have e2 : (d i * q.1 i + q.2 i) / d i = q.1 i := by
        rw [Nat.mul_add_div hdi, Nat.div_eq_of_lt hq2, add_zero]
      have h11 : p.1 i = q.1 i := by rw [← e1, ← e2, e]
      refine ⟨h11, ?_⟩
      rw [h11] at e
      omega
    exact Prod.ext (funext fun i => (key i).1) (funext fun i => (key i).2)

/-- Growth comparison: `P * B T ≤ s * B (T + K)` for all `T`, with `B` polynomially bounded and
`B 0 ≥ 1`, forces `P ≤ s`. -/
theorem bez_growth (P s K n : ℕ) (B : ℕ → ℕ) (h : ∀ T, P * B T ≤ s * B (T + K))
    (hB : ∀ T, B T ≤ (T + 1) ^ n) (h0 : 1 ≤ B 0) : P ≤ s := by
  by_contra hlt
  push Not at hlt
  have iter : ∀ k, P ^ k * B 0 ≤ s ^ k * B (k * K) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc P ^ (k + 1) * B 0 = P * (P ^ k * B 0) := by ring
        _ ≤ P * (s ^ k * B (k * K)) := Nat.mul_le_mul_left _ ih
        _ = s ^ k * (P * B (k * K)) := by ring
        _ ≤ s ^ k * (s * B (k * K + K)) := Nat.mul_le_mul_left _ (h _)
        _ = s ^ (k + 1) * B ((k + 1) * K) := by rw [add_mul, one_mul]; ring
  have hs : 0 < s := by
    rcases Nat.eq_zero_or_pos s with hs | hs
    · have h1 : P * B 0 ≤ 0 := by simpa [hs] using iter 1
      have h2 : 0 < P * B 0 := Nat.mul_pos (by omega) h0
      omega
    · exact hs
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hr1 : 1 < (P : ℝ) / s := by
    rw [one_lt_div hs']
    exact_mod_cast hlt
  have hrpos : (0 : ℝ) < (P : ℝ) / s := by linarith
  have bound : ∀ k : ℕ, 1 ≤ k → ((P : ℝ) / s) ^ k ≤ ((K : ℝ) + 1) ^ n * (k : ℝ) ^ n := by
    intro k hk
    have h1 : P ^ k ≤ s ^ k * (k * K + 1) ^ n := by
      calc P ^ k ≤ P ^ k * B 0 := Nat.le_mul_of_pos_right _ h0
        _ ≤ s ^ k * B (k * K) := iter k
        _ ≤ s ^ k * (k * K + 1) ^ n := Nat.mul_le_mul_left _ (hB _)
    have h2 : (P : ℝ) ^ k ≤ (s : ℝ) ^ k * ((k : ℝ) * K + 1) ^ n := by exact_mod_cast h1
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have h4 : (k : ℝ) * K + 1 ≤ ((K : ℝ) + 1) * k := by nlinarith
    have h3 : ((k : ℝ) * K + 1) ^ n ≤ (((K : ℝ) + 1) * k) ^ n :=
      pow_le_pow_left₀ (by positivity) h4 n
    rw [div_pow, div_le_iff₀ (by positivity)]
    calc (P : ℝ) ^ k ≤ (s : ℝ) ^ k * ((k : ℝ) * K + 1) ^ n := h2
      _ ≤ (s : ℝ) ^ k * (((K : ℝ) + 1) * k) ^ n := by gcongr
      _ = ((K : ℝ) + 1) ^ n * (k : ℝ) ^ n * (s : ℝ) ^ k := by rw [mul_pow]; ring
  have ht := tendsto_pow_const_div_const_pow_of_one_lt n hr1
  have hc : (0 : ℝ) < 1 / ((K : ℝ) + 1) ^ n := by positivity
  obtain ⟨k, hk1, hk2⟩ :=
    ((ht.eventually (gt_mem_nhds hc)).and (Filter.eventually_ge_atTop 1)).exists
  have hrk : (0 : ℝ) < ((P : ℝ) / s) ^ k := pow_pos hrpos k
  have hb := bound k hk2
  have hK : (0 : ℝ) < ((K : ℝ) + 1) ^ n := by positivity
  rw [div_lt_div_iff₀ hrk hK] at hk1
  nlinarith

end Count

section Poly

variable {n : ℕ} (f : Fin n → MvPolynomial (Fin n) ℂ)

open scoped Classical in
/-- `f^a`. -/
noncomputable def bezMono (a : Fin n → ℕ) : MvPolynomial (Fin n) ℂ := ∏ i, f i ^ a i

theorem bezMono_zero : bezMono f 0 = 1 := by simp [bezMono]

theorem bezMono_add (a b : Fin n → ℕ) : bezMono f (a + b) = bezMono f a * bezMono f b := by
  simp [bezMono, pow_add, Finset.prod_mul_distrib]

theorem bezMono_single (i : Fin n) : bezMono f (Pi.single i 1) = f i := by
  unfold bezMono
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
  simp

theorem bezMono_mem_adjoin (a : Fin n → ℕ) : bezMono f a ∈ Algebra.adjoin ℂ (Set.range f) :=
  Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self i)) _

open scoped Classical in
/-- The products `f^a * u` with `a` of weighted degree at most `T` and `u ∈ U`. -/
noncomputable def bezGen (d : Fin n → ℕ) (U : Finset (MvPolynomial (Fin n) ℂ)) (T : ℕ) :
    Finset (MvPolynomial (Fin n) ℂ) :=
  (bezWt d T ×ˢ U).image fun p => bezMono f p.1 * p.2

open scoped Classical in
/-- The span of `f^a` with `a` of weighted degree at most `T`. -/
noncomputable def bezV (d : Fin n → ℕ) (T : ℕ) : Submodule ℂ (MvPolynomial (Fin n) ℂ) :=
  Submodule.span ℂ ((bezWt d T).image (bezMono f) : Set (MvPolynomial (Fin n) ℂ))

open scoped Classical in
/-- Monomials of degree at most `D0`. -/
noncomputable def bezXs (n D0 : ℕ) : Finset (MvPolynomial (Fin n) ℂ) :=
  (bezSimplex n D0).image fun a => monomial (Finsupp.equivFunOnFinite.symm a) (1 : ℂ)

theorem bezGen_span_mono {d : Fin n → ℕ} (hd : ∀ i, 1 ≤ d i) (U : Finset (MvPolynomial (Fin n) ℂ))
    {T T' : ℕ} (h : T ≤ T') :
    Submodule.span ℂ (bezGen f d U T : Set (MvPolynomial (Fin n) ℂ)) ≤
      Submodule.span ℂ (bezGen f d U T' : Set (MvPolynomial (Fin n) ℂ)) := by
  classical
  apply Submodule.span_mono
  intro x hx
  simp only [bezGen, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product] at hx ⊢
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨p, ⟨bezWt_mono hd h hp.1, hp.2⟩, rfl⟩

theorem bez_V_mul_W {d : Fin n → ℕ} (hd : ∀ i, 1 ≤ d i) {U : Finset (MvPolynomial (Fin n) ℂ)}
    {T T' : ℕ} {x y : MvPolynomial (Fin n) ℂ} (hx : x ∈ bezV f d T)
    (hy : y ∈ Submodule.span ℂ (bezGen f d U T' : Set (MvPolynomial (Fin n) ℂ))) :
    x * y ∈ Submodule.span ℂ (bezGen f d U (T + T') : Set (MvPolynomial (Fin n) ℂ)) := by
  classical
  have hmul := Submodule.mul_mem_mul hx hy
  rw [bezV, Submodule.span_mul_span] at hmul
  refine (Submodule.span_le.mpr ?_) hmul
  rintro _ ⟨p, hp, q, hq, rfl⟩
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hp
  simp only [bezGen, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hq
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨⟨b, u⟩, hbu, rfl⟩ := hq
  rw [Finset.mem_product] at hbu
  apply Submodule.subset_span
  simp only [bezGen, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product]
  exact ⟨(a + b, u), ⟨bezWt_add hd ha hbu.1, hbu.2⟩, by rw [bezMono_add]; ring⟩

theorem bez_V_mul_V {d : Fin n → ℕ} (hd : ∀ i, 1 ≤ d i) {T T' : ℕ} {x y : MvPolynomial (Fin n) ℂ}
    (hx : x ∈ bezV f d T) (hy : y ∈ bezV f d T') : x * y ∈ bezV f d (T + T') := by
  classical
  have hmul := Submodule.mul_mem_mul hx hy
  rw [bezV, bezV, Submodule.span_mul_span] at hmul
  refine (Submodule.span_le.mpr ?_) hmul
  rintro _ ⟨p, hp, q, hq, rfl⟩
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hp hq
  obtain ⟨a, ha, rfl⟩ := hp
  obtain ⟨b, hb, rfl⟩ := hq
  apply Submodule.subset_span
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
  exact ⟨a + b, bezWt_add hd ha hb, bezMono_add f a b⟩

theorem bez_mono_mem_V {d : Fin n → ℕ} {T : ℕ} {a : Fin n → ℕ} (ha : a ∈ bezWt d T) :
    bezMono f a ∈ bezV f d T := by
  classical
  apply Submodule.subset_span
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
  exact ⟨a, ha, rfl⟩

theorem bez_adjoin_mem_V {d : Fin n → ℕ} (hd : ∀ i, 1 ≤ d i) {c : MvPolynomial (Fin n) ℂ}
    (hc : c ∈ Algebra.adjoin ℂ (Set.range f)) : ∃ E, c ∈ bezV f d E := by
  induction hc using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    refine ⟨d i, ?_⟩
    rw [← bezMono_single f i]
    refine bez_mono_mem_V f ((mem_bezWt hd).mpr ?_)
    simp [Pi.single_apply]
  | algebraMap k =>
    refine ⟨0, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one, ← bezMono_zero f]
    exact Submodule.smul_mem _ _ (bez_mono_mem_V f ((mem_bezWt hd).mpr (by simp)))
  | add x y _ _ hx hy =>
    obtain ⟨E1, h1⟩ := hx
    obtain ⟨E2, h2⟩ := hy
    refine ⟨max E1 E2, Submodule.add_mem _ ?_ ?_⟩
    · exact Submodule.span_mono (Finset.coe_subset.mpr (Finset.image_subset_image
        (bezWt_mono hd (le_max_left _ _)))) h1
    · exact Submodule.span_mono (Finset.coe_subset.mpr (Finset.image_subset_image
        (bezWt_mono hd (le_max_right _ _)))) h2
  | mul x y _ _ hx hy =>
    obtain ⟨E1, h1⟩ := hx
    obtain ⟨E2, h2⟩ := hy
    exact ⟨E1 + E2, bez_V_mul_V f hd h1 h2⟩

theorem bez_finset_bound {α : Type*} (S : Finset α) (p : α → ℕ → Prop)
    (hmono : ∀ x E E', E ≤ E' → p x E → p x E') (h : ∀ x ∈ S, ∃ E, p x E) :
    ∃ E, ∀ x ∈ S, p x E := by
  classical
  choose! F hF using h
  exact ⟨S.sup F, fun x hx => hmono x _ _ (Finset.le_sup hx) (hF x hx)⟩

/-- Filtered generation: every polynomial of degree at most `T` is a combination of `f^a * x^b`
with `sum_i d_i a_i ≤ T` and `|b| ≤ D0`. -/
theorem bez_filtered_gen
    (hinf : ∀ x : Fin n → ℂ,
      (∀ i, eval x (homogeneousComponent (f i).totalDegree (f i)) = 0) → x = 0)
    (hd : ∀ i, 1 ≤ (f i).totalDegree) :
    ∃ D0 : ℕ, ∀ (P : MvPolynomial (Fin n) ℂ) (T : ℕ), P.totalDegree ≤ T →
      P ∈ Submodule.span ℂ
        (bezGen f (fun i => (f i).totalDegree) (bezXs n D0) T : Set (MvPolynomial (Fin n) ℂ)) := by
  classical
  set d : Fin n → ℕ := fun i => (f i).totalDegree with hd_def
  have hd' : ∀ i, 1 ≤ d i := hd
  set g : Fin n → MvPolynomial (Fin n) ℂ := fun i => homogeneousComponent (d i) (f i) with hg
  obtain ⟨D0, hED0, hD0⟩ := bez_monomial_mem g hinf (∑ i, d i)
  have hdD0 : ∀ i, d i ≤ D0 := fun i =>
    (Finset.single_le_sum (fun j _ => Nat.zero_le (d j)) (Finset.mem_univ i)).trans hED0.le
  refine ⟨D0, fun P => ?_⟩
  induction hdeg : P.totalDegree using Nat.strong_induction_on generalizing P with
  | _ D ih =>
  intro T hT
  by_cases hlt : D < D0
  · rw [P.as_sum]
    refine Submodule.sum_mem _ fun s hs => ?_
    have hsdeg : s.degree ≤ D := by
      have := le_totalDegree hs
      rw [hdeg] at this
      exact this
    have hmono : monomial s (P.coeff s) = P.coeff s • monomial s (1 : ℂ) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hmono]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    simp only [bezGen, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product]
    refine ⟨(0, monomial s 1), ⟨(mem_bezWt hd').mpr (by simp), ?_⟩, by simp [bezMono_zero]⟩
    simp only [bezXs, Finset.mem_image]
    refine ⟨⇑s, mem_bezSimplex.mpr ?_, by simp⟩
    rw [← Finsupp.degree_eq_sum]
    omega
  push Not at hlt
  have hD : 0 < D := by omega
  obtain ⟨a, ha, hpa⟩ := bez_homog_decomp g d (fun i => homogeneousComponent_isHomogeneous _ _)
    D0 hdD0 hD0 hlt (homogeneousComponent D P) (homogeneousComponent_isHomogeneous _ _)
  set p' := P - ∑ i, f i * a i with hp'
  have hlt' : p'.totalDegree < D := by
    have hp'eq : p' = (P - homogeneousComponent D P) - ∑ i, (f i - g i) * a i := by
      rw [hp', hpa]
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    rw [hp'eq]
    refine lt_of_le_of_lt (totalDegree_sub _ _) (max_lt ?_ ?_)
    · exact bez_totalDegree_sub_homogeneousComponent_lt P hdeg.le hD
    · have hsum : (∑ i, (f i - g i) * a i).totalDegree ≤ D - 1 := by
        refine totalDegree_finsetSum_le fun i _ => ?_
        have hai : (a i).totalDegree ≤ D - d i := (ha i).totalDegree_le
        refine (totalDegree_mul _ _).trans ?_
        have hfg : (f i - g i).totalDegree < d i :=
          bez_totalDegree_sub_homogeneousComponent_lt (f i) le_rfl (hd i)
        have := hdD0 i
        omega
      omega
  have hP : P = p' + ∑ i, f i * a i := by rw [hp']; ring
  rw [hP]
  refine Submodule.add_mem _ (ih _ hlt' p' rfl T (by omega)) (Submodule.sum_mem _ fun i _ => ?_)
  have hai : (a i).totalDegree ≤ D - d i := (ha i).totalDegree_le
  have hdi := hd' i
  have hdi' := hdD0 i
  have hmem := ih _ (by omega : (a i).totalDegree < D) (a i) rfl (T - d i) (by omega)
  have hfi : f i ∈ bezV f d (d i) := by
    rw [← bezMono_single f i]
    refine bez_mono_mem_V f ((mem_bezWt hd').mpr ?_)
    simp [Pi.single_apply]
  have := bez_V_mul_W f hd' hfi hmem
  rwa [Nat.add_sub_cancel' (by omega : d i ≤ T)] at this

/-- **Dimension lower bound.** If the top forms of `f` have only the trivial common zero, then
`dim_C C[x]/(f) ≥ prod_i totalDegree f_i`. -/
theorem bez_finrank_ge
    (hinf : ∀ x : Fin n → ℂ,
      (∀ i, eval x (homogeneousComponent (f i).totalDegree (f i)) = 0) → x = 0) :
    ∏ i, (f i).totalDegree ≤
      Module.finrank ℂ (MvPolynomial (Fin n) ℂ ⧸ Ideal.span (Set.range f)) := by
  classical
  set d : Fin n → ℕ := fun i => (f i).totalDegree with hd_def
  by_cases hz : ∃ i, d i = 0
  · obtain ⟨i, hi⟩ := hz
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi]
    exact Nat.zero_le _
  push Not at hz
  have hd : ∀ i, 1 ≤ d i := fun i => Nat.one_le_iff_ne_zero.mpr (hz i)
  obtain ⟨D0, hgen⟩ := bez_filtered_gen f hinf hd
  -- `C[x]` is a finite module over `A = C[f]`.
  have hspanA : Submodule.span (Algebra.adjoin ℂ (Set.range f))
      (bezXs n D0 : Set (MvPolynomial (Fin n) ℂ)) = ⊤ := by
    rw [eq_top_iff]
    intro P _
    have h1 := hgen P _ le_rfl
    have h2 : Submodule.span ℂ (bezGen f d (bezXs n D0) P.totalDegree :
        Set (MvPolynomial (Fin n) ℂ)) ≤ (Submodule.span (Algebra.adjoin ℂ (Set.range f))
          (bezXs n D0 : Set (MvPolynomial (Fin n) ℂ))).restrictScalars ℂ := by
      rw [Submodule.span_le]
      intro x hx
      simp only [bezGen, Finset.coe_image, Set.mem_image, Finset.mem_coe,
        Finset.mem_product] at hx
      obtain ⟨⟨a, u⟩, hp, rfl⟩ := hx
      have : bezMono f a * u =
          (⟨bezMono f a, bezMono_mem_adjoin f a⟩ : Algebra.adjoin ℂ (Set.range f)) • u := by
        rw [Subalgebra.smul_def]
        rfl
      rw [SetLike.mem_coe, Submodule.restrictScalars_mem, this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hp.2)
    exact h2 h1
  haveI hfin : Module.Finite (Algebra.adjoin ℂ (Set.range f)) (MvPolynomial (Fin n) ℂ) :=
    ⟨⟨bezXs n D0, hspanA⟩⟩
  -- The `f_i` are algebraically independent.
  have hindep : AlgebraicIndependent ℂ f := by
    haveI : Algebra.IsIntegral (Algebra.adjoin ℂ (Set.range f)) (MvPolynomial (Fin n) ℂ) :=
      inferInstance
    haveI : Algebra.IsAlgebraic (Algebra.adjoin ℂ (Set.range f)) (MvPolynomial (Fin n) ℂ) :=
      inferInstance
    refine (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℂ f ?_).1
    rw [MvPolynomial.trdeg_of_isDomain]
    simp
  -- Nakayama over `A`.
  haveI : Module.Finite ℂ (MvPolynomial (Fin n) ℂ ⧸ Ideal.span (Set.range f)) :=
    bez_finite_quotient f hinf
  set s := Module.finrank ℂ (MvPolynomial (Fin n) ℂ ⧸ Ideal.span (Set.range f)) with hs_def
  let b := Module.finBasis ℂ (MvPolynomial (Fin n) ℂ ⧸ Ideal.span (Set.range f))
  have hu : ∀ l, ∃ p, Ideal.Quotient.mk (Ideal.span (Set.range f)) p = b l :=
    fun l => Ideal.Quotient.mk_surjective _
  choose u hu using hu
  set U : Finset (MvPolynomial (Fin n) ℂ) := Finset.univ.image u with hU
  let fA : Fin n → Algebra.adjoin ℂ (Set.range f) := fun i => ⟨f i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  have hsup : (⊤ : Submodule (Algebra.adjoin ℂ (Set.range f)) (MvPolynomial (Fin n) ℂ)) ≤
      Submodule.span (Algebra.adjoin ℂ (Set.range f)) (U : Set (MvPolynomial (Fin n) ℂ)) ⊔
        (Ideal.span (Set.range fA)) • ⊤ := by
    intro m _
    set v := ∑ l, b.repr (Ideal.Quotient.mk (Ideal.span (Set.range f)) m) l • u l with hv
    have hvq : Ideal.Quotient.mk (Ideal.span (Set.range f)) v =
        Ideal.Quotient.mk (Ideal.span (Set.range f)) m := by
      rw [hv, map_sum]
      conv_rhs => rw [← b.sum_repr (Ideal.Quotient.mk (Ideal.span (Set.range f)) m)]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← hu l, Algebra.smul_def, map_mul, Ideal.Quotient.mk_algebraMap, ← Algebra.smul_def]
    have hmv : m - v ∈ Ideal.span (Set.range f) := Ideal.Quotient.eq.mp hvq.symm
    rw [Submodule.mem_sup]
    refine ⟨v, ?_, m - v, ?_, by ring⟩
    · refine Submodule.sum_mem _ fun l _ => Submodule.smul_of_tower_mem _ _
        (Submodule.subset_span ?_)
      simp [hU]
    · obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmv
      rw [← hc]
      refine Submodule.sum_mem _ fun i _ => ?_
      have : c i * f i = fA i • c i := by
        rw [Subalgebra.smul_def, smul_eq_mul, mul_comm]
      rw [this]
      exact Submodule.smul_mem_smul (Ideal.subset_span ⟨i, rfl⟩) Submodule.mem_top
  obtain ⟨r, hr1, hrle⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (Module.Finite.fg_top) le_rfl hsup
  -- `r ≠ 0`.
  have hr0 : (r : MvPolynomial (Fin n) ℂ) ≠ 0 := by
    intro hr0
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hr1
    have hc' := congrArg Subtype.val hc
    have hmem : ∀ i, ∃ γ : MvPolynomial (Fin n) ℂ, aeval f γ = (c i : MvPolynomial (Fin n) ℂ) :=
      fun i => by
        have h : (c i : MvPolynomial (Fin n) ℂ) ∈
            (aeval f : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ).range := by
          rw [← Algebra.adjoin_range_eq_range_aeval]
          exact (c i).2
        exact (AlgHom.mem_range _).mp h
    choose γ hγ using hmem
    have key : aeval f ((1 : MvPolynomial (Fin n) ℂ) + ∑ i, γ i * X i) =
        aeval f (0 : MvPolynomial (Fin n) ℂ) := by
      rw [map_zero, map_add, map_one, map_sum]
      simp only [map_mul, aeval_X, hγ]
      push_cast at hc'
      rw [hc', hr0]
      ring
    have h0 := congrArg constantCoeff (hindep key)
    simp at h0
  -- Degree control on the Nakayama element.
  have hWA : ∀ y ∈ Submodule.span (Algebra.adjoin ℂ (Set.range f)) (U : Set (MvPolynomial (Fin n) ℂ)),
      ∃ E, y ∈ Submodule.span ℂ (bezGen f d U E : Set (MvPolynomial (Fin n) ℂ)) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      refine ⟨0, Submodule.subset_span ?_⟩
      simp only [bezGen, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product]
      exact ⟨(0, x), ⟨(mem_bezWt hd).mpr (by simp), hx⟩, by simp [bezMono_zero]⟩
    | zero => exact ⟨0, Submodule.zero_mem _⟩
    | add x y _ _ hx hy =>
      obtain ⟨E1, h1⟩ := hx
      obtain ⟨E2, h2⟩ := hy
      exact ⟨max E1 E2, Submodule.add_mem _ (bezGen_span_mono f hd U (le_max_left _ _) h1)
        (bezGen_span_mono f hd U (le_max_right _ _) h2)⟩
    | smul c x _ hx =>
      obtain ⟨E, h⟩ := hx
      obtain ⟨E', h'⟩ := bez_adjoin_mem_V f hd c.2
      refine ⟨E' + E, ?_⟩
      rw [Subalgebra.smul_def, smul_eq_mul]
      exact bez_V_mul_W f hd h' h
  obtain ⟨E, hE⟩ := bez_finset_bound (bezXs n D0)
    (fun u0 E => (r : MvPolynomial (Fin n) ℂ) * u0 ∈
      Submodule.span ℂ (bezGen f d U E : Set (MvPolynomial (Fin n) ℂ)))
    (fun x E E' h hx => bezGen_span_mono f hd U h hx)
    (fun u0 _ => by
      have h1 := hrle (Submodule.smul_mem_pointwise_smul u0 r ⊤ Submodule.mem_top)
      have h2 := hWA _ h1
      rwa [Subalgebra.smul_def, smul_eq_mul] at h2)
  have hrP : ∀ (T : ℕ) (P : MvPolynomial (Fin n) ℂ), P.totalDegree ≤ T →
      (r : MvPolynomial (Fin n) ℂ) * P ∈
        Submodule.span ℂ (bezGen f d U (T + E) : Set (MvPolynomial (Fin n) ℂ)) := by
    intro T P hP
    have h1 := hgen P T hP
    have h2 : Submodule.span ℂ (bezGen f d (bezXs n D0) T : Set (MvPolynomial (Fin n) ℂ)) ≤
        (Submodule.span ℂ (bezGen f d U (T + E) : Set (MvPolynomial (Fin n) ℂ))).comap
          (LinearMap.mulLeft ℂ (r : MvPolynomial (Fin n) ℂ)) := by
      rw [Submodule.span_le]
      intro x hx
      simp only [bezGen, Finset.coe_image, Set.mem_image, Finset.mem_coe,
        Finset.mem_product] at hx
      obtain ⟨⟨a, u0⟩, hp, rfl⟩ := hx
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
      rw [show (r : MvPolynomial (Fin n) ℂ) * (bezMono f a * u0) =
        bezMono f a * ((r : MvPolynomial (Fin n) ℂ) * u0) by ring]
      exact bez_V_mul_W f hd (bez_mono_mem_V f hp.1) (hE u0 hp.2)
    exact h2 h1
  -- Counting.
  have hcount : ∀ T, (bezSimplex n T).card ≤ s * (bezWt d (T + E)).card := by
    intro T
    let v : bezSimplex n T → MvPolynomial (Fin n) ℂ := fun a =>
      (r : MvPolynomial (Fin n) ℂ) * monomial (Finsupp.equivFunOnFinite.symm a.1) 1
    have hli : LinearIndependent ℂ v := by
      have h1 := ((MvPolynomial.basisMonomials (Fin n) ℂ).linearIndependent.comp _
          (Finsupp.equivFunOnFinite.symm.injective)).comp (Subtype.val : bezSimplex n T → _)
          Subtype.val_injective
      exact h1.map' (LinearMap.mulLeft ℂ (r : MvPolynomial (Fin n) ℂ))
        (LinearMap.ker_eq_bot.mpr (mul_right_injective₀ hr0))
    have hrange : Set.range v ≤
        Submodule.span ℂ (bezGen f d U (T + E) : Set (MvPolynomial (Fin n) ℂ)) := by
      rintro _ ⟨a, rfl⟩
      apply hrP T
      rw [totalDegree_monomial _ one_ne_zero]
      have h := mem_bezSimplex.mp a.2
      have : (Finsupp.equivFunOnFinite.symm a.1).sum (fun _ e => e) =
          (Finsupp.equivFunOnFinite.symm a.1).degree := rfl
      rw [this, Finsupp.degree_eq_sum]
      simpa using h
    have hle := linearIndependent_le_span' v hli _ hrange
    simp only [Cardinal.mk_fintype, Fintype.card_coe, Nat.cast_le, Finset.coe_sort_coe] at hle
    have hUc : U.card ≤ s := by
      rw [hU]
      refine Finset.card_image_le.trans ?_
      simp [hs_def]
    calc (bezSimplex n T).card ≤ (bezGen f d U (T + E)).card := hle
      _ ≤ (bezWt d (T + E) ×ˢ U).card := Finset.card_image_le
      _ = (bezWt d (T + E)).card * U.card := Finset.card_product _ _
      _ ≤ (bezWt d (T + E)).card * s := Nat.mul_le_mul_left _ hUc
      _ = s * (bezWt d (T + E)).card := Nat.mul_comm _ _
  have hfinal : ∀ T, (∏ i, d i) * (bezSimplex n T).card ≤
      s * (bezSimplex n (T + (E + ∑ i, d i))).card := by
    intro T
    calc (∏ i, d i) * (bezSimplex n T).card ≤ (∏ i, d i) * (s * (bezWt d (T + E)).card) :=
          Nat.mul_le_mul_left _ (hcount T)
      _ = s * ((bezWt d (T + E)).card * ∏ i, d i) := by ring
      _ ≤ s * (bezSimplex n (T + E + ∑ i, d i)).card :=
          Nat.mul_le_mul_left _ (bez_card_wt_mul hd _)
      _ = s * (bezSimplex n (T + (E + ∑ i, d i))).card := by rw [add_assoc]
  exact bez_growth _ s _ n (fun T => (bezSimplex n T).card) hfinal bezSimplex_card_le
    bezSimplex_card_pos

end Poly

end PEqualNP.Gct.Helpers
