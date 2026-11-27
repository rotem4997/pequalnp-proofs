import PEqualNP.Defs
import PEqualNP.Gct.Helpers.FermatFromKneser
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Roots

/-! Helper for L-gct-067, proofs only. The Kneser statement for codes over `ℂ` (the form of
L-gct-065) implies the iterated Fermat bound: a subspace `W` of `ℂ^M` on which the power sums
`∑ x_i^j`, `2 ≤ j ≤ k`, all vanish has `k * dim W ≤ M`. This generalizes the order 3 proof of
`FermatFromKneser.lean`: with `S = W + ℂ1` and the chain `V_a = S^a W`, polarization gives
`V_(k-2) ⊥ W`; one splits along an idempotent of the stabilizer of `V_(k-2)`, and when that
stabilizer is the scalars so are the stabilizers of all `V_a`, `a ≤ k - 2`, and Kneser applied
to `(S, V_a)` gives `dim V_(a+1) ≥ dim V_a + dim W`. -/

namespace PEqualNP.Gct.Helpers.FermatIter

open Module Finset PEqualNP.Gct.Helpers

section General

variable {ι : Type} [Fintype ι]

/-- The chain `V_a = (W + ℂ1)^a W = W + W^2 + ... + W^(a+1)`. -/
noncomputable def vChain (W : Submodule ℂ (ι → ℂ)) (a : ℕ) : Submodule ℂ (ι → ℂ) :=
  (W + 1) ^ a * W

/-- The orthogonal of `W` for the dot product (no conjugation). -/
def perp (W : Submodule ℂ (ι → ℂ)) : Submodule ℂ (ι → ℂ) where
  carrier := {v | ∀ z ∈ W, ∑ i, v i * z i = 0}
  add_mem' {a b} ha hb z hz := by
    simp only [Pi.add_apply, add_mul, sum_add_distrib, ha z hz, hb z hz, add_zero]
  zero_mem' z _ := by simp
  smul_mem' c x hx z hz := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum, hx z hz, mul_zero]

theorem mem_perp {W : Submodule ℂ (ι → ℂ)} {v : ι → ℂ} :
    v ∈ perp W ↔ ∀ z ∈ W, ∑ i, v i * z i = 0 := Iff.rfl

/-- One polarization step: if `∑ x_i^(n+1) c_i` vanishes for `x` in `W`, then so does
`∑ x_i^n y_i c_i` for `x`, `y` in `W` (derivative at `0` of a polynomial that is zero). -/
theorem polar_step (W : Submodule ℂ (ι → ℂ)) (c : ι → ℂ) (n : ℕ)
    (h : ∀ x ∈ W, ∑ i, x i ^ (n + 1) * c i = 0) :
    ∀ x ∈ W, ∀ y ∈ W, ∑ i, x i ^ n * (y i * c i) = 0 := by
  intro x hx y hy
  let q : Polynomial ℂ := ∑ i, Polynomial.C (c i) *
    (Polynomial.C (x i) + Polynomial.C (y i) * Polynomial.X) ^ (n + 1)
  have hq : q = 0 := by
    apply Polynomial.funext
    intro t
    have := h (x + t • y) (W.add_mem hx (W.smul_mem t hy))
    simp only [q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_zero]
    rw [← this]
    refine sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hd : Polynomial.eval 0 (Polynomial.derivative q) = 0 := by
    rw [hq]; simp
  have hd2 : Polynomial.eval 0 (Polynomial.derivative q) =
      ((n : ℂ) + 1) * ∑ i, x i ^ n * (y i * c i) := by
    simp only [q, Polynomial.derivative_sum, Polynomial.eval_finsetSum, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    simp [Polynomial.derivative_pow]
    ring
  rw [hd2] at hd
  exact (mul_eq_zero.1 hd).resolve_left (Nat.cast_add_one_ne_zero n)

/-- Polarization against powers of `W`: if the power sums of orders `2..k` vanish on `W`, then
`∑ x_i^n c_i = 0` for `x` in `W` and `c` in `W^r`, whenever `2 ≤ n + r ≤ k`. -/
theorem pow_perp (W : Submodule ℂ (ι → ℂ)) (k : ℕ)
    (h : ∀ j : ℕ, 2 ≤ j → j ≤ k → ∀ x ∈ W, ∑ i, x i ^ j = 0) :
    ∀ r n : ℕ, 2 ≤ n + r → n + r ≤ k → ∀ c ∈ W ^ r, ∀ x ∈ W, ∑ i, x i ^ n * c i = 0 := by
  intro r
  induction r with
  | zero =>
    intro n h2 hk c hc x hx
    rw [pow_zero, Submodule.one_eq_span] at hc
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hc
    have := h n h2 hk x hx
    simp only [Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one, ← sum_mul, this, zero_mul]
  | succ r ih =>
    intro n h2 hk c hc
    rw [pow_succ] at hc
    refine Submodule.mul_induction_on hc ?_ ?_
    · intro c' hc' y hy x hx
      have := polar_step W c' n (ih (n + 1) (by omega) (by omega) c' hc') x hx y hy
      refine (sum_congr rfl fun i _ => ?_).trans this
      rw [Pi.mul_apply, mul_comm (c' i)]
    · intro a b ha hb x hx
      simp only [Pi.add_apply, mul_add, sum_add_distrib, ha x hx, hb x hx, add_zero]

/-- The products `(W + ℂ1)^a W^b` with `1 ≤ b` and `a + b + 1 ≤ k` are orthogonal to `W`. -/
theorem chain_le_perp (W : Submodule ℂ (ι → ℂ)) (k : ℕ)
    (h : ∀ j : ℕ, 2 ≤ j → j ≤ k → ∀ x ∈ W, ∑ i, x i ^ j = 0) :
    ∀ a b : ℕ, 1 ≤ b → a + b + 1 ≤ k → (W + 1) ^ a * W ^ b ≤ perp W := by
  intro a
  induction a with
  | zero =>
    intro b hb hk v hv z hz
    rw [pow_zero, one_mul] at hv
    have := pow_perp W k h b 1 (by omega) (by omega) v hv z hz
    refine (sum_congr rfl fun i _ => ?_).trans this
    rw [pow_one, mul_comm]
  | succ a ih =>
    intro b hb hk
    have e : (W + 1) ^ (a + 1) * W ^ b = (W + 1) ^ a * W ^ (b + 1) + (W + 1) ^ a * W ^ b := by
      ring
    rw [e, Submodule.add_eq_sup]
    exact sup_le (ih (b + 1) (by omega) (by omega)) (ih b hb (by omega))

/-- Polarization, in the form used below: `V_(k-2) ⊥ W`. -/
theorem vChain_perp_of_psum (W : Submodule ℂ (ι → ℂ)) (a : ℕ)
    (h : ∀ j : ℕ, 2 ≤ j → j ≤ a + 2 → ∀ x ∈ W, ∑ i, x i ^ j = 0) :
    ∀ v ∈ vChain W a, ∀ z ∈ W, ∑ i, v i * z i = 0 := by
  intro v hv
  have := chain_le_perp W (a + 2) h a 1 le_rfl le_rfl
  rw [pow_one] at this
  exact this hv

omit [Fintype ι] in
theorem one_mem_add_one (W : Submodule ℂ (ι → ℂ)) : (1 : ι → ℂ) ∈ W + 1 :=
  Submodule.one_le.1 (le_sup_right : (1 : Submodule ℂ (ι → ℂ)) ≤ W ⊔ 1)

omit [Fintype ι] in
theorem vChain_zero (W : Submodule ℂ (ι → ℂ)) : vChain W 0 = W := by
  unfold vChain; rw [pow_zero, one_mul]

omit [Fintype ι] in
theorem vChain_succ (W : Submodule ℂ (ι → ℂ)) (a : ℕ) :
    vChain W (a + 1) = (W + 1) * vChain W a := by
  unfold vChain; rw [pow_succ', mul_assoc]

omit [Fintype ι] in
theorem le_vChain (W : Submodule ℂ (ι → ℂ)) (a : ℕ) : W ≤ vChain W a := by
  induction a with
  | zero => rw [vChain_zero]
  | succ a ih =>
    intro u hu
    rw [vChain_succ]
    have := Submodule.mul_mem_mul (one_mem_add_one W) (ih hu)
    rwa [one_mul] at this

omit [Fintype ι] in
/-- A stabilizer of `X` stabilizes `S X`. -/
theorem stab_le_stab_mul (S X : Submodule ℂ (ι → ℂ)) : stab X ≤ stab (S * X) := by
  intro x hx v hv
  refine Submodule.mul_induction_on hv ?_ ?_
  · intro s hs t ht
    rw [mul_left_comm]
    exact Submodule.mul_mem_mul hs (hx t ht)
  · intro a b ha hb
    rw [mul_add]
    exact Submodule.add_mem _ ha hb

omit [Fintype ι] in
theorem stab_vChain_mono (W : Submodule ℂ (ι → ℂ)) {a b : ℕ} (h : a ≤ b) :
    stab (vChain W a) ≤ stab (vChain W b) := by
  induction b, h using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih =>
    rw [vChain_succ]
    exact ih.trans (stab_le_stab_mul _ _)

/-- Restriction to the coordinates where `p` is one, as an algebra map. -/
noncomputable def restrAlg (p : ι → ℂ) : (ι → ℂ) →ₐ[ℂ] ({k // p k = 1} → ℂ) where
  toFun u k := u k
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

omit [Fintype ι] in
theorem restrAlg_toLinearMap (p : ι → ℂ) : (restrAlg p).toLinearMap = restr p := rfl

omit [Fintype ι] in
/-- The chain commutes with restriction. -/
theorem vChain_map (W : Submodule ℂ (ι → ℂ)) (p : ι → ℂ) (a : ℕ) :
    vChain (W.map (restr p)) a = (vChain W a).map (restr p) := by
  unfold vChain
  rw [← restrAlg_toLinearMap, Submodule.map_mul, Submodule.map_pow]
  simp only [Submodule.add_eq_sup, Submodule.map_sup, Submodule.map_one]

/-- The restriction of `W` along a 0/1 element of the stabilizer of `V_a` again has its chain
orthogonal to it. -/
theorem restr_perp {W : Submodule ℂ (ι → ℂ)} {a : ℕ}
    (hW : ∀ v ∈ vChain W a, ∀ z ∈ W, ∑ i, v i * z i = 0) {p : ι → ℂ}
    (hp : p ∈ stab (vChain W a)) (hp01 : ∀ k, p k = 0 ∨ p k = 1) :
    ∀ v ∈ vChain (W.map (restr p)) a, ∀ z ∈ W.map (restr p), ∑ i, v i * z i = 0 := by
  intro v hv z hz
  rw [vChain_map] at hv
  obtain ⟨v, hv, rfl⟩ := hv
  obtain ⟨z, hz, rfl⟩ := hz
  simp only [restr_apply]
  rw [sum_restr p hp01 (fun k => v k * z k)]
  have := hW _ (hp _ hv) z hz
  simpa only [Pi.mul_apply, mul_assoc] using this

end General

/-- The iterated Fermat bound for a chain orthogonal to `W`, on any finite index type, given
Kneser: if `V_a ⊥ W` then `(a + 2) dim W ≤ |ι|`. -/
theorem fermat_iter_general (hK : ∀ (ι : Type) [Fintype ι], KneserFor ι) (a : ℕ) :
    ∀ (n : ℕ) (ι : Type) [Fintype ι], Fintype.card ι = n →
      ∀ W : Submodule ℂ (ι → ℂ), (∀ v ∈ vChain W a, ∀ z ∈ W, ∑ i, v i * z i = 0) →
        (a + 2) * finrank ℂ W ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro ι _ hcard W hW
  classical
  by_cases hW0 : W = ⊥
  · rw [hW0, finrank_bot]; simp
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨i₀, -⟩ := Function.ne_iff.1 hu0
  have : Nonempty ι := ⟨i₀⟩
  have hone : (1 : ι → ℂ) ∉ W := by
    intro h
    have := hW 1 (le_vChain W a h) 1 h
    simp only [Pi.one_apply, mul_one, sum_const, card_univ, nsmul_eq_mul] at this
    exact Fintype.card_ne_zero (Nat.cast_eq_zero.1 this)
  by_cases hconst : ∀ x ∈ stab (vChain W a), ∀ j k, x j = x k
  · -- the stabilizer is the scalars: apply Kneser along the chain
    have hSt : ∀ b, b ≤ a → finrank ℂ (stab (vChain W b)) ≤ 1 := by
      intro b hb
      have : stab (vChain W b) ≤ Submodule.span ℂ {(1 : ι → ℂ)} := by
        intro x hx
        rw [Submodule.mem_span_singleton]
        refine ⟨x i₀, ?_⟩
        funext k
        simp [hconst x (stab_vChain_mono W hb hx) i₀ k]
      exact (Submodule.finrank_mono this).trans (finrank_span_singleton one_ne_zero).le
    have hS : W + 1 = W ⊔ Submodule.span ℂ {(1 : ι → ℂ)} := by
      rw [Submodule.add_eq_sup, Submodule.one_eq_span]
    have hU : finrank ℂ ↥(W + 1) = finrank ℂ W + 1 := by
      rw [hS]
      have hinf : W ⊓ Submodule.span ℂ {(1 : ι → ℂ)} = ⊥ := by
        rw [eq_bot_iff]
        intro x ⟨hxW, hx1⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx1
        rw [Submodule.mem_bot]
        by_contra hc
        have hc' : c ≠ 0 := by rintro rfl; exact hc (zero_smul _ _)
        apply hone
        have := W.smul_mem c⁻¹ hxW
        rwa [smul_smul, inv_mul_cancel₀ hc', one_smul] at this
      have h := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span ℂ {(1 : ι → ℂ)})
      rw [hinf, finrank_bot, add_zero,
        finrank_span_singleton (one_ne_zero : (1 : ι → ℂ) ≠ 0)] at h
      exact h
    have hUne : W + 1 ≠ ⊥ := by
      intro h
      have := one_mem_add_one W
      rw [h, Submodule.mem_bot] at this
      exact one_ne_zero this
    have hVne : ∀ b, vChain W b ≠ ⊥ := by
      intro b h
      apply hW0
      rw [eq_bot_iff, ← h]
      exact le_vChain W b
    have grow : ∀ b, b ≤ a → (b + 1) * finrank ℂ W ≤ finrank ℂ (vChain W b) := by
      intro b
      induction b with
      | zero => intro _; rw [vChain_zero]; simp
      | succ b ih =>
        intro hb
        have ih' := ih (by omega)
        have hk := hK ι (W + 1) (vChain W b) (stab ((W + 1) * vChain W b)) hUne (hVne b)
          (fun x => Iff.rfl)
        rw [← vChain_succ] at hk
        have hs := hSt (b + 1) hb
        have e : (b + 1 + 1) * finrank ℂ W = (b + 1) * finrank ℂ W + finrank ℂ W := by ring
        rw [e]
        omega
    have hg := grow a le_rfl
    have hp := perp_bound (vChain W a) W hW
    have e : (a + 2) * finrank ℂ W = (a + 1) * finrank ℂ W + finrank ℂ W := by ring
    rw [e]
    omega
  · push Not at hconst
    obtain ⟨x, hx, j, k, hjk⟩ := hconst
    obtain ⟨e, he, hev⟩ := exists_indicator hx j
    have he01 : ∀ l, e l = 0 ∨ e l = 1 := fun l => by
      rw [hev l]; split_ifs <;> simp
    set f : ι → ℂ := 1 - e with hf
    have hfS : f ∈ stab (vChain W a) :=
      (stab (vChain W a)).sub_mem (one_mem_stab (vChain W a)) he
    have hf01 : ∀ l, f l = 0 ∨ f l = 1 := fun l => by
      rcases he01 l with h | h <;> simp [hf, h]
    have hej : e j = 1 := by rw [hev]; simp
    have hek : e k = 0 := by rw [hev]; simp [Ne.symm hjk]
    have hcB : Fintype.card {l // e l = 1} < n := by
      rw [← hcard]; exact Fintype.card_subtype_lt (x := k) (by rw [hek]; exact zero_ne_one)
    have hcB' : Fintype.card {l // f l = 1} < n := by
      rw [← hcard]; exact Fintype.card_subtype_lt (x := j) (by simp [hf, hej])
    have hsum : Fintype.card {l // e l = 1} + Fintype.card {l // f l = 1} ≤ n := by
      rw [Fintype.card_subtype, Fintype.card_subtype, ← hcard,
        ← Finset.card_union_of_disjoint]
      · exact Finset.card_le_univ _
      · rw [Finset.disjoint_filter]
        intro l _ h1 h2
        simp [hf, h1] at h2
    have h1 := IH _ hcB {l // e l = 1} rfl _ (restr_perp hW he he01)
    have h2 := IH _ hcB' {l // f l = 1} rfl _ (restr_perp hW hfS hf01)
    have h3 := finrank_split W e f (fun l => by
      rcases he01 l with h | h
      · right; simp [hf, h]
      · left; exact h)
    calc (a + 2) * finrank ℂ W
        ≤ (a + 2) * (finrank ℂ (W.map (restr e)) + finrank ℂ (W.map (restr f))) :=
          Nat.mul_le_mul_left _ h3
      _ = (a + 2) * finrank ℂ (W.map (restr e)) + (a + 2) * finrank ℂ (W.map (restr f)) :=
          Nat.mul_add _ _ _
      _ ≤ n := by omega

/-- Kneser for codes implies the iterated Fermat bound. -/
theorem fermat_iter_of_kneser
    (hK : ∀ (n : ℕ) (S T St : Submodule ℂ (Fin n → ℂ)), S ≠ ⊥ → T ≠ ⊥ →
      (∀ x, x ∈ St ↔ ∀ v ∈ S * T, x * v ∈ S * T) →
        Module.finrank ℂ S + Module.finrank ℂ T ≤ Module.finrank ℂ (S * T) + Module.finrank ℂ St) :
    ∀ (M k : ℕ) (W : Submodule ℂ (Fin M → ℂ)), 2 ≤ k →
      (∀ j : ℕ, 2 ≤ j → j ≤ k → ∀ x ∈ W, ∑ i, x i ^ j = 0) → k * Module.finrank ℂ W ≤ M := by
  intro M k W hk h
  obtain ⟨a, rfl⟩ : ∃ a, k = a + 2 := ⟨k - 2, by omega⟩
  exact fermat_iter_general (kneserFor_of_fin hK) a M (Fin M) (Fintype.card_fin M) W
    (vChain_perp_of_psum W a h)

end PEqualNP.Gct.Helpers.FermatIter
