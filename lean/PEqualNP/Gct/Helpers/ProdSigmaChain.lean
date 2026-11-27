import Mathlib
import PEqualNP.Gct.L065
import PEqualNP.Gct.Helpers.FermatFromKneser

/-! Helper for L-gct-079, proofs only. Trace-independent subspaces of `ℂ^n`: if `V_1, ..., V_q`
are subspaces of `ℂ^n` such that the sum of the coordinates of every product `t_(i_1) ... t_(i_r)`
(coordinatewise, `r ≥ 1`, distinct indices, `t_i ∈ V_i`) vanishes, then the span of all such
products, the empty one included, has dimension at least `1 + ∑ dim V_i`.

The proof is a chain of Kneser steps (L-gct-065). With `A` the span of the products over subsets
of a set `T` of indices and `k ∉ T`, the step is `dim (A (V_k + ℂ1)) ≥ dim A + dim V_k`. Let `H`
be the stabilizer of `P = A (V_k + ℂ1)`; it is a subalgebra holding `1`. Kneser applied to `A H`
and `(V_k + ℂ1) H`, whose product is `P`, gives
`dim (A + H) + dim (V_k + ℂ1 + H) ≤ dim P + dim H`. The trace form `(x, y) ↦ ∑ x_i y_i` is
nondegenerate on `H` (Lagrange interpolation gives the indicator of a level set), and `A ∩ H`,
`V_k ∩ H` are orthogonal for it, so `dim (A ∩ H) + dim (V_k ∩ H) ≤ dim H`, and the count
closes. -/

namespace PEqualNP.Gct.Helpers.ProdSigmaChain

open Module Finset PEqualNP.Gct.Helpers

variable {n : ℕ}

/-- Two subspaces orthogonal for the trace form meet a stabilizer in subspaces whose dimensions
add up to at most the dimension of the stabilizer: the trace form is nondegenerate on it. -/
theorem orth_in_stab (P X Y : Submodule ℂ (Fin n → ℂ))
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, ∑ i, x i * y i = 0) :
    finrank ℂ ↥(X ⊓ stab P) + finrank ℂ ↥(Y ⊓ stab P) ≤ finrank ℂ ↥(stab P) := by
  classical
  let Φ : ↥(Y ⊓ stab P) →ₗ[ℂ] Module.Dual ℂ ↥(stab P) :=
    (stab P).subtype.dualMap ∘ₗ dotDual ∘ₗ (Y ⊓ stab P).subtype
  have hΦ : ∀ (y : ↥(Y ⊓ stab P)) (z : ↥(stab P)),
      Φ y z = ∑ i, (y : Fin n → ℂ) i * (z : Fin n → ℂ) i := fun _ _ => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    by_contra hne
    have hne' : (y : Fin n → ℂ) ≠ 0 := fun h => hne (Subtype.ext h)
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne'
    obtain ⟨e, he, hev⟩ := exists_indicator (V := P) y.2.2 i
    have h := LinearMap.congr_fun hy ⟨e, he⟩
    rw [hΦ] at h
    simp only [LinearMap.zero_apply] at h
    have hsum : ∑ k, (y : Fin n → ℂ) k * e k
        = ((univ.filter fun k => (y : Fin n → ℂ) k = (y : Fin n → ℂ) i).card : ℂ)
          * (y : Fin n → ℂ) i := by
      simp only [hev, mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter, Finset.sum_congr rfl (fun k hk => (Finset.mem_filter.1 hk).2),
        Finset.sum_const, nsmul_eq_mul]
    rw [hsum] at h
    rcases mul_eq_zero.1 h with h0 | h0
    · have hc : (univ.filter fun k => (y : Fin n → ℂ) k = (y : Fin n → ℂ) i).card ≠ 0 :=
        Finset.card_ne_zero.2 ⟨i, by simp⟩
      exact hc (Nat.cast_eq_zero.1 h0)
    · exact hi h0
  let X' : Submodule ℂ ↥(stab P) := (X ⊓ stab P).comap (stab P).subtype
  have hX' : finrank ℂ ↥X' = finrank ℂ ↥(X ⊓ stab P) :=
    (Submodule.comapSubtypeEquivOfLe (inf_le_right : X ⊓ stab P ≤ stab P)).finrank_eq
  have hrange : LinearMap.range Φ ≤ X'.dualAnnihilator := by
    rintro _ ⟨y, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro z hz
    rw [hΦ]
    have h0 := hXY _ (show (z : Fin n → ℂ) ∈ X from hz.1) _ y.2.1
    rw [← h0]
    exact sum_congr rfl fun i _ => mul_comm _ _
  have e1 := LinearMap.finrank_range_of_inj hinj
  have e2 := Subspace.finrank_add_finrank_dualAnnihilator_eq X'
  have e3 := Submodule.finrank_mono hrange
  omega

/-- The Kneser step: if `1 ∈ A` and `V` is orthogonal to `A` for the trace form, then
`dim A + dim V ≤ dim (A (V + ℂ1))`. -/
theorem step (hn : 1 ≤ n) (A V : Submodule ℂ (Fin n → ℂ)) (h1 : (1 : Fin n → ℂ) ∈ A)
    (hperp : ∀ a ∈ A, ∀ v ∈ V, ∑ i, a i * v i = 0) :
    finrank ℂ ↥A + finrank ℂ ↥V
      ≤ finrank ℂ ↥(A * (V ⊔ Submodule.span ℂ {(1 : Fin n → ℂ)})) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨E, hE⟩ : ∃ E : Submodule ℂ (Fin n → ℂ), E = Submodule.span ℂ {(1 : Fin n → ℂ)} :=
    ⟨_, rfl⟩
  rw [← hE]
  obtain ⟨S, hS⟩ : ∃ S : Submodule ℂ (Fin n → ℂ), S = V ⊔ E := ⟨_, rfl⟩
  rw [← hS]
  obtain ⟨P, hP⟩ : ∃ P : Submodule ℂ (Fin n → ℂ), P = A * S := ⟨_, rfl⟩
  rw [← hP]
  obtain ⟨H, hH⟩ : ∃ H : Submodule ℂ (Fin n → ℂ), H = stab P := ⟨_, rfl⟩
  have h1E : (1 : Fin n → ℂ) ∈ E := hE ▸ Submodule.mem_span_singleton_self _
  have h1S : (1 : Fin n → ℂ) ∈ S := hS ▸ Submodule.mem_sup_right h1E
  have h1H : (1 : Fin n → ℂ) ∈ H := hH ▸ one_mem_stab P
  have hHH : H * H = H := by
    apply le_antisymm
    · rw [Submodule.mul_le]
      intro x hx y hy
      rw [hH] at hx hy ⊢
      exact mul_mem_stab hx hy
    · intro x hx
      have := Submodule.mul_mem_mul h1H hx
      rwa [one_mul] at this
  have hPH : P * H = P := by
    apply le_antisymm
    · rw [Submodule.mul_le]
      intro p hp x hx
      rw [hH] at hx
      rw [mul_comm]
      exact hx p hp
    · intro p hp
      have := Submodule.mul_mem_mul hp h1H
      rwa [mul_one] at this
  have hprod : (A * H) * (S * H) = P := by
    rw [mul_mul_mul_comm, hHH, ← hP, hPH]
  have hAH : A ⊔ H ≤ A * H := by
    refine sup_le (fun a ha => ?_) (fun x hx => ?_)
    · have := Submodule.mul_mem_mul ha h1H
      rwa [mul_one] at this
    · have := Submodule.mul_mem_mul h1 hx
      rwa [one_mul] at this
  have hSH : S ⊔ H ≤ S * H := by
    refine sup_le (fun a ha => ?_) (fun x hx => ?_)
    · have := Submodule.mul_mem_mul ha h1H
      rwa [mul_one] at this
    · have := Submodule.mul_mem_mul h1S hx
      rwa [one_mul] at this
  have hne1 : A * H ≠ ⊥ := by
    intro h
    have : (1 : Fin n → ℂ) ∈ A * H := hAH (Submodule.mem_sup_left h1)
    rw [h, Submodule.mem_bot] at this
    exact one_ne_zero this
  have hne2 : S * H ≠ ⊥ := by
    intro h
    have : (1 : Fin n → ℂ) ∈ S * H := hSH (Submodule.mem_sup_left h1S)
    rw [h, Submodule.mem_bot] at this
    exact one_ne_zero this
  have hk := PEqualNP.Gct.L065 n (A * H) (S * H) H hne1 hne2
    (fun x => by rw [hprod, hH]; exact Iff.rfl)
  rw [hprod] at hk
  have a1 := Submodule.finrank_mono hAH
  have a2 := Submodule.finrank_mono hSH
  have a3 := Submodule.finrank_sup_add_finrank_inf_eq A H
  have a4 := Submodule.finrank_sup_add_finrank_inf_eq S H
  have hVE : V ⊓ E = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxV, hxE⟩
    rw [hE] at hxE
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hxE
    have h0 := hperp 1 h1 _ hxV
    simp only [Pi.one_apply, Pi.smul_apply, smul_eq_mul, mul_one, one_mul, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd (Nat.cast_eq_zero.1 h) (by omega)
    · rw [h, zero_smul]
      exact Submodule.zero_mem _
  have hfE : finrank ℂ ↥E = 1 := by
    rw [hE]
    exact finrank_span_singleton one_ne_zero
  have a5 : finrank ℂ ↥S = finrank ℂ ↥V + 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq V E
    rw [hVE, finrank_bot, add_zero, hfE, ← hS] at h
    exact h
  have a6 : finrank ℂ ↥(S ⊓ H) ≤ finrank ℂ ↥(V ⊓ H) + 1 := by
    have hle : S ⊓ H ≤ (V ⊓ H) ⊔ E := by
      rintro x ⟨hxS, hxH⟩
      rw [SetLike.mem_coe, hS] at hxS
      obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.1 hxS
      have hwH : w ∈ H := by
        rw [hE] at hw
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
        exact H.smul_mem c h1H
      have hvH : v ∈ H := by
        have := H.sub_mem hxH hwH
        rwa [add_sub_cancel_right] at this
      exact Submodule.add_mem_sup ⟨hv, hvH⟩ hw
    have h2 := Submodule.finrank_add_le_finrank_add_finrank (V ⊓ H) E
    have h3 := Submodule.finrank_mono hle
    rw [hfE] at h2
    exact h3.trans h2
  have a7 := orth_in_stab P A V hperp
  rw [← hH] at a7
  omega

/-- The span of the products over the subsets of a set `T` of indices. -/
def prodSpan {q : ℕ} (V : Fin q → Submodule ℂ (Fin n → ℂ)) (T : Finset (Fin q)) :
    Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ {v : Fin n → ℂ | ∃ (S : Finset (Fin q)) (t : Fin q → (Fin n → ℂ)),
    S ⊆ T ∧ (∀ i ∈ S, t i ∈ V i) ∧ v = ∏ i ∈ S, t i}

theorem one_mem_prodSpan {q : ℕ} (V : Fin q → Submodule ℂ (Fin n → ℂ)) (T : Finset (Fin q)) :
    (1 : Fin n → ℂ) ∈ prodSpan V T :=
  Submodule.subset_span ⟨∅, 0, empty_subset T, by simp, by simp⟩

/-- Adding one factor to a product over a set not holding its index. -/
theorem prod_insert_update {q : ℕ} (S : Finset (Fin q)) (t : Fin q → (Fin n → ℂ)) (k : Fin q)
    (hk : k ∉ S) (v : Fin n → ℂ) :
    ∏ i ∈ insert k S, Function.update t k v i = (∏ i ∈ S, t i) * v := by
  rw [Finset.prod_insert hk, Function.update_self, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (show i ≠ k from fun h => hk (h ▸ hi))]

theorem update_mem {q : ℕ} (V : Fin q → Submodule ℂ (Fin n → ℂ)) (S : Finset (Fin q))
    (t : Fin q → (Fin n → ℂ)) (k : Fin q) (hk : k ∉ S) (v : Fin n → ℂ) (hv : v ∈ V k)
    (ht : ∀ i ∈ S, t i ∈ V i) : ∀ i ∈ insert k S, Function.update t k v i ∈ V i := by
  intro i hi
  rcases Finset.mem_insert.1 hi with rfl | hi
  · rw [Function.update_self]
    exact hv
  · rw [Function.update_of_ne (show i ≠ k from fun h => hk (h ▸ hi))]
    exact ht i hi

/-- The span over `T`, times `V_k + ℂ1`, lies in the span over `T ∪ {k}`. -/
theorem mul_le_insert {q : ℕ} (V : Fin q → Submodule ℂ (Fin n → ℂ)) (T : Finset (Fin q))
    (k : Fin q) (hk : k ∉ T) :
    prodSpan V T * (V k ⊔ Submodule.span ℂ {(1 : Fin n → ℂ)}) ≤ prodSpan V (insert k T) := by
  have hmono : prodSpan V T ≤ prodSpan V (insert k T) := by
    refine Submodule.span_mono ?_
    rintro x ⟨S, t, hS, ht, rfl⟩
    exact ⟨S, t, hS.trans (subset_insert _ _), ht, rfl⟩
  have key : ∀ v ∈ V k, ∀ m ∈ prodSpan V T, m * v ∈ prodSpan V (insert k T) := by
    intro v hv m hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨S, t, hS, ht, rfl⟩ := hx
      have hkS : k ∉ S := fun h => hk (hS h)
      exact Submodule.subset_span ⟨insert k S, Function.update t k v, insert_subset_insert k hS,
        update_mem V S t k hkS v hv ht, (prod_insert_update S t k hkS v).symm⟩
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx
  rw [Submodule.mul_le]
  intro m hm s hs
  obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.1 hs
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
  rw [mul_add, mul_smul_comm, mul_one]
  exact Submodule.add_mem _ (key v hv m hm) (Submodule.smul_mem _ c (hmono hm))

/-- The span over `T` is orthogonal to `V_k` for the trace form, when `k ∉ T`. -/
theorem prodSpan_perp {q : ℕ} (V : Fin q → Submodule ℂ (Fin n → ℂ))
    (hI : ∀ S : Finset (Fin q), S.Nonempty → ∀ t : Fin q → (Fin n → ℂ),
      (∀ i ∈ S, t i ∈ V i) → ∑ j : Fin n, ∏ i ∈ S, t i j = 0)
    (T : Finset (Fin q)) (k : Fin q) (hk : k ∉ T) :
    ∀ a ∈ prodSpan V T, ∀ v ∈ V k, ∑ j, a j * v j = 0 := by
  intro a ha v hv
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨S, t, hS, ht, rfl⟩ := hx
    have hkS : k ∉ S := fun h => hk (hS h)
    have h0 := hI (insert k S) (insert_nonempty k S) (Function.update t k v)
      (update_mem V S t k hkS v hv ht)
    rw [← h0]
    refine sum_congr rfl fun j _ => ?_
    have := congr_fun (prod_insert_update S t k hkS v) j
    rw [Finset.prod_apply, Pi.mul_apply] at this
    exact this.symm
  | zero => simp
  | add x y _ _ hx hy => simp only [Pi.add_apply, add_mul, sum_add_distrib, hx, hy, add_zero]
  | smul c x _ hx => simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum, hx, mul_zero]

/-- The chain of Kneser steps over a set of indices. -/
theorem chain_aux {q : ℕ} (hn : 1 ≤ n) (V : Fin q → Submodule ℂ (Fin n → ℂ))
    (hI : ∀ S : Finset (Fin q), S.Nonempty → ∀ t : Fin q → (Fin n → ℂ),
      (∀ i ∈ S, t i ∈ V i) → ∑ j : Fin n, ∏ i ∈ S, t i j = 0) (T : Finset (Fin q)) :
    ∑ i ∈ T, finrank ℂ ↥(V i) + 1 ≤ finrank ℂ ↥(prodSpan V T) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have hle : Submodule.span ℂ {(1 : Fin n → ℂ)} ≤ prodSpan V ∅ :=
      (Submodule.span_singleton_le_iff_mem _ _).2 (one_mem_prodSpan V ∅)
    have := Submodule.finrank_mono hle
    rw [finrank_span_singleton one_ne_zero] at this
    simpa using this
  | insert k T hk ih =>
    rw [sum_insert hk]
    have h1 := step hn (prodSpan V T) (V k) (one_mem_prodSpan V T) (prodSpan_perp V hI T k hk)
    have h2 := Submodule.finrank_mono (mul_le_insert V T k hk)
    omega

/-- Trace-independent subspaces of `ℂ^n`: the span of the products over all subsets of the
indices has dimension at least one plus the sum of the dimensions. -/
theorem chain (n q : ℕ) (hn : 1 ≤ n)
    (V : Fin q → Submodule ℂ (Fin n → ℂ))
    (hI : ∀ S : Finset (Fin q), S.Nonempty → ∀ t : Fin q → (Fin n → ℂ),
      (∀ i ∈ S, t i ∈ V i) → ∑ j : Fin n, ∏ i ∈ S, t i j = 0) :
    ∑ i : Fin q, Module.finrank ℂ (V i) + 1 ≤
      Module.finrank ℂ (Submodule.span ℂ
        {v : Fin n → ℂ | ∃ (S : Finset (Fin q)) (t : Fin q → (Fin n → ℂ)),
          (∀ i ∈ S, t i ∈ V i) ∧ v = ∏ i ∈ S, t i}) := by
  have h := chain_aux hn V hI univ
  refine h.trans (Submodule.finrank_mono (Submodule.span_mono ?_))
  rintro x ⟨S, t, -, ht, rfl⟩
  exact ⟨S, t, ht, rfl⟩

end PEqualNP.Gct.Helpers.ProdSigmaChain
