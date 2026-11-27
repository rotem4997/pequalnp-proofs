import PEqualNP.Gct.Helpers.FermatFromKneser

/-! Helper for the t3 notes (F2, Lemma P), proofs only. Inside a unital subalgebra `H` of
`ℂ^m` the dot product is nondegenerate, because an element orthogonal to `H` has all power
sums zero. So an isotropic `N ≤ H` has `2 dim N ≤ dim H` (`iso_half`). If equality held and the
quartic form vanished on `N`, then every odd power of an `x ∈ N` would lie in `N`, so all power
sums of `x^2` vanish and `x = 0`; then `H = 0`, which `1 ∈ H` rules out (`lemmaP`). -/

namespace PEqualNP.Gct.Helpers.T3

open Module Finset

/-- A vector whose power sums `∑ g_i^(j+1)` all vanish is zero. -/
theorem psum_zero {ι : Type} [Fintype ι] (g : ι → ℂ) (h : ∀ j : ℕ, ∑ i, g i ^ (j + 1) = 0) :
    g = 0 := by
  classical
  let V : Submodule ℂ (ι → ℂ) :=
    { carrier := {w | ∀ j : ℕ, ∑ i, g i ^ (j + 1) * w i = 0}
      add_mem' := fun {a b} ha hb j => by
        simp only [Set.mem_setOf_eq, Pi.add_apply, mul_add, sum_add_distrib, ha j, hb j,
          add_zero]
      zero_mem' := fun j => by simp
      smul_mem' := fun c w hw j => by
        simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, ← mul_sum,
          hw j, mul_zero] }
  have hV1 : (1 : ι → ℂ) ∈ V := fun j => by simpa using h j
  have hg : g ∈ stab V := fun w hw j => by
    rw [← hw (j + 1)]
    exact sum_congr rfl fun i _ => by simp only [Pi.mul_apply]; ring
  funext i
  obtain ⟨e, he, hek⟩ := exists_indicator hg i
  have h0 := he 1 hV1 0
  have h2 : ∑ k, g k ^ (0 + 1) * (e * 1) k =
      ∑ k, (if g k = g i then (1 : ℂ) else 0) * g i := by
    refine sum_congr rfl fun k _ => ?_
    rw [mul_one, hek k]
    split_ifs with hk
    · rw [hk]; ring
    · ring
  rw [h2, ← sum_mul, sum_boole] at h0
  have hc : ((univ.filter fun k => g k = g i).card : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Finset.card_ne_zero.2 ⟨i, by simp⟩
  simpa [hc] using h0

/-- Powers of an element of a unital subalgebra stay in it. -/
theorem pow_mem' {m : ℕ} (H : Submodule ℂ (Fin m → ℂ)) (h1 : (1 : Fin m → ℂ) ∈ H)
    (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H) {x : Fin m → ℂ} (hx : x ∈ H) (j : ℕ) : x ^ j ∈ H := by
  induction j with
  | zero => simpa using h1
  | succ j ih => rw [pow_succ]; exact hmul _ ih _ hx

/-- Two mutually orthogonal subspaces of a unital subalgebra `H` have dimensions summing to at
most `dim H`. -/
theorem perp_in {m : ℕ} (H V W : Submodule ℂ (Fin m → ℂ)) (h1 : (1 : Fin m → ℂ) ∈ H)
    (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H) (hV : V ≤ H) (hW : W ≤ H)
    (h : ∀ v ∈ V, ∀ z ∈ W, ∑ i, v i * z i = 0) :
    finrank ℂ V + finrank ℂ W ≤ finrank ℂ H := by
  let D : H →ₗ[ℂ] Module.Dual ℂ H := dotDual.compl₁₂ H.subtype H.subtype
  have hD : Function.Injective D := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    refine Subtype.ext (psum_zero _ fun j => ?_)
    have := LinearMap.congr_fun hx ⟨(x : Fin m → ℂ) ^ j, pow_mem' H h1 hmul x.2 j⟩
    change ∑ i, (x : Fin m → ℂ) i * ((x : Fin m → ℂ) ^ j) i = 0 at this
    rw [← this]
    exact sum_congr rfl fun i _ => by simp only [Pi.pow_apply]; ring
  let V' := V.comap H.subtype
  let W' := W.comap H.subtype
  have hle : V'.map D ≤ W'.dualAnnihilator := by
    rintro _ ⟨v, hv, rfl⟩
    rw [Submodule.mem_dualAnnihilator]
    intro z hz
    exact h v hv z hz
  have e1 : finrank ℂ (V'.map D) = finrank ℂ V' :=
    (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hD V')).symm
  have e2 := Subspace.finrank_add_finrank_dualAnnihilator_eq W'
  have e3 := Submodule.finrank_mono hle
  have eV : finrank ℂ V' = finrank ℂ V := LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hV)
  have eW : finrank ℂ W' = finrank ℂ W := LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hW)
  omega

theorem iso_half {m : ℕ} (H N : Submodule ℂ (Fin m → ℂ))
    (h1 : (1 : Fin m → ℂ) ∈ H) (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    (hN : N ≤ H) (hiso : ∀ x ∈ N, ∀ y ∈ N, ∑ i, x i * y i = 0) :
    2 * Module.finrank ℂ N ≤ Module.finrank ℂ H := by
  have := perp_in H N N h1 hmul hN hN hiso
  omega

/-- If `2 dim N = dim H`, an element of `H` orthogonal to `N` lies in `N`. -/
theorem mem_of_perp {m : ℕ} (H N : Submodule ℂ (Fin m → ℂ))
    (h1 : (1 : Fin m → ℂ) ∈ H) (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    (hN : N ≤ H) (hiso : ∀ x ∈ N, ∀ y ∈ N, ∑ i, x i * y i = 0)
    (heq : Module.finrank ℂ H = 2 * Module.finrank ℂ N) {y : Fin m → ℂ} (hy : y ∈ H)
    (hyN : ∀ n ∈ N, ∑ i, y i * n i = 0) : y ∈ N := by
  have hPH : N ⊔ ℂ ∙ y ≤ H := sup_le hN ((Submodule.span_singleton_le_iff_mem _ _).2 hy)
  have hPN : ∀ v ∈ N ⊔ ℂ ∙ y, ∀ z ∈ N, ∑ i, v i * z i = 0 := by
    intro v hv z hz
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hb
    have e : ∑ i, (a + c • y) i * z i = ∑ i, a i * z i + c * ∑ i, y i * z i := by
      rw [mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun i _ => by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, hiso a ha z hz, hyN z hz, mul_zero, add_zero]
  have hb := perp_in H _ N h1 hmul hPH hN hPN
  have hP : N = N ⊔ ℂ ∙ y := Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
  rw [hP]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)

theorem lemmaP {m : ℕ} (hm : 0 < m) (H N : Submodule ℂ (Fin m → ℂ))
    (h1 : (1 : Fin m → ℂ) ∈ H) (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    (hN : N ≤ H) (hiso : ∀ x ∈ N, ∀ y ∈ N, ∑ i, x i * y i = 0)
    (h4 : ∀ x ∈ N, ∀ y ∈ N, ∀ z ∈ N, ∀ w ∈ N, ∑ i, x i * y i * z i * w i = 0) :
    2 * Module.finrank ℂ N + 1 ≤ Module.finrank ℂ H := by
  have hb := iso_half H N h1 hmul hN hiso
  by_contra hlt
  have heq : Module.finrank ℂ H = 2 * Module.finrank ℂ N := by omega
  have hodd : ∀ x ∈ N, ∀ k : ℕ, x ^ (2 * k + 1) ∈ N := by
    intro x hx k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      refine mem_of_perp H N h1 hmul hN hiso heq (pow_mem' H h1 hmul (hN hx) _) fun n hn => ?_
      rw [← h4 _ ih x hx x hx n hn]
      exact sum_congr rfl fun i _ => by simp only [Pi.pow_apply]; ring
  have hN0 : ∀ x ∈ N, x = 0 := by
    intro x hx
    have hg := psum_zero (x ^ 2) fun j => by
      rw [← hiso x hx _ (hodd x hx j)]
      exact sum_congr rfl fun i _ => by simp only [Pi.pow_apply]; ring
    funext i
    have := congr_fun hg i
    simpa using this
  have hbot : N = ⊥ := eq_bot_iff.2 fun x hx => (Submodule.mem_bot ℂ).2 (hN0 x hx)
  rw [hbot, finrank_bot, mul_zero] at heq
  have hH : H = ⊥ := Submodule.finrank_eq_zero.1 heq
  rw [hH, Submodule.mem_bot] at h1
  have := congr_fun h1 ⟨0, hm⟩
  simp at this

end PEqualNP.Gct.Helpers.T3
