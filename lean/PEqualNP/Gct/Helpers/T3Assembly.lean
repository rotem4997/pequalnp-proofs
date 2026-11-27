import PEqualNP.Defs
import PEqualNP.Gct.L065
import PEqualNP.Gct.Helpers.FermatFromKneser
import PEqualNP.Gct.Helpers.FermatIterated
import PEqualNP.Gct.Helpers.T3LemmaP

/-! Helper for L-gct-163, proofs only. Assembly of T3 (notes/gct-086-core/t3/notes.md, F2) from
Kneser (L-gct-065) and two facts about subalgebras from `T3LemmaP`: `iso_half` (an
isotropic subspace of a unital subalgebra `H` has at most half its dimension) and `lemmaP` (if it
is moreover isotropic for the four-fold form, strictly less than half). With `X = (C1 + A)(C1 + B)`
and `H = stab X`, Kneser applied to `H(C1 + A)` and `H(C1 + B)` gives
`a + b + h ≤ dim X + dim (H ⊓ A) + dim (H ⊓ B)`, and the two facts give
`dim (H ⊓ A) + dim (H ⊓ B) + 1 ≤ h`; so `a + b ≤ dim (A + B + AB)`, and `C` is orthogonal to that. -/

namespace PEqualNP.Gct.Helpers.T3

open Module Finset PEqualNP.Gct.Helpers

/-- The four-fold form vanishes on `A` once `∑ a_i^4` does (three polarization steps). -/
theorem four_of_p4 {m : ℕ} (A : Submodule ℂ (Fin m → ℂ)) (hp4 : ∀ a ∈ A, ∑ i, a i ^ 4 = 0) :
    ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, ∀ w ∈ A, ∑ i, x i * y i * z i * w i = 0 := by
  intro x hx y hy z hz w hw
  have s1 := FermatIter.polar_step A 1 3 (fun u hu => by
    simpa only [Pi.one_apply, mul_one, Nat.reduceAdd] using hp4 u hu)
  have s2 := FermatIter.polar_step A y 2 (fun u hu => by
    simpa only [Pi.one_apply, mul_one, Nat.reduceAdd] using s1 u hu y hy)
  have s3 := FermatIter.polar_step A (z * y) 1 (fun u hu => by
    simpa only [Pi.mul_apply, Nat.reduceAdd] using s2 u hu z hz)
  rw [← s3 x hx w hw]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [pow_one, Pi.mul_apply]
  ring

theorem t3 :
    ∀ (m : ℕ) (A B C : Submodule ℂ (Fin m → ℂ)),
      (∀ x ∈ A ⊔ B, ∀ y ∈ A ⊔ B, ∑ i, x i * y i = 0) →
      (∀ c ∈ C, (∀ a ∈ A, ∑ i, c i * a i = 0) ∧ (∀ b ∈ B, ∑ i, c i * b i = 0) ∧
        ∀ a ∈ A, ∀ b ∈ B, ∑ i, c i * (a i * b i) = 0) →
      (∀ a ∈ A, ∑ i, a i ^ 4 = 0) →
        Module.finrank ℂ A + Module.finrank ℂ B + Module.finrank ℂ C ≤ m := by
  intro m A B C hiso hC hp4
  -- `C` is orthogonal to `Z = A + B + AB`.
  have hZ : A ⊔ B ⊔ A * B ≤ FermatIter.perp C := by
    refine sup_le (sup_le ?_ ?_) (Submodule.mul_le.2 ?_)
    · intro a ha c hc
      exact (Finset.sum_congr rfl fun i _ => mul_comm _ _).trans ((hC c hc).1 a ha)
    · intro b hb c hc
      exact (Finset.sum_congr rfl fun i _ => mul_comm _ _).trans ((hC c hc).2.1 b hb)
    · intro a ha b hb c hc
      exact (Finset.sum_congr rfl fun i _ => by rw [Pi.mul_apply, mul_comm]).trans
        ((hC c hc).2.2 a ha b hb)
  have hperp := perp_bound (A ⊔ B ⊔ A * B) C fun v hv z hz => hZ hv z hz
  rw [Fintype.card_fin] at hperp
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 := Submodule.finrank_le A
    have h0' := Submodule.finrank_le B
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h0 h0'
    omega
  have h10 : (1 : Fin m → ℂ) ≠ 0 := fun h => one_ne_zero (congr_fun h ⟨0, hm⟩)
  set X := (1 ⊔ A) * (1 ⊔ B) with hXdef
  set H := stab X with hHdef
  have h1H : (1 : Fin m → ℂ) ∈ H := one_mem_stab X
  have hmulH : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H := fun x hx y hy => mul_mem_stab hx hy
  have h11 : (1 : Fin m → ℂ) ∈ (1 : Submodule ℂ (Fin m → ℂ)) := Submodule.one_le.1 le_rfl
  have h1A : (1 : Fin m → ℂ) ∈ 1 ⊔ A := Submodule.mem_sup_left h11
  have h1B : (1 : Fin m → ℂ) ∈ 1 ⊔ B := Submodule.mem_sup_left h11
  -- `S' T' = X`.
  have hST : H * (1 ⊔ A) * (H * (1 ⊔ B)) = X := by
    rw [mul_mul_mul_comm]
    refine le_antisymm (Submodule.mul_le.2 fun u hu x hx => ?_) ?_
    · have hHH : H * H ≤ H := Submodule.mul_le.2 hmulH
      exact hHH hu x hx
    · intro x hx
      have := Submodule.mul_mem_mul (Submodule.mul_mem_mul h1H h1H) hx
      rwa [one_mul, one_mul] at this
  have hS1 : (1 : Fin m → ℂ) ∈ H * (1 ⊔ A) := by
    have := Submodule.mul_mem_mul h1H h1A; rwa [one_mul] at this
  have hT1 : (1 : Fin m → ℂ) ∈ H * (1 ⊔ B) := by
    have := Submodule.mul_mem_mul h1H h1B; rwa [one_mul] at this
  have hK := PEqualNP.Gct.L065 m (H * (1 ⊔ A)) (H * (1 ⊔ B)) H
    ((Submodule.ne_bot_iff _).2 ⟨1, hS1, h10⟩) ((Submodule.ne_bot_iff _).2 ⟨1, hT1, h10⟩)
    (by rw [hST]; exact fun x => Iff.rfl)
  rw [hST] at hK
  -- `H + A ≤ S'`, `H + B ≤ T'`.
  have hHA : H ⊔ A ≤ H * (1 ⊔ A) := by
    refine sup_le (fun x hx => ?_) (fun a ha => ?_)
    · have := Submodule.mul_mem_mul hx h1A; rwa [mul_one] at this
    · have := Submodule.mul_mem_mul h1H (Submodule.mem_sup_right ha : a ∈ 1 ⊔ A)
      rwa [one_mul] at this
  have hHB : H ⊔ B ≤ H * (1 ⊔ B) := by
    refine sup_le (fun x hx => ?_) (fun b hb => ?_)
    · have := Submodule.mul_mem_mul hx h1B; rwa [mul_one] at this
    · have := Submodule.mul_mem_mul h1H (Submodule.mem_sup_right hb : b ∈ 1 ⊔ B)
      rwa [one_mul] at this
  have dA := Submodule.finrank_sup_add_finrank_inf_eq H A
  have dB := Submodule.finrank_sup_add_finrank_inf_eq H B
  have dN := Submodule.finrank_sup_add_finrank_inf_eq (H ⊓ A) (H ⊓ B)
  have eA := Submodule.finrank_mono hHA
  have eB := Submodule.finrank_mono hHB
  -- Parity.
  have hsumH : H ⊓ A ⊔ H ⊓ B ≤ H := sup_le inf_le_left inf_le_left
  have hsumAB : H ⊓ A ⊔ H ⊓ B ≤ A ⊔ B := sup_le_sup inf_le_right inf_le_right
  have hs := iso_half H (H ⊓ A ⊔ H ⊓ B) h1H hmulH hsumH
    (fun x hx y hy => hiso x (hsumAB hx) y (hsumAB hy))
  have hNH : H ⊓ A ⊓ (H ⊓ B) ≤ H := inf_le_left.trans inf_le_left
  have hNA' : H ⊓ A ⊓ (H ⊓ B) ≤ A := inf_le_left.trans inf_le_right
  have h4 := four_of_p4 A hp4
  have hn := lemmaP hm H (H ⊓ A ⊓ (H ⊓ B)) h1H hmulH hNH
    (fun x hx y hy => hiso x (Submodule.mem_sup_left (hNA' hx)) y
      (Submodule.mem_sup_left (hNA' hy)))
    (fun x hx y hy z hz w hw => h4 x (hNA' hx) y (hNA' hy) z (hNA' hz) w (hNA' hw))
  -- `X ≤ C1 + Z`.
  have hXZ : X ≤ 1 ⊔ (A ⊔ B ⊔ A * B) := by
    rw [hXdef, Submodule.sup_mul, Submodule.mul_sup, Submodule.mul_sup]
    simp only [one_mul, mul_one]
    exact sup_le (sup_le le_sup_left (le_sup_of_le_right (le_sup_of_le_left le_sup_right)))
      (sup_le (le_sup_of_le_right (le_sup_of_le_left le_sup_left))
        (le_sup_of_le_right le_sup_right))
  have dX := (Submodule.finrank_mono hXZ).trans
    (Submodule.finrank_add_le_finrank_add_finrank 1 (A ⊔ B ⊔ A * B))
  rw [Submodule.one_eq_span, finrank_span_singleton h10] at dX
  omega

end PEqualNP.Gct.Helpers.T3
