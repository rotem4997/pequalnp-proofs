import Mathlib

/-!
Helper module, proofs only, for L-gct-065 (Kneser for codes over the complex numbers, after
Mirandola and Zemor 2015, Theorem 3.3).

The assembly: from finiteness of the set of subalgebras of `Fin n → ℂ` and the e-transform
lemma (both taken as hypotheses here), the Kneser inequality
`dim S + dim T ≤ dim (S * T) + dim St (S * T)` for nonzero subspaces `S`, `T`.

Two stages.

* `Asm.full_of`: if `S` is nonzero with full support and `T` contains a unit, some subalgebra
  `H` stabilizes `S * T` and has `dim S + dim T ≤ dim (S * T) + dim H`. The units `x` of `S`
  are sorted by the subalgebra the e-transform gives for `x`; together with the coordinate
  hyperplanes these finitely many classes cover `S`, and a vector space over an infinite field
  is not a finite union of proper subspaces, so one class spans `S`.
* `kneser_of`: the general case, with no change of the index type. With `W` the space of
  vectors vanishing on the common support of `S` and `T`, stage one is applied to `S ⊔ W` and
  `T ⊔ W`, and the dimensions are compared.
-/

namespace PEqualNP.Gct.Helpers.Kneser

open Module

namespace Asm

/-- A subspace of `Fin n → ℂ` with full support contains a unit: it is not the union of its
intersections with the coordinate hyperplanes. -/
theorem exists_isUnit_of_support {n : ℕ} (U : Submodule ℂ (Fin n → ℂ))
    (hU : ∀ i, ∃ u ∈ U, u i ≠ 0) : ∃ u ∈ U, IsUnit u := by
  by_contra hno
  push Not at hno
  let P : Fin n → Submodule ℂ U := fun i =>
    (LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ)).comap U.subtype
  have hcov : ⋃ i, (P i : Set U) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro u
    have h1 := hno u.1 u.2
    rw [Pi.isUnit_iff] at h1
    push Not at h1
    obtain ⟨i, hi⟩ := h1
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    have h0 : u.1 i = 0 := by
      by_contra hne
      exact hi (isUnit_iff_ne_zero.2 hne)
    show U.subtype u ∈ LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ)
    rw [LinearMap.mem_ker]
    exact h0
  obtain ⟨i, hi⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcov
  obtain ⟨u, hu, hui⟩ := hU i
  have hmem : (⟨u, hu⟩ : U) ∈ P i := by
    rw [hi]
    exact Submodule.mem_top
  have h0 : U.subtype ⟨u, hu⟩ ∈ LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ) := hmem
  rw [LinearMap.mem_ker] at h0
  exact hui h0

/-- Stage one: full support. Some subalgebra stabilizes `S * T` and is large enough. -/
theorem full_of {n : ℕ} (hfin : Finite (Subalgebra ℂ (Fin n → ℂ)))
    (hetr : ∀ (S T : Submodule ℂ (Fin n → ℂ)) (x : Fin n → ℂ), x ∈ S → IsUnit x →
      (∃ t ∈ T, IsUnit t) →
      ∃ (H : Subalgebra ℂ (Fin n → ℂ)) (V : Submodule ℂ (Fin n → ℂ)),
        (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ (∀ t ∈ T, x * t ∈ V) ∧ V ≤ S * T ∧
        finrank ℂ S + finrank ℂ T ≤ finrank ℂ V + finrank ℂ (Subalgebra.toSubmodule H))
    (S T : Submodule ℂ (Fin n → ℂ)) (hS0 : S ≠ ⊥) (hS : ∀ i, ∃ s ∈ S, s i ≠ 0)
    (hT : ∃ t ∈ T, IsUnit t) :
    ∃ H : Subalgebra ℂ (Fin n → ℂ), (∀ h ∈ H, ∀ v ∈ S * T, h * v ∈ S * T) ∧
      finrank ℂ S + finrank ℂ T ≤
        finrank ℂ (S * T : Submodule ℂ (Fin n → ℂ)) +
          finrank ℂ (Subalgebra.toSubmodule H) := by
  -- the elements of `S` for which the e-transform can give the subalgebra `H`
  let G : Subalgebra ℂ (Fin n → ℂ) → Set (Fin n → ℂ) := fun H =>
    {x | x ∈ S ∧ ∃ V : Submodule ℂ (Fin n → ℂ),
      (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ (∀ t ∈ T, x * t ∈ V) ∧ V ≤ S * T ∧
      finrank ℂ S + finrank ℂ T ≤ finrank ℂ V + finrank ℂ (Subalgebra.toSubmodule H)}
  let P : Fin n ⊕ Subalgebra ℂ (Fin n → ℂ) → Submodule ℂ S := fun j =>
    Sum.elim
      (fun i => (LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ)).comap S.subtype)
      (fun H => (Submodule.span ℂ (G H)).comap S.subtype) j
  have hcov : ⋃ j, (P j : Set S) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro u
    by_cases hu : IsUnit u.1
    · obtain ⟨H, V, h1, h2, h3, h4⟩ := hetr S T u.1 u.2 hu hT
      refine Set.mem_iUnion.2 ⟨Sum.inr H, ?_⟩
      show S.subtype u ∈ Submodule.span ℂ (G H)
      exact Submodule.subset_span ⟨u.2, V, h1, h2, h3, h4⟩
    · rw [Pi.isUnit_iff] at hu
      push Not at hu
      obtain ⟨i, hi⟩ := hu
      refine Set.mem_iUnion.2 ⟨Sum.inl i, ?_⟩
      have h0 : u.1 i = 0 := by
        by_contra hne
        exact hi (isUnit_iff_ne_zero.2 hne)
      show S.subtype u ∈ LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ)
      rw [LinearMap.mem_ker]
      exact h0
  obtain ⟨j, hj⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcov
  rcases j with i | H
  · exfalso
    obtain ⟨u, hu, hui⟩ := hS i
    have hmem : (⟨u, hu⟩ : S) ∈ P (Sum.inl i) := by
      rw [hj]
      exact Submodule.mem_top
    have h0 : S.subtype ⟨u, hu⟩ ∈ LinearMap.ker (LinearMap.proj i : (Fin n → ℂ) →ₗ[ℂ] ℂ) :=
      hmem
    rw [LinearMap.mem_ker] at h0
    exact hui h0
  · have hspan : S ≤ Submodule.span ℂ (G H) := by
      intro s hs
      have hmem : (⟨s, hs⟩ : S) ∈ P (Sum.inr H) := by
        rw [hj]
        exact Submodule.mem_top
      exact hmem
    -- the largest `H`-stable subspace of `S * T`
    let M : Submodule ℂ (Fin n → ℂ) :=
      sSup {V | (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ V ≤ S * T}
    have hM_le : M ≤ S * T := sSup_le fun V hV => hV.2
    have hM_stab : ∀ h ∈ H, ∀ v ∈ M, h * v ∈ M := by
      intro h hh
      have hle : M ≤ M.comap (LinearMap.mulLeft ℂ h) := by
        refine sSup_le fun V hV v hv => ?_
        show (LinearMap.mulLeft ℂ h) v ∈ M
        rw [LinearMap.mulLeft_apply]
        exact (le_sSup hV : V ≤ M) (hV.1 h hh v hv)
      intro v hv
      have h1 := hle hv
      rw [Submodule.mem_comap, LinearMap.mulLeft_apply] at h1
      exact h1
    have hST_le : S * T ≤ M := by
      rw [Submodule.mul_le]
      intro s hs t ht
      have hle : Submodule.span ℂ (G H) ≤ M.comap (LinearMap.mulRight ℂ t) := by
        rw [Submodule.span_le]
        rintro x ⟨_, V, h1, h2, h3, _⟩
        show (LinearMap.mulRight ℂ t) x ∈ M
        rw [LinearMap.mulRight_apply]
        exact (le_sSup (show V ∈ {V | (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ V ≤ S * T} from
          ⟨h1, h3⟩) : V ≤ M) (h2 t ht)
      have h1 := hle (hspan hs)
      rw [Submodule.mem_comap, LinearMap.mulRight_apply] at h1
      exact h1
    have hne : (G H).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      apply hS0
      rw [eq_bot_iff]
      intro s hs
      have h1 := hspan hs
      rw [hemp, Submodule.span_empty] at h1
      exact h1
    obtain ⟨x, _, V, _, _, h3, h4⟩ := hne
    have hVle : finrank ℂ V ≤ finrank ℂ (S * T : Submodule ℂ (Fin n → ℂ)) :=
      Submodule.finrank_mono h3
    refine ⟨H, fun h hh v hv => hM_le (hM_stab h hh v (hST_le hv)), ?_⟩
    omega

/-- The vectors that vanish on the common support of `S` and `T`. -/
def offSupp {n : ℕ} (S T : Submodule ℂ (Fin n → ℂ)) : Submodule ℂ (Fin n → ℂ) where
  carrier := {x | ∀ i, (∃ s ∈ S, s i ≠ 0) → (∃ t ∈ T, t i ≠ 0) → x i = 0}
  add_mem' := by
    intro a b ha hb i h1 h2
    simp [ha i h1 h2, hb i h1 h2]
  zero_mem' := by
    intro i _ _
    rfl
  smul_mem' := by
    intro c a ha i h1 h2
    simp [ha i h1 h2]

theorem mem_offSupp {n : ℕ} {S T : Submodule ℂ (Fin n → ℂ)} {x : Fin n → ℂ} :
    x ∈ offSupp S T ↔ ∀ i, (∃ s ∈ S, s i ≠ 0) → (∃ t ∈ T, t i ≠ 0) → x i = 0 :=
  Iff.rfl

theorem mul_mem_offSupp {n : ℕ} {S T : Submodule ℂ (Fin n → ℂ)} {x : Fin n → ℂ}
    (hx : x ∈ offSupp S T) (a : Fin n → ℂ) : a * x ∈ offSupp S T := by
  intro i h1 h2
  simp [hx i h1 h2]

/-- The product `S * T` vanishes off the common support. -/
theorem mul_apply_eq_zero {n : ℕ} {S T : Submodule ℂ (Fin n → ℂ)} {v : Fin n → ℂ}
    (hv : v ∈ S * T) (i : Fin n) (hi : ¬((∃ s ∈ S, s i ≠ 0) ∧ (∃ t ∈ T, t i ≠ 0))) :
    v i = 0 := by
  refine Submodule.mul_induction_on hv ?_ ?_
  · intro s hs t ht
    by_contra hne
    rw [Pi.mul_apply] at hne
    exact hi ⟨⟨s, hs, left_ne_zero_of_mul hne⟩, ⟨t, ht, right_ne_zero_of_mul hne⟩⟩
  · intro a b ha hb
    simp [ha, hb]

/-- `S ⊔ offSupp S T` has full support. -/
theorem support_sup_offSupp {n : ℕ} (S T : Submodule ℂ (Fin n → ℂ)) (i : Fin n) :
    ∃ u ∈ S ⊔ offSupp S T, u i ≠ 0 := by
  by_cases hK : ∃ s ∈ S, s i ≠ 0
  · obtain ⟨s, hs, hsi⟩ := hK
    exact ⟨s, (le_sup_left : S ≤ S ⊔ offSupp S T) hs, hsi⟩
  · refine ⟨Pi.single i 1, (le_sup_right : offSupp S T ≤ S ⊔ offSupp S T) ?_, by simp⟩
    intro j h1 _
    by_cases hji : j = i
    · subst hji
      exact absurd h1 hK
    · simp [hji]

theorem support_sup_offSupp' {n : ℕ} (S T : Submodule ℂ (Fin n → ℂ)) (i : Fin n) :
    ∃ u ∈ T ⊔ offSupp S T, u i ≠ 0 := by
  by_cases hK : ∃ t ∈ T, t i ≠ 0
  · obtain ⟨t, ht, hti⟩ := hK
    exact ⟨t, (le_sup_left : T ≤ T ⊔ offSupp S T) ht, hti⟩
  · refine ⟨Pi.single i 1, (le_sup_right : offSupp S T ≤ T ⊔ offSupp S T) ?_, by simp⟩
    intro j _ h2
    by_cases hji : j = i
    · subst hji
      exact absurd h2 hK
    · simp [hji]

/-- The product of the enlarged spaces is inside `S * T ⊔ offSupp S T`. -/
theorem sup_mul_sup_le {n : ℕ} (S T : Submodule ℂ (Fin n → ℂ)) :
    (S ⊔ offSupp S T) * (T ⊔ offSupp S T) ≤ S * T ⊔ offSupp S T := by
  rw [Submodule.mul_le]
  intro a ha b hb
  obtain ⟨s, hs, w, hw, rfl⟩ := Submodule.mem_sup.1 ha
  obtain ⟨t, ht, w', hw', rfl⟩ := Submodule.mem_sup.1 hb
  have h1 : s * t ∈ S * T := Submodule.mul_mem_mul hs ht
  have h2 : s * w' + w * t + w * w' ∈ offSupp S T := by
    refine Submodule.add_mem _ (Submodule.add_mem _ (mul_mem_offSupp hw' s) ?_)
      (mul_mem_offSupp hw' w)
    rw [mul_comm]
    exact mul_mem_offSupp hw t
  have h3 : (s + w) * (t + w') = s * t + (s * w' + w * t + w * w') := by ring
  rw [h3]
  exact Submodule.add_mem _ (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)

/-- The parts of `S` and of `T` off the common support are independent. -/
theorem finrank_inf_offSupp_add_le {n : ℕ} (S T : Submodule ℂ (Fin n → ℂ)) :
    finrank ℂ (S ⊓ offSupp S T : Submodule ℂ (Fin n → ℂ)) +
      finrank ℂ (T ⊓ offSupp S T : Submodule ℂ (Fin n → ℂ)) ≤ finrank ℂ (offSupp S T) := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (S ⊓ offSupp S T) (T ⊓ offSupp S T)
  have h2 : (S ⊓ offSupp S T) ⊓ (T ⊓ offSupp S T) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨hxS, hxW⟩, ⟨hxT, _⟩⟩
    rw [Submodule.mem_bot]
    funext i
    by_contra hne
    exact hne (hxW i ⟨x, hxS, hne⟩ ⟨x, hxT, hne⟩)
  have h3 : finrank ℂ ((S ⊓ offSupp S T) ⊔ (T ⊓ offSupp S T) : Submodule ℂ (Fin n → ℂ)) ≤
      finrank ℂ (offSupp S T) :=
    Submodule.finrank_mono (sup_le inf_le_right inf_le_right)
  rw [h2, finrank_bot] at h1
  omega

end Asm

open Asm in
/-- Kneser for codes over the complex numbers, from finiteness of the set of subalgebras and
the e-transform lemma. -/
theorem kneser_of
    (hfin : ∀ n : ℕ, Finite (Subalgebra ℂ (Fin n → ℂ)))
    (hetr : ∀ (n : ℕ) (S T : Submodule ℂ (Fin n → ℂ)) (x : Fin n → ℂ), x ∈ S → IsUnit x →
      (∃ t ∈ T, IsUnit t) →
      ∃ (H : Subalgebra ℂ (Fin n → ℂ)) (V : Submodule ℂ (Fin n → ℂ)),
        (∀ h ∈ H, ∀ v ∈ V, h * v ∈ V) ∧ (∀ t ∈ T, x * t ∈ V) ∧ V ≤ S * T ∧
        Module.finrank ℂ S + Module.finrank ℂ T ≤
          Module.finrank ℂ V + Module.finrank ℂ (Subalgebra.toSubmodule H)) :
    ∀ (n : ℕ) (S T St : Submodule ℂ (Fin n → ℂ)), S ≠ ⊥ → T ≠ ⊥ →
      (∀ x, x ∈ St ↔ ∀ v ∈ S * T, x * v ∈ S * T) →
      Module.finrank ℂ S + Module.finrank ℂ T ≤ Module.finrank ℂ (S * T) + Module.finrank ℂ St := by
  intro n S T St hS _ hSt
  have hS' : S ⊔ offSupp S T ≠ ⊥ := by
    intro h
    apply hS
    rw [eq_bot_iff, ← h]
    exact le_sup_left
  obtain ⟨H, hH, hdim⟩ := full_of (hfin n) (hetr n) (S ⊔ offSupp S T) (T ⊔ offSupp S T) hS'
    (support_sup_offSupp S T) (exists_isUnit_of_support _ (support_sup_offSupp' S T))
  -- `H` stabilizes `S * T` itself
  have hHSt : Subalgebra.toSubmodule H ≤ St := by
    intro h hh
    rw [hSt]
    intro v hv
    have hv' : v ∈ (S ⊔ offSupp S T) * (T ⊔ offSupp S T) :=
      (Submodule.mul_le.2 fun s hs t ht =>
        Submodule.mul_mem_mul (Submodule.mem_sup_left hs) (Submodule.mem_sup_left ht)) hv
    obtain ⟨a, ha, w, hw, hsum⟩ :=
      Submodule.mem_sup.1 (sup_mul_sup_le S T (hH h ((Subalgebra.mem_toSubmodule _).1 hh) v hv'))
    have hw0 : w = 0 := by
      funext i
      by_cases hK : (∃ s ∈ S, s i ≠ 0) ∧ (∃ t ∈ T, t i ≠ 0)
      · exact hw i hK.1 hK.2
      · have e1 : a i + w i = h i * v i := by
          rw [← Pi.add_apply, hsum, Pi.mul_apply]
        rw [mul_apply_eq_zero ha i hK, mul_apply_eq_zero hv i hK] at e1
        simpa using e1
    rw [hw0, add_zero] at hsum
    rw [← hsum]
    exact ha
  have d1 := Submodule.finrank_sup_add_finrank_inf_eq S (offSupp S T)
  have d2 := Submodule.finrank_sup_add_finrank_inf_eq T (offSupp S T)
  have d3 := finrank_inf_offSupp_add_le S T
  have d4 : finrank ℂ ((S ⊔ offSupp S T) * (T ⊔ offSupp S T) : Submodule ℂ (Fin n → ℂ)) ≤
      finrank ℂ (S * T : Submodule ℂ (Fin n → ℂ)) + finrank ℂ (offSupp S T) :=
    (Submodule.finrank_mono (sup_mul_sup_le S T)).trans
      (Submodule.finrank_add_le_finrank_add_finrank _ _)
  have d5 : finrank ℂ (Subalgebra.toSubmodule H) ≤ finrank ℂ St := Submodule.finrank_mono hHSt
  omega

end PEqualNP.Gct.Helpers.Kneser
