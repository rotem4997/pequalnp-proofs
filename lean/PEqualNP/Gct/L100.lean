import Mathlib

/-- Conjecture S at `p = 1`: under the stated conditions on two subspaces `L` and `X` of
`Fin q → ℂ`, their dimensions add to at most `q - 1`, and the only admissible scalar is zero. -/
theorem PEqualNP.Gct.L100 : ∀ (q : ℕ) (L X : Submodule ℂ (Fin q → ℂ)), 1 ≤ q → (∀ a ∈ L, ∑ j, a j = 0) → (∀ a ∈ L, ∀ x ∈ X, (∑ j, a j) + (∑ j, x j) = 0 ∧ (∑ j, ∑ l, if j = l then 0 else a j * x l) = 0) → Module.finrank ℂ L + Module.finrank ℂ X + 1 ≤ q ∧ ∀ y : ℂ, (∀ a ∈ L, ∀ c : ℂ, (∑ j, a j) + c * y = 0) → y = 0 := by
  intro q L X hq hL hLX
  -- the sums of vectors in X vanish
  have hX : ∀ x ∈ X, ∑ j, x j = 0 := by
    intro x hx
    have := (hLX 0 L.zero_mem x hx).1
    simpa using this
  -- the dot product of a in L and x in X vanishes
  have hdot : ∀ a ∈ L, ∀ x ∈ X, dotProduct a x = 0 := by
    intro a ha x hx
    have h2 := (hLX a ha x hx).2
    have key : (∑ j, ∑ l, if j = l then (0 : ℂ) else a j * x l)
        = (∑ j, a j) * (∑ l, x l) - ∑ j, a j * x j := by
      rw [Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have e : ∀ l, (if j = l then (0 : ℂ) else a j * x l)
          = a j * x l - if j = l then a j * x l else 0 := by
        intro l; split_ifs <;> simp
      simp_rw [e]
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq]
      simp
    rw [key, hL a ha, zero_mul, zero_sub, neg_eq_zero] at h2
    simpa [dotProduct] using h2
  refine ⟨?_, fun y hy => by simpa using hy 0 L.zero_mem 1⟩
  -- the all ones vector
  set one : Fin q → ℂ := fun _ => 1 with hone
  have hone_sum : ∑ j, one j = (q : ℂ) := by simp [hone]
  have hone_notin : one ∉ X := by
    intro h
    have := hX one h
    rw [hone_sum] at this
    have : q = 0 := by exact_mod_cast this
    omega
  -- the annihilator side
  set W : Submodule ℂ (Module.Dual ℂ (Fin q → ℂ)) := L.map (dotProductEquiv ℂ (Fin q)).toLinearMap
    with hW
  have hWrank : Module.finrank ℂ W = Module.finrank ℂ L :=
    LinearEquiv.finrank_map_eq (dotProductEquiv ℂ (Fin q)) L
  have hsum := Subspace.finrank_add_finrank_dualCoannihilator_eq W
  rw [hWrank, Module.finrank_fin_fun] at hsum
  set S : Submodule ℂ (Fin q → ℂ) := X ⊔ Submodule.span ℂ {one} with hS
  have hSle : S ≤ W.dualCoannihilator := by
    rw [hS, sup_le_iff, Submodule.span_le, Set.singleton_subset_iff]
    constructor
    · intro x hx
      rw [Submodule.mem_dualCoannihilator]
      intro φ hφ
      obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hφ
      simpa using hdot a ha x hx
    · show one ∈ W.dualCoannihilator
      rw [Submodule.mem_dualCoannihilator]
      intro φ hφ
      obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hφ
      simpa [dotProduct, hone] using hL a ha
  have hinf : X ⊓ Submodule.span ℂ {one} = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvX, hvS⟩ := Submodule.mem_inf.1 hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hvS
    by_cases hc : c = 0
    · simp [hc]
    · exact absurd ((X.smul_mem_iff hc).1 hvX) hone_notin
  have hone_ne : one ≠ 0 := by
    intro h; apply hone_notin; rw [h]; exact X.zero_mem
  have hSrank : Module.finrank ℂ S = Module.finrank ℂ X + 1 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq X (Submodule.span ℂ {one})
    rw [hinf, finrank_bot, add_zero, finrank_span_singleton hone_ne] at this
    rw [hS, this]
  have := Submodule.finrank_mono hSle
  omega
