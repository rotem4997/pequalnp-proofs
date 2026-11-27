import Mathlib

namespace PEqualNP.Outside.L_gct_207

def form (x : (Fin 6 → ℂ) × (Fin 3 → ℂ)) (ij : Fin 5 × Fin 7) : ℂ :=
  Fin.cases
    (Fin.cases (-(∑ j, x.1 j)) x.1 ij.2)
    (fun i => if ij.2 = 0 then Fin.cases (-(∑ j, x.2 j)) x.2 i else 0)
    ij.1

def formMap : ((Fin 6 → ℂ) × (Fin 3 → ℂ)) →ₗ[ℂ] (Fin 5 × Fin 7 → ℂ) where
  toFun := form
  map_add' x y := by
    funext ij
    rcases ij with ⟨i, j⟩
    refine Fin.cases ?_ (fun k => ?_) i
    · refine Fin.cases ?_ (fun l => ?_) j <;>
        simp [form, Finset.sum_add_distrib, add_comm]
    · refine Fin.cases ?_ (fun l => ?_) j
      · refine Fin.cases ?_ (fun l => ?_) k
        · change -(∑ l, (x + y).2 l) = -(∑ l, x.2 l) + -(∑ l, y.2 l)
          simp [Finset.sum_add_distrib, add_comm]
        · simp [form]
      · simp [form]
  map_smul' c x := by
    funext ij
    rcases ij with ⟨i, j⟩
    refine Fin.cases ?_ (fun k => ?_) i
    · refine Fin.cases ?_ (fun l => ?_) j <;> simp [form, Finset.mul_sum]
    · refine Fin.cases ?_ (fun l => ?_) j
      · refine Fin.cases ?_ (fun l => ?_) k
        · change -(∑ l, (c • x).2 l) = c * -(∑ l, x.2 l)
          simp [Finset.mul_sum]
        · simp [form]
      · simp [form]

theorem formMap_injective : Function.Injective formMap := by
  intro x y h
  apply Prod.ext
  · funext j
    exact congrFun h ((0 : Fin 5), j.succ)
  · funext i
    have hh := congrFun h (i.succ.succ, (0 : Fin 7))
    exact hh

theorem form_zero (x : (Fin 6 → ℂ) × (Fin 3 → ℂ)) (i : Fin 5) (j : Fin 7)
    (hi : i ≠ 0) (hj : j ≠ 0) : form x (i, j) = 0 := by
  obtain ⟨i, rfl⟩ := Fin.exists_succ_eq.2 hi
  obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.2 hj
  simp [form, Fin.succ_ne_zero]

theorem form_row (x : (Fin 6 → ℂ) × (Fin 3 → ℂ)) : (∑ j : Fin 7, form x (0, j)) = 0 := by
  rw [Fin.sum_univ_succ]
  simp [form]

theorem form_col (x : (Fin 6 → ℂ) × (Fin 3 → ℂ)) :
    (∑ i : Fin 4, form x (i.succ, 0)) = 0 := by
  have h : ∀ i : Fin 4, form x (i.succ, 0) = Fin.cases (-(∑ j, x.2 j)) x.2 i :=
    fun i => by simp [form]
  simp_rw [h]
  rw [Fin.sum_univ_succ]
  simp

theorem exists_off {k : ℕ} {A B : Type} (f : Fin k → A) (g : Fin k → B) (a : A) (b : B)
    (hf : Function.Injective f) (hg : Function.Injective g) (hk : 3 ≤ k) :
    ∃ i, f i ≠ a ∧ g i ≠ b := by
  by_contra hcon
  push_neg at hcon
  have h4 : ∀ i j : Fin k, i ≠ j → ¬ (g i = b ∧ g j = b) :=
    fun i j hij hh => hij (hg (hh.1.trans hh.2.symm))
  have n01 : (⟨0, by omega⟩ : Fin k) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have n02 : (⟨0, by omega⟩ : Fin k) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have n12 : (⟨1, by omega⟩ : Fin k) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  by_cases c0 : f ⟨0, by omega⟩ = a
  · have e1 : f ⟨1, by omega⟩ ≠ a := fun e => n01 (hf (c0.trans e.symm))
    have e2 : f ⟨2, by omega⟩ ≠ a := fun e => n02 (hf (c0.trans e.symm))
    exact h4 _ _ n12 ⟨hcon _ e1, hcon _ e2⟩
  · by_cases c1 : f ⟨1, by omega⟩ = a
    · have e2 : f ⟨2, by omega⟩ ≠ a := fun e => n12 (hf (c1.trans e.symm))
      exact h4 _ _ n02 ⟨hcon _ c0, hcon _ e2⟩
    · exact h4 _ _ n01 ⟨hcon _ c0, hcon _ c1⟩

theorem singleSum {m : ℕ} (G : Fin m → ℂ) :
    (∑ R : Finset (Fin m), if h : R.card = 1 then G (R.orderEmbOfFin h 0) else 0)
      = ∑ i, G i := by
  classical
  have hsub : ∀ R ∈ (Finset.univ : Finset (Finset (Fin m))),
      R ∉ (Finset.univ : Finset (Fin m)).map
        ⟨fun i => ({i} : Finset (Fin m)), Finset.singleton_injective⟩ →
      (if h : R.card = 1 then G (R.orderEmbOfFin h 0) else 0) = 0 := by
    intro R _ hR
    by_cases h : R.card = 1
    · exfalso
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h
      exact hR (Finset.mem_map.2 ⟨a, Finset.mem_univ _, rfl⟩)
    · rw [dif_neg h]
  rw [← Finset.sum_subset (Finset.subset_univ _) hsub, Finset.sum_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [dif_pos (Finset.card_singleton i), Finset.orderEmbOfFin_singleton]

theorem pair_mem {m : ℕ} (R : Finset (Fin m)) (h : R.card = 2) (x : Fin m) :
    x ∈ R ↔ x = R.orderEmbOfFin h 0 ∨ x = R.orderEmbOfFin h 1 := by
  have hr := Finset.range_orderEmbOfFin R h
  constructor
  · intro hx
    have hx' : x ∈ Set.range (R.orderEmbOfFin h) := by rw [hr]; exact hx
    obtain ⟨a, rfl⟩ := hx'
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl) <;> exact Finset.orderEmbOfFin_mem R h _

theorem pair_lt {m : ℕ} (R : Finset (Fin m)) (h : R.card = 2) :
    R.orderEmbOfFin h 0 < R.orderEmbOfFin h 1 :=
  (R.orderEmbOfFin h).lt_iff_lt.2 (by decide)

theorem pair_one_ne {n : ℕ} (R : Finset (Fin (n + 1))) (h : R.card = 2) :
    R.orderEmbOfFin h 1 ≠ 0 :=
  ne_of_gt (lt_of_le_of_lt (Fin.zero_le _) (pair_lt R h))

theorem pairSum {n : ℕ} (g : Fin (n + 1) → ℂ) :
    (∑ R : Finset (Fin (n + 1)), if h : R.card = 2 then
        (if R.orderEmbOfFin h 0 = 0 then g (R.orderEmbOfFin h 1) else 0) else 0)
      = ∑ i : Fin n, g i.succ := by
  classical
  have hinj : Function.Injective (fun i : Fin n => ({0, i.succ} : Finset (Fin (n + 1)))) := by
    intro a b hab
    have hab' : ({0, a.succ} : Finset (Fin (n + 1))) = {0, b.succ} := hab
    have hmem : a.succ ∈ ({0, b.succ} : Finset (Fin (n + 1))) := by
      rw [← hab']; simp
    rcases Finset.mem_insert.1 hmem with h0 | h1
    · exact absurd h0 (Fin.succ_ne_zero a)
    · exact Fin.succ_injective _ (Finset.mem_singleton.1 h1)
  have hsub : ∀ R ∈ (Finset.univ : Finset (Finset (Fin (n + 1)))),
      R ∉ (Finset.univ : Finset (Fin n)).map ⟨_, hinj⟩ →
      (if h : R.card = 2 then
        (if R.orderEmbOfFin h 0 = 0 then g (R.orderEmbOfFin h 1) else 0) else 0) = 0 := by
    intro R _ hR
    by_cases h : R.card = 2
    · rw [dif_pos h]
      by_cases h0 : R.orderEmbOfFin h 0 = 0
      · exfalso
        obtain ⟨i, hi⟩ := Fin.exists_succ_eq.2 (pair_one_ne R h)
        apply hR
        refine Finset.mem_map.2 ⟨i, Finset.mem_univ _, ?_⟩
        ext x
        simp only [Function.Embedding.coeFn_mk, Finset.mem_insert, Finset.mem_singleton]
        rw [pair_mem R h x, h0, hi]
      · rw [if_neg h0]
    · rw [dif_neg h]
  rw [← Finset.sum_subset (Finset.subset_univ _) hsub, Finset.sum_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  have hc : ({0, i.succ} : Finset (Fin (n + 1))).card = 2 :=
    Finset.card_pair (Fin.succ_ne_zero i).symm
  rw [dif_pos hc]
  have hlt := pair_lt _ hc
  have m0 := Finset.orderEmbOfFin_mem ({0, i.succ} : Finset (Fin (n + 1))) hc 0
  have m1 := Finset.orderEmbOfFin_mem ({0, i.succ} : Finset (Fin (n + 1))) hc 1
  simp only [Finset.mem_insert, Finset.mem_singleton] at m0 m1
  have e0 : ({0, i.succ} : Finset (Fin (n + 1))).orderEmbOfFin hc 0 = 0 := by
    rcases m0 with h0 | h0
    · exact h0
    · exfalso
      rcases m1 with h1 | h1
      · rw [h1] at hlt; exact absurd hlt (Fin.not_lt_zero _)
      · rw [h0, h1] at hlt; exact lt_irrefl _ hlt
  have e1 : ({0, i.succ} : Finset (Fin (n + 1))).orderEmbOfFin hc 1 = i.succ := by
    rcases m1 with h1 | h1
    · rw [e0, h1] at hlt; exact absurd hlt (lt_irrefl _)
    · exact h1
  rw [if_pos e0, e1]

theorem perm_big (t : Fin 5 × Fin 7 → ℂ)
    (hZ : ∀ i j, i ≠ 0 → j ≠ 0 → t (i, j) = 0) (k : ℕ) (hk : 3 ≤ k)
    (R : Finset (Fin 5)) (C : Finset (Fin 7)) (hR : R.card = k) (hC : C.card = k) :
    Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin hR a, C.orderEmbOfFin hC b)) = 0 := by
  unfold Matrix.permanent
  refine Finset.sum_eq_zero fun σ _ => ?_
  obtain ⟨i, hi1, hi2⟩ := exists_off (fun i => R.orderEmbOfFin hR (σ i))
    (fun i => C.orderEmbOfFin hC i) 0 0
    (fun a b hab => σ.injective ((R.orderEmbOfFin hR).injective hab))
    (fun a b hab => (C.orderEmbOfFin hC).injective hab) hk
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  simp only [Matrix.of_apply]
  exact hZ _ _ hi1 hi2

theorem perm_one (t : Fin 5 × Fin 7 → ℂ)
    (R : Finset (Fin 5)) (C : Finset (Fin 7)) (hR : R.card = 1) (hC : C.card = 1) :
    Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin hR a, C.orderEmbOfFin hC b))
      = t (R.orderEmbOfFin hR 0, C.orderEmbOfFin hC 0) := by
  simp [Matrix.permanent]

theorem perm_two (t : Fin 5 × Fin 7 → ℂ)
    (hZ : ∀ i j, i ≠ 0 → j ≠ 0 → t (i, j) = 0)
    (R : Finset (Fin 5)) (C : Finset (Fin 7)) (hR : R.card = 2) (hC : C.card = 2) :
    Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin hR a, C.orderEmbOfFin hC b))
      = (if R.orderEmbOfFin hR 0 = 0 then t (R.orderEmbOfFin hR 1, 0) else 0) *
        (if C.orderEmbOfFin hC 0 = 0 then t (0, C.orderEmbOfFin hC 1) else 0) := by
  have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
  have hr1 := pair_one_ne R hR
  have hc1 := pair_one_ne C hC
  unfold Matrix.permanent
  rw [hu, Finset.sum_pair hne]
  simp only [Fin.prod_univ_two, Matrix.of_apply, Equiv.Perm.coe_one, id_eq,
    Equiv.swap_apply_left, Equiv.swap_apply_right]
  rw [hZ _ _ hr1 hc1, mul_zero, zero_add]
  by_cases h0 : R.orderEmbOfFin hR 0 = 0
  · by_cases g0 : C.orderEmbOfFin hC 0 = 0
    · rw [if_pos h0, if_pos g0, h0, g0]
    · rw [if_neg g0, mul_zero, hZ _ _ hr1 g0, zero_mul]
  · rw [if_neg h0, zero_mul, hZ _ _ h0 hc1, mul_zero]

theorem level (t : Fin 5 × Fin 7 → ℂ)
    (hZ : ∀ i j, i ≠ 0 → j ≠ 0 → t (i, j) = 0)
    (hRow : (∑ j : Fin 7, t (0, j)) = 0)
    (hCol : (∑ i : Fin 4, t (i.succ, 0)) = 0)
    (k : ℕ) (h1 : 1 ≤ k) :
    (∑ R : Finset (Fin 5), ∑ C : Finset (Fin 7), if h : R.card = k ∧ C.card = k then Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0 := by
  rcases Nat.lt_or_ge k 3 with hlt | hge
  · rcases (by omega : k = 1 ∨ k = 2) with rfl | rfl
    · have hpt : ∀ (R : Finset (Fin 5)) (C : Finset (Fin 7)),
          (if h : R.card = 1 ∧ C.card = 1 then Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0)
            = if hR : R.card = 1 then
                (if hC : C.card = 1 then t (R.orderEmbOfFin hR 0, C.orderEmbOfFin hC 0) else 0)
              else 0 := by
        intro R C
        by_cases hR : R.card = 1
        · by_cases hC : C.card = 1
          · rw [dif_pos ⟨hR, hC⟩, dif_pos hR, dif_pos hC, perm_one]
          · rw [dif_neg (fun h => hC h.2), dif_pos hR, dif_neg hC]
        · rw [dif_neg (fun h => hR h.1), dif_neg hR]
      simp_rw [hpt]
      have hinner : ∀ R : Finset (Fin 5),
          (∑ C : Finset (Fin 7), if hR : R.card = 1 then
            (if hC : C.card = 1 then t (R.orderEmbOfFin hR 0, C.orderEmbOfFin hC 0) else 0)
            else 0)
            = if hR : R.card = 1 then (∑ j : Fin 7, t (R.orderEmbOfFin hR 0, j)) else 0 := by
        intro R
        by_cases hR : R.card = 1
        · simp only [dif_pos hR]
          exact singleSum (fun j => t (R.orderEmbOfFin hR 0, j))
        · simp only [dif_neg hR]
          exact Finset.sum_const_zero
      simp_rw [hinner]
      rw [singleSum (fun i => ∑ j : Fin 7, t (i, j)), Fin.sum_univ_succ, hRow, zero_add]
      have hrow : ∀ i : Fin 4, (∑ j : Fin 7, t (i.succ, j)) = t (i.succ, 0) := by
        intro i
        rw [Fin.sum_univ_succ]
        have hz : (∑ j : Fin 6, t (i.succ, j.succ)) = 0 :=
          Finset.sum_eq_zero fun j _ => hZ _ _ (Fin.succ_ne_zero i) (Fin.succ_ne_zero j)
        rw [hz, add_zero]
      simp_rw [hrow]
      exact hCol
    · have hpt : ∀ (R : Finset (Fin 5)) (C : Finset (Fin 7)),
          (if h : R.card = 2 ∧ C.card = 2 then Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0)
            = (if hR : R.card = 2 then
                (if R.orderEmbOfFin hR 0 = 0 then t (R.orderEmbOfFin hR 1, 0) else 0) else 0) *
              (if hC : C.card = 2 then
                (if C.orderEmbOfFin hC 0 = 0 then t (0, C.orderEmbOfFin hC 1) else 0) else 0) := by
        intro R C
        by_cases hR : R.card = 2
        · by_cases hC : C.card = 2
          · rw [dif_pos ⟨hR, hC⟩, dif_pos hR, dif_pos hC, perm_two t hZ]
          · rw [dif_neg (fun h => hC h.2), dif_neg hC, mul_zero]
        · rw [dif_neg (fun h => hR h.1), dif_neg hR, zero_mul]
      simp_rw [hpt]
      rw [← Finset.sum_mul_sum, pairSum (fun i => t (i, 0)), hCol, zero_mul]
  · refine Finset.sum_eq_zero fun R _ => Finset.sum_eq_zero fun C _ => ?_
    by_cases h : R.card = k ∧ C.card = k
    · rw [dif_pos h]
      exact perm_big t hZ k hge R C h.1 h.2
    · rw [dif_neg h]

end PEqualNP.Outside.L_gct_207

theorem PEqualNP.Outside.L_gct_207 : ∃ L : Submodule ℂ (Fin 5 × Fin 7 → ℂ), Module.finrank ℂ L = 9 ∧ (∀ t ∈ L, ∀ k : ℕ, 1 ≤ k → k ≤ 5 → (∑ R : Finset (Fin 5), ∑ C : Finset (Fin 7), if h : R.card = k ∧ C.card = k then Matrix.permanent (Matrix.of fun a b => t (R.orderEmbOfFin h.1 a, C.orderEmbOfFin h.2 b)) else 0) = 0) := by
  refine ⟨LinearMap.range PEqualNP.Outside.L_gct_207.formMap, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj PEqualNP.Outside.L_gct_207.formMap_injective,
      Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card]
    decide
  · rintro t ⟨x, rfl⟩ k h1 _
    exact PEqualNP.Outside.L_gct_207.level _
      (PEqualNP.Outside.L_gct_207.form_zero x)
      (PEqualNP.Outside.L_gct_207.form_row x)
      (PEqualNP.Outside.L_gct_207.form_col x) k h1
