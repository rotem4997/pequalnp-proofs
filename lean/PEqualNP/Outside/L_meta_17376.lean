import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17376
open PEqualNP.CircuitLowerBounds



def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem ev_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (U V : List Bool)
    (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    g.op.eval (g.inputs.map fun i => U.getD i false) = true →
      g.op.eval (g.inputs.map fun i => V.getD i false) = true := by
  rcases hg with h1 | h1 <;> rw [h1] <;> simp only [GateOp.eval, List.all_eq_true, List.any_eq_true,
    List.mem_map, id_eq]
  · intro hu x ⟨i, hi, hx⟩
    subst hx
    exact h i (hu _ ⟨i, hi, rfl⟩)
  · rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨_, ⟨i, hi, rfl⟩, h i hx⟩

theorem key : ∀ (gs : List Gate), (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    ∀ U V : List Bool, U.length = V.length → (∀ i, U.getD i false = true → V.getD i false = true) →
    ∀ i, (gs.foldl stp U).getD i false = true → (gs.foldl stp V).getD i false = true := by
  intro gs
  induction gs with
  | nil => intro _ U V _ h i; exact h i
  | cons g gs ih =>
    intro hgs U V hl h i
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [stp, hl]
    · intro k hk
      unfold stp at hk ⊢
      rcases Nat.lt_trichotomy k U.length with hlt | heq | hgt
      · rw [List.getD_append _ _ _ _ hlt] at hk
        rw [List.getD_append _ _ _ _ (hl ▸ hlt)]
        exact h k hk
      · subst heq
        rw [List.getD_append_right _ _ _ _ (le_refl _)] at hk
        rw [hl, List.getD_append_right _ _ _ _ (le_refl _)]
        simp only [Nat.sub_self, List.getD_cons_zero] at hk ⊢
        exact ev_mono g (hgs g (List.mem_cons_self ..)) U V h hk
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hk
        exact absurd hk (by simp)
theorem cmono (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    PEqualNP.MetaComplexity.circuitFun n C x = true → PEqualNP.MetaComplexity.circuitFun n C y = true := by
  intro hx
  have hgs : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    have := (hC g hg).1
    simpa using this
  exact key C.gates hgs (List.ofFn x) (List.ofFn y) (by simp) (fun i hi => by
    by_cases h : i < n
    · have e1 : (List.ofFn x).getD i false = x ⟨i, h⟩ := by simp [List.getD_eq_getElem?_getD, h]
      have e2 : (List.ofFn y).getD i false = y ⟨i, h⟩ := by simp [List.getD_eq_getElem?_getD, h]
      rw [e1] at hi; rw [e2]; exact hxy _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hi; exact absurd hi (by simp)) C.output hx

def tr {n : ℕ} (y : Fin n → Bool) : Finset (Fin n) := Finset.univ.filter (fun i => y i = true)

theorem tr_lt {n : ℕ} (z y : Fin n → Bool) (hzy : ∀ i, z i = true → y i = true) (hne : z ≠ y) :
    (tr z).card < (tr y).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨?_, ?_⟩
  · intro i hi
    simp only [tr, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hzy i hi
  · intro heq
    apply hne
    funext i
    have h : i ∈ tr z ↔ i ∈ tr y := by rw [heq]
    simp only [tr, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact Bool.eq_iff_iff.mpr h

theorem fmono {n : ℕ} (f : (Fin n → Bool) → Bool) (hf : Monotone f) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) : f x = true → f y = true := by
  intro hx
  have hle : x ≤ y := fun i => by
    cases h : x i
    · exact Bool.false_le _
    · rw [hxy i h]
  have := hf hle
  rw [hx] at this
  revert this; cases f y <;> decide

end PEqualNP.Outside.L_meta_17376

open PEqualNP.Outside.L_meta_17376 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_17376 : ∀ (x1 : ℕ) (x2 : (Fin x1 → Bool) → Bool) (x3 : PEqualNP.CircuitLowerBounds.Circuit), Monotone x2 → PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x6 : Fin x1 → Bool), (∀ (x7 : Fin x1), x6 x7 = x2 x6 → x2 (Function.update x6 x7 !x6 x7) ≠ x2 x6) → PEqualNP.MetaComplexity.circuitFun x1 x3 x6 = x2 x6) → ∀ (x7 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x3 x7 = x2 x7 := by
  intro n f C hf hC hcrit x
  cases hfx : f x
  · -- a largest point above x where f is false
    let S : Finset (Fin n → Bool) := Finset.univ.filter (fun z => f z = false ∧ ∀ i, x i = true → z i = true)
    have hS : S.Nonempty := ⟨x, by simp [S, hfx]⟩
    obtain ⟨z, hzS, hmax⟩ := Finset.exists_max_image S (fun z => (tr z).card) hS
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hzS
    have hcz : PEqualNP.MetaComplexity.circuitFun n C z = f z := by
      apply hcrit
      intro i hi
      rw [hzS.1] at hi
      intro heq
      rw [hzS.1] at heq
      have hz' : Function.update z i (!z i) ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨heq, fun k hk => ?_⟩
        by_cases hki : k = i
        · subst hki; rw [hzS.2 k hk] at hi; exact absurd hi (by simp)
        · rw [Function.update_of_ne hki]; exact hzS.2 k hk
      have h1 := hmax _ hz'
      have h2 := tr_lt z (Function.update z i (!z i)) (fun k hk => by
        by_cases hki : k = i
        · subst hki; rw [hk] at hi; exact absurd hi (by simp)
        · rw [Function.update_of_ne hki]; exact hk) (fun he => by
          have := congrFun he i
          rw [Function.update_self, hi] at this
          exact absurd this (by simp))
      omega
    rw [hzS.1] at hcz
    cases hcx : PEqualNP.MetaComplexity.circuitFun n C x
    · rfl
    · have := cmono n C hC x z hzS.2 hcx
      rw [hcz] at this; exact absurd this (by simp)
  · -- a smallest point below x where f is true
    let S : Finset (Fin n → Bool) := Finset.univ.filter (fun y => f y = true ∧ ∀ i, y i = true → x i = true)
    have hS : S.Nonempty := ⟨x, by simp [S, hfx]⟩
    obtain ⟨y, hyS, hmin⟩ := Finset.exists_min_image S (fun y => (tr y).card) hS
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hyS
    have hcy : PEqualNP.MetaComplexity.circuitFun n C y = f y := by
      apply hcrit
      intro i hi
      rw [hyS.1] at hi
      intro heq
      rw [hyS.1] at heq
      have hy' : Function.update y i (!y i) ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨heq, fun k hk => ?_⟩
        by_cases hki : k = i
        · subst hki; rw [Function.update_self, hi] at hk; exact absurd hk (by simp)
        · rw [Function.update_of_ne hki] at hk; exact hyS.2 k hk
      have h1 := hmin _ hy'
      have h2 := tr_lt (Function.update y i (!y i)) y (fun k hk => by
        by_cases hki : k = i
        · subst hki; rw [Function.update_self, hi] at hk; exact absurd hk (by simp)
        · rw [Function.update_of_ne hki] at hk; exact hk) (fun he => by
          have := congrFun he i
          rw [Function.update_self, hi] at this
          exact absurd this (by simp))
      omega
    rw [hyS.1] at hcy
    exact cmono n C hC y x hyS.2 hcy
