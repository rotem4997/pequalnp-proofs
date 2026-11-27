import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside

private def delta {α : Type*} [DecidableEq α] (x y : α) : ℂ :=
  if x = y then 1 else 0

private lemma inj4_ind {α : Type*} [DecidableEq α] (a b c d : α) :
    (if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then (1 : ℂ) else 0) =
      (1 - delta a b - delta a c - delta a d - delta b c - delta b d - delta c d) +
      (delta a b * delta c d + delta a c * delta b d + delta a d * delta b c) +
      2 * (delta a b * delta a c + delta a b * delta a d + delta a c * delta a d + delta b c * delta b d) -
      6 * (delta a b * delta a c * delta a d) := by
  unfold delta
  by_cases hab : a = b
  · subst hab
    by_cases hac : a = c
    · subst hac
      by_cases had : a = d
      · subst had; simp; norm_num
      · simp [had]; norm_num
    · by_cases had : a = d
      · subst had; simp [hac]; norm_num
      · by_cases hcd : c = d
        · subst hcd; simp [hac]
        · simp [hac, had, hcd]
  · by_cases hac : a = c
    · subst hac
      by_cases had : a = d
      · subst had; simp [hab, Ne.symm hab]; norm_num
      · by_cases hbd : b = d
        · subst hbd; simp [hab, Ne.symm hab]
        · simp [hab, had, hbd, Ne.symm hab]
    · by_cases had : a = d
      · subst had
        by_cases hbc : b = c
        · subst hbc; simp [hab, Ne.symm hab]
        · simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac]
      · by_cases hbc : b = c
        · subst hbc
          by_cases hbd : b = d
          · subst hbd; simp [hab]; norm_num
          · simp [hab, had, hbd]
        · by_cases hbd : b = d
          · subst hbd; simp [hab, hac, hbc, Ne.symm hbc]
          · by_cases hcd : c = d
            · subst hcd; simp [hab, hac, hbc]
            · simp [hab, hac, had, hbc, hbd, hcd]

private lemma injective_vec4_iff {α : Type*} (a b c d : α) :
    Function.Injective ![a, b, c, d] ↔
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e; exact absurd (h (a₁ := 0) (a₂ := 1) e) (by decide)
    · intro e; exact absurd (h (a₁ := 0) (a₂ := 2) e) (by decide)
    · intro e; exact absurd (h (a₁ := 0) (a₂ := 3) e) (by decide)
    · intro e; exact absurd (h (a₁ := 1) (a₂ := 2) e) (by decide)
    · intro e; exact absurd (h (a₁ := 1) (a₂ := 3) e) (by decide)
    · intro e; exact absurd (h (a₁ := 2) (a₂ := 3) e) (by decide)
  · rintro ⟨hab, hac, had, hbc, hbd, hcd⟩ i j hij
    fin_cases i <;> fin_cases j <;> simp_all

private lemma sum_emb_fin4_eq_ind {α : Type*} [Fintype α] [DecidableEq α]
    (F : α → α → α → α → ℂ) :
    ∑ f : Fin 4 ↪ α, F (f 0) (f 1) (f 2) (f 3) =
      ∑ a : α, ∑ b : α, ∑ c : α, ∑ d : α,
        (if a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d then (1 : ℂ) else 0) * F a b c d := by
  let e1 : { f : Fin 4 → α // Function.Injective f } ≃ (Fin 4 ↪ α) :=
    { toFun := fun f => ⟨f.1, f.2⟩
      invFun := fun f => ⟨f, f.injective⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : (Fin 4 → α) ≃ α × α × α × α :=
    { toFun := fun f => (f 0, f 1, f 2, f 3)
      invFun := fun ⟨a, b, c, d⟩ => ![a, b, c, d]
      left_inv := fun f => by ext i; fin_cases i <;> rfl
      right_inv := fun ⟨_, _, _, _⟩ => rfl }
  have h1 : ∑ f : Fin 4 ↪ α, F (f 0) (f 1) (f 2) (f 3) =
      ∑ f : { f : Fin 4 → α // Function.Injective f }, F (f.1 0) (f.1 1) (f.1 2) (f.1 3) := by
    exact (Fintype.sum_equiv e1 _ _ (fun _ => rfl)).symm
  have h2 : ∑ f : { f : Fin 4 → α // Function.Injective f }, F (f.1 0) (f.1 1) (f.1 2) (f.1 3) =
      ∑ f : Fin 4 → α, if Function.Injective f then F (f 0) (f 1) (f 2) (f 3) else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun f _ => f.1) ?_ ?_ ?_ ?_
    · intro f _; simp [f.2]
    · intro f₁ _ f₂ _ h; exact Subtype.ext h
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      exact ⟨⟨f, hf⟩, Finset.mem_univ _, rfl⟩
    · intro _ _; rfl
  have h3 : ∑ f : Fin 4 → α, (if Function.Injective f then F (f 0) (f 1) (f 2) (f 3) else 0) =
      ∑ x : α × α × α × α,
        if Function.Injective ![x.1, x.2.1, x.2.2.1, x.2.2.2] then
          F x.1 x.2.1 x.2.2.1 x.2.2.2
        else 0 := by
    exact Fintype.sum_equiv e2 _ _ (fun f => by
      have hf : ![f 0, f 1, f 2, f 3] = f := e2.left_inv f
      simp [e2, hf])
  rw [h1, h2, h3]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [injective_vec4_iff]
  split_ifs <;> simp

private lemma sum_emb_fin4_of_zero_marginals {α : Type*} [Fintype α] [DecidableEq α]
    (F : α → α → α → α → ℂ)
    (h0 : ∀ b c d, ∑ a, F a b c d = 0)
    (h1 : ∀ a c d, ∑ b, F a b c d = 0)
    (h2 : ∀ a b d, ∑ c, F a b c d = 0)
    (h3 : ∀ a b c, ∑ d, F a b c d = 0) :
    ∑ f : Fin 4 ↪ α, F (f 0) (f 1) (f 2) (f 3) =
      (∑ x, ∑ y, F x x y y) + (∑ x, ∑ y, F x y x y) + (∑ x, ∑ y, F x y y x) -
      6 * ∑ x, F x x x x := by
  have hsum_a : ∀ (g : α → α → α → ℂ), ∑ a, ∑ b, ∑ c, ∑ d, g b c d * F a b c d = 0 := by
    intro g
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [← Finset.mul_sum, h0, mul_zero]
  have hsum_b : ∀ (g : α → α → α → ℂ), ∑ a, ∑ b, ∑ c, ∑ d, g a c d * F a b c d = 0 := by
    intro g
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [← Finset.mul_sum, h1, mul_zero]
  have hsum_c : ∀ (g : α → α → α → ℂ), ∑ a, ∑ b, ∑ c, ∑ d, g a b d * F a b c d = 0 := by
    intro g
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [← Finset.mul_sum, h2, mul_zero]
  have hsum_d : ∀ (g : α → α → α → ℂ), ∑ a, ∑ b, ∑ c, ∑ d, g a b c * F a b c d = 0 := by
    intro g
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ =>
      Finset.sum_eq_zero fun c _ => ?_
    rw [← Finset.mul_sum, h3, mul_zero]
  have hgrp1 : ∑ a, ∑ b, ∑ c, ∑ d,
      (1 - delta a b - delta a c - delta a d - delta b c - delta b d - delta c d) * F a b c d = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [hsum_a (fun _ _ _ => 1),
        hsum_c (fun a b _ => delta a b),
        hsum_b (fun a c _ => delta a c),
        hsum_b (fun a _ d => delta a d),
        hsum_a (fun b c _ => delta b c),
        hsum_a (fun b _ d => delta b d),
        hsum_a (fun _ c d => delta c d)]
    ring
  have hgrp3 : ∑ a, ∑ b, ∑ c, ∑ d,
      (2 * (delta a b * delta a c + delta a b * delta a d + delta a c * delta a d + delta b c * delta b d)) *
        F a b c d = 0 := by
    have hmul : ∀ a b c d,
        (2 * (delta a b * delta a c + delta a b * delta a d + delta a c * delta a d + delta b c * delta b d)) *
          F a b c d =
        (2 * (delta a b * delta a c)) * F a b c d +
        (2 * (delta a b * delta a d)) * F a b c d +
        (2 * (delta a c * delta a d)) * F a b c d +
        (2 * (delta b c * delta b d)) * F a b c d := fun _ _ _ _ => by ring
    simp only [hmul, Finset.sum_add_distrib]
    rw [hsum_d (fun a b c => 2 * (delta a b * delta a c)),
        hsum_c (fun a b d => 2 * (delta a b * delta a d)),
        hsum_b (fun a c d => 2 * (delta a c * delta a d)),
        hsum_a (fun b c d => 2 * (delta b c * delta b d))]
    ring
  have hdelta_sum : ∀ (x : α) (f : α → ℂ), ∑ y : α, delta x y * f y = f x := by
    intro x f
    simp only [delta, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  have hp1 : ∑ a, ∑ b, ∑ c, ∑ d, (delta a b * delta c d) * F a b c d = ∑ x, ∑ y, F x x y y := by
    refine Finset.sum_congr rfl fun a _ => ?_
    have h : ∀ b, ∑ c, ∑ d, (delta a b * delta c d) * F a b c d =
        delta a b * ∑ c, ∑ d, delta c d * F a b c d := by
      intro b; simp only [mul_assoc, ← Finset.mul_sum]
    simp only [h, hdelta_sum]
  have hp2 : ∑ a, ∑ b, ∑ c, ∑ d, (delta a c * delta b d) * F a b c d = ∑ x, ∑ y, F x y x y := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have h : ∀ c, ∑ d, (delta a c * delta b d) * F a b c d =
        delta a c * ∑ d, delta b d * F a b c d := by
      intro c; simp only [mul_assoc, ← Finset.mul_sum]
    simp only [h, hdelta_sum]
  have hp3 : ∑ a, ∑ b, ∑ c, ∑ d, (delta a d * delta b c) * F a b c d = ∑ x, ∑ y, F x y y x := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have h : ∀ c, ∑ d, (delta a d * delta b c) * F a b c d =
        delta b c * ∑ d, delta a d * F a b c d := by
      intro c
      have hcomm : ∀ d, (delta a d * delta b c) * F a b c d =
          delta b c * (delta a d * F a b c d) := fun _ => by ring
      simp only [hcomm, ← Finset.mul_sum]
    simp only [h, hdelta_sum]
  have hgrp2 : ∑ a, ∑ b, ∑ c, ∑ d,
      (delta a b * delta c d + delta a c * delta b d + delta a d * delta b c) * F a b c d =
      (∑ x, ∑ y, F x x y y) + (∑ x, ∑ y, F x y x y) + (∑ x, ∑ y, F x y y x) := by
    simp only [add_mul, Finset.sum_add_distrib]
    rw [hp1, hp2, hp3]
  have hgrp4 : ∑ a, ∑ b, ∑ c, ∑ d,
      (6 * (delta a b * delta a c * delta a d)) * F a b c d = 6 * ∑ x, F x x x x := by
    have hmul : ∀ a b c d,
        (6 * (delta a b * delta a c * delta a d)) * F a b c d =
        6 * (delta a b * (delta a c * (delta a d * F a b c d))) := fun _ _ _ _ => by ring
    simp only [hmul, ← Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hdelta_sum]
  have hsplit : ∀ (A B C D : α → α → α → α → ℂ),
      ∑ a, ∑ b, ∑ c, ∑ d, (A a b c d + B a b c d + C a b c d - D a b c d) * F a b c d =
        (∑ a, ∑ b, ∑ c, ∑ d, A a b c d * F a b c d) +
        (∑ a, ∑ b, ∑ c, ∑ d, B a b c d * F a b c d) +
        (∑ a, ∑ b, ∑ c, ∑ d, C a b c d * F a b c d) -
        (∑ a, ∑ b, ∑ c, ∑ d, D a b c d * F a b c d) := by
    intro A B C D
    simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [sum_emb_fin4_eq_ind]
  simp_rw [inj4_ind]
  rw [hsplit]
  rw [hgrp1, hgrp2, hgrp3, hgrp4]
  ring

theorem L_gct_134 : ∀ (p q : ℕ) (t : Fin p × Fin q → ℂ), (∀ i, ∑ j, t (i, j) = 0) → (∀ j, ∑ i, t (i, j) = 0) → ∑ f : Fin 4 ↪ Fin p, ∑ g : Fin 4 ↪ Fin q, ∏ k, t (f k, g k) = 36 * ∑ i, ∑ j, t (i, j) ^ 4 - 18 * (∑ i, (∑ j, t (i, j) ^ 2) ^ 2 + ∑ j, (∑ i, t (i, j) ^ 2) ^ 2) + 6 * ∑ i, ∑ i', ∑ j, ∑ j', t (i, j) * t (i, j') * t (i', j) * t (i', j') + 3 * (∑ i, ∑ j, t (i, j) ^ 2) ^ 2 := by
  intro p q t hrow hcol
  let G : Fin p → Fin p → Fin p → Fin p → ℂ := fun i0 i1 i2 i3 =>
    ∑ g : Fin 4 ↪ Fin q, t (i0, g 0) * t (i1, g 1) * t (i2, g 2) * t (i3, g 3)
  have hG_eval : ∀ i0 i1 i2 i3, G i0 i1 i2 i3 =
      (∑ x, ∑ y, t (i0, x) * t (i1, x) * t (i2, y) * t (i3, y)) +
      (∑ x, ∑ y, t (i0, x) * t (i1, y) * t (i2, x) * t (i3, y)) +
      (∑ x, ∑ y, t (i0, x) * t (i1, y) * t (i2, y) * t (i3, x)) -
      6 * ∑ x, t (i0, x) * t (i1, x) * t (i2, x) * t (i3, x) := by
    intro i0 i1 i2 i3
    exact sum_emb_fin4_of_zero_marginals
      (fun j0 j1 j2 j3 => t (i0, j0) * t (i1, j1) * t (i2, j2) * t (i3, j3))
      (fun j1 j2 j3 => by simp only [← Finset.sum_mul, hrow, zero_mul])
      (fun j0 j2 j3 => by
        have : ∀ j1, t (i0, j0) * t (i1, j1) * t (i2, j2) * t (i3, j3) =
            t (i1, j1) * (t (i0, j0) * t (i2, j2) * t (i3, j3)) := fun _ => by ring
        simp only [this, ← Finset.sum_mul, hrow, zero_mul])
      (fun j0 j1 j3 => by
        have : ∀ j2, t (i0, j0) * t (i1, j1) * t (i2, j2) * t (i3, j3) =
            t (i2, j2) * (t (i0, j0) * t (i1, j1) * t (i3, j3)) := fun _ => by ring
        simp only [this, ← Finset.sum_mul, hrow, zero_mul])
      (fun j0 j1 j2 => by simp only [← Finset.mul_sum, hrow, mul_zero])
  have hLHS : ∑ f : Fin 4 ↪ Fin p, ∑ g : Fin 4 ↪ Fin q, ∏ k, t (f k, g k) =
      ∑ f : Fin 4 ↪ Fin p, G (f 0) (f 1) (f 2) (f 3) := by
    refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun g _ => ?_
    exact Fin.prod_univ_four (fun k => t (f k, g k))
  rw [hLHS]
  rw [sum_emb_fin4_of_zero_marginals G
    (fun i1 i2 i3 => by
      dsimp only [G]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun g _ => ?_
      simp only [← Finset.sum_mul, hcol, zero_mul])
    (fun i0 i2 i3 => by
      dsimp only [G]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun g _ => ?_
      have : ∀ i1, t (i0, g 0) * t (i1, g 1) * t (i2, g 2) * t (i3, g 3) =
          t (i1, g 1) * (t (i0, g 0) * t (i2, g 2) * t (i3, g 3)) := fun _ => by ring
      simp only [this, ← Finset.sum_mul, hcol, zero_mul])
    (fun i0 i1 i3 => by
      dsimp only [G]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun g _ => ?_
      have : ∀ i2, t (i0, g 0) * t (i1, g 1) * t (i2, g 2) * t (i3, g 3) =
          t (i2, g 2) * (t (i0, g 0) * t (i1, g 1) * t (i3, g 3)) := fun _ => by ring
      simp only [this, ← Finset.sum_mul, hcol, zero_mul])
    (fun i0 i1 i2 => by
      dsimp only [G]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun g _ => ?_
      simp only [← Finset.mul_sum, hcol, mul_zero])]
  have hG_pair : ∀ i i',
      G i i i' i' =
        (∑ j, ∑ j', t (i, j) ^ 2 * t (i', j') ^ 2) +
        2 * (∑ j, ∑ j', t (i, j) * t (i, j') * t (i', j) * t (i', j')) -
        6 * (∑ j, t (i, j) ^ 2 * t (i', j) ^ 2) := by
    intro i i'
    rw [hG_eval]
    have h1 : (∑ x, ∑ y, t (i, x) * t (i, x) * t (i', y) * t (i', y)) =
        ∑ j, ∑ j', t (i, j) ^ 2 * t (i', j') ^ 2 := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring
    have h2 : (∑ x, ∑ y, t (i, x) * t (i, y) * t (i', y) * t (i', x)) =
        ∑ j, ∑ j', t (i, j) * t (i, j') * t (i', j) * t (i', j') := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring
    have h3 : (∑ x, t (i, x) * t (i, x) * t (i', x) * t (i', x)) =
        ∑ j, t (i, j) ^ 2 * t (i', j) ^ 2 := by
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [h1, h2, h3]
    ring
  have hG_alt1 : ∀ i i', G i i' i i' = G i i i' i' := by
    intro i i'
    rw [hG_eval, hG_eval]
    have h1 : (∑ x, ∑ y, t (i, x) * t (i', x) * t (i, y) * t (i', y)) =
        ∑ x, ∑ y, t (i, x) * t (i, y) * t (i', x) * t (i', y) := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    have h2 : (∑ x, ∑ y, t (i, x) * t (i', y) * t (i, x) * t (i', y)) =
        ∑ x, ∑ y, t (i, x) * t (i, x) * t (i', y) * t (i', y) := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    have h3 : (∑ x, ∑ y, t (i, x) * t (i', y) * t (i, y) * t (i', x)) =
        ∑ x, ∑ y, t (i, x) * t (i, y) * t (i', y) * t (i', x) := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    have h4 : (∑ x, t (i, x) * t (i', x) * t (i, x) * t (i', x)) =
        ∑ x, t (i, x) * t (i, x) * t (i', x) * t (i', x) := by
      refine Finset.sum_congr rfl fun x _ => by ring
    rw [h1, h2, h3, h4]
    ring
  have hG_alt2 : ∀ i i', G i i' i' i = G i i i' i' := by
    intro i i'
    rw [hG_eval, hG_eval]
    have h1 : (∑ x, ∑ y, t (i, x) * t (i', x) * t (i', y) * t (i, y)) =
        ∑ x, ∑ y, t (i, x) * t (i, y) * t (i', x) * t (i', y) := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    have h2 : (∑ x, ∑ y, t (i, x) * t (i', y) * t (i', x) * t (i, y)) =
        ∑ x, ∑ y, t (i, x) * t (i, y) * t (i', y) * t (i', x) := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    have h3 : (∑ x, ∑ y, t (i, x) * t (i', y) * t (i', y) * t (i, x)) =
        ∑ x, ∑ y, t (i, x) * t (i, x) * t (i', y) * t (i', y) := by
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    have h4 : (∑ x, t (i, x) * t (i', x) * t (i', x) * t (i, x)) =
        ∑ x, t (i, x) * t (i, x) * t (i', x) * t (i', x) := by
      refine Finset.sum_congr rfl fun x _ => by ring
    rw [h1, h2, h3, h4]
    ring
  have hG_diag : ∀ i, G i i i i = 3 * (∑ j, t (i, j) ^ 2) ^ 2 - 6 * ∑ j, t (i, j) ^ 4 := by
    intro i
    rw [hG_eval]
    have hsq : ∀ (f : Fin q → Fin q → ℂ),
        (∀ x y, f x y = t (i, x) ^ 2 * t (i, y) ^ 2) →
        ∑ x, ∑ y, f x y = (∑ j, t (i, j) ^ 2) ^ 2 := by
      intro f hf
      simp only [hf, ← Finset.mul_sum, ← Finset.sum_mul, sq]
    have h1 := hsq (fun x y => t (i, x) * t (i, x) * t (i, y) * t (i, y)) (fun x y => by ring)
    have h2 := hsq (fun x y => t (i, x) * t (i, y) * t (i, x) * t (i, y)) (fun x y => by ring)
    have h3 := hsq (fun x y => t (i, x) * t (i, y) * t (i, y) * t (i, x)) (fun x y => by ring)
    have h4 : ∑ x, t (i, x) * t (i, x) * t (i, x) * t (i, x) = ∑ j, t (i, j) ^ 4 := by
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [h1, h2, h3, h4]
    ring
  have hSum_alt1 : ∑ x, ∑ y, G x y x y = ∑ x, ∑ y, G x x y y :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hG_alt1 x y
  have hSum_alt2 : ∑ x, ∑ y, G x y y x = ∑ x, ∑ y, G x x y y :=
    Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hG_alt2 x y
  have hSum_pair : ∑ i, ∑ i', G i i i' i' =
      (∑ i, ∑ i', ∑ j, ∑ j', t (i, j) ^ 2 * t (i', j') ^ 2) +
      2 * (∑ i, ∑ i', ∑ j, ∑ j', t (i, j) * t (i, j') * t (i', j) * t (i', j')) -
      6 * (∑ i, ∑ i', ∑ j, t (i, j) ^ 2 * t (i', j) ^ 2) := by
    trans ∑ i, ∑ i',
        ((∑ j, ∑ j', t (i, j) ^ 2 * t (i', j') ^ 2) +
         2 * (∑ j, ∑ j', t (i, j) * t (i, j') * t (i', j) * t (i', j')) -
         6 * (∑ j, t (i, j) ^ 2 * t (i', j) ^ 2))
    · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => hG_pair i i'
    · simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hSum_diag : ∑ i, G i i i i =
      3 * (∑ i, (∑ j, t (i, j) ^ 2) ^ 2) - 6 * (∑ i, ∑ j, t (i, j) ^ 4) := by
    trans ∑ i, (3 * (∑ j, t (i, j) ^ 2) ^ 2 - 6 * ∑ j, t (i, j) ^ 4)
    · exact Finset.sum_congr rfl fun i _ => hG_diag i
    · simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hSum_alt1, hSum_alt2, hSum_pair, hSum_diag]
  have hS1 : (∑ i, ∑ i', ∑ j, ∑ j', t (i, j) ^ 2 * t (i', j') ^ 2) =
      (∑ i, ∑ j, t (i, j) ^ 2) ^ 2 := by
    simp only [← Finset.mul_sum, ← Finset.sum_mul, sq]
  have hS2 : (∑ i, ∑ i', ∑ j, t (i, j) ^ 2 * t (i', j) ^ 2) =
      ∑ j, (∑ i, t (i, j) ^ 2) ^ 2 := by
    calc
      ∑ i, ∑ i', ∑ j, t (i, j) ^ 2 * t (i', j) ^ 2
          = ∑ i, ∑ j, ∑ i', t (i, j) ^ 2 * t (i', j) ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ j, ∑ i, ∑ i', t (i, j) ^ 2 * t (i', j) ^ 2 := Finset.sum_comm
      _ = ∑ j, (∑ i, t (i, j) ^ 2) ^ 2 := by
            refine Finset.sum_congr rfl fun j _ => ?_
            simp only [← Finset.mul_sum, ← Finset.sum_mul, sq]
  rw [hS1, hS2]
  ring

end PEqualNP.Outside
