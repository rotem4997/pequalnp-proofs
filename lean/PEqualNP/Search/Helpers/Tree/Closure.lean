import PEqualNP.Search.Helpers.Tree.Count

/-!
# Helpers for L-lib-103: the closure lemma

`nc T Ψ` counts, with repetition, the entries of the list `Ψ` that touch a free pigeon of `T`
(not closed). The closure lemma: from any `T0` there is `T ⊇ T0` at which every entry of `Ψ`
is closed (touches no free pigeon) or dense (touches at least `r`), and the potential
`|T| + r * nc T Ψ` does not grow. Each step adds the fewer than `r` free pigeons of one sparse
entry, which closes that entry (and all its copies).
-/

namespace PEqualNP.Search.Helpers.Tree

open PEqualNP.Search

open scoped Classical

variable {ι : Type} [Fintype ι] [DecidableEq ι] {l : ℕ}

/-- The number of entries of `Ψ` not closed at `T`, with repetition. -/
noncomputable def nc (T : Finset ι) (Ψ : List (QEq (ι × Fin l))) : ℕ :=
  Ψ.countP fun e => decide (kT T e ≠ 0)

theorem nc_cons (T : Finset ι) (e : QEq (ι × Fin l)) (Ψ : List (QEq (ι × Fin l))) :
    nc T (e :: Ψ) = nc T Ψ + if kT T e ≠ 0 then 1 else 0 := by
  unfold nc
  rw [List.countP_cons]
  simp

theorem countP_le_of_imp {α : Type} (p q : α → Bool) :
    ∀ L : List α, (∀ x ∈ L, q x = true → p x = true) → L.countP q ≤ L.countP p
  | [] => by simp
  | a :: L => by
    intro h
    have ih := countP_le_of_imp p q L fun x hx => h x (List.mem_cons_of_mem _ hx)
    have ha := h a List.mem_cons_self
    rw [List.countP_cons, List.countP_cons]
    cases hq : q a <;> cases hp : p a <;> simp_all <;> omega

theorem countP_lt_of_imp {α : Type} (p q : α → Bool) :
    ∀ L : List α, (∀ x ∈ L, q x = true → p x = true) →
      (∃ x ∈ L, p x = true ∧ q x = false) → L.countP q < L.countP p
  | [] => by simp
  | a :: L => by
    intro h hex
    have hle := countP_le_of_imp p q L fun x hx => h x (List.mem_cons_of_mem _ hx)
    have ha := h a List.mem_cons_self
    rw [List.countP_cons, List.countP_cons]
    by_cases hx : ∃ x ∈ L, p x = true ∧ q x = false
    · have ih := countP_lt_of_imp p q L (fun x hx => h x (List.mem_cons_of_mem _ hx)) hx
      cases hq : q a <;> cases hp : p a <;> simp_all <;> omega
    · obtain ⟨x, hxm, hpx, hqx⟩ := hex
      rcases List.mem_cons.mp hxm with rfl | hxm
      · simp [hpx, hqx]; omega
      · exact absurd ⟨x, hxm, hpx, hqx⟩ hx

theorem nc_mono {T T' : Finset ι} (h : T ⊆ T') (Ψ : List (QEq (ι × Fin l))) :
    nc T' Ψ ≤ nc T Ψ := by
  unfold nc
  refine countP_le_of_imp _ _ Ψ fun x _ hx => ?_
  have := kT_mono h x
  simp only [decide_eq_true_eq] at hx ⊢
  omega

/-- One closing step: adding the free pigeons of `e0` closes `e0`. -/
theorem kT_union_touchP (T : Finset ι) (e0 : QEq (ι × Fin l)) :
    kT (T ∪ touchP T e0) e0 = 0 := by
  unfold kT
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro i hi
  obtain ⟨hiT, b, hb⟩ := mem_touchP.mp hi
  exact hiT (Finset.mem_union_right _ (mem_touchP.mpr ⟨fun h => hiT (Finset.mem_union_left _ h),
    b, hb⟩))

/-- CL: the closure lemma, with the potential `|T| + r * nc T Ψ`. -/
theorem closure (r : ℕ) (Ψ : List (QEq (ι × Fin l))) :
    ∀ T0 : Finset ι, ∃ T, T0 ⊆ T ∧ (∀ e ∈ Ψ, kT T e = 0 ∨ r ≤ kT T e) ∧
      T.card + r * nc T Ψ ≤ T0.card + r * nc T0 Ψ := by
  intro T0
  induction hM : nc T0 Ψ using Nat.strong_induction_on generalizing T0 with
  | _ M ih =>
    by_cases hs : ∃ e ∈ Ψ, kT T0 e ≠ 0 ∧ kT T0 e < r
    · obtain ⟨e0, he0, hne, hlt⟩ := hs
      set T1 := T0 ∪ touchP T0 e0
      have hsub : T0 ⊆ T1 := Finset.subset_union_left
      have h1 : kT T1 e0 = 0 := kT_union_touchP T0 e0
      have hlt1 : nc T1 Ψ < nc T0 Ψ := by
        unfold nc
        refine countP_lt_of_imp _ _ Ψ (fun x _ hx => ?_) ⟨e0, he0, ?_, ?_⟩
        · have := kT_mono hsub x
          simp only [decide_eq_true_eq] at hx ⊢
          omega
        · simpa using hne
        · simpa using h1
      obtain ⟨T, hT1, hd, hpot⟩ := ih (nc T1 Ψ) (hM ▸ hlt1) T1 rfl
      refine ⟨T, hsub.trans hT1, hd, ?_⟩
      have hc1 : T1.card ≤ T0.card + (r - 1) :=
        calc T1.card ≤ T0.card + (touchP T0 e0).card := Finset.card_union_le _ _
          _ ≤ _ := by unfold kT at hlt; omega
      have : r * nc T1 Ψ + r ≤ r * nc T0 Ψ := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt1
      rw [hM] at this
      omega
    · refine ⟨T0, Finset.Subset.refl _, fun e he => ?_, by rw [hM]⟩
      by_cases h0 : kT T0 e = 0
      · exact Or.inl h0
      · exact Or.inr (not_lt.mp fun h => hs ⟨e, he, h0, h⟩)

end PEqualNP.Search.Helpers.Tree
