import PEqualNP.Search.Helpers.BW.Defs

/-!
# Helpers: counting solutions of edge lists (L3a, L3b, L3c, L4)

Adding an edge not implied by `E` cuts the solutions of `E` by exactly `2 ^ t`; hence the
solutions of `E` are at most a `(2 ^ t) ^ rank E` fraction. A list of distinct edges between
different pigeons has length at most `4 * rank ^ 2`.
-/

namespace PEqualNP.Search.Helpers.BW

open Classical

variable {n t : ℕ}

/-- Solutions of `E` are constant along `EqvGen` paths of `E`. -/
theorem sat_eqvGen {E : List (Edge n)} {x : Half n t} (hx : Sat E x) {a b : Fin (n + 1)}
    (h : Relation.EqvGen (fun a b => (a, b) ∈ E) a b) : x a = x b := by
  induction h with
  | rel a b hab => exact hx (a, b) hab
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2

/-- Flip the bits `d` on every pigeon of the class `C`. -/
noncomputable def flipOn (C : Fin (n + 1) → Prop) (d : Fin t → Bool) (x : Half n t) : Half n t :=
  fun k => if C k then fun b => xor (x k b) (d b) else x k

theorem flipOn_flipOn (C : Fin (n + 1) → Prop) (d : Fin t → Bool) (x : Half n t) :
    flipOn C d (flipOn C d x) = x := by
  funext k b
  unfold flipOn
  by_cases hk : C k <;> simp [hk]

theorem sat_flipOn {E : List (Edge n)} (i : Fin (n + 1)) (d : Fin t → Bool) {x : Half n t}
    (hx : Sat E x) : Sat E (flipOn (Relation.EqvGen (fun a b => (a, b) ∈ E) i) d x) := by
  intro p hp
  have hr : Relation.EqvGen (fun a b => (a, b) ∈ E) p.1 p.2 := Relation.EqvGen.rel _ _ hp
  have hiff : Relation.EqvGen (fun a b => (a, b) ∈ E) i p.1 ↔
      Relation.EqvGen (fun a b => (a, b) ∈ E) i p.2 :=
    ⟨fun h => h.trans _ _ _ hr, fun h => h.trans _ _ _ (hr.symm _ _)⟩
  have hxp := hx p hp
  unfold flipOn
  by_cases h1 : Relation.EqvGen (fun a b => (a, b) ∈ E) i p.1
  · simp [h1, hiff.mp h1, hxp]
  · simp [h1, mt hiff.mpr h1, hxp]

/-- L3a: adding an edge not implied by `E` cuts the solutions by exactly `2 ^ t`. -/
theorem eqd_step (E : List (Edge n)) (i j : Fin (n + 1)) (h : ¬ Implied E (i, j)) :
    (Finset.univ.filter fun x : Half n t => Sat E x ∧ x i = x j).card * 2 ^ t =
      (Finset.univ.filter fun x : Half n t => Sat E x).card := by
  set C := Relation.EqvGen (fun a b => (a, b) ∈ E) i with hC
  have hi : C i := Relation.EqvGen.refl _
  have hj : ¬ C j := h
  have fi : ∀ (d : Fin t → Bool) (x : Half n t), flipOn C d x i = fun b => xor (x i b) (d b) :=
    fun d x => by simp [flipOn, hi]
  have fj : ∀ (d : Fin t → Bool) (x : Half n t), flipOn C d x j = x j :=
    fun d x => by simp [flipOn, hj]
  let e : {x : Half n t // Sat E x} ≃ {x : Half n t // Sat E x ∧ x i = x j} × (Fin t → Bool) :=
    { toFun := fun x =>
        (⟨flipOn C (fun b => xor (x.1 i b) (x.1 j b)) x.1,
          sat_flipOn i _ x.2, by funext b; rw [fi, fj]; simp⟩,
          fun b => xor (x.1 i b) (x.1 j b))
      invFun := fun yd => ⟨flipOn C yd.2 yd.1.1, sat_flipOn i _ yd.1.2.1⟩
      left_inv := fun x => by
        apply Subtype.ext
        exact flipOn_flipOn _ _ _
      right_inv := fun yd => by
        obtain ⟨⟨y, hy1, hy2⟩, d⟩ := yd
        have hd : (fun b => xor (flipOn C d y i b) (flipOn C d y j b)) = d := by
          funext b; rw [fi, fj, hy2]; dsimp only; cases d b <;> cases y j b <;> rfl
        simp only [hd, Prod.mk.injEq, and_true]
        apply Subtype.ext
        exact flipOn_flipOn _ _ _ }
  have h1 := Fintype.card_congr e
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Fintype.card_subtype, Fintype.card_subtype] at h1
  exact h1.symm

theorem sat_cons (e : Edge n) (E : List (Edge n)) (x : Half n t) :
    Sat (e :: E) x ↔ Sat E x ∧ x e.1 = x e.2 := by
  simp only [Sat, List.mem_cons, forall_eq_or_imp]
  exact And.comm

/-- L3b: the solutions of `E` are at most a `2 ^ (t * rank E)` fraction. -/
theorem eqd_rank (E : List (Edge n)) :
    (Finset.univ.filter fun x : Half n t => Sat E x).card * (2 ^ t) ^ rank E ≤
      Fintype.card (Half n t) := by
  induction E with
  | nil =>
    simp only [rank, pow_zero, mul_one]
    exact (Finset.card_le_univ _)
  | cons e E ih =>
    by_cases hI : Implied E e
    · have hf : (Finset.univ.filter fun x : Half n t => Sat (e :: E) x) =
          Finset.univ.filter fun x : Half n t => Sat E x := by
        apply Finset.filter_congr
        intro x _
        rw [sat_cons]
        exact ⟨fun h => h.1, fun h => ⟨h, sat_eqvGen h hI⟩⟩
      simp only [rank, hI, ite_true, add_zero, hf]
      exact ih
    · have hs := eqd_step (t := t) E e.1 e.2 hI
      have hf : (Finset.univ.filter fun x : Half n t => Sat (e :: E) x) =
          Finset.univ.filter fun x : Half n t => Sat E x ∧ x e.1 = x e.2 := by
        apply Finset.filter_congr
        intro x _
        exact sat_cons e E x
      simp only [rank, hI, ite_false, hf]
      calc _ = (Finset.univ.filter fun x : Half n t => Sat E x ∧ x e.1 = x e.2).card * 2 ^ t *
            (2 ^ t) ^ rank E := by ring
        _ = _ := by rw [hs]
        _ ≤ _ := ih

/-- L3c: two different pigeons collide on a `2 ^ -t` fraction. -/
theorem eqd_pair (i j : Fin (n + 1)) (h : i ≠ j) :
    (Finset.univ.filter fun y : Half n t => y i = y j).card * 2 ^ t =
      Fintype.card (Half n t) := by
  have hI : ¬ Implied ([] : List (Edge n)) (i, j) := by
    intro hI
    have : ∀ a b, Relation.EqvGen (fun a b => (a, b) ∈ ([] : List (Edge n))) a b → a = b := by
      intro a b hab
      induction hab with
      | rel a b hab => simp at hab
      | refl => rfl
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
    exact h (this _ _ hI)
  have hs := eqd_step (t := t) [] i j hI
  simp only [Sat, List.not_mem_nil, false_imp_iff, implies_true, true_and,
    Finset.filter_true] at hs
  rw [hs, Finset.card_univ]

/-- The endpoints of the edges of `E`. -/
def vt : List (Edge n) → Finset (Fin (n + 1))
  | [] => ∅
  | e :: E => insert e.1 (insert e.2 (vt E))

theorem mem_vt_of_mem {E : List (Edge n)} {p : Edge n} (hp : p ∈ E) :
    p.1 ∈ vt E ∧ p.2 ∈ vt E := by
  induction E with
  | nil => simp at hp
  | cons e E ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · simp [vt]
    · obtain ⟨h1, h2⟩ := ih hp
      simp [vt, h1, h2]

theorem eqvGen_vt {E : List (Edge n)} {a b : Fin (n + 1)}
    (h : Relation.EqvGen (fun a b => (a, b) ∈ E) a b) : a = b ∨ (a ∈ vt E ∧ b ∈ vt E) := by
  induction h with
  | rel a b hab => exact Or.inr (mem_vt_of_mem hab)
  | refl => exact Or.inl rfl
  | symm _ _ _ ih => rcases ih with h | h; exact Or.inl h.symm; exact Or.inr ⟨h.2, h.1⟩
  | trans _ _ _ _ _ ih1 ih2 =>
    rcases ih1 with h1 | h1 <;> rcases ih2 with h2 | h2
    · exact Or.inl (h1.trans h2)
    · subst h1; exact Or.inr h2
    · subst h2; exact Or.inr h1
    · exact Or.inr ⟨h1.1, h2.2⟩

theorem card_vt_le (E : List (Edge n)) (h : ∀ p ∈ E, p.1 ≠ p.2) :
    (vt E).card ≤ 2 * rank E := by
  induction E with
  | nil => simp [vt, rank]
  | cons e E ih =>
    have ih' := ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
    by_cases hI : Implied E e
    · rcases eqvGen_vt hI with he | ⟨h1, h2⟩
      · exact absurd he (h e (List.mem_cons_self ..))
      · simp only [vt, rank, hI, ite_true, add_zero, Finset.insert_eq_of_mem h2,
          Finset.insert_eq_of_mem h1]
        exact ih'
    · simp only [vt, rank, hI, ite_false]
      calc (insert e.1 (insert e.2 (vt E))).card ≤ (insert e.2 (vt E)).card + 1 :=
            Finset.card_insert_le _ _
        _ ≤ (vt E).card + 1 + 1 := by gcongr; exact Finset.card_insert_le _ _
        _ ≤ 2 * (rank E + 1) := by omega

/-- L4: a list of distinct edges between different pigeons has length at most
`4 * rank ^ 2`. -/
theorem rank_bound (E : List (Edge n)) (hE : E.Nodup) (h : ∀ p ∈ E, p.1 ≠ p.2) :
    E.length ≤ 4 * rank E ^ 2 := by
  have hsub : E.toFinset ⊆ vt E ×ˢ vt E := by
    intro p hp
    rw [List.mem_toFinset] at hp
    obtain ⟨h1, h2⟩ := mem_vt_of_mem hp
    exact Finset.mem_product.mpr ⟨h1, h2⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_product, List.toFinset_card_of_nodup hE] at hc
  have hv := card_vt_le E h
  calc E.length ≤ (vt E).card * (vt E).card := hc
    _ ≤ (2 * rank E) * (2 * rank E) := Nat.mul_le_mul hv hv
    _ = 4 * rank E ^ 2 := by ring

end PEqualNP.Search.Helpers.BW
