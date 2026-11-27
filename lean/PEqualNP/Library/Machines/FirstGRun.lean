import PEqualNP.Library.Machines.FirstG

/-!
# The run of the first-component machine over any alphabets

Helper module (proofs only, no statement may use it). Five loops and the run of `M` in between,
then the time bound: the output of `M` is at most the input plus `maxPush M` per step. The
result is that running a polynomial-time function on the first component of a pair is
polynomial time, for any encodings of the first component.
-/

namespace PEqualNP.Library.Machines.Gen

open Turing PEqualNP.Library.Machines

theorem iter_trans {σ : Type} (f : σ → Option σ) {a b : ℕ} {x y z : σ}
    (h₁ : (flip bind f)^[a] (some x) = some y) (h₂ : (flip bind f)^[b] (some y) = some z) :
    (flip bind f)^[b + a] (some x) = some z := by
  rw [Function.iterate_add_apply, h₁, h₂]

variable {M : FinTM2} {A B C : Type} [Inhabited A] [Inhabited B] [Inhabited C]
  (e₀ : A → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → B)

variable (v : M.σ) (S : ∀ k, List (M.Γ k)) (w : List C) (o : List (B ⊕ C))

/-! ### `l1`: split the input -/

theorem f1_inl (b : Option (A ⊕ B ⊕ C)) (a : A) (i : List (A ⊕ C)) (t : List A)
    (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inl a :: i) w t tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l1), (v, some (Sum.inl a)), fstk S i w (a :: t) tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I, fstk_set_TA, isA, getA, ofI]

theorem f1_inr (b : Option (A ⊕ B ⊕ C)) (a : C) (i : List (A ⊕ C)) (t : List A)
    (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inr a :: i) w t tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l1), (v, some (Sum.inr (Sum.inr a))),
        fstk S i (a :: w) t tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I, fstk_set_W, isA, getC, ofI]

theorem f1_nil (b : Option (A ⊕ B ⊕ C)) (t : List A) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l1), (v, b), fstk S [] w t tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l2), (v, none), fstk S [] w t tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_I]

theorem loop1 (tb : List B) : ∀ (i : List (A ⊕ C)) (w : List C) (t : List A)
    (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[i.length + 1]
        (some (⟨some (Sum.inr FL.l1), (v, b), fstk S i w t tb o⟩ : FCfg M A B C)) =
      some ⟨some (Sum.inr FL.l2), (v, none),
        fstk S [] ((i.filterMap Sum.getRight?).reverse ++ w)
          ((i.filterMap Sum.getLeft?).reverse ++ t) tb o⟩ := by
  intro i
  induction i with
  | nil => intro w t b; exact f1_nil e₀ e₁ v S w o b t tb
  | cons x i ih =>
    intro w t b
    rw [List.length_cons, Function.iterate_succ_apply]
    cases x with
    | inl a =>
      have e : flip bind (TM2.step (firstProg M C e₀ e₁))
          (some (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inl a :: i) w t tb o⟩ :
            FCfg M A B C)) =
          some ⟨some (Sum.inr FL.l1), (v, some (Sum.inl a)), fstk S i w (a :: t) tb o⟩ :=
        f1_inl e₀ e₁ v S w o b a i t tb
      rw [e, ih]; simp [List.filterMap_cons]
    | inr a =>
      have e : flip bind (TM2.step (firstProg M C e₀ e₁))
          (some (⟨some (Sum.inr FL.l1), (v, b), fstk S (Sum.inr a :: i) w t tb o⟩ :
            FCfg M A B C)) =
          some ⟨some (Sum.inr FL.l1), (v, some (Sum.inr (Sum.inr a))),
            fstk S i (a :: w) t tb o⟩ :=
        f1_inr e₀ e₁ v S w o b a i t tb
      rw [e, ih]; simp [List.filterMap_cons]

/-! ### `l2`: load the input stack of `M` -/

theorem f2_cons (b : Option (A ⊕ B ⊕ C)) (a : A) (t : List A) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w (a :: t) tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l2), (v, some (Sum.inl a)),
        fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TA, fstk_set_M, getA]

theorem f2_nil (b : Option (A ⊕ B ⊕ C)) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w [] tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inl M.main), (v, none), fstk S [] w [] tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TA]

theorem loop2 (tb : List B) : ∀ (t : List A) (S : ∀ k, List (M.Γ k))
    (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[t.length + 1]
        (some (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w t tb o⟩ : FCfg M A B C)) =
      some ⟨some (Sum.inl M.main), (v, none),
        fstk (Function.update S M.k₀ (t.reverse.map e₀ ++ S M.k₀)) [] w [] tb o⟩ := by
  intro t
  induction t with
  | nil =>
    intro S b
    have : Function.update S M.k₀ (([] : List A).reverse.map e₀ ++ S M.k₀) = S := by simp
    rw [this]
    exact f2_nil e₀ e₁ v S w o b tb
  | cons a t ih =>
    intro S b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M C e₀ e₁))
        (some (⟨some (Sum.inr FL.l2), (v, b), fstk S [] w (a :: t) tb o⟩ : FCfg M A B C)) =
        some ⟨some (Sum.inr FL.l2), (v, some (Sum.inl a)),
          fstk (Function.update S M.k₀ (e₀ a :: S M.k₀)) [] w t tb o⟩ :=
      f2_cons e₀ e₁ v S w o b a t tb
    rw [e, ih]; simp

/-! ### `l3`: the second component goes to the output -/

theorem f3_cons (b : Option (A ⊕ B ⊕ C)) (a : C) (w : List C) (ta : List A) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l3), (v, b), fstk S [] (a :: w) ta tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l3), (v, some (Sum.inr (Sum.inr a))),
        fstk S [] w ta tb (Sum.inr a :: o)⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_W, fstk_set_O, getC]

theorem f3_nil (b : Option (A ⊕ B ⊕ C)) (ta : List A) (tb : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l3), (v, b), fstk S [] [] ta tb o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l4), (v, none), fstk S [] [] ta tb o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_W]

theorem loop3 (ta : List A) (tb : List B) : ∀ (w : List C) (o : List (B ⊕ C))
    (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[w.length + 1]
        (some (⟨some (Sum.inr FL.l3), (v, b), fstk S [] w ta tb o⟩ : FCfg M A B C)) =
      some ⟨some (Sum.inr FL.l4), (v, none),
        fstk S [] [] ta tb (w.reverse.map Sum.inr ++ o)⟩ := by
  intro w
  induction w with
  | nil => intro o b; exact f3_nil e₀ e₁ v S o b ta tb
  | cons a w ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M C e₀ e₁))
        (some (⟨some (Sum.inr FL.l3), (v, b), fstk S [] (a :: w) ta tb o⟩ : FCfg M A B C)) =
        some ⟨some (Sum.inr FL.l3), (v, some (Sum.inr (Sum.inr a))),
          fstk S [] w ta tb (Sum.inr a :: o)⟩ :=
      f3_cons e₀ e₁ v S o b a w ta tb
    rw [e, ih]; simp

/-! ### `l4`: the output of `M` goes to the temporary stack -/

theorem f4_cons (b : Option (A ⊕ B ⊕ C)) (y : M.Γ M.k₁) (m : List (M.Γ M.k₁)) (ta : List A)
    (t : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ (y :: m)) [] [] ta t o⟩ :
          FCfg M A B C) =
      some ⟨some (Sum.inr FL.l4), (v, some (Sum.inr (Sum.inl (e₁ y)))),
        fstk (Function.update S M.k₁ m) [] [] ta (e₁ y :: t) o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TB, fstk_set_M, getB]

theorem f4_nil (b : Option (A ⊕ B ⊕ C)) (ta : List A) (t : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ []) [] [] ta t o⟩ :
          FCfg M A B C) =
      some ⟨some (Sum.inr FL.l5), (v, none),
        fstk (Function.update S M.k₁ []) [] [] ta t o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_M]

theorem loop4 (ta : List A) : ∀ (m : List (M.Γ M.k₁)) (t : List B) (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[m.length + 1]
        (some (⟨some (Sum.inr FL.l4), (v, b), fstk (Function.update S M.k₁ m) [] [] ta t o⟩ :
          FCfg M A B C)) =
      some ⟨some (Sum.inr FL.l5), (v, none),
        fstk (Function.update S M.k₁ []) [] [] ta (m.reverse.map e₁ ++ t) o⟩ := by
  intro m
  induction m with
  | nil => intro t b; exact f4_nil e₀ e₁ v S o b ta t
  | cons y m ih =>
    intro t b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M C e₀ e₁))
        (some (⟨some (Sum.inr FL.l4), (v, b),
          fstk (Function.update S M.k₁ (y :: m)) [] [] ta t o⟩ : FCfg M A B C)) =
        some ⟨some (Sum.inr FL.l4), (v, some (Sum.inr (Sum.inl (e₁ y)))),
          fstk (Function.update S M.k₁ m) [] [] ta (e₁ y :: t) o⟩ :=
      f4_cons e₀ e₁ v S o b y m ta t
    rw [e, ih]; simp

/-! ### `l5`: the first component goes to the output -/

theorem f5_cons (b : Option (A ⊕ B ⊕ C)) (a : B) (ta : List A) (t : List B) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] ta (a :: t) o⟩ : FCfg M A B C) =
      some ⟨some (Sum.inr FL.l5), (v, some (Sum.inr (Sum.inl a))),
        fstk S [] [] ta t (Sum.inl a :: o)⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TB, fstk_set_O, getB]

theorem f5_nil (b : Option (A ⊕ B ⊕ C)) (ta : List A) :
    TM2.step (firstProg M C e₀ e₁)
        (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] ta [] o⟩ : FCfg M A B C) =
      some ⟨none, (v, none), fstk S [] [] ta [] o⟩ := by
  simp [TM2.step, firstProg, TM2.stepAux, fstk_set_TB]

theorem loop5 (ta : List A) : ∀ (t : List B) (o : List (B ⊕ C)) (b : Option (A ⊕ B ⊕ C)),
    (flip bind (TM2.step (firstProg M C e₀ e₁)))^[t.length + 1]
        (some (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] ta t o⟩ : FCfg M A B C)) =
      some ⟨none, (v, none), fstk S [] [] ta [] (t.reverse.map Sum.inl ++ o)⟩ := by
  intro t
  induction t with
  | nil => intro o b; exact f5_nil e₀ e₁ v S o b ta
  | cons a t ih =>
    intro o b
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step (firstProg M C e₀ e₁))
        (some (⟨some (Sum.inr FL.l5), (v, b), fstk S [] [] ta (a :: t) o⟩ : FCfg M A B C)) =
        some ⟨some (Sum.inr FL.l5), (v, some (Sum.inr (Sum.inl a))),
          fstk S [] [] ta t (Sum.inl a :: o)⟩ :=
      f5_cons e₀ e₁ v S o b a ta t
    rw [e, ih]; simp

/-! ### The whole run -/

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem fstk_nil :
    (fstk (fun _ => []) [] [] [] [] [] : ∀ k, List (FstΓ M A B C k)) = fun _ => [] := by
  funext j; rcases j with j | (_ | _ | _ | _ | _) <;> rfl

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem fstk_nil_I (i : List (A ⊕ C)) :
    (fstk (fun _ => []) i [] [] [] [] : ∀ k, List (FstΓ M A B C k)) =
      Function.update (fun _ => [] : ∀ k, List (FstΓ M A B C k)) (Sum.inr FX.I) i :=
  (fstk_set_I (fun _ => []) [] [] [] [] [] i).symm.trans (by rw [fstk_nil])

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem fstk_nil_O (o : List (B ⊕ C)) :
    (fstk (fun _ => []) [] [] [] [] o : ∀ k, List (FstΓ M A B C k)) =
      Function.update (fun _ => [] : ∀ k, List (FstΓ M A B C k)) (Sum.inr FX.O) o :=
  (fstk_set_O (fun _ => []) [] [] [] [] [] o).symm.trans (by rw [fstk_nil])

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem embF_init (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C) (ta : List A)
    (tb : List B) (o : List (B ⊕ C)) (l : List (M.Γ M.k₀)) :
    embF b i w ta tb o (initList M l) =
      (⟨some (Sum.inl M.main), (M.initialState, b),
        fstk (Function.update (fun _ => []) M.k₀ l) i w ta tb o⟩ : FCfg M A B C) := by
  rw [initList_eq]; rfl

omit [Inhabited A] [Inhabited B] [Inhabited C] in
theorem embF_halt (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C) (ta : List A)
    (tb : List B) (o : List (B ⊕ C)) (m : List (M.Γ M.k₁)) :
    embF b i w ta tb o (haltList M m) =
      (⟨some (Sum.inr FL.l3), (M.initialState, b),
        fstk (Function.update (fun _ => []) M.k₁ m) i w ta tb o⟩ : FCfg M A B C) := by
  rw [haltList_eq]; rfl

theorem filterMap_const_none {γ δ : Type} (l : List γ) :
    l.filterMap (fun _ => (none : Option δ)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp

theorem gpair_left {A C : Type} (x : List A) (w : List C) :
    (gpair (x, w)).filterMap Sum.getLeft? = x := by
  have h1 : (Sum.getLeft? ∘ (Sum.inl : A → A ⊕ C) : A → Option A) = some := rfl
  have h2 : (Sum.getLeft? ∘ (Sum.inr : C → A ⊕ C) : C → Option A) = fun _ => none := rfl
  simp only [gpair, List.filterMap_append, List.filterMap_map, h1, h2,
    List.filterMap_some, filterMap_const_none, List.append_nil]

theorem gpair_right {A C : Type} (x : List A) (w : List C) :
    (gpair (x, w)).filterMap Sum.getRight? = w := by
  have h1 : (Sum.getRight? ∘ (Sum.inl : A → A ⊕ C) : A → Option C) = fun _ => none := rfl
  have h2 : (Sum.getRight? ∘ (Sum.inr : C → A ⊕ C) : C → Option C) = some := rfl
  simp only [gpair, List.filterMap_append, List.filterMap_map, h1, h2,
    List.filterMap_some, filterMap_const_none, List.nil_append]

theorem gpair_length {A C : Type} (x : List A) (w : List C) :
    (gpair (x, w)).length = x.length + w.length := by
  simp [gpair]

/-- The run of the composite on a pair. -/
theorem first_run [Fintype A] [Fintype B] [Fintype C] (x : List A) (w0 : List C)
    (m : List (M.Γ M.k₁)) (s : ℕ)
    (h : (flip bind (TM2.step M.m))^[s] (some (initList M (x.map e₀))) = some (haltList M m)) :
    ∃ n, n ≤ s + 2 * x.length + 2 * w0.length + 2 * m.length + 5 ∧
      (flip bind (TM2.step (firstProg M C e₀ e₁)))^[n]
          (some (initList (firstM M C e₀ e₁) (gpair (x, w0)))) =
        some (haltList (firstM M C e₀ e₁) (gpair (m.map e₁, w0))) := by
  have q1 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[(gpair (x, w0)).length + 1]
      (some (initList (firstM M C e₀ e₁) (gpair (x, w0)))) =
      some (⟨some (Sum.inr FL.l2), (M.initialState, none),
        fstk (fun _ => []) [] w0.reverse x.reverse [] []⟩ : FCfg M A B C) := by
    have := loop1 e₀ e₁ M.initialState (fun _ => []) [] [] (gpair (x, w0)) [] [] none
    rw [gpair_left, gpair_right, List.append_nil, List.append_nil, fstk_nil_I] at this
    exact (congrArg (fun c => (flip bind (TM2.step (firstProg M C e₀ e₁)))^[
      (gpair (x, w0)).length + 1] (some c))
      (initList_eq (firstM M C e₀ e₁) (gpair (x, w0)))).trans this
  have q2 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[x.reverse.length + 1]
      (some (⟨some (Sum.inr FL.l2), (M.initialState, none),
        fstk (fun _ => []) [] w0.reverse x.reverse [] []⟩ : FCfg M A B C)) =
      some (embF none [] w0.reverse [] [] [] (initList M (x.map e₀))) := by
    have := loop2 e₀ e₁ M.initialState w0.reverse ([] : List (B ⊕ C)) [] x.reverse
      (fun _ => []) none
    rw [embF_init]
    simpa using this
  have q3 := simulate (TM2.step M.m) (TM2.step (firstProg M C e₀ e₁))
    (embF none [] w0.reverse [] [] []) (stepF e₀ e₁ none [] w0.reverse [] [] []) s _ _ h
  rw [embF_halt] at q3
  have q4 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[w0.reverse.length + 1]
      (some (⟨some (Sum.inr FL.l3), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] w0.reverse [] [] []⟩ : FCfg M A B C)) =
      some (⟨some (Sum.inr FL.l4), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] [] (w0.map Sum.inr)⟩ :
          FCfg M A B C) := by
    have := loop3 e₀ e₁ M.initialState (Function.update (fun _ => []) M.k₁ m) ([] : List A)
      ([] : List B) w0.reverse [] none
    simpa using this
  have q5 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[m.length + 1]
      (some (⟨some (Sum.inr FL.l4), (M.initialState, none),
        fstk (Function.update (fun _ => []) M.k₁ m) [] [] [] [] (w0.map Sum.inr)⟩ :
          FCfg M A B C)) =
      some (⟨some (Sum.inr FL.l5), (M.initialState, none),
        fstk (fun _ => []) [] [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg M A B C) := by
    have := loop4 e₀ e₁ M.initialState (fun _ => []) (w0.map Sum.inr) ([] : List A) m [] none
    simpa using this
  have q6 : (flip bind (TM2.step (firstProg M C e₀ e₁)))^[(m.reverse.map e₁).length + 1]
      (some (⟨some (Sum.inr FL.l5), (M.initialState, none),
        fstk (fun _ => []) [] [] [] (m.reverse.map e₁) (w0.map Sum.inr)⟩ : FCfg M A B C)) =
      some (haltList (firstM M C e₀ e₁) (gpair (m.map e₁, w0))) := by
    have := loop5 e₀ e₁ M.initialState (fun _ => []) ([] : List A) (m.reverse.map e₁)
      (w0.map Sum.inr) none
    rw [fstk_nil_O] at this
    refine this.trans (Eq.trans ?_
      (congrArg some (haltList_eq (firstM M C e₀ e₁) (gpair (m.map e₁, w0)))).symm)
    simp [gpair]
    rfl
  refine ⟨_, ?_, iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ (iter_trans _ q1 q2) q3)
    q4) q5) q6⟩
  simp only [gpair_length, List.length_reverse, List.length_map]
  omega

/-- If `f` is polynomial-time computable for the encodings `ea`, `eb` then so is
`(a, w) ↦ (f a, w)` for the pair encodings. -/
theorem first_polyTime {α β A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    [Inhabited A] [Inhabited B] [Inhabited C]
    (ea : α → List A) (eb : β → List B) (f : α → β)
    (c : Turing.TM2ComputableInPolyTime ea eb f) :
    Nonempty (Turing.TM2ComputableInPolyTime
      (fun p : α × List C => gpair (ea p.1, p.2))
      (fun p : β × List C => gpair (eb p.1, p.2))
      (fun p : α × List C => (f p.1, p.2))) := by
  let e₀ : A → c.tm.Γ c.tm.k₀ := fun a => c.inputAlphabet.invFun a
  let e₁ : c.tm.Γ c.tm.k₁ → B := fun y => c.outputAlphabet y
  let T : Polynomial ℕ :=
    c.time + Polynomial.C 2 * (Polynomial.X + Polynomial.C (maxPush c.tm) * c.time) +
      Polynomial.C 2 * Polynomial.X + Polynomial.C 5
  have key : ∀ p : α × List C, ∃ n, n ≤ T.eval (gpair (ea p.1, p.2)).length ∧
      (flip bind (TM2.step (firstProg c.tm C e₀ e₁)))^[n]
          (some (initList (firstM c.tm C e₀ e₁) (gpair (ea p.1, p.2)))) =
        some (haltList (firstM c.tm C e₀ e₁) (gpair (eb (f p.1), p.2))) := by
    rintro ⟨a, w⟩
    have hs : ∃ s, s ≤ Polynomial.eval (ea a).length c.time ∧
        (flip bind (TM2.step c.tm.m))^[s] (some (initList c.tm ((ea a).map e₀))) =
          some (haltList c.tm (List.map c.outputAlphabet.invFun (eb (f a)))) :=
      ⟨(c.outputsFun a).steps, (c.outputsFun a).steps_le_m, (c.outputsFun a).evals_in_steps⟩
    obtain ⟨s, b1, h⟩ := hs
    obtain ⟨n, hn, hrun⟩ := first_run (C := C) e₀ e₁ (ea a) w _ s h
    have hm : (List.map c.outputAlphabet.invFun (eb (f a))).map e₁ = eb (f a) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (eb (f a))]
      exact List.map_congr_left fun y _ => c.outputAlphabet.right_inv y
    rw [hm] at hrun
    refine ⟨n, hn.trans ?_, hrun⟩
    have h' := h
    rw [haltList_eq, initList_eq] at h'
    have hlen := run_length c.tm c.tm.k₁ s _ _ h'
    simp only [Function.update_self, List.length_map] at hlen
    have hin : ((Function.update (fun _ => [] : ∀ k, List (c.tm.Γ k)) c.tm.k₀ ((ea a).map e₀))
        c.tm.k₁).length ≤ (ea a).length := by
      by_cases hk : c.tm.k₁ = c.tm.k₀
      · rw [hk, Function.update_self, List.length_map]
      · rw [Function.update_of_ne hk]; simp
    have b2 : Polynomial.eval (ea a).length c.time ≤
        Polynomial.eval ((ea a).length + w.length) c.time :=
      eval_mono _ (by omega)
    have hmul : maxPush c.tm * s ≤
        maxPush c.tm * Polynomial.eval ((ea a).length + w.length) c.time :=
      Nat.mul_le_mul_left _ (b1.trans b2)
    simp only [T, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, gpair_length, List.length_map]
    omega
  exact ⟨{
    tm := firstM c.tm C e₀ e₁
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := T
    outputsFun := fun p =>
      { steps := Classical.choose (key p)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step (firstProg c.tm C e₀ e₁)))^[
            Classical.choose (key p)] (some (initList (firstM c.tm C e₀ e₁) l)))
            (hm _ (gpair (ea p.1, p.2)))).trans ((Classical.choose_spec (key p)).2.trans
            (congrArg (fun l => some (haltList (firstM c.tm C e₀ e₁) l))
              (hm _ (gpair (eb (f p.1), p.2))).symm))
        steps_le_m := (Classical.choose_spec (key p)).1 } }⟩

end PEqualNP.Library.Machines.Gen
