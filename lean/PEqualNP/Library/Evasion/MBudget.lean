import PEqualNP.Library.Evasion.RungPlan
import PEqualNP.Library.Machines.Run

/-!
# M4 of note 209: a verifier run under a step budget

`budget : StmtBudget`. Given a decider of `S` on pairs, the set `B` holds `(z, w)` when `z` has a
`false`, and the decider, run on `(body z, w)`, reaches its accepting halt within `lead z` steps.

Part 1 (pure): soundness and completeness of that definition, from the determinism of `step`.
Part 2 (machine): a wrapper that strips the leading `true`s of the input onto a budget stack,
then runs the decider, popping one budget symbol per simulated step, and empties every stack at
the end.
-/

namespace PEqualNP.Library.Evasion

open Turing PEqualNP.Library.Machines

namespace Budget

/-! ## Part 1: the definition of `B` -/

/-- After a halting configuration the run is over. -/
theorem iter_halt (tm : FinTM2) (h : tm.Cfg) (hh : h.l = none) (j : ℕ) :
    (flip bind tm.step)^[j + 1] (some h) = none := by
  rw [Function.iterate_succ_apply]
  have : flip bind tm.step (some h) = none := by
    obtain ⟨l, v, S⟩ := h
    simp only at hh
    subst hh
    rfl
  rw [this, iterate_none]

/-- Two halting configurations reached from the same configuration are reached at the same time
and are equal. -/
theorem halt_unique (tm : FinTM2) (x h1 h2 : tm.Cfg) (a b : ℕ) (h1l : h1.l = none)
    (h2l : h2.l = none) (ha : (flip bind tm.step)^[a] (some x) = some h1)
    (hb : (flip bind tm.step)^[b] (some x) = some h2) : a = b ∧ h1 = h2 := by
  rcases lt_trichotomy a b with hab | hab | hab
  · obtain ⟨j, rfl⟩ : ∃ j, b = (j + 1) + a := ⟨b - a - 1, by omega⟩
    rw [Function.iterate_add_apply, ha, iter_halt tm h1 h1l] at hb
    exact absurd hb (by simp)
  · subst hab; rw [ha] at hb; exact ⟨rfl, Option.some.inj hb⟩
  · obtain ⟨j, rfl⟩ : ∃ j, a = (j + 1) + b := ⟨a - b - 1, by omega⟩
    rw [Function.iterate_add_apply, hb, iter_halt tm h2 h2l] at ha
    exact absurd ha (by simp)

variable {f : List Bool × List Bool → Bool}
  (c : TM2ComputableInTime encodePair Computability.encodeBool f)

/-- The initial configuration of the decider on a pair. -/
def ini (p : List Bool × List Bool) : c.tm.Cfg :=
  initList c.tm ((encodePair p).map c.inputAlphabet.invFun)

/-- The accepting halt of the decider. -/
def acc : c.tm.Cfg := haltList c.tm ([true].map c.outputAlphabet.invFun)

/-- The budgeted set. -/
def inB (p : List Bool × List Bool) : Prop :=
  false ∈ p.1 ∧ ∃ i ≤ lead p.1, (flip bind c.tm.step)^[i] (some (ini c (body p.1, p.2))) =
    some (acc c)

theorem haltList_inj (tm : FinTM2) (l l' : List (tm.Γ tm.k₁))
    (h : haltList tm l = haltList tm l') : l = l' := by
  have := congrArg (fun x => x.stk tm.k₁) h
  simpa [haltList] using this

theorem inB_sound (k : ℕ) (s w : List Bool)
    (h : inB c (List.replicate k true ++ false :: s, w)) : f (s, w) = true := by
  obtain ⟨-, i, -, hi⟩ := h
  rw [body_pad] at hi
  obtain ⟨⟨m, hm⟩, -⟩ := c.outputsFun (s, w)
  have e := halt_unique c.tm _ _ _ _ _ rfl rfl hi hm
  have e2 := haltList_inj c.tm _ _ e.2
  simp only [Computability.encodeBool, pure, List.map_cons, List.map_nil, List.cons.injEq,
    and_true] at e2
  exact (c.outputAlphabet.symm.injective e2).symm

theorem inB_complete (t : ℕ → ℕ) (ht : ∀ n, c.time n ≤ t n) (k : ℕ) (s w : List Bool)
    (hk : t (s.length + w.length) ≤ k) (hf : f (s, w) = true) :
    inB c (List.replicate k true ++ false :: s, w) := by
  refine ⟨by simp, ?_⟩
  rw [lead_pad, body_pad]
  obtain ⟨⟨m, hm⟩, hmT⟩ := c.outputsFun (s, w)
  refine ⟨m, ?_, ?_⟩
  · have h1 := ht ((encodePair (s, w)).length)
    simp only [encodePair, List.length_append, List.length_map] at h1 hmT
    change m ≤ _ at hmT
    omega
  · exact hm.trans (by rw [hf]; rfl)

/-! ## Part 2: the wrapper machine -/

section Machine

attribute [local instance] FinTM2.kFin

variable (M : FinTM2)

/-- Stacks of the wrapper: those of `M` (`some k`) and the budget (`none`). -/
abbrev BΓ : Option M.K → Type
  | none => Unit
  | some k => M.Γ k

/-- Labels: those of `M`, the strip loop (`inr true`) and the cleanup loop (`inr false`). -/
abbrev BΛ : Type := M.Λ ⊕ Bool

/-- States: that of `M`, the answer, and a flag. -/
abbrev Bσ : Type := M.σ × Bool × Bool

abbrev BStmt : Type := TM2.Stmt (BΓ M) (BΛ M) (Bσ M)

variable {M}

variable (φ : M.Γ M.k₀ ≃ Bool ⊕ Bool) (ψ : M.Γ M.k₁ ≃ Bool)

/-- A statement of `M` inside the wrapper; a halt of `M` reads the answer and goes to cleanup. -/
def trB : TM2.Stmt M.Γ M.Λ M.σ → BStmt M
  | .push k f q => .push (some k) (fun s => f s.1) (trB q)
  | .peek k f q => .peek (some k) (fun s o => (f s.1 o, s.2)) (trB q)
  | .pop k f q => .pop (some k) (fun s o => (f s.1 o, s.2)) (trB q)
  | .load a q => .load (fun s => (a s.1, s.2)) (trB q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (trB q₁) (trB q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .peek (some M.k₁)
      (fun s o => (s.1, decide ((o : Option (M.Γ M.k₁)).map ψ = some true), false))
      (.goto fun _ => Sum.inr false)

/-- Pop every stack of the list once, raising the flag if a symbol was there. -/
def popAll : List (Option M.K) → BStmt M → BStmt M
  | [], q => q
  | k :: ks, q => .pop k (fun s o => (s.1, s.2.1, s.2.2 || o.isSome)) (popAll ks q)

/-- The list of all stacks. -/
noncomputable def allK : List (Option M.K) :=
  haveI := M.kFin
  (Finset.univ : Finset (Option M.K)).toList

/-- The program of the wrapper. -/
noncomputable def progB : BΛ M → BStmt M
  | Sum.inl l =>
      .pop none (fun s o => (s.1, false, o.isSome))
        (.branch (fun s => s.2.2) (.load (fun s => (s.1, false, false)) (trB ψ (M.m l)))
          (.goto fun _ => Sum.inr false))
  | Sum.inr true =>
      .pop (some M.k₀)
        (fun s o => (s.1, decide ((o : Option (M.Γ M.k₀)).map φ = some (Sum.inl true)),
          decide ((o : Option (M.Γ M.k₀)).map φ = some (Sum.inl false))))
        (.branch (fun s => s.2.1) (.push none (fun _ => ()) (.goto fun _ => Sum.inr true))
          (.branch (fun s => s.2.2)
            (.load (fun _ => (M.initialState, false, false)) (.goto fun _ => Sum.inl M.main))
            (.load (fun s => (s.1, false, false)) (.goto fun _ => Sum.inr false))))
  | Sum.inr false =>
      .load (fun s => (s.1, s.2.1, false))
        (popAll allK
          (.branch (fun s => s.2.2) (.goto fun _ => Sum.inr false)
            (.push (some M.k₁) (fun s => ψ.symm s.2.1)
              (.load (fun _ => (M.initialState, false, false)) .halt))))

/-- The wrapper. -/
noncomputable def wrapB : FinTM2 :=
  haveI := M.kFin
  haveI := M.ΛFin
  haveI := M.σFin
  { K := Option M.K
    k₀ := some M.k₀
    k₁ := some M.k₁
    Γ := BΓ M
    Λ := BΛ M
    main := Sum.inr true
    σ := Bσ M
    initialState := (M.initialState, false, false)
    Γk₀Fin := M.Γk₀Fin
    m := progB φ ψ }

/-- The stacks of `M` and a budget of `b` symbols. -/
def embS (S : ∀ k, List (M.Γ k)) (b : ℕ) : ∀ k : Option M.K, List (BΓ M k)
  | none => List.replicate b ()
  | some k => S k

theorem embS_update (S : ∀ k, List (M.Γ k)) (b : ℕ) (k : M.K) (x : List (M.Γ k)) :
    embS (Function.update S k x) b = Function.update (embS S b) (some k) x := by
  funext k'
  cases k' with
  | none => simp [embS]
  | some k' =>
    by_cases h : k' = k
    · subst h; simp [embS]
    · rw [Function.update_of_ne (by simpa using h)]
      simp [embS, Function.update_of_ne h]

theorem embS_budget (S : ∀ k, List (M.Γ k)) (b b' : ℕ) :
    Function.update (embS S b) none (List.replicate b' ()) = embS S b' := by
  funext k'
  cases k' with
  | none => simp [embS]
  | some k' => simp [embS]

/-- A configuration of `M` inside the wrapper with budget `b`; a halted one sits at cleanup. -/
def embR (c : TM2.Cfg M.Γ M.Λ M.σ) (b : ℕ) : TM2.Cfg (BΓ M) (BΛ M) (Bσ M) :=
  match c.l with
  | some l => ⟨some (Sum.inl l), (c.var, false, false), embS c.stk b⟩
  | none => ⟨some (Sum.inr false),
      (c.var, decide ((c.stk M.k₁).head?.map ψ = some true), false), embS c.stk b⟩

theorem simB (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) (b : ℕ) :
    TM2.stepAux (trB ψ q) ((v, false, false) : Bσ M) (embS S b) =
      embR ψ (TM2.stepAux q v S) b := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [trB, TM2.stepAux]
    rw [← ih, embS_update]; rfl
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    simp only [trB, TM2.stepAux]
    rw [← ih, embS_update]; rfl
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trB, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem stepB (l : M.Λ) (v : M.σ) (S : ∀ k, List (M.Γ k)) (b : ℕ) :
    TM2.step (progB φ ψ) ⟨some (Sum.inl l), ((v, false, false) : Bσ M), embS S (b + 1)⟩ =
      some (embR ψ (TM2.stepAux (M.m l) v S) b) := by
  simp only [TM2.step, progB, TM2.stepAux, Option.some.injEq]
  have e1 : (embS S (b + 1) none).head?.isSome = true := by simp [embS, List.replicate_succ]
  have e2 : Function.update (embS S (b + 1)) none (embS S (b + 1) none).tail = embS S b := by
    rw [← embS_budget S (b + 1) b]; congr 1
  rw [e1, e2]
  exact simB ψ _ v S b

theorem stepB0 (l : M.Λ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.step (progB φ ψ) ⟨some (Sum.inl l), ((v, false, false) : Bσ M), embS S 0⟩ =
      some ⟨some (Sum.inr false), (v, false, false), embS S 0⟩ := by
  simp only [TM2.step, progB, TM2.stepAux, Option.some.injEq]
  have e1 : (embS S 0 none).head?.isSome = false := by simp [embS]
  have e2 : Function.update (embS S 0) none (embS S 0 none).tail = embS S 0 :=
    embS_budget S 0 0
  rw [e1, e2]
  rfl

theorem simRun (i : ℕ) : ∀ (b : ℕ) (c c' : M.Cfg), c.l.isSome → i ≤ b →
    (flip bind M.step)^[i] (some c) = some c' →
    (flip bind (TM2.step (progB φ ψ)))^[i] (some (embR ψ c b)) = some (embR ψ c' (b - i)) := by
  induction i with
  | zero =>
    intro b c c' _ _ h
    cases Option.some.inj h
    simp
  | succ i ih =>
    intro b c c' hc hb h
    obtain ⟨l, v, S⟩ := c
    cases l with
    | none => simp at hc
    | some l =>
      obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      rw [Function.iterate_succ_apply] at h ⊢
      have e1 : flip bind M.step (some ⟨some l, v, S⟩) =
          some (TM2.stepAux (M.m l) v S) := rfl
      have e2 : flip bind (TM2.step (progB φ ψ)) (some (embR ψ ⟨some l, v, S⟩ (b + 1))) =
          some (embR ψ (TM2.stepAux (M.m l) v S) b) := stepB φ ψ l v S b
      rw [e1] at h
      rw [e2]
      have hb' : b + 1 - (i + 1) = b - i := by omega
      rw [hb']
      cases hc1 : (TM2.stepAux (M.m l) v S).l with
      | none =>
        cases i with
        | zero =>
          cases Option.some.inj h
          rfl
        | succ j =>
          exact absurd ((iter_halt M (TM2.stepAux (M.m l) v S) hc1 j).symm.trans h) (by simp)
      | some l' =>
        exact ih b _ c' (by simp [hc1]) (by omega) h

theorem any_congr' {α : Type} (l : List α) (f g : α → Bool) (h : ∀ x ∈ l, f x = g x) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem popAll_run (q : BStmt M) (v : M.σ) (a : Bool) (ks : List (Option M.K)) (hks : ks.Nodup) :
    ∀ (x : Bool) (S' : ∀ k, List (BΓ M k)),
    TM2.stepAux (popAll ks q) ((v, a, x) : Bσ M) S' =
      TM2.stepAux q (v, a, x || ks.any (fun k => (S' k).head?.isSome))
        (fun k => if k ∈ ks then (S' k).tail else S' k) := by
  induction ks with
  | nil => intro x S'; simp [popAll]
  | cons k ks ih =>
    intro x S'
    rw [List.nodup_cons] at hks
    simp only [popAll, TM2.stepAux]
    rw [ih hks.2]
    have hne : ∀ k' ∈ ks, k' ≠ k := fun k' hk' h => hks.1 (h ▸ hk')
    have e1 : ks.any (fun k' => (Function.update S' k (S' k).tail k').head?.isSome) =
        ks.any (fun k' => (S' k').head?.isSome) :=
      any_congr' _ _ _ (fun k' hk' => by rw [Function.update_of_ne (hne k' hk')])
    rw [e1, List.any_cons, Bool.or_assoc]
    congr 1
    funext k'
    by_cases h : k' = k
    · subst h
      simp [hks.1]
    · simp [h]

theorem mem_allK (k : Option M.K) : k ∈ (allK : List (Option M.K)) := by
  simp [allK]

theorem nodup_allK : (allK : List (Option M.K)).Nodup := by
  simp only [allK]; exact Finset.nodup_toList _

theorem flip_bind_some {σ : Type} (f : σ → Option σ) (c : σ) :
    flip bind f (some c) = f c := rfl

theorem iter_succ_some {σ : Type} (f : σ → Option σ) (m : ℕ) (c : σ) :
    (flip bind f)^[m + 1] (some c) = (flip bind f)^[m] (f c) := by
  rw [Function.iterate_succ_apply]; rfl

theorem cleanStep (S' : ∀ k, List (BΓ M k)) (v : M.σ) (a x : Bool) :
    TM2.step (progB φ ψ) ⟨some (Sum.inr false), ((v, a, x) : Bσ M), S'⟩ =
      some (if allK.any (fun k => (S' k).head?.isSome) then
          ⟨some (Sum.inr false), (v, a, true), fun k => (S' k).tail⟩
        else ⟨none, (M.initialState, false, false),
          Function.update (fun k => (S' k).tail) (some M.k₁)
            (ψ.symm a :: (S' (some M.k₁)).tail)⟩) := by
  change some (TM2.stepAux (popAll allK _) ((v, a, false) : Bσ M) S') = _
  rw [popAll_run _ _ _ _ nodup_allK]
  simp only [mem_allK, ↓reduceIte, Bool.false_or]
  cases allK.any (fun k => (S' k).head?.isSome) <;> rfl

theorem cleanRun (n : ℕ) : ∀ (S' : ∀ k, List (BΓ M k)) (v : M.σ) (a x : Bool),
    (∑ k, (S' k).length) ≤ n →
    ∃ m ≤ n + 1, (flip bind (TM2.step (progB φ ψ)))^[m]
      (some ⟨some (Sum.inr false), ((v, a, x) : Bσ M), S'⟩) =
      some ⟨none, (M.initialState, false, false),
        Function.update (fun _ => []) (some M.k₁) [ψ.symm a]⟩ := by
  induction n with
  | zero =>
    intro S' v a x hS
    have h0 : ∀ k, S' k = [] := by
      intro k
      have := Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp hS) k (Finset.mem_univ k)
      exact List.length_eq_zero_iff.mp this
    refine ⟨1, le_rfl, ?_⟩
    rw [iter_succ_some, cleanStep]
    have e : allK.any (fun k => (S' k).head?.isSome) = false := by simp [h0]
    rw [e]
    simp only [Bool.false_eq_true, ↓reduceIte, Function.iterate_zero, id, h0, List.tail_nil]
  | succ n ih =>
    intro S' v a x hS
    by_cases e : allK.any (fun k => (S' k).head?.isSome) = true
    · have hlt : (∑ k, (S' k).tail.length) < ∑ k, (S' k).length := by
        apply Finset.sum_lt_sum
        · intro k _; simp
        · obtain ⟨k, -, hk⟩ := List.any_eq_true.mp e
          refine ⟨k, Finset.mem_univ k, ?_⟩
          cases h : S' k with
          | nil => simp [h] at hk
          | cons y ys => simp
      obtain ⟨m, hm, hrun⟩ := ih (fun k => (S' k).tail) v a true (by omega)
      refine ⟨m + 1, by omega, ?_⟩
      rw [iter_succ_some, cleanStep]; simp only [e, ↓reduceIte]
      exact hrun
    · have h0 : ∀ k, S' k = [] := by
        intro k
        have : ¬ (S' k).head?.isSome = true := by
          intro hk; exact e (List.any_eq_true.mpr ⟨k, mem_allK k, hk⟩)
        cases h : S' k with
        | nil => rfl
        | cons y ys => simp [h] at this
      refine ⟨1, by omega, ?_⟩
      rw [iter_succ_some, cleanStep, Bool.eq_false_iff.mpr e]
      simp only [Bool.false_eq_true, ↓reduceIte, Function.iterate_zero, id, h0, List.tail_nil]

/-- The initial stacks of `M` on input `x`. -/
def upd0 (x : List (M.Γ M.k₀)) : ∀ k, List (M.Γ k) := Function.update (fun _ => []) M.k₀ x

theorem embS_upd0 (x : List (M.Γ M.k₀)) :
    embS (upd0 x) 0 =
      Function.update (fun _ => [] : ∀ k : Option M.K, List (BΓ M k)) (some M.k₀) x := by
  unfold upd0
  rw [embS_update]
  congr 1
  funext k
  cases k <;> rfl

theorem upd0_k₀ (x : List (M.Γ M.k₀)) : embS (upd0 x) b (some M.k₀) = x := by
  simp [embS, upd0]

theorem upd0_pop (y : M.Γ M.k₀) (x : List (M.Γ M.k₀)) (b : ℕ) :
    Function.update (embS (upd0 (y :: x)) b) (some M.k₀) (embS (upd0 (y :: x)) b (some M.k₀)).tail
      = embS (upd0 x) b := by
  rw [upd0_k₀, List.tail_cons, ← embS_update]
  simp [upd0, Function.update_idem]

theorem upd0_pop2 (y : M.Γ M.k₀) (x : List (M.Γ M.k₀)) (b : ℕ) :
    Function.update (embS (upd0 (y :: x)) b) (some M.k₀) x = embS (upd0 x) b := by
  rw [← embS_update]
  simp [upd0, Function.update_idem]

theorem embS_none (S : ∀ k, List (M.Γ k)) (b : ℕ) : embS S b none = List.replicate b () := rfl

theorem embS_push (S : ∀ k, List (M.Γ k)) (b : ℕ) :
    Function.update (embS S b) none (() :: List.replicate b ()) = embS S (b + 1) := by
  rw [← embS_budget S b (b + 1)]
  rfl

theorem strip1 (st : Bσ M) (x : List (M.Γ M.k₀)) (b : ℕ) :
    TM2.step (progB φ ψ) ⟨some (Sum.inr true), st, embS (upd0 (φ.symm (Sum.inl true) :: x)) b⟩ =
      some ⟨some (Sum.inr true), (st.1, true, false), embS (upd0 x) (b + 1)⟩ := by
  change some (TM2.stepAux (progB φ ψ (Sum.inr true)) st _) = _
  simp only [progB, TM2.stepAux]
  simp [upd0_k₀, upd0_pop2, embS_none]
  exact embS_push _ _

theorem strip0 (st : Bσ M) (x : List (M.Γ M.k₀)) (b : ℕ) :
    TM2.step (progB φ ψ) ⟨some (Sum.inr true), st, embS (upd0 (φ.symm (Sum.inl false) :: x)) b⟩ =
      some (embR ψ (initList M x) b) := by
  change some (TM2.stepAux (progB φ ψ (Sum.inr true)) st _) = _
  simp only [progB, TM2.stepAux]
  simp [upd0_k₀, upd0_pop2]
  rw [initList_eq]
  rfl

theorem stripR (st : Bσ M) (y : Bool) (x : List (M.Γ M.k₀)) (b : ℕ) :
    TM2.step (progB φ ψ) ⟨some (Sum.inr true), st, embS (upd0 (φ.symm (Sum.inr y) :: x)) b⟩ =
      some ⟨some (Sum.inr false), (st.1, false, false), embS (upd0 x) b⟩ := by
  change some (TM2.stepAux (progB φ ψ (Sum.inr true)) st _) = _
  simp only [progB, TM2.stepAux]
  simp [upd0_k₀, upd0_pop2]

theorem stripE (st : Bσ M) (b : ℕ) :
    TM2.step (progB φ ψ) ⟨some (Sum.inr true), st, embS (upd0 []) b⟩ =
      some ⟨some (Sum.inr false), (st.1, false, false), embS (upd0 []) b⟩ := by
  change some (TM2.stepAux (progB φ ψ (Sum.inr true)) st _) = _
  simp only [progB, TM2.stepAux]
  simp [upd0_k₀]

theorem stripRun (x : List (M.Γ M.k₀)) (j : ℕ) : ∀ (st : Bσ M) (b : ℕ), ∃ st' : Bσ M,
    (flip bind (TM2.step (progB φ ψ)))^[j]
      (some ⟨some (Sum.inr true), st,
        embS (upd0 (List.replicate j (φ.symm (Sum.inl true)) ++ x)) b⟩) =
      some ⟨some (Sum.inr true), st', embS (upd0 x) (b + j)⟩ := by
  induction j with
  | zero => intro st b; exact ⟨st, rfl⟩
  | succ j ih =>
    intro st b
    obtain ⟨st', h⟩ := ih (st.1, true, false) (b + 1)
    refine ⟨st', ?_⟩
    rw [iter_succ_some, List.replicate_succ, List.cons_append, strip1]
    rw [h]
    congr 3
    omega

theorem sum_embS (S : ∀ k, List (M.Γ k)) (b : ℕ) :
    (∑ k, (embS S b k).length) = b + ∑ k, (S k).length := by
  rw [Fintype.sum_option]
  simp [embS]

theorem sum_upd {k₀ : M.K} (x : List (M.Γ k₀)) :
    (∑ k, (Function.update (fun _ => []) k₀ x k : List (M.Γ k)).length) = x.length := by
  rw [Finset.sum_eq_single k₀]
  · simp
  · intro k _ hk; simp [Function.update_of_ne hk]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem iter_prefix {σ : Type} (g : σ → Option σ) (x y : σ) (j m : ℕ) (hj : j ≤ m)
    (h : (flip bind g)^[m] (some x) = some y) : ∃ z, (flip bind g)^[j] (some x) = some z := by
  obtain ⟨d, rfl⟩ : ∃ d, m = d + j := ⟨m - j, by omega⟩
  rw [Function.iterate_add_apply] at h
  cases e : (flip bind g)^[j] (some x) with
  | none => rw [e, iterate_none] at h; exact absurd h (by simp)
  | some z => exact ⟨z, rfl⟩

theorem runSim (inp : List (M.Γ M.k₀)) (j m0 : ℕ) (ans : Bool)
    (hm : (flip bind M.step)^[m0] (some (initList M inp)) = some (haltList M [ψ.symm ans])) :
    ∃ m ≤ (Fintype.card M.K * maxPush M + 2) * j + inp.length + 3,
      (flip bind (TM2.step (progB φ ψ)))^[m] (some (embR ψ (initList M inp) j)) =
        some ⟨none, (M.initialState, false, false),
          Function.update (fun _ => []) (some M.k₁) [ψ.symm (decide (m0 ≤ j) && ans)]⟩ := by
  have hi : (initList M inp).l.isSome = true := rfl
  by_cases h : m0 ≤ j
  · have h1 := simRun φ ψ m0 j _ _ hi h hm
    have e : embR ψ (haltList M [ψ.symm ans]) (j - m0) =
        ⟨some (Sum.inr false), (M.initialState, ans, false),
          embS (Function.update (fun _ => []) M.k₁ [ψ.symm ans]) (j - m0)⟩ := by
      rw [haltList_eq]
      simp [embR]
    rw [e] at h1
    obtain ⟨m', hm', h2⟩ := cleanRun φ ψ (j - m0 + 1)
      (embS (Function.update (fun _ => []) M.k₁ [ψ.symm ans]) (j - m0)) M.initialState ans false
      (by rw [sum_embS, sum_upd]; rfl)
    have hj : 2 * j ≤ (Fintype.card M.K * maxPush M + 2) * j := Nat.mul_le_mul_right _ (by omega)
    refine ⟨m' + m0, by omega, ?_⟩
    rw [Function.iterate_add_apply, h1, h2]
    simp [h]
  · push Not at h
    obtain ⟨cj, hcj⟩ := iter_prefix _ _ _ j m0 h.le hm
    obtain ⟨l, v, S⟩ := cj
    cases l with
    | none =>
      obtain ⟨d, rfl⟩ : ∃ d, m0 = (d + 1) + j := ⟨m0 - j - 1, by omega⟩
      rw [Function.iterate_add_apply, hcj] at hm
      exact absurd ((iter_halt M _ rfl d).symm.trans hm) (by simp)
    | some l =>
      have h1 := simRun φ ψ j j _ _ hi le_rfl hcj
      rw [Nat.sub_self] at h1
      have hS : (∑ k, (S k).length) ≤ inp.length + Fintype.card M.K * maxPush M * j := by
        have hl : ∀ k, (S k).length ≤ ((initList M inp).stk k).length + maxPush M * j :=
          fun k => run_length M k j _ _ hcj
        calc (∑ k, (S k).length) ≤ ∑ k, (((initList M inp).stk k).length + maxPush M * j) :=
              Finset.sum_le_sum (fun k _ => hl k)
          _ = inp.length + Fintype.card M.K * maxPush M * j := by
              rw [Finset.sum_add_distrib, initList_eq]
              simp only [sum_upd, Finset.sum_const, Finset.card_univ, smul_eq_mul]
              ring
      obtain ⟨m', hm', h2⟩ := cleanRun φ ψ (inp.length + Fintype.card M.K * maxPush M * j)
        (embS S 0) v false false (by rw [sum_embS]; omega)
      refine ⟨m' + 1 + j, ?_, ?_⟩
      · have : Fintype.card M.K * maxPush M * j ≤ Fintype.card M.K * maxPush M * j := le_rfl
        nlinarith
      · rw [Function.iterate_add_apply, h1, Function.iterate_add_apply]
        have e3 : (flip bind (TM2.step (progB φ ψ)))^[1] (some (embR ψ ⟨some l, v, S⟩ 0)) =
            some ⟨some (Sum.inr false), (v, false, false), embS S 0⟩ := stepB0 φ ψ l v S
        rw [e3, h2]
        have : ¬ m0 ≤ j := by omega
        simp [this]

end Machine

/-! ## Part 3: the assembly -/

section Final

attribute [local instance] FinTM2.kFin

theorem split_z (z : List Bool) :
    (∃ j r, z = List.replicate j true ++ false :: r) ∨ z = List.replicate z.length true := by
  induction z with
  | nil => right; rfl
  | cons a z ih =>
    cases a with
    | false => left; exact ⟨0, z, rfl⟩
    | true =>
      rcases ih with ⟨j, r, rfl⟩ | h
      · left; exact ⟨j + 1, r, rfl⟩
      · right; simp only [List.length_cons, List.replicate_succ]; rw [← h]

/-- The decider of `B`. -/
noncomputable def fB (p : List Bool × List Bool) : Bool :=
  @decide (inB c p) (Classical.propDecidable _)

theorem fB_iff (p : List Bool × List Bool) : fB c p = true ↔ inB c p := by
  simp [fB]

/-- The time constant. -/
noncomputable def Kc : ℕ := Fintype.card c.tm.K * maxPush c.tm + 5

theorem inB_iff (j : ℕ) (r w : List Bool) (m0 : ℕ)
    (hm : (flip bind c.tm.step)^[m0] (some (ini c (r, w))) =
      some (haltList c.tm [c.outputAlphabet.symm (f (r, w))])) :
    fB c (List.replicate j true ++ false :: r, w) = (decide (m0 ≤ j) && f (r, w)) := by
  apply Bool.eq_iff_iff.mpr
  rw [fB_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨-, i, hi, h⟩
    rw [lead_pad] at hi
    rw [body_pad] at h
    obtain ⟨e1, e2⟩ := halt_unique c.tm _ _ _ _ _ rfl rfl h hm
    have e3 := haltList_inj c.tm _ _ e2
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at e3
    exact ⟨e1 ▸ hi, (c.outputAlphabet.symm.injective e3).symm⟩
  · rintro ⟨h1, h2⟩
    refine ⟨by simp, m0, by rw [lead_pad]; exact h1, ?_⟩
    rw [body_pad, hm, h2]
    rfl

theorem wrap_core (z w : List Bool) : ∃ m ≤ Kc c * (encodePair (z, w)).length + Kc c,
    (flip bind (TM2.step (progB c.inputAlphabet c.outputAlphabet)))^[m]
      (some ⟨some (Sum.inr true), (c.tm.initialState, false, false),
        embS (upd0 ((encodePair (z, w)).map c.inputAlphabet.symm)) 0⟩) =
      some ⟨none, (c.tm.initialState, false, false),
        Function.update (fun _ => []) (some c.tm.k₁) [c.outputAlphabet.symm (fB c (z, w))]⟩ := by
  rcases split_z z with ⟨j, r, rfl⟩ | hz
  · have einp : (encodePair (List.replicate j true ++ false :: r, w)).map c.inputAlphabet.symm =
        List.replicate j (c.inputAlphabet.symm (Sum.inl true)) ++
          c.inputAlphabet.symm (Sum.inl false) :: (encodePair (r, w)).map c.inputAlphabet.symm := by
      simp [encodePair, List.map_replicate]
    rw [einp]
    obtain ⟨st', h1⟩ := stripRun c.inputAlphabet c.outputAlphabet
      (c.inputAlphabet.symm (Sum.inl false) :: (encodePair (r, w)).map c.inputAlphabet.symm) j
      (c.tm.initialState, false, false) 0
    obtain ⟨⟨m0, hm⟩, -⟩ := c.outputsFun (r, w)
    have hm' : (flip bind c.tm.step)^[m0]
        (some (initList c.tm ((encodePair (r, w)).map c.inputAlphabet.symm))) =
        some (haltList c.tm [c.outputAlphabet.symm (f (r, w))]) := hm
    obtain ⟨m1, hm1, h2⟩ := runSim c.inputAlphabet c.outputAlphabet _ (0 + j) m0 (f (r, w)) hm'
    rw [inB_iff c j r w m0 hm']
    refine ⟨m1 + 1 + j, ?_, ?_⟩
    · have hl : (encodePair (List.replicate j true ++ false :: r, w)).length =
          j + 1 + ((encodePair (r, w)).map c.inputAlphabet.symm).length := by
        simp [encodePair]; omega
      rw [hl]
      simp only [Kc]
      simp only [Nat.zero_add] at hm1
      generalize Fintype.card c.tm.K * maxPush c.tm = C at hm1 ⊢
      generalize ((encodePair (r, w)).map c.inputAlphabet.symm).length = L at hm1 ⊢
      nlinarith
    · rw [Function.iterate_add_apply, h1, Function.iterate_add_apply, Function.iterate_one,
        flip_bind_some, strip0, h2]
      simp
  · obtain ⟨n, rfl⟩ : ∃ n, z = List.replicate n true := ⟨_, hz⟩
    have hf : fB c (List.replicate n true, w) = false := by
      apply Bool.eq_false_iff.mpr
      rw [ne_eq, fB_iff]
      rintro ⟨h, -⟩
      simp at h
    rw [hf]
    have hK : 2 ≤ Kc c := by simp only [Kc]; omega
    cases w with
    | nil =>
      have einp : (encodePair (List.replicate n true, [])).map c.inputAlphabet.symm =
          List.replicate n (c.inputAlphabet.symm (Sum.inl true)) ++ [] := by
        simp [encodePair, List.map_replicate]
      rw [einp]
      obtain ⟨st', h1⟩ := stripRun c.inputAlphabet c.outputAlphabet [] n
        (c.tm.initialState, false, false) 0
      obtain ⟨m', hm', h2⟩ := cleanRun c.inputAlphabet c.outputAlphabet n
        (embS (upd0 []) (0 + n)) st'.1 false false (by rw [sum_embS, upd0, sum_upd]; simp)
      refine ⟨m' + 1 + n, ?_, ?_⟩
      · have hl : (encodePair (List.replicate n true, ([] : List Bool))).length = n := by
          simp [encodePair]
        rw [hl]; nlinarith
      · rw [Function.iterate_add_apply, h1, Function.iterate_add_apply, Function.iterate_one,
          flip_bind_some, stripE, h2]
    | cons y w' =>
      have einp : (encodePair (List.replicate n true, y :: w')).map c.inputAlphabet.symm =
          List.replicate n (c.inputAlphabet.symm (Sum.inl true)) ++
            c.inputAlphabet.symm (Sum.inr y) :: (w'.map Sum.inr).map c.inputAlphabet.symm := by
        simp [encodePair, List.map_replicate]
      rw [einp]
      obtain ⟨st', h1⟩ := stripRun c.inputAlphabet c.outputAlphabet
        (c.inputAlphabet.symm (Sum.inr y) :: (w'.map Sum.inr).map c.inputAlphabet.symm) n
        (c.tm.initialState, false, false) 0
      obtain ⟨m', hm', h2⟩ := cleanRun c.inputAlphabet c.outputAlphabet (n + w'.length)
        (embS (upd0 ((w'.map Sum.inr).map c.inputAlphabet.symm)) (0 + n)) st'.1 false false
        (by rw [sum_embS, upd0, sum_upd]; simp)
      refine ⟨m' + 1 + n, ?_, ?_⟩
      · have hl : (encodePair (List.replicate n true, y :: w')).length = n + w'.length + 1 := by
          simp [encodePair]; omega
        rw [hl]; nlinarith
      · rw [Function.iterate_add_apply, h1, Function.iterate_add_apply, Function.iterate_one,
          flip_bind_some, stripR, h2]

theorem wrap_out (z w : List Bool) : ∃ m ≤ Kc c * (encodePair (z, w)).length + Kc c,
    (flip bind (TM2.step (progB c.inputAlphabet c.outputAlphabet)))^[m]
      (some (initList (wrapB c.inputAlphabet c.outputAlphabet)
        ((encodePair (z, w)).map c.inputAlphabet.invFun))) =
      some (haltList (wrapB c.inputAlphabet c.outputAlphabet)
        ([fB c (z, w)].map c.outputAlphabet.invFun)) := by
  obtain ⟨m, hm, h⟩ := wrap_core c z w
  refine ⟨m, hm, ?_⟩
  rw [initList_eq, haltList_eq]
  have e := congrArg (fun S => (⟨some (Sum.inr true), (c.tm.initialState, false, false), S⟩ :
    TM2.Cfg (BΓ c.tm) (BΛ c.tm) (Bσ c.tm))) (embS_upd0 ((encodePair (z, w)).map c.inputAlphabet.symm))
  exact (congrArg (fun x => (flip bind (TM2.step (progB c.inputAlphabet c.outputAlphabet)))^[m]
    (some x)) e).symm.trans h

end Final

end Budget

open Budget in
theorem budget : StmtBudget := by
  intro S t ⟨f, hf, c, hc⟩
  have key := wrap_out c
  refine ⟨{p | inB c p}, Kc c, ⟨fB c, fun p => (fB_iff c p).symm,
    ⟨{ tm := wrapB c.inputAlphabet c.outputAlphabet
       inputAlphabet := c.inputAlphabet
       outputAlphabet := c.outputAlphabet
       time := fun l => Kc c * l + Kc c
       outputsFun := fun p =>
         { steps := Classical.choose (key p.1 p.2)
           evals_in_steps := (Classical.choose_spec (key p.1 p.2)).2
           steps_le_m := (Classical.choose_spec (key p.1 p.2)).1 } }, fun n => le_rfl⟩⟩,
    fun k s w h => (hf (s, w)).mpr (inB_sound c k s w h),
    fun k s w hk hS => inB_complete c t hc k s w hk ((hf _).mp hS)⟩

end PEqualNP.Library.Evasion
