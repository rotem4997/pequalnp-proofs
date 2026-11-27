import PEqualNP.Library.Machines.Run

/-!
# Running a machine on the first component of a pair, any alphabets

Helper module (proofs only, no statement may use it).

A pair of a list over `A` and a list over `C` is written over `A ⊕ C`: the first list tagged
`Sum.inl`, then the second tagged `Sum.inr`. For a machine `M` computing `f` from strings over
`A` to strings over `B`, `firstM M e₀ e₁` computes `(a, w) ↦ (f a, w)`. It has the stacks of `M`
and five more: the input `I`, a store `W` for the second component, temporary stacks `TA` and
`TB`, and the output `O`.

1. `l1`: empty `I`; first components go to `TA`, second components to `W` (both reversed).
2. `l2`: move `TA` to the input stack of `M` (order restored).
3. run `M`, whose statements never touch the five extra stacks.
4. `l3`: move `W` to `O`, tagged as second components (order restored).
5. `l4`: move the output of `M` to `TB`. `l5`: move `TB` to `O`, tagged as first components.

A push needs a total function from the internal state to the symbol pushed, so the alphabets
are asked to be inhabited; the default symbols are never written.
-/

namespace PEqualNP.Library.Machines.Gen

open Turing PEqualNP.Library.Machines

/-- The pair of two lists, over the sum alphabet. -/
def gpair {A C : Type} (p : List A × List C) : List (A ⊕ C) :=
  p.1.map Sum.inl ++ p.2.map Sum.inr

/-- The five extra stacks. -/
inductive FX
  | I | W | TA | TB | O
  deriving DecidableEq

instance : Fintype FX :=
  Fintype.ofList [FX.I, FX.W, FX.TA, FX.TB, FX.O] (fun x => by cases x <;> simp)

/-- The five extra labels. -/
inductive FL
  | l1 | l2 | l3 | l4 | l5
  deriving DecidableEq

instance : Fintype FL :=
  Fintype.ofList [FL.l1, FL.l2, FL.l3, FL.l4, FL.l5] (fun x => by cases x <;> simp)

variable (M : FinTM2) (A B C : Type)

/-- Stack alphabets of the composite. -/
@[reducible] def FstΓ : M.K ⊕ FX → Type
  | Sum.inl k => M.Γ k
  | Sum.inr FX.I => A ⊕ C
  | Sum.inr FX.W => C
  | Sum.inr FX.TA => A
  | Sum.inr FX.TB => B
  | Sum.inr FX.O => B ⊕ C

/-- Labels of the composite. -/
abbrev FstΛ : Type := M.Λ ⊕ FL

/-- Internal state of the composite: that of `M` and one symbol in transit. -/
abbrev Fstσ : Type := M.σ × Option (A ⊕ B ⊕ C)

variable {A B C}

/-- The symbol in transit, read as a symbol of `A`. -/
def getA [Inhabited A] : Option (A ⊕ B ⊕ C) → A
  | some (Sum.inl a) => a
  | _ => default

/-- The symbol in transit, read as a symbol of `B`. -/
def getB [Inhabited B] : Option (A ⊕ B ⊕ C) → B
  | some (Sum.inr (Sum.inl b)) => b
  | _ => default

/-- The symbol in transit, read as a symbol of `C`. -/
def getC [Inhabited C] : Option (A ⊕ B ⊕ C) → C
  | some (Sum.inr (Sum.inr c)) => c
  | _ => default

/-- Whether the symbol in transit is a symbol of `A`. -/
def isA : Option (A ⊕ B ⊕ C) → Bool
  | some (Sum.inl _) => true
  | _ => false

/-- An input symbol as a symbol in transit. -/
def ofI : A ⊕ C → A ⊕ B ⊕ C
  | Sum.inl a => Sum.inl a
  | Sum.inr c => Sum.inr (Sum.inr c)

variable {M}
variable (A B C)

/-- A statement of `M` inside the composite. Halting becomes a jump to `l3`. -/
def trF : TM2.Stmt M.Γ M.Λ M.σ → TM2.Stmt (FstΓ M A B C) (FstΛ M) (Fstσ M A B C)
  | .push k f q => .push (Sum.inl k) (fun s => f s.1) (trF q)
  | .peek k f q => .peek (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trF q)
  | .pop k f q => .pop (Sum.inl k) (fun s o => (f s.1 o, s.2)) (trF q)
  | .load a q => .load (fun s => (a s.1, s.2)) (trF q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (trF q₁) (trF q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .goto (fun _ => Sum.inr FL.l3)

variable (M) {A B}
variable [Inhabited A] [Inhabited B] [Inhabited C]

/-- The program of the composite. -/
def firstProg (e₀ : A → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → B) :
    FstΛ M → TM2.Stmt (FstΓ M A B C) (FstΛ M) (Fstσ M A B C)
  | Sum.inl l => trF A B C (M.m l)
  | Sum.inr FL.l1 =>
    .pop (Sum.inr FX.I) (fun s o => (s.1, o.map ofI))
      (.branch (fun s => s.2.isSome)
        (.branch (fun s => isA s.2)
          (.push (Sum.inr FX.TA) (fun s => getA s.2) (.goto fun _ => Sum.inr FL.l1))
          (.push (Sum.inr FX.W) (fun s => getC s.2) (.goto fun _ => Sum.inr FL.l1)))
        (.goto fun _ => Sum.inr FL.l2))
  | Sum.inr FL.l2 =>
    .pop (Sum.inr FX.TA) (fun s o => (s.1, o.map Sum.inl))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inl M.k₀) (fun s => e₀ (getA s.2)) (.goto fun _ => Sum.inr FL.l2))
        (.goto fun _ => Sum.inl M.main))
  | Sum.inr FL.l3 =>
    .pop (Sum.inr FX.W) (fun s o => (s.1, o.map fun c => Sum.inr (Sum.inr c)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.O) (fun s => Sum.inr (getC s.2)) (.goto fun _ => Sum.inr FL.l3))
        (.goto fun _ => Sum.inr FL.l4))
  | Sum.inr FL.l4 =>
    .pop (Sum.inl M.k₁) (fun s o => (s.1, o.map fun y => Sum.inr (Sum.inl (e₁ y))))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.TB) (fun s => getB s.2) (.goto fun _ => Sum.inr FL.l4))
        (.goto fun _ => Sum.inr FL.l5))
  | Sum.inr FL.l5 =>
    .pop (Sum.inr FX.TB) (fun s o => (s.1, o.map fun b => Sum.inr (Sum.inl b)))
      (.branch (fun s => s.2.isSome)
        (.push (Sum.inr FX.O) (fun s => Sum.inl (getB s.2)) (.goto fun _ => Sum.inr FL.l5))
        .halt)

/-- The composite machine. -/
def firstM [Fintype A] [Fintype B] [Fintype C] (e₀ : A → M.Γ M.k₀) (e₁ : M.Γ M.k₁ → B) :
    FinTM2 :=
  haveI := M.kFin
  haveI := M.ΛFin
  haveI := M.σFin
  { K := M.K ⊕ FX
    k₀ := Sum.inr FX.I
    k₁ := Sum.inr FX.O
    Γ := FstΓ M A B C
    Λ := FstΛ M
    main := Sum.inr FL.l1
    σ := Fstσ M A B C
    initialState := (M.initialState, none)
    Γk₀Fin := inferInstanceAs (Fintype (A ⊕ C))
    m := firstProg M C e₀ e₁ }

omit [Inhabited A] [Inhabited B] [Inhabited C]
variable {M} {C}

/-- All stacks of the composite: those of `M`, then `I`, `W`, `TA`, `TB`, `O`. -/
def fstk (S : ∀ k, List (M.Γ k)) (i : List (A ⊕ C)) (w : List C) (ta : List A) (tb : List B)
    (o : List (B ⊕ C)) : ∀ k, List (FstΓ M A B C k)
  | Sum.inl k => S k
  | Sum.inr FX.I => i
  | Sum.inr FX.W => w
  | Sum.inr FX.TA => ta
  | Sum.inr FX.TB => tb
  | Sum.inr FX.O => o

section fstk

variable (S : ∀ k, List (M.Γ k)) (i : List (A ⊕ C)) (w : List C) (ta : List A) (tb : List B)
  (o : List (B ⊕ C))

@[simp] theorem fstk_M (k : M.K) : fstk S i w ta tb o (Sum.inl k) = S k := rfl
@[simp] theorem fstk_I : fstk S i w ta tb o (Sum.inr FX.I) = i := rfl
@[simp] theorem fstk_W : fstk S i w ta tb o (Sum.inr FX.W) = w := rfl
@[simp] theorem fstk_TA : fstk S i w ta tb o (Sum.inr FX.TA) = ta := rfl
@[simp] theorem fstk_TB : fstk S i w ta tb o (Sum.inr FX.TB) = tb := rfl
@[simp] theorem fstk_O : fstk S i w ta tb o (Sum.inr FX.O) = o := rfl

theorem fstk_set_M (k : M.K) (x : List (M.Γ k)) :
    Function.update (fstk S i w ta tb o) (Sum.inl k) x =
      fstk (Function.update S k x) i w ta tb o := by
  funext j
  rcases j with j | j
  · by_cases h : j = k
    · subst h
      rw [Function.update_self]
      show x = Function.update S j x j
      rw [Function.update_self]
    · rw [Function.update_of_ne (by simpa using h)]
      show S j = Function.update S k x j
      rw [Function.update_of_ne h]
  · rw [Function.update_of_ne (by simp)]; cases j <;> rfl

theorem fstk_set_I (i' : List (A ⊕ C)) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.I) i' = fstk S i' w ta tb o := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  all_goals rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_W (w' : List C) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.W) w' = fstk S i w' ta tb o := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  all_goals rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_TA (ta' : List A) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.TA) ta' = fstk S i w ta' tb o := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  all_goals rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_TB (tb' : List B) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.TB) tb' = fstk S i w ta tb' o := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl

theorem fstk_set_O (o' : List (B ⊕ C)) :
    Function.update (fstk S i w ta tb o) (Sum.inr FX.O) o' = fstk S i w ta tb o' := by
  funext j
  rcases j with j | (_ | _ | _ | _ | _)
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_of_ne (by simp)]; rfl
  · rw [Function.update_self]; rfl

end fstk

variable (M A B C) in
/-- Configurations of the composite. -/
abbrev FCfg : Type := TM2.Cfg (FstΓ M A B C) (FstΛ M) (Fstσ M A B C)

/-- A configuration of `M` inside the composite; a halted `M` stands at `l3`. -/
def embF (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C) (ta : List A) (tb : List B)
    (o : List (B ⊕ C)) (c : TM2.Cfg M.Γ M.Λ M.σ) : FCfg M A B C :=
  ⟨some (c.l.elim (Sum.inr FL.l3) Sum.inl), (c.var, b), fstk c.stk i w ta tb o⟩

theorem simF (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C) (ta : List A)
    (tb : List B) (o : List (B ⊕ C)) (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ)
    (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (trF A B C q) ((v, b) : Fstσ M A B C) (fstk S i w ta tb o) =
      embF b i w ta tb o (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih =>
    have := ih v (Function.update S k (f v :: S k))
    rw [← fstk_set_M] at this
    exact this
  | peek k f q ih => exact ih _ _
  | pop k f q ih =>
    have := ih (f v (S k).head?) (Function.update S k (S k).tail)
    rw [← fstk_set_M] at this
    exact this
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trF, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem stepF [Inhabited A] [Inhabited B] [Inhabited C] (e₀ : A → M.Γ M.k₀)
    (e₁ : M.Γ M.k₁ → B) (b : Option (A ⊕ B ⊕ C)) (i : List (A ⊕ C)) (w : List C)
    (ta : List A) (tb : List B) (o : List (B ⊕ C))
    (c c' : TM2.Cfg M.Γ M.Λ M.σ) (h : TM2.step M.m c = some c') :
    TM2.step (firstProg M C e₀ e₁) (embF b i w ta tb o c) = some (embF b i w ta tb o c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (simF b i w ta tb o (M.m l) v S)

end PEqualNP.Library.Machines.Gen
