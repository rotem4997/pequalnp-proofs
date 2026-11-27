import PEqualNP.Library.Machines.Run

/-!
# A machine that pads its input exponentially

Helper module (proofs only, no statement may use it).

Given a string `x` of length `n` on its input stack, the machine writes `2 ^ n` copies of `true`,
then one `false`, then `x` itself on its output stack. It has five stacks: the input `I`, a saved
copy `S` of the input (reversed), two unary counters `A` and `B`, and the output `O`.

* Label `start`: push one mark on `A`.
* Label `outer`: pop one symbol of the input and save it on `S`; when the input is empty go to
  `unsave`.
* Label `dbl`: move `A` to `B`, writing two marks on `B` per mark of `A`.
* Label `back`: move `B` back to `A`, then return to `outer`.
* Label `unsave`: move `S` to the output (this restores the order of `x`), then write `false`.
* Label `fin`: move `A` to the output, then halt.

It takes exactly `4 * 2 ^ n + 4 * n + 1` steps.
-/

namespace PEqualNP.Library.Machines.ExpPad

open Turing

/-- Exponential padding: `2 ^ length` ones, a separator, then the input itself. -/
def expPad (x : List Bool) : List Bool := List.replicate (2 ^ x.length) true ++ false :: x

/-- The stacks of the padding machine. -/
inductive PadK
  | I | S | A | B | O
  deriving DecidableEq

instance : Fintype PadK :=
  Fintype.ofList [.I, .S, .A, .B, .O] (fun x => by cases x <;> simp)

/-- The labels of the padding machine. -/
inductive PadL
  | start | outer | dbl | back | unsave | fin
  deriving DecidableEq

instance : Fintype PadL :=
  Fintype.ofList [.start, .outer, .dbl, .back, .unsave, .fin] (fun x => by cases x <;> simp)

/-- Stack alphabets: every stack holds bits. -/
@[reducible] def PadΓ : PadK → Type
  | .I => Bool
  | .S => Bool
  | .A => Bool
  | .B => Bool
  | .O => Bool

/-- The program. -/
def padProg : PadL → TM2.Stmt PadΓ PadL (Option Bool)
  | .start => .push .A (fun _ => true) (.goto fun _ => .outer)
  | .outer =>
    .pop .I (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .S (fun s => s.getD false) (.goto fun _ => .dbl))
        (.goto fun _ => .unsave))
  | .dbl =>
    .pop .A (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .B (fun _ => true) (.push .B (fun _ => true) (.goto fun _ => .dbl)))
        (.goto fun _ => .back))
  | .back =>
    .pop .B (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .A (fun _ => true) (.goto fun _ => .back))
        (.goto fun _ => .outer))
  | .unsave =>
    .pop .S (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .O (fun s => s.getD false) (.goto fun _ => .unsave))
        (.push .O (fun _ => false) (.goto fun _ => .fin)))
  | .fin =>
    .pop .A (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .O (fun _ => true) (.goto fun _ => .fin))
        .halt)

/-- The machine. -/
def padTM : FinTM2 where
  K := PadK
  k₀ := .I
  k₁ := .O
  Γ := PadΓ
  Λ := PadL
  main := .start
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := padProg

/-- All five stacks. -/
def pstk (i s a b o : List Bool) : ∀ k, List (PadΓ k)
  | .I => i
  | .S => s
  | .A => a
  | .B => b
  | .O => o

@[simp] theorem pstk_I (i s a b o : List Bool) : pstk i s a b o .I = i := rfl
@[simp] theorem pstk_S (i s a b o : List Bool) : pstk i s a b o .S = s := rfl
@[simp] theorem pstk_A (i s a b o : List Bool) : pstk i s a b o .A = a := rfl
@[simp] theorem pstk_B (i s a b o : List Bool) : pstk i s a b o .B = b := rfl
@[simp] theorem pstk_O (i s a b o : List Bool) : pstk i s a b o .O = o := rfl

@[simp] theorem pstk_set_I (i i' s a b o : List Bool) :
    Function.update (pstk i s a b o) .I i' = pstk i' s a b o := by
  funext k; cases k <;> simp [pstk]
@[simp] theorem pstk_set_S (i s s' a b o : List Bool) :
    Function.update (pstk i s a b o) .S s' = pstk i s' a b o := by
  funext k; cases k <;> simp [pstk]
@[simp] theorem pstk_set_A (i s a a' b o : List Bool) :
    Function.update (pstk i s a b o) .A a' = pstk i s a' b o := by
  funext k; cases k <;> simp [pstk]
@[simp] theorem pstk_set_B (i s a b b' o : List Bool) :
    Function.update (pstk i s a b o) .B b' = pstk i s a b' o := by
  funext k; cases k <;> simp [pstk]
@[simp] theorem pstk_set_O (i s a b o o' : List Bool) :
    Function.update (pstk i s a b o) .O o' = pstk i s a b o' := by
  funext k; cases k <;> simp [pstk]

theorem pstk_start (i : List Bool) :
    pstk i [] [] [] [] = Function.update (fun _ => [] : ∀ k, List (PadΓ k)) .I i := by
  funext k; cases k <;> simp [pstk]

theorem pstk_end (o : List Bool) :
    pstk [] [] [] [] o = Function.update (fun _ => [] : ∀ k, List (PadΓ k)) .O o := by
  funext k; cases k <;> simp [pstk]

/-- Configurations of the machine. -/
abbrev PadCfg : Type := TM2.Cfg PadΓ PadL (Option Bool)

/-- One step of the machine on an optional configuration. -/
abbrev padStep : Option PadCfg → Option PadCfg := flip bind (TM2.step padProg)

/-! ### Single steps -/

theorem start_step (st : Option Bool) (i s a b o : List Bool) :
    padStep (some ⟨some .start, st, pstk i s a b o⟩) =
      some ⟨some .outer, st, pstk i s (true :: a) b o⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem outer_cons (st : Option Bool) (y : Bool) (i s a b o : List Bool) :
    padStep (some ⟨some .outer, st, pstk (y :: i) s a b o⟩) =
      some ⟨some .dbl, some y, pstk i (y :: s) a b o⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem outer_nil (st : Option Bool) (s a b o : List Bool) :
    padStep (some ⟨some .outer, st, pstk [] s a b o⟩) =
      some ⟨some .unsave, none, pstk [] s a b o⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem dbl_cons (st : Option Bool) (y : Bool) (i s a b o : List Bool) :
    padStep (some ⟨some .dbl, st, pstk i s (y :: a) b o⟩) =
      some ⟨some .dbl, some y, pstk i s a (true :: true :: b) o⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem dbl_nil (st : Option Bool) (i s b o : List Bool) :
    padStep (some ⟨some .dbl, st, pstk i s [] b o⟩) =
      some ⟨some .back, none, pstk i s [] b o⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem back_cons (st : Option Bool) (y : Bool) (i s a b o : List Bool) :
    padStep (some ⟨some .back, st, pstk i s a (y :: b) o⟩) =
      some ⟨some .back, some y, pstk i s (true :: a) b o⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem back_nil (st : Option Bool) (i s a o : List Bool) :
    padStep (some ⟨some .back, st, pstk i s a [] o⟩) =
      some ⟨some .outer, none, pstk i s a [] o⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem unsave_cons (st : Option Bool) (y : Bool) (i s a b o : List Bool) :
    padStep (some ⟨some .unsave, st, pstk i (y :: s) a b o⟩) =
      some ⟨some .unsave, some y, pstk i s a b (y :: o)⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem unsave_nil (st : Option Bool) (i a b o : List Bool) :
    padStep (some ⟨some .unsave, st, pstk i [] a b o⟩) =
      some ⟨some .fin, none, pstk i [] a b (false :: o)⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem fin_cons (st : Option Bool) (y : Bool) (i s a b o : List Bool) :
    padStep (some ⟨some .fin, st, pstk i s (y :: a) b o⟩) =
      some ⟨some .fin, some y, pstk i s a b (true :: o)⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

theorem fin_nil (st : Option Bool) (i s b o : List Bool) :
    padStep (some ⟨some .fin, st, pstk i s [] b o⟩) =
      some ⟨none, none, pstk i s [] b o⟩ := by
  simp [padStep, flip, TM2.step, padProg, TM2.stepAux]

/-! ### Loops -/

/-- A stack of `n` copies of `true`. -/
abbrev rep (n : ℕ) : List Bool := List.replicate n true

theorem rep_succ (n : ℕ) : true :: rep n = rep (n + 1) := rfl

theorem dblLoop (i s o : List Bool) :
    ∀ (a b : ℕ) (st : Option Bool),
      padStep^[a + 1] (some ⟨some .dbl, st, pstk i s (rep a) (rep b) o⟩) =
        some ⟨some .back, none, pstk i s [] (rep (2 * a + b)) o⟩ := by
  intro a
  induction a with
  | zero => intro b st; simpa using dbl_nil st i s (rep b) o
  | succ a ih =>
    intro b st
    rw [Function.iterate_succ_apply, ← rep_succ a, dbl_cons, rep_succ, rep_succ, ih]
    rw [show 2 * a + (b + 1 + 1) = 2 * (a + 1) + b from by omega]

theorem backLoop (i s o : List Bool) :
    ∀ (b a : ℕ) (st : Option Bool),
      padStep^[b + 1] (some ⟨some .back, st, pstk i s (rep a) (rep b) o⟩) =
        some ⟨some .outer, none, pstk i s (rep (b + a)) [] o⟩ := by
  intro b
  induction b with
  | zero => intro a st; simpa using back_nil st i s (rep a) o
  | succ b ih =>
    intro a st
    rw [Function.iterate_succ_apply, ← rep_succ b, back_cons, rep_succ, ih]
    rw [show b + (a + 1) = b + 1 + a from by omega]

/-- The number of steps of the outer loop started with `a` marks and `n` input symbols. -/
def outerSteps : ℕ → ℕ → ℕ
  | _, 0 => 1
  | a, n + 1 => outerSteps (2 * a) n + ((2 * a + 1) + ((a + 1) + 1))

theorem outerSteps_eq : ∀ (n a : ℕ), outerSteps a n + 3 * a = 3 * a * 2 ^ n + 3 * n + 1 := by
  intro n
  induction n with
  | zero => intro a; simp [outerSteps]; omega
  | succ n ih =>
    intro a
    have h := ih (2 * a)
    have e : 3 * a * 2 ^ (n + 1) = 3 * (2 * a) * 2 ^ n := by ring
    rw [outerSteps, e]
    omega

theorem outerLoop :
    ∀ (x s : List Bool) (a : ℕ) (st : Option Bool),
      padStep^[outerSteps a x.length] (some ⟨some .outer, st, pstk x s (rep a) [] []⟩) =
        some ⟨some .unsave, none, pstk [] (x.reverse ++ s) (rep (a * 2 ^ x.length)) [] []⟩ := by
  intro x
  induction x with
  | nil => intro s a st; simpa [outerSteps] using outer_nil st s (rep a) [] []
  | cons y x ih =>
    intro s a st
    rw [List.length_cons, outerSteps,
      Function.iterate_add_apply padStep (outerSteps (2 * a) x.length),
      Function.iterate_add_apply padStep (2 * a + 1) ((a + 1) + 1),
      Function.iterate_succ_apply padStep (a + 1), outer_cons]
    have h1 : padStep^[a + 1]
        (some ⟨some .dbl, some y, pstk x (y :: s) (rep a) [] []⟩) =
        some ⟨some .back, none, pstk x (y :: s) [] (rep (2 * a)) []⟩ :=
      dblLoop x (y :: s) [] a 0 (some y)
    rw [h1]
    have h2 : padStep^[2 * a + 1]
        (some ⟨some .back, none, pstk x (y :: s) [] (rep (2 * a)) []⟩) =
        some ⟨some .outer, none, pstk x (y :: s) (rep (2 * a)) [] []⟩ :=
      backLoop x (y :: s) [] (2 * a) 0 none
    rw [h2, ih]
    rw [show 2 * a * 2 ^ x.length = a * 2 ^ (x.length + 1) from by ring]
    simp

theorem unsaveLoop (a : List Bool) :
    ∀ (s o : List Bool) (st : Option Bool),
      padStep^[s.length + 1] (some ⟨some .unsave, st, pstk [] s a [] o⟩) =
        some ⟨some .fin, none, pstk [] [] a [] (false :: (s.reverse ++ o))⟩ := by
  intro s
  induction s with
  | nil => intro o st; simpa using unsave_nil st [] a [] o
  | cons y s ih =>
    intro o st
    rw [List.length_cons, Function.iterate_succ_apply, unsave_cons, ih]
    simp

theorem finLoop :
    ∀ (a : ℕ) (o : List Bool) (st : Option Bool),
      padStep^[a + 1] (some ⟨some .fin, st, pstk [] [] (rep a) [] o⟩) =
        some ⟨none, none, pstk [] [] [] [] (rep a ++ o)⟩ := by
  intro a
  induction a with
  | zero => intro o st; simpa using fin_nil st [] [] [] o
  | succ a ih =>
    intro o st
    rw [Function.iterate_succ_apply, ← rep_succ a, fin_cons, ih]
    rw [show rep a ++ true :: o = true :: rep a ++ o from by
      simp [rep, ← List.replicate_succ, List.replicate_succ']]

/-- The number of steps of the machine on an input of length `n`. -/
def padSteps (n : ℕ) : ℕ := (2 ^ n + 1) + ((n + 1) + (outerSteps 1 n + 1))

theorem padSteps_eq (n : ℕ) : padSteps n = 4 * 2 ^ n + 4 * n + 1 := by
  have h := outerSteps_eq n 1
  unfold padSteps
  omega

theorem pad_run (x : List Bool) :
    (flip bind (TM2.step padProg))^[padSteps x.length] (some (initList padTM x)) =
      some (haltList padTM (expPad x)) := by
  refine (congrArg (fun c => (flip bind (TM2.step padProg))^[padSteps x.length]
    (some c)) (initList_eq padTM _)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq padTM _)).symm)
  show padStep^[padSteps x.length]
    (some (⟨some .start, none, Function.update (fun _ => []) .I x⟩ : PadCfg)) =
    some (⟨none, none, Function.update (fun _ => []) .O (expPad x)⟩ : PadCfg)
  rw [← pstk_start, ← pstk_end, padSteps, Function.iterate_add_apply padStep (2 ^ x.length + 1),
    Function.iterate_add_apply padStep (x.length + 1),
    Function.iterate_succ_apply padStep (outerSteps 1 x.length), start_step]
  have h1 : padStep^[outerSteps 1 x.length]
      (some ⟨some .outer, none, pstk x [] [true] [] []⟩) =
      some ⟨some .unsave, none, pstk [] x.reverse (rep (2 ^ x.length)) [] []⟩ := by
    simpa using outerLoop x [] 1 none
  have h2 : padStep^[x.length + 1]
      (some ⟨some .unsave, none, pstk [] x.reverse (rep (2 ^ x.length)) [] []⟩) =
      some ⟨some .fin, none, pstk [] [] (rep (2 ^ x.length)) [] (false :: x)⟩ := by
    simpa using unsaveLoop (rep (2 ^ x.length)) x.reverse [] none
  rw [h1, h2, finLoop]
  rfl

/-- Exponential padding is computable within an explicit exponential time bound. -/
theorem expPad_time : PEqualNP.Library.ComputableInTime
    (fun x : List Bool => x) (fun x : List Bool => x) expPad
    (fun n : ℕ => 8 * 2 ^ n + 8 * n + 8) := by
  refine ⟨{
    tm := padTM
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := padSteps
    outputsFun := fun x =>
      { steps := padSteps x.length
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := pad_run x
          exact (congrArg (fun l => (flip bind (TM2.step padProg))^[padSteps x.length]
            (some (initList padTM l))) (hm _ x)).trans
            (this.trans (congrArg (fun l => some (haltList padTM l)) (hm Bool _).symm))
        steps_le_m := le_refl _ } }, fun n => ?_⟩
  show padSteps n ≤ 8 * 2 ^ n + 8 * n + 8
  rw [padSteps_eq]
  omega

end PEqualNP.Library.Machines.ExpPad
