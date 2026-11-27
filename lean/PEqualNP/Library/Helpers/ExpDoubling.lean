import PEqualNP.Library.Machines.Run

/-!
# A machine that writes `2 ^ |x|` ones

Helper module (proofs only, no statement may use it).

Three stacks of bits: the input `I`, a temporary stack `B` and the output `O`.

* Label `start`: push one `true` on the output.
* Label `outer`: pop one symbol of the input; when the input is empty, halt.
* Label `dbl`: move the output to `B`, two symbols for each one.
* Label `back`: move `B` back to the output, then return to `outer`.

On an input of length `m` it takes `3 * 2 ^ m + 3 * m - 1` steps.
-/

namespace PEqualNP.Library.Helpers

open Turing PEqualNP.Library.Machines

/-- The stacks of the doubling machine. -/
inductive DblK
  | I | B | O
  deriving DecidableEq

instance : Fintype DblK :=
  Fintype.ofList [.I, .B, .O] (fun x => by cases x <;> simp)

/-- The labels of the doubling machine. -/
inductive DblL
  | start | outer | dbl | back
  deriving DecidableEq

instance : Fintype DblL :=
  Fintype.ofList [.start, .outer, .dbl, .back] (fun x => by cases x <;> simp)

/-- Stack alphabets: all bits. -/
@[reducible] def DblΓ : DblK → Type := fun _ => Bool

/-- The program. -/
def dblProg : DblL → TM2.Stmt DblΓ DblL (Option Bool)
  | .start => .push .O (fun _ => true) (.goto fun _ => .outer)
  | .outer =>
    .pop .I (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.goto fun _ => .dbl)
        .halt)
  | .dbl =>
    .pop .O (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .B (fun _ => true) (.push .B (fun _ => true) (.goto fun _ => .dbl)))
        (.goto fun _ => .back))
  | .back =>
    .pop .B (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push .O (fun _ => true) (.goto fun _ => .back))
        (.goto fun _ => .outer))

/-- The machine. -/
def dblTM : FinTM2 where
  K := DblK
  k₀ := .I
  k₁ := .O
  Γ := DblΓ
  Λ := DblL
  main := .start
  σ := Option Bool
  initialState := none
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m := dblProg

/-- All three stacks. -/
def dstk (i b o : List Bool) : ∀ k, List (DblΓ k)
  | .I => i
  | .B => b
  | .O => o

@[simp] theorem dstk_set_I (i i' b o : List Bool) :
    Function.update (dstk i b o) .I i' = dstk i' b o := by
  funext k; cases k <;> simp [dstk]
@[simp] theorem dstk_set_B (i b b' o : List Bool) :
    Function.update (dstk i b o) .B b' = dstk i b' o := by
  funext k; cases k <;> simp [dstk]
@[simp] theorem dstk_set_O (i b o o' : List Bool) :
    Function.update (dstk i b o) .O o' = dstk i b o' := by
  funext k; cases k <;> simp [dstk]

theorem dstk_start (i : List Bool) :
    dstk i [] [] = Function.update (fun _ => [] : ∀ k, List (DblΓ k)) .I i := by
  funext k; cases k <;> simp [dstk]

theorem dstk_end (o : List Bool) :
    dstk [] [] o = Function.update (fun _ => [] : ∀ k, List (DblΓ k)) .O o := by
  funext k; cases k <;> simp [dstk]

/-- Configurations of the machine. -/
abbrev DblCfg : Type := TM2.Cfg DblΓ DblL (Option Bool)

/-- One step of the machine on an optional configuration. -/
abbrev dblStep : Option DblCfg → Option DblCfg := flip bind (TM2.step dblProg)

/-! ### Single steps -/

theorem d_start (s : Option Bool) (i b o : List Bool) :
    dblStep (some ⟨some .start, s, dstk i b o⟩) =
      some ⟨some .outer, s, dstk i b (true :: o)⟩ := by
  simp [dblStep, flip, TM2.step, dblProg, TM2.stepAux, dstk]

theorem d_outer_cons (s : Option Bool) (y : Bool) (i b o : List Bool) :
    dblStep (some ⟨some .outer, s, dstk (y :: i) b o⟩) =
      some ⟨some .dbl, some y, dstk i b o⟩ := by
  simp [dblStep, flip, TM2.step, dblProg, TM2.stepAux, dstk]

theorem d_outer_nil (s : Option Bool) (b o : List Bool) :
    dblStep (some ⟨some .outer, s, dstk [] b o⟩) =
      some ⟨none, none, dstk [] b o⟩ := by
  simp [dblStep, flip, TM2.step, dblProg, TM2.stepAux, dstk]

theorem d_dbl_cons (s : Option Bool) (y : Bool) (i b o : List Bool) :
    dblStep (some ⟨some .dbl, s, dstk i b (y :: o)⟩) =
      some ⟨some .dbl, some y, dstk i (true :: true :: b) o⟩ := by
  simp [dblStep, flip, TM2.step, dblProg, TM2.stepAux, dstk]

theorem d_dbl_nil (s : Option Bool) (i b : List Bool) :
    dblStep (some ⟨some .dbl, s, dstk i b []⟩) =
      some ⟨some .back, none, dstk i b []⟩ := by
  simp [dblStep, flip, TM2.step, dblProg, TM2.stepAux, dstk]

theorem d_back_cons (s : Option Bool) (y : Bool) (i b o : List Bool) :
    dblStep (some ⟨some .back, s, dstk i (y :: b) o⟩) =
      some ⟨some .back, some y, dstk i b (true :: o)⟩ := by
  simp [dblStep, flip, TM2.step, dblProg, TM2.stepAux, dstk]

theorem d_back_nil (s : Option Bool) (i o : List Bool) :
    dblStep (some ⟨some .back, s, dstk i [] o⟩) =
      some ⟨some .outer, none, dstk i [] o⟩ := by
  simp [dblStep, flip, TM2.step, dblProg, TM2.stepAux, dstk]

/-! ### Loops -/

/-- A stack of `n` copies of `true`. -/
abbrev drep (n : ℕ) : List Bool := List.replicate n true

theorem drep_succ (n : ℕ) : true :: drep n = drep (n + 1) := rfl

theorem dblLoop (i : List Bool) :
    ∀ (L b : ℕ) (s : Option Bool),
      dblStep^[L + 1] (some ⟨some .dbl, s, dstk i (drep b) (drep L)⟩) =
        some ⟨some .back, none, dstk i (drep (2 * L + b)) []⟩ := by
  intro L
  induction L with
  | zero => intro b s; simpa using d_dbl_nil s i (drep b)
  | succ L ih =>
    intro b s
    rw [Function.iterate_succ_apply, ← drep_succ L, d_dbl_cons, drep_succ, drep_succ, ih]
    rw [show 2 * L + (b + 1 + 1) = 2 * (L + 1) + b from by omega]

theorem backLoop (i : List Bool) :
    ∀ (c o : ℕ) (s : Option Bool),
      dblStep^[c + 1] (some ⟨some .back, s, dstk i (drep c) (drep o)⟩) =
        some ⟨some .outer, none, dstk i [] (drep (c + o))⟩ := by
  intro c
  induction c with
  | zero => intro o s; simpa using d_back_nil s i (drep o)
  | succ c ih =>
    intro o s
    rw [Function.iterate_succ_apply, ← drep_succ c, d_back_cons, drep_succ, ih]
    rw [show c + (o + 1) = c + 1 + o from by omega]

/-- Steps of the outer loop on `m` remaining input symbols and `L` output symbols. -/
def osteps : ℕ → ℕ → ℕ
  | 0, _ => 1
  | m + 1, L => osteps m (2 * L) + ((2 * L + 1) + ((L + 1) + 1))

theorem osteps_eq : ∀ m L, osteps m L + 3 * L = 3 * 2 ^ m * L + 3 * m + 1 := by
  intro m
  induction m with
  | zero => intro L; simp [osteps]; ring
  | succ m ih =>
    intro L
    have h := ih (2 * L)
    simp only [osteps]
    rw [pow_succ]
    nlinarith [h]

theorem outerLoop : ∀ (i : List Bool) (L : ℕ) (s : Option Bool),
    dblStep^[osteps i.length L] (some ⟨some .outer, s, dstk i [] (drep L)⟩) =
      some ⟨none, none, dstk [] [] (drep (2 ^ i.length * L))⟩ := by
  intro i
  induction i with
  | nil => intro L s; simpa [osteps] using d_outer_nil s [] (drep L)
  | cons y i ih =>
    intro L s
    rw [List.length_cons, osteps, Function.iterate_add_apply,
      Function.iterate_add_apply dblStep (2 * L + 1),
      Function.iterate_succ_apply dblStep (L + 1), d_outer_cons]
    have h1 : dblStep^[L + 1] (some ⟨some .dbl, some y, dstk i (drep 0) (drep L)⟩) =
        some ⟨some .back, none, dstk i (drep (2 * L + 0)) []⟩ := dblLoop i L 0 (some y)
    simp only [drep, List.replicate_zero, Nat.add_zero] at h1
    rw [h1]
    have h2 : dblStep^[2 * L + 1]
        (some ⟨some .back, none, dstk i (drep (2 * L)) (drep 0)⟩) =
        some ⟨some .outer, none, dstk i [] (drep (2 * L + 0))⟩ := backLoop i (2 * L) 0 none
    simp only [drep, List.replicate_zero, Nat.add_zero] at h2
    rw [h2]
    have h3 := ih (2 * L) none
    simp only [drep] at h3
    rw [show 2 ^ (i.length + 1) * L = 2 ^ i.length * (2 * L) by ring]
    exact h3

theorem dbl_run (x : List Bool) :
    (flip bind (TM2.step dblProg))^[osteps x.length 1 + 1]
        (some (initList dblTM x)) =
      some (haltList dblTM (drep (2 ^ x.length))) := by
  refine (congrArg (fun c => (flip bind (TM2.step dblProg))^[osteps x.length 1 + 1]
    (some c)) (initList_eq dblTM _)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq dblTM _)).symm)
  show dblStep^[osteps x.length 1 + 1]
    (some (⟨some .start, none, Function.update (fun _ => []) .I x⟩ : DblCfg)) =
    some (⟨none, none, Function.update (fun _ => []) .O (drep (2 ^ x.length))⟩ : DblCfg)
  rw [← dstk_start, ← dstk_end, Function.iterate_succ_apply, d_start]
  have h := outerLoop x 1 none
  simp only [Nat.mul_one] at h
  exact h

/-- The time bound of the doubling machine. -/
def dblTime (m : ℕ) : ℕ := 3 * 2 ^ m + 3 * m

theorem dblTime_mono : Monotone dblTime := by
  intro a b h
  unfold dblTime
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h
  omega

/-- The function `x ↦ 2 ^ |x|` ones is computable within `3 * 2 ^ n + 3 * n` steps. -/
theorem dbl_time :
    PEqualNP.Library.ComputableInTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => List.replicate (2 ^ x.length) true) dblTime := by
  refine ⟨{
    tm := dblTM
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := dblTime
    outputsFun := fun x =>
      { steps := osteps x.length 1 + 1
        evals_in_steps := by
          have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l :=
            fun l => by simp
          have := dbl_run x
          exact (congrArg (fun l => (flip bind (TM2.step dblProg))^[osteps x.length 1 + 1]
            (some (initList dblTM l))) (hm x)).trans
            (this.trans (congrArg (fun l => some (haltList dblTM l)) (hm _).symm))
        steps_le_m := by
          have := osteps_eq x.length 1
          simp only [dblTime]
          omega } }, fun _ => le_rfl⟩

end PEqualNP.Library.Helpers
