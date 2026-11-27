import PEqualNP.Library.Machines.Run

/-!
# A machine that reverses its input

Helper module (proofs only, no statement may use it).

Two stacks of bits, the input (`false`) and the output (`true`), and one label. The single
labelled statement pops the input; if a symbol was there it pushes it on the output and loops,
otherwise it halts. The input stack has the first symbol on top, so the output stack ends with
the last symbol on top: the reversal. On an input of length `n` it halts after `n + 1` steps.
The internal state holds the symbol in transit and is `none` between steps.
-/

namespace PEqualNP.Library.Machines.Rev

open Turing

/-- The program: move one symbol from the input to the output, or halt. -/
def prog : Unit → TM2.Stmt (fun _ : Bool => Bool) Unit (Option Bool)
  | () =>
    .pop false (fun _ o => o)
      (.branch (fun s => s.isSome)
        (.push true (fun s => s.getD false) (.load (fun _ => none) (.goto fun _ => ())))
        .halt)

/-- The machine. -/
def tm : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Option Bool
  initialState := none
  m := prog

/-- Configurations of the machine. -/
abbrev RCfg : Type := TM2.Cfg (fun _ : Bool => Bool) Unit (Option Bool)

/-- The two stacks: input `l`, output `u`. -/
def st (l u : List Bool) : Bool → List Bool := fun k => cond k u l

theorem st_start (l : List Bool) :
    st l [] = Function.update (fun _ => ([] : List Bool)) false l := by
  funext k; cases k <;> simp [st]

theorem st_end (u : List Bool) :
    st [] u = Function.update (fun _ => ([] : List Bool)) true u := by
  funext k; cases k <;> simp [st]

theorem step_cons (x : Bool) (l u : List Bool) :
    TM2.step prog (⟨some (), none, st (x :: l) u⟩ : RCfg) =
      some ⟨some (), none, st l (x :: u)⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  simp only [st, Bool.cond_false, List.head?_cons, List.tail_cons, Option.isSome_some, Bool.cond_true,
    Option.getD_some, Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
  funext k; cases k <;> simp [st]

theorem step_nil (u : List Bool) :
    TM2.step prog (⟨some (), none, st [] u⟩ : RCfg) = some ⟨none, none, st [] u⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  simp only [st, Bool.cond_false, List.head?_nil, List.tail_nil, Option.isSome_none,
    Option.some.injEq, TM2.Cfg.mk.injEq, true_and]
  funext k; cases k <;> simp [st]

theorem loop : ∀ (l u : List Bool),
    (flip bind (TM2.step prog))^[l.length + 1] (some (⟨some (), none, st l u⟩ : RCfg)) =
      some ⟨none, none, st [] (l.reverse ++ u)⟩ := by
  intro l
  induction l with
  | nil => intro u; exact step_nil u
  | cons x l ih =>
    intro u
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step prog) (some (⟨some (), none, st (x :: l) u⟩ : RCfg)) =
        some ⟨some (), none, st l (x :: u)⟩ := step_cons x l u
    rw [e, ih]
    simp

theorem run (l : List Bool) :
    (flip bind (TM2.step prog))^[l.length + 1] (some (initList tm l)) =
      some (haltList tm l.reverse) := by
  refine (congrArg (fun c => (flip bind (TM2.step prog))^[l.length + 1] (some c))
    (initList_eq tm l)).trans (Eq.trans ?_ (congrArg some (haltList_eq tm l.reverse)).symm)
  show (flip bind (TM2.step prog))^[l.length + 1]
    (some (⟨some (), none, Function.update (fun _ => []) false l⟩ : RCfg)) =
    some (⟨none, none, Function.update (fun _ => []) true l.reverse⟩ : RCfg)
  rw [← st_start, loop, ← st_end]
  simp

/-- Reversal of binary strings is computable in `n + 1` steps. -/
noncomputable def reverseComputable :
    TM2ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => x.reverse) where
  tm := tm
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + 1
  outputsFun a :=
    { steps := a.length + 1
      evals_in_steps := by
        have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l := fun l => by simp
        exact (congrArg (fun l => (flip bind (TM2.step prog))^[a.length + 1]
          (some (initList tm l))) (hm a)).trans
          ((run a).trans (congrArg (fun l => some (haltList tm l)) (hm a.reverse).symm))
      steps_le_m := by simp }

end PEqualNP.Library.Machines.Rev
