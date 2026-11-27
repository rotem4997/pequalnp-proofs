import PEqualNP.Defs
import Mathlib.Tactic

/-!
# A machine that erases its input and answers a fixed bit

Helper module (proofs only, no statement may use it). One stack of bits, used for both input and
output. The single labelled statement pops one symbol; if there was one it loops, otherwise it
pushes the answer and halts. On an input of length `n` it halts after `n + 1` steps.
-/

namespace PEqualNP.Library.Machines

open Turing

/-- Erase the input, then write `b`. -/
def constBool (b : Bool) : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := Bool
  initialState := false
  m _ := TM2.Stmt.pop () (fun _ o => o.isSome)
    (TM2.Stmt.branch (fun s => s)
      (TM2.Stmt.load (fun _ => false) (TM2.Stmt.goto fun _ => ()))
      (TM2.Stmt.push () (fun _ => b) TM2.Stmt.halt))

theorem constBool_run (b : Bool) (l : List Bool) :
    (flip bind (constBool b).step)^[l.length + 1]
      (some (⟨some (), false, fun _ => l⟩ : (constBool b).Cfg)) =
      some (⟨none, false, fun _ => [b]⟩ : (constBool b).Cfg) := by
  induction l with
  | nil =>
    simp only [List.length_nil, Function.iterate_succ_apply, Function.iterate_zero_apply]
    show some _ = some _
    congr 1
  | cons a l ih =>
    rw [List.length_cons, Function.iterate_succ_apply]
    rw [← ih]
    congr 1

/-- The constant function to `b` on binary strings is computable in `n + 1` steps. -/
noncomputable def constBoolComputable (b : Bool) :
    TM2ComputableInPolyTime (fun x : List Bool => x) Computability.encodeBool
      (fun _ : List Bool => b) where
  tm := constBool b
  inputAlphabet := Equiv.refl _
  outputAlphabet := Equiv.refl _
  time := Polynomial.X + 1
  outputsFun a :=
    { steps := a.length + 1
      evals_in_steps := by
        have hm : ∀ l : List Bool, List.map (Equiv.refl Bool).invFun l = l := fun l => by simp
        have e1 : (some (initList (constBool b) (List.map (Equiv.refl Bool).invFun a)) :
            Option (constBool b).Cfg) = some ⟨some (), false, fun _ => a⟩ :=
          congrArg (fun l : List Bool =>
            (some (⟨some (), false, fun _ => l⟩ : (constBool b).Cfg))) (hm a)
        exact Eq.trans (congrArg ((flip bind (constBool b).step)^[a.length + 1]) e1)
          (constBool_run b a)
      steps_le_m := by simp }

end PEqualNP.Library.Machines
