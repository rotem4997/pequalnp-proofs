import PEqualNP.Library.Machines.Transducer
import PEqualNP.Library.Machines.ComposeTime

/-!
# Linear-time transducers with an explicit time bound, and two small rewrites

Helper module (proofs only, no statement may use it).

* `fst2_time`: a function produced by a finite-state transducer (at most two output symbols per
  input symbol, at most one at the end) is computable within `2 * n + 3` steps. This is
  `fst2_polyTime` with the time bound kept explicit.
* `sepPair_time`: the pair `(a, x)`, in the pair encoding, goes to `a ++ false :: x`.
* `consTrue_time`: `y` goes to `true :: y`.
-/

namespace PEqualNP.Library.Helpers

open Turing PEqualNP.Library.Machines

/-- A transducer function is computable within `2 * n + 3` steps. -/
theorem fst2_time {α β αΓ βΓ Q : Type} [Fintype αΓ] [Fintype Q] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (δ : Q → αΓ → Q × Option βΓ × Option βΓ)
    (fin : Q → Option βΓ) (q₀ : Q) (h : ∀ a, eb (f a) = fstRun2 δ fin q₀ (ea a)) :
    PEqualNP.Library.ComputableInTime ea eb f (fun n => 2 * n + 3) := by
  classical
  let d : Option βΓ := if h : Nonempty βΓ then some (Classical.choice h) else none
  have hd : ∀ _ : βΓ, d ≠ none := by
    intro y
    have hn : Nonempty βΓ := ⟨y⟩
    simp [d, hn]
  exact ⟨{
    tm := trM δ fin q₀ d
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := fun n => 2 * n + 3
    outputsFun := fun a =>
      { steps := (ea a).length + 1 + 1 + ((ea a).length + 1)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := trM_run δ fin q₀ d hd (ea a)
          exact (congrArg (fun l => (flip bind (TM2.step (trProg δ fin q₀ d)))^[(ea a).length +
            1 + 1 + ((ea a).length + 1)] (some (initList (trM δ fin q₀ d) l)))
            (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l => some (haltList (trM δ fin q₀ d) l))
              ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m := by omega } }, fun _ => le_rfl⟩

/-- Transducer writing the separator at the first symbol of the second component. -/
def sepδ : Bool → (Bool ⊕ Bool) → Bool × Option Bool × Option Bool
  | false, Sum.inl b => (false, some b, none)
  | false, Sum.inr b => (true, some false, some b)
  | true, Sum.inl b => (true, some b, none)
  | true, Sum.inr b => (true, some b, none)

/-- End of input: write the separator if it was not written. -/
def sepFin : Bool → Option Bool
  | false => some false
  | true => none

theorem sep_run_true (x : List Bool) : fstRun2 sepδ sepFin true (x.map Sum.inr) = x := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [fstRun2, sepδ, ih]

theorem sep_run_false (a x : List Bool) :
    fstRun2 sepδ sepFin false (a.map Sum.inl ++ x.map Sum.inr) = a ++ false :: x := by
  induction a with
  | nil =>
    cases x with
    | nil => rfl
    | cons b x => simp [fstRun2, sepδ, sep_run_true]
  | cons b a ih => simp [fstRun2, sepδ, ih]

theorem sepPair_time : PEqualNP.Library.ComputableInTime PEqualNP.Library.encodePair
    (fun x : List Bool => x) (fun p : List Bool × List Bool => p.1 ++ false :: p.2)
    (fun n => 2 * n + 3) :=
  fst2_time _ _ _ sepδ sepFin false (fun p => (sep_run_false p.1 p.2).symm)

/-- Transducer writing one extra `true` in front. -/
def consδ : Bool → Bool → Bool × Option Bool × Option Bool
  | false, b => (true, some true, some b)
  | true, b => (true, some b, none)

/-- End of input: write the extra `true` if it was not written. -/
def consFin : Bool → Option Bool
  | false => some true
  | true => none

theorem cons_run_true (y : List Bool) : fstRun2 consδ consFin true y = y := by
  induction y with
  | nil => rfl
  | cons b y ih => simp [fstRun2, consδ, ih]

theorem cons_run_false (y : List Bool) : fstRun2 consδ consFin false y = true :: y := by
  cases y with
  | nil => rfl
  | cons b y => simp [fstRun2, consδ, cons_run_true]

theorem consTrue_time : PEqualNP.Library.ComputableInTime (fun x : List Bool => x)
    (fun x : List Bool => x) (fun y : List Bool => true :: y) (fun n => 2 * n + 3) :=
  fst2_time _ _ _ consδ consFin false (fun y => (cons_run_false y).symm)

end PEqualNP.Library.Helpers
