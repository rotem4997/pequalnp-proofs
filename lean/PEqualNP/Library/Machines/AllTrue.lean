import PEqualNP.Library.Machines.Run

/-!
# A machine that decides whether every bit of a pair of strings is true

Helper module (proofs only, no statement may use it). Two stacks: the input (tagged bits) and the
output (one bit). The single labelled statement pops one input symbol and ANDs its bit into the
internal state; when the input is empty it pushes the accumulated bit onto the output, resets the
internal state and halts. On an input of length `n` it halts after `n + 1` steps.
-/

namespace PEqualNP.Library.Machines

open Turing

/-- Stack alphabets: input (`false`), output (`true`). -/
@[reducible] def AΓ : Bool → Type
  | false => Bool ⊕ Bool
  | true => Bool

/-- The bit carried by a tagged symbol. -/
def aval : Bool ⊕ Bool → Bool := Sum.elim id id

/-- The program. The state is (accumulated bit, whether a symbol was popped). -/
def atProg : Unit → TM2.Stmt AΓ Unit (Bool × Bool) :=
  fun _ => .pop false (fun s o => (s.1 && (o.map aval).getD true, o.isSome))
    (.branch (fun s => s.2)
      (.goto fun _ => ())
      (.push true (fun s => s.1) (.load (fun _ => (true, false)) .halt)))

/-- The machine. -/
def atM : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ := AΓ
  Λ := Unit
  main := ()
  σ := Bool × Bool
  initialState := (true, false)
  Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
  m := atProg

/-- The stacks: input, output. -/
def ast (l : List (Bool ⊕ Bool)) (u : List Bool) : ∀ k, List (AΓ k)
  | false => l
  | true => u

theorem ast_in (l : List (Bool ⊕ Bool)) (u : List Bool) : ast l u false = l := rfl

theorem ast_out (l : List (Bool ⊕ Bool)) (u : List Bool) : ast l u true = u := rfl

theorem ast_set_in (l l' : List (Bool ⊕ Bool)) (u : List Bool) :
    Function.update (ast l u) false l' = ast l' u := by
  funext k
  cases k <;> simp [ast]

theorem ast_set_out (l : List (Bool ⊕ Bool)) (u u' : List Bool) :
    Function.update (ast l u) true u' = ast l u' := by
  funext k
  cases k <;> simp [ast]

theorem ast_start (l : List (Bool ⊕ Bool)) :
    ast l [] = Function.update (fun _ => [] : ∀ k, List (AΓ k)) false l := by
  funext k
  cases k <;> simp [ast]

theorem ast_end (u : List Bool) :
    ast [] u = Function.update (fun _ => [] : ∀ k, List (AΓ k)) true u := by
  funext k
  cases k <;> simp [ast]

/-- Configurations of the machine. -/
abbrev ACfg : Type := TM2.Cfg AΓ Unit (Bool × Bool)

theorem at_cons (s : Bool × Bool) (x : Bool ⊕ Bool) (l : List (Bool ⊕ Bool)) (u : List Bool) :
    TM2.step atProg (⟨some (), s, ast (x :: l) u⟩ : ACfg) =
      some ⟨some (), (s.1 && aval x, true), ast l u⟩ := by
  simp [TM2.step, atProg, TM2.stepAux, ast_in, ast_set_in]

theorem at_nil (s : Bool × Bool) (u : List Bool) :
    TM2.step atProg (⟨some (), s, ast [] u⟩ : ACfg) =
      some ⟨none, (true, false), ast [] (s.1 :: u)⟩ := by
  simp [TM2.step, atProg, TM2.stepAux, ast_in, ast_out, ast_set_in, ast_set_out]

theorem at_loop :
    ∀ (l : List (Bool ⊕ Bool)) (s : Bool × Bool),
      (flip bind (TM2.step atProg))^[l.length + 1]
          (some (⟨some (), s, ast l []⟩ : ACfg)) =
        some ⟨none, (true, false), ast [] [s.1 && l.all aval]⟩ := by
  intro l
  induction l with
  | nil =>
    intro s
    have h : (s.1 && ([] : List (Bool ⊕ Bool)).all aval) = s.1 := by simp
    rw [h]
    exact at_nil s []
  | cons x l ih =>
    intro s
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step atProg)
        (some (⟨some (), s, ast (x :: l) []⟩ : ACfg)) =
        some ⟨some (), (s.1 && aval x, true), ast l []⟩ := at_cons s x l []
    rw [e, ih]
    simp [Bool.and_assoc]

theorem at_run (l : List (Bool ⊕ Bool)) :
    (flip bind (TM2.step atProg))^[l.length + 1]
        (some (initList atM l)) = some (haltList atM [l.all aval]) := by
  refine (congrArg (fun c => (flip bind (TM2.step atProg))^[l.length + 1]
    (some c)) (initList_eq atM l)).trans
    (Eq.trans ?_ (congrArg some (haltList_eq atM [l.all aval])).symm)
  show (flip bind (TM2.step atProg))^[l.length + 1]
    (some (⟨some (), (true, false), Function.update (fun _ => []) false l⟩ : ACfg)) =
    some (⟨none, (true, false), Function.update (fun _ => []) true [l.all aval]⟩ : ACfg)
  rw [← ast_start, at_loop, ← ast_end]
  simp

theorem all_aval_encodePair (p : List Bool × List Bool) :
    (PEqualNP.Library.encodePair p).all aval = (p.1 ++ p.2).all id := by
  have h1 : ∀ l : List Bool, (l.map Sum.inl : List (Bool ⊕ Bool)).all aval = l.all id := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => simp [aval]
  have h2 : ∀ l : List Bool, (l.map Sum.inr : List (Bool ⊕ Bool)).all aval = l.all id := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => simp [aval]
  unfold PEqualNP.Library.encodePair
  rw [List.all_append, List.all_append, h1, h2]

/-- Whether every bit of both components of a pair is true is decidable in `n + 1` steps. -/
theorem allTrue_polyTime :
    Nonempty (Turing.TM2ComputableInPolyTime PEqualNP.Library.encodePair
      Computability.encodeBool
      (fun p : List Bool × List Bool => (p.1 ++ p.2).all id)) :=
  ⟨{
    tm := atM
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.X + 1
    outputsFun := fun p =>
      { steps := (PEqualNP.Library.encodePair p).length + 1
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have hout : [(PEqualNP.Library.encodePair p).all aval] =
              List.map (Equiv.refl Bool).invFun
                (Computability.encodeBool ((p.1 ++ p.2).all id)) := by
            rw [hm, all_aval_encodePair]
            rfl
          exact (congrArg (fun x => (flip bind (TM2.step atProg))^[
            (PEqualNP.Library.encodePair p).length + 1]
            (some (initList atM x))) (hm _ (PEqualNP.Library.encodePair p))).trans
            ((at_run (PEqualNP.Library.encodePair p)).trans
              (congrArg (fun x => some (haltList atM x)) hout))
        steps_le_m := by simp } }⟩

end PEqualNP.Library.Machines
