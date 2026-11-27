import PEqualNP.Library.Evasion.Plan
import PEqualNP.Library.Machines.Run

/-!
# T5b, the patch lemma

A machine `M` deciding `L` within `K * s n + K` steps is wrapped into a machine deciding `L`
within `t n` steps, with the constant `C0 = 1`.

In this model one step of a machine runs a whole labelled statement until a jump or a halt, and a
statement is a finite tree. The start statement of the wrapper pops up to `n0` input symbols,
branching on each bit, so the prefix read so far is kept in the tree and only one symbol in
transit is kept in the state. If the input ends first, the statement pushes the answer and halts:
one step in all. Otherwise it pushes the `n0` bits back, loads the initial state of `M` and jumps
to the start of `M`: one step, then the unchanged run of `M`.
-/

namespace PEqualNP.Library.Evasion

open Turing PEqualNP.Library.Machines

namespace Patch

variable (M : FinTM2)

/-- Labels of the wrapper: those of `M` and the start. -/
abbrev PΛ : Type := M.Λ ⊕ Unit

/-- Internal state of the wrapper: that of `M` and one input symbol in transit. -/
abbrev Pσ : Type := M.σ × Option (M.Γ M.k₀)

/-- The statements of the wrapper. -/
abbrev PStmt : Type := TM2.Stmt M.Γ (PΛ M) (Pσ M)

variable {M}

/-- A statement of `M` inside the wrapper. -/
def trP : TM2.Stmt M.Γ M.Λ M.σ → PStmt M
  | .push k f q => .push k (fun s => f s.1) (trP q)
  | .peek k f q => .peek k (fun s o => (f s.1 o, s.2)) (trP q)
  | .pop k f q => .pop k (fun s o => (f s.1 o, s.2)) (trP q)
  | .load a q => .load (fun s => (a s.1, s.2)) (trP q)
  | .branch f q₁ q₂ => .branch (fun s => f s.1) (trP q₁) (trP q₂)
  | .goto f => .goto (fun s => Sum.inl (f s.1))
  | .halt => .halt

variable (φ : M.Γ M.k₀ ≃ Bool)

/-- Push the bits of `l` on the input stack, the head of `l` ending on top, then run `q`. -/
def pb : List Bool → PStmt M → PStmt M
  | [], q => q
  | a :: l, q => pb l (.push M.k₀ (fun _ => φ.symm a) q)

variable (out : Bool → M.Γ M.k₁) (f : List Bool → Bool)

/-- Read up to `r` more symbols, `pre` being the bits read so far. -/
def rd : ℕ → List Bool → PStmt M
  | 0, pre => pb φ pre (.load (fun _ => (M.initialState, none)) (.goto fun _ => Sum.inl M.main))
  | r + 1, pre =>
    .pop M.k₀ (fun s o => (s.1, o))
      (.branch (fun s => s.2.isSome)
        (.branch (fun s => s.2.elim false φ)
          (rd r (pre ++ [true])) (rd r (pre ++ [false])))
        (.push M.k₁ (fun _ => out (f pre)) .halt))

/-- The program of the wrapper. -/
def prog (n0 : ℕ) : PΛ M → PStmt M
  | Sum.inl l => trP (M.m l)
  | Sum.inr () => rd φ out f n0 []

/-- The wrapper. -/
def wrap (n0 : ℕ) : FinTM2 :=
  haveI := M.kFin
  haveI := M.ΛFin
  haveI := M.σFin
  haveI := M.Γk₀Fin
  { K := M.K
    k₀ := M.k₀
    k₁ := M.k₁
    Γ := M.Γ
    Λ := PΛ M
    main := Sum.inr ()
    σ := Pσ M
    initialState := (M.initialState, none)
    Γk₀Fin := M.Γk₀Fin
    m := prog φ out f n0 }

/-- A configuration of `M` inside the wrapper. -/
def emb (c : TM2.Cfg M.Γ M.Λ M.σ) : TM2.Cfg M.Γ (PΛ M) (Pσ M) :=
  ⟨c.l.map Sum.inl, (c.var, none), c.stk⟩

theorem simP (q : TM2.Stmt M.Γ M.Λ M.σ) (v : M.σ) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (trP q) ((v, none) : Pσ M) S = emb (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih => exact ih _ _
  | load a q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [trP, TM2.stepAux]
    cases f v
    · exact ih₂ v S
    · exact ih₁ v S
  | goto f => rfl
  | halt => rfl

theorem stepP (n0 : ℕ) (c c' : TM2.Cfg M.Γ M.Λ M.σ) (h : TM2.step M.m c = some c') :
    TM2.step (prog φ out f n0) (emb c) = some (emb c') := by
  obtain ⟨l, v, S⟩ := c
  cases l with
  | none => simp [TM2.step] at h
  | some l =>
    simp only [TM2.step, Option.some.injEq] at h
    subst h
    exact congrArg some (simP (M.m l) v S)

theorem pb_run (l : List Bool) (q : PStmt M) (w : Pσ M) (S : ∀ k, List (M.Γ k)) :
    TM2.stepAux (pb φ l q) w S =
      TM2.stepAux q w (Function.update S M.k₀ (l.map φ.symm ++ S M.k₀)) := by
  induction l generalizing q S with
  | nil => simp [pb]
  | cons a l ih =>
    rw [pb, ih]
    simp [TM2.stepAux, Function.update_idem]

theorem rd_long (r : ℕ) : ∀ (pre x : List Bool) (w : Pσ M) (S : ∀ k, List (M.Γ k)),
    S M.k₀ = x.map φ.symm → r ≤ x.length →
    TM2.stepAux (rd φ out f r pre) w S =
      ⟨some (Sum.inl M.main), (M.initialState, none),
        Function.update S M.k₀ ((pre ++ x).map φ.symm)⟩ := by
  induction r with
  | zero =>
    intro pre x w S hS _
    rw [rd, pb_run]
    simp [TM2.stepAux, hS]
  | succ r ih =>
    intro pre x w S hS hr
    obtain _ | ⟨c, x⟩ := x
    · simp at hr
    · simp only [rd, TM2.stepAux, hS, List.map_cons, List.head?_cons, List.tail_cons,
        Option.isSome_some, Option.elim_some, Equiv.apply_symm_apply]
      have hS' : Function.update S M.k₀ (x.map φ.symm) M.k₀ = x.map φ.symm := by simp
      have hr' : r ≤ x.length := by simp at hr; omega
      cases c
      · simp only [Bool.cond_false]
        rw [ih _ x _ _ hS' hr', Function.update_idem]
        simp
      · simp only [Bool.cond_true]
        rw [ih _ x _ _ hS' hr', Function.update_idem]
        simp

theorem rd_short (r : ℕ) : ∀ (pre x : List Bool) (w : Pσ M) (S : ∀ k, List (M.Γ k)),
    S M.k₀ = x.map φ.symm → x.length < r →
    TM2.stepAux (rd φ out f r pre) w S =
      ⟨none, (w.1, none),
        Function.update (Function.update S M.k₀ []) M.k₁
          (out (f (pre ++ x)) :: Function.update S M.k₀ [] M.k₁)⟩ := by
  induction r with
  | zero => intro _ _ _ _ _ h; omega
  | succ r ih =>
    intro pre x w S hS hr
    obtain _ | ⟨c, x⟩ := x
    · simp [rd, TM2.stepAux, hS]
    · simp only [rd, TM2.stepAux, hS, List.map_cons, List.head?_cons, List.tail_cons,
        Option.isSome_some, Option.elim_some, Equiv.apply_symm_apply]
      have hS' : Function.update S M.k₀ (x.map φ.symm) M.k₀ = x.map φ.symm := by simp
      have hr' : x.length < r := by simp at hr; omega
      cases c
      · simp only [Bool.cond_false]
        rw [ih _ x _ _ hS' hr', Function.update_idem]
        simp
      · simp only [Bool.cond_true]
        rw [ih _ x _ _ hS' hr', Function.update_idem]
        simp

theorem wrap_run (ψ : M.Γ M.k₁ ≃ Bool) (n0 : ℕ) (x : List Bool) (T : ℕ)
    (hM : TM2OutputsInTime M (x.map φ.invFun) (some ([f x].map ψ.invFun)) T) :
    ∃ m, (flip bind (wrap φ ψ.symm f n0).step)^[m]
        (some (initList (wrap φ ψ.symm f n0) (x.map φ.invFun))) =
        some (haltList (wrap φ ψ.symm f n0) ([f x].map ψ.invFun)) ∧
      (x.length < n0 → m = 1) ∧ (n0 ≤ x.length → m ≤ T + 1) := by
  have hS0 : (Function.update (fun _ => []) M.k₀ (x.map φ.symm) : ∀ k, List (M.Γ k)) M.k₀ =
      x.map φ.symm := by simp
  have hi : initList (wrap φ ψ.symm f n0) (x.map φ.invFun) =
      ⟨some (Sum.inr ()), (M.initialState, none),
        Function.update (fun _ => []) M.k₀ (x.map φ.symm)⟩ := initList_eq _ _
  have hh : haltList (wrap φ ψ.symm f n0) ([f x].map ψ.invFun) =
      ⟨none, (M.initialState, none), Function.update (fun _ => []) M.k₁ [ψ.symm (f x)]⟩ :=
    haltList_eq _ _
  by_cases hx : x.length < n0
  · refine ⟨1, ?_, fun _ => rfl, fun h => absurd h (by omega)⟩
    rw [hi, hh]
    refine congrArg some ((rd_short φ ψ.symm f n0 [] x _ _ hS0 hx).trans ?_)
    simp [Function.update_idem]
    rfl
  · push Not at hx
    obtain ⟨⟨m, hm⟩, hmT⟩ := hM
    change m ≤ T at hmT
    refine ⟨m + 1, ?_, fun h => absurd hx (by omega), fun _ => by omega⟩
    rw [Function.iterate_succ_apply, hi, hh]
    have h1 : flip bind (wrap φ ψ.symm f n0).step (some ⟨some (Sum.inr ()), (M.initialState, none),
        Function.update (fun _ => []) M.k₀ (x.map φ.symm)⟩) =
        some (emb (initList M (x.map φ.invFun))) := by
      refine congrArg some ((rd_long φ ψ.symm f n0 [] x _ _ hS0 hx).trans ?_)
      rw [initList_eq]
      simp [emb, Function.update_idem]
    rw [h1]
    have h2 := simulate (TM2.step M.m) (TM2.step (prog φ ψ.symm f n0)) emb
      (stepP φ ψ.symm f n0) m _ _ hm
    refine h2.trans ?_
    rw [haltList_eq]
    rfl

end Patch

open Patch in
theorem t5b : StmtT5b := by
  refine ⟨1, ?_⟩
  intro L s t K hL ⟨n0, hn0⟩ hall
  obtain ⟨f, hf, c, hc⟩ := hL
  refine ⟨f, hf, ?_⟩
  have key : ∀ x : List Bool, ∃ m, (flip bind (wrap c.inputAlphabet c.outputAlphabet.symm f n0).step)^[m]
        (some (initList (wrap c.inputAlphabet c.outputAlphabet.symm f n0)
          (x.map c.inputAlphabet.invFun))) =
        some (haltList (wrap c.inputAlphabet c.outputAlphabet.symm f n0)
          ([f x].map c.outputAlphabet.invFun)) ∧ m ≤ t x.length := by
    intro x
    obtain ⟨m, hm, h1, h2⟩ := wrap_run c.inputAlphabet f c.outputAlphabet n0 x _ (c.outputsFun x)
    refine ⟨m, hm, ?_⟩
    by_cases hx : x.length < n0
    · have := hall x.length; rw [h1 hx]; omega
    · push Not at hx
      have := h2 hx
      have h3 : c.time x.length ≤ K * s x.length + K := hc x.length
      have h4 := hn0 x.length hx
      omega
  refine ⟨{ tm := wrap c.inputAlphabet c.outputAlphabet.symm f n0
            inputAlphabet := c.inputAlphabet
            outputAlphabet := c.outputAlphabet
            time := t
            outputsFun := fun x =>
              { steps := Classical.choose (key x)
                evals_in_steps := (Classical.choose_spec (key x)).1
                steps_le_m := (Classical.choose_spec (key x)).2 } }, fun n => le_rfl⟩

end PEqualNP.Library.Evasion
