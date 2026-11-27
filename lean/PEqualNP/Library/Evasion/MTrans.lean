import PEqualNP.Library.Evasion.RungPlan
import PEqualNP.Library.Evasion.Clock
import PEqualNP.Library.Machines.Transducer

/-!
# Evasion chain: the two symbol-level transducers of note 209 (M5, M6)

* `toPairBody : StmtToPairBody`: `s ↦ (s, [])` by the two-pass machine, and
  `(s, w) ↦ (body s, w)` by a two-state finite transducer.
* `fixLead : StmtFixLead`: `(s, w) ↦ (s, fixLen (lead s) w)` by a hand-built machine with a
  unary counter stack, within `4 * n + 4` steps.
-/

namespace PEqualNP.Library.Evasion

open Turing PEqualNP.Library.Machines

/-- A finite-state transducer with an explicit linear time bound. -/
theorem fst2_time {α β αΓ βΓ Q : Type} [Fintype αΓ] [Fintype Q] (ea : α → List αΓ)
    (eb : β → List βΓ) (f : α → β) (δ : Q → αΓ → Q × Option βΓ × Option βΓ)
    (fin : Q → Option βΓ) (q₀ : Q) (y : βΓ) (h : ∀ a, eb (f a) = fstRun2 δ fin q₀ (ea a)) :
    PEqualNP.Library.ComputableInTime ea eb f (fun n => 2 * n + 3) := by
  have hd : ∀ _ : βΓ, (some y : Option βΓ) ≠ none := fun _ => by simp
  exact ⟨{
    tm := trM δ fin q₀ (some y)
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := fun n => 2 * n + 3
    outputsFun := fun a =>
      { steps := (ea a).length + 1 + 1 + ((ea a).length + 1)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          have := trM_run δ fin q₀ (some y) hd (ea a)
          exact (congrArg (fun l => (flip bind (TM2.step (trProg δ fin q₀ (some y))))^[(ea a).length +
            1 + 1 + ((ea a).length + 1)] (some (initList (trM δ fin q₀ (some y)) l)))
            (hm αΓ (ea a))).trans
            (this.trans (congrArg (fun l => some (haltList (trM δ fin q₀ (some y)) l))
              ((h a).symm.trans (hm βΓ (eb (f a))).symm)))
        steps_le_m := by
          show _ ≤ 2 * (ea a).length + 3
          omega } }, fun _ => le_rfl⟩

/-! ## M6: the two fixed transducers -/

/-- Drop the leading `inl true` symbols and the first `inl false`, copy the rest. -/
def bδ : Bool → Bool ⊕ Bool → Bool × Option (Bool ⊕ Bool) × Option (Bool ⊕ Bool)
  | true, Sum.inl true => (true, none, none)
  | true, Sum.inl false => (false, none, none)
  | true, Sum.inr b => (false, some (Sum.inr b), none)
  | false, x => (false, some x, none)

theorem bδ_false (l : List (Bool ⊕ Bool)) : fstRun2 bδ (fun _ => none) false l = l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [fstRun2, bδ, ih]

theorem bδ_run (s w : List Bool) :
    fstRun2 bδ (fun _ => none) true (PEqualNP.Library.encodePair (s, w)) =
      PEqualNP.Library.encodePair (body s, w) := by
  induction s with
  | nil =>
    cases w with
    | nil => rfl
    | cons b w => simp [PEqualNP.Library.encodePair, fstRun2, bδ, bδ_false, body]
  | cons b s ih =>
    cases b
    · simp [PEqualNP.Library.encodePair, fstRun2, bδ, bδ_false, body]
    · simpa [PEqualNP.Library.encodePair, fstRun2, bδ, body] using ih

theorem toPairBody : StmtToPairBody := by
  refine ⟨4, ?_, ?_⟩
  · exact tp_time _ _ _ (fun b => some (Sum.inl b)) (fun _ => none) (Sum.inl true)
      (fun x => by simp [PEqualNP.Library.encodePair])
  · exact time_mono (fst2_time _ _ _ bδ (fun _ => none) true (Sum.inl true)
      (fun p => (bδ_run p.1 p.2).symm)) (fun n => by omega)

/-! ## M5: cut or pad the witness to the number of leading trues -/

namespace FixLead

/-- Stacks: input, unary counter, reversed output, output. -/
inductive Kk : Type
  | inp | cnt | tmp | out
  deriving DecidableEq

instance : Fintype Kk :=
  Fintype.ofList [.inp, .cnt, .tmp, .out] (fun x => by cases x <;> simp)

/-- Labels: copy `s` and count (A), copy the cut or padded `w` (B), discard (C), reverse (D). -/
inductive Lb : Type
  | A | B | C | D
  deriving DecidableEq

instance : Fintype Lb :=
  Fintype.ofList [.A, .B, .C, .D] (fun x => by cases x <;> simp)

/-- The stack symbols. -/
abbrev G : Type := Bool ⊕ Bool

/-- Internal state: a flag and one symbol in transit. -/
abbrev S : Type := Bool × Option G

def isInl : S → Bool
  | (_, some (Sum.inl _)) => true
  | _ => false

def isT : S → Bool
  | (fl, some (Sum.inl b)) => fl && b
  | _ => false

def prog : Lb → TM2.Stmt (fun _ : Kk => G) Lb S
  | .A => .pop .inp (fun s o => (s.1, o))
      (.branch isInl
        (.push .tmp (fun s => s.2.getD (Sum.inl false))
          (.branch isT
            (.push .cnt (fun _ => Sum.inl true)
              (.load (fun s => (isT s, none)) (.goto fun _ => .A)))
            (.load (fun s => (isT s, none)) (.goto fun _ => .A))))
        (.goto fun _ => .B))
  | .B => .pop .cnt (fun s c => (c.isSome, s.2))
      (.branch (fun s => s.1)
        (.branch (fun s => s.2.isSome)
          (.push .tmp (fun s => s.2.getD (Sum.inr false))
            (.pop .inp (fun s o => (s.1, o)) (.goto fun _ => .B)))
          (.push .tmp (fun _ => Sum.inr false) (.goto fun _ => .B)))
        (.goto fun _ => .C))
  | .C => .pop .inp (fun _ o => (o.isSome, none))
      (.branch (fun s => s.1) (.goto fun _ => .C) (.goto fun _ => .D))
  | .D => .pop .tmp (fun _ o => (o.isSome, o))
      (.branch (fun s => s.1)
        (.push .out (fun s => s.2.getD (Sum.inl false)) (.goto fun _ => .D))
        (.load (fun _ => (true, none)) .halt))

def tm : FinTM2 where
  K := Kk
  k₀ := .inp
  k₁ := .out
  Γ := fun _ => G
  Λ := Lb
  main := .A
  σ := S
  initialState := (true, none)
  Γk₀Fin := inferInstanceAs (Fintype (Bool ⊕ Bool))
  m := prog

def st (i c t o : List G) : ∀ _ : Kk, List G
  | .inp => i
  | .cnt => c
  | .tmp => t
  | .out => o

theorem st_set_inp (i i' c t o : List G) :
    Function.update (st i c t o) .inp i' = st i' c t o := by
  funext k; cases k <;> simp [st]

theorem st_set_cnt (i c c' t o : List G) :
    Function.update (st i c t o) .cnt c' = st i c' t o := by
  funext k; cases k <;> simp [st]

theorem st_set_tmp (i c t t' o : List G) :
    Function.update (st i c t o) .tmp t' = st i c t' o := by
  funext k; cases k <;> simp [st]

theorem st_set_out (i c t o o' : List G) :
    Function.update (st i c t o) .out o' = st i c t o' := by
  funext k; cases k <;> simp [st]

abbrev Cfg : Type := TM2.Cfg (fun _ : Kk => G) Lb S

/-- Counter pushes during A. -/
def cA : Bool → List Bool → ℕ
  | _, [] => 0
  | fl, b :: s => (if (fl && b) = true then 1 else 0) + cA (fl && b) s

/-- Flag after A. -/
def fA : Bool → List Bool → Bool
  | fl, [] => fl
  | fl, b :: s => fA (fl && b) s

theorem cA_false (s : List Bool) : cA false s = 0 := by
  induction s with
  | nil => rfl
  | cons b s ih => simp [cA, ih]

theorem cA_true (s : List Bool) : cA true s = lead s := by
  induction s with
  | nil => rfl
  | cons b s ih =>
    cases b
    · simp [cA, cA_false, lead]
    · simp [cA, ih, lead]; omega

theorem fixLen_succ_nil (k : ℕ) : fixLen (k + 1) [] = false :: fixLen k [] := by
  simp [fixLen, List.replicate_succ, List.take_replicate]

theorem fixLen_succ_cons (k : ℕ) (b : Bool) (w : List Bool) :
    fixLen (k + 1) (b :: w) = b :: fixLen k w := by
  simp only [fixLen, List.cons_append, List.take_succ_cons, List.cons.injEq, true_and,
    List.take_append, List.take_replicate]
  congr 2
  omega

theorem stepA_inl (fl b : Bool) (x : Option G) (i c t o : List G) :
    TM2.step prog (⟨some .A, (fl, x), st (Sum.inl b :: i) c t o⟩ : Cfg) =
      some ⟨some .A, (fl && b, none),
        st i (List.replicate (if (fl && b) = true then 1 else 0) (Sum.inl true) ++ c)
          (Sum.inl b :: t) o⟩ := by
  cases fl <;> cases b <;>
    simp [TM2.step, prog, TM2.stepAux, st, st_set_inp, st_set_cnt, st_set_tmp, isInl, isT]

theorem stepA_end (fl : Bool) (x : Option G) (w : List Bool) (c t o : List G) :
    TM2.step prog (⟨some .A, (fl, x), st (w.map Sum.inr) c t o⟩ : Cfg) =
      some ⟨some .B, (fl, w.head?.map Sum.inr), st (w.tail.map Sum.inr) c t o⟩ := by
  cases w <;> simp [TM2.step, prog, TM2.stepAux, st, st_set_inp, isInl]

theorem loopA (w : List Bool) (o : List G) :
    ∀ (s : List Bool) (fl : Bool) (x : Option G) (c t : List G),
      (flip bind (TM2.step prog))^[s.length + 1]
          (some (⟨some .A, (fl, x), st (s.map Sum.inl ++ w.map Sum.inr) c t o⟩ : Cfg)) =
        some ⟨some .B, (fA fl s, w.head?.map Sum.inr),
          st (w.tail.map Sum.inr) (List.replicate (cA fl s) (Sum.inl true) ++ c)
            ((s.map Sum.inl).reverse ++ t) o⟩ := by
  intro s
  induction s with
  | nil =>
    intro fl x c t
    exact stepA_end fl x w c t o
  | cons b s ih =>
    intro fl x c t
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step prog)
        (some (⟨some .A, (fl, x), st ((b :: s).map Sum.inl ++ w.map Sum.inr) c t o⟩ : Cfg)) =
        some ⟨some .A, (fl && b, none),
          st (s.map Sum.inl ++ w.map Sum.inr)
            (List.replicate (if (fl && b) = true then 1 else 0) (Sum.inl true) ++ c)
            (Sum.inl b :: t) o⟩ :=
      stepA_inl fl b x _ c t o
    rw [e, ih]
    have hc : cA fl (b :: s) = cA (fl && b) s + (if (fl && b) = true then 1 else 0) := by
      rw [cA, Nat.add_comm]
    rw [hc, List.replicate_add, List.append_assoc]
    simp only [fA, List.map_cons, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append]

theorem stepB_nil (y : Bool) (k : ℕ) (t o : List G) :
    TM2.step prog (⟨some .B, (y, none), st [] (Sum.inl true :: List.replicate k (Sum.inl true))
      t o⟩ : Cfg) =
      some ⟨some .B, (true, none), st [] (List.replicate k (Sum.inl true))
        (Sum.inr false :: t) o⟩ := by
  simp [TM2.step, prog, TM2.stepAux, st, st_set_cnt, st_set_tmp]

theorem stepB_cons (y b : Bool) (w : List Bool) (k : ℕ) (t o : List G) :
    TM2.step prog (⟨some .B, (y, some (Sum.inr b)),
      st (w.map Sum.inr) (Sum.inl true :: List.replicate k (Sum.inl true)) t o⟩ : Cfg) =
      some ⟨some .B, (true, w.head?.map Sum.inr), st (w.tail.map Sum.inr)
        (List.replicate k (Sum.inl true)) (Sum.inr b :: t) o⟩ := by
  cases w <;> simp [TM2.step, prog, TM2.stepAux, st, st_set_cnt, st_set_tmp, st_set_inp]

theorem stepB_end (y : Bool) (x : Option G) (i t o : List G) :
    TM2.step prog (⟨some .B, (y, x), st i [] t o⟩ : Cfg) =
      some ⟨some .C, (false, x), st i [] t o⟩ := by
  simp [TM2.step, prog, TM2.stepAux, st, st_set_cnt]

theorem loopB (o : List G) :
    ∀ (k : ℕ) (w : List Bool) (y : Bool) (t : List G),
      (flip bind (TM2.step prog))^[k + 1]
          (some (⟨some .B, (y, w.head?.map Sum.inr),
            st (w.tail.map Sum.inr) (List.replicate k (Sum.inl true)) t o⟩ : Cfg)) =
        some ⟨some .C, (false, (w.drop k).head?.map Sum.inr),
          st ((w.drop k).tail.map Sum.inr) [] (((fixLen k w).map Sum.inr).reverse ++ t) o⟩ := by
  intro k
  induction k with
  | zero =>
    intro w y t
    have h0 : fixLen 0 w = [] := by simp [fixLen]
    rw [h0]
    simp only [List.drop_zero, List.replicate_zero, List.map_nil, List.reverse_nil,
      List.nil_append]
    exact stepB_end y (w.head?.map Sum.inr) (w.tail.map Sum.inr) t o
  | succ k ih =>
    intro w y t
    rw [Function.iterate_succ_apply, List.replicate_succ]
    cases w with
    | nil =>
      have e : flip bind (TM2.step prog) (some (⟨some .B, (y, none),
          st [] (Sum.inl true :: List.replicate k (Sum.inl true)) t o⟩ : Cfg)) =
          some ⟨some .B, (true, none), st [] (List.replicate k (Sum.inl true))
            (Sum.inr false :: t) o⟩ := stepB_nil y k t o
      simp only [List.head?_nil, Option.map_none, List.tail_nil, List.map_nil]
      rw [e]
      have := ih [] true (Sum.inr false :: t)
      simp only [List.head?_nil, Option.map_none, List.tail_nil, List.map_nil] at this
      rw [this, fixLen_succ_nil]
      simp
    | cons b w =>
      have e : flip bind (TM2.step prog) (some (⟨some .B, (y, some (Sum.inr b)),
          st (w.map Sum.inr) (Sum.inl true :: List.replicate k (Sum.inl true)) t o⟩ : Cfg)) =
          some ⟨some .B, (true, w.head?.map Sum.inr), st (w.tail.map Sum.inr)
            (List.replicate k (Sum.inl true)) (Sum.inr b :: t) o⟩ := stepB_cons y b w k t o
      simp only [List.head?_cons, Option.map_some, List.tail_cons]
      rw [e]
      rw [ih w true (Sum.inr b :: t), fixLen_succ_cons]
      simp

theorem loopC (o t : List G) :
    ∀ (R : List G) (y : S),
      (flip bind (TM2.step prog))^[R.length + 1] (some (⟨some .C, y, st R [] t o⟩ : Cfg)) =
        some ⟨some .D, (false, none), st [] [] t o⟩ := by
  intro R
  induction R with
  | nil =>
    intro y
    show TM2.step prog ⟨some .C, y, st [] [] t o⟩ = _
    simp [TM2.step, prog, TM2.stepAux, st, st_set_inp]
  | cons a R ih =>
    intro y
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step prog) (some (⟨some .C, y, st (a :: R) [] t o⟩ : Cfg)) =
        some ⟨some .C, (true, none), st R [] t o⟩ := by
      simp [flip, TM2.step, prog, TM2.stepAux, st, st_set_inp]
    rw [e, ih]

theorem loopD :
    ∀ (t u : List G) (y : S),
      (flip bind (TM2.step prog))^[t.length + 1] (some (⟨some .D, y, st [] [] t u⟩ : Cfg)) =
        some ⟨none, (true, none), st [] [] [] (t.reverse ++ u)⟩ := by
  intro t
  induction t with
  | nil =>
    intro u y
    show TM2.step prog ⟨some .D, y, st [] [] [] u⟩ = _
    simp [TM2.step, prog, TM2.stepAux, st, st_set_tmp]
  | cons a t ih =>
    intro u y
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : flip bind (TM2.step prog) (some (⟨some .D, y, st [] [] (a :: t) u⟩ : Cfg)) =
        some ⟨some .D, (true, some a), st [] [] t (a :: u)⟩ := by
      simp [flip, TM2.step, prog, TM2.stepAux, st, st_set_tmp, st_set_out]
    rw [e, ih]
    simp

theorem st_start (l : List G) :
    st l [] [] [] = Function.update (fun _ => ([] : List G)) Kk.inp l := by
  funext k; cases k <;> simp [st]

theorem st_end (u : List G) :
    st [] [] [] u = Function.update (fun _ => ([] : List G)) Kk.out u := by
  funext k; cases k <;> simp [st]

/-- The number of steps on `(s, w)`. -/
def steps (s w : List Bool) : ℕ :=
  (lead s + s.length + 1) + (((w.drop (lead s)).tail.length + 1) + ((lead s + 1) + (s.length + 1)))

theorem run (s w : List Bool) :
    (flip bind (TM2.step prog))^[steps s w]
        (some (initList tm (PEqualNP.Library.encodePair (s, w)))) =
      some (haltList tm (PEqualNP.Library.encodePair (s, fixLen (lead s) w))) := by
  have h1 : initList tm (PEqualNP.Library.encodePair (s, w)) =
      (⟨some .A, (true, none), Function.update (fun _ => ([] : List G)) Kk.inp
        (s.map Sum.inl ++ w.map Sum.inr)⟩ : Cfg) := initList_eq tm _
  have h2 : haltList tm (PEqualNP.Library.encodePair (s, fixLen (lead s) w)) =
      (⟨none, (true, none), Function.update (fun _ => ([] : List G)) Kk.out
        (s.map Sum.inl ++ (fixLen (lead s) w).map Sum.inr)⟩ : Cfg) := haltList_eq tm _
  rw [h1, h2]
  show (flip bind (TM2.step prog))^[steps s w]
      (some (⟨some .A, (true, none), Function.update (fun _ => ([] : List G)) Kk.inp
        (s.map Sum.inl ++ w.map Sum.inr)⟩ : Cfg)) =
    some (⟨none, (true, none), Function.update (fun _ => ([] : List G)) Kk.out
        (s.map Sum.inl ++ (fixLen (lead s) w).map Sum.inr)⟩ : Cfg)
  rw [← st_start, ← st_end, steps, Function.iterate_add_apply _ (lead s + s.length + 1),
    Function.iterate_add_apply _ ((w.drop (lead s)).tail.length + 1),
    Function.iterate_add_apply _ (lead s + 1), loopA w [] s true none [] [], cA_true]
  simp only [List.append_nil]
  rw [loopB [] (lead s) w (fA true s),
    show ((w.drop (lead s)).tail).length = ((w.drop (lead s)).tail.map (Sum.inr : Bool → G)).length
      by simp, loopC]
  have hD := loopD (((fixLen (lead s) w).map Sum.inr).reverse ++ (s.map Sum.inl).reverse) []
    (false, none)
  simp only [List.length_append, List.length_reverse, List.length_map, fixLen_length,
    List.reverse_append, List.reverse_reverse, List.append_nil] at hD
  rw [hD]

end FixLead

theorem fixLead : StmtFixLead := by
  refine ⟨4, ⟨{
    tm := FixLead.tm
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := fun n => 4 * n + 4
    outputsFun := fun p =>
      { steps := FixLead.steps p.1 p.2
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun l => (flip bind (TM2.step FixLead.prog))^[FixLead.steps p.1 p.2]
            (some (initList FixLead.tm l))) (hm _ (PEqualNP.Library.encodePair p))).trans
            ((FixLead.run p.1 p.2).trans (congrArg (fun l => some (haltList FixLead.tm l))
              (hm _ _).symm))
        steps_le_m := by
          show _ ≤ 4 * (PEqualNP.Library.encodePair p).length + 4
          have h1 := lead_le p.1
          have h2 : (p.2.drop (lead p.1)).tail.length ≤ p.2.length := by
            simp
          simp only [FixLead.steps, PEqualNP.Library.encodePair, List.length_append,
            List.length_map]
          omega } }, fun _ => le_rfl⟩⟩

end PEqualNP.Library.Evasion
