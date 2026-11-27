import PEqualNP.Library.Machines.Run
import PEqualNP.Library.Machines.Pairing

/-!
# A machine that mirrors every segment of a string

Helper module (proofs only, no statement may use it).

The alphabet `Γ` is any finite type, with a predicate `sep` naming the separators and a symbol
`m` (the middle mark). The string is cut at the separators; every segment `s` (separator free,
the last one possibly not followed by a separator) is replaced by `s.reverse ++ m :: s`, the
separators stay. Four stacks: input `I`, reversed input `R`, store `S`, output `O`.

1. `mv`: move the input onto `R` (now the last symbol is on top).
2. `rd`: pop `R`; a non-separator is pushed on `S` and on `O`; at a separator (or at the end)
   `m` is pushed on `O` and the store is flushed onto `O` (`fl`), then the separator is pushed.

The pushes on `O` come in the reverse order of the output, and the output stack lists its top
first, so the final output is in order.
-/

namespace PEqualNP.MetaComplexity.Helpers.MachinePrint

open Turing PEqualNP.Library PEqualNP.Library.Machines

namespace Mir

inductive MK : Type
  | I | R | S | O
  deriving DecidableEq

instance : Fintype MK :=
  Fintype.ofList [MK.I, MK.R, MK.S, MK.O] (fun x => by cases x <;> simp)

inductive ML : Type
  | mv | rd | fl
  deriving DecidableEq

instance : Fintype ML :=
  Fintype.ofList [ML.mv, ML.rd, ML.fl] (fun x => by cases x <;> simp)

variable {Γ : Type} (sep : Γ → Bool) (m : Γ)

abbrev MΓ (Γ : Type) : MK → Type := fun _ => Γ

abbrev Mσ (Γ : Type) : Type := Option Γ × Option Γ

def prog : ML → TM2.Stmt (MΓ Γ) ML (Mσ Γ)
  | .mv =>
    .pop .I (fun _ o => (o, none))
      (.branch (fun s => s.1.isSome)
        (.push .R (fun s => s.1.getD m) (.goto fun _ => .mv))
        (.goto fun _ => .rd))
  | .rd =>
    .pop .R (fun _ o => (o, none))
      (.branch (fun s => s.1.isSome)
        (.branch (fun s => sep (s.1.getD m))
          (.load (fun s => (none, s.1)) (.push .O (fun _ => m) (.goto fun _ => .fl)))
          (.push .S (fun s => s.1.getD m) (.push .O (fun s => s.1.getD m) (.goto fun _ => .rd))))
        (.push .O (fun _ => m) (.goto fun _ => .fl)))
  | .fl =>
    .pop .S (fun s o => (o, s.2))
      (.branch (fun s => s.1.isSome)
        (.push .O (fun s => s.1.getD m) (.goto fun _ => .fl))
        (.branch (fun s => s.2.isSome)
          (.push .O (fun s => s.2.getD m) (.load (fun _ => (none, none)) (.goto fun _ => .rd)))
          .halt))

def tm [Fintype Γ] : FinTM2 where
  K := MK
  k₀ := .I
  k₁ := .O
  Γ := MΓ Γ
  Λ := ML
  main := .mv
  σ := Mσ Γ
  initialState := (none, none)
  Γk₀Fin := inferInstanceAs (Fintype Γ)
  m := prog sep m

def lst (i r s o : List Γ) : ∀ k, List (MΓ Γ k)
  | .I => i
  | .R => r
  | .S => s
  | .O => o

section stackLemmas

variable (i i' r r' s s' o o' : List Γ)

theorem lst_set_I : Function.update (lst i r s o) .I i' = lst i' r s o := by
  funext k; cases k <;> simp [lst]
theorem lst_set_R : Function.update (lst i r s o) .R r' = lst i r' s o := by
  funext k; cases k <;> simp [lst]
theorem lst_set_S : Function.update (lst i r s o) .S s' = lst i r s' o := by
  funext k; cases k <;> simp [lst]
theorem lst_set_O : Function.update (lst i r s o) .O o' = lst i r s o' := by
  funext k; cases k <;> simp [lst]

theorem lst_start : lst i [] [] [] = Function.update (fun _ => [] : ∀ k, List (MΓ Γ k)) .I i := by
  funext k; cases k <;> simp [lst]

theorem lst_end : lst [] [] [] o = Function.update (fun _ => [] : ∀ k, List (MΓ Γ k)) .O o := by
  funext k; cases k <;> simp [lst]

end stackLemmas

abbrev MCfg (Γ : Type) : Type := TM2.Cfg (MΓ Γ) ML (Mσ Γ)

abbrev mStep : Option (MCfg Γ) → Option (MCfg Γ) := flip bind (TM2.step (prog sep m))

theorem chain {a b c : Option (MCfg Γ)} {p q : ℕ} (h1 : (mStep sep m)^[p] a = b)
    (h2 : (mStep sep m)^[q] b = c) : (mStep sep m)^[q + p] a = c := by
  rw [Function.iterate_add_apply, h1, h2]

section steps

variable (st : Mσ Γ) (i r s o : List Γ)

theorem mv_cons (x : Γ) :
    TM2.step (prog sep m) (⟨some .mv, st, lst (x :: i) r s o⟩ : MCfg Γ) =
      some ⟨some .mv, (some x, none), lst i (x :: r) s o⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  simp [lst, lst_set_I, lst_set_R]

theorem mv_nil :
    TM2.step (prog sep m) (⟨some .mv, st, lst [] r s o⟩ : MCfg Γ) =
      some ⟨some .rd, (none, none), lst [] r s o⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  simp [lst, lst_set_I]

theorem rd_nonsep (x : Γ) (hx : sep x = false) :
    TM2.step (prog sep m) (⟨some .rd, st, lst i (x :: r) s o⟩ : MCfg Γ) =
      some ⟨some .rd, (some x, none), lst i r (x :: s) (x :: o)⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  simp [lst, lst_set_R, lst_set_S, lst_set_O, hx]

theorem rd_sep (x : Γ) (hx : sep x = true) :
    TM2.step (prog sep m) (⟨some .rd, st, lst i (x :: r) s o⟩ : MCfg Γ) =
      some ⟨some .fl, (none, some x), lst i r s (m :: o)⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  simp [lst, lst_set_R, lst_set_O, hx]

theorem rd_nil :
    TM2.step (prog sep m) (⟨some .rd, st, lst i [] s o⟩ : MCfg Γ) =
      some ⟨some .fl, (none, none), lst i [] s (m :: o)⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  simp [lst, lst_set_R, lst_set_O]

theorem fl_cons (x : Γ) (sv : Option Γ) :
    TM2.step (prog sep m) (⟨some .fl, (st.1, sv), lst i r (x :: s) o⟩ : MCfg Γ) =
      some ⟨some .fl, (some x, sv), lst i r s (x :: o)⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  simp [lst, lst_set_S, lst_set_O]

theorem fl_nil_some (x : Γ) :
    TM2.step (prog sep m) (⟨some .fl, (st.1, some x), lst i r [] o⟩ : MCfg Γ) =
      some ⟨some .rd, (none, none), lst i r [] (x :: o)⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  simp [lst, lst_set_S, lst_set_O]

theorem fl_nil_none :
    TM2.step (prog sep m) (⟨some .fl, (st.1, none), lst i r [] o⟩ : MCfg Γ) =
      some ⟨none, (none, none), lst i r [] o⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  simp [lst, lst_set_S]

end steps

theorem mvLoop : ∀ (i r : List Γ) (st : Mσ Γ),
    (mStep sep m)^[i.length + 1] (some (⟨some .mv, st, lst i r [] []⟩ : MCfg Γ)) =
      some ⟨some .rd, (none, none), lst [] (i.reverse ++ r) [] []⟩ := by
  intro i
  induction i with
  | nil => intro r st; exact mv_nil sep m st r [] []
  | cons x i ih =>
    intro r st
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : mStep sep m (some (⟨some .mv, st, lst (x :: i) r [] []⟩ : MCfg Γ)) =
        some ⟨some .mv, (some x, none), lst i (x :: r) [] []⟩ := mv_cons sep m st i r [] [] x
    rw [e, ih]
    simp

theorem flLoop : ∀ (s r o : List Γ) (a : Option Γ) (sv : Option Γ),
    (mStep sep m)^[s.length] (some (⟨some .fl, (a, sv), lst [] r s o⟩ : MCfg Γ)) =
      some ⟨some .fl, ((s.getLast?).orElse (fun _ => a), sv), lst [] r [] (s.reverse ++ o)⟩ := by
  intro s
  induction s with
  | nil => intro r o a sv; simp
  | cons x s ih =>
    intro r o a sv
    rw [List.length_cons, Function.iterate_succ_apply]
    have e : mStep sep m (some (⟨some .fl, (a, sv), lst [] r (x :: s) o⟩ : MCfg Γ)) =
        some ⟨some .fl, (some x, sv), lst [] r s (x :: o)⟩ := fl_cons sep m (a, sv) [] r s o x sv
    rw [e, ih]
    congr 3
    · cases s <;> simp [List.getLast?_cons]
    · simp

/-- The output, in machine order: `S` the store, `y` the rest of `R`, `o` the output. -/
def mB : List Γ → List Γ → List Γ → List Γ
  | S, [], o => S.reverse ++ m :: o
  | S, x :: y, o => if sep x then mB [] y (x :: S.reverse ++ m :: o) else mB (x :: S) y (x :: o)

/-- The number of steps from `rd`. -/
def cB : List Γ → List Γ → ℕ
  | S, [] => S.length + 2
  | S, x :: y => if sep x then S.length + 2 + cB [] y else 1 + cB (x :: S) y

theorem cB_le : ∀ (y S : List Γ), cB sep S y ≤ 2 * y.length + S.length + 2 := by
  intro y
  induction y with
  | nil => intro S; simp [cB]
  | cons x y ih =>
    intro S
    simp only [cB]
    split
    · have := ih []; simp at this ⊢; omega
    · have := ih (x :: S); simp at this ⊢; omega

theorem rdLoop : ∀ (y S o : List Γ) (st : Mσ Γ),
    (mStep sep m)^[cB sep S y] (some (⟨some .rd, st, lst [] y S o⟩ : MCfg Γ)) =
      some ⟨none, (none, none), lst [] [] [] (mB sep m S y o)⟩ := by
  intro y
  induction y with
  | nil =>
    intro S o st
    simp only [cB, mB]
    rw [show S.length + 2 = (S.length + 1) + 1 by omega, Function.iterate_add_apply]
    have e : (mStep sep m)^[1] (some (⟨some .rd, st, lst [] [] S o⟩ : MCfg Γ)) =
        some ⟨some .fl, (none, none), lst [] [] S (m :: o)⟩ := rd_nil sep m st [] S o
    rw [e, Function.iterate_succ_apply', flLoop]
    exact fl_nil_none sep m (_, none) [] [] _
  | cons x y ih =>
    intro S o st
    simp only [cB, mB]
    cases hx : sep x
    · simp only [Bool.false_eq_true, if_false]
      rw [Nat.add_comm, Function.iterate_add_apply]
      have e : (mStep sep m)^[1] (some (⟨some .rd, st, lst [] (x :: y) S o⟩ : MCfg Γ)) =
          some ⟨some .rd, (some x, none), lst [] y (x :: S) (x :: o)⟩ :=
        rd_nonsep sep m st [] y S o x hx
      rw [e, ih]
    · simp only [if_true]
      rw [show S.length + 2 + cB sep [] y = cB sep [] y + ((S.length + 1) + 1) by omega,
        Function.iterate_add_apply, Function.iterate_add_apply]
      have e : (mStep sep m)^[1] (some (⟨some .rd, st, lst [] (x :: y) S o⟩ : MCfg Γ)) =
          some ⟨some .fl, (none, some x), lst [] y S (m :: o)⟩ := rd_sep sep m st [] y S o x hx
      rw [e, Function.iterate_succ_apply', flLoop]
      have e2 : mStep sep m (some (⟨some .fl, ((S.getLast?).orElse (fun _ => none), some x),
          lst [] y [] (S.reverse ++ m :: o)⟩ : MCfg Γ)) =
          some ⟨some .rd, (none, none), lst [] y [] (x :: (S.reverse ++ m :: o))⟩ :=
        fl_nil_some sep m (_, some x) [] y _ x
      rw [e2, ih]
      rfl

theorem mir_run [Fintype Γ] (w : List Γ) :
    ∃ n, n ≤ 3 * w.length + 3 ∧
      (mStep sep m)^[n] (some (initList (tm sep m) w)) =
        some (haltList (tm sep m) (mB sep m [] w.reverse [])) := by
  refine ⟨cB sep [] w.reverse + (w.length + 1), ?_, ?_⟩
  · have := cB_le sep w.reverse []
    simp at this
    omega
  · refine (congrArg (fun c => (mStep sep m)^[_] (some c)) (initList_eq (tm sep m) _)).trans
      (Eq.trans ?_ (congrArg some (haltList_eq (tm sep m) _)).symm)
    show (mStep sep m)^[_]
      (some (⟨some .mv, (none, none), Function.update (fun _ => []) MK.I w⟩ : MCfg Γ)) =
      some (⟨none, (none, none), Function.update (fun _ => []) MK.O _⟩ : MCfg Γ)
    rw [← lst_start]
    have h1 := mvLoop sep m w [] (none, none)
    rw [List.append_nil] at h1
    refine (chain sep m h1 (rdLoop sep m w.reverse [] [] (none, none))).trans ?_
    rw [lst_end]
    rfl

end Mir

open Mir in
/-- The segment mirror is computable in linear time. -/
theorem cpt_mir {Γ : Type} [Fintype Γ] (sep : Γ → Bool) (m : Γ) :
    ComputableInPolyTime (fun l : List Γ => l) (fun l : List Γ => l)
      (fun w : List Γ => mB sep m [] w.reverse []) :=
  ⟨{
    tm := tm sep m
    inputAlphabet := Equiv.refl _
    outputAlphabet := Equiv.refl _
    time := Polynomial.C 3 * Polynomial.X + Polynomial.C 3
    outputsFun := fun w =>
      { steps := Classical.choose (mir_run sep m w)
        evals_in_steps := by
          have hm : ∀ (γ : Type) (l : List γ), List.map (Equiv.refl γ).invFun l = l :=
            fun γ l => by simp
          exact (congrArg (fun x => (mStep sep m)^[Classical.choose (mir_run sep m w)]
            (some (initList (tm sep m) x))) (hm _ w)).trans
            ((Classical.choose_spec (mir_run sep m w)).2.trans
              (congrArg (fun x => some (haltList (tm sep m) x)) (hm _ _).symm))
        steps_le_m := by
          have h := (Classical.choose_spec (mir_run sep m w)).1
          simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_X]
          exact h } }⟩

/-! ## The output, segment by segment -/

/-- Segments with their separators, then a last segment. -/
def joinS {Γ : Type} (segs : List (List Γ × Γ)) (last : List Γ) : List Γ :=
  segs.flatMap (fun p => p.1 ++ [p.2]) ++ last

/-- One mirrored segment. -/
def mirSeg {Γ : Type} (m : Γ) (s : List Γ) : List Γ := s.reverse ++ m :: s

theorem joinS_snoc {Γ : Type} (segs : List (List Γ × Γ)) (s : List Γ) (x : Γ) (last : List Γ) :
    joinS (segs ++ [(s, x)]) last = joinS segs s ++ x :: last := by
  simp [joinS]

theorem mB_nonsep {Γ : Type} (sep : Γ → Bool) (m : Γ) : ∀ (u S rest o : List Γ),
    (∀ x ∈ u, sep x = false) →
      Mir.mB sep m S (u ++ rest) o = Mir.mB sep m (u.reverse ++ S) rest (u.reverse ++ o) := by
  intro u
  induction u with
  | nil => intro S rest o _; rfl
  | cons a u ih =>
    intro S rest o h
    have ha := h a (by simp)
    simp only [List.cons_append, Mir.mB, ha, Bool.false_eq_true, if_false]
    rw [ih _ _ _ (fun x hx => h x (by simp [hx]))]
    simp

theorem mB_joinS {Γ : Type} (sep : Γ → Bool) (m : Γ) : ∀ (segs : List (List Γ × Γ))
    (last o : List Γ),
    (∀ p ∈ segs, (∀ x ∈ p.1, sep x = false) ∧ sep p.2 = true) → (∀ x ∈ last, sep x = false) →
      Mir.mB sep m [] (joinS segs last).reverse o =
        joinS (segs.map (fun p => (mirSeg m p.1, p.2))) (mirSeg m last) ++ o := by
  intro segs
  induction segs using List.reverseRecOn with
  | nil =>
    intro last o _ hl
    simp only [joinS, List.flatMap_nil, List.nil_append, List.map_nil]
    have := mB_nonsep sep m last.reverse [] [] o (by simpa using hl)
    rw [List.append_nil] at this
    rw [this]
    simp [Mir.mB, mirSeg]
  | append_singleton segs p ih =>
    intro last o hs hl
    obtain ⟨s, x⟩ := p
    have hp := hs (s, x) (by simp)
    rw [joinS_snoc, List.reverse_append, List.reverse_cons, List.append_assoc]
    rw [mB_nonsep sep m last.reverse [] _ o (by simpa using hl)]
    simp only [List.reverse_reverse, List.append_nil, List.singleton_append, Mir.mB, hp.2,
      if_true, List.reverse_nil]
    rw [ih s _ (fun q hq => hs q (by simp [hq])) hp.1]
    simp [joinS, mirSeg]

/-- The segment mirror, segment by segment. -/
theorem cpt_mir_joinS {Γ : Type} [Fintype Γ] (sep : Γ → Bool) (m : Γ) :
    ComputableInPolyTime (fun l : List Γ => l) (fun l : List Γ => l)
      (fun w : List Γ => Mir.mB sep m [] w.reverse []) := cpt_mir sep m

end PEqualNP.MetaComplexity.Helpers.MachinePrint
