import PEqualNP.Library.Evasion.RungPlan
import PEqualNP.Library.Machines.Transducer

/-!
# Evasion chain: the inner encoding `E` and its reader `D` (piece `StmtED`)

Both maps are outputs of finite-state transducers (`Machines/Transducer.lean`), so each is
computed in `2 * n + 3` steps.

* `E (s, y) = 1^k 0 (1 b₁) (1 b₂) ... (1 bₘ) 0 y` when `s = 1^k 0 b₁ ... bₘ`: the leading
  `true`s of `s` and its first `false` are copied, every later bit of `s` is preceded by the
  marker `true`, and the marker `false` ends `s`. At most two output symbols per input symbol
  and one at the end, so `|E p| ≤ 2 (|p.1| + |p.2|) + 1`.
* `D (e, w)` reads `e` back as `(s, y)` and returns `(s, y ++ w)`; one output symbol per input
  symbol at most, so it does not lengthen the pair.
-/

namespace PEqualNP.Library.Evasion

open Turing PEqualNP.Library.Machines

/-! ## A timed transducer machine -/

/-- `fst2_polyTime` with the explicit bound `2 * n + 3`. -/
theorem fst2_time_ed {α β αΓ βΓ Q : Type} [Fintype αΓ] [Fintype Q] (ea : α → List αΓ)
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
        steps_le_m := by
          show _ ≤ 2 * (ea a).length + 3
          omega } }, fun _ => le_rfl⟩

theorem fstRun2_length_le {Γ₀ Γ₁ Q : Type} (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁)
    (fin : Q → Option Γ₁) (q : Q) (l : List Γ₀) :
    (fstRun2 δ fin q l).length ≤ 2 * l.length + 1 := by
  induction l generalizing q with
  | nil =>
    simp only [fstRun2]
    cases fin q <;> simp
  | cons a l ih =>
    simp only [fstRun2, List.length_append, List.length_cons]
    have h1 : ((δ q a).2.1.toList).length ≤ 1 := by cases (δ q a).2.1 <;> simp
    have h2 : ((δ q a).2.2.toList).length ≤ 1 := by cases (δ q a).2.2 <;> simp
    have := ih (δ q a).1
    omega

theorem fstRun2_length_le_one {Γ₀ Γ₁ Q : Type} (δ : Q → Γ₀ → Q × Option Γ₁ × Option Γ₁)
    (hδ : ∀ q a, (δ q a).2.2 = none) (q : Q) (l : List Γ₀) :
    (fstRun2 δ (fun _ => none) q l).length ≤ l.length := by
  induction l generalizing q with
  | nil => simp [fstRun2]
  | cons a l ih =>
    simp only [fstRun2, List.length_append, List.length_cons, hδ, Option.toList_none,
      List.length_nil, Nat.add_zero]
    have h1 : ((δ q a).2.1.toList).length ≤ 1 := by cases (δ q a).2.1 <;> simp
    have := ih (δ q a).1
    omega

/-! ## The encoder -/

/-- States of the encoder: in the leading `true`s, in the rest of `s`, in `y`. -/
inductive QE | L | B | Y
  deriving DecidableEq

instance : Fintype QE :=
  Fintype.ofList [.L, .B, .Y] (fun x => by cases x <;> simp)

/-- The encoder's step. -/
def δE : QE → Bool ⊕ Bool → QE × Option Bool × Option Bool
  | .L, .inl true => (.L, some true, none)
  | .L, .inl false => (.B, some false, none)
  | .B, .inl b => (.B, some true, some b)
  | .Y, .inl _ => (.Y, none, none)
  | .Y, .inr b => (.Y, some b, none)
  | _, .inr b => (.Y, some false, some b)

/-- The encoder's last symbol. -/
def finE : QE → Option Bool
  | .Y => none
  | _ => some false

/-- The inner encoding. -/
def encE (p : List Bool × List Bool) : List Bool :=
  fstRun2 δE finE .L (PEqualNP.Library.encodePair p)

/-- The body of `s` with a marker `true` before every bit. -/
def dbl (l : List Bool) : List Bool := l.flatMap (fun b => [true, b])

theorem runE_Y (y : List Bool) : fstRun2 δE finE .Y (y.map Sum.inr) = y := by
  induction y with
  | nil => rfl
  | cons b y ih => simpa [fstRun2, δE] using ih

theorem runE_B (body y : List Bool) :
    fstRun2 δE finE .B (body.map Sum.inl ++ y.map Sum.inr) = dbl body ++ false :: y := by
  induction body with
  | nil =>
    cases y with
    | nil => rfl
    | cons b y => simp [fstRun2, δE, runE_Y, dbl]
  | cons b body ih => simp [fstRun2, δE, ih, dbl]

/-! ## The reader -/

/-- States of the reader: in the leading `true`s, at a marker, at a bit, in `y`. -/
inductive QD | L | B | Bb | Y
  deriving DecidableEq

instance : Fintype QD :=
  Fintype.ofList [.L, .B, .Bb, .Y] (fun x => by cases x <;> simp)

/-- The reader's step. -/
def δD : QD → Bool ⊕ Bool → QD × Option (Bool ⊕ Bool) × Option (Bool ⊕ Bool)
  | .L, .inl true => (.L, some (.inl true), none)
  | .L, .inl false => (.B, some (.inl false), none)
  | .B, .inl true => (.Bb, none, none)
  | .B, .inl false => (.Y, none, none)
  | .Bb, .inl b => (.B, some (.inl b), none)
  | .Y, .inl b => (.Y, some (.inr b), none)
  | _, .inr b => (.Y, some (.inr b), none)

/-- What the reader makes of the first component, from a state. -/
def decD : QD → List Bool → List Bool × List Bool
  | .Y, e => ([], e)
  | _, [] => ([], [])
  | .L, true :: e => (true :: (decD .L e).1, (decD .L e).2)
  | .L, false :: e => (false :: (decD .B e).1, (decD .B e).2)
  | .B, true :: e => decD .Bb e
  | .B, false :: e => decD .Y e
  | .Bb, b :: e => (b :: (decD .B e).1, (decD .B e).2)

/-- The reader. -/
def decodeD (p : List Bool × List Bool) : List Bool × List Bool :=
  ((decD .L p.1).1, (decD .L p.1).2 ++ p.2)

theorem runD_w (q : QD) (w : List Bool) :
    fstRun2 δD (fun _ => none) q (w.map Sum.inr) = w.map Sum.inr := by
  induction w generalizing q with
  | nil => rfl
  | cons b w ih => cases q <;> simp [fstRun2, δD, ih]

theorem runD_Y (e w : List Bool) :
    fstRun2 δD (fun _ => none) .Y (e.map Sum.inl ++ w.map Sum.inr) =
      e.map Sum.inr ++ w.map Sum.inr := by
  induction e with
  | nil => simpa using runD_w .Y w
  | cons b e ih => simp [fstRun2, δD, ih]

theorem runD (q : QD) (e w : List Bool) :
    fstRun2 δD (fun _ => none) q (e.map Sum.inl ++ w.map Sum.inr) =
      PEqualNP.Library.encodePair ((decD q e).1, (decD q e).2 ++ w) := by
  induction e generalizing q with
  | nil =>
    cases q <;> simpa [decD, PEqualNP.Library.encodePair] using runD_w _ w
  | cons b e ih =>
    cases q with
    | Y => simpa [decD, PEqualNP.Library.encodePair] using runD_Y (b :: e) w
    | L => cases b <;> simp [fstRun2, δD, decD, ih, PEqualNP.Library.encodePair]
    | B => cases b <;> simp [fstRun2, δD, decD, ih, PEqualNP.Library.encodePair]
    | Bb => simp [fstRun2, δD, decD, ih, PEqualNP.Library.encodePair]

theorem runD_pair (p : List Bool × List Bool) :
    PEqualNP.Library.encodePair (decodeD p) =
      fstRun2 δD (fun _ => none) .L (PEqualNP.Library.encodePair p) :=
  (runD .L p.1 p.2).symm

theorem decD_B (body y : List Bool) : decD .B (dbl body ++ false :: y) = (body, y) := by
  induction body with
  | nil => simp [dbl, decD]
  | cons b body ih =>
    simp only [dbl, List.flatMap_cons, List.cons_append, List.nil_append] at ih ⊢
    simp [decD, ih]

/-! ## The properties on inputs with a `false` -/

theorem encE_props (y : List Bool) : ∀ s : List Bool, false ∈ s →
    lead (encE (s, y)) = lead s ∧ false ∈ encE (s, y) ∧ decD .L (encE (s, y)) = (s, y)
  | [], h => by simp at h
  | true :: s, h => by
    have h' : false ∈ s := by simpa using h
    obtain ⟨h1, h2, h3⟩ := encE_props y s h'
    have e : encE (true :: s, y) = true :: encE (s, y) := by
      simp [encE, PEqualNP.Library.encodePair, fstRun2, δE]
    rw [e]
    refine ⟨?_, by simp [h2], ?_⟩
    · simpa [lead] using h1
    · simp [decD, h3]
  | false :: body, _ => by
    have e : encE (false :: body, y) = false :: (dbl body ++ false :: y) := by
      simp [encE, PEqualNP.Library.encodePair, fstRun2, δE, runE_B]
    rw [e]
    refine ⟨by simp [lead], by simp, ?_⟩
    simp [decD, decD_B]

/-! ## The piece -/

theorem ed : StmtED := by
  refine ⟨encE, decodeD, 3, ?_, ?_, ?_, ?_, ?_⟩
  · exact time_mono (fst2_time_ed _ _ _ δE finE .L (fun _ => rfl)) fun n => by omega
  · exact time_mono (fst2_time_ed _ _ _ δD (fun _ => none) .L runD_pair) fun n => by omega
  · intro p
    have := fstRun2_length_le δE finE .L (PEqualNP.Library.encodePair p)
    simpa [encE, PEqualNP.Library.encodePair] using this
  · intro p
    rw [runD_pair]
    exact fstRun2_length_le_one δD (fun q a => by cases q <;> cases a <;>
      (rename_i b; cases b <;> rfl)) .L _
  · intro s y w h
    obtain ⟨h1, h2, h3⟩ := encE_props y s h
    refine ⟨h1, h2, ?_⟩
    simp [decodeD, h3]

end PEqualNP.Library.Evasion
