import PEqualNP.Library.Helpers.TableauExpr
import PEqualNP.Library.Helpers.TableauMachine

/-!
# Configurations of a stack machine as bit vectors

Helper module (proofs only, no statement may use it).

A configuration whose symbols lie in a finite set `T` and whose stacks hold at most `H` symbols
is written as bits (`enc`): one bit per label and per internal state (one-hot), and for each
stack and each of `H` cells (counted from the bottom) one bit per symbol of `T`, plus a bit
saying whether the cell is below the height. `wenc` writes the label, the state and the top `d`
symbols of each stack (the window). `locenc` adds, for one cell, its old content and the height
of its stack relative to the cell, clamped. The new value of each bit after a step is
determined by the window (label and state bits) or by the local bits (cell bits).
-/

open Turing

namespace PEqualNP.Library.Helpers.Tableau

open PEqualNP.Library.Helpers.Enum
open Classical

set_option linter.unusedSectionVars false
set_option linter.deprecated false

section enc

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- Bit `g` of the content `o` of a cell of stack `k`. -/
noncomputable def symBit {T : Set (Σ k, Γ k)} (k : K) (o : Option (Γ k)) (g : T) : Bool :=
  decide (o.map (Sigma.mk k) = some g.1)

theorem symBit_inj {T : Set (Σ k, Γ k)} (k : K) (o o' : Option (Γ k))
    (ho : ∀ s, o = some s → (⟨k, s⟩ : Σ k, Γ k) ∈ T)
    (ho' : ∀ s, o' = some s → (⟨k, s⟩ : Σ k, Γ k) ∈ T)
    (h : ∀ g : T, symBit k o g = symBit k o' g) : o = o' := by
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some s' =>
      have := h ⟨⟨k, s'⟩, ho' s' rfl⟩
      simp [symBit] at this
  | some s =>
    have := h ⟨⟨k, s⟩, ho s rfl⟩
    simp only [symBit, Option.map_some, decide_true] at this
    cases o' with
    | none => simp at this
    | some s' =>
      simp only [Option.map_some, Option.some.injEq] at this
      have := (Sigma.mk.inj (decide_eq_true_iff.1 this.symm)).2
      rw [eq_of_heq this]

/-- The configuration bits. -/
abbrev Idx (Λ σ : Type) (T : Set (Σ k, Γ k)) (H : ℕ) : Type :=
  Option Λ ⊕ σ ⊕ (K × Fin H × T) ⊕ (K × Fin H)

/-- The window bits. -/
abbrev Wix (Λ σ : Type) (T : Set (Σ k, Γ k)) (d : ℕ) : Type :=
  Option Λ ⊕ σ ⊕ (K × Fin d × T)

variable (T : Set (Σ k, Γ k)) (H d : ℕ)

/-- The bits of a configuration. -/
noncomputable def enc (c : TM2.Cfg Γ Λ σ) : Idx Λ σ T H → Bool
  | .inl l => decide (c.l = l)
  | .inr (.inl s) => decide (c.var = s)
  | .inr (.inr (.inl (k, i, g))) => symBit k ((c.stk k).reverse[i.1]?) g
  | .inr (.inr (.inr (k, i))) => decide (i.1 < (c.stk k).length)

/-- The window bits of a configuration. -/
noncomputable def wenc (c : TM2.Cfg Γ Λ σ) : Wix Λ σ T d → Bool
  | .inl l => decide (c.l = l)
  | .inr (.inl s) => decide (c.var = s)
  | .inr (.inr (k, r, g)) => symBit k ((c.stk k)[r.1]?) g

theorem good_getElem? {S : ∀ k, List (Γ k)} (hS : Good T S) (k : K) (l : List (Γ k))
    (hl : ∀ s ∈ l, s ∈ S k) (j : ℕ) : ∀ s, l[j]? = some s → (⟨k, s⟩ : Σ k, Γ k) ∈ T := by
  intro s hs
  exact hS k s (hl s (List.mem_of_getElem? hs))

theorem window_det (c c' : TM2.Cfg Γ Λ σ) (hc : Good T c.stk) (hc' : Good T c'.stk)
    (h : wenc T d c = wenc T d c') :
    c.l = c'.l ∧ c.var = c'.var ∧ ∀ k, (c.stk k).take d = (c'.stk k).take d := by
  refine ⟨?_, ?_, ?_⟩
  · have := congrFun h (.inl c.l)
    simp only [wenc, decide_true] at this
    exact (decide_eq_true_iff.1 this.symm).symm
  · have := congrFun h (.inr (.inl c.var))
    simp only [wenc, decide_true] at this
    exact (decide_eq_true_iff.1 this.symm).symm
  · intro k
    apply List.ext_getElem?
    intro r
    rw [List.getElem?_take, List.getElem?_take]
    split_ifs with hr
    · apply symBit_inj (T := T) k
      · exact good_getElem? T hc k _ (fun s hs => hs) r
      · exact good_getElem? T hc' k _ (fun s hs => hs) r
      · intro g
        exact congrFun h (.inr (.inr (k, ⟨r, hr⟩, g)))
    · rfl

/-! ## One step -/

variable (M : Λ → TM2.Stmt Γ Λ σ)

/-- The new top part of stack `k` after one step from a configuration at label `l`. -/
def newTop (l : Λ) (c : TM2.Cfg Γ Λ σ) (k : K) : List (Γ k) :=
  (TM2.stepAux (M l) c.var (fun k => (c.stk k).take d)).stk k

theorem stepT_some (hd : ∀ l, pops (M l) ≤ d) (c : TM2.Cfg Γ Λ σ) (l : Λ) (hl : c.l = some l) :
    stepT M c = ⟨(TM2.stepAux (M l) c.var (fun k => (c.stk k).take d)).l,
      (TM2.stepAux (M l) c.var (fun k => (c.stk k).take d)).var,
      fun k => newTop d M l c k ++ (c.stk k).drop d⟩ := by
  simp only [stepT, hl]
  exact stepAux_take (M l) d (hd l) c.var c.stk

theorem newTop_length (p : ℕ) (hp : ∀ l, PEqualNP.Library.Machines.pushes (M l) ≤ p)
    (l : Λ) (c : TM2.Cfg Γ Λ σ) (k : K) :
    (newTop d M l c k).length ≤ min (c.stk k).length d + p := by
  have h1 := PEqualNP.Library.Machines.stepAux_length (M l) c.var
    (fun k => (c.stk k).take d) k
  have h2 := hp l
  simp only [List.length_take] at h1
  unfold newTop
  omega

theorem stepT_det_l (hd : ∀ l, pops (M l) ≤ d) (c c' : TM2.Cfg Γ Λ σ) (hc : Good T c.stk)
    (hc' : Good T c'.stk) (h : wenc T d c = wenc T d c') :
    (stepT M c).l = (stepT M c').l ∧ (stepT M c).var = (stepT M c').var := by
  obtain ⟨h1, h2, h3⟩ := window_det T d c c' hc hc' h
  cases hl : c.l with
  | none =>
    have hl' : c'.l = none := by rw [← h1, hl]
    rw [stepT_none M c hl, stepT_none M c' hl']
    exact ⟨by rw [hl, hl'], h2⟩
  | some l =>
    have hl' : c'.l = some l := by rw [← h1, hl]
    rw [stepT_some d M hd c l hl, stepT_some d M hd c' l hl']
    have e : (fun k => (c.stk k).take d) = (fun k => (c'.stk k).take d) := funext h3
    simp only [e, h2]
    exact ⟨trivial, trivial⟩

/-- The new content of cell `i` given the new top `r`, the height `h` and the old content
`o`. -/
def newCell {α : Type} (r : List α) (h : ℕ) (o : Option α) (i : ℕ) : Option α :=
  if i < h - d then o else r.reverse[i - (h - d)]?

theorem newCell_true {α : Type} (r S : List α) (i : ℕ) :
    (r ++ S.drop d).reverse[i]? = newCell d r S.length S.reverse[i]? i := by
  unfold newCell
  rw [List.reverse_append, List.getElem?_append, List.length_reverse, List.length_drop]
  split_ifs with h
  · have e : S.reverse = (S.drop d).reverse ++ (S.take d).reverse := by
      rw [← List.reverse_append, List.take_append_drop]
    rw [e, List.getElem?_append_left (by rw [List.length_reverse, List.length_drop]; exact h)]
  · rfl

variable (p : ℕ)

/-- The local radius. -/
def rad : ℕ := d + p + 1

/-- The clamped height `h` of a stack seen from cell `i`. -/
def clampH (h i : ℕ) : ℕ := min (2 * rad d p) (h + rad d p - i) + i - rad d p

theorem newCell_clamp {α : Type} (r : List α) (h : ℕ) (o : Option α) (i : ℕ)
    (hr : r.length ≤ d + p) : newCell d r h o i = newCell d r (clampH d p h i) o i := by
  unfold newCell clampH rad
  rcases Nat.lt_or_ge h (i + (d + p + 1)) with h1 | h1
  · rcases Nat.lt_or_ge i (h + (d + p + 1)) with h2 | h2
    · have e : min (2 * (d + p + 1)) (h + (d + p + 1) - i) + i - (d + p + 1) = h := by omega
      rw [e]
    · have e : min (2 * (d + p + 1)) (h + (d + p + 1) - i) + i - (d + p + 1) =
          i - (d + p + 1) := by omega
      rw [e, if_neg (show ¬ _ by omega), if_neg (show ¬ _ by omega), List.getElem?_eq_none, List.getElem?_eq_none]
      · rw [List.length_reverse]; omega
      · rw [List.length_reverse]; omega
  · have e : min (2 * (d + p + 1)) (h + (d + p + 1) - i) + i - (d + p + 1) =
        i + (d + p + 1) := by omega
    rw [e, if_pos (by omega), if_pos (by omega)]

theorem newMark_clamp (rl h i : ℕ) (hr : rl ≤ d + p) :
    i < rl + (h - d) ↔ i < rl + (clampH d p h i - d) := by
  unfold clampH rad; omega

theorem oldMark_clamp (h i : ℕ) : i < h ↔ rad d p < min (2 * rad d p) (h + rad d p - i) := by
  unfold rad; omega

/-- The local bits of cell `i` of stack `k`: the window, the height of the stack seen from the
cell (in unary, clamped) and the old content of the cell. -/
noncomputable def locenc (c : TM2.Cfg Γ Λ σ) (k : K) (i : ℕ) :
    Wix Λ σ T d ⊕ Fin (2 * rad d p) ⊕ T → Bool
  | .inl w => wenc T d c w
  | .inr (.inl δ) => decide (δ.1 + i < (c.stk k).length + rad d p)
  | .inr (.inr g) => symBit k ((c.stk k).reverse[i]?) g

theorem cnt_det (R h h' i : ℕ)
    (H : ∀ δ : Fin (2 * R), decide (δ.1 + i < h + R) = decide (δ.1 + i < h' + R)) :
    min (2 * R) (h + R - i) = min (2 * R) (h' + R - i) := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have hb : min (2 * R) (h + R - i) < 2 * R := by omega
    have := H ⟨_, hb⟩
    simp only [decide_eq_decide] at this
    omega
  · have hb : min (2 * R) (h' + R - i) < 2 * R := by omega
    have := H ⟨_, hb⟩
    simp only [decide_eq_decide] at this
    omega

theorem locenc_det (hd : ∀ l, pops (M l) ≤ d)
    (hp : ∀ l, PEqualNP.Library.Machines.pushes (M l) ≤ p) (c c' : TM2.Cfg Γ Λ σ) (k : K) (i : ℕ)
    (hc : Good T c.stk) (hc' : Good T c'.stk) (h : locenc T d p c k i = locenc T d p c' k i) :
    ((stepT M c).stk k).reverse[i]? = ((stepT M c').stk k).reverse[i]? ∧
      (i < ((stepT M c).stk k).length ↔ i < ((stepT M c').stk k).length) := by
  have hw : wenc T d c = wenc T d c' := funext fun w => congrFun h (.inl w)
  obtain ⟨h1, h2, h3⟩ := window_det T d c c' hc hc' hw
  have ho : (c.stk k).reverse[i]? = (c'.stk k).reverse[i]? := by
    apply symBit_inj (T := T) k
    · exact good_getElem? T hc k _ (fun s hs => List.mem_reverse.1 hs) i
    · exact good_getElem? T hc' k _ (fun s hs => List.mem_reverse.1 hs) i
    · intro g; exact congrFun h (.inr (.inr g))
  have hn := cnt_det (rad d p) (c.stk k).length (c'.stk k).length i
    (fun δ => congrFun h (.inr (.inl δ)))
  have hcl : clampH d p (c.stk k).length i = clampH d p (c'.stk k).length i := by
    unfold clampH; rw [hn]
  cases hl : c.l with
  | none =>
    have hl' : c'.l = none := by rw [← h1, hl]
    rw [stepT_none M c hl, stepT_none M c' hl']
    refine ⟨ho, ?_⟩
    rw [oldMark_clamp d p (c.stk k).length i, oldMark_clamp d p (c'.stk k).length i, hn]
  | some l =>
    have hl' : c'.l = some l := by rw [← h1, hl]
    rw [stepT_some d M hd c l hl, stepT_some d M hd c' l hl']
    have hr : newTop d M l c k = newTop d M l c' k := by
      unfold newTop
      have e : (fun k => (c.stk k).take d) = (fun k => (c'.stk k).take d) := funext h3
      rw [e, h2]
    have hlen := newTop_length d M p hp l c k
    have hlen' : (newTop d M l c k).length ≤ d + p := by omega
    simp only
    refine ⟨?_, ?_⟩
    · rw [newCell_true, newCell_true, newCell_clamp d p _ _ _ _ hlen', ho, hcl, hr,
        ← newCell_clamp d p _ _ _ _ (hr ▸ hlen')]
    · rw [List.length_append, List.length_append, List.length_drop, List.length_drop,
        newMark_clamp d p _ _ _ hlen', hcl, hr, ← newMark_clamp d p _ _ _ (hr ▸ hlen')]

end enc

end PEqualNP.Library.Helpers.Tableau
