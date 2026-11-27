import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2621
open PEqualNP.CircuitLowerBounds

def fl (F : List Bool → Gate → Bool) (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [F w g]) w

theorem fl_append (F : List Bool → Gate → Bool) (a b : List Gate) (w : List Bool) :
    fl F (a ++ b) w = fl F b (fl F a w) := by
  simp [fl, List.foldl_append]

theorem fl_cons (F : List Bool → Gate → Bool) (g : Gate) (gs : List Gate) (w : List Bool) :
    fl F (g :: gs) w = fl F gs (w ++ [F w g]) := rfl

theorem fl_len (F : List Bool → Gate → Bool) (gs : List Gate) :
    ∀ w : List Bool, (fl F gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    rw [fl_cons, ih]
    simp
    omega

theorem fl_keep (F : List Bool → Gate → Bool) (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (fl F gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [fl_cons, ih _ _ (by simp; omega), List.getD_append _ _ _ _ hi]

theorem fl_at (F : List Bool → Gate → Bool) (gs : List Gate) (w : List Bool) (k : ℕ)
    (hk : k < gs.length) :
    (fl F gs w).getD (w.length + k) false = F (fl F (gs.take k) w) gs[k] ∧
      ∀ a, a < w.length + k → (fl F gs w).getD a false = (fl F (gs.take k) w).getD a false := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hlen : (fl F (gs.take k) w).length = w.length + k := by
    rw [fl_len, List.length_take, Nat.min_eq_left (le_of_lt hk)]
  have e : fl F gs w = fl F (gs.drop (k + 1))
      (fl F (gs.take k) w ++ [F (fl F (gs.take k) w) gs[k]]) := by
    conv_lhs => rw [hsplit]
    rw [fl_append, fl_cons]
  constructor
  · rw [e, fl_keep _ _ _ _ (by simp; omega), ← hlen]
    simp
  · intro a ha
    rw [e, fl_keep _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]

def sel (op : GateOp) (p q : Bool) : Bool :=
  match op with
  | GateOp.and => p
  | _ => q

end PEqualNP.Outside.L_meta_2621

open PEqualNP.Outside.L_meta_2621 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_2621 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → ∀ (x3 : ℕ) (x4 : List Bool), ∃ (x5 : ℕ → Bool), (∀ x6 < (26 : ℕ), x5 x6 = Decidable.decide (x6 = x3)) ∧ ∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ), x1.gates[x6]? = Option.some x7 → x7.inputs = [x8, x9] → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((26 : ℕ) + x6) = (x4.getD x8 Bool.false && x5 x9 || x5 x8 && x4.getD x9 Bool.false)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((26 : ℕ) + x6) = (x5 x8 || x5 x9)) := by
  intro C hC x3 x4
  obtain ⟨_, hrb, _⟩ := hC
  let F : List Bool → Gate → Bool := fun D g =>
    sel g.op
      (x4.getD (g.inputs.getD 0 0) false && D.getD (g.inputs.getD 1 0) false
        || D.getD (g.inputs.getD 0 0) false && x4.getD (g.inputs.getD 1 0) false)
      (D.getD (g.inputs.getD 0 0) false || D.getD (g.inputs.getD 1 0) false)
  let W0 : List Bool := (List.range 26).map (fun i => decide (i = x3))
  have hW0 : W0.length = 26 := by simp [W0]
  refine ⟨fun w => (fl F C.gates W0).getD w false, ?_, ?_⟩
  · intro w hw
    show (fl F C.gates W0).getD w false = _
    rw [fl_keep _ _ _ _ (by omega)]
    simp [W0, List.getD_eq_getElem?_getD, hw]
  · intro k g a b hk hin
    obtain ⟨hlt, hg⟩ := List.getElem?_eq_some_iff.mp hk
    have hlt2 : ∀ i ∈ [a, b], i < 26 + k := by
      intro i hi
      refine hrb k hlt i ?_
      have : PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
        unfold PEqualNP.MetaComplexity.NestedCover.gateAt
        rw [List.getD_eq_getElem _ _ hlt]
      rw [this, hg, hin]
      exact hi
    obtain ⟨h1, h2⟩ := fl_at F C.gates W0 k hlt
    rw [hW0, hg] at h1
    rw [hW0] at h2
    have ea := h2 a (hlt2 a (by simp))
    have eb := h2 b (hlt2 b (by simp))
    have hF : F (fl F (C.gates.take k) W0) g
        = sel g.op
          (x4.getD a false && (fl F (C.gates.take k) W0).getD b false
            || (fl F (C.gates.take k) W0).getD a false && x4.getD b false)
          ((fl F (C.gates.take k) W0).getD a false || (fl F (C.gates.take k) W0).getD b false) := by
      show sel g.op _ _ = _
      rw [hin]
      rfl
    constructor
    · intro hop
      show (fl F C.gates W0).getD (26 + k) false
        = (x4.getD a false && (fl F C.gates W0).getD b false
          || (fl F C.gates W0).getD a false && x4.getD b false)
      rw [h1, hF, hop, ea, eb]
      rfl
    · intro hop
      show (fl F C.gates W0).getD (26 + k) false
        = ((fl F C.gates W0).getD a false || (fl F C.gates W0).getD b false)
      rw [h1, hF, hop, ea, eb]
      rfl
