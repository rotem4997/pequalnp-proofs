import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9043
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

theorem gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hk]

end PEqualNP.Outside.L_meta_9043

open PEqualNP.Outside.L_meta_9043 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_9043 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → x1 ≤ x2.output → x2.output < x1 + x2.size → (∃ (x6 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x2.output - x1]? = Option.some x6 ∧ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∃ (x7 : ℕ) (x8 : ℕ), x7 < x2.output ∧ x8 < x2.output ∧ ∀ (x9 : List Bool), x9.length = x1 → x2.eval x9 = ((x2.wires x9).getD x7 Bool.false || (x2.wires x9).getD x8 Bool.false) := by
  intro n C hAO hn ho ⟨g, hg, hop⟩
  have hm : C.output - n < C.gates.length := by
    have : C.size = C.gates.length := rfl
    omega
  have hgm : C.gates[C.output - n] = g := by
    rw [List.getElem?_eq_getElem hm] at hg
    exact Option.some.inj hg
  have hlen := hAO.2.2 g (hgm ▸ List.getElem_mem hm)
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen
  subst hop
  match ins, hlen with
  | [a, b], _ =>
    have hrb := hAO.2.1 (C.output - n) hm
    rw [gateAt_eq C _ hm, hgm] at hrb
    have ha := hrb a (by simp)
    have hb := hrb b (by simp)
    refine ⟨a, b, by omega, by omega, fun x hx => ?_⟩
    have h := gate_val C.gates x (C.output - n) hm
    rw [hgm, hx] at h
    have e : n + (C.output - n) = C.output := by omega
    rw [e] at h
    show (wf C.gates x).getD C.output false = ((wf C.gates x).getD a false || (wf C.gates x).getD b false)
    rw [h, wire_take C.gates x (C.output - n) a (by omega) (le_of_lt hm),
      wire_take C.gates x (C.output - n) b (by omega) (le_of_lt hm)]
    simp [GateOp.eval]
