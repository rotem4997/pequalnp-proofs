import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3586

open PEqualNP.CircuitLowerBounds

lemma getD_foldl_prefix (l : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (l.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
      = w.getD i false := by
  induction l with
  | nil => intro w i h; rfl
  | cons g l ih =>
    intro w i h
    rw [List.foldl_cons, ih _ i (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

def idx (i : ℕ) : Fin 11 := if h : i < 11 then ⟨i, h⟩ else ⟨10, by omega⟩

lemma getD_idx (x9 : List Bool) (h : x9.length = 10) (i : ℕ) :
    x9.getD (idx i : ℕ) false = x9.getD i false := by
  unfold idx
  split
  · rfl
  · rw [List.getD_eq_default _ _ (by simp [h]), List.getD_eq_default _ _ (by omega)]

lemma or_inputs (x9 : List Bool) (h : x9.length = 10) (ins : List ℕ) (hl : ins.length ≤ 2) :
    GateOp.or.eval (ins.map fun i => x9.getD i false) =
      (x9.getD (idx (ins.headD 10) : ℕ) false || x9.getD (idx (ins.getLastD 10) : ℕ) false) := by
  rw [getD_idx x9 h, getD_idx x9 h]
  match ins, hl with
  | [], _ => simp [GateOp.eval, h]
  | [a], _ => simp [GateOp.eval]
  | [a, b], _ => simp [GateOp.eval]
  | _ :: _ :: _ :: _, hl => simp at hl

end PEqualNP.Outside.L_meta_3586

theorem PEqualNP.Outside.L_meta_3586 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (0 : Fin (9 : ℕ)) || x3 (4 : Fin (9 : ℕ)))) →       Option.map PEqualNP.CircuitLowerBounds.Gate.op x1.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or →         ∃ (x5 : Fin (11 : ℕ)) (x6 : Fin (11 : ℕ)) (x7 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x7 ∧             x7.size + (2 : ℕ) = x1.size ∧               ∀ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ))];                 x7.eval (x9 ++ [x9.getD (↑x5) Bool.false || x9.getD (↑x6) Bool.false]) = PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 x8 := by
  intro x1 hfan hw hop
  obtain ⟨gs, out⟩ := x1
  match gs, hfan, hw, hop with
  | [], _, _, hop => simp at hop
  | [_], _, _, hop => simp at hop
  | g0 :: g1 :: rest, hfan, hw, hop =>
    have hop1 : g1.op = PEqualNP.CircuitLowerBounds.GateOp.or := by simpa using hop
    have hl1 : g1.inputs.length ≤ 2 := (hfan g1 (by simp)).2
    refine ⟨PEqualNP.Outside.L_meta_3586.idx (g1.inputs.headD 10),
      PEqualNP.Outside.L_meta_3586.idx (g1.inputs.getLastD 10), ⟨rest, out⟩, ?_, ?_, ?_⟩
    · intro g hg
      exact hfan g (by simp [hg])
    · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
    · intro x8
      have hv := hw x8
      simp only [PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_cons] at hv
      rw [PEqualNP.Outside.L_meta_3586.getD_foldl_prefix _ _ 9 (by simp)] at hv
      have hlen : (List.ofFn x8).length = 9 := by simp
      have hv0 : g0.op.eval (g0.inputs.map fun i => (List.ofFn x8).getD i false) =
          (x8 0 || x8 4) := by
        simpa [List.getD_eq_getElem?_getD, List.getElem?_append_right, hlen] using hv
      show (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨rest, out⟩ _) =
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨g0 :: g1 :: rest, out⟩ (List.ofFn x8)
      simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
        List.foldl_cons]
      rw [hv0, hop1, PEqualNP.Outside.L_meta_3586.or_inputs _ (by simp) _ hl1]
