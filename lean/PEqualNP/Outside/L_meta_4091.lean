import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_4091

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

lemma run_nil (x : List Bool) : run [] x = x := rfl

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (step x g) := rfl

lemma run_append (l1 l2 : List Gate) (x : List Bool) :
    run (l1 ++ l2) x = run l2 (run l1 x) := by
  simp [run, List.foldl_append]

lemma step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih, step_length]; simp; omega

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp only [step]
  exact List.getD_append _ _ _ _ hi

lemma step_getD_last (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [step]
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

lemma run_getD (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => rw [run_cons, ih _ (by rw [step_length]; omega), step_getD _ _ _ hi]

end PEqualNP.Outside.L_meta_4091

theorem PEqualNP.Outside.L_meta_4091 : ∀ (x1 x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size = (44 : ℕ) → x1.output < (70 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x2 → x2.size ≤ (18 : ℕ) → ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x8 ∧ x8.size ≤ (63 : ℕ) ∧ ∀ (x9 : List Bool), x9.length = (26 : ℕ) → x8.eval x9 = (x1.eval x9 || x2.eval (x1.wires x9)) := by
  intro x1 x2 h1 hs1 ho1 h2 hs2
  have hl1 : x1.gates.length = 44 := hs1
  refine ⟨⟨x1.gates ++ x2.gates ++ [⟨GateOp.or, [x1.output, x2.output]⟩], 26 + 44 + x2.gates.length⟩,
    ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | rfl
    · exact h1 g hg
    · exact h2 g hg
    · exact ⟨by simp, by simp⟩
  · change (x1.gates ++ x2.gates ++ [_]).length ≤ 63
    have : x2.gates.length ≤ 18 := hs2
    simp only [List.length_append, List.length_singleton]
    omega
  · intro x9 hx9
    change (PEqualNP.Outside.L_meta_4091.run (x1.gates ++ x2.gates ++ [⟨GateOp.or, [x1.output, x2.output]⟩]) x9).getD
        (26 + 44 + x2.gates.length) false =
      ((PEqualNP.Outside.L_meta_4091.run x1.gates x9).getD x1.output false ||
        (PEqualNP.Outside.L_meta_4091.run x2.gates (PEqualNP.Outside.L_meta_4091.run x1.gates x9)).getD x2.output false)
    rw [PEqualNP.Outside.L_meta_4091.run_append, PEqualNP.Outside.L_meta_4091.run_append]
    have hW : (PEqualNP.Outside.L_meta_4091.run x2.gates (PEqualNP.Outside.L_meta_4091.run x1.gates x9)).length =
        26 + 44 + x2.gates.length := by
      rw [PEqualNP.Outside.L_meta_4091.run_length, PEqualNP.Outside.L_meta_4091.run_length, hx9, hl1]
    rw [show PEqualNP.Outside.L_meta_4091.run [(⟨GateOp.or, [x1.output, x2.output]⟩ : Gate)]
        (PEqualNP.Outside.L_meta_4091.run x2.gates (PEqualNP.Outside.L_meta_4091.run x1.gates x9)) =
        PEqualNP.Outside.L_meta_4091.step (PEqualNP.Outside.L_meta_4091.run x2.gates (PEqualNP.Outside.L_meta_4091.run x1.gates x9))
          ⟨GateOp.or, [x1.output, x2.output]⟩ from rfl, ← hW, PEqualNP.Outside.L_meta_4091.step_getD_last]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
      Bool.or_false]
    rw [PEqualNP.Outside.L_meta_4091.run_getD x2.gates _ x1.output (by rw [PEqualNP.Outside.L_meta_4091.run_length, hx9, hl1]; omega)]
