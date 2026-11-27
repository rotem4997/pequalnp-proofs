import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4700

open PEqualNP.CircuitLowerBounds

/-- Clamp every wire index at `23`. -/
def clampGate (g : Gate) : Gate := { op := g.op, inputs := g.inputs.map fun i => min i 23 }

def clamp (C : Circuit) : Circuit :=
  { gates := C.gates.map clampGate, output := min C.output 23 }

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_min (w : List Bool) (hw : w.length ≤ 23) (i : ℕ) :
    w.getD (min i 23) false = w.getD i false := by
  by_cases h : i ≤ 23
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show w.length ≤ 23 by omega),
      List.getElem?_eq_none (show w.length ≤ i by omega)]

theorem step_clamp (w : List Bool) (hw : w.length ≤ 23) (g : Gate) :
    step w (clampGate g) = step w g := by
  simp only [step, clampGate, List.map_map]
  congr 3
  apply List.map_congr_left
  intro i _
  exact getD_min w hw i

theorem foldl_clamp : ∀ (gs : List Gate) (w : List Bool), w.length + gs.length ≤ 23 →
    (gs.map clampGate).foldl step w = gs.foldl step w
  | [], _, _ => rfl
  | g :: gs, w, h => by
    simp only [List.map_cons, List.foldl_cons, List.length_cons] at h ⊢
    rw [step_clamp w (by omega) g]
    exact foldl_clamp gs (step w g) (by simp [step]; omega)

theorem foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega

end PEqualNP.Outside.L_meta_4700

open PEqualNP.Outside.L_meta_4700 in
theorem PEqualNP.Outside.L_meta_4700 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (13 : ℕ) → PEqualNP.MetaComplexity.FanInTwo x1 → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 ∧ x4.size = x1.size ∧ x4.output ≤ (23 : ℕ) ∧ (∀ x5 ∈ x4.gates, ∀ x7 ∈ x5.inputs, x7 ≤ (23 : ℕ)) ∧ ∀ (x5 : List Bool), x5.length = (10 : ℕ) → x4.eval x5 = x1.eval x5 := by
  intro C hs hf
  refine ⟨clamp C, ?_, by simp [clamp, PEqualNP.CircuitLowerBounds.Circuit.size], Nat.min_le_right _ _, ?_, ?_⟩
  · intro g hg
    simp only [clamp, List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    obtain ⟨h1, h2⟩ := hf g0 hg0
    exact ⟨h1, by simpa [clampGate] using h2⟩
  · intro g hg i hi
    simp only [clamp, List.mem_map] at hg
    obtain ⟨g0, _, rfl⟩ := hg
    simp only [clampGate, List.mem_map] at hi
    obtain ⟨j, _, rfl⟩ := hi
    exact Nat.min_le_right _ _
  · intro x hx
    have hsz : C.gates.length ≤ 13 := hs
    have e : (clamp C).wires x = C.wires x := by
      show (C.gates.map clampGate).foldl step x = C.gates.foldl step x
      exact foldl_clamp C.gates x (by omega)
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [e]
    show (C.wires x).getD (min C.output 23) false = (C.wires x).getD C.output false
    apply getD_min
    show (C.gates.foldl step x).length ≤ 23
    rw [foldl_length]; omega
