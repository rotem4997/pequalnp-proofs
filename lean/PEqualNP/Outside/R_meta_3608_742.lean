import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Separate the six inputs that can be read only once from synthesis with those reads fixed.
theorem PEqualNP.Outside.R_meta_3608_742
    (singleRead : ∀ C : Circuit, FanInTwo C → C.size = 14 → C.output = 23 →
      (∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1) →
      (∃ a b : Fin C.gates.length, a < b ∧ 3 ≤ a.val ∧ a.val ≤ 6 ∧ b.val < 13 ∧
        (C.gates.get a).op = .not ∧ (C.gates.get b).op = .not ∧
        ∀ j : Fin C.gates.length, (C.gates.get j).op = .not → j = a ∨ j = b) →
      let W := C.gates.flatMap Gate.inputs
      let T (x : ℕ) := C.eval (List.ofFn (fun i : Fin 9 => x.testBit i.val) ++ [x.testBit 0 || x.testBit 2]) =
        ([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ).any (fun e => x &&& e == e)
      (∀ w < 23, w ∈ W) →
      ({w ∈ Finset.range 23 | 2 ≤ W.count w} : Finset ℕ).card ≤ 3 →
      (∀ x < 512, T x) → (∀ w ∈ ([0,1,2,4,7,8] : List ℕ), W.count w ≤ 1))
    (search : ∀ C : Circuit, FanInTwo C → C.size = 14 → C.output = 23 →
      (∀ g ∈ C.gates, g.op = .not → g.inputs.length ≤ 1) →
      (∃ a b : Fin C.gates.length, a < b ∧ 3 ≤ a.val ∧ a.val ≤ 6 ∧ b.val < 13 ∧
        (C.gates.get a).op = .not ∧ (C.gates.get b).op = .not ∧
        ∀ j : Fin C.gates.length, (C.gates.get j).op = .not → j = a ∨ j = b) →
      let W := C.gates.flatMap Gate.inputs
      let T (x : ℕ) := C.eval (List.ofFn (fun i : Fin 9 => x.testBit i.val) ++ [x.testBit 0 || x.testBit 2]) =
        ([3,6,12,17,24,33,66,132,160,264,288,320] : List ℕ).any (fun e => x &&& e == e)
      (∀ w < 23, w ∈ W) →
      let R := {w ∈ Finset.range 23 | 2 ≤ W.count w}
      R.card ≤ 3 →
      (∀ g ∈ C.gates, ∀ a b : Fin 9, a ≠ b → g.op = .and ∨ g.op = .or →
        g.inputs = [a.val,b.val] → a.val ∈ R ∨ b.val ∈ R) →
      (∀ w ∈ ([0,1,2,4,7,8] : List ℕ), W.count w ≤ 1) → ∃ x < 512, ¬T x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size = (14 : ℕ) →       x1.output = (23 : ℕ) →         (∀ x5 ∈ x1.gates, x5.op = PEqualNP.CircuitLowerBounds.GateOp.not → x5.inputs.length ≤ (1 : ℕ)) →           (∃ (x6 : Fin x1.gates.length) (x7 : Fin x1.gates.length), x6 < x7 ∧ (3 : ℕ) ≤ ↑x6 ∧ ↑x6 ≤ (6 : ℕ) ∧ ↑x7 < (13 : ℕ) ∧ (x1.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x8 : Fin x1.gates.length), (x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.not → x8 = x6 ∨ x8 = x7) →             have x7 : List ℕ := List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x1.gates;             have x8 : Finset ℕ := {x8 ∈ Finset.range (23 : ℕ) | (2 : ℕ) ≤ List.count x8 x7};             (∀ x9 < (23 : ℕ), x9 ∈ x7) → x8.card ≤ (3 : ℕ) → (∀ x11 ∈ x1.gates, ∀ (x13 x14 : Fin (9 : ℕ)), x13 ≠ x14 → x11.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or → x11.inputs = [↑x13, ↑x14] → ↑x13 ∈ x8 ∨ ↑x14 ∈ x8) → ∃ x12 < (512 : ℕ), x1.eval ((List.ofFn fun (x13 : Fin (9 : ℕ)) => x12.testBit ↑x13) ++ [x12.testBit (0 : ℕ) || x12.testBit (2 : ℕ)]) ≠ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)].any fun (x13 : ℕ) => x12 &&& x13 == x13 := by
  intro C hfan hsize houtput hnot htwo
  dsimp only
  intro hused hbudget hlocal
  by_contra! h
  obtain ⟨x, hx, hwrong⟩ :=
    search C hfan hsize houtput hnot htwo hused hbudget hlocal
      (singleRead C hfan hsize houtput hnot htwo hused hbudget h)
  exact hwrong (h x hx)
