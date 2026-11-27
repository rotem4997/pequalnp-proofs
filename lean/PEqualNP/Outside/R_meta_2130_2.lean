import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- For a fixed set of lines, test all points avoiding those lines in one input.
-- The loss bound only needs soundness on these inputs.
theorem PEqualNP.Outside.R_meta_2130_2 :
  (∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
    let z := fun (S : Finset (Fin N)) (i : Fin (N + N)) =>
      Fin.addCases (motive := fun _ => Bool) (fun p : Fin N => decide (¬ ∃ l ∈ S, I p l))
        (fun l : Fin N => decide (l ∈ S)) i
    ∀ S : Finset (Fin N), Fintype.card {l : Fin N // z S (Fin.natAdd N l) = true} = S.card ∧
      ¬ ∃ p l : Fin N, I p l ∧ z S (Fin.castAdd N p) = true ∧ z S (Fin.natAdd N l) = true) →
  (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
    2 ≤ q → N = q ^ 2 + q + 1 →
    (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
    IsMinimalMonoCircuit (N + N) C →
    let z := fun (S : Finset (Fin N)) (i : Fin (N + N)) =>
      Fin.addCases (motive := fun _ => Bool) (fun p : Fin N => decide (¬ ∃ l ∈ S, I p l))
        (fun l : Fin N => decide (l ∈ S)) i
    (∀ S : Finset (Fin N), S.card ≤ q → C.eval (List.ofFn (z S)) = false) →
    let D : Circuit := ⟨C.gates.map (fun g =>
      if g.op.eval [] = true ∧ g.inputs.length = 2 ∧
          (g.inputs.all fun i => decide (0 < (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD i 0)) = true
      then ⟨GateOp.or, []⟩ else g), C.output⟩
    let e := fun (p l : Fin N) (i : Fin (N + N)) =>
      decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)
    ∀ T : Fin N → Finset (Fin N),
      (∀ l p, p ∈ T l → I p l ∧ C.eval (List.ofFn (e p l)) = true ∧
        D.eval (List.ofFn (e p l)) = false) →
      ∑ l, (T l).card ≤ 44 * Fintype.card {j : Fin C.size //
        (C.wires (List.replicate (N + N) false)).getD (N + N + j.val) false = false ∧
        ∃ l p, p ∈ T l ∧ (C.wires (List.ofFn (e p l))).getD (N + N + j.val) false = true}) →
  ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (2 : ℕ) ≤ x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →         (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) →           PEqualNP.MetaComplexity.IsMinimalMonoCircuit (x2 + x2) x5 →             (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) →               have x12 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x12 : PEqualNP.CircuitLowerBounds.Gate) => if x12.op.eval [] = Bool.true ∧ x12.inputs.length = (2 : ℕ) ∧ (x12.inputs.all fun (x13 : ℕ) => Decidable.decide ((0 : ℕ) < (x5.lineDegrees (x2 + x2) (Finset.Ico x2 (x2 + x2))).getD x13 (0 : ℕ))) = Bool.true then { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate } else x12) x5.gates, output := x5.output : PEqualNP.CircuitLowerBounds.Circuit };               have x13 : Fin x2 → Fin x2 → Fin (x2 + x2) → Bool := fun (x13 x14 : Fin x2) (x15 : Fin (x2 + x2)) => Decidable.decide (x15 = Fin.castAdd x2 x13 ∨ x15 = Fin.natAdd x2 x14);               ∀ (x14 : Fin x2 → Finset (Fin x2)), (∀ (x15 x16 : Fin x2), x16 ∈ x14 x15 → x3 x16 x15 ∧ PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 (x13 x16 x15) = Bool.true ∧ PEqualNP.MetaComplexity.circuitFun (x2 + x2) x12 (x13 x16 x15) = Bool.false) → ∑ x16 : Fin x2, (x14 x16).card ≤ (44 : ℕ) * Fintype.card { x16 : Fin x5.size // (x5.wires (List.replicate (x2 + x2) Bool.false)).getD (x2 + x2 + ↑x16) Bool.false = Bool.false ∧ ∃ (x17 : Fin x2), ∃ x18 ∈ x14 x17, (x5.wires (List.ofFn (x13 x18 x17))).getD (x2 + x2 + ↑x16) Bool.false = Bool.true } := by
  intro labels bound q N I _ C hq hN column unique minimal sound
  dsimp only
  intro T hT
  refine bound q N I C hq hN column unique minimal (fun S hS => ?_) T hT
  obtain ⟨count, negative⟩ := labels N I S
  exact sound _ (count.trans_le hS) negative
