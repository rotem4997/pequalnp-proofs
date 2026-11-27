import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4035_2
  (hTrace : have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ)))); have x2 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Gate) (x3 : ℕ) => x2.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2.inputs.head? = Option.some x3 ∨ x2.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x3 ∈ x2.inputs; have x3 : Bool → List Bool := fun (x3 : Bool) => x3 :: Bool.true :: List.replicate (8 : ℕ) Bool.false ++ [!x3]; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → (∀ (x6 : Fin (10 : ℕ) → Bool), x4.eval (List.ofFn x6 ++ [!x6 (0 : Fin (10 : ℕ))]) = x1 x6) → (∀ (x7 : Fin x4.size), ¬x2 (x4.gates.get x7) (0 : ℕ)) → (∃ (x8 : Fin x4.size), x2 (x4.gates.get x8) (10 : ℕ)) ∧ ∃ (x8 : Fin x4.size), (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x4.wires (x3 Bool.false)).getD ((11 : ℕ) + ↑x8) Bool.false = Bool.false ∧ (x4.wires (x3 Bool.true)).getD ((11 : ℕ) + ↑x8) Bool.false = Bool.true)
  (hRest : have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ)))); have x2 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Gate) (x3 : ℕ) => x2.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x2.inputs.head? = Option.some x3 ∨ x2.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x3 ∈ x2.inputs; have x3 : Bool → List Bool := fun (x3 : Bool) => x3 :: Bool.true :: List.replicate (8 : ℕ) Bool.false ++ [!x3]; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (18 : ℕ) → (∀ (x6 : Fin (10 : ℕ) → Bool), x4.eval (List.ofFn x6 ++ [!x6 (0 : Fin (10 : ℕ))]) = x1 x6) → (∀ (x7 : Fin x4.size), ¬x2 (x4.gates.get x7) (0 : ℕ)) → (∃ (x8 : Fin x4.size), x2 (x4.gates.get x8) (10 : ℕ)) → (∃ (x8 : Fin x4.size), (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x4.wires (x3 Bool.false)).getD ((11 : ℕ) + ↑x8) Bool.false = Bool.false ∧ (x4.wires (x3 Bool.true)).getD ((11 : ℕ) + ↑x8) Bool.false = Bool.true) → ¬∃ (x9 : Fin x4.size) (x10 : Fin x4.size), ∀ (x11 : Fin x4.size), x2 (x4.gates.get x11) (10 : ℕ) → x11 = x9 ∨ x11 = x10) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∀ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (10 : ℕ))]) = (x4 (0 : Fin (10 : ℕ)) && x4 (1 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (2 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (3 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (4 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (0 : Fin (10 : ℕ)) || x4 (0 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (2 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (3 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (4 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (5 : Fin (10 : ℕ)) && x4 (7 : Fin (10 : ℕ)) || x4 (7 : Fin (10 : ℕ)) && x4 (9 : Fin (10 : ℕ)) || x4 (9 : Fin (10 : ℕ)) && x4 (6 : Fin (10 : ℕ)) || x4 (6 : Fin (10 : ℕ)) && x4 (8 : Fin (10 : ℕ)) || x4 (8 : Fin (10 : ℕ)) && x4 (5 : Fin (10 : ℕ)))) → (∀ (x5 : Fin x1.gates.length), ((x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x5).inputs.head? ≠ Option.some (0 : ℕ)) ∧ ((x1.gates.get x5).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → (0 : ℕ) ∉ (x1.gates.get x5).inputs)) → ¬∃ (x6 : Fin x1.gates.length) (x7 : Fin x1.gates.length), ∀ (x8 : Fin x1.gates.length), ((x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.not → (x1.gates.get x8).inputs.head? = Option.some (10 : ℕ) → x8 = x6 ∨ x8 = x7) ∧ ((x1.gates.get x8).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → (10 : ℕ) ∈ (x1.gates.get x8).inputs → x8 = x6 ∨ x8 = x7) := by
  intro C model size computes nozero
  rintro ⟨a, b, alleged⟩
  have equiv : ∀ x : Fin 10 → Bool, ((List.finRange 5).any fun i => x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1)) || x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) || x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) := by
    intro x
    change ((((x 0 && x 1) || (x 0 && x 5) || (x 5 && x 7)) ||
      (((x 1 && x 2) || (x 1 && x 6) || (x 6 && x 8)) ||
      (((x 2 && x 3) || (x 2 && x 7) || (x 7 && x 9)) ||
      (((x 3 && x 4) || (x 3 && x 8) || (x 8 && x 5)) ||
      (((x 4 && x 0) || (x 4 && x 9) || (x 9 && x 6)) ||
      false)))))) = _
    simp only [Bool.or_false]
    ac_rfl
  have computes' : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!x 0]) = ((List.finRange 5).any fun i => x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1)) || x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i) || x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2))) :=
    fun x => (computes x).trans (equiv x).symm
  have zero : ∀ j : Fin C.size, ¬ ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
      (C.gates.get j).inputs.head? = some 0 ∨
      (C.gates.get j).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ 0 ∈ (C.gates.get j).inputs) := by
    rintro j (⟨op, hin⟩ | ⟨op, hin⟩)
    · exact (nozero j).1 op hin
    · exact (nozero j).2 op hin
  obtain ⟨present, turns⟩ := hTrace C model computes' zero
  exact hRest C model size computes' zero present turns ⟨a, b, fun j hj => by
    rcases hj with ⟨op, hd⟩ | ⟨op, hm⟩
    · exact (alleged j).1 op hd
    · exact (alleged j).2 op hm⟩
