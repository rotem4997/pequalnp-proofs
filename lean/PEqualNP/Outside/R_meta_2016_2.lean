import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2016_2
    (h : ∃ n : ℕ, ∀ m : ℕ, n ≤ m)
    (hn : ¬ ∃ n : ℕ, ∀ m : ℕ, n ≤ m) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 ∧ x2.size = (11 : ℕ) ∧ (PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x2 = fun (x3 : Fin (7 : ℕ) → Bool) => x1 (Fin.insertNth (0 : Fin (9 : ℕ)) Bool.false (Fin.insertNth (3 : Fin (8 : ℕ)) Bool.false x3))) ∧ ∀ (x3 : Bool), ∃ (x4 : ℕ) (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Circuit), x6.output = x2.output + (1 : ℕ) ∧ List.Forall₂ (fun (x7 x8 : PEqualNP.CircuitLowerBounds.Gate) => x7.op = x8.op ∧ List.Forall₂ (fun (x9 x10 : ℕ) => x10 = x9 + (1 : ℕ) ∨ x10 = (0 : ℕ) ∧ (x9 = x4 ∨ x9 = x5)) x7.inputs x8.inputs) x2.gates x6.gates ∧ ∀ (x7 : Fin (7 : ℕ) → Bool), x6.eval (Bool.true :: List.ofFn x7) = x1 (Fin.insertNth (0 : Fin (9 : ℕ)) x3 (Fin.insertNth (3 : Fin (8 : ℕ)) (!x3) x7)) := by
  exact absurd h hn
