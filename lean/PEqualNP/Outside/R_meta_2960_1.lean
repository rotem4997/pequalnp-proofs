import Mathlib.Data.Fin.Basic
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Track the signs of wire aliases, then keep only gates that contribute to the output.
-- The read count leaves at least three raw inputs that each have one reader.
theorem PEqualNP.Outside.R_meta_2960_1
    (normalize :
    let f := fun x : Fin 7 → Bool =>
      ([1,12,4,15,26,35,46,63] : List ℕ).any
        (fun e => x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10)))
    let seed (x : Fin 7 → Bool) := List.ofFn x ++ [false]
    let valid (n : ℕ) (t : BinaryGate) :=
      (∃ a b : Bool, t.op = fun x y => (x == a) && (y == b)) ∧
      t.left < n ∧ t.right < n ∧ t.left ≠ 7 ∧ t.right ≠ 7 ∧ t.left ≠ t.right
    ∀ C : Circuit, FanInTwo C → circuitFun 7 C = f →
      C.gates.countP (fun g => GateOp.rec (motive := fun _ => Bool) true true false
        (fun _ => true) true g.op) ≤ 10 →
    ∃ (gs : List BinaryGate) (g : BinaryGate) (q : Bool),
      let p := (gs++[g]).flatMap fun t => [t.left,t.right]
      7 ≤ gs.length ∧ gs.length ≤ 9 ∧
      (∀ (j : ℕ) (hj : j < gs.length), valid (8+j) gs[j]) ∧
      valid (8+gs.length) g ∧ 8 ≤ g.left ∧ 8 ≤ g.right ∧
      (∀ i < gs.length, ∃ t ∈ (gs++[g]).drop (i+1), t.left = 8+i ∨ t.right = 8+i) ∧
      12 ≤ gs.length + ((Finset.range 7).filter (fun i => p.count i = 1)).card ∧
      (∀ h ∈ gs++[g], h.left < 7 → h.right < 7 → p.count h.left ≠ 1 ∨ p.count h.right ≠ 1) ∧
      ∀ x, ((BinaryCircuit.eval ⟨gs++[g],8+gs.length⟩ (seed x)) != q) = f x)
    (exclude :
    let f := fun x : Fin 7 → Bool =>
      ([1,12,4,15,26,35,46,63] : List ℕ).any
        (fun e => x (Fin.ofNat 7 (e / 10)) && x (Fin.ofNat 7 (e % 10)))
    let seed (x : Fin 7 → Bool) := List.ofFn x ++ [false]
    let valid (n : ℕ) (t : BinaryGate) :=
      (∃ a b : Bool, t.op = fun x y => (x == a) && (y == b)) ∧
      t.left < n ∧ t.right < n ∧ t.left ≠ 7 ∧ t.right ≠ 7 ∧ t.left ≠ t.right
    ¬ (∃ (gs : List BinaryGate) (g : BinaryGate) (q : Bool),
      let p := (gs++[g]).flatMap fun t => [t.left,t.right]
      7 ≤ gs.length ∧ gs.length ≤ 9 ∧
      (∀ (j : ℕ) (hj : j < gs.length), valid (8+j) gs[j]) ∧
      valid (8+gs.length) g ∧ 8 ≤ g.left ∧ 8 ≤ g.right ∧
      (∀ i < gs.length, ∃ t ∈ (gs++[g]).drop (i+1), t.left = 8+i ∨ t.right = 8+i) ∧
      12 ≤ gs.length + ((Finset.range 7).filter (fun i => p.count i = 1)).card ∧
      (∀ h ∈ gs++[g], h.left < 7 → h.right < 7 → p.count h.left ≠ 1 ∨ p.count h.right ≠ 1) ∧
      ∀ x, ((BinaryCircuit.eval ⟨gs++[g],8+gs.length⟩ (seed x)) != q) = f x)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (PEqualNP.MetaComplexity.circuitFun (7 : ℕ) x1 = fun (x3 : Fin (7 : ℕ) → Bool) => [((0 : Fin (7 : ℕ)), (1 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (2 : Fin (7 : ℕ))), ((0 : Fin (7 : ℕ)), (4 : Fin (7 : ℕ))), ((1 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((2 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((3 : Fin (7 : ℕ)), (5 : Fin (7 : ℕ))), ((4 : Fin (7 : ℕ)), (6 : Fin (7 : ℕ))), ((6 : Fin (7 : ℕ)), (3 : Fin (7 : ℕ)))].any fun (x4 : Fin (7 : ℕ) × Fin (7 : ℕ)) => x3 x4.1 && x3 x4.2) → (11 : ℕ) ≤ List.countP (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.rec Bool.true Bool.true Bool.false (fun (x5 : ℕ) => Bool.true) Bool.true x4.op) x1.gates := by
  intro C fan good
  by_contra! short
  exact exclude (normalize C fan good (by omega))
