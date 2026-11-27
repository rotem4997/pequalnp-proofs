import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The three degree-two vertices have isomorphic false restrictions.
-- Two gates reading any one of those inputs can both be eliminated.
set_option maxRecDepth 8000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_2012_1
    (contract : ∀ (n m s : ℕ) (C : Circuit) (v : Fin n) (p : Fin n → Fin m),
      let reader := fun (v : ℕ) (g : Gate) => v ∈ g.inputs ∧ (g.op = GateOp.not → g.inputs.head? = some v)
      let fixed := fun (y : Fin m → Bool) => C.eval (List.ofFn (fun i => if i = v then false else y (p i)))
      FanInTwo C → C.size ≤ s + 2 → fixed (fun _ => false) = false →
      (∃ i j : Fin C.gates.length, i ≠ j ∧ reader v (C.gates.get i) ∧ reader v (C.gates.get j)) →
      HasCircuitSize m fixed s)
    (minor : ¬ HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)) 12)
    (single : ∀ C : Circuit,
      let reader := fun (v : ℕ) (g : Gate) => v ∈ g.inputs ∧ (g.op = GateOp.not → g.inputs.head? = some v)
      FanInTwo C → (∀ v : Fin 9, v = 4 ∨ v = 6 ∨ v = 7 →
        ∀ (i j : Fin C.gates.length), reader v (C.gates.get i) → reader v (C.gates.get j) → i = j) →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = (fun x : Fin 9 → Bool => ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) x) → 15 ≤ C.size) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) x1 (14 : ℕ) := by
  let f := fun x : Fin 9 → Bool => ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  let h := fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) || (x 5 && x 7) || (x 7 && x 4)
  let reader := fun (v : ℕ) (g : Gate) => v ∈ g.inputs ∧ (g.op = GateOp.not → g.inputs.head? = some v)
  change ¬ HasCircuitSize 9 f 14
  rintro ⟨C, fan, size, computes⟩
  have unique : ∀ v : Fin 9, v = 4 ∨ v = 6 ∨ v = 7 → ∀ (i j : Fin C.gates.length), reader v (C.gates.get i) → reader v (C.gates.get j) → i = j := by
    intro v hv i j hi hj
    by_contra different
    have ruled (p : Fin 9 → Fin 8)
        (eqn : ∀ y : Fin 8 → Bool, f (fun i => if i = v then false else y (p i)) = h y) : False := by
      have fixed (y : Fin 8 → Bool) :
          C.eval (List.ofFn (fun i => if i = v then false else y (p i))) = h y :=
        (computes _).trans (eqn y)
      have zero : h (fun _ => false) = false := rfl
      have small := contract 9 8 12 C v p fan size ((fixed (fun _ => false)).trans zero)
        ⟨i, j, different, hi, hj⟩
      apply minor
      have same : (fun y : Fin 8 → Bool => C.eval (List.ofFn (fun i => if i = v then false else y (p i)))) = h :=
        funext fixed
      rwa [same] at small
    rcases hv with rfl | rfl | rfl
    · apply ruled ![0, 1, 2, 3, 0, 4, 5, 6, 7]
      decide +kernel
    · apply ruled ![1, 0, 4, 7, 5, 2, 0, 6, 3]
      decide +kernel
    · apply ruled ![1, 2, 3, 7, 5, 0, 6, 0, 4]
      decide +kernel
  have lower := single C fan unique computes
  omega
