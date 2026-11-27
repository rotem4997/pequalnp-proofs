import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The Petersen binary lower bound counts AND and OR gates with negations free.
-- One NOT consumes the only remaining gate in the fifteen-gate budget.
theorem PEqualNP.Outside.R_meta_4225_823
    (lower : ∀ C : Circuit, FanInTwo C → circuitFun 9 C = (fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List Nat).any fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 e)) →
      14 ≤ C.gates.countP (fun g : Gate => !(GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op)))
    (single : ∀ (C : Circuit), IsMinimalCircuit 9 C → circuitFun 9 C = (fun x : Fin 9 → Bool => ([1,11,21,31,36,5,15,25,35,52,62,77] : List Nat).any fun e => x (Fin.ofNat 9 (e / 9)) && x (Fin.ofNat 9 e)) →
      (∀ i : Fin C.size, (∀ w ∈ (C.gates.get i).inputs, w < 9 + i.val) ∧ (C.gates.get i).inputs.Nodup ∧
        (((C.gates.get i).op = .not ∧ (C.gates.get i).inputs.length = 1) ∨
         ((C.gates.get i).op ≠ .not ∧ (C.gates.get i).inputs.length = 2))) →
      (∀ u ∈ ([4,6,7] : List (Fin 9)), ∃ i : Fin C.size,
        (∀ j : Fin C.size, u.val ∈ (C.gates.get j).inputs ↔ j = i) ∧ (C.gates.get i).op = .or) →
      (∀ i : Fin C.size, ∀ a ∈ (C.gates.get i).inputs, ∀ b ∈ (C.gates.get i).inputs,
        a ∈ ([4,6,7] : List Nat) → b ∈ ([4,6,7] : List Nat) → a = b) →
      C.size = 15 → C.gates.countP (fun g : Gate => GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op) = 1 → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x1 → x1.size ≤ (15 : ℕ) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x5 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x4 x5.1 && x4 x5.2) → (∀ (x5 : Fin x1.size), (∀ x6 ∈ (x1.gates.get x5).inputs, x6 < (9 : ℕ) + ↑x5) ∧ (x1.gates.get x5).inputs.Nodup ∧ ((x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x5).inputs.length = (1 : ℕ) ∨ (x1.gates.get x5).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x5).inputs.length = (2 : ℕ))) → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], ∃ (x8 : Fin x1.size), (∀ (x9 : Fin x1.size), ↑x6 ∈ (x1.gates.get x9).inputs ↔ x9 = x8) ∧ (x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ (x7 : Fin x1.size), ∀ x8 ∈ (x1.gates.get x7).inputs, ∀ x10 ∈ (x1.gates.get x7).inputs, x8 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)] → x10 ∈ [(4 : ℕ), (6 : ℕ), (7 : ℕ)] → x8 = x10) → (∃ (x8 : Fin x1.size), (x1.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.not) → False := by
  intro C minimal size computes regular uniqueUse separate hasNot
  let p : Gate → Bool := (fun g : Gate => GateOp.rec (motive := fun _ => Bool) false false true (fun _ => false) false g.op)
  have bin : 14 ≤ C.gates.countP (fun g => !(p g)) := lower C minimal.1 computes
  have part : C.size = C.gates.countP p + C.gates.countP (fun g => !(p g)) := by
    change C.gates.length = _
    simpa using (List.length_eq_countP_add_countP p (l := C.gates))
  obtain ⟨i, hop⟩ := hasNot
  have pos : 0 < C.gates.countP p := List.countP_pos_iff.mpr
    ⟨C.gates.get i, List.get_mem _ _, by simp [p, hop]⟩
  exact single C minimal computes regular uniqueUse separate (by omega) (show C.gates.countP p = 1 by omega)
