import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5757_525
    (transport :
      let S : Finset (Fin 13) := {0,1,3,9}
      let T := fun eval : List Bool → Bool =>
        (∀ p l : Fin 13, p - l ∈ S →
          eval (List.ofFn (fun j : Fin 13 => decide (j = p)) ++
            List.ofFn (fun j : Fin 13 => decide (j = l))) = true) ∧
        (∀ P : Finset (Fin 13), P.card = 4 →
          (∀ l : Fin 13, (P.filter fun p => p - l ∈ S).card ≤ 2) →
          eval (List.ofFn (fun j : Fin 13 => decide (j ∈ P)) ++
            List.ofFn (fun j : Fin 13 => decide (∀ p ∈ P, p - j ∉ S))) = false)
      let A := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (ops : List ℕ) =>
        T (fun x => C.eval (x ++ [ops.any fun j => x.getD j false]))
      let earlier := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
        ∀ (i : Fin C.gates.length), ∀ a ∈ (C.gates.get i).inputs, a < 27 + i.val
      let noAA := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
        ¬∃ (j : Fin C.gates.length), ∃ i ∈ (C.gates.get j).inputs, (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ 27 ≤ i ∧
          ∃ (k : Fin C.gates.length), i = 27 + k.val ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and
      let reps : List (List ℕ) := [[],[0],[13],[0,1],[0,2],[0,13],[0,14],[0,15],[0,17],[0,20],[13,14],[13,15]]
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (ops : List ℕ), ops.length ≤ 2 → PEqualNP.MetaComplexity.Monotone2 C → earlier C → A C ops → noAA C →
        ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (rep : List ℕ), rep ∈ reps ∧ PEqualNP.MetaComplexity.Monotone2 D ∧ earlier D ∧
          A D rep ∧ noAA D ∧ D.size ≤ C.size)
    (canonical :
      let S : Finset (Fin 13) := {0,1,3,9}
      let T := fun eval : List Bool → Bool =>
        (∀ p l : Fin 13, p - l ∈ S →
          eval (List.ofFn (fun j : Fin 13 => decide (j = p)) ++
            List.ofFn (fun j : Fin 13 => decide (j = l))) = true) ∧
        (∀ P : Finset (Fin 13), P.card = 4 →
          (∀ l : Fin 13, (P.filter fun p => p - l ∈ S).card ≤ 2) →
          eval (List.ofFn (fun j : Fin 13 => decide (j ∈ P)) ++
            List.ofFn (fun j : Fin 13 => decide (∀ p ∈ P, p - j ∉ S))) = false)
      let A := fun (C : PEqualNP.CircuitLowerBounds.Circuit) (ops : List ℕ) =>
        T (fun x => C.eval (x ++ [ops.any fun j => x.getD j false]))
      let earlier := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
        ∀ (i : Fin C.gates.length), ∀ a ∈ (C.gates.get i).inputs, a < 27 + i.val
      let noAA := fun C : PEqualNP.CircuitLowerBounds.Circuit =>
        ¬∃ (j : Fin C.gates.length), ∃ i ∈ (C.gates.get j).inputs, (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ 27 ≤ i ∧
          ∃ (k : Fin C.gates.length), i = 27 + k.val ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and
      let reps : List (List ℕ) := [[],[0],[13],[0,1],[0,2],[0,13],[0,14],[0,15],[0,17],[0,20],[13,14],[13,15]]
      ∀ (D : PEqualNP.CircuitLowerBounds.Circuit) (rep : List ℕ), rep ∈ reps → PEqualNP.MetaComplexity.Monotone2 D → earlier D → A D rep → noAA D →
        63 ≤ D.size) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   x2.length ≤ (2 : ℕ) →     PEqualNP.MetaComplexity.Monotone2 x1 →       (∀ (x5 : Fin x1.gates.length), ∀ x6 ∈ (x1.gates.get x5).inputs, x6 < (27 : ℕ) + ↑x5) →         have x6 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};         have x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x7 x8 : Fin (13 : ℕ)) => (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x7)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 = x8);         have x8 : Finset (Fin (13 : ℕ)) → List Bool := fun (x8 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x8)) ++ List.ofFn fun (x9 : Fin (13 : ℕ)) => Decidable.decide (∀ x10 ∈ x8, x10 - x9 ∉ x6);         have x9 : Finset (Fin (13 : ℕ)) → Prop := fun (x9 : Finset (Fin (13 : ℕ))) => x9.card = (4 : ℕ) ∧ ∀ (x10 : Fin (13 : ℕ)), {x11 ∈ x9 | x11 - x10 ∈ x6}.card ≤ (2 : ℕ);         have x10 : List Bool → List Bool := fun (x10 : List Bool) => x10 ++ [x2.any fun (x11 : ℕ) => x10.getD x11 Bool.false];         (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x6 → x1.eval (x10 (x7 x11 x12)) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), x9 x12 → x1.eval (x10 (x8 x12)) = Bool.false) → (¬∃ (x13 : Fin x1.gates.length), ∃ x14 ∈ (x1.gates.get x13).inputs, (x1.gates.get x13).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (27 : ℕ) ≤ x14 ∧ ∃ (x15 : Fin x1.gates.length), x14 = (27 : ℕ) + ↑x15 ∧ (x1.gates.get x15).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (63 : ℕ) ≤ x1.size := by
  intro C ops hlen hmono hear S positive negative quad augment hpos hneg hna
  obtain ⟨D, rep, hr, hd, hde, ha, hn, hs⟩ :=
    transport C ops hlen hmono hear ⟨hpos, fun P hcard hquad => hneg P ⟨hcard, hquad⟩⟩ hna
  exact (canonical D rep hr hd hde ha hn).trans hs
