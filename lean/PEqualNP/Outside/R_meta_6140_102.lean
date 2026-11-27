import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_6140_102
    (small :
      let diff : Finset (Fin 13) := {0,1,3,9}
      let F : (Fin 26 → Bool) → Prop := fun x => ∃ p l : Fin 13,
        p-l ∈ diff ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true
      let valid : Circuit → Prop := fun C => Monotone2 C ∧ ReadsBack 26 C ∧
        ∀ x, C.eval (List.ofFn x)=true ↔ F x
      let pair : Fin 26 → Fin 26 → Fin 26 → Bool := fun a b i => decide (i=a ∨ i=b)
      let hit : Circuit → Fin 26 → Fin 26 → Prop := fun C a b => ∃ j : Fin C.gates.length,
        (C.gates.get j).op = GateOp.and ∧ (C.wires (List.ofFn (pair a b))).getD (26+j.val) false = true
      ∀ C, valid C → C.size ≤ 63 → ∃ a b, ¬F (pair a b) ∧ hit C a b)
    (move :
      let diff : Finset (Fin 13) := {0,1,3,9}
      let F : (Fin 26 → Bool) → Prop := fun x => ∃ p l : Fin 13,
        p-l ∈ diff ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true
      let valid : Circuit → Prop := fun C => Monotone2 C ∧ ReadsBack 26 C ∧
        ∀ x, C.eval (List.ofFn x)=true ↔ F x
      let pair : Fin 26 → Fin 26 → Fin 26 → Bool := fun a b i => decide (i=a ∨ i=b)
      let hit : Circuit → Fin 26 → Fin 26 → Prop := fun C a b => ∃ j : Fin C.gates.length,
        (C.gates.get j).op = GateOp.and ∧ (C.wires (List.ofFn (pair a b))).getD (26+j.val) false = true
      ∀ C, valid C → ∀ a b, ¬F (pair a b) → hit C a b →
        ∃ D, valid D ∧ D.size ≤ C.size ∧ (hit D 0 1 ∨ hit D 0 14))
    (same :
      let diff : Finset (Fin 13) := {0,1,3,9}
      let F : (Fin 26 → Bool) → Prop := fun x => ∃ p l : Fin 13,
        p-l ∈ diff ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true
      let valid : Circuit → Prop := fun C => Monotone2 C ∧ ReadsBack 26 C ∧
        ∀ x, C.eval (List.ofFn x)=true ↔ F x
      let pair : Fin 26 → Fin 26 → Fin 26 → Bool := fun a b i => decide (i=a ∨ i=b)
      let hit : Circuit → Fin 26 → Fin 26 → Prop := fun C a b => ∃ j : Fin C.gates.length,
        (C.gates.get j).op = GateOp.and ∧ (C.wires (List.ofFn (pair a b))).getD (26+j.val) false = true
      ∀ C, valid C → (∀ D, valid D → C.size ≤ D.size) → hit C 0 1 → 64 ≤ C.size)
    (opposite :
      let diff : Finset (Fin 13) := {0,1,3,9}
      let F : (Fin 26 → Bool) → Prop := fun x => ∃ p l : Fin 13,
        p-l ∈ diff ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true
      let valid : Circuit → Prop := fun C => Monotone2 C ∧ ReadsBack 26 C ∧
        ∀ x, C.eval (List.ofFn x)=true ↔ F x
      let pair : Fin 26 → Fin 26 → Fin 26 → Bool := fun a b i => decide (i=a ∨ i=b)
      let hit : Circuit → Fin 26 → Fin 26 → Prop := fun C a b => ∃ j : Fin C.gates.length,
        (C.gates.get j).op = GateOp.and ∧ (C.wires (List.ofFn (pair a b))).getD (26+j.val) false = true
      ∀ C, valid C → (∀ D, valid D → C.size ≤ D.size) → hit C 0 14 → 64 ≤ C.size)
    : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x3 : Fin (26 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), x4 - x5 ∈ x1 ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x3 → x2 x3 → (∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x7 → x2 x7 → x3.size ≤ x7.size) → (∃ (x8 : ℕ) (x9 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x8).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x8 x9) → (64 : ℕ) ≤ x3.size := by
  dsimp only
  intro C mono back exactC least _nested
  let diff : Finset (Fin 13) := {0,1,3,9}
  let F : (Fin 26 → Bool) → Prop := fun x => ∃ p l : Fin 13,
    p-l ∈ diff ∧ x (Fin.castAdd 13 p)=true ∧ x (Fin.natAdd 13 l)=true
  let valid : Circuit → Prop := fun C => Monotone2 C ∧ ReadsBack 26 C ∧
    ∀ x, C.eval (List.ofFn x)=true ↔ F x
  have vc : valid C := ⟨mono,back,exactC⟩
  have leastC (D) (vD : valid D) : C.size ≤ D.size := least D vD.1 vD.2.1 vD.2.2
  by_contra! lower
  obtain ⟨a,b,neg,hit⟩ := small C vc (by omega)
  obtain ⟨D,vD,cost,hD⟩ := move C vc a b neg hit
  have leastD (K) (vK : valid K) : D.size ≤ K.size := cost.trans (leastC K vK)
  rcases hD with p|p
  · have h64 := same D vD leastD p
    omega
  · have h64 := opposite D vD leastD p
    omega
