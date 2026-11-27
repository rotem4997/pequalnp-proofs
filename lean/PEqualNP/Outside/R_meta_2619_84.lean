import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

-- Synthesize the two final AND operands on the edge and closed false rows.
-- The other steps assemble the gate and extend the tests by monotonicity.
theorem PEqualNP.Outside.R_meta_2619_84
    (prefixWitness : let hit : (Fin 13 → Bool) → Fin 13 → Bool := fun x l => x l || x (l+1) || x (l+3) || x (l+9)
      let inc : Fin 13 → Fin 13 → Prop := fun p l => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
      let row : (Fin 13 → Bool) → (Fin 13 → Bool) → List Bool := fun x y =>
        List.ofFn fun z : Fin (13+13) => Fin.addCases x y z
      let one : Fin 13 → Fin 13 → Bool := fun p z => decide (z = p)
      let test : Circuit → ℕ → ℕ → List Bool → Bool := fun C a b w =>
        (C.wires w).getD a false && (C.wires w).getD b false
      ∃ (C : Circuit) (a b : ℕ), C.size ≤ 63 ∧ IsAO2 26 C ∧
        (∀ g ∈ C.gates, g.inputs.Nodup) ∧ a ≠ b ∧ a < 26+C.size ∧ b < 26+C.size ∧
        (∀ p l, inc p l → test C a b (row (one p) (one l)) = true) ∧
        (∀ x, (∀ p, x p = false → ∃ l, inc p l ∧ hit x l = false) →
          test C a b (row x (fun l => !(hit x l))) = false) ∧
        ∀ t : Bool, let w := C.wires (List.ofFn fun z : Fin 26 => decide (z.val = if t = true then 13 else 0))
          w.getD a false = false ∧ w.getD b false = false)
    (appendAnd : ∀ (n : ℕ) (C : Circuit) (a b : ℕ),
      IsAO2 n C → (∀ g ∈ C.gates, g.inputs.Nodup) → a ≠ b → a < n+C.size → b < n+C.size →
      let D : Circuit := ⟨C.gates ++ [⟨.and,[a,b]⟩], n+C.size⟩
      IsAO2 n D ∧ (∀ g ∈ D.gates, g.inputs.Nodup) ∧
        ∀ w : List Bool, w.length = n →
          D.eval w = ((C.wires w).getD a false && (C.wires w).getD b false) ∧
          (D.wires w).getD a false = (C.wires w).getD a false ∧
          (D.wires w).getD b false = (C.wires w).getD b false)
    (complete : let hit : (Fin 13 → Bool) → Fin 13 → Bool := fun x l => x l || x (l+1) || x (l+3) || x (l+9)
      let inc : Fin 13 → Fin 13 → Prop := fun p l => p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9
      let row : (Fin 13 → Bool) → (Fin 13 → Bool) → List Bool := fun x y =>
        List.ofFn fun z : Fin (13+13) => Fin.addCases x y z
      let one : Fin 13 → Fin 13 → Bool := fun p z => decide (z = p)
      ∀ C : Circuit, IsAO2 26 C →
        (∀ p l, inc p l → C.eval (row (one p) (one l)) = true) →
        (∀ x, (∀ p, x p = false → ∃ l, inc p l ∧ hit x l = false) →
          C.eval (row x (fun l => !(hit x l))) = false) →
        ∀ x y, C.eval (row x y) = true ↔ ∃ l, y l = true ∧ hit x l = true) :
    ∃ C : Circuit, C.size ≤ 64 ∧ IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      (∀ x y : Fin 13 → Bool, C.eval (List.ofFn fun z : Fin (13+13) => Fin.addCases x y z) = true ↔
        ∃ l : Fin 13, y l = true ∧ (x l || x (l+1) || x (l+3) || x (l+9)) = true) ∧
      ∃ j a b : ℕ, C.output = 26+j ∧ C.gates[j]? = some ⟨.and,[a,b]⟩ ∧
        ∀ t : Bool, let w := C.wires (List.ofFn fun z : Fin 26 => decide (z.val = if t = true then 13 else 0))
          w.getD a false = false ∧ w.getD b false = false := by
  obtain ⟨C,a,b,small,shape,unique,distinct,ha,hb,positive,negative,singletons⟩ := prefixWitness
  let D : Circuit := ⟨C.gates ++ [⟨.and,[a,b]⟩], 26+C.size⟩
  obtain ⟨shapeD, uniqueD, values⟩ := appendAnd 26 C a b shape unique distinct ha hb
  have sizeD : D.size ≤ 64 := by
    change (C.gates ++ [Gate.mk .and [a,b]]).length ≤ 64
    rw [List.length_append, List.length_singleton]
    exact Nat.add_le_add_right small 1
  have correct := complete D shapeD (fun p l inc => by
    have e := values (List.ofFn fun z : Fin (13+13) =>
      Fin.addCases (fun w => decide (w = p)) (fun w => decide (w = l)) z) (by simp)
    exact e.1.trans (positive p l inc)) (fun x closed => by
    have e := values (List.ofFn fun z : Fin (13+13) =>
      Fin.addCases x (fun l => !(x l || x (l+1) || x (l+3) || x (l+9))) z) (by simp)
    exact e.1.trans (negative x closed))
  refine ⟨D,sizeD,shapeD,uniqueD,correct,C.size,a,b,rfl,?_,?_⟩
  · change (C.gates ++ [Gate.mk .and [a,b]])[C.gates.length]? = some ⟨.and,[a,b]⟩
    simp
  · intro t
    let w := List.ofFn fun z : Fin 26 => decide (z.val = if t = true then 13 else 0)
    have e := values w (by simp [w])
    exact ⟨e.2.1.trans (singletons t).1, e.2.2.trans (singletons t).2⟩
