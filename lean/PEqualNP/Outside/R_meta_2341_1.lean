import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2341_1 :
  (let D : Finset (Fin 13) := {0,1,3,9}
    let pos := fun (p l : Fin 13) => (List.ofFn fun i : Fin 13 => decide (i = p)) ++ List.ofFn fun i : Fin 13 => decide (i = l)
    let neg := fun (Q : Finset (Fin 13)) => (List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++ List.ofFn fun i : Fin 13 => decide (∀ p ∈ Q, p-i ∉ D)
    let quad := fun (Q : Finset (Fin 13)) => Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter fun p => p-l ∈ D).card ≤ 2
    ∀ (c : PEqualNP.CircuitLowerBounds.Circuit) (a : Fin 13) (b : Bool), PEqualNP.MetaComplexity.Monotone2 c → (∀ j : Fin c.gates.length, ∀ i ∈ (c.gates.get j).inputs, i < 27 + j.val) →
      (∀ Q, quad Q → c.eval (neg Q ++ [b]) = false) →
      ∃ e : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 e ∧ (∀ j : Fin e.gates.length, ∀ i ∈ (e.gates.get j).inputs, i < 27 + j.val) ∧ e.size ≤ c.size ∧
        (∀ p l, e.eval (pos p l ++ [b]) = c.eval (pos (p+a) (l+a) ++ [b])) ∧
        ∀ Q, quad Q → e.eval (neg Q ++ [b]) = false) →
  (let D : Finset (Fin 13) := {0,1,3,9}
    let pos := fun (p l : Fin 13) => (List.ofFn fun i : Fin 13 => decide (i = p)) ++ List.ofFn fun i : Fin 13 => decide (i = l)
    let neg := fun (Q : Finset (Fin 13)) => (List.ofFn fun i : Fin 13 => decide (i ∈ Q)) ++ List.ofFn fun i : Fin 13 => decide (∀ p ∈ Q, p-i ∉ D)
    let quad := fun (Q : Finset (Fin 13)) => Q.card = 4 ∧ ∀ l : Fin 13, (Q.filter fun p => p-l ∈ D).card ≤ 2
    ∀ (c : PEqualNP.CircuitLowerBounds.Circuit) (l : Fin 13) (b : Bool), PEqualNP.MetaComplexity.Monotone2 c → (∀ j : Fin c.gates.length, ∀ i ∈ (c.gates.get j).inputs, i < 27 + j.val) →
      (∀ p j, p-j ∈ D → p ≠ 0 ∨ j ≠ l → c.eval (pos p j ++ [b]) = true) →
      (∀ Q, quad Q → c.eval (neg Q ++ [b]) = false) → 63 ≤ c.size) →
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin (13 : ℕ)) (x4 : Bool),   PEqualNP.MetaComplexity.Monotone2 x1 →     (∀ (x6 : Fin x1.gates.length), ∀ x7 ∈ (x1.gates.get x6).inputs, x7 < (27 : ℕ) + ↑x6) →       have x7 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};       have x8 : Fin (13 : ℕ) → Fin (13 : ℕ) → List Bool := fun (x8 x9 : Fin (13 : ℕ)) => (List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 = x8)) ++ List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 = x9);       have x9 : Finset (Fin (13 : ℕ)) → List Bool := fun (x9 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (x10 ∈ x9)) ++ List.ofFn fun (x10 : Fin (13 : ℕ)) => Decidable.decide (∀ x11 ∈ x9, x11 - x10 ∉ x7);       have x10 : Finset (Fin (13 : ℕ)) → Prop := fun (x10 : Finset (Fin (13 : ℕ))) => x10.card = (4 : ℕ) ∧ ∀ (x11 : Fin (13 : ℕ)), {x12 ∈ x10 | x12 - x11 ∈ x7}.card ≤ (2 : ℕ);       (∀ (x11 x12 : Fin (13 : ℕ)), x11 - x12 ∈ x7 → x11 ≠ x2 ∨ x12 ≠ x3 → x1.eval (x8 x11 x12 ++ [x4]) = Bool.true) → (∀ (x12 : Finset (Fin (13 : ℕ))), x10 x12 → x1.eval (x9 x12 ++ [x4]) = Bool.false) → (63 : ℕ) ≤ x1.size := by
  intro transport normalized c a l b hm hw
  dsimp only
  intro hp hn
  obtain ⟨e, em, ew, sz, ep, en⟩ := transport c a b hm hw hn
  apply Nat.le_trans (normalized e (l-a) b em ew ?_ en) sz
  intro p j inc ne
  rw [ep]
  apply hp
  · simpa only [add_sub_add_right_eq_sub] using inc
  · rcases ne with h | h
    · left
      exact fun eq => h (add_left_cancel (show a+p = a+0 by simpa [add_comm] using eq))
    · right
      exact fun eq => h (eq_sub_of_add_eq eq)
