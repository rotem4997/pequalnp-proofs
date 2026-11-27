import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_7235

theorem main (x1 : Circuit) (x2 x3 : ℕ) (h2 : x2 < 14 + x1.size) (hg : x1.gates = [])
    (P : (Fin 14 → Bool) → Prop)
    (hP : ∀ f, P f → ∃ a b : Fin 14, a.val ≠ b.val ∧ f a = true ∧ f b = true)
    (H : ∀ f : Fin 14 → Bool, ¬P f → (x1.wires (List.ofFn f)).getD x2 false = false ∧ (x1.wires (List.ofFn f)).getD x3 false = false) : False := by
  have hsz : x1.size = 0 := by simp [Circuit.size, hg]
  have hx : x2 < 14 := by omega
  have hn : ¬ P (fun i : Fin 14 => decide (i.val = x2)) := by
    intro hp
    obtain ⟨a, b, hab, ha, hb⟩ := hP _ hp
    simp only [decide_eq_true_eq] at ha hb
    omega
  have h := (H _ hn).1
  have hw : x1.wires (List.ofFn fun i : Fin 14 => decide (i.val = x2)) = List.ofFn fun i : Fin 14 => decide (i.val = x2) := by
    simp [Circuit.wires, hg]
  rw [hw] at h
  simp [List.getD_eq_getElem?_getD, hx] at h
  clear hn hw H hP h2 hsz
  interval_cases x2 <;> simp at h

end PEqualNP.Outside.L_meta_7235

theorem PEqualNP.Outside.L_meta_7235 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2 < (14 : ℕ) + x1.size →       x3 < (14 : ℕ) + x1.size →         have x7 : List (ℕ × ℕ) := [((0 : ℕ), (7 : ℕ)), ((0 : ℕ), (8 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (7 : ℕ)), ((1 : ℕ), (9 : ℕ)), ((1 : ℕ), (13 : ℕ)), ((2 : ℕ), (8 : ℕ)), ((2 : ℕ), (12 : ℕ)), ((2 : ℕ), (13 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((3 : ℕ), (11 : ℕ)), ((3 : ℕ), (12 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((4 : ℕ), (11 : ℕ)), ((4 : ℕ), (13 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((5 : ℕ), (10 : ℕ)), ((5 : ℕ), (12 : ℕ)), ((6 : ℕ), (8 : ℕ)), ((6 : ℕ), (9 : ℕ)), ((6 : ℕ), (11 : ℕ))];         have x8 : (Fin (14 : ℕ) → Bool) → Prop := fun (x8 : Fin (14 : ℕ) → Bool) => ∃ (x9 : Fin (14 : ℕ)) (x10 : Fin (14 : ℕ)), (↑x9, ↑x10) ∈ x7 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true;         have x9 : ℕ → (Fin (14 : ℕ) → Bool) → Bool := fun (x9 : ℕ) (x10 : Fin (14 : ℕ) → Bool) => (x1.wires (List.ofFn x10)).getD x9 Bool.false;         (∀ (x10 : Fin (14 : ℕ) → Bool), x8 x10 → x9 x2 x10 = Bool.true ∨ x9 x3 x10 = Bool.true) → (∀ (x11 : Fin (14 : ℕ) → Bool), ¬x8 x11 → x9 x2 x11 = Bool.false ∧ x9 x3 x11 = Bool.false) → (∃ (x12 : Fin (14 : ℕ) → Bool), x8 x12 ∧ x9 x2 x12 = Bool.true ∧ x9 x3 x12 = Bool.false) → (∃ (x13 : Fin (14 : ℕ) → Bool), x8 x13 ∧ x9 x3 x13 = Bool.true ∧ x9 x2 x13 = Bool.false) → x1.gates = [] → (26 : ℕ) ≤ x1.size := by
  intro x1 x2 x3 hm h2 h3
  exact fun _ H _ _ hg => (PEqualNP.Outside.L_meta_7235.main x1 x2 x3 h2 hg _ (fun f hf => by
    obtain ⟨a, b, hab, ha, hb⟩ := hf
    refine ⟨a, b, ?_, ha, hb⟩
    intro e
    rw [e] at hab
    simp at hab
    omega) H).elim
