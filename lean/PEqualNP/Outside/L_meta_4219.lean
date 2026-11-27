import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4219

theorem wires_getD (C : PEqualNP.CircuitLowerBounds.Circuit) (xs : List Bool) (i : ℕ)
    (hi : i < xs.length) : (C.wires xs).getD i false = xs.getD i false := by
  unfold PEqualNP.CircuitLowerBounds.Circuit.wires
  generalize C.gates = gs
  induction gs generalizing xs with
  | nil => rfl
  | cons g rest ih =>
    rw [List.foldl_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

def pt (X Y : Finset (Fin 13)) : Fin 26 → Bool :=
  fun (x9 : Fin (26 : ℕ)) => if ↑x9 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x9 ∈ X) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x9 ∈ Y)

theorem key : ∀ i < 26, ¬ ((List.ofFn (pt {0} {0})).getD i false = true ∧
    (List.ofFn (pt {1} {12})).getD i false = true) := by
  decide

end PEqualNP.Outside.L_meta_4219

theorem PEqualNP.Outside.L_meta_4219 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 →     x2.length ≤ (2 : ℕ) →       (∀ x5 ∈ x2, x5 < (26 : ℕ)) →         (let x6 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x6 x7 : Fin (13 : ℕ)) => (↑x6 + ↑x7) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];           have x7 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x7 x8 : Finset (Fin (13 : ℕ))) (x9 : Fin (26 : ℕ)) => if ↑x9 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x9 ∈ x7) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x9 ∈ x8);           have x8 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x8 : Finset (Fin (13 : ℕ))) => {x9 : Fin (13 : ℕ) | ∀ x10 ∈ x8, ¬x6 x10 x9};           have x9 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x9 x10 : Finset (Fin (13 : ℕ))) => PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x11 : ℕ) => (x1.wires (List.ofFn (x7 x9 x10))).getD x11 Bool.false) x2);           (∀ (x10 x11 : Fin (13 : ℕ)), x6 x10 x11 → x9 {x10} {x11} = Bool.true) ∧ ∀ (x10 : Finset (Fin (13 : ℕ))), x10.card ≤ (3 : ℕ) → x9 x10 (x8 x10) = Bool.false ∧ x9 (x8 x10) x10 = Bool.false) →           (63 : ℕ) ≤ x1.size := by
  intro C l _ _ hlt h
  obtain ⟨hinc, hfalse⟩ := h
  cases l with
  | nil =>
    have h0 := (hfalse ∅ (by simp)).1
    simp [PEqualNP.CircuitLowerBounds.GateOp.eval] at h0
  | cons i rest =>
    have hi : i < 26 := hlt i (by simp)
    have a := hinc 0 0 (by decide)
    have b := hinc 1 12 (by decide)
    simp only [List.map_cons, PEqualNP.CircuitLowerBounds.GateOp.eval, List.all_cons, Bool.and_eq_true, id] at a b
    have a1 := a.1
    have b1 := b.1
    rw [PEqualNP.Outside.L_meta_4219.wires_getD _ _ _ (by simpa using hi)] at a1 b1
    exact (PEqualNP.Outside.L_meta_4219.key i hi ⟨a1, b1⟩).elim
