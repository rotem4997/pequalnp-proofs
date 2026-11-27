import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_5825_41
    (firstWire : ∀ (x1 x2 : Fin (10 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (17 : ℕ)),   x1 ≠ x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (17 : ℕ) →         have x9 : PEqualNP.CircuitLowerBounds.Gate := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [↑x1, ↑x2] : PEqualNP.CircuitLowerBounds.Gate };         have x10 : (Fin (10 : ℕ) → Bool) → Bool := fun (x10 : Fin (10 : ℕ) → Bool) => x10 (0 : Fin (10 : ℕ)) && x10 (1 : Fin (10 : ℕ)) || x10 (1 : Fin (10 : ℕ)) && x10 (2 : Fin (10 : ℕ)) || x10 (2 : Fin (10 : ℕ)) && x10 (3 : Fin (10 : ℕ)) || x10 (3 : Fin (10 : ℕ)) && x10 (4 : Fin (10 : ℕ)) || x10 (4 : Fin (10 : ℕ)) && x10 (0 : Fin (10 : ℕ)) || x10 (0 : Fin (10 : ℕ)) && x10 (5 : Fin (10 : ℕ)) || x10 (1 : Fin (10 : ℕ)) && x10 (6 : Fin (10 : ℕ)) || x10 (2 : Fin (10 : ℕ)) && x10 (7 : Fin (10 : ℕ)) || x10 (3 : Fin (10 : ℕ)) && x10 (8 : Fin (10 : ℕ)) || x10 (4 : Fin (10 : ℕ)) && x10 (9 : Fin (10 : ℕ)) || x10 (5 : Fin (10 : ℕ)) && x10 (7 : Fin (10 : ℕ)) || x10 (7 : Fin (10 : ℕ)) && x10 (9 : Fin (10 : ℕ)) || x10 (9 : Fin (10 : ℕ)) && x10 (6 : Fin (10 : ℕ)) || x10 (6 : Fin (10 : ℕ)) && x10 (8 : Fin (10 : ℕ)) || x10 (8 : Fin (10 : ℕ)) && x10 (5 : Fin (10 : ℕ));         have x11 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x11 : Fin (10 : ℕ) → Bool) (x12 : ℕ) => (x3.wires ({ gates := [x9], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x11))).getD x12 Bool.false;         (∃ (x12 : Fin (10 : ℕ) → Bool), (x12 x1 && x12 x2) = Bool.true ∧ x11 x12 ((11 : ℕ) + ↑x4) = Bool.false) → (∃ (x13 : Fin (10 : ℕ) → Bool), (x13 x1 && x13 x2) = Bool.false ∧ x11 x13 ((11 : ℕ) + ↑x4) = Bool.true) → (∀ (x14 : Fin (10 : ℕ) → Bool), x10 x14 = Bool.false → (x14 x1 && x14 x2) = Bool.false ∧ x11 x14 ((11 : ℕ) + ↑x4) = Bool.false) → ∃ (x15 : Fin (10 : ℕ) → Bool), x10 x15 = Bool.true ∧ (x15 x1 && x15 x2) = Bool.false ∧ x11 x15 ((11 : ℕ) + ↑x4) = Bool.false)
    (laterWires : ∀ (x1 x2 : Fin (10 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : Fin (17 : ℕ)),   x1 ≠ x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (17 : ℕ) →         have x9 : PEqualNP.CircuitLowerBounds.Gate := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [↑x1, ↑x2] : PEqualNP.CircuitLowerBounds.Gate };         have x10 : (Fin (10 : ℕ) → Bool) → Bool := fun (x10 : Fin (10 : ℕ) → Bool) => x10 (0 : Fin (10 : ℕ)) && x10 (1 : Fin (10 : ℕ)) || x10 (1 : Fin (10 : ℕ)) && x10 (2 : Fin (10 : ℕ)) || x10 (2 : Fin (10 : ℕ)) && x10 (3 : Fin (10 : ℕ)) || x10 (3 : Fin (10 : ℕ)) && x10 (4 : Fin (10 : ℕ)) || x10 (4 : Fin (10 : ℕ)) && x10 (0 : Fin (10 : ℕ)) || x10 (0 : Fin (10 : ℕ)) && x10 (5 : Fin (10 : ℕ)) || x10 (1 : Fin (10 : ℕ)) && x10 (6 : Fin (10 : ℕ)) || x10 (2 : Fin (10 : ℕ)) && x10 (7 : Fin (10 : ℕ)) || x10 (3 : Fin (10 : ℕ)) && x10 (8 : Fin (10 : ℕ)) || x10 (4 : Fin (10 : ℕ)) && x10 (9 : Fin (10 : ℕ)) || x10 (5 : Fin (10 : ℕ)) && x10 (7 : Fin (10 : ℕ)) || x10 (7 : Fin (10 : ℕ)) && x10 (9 : Fin (10 : ℕ)) || x10 (9 : Fin (10 : ℕ)) && x10 (6 : Fin (10 : ℕ)) || x10 (6 : Fin (10 : ℕ)) && x10 (8 : Fin (10 : ℕ)) || x10 (8 : Fin (10 : ℕ)) && x10 (5 : Fin (10 : ℕ));         have x11 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x11 : Fin (10 : ℕ) → Bool) (x12 : ℕ) => (x3.wires ({ gates := [x9], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x11))).getD x12 Bool.false;         (∃ (x12 : Fin (10 : ℕ) → Bool), x11 x12 ((11 : ℕ) + ↑x4) = Bool.true ∧ x11 x12 ((11 : ℕ) + ↑x5) = Bool.false) → (∃ (x13 : Fin (10 : ℕ) → Bool), x11 x13 ((11 : ℕ) + ↑x4) = Bool.false ∧ x11 x13 ((11 : ℕ) + ↑x5) = Bool.true) → (∀ (x14 : Fin (10 : ℕ) → Bool), x10 x14 = Bool.false → x11 x14 ((11 : ℕ) + ↑x4) = Bool.false ∧ x11 x14 ((11 : ℕ) + ↑x5) = Bool.false) → ∃ (x15 : Fin (10 : ℕ) → Bool), x10 x15 = Bool.true ∧ x11 x15 ((11 : ℕ) + ↑x4) = Bool.false ∧ x11 x15 ((11 : ℕ) + ↑x5) = Bool.false)
    : ∀ (x1 x2 : Fin (10 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : Fin (18 : ℕ)),   x1 ≠ x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (17 : ℕ) →         have x9 : PEqualNP.CircuitLowerBounds.Gate := { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [↑x1, ↑x2] : PEqualNP.CircuitLowerBounds.Gate };         have x10 : (Fin (10 : ℕ) → Bool) → Bool := fun (x10 : Fin (10 : ℕ) → Bool) => x10 (0 : Fin (10 : ℕ)) && x10 (1 : Fin (10 : ℕ)) || x10 (1 : Fin (10 : ℕ)) && x10 (2 : Fin (10 : ℕ)) || x10 (2 : Fin (10 : ℕ)) && x10 (3 : Fin (10 : ℕ)) || x10 (3 : Fin (10 : ℕ)) && x10 (4 : Fin (10 : ℕ)) || x10 (4 : Fin (10 : ℕ)) && x10 (0 : Fin (10 : ℕ)) || x10 (0 : Fin (10 : ℕ)) && x10 (5 : Fin (10 : ℕ)) || x10 (1 : Fin (10 : ℕ)) && x10 (6 : Fin (10 : ℕ)) || x10 (2 : Fin (10 : ℕ)) && x10 (7 : Fin (10 : ℕ)) || x10 (3 : Fin (10 : ℕ)) && x10 (8 : Fin (10 : ℕ)) || x10 (4 : Fin (10 : ℕ)) && x10 (9 : Fin (10 : ℕ)) || x10 (5 : Fin (10 : ℕ)) && x10 (7 : Fin (10 : ℕ)) || x10 (7 : Fin (10 : ℕ)) && x10 (9 : Fin (10 : ℕ)) || x10 (9 : Fin (10 : ℕ)) && x10 (6 : Fin (10 : ℕ)) || x10 (6 : Fin (10 : ℕ)) && x10 (8 : Fin (10 : ℕ)) || x10 (8 : Fin (10 : ℕ)) && x10 (5 : Fin (10 : ℕ));         have x11 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x11 : Fin (10 : ℕ) → Bool) (x12 : ℕ) => (x3.wires ({ gates := [x9], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x11))).getD x12 Bool.false;         (∃ (x12 : Fin (10 : ℕ) → Bool), x11 x12 ((10 : ℕ) + ↑x4) = Bool.true ∧ x11 x12 ((10 : ℕ) + ↑x5) = Bool.false) → (∃ (x13 : Fin (10 : ℕ) → Bool), x11 x13 ((10 : ℕ) + ↑x4) = Bool.false ∧ x11 x13 ((10 : ℕ) + ↑x5) = Bool.true) → (∀ (x14 : Fin (10 : ℕ) → Bool), x10 x14 = Bool.false → x11 x14 ((10 : ℕ) + ↑x4) = Bool.false ∧ x11 x14 ((10 : ℕ) + ↑x5) = Bool.false) → ∃ (x15 : Fin (10 : ℕ) → Bool), x10 x15 = Bool.true ∧ x11 x15 ((10 : ℕ) + ↑x4) = Bool.false ∧ x11 x15 ((10 : ℕ) + ↑x5) = Bool.false := by
  intro p q C a b hpq hFan hSize gate edge out h1 h2 h3
  have pre : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false =
        w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih _ i (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have inGet : ∀ (x : Fin 10 → Bool) (k : Fin 10), (List.ofFn x).getD k.val false = x k := by
    intro x k
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp
  have base : ∀ x : Fin 10 → Bool,
      ({ gates := [gate], output := 0 } : Circuit).wires (List.ofFn x) = List.ofFn x ++ [x p && x q] := by
    intro x
    have unfolded : ({ gates := [gate], output := 0 } : Circuit).wires (List.ofFn x) =
        List.ofFn x ++ [(List.ofFn x).getD p.val false && ((List.ofFn x).getD q.val false && true)] := rfl
    rw [unfolded, inGet, inGet, Bool.and_true]
  have firstVal : ∀ x : Fin 10 → Bool, out x 10 = (x p && x q) := by
    intro x
    show (C.wires (({ gates := [gate], output := 0 } : Circuit).wires (List.ofFn x))).getD 10 false = _
    rw [base]
    unfold Circuit.wires
    rw [pre _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]
  by_cases ha : a.val = 0
  · have ea : 10 + a.val = 10 := by omega
    by_cases hb : b.val = 0
    · have eb : 10 + b.val = 10 := by omega
      obtain ⟨x, hx1, hx2⟩ := h1
      rw [ea] at hx1
      rw [eb] at hx2
      rw [hx1] at hx2
      exact absurd hx2 (by decide)
    · have eb : 10 + b.val = 11 + (b.val - 1) := by omega
      rw [ea, eb] at h1 h2 h3 ⊢
      simp only [firstVal] at h1 h2 h3 ⊢
      exact firstWire p q C ⟨b.val - 1, by omega⟩ hpq hFan hSize h1 h2 h3
  · have ea : 10 + a.val = 11 + (a.val - 1) := by omega
    by_cases hb : b.val = 0
    · have eb : 10 + b.val = 10 := by omega
      rw [ea, eb] at h1 h2 h3 ⊢
      simp only [firstVal] at h1 h2 h3 ⊢
      obtain ⟨x, hx, hxa, hxb⟩ := firstWire p q C ⟨a.val - 1, by omega⟩ hpq hFan hSize
        (by obtain ⟨x, hx1, hx2⟩ := h2; exact ⟨x, hx2, hx1⟩)
        (by obtain ⟨x, hx1, hx2⟩ := h1; exact ⟨x, hx2, hx1⟩)
        (fun x hx => ⟨(h3 x hx).2, (h3 x hx).1⟩)
      exact ⟨x, hx, hxb, hxa⟩
    · have eb : 10 + b.val = 11 + (b.val - 1) := by omega
      rw [ea, eb] at h1 h2 h3 ⊢
      exact laterWires p q C ⟨a.val - 1, by omega⟩ ⟨b.val - 1, by omega⟩ hpq hFan hSize h1 h2 h3
