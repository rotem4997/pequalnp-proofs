import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2373_267
  (andFirst : ∀ (a b : Fin 10) (x2 : Circuit) (x3 x4 : Fin 18),
    a ≠ b → FanInTwo x2 → x2.size ≤ 17 →
    have x1 : Gate := ⟨GateOp.and, [a.val, b.val]⟩;
    have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 (10 + x3.val) = Bool.true ∧ x9 x10 (10 + x4.val) = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 (10 + x3.val) = Bool.false ∧ x9 x11 (10 + x4.val) = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 (10 + x3.val) = Bool.false ∧ x9 x12 (10 + x4.val) = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 (10 + x3.val) = Bool.false ∧ x9 x13 (10 + x4.val) = Bool.false)
  (orFirst : ∀ (a b : Fin 11) (x2 : Circuit) (x3 x4 : Fin 18),
    FanInTwo x2 → x2.size ≤ 17 →
    have x1 : Gate := ⟨GateOp.or, [a.val, b.val]⟩;
    have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 (10 + x3.val) = Bool.true ∧ x9 x10 (10 + x4.val) = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 (10 + x3.val) = Bool.false ∧ x9 x11 (10 + x4.val) = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 (10 + x3.val) = Bool.false ∧ x9 x12 (10 + x4.val) = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 (10 + x3.val) = Bool.false ∧ x9 x13 (10 + x4.val) = Bool.false)
  (notFirst : ∀ (a : Fin 11) (x2 : Circuit) (x3 x4 : Fin 18),
    FanInTwo x2 → x2.size ≤ 17 →
    have x1 : Gate := ⟨GateOp.not, [a.val]⟩;
    have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 (10 + x3.val) = Bool.true ∧ x9 x10 (10 + x4.val) = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 (10 + x3.val) = Bool.false ∧ x9 x11 (10 + x4.val) = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 (10 + x3.val) = Bool.false ∧ x9 x12 (10 + x4.val) = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 (10 + x3.val) = Bool.false ∧ x9 x13 (10 + x4.val) = Bool.false)
  : ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         (∃ (x10 : Fin (10 : ℕ) → Bool), x9 x10 x3 = Bool.true ∧ x9 x10 x4 = Bool.false) → (∃ (x11 : Fin (10 : ℕ) → Bool), x9 x11 x3 = Bool.false ∧ x9 x11 x4 = Bool.true) → (∀ (x12 : Fin (10 : ℕ) → Bool), x8 x12 = Bool.false → x9 x12 x3 = Bool.false ∧ x9 x12 x4 = Bool.false) → ∃ (x13 : Fin (10 : ℕ) → Bool), x8 x13 = Bool.true ∧ x9 x13 x3 = Bool.false ∧ x9 x13 x4 = Bool.false := by
  intro original C u v firstFan tailFan tailSize
  rcases original with ⟨op, inputs⟩
  let target : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))
  let value (g : Gate) (z : Fin 10 → Bool) (i : ℕ) :=
    (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn z))).getD i false
  let question (g : Gate) : Prop :=
    (∃ z, value g z u = true ∧ value g z v = false) →
    (∃ z, value g z u = false ∧ value g z v = true) →
    (∀ z, target z = false → value g z u = false ∧ value g z v = false) →
    ∃ z, target z = true ∧ value g z u = false ∧ value g z v = false
  change question ⟨op, inputs⟩
  intro leftExclusive rightExclusive sound
  let read (z : Fin 10 → Bool) (i : ℕ) := (List.ofFn z).getD i false
  have wireLength (gs : List Gate) (xs : List Bool) :
      (Circuit.wires ⟨gs, 0⟩ xs).length = xs.length + gs.length := by
    induction gs generalizing xs with
    | nil => rfl
    | cons g gs ih =>
      change (Circuit.wires ⟨gs, 0⟩ (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)])).length = _
      rw [ih]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have wireInput (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
      (Circuit.wires ⟨gs, 0⟩ xs).getD i false = xs.getD i false := by
    induction gs generalizing xs with
    | nil => rfl
    | cons g gs ih =>
      change (Circuit.wires ⟨gs, 0⟩ (xs ++ [g.op.eval (g.inputs.map fun j => xs.getD j false)])).getD i false = _
      rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]
  have inputValue (z : Fin 10 → Bool) (j : Fin 10) :
      value ⟨op, inputs⟩ z j.val = z j := by
    let xs := (Circuit.wires ⟨[⟨op, inputs⟩], 0⟩ (List.ofFn z))
    have hlen : xs.length = 11 := by
      change (Circuit.wires ⟨[⟨op, inputs⟩], 0⟩ (List.ofFn z)).length = 11
      rw [wireLength]
      simp
    change (Circuit.wires ⟨C.gates, 0⟩ xs).getD j.val false = z j
    rw [wireInput _ _ _ (by omega)]
    unfold xs
    rw [wireInput _ _ _ (by simp)]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact j.isLt), List.getElem_ofFn]
  have unitFalse (j : Fin 10) : target (fun i => decide (i = j)) = false := by
    fin_cases j <;> decide
  have low (i : ℕ) (hs : ∀ z, target z = false → value ⟨op, inputs⟩ z i = false) : 10 ≤ i := by
    by_contra! hi
    let j : Fin 10 := ⟨i, hi⟩
    let z : Fin 10 → Bool := fun k => decide (k = j)
    have h := hs z (unitFalse j)
    change value ⟨op, inputs⟩ z j.val = false at h
    rw [inputValue, show z j = true by simp [z]] at h
    contradiction
  have high (i : ℕ) (h : ∃ z, value ⟨op, inputs⟩ z i = true) : i < 28 := by
    obtain ⟨z, hz⟩ := h
    let xs := Circuit.wires ⟨[⟨op, inputs⟩], 0⟩ (List.ofFn z)
    have hlen : xs.length = 11 := by
      change (Circuit.wires ⟨[⟨op, inputs⟩], 0⟩ (List.ofFn z)).length = 11
      rw [wireLength]
      simp
    by_contra! hi
    change (Circuit.wires ⟨C.gates, 0⟩ xs).getD i false = true at hz
    rw [List.getD_eq_default _ _ (by rw [wireLength, hlen]; change 11 + C.size ≤ i; omega)] at hz
    contradiction
  have hlu := low u (fun z hz => (sound z hz).1)
  have hlv := low v (fun z hz => (sound z hz).2)
  have hhu : u < 28 := by
    obtain ⟨z, h, _⟩ := leftExclusive
    exact high u ⟨z, h⟩
  have hhv : v < 28 := by
    obtain ⟨z, _, h⟩ := rightExclusive
    exact high v ⟨z, h⟩
  let uFin : Fin 18 := ⟨u - 10, by omega⟩
  let vFin : Fin 18 := ⟨v - 10, by omega⟩
  have huFin : 10 + uFin.val = u := Nat.add_sub_of_le hlu
  have hvFin : 10 + vFin.val = v := Nat.add_sub_of_le hlv
  let conclusion := ∃ z, target z = true ∧ value ⟨op, inputs⟩ z u = false ∧
    value ⟨op, inputs⟩ z v = false
  change conclusion
  have evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
  have evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have transfer (g : Gate)
      (same : ∀ z, g.op.eval (g.inputs.map (read z)) = op.eval (inputs.map (read z)))
      (h : question g) : conclusion := by
    have hvalue (z : Fin 10 → Bool) (i : ℕ) : value g z i = value ⟨op, inputs⟩ z i := by
      change (C.wires (List.ofFn z ++ [g.op.eval (g.inputs.map (read z))])).getD i false =
        (C.wires (List.ofFn z ++ [op.eval (inputs.map (read z))])).getD i false
      rw [same]
    have q : question ⟨op, inputs⟩ := by simpa only [question, hvalue] using h
    exact q leftExclusive rightExclusive sound
  have hG := firstFan ⟨op, inputs⟩ (by simp)
  have hOp : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hG.1
  have hInputs : inputs.length ≤ 2 := hG.2
  let clip (i : ℕ) : Fin 11 := if h : i < 10 then ⟨i, by omega⟩ else 10
  have missing (z : Fin 10 → Bool) : read z 10 = false := by simp [read]
  have clipped (z : Fin 10 → Bool) (i : ℕ) : read z (clip i).val = read z i := by
    by_cases h : i < 10
    · simp [clip, h]
    · have hread : read z i = false := List.getD_eq_default _ _ (by
        simpa using (Nat.le_of_not_gt h))
      simpa [clip, h, hread] using missing z
  have toOr (a b : Fin 11)
      (he : ∀ z, (read z a.val || read z b.val) = op.eval (inputs.map (read z))) :
      conclusion := by
    apply transfer ⟨GateOp.or, [a.val, b.val]⟩
    · intro z
      simpa only [evalOr, Gate.op, Gate.inputs, List.map_cons, List.map_nil,
        List.any_cons, List.any_nil, id_eq, Bool.or_false] using he z
    · simpa only [huFin, hvFin] using orFirst a b C uFin vFin tailFan tailSize
  have toNot (a : Fin 11) (he : ∀ z, (!read z a.val) = op.eval (inputs.map (read z))) :
      conclusion := by
    apply transfer ⟨GateOp.not, [a.val]⟩
    · intro z
      exact he z
    · simpa only [huFin, hvFin] using notFirst a C uFin vFin tailFan tailSize
  have toAnd (a b : Fin 10) (ne : a ≠ b)
      (he : ∀ z, (read z a.val && read z b.val) = op.eval (inputs.map (read z))) :
      conclusion := by
    apply transfer ⟨GateOp.and, [a.val, b.val]⟩
    · intro z
      simpa only [evalAnd, Gate.op, Gate.inputs, List.map_cons, List.map_nil,
        List.all_cons, List.all_nil, id_eq, Bool.and_true] using he z
    · simpa only [huFin, hvFin] using andFirst a b C uFin vFin ne tailFan tailSize
  rcases hOp with rfl | rfl | rfl
  · rcases inputs with _ | ⟨a, rest⟩
    · apply toNot 10
      intro z
      simp [missing, evalAnd]
    · rcases rest with _ | ⟨b, rest⟩
      · apply toOr (clip a) 10
        intro z
        simp only [evalAnd, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, clipped]
        rw [show read z (10 : Fin 11).val = false from missing z, Bool.or_false]
      · have hRest : rest = [] := by
          apply List.length_eq_zero_iff.mp
          change (a :: b :: rest : List ℕ).length ≤ 2 at hInputs
          simp only [List.length_cons] at hInputs
          omega
        subst rest
        by_cases ha : a < 10
        · by_cases hb : b < 10
          · by_cases hab : a = b
            · subst b
              apply toOr (clip a) 10
              intro z
              simp only [evalAnd, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                id_eq, Bool.and_true, clipped, Bool.and_self]
              rw [show read z (10 : Fin 11).val = false from missing z, Bool.or_false]
            · apply toAnd ⟨a, ha⟩ ⟨b, hb⟩ (fun h => hab (congrArg Fin.val h))
              intro z
              simp only [evalAnd, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                id_eq, Bool.and_true]
          · apply toOr 10 10
            intro z
            have hread : read z b = false := List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hb)
            simp only [evalAnd, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              id_eq, Bool.and_true, hread, Bool.and_false]
            rw [show read z (10 : Fin 11).val = false from missing z, Bool.or_false]
        · apply toOr 10 10
          intro z
          have hread : read z a = false := List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt ha)
          simp only [evalAnd, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
            id_eq, Bool.and_true, hread, Bool.false_and]
          rw [show read z (10 : Fin 11).val = false from missing z, Bool.or_false]
  · rcases inputs with _ | ⟨a, rest⟩
    · apply toOr 10 10
      intro z
      rw [show read z (10 : Fin 11).val = false from missing z, Bool.or_false]
      rfl
    · rcases rest with _ | ⟨b, rest⟩
      · apply toOr (clip a) 10
        intro z
        rw [clipped, show read z (10 : Fin 11).val = false from missing z, Bool.or_false]
        simp only [evalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false]
      · have hRest : rest = [] := by
          apply List.length_eq_zero_iff.mp
          change (a :: b :: rest : List ℕ).length ≤ 2 at hInputs
          simp only [List.length_cons] at hInputs
          omega
        subst rest
        apply toOr (clip a) (clip b)
        intro z
        simp only [evalOr, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, clipped]
  · rcases inputs with _ | ⟨a, rest⟩
    · apply toNot 10
      intro z
      rw [show read z (10 : Fin 11).val = false from missing z]
      rfl
    · apply toNot (clip a)
      intro z
      rw [clipped]
      rfl
