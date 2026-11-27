import Mathlib
import PEqualNP.Defs

-- Cut of L-meta-6078 by the place of the output gate. The output is the AND gate x4 and the
-- circuit has at most 65 gates, so x4 is at most 64. When x4 is at most 63, the gates after x4
-- are dropped: the first x4 + 1 gates keep every wire below the output (the AND gate reads
-- only earlier wires), so the shorter circuit has at most 64 gates and the same two inputs.
-- The case x4 = 64 is left, split by which of the two AND inputs is the earlier wire
-- (they differ, since the inputs of every gate are distinct).
theorem PEqualNP.Outside.R_meta_6078_1
    (h1 : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : ℕ), x5 < x6 →   (x3.size ≤ (65 : ℕ) ∧       PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧         (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧           x3.output = (90 : ℕ) ∧             x3.gates[(64 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧               (∀ (x7 x8 : Fin (13 : ℕ)),                   x1 x7 x8 →                     have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8);                     PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x5 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x6 = Bool.true) ∧                 ∀ (x7 : Fin (26 : ℕ) → Bool), Maximal (fun (x8 : Fin (26 : ℕ) → Bool) => ¬x2 x8) x7 → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x7 (if x7 (13 : Fin (26 : ℕ)) = Bool.true then x5 else x6) = Bool.false) →     ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : ℕ) (x10 : ℕ) (x11 : ℕ), x8.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x8 ∧ (∀ x12 ∈ x8.gates, x12.inputs.Nodup) ∧ x8.output = (26 : ℕ) + x9 ∧ x8.gates[x9]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x10, x11] : PEqualNP.CircuitLowerBounds.Gate } ∧ ∀ (x12 : Fin (26 : ℕ) → Bool), PEqualNP.BlindGate.wireValue x8 (26 : ℕ) x12 x10 = PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x12 x5 ∧ PEqualNP.BlindGate.wireValue x8 (26 : ℕ) x12 x11 = PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x12 x6)
    (h2 : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : ℕ), x6 < x5 →   (x3.size ≤ (65 : ℕ) ∧       PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧         (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧           x3.output = (90 : ℕ) ∧             x3.gates[(64 : ℕ)]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧               (∀ (x7 x8 : Fin (13 : ℕ)),                   x1 x7 x8 →                     have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8);                     PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x5 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x6 = Bool.true) ∧                 ∀ (x7 : Fin (26 : ℕ) → Bool), Maximal (fun (x8 : Fin (26 : ℕ) → Bool) => ¬x2 x8) x7 → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x7 (if x7 (13 : Fin (26 : ℕ)) = Bool.true then x5 else x6) = Bool.false) →     ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : ℕ) (x10 : ℕ) (x11 : ℕ), x8.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x8 ∧ (∀ x12 ∈ x8.gates, x12.inputs.Nodup) ∧ x8.output = (26 : ℕ) + x9 ∧ x8.gates[x9]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x10, x11] : PEqualNP.CircuitLowerBounds.Gate } ∧ ∀ (x12 : Fin (26 : ℕ) → Bool), PEqualNP.BlindGate.wireValue x8 (26 : ℕ) x12 x10 = PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x12 x5 ∧ PEqualNP.BlindGate.wireValue x8 (26 : ℕ) x12 x11 = PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x12 x6) :
    have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 x6 : ℕ),   (x3.size ≤ (65 : ℕ) ∧       PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧         (∀ x7 ∈ x3.gates, x7.inputs.Nodup) ∧           x3.output = (26 : ℕ) + x4 ∧             x3.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∧               (∀ (x7 x8 : Fin (13 : ℕ)),                   x1 x7 x8 →                     have x10 : Fin (26 : ℕ) → Bool := fun (x10 : Fin (26 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (13 : ℕ) x7 ∨ x10 = Fin.natAdd (13 : ℕ) x8);                     PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x5 = Bool.true ∧ PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x10 x6 = Bool.true) ∧                 ∀ (x7 : Fin (26 : ℕ) → Bool), Maximal (fun (x8 : Fin (26 : ℕ) → Bool) => ¬x2 x8) x7 → PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x7 (if x7 (13 : Fin (26 : ℕ)) = Bool.true then x5 else x6) = Bool.false) →     ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit) (x9 : ℕ) (x10 : ℕ) (x11 : ℕ), x8.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x8 ∧ (∀ x12 ∈ x8.gates, x12.inputs.Nodup) ∧ x8.output = (26 : ℕ) + x9 ∧ x8.gates[x9]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x10, x11] : PEqualNP.CircuitLowerBounds.Gate } ∧ ∀ (x12 : Fin (26 : ℕ) → Bool), PEqualNP.BlindGate.wireValue x8 (26 : ℕ) x12 x10 = PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x12 x5 ∧ PEqualNP.BlindGate.wireValue x8 (26 : ℕ) x12 x11 = PEqualNP.BlindGate.wireValue x3 (26 : ℕ) x12 x6 := by
  intro p1 p2 x3 x4 x5 x6 h
  have hc := h
  obtain ⟨hsz, hao, hnd, hout, hg, hedge, hmax⟩ := hc
  have hlen : x3.gates.length ≤ 65 := hsz
  have hlt : x4 < x3.gates.length := by
    by_contra hcon
    rw [List.getElem?_eq_none (by omega)] at hg
    cases hg
  by_cases hx : x4 = 64
  · have hne : x5 ≠ x6 := by
      have hm := hnd _ (List.mem_of_getElem? hg)
      intro e
      subst e
      simp at hm
    subst hx
    rcases Nat.lt_or_gt_of_ne hne with hl | hl
    · exact h1 x3 x5 x6 hl h
    · exact h2 x3 x5 x6 hl h
  have hiso : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 26 C ↔
      ((∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        (∀ j < C.gates.length, ∀ i ∈ (C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs,
          i < 26 + j) ∧
        ∀ g ∈ C.gates, g.inputs.length = 2) := fun _ => Iff.rfl
  have hwv : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (y : Fin 26 → Bool) (w : ℕ),
      PEqualNP.BlindGate.wireValue C 26 y w =
        (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (List.ofFn y)).getD w false := fun _ _ _ => rfl
  rw [hiso] at hao
  obtain ⟨ha1, ha2, ha3⟩ := hao
  have htk : ∀ j, j < x4 + 1 → (x3.gates.take (x4 + 1))[j]? = x3.gates[j]? := fun j hj =>
    List.getElem?_take_of_lt hj
  have hlt5 : x5 < 26 + x4 ∧ x6 < 26 + x4 := by
    have hr := ha2 x4 hlt
    rw [List.getD_eq_getElem?_getD, hg] at hr
    exact ⟨hr x5 (by simp), hr x6 (by simp)⟩
  have pre : ∀ (L : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool), ∃ t : List Bool,
      L.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w = w ++ t := by
    intro L
    induction L with
    | nil => intro w; exact ⟨[], by simp⟩
    | cons g L ih =>
      intro w
      obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      exact ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, by rw [List.foldl_cons, ht]; simp⟩
  have len : ∀ (L : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool),
      (L.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length
        = w.length + L.length := by
    intro L
    induction L with
    | nil => intro w; simp
    | cons g L ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp
      omega
  have hwire : ∀ (y : Fin 26 → Bool) (w : ℕ), w < 26 + x4 →
      PEqualNP.BlindGate.wireValue ⟨x3.gates.take (x4 + 1), 26 + x4⟩ 26 y w =
        PEqualNP.BlindGate.wireValue x3 26 y w := by
    intro y w hw
    have e : x3.gates = x3.gates.take (x4 + 1) ++ x3.gates.drop (x4 + 1) :=
      (List.take_append_drop _ _).symm
    rw [hwv, hwv]
    conv_rhs => rw [e]
    rw [List.foldl_append]
    obtain ⟨t, ht⟩ := pre (x3.gates.drop (x4 + 1))
      ((x3.gates.take (x4 + 1)).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn y))
    rw [ht, List.getD_append _ _ _ _ (by rw [len]; simp; omega)]
  refine ⟨⟨x3.gates.take (x4 + 1), 26 + x4⟩, x4, x5, x6, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · show (x3.gates.take (x4 + 1)).length ≤ 64
    simp
    omega
  · rw [hiso]
    refine ⟨fun g hg' => ha1 g (List.mem_of_mem_take hg'), fun j hj i hi => ?_,
      fun g hg' => ha3 g (List.mem_of_mem_take hg')⟩
    have hj' : j < x4 + 1 := by simp at hj; omega
    rw [List.getD_eq_getElem?_getD, htk j hj', ← List.getD_eq_getElem?_getD] at hi
    exact ha2 j (by omega) i hi
  · intro g hg'
    exact hnd g (List.mem_of_mem_take hg')
  · show (x3.gates.take (x4 + 1))[x4]? = _
    rw [htk x4 (by omega)]
    exact hg
  · intro y
    exact ⟨hwire y x5 hlt5.1, hwire y x6 hlt5.2⟩
