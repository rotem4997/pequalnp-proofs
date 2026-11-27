import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The output wire is a gate: an input wire is false at the pair of point 0 and line 0 or at
-- the pair of point 1 and line 1, and a wire past the last gate is false everywhere.
-- A gate is an AND or an OR, so two cases remain, by the operation of the output gate.
theorem PEqualNP.Outside.R_meta_4071_184
    (outAnd : let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x2 : Finset (Fin (13 : ℕ))) => {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x2, ¬x1 x4 x3}; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x3 : Finset (Fin (13 : ℕ))) => {x4 : Fin (13 : ℕ) | ∀ x5 ∈ x3, ¬x1 x4 x5}; have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x1 x6 x5}.card ≤ (2 : ℕ); have x5 : Finset (Fin (13 : ℕ)) → Prop := fun (x5 : Finset (Fin (13 : ℕ))) => ∀ (x6 : Fin (13 : ℕ)), (Finset.filter (x1 x6) x5).card ≤ (2 : ℕ); have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => Fin.addCases (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x6)) (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x7)) x8; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x7.size ≤ (63 : ℕ) → (∀ (x10 x11 : Fin (13 : ℕ)), x1 x10 x11 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 fun (x13 : Fin (26 : ℕ)) => Decidable.decide (x13 = Fin.castAdd (13 : ℕ) x10 ∨ x13 = Fin.natAdd (13 : ℕ) x11)) = Bool.true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt x7 (x7.output - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ 26 ≤ x7.output ∧ x7.output < 26 + x7.size) → (∃ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) ∧ x4 x11 ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x6 x11 (x2 x11)) = Bool.true) ∨ ∃ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) ∧ x5 x11 ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x6 (x3 x11) x11) = Bool.true)
    (outOr : let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x2 : Finset (Fin (13 : ℕ))) => {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x2, ¬x1 x4 x3}; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x3 : Finset (Fin (13 : ℕ))) => {x4 : Fin (13 : ℕ) | ∀ x5 ∈ x3, ¬x1 x4 x5}; have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x1 x6 x5}.card ≤ (2 : ℕ); have x5 : Finset (Fin (13 : ℕ)) → Prop := fun (x5 : Finset (Fin (13 : ℕ))) => ∀ (x6 : Fin (13 : ℕ)), (Finset.filter (x1 x6) x5).card ≤ (2 : ℕ); have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => Fin.addCases (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x6)) (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x7)) x8; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x7.size ≤ (63 : ℕ) → (∀ (x10 x11 : Fin (13 : ℕ)), x1 x10 x11 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 fun (x13 : Fin (26 : ℕ)) => Decidable.decide (x13 = Fin.castAdd (13 : ℕ) x10 ∨ x13 = Fin.natAdd (13 : ℕ) x11)) = Bool.true) → ((PEqualNP.MetaComplexity.NestedCover.gateAt x7 (x7.output - 26)).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 26 ≤ x7.output ∧ x7.output < 26 + x7.size) → (∃ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) ∧ x4 x11 ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x6 x11 (x2 x11)) = Bool.true) ∨ ∃ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) ∧ x5 x11 ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x6 (x3 x11) x11) = Bool.true) :
    let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x2 : Finset (Fin (13 : ℕ))) => {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x2, ¬x1 x4 x3}; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x3 : Finset (Fin (13 : ℕ))) => {x4 : Fin (13 : ℕ) | ∀ x5 ∈ x3, ¬x1 x4 x5}; have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x1 x6 x5}.card ≤ (2 : ℕ); have x5 : Finset (Fin (13 : ℕ)) → Prop := fun (x5 : Finset (Fin (13 : ℕ))) => ∀ (x6 : Fin (13 : ℕ)), (Finset.filter (x1 x6) x5).card ≤ (2 : ℕ); have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => Fin.addCases (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x6)) (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x7)) x8; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x7.size ≤ (63 : ℕ) → (∀ (x10 x11 : Fin (13 : ℕ)), x1 x10 x11 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 fun (x13 : Fin (26 : ℕ)) => Decidable.decide (x13 = Fin.castAdd (13 : ℕ) x10 ∨ x13 = Fin.natAdd (13 : ℕ) x11)) = Bool.true) → (∃ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) ∧ x4 x11 ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x6 x11 (x2 x11)) = Bool.true) ∨ ∃ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) ∧ x5 x11 ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x6 (x3 x11) x11) = Bool.true := by
  dsimp only
  intro C hmono hsize P1
  have hpre : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      have h1 := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i
        (by rw [List.length_append]; omega)
      have h2 : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).getD i false
          = w.getD i false := List.getD_append _ _ _ _ hi
      exact h1.trans h2
  have hlen : ∀ (gs : List Gate) (w : List Bool),
      (gs.foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; rfl
    | cons g gs ih =>
      intro w
      have h1 := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      have h2 : (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length = w.length + 1 := by
        rw [List.length_append]
        rfl
      have h3 : (g :: gs).length = gs.length + 1 := rfl
      rw [h2] at h1
      rw [h3]
      exact h1.trans (by omega)
  have hinput : ∀ i : ℕ, i < 26 →
      (((List.ofFn fun (k : Fin 26) => decide (k = Fin.castAdd 13 (0 : Fin 13) ∨ k = Fin.natAdd 13 (0 : Fin 13)))).getD i false && ((List.ofFn fun (k : Fin 26) => decide (k = Fin.castAdd 13 (1 : Fin 13) ∨ k = Fin.natAdd 13 (1 : Fin 13)))).getD i false) = false := by decide
  have e0 : (C.gates.foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn fun (k : Fin 26) => decide (k = Fin.castAdd 13 (0 : Fin 13) ∨ k = Fin.natAdd 13 (0 : Fin 13)))).getD C.output false = true := P1 0 0 (Or.inl rfl)
  have e1 : (C.gates.foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn fun (k : Fin 26) => decide (k = Fin.castAdd 13 (1 : Fin 13) ∨ k = Fin.natAdd 13 (1 : Fin 13)))).getD C.output false = true := P1 1 1 (Or.inl rfl)
  have hlo : 26 ≤ C.output := by
    by_contra hlt
    have hc26 : C.output < 26 := by omega
    rw [hpre _ _ C.output (by simp; omega)] at e0 e1
    have h := hinput C.output hc26
    rw [e0, e1] at h
    exact absurd h (by decide)
  have hhi : C.output < 26 + C.size := by
    by_contra hge
    have hl := hlen C.gates (List.ofFn fun (k : Fin 26) => decide (k = Fin.castAdd 13 (0 : Fin 13) ∨ k = Fin.natAdd 13 (0 : Fin 13)))
    have hd : (C.gates.foldl (fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn fun (k : Fin 26) => decide (k = Fin.castAdd 13 (0 : Fin 13) ∨ k = Fin.natAdd 13 (0 : Fin 13)))).getD C.output false = false :=
      List.getD_eq_default _ _ (by
        rw [hl]
        have : C.size = C.gates.length := rfl
        simp
        omega)
    rw [hd] at e0
    exact absurd e0 (by decide)
  have hj : C.output - 26 < C.gates.length := by
    have : C.size = C.gates.length := rfl
    omega
  have hmem : NestedCover.gateAt C (C.output - 26) ∈ C.gates := by
    show C.gates.getD (C.output - 26) _ ∈ C.gates
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  rcases (hmono _ hmem).1 with hA | hA
  · exact outAnd C hmono hsize P1 ⟨hA, hlo, hhi⟩
  · exact outOr C hmono hsize P1 ⟨hA, hlo, hhi⟩
