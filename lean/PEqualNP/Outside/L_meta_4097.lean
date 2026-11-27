import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4097

open PEqualNP.CircuitLowerBounds

private def appendGate (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]

private lemma fold_extends (gs : List Gate) (ws : List Bool) :
    ∃ tail, gs.foldl appendGate ws = ws ++ tail := by
  induction gs generalizing ws with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨tail, htail⟩ := ih (appendGate ws g)
    refine ⟨g.op.eval (g.inputs.map fun i => ws.getD i false) :: tail, ?_⟩
    simpa only [List.foldl_cons, appendGate, List.append_assoc, List.singleton_append] using htail

private lemma and_value (gs : List Gate) (ws : List Bool) (i a b : ℕ)
    (ha : a < ws.length + i) (hb : b < ws.length + i)
    (hgate : gs[i]? = some ⟨GateOp.and, [a,b]⟩) :
    let all := gs.foldl appendGate ws
    all.getD (ws.length + i) false = (all.getD a false && all.getD b false) := by
  induction gs generalizing ws i with
  | nil => simp at hgate
  | cons g gs ih =>
    cases i with
    | zero =>
      have hhead : g = ⟨GateOp.and, [a,b]⟩ := by simpa using hgate
      subst g
      let z := ws.getD a false && ws.getD b false
      have eval : appendGate ws ⟨GateOp.and, [a,b]⟩ = ws ++ [z] := by
        simp [appendGate, GateOp.eval, z]
      obtain ⟨tail, htail⟩ := fold_extends gs (appendGate ws ⟨GateOp.and, [a,b]⟩)
      simp only [List.foldl_cons, Nat.add_zero]
      rw [htail, eval, List.append_assoc]
      have ha' : a < ws.length := by omega
      have hb' : b < ws.length := by omega
      rw [List.getD_append _ _ _ _ ha', List.getD_append _ _ _ _ hb',
        List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self]
      rfl
    | succ i =>
      have length : (appendGate ws g).length + i = ws.length + (i + 1) := by
        simp [appendGate]
        omega
      simpa only [List.foldl_cons, length] using
        ih (appendGate ws g) i (by omega) (by omega) hgate

end PEqualNP.Outside.L_meta_4097

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.L_meta_4097 : have x1 : PEqualNP.CircuitLowerBounds.Circuit → (Fin (26 : ℕ) → Bool) → ℕ → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ) → Bool) (x3 : ℕ) => (x1.wires (List.ofFn x2)).getD x3 Bool.false; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (26 : ℕ) → Bool) (x4 x5 x6 : ℕ), PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 → x2.gates[x4]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } → x1 x2 x3 ((26 : ℕ) + x4) = (x1 x2 x3 x5 && x1 x2 x3 x6) := by
  intro signal C x i a b hAO hgate
  have hi := List.getElem?_eq_some_iff.mp hgate
  obtain ⟨hlt, _⟩ := hi
  have gate : gateAt C i = ⟨GateOp.and, [a,b]⟩ := by
    simp [gateAt, List.getD_eq_getElem?_getD, hgate]
  have reads := hAO.2.1 i hlt
  rw [gate] at reads
  have ha := reads a (by simp)
  have hb := reads b (by simp)
  have value := PEqualNP.Outside.L_meta_4097.and_value C.gates (List.ofFn x) i a b
    (by simpa using ha) (by simpa using hb) hgate
  dsimp only [List.length_ofFn] at value
  exact value
