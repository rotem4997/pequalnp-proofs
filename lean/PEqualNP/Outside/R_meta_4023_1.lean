import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_4023_1
    (h1 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 64 ∧ PEqualNP.TopForm.IsAO2 26 C ∧
        (∀ g ∈ C.gates, g.inputs.Nodup) ∧
        (∀ p l : Fin 13 → Bool,
          C.eval (List.ofFn (Fin.addCases p l)) = true ↔
          ∃ j : Fin 13, l j = true ∧
            (p j || p (j + 1) || p (j + 3) || p (j + 9)) = true) ∧
        ∃ k a b : Nat, C.output = 26 + k ∧
          C.gates[k]? = some ⟨.and,[a,b]⟩ ∧
          ∀ s : Bool,
            let ws := C.wires (List.ofFn fun i : Fin 26 =>
              decide (i.val = if s = true then 13 else 0))
            ws.getD a false = false ∧ ws.getD b false = false)
    (h2 : ∀ (x1 x2 x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x2 < x1 →     x3 < x1 →       x2 ≠ x3 →         PEqualNP.TopForm.IsAO2 x1 x4 →           have x9 : List (Bool × Bool) := PEqualNP.ReadK.linearParts x4 (fun (x9 : ℕ) => Decidable.decide (x9 = x2)) (List.map (fun (x9 : ℕ) => x9 == x2 || x9 == x3) (List.range x1));           have x10 : ℕ → Bool := fun (x10 : ℕ) => (x9.getD x10 (Bool.false, Bool.false)).2;           have x11 : List Bool := x4.wires (List.ofFn fun (x11 : Fin x1) => Decidable.decide (↑x11 = x3));           ∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate) (x14 x15 : ℕ), x4.gates[x12]? = Option.some x13 → x13.inputs = [x14, x15] → (x13.op = PEqualNP.CircuitLowerBounds.GateOp.and → x10 (x1 + x12) = (x11.getD x14 Bool.false && x10 x15 || x10 x14 && x11.getD x15 Bool.false)) ∧ (x13.op = PEqualNP.CircuitLowerBounds.GateOp.or → x10 (x1 + x12) = (x10 x14 || x10 x15))) : have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x2 : Fin (13 : ℕ) → Bool) (x3 : Fin (13 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (13 : ℕ))) || x2 (x3 + (3 : Fin (13 : ℕ))) || x2 (x3 + (9 : Fin (13 : ℕ)))); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x3.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧ (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧ (∀ (x4 x5 : Fin (13 : ℕ)), x1 x4 x5 → x3.eval (List.ofFn fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x4)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) x7) = Bool.true) ∧ (∀ (x4 : Fin (13 : ℕ) → Bool), (∀ (x5 : Fin (13 : ℕ)), x4 x5 = Bool.false → ∃ (x7 : Fin (13 : ℕ)), x1 x5 x7 ∧ x2 x4 x7 = Bool.true) → x3.eval (List.ofFn fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x4 (x2 x4) x6) = Bool.false) ∧ ∀ (x4 : Bool), PEqualNP.ReadK.lineSingle x3 (26 : ℕ) (fun (x5 : ℕ) => Decidable.decide (x5 = if x4 = Bool.true then (0 : ℕ) else (13 : ℕ))) (0 : ℕ) (13 : ℕ) = Bool.false := by
  classical
  dsimp only
  obtain ⟨C, hs, hAO, hnd, heval, k, a, b, hout, hgate, hcold⟩ := h1
  refine ⟨C, hs, hAO, hnd, ?_, ?_, ?_⟩
  · intro i j hij
    apply (heval (fun t => decide (t = i)) (fun t => decide (t = j))).2
    refine ⟨j, by simp, ?_⟩
    rcases hij with h | h | h | h <;> subst i <;> simp
  · intro p _
    let l : Fin 13 → Bool := fun j => !(p j || p (j + 1) || p (j + 3) || p (j + 9))
    change C.eval (List.ofFn (Fin.addCases p l)) = false
    cases hv : C.eval (List.ofFn (Fin.addCases p l)) with
    | false => rfl
    | true =>
      obtain ⟨j, hj, hp⟩ := (heval p l).1 hv
      change (!(p j || p (j + 1) || p (j + 3) || p (j + 9))) = true at hj
      rw [hp] at hj
      contradiction
  · intro s
    cases s
    · have hg := (h2 26 13 0 C (by decide) (by decide) (by decide) hAO k ⟨.and, [a, b]⟩ a b hgate rfl).1 rfl
      obtain ⟨ha, hb⟩ := hcold false
      change (C.wires (List.ofFn fun i : Fin 26 => decide (i.val = 0))).getD a false = false at ha
      change (C.wires (List.ofFn fun i : Fin 26 => decide (i.val = 0))).getD b false = false at hb
      dsimp only at hg
      rw [ha, hb] at hg
      have hbits : (List.map (fun (i : ℕ) => i == 13 || i == 0) (List.range 26)) = (List.range 26).map (fun i => i == 0 || i == 13) := by decide
      rw [hbits] at hg
      change ((PEqualNP.ReadK.linearParts C (fun i => decide (i = 13)) ((List.range 26).map fun i => i == 0 || i == 13)).getD C.output (false, false)).2 = false
      rw [hout, hg]
      simp
    · have hg := (h2 26 0 13 C (by decide) (by decide) (by decide) hAO k ⟨.and, [a, b]⟩ a b hgate rfl).1 rfl
      obtain ⟨ha, hb⟩ := hcold true
      change (C.wires (List.ofFn fun i : Fin 26 => decide (i.val = 13))).getD a false = false at ha
      change (C.wires (List.ofFn fun i : Fin 26 => decide (i.val = 13))).getD b false = false at hb
      dsimp only at hg
      rw [ha, hb] at hg
      change ((PEqualNP.ReadK.linearParts C (fun i => decide (i = 0)) ((List.range 26).map fun i => i == 0 || i == 13)).getD C.output (false, false)).2 = false
      rw [hout, hg]
      simp
