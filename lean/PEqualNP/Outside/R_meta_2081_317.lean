import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

-- A final conjunction has zero mark if both ordinary operands are false.
-- The two factors need this property on the point singleton and the line singleton.
-- On every input their intersection must be exactly the incidence function.

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_2081_317
    (factor :
      ∃ C : Circuit, C.size ≤ 64 ∧ PEqualNP.TopForm.IsAO2 26 C ∧
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
    (traces : ∀ C : Circuit, PEqualNP.TopForm.IsAO2 26 C →
      ∀ (r : Nat) (ws : List Bool), ∃ d : Nat → Bool,
        (∀ n < 26, d n = decide (n = r)) ∧
        ∀ (k : Nat) (g : Gate) (a b : Nat), C.gates[k]? = some g →
          g.inputs = [a,b] →
          (g.op = .and → d (26 + k) = ((ws.getD a false && d b) || (d a && ws.getD b false))) ∧
          (g.op = .or → d (26 + k) = (d a || d b))) :
    have x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : (Fin (13 : ℕ) → Bool) → Fin (13 : ℕ) → Bool := fun (x2 : Fin (13 : ℕ) → Bool) (x3 : Fin (13 : ℕ)) => !(x2 x3 || x2 (x3 + (1 : Fin (13 : ℕ))) || x2 (x3 + (3 : Fin (13 : ℕ))) || x2 (x3 + (9 : Fin (13 : ℕ)))); ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x3.size ≤ (64 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧       (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧         (∀ (x4 x5 : Fin (13 : ℕ)), x1 x4 x5 → x3.eval (List.ofFn fun (x7 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x4)) (fun (x8 : Fin (13 : ℕ)) => Decidable.decide (x8 = x5)) x7) = Bool.true) ∧           (∀ (x4 : Fin (13 : ℕ) → Bool), (∀ (x5 : Fin (13 : ℕ)), x4 x5 = Bool.false → ∃ (x7 : Fin (13 : ℕ)), x1 x5 x7 ∧ x2 x4 x7 = Bool.true) → x3.eval (List.ofFn fun (x6 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases x4 (x2 x4) x6) = Bool.false) ∧             ∀ (x4 : Bool),               ∃ (x5 : ℕ → Bool),                 (∀ x6 < (26 : ℕ), x5 x6 = Decidable.decide (x6 = if x4 = Bool.true then (0 : ℕ) else (13 : ℕ))) ∧                   (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate) (x8 x9 : ℕ),                       x3.gates[x6]? = Option.some x7 →                         x7.inputs = [x8, x9] →                           have x12 : List Bool := x3.wires (List.ofFn fun (x12 : Fin (26 : ℕ)) => Decidable.decide (↑x12 = if x4 = Bool.true then (13 : ℕ) else (0 : ℕ)));                           (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and → x5 ((26 : ℕ) + x6) = (x12.getD x8 Bool.false && x5 x9 || x5 x8 && x12.getD x9 Bool.false)) ∧ (x7.op = PEqualNP.CircuitLowerBounds.GateOp.or → x5 ((26 : ℕ) + x6) = (x5 x8 || x5 x9))) ∧                     x5 x3.output = Bool.false := by
  classical
  dsimp only
  obtain ⟨C, hs, hAO, hnd, heval, k, a, b, hout, hgate, hcold⟩ := factor
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
    let ws := C.wires (List.ofFn fun i : Fin 26 =>
      decide (i.val = if s = true then 13 else 0))
    obtain ⟨d, hraw, hrec⟩ := traces C hAO (if s = true then 0 else 13) ws
    refine ⟨d, hraw, hrec, ?_⟩
    obtain ⟨ha, hb⟩ := hcold s
    change ws.getD a false = false at ha
    change ws.getD b false = false at hb
    rw [hout, (hrec k ⟨.and,[a,b]⟩ a b hgate rfl).1 rfl, ha, hb]
    simp
