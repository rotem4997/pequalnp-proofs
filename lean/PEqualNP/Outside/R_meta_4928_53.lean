import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.ReadTwo PEqualNP.MetaComplexity.SingleLevel

theorem PEqualNP.Outside.R_meta_4928_53
    (clean_case : let inc := fun u t : Fin 7 => u=t ∨ u=t+1 ∨ u=t+3
    let valid := fun C : Circuit =>
      C.size ≤ 27 ∧
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        (g.op = .and ∨ g.op = .or) ∧
        ∃ a b : ℕ, g.inputs=[a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j) ∧
      ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, inc u t ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true
    ∀ C : Circuit, valid C → (∀ j, isAnd C j → ∀ u v : Fin 14,
          let x := pairInput u v
          gateVal 14 C j x = true → C.eval (List.ofFn x) = true) →
      ∀ p t : Fin 7, inc p t → C.lineDeg 14 {p.val} ≤ 1 ∨ C.lineDeg 14 {7+t.val} ≤ 1)
    (dirty_case : let inc := fun u t : Fin 7 => u=t ∨ u=t+1 ∨ u=t+3
    let valid := fun C : Circuit =>
      C.size ≤ 27 ∧
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        (g.op = .and ∨ g.op = .or) ∧
        ∃ a b : ℕ, g.inputs=[a,b] ∧ a ≠ b ∧ a < 14+j ∧ b < 14+j) ∧
      ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ u t : Fin 7, inc u t ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true
    let tree := fun C : Circuit =>
      ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup
    ∀ p t : Fin 7, inc p t →
      let marked := fun C : Circuit => valid C ∧
        2 ≤ C.lineDeg 14 {p.val} ∧ 2 ≤ C.lineDeg 14 {7+t.val}
      ∀ C : Circuit, marked C → ¬(∀ j, isAnd C j → ∀ u v : Fin 14,
          let x := pairInput u v
          gateVal 14 C j x = true → C.eval (List.ofFn x) = true) →
        2 ≤ (andDepths C 14).getD C.output 0 → ¬tree C →
        ∃ D : Circuit, marked D ∧ tree D) :
    (have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (7 : ℕ)), x2 x4 → x1 x5 x6 → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {↑x5} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} → (2 : ℕ) ≤ (PEqualNP.MetaComplexity.SingleLevel.andDepths x4 (14 : ℕ)).getD x4.output (0 : ℕ) → ¬x3 x4 → ∃ (x13 : PEqualNP.CircuitLowerBounds.Circuit), x2 x13 ∧ x3 x13 ∧ (2 : ℕ) ≤ x13.lineDeg (14 : ℕ) {↑x5} ∧ (2 : ℕ) ≤ x13.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6}) := by

  intro inc valid tree C p t hC hi hp ht hd hs
  by_cases hc : (∀ j, isAnd C j → ∀ u v : Fin 14,
          let x := pairInput u v
          gateVal 14 C j x = true → C.eval (List.ofFn x) = true)
  · have low := clean_case C hC hc p t hi
    omega
  · obtain ⟨D,⟨hD,hp',ht'⟩,htr⟩ := dirty_case p t hi C ⟨hC,hp,ht⟩ hc hd hs
    exact ⟨D,hD,htr,hp',ht'⟩
