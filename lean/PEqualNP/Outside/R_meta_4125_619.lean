import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

-- Exploit flag-transitivity of the Fano plane PG(2, 2) (order 168 collineation group):
-- any incident pair (p, l) maps to (0, 0) via a cyclic shift composed with one of two explicit
-- line-0-fixing collineations. This reduces the fixed-(0, 7) double-reread target to finding a
-- 27-gate Fano circuit with a double reread at ANY incident pair, plus input-relabeling transport.
theorem PEqualNP.Outside.R_meta_4125_619
    (hAnyEdge : ∃ (C : Circuit) (p l : Fin 7),
      (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
      C.size ≤ 27 ∧
      (∀ (i : ℕ) (g : Gate), C.gates[i]? = some g →
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + i ∧ b < 14 + i) ∧
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) =
        decide (∃ p' l' : Fin 7, (p' = l' ∨ p' = l' + 1 ∨ p' = l' + 3) ∧
          x (Fin.castAdd 7 p') = true ∧ x (Fin.natAdd 7 l') = true)) ∧
      (∀ b : Bool,
        ((linearParts C
          (fun w : ℕ => decide (w = if b = true then 7 + (l : ℕ) else (p : ℕ)))
          (List.ofFn fun j : Fin 14 => decide (j = Fin.castAdd 7 p ∨ j = Fin.natAdd 7 l))).getD
          C.output (false, false)).2 = false))
    (hRelabel :
      let valid (C : Circuit) (p l : Fin 7) : Prop :=
        C.size ≤ 27 ∧
        (∀ (i : ℕ) (g : Gate), C.gates[i]? = some g →
          (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
          ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + i ∧ b < 14 + i) ∧
        (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) =
          decide (∃ p' l' : Fin 7, (p' = l' ∨ p' = l' + 1 ∨ p' = l' + 3) ∧
            x (Fin.castAdd 7 p') = true ∧ x (Fin.natAdd 7 l') = true)) ∧
        (∀ b : Bool,
          ((linearParts C
            (fun w : ℕ => decide (w = if b = true then 7 + (l : ℕ) else (p : ℕ)))
            (List.ofFn fun j : Fin 14 => decide (j = Fin.castAdd 7 p ∨ j = Fin.natAdd 7 l))).getD
            C.output (false, false)).2 = false)
      ∀ (πP πL : Fin 7 → Fin 7),
        Function.Bijective πP → Function.Bijective πL →
        (∀ p l : Fin 7,
          (πP p = πL l ∨ πP p = πL l + 1 ∨ πP p = πL l + 3) ↔
          (p = l ∨ p = l + 1 ∨ p = l + 3)) →
        ∀ (C : Circuit) (p l : Fin 7), valid C p l → ∃ D : Circuit, valid D (πP p) (πL l)) :
    have x1 : (Fin (14 : ℕ) → Bool) → Prop := fun (x1 : Fin (14 : ℕ) → Bool) => ∃ (x2 : Fin (7 : ℕ)) (x3 : Fin (7 : ℕ)), (x2 = x3 ∨ x2 = x3 + (1 : Fin (7 : ℕ)) ∨ x2 = x3 + (3 : Fin (7 : ℕ))) ∧ x1 (Fin.castAdd (7 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (7 : ℕ) x3) = Bool.true; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ (∀ (x3 x4 : Fin (7 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ)) → x2.eval (List.ofFn fun (x6 : Fin (14 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (7 : ℕ) x3 ∨ x6 = Fin.natAdd (7 : ℕ) x4)) = Bool.true) ∧ (∀ (x3 : Fin (14 : ℕ) → Bool), ¬x1 x3 → (∀ (x5 : Fin (14 : ℕ) → Bool), (∀ (x6 : Fin (14 : ℕ)), x3 x6 = Bool.true → x5 x6 = Bool.true) → x3 ≠ x5 → x1 x5) → x2.eval (List.ofFn x3) = Bool.false) ∧ ∀ (x3 : Bool), ((PEqualNP.ReadK.linearParts x2 (fun (x4 : ℕ) => Decidable.decide (x4 = if x3 = Bool.true then (7 : ℕ) else (0 : ℕ))) (List.ofFn fun (x4 : Fin (14 : ℕ)) => Decidable.decide (↑x4 = (0 : ℕ) ∨ ↑x4 = (7 : ℕ)))).getD x2.output (Bool.false, Bool.false)).2 = Bool.false := by
  classical
  rcases hAnyEdge with ⟨C, p, l, hInc, hSz, hGates, hEval, hDR⟩
  have hFlag : ∃ (πP πL : Fin 7 → Fin 7),
      Function.Bijective πP ∧ Function.Bijective πL ∧
      (∀ p' l' : Fin 7,
        (πP p' = πL l' ∨ πP p' = πL l' + 1 ∨ πP p' = πL l' + 3) ↔
        (p' = l' ∨ p' = l' + 1 ∨ p' = l' + 3)) ∧
      πP p = 0 ∧ πL l = 0 := by
    have hShift : ∀ (s : Fin 7),
        Function.Bijective (fun t : Fin 7 => t - s) ∧
        ∀ p' l' : Fin 7,
          (p' - s = l' - s ∨ p' - s = l' - s + 1 ∨ p' - s = l' - s + 3) ↔
          (p' = l' ∨ p' = l' + 1 ∨ p' = l' + 3) := by
      intro s
      refine ⟨⟨fun a b h => sub_left_inj.mp h, fun y => ⟨y + s, add_sub_cancel_right y s⟩⟩, ?_⟩
      intro p' l'
      have h1 : p' - s = l' - s ↔ p' = l' := sub_left_inj
      have h2 : p' - s = l' - s + 1 ↔ p' = l' + 1 := by
        rw [sub_add_eq_add_sub]; exact sub_left_inj
      have h3 : p' - s = l' - s + 3 ↔ p' = l' + 3 := by
        rw [sub_add_eq_add_sub]; exact sub_left_inj
      rw [h1, h2, h3]
    let p1 : Fin 7 → Fin 7 := fun t => ([1, 0, 2, 3, 6, 5, 4] : List (Fin 7)).getD t.val 0
    let l1 : Fin 7 → Fin 7 := fun t => ([0, 6, 2, 3, 5, 4, 1] : List (Fin 7)).getD t.val 0
    let p3 : Fin 7 → Fin 7 := fun t => ([1, 3, 2, 0, 5, 6, 4] : List (Fin 7)).getD t.val 0
    let l3 : Fin 7 → Fin 7 := fun t => ([0, 2, 6, 4, 5, 3, 1] : List (Fin 7)).getD t.val 0
    have hp1_bij : Function.Bijective p1 := ⟨by decide, by decide⟩
    have hl1_bij : Function.Bijective l1 := ⟨by decide, by decide⟩
    have h1_inc : ∀ a b : Fin 7,
        (p1 a = l1 b ∨ p1 a = l1 b + 1 ∨ p1 a = l1 b + 3) ↔ (a = b ∨ a = b + 1 ∨ a = b + 3) := by
      decide
    have hp3_bij : Function.Bijective p3 := ⟨by decide, by decide⟩
    have hl3_bij : Function.Bijective l3 := ⟨by decide, by decide⟩
    have h3_inc : ∀ a b : Fin 7,
        (p3 a = l3 b ∨ p3 a = l3 b + 1 ∨ p3 a = l3 b + 3) ↔ (a = b ∨ a = b + 1 ∨ a = b + 3) := by
      decide
    rcases hInc with rfl | rfl | rfl
    · refine ⟨fun t => t - p, fun t => t - p, (hShift p).1, (hShift p).1, (hShift p).2,
        sub_self p, sub_self p⟩
    · refine ⟨fun t => p1 (t - l), fun t => l1 (t - l),
        hp1_bij.comp (hShift l).1, hl1_bij.comp (hShift l).1,
        fun p' l' => (h1_inc (p' - l) (l' - l)).trans ((hShift l).2 p' l'), ?_, ?_⟩
      · dsimp only; rw [add_sub_cancel_left]; decide
      · dsimp only; rw [sub_self]; decide
    · refine ⟨fun t => p3 (t - l), fun t => l3 (t - l),
        hp3_bij.comp (hShift l).1, hl3_bij.comp (hShift l).1,
        fun p' l' => (h3_inc (p' - l) (l' - l)).trans ((hShift l).2 p' l'), ?_, ?_⟩
      · dsimp only; rw [add_sub_cancel_left]; decide
      · dsimp only; rw [sub_self]; decide
  rcases hFlag with ⟨πP, πL, hPbij, hLbij, hPres, hP0, hL0⟩
  have hRel := hRelabel πP πL hPbij hLbij hPres C p l ⟨hSz, hGates, hEval, hDR⟩
  rcases hRel with ⟨D, hDSz, hDGates, hDEval, hDDR⟩
  refine ⟨D, hDSz, hDGates, ?_, ?_, ?_⟩
  · intro p' l' hpl'
    rw [hDEval]
    rw [decide_eq_true_eq]
    refine ⟨p', l', hpl', ?_, ?_⟩
    · rw [decide_eq_true_eq]; exact Or.inl rfl
    · rw [decide_eq_true_eq]; exact Or.inr rfl
  · intro x hnx _
    rw [hDEval]
    rw [decide_eq_false_iff_not]
    exact hnx
  · intro b
    have hb := hDDR b
    rw [hP0, hL0] at hb
    have hInEq : (List.ofFn fun j : Fin 14 => decide (j = Fin.castAdd 7 (0 : Fin 7) ∨ j = Fin.natAdd 7 (0 : Fin 7))) =
        (List.ofFn fun j : Fin 14 => decide ((j : ℕ) = 0 ∨ (j : ℕ) = 7)) := by
      decide
    rw [hInEq] at hb
    exact hb
