import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Reduce the exact large-order plane bound to normalization plus the same
-- bound for a normalized circuit that has fewer than N * q / 100 cross AND gates.
-- If there are at least that many cross AND gates, their count already prices the size.
theorem PEqualNP.Outside.R_meta_1780_1 :
    (∀ (n : ℕ) (C : Circuit), Monotone2 C →
      (∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y) →
      ∃ C' : Circuit, Monotone2 C' ∧ C'.size ≤ C.size ∧ circuitFun n C' = circuitFun n C ∧
        C'.output < n + C'.size ∧
        ∀ (j : ℕ) (g : Gate), C'.gates[j]? = some g →
          ∃ a b : ℕ, g.inputs = [a, b] ∧ a < b ∧ b < n + j) →
    (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      199 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      Monotone2 C →
      C.output < N + N + C.size →
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a < b ∧ b < N + N + j) →
      (∀ p l : Fin N, I p l →
        circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) →
      (∀ z : Fin (N + N) → Bool,
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N + N) C z = false) →
      ∀ X : Finset ℕ,
        (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and → j ∉ X →
          ¬ ((∀ i ∈ g.inputs, ∃ x : Fin N → Bool,
                (C.wires (List.ofFn x ++ List.replicate N false)).getD i false ≠
                (C.wires (List.ofFn x ++ List.replicate N true)).getD i false) ∨
             (∀ i ∈ g.inputs, ∃ y : Fin N → Bool,
                (C.wires (List.replicate N false ++ List.ofFn y)).getD i false ≠
                (C.wires (List.replicate N true ++ List.ofFn y)).getD i false))) →
        100 * X.card < N * q →
        N * q ≤ 100 * C.size) →
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (199 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  intro hnorm hcore q N I _ C hq hN hcard hline hmon hacc hsound
  have hNpos : 2 ≤ N := by nlinarith
  have hcast_ne_nat : ∀ (p l : Fin N), Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro p l h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  have hsens : ∀ k : Fin (N + N), ∃ x y : Fin (N + N) → Bool,
      (∀ j : Fin (N + N), j ≠ k → x j = y j) ∧
      circuitFun (N + N) C x ≠ circuitFun (N + N) C y := by
    intro k
    by_cases hk : k.val < N
    · let p : Fin N := ⟨k.val, hk⟩
      have hkp : k = Fin.castAdd N p := Fin.ext rfl
      let p' : Fin N := if p.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩
      have hne : p ≠ p' := by
        intro h
        have hv := congrArg Fin.val h
        by_cases hp0 : p.val = 0 <;> simp [p', hp0] at hv
      obtain ⟨l, ⟨hIpl, _⟩, _⟩ := hline p p' hne
      let x : Fin (N + N) → Bool := fun j => decide (j = Fin.natAdd N l)
      let y : Fin (N + N) → Bool := fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l)
      refine ⟨x, y, ?_, ?_⟩
      · intro j hj
        rw [hkp] at hj
        simp only [x, y, hj, false_or]
      · have hy : circuitFun (N + N) C y = true := hacc p l hIpl
        have hx : circuitFun (N + N) C x = false := by
          apply hsound x
          rintro ⟨p0, l0, _, hp0, _⟩
          simp only [x, decide_eq_true_eq] at hp0
          exact hcast_ne_nat p0 l hp0
        rw [hx, hy]
        decide
    · let l : Fin N := ⟨k.val - N, by omega⟩
      have hkl : k = Fin.natAdd N l := Fin.ext (by simp [l]; omega)
      have hpos : 0 < (Finset.univ.filter (fun p : Fin N => I p l)).card := by
        have hc := hcard l
        rw [Fintype.card_subtype] at hc
        omega
      obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
      have hIpl : I p l := (Finset.mem_filter.mp hp).2
      let x : Fin (N + N) → Bool := fun j => decide (j = Fin.castAdd N p)
      let y : Fin (N + N) → Bool := fun j => decide (j = Fin.castAdd N p ∨ j = Fin.natAdd N l)
      refine ⟨x, y, ?_, ?_⟩
      · intro j hj
        rw [hkl] at hj
        simp only [x, y, hj, or_false]
      · have hy : circuitFun (N + N) C y = true := hacc p l hIpl
        have hx : circuitFun (N + N) C x = false := by
          apply hsound x
          rintro ⟨p0, l0, _, _, hl0⟩
          simp only [x, decide_eq_true_eq] at hl0
          exact hcast_ne_nat p l0 hl0.symm
        rw [hx, hy]
        decide
  have hnc : ∃ x y : Fin (N + N) → Bool, circuitFun (N + N) C x ≠ circuitFun (N + N) C y := by
    obtain ⟨x, y, _, hne⟩ := hsens ⟨0, by omega⟩
    exact ⟨x, y, hne⟩
  obtain ⟨C', hmon', hsize', hfun', hout', hgates'⟩ := hnorm (N + N) C hmon hnc
  have hacc' : ∀ p l : Fin N, I p l →
      circuitFun (N + N) C' (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true := by
    intro p l hI
    rw [hfun']
    exact hacc p l hI
  have hsound' : ∀ z : Fin (N + N) → Bool,
      (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      circuitFun (N + N) C' z = false := by
    intro z hno
    rw [hfun']
    exact hsound z hno
  classical
  let X : Finset ℕ := (Finset.range C'.gates.length).filter (fun j =>
    ∃ g : Gate, C'.gates[j]? = some g ∧ g.op = GateOp.and ∧
      ((∀ i ∈ g.inputs, ∃ x : Fin N → Bool,
          (C'.wires (List.ofFn x ++ List.replicate N false)).getD i false ≠
          (C'.wires (List.ofFn x ++ List.replicate N true)).getD i false) ∨
       (∀ i ∈ g.inputs, ∃ y : Fin N → Bool,
          (C'.wires (List.replicate N false ++ List.ofFn y)).getD i false ≠
          (C'.wires (List.replicate N true ++ List.ofFn y)).getD i false)))
  have hXle : X.card ≤ C'.size := by
    calc X.card ≤ (Finset.range C'.gates.length).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = C'.gates.length := Finset.card_range _
      _ = C'.size := rfl
  by_cases hXsmall : 100 * X.card < N * q
  · have hcov : ∀ (j : ℕ) (g : Gate), C'.gates[j]? = some g → g.op = GateOp.and → j ∉ X →
        ¬ ((∀ i ∈ g.inputs, ∃ x : Fin N → Bool,
              (C'.wires (List.ofFn x ++ List.replicate N false)).getD i false ≠
              (C'.wires (List.ofFn x ++ List.replicate N true)).getD i false) ∨
           (∀ i ∈ g.inputs, ∃ y : Fin N → Bool,
              (C'.wires (List.replicate N false ++ List.ofFn y)).getD i false ≠
              (C'.wires (List.replicate N true ++ List.ofFn y)).getD i false)) := by
      intro j g hj hop hnot hcross
      apply hnot
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, g, hj, hop, hcross⟩
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hj
      cases hj
    have hres := hcore q N I C' hq hN hcard hline hmon' hout' hgates' hacc' hsound' X hcov hXsmall
    exact hres.trans (Nat.mul_le_mul_left 100 hsize')
  · calc N * q ≤ 100 * X.card := by omega
      _ ≤ 100 * C'.size := Nat.mul_le_mul_left 100 hXle
      _ ≤ 100 * C.size := Nat.mul_le_mul_left 100 hsize'
