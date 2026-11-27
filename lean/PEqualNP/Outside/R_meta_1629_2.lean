import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Reduce the projective-plane monotone lower bound to three clean obligations:
-- (1) a linear sensitivity bound closing q <= 100,
-- (2) normalization of non-constant fan-in-two monotone circuits to strict fan-in-two DAGs, and
-- (3) the large-q bound for normalized circuits with fewer than N * q / 100 cross AND gates.
theorem PEqualNP.Outside.R_meta_1629_2 :
    (∀ (n : ℕ) (C : Circuit), Monotone2 C →
      (∀ k : Fin n, ∃ x y : Fin n → Bool, (∀ j : Fin n, j ≠ k → x j = y j) ∧
        circuitFun n C x ≠ circuitFun n C y) →
      n ≤ C.size + 1) →
    (∀ (n : ℕ) (C : Circuit), Monotone2 C →
      (∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y) →
      ∃ C' : Circuit, Monotone2 C' ∧ C'.size ≤ C.size ∧ circuitFun n C' = circuitFun n C ∧
        C'.output < n + C'.size ∧
        ∀ (j : ℕ) (g : Gate), C'.gates[j]? = some g →
          ∃ a b : ℕ, g.inputs = [a, b] ∧ a < b ∧ b < n + j) →
    (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      100 < q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      Monotone2 C →
      C.output < N + N + C.size →
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a < b ∧ b < N + N + j) →
      (∀ p l : Fin N, I p l →
        circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) →
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
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
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ p l : Fin N, I p l → PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true) →
      (∀ z : Fin (N + N) → Bool, (Finset.univ.filter (fun l : Fin N => z (Fin.natAdd N l) = true)).card ≤ q → (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) →
      N * q ≤ 100 * C.size := by
  intro hlin hnorm hcore q N I _ C hq hN hcard hline hmon hacc hsound
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
          · have hsub : Finset.univ.filter (fun l' : Fin N => x (Fin.natAdd N l') = true) ⊆ {l} := by
              intro l' hl'
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, x, decide_eq_true_eq] at hl'
              have hval := congrArg Fin.val hl'
              simp only [Fin.val_natAdd] at hval
              exact Finset.mem_singleton.mpr (Fin.ext (by omega))
            exact (Finset.card_le_card hsub).trans (by simp; omega)
          · rintro ⟨p0, l0, _, hp0, _⟩
            simp only [x, decide_eq_true_eq] at hp0
            exact hcast_ne_nat p0 l hp0
        rw [hx, hy]
        decide
    · let l : Fin N := ⟨k.val - N, by omega⟩
      have hkl : k = Fin.natAdd N l := Fin.ext (by simp [l]; omega)
      have hpos : 0 < (Finset.univ.filter (fun p : Fin N => I p l)).card := by
        rw [hcard l]; omega
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
          · have hemp : Finset.univ.filter (fun l' : Fin N => x (Fin.natAdd N l') = true) = ∅ := by
              ext l'
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
                iff_false, x, decide_eq_true_eq]
              intro h
              exact hcast_ne_nat p l' h.symm
            rw [hemp]
            simp
          · rintro ⟨p0, l0, _, _, hl0⟩
            simp only [x, decide_eq_true_eq] at hl0
            exact hcast_ne_nat p l0 hl0.symm
        rw [hx, hy]
        decide
  have hNsize : N ≤ C.size := by
    have h2N := hlin (N + N) C hmon hsens
    omega
  by_cases hq100 : q ≤ 100
  · calc N * q ≤ N * 100 := Nat.mul_le_mul_left N hq100
      _ = 100 * N := Nat.mul_comm N 100
      _ ≤ 100 * C.size := Nat.mul_le_mul_left 100 hNsize
  · have hqgt : 100 < q := by omega
    have hnc : ∃ x y : Fin (N + N) → Bool, circuitFun (N + N) C x ≠ circuitFun (N + N) C y := by
      obtain ⟨x, y, _, hne⟩ := hsens ⟨0, by omega⟩
      exact ⟨x, y, hne⟩
    obtain ⟨C', hmon', hsize', hfun', hout', hgates'⟩ := hnorm (N + N) C hmon hnc
    have hacc' : ∀ p l : Fin N, I p l →
        circuitFun (N + N) C' (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true := by
      intro p l hI
      rw [hfun']
      exact hacc p l hI
    have hcard' : ∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1 := by
      intro l
      rw [Fintype.card_subtype]
      exact hcard l
    have hsound' : ∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        circuitFun (N + N) C' z = false := by
      intro z hle hno
      rw [hfun']
      rw [Fintype.card_subtype] at hle
      exact hsound z hle hno
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
      have hres := hcore q N I C' hqgt hN hcard' hline hmon' hout' hgates' hacc' hsound' X hcov hXsmall
      exact hres.trans (Nat.mul_le_mul_left 100 hsize')
    · calc N * q ≤ 100 * X.card := by omega
        _ ≤ 100 * C'.size := Nat.mul_le_mul_left 100 hXle
        _ ≤ 100 * C.size := Nat.mul_le_mul_left 100 hsize'
