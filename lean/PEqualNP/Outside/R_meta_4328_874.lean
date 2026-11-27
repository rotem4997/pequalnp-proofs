import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4328_874
    (move :
      have E : Fin 42 → Fin 42 → Prop := fun u v =>
        u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      have Good : Circuit → Prop := fun C => Monotone2 C ∧
        (∀ u v : Fin 42, E u v →
          C.eval (List.ofFn fun w : Fin 42 => decide (w = u ∨ w = v)) = true) ∧
        ∀ x : Fin 42 → Bool, (∀ u, x u = true ↔ ∀ v, x v = true → ¬ (E u v ∨ E v u)) →
          C.eval (List.ofFn x) = false
      ∀ C : Circuit, Good C → C.size ≤ 124 →
        ∃ D : Circuit, Good D ∧ D.size ≤ C.size ∧
          ∃ (j : ℕ) (g : Gate), D.gates[j]? = some g ∧ g.op = GateOp.and ∧
            (D.wires (List.ofFn fun i : Fin 42 =>
              decide (i.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ)))).getD (42 + j) false
              = true)
    (noConstant :
      have E : Fin 42 → Fin 42 → Prop := fun u v =>
        u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      have Good : Circuit → Prop := fun C => Monotone2 C ∧
        (∀ u v : Fin 42, E u v →
          C.eval (List.ofFn fun w : Fin 42 => decide (w = u ∨ w = v)) = true) ∧
        ∀ x : Fin 42 → Bool, (∀ u, x u = true ↔ ∀ v, x v = true → ¬ (E u v ∨ E v u)) →
          C.eval (List.ofFn x) = false
      ∀ C : Circuit, Good C →
        (∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ g.op = GateOp.and ∧
          (C.wires (List.ofFn fun _ : Fin 42 => false)).getD (42 + j) false = true) →
        ∃ D : Circuit, Good D ∧ D.size < C.size)
    (single :
      have E : Fin 42 → Fin 42 → Prop := fun u v =>
        u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      have Good : Circuit → Prop := fun C => Monotone2 C ∧
        (∀ u v : Fin 42, E u v →
          C.eval (List.ofFn fun w : Fin 42 => decide (w = u ∨ w = v)) = true) ∧
        ∀ x : Fin 42 → Bool, (∀ u, x u = true ↔ ∀ v, x v = true → ¬ (E u v ∨ E v u)) →
          C.eval (List.ofFn x) = false
      ∀ C : Circuit, Good C → C.size ≤ 124 → (∀ D : Circuit, Good D → C.size ≤ D.size) →
        (∃ (u : Fin 42) (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ g.op = GateOp.and ∧
          (C.wires (List.ofFn fun i : Fin 42 => decide (i = u))).getD (42 + j) false = true) →
        False)
    (pair :
      have E : Fin 42 → Fin 42 → Prop := fun u v =>
        u.val < 21 ∧ 21 ≤ v.val ∧ (v.val + 21 - u.val) % 21 ∈ ([0, 5, 7, 17, 20] : List ℕ)
      have Good : Circuit → Prop := fun C => Monotone2 C ∧
        (∀ u v : Fin 42, E u v →
          C.eval (List.ofFn fun w : Fin 42 => decide (w = u ∨ w = v)) = true) ∧
        ∀ x : Fin 42 → Bool, (∀ u, x u = true ↔ ∀ v, x v = true → ¬ (E u v ∨ E v u)) →
          C.eval (List.ofFn x) = false
      ∀ C : Circuit, Good C → C.size ≤ 124 → (∀ D : Circuit, Good D → C.size ≤ D.size) →
        (∀ (u : Fin 42) (j : ℕ) (g : Gate), C.gates[j]? = some g → g.op = GateOp.and →
          (C.wires (List.ofFn fun i : Fin 42 => decide (i = u))).getD (42 + j) false = false) →
        (∃ (j : ℕ) (g : Gate), C.gates[j]? = some g ∧ g.op = GateOp.and ∧
          (C.wires (List.ofFn fun i : Fin 42 =>
            decide (i.val ∈ ([0, 1, 2, 6, 8, 18, 24, 31, 33, 37] : List ℕ)))).getD (42 + j) false
            = true) →
        False) :
    have x1 : Fin (42 : ℕ) → Fin (42 : ℕ) → Prop := fun (x1 x2 : Fin (42 : ℕ)) => ↑x1 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x2 ∧ (↑x2 + (21 : ℕ) - ↑x1) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]; have x2 : (Fin (42 : ℕ) → Bool) → Prop := fun (x2 : Fin (42 : ℕ) → Bool) => ∀ (x3 : Fin (42 : ℕ)), x2 x3 = Bool.true ↔ ∀ (x4 : Fin (42 : ℕ)), x2 x4 = Bool.true → ¬(x1 x3 x4 ∨ x1 x4 x3); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → x3.size ≤ (124 : ℕ) → (∃ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x3.gates[x6]? = Option.some x7 ∧ x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x3.wires (List.ofFn fun (x8 : Fin (42 : ℕ)) => Decidable.decide (↑x8 ∈ [(0 : ℕ), (1 : ℕ), (2 : ℕ), (6 : ℕ), (8 : ℕ), (18 : ℕ), (24 : ℕ), (31 : ℕ), (33 : ℕ), (37 : ℕ)]))).getD ((42 : ℕ) + x6) Bool.false = Bool.true) → (∀ (x7 x8 : Fin (42 : ℕ)), x1 x7 x8 → x3.eval (List.ofFn fun (x10 : Fin (42 : ℕ)) => Decidable.decide (x10 = x7 ∨ x10 = x8)) = Bool.true) → (∀ (x8 : Fin (42 : ℕ) → Bool), x2 x8 → x3.eval (List.ofFn x8) = Bool.false) → False := by
  intro E Closed C hmono hsize _ hpos hneg
  classical
  have hex : ∃ m : ℕ, ∃ D : Circuit, (Monotone2 D ∧
      (∀ u v : Fin 42, E u v →
        D.eval (List.ofFn fun w : Fin 42 => decide (w = u ∨ w = v)) = true) ∧
      ∀ x : Fin 42 → Bool, (∀ u, x u = true ↔ ∀ v, x v = true → ¬ (E u v ∨ E v u)) →
        D.eval (List.ofFn x) = false) ∧ D.size = m :=
    ⟨C.size, C, ⟨hmono, hpos, hneg⟩, rfl⟩
  obtain ⟨C0, hG0, hs0⟩ := Nat.find_spec hex
  have hmin : ∀ D : Circuit, (Monotone2 D ∧
      (∀ u v : Fin 42, E u v →
        D.eval (List.ofFn fun w : Fin 42 => decide (w = u ∨ w = v)) = true) ∧
      ∀ x : Fin 42 → Bool, (∀ u, x u = true ↔ ∀ v, x v = true → ¬ (E u v ∨ E v u)) →
        D.eval (List.ofFn x) = false) → Nat.find hex ≤ D.size :=
    fun D hD => Nat.find_min' hex ⟨D, hD, rfl⟩
  have hle : Nat.find hex ≤ C.size := hmin C ⟨hmono, hpos, hneg⟩
  obtain ⟨D, hGD, hsD, hdD⟩ := move C0 hG0 (by omega)
  have hDleast : ∀ D' : Circuit, (Monotone2 D' ∧
      (∀ u v : Fin 42, E u v →
        D'.eval (List.ofFn fun w : Fin 42 => decide (w = u ∨ w = v)) = true) ∧
      ∀ x : Fin 42 → Bool, (∀ u, x u = true ↔ ∀ v, x v = true → ¬ (E u v ∨ E v u)) →
        D'.eval (List.ofFn x) = false) → D.size ≤ D'.size := by
    intro D' hD'
    have h := hmin D' hD'
    omega
  by_cases hA : ∃ (j : ℕ) (g : Gate), D.gates[j]? = some g ∧ g.op = GateOp.and ∧
      (D.wires (List.ofFn fun _ : Fin 42 => false)).getD (42 + j) false = true
  · obtain ⟨D2, hG2, hs2⟩ := noConstant D hGD hA
    have h := hDleast D2 hG2
    omega
  · by_cases hB : ∃ (u : Fin 42) (j : ℕ) (g : Gate), D.gates[j]? = some g ∧
        g.op = GateOp.and ∧
        (D.wires (List.ofFn fun i : Fin 42 => decide (i = u))).getD (42 + j) false = true
    · exact single D hGD (by omega) hDleast hB
    · refine pair D hGD (by omega) hDleast ?_ hdD
      intro u j g hj hop
      by_contra hne
      exact hB ⟨u, j, g, hj, hop, Bool.eq_true_of_not_eq_false hne⟩
