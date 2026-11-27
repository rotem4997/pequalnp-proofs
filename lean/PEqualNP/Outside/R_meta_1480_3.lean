import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

-- Reduction of the Fano double re-read bound to two sub-goals. First: in the AND/OR model of
-- fan-in exactly two with distinct earlier reads, every circuit that computes the incidence and
-- carries the double re-read has at least 29 gates. Second: a size of at most 27 cannot carry
-- 29 gates. The two give the row by the boundary arithmetic alone.
theorem PEqualNP.Outside.R_meta_1480_3 :
    (∀ (C : Circuit), IsAO2 14 C → (∀ j < C.size, opnd C j 0 ≠ opnd C j 1) →
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, u ∈ fanoLines t ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) →
      (∃ p l : Fin 7, p ∈ fanoLines l ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false)) →
      29 ≤ C.size) →
    (∀ (s : ℕ), s ≤ 27 → 29 ≤ s → False) →
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, C.size ≤ 27 ∧ (∀ (j : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[j]? = some g → (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧ (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ ∃ u t : Fin 7, (u = t ∨ u = t + 1 ∨ u = t + 3) ∧ x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true) ∧ ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧ (∃ v : ℕ → Bool, (∀ my : Fin 7, v my.val = false ∧ v (7 + my.val) = decide (my = l)) ∧ (∀ (ky : ℕ) (hy : PEqualNP.CircuitLowerBounds.Gate) (cy dy : ℕ), C.gates[ky]? = some hy → hy.inputs = [cy, dy] → (hy.op = PEqualNP.CircuitLowerBounds.GateOp.and → v (14 + ky) = (((C.wires (List.ofFn (fun iy : Fin 14 => decide (iy = Fin.castAdd 7 p)))).getD cy false && v dy) || (v cy && (C.wires (List.ofFn (fun ey : Fin 14 => decide (ey = Fin.castAdd 7 p)))).getD dy false))) ∧ (hy.op = PEqualNP.CircuitLowerBounds.GateOp.or → v (14 + ky) = (v cy || v dy))) ∧ v C.output = false) ∧ (∃ w : ℕ → Bool, (∀ mx : Fin 7, w mx.val = decide (mx = p) ∧ w (7 + mx.val) = false) ∧ (∀ (kx : ℕ) (hx : PEqualNP.CircuitLowerBounds.Gate) (cx dx : ℕ), C.gates[kx]? = some hx → hx.inputs = [cx, dx] → (hx.op = PEqualNP.CircuitLowerBounds.GateOp.and → w (14 + kx) = (((C.wires (List.ofFn (fun ix : Fin 14 => decide (ix = Fin.natAdd 7 l)))).getD cx false && w dx) || (w cx && (C.wires (List.ofFn (fun ex : Fin 14 => decide (ex = Fin.natAdd 7 l)))).getD dx false))) ∧ (hx.op = PEqualNP.CircuitLowerBounds.GateOp.or → w (14 + kx) = (w cx || w dx))) ∧ w C.output = false)) := by
  intro hBound hArith
  rintro ⟨C, hsize, hA, hB, hR⟩
  have hInc : ∀ p l : Fin 7, ((p = l ∨ p = l + 1 ∨ p = l + 3) ↔ p ∈ fanoLines l) := by
    decide
  have hgates : ∀ j < C.gates.length, C.gates[j]? = some (gateAt C j) := by
      intro j hj
      show C.gates[j]? = some (C.gates.getD j ⟨GateOp.or, []⟩)
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  have hspec : ∀ j < C.gates.length,
      ∃ a b : ℕ, (gateAt C j).inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j := by
    intro j hj
    obtain ⟨-, a, b, hins, hab, ha, hb⟩ := hA j (gateAt C j) (hgates j hj)
    exact ⟨a, b, hins, hab, ha, hb⟩
  have hAO2 : IsAO2 14 C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hg
      have hgj : C.gates[j]? = some g := by rw [List.getElem?_eq_getElem hj, hjeq]
      exact (hA j g hgj).1
    · intro j hj i hi
      obtain ⟨a, b, hins, -, ha, hb⟩ := hspec j hj
      rw [hins] at hi
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      omega
    · intro g hg
      obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hg
      have hgj : C.gates[j]? = some g := by rw [List.getElem?_eq_getElem hj, hjeq]
      obtain ⟨a, b, hins, -⟩ := (hA j g hgj).2
      rw [hins]
      simp
  have hdist : ∀ j < C.size, opnd C j 0 ≠ opnd C j 1 := by
      intro j hj
      obtain ⟨a, b, hins, hab, -, -⟩ := hspec j hj
      have h0 : opnd C j 0 = a := by
        show (gateAt C j).inputs.getD 0 0 = a
        rw [hins]
        rfl
      have h1 : opnd C j 1 = b := by
        show (gateAt C j).inputs.getD 1 0 = b
        rw [hins]
        rfl
      rw [h0, h1]
      exact hab
  have hB' : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u t : Fin 7, u ∈ fanoLines t ∧
        x (Fin.castAdd 7 u) = true ∧ x (Fin.natAdd 7 t) = true := by
    intro x
    rw [hB x]
    constructor
    · rintro ⟨u, t, h, h1, h2⟩
      exact ⟨u, t, (hInc u t).mp h, h1, h2⟩
    · rintro ⟨u, t, h, h1, h2⟩
      exact ⟨u, t, (hInc u t).mpr h, h1, h2⟩
  obtain ⟨p, l, hinc, hv, hw⟩ := hR
  have h29 : 29 ≤ C.size := hBound C hAO2 hdist hB' ⟨p, l, (hInc p l).mp hinc, hv, hw⟩
  exact hArith C.size hsize h29
