import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- A reread AND gate requires line-degree two at both endpoints.
-- The fan-out-one bound is the fixed-incidence case of L_meta_2225.
theorem PEqualNP.Outside.R_meta_1965_761
    (counts : ∀ (n : ℕ) (C : Circuit) (u v : Fin n) (g : ℕ), IsAO2 n C →
      (gateAt C g).op = .and → (n + g = C.output ∨ InCone n C g (C.output - n)) →
      gateVal n C g (pairInput u v) = true →
      (∀ b : Fin 2, wireVal n C (opnd C g b) (pairInput u u) = false ∧
        wireVal n C (opnd C g b) (pairInput v v) = false) →
      2 ≤ C.lineDeg n {u.val} ∧ 2 ≤ C.lineDeg n {v.val})
    (formula : ∀ C : Circuit, C.size ≤ 27 → IsAO2 14 C →
      (∀ j < C.gates.length, (gateAt C j).inputs.Nodup) →
      circuitFun 14 C = (fun x => decide (∃ p l : Fin 7,
        p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) →
      ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup →
      HasLineDegree 14 {0} C 1 ∨ HasLineDegree 14 {7} C 1)
    (shared : ∀ C : Circuit,
      let V (w : ℕ) (u v : Fin 14) := wireVal 14 C w (pairInput u v)
      C.size ≤ 27 → IsAO2 14 C → (∀ j < C.gates.length, (gateAt C j).inputs.Nodup) →
      circuitFun 14 C = (fun x => decide (∃ p l : Fin 7,
        p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) →
      ¬ ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup →
      2 ≤ C.lineDeg 14 {0} → 2 ≤ C.lineDeg 14 {7} →
      ∀ g : ℕ, (gateAt C g).op = .and → (14 + g = C.output ∨ InCone 14 C g (C.output - 14)) →
      V (14 + g) 0 7 = true →
      (∀ b : Fin 2, V (opnd C g b) 0 0 = false ∧ V (opnd C g b) 7 7 = false) → False) :
    ¬ ∃ C : Circuit,
      C.size ≤ 27 ∧
      (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
        (g.op = .and ∨ g.op = .or) ∧
        ∃ a b : ℕ, g.inputs = [a, b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) ∧
      ∃ j : ℕ, (gateAt C j).op = .and ∧
        (14 + j = C.output ∨ InCone 14 C j (C.output - 14)) ∧
        gateVal 14 C j (pairInput (0 : Fin 14) 7) = true ∧
        ∀ b : Fin 2, wireVal 14 C (opnd C j b) (pairInput (0 : Fin 14) 0) = false ∧
          wireVal 14 C (opnd C j b) (pairInput (7 : Fin 14) 7) = false := by
  -- The shape and Fano table conversion follow R_meta_1965_5.
  intro h
  obtain ⟨C, hSize, hGate, hEval, g, hAnd, hOut, hPair, hSingles⟩ := h
  have get (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
    change C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j]
    exact List.getD_eq_getElem _ _ hj
  have facts (j : ℕ) (hj : j < C.gates.length) :=
    hGate j (C.gates[j]'hj) (List.getElem?_eq_some_iff.mpr ⟨hj, rfl⟩)
  have hAO : IsAO2 14 C := by
    refine ⟨?_, ?_, ?_⟩
    · intro g' hg'
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg'
      exact (facts j hj).1
    · intro j hj w hw
      obtain ⟨a, b, he, _, ha, hb⟩ := (facts j hj).2
      rw [get j hj, he] at hw
      rcases (show w = a ∨ w = b by simpa using hw) with rfl | rfl
      · exact ha
      · exact hb
    · intro g' hg'
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg'
      obtain ⟨a, b, he, _, _, _⟩ := (facts j hj).2
      simp [he]
  have hDistinct (j : ℕ) (hj : j < C.gates.length) : (gateAt C j).inputs.Nodup := by
    obtain ⟨a, b, he, hn, _, _⟩ := (facts j hj).2
    rw [get j hj, he]
    simpa using hn
  have geometry : ∀ p l : Fin 7, p ∈ fanoLines l ↔ p = l ∨ p = l + 1 ∨ p = l + 3 := by
    decide +kernel
  have hTarget : circuitFun 14 C = (fun x => decide (∃ p l : Fin 7,
      p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)) := by
    funext x
    exact Bool.eq_iff_iff.mpr ((hEval x).trans (by simp only [decide_eq_true_eq, geometry]))
  have degree := counts 14 C 0 7 g hAO hAnd hOut hPair hSingles
  change 2 ≤ C.lineDeg 14 {0} ∧ 2 ≤ C.lineDeg 14 {7} at degree
  by_cases tree : ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup
  · rcases formula C hSize hAO hDistinct hTarget tree with left | right
    · change C.lineDeg 14 {0} ≤ 1 at left
      omega
    · change C.lineDeg 14 {7} ≤ 1 at right
      omega
  · exact shared C hSize hAO hDistinct hTarget tree degree.1 degree.2 g hAnd hOut hPair hSingles
