import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Identify the rows selected by zero or one active line.
-- Extract just those rows within the original gate budget, then count gates.
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_1684_1
    (rows :
      let diff : Finset (Fin 13) := {0, 1, 3, 9}
      let inc := fun p w : Fin 13 => ∃ d ∈ diff, p = w + d
      let avoids := fun (P : Finset (Fin 13)) (w : Fin 13) => ∀ p ∈ P, ¬inc p w
      let good := fun C : Circuit =>
        (∀ p w : Fin 13, inc p w → circuitFun 26 C
          (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧
        (∀ P : Finset (Fin 13), (∀ v ∉ P, ∃ w, avoids P w ∧ inc v w) →
          ((∃ w, ∀ p ∈ P, inc p w) ∨ (∃ v, ∀ w, avoids P w → inc v w)) →
          circuitFun 26 C (fun k => decide ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨
            (∃ w, k = Fin.natAdd 13 w ∧ avoids P w))) = false)
      let thin := fun x : Fin 26 → Bool =>
        ∃ w₀ : Fin 13, ∀ w : Fin 13, x (Fin.natAdd 13 w) = true → w = w₀
      let hit := fun x : Fin 26 → Bool => ∃ p w : Fin 13,
        (∃ d ∈ diff, p = w + d) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true
      ∀ C, Monotone2 C → good C → ∀ x, thin x → (circuitFun 26 C x = true ↔ hit x))
    (extract :
      let diff : Finset (Fin 13) := {0, 1, 3, 9}
      let inc := fun p w : Fin 13 => ∃ d ∈ diff, p = w + d
      let avoids := fun (P : Finset (Fin 13)) (w : Fin 13) => ∀ p ∈ P, ¬inc p w
      let good := fun C : Circuit =>
        (∀ p w : Fin 13, inc p w → circuitFun 26 C
          (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧
        (∀ P : Finset (Fin 13), (∀ v ∉ P, ∃ w, avoids P w ∧ inc v w) →
          ((∃ w, ∀ p ∈ P, inc p w) ∨ (∃ v, ∀ w, avoids P w → inc v w)) →
          circuitFun 26 C (fun k => decide ((∃ p ∈ P, k = Fin.castAdd 13 p) ∨
            (∃ w, k = Fin.natAdd 13 w ∧ avoids P w))) = false)
      let thin := fun x : Fin 26 → Bool =>
        ∃ w₀ : Fin 13, ∀ w : Fin 13, x (Fin.natAdd 13 w) = true → w = w₀
      ∀ C, Monotone2 C → C.size ≤ 63 → good C →
        ∃ D, Monotone2 D ∧ D.size ≤ C.size ∧ HasLineDegree 26 (Finset.Ico 13 26) D 1 ∧
          ∀ x, thin x → circuitFun 26 D x = circuitFun 26 C x)
    (countRows :
      let diff : Finset (Fin 13) := {0, 1, 3, 9}
      let thin := fun x : Fin 26 → Bool =>
        ∃ w₀ : Fin 13, ∀ w : Fin 13, x (Fin.natAdd 13 w) = true → w = w₀
      let hit := fun x : Fin 26 → Bool => ∃ p w : Fin 13,
        (∃ d ∈ diff, p = w + d) ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true
      ∀ D, Monotone2 D → HasLineDegree 26 (Finset.Ico 13 26) D 1 →
        (∀ x, thin x → (circuitFun 26 D x = true ↔ hit x)) → 64 ≤ D.size) :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ((∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∨ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd))) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false)) := by
  rintro ⟨C, hmono, hsize, hpos, hneg⟩
  obtain ⟨D, hD, hDC, hdegree, hagree⟩ := extract C hmono hsize ⟨hpos, hneg⟩
  have hrows := rows C hmono ⟨hpos, hneg⟩
  have hlower := countRows D hD hdegree (fun x hx => by
    rw [hagree x hx]
    exact hrows x hx)
  exact Nat.not_succ_le_self 63 (hlower.trans (hDC.trans hsize))
