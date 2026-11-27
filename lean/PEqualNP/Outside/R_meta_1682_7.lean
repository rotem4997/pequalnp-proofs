import Mathlib
import PEqualNP.Defs

-- Count OR gates and AND gates separately: a circuit right on these inputs has at least 51 OR
-- gates (the 52 incident pairs less one) and at least 13 AND gates (the cover number), so at
-- least 64 gates in all. The line of w is written as the four points w, w + 1, w + 3, w + 9.
theorem PEqualNP.Outside.R_meta_1682_7 :
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ p w : Fin 13, (p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) → (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (pp = w2 ∨ pp = w2 + 1 ∨ pp = w2 + 3 ∨ pp = w2 + 9)) ∧ (v = w2 ∨ v = w2 + 1 ∨ v = w2 + 3 ∨ v = w2 + 9)) → ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, (p3 = w3 ∨ p3 = w3 + 1 ∨ p3 = w3 + 3 ∨ p3 = w3 + 9)) ∧ ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (pp = w4 ∨ pp = w4 + 1 ∨ pp = w4 + 3 ∨ pp = w4 + 9)) → (v4 = w4 ∨ v4 = w4 + 1 ∨ v4 = w4 + 3 ∨ v4 = w4 + 9)) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (pp = ww ∨ pp = ww + 1 ∨ pp = ww + 3 ∨ pp = ww + 9))))) = false) → 51 ≤ {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or}.ncard) →
    (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → (∀ p w : Fin 13, (p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) → (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (pp = w2 ∨ pp = w2 + 1 ∨ pp = w2 + 3 ∨ pp = w2 + 9)) ∧ (v = w2 ∨ v = w2 + 1 ∨ v = w2 + 3 ∨ v = w2 + 9)) → ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, (p3 = w3 ∨ p3 = w3 + 1 ∨ p3 = w3 + 3 ∨ p3 = w3 + 9)) ∧ ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (pp = w4 ∨ pp = w4 + 1 ∨ pp = w4 + 3 ∨ pp = w4 + 9)) → (v4 = w4 ∨ v4 = w4 + 1 ∨ v4 = w4 + 3 ∨ v4 = w4 + 9)) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (pp = ww ∨ pp = ww + 1 ∨ pp = ww + 3 ∨ pp = ww + 9))))) = false) → 13 ≤ {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}.ncard) →
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ p w : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = w + dd) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun k => decide (k = Fin.castAdd 13 p ∨ k = Fin.natAdd 13 w)) = true) ∧ (∀ P : Finset (Fin 13), (∀ v : Fin 13, v ∉ P → ∃ w2 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w2 + dd)) ∧ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v = w2 + dd)) → ¬ (∃ w3 : Fin 13, ∀ p3 ∈ P, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p3 = w3 + dd)) ∧ ¬ (∃ v4 : Fin 13, ∀ w4 : Fin 13, (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = w4 + dd)) → (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), v4 = w4 + dd)) → PEqualNP.MetaComplexity.circuitFun (13 + 13) C (fun kk : Fin (13 + 13) => decide ((∃ pp ∈ P, kk = Fin.castAdd 13 pp) ∨ (∃ ww : Fin 13, kk = Fin.natAdd 13 ww ∧ (∀ pp ∈ P, ¬ (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), pp = ww + dd))))) = false)) := by
  intro hor hand hex
  obtain ⟨C, hmono, hsize, h1, h2⟩ := hex
  have key : ∀ a b : Fin 13, (∃ dd ∈ ({0, 1, 3, 9} : Finset (Fin 13)), a = b + dd) ↔
      (a = b ∨ a = b + 1 ∨ a = b + 3 ∨ a = b + 9) := by
    intro a b
    simp
  simp only [key] at h1 h2
  have e1 := hor C hmono h1 h2
  have e2 := hand C hmono h1 h2
  have hdisj : Disjoint {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or}
      {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and} := by
    rw [Set.disjoint_left]
    intro i ha hb
    rw [Set.mem_ofPred_eq] at ha hb
    rw [ha] at hb
    exact PEqualNP.CircuitLowerBounds.GateOp.noConfusion hb
  have hsum := Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
  have hle : ({i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or} ∪
      {i : Fin C.gates.length | (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and}).ncard ≤
      C.gates.length := by
    calc _ ≤ (Set.univ : Set (Fin C.gates.length)).ncard := Set.ncard_le_ncard (Set.subset_univ _)
      _ = C.gates.length := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hs : C.size = C.gates.length := rfl
  omega
