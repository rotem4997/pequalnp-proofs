import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 6000 in
set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_2830_691
    (project : ∀ (C : Circuit) (xs : Fin 24 → List Bool) (seed : List (BitVec 24)),
      Monotone2 C → (∀ i, seed.map (fun w => w.getLsbD i.val) = xs i) →
      ∃ ws : List (BitVec 24), ws.length = seed.length + C.size ∧
        ws.take seed.length = seed ∧
        (∀ i, (ws.getD C.output 0).getLsbD i.val = C.eval (xs i)) ∧
        ∀ j, seed.length ≤ j → j < ws.length →
          ws.getD j 0 = BitVec.allOnes 24 ∨
          ∃ a ∈ (0 :: ws.take j), ∃ b ∈ (0 :: ws.take j),
            ws.getD j 0 = a &&& b ∨ ws.getD j 0 = a ||| b)
    (exclude : ¬∃ ws : List (BitVec 24), ws.length ≤ 24 ∧
      ws.take 10 = [5521449,8532035,3227782,430612,11083800,111904,903232,13500800,15732224,14053483] ∧
      (4095 : BitVec 24) ∈ ws ∧
      ∀ j, 10 ≤ j → j < ws.length →
        ws.getD j 0 = BitVec.allOnes 24 ∨
        ∃ a ∈ (0 :: ws.take j), ∃ b ∈ (0 :: ws.take j),
          ws.getD j 0 = a &&& b ∨ ws.getD j 0 = a ||| b) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (∀ x3 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (17 : ℕ), (24 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (160 : ℕ), (264 : ℕ), (288 : ℕ), (320 : ℕ)], x1.eval ((List.ofFn fun (x5 : Fin (9 : ℕ)) => x3.testBit ↑x5) ++ [x3.testBit (0 : ℕ) || x3.testBit (1 : ℕ)]) = Bool.true) → (∀ x4 ∈ [(42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)], x1.eval ((List.ofFn fun (x6 : Fin (9 : ℕ)) => x4.testBit ↑x6) ++ [x4.testBit (0 : ℕ) || x4.testBit (1 : ℕ)]) = Bool.false) → (15 : ℕ) ≤ x1.size := by
  intro C mono yes no
  by_contra! small
  let pos : List ℕ := [3,6,12,17,24,33,66,132,160,264,288,320]
  let neg : List ℕ := [42,50,69,104,116,138,201,208,261,276,385,402]
  let row (i : Fin 24) := (pos ++ neg).getD i.val 0
  let xs (i : Fin 24) := (List.ofFn fun k : Fin 9 => (row i).testBit k.val) ++
    [(row i).testBit 0 || (row i).testBit 1]
  let seed : List (BitVec 24) :=
    [5521449,8532035,3227782,430612,11083800,111904,903232,13500800,15732224,14053483]
  have seedLength : seed.length = 10 := rfl
  have seedRows (i : Fin 24) : seed.map (fun w => w.getLsbD i.val) = xs i := by
    fin_cases i <;> decide
  have rows (i : Fin 24) :
      (row i ∈ pos ∧ (4095 : BitVec 24).getLsbD i.val = true) ∨
      (row i ∈ neg ∧ (4095 : BitVec 24).getLsbD i.val = false) := by
    fin_cases i <;> decide
  obtain ⟨ws, len, head, cols, rule⟩ := project C xs seed mono seedRows
  have value : ws.getD C.output 0 = (4095 : BitVec 24) := by
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro j hj
    let i : Fin 24 := ⟨j, hj⟩
    change (ws.getD C.output 0).getLsbD i.val = (4095 : BitVec 24).getLsbD i.val
    rw [cols i]
    rcases rows i with ⟨hp, ht⟩ | ⟨hn, hf⟩
    · rw [ht]
      exact yes (row i) hp
    · rw [hf]
      exact no (row i) hn
  have live : C.output < ws.length := by
    by_contra! late
    rw [List.getD_eq_default _ _ late] at value
    exact (show (0 : BitVec 24) ≠ 4095 by decide) value
  have member : (4095 : BitVec 24) ∈ ws := by
    rw [← value, List.getD_eq_getElem _ _ live]
    exact List.getElem_mem live
  exact exclude ⟨ws, by omega, head, member, fun j lo hi => rule j (by omega) hi⟩
