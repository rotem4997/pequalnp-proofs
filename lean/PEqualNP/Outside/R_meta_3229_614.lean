import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Defs.LratEncoding in
set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.R_meta_3229_614
    (complete : ∀ (n s : ℕ) (g : ℕ → Bool) (rows : List ℕ) (C : Circuit),
      (∀ r ∈ rows, r < 2^n) → Monotone2 C → C.size ≤ s →
      (∀ r ∈ rows, C.eval (List.ofFn fun i : Fin n => r.testBit i.val) = g r) →
      FormulaSat (enc n s g rows))
    (impossible :
      let p : List ℕ := [515,6,524,536,529,545,66,132,776,160,320,288]
      let n : List ℕ := [554,50,581,616,116,650,713,208,773,276,897,402]
      ¬ FormulaSat (enc 10 14 (fun r => p.contains r) (p ++ n))) :
    have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => (∃ x2 ∈ [(3 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (264 : ℕ)], x1.eval ((List.ofFn fun (x3 : Fin (9 : ℕ)) => x2.testBit ↑x3) ++ [Bool.false]) = Bool.false) ∧ ∃ x2 ∈ [(50 : ℕ), (116 : ℕ), (208 : ℕ), (276 : ℕ), (402 : ℕ)], x1.eval ((List.ofFn fun (x3 : Fin (9 : ℕ)) => x2.testBit ↑x3) ++ [Bool.true]) = Bool.true; have x2 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → Bool := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) => x2.eval ((List.ofFn fun (x4 : Fin (9 : ℕ)) => x3.testBit ↑x4) ++ [x3.testBit (0 : ℕ) || x3.testBit (3 : ℕ)]); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x3.gates.length = (14 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x3 → x3.output = (23 : ℕ) → x1 x3 → (∀ x8 ∈ [(3 : ℕ), (6 : ℕ), (12 : ℕ), (24 : ℕ), (17 : ℕ), (33 : ℕ), (66 : ℕ), (132 : ℕ), (264 : ℕ), (160 : ℕ), (320 : ℕ), (288 : ℕ)], x2 x3 x8 = Bool.true) → ¬∀ x9 ∈ [(42 : ℕ), (50 : ℕ), (69 : ℕ), (104 : ℕ), (116 : ℕ), (138 : ℕ), (201 : ℕ), (208 : ℕ), (261 : ℕ), (276 : ℕ), (385 : ℕ), (402 : ℕ)], x2 x3 x9 = Bool.false := by
  dsimp only
  intro C len mono _ _ yes no
  let p : List ℕ := [515,6,524,536,529,545,66,132,776,160,320,288]
  let n : List ℕ := [554,50,581,616,116,650,713,208,773,276,897,402]
  let rawPos : List ℕ := [3,6,12,24,17,33,66,132,264,160,320,288]
  let rawNeg : List ℕ := [42,50,69,104,116,138,201,208,261,276,385,402]
  let bare (r : ℕ) := List.ofFn fun i : Fin 10 => r.testBit i.val
  let added (r : ℕ) := (List.ofFn fun i : Fin 9 => r.testBit i.val) ++ [r.testBit 0 || r.testBit 3]
  have bounded : ∀ r ∈ p ++ n, r < 2^10 := by
    intro r hr
    exact of_decide_eq_true (List.all_eq_true.mp (show (p ++ n).all (fun m => decide (m < 2^10)) = true from by decide +kernel) r hr)
  have checkPos : ∀ m ∈ p, bare m = added (m % 512) ∧ m % 512 ∈ rawPos := by
    intro m hm
    exact of_decide_eq_true (List.all_eq_true.mp (show p.all (fun m => decide
      (bare m = added (m % 512) ∧ m % 512 ∈ rawPos)) = true from by decide +kernel) m hm)
  have checkNeg : ∀ m ∈ n, bare m = added (m % 512) ∧ m % 512 ∈ rawNeg ∧ p.contains m = false := by
    intro m hm
    exact of_decide_eq_true (List.all_eq_true.mp (show n.all (fun m => decide
      (bare m = added (m % 512) ∧ m % 512 ∈ rawNeg ∧ p.contains m = false)) = true from by decide +kernel) m hm)
  have small : C.size ≤ 14 := by
    unfold Circuit.size
    omega
  apply impossible
  apply complete 10 14 (fun r => p.contains r) (p ++ n) C bounded mono small
  intro r hr
  change C.eval (bare r) = p.contains r
  rcases List.mem_append.mp hr with inPos | inNeg
  · obtain ⟨e,mem⟩ := checkPos r inPos
    rw [e, List.contains_iff_mem.mpr inPos]
    exact yes _ mem
  · obtain ⟨e,mem,off⟩ := checkNeg r inNeg
    rw [e,off]
    exact no _ mem
