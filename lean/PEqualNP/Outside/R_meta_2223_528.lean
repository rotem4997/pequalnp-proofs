import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_2223_528
    (transport :
      let inc := fun p l : Fin 7 => p = l ∨ p = l + 1 ∨ p = l + 3
      let valid := fun C : Circuit => C.size ≤ 27 ∧
        (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
          (g.op = .and ∨ g.op = .or) ∧
          ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧
        ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 7, inc p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true
      let tree := fun C : Circuit =>
        ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup
      ∀ (P L : Equiv.Perm (Fin 7)), (∀ p l, inc (P p) (L l) ↔ inc p l) →
        ∀ C : Circuit, valid C → ∃ D : Circuit, valid D ∧ (tree D ↔ tree C) ∧
          (∀ p : Fin 7, D.lineDeg 14 {↑(P p)} = C.lineDeg 14 {↑p}) ∧
          (∀ l : Fin 7, D.lineDeg 14 {7 + (L l).val} = C.lineDeg 14 {7 + l.val}))
    (canonical :
      let inc := fun p l : Fin 7 => p = l ∨ p = l + 1 ∨ p = l + 3
      let valid := fun C : Circuit => C.size ≤ 27 ∧
        (∀ (j : ℕ) (g : Gate), C.gates[j]? = some g →
          (g.op = .and ∨ g.op = .or) ∧
          ∃ a b : ℕ, g.inputs = [a,b] ∧ a ≠ b ∧ a < 14 + j ∧ b < 14 + j) ∧
        ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔
          ∃ p l : Fin 7, inc p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true
      let tree := fun C : Circuit =>
        ((C.output :: C.gates.flatMap Gate.inputs).filter (fun w => decide (14 ≤ w))).Nodup
      ∀ C : Circuit, valid C → ¬ tree C →
        2 ≤ C.lineDeg 14 {0} → 2 ≤ C.lineDeg 14 {7} →
        ∃ D : Circuit, valid D ∧ tree D ∧
          2 ≤ D.lineDeg 14 {0} ∧ 2 ≤ D.lineDeg 14 {7}) :
have x1 : Fin (7 : ℕ) → Fin (7 : ℕ) → Prop := fun (x1 x2 : Fin (7 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (7 : ℕ)) ∨ x1 = x2 + (3 : Fin (7 : ℕ)); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ ∀ (x3 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (7 : ℕ)) (x5 : Fin (7 : ℕ)), x1 x4 x5 ∧ x3 (Fin.castAdd (7 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (7 : ℕ) x5) = Bool.true; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => (List.filter (fun (x4 : ℕ) => Decidable.decide ((14 : ℕ) ≤ x4)) (x3.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x3.gates)).Nodup; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 x6 : Fin (7 : ℕ)), x2 x4 → x1 x5 x6 → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {↑x5} → (2 : ℕ) ≤ x4.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), x2 x11 ∧ x3 x11 ∧ (2 : ℕ) ≤ x11.lineDeg (14 : ℕ) {↑x5} ∧ (2 : ℕ) ≤ x11.lineDeg (14 : ℕ) {(7 : ℕ) + ↑x6} := by
  intro inc valid tree C p l hv hflag hp hl
  by_cases ht : tree C
  · exact ⟨C, hv, ht, hp, hl⟩
  let mul : Fin 3 → Fin 7 := fun k => if k = 0 then 1 else if k = 1 then 2 else 4
  let off : Fin 3 → Fin 7 := fun k => if k = 0 then 0 else if k = 1 then 1 else 3
  let point (k : Fin 3) (b z : Fin 7) := mul k * (z - b) + off k
  let line (k : Fin 3) (b z : Fin 7) := mul k * (z - b)
  have pinj : ∀ (k : Fin 3) (b u v : Fin 7), point k b u = point k b v → u = v := by
    dsimp only [point, mul, off]
    decide +kernel
  have linj : ∀ (k : Fin 3) (b u v : Fin 7), line k b u = line k b v → u = v := by
    dsimp only [line, mul]
    decide +kernel
  have psurj : ∀ (k : Fin 3) (b v : Fin 7), ∃ u : Fin 7, point k b u = v := by
    dsimp only [point, mul, off]
    decide +kernel
  have lsurj : ∀ (k : Fin 3) (b v : Fin 7), ∃ u : Fin 7, line k b u = v := by
    dsimp only [line, mul]
    decide +kernel
  have hauto : ∀ (k : Fin 3) (b u v : Fin 7), inc (point k b u) (line k b v) ↔ inc u v := by
    dsimp only [inc, point, line, mul, off]
    decide +kernel
  have hmove : ∀ u v : Fin 7, inc u v → ∃ k : Fin 3, point k v u = 0 ∧ line k v v = 0 := by
    dsimp only [inc, point, line, mul, off]
    decide +kernel
  obtain ⟨k, hmP, hmL⟩ := hmove p l hflag
  classical
  let P : Equiv.Perm (Fin 7) :=
    Equiv.ofBijective (point k l) ⟨fun _ _ => pinj k l _ _, psurj k l⟩
  let L : Equiv.Perm (Fin 7) :=
    Equiv.ofBijective (line k l) ⟨fun _ _ => linj k l _ _, lsurj k l⟩
  have pzero : P p = 0 := hmP
  have lzero : L l = 0 := hmL
  have hi : ∀ u v, inc (P u) (L v) ↔ inc u v := hauto k l
  obtain ⟨E, he, hte, hep, hel⟩ := transport P L hi C hv
  have ep : 2 ≤ E.lineDeg 14 {0} := by
    have eq := hep p
    rw [pzero] at eq
    change E.lineDeg 14 {0} = _ at eq
    rw [eq]
    exact hp
  have el : 2 ≤ E.lineDeg 14 {7} := by
    have eq := hel l
    rw [lzero] at eq
    change E.lineDeg 14 {7} = _ at eq
    rw [eq]
    exact hl
  obtain ⟨F, hf, htf, fp, fl⟩ := canonical E he (fun h => ht (hte.mp h)) ep el
  have hir : ∀ u v, inc (P.symm u) (L.symm v) ↔ inc u v := by
    intro u v
    simpa only [Equiv.apply_symm_apply] using (hi (P.symm u) (L.symm v)).symm
  obtain ⟨D, hd, htd, hdp, hdl⟩ := transport P.symm L.symm hir F hf
  have pb : P.symm 0 = p := by rw [← pzero, Equiv.symm_apply_apply]
  have lb : L.symm 0 = l := by rw [← lzero, Equiv.symm_apply_apply]
  refine ⟨D, hd, htd.mpr htf, ?_, ?_⟩
  · have eq := hdp 0
    rw [pb] at eq
    rw [eq]
    exact fp
  · have eq := hdl 0
    rw [lb] at eq
    rw [eq]
    exact fl
