import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadTwo

theorem PEqualNP.Outside.R_meta_5232_743
    (h_p9 : ∀ (E : Circuit), Monotone2 E → E.size ≤ 15 →
      ∃ y : Fin 9 → Bool, E.eval (List.ofFn y) ≠ (y (0 : Fin (9 : ℕ)) && y (1 : Fin (9 : ℕ)) || y (1 : Fin (9 : ℕ)) && y (2 : Fin (9 : ℕ)) || y (2 : Fin (9 : ℕ)) && y (3 : Fin (9 : ℕ)) || y (0 : Fin (9 : ℕ)) && y (5 : Fin (9 : ℕ)) || y (1 : Fin (9 : ℕ)) && y (6 : Fin (9 : ℕ)) || y (2 : Fin (9 : ℕ)) && y (7 : Fin (9 : ℕ)) || y (3 : Fin (9 : ℕ)) && y (8 : Fin (9 : ℕ)) || y (4 : Fin (9 : ℕ)) && y (6 : Fin (9 : ℕ)) || y (6 : Fin (9 : ℕ)) && y (8 : Fin (9 : ℕ)) || y (8 : Fin (9 : ℕ)) && y (5 : Fin (9 : ℕ)) || y (5 : Fin (9 : ℕ)) && y (7 : Fin (9 : ℕ)) || y (7 : Fin (9 : ℕ)) && y (4 : Fin (9 : ℕ))))
    (h_and_and : ∀ (C : Circuit) (i0 j0 i2 j2 : ℕ),
      Monotone2 C → ReadsBack 11 C → C.size ≤ 18 → 11 ≤ C.output → C.output < 11 + C.size →
      (let g : ℕ → Gate := gateAt C
       let f : ℕ → ℕ := readsIn C (Finset.range C.size)
       isAnd C i0 ∧ isOr C j0 ∧ 0 ∈ (g i0).inputs ∧ 11 + i0 ∈ (g j0).inputs ∧
       isAnd C i2 ∧ isOr C j2 ∧ 2 ∈ (g i2).inputs ∧ 11 + i2 ∈ (g j2).inputs ∧
       f 0 = 1 ∧ f (11 + i0) = 1 ∧ f 2 = 1 ∧ f (11 + i2) = 1) →
      ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 || x 2]) ≠ (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) || x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ))))
    (h_and_or : ∀ (C : Circuit) (i0 j0 : ℕ),
      Monotone2 C → ReadsBack 11 C → C.size ≤ 18 → 11 ≤ C.output → C.output < 11 + C.size →
      isAnd C i0 → isOr C j0 → 0 ∈ (gateAt C i0).inputs → 11 + i0 ∈ (gateAt C j0).inputs →
      (let f : ℕ → ℕ := readsIn C (Finset.range C.size)
       f 0 = 1 ∧ f (11 + i0) = 1 ∧ 1 ≤ f 2 ∧ f 2 ≤ 2) →
      (∀ k < C.size, 2 ∈ (gateAt C k).inputs → isOr C k) →
      ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 || x 2]) ≠ (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) || x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ))))
    (h_or_or : ∀ (C : Circuit),
      Monotone2 C → ReadsBack 11 C → C.size ≤ 18 → 11 ≤ C.output → C.output < 11 + C.size →
      (let f : ℕ → ℕ := readsIn C (Finset.range C.size)
       1 ≤ f 0 ∧ f 0 ≤ 2 ∧ 1 ≤ f 2 ∧ f 2 ≤ 2) →
      (∀ k < C.size, 0 ∈ (gateAt C k).inputs → isOr C k) →
      (∀ k < C.size, 2 ∈ (gateAt C k).inputs → isOr C k) →
      ∃ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [x 0 || x 2]) ≠ (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) || x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)))) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (11 : ℕ) x1 → x1.size ≤ (18 : ℕ) → (11 : ℕ) ≤ x1.output → x1.output < (11 : ℕ) + x1.size → ∃ (x7 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [x7 (0 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ))]) ≠ (x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) := by
  intro C0 hM0 hRB0 hSz0 hOutLo0 hOutHi0
  by_contra hContra0
  push Not at hContra0
  let fP10 : (Fin 10 → Bool) → Bool := fun x => (x (0 : Fin (10 : ℕ)) && x (1 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (2 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (3 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (4 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (0 : Fin (10 : ℕ)) || x (0 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)) || x (1 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (2 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (3 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (4 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (5 : Fin (10 : ℕ)) && x (7 : Fin (10 : ℕ)) || x (7 : Fin (10 : ℕ)) && x (9 : Fin (10 : ℕ)) || x (9 : Fin (10 : ℕ)) && x (6 : Fin (10 : ℕ)) || x (6 : Fin (10 : ℕ)) && x (8 : Fin (10 : ℕ)) || x (8 : Fin (10 : ℕ)) && x (5 : Fin (10 : ℕ)))
  let fP9 : (Fin 9 → Bool) → Bool := fun y => (y (0 : Fin (9 : ℕ)) && y (1 : Fin (9 : ℕ)) || y (1 : Fin (9 : ℕ)) && y (2 : Fin (9 : ℕ)) || y (2 : Fin (9 : ℕ)) && y (3 : Fin (9 : ℕ)) || y (0 : Fin (9 : ℕ)) && y (5 : Fin (9 : ℕ)) || y (1 : Fin (9 : ℕ)) && y (6 : Fin (9 : ℕ)) || y (2 : Fin (9 : ℕ)) && y (7 : Fin (9 : ℕ)) || y (3 : Fin (9 : ℕ)) && y (8 : Fin (9 : ℕ)) || y (4 : Fin (9 : ℕ)) && y (6 : Fin (9 : ℕ)) || y (6 : Fin (9 : ℕ)) && y (8 : Fin (9 : ℕ)) || y (8 : Fin (9 : ℕ)) && y (5 : Fin (9 : ℕ)) || y (5 : Fin (9 : ℕ)) && y (7 : Fin (9 : ℕ)) || y (7 : Fin (9 : ℕ)) && y (4 : Fin (9 : ℕ)))
  let inp : (Fin 10 → Bool) → List Bool := fun x => List.ofFn x ++ [x 0 || x 2]
  let stepW : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let wF : List Gate → List Bool → List Bool := fun gs w => gs.foldl stepW w
  have hEvalAnd : ∀ ls : List Bool, GateOp.and.eval ls = ls.all id := fun _ => rfl
  have hEvalOr : ∀ ls : List Bool, GateOp.or.eval ls = ls.any id := fun _ => rfl
  have hGateAt : ∀ (E : Circuit) (j : ℕ), gateAt E j = E.gates.getD j ⟨GateOp.or, []⟩ := fun _ _ => rfl
  have hGateAtEq : ∀ (E : Circuit) (j : ℕ) (hj : j < E.gates.length), gateAt E j = E.gates[j] := by
    intro E j hj; rw [hGateAt, List.getD_eq_getElem E.gates _ hj]
  have hSnocLen : ∀ {α : Type} (l : List α) (a d : α) (n : ℕ), l.length = n → (l ++ [a]).getD n d = a := by
    intro α l a d n h; subst h
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (le_refl _)]
    simp
  have hLenWF : ∀ (gs : List Gate) (w : List Bool), (wF gs w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp [wF]
    | cons g gs ih =>
      intro w
      change (wF gs (stepW w g)).length = w.length + (gs.length + 1)
      rw [ih]; simp [stepW]; omega
  have hWFAppend : ∀ (gs1 gs2 : List Gate) (w : List Bool), wF (gs1 ++ gs2) w = wF gs2 (wF gs1 w) := by
    intro gs1 gs2 w; exact List.foldl_append
  have hWFLt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (wF gs w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      change (wF gs (stepW w g)).getD i false = w.getD i false
      rw [ih (stepW w g) i (by simp [stepW]; omega)]
      exact List.getD_append w _ false i hi
  -- No input wire 0..10 computes fP10
  have hNoInpEq : ∀ r < 11, ∃ x : Fin 10 → Bool, (inp x).getD r false ≠ fP10 x := by
    intro r hr
    by_cases h10 : r < 10
    · refine ⟨fun z => decide (z.val = r), ?_⟩
      interval_cases r <;> decide
    · have hr10 : r = 10 := by omega
      subst hr10
      exact ⟨fun z => decide (z = 0), by decide⟩
  -- Gate erasure lemma: deleting a redundant or dead gate decreases size by 1
  have hErase : ∀ (C : Circuit), Monotone2 C → ReadsBack 11 C →
      11 ≤ C.output → C.output < 11 + C.size →
      (∀ x : Fin 10 → Bool, C.eval (inp x) = fP10 x) →
      ∀ (d r : ℕ), d < C.gates.length → r < 11 + d →
      ((∀ x : Fin 10 → Bool, (C.wires (inp x)).getD (11 + d) false = (C.wires (inp x)).getD r false) ∨
        (C.output ≠ 11 + d ∧ ∀ j < C.gates.length, 11 + d ∉ (gateAt C j).inputs)) →
      ∃ C' : Circuit, C'.size < C.size ∧ Monotone2 C' ∧ ReadsBack 11 C' ∧
        11 ≤ C'.output ∧ C'.output < 11 + C'.size ∧
        ∀ x : Fin 10 → Bool, C'.eval (inp x) = fP10 x := by
    intro C hM hRB hOutLo hOutHi hComp d r hd hr hRepl
    let remap : ℕ → ℕ := fun w => if w < 11 + d then w else if w = 11 + d then r else w - 1
    let remapG : Gate → Gate := fun g => ⟨g.op, g.inputs.map remap⟩
    let pref : List Gate := C.gates.take d
    let gd : Gate := C.gates[d]
    let suff : List Gate := C.gates.drop (d + 1)
    have hPrefLen : pref.length = d := List.length_take_of_le (le_of_lt hd)
    have hSplit : C.gates = pref ++ (gd :: suff) := by
      have h1 := (List.take_append_drop d C.gates).symm
      have h2 : C.gates.drop d = gd :: suff := List.drop_eq_getElem_cons hd
      rw [h2] at h1; exact h1
    have hSuffLen : suff.length = C.gates.length - d - 1 := by simp [suff]; omega
    let gs' : List Gate := pref ++ suff.map remapG
    let C' : Circuit := ⟨gs', remap C.output⟩
    have hGsLen : gs'.length = C.gates.length - 1 := by
      simp only [gs', List.length_append, List.length_map, hPrefLen, hSuffLen]; omega
    have hSzLt : C'.size < C.size := by change gs'.length < C.gates.length; omega
    have hM' : Monotone2 C' := by
      intro g hg
      simp only [C', gs', List.mem_append, List.mem_map] at hg
      rcases hg with hg | ⟨g0, hg0, rfl⟩
      · exact hM g (List.mem_of_mem_take hg)
      · have hm := hM g0 (List.mem_of_mem_drop hg0)
        exact ⟨hm.1, by simp [remapG, hm.2]⟩
    have hRB' : ReadsBack 11 C' := by
      intro j hj w hw
      have hj' : j < gs'.length := hj
      rw [hGateAtEq C' j hj] at hw
      change w ∈ gs'[j].inputs at hw
      by_cases hjd : j < d
      · have hjP : j < pref.length := by omega
        have hget : gs'[j] = C.gates[j] := by
          simp only [gs', List.getElem_append_left hjP, pref, List.getElem_take]
        rw [hget] at hw
        exact hRB j (by omega) w (by rw [hGateAtEq C j (by omega)]; exact hw)
      · have hget : gs'[j] = remapG (C.gates[j + 1]'(by omega)) := by
          have hgeP : pref.length ≤ j := by omega
          dsimp only [gs']
          rw [List.getElem_append_right hgeP, List.getElem_map]
          dsimp only [suff]
          rw [List.getElem_drop]
          congr 2; omega
        rw [hget] at hw
        simp only [remapG, List.mem_map] at hw
        obtain ⟨w0, hw0, rfl⟩ := hw
        have hw0lt : w0 < 11 + (j + 1) :=
          hRB (j + 1) (by omega) w0 (by rw [hGateAtEq C (j + 1) (by omega)]; exact hw0)
        dsimp only [remap]
        split_ifs <;> omega
    have hOutHi' : C'.output < 11 + C'.size := by
      change remap C.output < 11 + gs'.length
      change C.output < 11 + C.gates.length at hOutHi
      dsimp only [remap]; split_ifs <;> omega
    have hOutLo' : 11 ≤ C'.output := by
      change 11 ≤ remap C.output
      dsimp only [remap]
      split_ifs with hlt heq
      · exact hOutLo
      · rcases hRepl with hSem | ⟨hne, _⟩
        · by_contra hlt11
          have hr11 : r < 11 := by omega
          obtain ⟨x, hx⟩ := hNoInpEq r hr11
          have h1 := hSem x
          have h2 : (C.wires (inp x)).getD r false = (inp x).getD r false :=
            hWFLt C.gates (inp x) r (by simp [inp]; omega)
          have h3 : (C.wires (inp x)).getD (11 + d) false = fP10 x := by
            rw [← heq]; exact hComp x
          rw [h3, h2] at h1
          exact hx h1.symm
        · exact absurd heq hne
      · omega
    have hEval' : ∀ x : Fin 10 → Bool, C'.eval (inp x) = fP10 x := by
      intro x
      rw [← hComp x]
      change (wF gs' (inp x)).getD (remap C.output) false = (wF C.gates (inp x)).getD C.output false
      rw [hSplit, hWFAppend pref (gd :: suff) (inp x)]
      have hEqPref : wF gs' (inp x) = wF (suff.map remapG) (wF pref (inp x)) := hWFAppend pref (suff.map remapG) (inp x)
      rw [hEqPref]
      let wP := wF pref (inp x)
      have hwPLen : wP.length = 11 + d := by
        dsimp only [wP]; rw [hLenWF]; simp [inp, hPrefLen]
      let wMid := stepW wP gd
      have hStepHead : wF (gd :: suff) wP = wF suff wMid := rfl
      rw [hStepHead]
      have hRelStep : ∀ (gs : List Gate) (wC wC' : List Bool),
          wC.length = wC'.length + 1 → 11 + d ≤ wC'.length →
          (∀ i < 11 + d, wC'.getD i false = wC.getD i false) →
          (∀ i, 11 + d ≤ i → wC'.getD i false = wC.getD (i + 1) false) →
          (wC.getD (11 + d) false = wC.getD r false ∨ ∀ g ∈ gs, 11 + d ∉ g.inputs) →
          (∀ i < 11 + d, (wF (gs.map remapG) wC').getD i false = (wF gs wC).getD i false) ∧
          (∀ i, 11 + d ≤ i → (wF (gs.map remapG) wC').getD i false = (wF gs wC).getD (i + 1) false) := by
        intro gs
        induction gs with
        | nil => intro wC wC' _ _ h1 h2 _; exact ⟨h1, h2⟩
        | cons g gs ih =>
          intro wC wC' hlen hge h1 h2 hCond
          have hgeval : (remapG g).op.eval ((remapG g).inputs.map fun w => wC'.getD w false) =
              g.op.eval (g.inputs.map fun w => wC.getD w false) := by
            dsimp only [remapG]
            congr 1
            rw [List.map_map]
            apply List.map_congr_left
            intro w hw
            dsimp only [Function.comp, remap]
            split_ifs with hlt heq
            · exact h1 w hlt
            · subst heq
              rcases hCond with hEq | hNo
              · rw [h1 r hr, ← hEq]
              · exact absurd hw (hNo g List.mem_cons_self)
            · have hle : 11 + d ≤ w - 1 := by omega
              have := h2 (w - 1) hle
              rwa [show w - 1 + 1 = w by omega] at this
          change (∀ i < 11 + d, (wF (gs.map remapG) (stepW wC' (remapG g))).getD i false = (wF gs (stepW wC g)).getD i false) ∧
            (∀ i, 11 + d ≤ i → (wF (gs.map remapG) (stepW wC' (remapG g))).getD i false = (wF gs (stepW wC g)).getD (i + 1) false)
          apply ih (stepW wC g) (stepW wC' (remapG g)) (by simp [stepW, hlen]) (by simp [stepW]; omega)
          · intro i hi
            rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
            exact h1 i hi
          · intro i hi
            by_cases hlt : i < wC'.length
            · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
              exact h2 i hi
            · by_cases heq : i = wC'.length
              · subst heq
                rw [hSnocLen _ _ _ _ rfl, hSnocLen _ _ _ _ hlen, hgeval]
              · rw [List.getD_eq_default _ _ (by simp [stepW]; omega), List.getD_eq_default _ _ (by simp [stepW]; omega)]
          · rcases hCond with hEq | hNo
            · left
              rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
              exact hEq
            · right; exact fun g' hg' => hNo g' (List.mem_cons_of_mem _ hg')
      have hCondMid : wMid.getD (11 + d) false = wMid.getD r false ∨ ∀ g ∈ suff, 11 + d ∉ g.inputs := by
        rcases hRepl with hSem | ⟨_, hNo⟩
        · left
          have h1 : (wF suff wMid).getD (11 + d) false = wMid.getD (11 + d) false :=
            hWFLt suff wMid (11 + d) (by simp [wMid, stepW, hwPLen])
          have h2 : (wF suff wMid).getD r false = wMid.getD r false :=
            hWFLt suff wMid r (by simp [wMid, stepW, hwPLen]; omega)
          have hW : wF suff wMid = C.wires (inp x) := by
            change wF suff (stepW (wF pref (inp x)) gd) = wF C.gates (inp x)
            rw [hSplit, hWFAppend pref (gd :: suff) (inp x)]; rfl
          rw [← h1, ← h2, hW]; exact hSem x
        · right
          intro g hg
          obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hg
          have hkC : d + 1 + k < C.gates.length := by omega
          have hge : suff[k] = C.gates[d + 1 + k] := List.getElem_drop
          rw [hge, ← hGateAtEq C (d + 1 + k) hkC]
          exact hNo (d + 1 + k) hkC
      have hMid1 : ∀ i < 11 + d, wP.getD i false = wMid.getD i false := by
        intro i hi; exact (List.getD_append wP _ false i (by omega)).symm
      have hMid2 : ∀ i, 11 + d ≤ i → wP.getD i false = wMid.getD (i + 1) false := by
        intro i hi
        rw [List.getD_eq_default wP false (by omega), List.getD_eq_default wMid false (by simp [wMid, stepW, hwPLen]; omega)]
      obtain ⟨hFin1, hFin2⟩ := hRelStep suff wMid wP (by simp [wMid, stepW]) (by omega) hMid1 hMid2 hCondMid
      dsimp only [remap]
      split_ifs with hlt heq
      · exact hFin1 C.output hlt
      · rcases hRepl with hSem | ⟨hne, _⟩
        · rw [hFin1 r hr]
          have hW : wF suff wMid = C.wires (inp x) := by
            change wF suff (stepW (wF pref (inp x)) gd) = wF C.gates (inp x)
            rw [hSplit, hWFAppend pref (gd :: suff) (inp x)]; rfl
          rw [hW, heq]; exact (hSem x).symm
        · exact absurd heq hne
      · have hle : 11 + d ≤ C.output - 1 := by omega
        have := hFin2 (C.output - 1) hle
        rwa [show C.output - 1 + 1 = C.output by omega] at this
    exact ⟨C', hSzLt, hM', hRB', hOutLo', hOutHi', hEval'⟩
  -- Pick a minimum-size counterexample C
  let Good : ℕ → Prop := fun s => ∃ C : Circuit, C.size = s ∧ Monotone2 C ∧ ReadsBack 11 C ∧
    11 ≤ C.output ∧ C.output < 11 + C.size ∧ ∀ x : Fin 10 → Bool, C.eval (inp x) = fP10 x
  have hExGood : ∃ s, Good s := ⟨C0.size, C0, rfl, hM0, hRB0, hOutLo0, hOutHi0, hContra0⟩
  classical
  let sMin := Nat.find hExGood
  have hsMinLe : sMin ≤ 18 := le_trans (Nat.find_min' hExGood ⟨C0, rfl, hM0, hRB0, hOutLo0, hOutHi0, hContra0⟩) hSz0
  obtain ⟨C, hCs, hM, hRB, hOutLo, hOutHi, hComp⟩ := Nat.find_spec hExGood
  have hSz : C.size ≤ 18 := by omega
  have hMin : ∀ C' : Circuit, C'.size < C.size → Monotone2 C' → ReadsBack 11 C' →
      11 ≤ C'.output → C'.output < 11 + C'.size → ¬ (∀ x : Fin 10 → Bool, C'.eval (inp x) = fP10 x) := by
    intro C' hlt hM' hRB' hLo' hHi' hComp'
    exact Nat.find_min hExGood (by omega) ⟨C', rfl, hM', hRB', hLo', hHi', hComp'⟩
  -- Minimality consequences for C: no dead gates, count <= 1, readsIn = card, no absorption
  have hNoDead : ∀ d < C.gates.length, C.output = 11 + d ∨ ∃ j < C.gates.length, 11 + d ∈ (gateAt C j).inputs := by
    intro d hd
    by_contra h
    push Not at h
    obtain ⟨C', h1, h2, h3, h4, h5, h6⟩ := hErase C hM hRB hOutLo hOutHi hComp d 0 hd (by omega) (Or.inr h)
    exact hMin C' h1 h2 h3 h4 h5 h6
  have hCountLe1 : ∀ d < C.gates.length, ∀ w : ℕ, (gateAt C d).inputs.count w ≤ 1 := by
    intro d hd w
    have hMd := hM (gateAt C d) (by rw [hGateAtEq C d hd]; exact List.getElem_mem hd)
    rcases hins : (gateAt C d).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
    · simp
    · simp only [List.count_cons, List.count_nil, beq_iff_eq]; split_ifs <;> omega
    · by_cases hab : a = b
      · subst hab
        exfalso
        have haLt : a < 11 + d := hRB d hd a (by rw [hins]; simp)
        have hSem : ∀ x : Fin 10 → Bool, (C.wires (inp x)).getD (11 + d) false = (C.wires (inp x)).getD a false := by
          intro x
          have hSplit : C.gates = C.gates.take d ++ (C.gates[d] :: C.gates.drop (d + 1)) := by
            have h1 := (List.take_append_drop d C.gates).symm
            rw [List.drop_eq_getElem_cons hd] at h1; exact h1
          have hPrefLen : (C.gates.take d).length = d := List.length_take_of_le (le_of_lt hd)
          let wP := wF (C.gates.take d) (inp x)
          have hwPLen : wP.length = 11 + d := by dsimp only [wP]; rw [hLenWF]; simp [inp, hPrefLen]
          have hW : C.wires (inp x) = wF (C.gates.drop (d + 1)) (stepW wP C.gates[d]) := by
            change wF C.gates (inp x) = _
            conv_lhs => rw [hSplit]
            rw [hWFAppend]; rfl
          rw [hW, hWFLt _ _ (11 + d) (by simp [stepW, hwPLen]), hWFLt _ _ a (by simp [stepW, hwPLen]; omega)]
          rw [hSnocLen _ _ _ _ hwPLen, List.getD_append _ _ _ _ (by omega)]
          rw [← hGateAtEq C d hd, hins]
          rcases hMd.1 with hop | hop
          · rw [hop, hEvalAnd]; simp
          · rw [hop, hEvalOr]; simp
        obtain ⟨C', h1, h2, h3, h4, h5, h6⟩ := hErase C hM hRB hOutLo hOutHi hComp d a hd haLt (Or.inl hSem)
        exact hMin C' h1 h2 h3 h4 h5 h6
      · simp only [List.count_cons, List.count_nil, beq_iff_eq]
        split_ifs <;> omega
    · have := hMd.2; rw [hins] at this; simp at this
  have hReadsEqCard : ∀ w : ℕ,
      readsIn C (Finset.range C.size) w = ((Finset.range C.size).filter (fun k => w ∈ (gateAt C k).inputs)).card := by
    intro w
    dsimp only [readsIn]
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro k hk
    have hkLt : k < C.gates.length := Finset.mem_range.1 hk
    have hle := hCountLe1 k hkLt w
    by_cases hmem : w ∈ (gateAt C k).inputs
    · have hpos : 0 < (gateAt C k).inputs.count w := List.count_pos_iff.2 hmem
      simp [hmem]; omega
    · have h0 : (gateAt C k).inputs.count w = 0 := List.count_eq_zero.2 hmem
      simp [hmem, h0]
  have hNoAbsorb : ∀ (i j u : ℕ), i < C.gates.length → j < C.gates.length → u < 11 →
      (gateAt C i).op = GateOp.and → (gateAt C j).op = GateOp.or →
      u ∈ (gateAt C i).inputs → 11 + i ∈ (gateAt C j).inputs → u ∉ (gateAt C j).inputs := by
    intro i j u hi hj hu hopI hopJ hui hij huj
    have hMj := hM (gateAt C j) (by rw [hGateAtEq C j hj]; exact List.getElem_mem hj)
    have hSem : ∀ x : Fin 10 → Bool, (C.wires (inp x)).getD (11 + j) false = (C.wires (inp x)).getD u false := by
      intro x
      have hGetGate : ∀ (k : ℕ) (hk : k < C.gates.length),
          (C.wires (inp x)).getD (11 + k) false =
            (gateAt C k).op.eval ((gateAt C k).inputs.map fun w => (C.wires (inp x)).getD w false) := by
        intro k hk
        have hSplit : C.gates = C.gates.take k ++ (C.gates[k] :: C.gates.drop (k + 1)) := by
          have h1 := (List.take_append_drop k C.gates).symm
          rw [List.drop_eq_getElem_cons hk] at h1; exact h1
        have hPrefLen : (C.gates.take k).length = k := List.length_take_of_le (le_of_lt hk)
        let wP := wF (C.gates.take k) (inp x)
        have hwPLen : wP.length = 11 + k := by dsimp only [wP]; rw [hLenWF]; simp [inp, hPrefLen]
        have hW : C.wires (inp x) = wF (C.gates.drop (k + 1)) (stepW wP C.gates[k]) := by
          change wF C.gates (inp x) = _
          conv_lhs => rw [hSplit]
          rw [hWFAppend]; rfl
        rw [hW, hWFLt _ _ (11 + k) (by simp [stepW, hwPLen]), hSnocLen _ _ _ _ hwPLen, ← hGateAtEq C k hk]
        congr 1
        apply List.map_congr_left
        intro w hw
        have hwLt : w < 11 + k := hRB k hk w hw
        rw [hWFLt (C.gates.drop (k + 1)) (stepW wP (gateAt C k)) w (by simp [stepW, hwPLen]; omega)]
        exact (List.getD_append wP _ false w (by omega)).symm
      have hVi := hGetGate i hi
      have hVj := hGetGate j hj
      rw [hopI, hEvalAnd] at hVi
      rw [hopJ, hEvalOr] at hVj
      have hImp : (C.wires (inp x)).getD (11 + i) false = true → (C.wires (inp x)).getD u false = true := by
        intro hT
        rw [hVi, List.all_eq_true] at hT
        exact hT ((C.wires (inp x)).getD u false) (List.mem_map_of_mem hui)
      rcases hinsJ : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · rw [hinsJ] at huj; simp at huj
      · rw [hinsJ] at huj hij; simp at huj hij; omega
      · rw [hinsJ] at huj hij hVj
        simp only [List.mem_cons, List.not_mem_nil, or_false] at huj hij
        simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false] at hVj
        rcases huj with rfl | rfl <;> rcases hij with h1 | h1
        · omega
        · rw [hVj, ← h1]
          cases hvu : (C.wires (inp x)).getD u false <;> cases hvi : (C.wires (inp x)).getD (11 + i) false
          · rfl
          · have := hImp hvi; rw [hvu] at this; exact Bool.noConfusion this
          · rfl
          · rfl
        · rw [hVj, ← h1]
          cases hvu : (C.wires (inp x)).getD u false <;> cases hvi : (C.wires (inp x)).getD (11 + i) false
          · rfl
          · have := hImp hvi; rw [hvu] at this; exact Bool.noConfusion this
          · rfl
          · rfl
        · omega
      · have := hMj.2; rw [hinsJ] at this; simp at this
    obtain ⟨C', h1, h2, h3, h4, h5, h6⟩ := hErase C hM hRB hOutLo hOutHi hComp j u hj (by omega) (Or.inl hSem)
    exact hMin C' h1 h2 h3 h4 h5 h6
  -- Symbolic gate elimination via List.foldl (SVal := Option (Option Nat): none=cF, some none=cT, some (some k)=wr k)
  let evalS : List Bool → Option (Option ℕ) → Bool := fun w v =>
    Option.casesOn v false (fun o => Option.casesOn o true (fun k => w.getD k false))
  let stepAnd2 : List (Option (Option ℕ)) → List Gate → Option (Option ℕ) → Option (Option ℕ) →
      List (Option (Option ℕ)) × List Gate × Bool := fun env em va vb =>
    Option.casesOn va (env ++ [none], em, true) (fun oa =>
      Option.casesOn oa
        (Option.casesOn vb (env ++ [none], em, true) (fun _ => (env ++ [vb], em, true)))
        (fun u =>
          Option.casesOn vb (env ++ [none], em, true) (fun ob =>
            Option.casesOn ob (env ++ [va], em, true)
              (fun v => (env ++ [some (some (9 + em.length))], em ++ [⟨.and, [u, v]⟩], false)))))
  let stepOr2 : List (Option (Option ℕ)) → List Gate → Option (Option ℕ) → Option (Option ℕ) →
      List (Option (Option ℕ)) × List Gate × Bool := fun env em va vb =>
    Option.casesOn va
      (Option.casesOn vb (env ++ [none], em, true) (fun _ => (env ++ [vb], em, true)))
      (fun oa =>
        Option.casesOn oa (env ++ [some none], em, true)
          (fun u =>
            Option.casesOn vb (env ++ [va], em, true) (fun ob =>
              Option.casesOn ob (env ++ [some none], em, true)
                (fun v => (env ++ [some (some (9 + em.length))], em ++ [⟨.or, [u, v]⟩], false)))))
  let stepRed : List (Option (Option ℕ)) → List Gate → Gate →
      List (Option (Option ℕ)) × List Gate × Bool := fun env em g =>
    GateOp.casesOn g.op
      (List.casesOn g.inputs (env ++ [some none], em, true) (fun a l =>
        List.casesOn l (env ++ [env.getD a none], em, true) (fun b _ =>
          stepAnd2 env em (env.getD a none) (env.getD b none))))
      (List.casesOn g.inputs (env ++ [none], em, true) (fun a l =>
        List.casesOn l (env ++ [env.getD a none], em, true) (fun b _ =>
          stepOr2 env em (env.getD a none) (env.getD b none))))
      (env ++ [none], em, true)
      (fun _ => (env ++ [none], em, true))
      (env ++ [none], em, true)
  let stepFold : ℕ × List (Option (Option ℕ)) × List Gate × List ℕ → Gate →
      ℕ × List (Option (Option ℕ)) × List Gate × List ℕ := fun st g =>
    let r := stepRed st.2.1 st.2.2.1 g
    (st.1 + 1, r.1, r.2.1, if r.2.2 then st.1 :: st.2.2.2 else st.2.2.2)
  have hEvalSApp : ∀ (w extra : List Bool) (v : Option (Option ℕ)),
      (∀ k, v = some (some k) → k < w.length) → evalS (w ++ extra) v = evalS w v := by
    intro w extra v hv
    rcases v with _ | (_ | k)
    · rfl
    · rfl
    · exact List.getD_append w extra false k (hv k rfl)
  have hMkDrop : ∀ (env : List (Option (Option ℕ))) (em : List Gate) (g : Gate) (v : Option (Option ℕ)),
      (∀ i < env.length, ∀ k, env.getD i none = some (some k) → k < 9 + em.length) →
      (∀ k, v = some (some k) → k < 9 + em.length) →
      (∀ (origW y9 : List Bool), origW.length = env.length → y9.length = 9 →
        (∀ i < env.length, origW.getD i false = evalS (wF em y9) (env.getD i none)) →
        g.op.eval (g.inputs.map fun w => origW.getD w false) = evalS (wF em y9) v) →
      (∀ a ∈ g.inputs, env.getD a none = none → g.op = GateOp.and → v = none) →
      let r : List (Option (Option ℕ)) × List Gate × Bool := (env ++ [v], em, true)
      r.1.length = env.length + 1 ∧
      (∀ i < env.length, r.1.getD i none = env.getD i none) ∧
      (∀ g' ∈ r.2.1, g' ∈ em ∨ ((g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2)) ∧
      r.2.1.length + (if r.2.2 then 1 else 0) = em.length + 1 ∧
      (∀ i < r.1.length, ∀ k, r.1.getD i none = some (some k) → k < 9 + r.2.1.length) ∧
      (∀ (origW y9 : List Bool), origW.length = env.length → y9.length = 9 →
        (∀ i < env.length, origW.getD i false = evalS (wF em y9) (env.getD i none)) →
        ∀ i < r.1.length, (stepW origW g).getD i false = evalS (wF r.2.1 y9) (r.1.getD i none)) ∧
      (∀ a ∈ g.inputs, env.getD a none = none → r.2.2 = true ∧ (g.op = GateOp.and → r.1.getD env.length none = none)) := by
    intro env em g v hW hWv hEvv hCF
    refine ⟨by simp, fun i hi => List.getD_append env [v] none i hi, fun g' hg' => Or.inl hg', by simp, ?_, ?_, ?_⟩
    · intro i hi k hk
      by_cases hlt : i < env.length
      · rw [List.getD_append env [v] none i hlt] at hk; exact hW i hlt k hk
      · have heq : i = env.length := by simp at hi; omega
        subst heq; rw [hSnocLen _ _ _ _ rfl] at hk; exact hWv k hk
    · intro origW y9 hO hY hAg i hi
      by_cases hlt : i < env.length
      · rw [List.getD_append _ _ _ _ (by omega), hAg i hlt, List.getD_append env [v] none i hlt]
      · have heq : i = env.length := by simp at hi; omega
        subst heq; rw [hSnocLen _ _ _ _ hO, hSnocLen _ _ _ _ rfl]
        exact hEvv origW y9 hO hY hAg
    · intro a ha hcf
      refine ⟨rfl, fun hop => ?_⟩
      rw [hSnocLen _ _ _ _ rfl]
      exact hCF a ha hcf hop
  have hMkEmit : ∀ (env : List (Option (Option ℕ))) (em : List Gate) (op : GateOp) (a b u v : ℕ),
      (op = GateOp.and ∨ op = GateOp.or) →
      a < env.length → b < env.length →
      env.getD a none = some (some u) → env.getD b none = some (some v) →
      (∀ i < env.length, ∀ k, env.getD i none = some (some k) → k < 9 + em.length) →
      let r : List (Option (Option ℕ)) × List Gate × Bool :=
        (env ++ [some (some (9 + em.length))], em ++ [⟨op, [u, v]⟩], false)
      r.1.length = env.length + 1 ∧
      (∀ i < env.length, r.1.getD i none = env.getD i none) ∧
      (∀ g' ∈ r.2.1, g' ∈ em ∨ ((g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2)) ∧
      r.2.1.length + (if r.2.2 then 1 else 0) = em.length + 1 ∧
      (∀ i < r.1.length, ∀ k, r.1.getD i none = some (some k) → k < 9 + r.2.1.length) ∧
      (∀ (origW y9 : List Bool), origW.length = env.length → y9.length = 9 →
        (∀ i < env.length, origW.getD i false = evalS (wF em y9) (env.getD i none)) →
        ∀ i < r.1.length, (stepW origW ⟨op, [a, b]⟩).getD i false = evalS (wF r.2.1 y9) (r.1.getD i none)) ∧
      (∀ x ∈ ([a, b] : List ℕ), env.getD x none = none → r.2.2 = true ∧ (op = GateOp.and → r.1.getD env.length none = none)) := by
    intro env em op a b u v hop ha hb hva hvb hW
    refine ⟨by simp, fun i hi => List.getD_append env _ none i hi, ?_, by simp, ?_, ?_, ?_⟩
    · intro g' hg'
      simp only [List.mem_append, List.mem_singleton] at hg'
      rcases hg' with hg' | rfl
      · exact Or.inl hg'
      · exact Or.inr ⟨hop, by simp⟩
    · intro i hi k hk
      by_cases hlt : i < env.length
      · rw [List.getD_append env _ none i hlt] at hk
        have := hW i hlt k hk; simp; omega
      · have heq : i = env.length := by simp at hi; omega
        subst heq; rw [hSnocLen _ _ _ _ rfl] at hk
        injection hk with hk; injection hk with hk; simp; omega
    · intro origW y9 hO hY hAg i hi
      have hwem : wF (em ++ [⟨op, [u, v]⟩]) y9 = stepW (wF em y9) ⟨op, [u, v]⟩ := by
        rw [hWFAppend]; rfl
      have hlenW : (wF em y9).length = 9 + em.length := by rw [hLenWF, hY]
      by_cases hlt : i < env.length
      · rw [List.getD_append _ _ _ _ (by omega), hAg i hlt, List.getD_append env _ none i hlt, hwem]
        exact (hEvalSApp _ _ _ fun k hk => by rw [hlenW]; exact hW i hlt k hk).symm
      · have heq : i = env.length := by simp at hi; omega
        subst heq; rw [hSnocLen _ _ _ _ hO, hSnocLen _ _ _ _ rfl, hwem]
        dsimp only [evalS]
        rw [hSnocLen _ _ _ _ hlenW]
        have h1 := hAg a ha; rw [hva] at h1
        have h2 := hAg b hb; rw [hvb] at h2
        simp only [List.map_cons, List.map_nil, h1, h2, evalS]
    · intro x hx hcf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · rw [hva] at hcf; cases hcf
      · rw [hvb] at hcf; cases hcf
  have hStepRed : ∀ (env : List (Option (Option ℕ))) (em : List Gate) (g : Gate),
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      (∀ w ∈ g.inputs, w < env.length) →
      (∀ i < env.length, ∀ k, env.getD i none = some (some k) → k < 9 + em.length) →
      let r := stepRed env em g
      r.1.length = env.length + 1 ∧
      (∀ i < env.length, r.1.getD i none = env.getD i none) ∧
      (∀ g' ∈ r.2.1, g' ∈ em ∨ ((g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2)) ∧
      r.2.1.length + (if r.2.2 then 1 else 0) = em.length + 1 ∧
      (∀ i < r.1.length, ∀ k, r.1.getD i none = some (some k) → k < 9 + r.2.1.length) ∧
      (∀ (origW y9 : List Bool), origW.length = env.length → y9.length = 9 →
        (∀ i < env.length, origW.getD i false = evalS (wF em y9) (env.getD i none)) →
        ∀ i < r.1.length, (stepW origW g).getD i false = evalS (wF r.2.1 y9) (r.1.getD i none)) ∧
      (∀ a ∈ g.inputs, env.getD a none = none → r.2.2 = true ∧ (g.op = GateOp.and → r.1.getD env.length none = none)) := by
    intro env em g hMg hBg hW
    rcases g with ⟨op, ins⟩
    obtain ⟨hop, hlen⟩ := hMg
    dsimp only at hop hlen hBg
    rcases hop with rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · exact hMkDrop env em ⟨.and, []⟩ (some none) hW (by intro k hk; cases hk)
          (fun _ _ _ _ _ => rfl) (fun _ h => by simp at h)
      · exact hMkDrop env em ⟨.and, [a]⟩ (env.getD a none) hW (hW a (hBg a (by simp)))
          (fun origW y9 _ _ hAg => by
            have h1 := hAg a (hBg a (by simp))
            rw [hEvalAnd]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, h1])
          (fun x hx hcf _ => by
            have hx' : x = a := by simpa using hx
            rw [← hx']; exact hcf)
      · have ha : a < env.length := hBg a (by simp)
        have hb : b < env.length := hBg b (by simp)
        dsimp only [stepRed]
        rcases hva : env.getD a none with _ | (_ | u)
        · exact hMkDrop env em ⟨.and, [a, b]⟩ none hW (by intro k hk; cases hk)
            (fun origW y9 _ _ hAg => by
              have h1 := hAg a ha; rw [hva] at h1
              rw [hEvalAnd]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, h1, evalS, Bool.false_and])
            (fun _ _ _ _ => rfl)
        · rcases hvb : env.getD b none with _ | (_ | v)
          · exact hMkDrop env em ⟨.and, [a, b]⟩ none hW (by intro k hk; cases hk)
              (fun origW y9 _ _ hAg => by
                have h2 := hAg b hb; rw [hvb] at h2
                rw [hEvalAnd]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, h2, evalS, Bool.false_and, Bool.and_false])
              (fun _ _ _ _ => rfl)
          · exact hMkDrop env em ⟨.and, [a, b]⟩ (some none) hW (by intro k hk; cases hk)
              (fun origW y9 _ _ hAg => by
                have h1 := hAg a ha; rw [hva] at h1; have h2 := hAg b hb; rw [hvb] at h2
                rw [hEvalAnd]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, h1, h2, evalS, Bool.and_true])
              (fun x hx hcf _ => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                rcases hx with rfl | rfl
                · rw [hva] at hcf; cases hcf
                · rw [hvb] at hcf; cases hcf)
          · exact hMkDrop env em ⟨.and, [a, b]⟩ (some (some v)) hW (fun k hk => hW b hb k (hvb.trans hk))
              (fun origW y9 _ _ hAg => by
                have h1 := hAg a ha; rw [hva] at h1; have h2 := hAg b hb; rw [hvb] at h2
                rw [hEvalAnd]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, h1, h2, evalS, Bool.true_and, Bool.and_true])
              (fun x hx hcf _ => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                rcases hx with rfl | rfl
                · rw [hva] at hcf; cases hcf
                · rw [hvb] at hcf; cases hcf)
        · rcases hvb : env.getD b none with _ | (_ | v)
          · exact hMkDrop env em ⟨.and, [a, b]⟩ none hW (by intro k hk; cases hk)
              (fun origW y9 _ _ hAg => by
                have h2 := hAg b hb; rw [hvb] at h2
                rw [hEvalAnd]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, h2, evalS, Bool.false_and, Bool.and_false])
              (fun _ _ _ _ => rfl)
          · exact hMkDrop env em ⟨.and, [a, b]⟩ (some (some u)) hW (fun k hk => hW a ha k (hva.trans hk))
              (fun origW y9 _ _ hAg => by
                have h1 := hAg a ha; rw [hva] at h1; have h2 := hAg b hb; rw [hvb] at h2
                rw [hEvalAnd]; simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, h1, h2, evalS, Bool.and_true])
              (fun x hx hcf _ => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                rcases hx with rfl | rfl
                · rw [hva] at hcf; cases hcf
                · rw [hvb] at hcf; cases hcf)
          · exact hMkEmit env em .and a b u v (Or.inl rfl) ha hb hva hvb hW
      · simp at hlen
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩
      · exact hMkDrop env em ⟨.or, []⟩ none hW (by intro k hk; cases hk)
          (fun _ _ _ _ _ => rfl) (fun _ h => by simp at h)
      · exact hMkDrop env em ⟨.or, [a]⟩ (env.getD a none) hW (hW a (hBg a (by simp)))
          (fun origW y9 _ _ hAg => by
            have h1 := hAg a (hBg a (by simp))
            rw [hEvalOr]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, h1])
          (fun _ _ _ hop => by cases hop)
      · have ha : a < env.length := hBg a (by simp)
        have hb : b < env.length := hBg b (by simp)
        dsimp only [stepRed]
        rcases hva : env.getD a none with _ | (_ | u)
        · rcases hvb : env.getD b none with _ | (_ | v)
          · exact hMkDrop env em ⟨.or, [a, b]⟩ none hW (by intro k hk; cases hk)
              (fun origW y9 _ _ hAg => by
                have h1 := hAg a ha; rw [hva] at h1; have h2 := hAg b hb; rw [hvb] at h2
                rw [hEvalOr]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, h1, h2, evalS, Bool.or_false])
              (fun _ _ _ hop => by cases hop)
          · exact hMkDrop env em ⟨.or, [a, b]⟩ (some none) hW (by intro k hk; cases hk)
              (fun origW y9 _ _ hAg => by
                have h2 := hAg b hb; rw [hvb] at h2
                rw [hEvalOr]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, h2, evalS, Bool.true_or, Bool.or_true])
              (fun _ _ _ hop => by cases hop)
          · exact hMkDrop env em ⟨.or, [a, b]⟩ (some (some v)) hW (fun k hk => hW b hb k (hvb.trans hk))
              (fun origW y9 _ _ hAg => by
                have h1 := hAg a ha; rw [hva] at h1; have h2 := hAg b hb; rw [hvb] at h2
                rw [hEvalOr]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, h1, h2, evalS, Bool.false_or, Bool.or_false])
              (fun _ _ _ hop => by cases hop)
        · exact hMkDrop env em ⟨.or, [a, b]⟩ (some none) hW (by intro k hk; cases hk)
            (fun origW y9 _ _ hAg => by
              have h1 := hAg a ha; rw [hva] at h1
              rw [hEvalOr]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, h1, evalS, Bool.true_or])
            (fun _ _ _ hop => by cases hop)
        · rcases hvb : env.getD b none with _ | (_ | v)
          · exact hMkDrop env em ⟨.or, [a, b]⟩ (some (some u)) hW (fun k hk => hW a ha k (hva.trans hk))
              (fun origW y9 _ _ hAg => by
                have h1 := hAg a ha; rw [hva] at h1; have h2 := hAg b hb; rw [hvb] at h2
                rw [hEvalOr]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, h1, h2, evalS, Bool.or_false])
              (fun _ _ _ hop => by cases hop)
          · exact hMkDrop env em ⟨.or, [a, b]⟩ (some none) hW (by intro k hk; cases hk)
              (fun origW y9 _ _ hAg => by
                have h2 := hAg b hb; rw [hvb] at h2
                rw [hEvalOr]; simp only [List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, h2, evalS, Bool.true_or, Bool.or_true])
              (fun _ _ _ hop => by cases hop)
          · exact hMkEmit env em .or a b u v (Or.inr rfl) ha hb hva hvb hW
      · simp at hlen
  have hRedFold : ∀ (gs : List Gate) (idx : ℕ) (env : List (Option (Option ℕ))) (em : List Gate) (dr : List ℕ),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      (∀ t, ∀ ht : t < gs.length, ∀ w ∈ gs[t].inputs, w < env.length + t) →
      (∀ g ∈ em, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      (∀ i < env.length, ∀ k, env.getD i none = some (some k) → k < 9 + em.length) →
      (∀ x ∈ dr, x < idx) → dr.Nodup →
      let res := gs.foldl stepFold (idx, env, em, dr)
      res.2.1.length = env.length + gs.length ∧
      (∀ i < env.length, res.2.1.getD i none = env.getD i none) ∧
      (∀ g ∈ res.2.2.1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      res.2.2.1.length + res.2.2.2.length = em.length + dr.length + gs.length ∧
      res.2.2.2.Nodup ∧
      (∀ x ∈ dr, x ∈ res.2.2.2) ∧
      (∀ (origW y9 : List Bool), origW.length = env.length → y9.length = 9 →
        (∀ i < env.length, origW.getD i false = evalS (wF em y9) (env.getD i none)) →
        ∀ i < res.2.1.length, (wF gs origW).getD i false = evalS (wF res.2.2.1 y9) (res.2.1.getD i none)) ∧
      (∀ t, ∀ ht : t < gs.length, ∀ a ∈ gs[t].inputs, res.2.1.getD a none = none →
        (idx + t) ∈ res.2.2.2 ∧ (gs[t].op = GateOp.and → res.2.1.getD (env.length + t) none = none)) := by
    intro gs
    induction gs with
    | nil =>
      intro idx env em dr _ _ hEm _ _ hNd
      refine ⟨by simp, fun _ _ => rfl, hEm, by simp, hNd, fun _ h => h, ?_, ?_⟩
      · intro origW y9 _ _ hAg i hi; exact hAg i hi
      · intro t ht; simp at ht
    | cons g gs ih =>
      intro idx env em dr hMg hBg hEm hW hDrLt hNd
      have hM1 := hMg g List.mem_cons_self
      have hMgs := fun g' hg' => hMg g' (List.mem_cons_of_mem _ hg')
      have hB1 : ∀ w ∈ g.inputs, w < env.length := fun w hw => hBg 0 (by simp) w hw
      obtain ⟨hL1, hExt1, hEm1, hSz1, hW1, hEv1, hDr1⟩ := hStepRed env em g hM1 hB1 hW
      set r := stepRed env em g
      have hEm' : ∀ g' ∈ r.2.1, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
        fun g' hg' => (hEm1 g' hg').elim (hEm g') id
      have hBgs : ∀ t, ∀ ht : t < gs.length, ∀ w ∈ gs[t].inputs, w < r.1.length + t := by
        intro t ht w hw
        have := hBg (t + 1) (by simp; omega) w hw
        rw [hL1]; omega
      let dr' := if r.2.2 then idx :: dr else dr
      have hDrLt' : ∀ x ∈ dr', x < idx + 1 := by
        intro x hx; dsimp only [dr'] at hx; split_ifs at hx
        · rcases List.mem_cons.1 hx with rfl | hx
          · omega
          · have := hDrLt x hx; omega
        · have := hDrLt x hx; omega
      have hNd' : dr'.Nodup := by
        dsimp only [dr']; split_ifs
        · exact List.nodup_cons.2 ⟨fun h => by have := hDrLt idx h; omega, hNd⟩
        · exact hNd
      have hDrLen' : dr'.length = dr.length + (if r.2.2 then 1 else 0) := by
        dsimp only [dr']; split_ifs <;> simp
      obtain ⟨hL2, hExt2, hEm2, hSz2, hNd2, hSub2, hEv2, hDr2⟩ :=
        ih (idx + 1) r.1 r.2.1 dr' hMgs hBgs hEm' hW1 hDrLt' hNd'
      refine ⟨?_, ?_, hEm2, ?_, hNd2, ?_, ?_, ?_⟩
      · change (gs.foldl stepFold (idx + 1, r.1, r.2.1, dr')).2.1.length = env.length + (gs.length + 1)
        rw [hL2, hL1]; omega
      · intro i hi
        change (gs.foldl stepFold (idx + 1, r.1, r.2.1, dr')).2.1.getD i none = env.getD i none
        rw [hExt2 i (by rw [hL1]; omega), hExt1 i hi]
      · change (gs.foldl stepFold (idx + 1, r.1, r.2.1, dr')).2.2.1.length +
            (gs.foldl stepFold (idx + 1, r.1, r.2.1, dr')).2.2.2.length = _
        rw [hSz2, hDrLen']; simp only [List.length_cons]; omega
      · intro x hx
        apply hSub2; dsimp only [dr']; split_ifs
        · exact List.mem_cons_of_mem _ hx
        · exact hx
      · intro origW y9 hO hY hAg i hi
        change (wF gs (stepW origW g)).getD i false = _
        exact hEv2 _ y9 (by simp [stepW, hO, hL1]) hY (hEv1 origW y9 hO hY hAg) i hi
      · intro t ht a ha hcf
        cases t with
        | zero =>
          simp only [List.getElem_cons_zero, Nat.add_zero] at ha hcf ⊢
          have halt : a < env.length := hB1 a ha
          have hcf0 : env.getD a none = none := by
            have := hExt2 a (by rw [hL1]; omega)
            rw [hExt1 a halt] at this
            exact this.symm.trans hcf
          obtain ⟨hflag, hand⟩ := hDr1 a ha hcf0
          refine ⟨?_, fun hop => ?_⟩
          · apply hSub2; simp [dr', hflag]
          · have := hExt2 env.length (by rw [hL1]; omega)
            change (gs.foldl stepFold (idx + 1, r.1, r.2.1, dr')).2.1.getD env.length none = none
            rw [this, hand hop]
        | succ t' =>
          have ht' : t' < gs.length := by simp at ht; omega
          have hstep := hDr2 t' ht' a ha hcf
          rw [show idx + (t' + 1) = (idx + 1) + t' by omega, show env.length + (t' + 1) = r.1.length + t' by rw [hL1]; omega]
          exact hstep
  -- Classification lemma for wire u in {0, 2} via h_p9
  have hClassify : ∀ (u : ℕ) (env0 : List (Option (Option ℕ))) (embed : (Fin 9 → Bool) → (Fin 10 → Bool)),
      u < 11 → env0.length = 11 →
      (∀ i < 11, ∀ k, env0.getD i none = some (some k) → k < 9) →
      env0.getD u none = none →
      (∀ (y : Fin 9 → Bool) (i : ℕ), i < 11 → (inp (embed y)).getD i false = evalS (List.ofFn y) (env0.getD i none)) →
      (∀ y : Fin 9 → Bool, fP10 (embed y) = fP9 y) →
      (∃ j < C.gates.length, u ∈ (gateAt C j).inputs) →
      (∃ i j : ℕ, isAnd C i ∧ isOr C j ∧ u ∈ (gateAt C i).inputs ∧ 11 + i ∈ (gateAt C j).inputs ∧
        readsIn C (Finset.range C.size) u = 1 ∧ readsIn C (Finset.range C.size) (11 + i) = 1) ∨
      (1 ≤ readsIn C (Finset.range C.size) u ∧ readsIn C (Finset.range C.size) u ≤ 2 ∧
        ∀ k < C.size, u ∈ (gateAt C k).inputs → isOr C k) := by
    intro u env0 embed hu hEnvLen hEnvW hEnvU hEnvAg hP9eq hExU
    have hM' : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
      fun g hg => ⟨by simpa using (hM g hg).1, (hM g hg).2⟩
    have hB' : ∀ t, ∀ ht : t < C.gates.length, ∀ w ∈ C.gates[t].inputs, w < env0.length + t := by
      intro t ht w hw; rw [hEnvLen]; exact hRB t ht w (by rw [hGateAtEq C t ht]; exact hw)
    obtain ⟨hL, hExt, hEm, hSzF, hNd, _, hEv, hDr⟩ :=
      hRedFold C.gates 0 env0 [] [] hM' hB' (fun _ h => by simp at h)
        (fun i hi k hk => hEnvW i (by omega) k hk) (fun _ h => by simp at h) List.nodup_nil
    set res := C.gates.foldl stepFold (0, env0, [], [])
    have hOutLt : C.output < res.2.1.length := by
      change C.output < 11 + C.gates.length at hOutHi; rw [hL, hEnvLen]; exact hOutHi
    have hOutEv : ∀ y : Fin 9 → Bool, evalS (wF res.2.2.1 (List.ofFn y)) (res.2.1.getD C.output none) = fP9 y := by
      intro y
      have h1 := hEv (inp (embed y)) (List.ofFn y) (by simp [inp, hEnvLen]) (by simp)
        (fun i hi => hEnvAg y i (by omega)) C.output hOutLt
      rw [← h1]
      change C.eval (inp (embed y)) = fP9 y
      rw [hComp (embed y), hP9eq y]
    have hf9F : fP9 (fun _ => false) = false := by decide
    have hf9T : fP9 (fun i => decide (i = 0 ∨ i = 1)) = true := by decide
    have hOutNotF : res.2.1.getD C.output none ≠ none := by
      intro heq
      have := hOutEv (fun i => decide (i = 0 ∨ i = 1))
      rw [heq, hf9T] at this; exact Bool.noConfusion this
    have hOutNotT : res.2.1.getD C.output none ≠ some none := by
      intro heq
      have := hOutEv (fun _ => false)
      rw [heq, hf9F] at this; exact Bool.noConfusion this
    have hDrLe2 : res.2.2.2.length ≤ 2 := by
      rcases houtv : res.2.1.getD C.output none with _ | (_ | k)
      · exact absurd houtv hOutNotF
      · exact absurd houtv hOutNotT
      · by_contra hgt
        have hEsz : res.2.2.1.length ≤ 15 := by
          simp only [List.length_nil, Nat.zero_add] at hSzF
          change C.gates.length ≤ 18 at hSz; omega
        obtain ⟨y, hy⟩ := h_p9 ⟨res.2.2.1, k⟩ (fun g hg => ⟨by simpa using (hEm g hg).1, (hEm g hg).2⟩) hEsz
        have := hOutEv y
        rw [houtv] at this
        exact hy this
    have huCF : res.2.1.getD u none = none := by rw [hExt u (by omega), hEnvU]
    by_cases hHasAnd : ∃ i < C.gates.length, (gateAt C i).op = GateOp.and ∧ u ∈ (gateAt C i).inputs
    · left
      obtain ⟨i, hiLt, hiAnd, hiIn⟩ := hHasAnd
      have hiDr : i ∈ res.2.2.2 := by
        simpa using (hDr i hiLt u (by rwa [← hGateAtEq C i hiLt]) huCF).1
      have hiCF : res.2.1.getD (11 + i) none = none := by
        have := (hDr i hiLt u (by rwa [← hGateAtEq C i hiLt]) huCF).2 (by rwa [← hGateAtEq C i hiLt])
        rwa [hEnvLen] at this
      have hOutNeI : C.output ≠ 11 + i := fun h => hOutNotF (by rw [h, hiCF])
      have hExJ : ∃ j < C.gates.length, 11 + i ∈ (gateAt C j).inputs :=
        (hNoDead i hiLt).resolve_left hOutNeI
      obtain ⟨j, hjLt, hjIn⟩ := hExJ
      have hij : i < j := by
        have := hRB j hjLt (11 + i) hjIn; omega
      have hjDr : j ∈ res.2.2.2 := by
        simpa using (hDr j hjLt (11 + i) (by rwa [← hGateAtEq C j hjLt]) hiCF).1
      have hSubIJ : ∀ x ∈ res.2.2.2, x = i ∨ x = j := by
        have hCard : ({i, j} : Finset ℕ).card = 2 := Finset.card_pair (by omega)
        have hSub : ({i, j} : Finset ℕ) ⊆ res.2.2.2.toFinset := by
          intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton, List.mem_toFinset] at hx ⊢
          rcases hx with rfl | rfl <;> assumption
        have hEq : ({i, j} : Finset ℕ) = res.2.2.2.toFinset :=
          Finset.eq_of_subset_of_card_le hSub (by have := List.toFinset_card_le res.2.2.2; omega)
        intro x hx
        have : x ∈ ({i, j} : Finset ℕ) := by rw [hEq]; exact List.mem_toFinset.2 hx
        simpa using this
      have hjOr : (gateAt C j).op = GateOp.or := by
        have hMj := (hM (gateAt C j) (by rw [hGateAtEq C j hjLt]; exact List.getElem_mem hjLt)).1
        rcases hMj with hjAnd | hjOr
        · exfalso
          have hjCF : res.2.1.getD (11 + j) none = none := by
            have := (hDr j hjLt (11 + i) (by rwa [← hGateAtEq C j hjLt]) hiCF).2 (by rwa [← hGateAtEq C j hjLt])
            rwa [hEnvLen] at this
          have hOutNeJ : C.output ≠ 11 + j := fun h => hOutNotF (by rw [h, hjCF])
          obtain ⟨k, hkLt, hkIn⟩ := (hNoDead j hjLt).resolve_left hOutNeJ
          have hjk : j < k := by have := hRB k hkLt (11 + j) hkIn; omega
          have hkDr : k ∈ res.2.2.2 := by
            simpa using (hDr k hkLt (11 + j) (by rwa [← hGateAtEq C k hkLt]) hjCF).1
          rcases hSubIJ k hkDr with rfl | rfl <;> omega
        · exact hjOr
      have hjNotU : u ∉ (gateAt C j).inputs := hNoAbsorb i j u hiLt hjLt hu hiAnd hjOr hiIn hjIn
      have hReadU : readsIn C (Finset.range C.size) u = 1 := by
        rw [hReadsEqCard u]
        have hEqSet : (Finset.range C.size).filter (fun k => u ∈ (gateAt C k).inputs) = {i} := by
          ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
          constructor
          · rintro ⟨hkLt, hkIn⟩
            have hkDr : k ∈ res.2.2.2 := by
              simpa using (hDr k hkLt u (by rwa [← hGateAtEq C k hkLt]) huCF).1
            rcases hSubIJ k hkDr with rfl | rfl
            · rfl
            · exact absurd hkIn hjNotU
          · rintro rfl; exact ⟨hiLt, hiIn⟩
        rw [hEqSet]; simp
      have hReadI : readsIn C (Finset.range C.size) (11 + i) = 1 := by
        rw [hReadsEqCard (11 + i)]
        have hEqSet : (Finset.range C.size).filter (fun k => 11 + i ∈ (gateAt C k).inputs) = {j} := by
          ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
          constructor
          · rintro ⟨hkLt, hkIn⟩
            have hik : i < k := by have := hRB k hkLt (11 + i) hkIn; omega
            have hkDr : k ∈ res.2.2.2 := by
              simpa using (hDr k hkLt (11 + i) (by rwa [← hGateAtEq C k hkLt]) hiCF).1
            rcases hSubIJ k hkDr with rfl | rfl
            · omega
            · rfl
          · rintro rfl; exact ⟨hjLt, hjIn⟩
        rw [hEqSet]; simp
      exact ⟨i, j, ⟨hiLt, hiAnd⟩, ⟨hjLt, hjOr⟩, hiIn, hjIn, hReadU, hReadI⟩
    · right
      push Not at hHasAnd
      have hAllOr : ∀ k < C.size, u ∈ (gateAt C k).inputs → isOr C k := by
        intro k hkLt hkIn
        have hMk := (hM (gateAt C k) (by rw [hGateAtEq C k hkLt]; exact List.getElem_mem hkLt)).1
        rcases hMk with hA | hO
        · exact absurd hkIn (hHasAnd k hkLt hA)
        · exact ⟨hkLt, hO⟩
      have hLe2 : readsIn C (Finset.range C.size) u ≤ 2 := by
        rw [hReadsEqCard u]
        have hSub : (Finset.range C.size).filter (fun k => u ∈ (gateAt C k).inputs) ⊆ res.2.2.2.toFinset := by
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset] at hk ⊢
          have hkLt : k < C.gates.length := hk.1
          have hkIn : u ∈ C.gates[k].inputs := by rw [← hGateAtEq C k hkLt]; exact hk.2
          simpa using (hDr k hkLt u hkIn huCF).1
        exact le_trans (Finset.card_le_card hSub) (le_trans (List.toFinset_card_le res.2.2.2) hDrLe2)
      have hGe1 : 1 ≤ readsIn C (Finset.range C.size) u := by
        rw [hReadsEqCard u]
        obtain ⟨j, hjLt, hjIn⟩ := hExU
        exact Finset.card_pos.2 ⟨j, Finset.mem_filter.2 ⟨Finset.mem_range.2 hjLt, hjIn⟩⟩
      exact ⟨hGe1, hLe2, hAllOr⟩
  -- Non-degeneracy: wire 0 and wire 2 are each read by at least one gate of C
  have hWireRead : ∀ (u : ℕ) (xA xB : Fin 10 → Bool),
      (∀ i, i ≠ u → (inp xA).getD i false = (inp xB).getD i false) →
      fP10 xA ≠ fP10 xB → u < 11 → ∃ j < C.gates.length, u ∈ (gateAt C j).inputs := by
    intro u xA xB hAg hNe hu
    by_contra hnone; push Not at hnone
    have h1 : ∀ (gs : List Gate) (wA wB : List Bool),
        wA.length = wB.length →
        (∀ i, i ≠ u → wA.getD i false = wB.getD i false) →
        (∀ g ∈ gs, u ∉ g.inputs) →
        ∀ i, i ≠ u → (wF gs wA).getD i false = (wF gs wB).getD i false := by
      intro gs
      induction gs with
      | nil => intro wA wB _ hA _ i hi; exact hA i hi
      | cons g gs ih =>
        intro wA wB hlen hA hN i hi
        have hge : g.op.eval (g.inputs.map fun k => wA.getD k false) =
            g.op.eval (g.inputs.map fun k => wB.getD k false) := by
          congr 1; apply List.map_congr_left
          intro k hk; exact hA k (fun e => hN g List.mem_cons_self (e ▸ hk))
        apply ih (stepW wA g) (stepW wB g) (by simp [stepW, hlen]) _ (fun g' hg' => hN g' (List.mem_cons_of_mem _ hg')) i hi
        intro k hk
        by_cases hlt : k < wA.length
        · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]; exact hA k hk
        · by_cases heq : k = wA.length
          · subst heq; rw [hSnocLen _ _ _ _ rfl, hSnocLen _ _ _ _ hlen.symm, hge]
          · rw [List.getD_eq_default _ _ (by simp [stepW]; omega), List.getD_eq_default _ _ (by simp [stepW]; omega)]
    have hN : ∀ g ∈ C.gates, u ∉ g.inputs := by
      intro g hg; obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hg
      have := hnone j hj; rwa [hGateAtEq C j hj] at this
    have hEq := h1 C.gates (inp xA) (inp xB) (by simp [inp]) hAg hN C.output (by omega)
    change C.eval (inp xA) = C.eval (inp xB) at hEq
    rw [hComp xA, hComp xB] at hEq
    exact hNe hEq
  have hEx0 : ∃ j < C.gates.length, 0 ∈ (gateAt C j).inputs := by
    apply hWireRead 0 (fun i => decide (i = 2 ∨ i = 4)) (fun i => decide (i = 0 ∨ i = 2 ∨ i = 4))
    · intro i hi
      by_cases h11 : i < 11
      · interval_cases i <;> first | exact absurd rfl hi | decide
      · rw [List.getD_eq_default _ _ (by simp [inp]; omega), List.getD_eq_default _ _ (by simp [inp]; omega)]
    · decide
    · omega
  have hEx2 : ∃ j < C.gates.length, 2 ∈ (gateAt C j).inputs := by
    apply hWireRead 2 (fun i => decide (i = 0 ∨ i = 3)) (fun i => decide (i = 0 ∨ i = 2 ∨ i = 3))
    · intro i hi
      by_cases h11 : i < 11
      · interval_cases i <;> first | exact absurd rfl hi | decide
      · rw [List.getD_eq_default _ _ (by simp [inp]; omega), List.getD_eq_default _ _ (by simp [inp]; omega)]
    · decide
    · omega
  -- Instantiate embeddings for wire 0 and wire 2
  let env0 : List (Option (Option ℕ)) :=
    [none, some (some 0), some (some 1), some (some 2), some (some 3),
     some (some 4), some (some 5), some (some 6), some (some 7), some (some 8), some (some 1)]
  let embed0 : (Fin 9 → Bool) → (Fin 10 → Bool) := fun y i =>
    if h : i.val = 0 then false else y ⟨i.val - 1, by omega⟩
  let sigma2 : Fin 10 → Fin 10 := fun i =>
    ([2, 1, 0, 4, 3, 7, 6, 5, 9, 8] : List (Fin 10)).getD i.val 0
  let env2 : List (Option (Option ℕ)) :=
    [some (some 1), some (some 0), none, some (some 3), some (some 2),
     some (some 6), some (some 5), some (some 4), some (some 8), some (some 7), some (some 1)]
  let embed2 : (Fin 9 → Bool) → (Fin 10 → Bool) := fun y i => embed0 y (sigma2 i)
  have hp9_0 : ∀ y : Fin 9 → Bool, fP10 (embed0 y) = fP9 y := by
    intro y; dsimp only [fP10, fP9, embed0]; simp
  have hSigma2P10 : ∀ x : Fin 10 → Bool, fP10 (fun i => x (sigma2 i)) = fP10 x := by
    intro x
    dsimp only [fP10, sigma2]
    change (x 2 && x 1 || x 1 && x 0 || x 0 && x 4 || x 4 && x 3 || x 3 && x 2 ||
      x 2 && x 7 || x 1 && x 6 || x 0 && x 5 || x 4 && x 9 || x 3 && x 8 ||
      x 7 && x 5 || x 5 && x 8 || x 8 && x 6 || x 6 && x 9 || x 9 && x 7) =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
      x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)
    rw [Bool.and_comm (x 2) (x 1), Bool.and_comm (x 1) (x 0), Bool.and_comm (x 0) (x 4),
      Bool.and_comm (x 4) (x 3), Bool.and_comm (x 3) (x 2), Bool.and_comm (x 7) (x 5),
      Bool.and_comm (x 5) (x 8), Bool.and_comm (x 8) (x 6), Bool.and_comm (x 6) (x 9),
      Bool.and_comm (x 9) (x 7)]
    ac_rfl
  have hp9_2 : ∀ y : Fin 9 → Bool, fP10 (embed2 y) = fP9 y := by
    intro y; exact (hSigma2P10 (embed0 y)).trans (hp9_0 y)
  have hEnv0Ag : ∀ (y : Fin 9 → Bool) (i : ℕ), i < 11 →
      (inp (embed0 y)).getD i false = evalS (List.ofFn y) (env0.getD i none) := by
    intro y i hi
    interval_cases i <;> simp [inp, embed0, env0, evalS]
  have hEnv2Ag : ∀ (y : Fin 9 → Bool) (i : ℕ), i < 11 →
      (inp (embed2 y)).getD i false = evalS (List.ofFn y) (env2.getD i none) := by
    intro y i hi
    interval_cases i <;> simp [inp, embed2, embed0, sigma2, env2, evalS]
  have hClass0 := hClassify 0 env0 embed0 (by omega) rfl (by intro i hi k hk; interval_cases i <;> simp [env0] at hk <;> omega) rfl hEnv0Ag hp9_0 hEx0
  have hClass2 := hClassify 2 env2 embed2 (by omega) rfl (by intro i hi k hk; interval_cases i <;> simp [env2] at hk <;> omega) rfl hEnv2Ag hp9_2 hEx2
  -- Dispatch the 4 cases, collapsing (Or, And) into (And, Or) via sigma2 symmetry
  rcases hClass0 with ⟨i0, j0, hi0A, hj0O, hi0In, hj0In, hr0, hri0⟩ | ⟨h0Lo, h0Hi, h0Or⟩
  · rcases hClass2 with ⟨i2, j2, hi2A, hj2O, hi2In, hj2In, hr2, hri2⟩ | ⟨h2Lo, h2Hi, h2Or⟩
    · obtain ⟨x, hx⟩ := h_and_and C i0 j0 i2 j2 hM hRB hSz hOutLo hOutHi
        ⟨hi0A, hj0O, hi0In, hj0In, hi2A, hj2O, hi2In, hj2In, hr0, hri0, hr2, hri2⟩
      exact hx (hComp x)
    · obtain ⟨x, hx⟩ := h_and_or C i0 j0 hM hRB hSz hOutLo hOutHi
        hi0A hj0O hi0In hj0In ⟨hr0, hri0, h2Lo, h2Hi⟩ h2Or
      exact hx (hComp x)
  · rcases hClass2 with ⟨i2, j2, hi2A, hj2O, hi2In, hj2In, hr2, hri2⟩ | ⟨h2Lo, h2Hi, h2Or⟩
    · -- Apply sigma2 involution to swap wire 0 and wire 2
      let permW : ℕ → ℕ := fun w => if h : w < 10 then (sigma2 ⟨w, h⟩).val else w
      have hPermInv : ∀ w, permW (permW w) = w := by
        intro w
        by_cases h10 : w < 10
        · interval_cases w <;> decide
        · simp [permW, h10]
      have hPermLt : ∀ w k, w < 11 + k → permW w < 11 + k := by
        intro w k hwk
        by_cases h10 : w < 10
        · have := (sigma2 ⟨w, h10⟩).isLt; dsimp only [permW]; rw [dif_pos h10]; omega
        · dsimp only [permW]; rw [dif_neg h10]; exact hwk
      let Csym : Circuit := ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map permW⟩), C.output⟩
      have hSymSz : Csym.size = C.size := List.length_map _
      have hSymM : Monotone2 Csym := by
        intro g hg
        simp only [Csym, List.mem_map] at hg
        obtain ⟨g0, hg0, rfl⟩ := hg
        exact ⟨(hM g0 hg0).1, by simp [(hM g0 hg0).2]⟩
      have hSymRB : ReadsBack 11 Csym := by
        intro j hj w hw
        rw [hGateAtEq Csym j hj] at hw
        simp only [Csym, List.getElem_map, List.mem_map] at hw
        obtain ⟨w0, hw0, rfl⟩ := hw
        have hjC : j < C.gates.length := by simpa [Csym] using hj
        exact hPermLt w0 j (hRB j hjC w0 (by rw [hGateAtEq C j hjC]; exact hw0))
      have hSymComp : ∀ x : Fin 10 → Bool, Csym.eval (inp x) = fP10 x := by
        intro x
        let x' : Fin 10 → Bool := fun i => x (sigma2 i)
        have hRel : ∀ (gs : List Gate) (wS wO : List Bool),
            wS.length = wO.length → 11 ≤ wS.length →
            (∀ w < wS.length, wS.getD (permW w) false = wO.getD w false) →
            (∀ w < (wF gs wO).length, (wF (gs.map fun g => ⟨g.op, g.inputs.map permW⟩) wS).getD (permW w) false = (wF gs wO).getD w false) := by
          intro gs
          induction gs with
          | nil => intro wS wO hlen _ hA w hw; exact hA w (by change w < wO.length at hw; omega)
          | cons g gs ih =>
            intro wS wO hlen h11 hA
            have hge : g.op.eval ((g.inputs.map permW).map fun w => wS.getD w false) =
                g.op.eval (g.inputs.map fun w => wO.getD w false) := by
              congr 1; rw [List.map_map]; apply List.map_congr_left
              intro w _
              by_cases hlt : w < wS.length
              · exact hA w hlt
              · have hge10 : ¬ (w < 10) := by omega
                have hpw : permW w = w := by dsimp only [permW]; rw [dif_neg hge10]
                dsimp only [Function.comp]; rw [hpw, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
            apply ih (stepW wS ⟨g.op, g.inputs.map permW⟩) (stepW wO g) (by simp [stepW, hlen]) (by simp [stepW]; omega)
            intro w hw
            simp only [stepW, List.length_append, List.length_singleton] at hw
            by_cases hlt : w < wS.length
            · have hplt : permW w < wS.length := by
                by_cases h10 : w < 10
                · have := (sigma2 ⟨w, h10⟩).isLt; dsimp only [permW]; rw [dif_pos h10]; omega
                · dsimp only [permW]; rw [dif_neg h10]; exact hlt
              rw [List.getD_append _ _ _ _ hplt, List.getD_append _ _ _ _ (by omega)]
              exact hA w hlt
            · have heq : w = wS.length := by omega
              subst heq
              have hpw : permW wS.length = wS.length := by dsimp only [permW]; rw [dif_neg (by omega)]
              rw [hpw, hSnocLen _ _ _ _ rfl, hSnocLen _ _ _ _ hlen.symm, hge]
        have hInit : ∀ w < (inp x).length, (inp x).getD (permW w) false = (inp x').getD w false := by
          intro w hw
          have hw11 : w < 11 := by simpa [inp] using hw
          interval_cases w <;> simp [inp, permW, x', sigma2, Bool.or_comm]
        have hOutLt' : C.output < (wF C.gates (inp x')).length := by
          rw [hLenWF]; simp [inp]; exact hOutHi
        have hEnd := hRel C.gates (inp x) (inp x') (by simp [inp]) (by simp [inp]) hInit C.output hOutLt'
        have hOutFix : permW C.output = C.output := by dsimp only [permW]; rw [dif_neg (by omega)]
        rw [hOutFix] at hEnd
        change (wF (C.gates.map fun g => ⟨g.op, g.inputs.map permW⟩) (inp x)).getD C.output false = fP10 x
        rw [hEnd]
        change C.eval (inp x') = fP10 x
        rw [hComp x', hSigma2P10 x]
      have hSymGateAt : ∀ k < C.gates.length, gateAt Csym k = ⟨(gateAt C k).op, (gateAt C k).inputs.map permW⟩ := by
        intro k hk
        rw [hGateAtEq Csym k (by simpa [Csym] using hk), hGateAtEq C k hk]
        exact List.getElem_map _
      have hSymCount : ∀ k < C.gates.length, ∀ w, (gateAt Csym k).inputs.count w = (gateAt C k).inputs.count (permW w) := by
        intro k hk w
        rw [hSymGateAt k hk]
        have hInj : Function.Injective permW := fun a b hab => by
          have := congrArg permW hab; rwa [hPermInv, hPermInv] at this
        have hEq : w = permW (permW w) := (hPermInv w).symm
        conv_lhs => rw [hEq]
        exact List.count_map_of_injective (gateAt C k).inputs permW hInj (permW w)
      have hSymReads : ∀ w, readsIn Csym (Finset.range Csym.size) w = readsIn C (Finset.range C.size) (permW w) := by
        intro w
        dsimp only [readsIn]; rw [hSymSz]
        apply Finset.sum_congr rfl
        intro k hk; exact hSymCount k (Finset.mem_range.1 hk) w
      have hSymMem : ∀ k < C.gates.length, ∀ w, w ∈ (gateAt Csym k).inputs ↔ permW w ∈ (gateAt C k).inputs := by
        intro k hk w
        rw [hSymGateAt k hk]
        simp only [List.mem_map]
        constructor
        · rintro ⟨a, ha, rfl⟩; rwa [hPermInv]
        · intro h; exact ⟨permW w, h, hPermInv w⟩
      have hPerm0 : permW 0 = 2 := by decide
      have hPerm2 : permW 2 = 0 := by decide
      have hPermI2 : permW (11 + i2) = 11 + i2 := by dsimp only [permW]; rw [dif_neg (by omega)]
      have hi2Lt : i2 < C.gates.length := hi2A.1
      have hj2Lt : j2 < C.gates.length := hj2O.1
      obtain ⟨x, hx⟩ := h_and_or Csym i2 j2 hSymM hSymRB
        (by rw [hSymSz]; exact hSz) hOutLo (by change C.output < 11 + Csym.size; rw [hSymSz]; exact hOutHi)
        ⟨by simpa [Csym] using hi2Lt, by rw [hSymGateAt i2 hi2Lt]; exact hi2A.2⟩
        ⟨by simpa [Csym] using hj2Lt, by rw [hSymGateAt j2 hj2Lt]; exact hj2O.2⟩
        ((hSymMem i2 hi2Lt 0).2 (by rwa [hPerm0]))
        ((hSymMem j2 hj2Lt (11 + i2)).2 (by rwa [hPermI2]))
        ⟨by rw [hSymReads 0, hPerm0]; exact hr2,
         by rw [hSymReads (11 + i2), hPermI2]; exact hri2,
         by rw [hSymReads 2, hPerm2]; exact h0Lo,
         by rw [hSymReads 2, hPerm2]; exact h0Hi⟩
        (fun k hk hmem => by
          have hkC : k < C.gates.length := by rw [hSymSz] at hk; exact hk
          have hmem0 : 0 ∈ (gateAt C k).inputs := by rw [← hPerm2]; exact (hSymMem k hkC 2).1 hmem
          have hO := h0Or k hkC hmem0
          exact ⟨hk, by rw [hSymGateAt k hkC]; exact hO.2⟩)
      exact hx (hSymComp x)
    · obtain ⟨x, hx⟩ := h_or_or C hM hRB hSz hOutLo hOutHi ⟨h0Lo, h0Hi, h2Lo, h2Hi⟩ h0Or h2Or
      exact hx (hComp x)
