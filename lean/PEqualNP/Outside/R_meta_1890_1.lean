import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Input reindexing follows the wire evaluation argument of R-meta-2736-91.
theorem PEqualNP.Outside.R_meta_1890_1
    (andCases : ∀ (D : Circuit) (pins : List (Fin 12)),
      FanInTwo D → D.size ≤ 17 → pins.length ≤ 2 → ∃ x : Fin 10 → Bool,
        let pre := List.ofFn x ++ [x 0 && x 2]
        D.eval (pre ++ [GateOp.and.eval (pins.map fun j => pre.getD j.val false)]) ≠
          (fun x : Fin 10 → Bool =>
          (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
          (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x)
    (orCases : ∀ (D : Circuit) (pins : List (Fin 12)),
      FanInTwo D → D.size ≤ 17 → pins.length ≤ 2 → ∃ x : Fin 10 → Bool,
        let pre := List.ofFn x ++ [x 0 && x 2]
        D.eval (pre ++ [GateOp.or.eval (pins.map fun j => pre.getD j.val false)]) ≠
          (fun x : Fin 10 → Bool =>
          (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
          (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x)
    (notCases : ∀ (D : Circuit) (pin : Fin 12),
      FanInTwo D → D.size ≤ 17 → ∃ x : Fin 10 → Bool,
        let pre := List.ofFn x ++ [x 0 && x 2]
        D.eval (pre ++ [!(pre.getD pin.val false)]) ≠
          (fun x : Fin 10 → Bool =>
          (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
          (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  have transport :
      ∀ (n : ℕ) (C : Circuit) (p : Fin n → Fin n), FanInTwo C →
        ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
          ∀ (x : Fin n → Bool) (tail : List Bool),
            D.eval (List.ofFn x ++ tail) = C.eval (List.ofFn (x ∘ p) ++ tail) := by
    intro n C p hfan
    let rename (i : ℕ) : ℕ := if hi : i < n then (p ⟨i, hi⟩).val else i
    have early (i : ℕ) (hi : i < n) : rename i < n := by simp [rename, hi]
    have late (i : ℕ) (hi : n ≤ i) : rename i = i := by simp [rename, Nat.not_lt.mpr hi]
    let mapGate (g : Gate) : Gate := ⟨g.op, g.inputs.map rename⟩
    let D : Circuit := ⟨C.gates.map mapGate, rename C.output⟩
    refine ⟨D, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      exact ⟨(hfan g' hg').1, by simpa [mapGate] using (hfan g' hg').2⟩
    · exact List.length_map mapGate
    have run (gs : List Gate) (x y : List Bool) (len : x.length = y.length)
        (lo : n ≤ x.length) (agree : ∀ i, y.getD (rename i) false = x.getD i false) :
        ∀ i, ((Circuit.mk (gs.map mapGate) 0).wires y).getD (rename i) false =
          ((Circuit.mk gs 0).wires x).getD i false := by
      induction gs generalizing x y with
      | nil => exact agree
      | cons g rest ih =>
        let b := g.op.eval (g.inputs.map fun i => x.getD i false)
        have next : (mapGate g).op.eval ((mapGate g).inputs.map fun i => y.getD i false) = b := by
          simp only [b, mapGate, List.map_map, Function.comp_def, agree]
        change ∀ i, ((Circuit.mk (rest.map mapGate) 0).wires (y ++ [_])).getD (rename i) false =
          ((Circuit.mk rest 0).wires (x ++ [b])).getD i false
        rw [next]
        apply ih _ _ (by simp [len]) (by simp; omega)
        intro i
        by_cases hi : i < x.length
        · have hy : rename i < y.length := by
            by_cases hn : i < n
            · have := early i hn
              omega
            · rw [late i (by omega)]
              omega
          rw [List.getD_append _ _ _ _ hy, List.getD_append _ _ _ _ hi]
          exact agree i
        · rw [late i (by omega), List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega), len]
    intro x tail
    apply run C.gates _ _ (by simp) (by simp) _ C.output
    intro i
    by_cases hi : i < n
    · have hx : rename i < (List.ofFn x).length := by simpa using early i hi
      have hy : i < (List.ofFn (x ∘ p)).length := by simpa using hi
      rw [List.getD_append _ _ _ _ hx, List.getD_append _ _ _ _ hy,
          List.getD_eq_getElem _ _ hx, List.getD_eq_getElem _ _ hy]
      simp only [List.getElem_ofFn, Function.comp_apply]
      congr 1
      apply Fin.ext
      exact dite_eq_left hi
    · rw [late i (by omega), List.getD_append_right _ _ _ _ (by simpa using Nat.not_lt.mp hi),
          List.getD_append_right _ _ _ _ (by simpa using Nat.not_lt.mp hi)]
      simp
  intro C p hC small
  obtain ⟨E, eFan, eSize, agree⟩ := transport 10 C p hC
  have eBound : E.size ≤ 18 := eSize.le.trans small
  let f := (fun x : Fin 10 → Bool =>
          (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
          (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
          (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
          (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
  let pre (x : Fin 10 → Bool) := List.ofFn x ++ [x 0 && x 2]
  have preLen (x : Fin 10 → Bool) : (pre x).length = 11 := by simp [pre]
  let clip (i : ℕ) : Fin 12 := ⟨min i 11, Nat.lt_succ_of_le (min_le_right i 11)⟩
  have clipRead (x : Fin 10 → Bool) (i : ℕ) :
      (pre x).getD (clip i).val false = (pre x).getD i false := by
    rcases le_or_gt i 11 with hi | hi
    · simp [clip, min_eq_left hi]
    · have hn := preLen x
      simp only [clip, min_eq_right (le_of_lt hi)]
      rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  have found : ∃ x, E.eval (pre x) ≠ f x := by
    rcases E with ⟨gs, out⟩
    cases gs with
    | nil =>
      let witness (i : Fin 12) (j : Fin 10) : Bool :=
        if i.val < 10 then decide (j.val = i.val)
        else if i.val = 10 then decide (j = 0 ∨ j = 2)
        else decide (j = 0 ∨ j = 1)
      have different (i : Fin 12) : (pre (witness i)).getD i.val false ≠ f (witness i) := by
        fin_cases i <;> decide
      refine ⟨witness (clip out), ?_⟩
      change (pre (witness (clip out))).getD out false ≠ f (witness (clip out))
      rw [← clipRead (witness (clip out)) out]
      exact different (clip out)
    | cons g rest =>
      let D : Circuit := ⟨rest, out⟩
      have dFan : FanInTwo D := fun a ha => eFan a (List.mem_cons_of_mem _ ha)
      have dSize : D.size ≤ 17 := by
        change rest.length ≤ 17
        change rest.length + 1 ≤ 18 at eBound
        omega
      obtain ⟨op, length⟩ := eFan g (List.mem_cons_self)
      let pins := g.inputs.map clip
      have pinLen : pins.length ≤ 2 := by simpa [pins] using length
      have step : ∃ x : Fin 10 → Bool,
          D.eval (pre x ++ [g.op.eval (pins.map fun j => (pre x).getD j.val false)]) ≠ f x := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op
        rcases op with h | h | h
        · rw [h]
          exact andCases D pins dFan dSize pinLen
        · rw [h]
          exact orCases D pins dFan dSize pinLen
        · rw [h]
          let firstPin : Fin 12 := pins.headD 11
          have notSignal (x : Fin 10 → Bool) :
              GateOp.not.eval (pins.map fun j => (pre x).getD j.val false) =
                !((pre x).getD firstPin.val false) := by
            change Bool.not ((pins.map fun j => (pre x).getD j.val false).headD false) =
              Bool.not ((pre x).getD firstPin.val false)
            cases hp : pins with
            | nil =>
              have hz : (pre x).getD 11 false = false := List.getD_eq_default _ _ (by rw [preLen])
              have hpin : firstPin.val = 11 := by simp [firstPin, hp]
              rw [hpin, hz] <;> rfl
            | cons head rest =>
              have hpin : firstPin = head := by simp [firstPin, hp]
              rw [hpin] <;> rfl
          simp_rw [notSignal]
          exact notCases D firstPin dFan dSize
      obtain ⟨x, hx⟩ := step
      refine ⟨x, ?_⟩
      change D.eval (pre x ++ [g.op.eval (g.inputs.map fun i => (pre x).getD i false)]) ≠ f x
      simpa only [pins, List.map_map, Function.comp_def, clipRead] using hx
  obtain ⟨x, hx⟩ := found
  refine ⟨x, ?_⟩
  rw [← agree x [x 0 && x 2]]
  exact hx
