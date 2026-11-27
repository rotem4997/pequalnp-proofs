import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Input transport follows the checked R_meta_1890_1. The marked-pair stabilizer reduces raw pins to five orbits.
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_6030_314
    (raw : ∀ (D : Circuit) (k : Fin 12), k ∈ ([0,1,3,6,8] : List (Fin 12)) →
      FanInTwo D → D.size ≤ 17 → ∃ x : Fin 10 → Bool,
        let pre := List.ofFn x ++ [x 0 && x 2]
        D.eval (pre ++ [!(pre.getD k.val false)]) ≠ ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))))
    (aux : ∀ (D : Circuit) (k : Fin 12), k ∈ ([10,11] : List (Fin 12)) →
      FanInTwo D → D.size ≤ 17 → ∃ x : Fin 10 → Bool,
        let pre := List.ofFn x ++ [x 0 && x 2]
        D.eval (pre ++ [!(pre.getD k.val false)]) ≠ ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))) : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∃ (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : List PEqualNP.CircuitLowerBounds.Gate), x1.gates = x5 :: x6 ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.not) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 (0 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
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
  intro C p fits small first
  obtain ⟨g, gs, shape, hop⟩ := first
  let D : Circuit := ⟨gs, C.output⟩
  have df : FanInTwo D := fun h hh => fits h (shape ▸ List.mem_cons_of_mem g hh)
  have ds : D.size ≤ 17 := by
    change gs.length ≤ 17
    change C.gates.length ≤ 18 at small
    rw [shape, List.length_cons] at small
    omega
  let pre (x : Fin 10 → Bool) := List.ofFn x ++ [x 0 && x 2]
  let F (x : Fin 10 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let read (k : Fin 12) (x : Fin 10 → Bool) := (pre x).getD k.val false
  let idx := g.inputs.headD 11
  let k : Fin 12 := if h : idx < 10 then ⟨(p ⟨idx,h⟩).val, by omega⟩ else ⟨min idx 11, by omega⟩
  have input (x : Fin 10 → Bool) :
      g.op.eval (g.inputs.map fun i => (List.ofFn (x ∘ p) ++ [x 0 && x 2]).getD i false) = !(read k x) := by
    rw [hop]
    let w := List.ofFn (x ∘ p) ++ [x 0 && x 2]
    have hw : w.length = 11 := by simp [w]
    have hp : (pre x).length = 11 := by simp [pre]
    have hfirst : GateOp.not.eval (g.inputs.map fun i => w.getD i false) = !(w.getD idx false) := by
      cases he : g.inputs with
      | nil =>
        change (!false) = !(w.getD idx false)
        rw [show idx = 11 by simp [idx,he], List.getD_eq_default _ _ (by omega)]
      | cons u us =>
        change (!(w.getD u false)) = !(w.getD idx false)
        rw [show idx = u by simp [idx, he]]
    change GateOp.not.eval (g.inputs.map fun i => w.getD i false) = _
    rw [hfirst]
    congr 1
    by_cases hi : idx < 10
    · have hpi : (p ⟨idx,hi⟩).val < (List.ofFn x).length := by simp
      simp only [read, k, dif_pos hi, w, pre]
      rw [List.getD_append _ _ _ _ (by simpa using hi), List.getD_append _ _ _ _ hpi,
        List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hpi]
      simp only [List.getElem_ofFn,Function.comp_apply]
    · by_cases e : idx = 10
      · simp [read,k,hi,e,w,pre]
      · have ge : 11 ≤ idx := by omega
        simp only [read,k,dif_neg hi,min_eq_right ge]
        rw [List.getD_eq_default _ _ (show w.length ≤ idx by omega), List.getD_eq_default _ _ (show (pre x).length ≤ 11 by omega)]
  let perm : Fin 12 → Fin 10 → Fin 10 := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9], ![2, 1, 0, 5, 7, 3, 6, 4, 8, 9], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9], ![2, 1, 0, 4, 3, 7, 6, 5, 9, 8], ![2, 1, 0, 5, 7, 3, 6, 4, 8, 9], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9], ![0, 1, 2, 7, 5, 4, 6, 3, 9, 8], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9], ![0, 1, 2, 7, 5, 4, 6, 3, 9, 8], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]
  let rep : Fin 12 → Fin 12 := ![0, 1, 0, 3, 3, 3, 6, 3, 8, 8, 10, 11]
  have equiv (i : Fin 12) (x : Fin 10 → Bool) :
      F (x ∘ perm i) = F x ∧
      ((x ∘ perm i) 0 && (x ∘ perm i) 2) = (x 0 && x 2) ∧
      read i (x ∘ perm i) = read (rep i) x := by
    fin_cases i <;> refine ⟨?_, ?_, ?_⟩
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change (x 0 && x 2) = (x 0 && x 2)
      ac_rfl
    · rfl
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change (x 0 && x 2) = (x 0 && x 2)
      ac_rfl
    · rfl
    · change ((x 2 && x 1) || (x 1 && x 0) || (x 0 && x 5) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 3) || (x 1 && x 6) || (x 0 && x 4) || (x 5 && x 8) || (x 7 && x 9) || (x 3 && x 4) || (x 4 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 3)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change (x 2 && x 0) = (x 0 && x 2)
      ac_rfl
    · rfl
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change (x 0 && x 2) = (x 0 && x 2)
      ac_rfl
    · rfl
    · change ((x 2 && x 1) || (x 1 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 2) || (x 2 && x 7) || (x 1 && x 6) || (x 0 && x 5) || (x 4 && x 9) || (x 3 && x 8) || (x 7 && x 5) || (x 5 && x 8) || (x 8 && x 6) || (x 6 && x 9) || (x 9 && x 7)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change (x 2 && x 0) = (x 0 && x 2)
      ac_rfl
    · rfl
    · change ((x 2 && x 1) || (x 1 && x 0) || (x 0 && x 5) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 3) || (x 1 && x 6) || (x 0 && x 4) || (x 5 && x 8) || (x 7 && x 9) || (x 3 && x 4) || (x 4 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 3)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change (x 2 && x 0) = (x 0 && x 2)
      ac_rfl
    · rfl
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change (x 0 && x 2) = (x 0 && x 2)
      ac_rfl
    · rfl
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 1 && x 6) || (x 2 && x 3) || (x 7 && x 9) || (x 5 && x 8) || (x 4 && x 3) || (x 3 && x 8) || (x 8 && x 6) || (x 6 && x 9) || (x 9 && x 4)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change (x 0 && x 2) = (x 0 && x 2)
      ac_rfl
    · rfl
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change (x 0 && x 2) = (x 0 && x 2)
      ac_rfl
    · rfl
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 1 && x 6) || (x 2 && x 3) || (x 7 && x 9) || (x 5 && x 8) || (x 4 && x 3) || (x 3 && x 8) || (x 8 && x 6) || (x 6 && x 9) || (x 9 && x 4)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change (x 0 && x 2) = (x 0 && x 2)
      ac_rfl
    · rfl
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change (x 0 && x 2) = (x 0 && x 2)
      ac_rfl
    · rfl
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change (x 0 && x 2) = (x 0 && x 2)
      ac_rfl
    · rfl
  obtain ⟨E, ef, sz, run⟩ := transport 10 D (perm k ∘ p) df
  have bound := sz.le.trans ds
  have repmem (i : Fin 12) : rep i ∈ ([0,1,3,6,8] : List (Fin 12)) ∨
      rep i ∈ ([10,11] : List (Fin 12)) := by fin_cases i <;> decide
  have pick : ∃ x : Fin 10 → Bool, E.eval (pre x ++ [!(read (rep k) x)]) ≠ ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))) := by
    rcases repmem k with h | h
    · exact raw E _ h ef bound
    · exact aux E _ h ef bound
  obtain ⟨x,hx⟩ := pick
  have fe : F x = ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))) := by
    change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) = (((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) || ((x 3 && x 8) || ((x 4 && x 9) || ((x 5 && x 7) || ((x 7 && x 9) || ((x 9 && x 6) || ((x 6 && x 8) || ((x 8 && x 5) || false))))))))))))))))
    simp only [Bool.or_false]
    ac_rfl
  let y := x ∘ perm k
  refine ⟨y, ?_⟩
  change C.eval (List.ofFn (y ∘ p) ++ [y 0 && y 2]) ≠ F y
  intro he
  apply hx
  rw [← fe, ← (equiv k x).1]
  change E.eval (List.ofFn x ++ [x 0 && x 2, !(read (rep k) x)]) = F y
  rw [run]
  have eqC : C.eval (List.ofFn (y ∘ p) ++ [y 0 && y 2]) =
      D.eval ((List.ofFn (y ∘ p) ++ [y 0 && y 2]) ++ [!(read k y)]) := by
    unfold Circuit.eval Circuit.wires
    rw [shape, List.foldl_cons, input y]
  rw [eqC] at he
  rw [(equiv k x).2.1, (equiv k x).2.2] at he
  exact he
