import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1890_811
    (bound : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x3) = (x3 (0 : Fin (10 : ℕ)) && x3 (1 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (2 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (3 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (4 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (0 : Fin (10 : ℕ)) || x3 (0 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (5 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (7 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (9 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (6 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (8 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ)))) → (17 : ℕ) + PEqualNP.NotBracket.notCount x1 ≤ x1.size))
    (dense : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → PEqualNP.NotBracket.notCount x1 + (16 : ℕ) ≤ x1.size → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x5 ∘ x2) ++ [x5 (0 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ))]) ≠ (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x5 := by
  let _ : DecidableEq PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
  intro C p fan small
  by_contra none
  by_cases hn : PEqualNP.NotBracket.notCount C + (16 : ℕ) ≤ C.size
  · exact none (dense C p fan small hn)
  · have comp : ∀ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ p) ++ [x 0 && x 2]) = (fun (x6 : Fin (10 : ℕ) → Bool) => x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) x := by
      intro x
      by_contra h
      exact none ⟨x, h⟩
    let rename (i : ℕ) : ℕ := if hi : i < 10 then (p ⟨i, hi⟩).val else i
    have early (i : ℕ) (hi : i < 10) : rename i < 10 := by simp [rename, hi]
    have late (i : ℕ) (hi : 10 ≤ i) : rename i = i := by simp [rename, Nat.not_lt.mpr hi]
    let mapGate (g : PEqualNP.CircuitLowerBounds.Gate) : PEqualNP.CircuitLowerBounds.Gate := ⟨g.op, g.inputs.map rename⟩
    let E : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map mapGate, rename C.output⟩
    have eFan : PEqualNP.MetaComplexity.FanInTwo E := by
      intro g hg
      obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      exact ⟨(fan g' hg').1, by simpa [mapGate] using (fan g' hg').2⟩
    have eSize : E.size = C.size := List.length_map mapGate
    have eNot : PEqualNP.NotBracket.notCount E = PEqualNP.NotBracket.notCount C := by
      change ((C.gates.map mapGate).filter fun h => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)).length = (C.gates.filter fun h => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)).length
      rw [List.filter_map, List.length_map]
      rfl
    have run (gs : List PEqualNP.CircuitLowerBounds.Gate) (x y : List Bool) (len : x.length = y.length)
        (lo : 10 ≤ x.length) (agree : ∀ i, y.getD (rename i) false = x.getD i false) :
        ∀ i, ((PEqualNP.CircuitLowerBounds.Circuit.mk (gs.map mapGate) 0).wires y).getD (rename i) false =
          ((PEqualNP.CircuitLowerBounds.Circuit.mk gs 0).wires x).getD i false := by
      induction gs generalizing x y with
      | nil => exact agree
      | cons g rest ih =>
        let b := g.op.eval (g.inputs.map fun i => x.getD i false)
        have next : (mapGate g).op.eval ((mapGate g).inputs.map fun i => y.getD i false) = b := by
          simp only [b, mapGate, List.map_map, Function.comp_def, agree]
        change ∀ i, ((PEqualNP.CircuitLowerBounds.Circuit.mk (rest.map mapGate) 0).wires (y ++ [_])).getD (rename i) false =
          ((PEqualNP.CircuitLowerBounds.Circuit.mk rest 0).wires (x ++ [b])).getD i false
        rw [next]
        apply ih _ _ (by simp [len]) (by simp; omega)
        intro i
        by_cases hi : i < x.length
        · have hy : rename i < y.length := by
            by_cases hn : i < 10
            · have := early i hn
              omega
            · rw [late i (by omega)]
              omega
          rw [List.getD_append _ _ _ _ hy, List.getD_append _ _ _ _ hi]
          exact agree i
        · rw [late i (by omega), List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega), len]
    have agreeE : ∀ (x : Fin 10 → Bool), E.eval (List.ofFn x ++ [x 0 && x 2]) = C.eval (List.ofFn (x ∘ p) ++ [x 0 && x 2]) := by
      intro x
      apply run C.gates _ _ (by simp) (by simp) _ C.output
      intro i
      by_cases hi : i < 10
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
    let step := fun (w : List Bool) (h : PEqualNP.CircuitLowerBounds.Gate) => w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]
    let g0 : PEqualNP.CircuitLowerBounds.Gate := ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 2]⟩
    let F : PEqualNP.CircuitLowerBounds.Circuit := ⟨g0 :: E.gates, E.output⟩
    have fanF : PEqualNP.MetaComplexity.FanInTwo F := by
      intro h hh
      rcases List.mem_cons.mp hh with e | hh
      · rw [e]
        exact ⟨Or.inl rfl, Nat.le_refl 2⟩
      · exact eFan h hh
    have first : ∀ x : Fin 10 → Bool, step (List.ofFn x) g0 = List.ofFn x ++ [x 0 && x 2] := by
      intro x
      show List.ofFn x ++ [List.all [(List.ofFn x).getD 0 false, (List.ofFn x).getD 2 false] id] = _
      simp [List.getD_eq_getElem?_getD]
    have evalF : ∀ (x3 : Fin (10 : ℕ) → Bool), F.eval (List.ofFn x3) = (x3 (0 : Fin (10 : ℕ)) && x3 (1 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (2 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (3 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (4 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (0 : Fin (10 : ℕ)) || x3 (0 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (5 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (7 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (9 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (6 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (8 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ))) := by
      intro x
      change (E.gates.foldl step (step (List.ofFn x) g0)).getD E.output false = _
      rw [first x]
      exact (agreeE x).trans (comp x)
    have bd := bound F fanF evalF
    have hg0 : ¬(decide (g0.op = PEqualNP.CircuitLowerBounds.GateOp.not) = true) := by
      intro hd
      have e := of_decide_eq_true hd
      cases e
    have nc : PEqualNP.NotBracket.notCount F = PEqualNP.NotBracket.notCount E := by
      change ((g0 :: E.gates).filter fun h => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)).length = (E.gates.filter fun h => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)).length
      rw [List.filter_cons_of_neg (p := fun (h : PEqualNP.CircuitLowerBounds.Gate) => decide (h.op = PEqualNP.CircuitLowerBounds.GateOp.not)) hg0]
    have dl : F.size = E.size + 1 := List.length_cons
    omega
