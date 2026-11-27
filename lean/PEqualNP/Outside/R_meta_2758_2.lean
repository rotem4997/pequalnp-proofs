import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2758_2
    (h1 : ∀ (x1 : List ℕ), (x1 = [0, 0] ∨ x1 = [9, 9] ∨ x1 = [0, 9]) →
      ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x5 → x5.size ≤ (13 : ℕ) →
        ∃ (x8 : Fin (9 : ℕ) → Bool),
          have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];
          x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))))
    (h2 : ∀ (x1 : List ℕ), (x1 = [0, 1] ∨ x1 = [0, 4]) →
      ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x5 → x5.size ≤ (13 : ℕ) →
        ∃ (x8 : Fin (9 : ℕ) → Bool),
          have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];
          x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))))
    (h3 : ∀ (x1 : List ℕ), (x1 = [0, 2] ∨ x1 = [0, 3] ∨ x1 = [0, 6]) →
      ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x5 → x5.size ≤ (13 : ℕ) →
        ∃ (x8 : Fin (9 : ℕ) → Bool),
          have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];
          x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))))
    (h4 : ∀ (x1 : List ℕ), (x1 = [9, 1] ∨ x1 = [9, 2] ∨ x1 = [9, 3] ∨ x1 = [9, 4] ∨ x1 = [9, 6]) →
      ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x5 → x5.size ≤ (13 : ℕ) →
        ∃ (x8 : Fin (9 : ℕ) → Bool),
          have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];
          x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)))) :
    ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 < (10 : ℕ)) →       (0 : ℕ) ∈ x1 ∨ (9 : ℕ) ∈ x1 →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  intro x1 hlen hlt h09 C hfan hsz
  rcases x1 with _ | ⟨a, _ | ⟨b, _ | _⟩⟩ <;> simp only [List.length_nil, List.length_cons] at hlen
  · omega
  · omega
  · have ha : a < 10 := hlt a (by simp)
    have hb : b < 10 := hlt b (by simp)
    have hor_eval : ∀ u v : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [u, v] = (u || v) :=
      fun u v => by cases u <;> cases v <;> rfl
    have hcomm : ∀ (p q : ℕ) (x : Fin 9 → Bool),
        let x9 : List Bool := List.ofFn x ++ [!x 0]
        PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun k => x9.getD k false) [p, q]) =
        PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun k => x9.getD k false) [q, p]) := by
      intro p q x
      simp only [List.map_cons, List.map_nil, hor_eval]
      exact Bool.or_comm _ _
    let σ : Fin 9 → Fin 9 := fun i =>
      if i = 1 then 5 else if i = 5 then 1
      else if i = 2 then 8 else if i = 8 then 2
      else if i = 6 then 7 else if i = 7 then 6
      else i
    let π : ℕ → ℕ := fun w => if h : w < 9 then (σ ⟨w, h⟩).val else w
    have hσ_inv : ∀ i : Fin 9, σ (σ i) = i := by decide
    have hπ_lt9 : ∀ (w : ℕ) (hw : w < 9), π w = (σ ⟨w, hw⟩).val := fun w hw => by
      simp only [π, hw, ↓reduceDIte]
    have hπ_ge9 : ∀ (w : ℕ), 9 ≤ w → π w = w := fun w hw => by
      have hnot : ¬ w < 9 := Nat.not_lt.mpr hw
      simp only [π, hnot, ↓reduceDIte]
    have hπ_inv : ∀ w : ℕ, π (π w) = w := by
      intro w
      by_cases hw : w < 9
      · rw [hπ_lt9 w hw, hπ_lt9 _ (σ ⟨w, hw⟩).isLt]
        exact congrArg Fin.val (hσ_inv ⟨w, hw⟩)
      · rw [hπ_ge9 w (Nat.le_of_not_lt hw), hπ_ge9 w (Nat.le_of_not_lt hw)]
    let mapGate : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate :=
      fun g => ⟨g.op, g.inputs.map π⟩
    let mapC : PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Circuit :=
      fun C0 => ⟨C0.gates.map mapGate, π C0.output⟩
    have hmap_fan : PEqualNP.MetaComplexity.FanInTwo (mapC C) := by
      intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      obtain ⟨hop, hlen'⟩ := hfan g0 hg0
      exact ⟨hop, by simpa [mapGate] using hlen'⟩
    have hmap_sz : (mapC C).size ≤ 13 := by
      change (C.gates.map mapGate).length ≤ 13
      rw [List.length_map]
      exact hsz
    let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool :=
      fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
    have hfold_trans : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (ws ws' : List Bool),
        ws.length = ws'.length →
        9 ≤ ws.length →
        (∀ w, ws'.getD w false = ws.getD (π w) false) →
        (gs.foldl step ws).length = ((gs.map mapGate).foldl step ws').length ∧
        ∀ w, ((gs.map mapGate).foldl step ws').getD w false = (gs.foldl step ws).getD (π w) false := by
      intro gs
      induction gs with
      | nil =>
        intro ws ws' hlen' _ hrel
        exact ⟨hlen', hrel⟩
      | cons g gs ih =>
        intro ws ws' hlen' h9 hrel
        simp only [List.map_cons, List.foldl_cons]
        have heval_eq : (mapGate g).op.eval ((mapGate g).inputs.map fun i => ws'.getD i false) =
            g.op.eval (g.inputs.map fun i => ws.getD i false) := by
          dsimp only [mapGate]
          congr 1
          rw [List.map_map]
          apply List.map_congr_left
          intro i _
          dsimp only [Function.comp]
          rw [hrel, hπ_inv]
        apply ih
        · simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        · simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        · intro w
          dsimp only [step]
          rw [heval_eq]
          by_cases hw : w < ws'.length
          · have hπw : π w < ws.length := by
              by_cases hw9 : w < 9
              · rw [hπ_lt9 w hw9]; have := (σ ⟨w, hw9⟩).isLt; omega
              · rw [hπ_ge9 w (Nat.le_of_not_lt hw9)]; omega
            simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hw,
              List.getElem?_append_left hπw]
            simpa only [List.getD_eq_getElem?_getD] using hrel w
          · have hge : ws'.length ≤ w := Nat.le_of_not_lt hw
            have hπeq : π w = w := hπ_ge9 w (by omega)
            rw [hπeq]
            simp only [List.getD_eq_getElem?_getD,
              List.getElem?_append_right hge,
              List.getElem?_append_right (show ws.length ≤ w by omega), hlen']
    have hpet_sym : ∀ x : Fin 9 → Bool,
        (x (σ 0) && x (σ 1) || x (σ 1) && x (σ 2) || x (σ 2) && x (σ 3) || x (σ 3) && x (σ 4) ||
          x (σ 4) && x (σ 0) || x (σ 0) && x (σ 5) || x (σ 1) && x (σ 6) || x (σ 2) && x (σ 7) ||
          x (σ 3) && x (σ 8) || x (σ 5) && x (σ 7) || x (σ 6) && x (σ 8) || x (σ 8) && x (σ 5)) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
          x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
          x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
      intro x
      have h0 : σ 0 = 0 := rfl
      have h1' : σ 1 = 5 := rfl
      have h2' : σ 2 = 8 := rfl
      have h3' : σ 3 = 3 := rfl
      have h4' : σ 4 = 4 := rfl
      have h5' : σ 5 = 1 := rfl
      have h6' : σ 6 = 7 := rfl
      have h7' : σ 7 = 6 := rfl
      have h8' : σ 8 = 2 := rfl
      rw [h0, h1', h2', h3', h4', h5', h6', h7', h8']
      have hc1 : (x 5 && x 8) = (x 8 && x 5) := Bool.and_comm _ _
      have hc2 : (x 8 && x 3) = (x 3 && x 8) := Bool.and_comm _ _
      have hc3 : (x 8 && x 6) = (x 6 && x 8) := Bool.and_comm _ _
      have hc4 : (x 7 && x 2) = (x 2 && x 7) := Bool.and_comm _ _
      have hc5 : (x 2 && x 1) = (x 1 && x 2) := Bool.and_comm _ _
      rw [hc1, hc2, hc3, hc4, hc5]
      ac_rfl
    have htransport : ∀ (p q : ℕ), p < 10 → q < 10 →
        (∃ x : Fin 9 → Bool,
          let x9 : List Bool := List.ofFn x ++ [!x 0]
          (mapC C).eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
            (List.map (fun k => x9.getD k false) [π p, π q])]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
            x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
            x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5)) →
        ∃ x : Fin 9 → Bool,
          let x9 : List Bool := List.ofFn x ++ [!x 0]
          C.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
            (List.map (fun k => x9.getD k false) [p, q])]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
            x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
            x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
      intro p q hp hq hex
      obtain ⟨x, hx⟩ := hex
      refine ⟨fun i => x (σ i), ?_⟩
      let x9' : List Bool := List.ofFn x ++ [!x 0]
      let x9 : List Bool := List.ofFn (fun i => x (σ i)) ++ [!x (σ 0)]
      have hget_x9 : ∀ w : ℕ, x9'.getD w false = x9.getD (π w) false := by
        intro w
        by_cases hw : w < 9
        · rw [hπ_lt9 w hw]
          have h1' : w < (List.ofFn x).length := by simp [hw]
          have h2' : (σ ⟨w, hw⟩).val < (List.ofFn (fun i => x (σ i))).length := by
            simp [(σ ⟨w, hw⟩).isLt]
          dsimp only [x9', x9]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h1',
            List.getElem?_append_left h2']
          rw [List.getElem?_eq_getElem h1', List.getElem?_eq_getElem h2']
          simp only [Option.getD_some, List.getElem_ofFn, Fin.eta]
          exact congrArg x (hσ_inv ⟨w, hw⟩).symm
        · rw [hπ_ge9 w (Nat.le_of_not_lt hw)]
          have hge : 9 ≤ w := Nat.le_of_not_lt hw
          dsimp only [x9', x9]
          simp only [List.getD_eq_getElem?_getD,
            List.getElem?_append_right (show (List.ofFn x).length ≤ w by simp [hge]),
            List.getElem?_append_right (show (List.ofFn (fun i => x (σ i))).length ≤ w by simp [hge]),
            List.length_ofFn]
          have h0 : σ 0 = 0 := rfl
          rw [h0]
      have hor_same : PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun k => x9'.getD k false) [π p, π q]) =
          PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun k => x9.getD k false) [p, q]) := by
        simp only [List.map_cons, List.map_nil, hor_eval, hget_x9, hπ_inv]
      let ws' : List Bool := x9' ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
        (List.map (fun k => x9'.getD k false) [π p, π q])]
      let ws : List Bool := x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
        (List.map (fun k => x9.getD k false) [p, q])]
      have hlen_ws : ws.length = ws'.length := by simp [ws, ws', x9, x9']
      have h9_ws : 9 ≤ ws.length := by simp [ws, x9]
      have hrel_ws : ∀ w, ws'.getD w false = ws.getD (π w) false := by
        intro w
        by_cases hw10 : w < 10
        · have hπlt10 : π w < 10 := by
            by_cases hw9 : w < 9
            · rw [hπ_lt9 w hw9]; have := (σ ⟨w, hw9⟩).isLt; omega
            · rw [hπ_ge9 w (Nat.le_of_not_lt hw9)]; omega
          have h1' : w < x9'.length := by simp [x9', hw10]
          have h2' : π w < x9.length := by simp [x9, hπlt10]
          dsimp only [ws', ws]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h1',
            List.getElem?_append_left h2']
          simpa only [List.getD_eq_getElem?_getD] using hget_x9 w
        · have hge10 : 10 ≤ w := Nat.le_of_not_lt hw10
          rw [hπ_ge9 w (by omega)]
          dsimp only [ws', ws]
          rw [hor_same]
          simp only [List.getD_eq_getElem?_getD,
            List.getElem?_append_right (show x9'.length ≤ w by simp [x9', hge10]),
            List.getElem?_append_right (show x9.length ≤ w by simp [x9, hge10]),
            show x9'.length = 10 by simp [x9'], show x9.length = 10 by simp [x9]]
      have heval_eq : (mapC C).eval ws' = C.eval ws := by
        change ((C.gates.map mapGate).foldl step ws').getD (π C.output) false =
          (C.gates.foldl step ws).getD C.output false
        have hres' := (hfold_trans C.gates ws ws' hlen_ws h9_ws hrel_ws).2 (π C.output)
        rw [hπ_inv] at hres'
        exact hres'
      dsimp only
      rw [hpet_sym x]
      intro hEq
      exact hx (heval_eq.trans hEq)
    have hsolve_0 : ∀ k : ℕ, k < 10 →
        ∃ x : Fin 9 → Bool,
          let x9 : List Bool := List.ofFn x ++ [!x 0]
          C.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
            (List.map (fun j => x9.getD j false) [0, k])]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
            x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
            x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
      intro k hk
      have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
      rcases hk_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1 [0, 0] (Or.inl rfl) C hfan hsz
      · exact h2 [0, 1] (Or.inl rfl) C hfan hsz
      · exact h3 [0, 2] (Or.inl rfl) C hfan hsz
      · exact h3 [0, 3] (Or.inr (Or.inl rfl)) C hfan hsz
      · exact h2 [0, 4] (Or.inr rfl) C hfan hsz
      · exact htransport 0 5 (by omega) (by omega) (h2 [0, 1] (Or.inl rfl) (mapC C) hmap_fan hmap_sz)
      · exact h3 [0, 6] (Or.inr (Or.inr rfl)) C hfan hsz
      · exact htransport 0 7 (by omega) (by omega) (h3 [0, 6] (Or.inr (Or.inr rfl)) (mapC C) hmap_fan hmap_sz)
      · exact htransport 0 8 (by omega) (by omega) (h3 [0, 2] (Or.inl rfl) (mapC C) hmap_fan hmap_sz)
      · exact h1 [0, 9] (Or.inr (Or.inr rfl)) C hfan hsz
    have hsolve_9 : ∀ k : ℕ, k < 10 →
        ∃ x : Fin 9 → Bool,
          let x9 : List Bool := List.ofFn x ++ [!x 0]
          C.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval
            (List.map (fun j => x9.getD j false) [9, k])]) ≠
          (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
            x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
            x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5) := by
      intro k hk
      have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
      rcases hk_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain ⟨x, hx⟩ := h1 [0, 9] (Or.inr (Or.inr rfl)) C hfan hsz
        exact ⟨x, by simpa only [hcomm 9 0 x] using hx⟩
      · exact h4 [9, 1] (Or.inl rfl) C hfan hsz
      · exact h4 [9, 2] (Or.inr (Or.inl rfl)) C hfan hsz
      · exact h4 [9, 3] (Or.inr (Or.inr (Or.inl rfl))) C hfan hsz
      · exact h4 [9, 4] (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) C hfan hsz
      · exact htransport 9 5 (by omega) (by omega) (h4 [9, 1] (Or.inl rfl) (mapC C) hmap_fan hmap_sz)
      · exact h4 [9, 6] (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) C hfan hsz
      · exact htransport 9 7 (by omega) (by omega) (h4 [9, 6] (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (mapC C) hmap_fan hmap_sz)
      · exact htransport 9 8 (by omega) (by omega) (h4 [9, 2] (Or.inr (Or.inl rfl)) (mapC C) hmap_fan hmap_sz)
      · exact h1 [9, 9] (Or.inr (Or.inl rfl)) C hfan hsz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h09
    rcases h09 with (rfl | rfl) | (rfl | rfl)
    · exact hsolve_0 b hb
    · obtain ⟨x, hx⟩ := hsolve_0 a ha
      exact ⟨x, by simpa only [hcomm a 0 x] using hx⟩
    · exact hsolve_9 b hb
    · obtain ⟨x, hx⟩ := hsolve_9 a ha
      exact ⟨x, by simpa only [hcomm a 9 x] using hx⟩
  · omega
