import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 16000 in
set_option maxHeartbeats 12000000 in
theorem PEqualNP.Outside.R_meta_5835_2
    (c6 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0)) 7)
    (fewHits : ∀ (C : Circuit), FanInTwo C → 11 ≤ C.size → C.size ≤ 17 → ReadsBack 10 C → C.output = 9 + C.size →
      let reads : Gate → List ℕ := fun g => if g.op.eval [false] then g.inputs.take 1 else g.inputs
      let hits : ℕ → ℕ := fun v => C.gates.countP fun g => (reads g).contains v
      let killed : ℕ → ℕ := fun v => C.gates.countP fun g =>
        (reads g).any fun k => k == v || (10 ≤ k && (C.gates[k - 10]?).any fun h =>
          (reads h).contains v && (h.op.eval [false] || h.op.eval [true, false]))
      (∀ g ∈ C.gates, g.inputs.length = (if g.op.eval [false] then 1 else 2) ∧
        (g.inputs.length = 2 → g.inputs.getD 0 0 ≠ g.inputs.getD 1 0)) →
      (∀ j : ℕ, j + 1 < C.size → ∃ g ∈ C.gates, 10 + j ∈ reads g) →
      (∀ i : Fin 10, ∃ g ∈ C.gates, i.val ∈ reads g) →
      hits 0 ≤ hits 1 → killed 0 ≤ 6 → killed 1 ≤ 6 →
      C.gates.countP (fun g => (reads g).contains 0 || (reads g).contains 1) ≤ 4 →
      ∃ x : Fin 10 → Bool, (x 0 || x 1) = true ∧ C.eval (List.ofFn x) ≠
        decide (∃ i j : Fin 10, x i = true ∧ x j = true ∧
          (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD i.val 0).testBit j.val = true))
    (manyHits : ∀ (C : Circuit), FanInTwo C → 15 ≤ C.size → C.size ≤ 17 → ReadsBack 10 C → C.output = 9 + C.size →
      let reads : Gate → List ℕ := fun g => if g.op.eval [false] then g.inputs.take 1 else g.inputs
      let hits : ℕ → ℕ := fun v => C.gates.countP fun g => (reads g).contains v
      let hits01 : ℕ := C.gates.countP fun g => (reads g).contains 0 || (reads g).contains 1
      let killed : ℕ → ℕ := fun v => C.gates.countP fun g =>
        (reads g).any fun k => k == v || (10 ≤ k && (C.gates[k - 10]?).any fun h =>
          (reads h).contains v && (h.op.eval [false] || h.op.eval [true, false]))
      (∀ g ∈ C.gates, g.inputs.length = (if g.op.eval [false] then 1 else 2) ∧
        (g.inputs.length = 2 → g.inputs.getD 0 0 ≠ g.inputs.getD 1 0)) →
      (∀ j : ℕ, j + 1 < C.size → ∃ g ∈ C.gates, 10 + j ∈ reads g) →
      (∀ i : Fin 10, ∃ g ∈ C.gates, i.val ∈ reads g) →
      hits 0 ≤ hits 1 → killed 0 ≤ 6 → killed 1 ≤ 6 → 5 ≤ hits01 → hits01 ≤ 7 → 10 + hits01 ≤ C.size →
      ∃ x : Fin 10 → Bool, (x 0 || x 1) = true ∧ C.eval (List.ofFn x) ≠
        decide (∃ i j : Fin 10, x i = true ∧ x j = true ∧
          (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD i.val 0).testBit j.val = true)) :
    (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (17 : ℕ) → ∃ (x4 : Fin (10 : ℕ) → Bool), (x4 (0 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ))) = Bool.true ∧ x1.eval (List.ofFn x4) ≠ (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4) := by
  classical
  let P : (Fin 10 → Bool) → Bool := fun x5 =>
    x5 0 && x5 1 || x5 1 && x5 2 || x5 2 && x5 3 || x5 3 && x5 4 || x5 4 && x5 0 ||
    x5 0 && x5 5 || x5 1 && x5 6 || x5 2 && x5 7 || x5 3 && x5 8 || x5 4 && x5 9 ||
    x5 5 && x5 7 || x5 7 && x5 9 || x5 9 && x5 6 || x5 6 && x5 8 || x5 8 && x5 5
  let Q : (Fin 10 → Bool) → Bool := fun x =>
    decide (∃ i j : Fin 10, x i = true ∧ x j = true ∧
      (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD i.val 0).testBit j.val = true)
  have hPQ : ∀ x : Fin 10 → Bool, P x = Q x := by decide +kernel
  let C6 : (Fin 6 → Bool) → Bool := fun x =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 0)
  let reads : Gate → List ℕ := fun g => if g.op.eval [false] then g.inputs.take 1 else g.inputs
  let wstep : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have andEval (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have orEval (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have notEval (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
  have wlen : ∀ (gs : List Gate) (w : List Bool), (gs.foldl wstep w).length = w.length + gs.length := by
    intro gs; induction gs with
    | nil => intro w; simp
    | cons g gs ih => intro w; rw [List.foldl_cons, ih]; simp [wstep]; omega
  have wpres : ∀ (gs : List Gate) (w : List Bool) (i : ℕ),
      i < w.length → (gs.foldl wstep w).getD i false = w.getD i false := by
    intro gs; induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi; rw [List.foldl_cons, ih (wstep w g) i (by simp [wstep]; omega)]
      exact List.getD_append _ _ _ _ hi
  let evalSym : List Bool → Sum Bool ℕ → Bool := fun w s => Sum.elim id (fun k => w.getD k false) s
  let symBd : ℕ → Sum Bool ℕ → Prop := fun m s => Sum.elim (fun _ => True) (fun k => k < m) s
  let cstep (n : ℕ) : (List (Sum Bool ℕ) × List Gate) → Gate → (List (Sum Bool ℕ) × List Gate) :=
    fun st g =>
      let env := st.1
      let dgs := st.2
      if g.op.eval [false] then
        if g.inputs.isEmpty then (env ++ [Sum.inl true], dgs)
        else
          Sum.elim
            (fun b => (env ++ [Sum.inl (!b)], dgs))
            (fun k => (env ++ [Sum.inr (n + dgs.length)], dgs ++ [⟨GateOp.not, [k]⟩]))
            (env.getD (g.inputs.getD 0 0) (Sum.inl false))
      else if g.op.eval [] then
        if g.inputs.length == 0 then (env ++ [Sum.inl true], dgs)
        else if g.inputs.length == 1 then (env ++ [env.getD (g.inputs.getD 0 0) (Sum.inl false)], dgs)
        else
          let ea := env.getD (g.inputs.getD 0 0) (Sum.inl false)
          let eb := env.getD (g.inputs.getD 1 0) (Sum.inl false)
          Sum.elim
            (fun ba => if ba then (env ++ [eb], dgs) else (env ++ [Sum.inl false], dgs))
            (fun ka =>
              Sum.elim
                (fun bb => if bb then (env ++ [Sum.inr ka], dgs) else (env ++ [Sum.inl false], dgs))
                (fun kb =>
                  if ka == kb then (env ++ [Sum.inr ka], dgs)
                  else (env ++ [Sum.inr (n + dgs.length)], dgs ++ [⟨GateOp.and, [ka, kb]⟩]))
                eb)
            ea
      else
        if g.inputs.length == 0 then (env ++ [Sum.inl false], dgs)
        else if g.inputs.length == 1 then (env ++ [env.getD (g.inputs.getD 0 0) (Sum.inl false)], dgs)
        else
          let ea := env.getD (g.inputs.getD 0 0) (Sum.inl false)
          let eb := env.getD (g.inputs.getD 1 0) (Sum.inl false)
          Sum.elim
            (fun ba => if ba then (env ++ [Sum.inl true], dgs) else (env ++ [eb], dgs))
            (fun ka =>
              Sum.elim
                (fun bb => if bb then (env ++ [Sum.inl true], dgs) else (env ++ [Sum.inr ka], dgs))
                (fun kb =>
                  if ka == kb then (env ++ [Sum.inr ka], dgs)
                  else (env ++ [Sum.inr (n + dgs.length)], dgs ++ [⟨GateOp.or, [ka, kb]⟩]))
                eb)
            ea
  have cstep_env_pres : ∀ (n : ℕ) (env : List (Sum Bool ℕ)) (dgs : List Gate) (g : Gate),
      ∃ v : Sum Bool ℕ, (cstep n (env, dgs) g).1 = env ++ [v] := by
    intro n env dgs g; dsimp only [cstep]
    split_ifs
    all_goals try exact ⟨_, rfl⟩
    · cases env.getD (g.inputs.getD 0 0) (Sum.inl false) <;> exact ⟨_, rfl⟩
    · cases env.getD (g.inputs.getD 0 0) (Sum.inl false) with
      | inl ba => cases ba <;> exact ⟨_, rfl⟩
      | inr ka =>
        cases env.getD (g.inputs.getD 1 0) (Sum.inl false) with
        | inl bb => cases bb <;> exact ⟨_, rfl⟩
        | inr kb => by_cases h : ka = kb <;> simp [h]
    · cases env.getD (g.inputs.getD 0 0) (Sum.inl false) with
      | inl ba => cases ba <;> exact ⟨_, rfl⟩
      | inr ka =>
        cases env.getD (g.inputs.getD 1 0) (Sum.inl false) with
        | inl bb => cases bb <;> exact ⟨_, rfl⟩
        | inr kb => by_cases h : ka = kb <;> simp [h]
  have cstep_dlen_le : ∀ (n : ℕ) (env : List (Sum Bool ℕ)) (dgs : List Gate) (g : Gate),
      (cstep n (env, dgs) g).2.length ≤ dgs.length + 1 := by
    intro n env dgs g; dsimp only [cstep]
    by_cases hnot : g.op.eval [false] = true
    · simp only [hnot, ↓reduceIte]
      by_cases he : g.inputs.isEmpty = true
      · simp [he]
      · simp only [he, Bool.false_eq_true, ↓reduceIte]
        cases env.getD (g.inputs.getD 0 0) (Sum.inl false) <;> simp
    · simp only [hnot, Bool.false_eq_true, ↓reduceIte]
      by_cases hand : g.op.eval [] = true
      · simp only [hand, ↓reduceIte]
        by_cases h0 : (g.inputs.length == 0) = true
        · simp [h0]
        · simp only [h0, Bool.false_eq_true, ↓reduceIte]
          by_cases h1 : (g.inputs.length == 1) = true
          · simp [h1]
          · simp only [h1, Bool.false_eq_true, ↓reduceIte]
            cases env.getD (g.inputs.getD 0 0) (Sum.inl false) with
            | inl ba => cases ba <;> simp
            | inr ka =>
              cases env.getD (g.inputs.getD 1 0) (Sum.inl false) with
              | inl bb => cases bb <;> simp
              | inr kb => by_cases h : ka = kb <;> simp [h]
      · simp only [hand, Bool.false_eq_true, ↓reduceIte]
        by_cases h0 : (g.inputs.length == 0) = true
        · simp [h0]
        · simp only [h0, Bool.false_eq_true, ↓reduceIte]
          by_cases h1 : (g.inputs.length == 1) = true
          · simp [h1]
          · simp only [h1, Bool.false_eq_true, ↓reduceIte]
            cases env.getD (g.inputs.getD 0 0) (Sum.inl false) with
            | inl ba => cases ba <;> simp
            | inr ka =>
              cases env.getD (g.inputs.getD 1 0) (Sum.inl false) with
              | inl bb => cases bb <;> simp
              | inr kb => by_cases h : ka = kb <;> simp [h]
  have cstep_fold_le : ∀ (n : ℕ) (ls : List Gate) (st : List (Sum Bool ℕ) × List Gate),
      (ls.foldl (cstep n) st).2.length ≤ st.2.length + ls.length := by
    intro n ls; induction ls with
    | nil => intro st; simp
    | cons a as ih =>
      intro st; rcases st with ⟨env, dgs⟩; rw [List.foldl_cons]
      exact (ih _).trans (by have := cstep_dlen_le n env dgs a; simp only [List.length_cons]; omega)
  have cstep_no_emit : ∀ (n : ℕ) (env : List (Sum Bool ℕ)) (dgs : List Gate) (g : Gate),
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) → g.inputs.length ≤ 2 →
      (∃ w ∈ reads g, ∃ c : Bool, env.getD w (Sum.inl false) = Sum.inl c) →
      (cstep n (env, dgs) g).2.length = dgs.length := by
    intro n env dgs g hgop hlen hEx
    obtain ⟨w, hw, c, hc⟩ := hEx
    have hop : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hgop
    rcases hop with hop | hop | hop
    · cases hgin : g.inputs with
      | nil => simp [cstep, hop, andEval, hgin]
      | cons a tl =>
        cases tl with
        | nil => simp [cstep, hop, andEval, hgin]
        | cons b tl2 =>
          cases tl2 with
          | cons _ _ => simp [hgin] at hlen
          | nil =>
            have hmem : w = a ∨ w = b := by
              dsimp only [reads] at hw; rw [hop] at hw; simpa [andEval, hgin] using hw
            dsimp only [cstep]; rw [hop, andEval, andEval, hgin]
            simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.false_eq_true, ↓reduceIte,
              List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero, List.getD_cons_succ]
            rcases hmem with rfl | rfl
            · rw [hc]; cases c <;> rfl
            · rw [hc]; cases env.getD a (Sum.inl false) with
              | inl ba => cases ba <;> rfl
              | inr ka => cases c <;> rfl
    · cases hgin : g.inputs with
      | nil => simp [cstep, hop, orEval, hgin]
      | cons a tl =>
        cases tl with
        | nil => simp [cstep, hop, orEval, hgin]
        | cons b tl2 =>
          cases tl2 with
          | cons _ _ => simp [hgin] at hlen
          | nil =>
            have hmem : w = a ∨ w = b := by
              dsimp only [reads] at hw; rw [hop] at hw; simpa [orEval, hgin] using hw
            dsimp only [cstep]; rw [hop, orEval, orEval, hgin]
            simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
              List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero, List.getD_cons_succ]
            rcases hmem with rfl | rfl
            · rw [hc]; cases c <;> rfl
            · rw [hc]; cases env.getD a (Sum.inl false) with
              | inl ba => cases ba <;> rfl
              | inr ka => cases c <;> rfl
    · cases hgin : g.inputs with
      | nil => dsimp only [reads] at hw; rw [hop] at hw; simp [notEval, hgin] at hw
      | cons a tl =>
        have hwa : w = a := by dsimp only [reads] at hw; rw [hop] at hw; simpa [notEval, hgin] using hw
        subst hwa; dsimp only [cstep]; rw [hop, notEval, hgin]
        simp only [List.headD_cons, Bool.not_false, ↓reduceIte, List.isEmpty_cons, Bool.false_eq_true,
          List.getD_cons_zero, hc, Sum.elim_inl]
  have cstep_const_out : ∀ (n : ℕ) (env : List (Sum Bool ℕ)) (dgs : List Gate) (g : Gate) (w : ℕ),
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) → g.inputs.length ≤ 2 →
      w ∈ reads g → (g.op.eval [false] || g.op.eval [true, false]) = true →
      env.getD w (Sum.inl false) = Sum.inl true →
      ∃ b : Bool, (cstep n (env, dgs) g).1 = env ++ [Sum.inl b] := by
    intro n env dgs g w hgop hlen hw hornot hwt
    have hop : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hgop
    rcases hop with hop | hop | hop
    · rw [hop] at hornot; simp [andEval] at hornot
    · cases hgin : g.inputs with
      | nil => dsimp only [reads] at hw; rw [hop] at hw; simp [orEval, hgin] at hw
      | cons a tl =>
        cases tl with
        | nil =>
          have hwa : w = a := by dsimp only [reads] at hw; rw [hop] at hw; simpa [orEval, hgin] using hw
          subst hwa; dsimp only [cstep]; rw [hop, orEval, orEval, hgin]
          simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
            List.length_cons, List.length_nil, Nat.reduceBEq, List.getD_cons_zero, hwt]
          exact ⟨true, rfl⟩
        | cons b tl2 =>
          cases tl2 with
          | cons _ _ => simp [hgin] at hlen
          | nil =>
            have hmem : w = a ∨ w = b := by
              dsimp only [reads] at hw; rw [hop] at hw; simpa [orEval, hgin] using hw
            dsimp only [cstep]; rw [hop, orEval, orEval, hgin]
            simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
              List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero, List.getD_cons_succ]
            rcases hmem with rfl | rfl
            · rw [hwt]; exact ⟨true, rfl⟩
            · rw [hwt]; cases env.getD a (Sum.inl false) with
              | inl ba => cases ba <;> exact ⟨true, rfl⟩
              | inr ka => exact ⟨true, rfl⟩
    · cases hgin : g.inputs with
      | nil => dsimp only [reads] at hw; rw [hop] at hw; simp [notEval, hgin] at hw
      | cons a tl =>
        have hwa : w = a := by dsimp only [reads] at hw; rw [hop] at hw; simpa [notEval, hgin] using hw
        subst hwa; dsimp only [cstep]; rw [hop, notEval, hgin]
        simp only [List.headD_cons, Bool.not_false, ↓reduceIte, List.isEmpty_cons, Bool.false_eq_true,
          List.getD_cons_zero, hwt, Sum.elim_inl]
        exact ⟨false, rfl⟩
  have cstep_ind : ∀ (n : ℕ) (gs : List Gate) (env : List (Sum Bool ℕ)) (dgs : List Gate)
      {X : Type} (wC : X → List Bool) (wD : X → List Bool),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ g ∈ dgs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      (∀ x : X, (wC x).length = env.length) →
      (∀ x : X, (wD x).length = n) →
      (∀ i : ℕ, symBd (n + dgs.length) (env.getD i (Sum.inl false))) →
      (∀ (x : X) (i : ℕ), evalSym (dgs.foldl wstep (wD x)) (env.getD i (Sum.inl false)) = (wC x).getD i false) →
      let res := gs.foldl (cstep n) (env, dgs)
      res.1.length = env.length + gs.length ∧
      res.2.length ≤ dgs.length + gs.length ∧
      (∀ g ∈ res.2, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
      (∀ i : ℕ, i < env.length → res.1.getD i (Sum.inl false) = env.getD i (Sum.inl false)) ∧
      (∀ (x : X) (i : ℕ), evalSym (res.2.foldl wstep (wD x)) (res.1.getD i (Sum.inl false)) =
        (gs.foldl wstep (wC x)).getD i false) := by
    intro n gs; induction gs with
    | nil =>
      intro env dgs X wC wD _ hdgs _ _ _ heq
      exact ⟨rfl, le_rfl, hdgs, fun _ _ => rfl, heq⟩
    | cons g rest ih =>
      intro env dgs X wC wD hfg hdgs hwC hwD hbd heq
      have hgf := hfg g List.mem_cons_self
      have hgop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hgf.1
      let st1 := cstep n (env, dgs) g
      have hstep :
          st1.1.length = env.length + 1 ∧
          st1.2.length ≤ dgs.length + 1 ∧
          (∀ g' ∈ st1.2, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
          (∀ i : ℕ, i < env.length → st1.1.getD i (Sum.inl false) = env.getD i (Sum.inl false)) ∧
          (∀ i : ℕ, symBd (n + st1.2.length) (st1.1.getD i (Sum.inl false))) ∧
          (∀ (x : X) (i : ℕ), evalSym (st1.2.foldl wstep (wD x)) (st1.1.getD i (Sum.inl false)) =
            (wstep (wC x) g).getD i false) := by
        have hno : ∀ (v : Sum Bool ℕ),
            symBd (n + dgs.length) v →
            (∀ x : X, evalSym (dgs.foldl wstep (wD x)) v =
              g.op.eval (g.inputs.map fun i => (wC x).getD i false)) →
            (env ++ [v]).length = env.length + 1 ∧
            dgs.length ≤ dgs.length + 1 ∧
            (∀ g' ∈ dgs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
            (∀ i : ℕ, i < env.length → (env ++ [v]).getD i (Sum.inl false) = env.getD i (Sum.inl false)) ∧
            (∀ i : ℕ, symBd (n + dgs.length) ((env ++ [v]).getD i (Sum.inl false))) ∧
            (∀ (x : X) (i : ℕ), evalSym (dgs.foldl wstep (wD x)) ((env ++ [v]).getD i (Sum.inl false)) =
              (wstep (wC x) g).getD i false) := by
          intro v hvbd hveval
          refine ⟨by simp, Nat.le_succ _, hdgs, fun i hi => List.getD_append _ _ _ _ hi, ?_, ?_⟩
          · intro i; by_cases hi : i < env.length
            · rw [List.getD_append _ _ _ _ hi]; exact hbd i
            · by_cases hi2 : i = env.length
              · subst hi2; rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]; exact hvbd
              · rw [List.getD_eq_default _ _ (by simp; omega)]; trivial
          · intro x i; by_cases hi : i < env.length
            · rw [List.getD_append _ _ _ _ hi]; simp only [wstep]
              rw [List.getD_append _ _ _ _ (by rw [hwC x]; exact hi)]; exact heq x i
            · by_cases hi2 : i = env.length
              · subst hi2; rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
                simp only [wstep]; rw [List.getD_append_right _ _ _ _ (by rw [hwC x]), hwC x, Nat.sub_self, List.getD_cons_zero]
                exact hveval x
              · rw [List.getD_eq_default _ _ (by simp; omega)]; simp only [wstep]
                rw [List.getD_eq_default _ _ (by simp [hwC x]; omega)]; rfl
        have hemit : ∀ (ng : Gate),
            ng.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ ng.inputs.length ≤ 2 →
            (∀ x : X,
              ng.op.eval (ng.inputs.map fun i => (dgs.foldl wstep (wD x)).getD i false) =
                g.op.eval (g.inputs.map fun i => (wC x).getD i false)) →
            (env ++ [Sum.inr (n + dgs.length)]).length = env.length + 1 ∧
            (dgs ++ [ng]).length ≤ dgs.length + 1 ∧
            (∀ g' ∈ dgs ++ [ng], g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) ∧
            (∀ i : ℕ, i < env.length → (env ++ [Sum.inr (n + dgs.length)]).getD i (Sum.inl false) = env.getD i (Sum.inl false)) ∧
            (∀ i : ℕ, symBd (n + (dgs ++ [ng]).length) ((env ++ [Sum.inr (n + dgs.length)]).getD i (Sum.inl false))) ∧
            (∀ (x : X) (i : ℕ), evalSym ((dgs ++ [ng]).foldl wstep (wD x))
                ((env ++ [Sum.inr (n + dgs.length)]).getD i (Sum.inl false)) =
              (wstep (wC x) g).getD i false) := by
          intro ng hng hngeval
          refine ⟨by simp, by simp, ?_, fun i hi => List.getD_append _ _ _ _ hi, ?_, ?_⟩
          · intro g' hg'; rcases List.mem_append.mp hg' with hg' | hg'
            · exact hdgs g' hg'
            · simp only [List.mem_singleton] at hg'; subst hg'; exact hng
          · intro i; by_cases hi : i < env.length
            · rw [List.getD_append _ _ _ _ hi]; have hbi := hbd i
              cases hvi : env.getD i (Sum.inl false) with
              | inl _ => trivial
              | inr k => rw [hvi] at hbi; simp only [symBd, Sum.elim_inr, List.length_append, List.length_singleton] at hbi ⊢; omega
            · by_cases hi2 : i = env.length
              · subst hi2; rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]; simp [symBd]
              · rw [List.getD_eq_default _ _ (by simp; omega)]; trivial
          · intro x i
            have hfold : (dgs ++ [ng]).foldl wstep (wD x) = wstep (dgs.foldl wstep (wD x)) ng := by rw [List.foldl_append]; rfl
            have hdwlen : (dgs.foldl wstep (wD x)).length = n + dgs.length := by rw [wlen, hwD x]
            by_cases hi : i < env.length
            · rw [List.getD_append _ _ _ _ hi]; simp only [wstep]
              rw [List.getD_append _ _ _ _ (by rw [hwC x]; exact hi), ← heq x i, hfold]
              have hbi := hbd i; cases hvi : env.getD i (Sum.inl false) with
              | inl _ => rfl
              | inr k =>
                rw [hvi] at hbi; simp only [symBd, Sum.elim_inr] at hbi; simp only [evalSym, Sum.elim_inr, wstep]
                exact List.getD_append _ _ _ _ (by rw [hdwlen]; exact hbi)
            · by_cases hi2 : i = env.length
              · subst hi2; rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
                simp only [wstep]; rw [List.getD_append_right _ _ _ _ (by rw [hwC x]), hwC x, Nat.sub_self, List.getD_cons_zero]
                simp only [evalSym, Sum.elim_inr, hfold, wstep]
                rw [List.getD_append_right _ _ _ _ (by rw [hdwlen]), hdwlen, Nat.sub_self, List.getD_cons_zero]
                exact hngeval x
              · rw [List.getD_eq_default _ _ (by simp; omega)]; simp only [wstep]
                rw [List.getD_eq_default _ _ (by simp [hwC x]; omega)]; rfl
        rcases hgop with hop | hop | hop
        · have hlen2 : g.inputs.length ≤ 2 := hgf.2
          cases hgin : g.inputs with
          | nil =>
            have hst : st1 = (env ++ [Sum.inl true], dgs) := by dsimp only [st1, cstep]; rw [hop, andEval, andEval, hgin]; rfl
            rw [hst]; exact hno (Sum.inl true) trivial (fun x => by simp [hop, hgin, andEval, evalSym])
          | cons a tl =>
            cases tl with
            | nil =>
              have hst : st1 = (env ++ [env.getD a (Sum.inl false)], dgs) := by dsimp only [st1, cstep]; rw [hop, andEval, andEval, hgin]; rfl
              rw [hst]; exact hno (env.getD a (Sum.inl false)) (hbd a)
                (fun x => by simp only [hop, hgin, List.map_cons, List.map_nil, andEval, List.all_cons, List.all_nil, id_eq, Bool.and_true]; exact heq x a)
            | cons b tl2 =>
              cases tl2 with
              | cons _ _ => simp [hgin] at hlen2
              | nil =>
                cases ha : env.getD a (Sum.inl false) with
                | inl ba =>
                  cases ba with
                  | false =>
                    have hst : st1 = (env ++ [Sum.inl false], dgs) := by
                      dsimp only [st1, cstep]; rw [hop, andEval, andEval, hgin]
                      simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.false_eq_true, ↓reduceIte,
                        List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero, ha, Sum.elim_inl]
                    rw [hst]; exact hno (Sum.inl false) trivial (fun x => by
                      have h1 := heq x a; rw [ha] at h1; simp only [evalSym, Sum.elim_inl, id_eq] at h1
                      simp only [hop, hgin, List.map_cons, List.map_nil, andEval, List.all_cons, List.all_nil, id_eq, evalSym, Sum.elim_inl]
                      rw [← h1]; rfl)
                  | true =>
                    have hst : st1 = (env ++ [env.getD b (Sum.inl false)], dgs) := by
                      dsimp only [st1, cstep]; rw [hop, andEval, andEval, hgin]
                      simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.false_eq_true, ↓reduceIte,
                        List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero, List.getD_cons_succ, ha, Sum.elim_inl]
                    rw [hst]; exact hno (env.getD b (Sum.inl false)) (hbd b) (fun x => by
                      have h1 := heq x a; rw [ha] at h1; simp only [evalSym, Sum.elim_inl, id_eq] at h1
                      simp only [hop, hgin, List.map_cons, List.map_nil, andEval, List.all_cons, List.all_nil, id_eq]
                      rw [← h1, Bool.true_and, Bool.and_true]; exact heq x b)
                | inr ka =>
                  cases hb : env.getD b (Sum.inl false) with
                  | inl bb =>
                    cases bb with
                    | false =>
                      have hst : st1 = (env ++ [Sum.inl false], dgs) := by
                        dsimp only [st1, cstep]; rw [hop, andEval, andEval, hgin]
                        simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.false_eq_true, ↓reduceIte,
                          List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero, List.getD_cons_succ, ha, hb, Sum.elim_inr, Sum.elim_inl]
                      rw [hst]; exact hno (Sum.inl false) trivial (fun x => by
                        have h2 := heq x b; rw [hb] at h2; simp only [evalSym, Sum.elim_inl, id_eq] at h2
                        simp only [hop, hgin, List.map_cons, List.map_nil, andEval, List.all_cons, List.all_nil, id_eq, evalSym, Sum.elim_inl]
                        rw [← h2]; simp)
                    | true =>
                      have hst : st1 = (env ++ [Sum.inr ka], dgs) := by
                        dsimp only [st1, cstep]; rw [hop, andEval, andEval, hgin]
                        simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.false_eq_true, ↓reduceIte,
                          List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero, List.getD_cons_succ, ha, hb, Sum.elim_inr, Sum.elim_inl]
                      rw [hst]; exact hno (Sum.inr ka) (by have h := hbd a; rw [ha] at h; exact h) (fun x => by
                        have h1 := heq x a; have h2 := heq x b; rw [ha] at h1; rw [hb] at h2
                        simp only [evalSym, Sum.elim_inl, Sum.elim_inr, id_eq] at h1 h2
                        simp only [hop, hgin, List.map_cons, List.map_nil, andEval, List.all_cons, List.all_nil, id_eq, evalSym, Sum.elim_inr]
                        rw [← h1, ← h2]; simp)
                  | inr kb =>
                    by_cases hkeq : ka = kb
                    · subst hkeq
                      have hst : st1 = (env ++ [Sum.inr ka], dgs) := by
                        dsimp only [st1, cstep]; rw [hop, andEval, andEval, hgin]
                        simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.false_eq_true, ↓reduceIte,
                          List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero, List.getD_cons_succ, ha, hb, Sum.elim_inr, beq_self_eq_true]
                      rw [hst]; exact hno (Sum.inr ka) (by have h := hbd a; rw [ha] at h; exact h) (fun x => by
                        have h1 := heq x a; have h2 := heq x b; rw [ha] at h1; rw [hb] at h2
                        simp only [evalSym, Sum.elim_inr] at h1 h2
                        simp only [hop, hgin, List.map_cons, List.map_nil, andEval, List.all_cons, List.all_nil, id_eq, evalSym, Sum.elim_inr]
                        rw [← h1, ← h2]; simp)
                    · have hst : st1 = (env ++ [Sum.inr (n + dgs.length)], dgs ++ [⟨GateOp.and, [ka, kb]⟩]) := by
                        dsimp only [st1, cstep]; rw [hop, andEval, andEval, hgin]
                        simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.false_eq_true, ↓reduceIte,
                          List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero, List.getD_cons_succ, ha, hb, Sum.elim_inr, beq_iff_eq, hkeq]
                      rw [hst]; exact hemit ⟨GateOp.and, [ka, kb]⟩ ⟨Or.inl rfl, by simp⟩ (fun x => by
                        have h1 := heq x a; have h2 := heq x b; rw [ha] at h1; rw [hb] at h2
                        simp only [evalSym, Sum.elim_inr] at h1 h2
                        simp only [hop, hgin, List.map_cons, List.map_nil, andEval, List.all_cons, List.all_nil, id_eq]
                        rw [h1, h2])
        · have hlen2 : g.inputs.length ≤ 2 := hgf.2
          cases hgin : g.inputs with
          | nil =>
            have hst : st1 = (env ++ [Sum.inl false], dgs) := by dsimp only [st1, cstep]; rw [hop, orEval, orEval, hgin]; rfl
            rw [hst]; exact hno (Sum.inl false) trivial (fun x => by simp [hop, hgin, orEval, evalSym])
          | cons a tl =>
            cases tl with
            | nil =>
              have hst : st1 = (env ++ [env.getD a (Sum.inl false)], dgs) := by dsimp only [st1, cstep]; rw [hop, orEval, orEval, hgin]; rfl
              rw [hst]; exact hno (env.getD a (Sum.inl false)) (hbd a)
                (fun x => by simp only [hop, hgin, List.map_cons, List.map_nil, orEval, List.any_cons, List.any_nil, id_eq, Bool.or_false]; exact heq x a)
            | cons b tl2 =>
              cases tl2 with
              | cons _ _ => simp [hgin] at hlen2
              | nil =>
                cases ha : env.getD a (Sum.inl false) with
                | inl ba =>
                  cases ba with
                  | true =>
                    have hst : st1 = (env ++ [Sum.inl true], dgs) := by
                      dsimp only [st1, cstep]; rw [hop, orEval, orEval, hgin]
                      simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
                        List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero, ha, Sum.elim_inl]
                    rw [hst]; exact hno (Sum.inl true) trivial (fun x => by
                      have h1 := heq x a; rw [ha] at h1; simp only [evalSym, Sum.elim_inl, id_eq] at h1
                      simp only [hop, hgin, List.map_cons, List.map_nil, orEval, List.any_cons, List.any_nil, id_eq, evalSym, Sum.elim_inl]
                      rw [← h1]; rfl)
                  | false =>
                    have hst : st1 = (env ++ [env.getD b (Sum.inl false)], dgs) := by
                      dsimp only [st1, cstep]; rw [hop, orEval, orEval, hgin]
                      simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
                        List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero, List.getD_cons_succ, ha, Sum.elim_inl]
                    rw [hst]; exact hno (env.getD b (Sum.inl false)) (hbd b) (fun x => by
                      have h1 := heq x a; rw [ha] at h1; simp only [evalSym, Sum.elim_inl, id_eq] at h1
                      simp only [hop, hgin, List.map_cons, List.map_nil, orEval, List.any_cons, List.any_nil, id_eq]
                      rw [← h1, Bool.false_or, Bool.or_false]; exact heq x b)
                | inr ka =>
                  cases hb : env.getD b (Sum.inl false) with
                  | inl bb =>
                    cases bb with
                    | true =>
                      have hst : st1 = (env ++ [Sum.inl true], dgs) := by
                        dsimp only [st1, cstep]; rw [hop, orEval, orEval, hgin]
                        simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
                          List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero, List.getD_cons_succ, ha, hb, Sum.elim_inr, Sum.elim_inl]
                      rw [hst]; exact hno (Sum.inl true) trivial (fun x => by
                        have h2 := heq x b; rw [hb] at h2; simp only [evalSym, Sum.elim_inl, id_eq] at h2
                        simp only [hop, hgin, List.map_cons, List.map_nil, orEval, List.any_cons, List.any_nil, id_eq, evalSym, Sum.elim_inl]
                        rw [← h2]; simp)
                    | false =>
                      have hst : st1 = (env ++ [Sum.inr ka], dgs) := by
                        dsimp only [st1, cstep]; rw [hop, orEval, orEval, hgin]
                        simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
                          List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero, List.getD_cons_succ, ha, hb, Sum.elim_inr, Sum.elim_inl]
                      rw [hst]; exact hno (Sum.inr ka) (by have h := hbd a; rw [ha] at h; exact h) (fun x => by
                        have h1 := heq x a; have h2 := heq x b; rw [ha] at h1; rw [hb] at h2
                        simp only [evalSym, Sum.elim_inl, Sum.elim_inr, id_eq] at h1 h2
                        simp only [hop, hgin, List.map_cons, List.map_nil, orEval, List.any_cons, List.any_nil, id_eq, evalSym, Sum.elim_inr]
                        rw [← h1, ← h2]; simp)
                  | inr kb =>
                    by_cases hkeq : ka = kb
                    · subst hkeq
                      have hst : st1 = (env ++ [Sum.inr ka], dgs) := by
                        dsimp only [st1, cstep]; rw [hop, orEval, orEval, hgin]
                        simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
                          List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero, List.getD_cons_succ, ha, hb, Sum.elim_inr, beq_self_eq_true]
                      rw [hst]; exact hno (Sum.inr ka) (by have h := hbd a; rw [ha] at h; exact h) (fun x => by
                        have h1 := heq x a; have h2 := heq x b; rw [ha] at h1; rw [hb] at h2
                        simp only [evalSym, Sum.elim_inr] at h1 h2
                        simp only [hop, hgin, List.map_cons, List.map_nil, orEval, List.any_cons, List.any_nil, id_eq, evalSym, Sum.elim_inr]
                        rw [← h1, ← h2]; simp)
                    · have hst : st1 = (env ++ [Sum.inr (n + dgs.length)], dgs ++ [⟨GateOp.or, [ka, kb]⟩]) := by
                        dsimp only [st1, cstep]; rw [hop, orEval, orEval, hgin]
                        simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
                          List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero, List.getD_cons_succ, ha, hb, Sum.elim_inr, beq_iff_eq, hkeq]
                      rw [hst]; exact hemit ⟨GateOp.or, [ka, kb]⟩ ⟨Or.inr (Or.inl rfl), by simp⟩ (fun x => by
                        have h1 := heq x a; have h2 := heq x b; rw [ha] at h1; rw [hb] at h2
                        simp only [evalSym, Sum.elim_inr] at h1 h2
                        simp only [hop, hgin, List.map_cons, List.map_nil, orEval, List.any_cons, List.any_nil, id_eq]
                        rw [h1, h2])
        · cases hgin : g.inputs with
          | nil =>
            have hst : st1 = (env ++ [Sum.inl true], dgs) := by dsimp only [st1, cstep]; rw [hop, notEval, hgin]; rfl
            rw [hst]; exact hno (Sum.inl true) trivial (fun x => by simp [hop, hgin, notEval, evalSym])
          | cons a tl =>
            cases ha : env.getD a (Sum.inl false) with
            | inl ba =>
              have hst : st1 = (env ++ [Sum.inl (!ba)], dgs) := by
                dsimp only [st1, cstep]; rw [hop, notEval, hgin]
                simp only [List.headD_cons, Bool.not_false, ↓reduceIte, List.isEmpty_cons, Bool.false_eq_true,
                  List.getD_cons_zero, ha, Sum.elim_inl]
              rw [hst]; exact hno (Sum.inl (!ba)) trivial (fun x => by
                have h1 := heq x a; rw [ha] at h1; simp only [evalSym, Sum.elim_inl, id_eq] at h1
                simp only [hop, hgin, List.map_cons, notEval, List.headD_cons, evalSym, Sum.elim_inl, id_eq]
                rw [← h1])
            | inr ka =>
              have hst : st1 = (env ++ [Sum.inr (n + dgs.length)], dgs ++ [⟨GateOp.not, [ka]⟩]) := by
                dsimp only [st1, cstep]; rw [hop, notEval, hgin]
                simp only [List.headD_cons, Bool.not_false, ↓reduceIte, List.isEmpty_cons, Bool.false_eq_true,
                  List.getD_cons_zero, ha, Sum.elim_inr]
              rw [hst]; exact hemit ⟨GateOp.not, [ka]⟩ ⟨Or.inr (Or.inr rfl), by simp⟩ (fun x => by
                have h1 := heq x a; rw [ha] at h1; simp only [evalSym, Sum.elim_inr] at h1
                simp only [hop, hgin, List.map_cons, List.map_nil, notEval, List.headD_cons]; rw [h1])
      obtain ⟨rlen, rsz, rfan, rkeep, req⟩ := ih st1.1 st1.2 (fun x => wstep (wC x) g) wD
        (fun g' hg' => hfg g' (List.mem_cons_of_mem _ hg')) hstep.2.2.1
        (fun x => by simp [wstep, hwC x]; exact hstep.1.symm) hwD hstep.2.2.2.2.1 hstep.2.2.2.2.2
      rw [List.foldl_cons]; change (rest.foldl (cstep n) (st1.1, st1.2)).1.length = _ ∧ _
      refine ⟨by rw [rlen, hstep.1, List.length_cons]; omega, ?_, rfan, ?_, req⟩
      · change (rest.foldl (cstep n) (st1.1, st1.2)).2.length ≤ dgs.length + (g :: rest).length
        rw [List.length_cons]; omega
      · intro i hi; rw [rkeep i (by omega), hstep.2.2.2.1 i hi]

  -- Relabel inputs of a circuit via ρ : Fin n → Fin m
  have relabelC : ∀ {n m : ℕ} (ρ : Fin n → Fin m) (C : Circuit), FanInTwo C →
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧
        (∀ x : Fin m → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ ρ))) := by
    intro n m ρ C hfan
    let ext (i : ℕ) : ℕ := if h : i < n then (ρ ⟨i, h⟩).val else i - n + m
    let rGate (g : Gate) : Gate := ⟨g.op, g.inputs.map ext⟩
    let D : Circuit := ⟨C.gates.map rGate, ext C.output⟩
    let Rel (W W' : List Bool) : Prop :=
      n ≤ W.length ∧ W'.length + n = W.length + m ∧ ∀ w, W'.getD (ext w) false = W.getD w false
    have hstep : ∀ (W W' : List Bool) (g : Gate), Rel W W' → Rel (wstep W g) (wstep W' (rGate g)) := by
      intro W W' g hrel
      obtain ⟨h1, h2, h3⟩ := hrel
      have hv : (rGate g).op.eval ((rGate g).inputs.map fun i => W'.getD i false) =
          g.op.eval (g.inputs.map fun i => W.getD i false) := by
        simp only [rGate, List.map_map, Function.comp_def]
        congr 1; apply List.map_congr_left; intro a _; exact h3 a
      refine ⟨by simp [wstep]; omega, by simp [wstep]; omega, fun w => ?_⟩
      simp only [wstep, hv]
      rcases Nat.lt_trichotomy w W.length with hw | hw | hw
      · have hlt : ext w < W'.length := by
          dsimp only [ext]; split_ifs with h
          · have := (ρ ⟨w, h⟩).isLt; omega
          · omega
        rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]; exact h3 w
      · have he : ext w = W'.length := by dsimp only [ext]; split_ifs with h <;> omega
        rw [he, hw, List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ le_rfl]; simp
      · have hge : W'.length + 1 ≤ ext w := by
          dsimp only [ext]; split_ifs with h
          · have := (ρ ⟨w, h⟩).isLt; omega
          · omega
        rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have hrun : ∀ (gs : List Gate) (W W' : List Bool), Rel W W' →
        Rel (gs.foldl wstep W) ((gs.map rGate).foldl wstep W') := by
      intro gs; induction gs with
      | nil => intro W W' h; exact h
      | cons g gs ih => intro W W' h; exact ih _ _ (hstep W W' g h)
    have hinit : ∀ x : Fin m → Bool, Rel (List.ofFn (x ∘ ρ)) (List.ofFn x) := by
      intro x; refine ⟨by simp, by simp; omega, fun w => ?_⟩
      dsimp only [ext]; split_ifs with hw
      · rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simp; exact hw)]; simp
      · rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]
    refine ⟨D, ?_, ?_, ?_⟩
    · intro g hg; obtain ⟨g0, hm, rfl⟩ := List.mem_map.mp hg
      exact ⟨(hfan g0 hm).1, by simpa [rGate] using (hfan g0 hm).2⟩
    · change (C.gates.map rGate).length = C.gates.length; simp
    · intro x; exact (hrun C.gates _ _ (hinit x)).2.2 C.output

  -- Helper: pin one input of a circuit when target depends on v and restricted target is non-constant
  have pinCompile : ∀ {n : ℕ} (C : Circuit) (v : Fin (n + 1)) (b : Bool)
      (f : (Fin (n + 1) → Bool) → Bool),
      FanInTwo C →
      (∀ x : Fin (n + 1) → Bool, C.eval (List.ofFn x) = f x) →
      (∃ x : Fin (n + 1) → Bool, f (Function.update x v false) ≠ f (Function.update x v true)) →
      (∃ x y : Fin (n + 1) → Bool, f (Function.update x v b) ≠ f (Function.update y v b)) →
      ∃ D : Circuit, FanInTwo D ∧ D.size + 1 ≤ C.size ∧
        ∀ y : Fin n → Bool, D.eval (List.ofFn y) = f (v.insertNth b y) := by
    intro n C v b f hfan hcorr hdep hnc
    have hasRead : ∃ g ∈ C.gates, v.val ∈ reads g := by
      by_contra hno; push Not at hno; obtain ⟨x0, hdiff⟩ := hdep
      let xF := Function.update x0 v false; let xT := Function.update x0 v true
      have hout : C.output ≠ v.val := by
        intro ho; obtain ⟨y1, y2, hne⟩ := hnc
        have e1 : C.eval (List.ofFn (Function.update y1 v b)) = b := by
          change (C.gates.foldl wstep (List.ofFn (Function.update y1 v b))).getD C.output false = b
          rw [ho, wpres _ _ _ (by rw [List.length_ofFn]; exact v.isLt),
            List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact v.isLt), List.getElem_ofFn]; simp
        have e2 : C.eval (List.ofFn (Function.update y2 v b)) = b := by
          change (C.gates.foldl wstep (List.ofFn (Function.update y2 v b))).getD C.output false = b
          rw [ho, wpres _ _ _ (by rw [List.length_ofFn]; exact v.isLt),
            List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact v.isLt), List.getElem_ofFn]; simp
        rw [hcorr] at e1; rw [hcorr] at e2; exact hne (e1.trans e2.symm)
      have hprop : ∀ (gs : List Gate) (w1 w2 : List Bool),
          (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
          (∀ g ∈ gs, v.val ∉ reads g) →
          w1.length = w2.length → n + 1 ≤ w1.length →
          (∀ i, i ≠ v.val → w1.getD i false = w2.getD i false) →
          ∀ i, i ≠ v.val → (gs.foldl wstep w1).getD i false = (gs.foldl wstep w2).getD i false := by
        intro gs; induction gs with
        | nil => intro w1 w2 _ _ _ _ hag i hi; exact hag i hi
        | cons g gs ih =>
          intro w1 w2 hfg hrg hlen hn1 hag
          have hgf := hfg g List.mem_cons_self; have hgr := hrg g List.mem_cons_self
          have hgop : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
            simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hgf.1
          have hev : g.op.eval (g.inputs.map fun i => w1.getD i false) =
              g.op.eval (g.inputs.map fun i => w2.getD i false) := by
            rcases hgop with hop | hop | hop
            · have hm : v.val ∉ g.inputs := by dsimp only [reads] at hgr; rw [hop] at hgr; simpa [andEval] using hgr
              rw [hop]; congr 1; apply List.map_congr_left; intro a ha; exact hag a (fun e => hm (e ▸ ha))
            · have hm : v.val ∉ g.inputs := by dsimp only [reads] at hgr; rw [hop] at hgr; simpa [orEval] using hgr
              rw [hop]; congr 1; apply List.map_congr_left; intro a ha; exact hag a (fun e => hm (e ▸ ha))
            · rw [hop]; cases hgin : g.inputs with
              | nil => rfl
              | cons a tl =>
                have hne : a ≠ v.val := by intro e; apply hgr; simp [reads, hop, notEval, hgin, e]
                simp only [List.map_cons, notEval, List.headD_cons, hag a hne]
          apply ih (wstep w1 g) (wstep w2 g) (fun g' hg' => hfg g' (List.mem_cons_of_mem _ hg'))
            (fun g' hg' => hrg g' (List.mem_cons_of_mem _ hg')) (by simp [wstep, hlen]) (by simp [wstep]; omega)
          intro i hi; simp only [wstep]
          by_cases hlt : i < w1.length
          · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (hlen ▸ hlt)]; exact hag i hi
          · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_lt hlt),
                List.getD_append_right _ _ _ _ (hlen ▸ Nat.le_of_not_lt hlt), hlen, hev]
      have hinit : ∀ i, i ≠ v.val → (List.ofFn xF).getD i false = (List.ofFn xT).getD i false := by
        intro i hi
        by_cases hlt : i < n + 1
        · rw [List.getD_eq_getElem _ _ (List.length_ofFn.symm ▸ hlt), List.getD_eq_getElem _ _ (List.length_ofFn.symm ▸ hlt)]
          simp only [List.getElem_ofFn, xF, xT]
          have hne : (⟨i, hlt⟩ : Fin (n + 1)) ≠ v := fun e => hi (congrArg Fin.val e)
          simp [Function.update_of_ne hne]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      have heq := hprop C.gates (List.ofFn xF) (List.ofFn xT) hfan hno (by simp) (by simp) hinit C.output hout
      change C.eval (List.ofFn xF) = C.eval (List.ofFn xT) at heq
      rw [hcorr xF, hcorr xT] at heq; exact hdiff heq
    let init : List (Sum Bool ℕ) := List.ofFn fun i : Fin (n + 1) =>
      if i = v then Sum.inl b else Sum.inr (if i.val < v.val then i.val else i.val - 1)
    have hinit_bd : ∀ i : ℕ, symBd (n + 0) (init.getD i (Sum.inl false)) := by
      intro i; by_cases hi : i < n + 1
      · rw [List.getD_eq_getElem _ _ (by simpa [init] using hi)]; simp only [init, List.getElem_ofFn]
        by_cases h1 : (⟨i, hi⟩ : Fin (n + 1)) = v
        · simp [h1, symBd]
        · simp only [h1, ↓reduceIte]
          split_ifs with h2
          · simp [symBd]; omega
          · simp [symBd]; have hlt := (⟨i, hi⟩ : Fin (n + 1)).isLt
            have hne : i ≠ v.val := fun e => h1 (Fin.ext e); omega
      · rw [List.getD_eq_default _ _ (by simp [init]; omega)]; trivial
    have hinit_eq : ∀ (y : Fin n → Bool) (i : ℕ),
        evalSym (([] : List Gate).foldl wstep (List.ofFn y)) (init.getD i (Sum.inl false)) =
          (List.ofFn (v.insertNth b y)).getD i false := by
      intro y i; by_cases hi : i < n + 1
      · rw [List.getD_eq_getElem _ _ (by simp [init, hi]), List.getD_eq_getElem _ _ (List.length_ofFn.symm ▸ hi)]
        simp only [init, List.getElem_ofFn]
        by_cases h1 : (⟨i, hi⟩ : Fin (n + 1)) = v
        · rw [if_pos h1, ← h1]; simp [evalSym]
        · rw [if_neg h1]; have hne : i ≠ v.val := fun e => h1 (Fin.ext e)
          by_cases h2 : i < v.val
          · rw [if_pos h2]; simp only [evalSym, List.foldl_nil, Sum.elim_inr]; have hj : i < n := by have := v.isLt; omega
            rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hj), List.getElem_ofFn]
            have hltv : (⟨i, hi⟩ : Fin (n + 1)) < v := Fin.mk_lt_mk.mpr h2
            rw [Fin.insertNth_apply_below (α := fun _ => Bool) hltv b y]; simp; rfl
          · rw [if_neg h2]; simp only [evalSym, List.foldl_nil, Sum.elim_inr]; have hi1 : i - 1 < n := by have := v.isLt; omega
            rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact hi1), List.getElem_ofFn]
            have hgtv : v < (⟨i, hi⟩ : Fin (n + 1)) := Fin.mk_lt_mk.mpr (by omega)
            rw [Fin.insertNth_apply_above (α := fun _ => Bool) hgtv b y]; simp; rfl
      · rw [List.getD_eq_default _ _ (by simp [init]; omega), List.getD_eq_default _ _ (by simp; omega)]; rfl
    have hc := cstep_ind n C.gates init [] (fun y : Fin n → Bool => List.ofFn (v.insertNth b y))
      (fun y => List.ofFn y) hfan (fun _ h => by cases h) (fun _ => by simp [init]) (fun _ => by simp)
      hinit_bd hinit_eq
    have hdrop : ∀ (gs : List Gate) (env : List (Sum Bool ℕ)) (dgs : List Gate),
        (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        v.val < env.length → env.getD v.val (Sum.inl false) = Sum.inl b →
        (∃ g ∈ gs, v.val ∈ reads g) →
        (gs.foldl (cstep n) (env, dgs)).2.length + 1 ≤ dgs.length + gs.length := by
      intro gs; induction gs with
      | nil => intro _ _ _ _ _ hEx; obtain ⟨_, hm, _⟩ := hEx; cases hm
      | cons g rest ih =>
        intro env dgs hfg hvl hv hEx
        obtain ⟨g0, hg0, hread0⟩ := hEx
        have hgf := hfg g List.mem_cons_self
        obtain ⟨x_new, hst_env⟩ := cstep_env_pres n env dgs g
        have hvl' : v.val < (cstep n (env, dgs) g).1.length := by rw [hst_env]; simp; omega
        have hv' : (cstep n (env, dgs) g).1.getD v.val (Sum.inl false) = Sum.inl b := by
          rw [hst_env, List.getD_append _ _ _ _ hvl]; exact hv
        rcases List.mem_cons.mp hg0 with h_eq | hmem
        · rw [h_eq] at hread0
          have hno := cstep_no_emit n env dgs g hgf.1 hgf.2 ⟨v.val, hread0, b, hv⟩
          have h1 := cstep_fold_le n rest (cstep n (env, dgs) g)
          rw [List.foldl_cons, hno] at *; simp only [List.length_cons] at *; omega
        · rcases hst : cstep n (env, dgs) g with ⟨env1, dgs1⟩
          have hvl1 : v.val < env1.length := by simpa [hst] using hvl'
          have hv1 : env1.getD v.val (Sum.inl false) = Sum.inl b := by simpa [hst] using hv'
          have h1 := ih env1 dgs1 (fun a ha => hfg a (List.mem_cons_of_mem _ ha)) hvl1 hv1 ⟨g0, hmem, hread0⟩
          have h2 := cstep_dlen_le n env dgs g
          rw [hst] at h2; rw [List.foldl_cons, hst]; simp only [List.length_cons] at *; omega
    have hdropped := hdrop C.gates init [] hfan (by dsimp only [init]; rw [List.length_ofFn]; exact v.isLt) (by
      rw [List.getD_eq_getElem _ _ (by dsimp only [init]; rw [List.length_ofFn]; exact v.isLt)]
      simp only [init, List.getElem_ofFn, Fin.eta, ↓reduceIte]) hasRead
    let res := C.gates.foldl (cstep n) (init, [])
    have hout_not_const : ∀ b0 : Bool, res.1.getD C.output (Sum.inl false) ≠ Sum.inl b0 := by
      intro b0 heq
      obtain ⟨y1, y2, hne⟩ := hnc
      have hupd : ∀ x : Fin (n + 1) → Bool, v.insertNth b (x ∘ v.succAbove) = Function.update x v b := by
        intro x; funext i; refine Fin.succAboveCases v ?_ ?_ i
        · simp
        · intro j; simp [Function.update_of_ne (Fin.succAbove_ne v j)]
      have r1 := hc.2.2.2.2 (y1 ∘ v.succAbove) C.output
      have r2 := hc.2.2.2.2 (y2 ∘ v.succAbove) C.output
      rw [heq] at r1 r2; simp only [evalSym, Sum.elim_inl, id_eq] at r1 r2
      change b0 = C.eval (List.ofFn (v.insertNth b (y1 ∘ v.succAbove))) at r1
      change b0 = C.eval (List.ofFn (v.insertNth b (y2 ∘ v.succAbove))) at r2
      rw [hupd y1, hcorr] at r1; rw [hupd y2, hcorr] at r2
      exact hne (r1.symm.trans r2)
    cases ho : res.1.getD C.output (Sum.inl false) with
    | inl b0 => exact False.elim (hout_not_const b0 ho)
    | inr ko =>
      refine ⟨⟨res.2, ko⟩, hc.2.2.1, ?_, fun y => ?_⟩
      · change res.2.length + 1 ≤ C.gates.length; simp only [List.length_nil, Nat.zero_add] at hdropped; exact hdropped
      · have r := hc.2.2.2.2 y C.output
        rw [ho] at r; simp only [evalSym, Sum.elim_inr] at r
        exact r.trans (hcorr (v.insertNth b y))

  -- Lower bounds for f10 (8 vars) and f11 (9 vars) from c6
  let f10 : (Fin 8 → Bool) → Bool := fun x =>
    x 2 || x 3 || (x 0 && x 1) || (x 1 && x 6) || (x 6 && x 4) || (x 4 && x 7) || (x 7 && x 5) || (x 5 && x 0)
  let f11 : (Fin 9 → Bool) → Bool := fun x =>
    x 0 || x 3 || x 4 || (x 1 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 8) || (x 8 && x 6) || (x 6 && x 1)
  have hf10_lb : ¬ HasCircuitSize 8 f10 9 := by
    rintro ⟨D, hD, hsz, hev⟩
    have dep2 : ∃ x : Fin 8 → Bool, f10 (Function.update x 2 false) ≠ f10 (Function.update x 2 true) :=
      ⟨fun _ => false, by decide⟩
    have nc2 : ∃ x y : Fin 8 → Bool, f10 (Function.update x 2 false) ≠ f10 (Function.update y 2 false) :=
      ⟨fun _ => false, fun _ => true, by decide⟩
    obtain ⟨D1, hD1, hsz1, hev1⟩ := pinCompile D 2 false f10 hD hev dep2 nc2
    let f7 : (Fin 7 → Bool) → Bool := fun x =>
      x 2 || (x 0 && x 1) || (x 1 && x 5) || (x 5 && x 3) || (x 3 && x 6) || (x 6 && x 4) || (x 4 && x 0)
    have h7eq : ∀ y : Fin 7 → Bool, f10 ((2 : Fin 8).insertNth false y) = f7 y := by decide +kernel
    have hev1' : ∀ y : Fin 7 → Bool, D1.eval (List.ofFn y) = f7 y := fun y => (hev1 y).trans (h7eq y)
    have dep2' : ∃ x : Fin 7 → Bool, f7 (Function.update x 2 false) ≠ f7 (Function.update x 2 true) :=
      ⟨fun _ => false, by decide⟩
    have nc2' : ∃ x y : Fin 7 → Bool, f7 (Function.update x 2 false) ≠ f7 (Function.update y 2 false) :=
      ⟨fun _ => false, fun _ => true, by decide⟩
    obtain ⟨D2, hD2, hsz2, hev2⟩ := pinCompile D1 2 false f7 hD1 hev1' dep2' nc2'
    let ρ : Fin 6 → Fin 6 := ![0, 1, 3, 5, 2, 4]
    obtain ⟨D3, hD3, hsz3, hev3⟩ := relabelC ρ D2 hD2
    have h6eq : ∀ x : Fin 6 → Bool, f7 ((2 : Fin 7).insertNth false (x ∘ ρ)) = C6 x := by decide +kernel
    apply c6
    exact ⟨D3, hD3, by omega, fun x => (hev3 x).trans ((hev2 (x ∘ ρ)).trans (h6eq x))⟩
  have hf11_lb : ¬ HasCircuitSize 9 f11 10 := by
    rintro ⟨D, hD, hsz, hev⟩
    have dep0 : ∃ x : Fin 9 → Bool, f11 (Function.update x 0 false) ≠ f11 (Function.update x 0 true) :=
      ⟨fun _ => false, by decide⟩
    have nc0 : ∃ x y : Fin 9 → Bool, f11 (Function.update x 0 false) ≠ f11 (Function.update y 0 false) :=
      ⟨fun _ => false, fun _ => true, by decide⟩
    obtain ⟨D1, hD1, hsz1, hev1⟩ := pinCompile D 0 false f11 hD hev dep0 nc0
    have h10eq : ∀ y : Fin 8 → Bool, f11 ((0 : Fin 9).insertNth false y) = f10 y := by decide +kernel
    exact hf10_lb ⟨D1, hD1, by omega, fun y => (hev1 y).trans (h10eq y)⟩

  -- Gate elimination bounds on C (for x0=1, x1=1, and (x0=1, x1=0))
  have cstep_drop_killed : ∀ (C : Circuit) (v : Fin 10) (pre gs : List Gate) (env : List (Sum Bool ℕ)) (dgs : List Gate),
      FanInTwo C → C.gates = pre ++ gs → env.length = 10 + pre.length →
      env.getD v.val (Sum.inl false) = Sum.inl true →
      (∀ k < pre.length, ∀ h : Gate, pre[k]? = some h → (reads h).contains v.val →
        (h.op.eval [false] || h.op.eval [true, false]) = true →
        ∃ b : Bool, env.getD (10 + k) (Sum.inl false) = Sum.inl b) →
      (gs.foldl (cstep 9) (env, dgs)).2.length + gs.countP (fun g =>
        (reads g).any fun k => k == v.val || (10 ≤ k && (C.gates[k - 10]?).any fun h =>
          (reads h).contains v.val && (h.op.eval [false] || h.op.eval [true, false]))) ≤ dgs.length + gs.length := by
    intro C v pre gs; induction gs generalizing pre with
    | nil => intro env dgs _ _ _ _ _; simp
    | cons g rest ih =>
      intro env dgs hfan hCeq hlen hv hinv
      have hgf := hfan g (by rw [hCeq]; simp)
      obtain ⟨x_new, hst_env⟩ := cstep_env_pres 9 env dgs g
      have hlen' : (cstep 9 (env, dgs) g).1.length = 10 + (pre ++ [g]).length := by
        rw [hst_env]; simp; omega
      have hv' : (cstep 9 (env, dgs) g).1.getD v.val (Sum.inl false) = Sum.inl true := by
        rw [hst_env, List.getD_append _ _ _ _ (by have := v.isLt; omega)]; exact hv
      have hinv' : ∀ k < (pre ++ [g]).length, ∀ h : Gate, (pre ++ [g])[k]? = some h →
          (reads h).contains v.val → (h.op.eval [false] || h.op.eval [true, false]) = true →
          ∃ b : Bool, (cstep 9 (env, dgs) g).1.getD (10 + k) (Sum.inl false) = Sum.inl b := by
        intro k hk h hget hr hornot
        by_cases hlt : k < pre.length
        · rw [List.getElem?_append_left hlt] at hget
          obtain ⟨b, hb⟩ := hinv k hlt h hget hr hornot
          refine ⟨b, ?_⟩
          rw [hst_env, List.getD_append _ _ _ _ (by omega)]; exact hb
        · have keq : k = pre.length := by simp at hk; omega
          subst keq
          rw [List.getElem?_append_right le_rfl] at hget; simp at hget; subst hget
          have hr' : v.val ∈ reads g := by simpa using hr
          obtain ⟨b, hb⟩ := cstep_const_out 9 env dgs g v.val hgf.1 hgf.2 hr' hornot hv
          refine ⟨b, ?_⟩
          rw [hb, List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self, List.getD_cons_zero]
      rcases hst : cstep 9 (env, dgs) g with ⟨env1, dgs1⟩
      have hih := ih (pre ++ [g]) env1 dgs1 hfan
        (by rw [hCeq, List.append_assoc]; rfl) (by simpa [hst] using hlen')
        (by simpa [hst] using hv') (by simpa [hst] using hinv')
      by_cases hhit : ((reads g).any fun k => k == v.val || (10 ≤ k && (C.gates[k - 10]?).any fun h =>
          (reads h).contains v.val && (h.op.eval [false] || h.op.eval [true, false]))) = true
      · have hno : dgs1.length = dgs.length := by
          have h0 : (cstep 9 (env, dgs) g).2.length = dgs.length := by
            apply cstep_no_emit 9 env dgs g hgf.1 hgf.2
            simp only [List.any_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at hhit
            obtain ⟨k, hk, hcond⟩ := hhit
            rcases hcond with hk_eq | ⟨hk10, hopt⟩
            · exact ⟨k, hk, true, by rwa [hk_eq]⟩
            · by_cases hlt : k - 10 < pre.length
              · have hkC : C.gates[k - 10]? = pre[k - 10]? := by
                  rw [hCeq, List.getElem?_append_left hlt]
                rw [hkC] at hopt
                cases hget : pre[k - 10]? with
                | none => simp [hget] at hopt
                | some h =>
                  rw [hget] at hopt; simp only [Option.any_some, Bool.and_eq_true] at hopt
                  obtain ⟨b, hb⟩ := hinv (k - 10) hlt h hget hopt.1 hopt.2
                  exact ⟨k, hk, b, by rwa [show 10 + (k - 10) = k by omega] at hb⟩
              · exact ⟨k, hk, false, List.getD_eq_default _ _ (by omega)⟩
          simpa [hst] using h0
        rw [List.foldl_cons, hst, List.countP_cons, if_pos hhit]; simp only [List.length_cons]
        rw [hno] at hih; omega
      · have h2 : dgs1.length ≤ dgs.length + 1 := by simpa [hst] using cstep_dlen_le 9 env dgs g
        rw [List.foldl_cons, hst, List.countP_cons, if_neg hhit]; simp only [List.length_cons]; omega

  have cstep_drop_hits01 : ∀ (gs : List Gate) (env : List (Sum Bool ℕ)) (dgs : List Gate),
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
      10 ≤ env.length →
      (∃ c0 : Bool, env.getD 0 (Sum.inl false) = Sum.inl c0) →
      (∃ c1 : Bool, env.getD 1 (Sum.inl false) = Sum.inl c1) →
      (gs.foldl (cstep 8) (env, dgs)).2.length +
        gs.countP (fun g => (reads g).contains 0 || (reads g).contains 1) ≤ dgs.length + gs.length := by
    intro gs; induction gs with
    | nil => intro _ _ _ _ _ _; simp
    | cons g rest ih =>
      intro env dgs hfan hlen hEx0 hEx1
      obtain ⟨c0, hc0⟩ := hEx0; obtain ⟨c1, hc1⟩ := hEx1
      have hgf := hfan g List.mem_cons_self
      obtain ⟨x_new, hst_env⟩ := cstep_env_pres 8 env dgs g
      have hlen' : 10 ≤ (cstep 8 (env, dgs) g).1.length := by rw [hst_env]; simp; omega
      have hc0' : (cstep 8 (env, dgs) g).1.getD 0 (Sum.inl false) = Sum.inl c0 := by
        rw [hst_env, List.getD_append _ _ _ _ (by omega)]; exact hc0
      have hc1' : (cstep 8 (env, dgs) g).1.getD 1 (Sum.inl false) = Sum.inl c1 := by
        rw [hst_env, List.getD_append _ _ _ _ (by omega)]; exact hc1
      rcases hst : cstep 8 (env, dgs) g with ⟨env1, dgs1⟩
      have hih := ih env1 dgs1 (fun a ha => hfan a (List.mem_cons_of_mem _ ha))
        (by simpa [hst] using hlen') ⟨c0, by simpa [hst] using hc0'⟩ ⟨c1, by simpa [hst] using hc1'⟩
      by_cases hhit : ((reads g).contains 0 || (reads g).contains 1) = true
      · have hno : dgs1.length = dgs.length := by
          have h0 : (cstep 8 (env, dgs) g).2.length = dgs.length := by
            apply cstep_no_emit 8 env dgs g hgf.1 hgf.2
            simp only [Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hhit
            rcases hhit with h0 | h1
            · exact ⟨0, h0, c0, hc0⟩
            · exact ⟨1, h1, c1, hc1⟩
          simpa [hst] using h0
        rw [List.foldl_cons, hst, List.countP_cons, if_pos hhit]; simp only [List.length_cons]
        rw [hno] at hih; omega
      · have h2 : dgs1.length ≤ dgs.length + 1 := by simpa [hst] using cstep_dlen_le 8 env dgs g
        rw [List.foldl_cons, hst, List.countP_cons, if_neg hhit]; simp only [List.length_cons]; omega

  -- Now assume ¬ L_meta_5835 and extract minimal counterexample
  by_contra hno
  push Not at hno
  let agree (C : Circuit) : Prop :=
    FanInTwo C ∧ ∀ x : Fin 10 → Bool, (x 0 || x 1) = true → C.eval (List.ofFn x) = P x
  have hex : ∃ k : ℕ, ∃ C : Circuit, agree C ∧ C.size = k := by
    obtain ⟨C, hfan, hsz, hev⟩ := hno
    exact ⟨C.size, C, ⟨hfan, hev⟩, rfl⟩
  let m := Nat.find hex
  have hm_le : m ≤ 17 := by
    obtain ⟨C, hfan, hsz, hev⟩ := hno
    exact (Nat.find_min' hex ⟨C, ⟨hfan, hev⟩, rfl⟩).trans hsz
  obtain ⟨C0, hagree0, hsz0⟩ := Nat.find_spec hex
  have hmin : ∀ C' : Circuit, agree C' → m ≤ C'.size := fun C' h' => Nat.find_min' hex ⟨C', h', rfl⟩

  -- Step 1: Normalize NOT gates to length ≤ 1 (preserves size)
  let vg (g : Gate) : Gate := if g.op.eval [false] then ⟨GateOp.not, g.inputs.take 1⟩ else g
  let C1 : Circuit := ⟨C0.gates.map vg, C0.output⟩
  have hvg_eval : ∀ (g : Gate) (w : List Bool),
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) →
      (vg g).op.eval ((vg g).inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
    intro g w hg; rcases g with ⟨op, ins⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · rfl
    · rfl
    · cases ins <;> simp [vg, notEval]
  have hC1_agree : agree C1 := by
    refine ⟨?_, ?_⟩
    · intro g hg; obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      have h0 := hagree0.1 g0 hg0
      by_cases h : g0.op.eval [false] = true
      · simp [vg, h]
      · simp [vg, h]; exact h0
    · intro x hx
      have hfold : ∀ (gs : List Gate) (w : List Bool),
          (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) →
          (gs.map vg).foldl wstep w = gs.foldl wstep w := by
        intro gs; induction gs with
        | nil => intro _ _; rfl
        | cons g gs ih =>
          intro w hgs; simp only [List.map_cons, List.foldl_cons, wstep]
          rw [hvg_eval g w (hgs g List.mem_cons_self)]
          exact ih _ (fun a ha => hgs a (List.mem_cons_of_mem _ ha))
      change ((C0.gates.map vg).foldl wstep (List.ofFn x)).getD C0.output false = P x
      rw [hfold C0.gates _ (fun g hg => (hagree0.1 g hg).1)]
      exact hagree0.2 x hx
  have hC1_sz : C1.size = m := by
    change (C0.gates.map vg).length = m; rw [List.length_map]; exact hsz0
  have hC1_not : ∀ g ∈ C1.gates, g.op = GateOp.not → g.inputs.length ≤ 1 := by
    intro g hg hop; obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    have hop0 : g0.op = .and ∨ g0.op = .or ∨ g0.op = .not := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using (hagree0.1 g0 hg0).1
    rcases hop0 with h | h | h
    · simp [vg, andEval, h] at hop
    · simp [vg, orEval, h] at hop
    · simp [vg, notEval, h]

  -- Step 2: Swap 0 and 1 via Petersen automorphism if needed so hits 0 ≤ hits 1
  let swap01 : Fin 10 → Fin 10 := ![1, 0, 4, 3, 2, 6, 5, 9, 8, 7]
  have hSwapP : ∀ x : Fin 10 → Bool, P (x ∘ swap01) = P x := by decide +kernel
  have hSwapD : ∀ x : Fin 10 → Bool, (x (swap01 0) || x (swap01 1)) = (x 0 || x 1) := by decide +kernel
  let extSwap (i : ℕ) : ℕ := if h : i < 10 then (swap01 ⟨i, h⟩).val else i
  let rGateSwap (g : Gate) : Gate := ⟨g.op, g.inputs.map extSwap⟩
  let C1_sw : Circuit := ⟨C1.gates.map rGateSwap, extSwap C1.output⟩
  have hC1_sw_agree : agree C1_sw := by
    refine ⟨?_, fun x hx => ?_⟩
    · intro g hg; obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      exact ⟨(hC1_agree.1 g0 hg0).1, by simpa [rGateSwap] using (hC1_agree.1 g0 hg0).2⟩
    · have hstep : ∀ (W W' : List Bool) (g : Gate),
          (∀ w, W'.getD (extSwap w) false = W.getD w false) →
          W'.length = W.length → 10 ≤ W.length →
          ∀ w, (wstep W' (rGateSwap g)).getD (extSwap w) false = (wstep W g).getD w false := by
        intro W W' g h3 hlen h10 w
        have hv : (rGateSwap g).op.eval ((rGateSwap g).inputs.map fun i => W'.getD i false) =
            g.op.eval (g.inputs.map fun i => W.getD i false) := by
          simp only [rGateSwap, List.map_map, Function.comp_def]
          congr 1; apply List.map_congr_left; intro a _; exact h3 a
        simp only [wstep, hv]
        rcases Nat.lt_trichotomy w W.length with hw | hw | hw
        · have hlt : extSwap w < W'.length := by
            dsimp only [extSwap]; split_ifs with h
            · have := (swap01 ⟨w, h⟩).isLt; omega
            · omega
          rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]; exact h3 w
        · have he : extSwap w = W'.length := by dsimp only [extSwap]; split_ifs with h <;> omega
          rw [he, hw, List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ le_rfl]; simp
        · have hge : W'.length + 1 ≤ extSwap w := by
            dsimp only [extSwap]; split_ifs with h
            · have := (swap01 ⟨w, h⟩).isLt; omega
            · omega
          rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      have hrun : ∀ (gs : List Gate) (W W' : List Bool),
          W'.length = W.length → 10 ≤ W.length →
          (∀ w, W'.getD (extSwap w) false = W.getD w false) →
          ∀ w, ((gs.map rGateSwap).foldl wstep W').getD (extSwap w) false = (gs.foldl wstep W).getD w false := by
        intro gs; induction gs with
        | nil => intro W W' _ _ h w; exact h w
        | cons g gs ih =>
          intro W W' hlen h10 h w
          rw [List.map_cons, List.foldl_cons, List.foldl_cons]
          exact ih _ _ (by simp [wstep, hlen]) (by simp [wstep]; omega) (hstep W W' g h hlen h10) w
      have hinit : ∀ w, (List.ofFn x).getD (extSwap w) false = (List.ofFn (x ∘ swap01)).getD w false := by
        intro w; dsimp only [extSwap]; split_ifs with hw
        · rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simp; exact hw),
            List.getElem_ofFn, List.getElem_ofFn]; rfl
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      have hev := hrun C1.gates (List.ofFn (x ∘ swap01)) (List.ofFn x) (by simp) (by simp) hinit C1.output
      exact hev.trans ((hC1_agree.2 (x ∘ swap01) (by simpa [hSwapD] using hx)).trans (hSwapP x))
  have hC1_sw_not : ∀ g ∈ C1_sw.gates, g.op = GateOp.not → g.inputs.length ≤ 1 := by
    intro g hg hop; obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    simpa [rGateSwap] using hC1_not g0 hg0 hop
  have hreads_swap0 : ∀ g : Gate, (reads (rGateSwap g)).contains 0 = (reads g).contains 1 := by
    intro g; apply Bool.eq_iff_iff.mpr
    have hext0 : ∀ w : ℕ, extSwap w = 0 ↔ w = 1 := by
      intro w; by_cases hw : w < 10
      · lift w to Fin 10 using hw; simp only [extSwap, w.isLt, dite_true, Fin.eta]
        revert w; decide
      · simp only [extSwap, hw, dite_false]; omega
    rcases g with ⟨op, ins⟩
    by_cases hnot : op.eval [false] = true
    · simp only [reads, rGateSwap, hnot, ↓reduceIte, List.contains_eq_mem, decide_eq_true_eq]
      rw [show (List.map extSwap ins).take 1 = (ins.take 1).map extSwap from by cases ins <;> rfl, List.mem_map]
      constructor
      · rintro ⟨w, hw, hw0⟩; exact (hext0 w).mp hw0 ▸ hw
      · intro h1; exact ⟨1, h1, (hext0 1).mpr rfl⟩
    · simp only [reads, rGateSwap, hnot, Bool.false_eq_true, ↓reduceIte, List.contains_eq_mem,
        decide_eq_true_eq, List.mem_map]
      constructor
      · rintro ⟨w, hw, hw0⟩; exact (hext0 w).mp hw0 ▸ hw
      · intro h1; exact ⟨1, h1, (hext0 1).mpr rfl⟩
  have hreads_swap1 : ∀ g : Gate, (reads (rGateSwap g)).contains 1 = (reads g).contains 0 := by
    intro g; apply Bool.eq_iff_iff.mpr
    have hext1 : ∀ w : ℕ, extSwap w = 1 ↔ w = 0 := by
      intro w; by_cases hw : w < 10
      · lift w to Fin 10 using hw; simp only [extSwap, w.isLt, dite_true, Fin.eta]
        revert w; decide
      · simp only [extSwap, hw, dite_false]; omega
    rcases g with ⟨op, ins⟩
    by_cases hnot : op.eval [false] = true
    · simp only [reads, rGateSwap, hnot, ↓reduceIte, List.contains_eq_mem, decide_eq_true_eq]
      rw [show (List.map extSwap ins).take 1 = (ins.take 1).map extSwap from by cases ins <;> rfl, List.mem_map]
      constructor
      · rintro ⟨w, hw, hw1⟩; exact (hext1 w).mp hw1 ▸ hw
      · intro h0; exact ⟨0, h0, (hext1 0).mpr rfl⟩
    · simp only [reads, rGateSwap, hnot, Bool.false_eq_true, ↓reduceIte, List.contains_eq_mem,
        decide_eq_true_eq, List.mem_map]
      constructor
      · rintro ⟨w, hw, hw1⟩; exact (hext1 w).mp hw1 ▸ hw
      · intro h0; exact ⟨0, h0, (hext1 0).mpr rfl⟩
  let C : Circuit := if C1.gates.countP (fun g => (reads g).contains 0) ≤
      C1.gates.countP (fun g => (reads g).contains 1) then C1 else C1_sw
  have hC_agree : agree C := by
    dsimp only [C]; split_ifs
    · exact hC1_agree
    · exact hC1_sw_agree
  have hC_sz : C.size = m := by
    dsimp only [C]; split_ifs
    · exact hC1_sz
    · change (C1.gates.map rGateSwap).length = m; rw [List.length_map]; exact hC1_sz
  have hC_not : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1 := by
    dsimp only [C]; split_ifs
    · exact hC1_not
    · exact hC1_sw_not
  have hC_hits : C.gates.countP (fun g => (reads g).contains 0) ≤
      C.gates.countP (fun g => (reads g).contains 1) := by
    dsimp only [C]; split_ifs with h
    · exact h
    · change (C1.gates.map rGateSwap).countP (fun g => (reads g).contains 0) ≤
        (C1.gates.map rGateSwap).countP (fun g => (reads g).contains 1)
      simp only [List.countP_map, Function.comp_def, hreads_swap0, hreads_swap1]; omega

  -- Step 3: Sensitivity on all 10 inputs + C.output >= 10
  have hSensWit : ∀ i : Fin 10, ∃ x y : Fin 10 → Bool,
      (x 0 || x 1) = true ∧ (y 0 || y 1) = true ∧ P x ≠ P y ∧ ∀ k : Fin 10, k ≠ i → x k = y k := by
    intro i; fin_cases i
    · exact ⟨![false, true, false, false, false, false, false, false, false, false],
        ![true, true, false, false, false, false, false, false, false, false], by decide⟩
    · exact ⟨![true, false, false, false, false, false, false, false, false, false],
        ![true, true, false, false, false, false, false, false, false, false], by decide⟩
    · exact ⟨![false, true, false, false, false, false, false, false, false, false],
        ![false, true, true, false, false, false, false, false, false, false], by decide⟩
    · exact ⟨![true, false, true, false, false, false, false, false, false, false],
        ![true, false, true, true, false, false, false, false, false, false], by decide⟩
    · exact ⟨![true, false, false, false, false, false, false, false, false, false],
        ![true, false, false, false, true, false, false, false, false, false], by decide⟩
    · exact ⟨![true, false, false, false, false, false, false, false, false, false],
        ![true, false, false, false, false, true, false, false, false, false], by decide⟩
    · exact ⟨![false, true, false, false, false, false, false, false, false, false],
        ![false, true, false, false, false, false, true, false, false, false], by decide⟩
    · exact ⟨![true, false, true, false, false, false, false, false, false, false],
        ![true, false, true, false, false, false, false, true, false, false], by decide⟩
    · exact ⟨![true, false, false, true, false, false, false, false, false, false],
        ![true, false, false, true, false, false, false, false, true, false], by decide⟩
    · exact ⟨![true, false, false, false, false, false, false, true, false, false],
        ![true, false, false, false, false, false, false, true, false, true], by decide⟩
  have hOut10 : 10 ≤ C.output := by
    by_contra hlt
    have ho : C.output < 10 := by omega
    let i : Fin 10 := ⟨C.output, ho⟩
    let x : Fin 10 → Bool := Function.update (fun _ => true) i false
    have hxProp : ∀ j : Fin 10,
        (Function.update (fun _ : Fin 10 => true) j false 0 ||
          Function.update (fun _ : Fin 10 => true) j false 1) = true ∧
        P (Function.update (fun _ : Fin 10 => true) j false) = true := by decide +kernel
    have hxD : (x 0 || x 1) = true := (hxProp i).1
    have hxP : P x = true := (hxProp i).2
    have hval : C.eval (List.ofFn x) = false := by
      change (C.gates.foldl wstep (List.ofFn x)).getD C.output false = false
      rw [wpres _ _ _ (by simp; exact ho), List.getD_eq_getElem _ _ (by simp; exact ho), List.getElem_ofFn]
      simp [x, i]
    have heq := hC_agree.2 x hxD
    rw [hval, hxP] at heq
    exact Bool.false_ne_true heq
  have hAllRead : ∀ i : Fin 10, ∃ g ∈ C.gates, i.val ∈ reads g := by
    intro i; by_contra hno; push Not at hno
    obtain ⟨x, y, hxD, hyD, hdiff, hsame⟩ := hSensWit i
    have hout : C.output ≠ i.val := by have := i.isLt; omega
    have hprop : ∀ (gs : List Gate) (w1 w2 : List Bool),
        (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) →
        (∀ g ∈ gs, i.val ∉ reads g) → w1.length = w2.length → 10 ≤ w1.length →
        (∀ j, j ≠ i.val → w1.getD j false = w2.getD j false) →
        ∀ j, j ≠ i.val → (gs.foldl wstep w1).getD j false = (gs.foldl wstep w2).getD j false := by
      intro gs; induction gs with
      | nil => intro w1 w2 _ _ _ _ hag j hj; exact hag j hj
      | cons g gs ih =>
        intro w1 w2 hfg hrg hlen h10 hag
        have hgf := hfg g List.mem_cons_self; have hgr := hrg g List.mem_cons_self
        have hgop : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hgf.1
        have hev : g.op.eval (g.inputs.map fun j => w1.getD j false) =
            g.op.eval (g.inputs.map fun j => w2.getD j false) := by
          rcases hgop with hop | hop | hop
          · have hm : i.val ∉ g.inputs := by simpa [reads, hop, andEval] using hgr
            rw [hop]; congr 1; apply List.map_congr_left; intro a ha; exact hag a (fun e => hm (e ▸ ha))
          · have hm : i.val ∉ g.inputs := by simpa [reads, hop, orEval] using hgr
            rw [hop]; congr 1; apply List.map_congr_left; intro a ha; exact hag a (fun e => hm (e ▸ ha))
          · rw [hop]; cases hgin : g.inputs with
            | nil => rfl
            | cons a tl =>
              have hne : a ≠ i.val := by intro e; apply hgr; simp [reads, hop, notEval, hgin, e]
              simp only [List.map_cons, notEval, List.headD_cons, hag a hne]
        apply ih (wstep w1 g) (wstep w2 g) (fun g' hg' => hfg g' (List.mem_cons_of_mem _ hg'))
          (fun g' hg' => hrg g' (List.mem_cons_of_mem _ hg')) (by simp [wstep, hlen]) (by simp [wstep]; omega)
        intro j hj; simp only [wstep]
        by_cases hlt : j < w1.length
        · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (hlen ▸ hlt)]; exact hag j hj
        · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_lt hlt),
              List.getD_append_right _ _ _ _ (hlen ▸ Nat.le_of_not_lt hlt), hlen, hev]
    have hinit : ∀ j, j ≠ i.val → (List.ofFn x).getD j false = (List.ofFn y).getD j false := by
      intro j hj; by_cases hlt : j < 10
      · rw [List.getD_eq_getElem _ _ (by simp; exact hlt), List.getD_eq_getElem _ _ (by simp; exact hlt)]
        simp only [List.getElem_ofFn]; exact hsame ⟨j, hlt⟩ (fun e => hj (congrArg Fin.val e))
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have heq := hprop C.gates (List.ofFn x) (List.ofFn y) hC_agree.1 hno (by simp) (by simp) hinit C.output hout
    change C.eval (List.ofFn x) = C.eval (List.ofFn y) at heq
    rw [hC_agree.2 x hxD, hC_agree.2 y hyD] at heq; exact hdiff heq

  -- Step 4: Prove ReadsBack 10 C and canonical gate arity / distinct binary inputs via cstep 10
  have hOutLt : C.output < 10 + C.size := by
    by_contra hge
    have hfalse : C.eval (List.ofFn ![true, true, false, false, false, false, false, false, false, false]) = false := by
      change (C.gates.foldl wstep _).getD C.output false = false
      apply List.getD_eq_default
      rw [wlen]; simp; change ¬ C.output < 10 + C.gates.length at hge; omega
    have htrue := hC_agree.2 ![true, true, false, false, false, false, false, false, false, false] rfl
    rw [htrue] at hfalse; revert hfalse; decide
  have hOutEq : C.output = 9 + C.size := by
    have hpos : 1 ≤ C.size := by omega
    by_contra hne
    have hlt : C.output < 10 + (C.size - 1) := by omega
    let C' : Circuit := ⟨C.gates.dropLast, C.output⟩
    have hC'_fan : FanInTwo C' := fun g hg => hC_agree.1 g (List.dropLast_subset _ hg)
    have hC'_ev : ∀ x : Fin 10 → Bool, (x 0 || x 1) = true → C'.eval (List.ofFn x) = P x := by
      intro x hx
      have hne_nil : C.gates ≠ [] := by intro e; change 1 ≤ C.gates.length at hpos; rw [e] at hpos; simp at hpos
      have heq_app := List.dropLast_append_getLast hne_nil
      have hev := hC_agree.2 x hx
      change (C.gates.foldl wstep (List.ofFn x)).getD C.output false = P x at hev
      rw [← heq_app, List.foldl_append, List.foldl_cons, List.foldl_nil] at hev
      change (wstep (C'.gates.foldl wstep (List.ofFn x)) (C.gates.getLast hne_nil)).getD C.output false = P x at hev
      have hlen_pre : (C'.gates.foldl wstep (List.ofFn x)).length = 10 + (C.size - 1) := by
        change (C'.gates.foldl wstep (List.ofFn x)).length = 10 + (C.gates.length - 1)
        rw [wlen]; simp [C']
      dsimp only [wstep] at hev
      rw [List.getD_append _ _ _ _ (by rw [hlen_pre]; exact hlt)] at hev
      exact hev
    have hm_le' := hmin C' ⟨hC'_fan, hC'_ev⟩
    have hsz' : C'.size = m - 1 := by
      change C.gates.dropLast.length = m - 1
      rw [List.length_dropLast]; change C.gates.length = m at hC_sz; omega
    omega

  -- Run cstep 10 on C to prove ReadsBack 10 C and canonical gate arities
  let init10 : List (Sum Bool ℕ) := (List.range 10).map Sum.inr
  have hinit10_bd : ∀ i : ℕ, symBd (10 + 0) (init10.getD i (Sum.inl false)) := by
    intro i; by_cases hi : i < 10
    · rw [List.getD_eq_getElem _ _ (by simpa [init10] using hi)]
      simp [init10, symBd, hi]
    · rw [List.getD_eq_default _ _ (by simp [init10]; omega)]; trivial
  have hinit10_eq : ∀ (x : Fin 10 → Bool) (i : ℕ),
      evalSym (([] : List Gate).foldl wstep (List.ofFn x)) (init10.getD i (Sum.inl false)) =
        (List.ofFn x).getD i false := by
    intro x i; by_cases hi : i < 10
    · rw [List.getD_eq_getElem _ _ (by simpa [init10] using hi)]
      simp [init10, evalSym, hi]
    · rw [List.getD_eq_default _ _ (by simp [init10]; omega), List.getD_eq_default _ _ (by simp; omega)]; rfl
  have hc10 := cstep_ind 10 C.gates init10 [] (fun x : Fin 10 → Bool => List.ofFn x)
    (fun x => List.ofFn x) hC_agree.1 (fun _ h => by cases h) (fun _ => by simp [init10])
    (fun _ => by simp) hinit10_bd hinit10_eq
  let res10 := C.gates.foldl (cstep 10) (init10, [])
  have hres10_out : ∃ ko : ℕ, res10.1.getD C.output (Sum.inl false) = Sum.inr ko := by
    cases ho : res10.1.getD C.output (Sum.inl false) with
    | inl b0 =>
      exfalso
      have hxT := hc10.2.2.2.2 ![true, true, false, false, false, false, false, false, false, false] C.output
      have hxF := hc10.2.2.2.2 ![true, false, false, false, false, false, false, false, false, false] C.output
      rw [ho] at hxT hxF; simp only [evalSym, Sum.elim_inl, id_eq] at hxT hxF
      change b0 = C.eval (List.ofFn ![true, true, false, false, false, false, false, false, false, false]) at hxT
      change b0 = C.eval (List.ofFn ![true, false, false, false, false, false, false, false, false, false]) at hxF
      rw [hC_agree.2 _ rfl] at hxT hxF
      have h1 : P ![true, true, false, false, false, false, false, false, false, false] = true := by decide
      have h2 : P ![true, false, false, false, false, false, false, false, false, false] = false := by decide
      rw [h1] at hxT; rw [h2] at hxF
      exact Bool.false_ne_true (hxF.symm.trans hxT)
    | inr ko => exact ⟨ko, rfl⟩
  have hres10_len : res10.2.length = C.gates.length := by
    obtain ⟨ko, hko⟩ := hres10_out
    let D : Circuit := ⟨res10.2, ko⟩
    have hD_agree : agree D := by
      refine ⟨hc10.2.2.1, fun x hx => ?_⟩
      have hr := hc10.2.2.2.2 x C.output
      rw [hko] at hr; simp only [evalSym, Sum.elim_inr] at hr
      exact hr.trans (hC_agree.2 x hx)
    have hle := hmin D ⟨hD_agree.1, hD_agree.2⟩
    have hle2 := hc10.2.1
    change res10.2.length ≤ [].length + C.gates.length at hle2
    change m ≤ res10.2.length at hle; change C.gates.length = m at hC_sz; simp at hle2; omega
  have hC_norm : ∀ (pre post : List Gate) (g : Gate), C.gates = pre ++ g :: post →
      (∀ i ∈ g.inputs, i < 10 + pre.length) ∧
      g.inputs.length = (if g.op.eval [false] then 1 else 2) ∧
      (g.inputs.length = 2 → g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) := by
    intro pre post g hsplit
    have hwalk : ∀ (gs : List Gate) (env : List (Sum Bool ℕ)) (dgs : List Gate),
        (∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 ∧
          (g'.op = GateOp.not → g'.inputs.length ≤ 1)) →
        (∀ j < env.length, ∃ k, env.getD j (Sum.inl false) = Sum.inr k) →
        (∀ i j, i < env.length → j < env.length → i ≠ j →
          env.getD i (Sum.inl false) ≠ env.getD j (Sum.inl false)) →
        (∀ j < env.length, ∀ k, env.getD j (Sum.inl false) = Sum.inr k → k < 10 + dgs.length) →
        (gs.foldl (cstep 10) (env, dgs)).2.length = dgs.length + gs.length →
        ∀ (p1 p2 : List Gate) (g0 : Gate), gs = p1 ++ g0 :: p2 →
          (∀ i ∈ g0.inputs, i < env.length + p1.length) ∧
          g0.inputs.length = (if g0.op.eval [false] then 1 else 2) ∧
          (g0.inputs.length = 2 → g0.inputs.getD 0 0 ≠ g0.inputs.getD 1 0) := by
      intro gs; induction gs with
      | nil => intro _ _ _ _ _ _ _ _ _ _ h; simp at h
      | cons g' rest ih =>
        intro env dgs hgs h_inr h_inj h_bd h_full p1 p2 g0 hsplit'
        have hg' := hgs g' List.mem_cons_self
        have hstep_emit : (cstep 10 (env, dgs) g').2.length = dgs.length + 1 := by
          have h1 := cstep_fold_le 10 rest (cstep 10 (env, dgs) g')
          have h2 := cstep_dlen_le 10 env dgs g'
          rw [List.foldl_cons] at h_full; simp only [List.length_cons] at h_full; omega
        have h_rest_full : (rest.foldl (cstep 10) (cstep 10 (env, dgs) g')).2.length =
            (cstep 10 (env, dgs) g').2.length + rest.length := by
          rw [List.foldl_cons] at h_full; simp only [List.length_cons] at h_full; omega
        have hg'_prop : (∀ i ∈ g'.inputs, i < env.length) ∧
            g'.inputs.length = (if g'.op.eval [false] then 1 else 2) ∧
            (g'.inputs.length = 2 → g'.inputs.getD 0 0 ≠ g'.inputs.getD 1 0) ∧
            (cstep 10 (env, dgs) g').1 = env ++ [Sum.inr (10 + dgs.length)] := by
          have hgop : g'.op = .and ∨ g'.op = .or ∨ g'.op = .not := by
            simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hg'.1
          rcases hgop with hop | hop | hop
          · cases hgin : g'.inputs with
            | nil => simp [cstep, hop, andEval, hgin] at hstep_emit
            | cons a tl =>
              cases tl with
              | nil => simp [cstep, hop, andEval, hgin] at hstep_emit
              | cons b tl2 =>
                cases tl2 with
                | cons _ _ => have := hg'.2.1; simp [hgin] at this
                | nil =>
                  have ha_lt : a < env.length := by
                    by_contra hge
                    have ha_def : env.getD a (Sum.inl false) = Sum.inl false := List.getD_eq_default _ _ (Nat.le_of_not_lt hge)
                    have hne := cstep_no_emit 10 env dgs g' hg'.1 hg'.2.1 ⟨a, by simp [reads, hop, andEval, hgin], false, ha_def⟩
                    omega
                  have hb_lt : b < env.length := by
                    by_contra hge
                    have hb_def : env.getD b (Sum.inl false) = Sum.inl false := List.getD_eq_default _ _ (Nat.le_of_not_lt hge)
                    have hne := cstep_no_emit 10 env dgs g' hg'.1 hg'.2.1 ⟨b, by simp [reads, hop, andEval, hgin], false, hb_def⟩
                    omega
                  obtain ⟨ka, hka⟩ := h_inr a ha_lt
                  obtain ⟨kb, hkb⟩ := h_inr b hb_lt
                  have hne_k : ka ≠ kb := by
                    intro hk; subst hk
                    dsimp only [cstep] at hstep_emit
                    simp only [hop, andEval, hgin, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.false_eq_true, ↓reduceIte,
                      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero, List.getD_cons_succ,
                      hka, hkb, Sum.elim_inr, beq_self_eq_true] at hstep_emit
                    omega
                  have hne_ab : a ≠ b := fun e => hne_k (by rw [e] at hka; rw [hka] at hkb; cases hkb; rfl)
                  have hcst : (cstep 10 (env, dgs) g').1 = env ++ [Sum.inr (10 + dgs.length)] := by
                    dsimp only [cstep]; rw [hop, andEval, andEval, hgin]
                    simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.false_eq_true, ↓reduceIte,
                      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero, List.getD_cons_succ,
                      hka, hkb, Sum.elim_inr, beq_iff_eq, hne_k]
                  refine ⟨fun i hi => ?_, by simp [hop, andEval, hgin], fun _ => by simpa [hgin] using hne_ab, hcst⟩
                  simp only [hgin, List.mem_cons, List.not_mem_nil, or_false] at hi
                  rcases hi with rfl | rfl <;> assumption
          · cases hgin : g'.inputs with
            | nil => simp [cstep, hop, orEval, hgin] at hstep_emit
            | cons a tl =>
              cases tl with
              | nil => simp [cstep, hop, orEval, hgin] at hstep_emit
              | cons b tl2 =>
                cases tl2 with
                | cons _ _ => have := hg'.2.1; simp [hgin] at this
                | nil =>
                  have ha_lt : a < env.length := by
                    by_contra hge
                    have ha_def : env.getD a (Sum.inl false) = Sum.inl false := List.getD_eq_default _ _ (Nat.le_of_not_lt hge)
                    have hne := cstep_no_emit 10 env dgs g' hg'.1 hg'.2.1 ⟨a, by simp [reads, hop, orEval, hgin], false, ha_def⟩
                    omega
                  have hb_lt : b < env.length := by
                    by_contra hge
                    have hb_def : env.getD b (Sum.inl false) = Sum.inl false := List.getD_eq_default _ _ (Nat.le_of_not_lt hge)
                    have hne := cstep_no_emit 10 env dgs g' hg'.1 hg'.2.1 ⟨b, by simp [reads, hop, orEval, hgin], false, hb_def⟩
                    omega
                  obtain ⟨ka, hka⟩ := h_inr a ha_lt
                  obtain ⟨kb, hkb⟩ := h_inr b hb_lt
                  have hne_k : ka ≠ kb := by
                    intro hk; subst hk
                    dsimp only [cstep] at hstep_emit
                    simp only [hop, orEval, hgin, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
                      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero, List.getD_cons_succ,
                      hka, hkb, Sum.elim_inr, beq_self_eq_true] at hstep_emit
                    omega
                  have hne_ab : a ≠ b := fun e => hne_k (by rw [e] at hka; rw [hka] at hkb; cases hkb; rfl)
                  have hcst : (cstep 10 (env, dgs) g').1 = env ++ [Sum.inr (10 + dgs.length)] := by
                    dsimp only [cstep]; rw [hop, orEval, orEval, hgin]
                    simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
                      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceBEq, List.getD_cons_zero, List.getD_cons_succ,
                      hka, hkb, Sum.elim_inr, beq_iff_eq, hne_k]
                  refine ⟨fun i hi => ?_, by simp [hop, orEval, hgin], fun _ => by simpa [hgin] using hne_ab, hcst⟩
                  simp only [hgin, List.mem_cons, List.not_mem_nil, or_false] at hi
                  rcases hi with rfl | rfl <;> assumption
          · have hnot1 := hg'.2.2 hop
            cases hgin : g'.inputs with
            | nil => simp [cstep, hop, notEval, hgin] at hstep_emit
            | cons a tl =>
              cases tl with
              | cons _ _ => simp [hgin] at hnot1
              | nil =>
                have ha_lt : a < env.length := by
                  by_contra hge
                  have ha_def : env.getD a (Sum.inl false) = Sum.inl false := List.getD_eq_default _ _ (Nat.le_of_not_lt hge)
                  have hne := cstep_no_emit 10 env dgs g' hg'.1 hg'.2.1 ⟨a, by simp [reads, hop, notEval, hgin], false, ha_def⟩
                  omega
                obtain ⟨ka, hka⟩ := h_inr a ha_lt
                have hcst : (cstep 10 (env, dgs) g').1 = env ++ [Sum.inr (10 + dgs.length)] := by
                  dsimp only [cstep]; rw [hop, notEval, hgin]
                  simp only [List.headD_cons, Bool.not_false, ↓reduceIte, List.isEmpty_cons, Bool.false_eq_true,
                    List.getD_cons_zero, hka, Sum.elim_inr]
                refine ⟨fun i hi => ?_, by simp [hop, notEval, hgin], fun h2 => by simp [hgin] at h2, hcst⟩
                simp only [hgin, List.mem_singleton] at hi; subst hi; exact ha_lt
        cases p1 with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at hsplit'
          obtain ⟨rfl, rfl⟩ := hsplit'
          exact ⟨hg'_prop.1, hg'_prop.2.1, hg'_prop.2.2.1⟩
        | cons h p1' =>
          simp only [List.cons_append, List.cons.injEq] at hsplit'
          obtain ⟨rfl, hrest_eq⟩ := hsplit'
          have h_inr' : ∀ j < (cstep 10 (env, dgs) g').1.length, ∃ k, (cstep 10 (env, dgs) g').1.getD j (Sum.inl false) = Sum.inr k := by
            intro j hj; rw [hg'_prop.2.2.2] at hj ⊢
            by_cases hlt : j < env.length
            · rw [List.getD_append _ _ _ _ hlt]; exact h_inr j hlt
            · have jeq : j = env.length := by simp at hj; omega
              subst jeq; rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]; exact ⟨_, rfl⟩
          have h_inj' : ∀ i j, i < (cstep 10 (env, dgs) g').1.length → j < (cstep 10 (env, dgs) g').1.length → i ≠ j →
              (cstep 10 (env, dgs) g').1.getD i (Sum.inl false) ≠ (cstep 10 (env, dgs) g').1.getD j (Sum.inl false) := by
            intro i j hi hj hij; rw [hg'_prop.2.2.2] at hi hj ⊢
            by_cases hil : i < env.length <;> by_cases hjl : j < env.length
            · rw [List.getD_append _ _ _ _ hil, List.getD_append _ _ _ _ hjl]; exact h_inj i j hil hjl hij
            · have jeq : j = env.length := by simp at hj; omega
              subst jeq; rw [List.getD_append _ _ _ _ hil, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
              obtain ⟨k, hk⟩ := h_inr i hil; have hkb := h_bd i hil k hk; rw [hk]; intro e; cases e; omega
            · have ieq : i = env.length := by simp at hi; omega
              subst ieq; rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero, List.getD_append _ _ _ _ hjl]
              obtain ⟨k, hk⟩ := h_inr j hjl; have hkb := h_bd j hjl k hk; rw [hk]; intro e; cases e; omega
            · exfalso; simp at hi hj; omega
          have h_bd' : ∀ j < (cstep 10 (env, dgs) g').1.length, ∀ k,
              (cstep 10 (env, dgs) g').1.getD j (Sum.inl false) = Sum.inr k → k < 10 + (cstep 10 (env, dgs) g').2.length := by
            intro j hj k hk; rw [hg'_prop.2.2.2] at hj hk
            by_cases hlt : j < env.length
            · rw [List.getD_append _ _ _ _ hlt] at hk; have := h_bd j hlt k hk; omega
            · have jeq : j = env.length := by simp at hj; omega
              subst jeq; rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero] at hk
              cases hk; omega
          have hres := ih (cstep 10 (env, dgs) g').1 (cstep 10 (env, dgs) g').2
            (fun a ha => hgs a (List.mem_cons_of_mem _ ha)) h_inr' h_inj' h_bd' h_rest_full p1' p2 g0 hrest_eq
          have hlen_step : (cstep 10 (env, dgs) g').1.length = env.length + 1 := by rw [hg'_prop.2.2.2]; simp
          rw [hlen_step] at hres
          refine ⟨fun i hi => by have := hres.1 i hi; simp only [List.length_cons] at *; omega, hres.2⟩
    apply hwalk C.gates init10 [] (fun a ha => ⟨(hC_agree.1 a ha).1, (hC_agree.1 a ha).2, hC_not a ha⟩)
      (fun j hj => ⟨j, by
        rw [List.getD_eq_getElem _ _ (by simp [init10]; exact hj)]
        simp [init10, hj]⟩)
      (fun i j hi hj hij => by
        simp [init10] at hi hj
        rw [List.getD_eq_getElem _ _ (by simp [init10]; exact hi), List.getD_eq_getElem _ _ (by simp [init10]; exact hj)]
        simp [init10, hi, hj, hij])
      (fun j hj k hk => by
        simp [init10] at hj
        rw [List.getD_eq_getElem _ _ (by simp [init10]; exact hj)] at hk
        simp [init10, hj] at hk; subst hk; exact hj)
      (by simpa using hres10_len) pre post g hsplit

  have hReadsBack : ReadsBack 10 C := by
    intro j hj
    have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
      have h1 := List.take_append_drop j C.gates
      have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
      rw [h2] at h1; exact h1.symm
    have hnorm := (hC_norm (C.gates.take j) (C.gates.drop (j + 1)) C.gates[j] hsplit).1
    have hlen_take : (C.gates.take j).length = j := List.length_take_of_le (Nat.le_of_lt hj)
    have hgat : gateAt C j = C.gates[j] := by unfold gateAt; rw [List.getD_eq_getElem _ _ hj]
    rw [hgat]; intro i hi; exact hlen_take ▸ hnorm i hi

  have hGateArity : ∀ g ∈ C.gates, g.inputs.length = (if g.op.eval [false] then 1 else 2) ∧
      (g.inputs.length = 2 → g.inputs.getD 0 0 ≠ g.inputs.getD 1 0) := by
    intro g hg
    obtain ⟨pre, post, hsplit⟩ := List.append_of_mem hg
    exact (hC_norm pre post g hsplit).2

  have hNoDead : ∀ j : ℕ, j + 1 < C.size → ∃ g ∈ C.gates, 10 + j ∈ reads g := by
    intro j hj
    by_contra hno; push Not at hno
    have hj_lt : j < C.gates.length := by change j + 1 < C.gates.length at hj; omega
    let pre := C.gates.take j
    let post := C.gates.drop (j + 1)
    have hsplit : C.gates = pre ++ C.gates[j] :: post := by
      have h1 := List.take_append_drop j C.gates
      have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj_lt
      rw [h2] at h1; exact h1.symm
    have hpre_len : pre.length = j := List.length_take_of_le (Nat.le_of_lt hj_lt)
    let red (w : ℕ) : ℕ := if w = 10 + j then 0 else if 10 + j < w then w - 1 else w
    let C' : Circuit := ⟨pre ++ post.map (fun h => ⟨h.op, h.inputs.map red⟩), red C.output⟩
    have hC'_fan : FanInTwo C' := by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hC_agree.1 g (hsplit ▸ List.mem_append_left _ hg)
      · obtain ⟨h0, hm, rfl⟩ := List.mem_map.mp hg
        have h0' := hC_agree.1 h0 (hsplit ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hm))
        exact ⟨h0'.1, by simpa using h0'.2⟩
    have hC'_sz : C'.size = m - 1 := by
      change (pre ++ post.map _).length = m - 1
      have hlen : C.gates.length = pre.length + 1 + post.length := by
        rw [hsplit, List.length_append, List.length_cons]; omega
      simp [List.length_map]; change C.gates.length = m at hC_sz; omega
    have hC'_ev : ∀ x : Fin 10 → Bool, (x 0 || x 1) = true → C'.eval (List.ofFn x) = P x := by
      intro x hx
      let ERel (k : ℕ) (wC wD : List Bool) : Prop :=
        wC.length = 10 + j + 1 + k ∧ wD.length = 10 + j + k ∧
        ∀ i, i ≠ 10 + j → wC.getD i false = wD.getD (red i) false
      have heval_step : ∀ (ls : List Gate) (k : ℕ) (wC wD : List Bool),
          (∀ h ∈ ls, h.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ h.inputs.length ≤ 2) →
          (∀ h ∈ ls, 10 + j ∉ reads h) →
          ERel k wC wD →
          ERel (k + ls.length) (ls.foldl wstep wC) ((ls.map (fun h => ⟨h.op, h.inputs.map red⟩)).foldl wstep wD) := by
        intro ls; induction ls with
        | nil => intro k wC wD _ _ hrel; simpa using hrel
        | cons h rest ih =>
          intro k wC wD hls hnr hrel
          have hh := hls h List.mem_cons_self
          have hnr_h := hnr h List.mem_cons_self
          have hv : (⟨h.op, h.inputs.map red⟩ : Gate).op.eval ((h.inputs.map red).map fun i => wD.getD i false) =
              h.op.eval (h.inputs.map fun i => wC.getD i false) := by
            have hgop : h.op = .and ∨ h.op = .or ∨ h.op = .not := by
              simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hh.1
            rcases hgop with hop | hop | hop
            · have hm : 10 + j ∉ h.inputs := by simpa [reads, hop, andEval] using hnr_h
              rw [hop]; congr 1; simp only [List.map_map, Function.comp_def]
              apply List.map_congr_left; intro a ha
              exact (hrel.2.2 a (fun e => hm (e ▸ ha))).symm
            · have hm : 10 + j ∉ h.inputs := by simpa [reads, hop, orEval] using hnr_h
              rw [hop]; congr 1; simp only [List.map_map, Function.comp_def]
              apply List.map_congr_left; intro a ha
              exact (hrel.2.2 a (fun e => hm (e ▸ ha))).symm
            · rw [hop]; cases hgin : h.inputs with
              | nil => rfl
              | cons a tl =>
                have hne : a ≠ 10 + j := by intro e; apply hnr_h; simp [reads, hop, notEval, hgin, e]
                simp only [List.map_cons, notEval, List.headD_cons, hrel.2.2 a hne]
          simp only [List.map_cons, List.foldl_cons]
          have hstep_rel : ERel (k + 1) (wstep wC h) (wstep wD ⟨h.op, h.inputs.map red⟩) := by
            obtain ⟨hlC, hlD, heq⟩ := hrel
            refine ⟨by simp [wstep, hlC]; omega, by simp [wstep, hlD]; omega, fun i hi => ?_⟩
            simp only [wstep, hv]
            by_cases hi_eq : i = wC.length
            · subst hi_eq; have hri : red wC.length = wD.length := by
                dsimp only [red]; split_ifs with e1 e2 <;> omega
              rw [hri, List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ le_rfl]
              simp
            · by_cases hi_lt : i < wC.length
              · have hri : red i < wD.length := by
                  dsimp only [red]; split_ifs with e1 e2 <;> omega
                rw [List.getD_append _ _ _ _ hi_lt, List.getD_append _ _ _ _ hri]; exact heq i hi
              · have hri : wD.length + 1 ≤ red i := by
                  dsimp only [red]; split_ifs with e1 e2 <;> omega
                rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
          have hres := ih (k + 1) _ _ (fun a ha => hls a (List.mem_cons_of_mem _ ha))
            (fun a ha => hnr a (List.mem_cons_of_mem _ ha)) hstep_rel
          rw [List.length_cons, show k + (rest.length + 1) = k + 1 + rest.length by omega]
          exact hres
      have hrel0 : ERel 0 (wstep (pre.foldl wstep (List.ofFn x)) C.gates[j]) (pre.foldl wstep (List.ofFn x)) := by
        have hlen_pre : (pre.foldl wstep (List.ofFn x)).length = 10 + j := by rw [wlen]; simp [hpre_len]
        refine ⟨by dsimp only [wstep]; rw [List.length_append, hlen_pre]; simp, hlen_pre, fun i hi => ?_⟩
        by_cases hlt : i < 10 + j
        · have hri : red i = i := by dsimp only [red]; split_ifs <;> omega
          dsimp only [wstep]
          rw [hri, List.getD_append _ _ _ _ (by rw [hlen_pre]; exact hlt)]
        · have hgt : 10 + j < i := by omega
          have hri : 10 + j ≤ red i := by dsimp only [red]; split_ifs <;> omega
          rw [List.getD_eq_default _ _ (by dsimp only [wstep]; rw [List.length_append, hlen_pre]; simp; omega),
              List.getD_eq_default _ _ (by rw [hlen_pre]; exact hri)]
      have hfinal := heval_step post 0 _ _
        (fun h hh => hC_agree.1 h (hsplit ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hh)))
        (fun h hh => hno h (hsplit ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hh)))
        hrel0
      have hout_ne : C.output ≠ 10 + j := by
        change j + 1 < C.gates.length at hj
        change C.output = 9 + C.gates.length at hOutEq; omega
      have hev_C := hC_agree.2 x hx
      change (C.gates.foldl wstep (List.ofFn x)).getD C.output false = P x at hev_C
      rw [hsplit, List.foldl_append, List.foldl_cons] at hev_C
      change (post.foldl wstep (wstep (pre.foldl wstep (List.ofFn x)) C.gates[j])).getD C.output false = P x at hev_C
      change ((pre ++ post.map _).foldl wstep (List.ofFn x)).getD (red C.output) false = P x
      rw [List.foldl_append, ← hfinal.2.2 C.output hout_ne]
      exact hev_C
    have hm_le' := hmin C' ⟨hC'_fan, hC'_ev⟩
    omega

  -- Step 5: Prove 11 + killed 0 C <= m, 11 + killed 1 C <= m, 10 + hits01 C <= m
  have hKilled0 : 11 + C.gates.countP (fun g => (reads g).any fun k => k == 0 ||
      (10 ≤ k && (C.gates[k - 10]?).any fun h => (reads h).contains 0 &&
        (h.op.eval [false] || h.op.eval [true, false]))) ≤ C.size := by
    let init0 : List (Sum Bool ℕ) := Sum.inl true :: (List.range 9).map Sum.inr
    have hinit0_bd : ∀ i : ℕ, symBd (9 + 0) (init0.getD i (Sum.inl false)) := by
      intro i; by_cases hi : i < 10
      · rw [List.getD_eq_getElem _ _ (by simpa [init0] using hi)]
        cases i with
        | zero => trivial
        | succ k => simp [init0, symBd]; omega
      · rw [List.getD_eq_default _ _ (by simp [init0]; omega)]; trivial
    have hinit0_eq : ∀ (y : Fin 9 → Bool) (i : ℕ),
        evalSym (([] : List Gate).foldl wstep (List.ofFn y)) (init0.getD i (Sum.inl false)) =
          (List.ofFn (Fin.cons true y)).getD i false := by
      intro y i; by_cases hi : i < 10
      · rw [List.getD_eq_getElem _ _ (by simpa [init0] using hi), List.getD_eq_getElem _ _ (by simp; exact hi)]
        cases i with
        | zero => simp [init0, evalSym]
        | succ k => simp [init0, evalSym, show k < 9 by omega]
      · rw [List.getD_eq_default _ _ (by simp [init0]; omega), List.getD_eq_default _ _ (by simp; omega)]; rfl
    have hc0 := cstep_ind 9 C.gates init0 [] (fun y : Fin 9 → Bool => List.ofFn (Fin.cons true y))
      (fun y => List.ofFn y) hC_agree.1 (fun _ h => by cases h) (fun _ => by simp [init0])
      (fun _ => by simp) hinit0_bd hinit0_eq
    have hdrop0 := cstep_drop_killed C 0 [] C.gates init0 [] hC_agree.1 rfl (by simp [init0])
      (by simp [init0]) (fun k hk => by simp at hk)
    let res := C.gates.foldl (cstep 9) (init0, [])
    have hfin_eq : ∀ y : Fin 9 → Bool, P (Fin.cons true y) = f11 y := by decide +kernel
    have hC_f11 : ∀ y : Fin 9 → Bool, C.eval (List.ofFn (Fin.cons true y)) = f11 y := fun y =>
      (hC_agree.2 (Fin.cons true y) rfl).trans (hfin_eq y)
    have hnot_const : ∀ b0 : Bool, res.1.getD C.output (Sum.inl false) ≠ Sum.inl b0 := by
      intro b0 heq
      have rF := hc0.2.2.2.2 (fun _ => false) C.output
      have rT := hc0.2.2.2.2 (fun _ => true) C.output
      rw [heq] at rF rT; simp only [evalSym, Sum.elim_inl, id_eq] at rF rT
      change b0 = C.eval (List.ofFn (Fin.cons true (fun _ : Fin 9 => false))) at rF
      change b0 = C.eval (List.ofFn (Fin.cons true (fun _ : Fin 9 => true))) at rT
      rw [hC_f11] at rF; rw [hC_f11] at rT
      have eF : f11 (fun _ => false) = false := by decide
      have eT : f11 (fun _ => true) = true := by decide
      rw [eF] at rF; rw [eT] at rT; exact Bool.false_ne_true (rF.symm.trans rT)
    cases ho : res.1.getD C.output (Sum.inl false) with
    | inl b0 => exact False.elim (hnot_const b0 ho)
    | inr ko =>
      have hge11 : 11 ≤ res.2.length := by
        by_contra hlt
        apply hf11_lb
        refine ⟨⟨res.2, ko⟩, hc0.2.2.1, by change res.2.length ≤ 10; omega, fun y => ?_⟩
        have r := hc0.2.2.2.2 y C.output
        rw [ho] at r; simp only [evalSym, Sum.elim_inr] at r
        exact r.trans (hC_f11 y)
      have hsum : res.2.length + C.gates.countP (fun g => (reads g).any fun k => k == 0 ||
          (10 ≤ k && (C.gates[k - 10]?).any fun h => (reads h).contains 0 &&
            (h.op.eval [false] || h.op.eval [true, false]))) ≤ C.gates.length := by simpa using hdrop0
      change 11 + _ ≤ C.gates.length; omega

  have hKilled1 : 11 + C.gates.countP (fun g => (reads g).any fun k => k == 1 ||
      (10 ≤ k && (C.gates[k - 10]?).any fun h => (reads h).contains 1 &&
        (h.op.eval [false] || h.op.eval [true, false]))) ≤ C.size := by
    let init1 : List (Sum Bool ℕ) := Sum.inr 0 :: Sum.inl true :: (List.range 8).map (fun i => Sum.inr (i + 1))
    have hinit1_bd : ∀ i : ℕ, symBd (9 + 0) (init1.getD i (Sum.inl false)) := by
      intro i; by_cases hi : i < 10
      · rw [List.getD_eq_getElem _ _ (by simpa [init1] using hi)]
        rcases i with _ | _ | k
        · simp [init1, symBd]
        · trivial
        · simp [init1, symBd]; omega
      · rw [List.getD_eq_default _ _ (by simp [init1]; omega)]; trivial
    have hinit1_eq : ∀ (y : Fin 9 → Bool) (i : ℕ),
        evalSym (([] : List Gate).foldl wstep (List.ofFn y)) (init1.getD i (Sum.inl false)) =
          (List.ofFn ((1 : Fin 10).insertNth true y)).getD i false := by
      intro y i; by_cases hi : i < 10
      · rw [List.getD_eq_getElem _ _ (by simpa [init1] using hi), List.getD_eq_getElem _ _ (by simp; exact hi)]
        rcases i with _ | _ | k
        · simp [init1, evalSym]
          rw [Fin.insertNth_apply_below (α := fun _ => Bool) (by decide : (0 : Fin 10) < 1)]; simp
        · simp [init1, evalSym]
        · simp only [init1, evalSym, List.foldl_nil, Sum.elim_inr, List.getElem_cons_succ, List.getElem_map,
            List.getElem_range, List.getElem_ofFn]
          rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
          have hgt1 : (1 : Fin 10) < ⟨k + 2, hi⟩ := by simp [Fin.lt_def]
          rw [Fin.insertNth_apply_above (α := fun _ => Bool) hgt1]; simp
      · rw [List.getD_eq_default _ _ (by simp [init1]; omega), List.getD_eq_default _ _ (by simp; omega)]; rfl
    have hc1 := cstep_ind 9 C.gates init1 [] (fun y : Fin 9 → Bool => List.ofFn ((1 : Fin 10).insertNth true y))
      (fun y => List.ofFn y) hC_agree.1 (fun _ h => by cases h) (fun _ => by simp [init1])
      (fun _ => by simp) hinit1_bd hinit1_eq
    have hdrop1 := cstep_drop_killed C 1 [] C.gates init1 [] hC_agree.1 rfl (by simp [init1])
      (by simp [init1]) (fun k hk => by simp at hk)
    let res := C.gates.foldl (cstep 9) (init1, [])
    let ρ1 : Fin 9 → Fin 9 := ![0, 3, 2, 1, 5, 4, 8, 7, 6]
    have hfin_eq : ∀ y : Fin 9 → Bool, P ((1 : Fin 10).insertNth true (y ∘ ρ1)) = f11 y := by decide +kernel
    have hD1_agree : ∀ y : Fin 9 → Bool,
        ((1 : Fin 10).insertNth (α := fun _ => Bool) true y 0 ||
          (1 : Fin 10).insertNth (α := fun _ => Bool) true y 1) = true := by
      intro y; simp
    have hnot_const : ∀ b0 : Bool, res.1.getD C.output (Sum.inl false) ≠ Sum.inl b0 := by
      intro b0 heq
      have rF := hc1.2.2.2.2 ((fun _ => false) ∘ ρ1) C.output
      have rT := hc1.2.2.2.2 ((fun _ => true) ∘ ρ1) C.output
      rw [heq] at rF rT; simp only [evalSym, Sum.elim_inl, id_eq] at rF rT
      change b0 = C.eval (List.ofFn ((1 : Fin 10).insertNth true ((fun _ : Fin 9 => false) ∘ ρ1))) at rF
      change b0 = C.eval (List.ofFn ((1 : Fin 10).insertNth true ((fun _ : Fin 9 => true) ∘ ρ1))) at rT
      rw [hC_agree.2 _ (hD1_agree _), hfin_eq] at rF
      rw [hC_agree.2 _ (hD1_agree _), hfin_eq] at rT
      have eF : f11 (fun _ => false) = false := by decide
      have eT : f11 (fun _ => true) = true := by decide
      rw [eF] at rF; rw [eT] at rT; exact Bool.false_ne_true (rF.symm.trans rT)
    cases ho : res.1.getD C.output (Sum.inl false) with
    | inl b0 => exact False.elim (hnot_const b0 ho)
    | inr ko =>
      have hge11 : 11 ≤ res.2.length := by
        by_contra hlt
        obtain ⟨D1, hD1, hsz1, hev1⟩ := relabelC ρ1 ⟨res.2, ko⟩ hc1.2.2.1
        apply hf11_lb
        refine ⟨D1, hD1, by change D1.size ≤ 10; rw [hsz1]; change res.2.length ≤ 10; omega, fun y => ?_⟩
        rw [hev1 y]
        have r := hc1.2.2.2.2 (y ∘ ρ1) C.output
        rw [ho] at r; simp only [evalSym, Sum.elim_inr] at r
        exact r.trans ((hC_agree.2 _ (hD1_agree _)).trans (hfin_eq y))
      have hsum : res.2.length + C.gates.countP (fun g => (reads g).any fun k => k == 1 ||
          (10 ≤ k && (C.gates[k - 10]?).any fun h => (reads h).contains 1 &&
            (h.op.eval [false] || h.op.eval [true, false]))) ≤ C.gates.length := by simpa using hdrop1
      change 11 + _ ≤ C.gates.length; omega

  have hHits01 : 10 + C.gates.countP (fun g => (reads g).contains 0 || (reads g).contains 1) ≤ C.size := by
    let init01 : List (Sum Bool ℕ) := Sum.inl true :: Sum.inl false :: (List.range 8).map Sum.inr
    have hinit01_bd : ∀ i : ℕ, symBd (8 + 0) (init01.getD i (Sum.inl false)) := by
      intro i; by_cases hi : i < 10
      · rw [List.getD_eq_getElem _ _ (by simpa [init01] using hi)]
        rcases i with _ | _ | k
        · trivial
        · trivial
        · simp [init01, symBd]; omega
      · rw [List.getD_eq_default _ _ (by simp [init01]; omega)]; trivial
    have hinit01_eq : ∀ (y : Fin 8 → Bool) (i : ℕ),
        evalSym (([] : List Gate).foldl wstep (List.ofFn y)) (init01.getD i (Sum.inl false)) =
          (List.ofFn (Fin.cons true (Fin.cons false y))).getD i false := by
      intro y i; by_cases hi : i < 10
      · rw [List.getD_eq_getElem _ _ (by simpa [init01] using hi), List.getD_eq_getElem _ _ (by simp; exact hi)]
        rcases i with _ | _ | k
        · simp [init01, evalSym]
        · simp [init01, evalSym]
        · simp [init01, evalSym, show k < 8 by omega]
      · rw [List.getD_eq_default _ _ (by simp [init01]; omega), List.getD_eq_default _ _ (by simp; omega)]; rfl
    have hc01 := cstep_ind 8 C.gates init01 [] (fun y : Fin 8 → Bool => List.ofFn (Fin.cons true (Fin.cons false y)))
      (fun y => List.ofFn y) hC_agree.1 (fun _ h => by cases h) (fun _ => by simp [init01])
      (fun _ => by simp) hinit01_bd hinit01_eq
    have hdrop01 := cstep_drop_hits01 C.gates init01 [] hC_agree.1 (by simp [init01])
      ⟨true, by simp [init01]⟩ ⟨false, by simp [init01]⟩
    let res := C.gates.foldl (cstep 8) (init01, [])
    have hfin_eq : ∀ y : Fin 8 → Bool, P (Fin.cons true (Fin.cons false y)) = f10 y := by decide +kernel
    have hC_f10 : ∀ y : Fin 8 → Bool, C.eval (List.ofFn (Fin.cons true (Fin.cons false y))) = f10 y := fun y =>
      (hC_agree.2 (Fin.cons true (Fin.cons false y)) rfl).trans (hfin_eq y)
    have hnot_const : ∀ b0 : Bool, res.1.getD C.output (Sum.inl false) ≠ Sum.inl b0 := by
      intro b0 heq
      have rF := hc01.2.2.2.2 (fun _ => false) C.output
      have rT := hc01.2.2.2.2 (fun _ => true) C.output
      rw [heq] at rF rT; simp only [evalSym, Sum.elim_inl, id_eq] at rF rT
      change b0 = C.eval (List.ofFn (Fin.cons true (Fin.cons false (fun _ : Fin 8 => false)))) at rF
      change b0 = C.eval (List.ofFn (Fin.cons true (Fin.cons false (fun _ : Fin 8 => true)))) at rT
      rw [hC_f10] at rF; rw [hC_f10] at rT
      have eF : f10 (fun _ => false) = false := by decide
      have eT : f10 (fun _ => true) = true := by decide
      rw [eF] at rF; rw [eT] at rT; exact Bool.false_ne_true (rF.symm.trans rT)
    cases ho : res.1.getD C.output (Sum.inl false) with
    | inl b0 => exact False.elim (hnot_const b0 ho)
    | inr ko =>
      have hge10 : 10 ≤ res.2.length := by
        by_contra hlt
        apply hf10_lb
        refine ⟨⟨res.2, ko⟩, hc01.2.2.1, by change res.2.length ≤ 9; omega, fun y => ?_⟩
        have r := hc01.2.2.2.2 y C.output
        rw [ho] at r; simp only [evalSym, Sum.elim_inr] at r
        exact r.trans (hC_f10 y)
      have hsum : res.2.length + C.gates.countP (fun g => (reads g).contains 0 || (reads g).contains 1) ≤
          C.gates.length := by simpa using hdrop01
      change 10 + _ ≤ C.gates.length; omega

  -- Final dispatch to fewHits or manyHits
  have h11 : 11 ≤ C.size := by omega
  have hle17 : C.size ≤ 17 := hC_sz ▸ hm_le
  have hk0 : C.gates.countP (fun g => (reads g).any fun k => k == 0 ||
      (10 ≤ k && (C.gates[k - 10]?).any fun h => (reads h).contains 0 &&
        (h.op.eval [false] || h.op.eval [true, false]))) ≤ 6 := by omega
  have hk1 : C.gates.countP (fun g => (reads g).any fun k => k == 1 ||
      (10 ≤ k && (C.gates[k - 10]?).any fun h => (reads h).contains 1 &&
        (h.op.eval [false] || h.op.eval [true, false]))) ≤ 6 := by omega
  by_cases hfew : C.gates.countP (fun g => (reads g).contains 0 || (reads g).contains 1) ≤ 4
  · obtain ⟨x, hxD, hbad⟩ := fewHits C hC_agree.1 h11 hle17 hReadsBack hOutEq
      hGateArity hNoDead hAllRead hC_hits hk0 hk1 hfew
    exact hbad ((hC_agree.2 x hxD).trans (hPQ x))
  · have h5 : 5 ≤ C.gates.countP (fun g => (reads g).contains 0 || (reads g).contains 1) := by omega
    have h7 : C.gates.countP (fun g => (reads g).contains 0 || (reads g).contains 1) ≤ 7 := by omega
    have h15 : 15 ≤ C.size := by omega
    obtain ⟨x, hxD, hbad⟩ := manyHits C hC_agree.1 h15 hle17 hReadsBack hOutEq
      hGateArity hNoDead hAllRead hC_hits hk0 hk1 h5 h7 hHits01
    exact hbad ((hC_agree.2 x hxD).trans (hPQ x))
