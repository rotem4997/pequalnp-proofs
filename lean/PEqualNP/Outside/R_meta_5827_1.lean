import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 16000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_5827_1
    (noSize18 :
      let f : (Fin 10 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
      ¬ PEqualNP.MetaComplexity.HasCircuitSize 10 f 18)
    (mono19 :
      let f : (Fin 10 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
      ∀ E : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 E → E.size ≤ 19 →
        ¬ ∀ x : Fin 10 → Bool, E.eval (List.ofFn x) = f x)
    (oneNot19 :
      let f : (Fin 10 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
      ∀ A B : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 A → PEqualNP.MetaComplexity.Monotone2 B →
        A.size + B.size = 18 →
        ¬ ∀ x : Fin 10 → Bool, B.eval (A.wires (List.ofFn x) ++ [!A.eval (List.ofFn x)]) = f x)
    (multiNot19 :
      let f : (Fin 10 → Bool) → Bool := fun x =>
        x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
        x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
        x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
      ∀ (j : Fin 10) (D : PEqualNP.CircuitLowerBounds.Circuit) (u : ℕ),
        (j = 1 ∨ j = 2) → PEqualNP.MetaComplexity.FanInTwo D → D.size = 17 →
        2 ≤ PEqualNP.NotBracket.notCount D → 1 ≤ u → u < 17 →
        ¬ ∀ x : Fin 10 → Bool, let w := D.wires (List.ofFn x ++ [x 0 || x j]);
          (w.getD (10 + u) false || w.getD 27 false) = f x) :
    (∀ (x1 x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : Fin (18 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x3 →     x3.size ≤ (17 : ℕ) →       have x8 : PEqualNP.CircuitLowerBounds.Gate := { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [↑x1, ↑x2] : PEqualNP.CircuitLowerBounds.Gate };       have x9 : (Fin (10 : ℕ) → Bool) → Bool := fun (x9 : Fin (10 : ℕ) → Bool) => x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ));       have x10 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x10 : Fin (10 : ℕ) → Bool) (x11 : ℕ) => (x3.wires ({ gates := [x8], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10))).getD x11 Bool.false;       (∃ (x11 : Fin (10 : ℕ) → Bool), x10 x11 ((10 : ℕ) + ↑x4) = Bool.true ∧ x10 x11 ((10 : ℕ) + ↑x5) = Bool.false) → (∃ (x12 : Fin (10 : ℕ) → Bool), x10 x12 ((10 : ℕ) + ↑x4) = Bool.false ∧ x10 x12 ((10 : ℕ) + ↑x5) = Bool.true) → (∀ (x13 : Fin (10 : ℕ) → Bool), x9 x13 = Bool.false → x10 x13 ((10 : ℕ) + ↑x4) = Bool.false ∧ x10 x13 ((10 : ℕ) + ↑x5) = Bool.false) → ∃ (x14 : Fin (10 : ℕ) → Bool), x9 x14 = Bool.true ∧ x10 x14 ((10 : ℕ) + ↑x4) = Bool.false ∧ x10 x14 ((10 : ℕ) + ↑x5) = Bool.false) := by
  intro a b C u v fan budget
  let target (x : Fin 10 → Bool) : Bool :=
    x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5
  let x8 : Gate := ⟨.or, [a.val, b.val]⟩
  let out (x : Fin 10 → Bool) (i : ℕ) : Bool :=
    (C.wires (({ gates := [x8], output := 0 } : Circuit).wires (List.ofFn x))).getD i false
  dsimp only
  intro hEx1 hEx2 hSound
  by_contra hUncov
  have hCover : ∀ x : Fin 10 → Bool,
      (out x (10 + u.val) || out x (10 + v.val)) = target x := by
    intro x
    cases hf : target x with
    | false =>
      obtain ⟨hu, hv⟩ := hSound x hf
      change out x (10 + u.val) = false at hu
      change out x (10 + v.val) = false at hv
      simp [hu, hv]
    | true =>
      cases ha : out x (10 + u.val) <;> cases hb : out x (10 + v.val)
      · exfalso
        exact hUncov ⟨x, hf, ha, hb⟩
      · simp
      · simp
      · simp
  let step : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have wires_eq (D : Circuit) (xs : List Bool) : D.wires xs = D.gates.foldl step xs := rfl
  have stepLen (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have stepGetLt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      simp only [step, List.getD_append _ _ _ _ hi]
  have x8Wires (x : Fin 10 → Bool) :
      ({ gates := [x8], output := 0 } : Circuit).wires (List.ofFn x) =
        List.ofFn x ++ [(List.ofFn x).getD a.val false || (List.ofFn x).getD b.val false] := by
    change List.ofFn x ++ [(List.ofFn x).getD a.val false || ((List.ofFn x).getD b.val false || false)] = _
    rw [Bool.or_false]
  have fullEval (pre : Gate) (mid : List Gate) (p q : ℕ) (_hp : p < 11 + mid.length) (_hq : q < 11 + mid.length)
      (x : Fin 10 → Bool) :
      let E : Circuit := ⟨pre :: (mid ++ [⟨.or, [p, q]⟩]), 11 + mid.length⟩
      E.eval (List.ofFn x) =
        ((mid.foldl step (({ gates := [pre], output := 0 } : Circuit).wires (List.ofFn x))).getD p false ||
         (mid.foldl step (({ gates := [pre], output := 0 } : Circuit).wires (List.ofFn x))).getD q false) := by
    let ws0 := ({ gates := [pre], output := 0 } : Circuit).wires (List.ofFn x)
    let ws1 := mid.foldl step ws0
    have hws0 : ws0.length = 11 := by
      change (step (List.ofFn x) pre).length = 11
      simp [step]
    have hws1 : ws1.length = 11 + mid.length := by
      dsimp only [ws1]
      rw [stepLen, hws0]
    change ((pre :: (mid ++ [⟨.or, [p, q]⟩])).foldl step (List.ofFn x)).getD (11 + mid.length) false =
      ((mid.foldl step ws0).getD p false || (mid.foldl step ws0).getD q false)
    rw [List.foldl_cons, List.foldl_append]
    have hws0_step : step (List.ofFn x) pre = ws0 := rfl
    rw [hws0_step]
    change (step ws1 ⟨.or, [p, q]⟩).getD (11 + mid.length) false = _
    have hstep_post : step ws1 ⟨.or, [p, q]⟩ = ws1 ++ [ws1.getD p false || ws1.getD q false] := by
      change ws1 ++ [(ws1.getD p false || (ws1.getD q false || false))] = _
      rw [Bool.or_false]
    rw [hstep_post, ← hws1, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
  have h18_impossible (D : Circuit) (hDfan : FanInTwo D) (hDsz : D.size ≤ 18)
      (hDeval : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = target x) : False :=
    noSize18 ⟨D, hDfan, hDsz, hDeval⟩
  have hCsz17 : C.size = 17 := by
    by_contra hne
    have hClen : C.gates.length ≤ 17 := budget
    have hne' : C.gates.length ≠ 17 := hne
    have hle16 : C.gates.length ≤ 16 := by omega
    let E : Circuit := ⟨x8 :: (C.gates ++ [⟨.or, [10 + u.val, 10 + v.val]⟩]), 11 + C.gates.length⟩
    have hEfan : FanInTwo E := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨Or.inr (Or.inl rfl), Nat.le_refl 2⟩
      · rcases List.mem_append.mp hg with hg | hg
        · exact fan g hg
        · obtain rfl := List.mem_singleton.mp hg
          exact ⟨Or.inr (Or.inl rfl), Nat.le_refl 2⟩
    have hEsz : E.size ≤ 18 := by
      show (x8 :: (C.gates ++ [(⟨.or, [10 + u.val, 10 + v.val]⟩ : Gate)])).length ≤ 18
      rw [List.length_cons, List.length_append, List.length_singleton]
      omega
    have hu_lt : 10 + u.val < 11 + C.gates.length := by
      by_contra! hge
      obtain ⟨y, hy, _⟩ := hEx1
      rw [wires_eq] at hy
      have hl : (C.gates.foldl step (({ gates := [x8], output := 0 } : Circuit).wires (List.ofFn y))).length = 11 + C.gates.length := by
        rw [stepLen, x8Wires]; simp
      rw [List.getD_eq_default _ _ (by rw [hl]; exact hge)] at hy
      cases hy
    have hv_lt : 10 + v.val < 11 + C.gates.length := by
      by_contra! hge
      obtain ⟨y, _, hy⟩ := hEx2
      rw [wires_eq] at hy
      have hl : (C.gates.foldl step (({ gates := [x8], output := 0 } : Circuit).wires (List.ofFn y))).length = 11 + C.gates.length := by
        rw [stepLen, x8Wires]; simp
      rw [List.getD_eq_default _ _ (by rw [hl]; exact hge)] at hy
      cases hy
    apply h18_impossible E hEfan hEsz
    intro x
    have hev := fullEval x8 C.gates (10 + u.val) (10 + v.val) hu_lt hv_lt x
    change E.eval (List.ofFn x) = _ at hev
    rw [hev]
    exact hCover x
  have hDegenerate : a.val < 10 ∧ b.val < 10 ∧ a ≠ b := by
    by_contra hbad
    let rep : ℕ :=
      if a.val = 10 ∧ b.val = 10 then 99
      else if a.val = 10 then b.val
      else a.val
    have hrepRange : rep < 10 ∨ rep = 99 := by
      dsimp only [rep]
      split_ifs with h1 h2
      · exact Or.inr rfl
      · exact Or.inl (by have := b.isLt; omega)
      · have : a.val < 10 ∨ b.val < 10 := by
          by_contra! h10
          exact h1 ⟨by have := a.isLt; omega, by have := b.isLt; omega⟩
        by_cases ha10 : a.val = 10
        · exact absurd ha10 h2
        · exact Or.inl (by have := a.isLt; omega)
    have hrepVal (x : Fin 10 → Bool) :
        ((List.ofFn x).getD a.val false || (List.ofFn x).getD b.val false) =
          (List.ofFn x).getD rep false := by
      dsimp only [rep]
      split_ifs with h1 h2
      · rw [h1.1, h1.2, List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp)]
        rfl
      · have haf : (List.ofFn x).getD a.val false = false :=
          List.getD_eq_default _ _ (by simp [h2])
        rw [haf, Bool.false_or]
      · by_cases hb10 : b.val = 10
        · have hbf : (List.ofFn x).getD b.val false = false :=
            List.getD_eq_default _ _ (by simp [hb10])
          rw [hbf, Bool.or_false]
        · have hab : a = b := by
            by_contra hne
            apply hbad
            exact ⟨by have := a.isLt; omega, by have := b.isLt; omega, hne⟩
          rw [hab, Bool.or_self]
    let ρ0 (i : ℕ) : ℕ := if i < 10 then i else if i = 10 then rep else i - 1
    have hρ0 (n : ℕ) (hlo : 10 ≤ n) (hhi : n ≤ 28) (i : ℕ) : ρ0 i = n ↔ i = n + 1 := by
      by_cases hi : i < 10
      · simp only [ρ0, ite_eq_left hi]; omega
      · by_cases hi10 : i = 10
        · simp only [ρ0, ite_eq_right hi, ite_eq_left hi10]
          rcases hrepRange with hr | hr <;> omega
        · simp only [ρ0, ite_eq_right hi, ite_eq_right hi10]
          omega
    let rg0 (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ0⟩
    have app (w : List Bool) (z : Bool) (i : ℕ) :
        (w ++ [z]).getD i false = if i = w.length then z else w.getD i false := by
      by_cases hi : i < w.length
      · rw [List.getD_append _ _ _ _ hi, ite_eq_right (by omega)]
      · by_cases heq : i = w.length
        · subst i; simp [List.getD_eq_getElem?_getD]
        · rw [ite_eq_right heq, List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by omega)]
    have simDrop (gs : List Gate) (xs ys : List Bool)
        (hlen : xs.length = ys.length + 1) (hlow : 11 ≤ xs.length) (hcap : xs.length + gs.length ≤ 29)
        (hinit : ∀ i, xs.getD i false = ys.getD (ρ0 i) false) :
        ∀ i, (gs.foldl step xs).getD i false = ((gs.map rg0).foldl step ys).getD (ρ0 i) false := by
      induction gs generalizing xs ys with
      | nil => exact hinit
      | cons g gs ih =>
        let z := g.op.eval (g.inputs.map fun i => xs.getD i false)
        have hnext : (rg0 g).op.eval ((rg0 g).inputs.map fun i => ys.getD i false) = z := by
          change g.op.eval _ = g.op.eval _
          congr 1
          simp only [rg0, List.map_map, Function.comp_def]
          exact List.map_congr_left fun i _ => (hinit i).symm
        change ∀ i, (gs.foldl step (xs ++ [z])).getD i false =
          ((gs.map rg0).foldl step (ys ++ [(rg0 g).op.eval ((rg0 g).inputs.map fun i => ys.getD i false)])).getD (ρ0 i) false
        rw [hnext]
        apply ih
        · simp [hlen]
        · simp; omega
        · simp only [List.length_append, List.length_cons, List.length_nil] at hcap ⊢; omega
        · intro i
          have hcond : (ρ0 i = ys.length) ↔ (i = xs.length) := by
            rw [hρ0 ys.length (by omega) (by omega) i, hlen]
          simp only [app, hcond, hinit i]
    let D0 : Circuit := ⟨C.gates.map rg0 ++ [⟨.or, [ρ0 (10 + u.val), ρ0 (10 + v.val)]⟩], 10 + C.gates.length⟩
    have hD0fan : FanInTwo D0 := by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
        simpa [rg0] using fan g' hg'
      · obtain rfl := List.mem_singleton.mp hg
        exact ⟨Or.inr (Or.inl rfl), Nat.le_refl 2⟩
    have hD0sz : D0.size ≤ 18 := by
      show (C.gates.map rg0 ++ [(⟨.or, [ρ0 (10 + u.val), ρ0 (10 + v.val)]⟩ : Gate)]).length ≤ 18
      simp only [List.length_append, List.length_map, List.length_singleton]
      have hClen : C.gates.length = 17 := hCsz17
      omega
    apply h18_impossible D0 hD0fan hD0sz
    intro x
    have hsim (i : ℕ) : out x i = ((C.gates.map rg0).foldl step (List.ofFn x)).getD (ρ0 i) false := by
      dsimp only [out]
      rw [wires_eq, x8Wires]
      apply simDrop
      · simp
      · simp
      · have hClen : C.gates.length = 17 := hCsz17
        simp only [List.length_append, List.length_ofFn, List.length_singleton]
        omega
      · intro k
        by_cases hk : k < 10
        · simp only [ρ0, ite_eq_left hk]
          rw [List.getD_append _ _ _ _ (by simp [hk])]
        · by_cases hk10 : k = 10
          · subst k
            simp only [ρ0, show ¬ 10 < 10 by decide, ite_eq_left]
            rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.sub_self, List.getD_cons_zero]
            exact hrepVal x
          · simp only [ρ0, ite_eq_right hk, ite_eq_right hk10]
            rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    let W := (C.gates.map rg0).foldl step (List.ofFn x)
    have hWlen : W.length = 10 + C.gates.length := by
      dsimp only [W]; rw [stepLen, List.length_ofFn, List.length_map]
    show (D0.wires (List.ofFn x)).getD (10 + C.gates.length) false = target x
    rw [wires_eq]
    dsimp only [D0]
    rw [List.foldl_append]
    change (W ++ [(W.getD (ρ0 (10 + u.val)) false || (W.getD (ρ0 (10 + v.val)) false || false))]).getD (10 + C.gates.length) false = _
    rw [Bool.or_false]
    rw [← hWlen, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero]
    rw [← hsim (10 + u.val), ← hsim (10 + v.val)]
    exact hCover x
  obtain ⟨haLt, hbLt, habNe⟩ := hDegenerate
  have hunitFalse (k : Fin 10) : target (fun i => decide (i = k)) = false := by
    fin_cases k <;> decide
  have huPos : 1 ≤ u.val := by
    by_contra! hu0
    have h0 : u.val = 0 := by omega
    let z : Fin 10 → Bool := fun i => decide (i = ⟨a.val, haLt⟩)
    have hs := (hSound z (hunitFalse ⟨a.val, haLt⟩)).1
    have h10 : out z (10 + u.val) = true := by
      dsimp only [out]
      rw [h0, Nat.add_zero, wires_eq, stepGetLt _ _ _ (by rw [x8Wires]; simp), x8Wires,
        List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.sub_self, List.getD_cons_zero]
      rw [List.getD_eq_getElem _ _ (by simpa using haLt), List.getElem_ofFn]
      simp [z]
    change out z (10 + u.val) = false at hs
    rw [h10] at hs
    cases hs
  have hvPos : 1 ≤ v.val := by
    by_contra! hv0
    have h0 : v.val = 0 := by omega
    let z : Fin 10 → Bool := fun i => decide (i = ⟨a.val, haLt⟩)
    have hs := (hSound z (hunitFalse ⟨a.val, haLt⟩)).2
    have h10 : out z (10 + v.val) = true := by
      dsimp only [out]
      rw [h0, Nat.add_zero, wires_eq, stepGetLt _ _ _ (by rw [x8Wires]; simp), x8Wires,
        List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.sub_self, List.getD_cons_zero]
      rw [List.getD_eq_getElem _ _ (by simpa using haLt), List.getElem_ofFn]
      simp [z]
    change out z (10 + v.val) = false at hs
    rw [h10] at hs
    cases hs
  have huvNe : u.val ≠ v.val := by
    intro heq
    obtain ⟨y, hy1, hy2⟩ := hEx1
    rw [heq] at hy1
    rw [hy1] at hy2
    cases hy2
  have hOneAt17 : u.val = 17 ∨ v.val = 17 := by
    by_contra hlt
    have hu17 : u.val < 17 := by have := u.isLt; omega
    have hv17 : v.val < 17 := by have := v.isLt; omega
    let init := C.gates.take 16
    have hinitLen : init.length = 16 := by
      dsimp only [init]; rw [List.length_take]; have hClen : C.gates.length = 17 := hCsz17; omega
    have hsplit : C.gates = init ++ C.gates.drop 16 := (List.take_append_drop 16 C.gates).symm
    let E : Circuit := ⟨x8 :: (init ++ [⟨.or, [10 + u.val, 10 + v.val]⟩]), 11 + init.length⟩
    have hEfan : FanInTwo E := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨Or.inr (Or.inl rfl), Nat.le_refl 2⟩
      · rcases List.mem_append.mp hg with hg | hg
        · exact fan g (List.mem_of_mem_take hg)
        · obtain rfl := List.mem_singleton.mp hg
          exact ⟨Or.inr (Or.inl rfl), Nat.le_refl 2⟩
    have hEsz : E.size ≤ 18 := by
      show (x8 :: (init ++ [(⟨.or, [10 + u.val, 10 + v.val]⟩ : Gate)])).length ≤ 18
      simp [hinitLen]
    apply h18_impossible E hEfan hEsz
    intro x
    have hev := fullEval x8 init (10 + u.val) (10 + v.val) (by omega) (by omega) x
    change E.eval (List.ofFn x) = _ at hev
    rw [hev]
    have hkeep (p : ℕ) (hp : p < 27) :
        (init.foldl step (({ gates := [x8], output := 0 } : Circuit).wires (List.ofFn x))).getD p false = out x p := by
      dsimp only [out]
      conv_rhs => rw [wires_eq C, hsplit, List.foldl_append]
      rw [stepGetLt (C.gates.drop 16) _ _ (by rw [stepLen, x8Wires]; simp; omega)]
    rw [hkeep (10 + u.val) (by omega), hkeep (10 + v.val) (by omega)]
    exact hCover x
  let u1 : ℕ := if v.val = 17 then u.val else v.val
  have hu1_lo : 1 ≤ u1 := by dsimp only [u1]; split_ifs <;> omega
  have hu1_hi : u1 < 17 := by dsimp only [u1]; split_ifs <;> omega
  have hCoverOrd (x : Fin 10 → Bool) : (out x (10 + u1) || out x 27) = target x := by
    dsimp only [u1]
    rcases hOneAt17 with hu17 | hv17
    · by_cases hv17 : v.val = 17
      · exact absurd (hu17.trans hv17.symm) huvNe
      · rw [ite_eq_right hv17, show (27 : ℕ) = 10 + 17 from rfl, ← hu17, Bool.or_comm]
        exact hCover x
    · rw [ite_eq_left hv17, show (27 : ℕ) = 10 + 17 from rfl, ← hv17]
      exact hCover x

  let generator (g : Bool) (i : Fin 10) : Fin 10 :=
    ((if g then [2, 1, 6, 8, 3, 7, 0, 9, 5, 4] else [1, 0, 4, 3, 2, 6, 5, 9, 8, 7]) : List (Fin 10)).getD i.val 0
  let run (w : List Bool) (i : Fin 10) := w.foldr generator i
  let words : List (List Bool) := [[], [], [], [false, true, false, true, true, true], [false, true, false, true, true, true], [false, true, false], [true, true, true, false, true, true, true, false], [false, true, false], [false, true, true, true, true, false], [true, true, true, false, true, true, false], [], [false], [false], [false, true, false, true, true, true, false], [false, true, false, true, true, true, false], [false], [false, true, true, true], [false, true, true, true, true], [true, true, true, false, true, true], [false, true, true, true, true], [false, true], [false], [true, false, true, true, true, false], [true, false, true, true, true, false], [true, false, true, true, true, false], [true, false, true, false, true, true, false], [true, false, true, false, true, true, false], [false, true, false, true, false, true, true, true, false], [true, true, true, true, true], [false, true, false, true, false, true, true, true, false], [true, false, true, false, true, false, true, false], [false, true, true, true, true, true, false, true, true], [true, false, true, true, true, false], [false, true, false, true, false, true, true], [true, true, true, true, false, true, true], [true, true, true, true, false, true, true], [false, true, false, true, false, true, true], [false, true, false, true, false, true, true], [true, false, true, false, true, false], [true, false, true, false, true], [false, true, false, true, false, true, false, true, false], [true, false, true, false, true, false], [false, true, false, true, false, true, false, true], [false, true, false, true, false, true, true], [true, false, true, true, true], [true, false, true, true, true], [true, false, true, false, true, true], [true, false, true, false, true, true], [true, false, true, true, true], [true, true, false], [false, true, false, true, false, true, true, true], [false, true, false, true, true, true, true, true, false], [false, true, false, true, true, false], [false, true, false, true, false, true, true, true], [true, false, true, true, true], [true, false], [true, false], [false, true, false, true, true, true, true, false], [false, true, true, true, true, false, true, false], [true, true, false, true, true, true], [true, false], [false, true, false, true, false], [false, true, false, true, true, true, true, false], [false, true, false, true, false], [true, true, false, true, true, false, true, true], [true, false], [true], [true], [true, true, false, true, true, true, false], [true, true, false, true, false, true, false], [false, true, false, true, true, true, true], [false, true, false, true], [true], [false, true, true, false, true], [false, true, false, true], [false, true, false, true, true, true, true], [true], [true, false, true, true, true, true, false], [true, false, true, false, true, true, true, false], [true, false, true, false, true, true, true, false], [true, true, true, true, true, false, true, true], [true, false, true, false, true, false, true, true, true], [true, false, true, true, true, true, false], [true, false, true, false, true, true, true, true], [true, false, true, true, true, true, false], [true, true, false, true, false], [true, false, true, false, true, false, true, true, true], [true, false, true, true, true, true, false], [true, false, true, false], [true, false, true], [false, true, false, true, false, true], [false, true, false, true, false, true, false], [false, true, false, true, false, true, false], [true, false, true, false], [true, false, true], [false, true, true, false, true, false, true], [true, false, true, false], [true, true, false, true, true, true, true], [true, false, true, false], [true, false, true, false, true, true, true], [true, false, true, true, true, true], [false, true, false, true, false, true, true, true, true], [true, false, true, false, true, false, true, true], [true, false, true, false, true, true, true], [true, false, true, false, true, true, true, true, false], [true, false, true, true, true, true], [true, false, true, false, true, true, true, true, false], [true, true, false, true], [true, false, true, false, true, true, true], [true, false, true, false, true, true, true], [], [false], [true, false, true, true, true, false], [false, true, false, true, false, true, true], [true, false, true, true, true], [true, false], [true], [true, false, true, true, true, true, false], [true, false, true, false], [true, false, true, false, true, true, true], []]
  let second : List (Fin 10) := [1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  let source : List Nat := [0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 10, 0, 10, 10, 10, 10, 10, 10, 10, 10, 0, 10, 10, 0, 10, 10, 10, 10, 10, 10, 10, 0, 10, 10, 10, 0, 10, 10, 10, 10, 10, 10, 0, 10, 10, 10, 10, 0, 10, 10, 10, 10, 10, 0, 10, 10, 10, 10, 10, 0, 10, 10, 10, 10, 0, 10, 10, 10, 10, 10, 10, 0, 10, 10, 10, 0, 10, 10, 10, 10, 10, 10, 10, 0, 10, 10, 0, 10, 10, 10, 10, 10, 10, 10, 10, 0, 10, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99]
  let ix (p q : Fin 11) := p.val * 11 + q.val
  let σ (i : Fin 10) : Fin 10 := run (words.getD (ix a b) []) i
  let j : Fin 10 := second.getD (ix a b) 1
  let src := source.getD (ix a b) 0
  have choices : ∀ p q : Fin 11, second.getD (ix p q) 1 = 1 ∨ second.getD (ix p q) 1 = 2 := by decide +kernel
  have kinds : ∀ p q : Fin 11, p.val < 10 → q.val < 10 → p ≠ q →
      source.getD (ix p q) 0 = 10 ∧
      run (words.getD (ix p q) []) ⟨p.val % 10, Nat.mod_lt _ (by decide)⟩ = 0 ∧
      run (words.getD (ix p q) []) ⟨q.val % 10, Nat.mod_lt _ (by decide)⟩ = second.getD (ix p q) 1 := by decide +kernel
  have hj : j = 1 ∨ j = 2 := choices a b
  obtain ⟨hsrc, hσa, hσb⟩ := kinds a b haLt hbLt habNe
  have one (g : Bool) (x : Fin 10 → Bool) : target (x ∘ generator g) = target x := by
    cases g
    · change ((x 1 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 2) || (x 2 && x 1) || (x 1 && x 6) || (x 0 && x 5) || (x 4 && x 9) || (x 3 && x 8) || (x 2 && x 7) || (x 6 && x 9) || (x 9 && x 7) || (x 7 && x 5) || (x 5 && x 8) || (x 8 && x 6)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change ((x 2 && x 1) || (x 1 && x 6) || (x 6 && x 8) || (x 8 && x 3) || (x 3 && x 2) || (x 2 && x 7) || (x 1 && x 0) || (x 6 && x 9) || (x 8 && x 5) || (x 3 && x 4) || (x 7 && x 9) || (x 9 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 5 && x 7)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
  have word (w : List Bool) (x : Fin 10 → Bool) : target (x ∘ run w) = target x := by
    induction w generalizing x with
    | nil => rfl
    | cons g w ih => exact (ih (x ∘ generator g)).trans (one g x)
  have invariant (x : Fin 10 → Bool) : target (x ∘ σ) = target x := word _ x
  let ρ (i : Nat) := if h : i < 10 then (σ ⟨i, h⟩).val else if i = 10 then 10 else i
  have hρ (n : Nat) (lo : 11 ≤ n) (hi : n ≤ 28) (i : Nat) : ρ i = n ↔ i = n := by
    by_cases h : i < 10
    · simp only [ρ, dite_eq_left h]
      have := (σ ⟨i, h⟩).isLt
      omega
    · by_cases e : i = 10
      · simp only [ρ, dite_eq_right h, ite_eq_left e]; omega
      · simp [ρ, h, e]
  let rg (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩
  have app (w : List Bool) (z : Bool) (i : Nat) :
      (w ++ [z]).getD i false = if i = w.length then z else w.getD i false := by
    by_cases hi : i < w.length
    · rw [List.getD_append _ _ _ _ hi, ite_eq_right (by omega)]
    · by_cases eq : i = w.length
      · subst i; simp [List.getD_eq_getElem?_getD]
      · rw [ite_eq_right eq, List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by omega)]
  have simulation (gs : List Gate) (xs ys : List Bool)
      (len : xs.length = ys.length) (lower : 11 ≤ xs.length) (cap : xs.length + gs.length ≤ 28)
      (initial : ∀ i, xs.getD i false = ys.getD (ρ i) false) :
      ∀ i, (gs.foldl step xs).getD i false =
        ((gs.map rg).foldl step ys).getD (ρ i) false := by
    induction gs generalizing xs ys with
    | nil => exact initial
    | cons g gs ih =>
      let z := g.op.eval (g.inputs.map fun i => xs.getD i false)
      have next : (rg g).op.eval ((rg g).inputs.map fun i => ys.getD i false) = z := by
        change g.op.eval _ = g.op.eval _
        congr 1
        simp only [rg, List.map_map, Function.comp_def]
        exact List.map_congr_left fun i _ => (initial i).symm
      change ∀ i, (gs.foldl step (xs ++ [z])).getD i false =
        ((gs.map rg).foldl step (ys ++ [(rg g).op.eval ((rg g).inputs.map fun i => ys.getD i false)])).getD (ρ i) false
      rw [next]
      apply ih
      · simp [len]
      · simp; omega
      · simp_all only [List.length_cons, List.length_append, List.length_nil]; omega
      · intro i
        simp only [app, ← len, hρ _ lower (by omega) i, initial i]
  let D : Circuit := ⟨C.gates.map rg, 0⟩
  have hDfan : FanInTwo D := by
    intro g hg
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
    simpa [rg] using fan h hh
  have hDsz : D.size = 17 := by
    change (C.gates.map rg).length = 17
    rw [List.length_map]; exact hCsz17
  have hDeval (x : Fin 10 → Bool) :
      let w := D.wires (List.ofFn x ++ [x 0 || x j])
      (w.getD (10 + u1) false || w.getD 27 false) = target x := by
    let y := x ∘ σ
    have hsim (i : ℕ) : out y i = (D.wires (List.ofFn x ++ [x 0 || x j])).getD (ρ i) false := by
      dsimp only [out]
      rw [wires_eq C, wires_eq D, x8Wires]
      apply simulation
      · simp
      · simp
      · have hClen : C.gates.length = 17 := hCsz17
        simp only [List.length_append, List.length_ofFn, List.length_singleton]
        omega
      · intro k
        by_cases hk : k < 10
        · simp only [ρ, dite_eq_left hk]
          rw [List.getD_append _ _ _ _ (by simpa using hk), List.getD_append _ _ _ _ (by simp)]
          rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getD_eq_getElem _ _ (by simp)]
          simp only [List.getElem_ofFn]; rfl
        · by_cases hk10 : k = 10
          · subst k
            simp only [ρ, show ¬ 10 < 10 by decide, dite_false, ite_true]
            rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.sub_self, List.getD_cons_zero]
            rw [List.getD_append_right _ _ _ _ (by simp), List.length_ofFn, Nat.sub_self, List.getD_cons_zero]
            rw [List.getD_eq_getElem _ _ (by simpa using haLt), List.getElem_ofFn,
              List.getD_eq_getElem _ _ (by simpa using hbLt), List.getElem_ofFn]
            have e1 : σ ⟨a.val, haLt⟩ = 0 := by
              dsimp only [σ]; simpa [Nat.mod_eq_of_lt haLt] using hσa
            have e2 : σ ⟨b.val, hbLt⟩ = j := by
              dsimp only [σ, j]; simpa [Nat.mod_eq_of_lt hbLt] using hσb
            change (y ⟨a.val, haLt⟩ || y ⟨b.val, hbLt⟩) = (x 0 || x j)
            change (x (σ ⟨a.val, haLt⟩) || x (σ ⟨b.val, hbLt⟩)) = (x 0 || x j)
            rw [e1, e2]
          · simp only [ρ, dite_eq_right hk, ite_eq_right hk10]
            rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    have hρu : ρ (10 + u1) = 10 + u1 := (hρ (10 + u1) (by omega) (by omega) (10 + u1)).mpr rfl
    have hρv : ρ 27 = 27 := (hρ 27 (by omega) (by omega) 27).mpr rfl
    dsimp only
    rw [← hρu, ← hρv, ← hsim (10 + u1), ← hsim 27, hCoverOrd y, invariant x]

  let nc := PEqualNP.NotBracket.notCount D
  let isNotPred : Gate → Bool := fun g => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)
  by_cases hnc0 : nc = 0
  · have hDmono : ∀ g ∈ D.gates, g.op = .and ∨ g.op = .or := by
      intro g hg
      obtain ⟨hop, _⟩ := hDfan g hg
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        have hpos : 0 < (D.gates.filter isNotPred).length := by
          have hm : g ∈ D.gates.filter isNotPred :=
            List.mem_filter.mpr ⟨hg, by dsimp only [isNotPred]; exact @decide_eq_true _ (lineDegreeGateOpDecEq _ _) h⟩
          cases hf : D.gates.filter isNotPred with
          | nil => simp [hf] at hm
          | cons _ _ => exact Nat.zero_lt_succ _
        have hnc0' : (D.gates.filter isNotPred).length = 0 := hnc0
        omega
    let pre : Gate := ⟨.or, [0, j.val]⟩
    let post : Gate := ⟨.or, [10 + u1, 27]⟩
    let E : Circuit := ⟨pre :: (D.gates ++ [post]), 28⟩
    have hEmono : Monotone2 E := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨Or.inr rfl, Nat.le_refl 2⟩
      · rcases List.mem_append.mp hg with hg | hg
        · obtain ⟨_, hlen⟩ := hDfan g hg
          have hno := hDmono g hg
          exact ⟨hno.elim (fun h => Or.inl h) (fun h => Or.inr h), hlen⟩
        · obtain rfl := List.mem_singleton.mp hg
          exact ⟨Or.inr rfl, Nat.le_refl 2⟩
    have hEsz : E.size ≤ 19 := by
      show (pre :: (D.gates ++ [post])).length ≤ 19
      have hDlen : D.gates.length = 17 := hDsz
      simp [hDlen]
    apply mono19 E hEmono hEsz
    intro x
    have hpre : ({ gates := [pre], output := 0 } : Circuit).wires (List.ofFn x) = List.ofFn x ++ [x 0 || x j] := by
      change List.ofFn x ++ [(List.ofFn x).getD 0 false || ((List.ofFn x).getD j.val false || false)] = _
      rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simp), Bool.or_false]
      simp only [List.getElem_ofFn]
      rfl
    have hEev : E.eval (List.ofFn x) =
        ((D.wires (List.ofFn x ++ [x 0 || x j])).getD (10 + u1) false ||
         (D.wires (List.ofFn x ++ [x 0 || x j])).getD 27 false) := by
      have hDlen : D.gates.length = 17 := hDsz
      have hev := fullEval pre D.gates (10 + u1) 27 (by omega) (by omega) x
      change (⟨pre :: (D.gates ++ [post]), 11 + D.gates.length⟩ : Circuit).eval (List.ofFn x) = _ at hev
      rw [hDlen] at hev
      change E.eval (List.ofFn x) = _
      rw [hev, hpre, ← wires_eq D]
    rw [hEev]
    exact hDeval x
  · by_cases hnc1 : nc = 1
    · let pre : Gate := ⟨.or, [0, j.val]⟩
      let post : Gate := ⟨.or, [10 + u1, 27]⟩
      let E : Circuit := ⟨pre :: (D.gates ++ [post]), 28⟩
      have hEfan : FanInTwo E := by
        intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact ⟨Or.inr (Or.inl rfl), Nat.le_refl 2⟩
        · rcases List.mem_append.mp hg with hg | hg
          · exact hDfan g hg
          · obtain rfl := List.mem_singleton.mp hg
            exact ⟨Or.inr (Or.inl rfl), Nat.le_refl 2⟩
      have hEsz : E.size = 19 := by
        show (pre :: (D.gates ++ [post])).length = 19
        have hDlen : D.gates.length = 17 := hDsz
        simp [hDlen]
      have hEnot : (E.gates.filter isNotPred).length = 1 := by
        change ((pre :: (D.gates ++ [post])).filter isNotPred).length = 1
        rw [List.filter_cons_of_neg (by simp [isNotPred, pre]), List.filter_append,
          List.filter_cons_of_neg (by simp [isNotPred, post]), List.filter_nil, List.append_nil]
        have hnc1' : (D.gates.filter isNotPred).length = 1 := hnc1
        exact hnc1'
      have hSplit : ∀ gs : List Gate, (gs.filter isNotPred).length = 1 →
          ∃ before g after, gs = before ++ g :: after ∧ g.op = .not ∧
            (∀ h ∈ before, h.op ≠ .not) ∧ (∀ h ∈ after, h.op ≠ .not) := by
        intro gs
        induction gs with
        | nil => intro h; simp at h
        | cons x xs ih =>
          intro h
          by_cases hx : x.op = .not
          · rw [List.filter_cons_of_pos (by simp [isNotPred, hx]), List.length_cons] at h
            have h0 : (xs.filter isNotPred).length = 0 := by omega
            refine ⟨[], x, xs, rfl, hx, fun _ hm => by simp at hm, fun y hy heq => ?_⟩
            have hm : y ∈ xs.filter isNotPred :=
              List.mem_filter.mpr ⟨hy, by simp [isNotPred, heq]⟩
            rw [List.length_eq_zero_iff.mp h0] at hm
            simp at hm
          · rw [List.filter_cons_of_neg (by simp [isNotPred, hx])] at h
            obtain ⟨bef, g, aft, hgs, hg, hbef, haft⟩ := ih h
            refine ⟨x :: bef, g, aft, by rw [hgs]; rfl, hg, ?_, haft⟩
            intro y hy
            rcases List.mem_cons.mp hy with rfl | hy
            · exact hx
            · exact hbef y hy
      obtain ⟨bef, gnot, aft, hEeq, hgnot, hbefNo, haftNo⟩ := hSplit E.gates hEnot
      let w : ℕ := gnot.inputs.headD (10 + bef.length)
      let A : Circuit := ⟨bef, w⟩
      let B : Circuit := ⟨aft, 28⟩
      have hAmono : Monotone2 A := by
        intro g hg
        have hgE : g ∈ E.gates := by rw [hEeq]; exact List.mem_append_left _ hg
        obtain ⟨hop, hlen⟩ := hEfan g hgE
        refine ⟨?_, hlen⟩
        rcases hop with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h (hbefNo g hg)
      have hBmono : Monotone2 B := by
        intro g hg
        have hgE : g ∈ E.gates := by rw [hEeq]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hg)
        obtain ⟨hop, hlen⟩ := hEfan g hgE
        refine ⟨?_, hlen⟩
        rcases hop with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact absurd h (haftNo g hg)
      have hABsz : A.size + B.size = 18 := by
        have hlen := congrArg List.length hEeq
        simp only [List.length_append, List.length_cons] at hlen
        change bef.length + aft.length = 18
        change E.gates.length = 19 at hEsz
        omega
      apply oneNot19 A B hAmono hBmono hABsz
      intro x
      have hstep : A.wires (List.ofFn x) ++ [!A.eval (List.ofFn x)] =
          (bef ++ [gnot]).foldl step (List.ofFn x) := by
        rw [List.foldl_append]
        change A.wires (List.ofFn x) ++ [!((A.wires (List.ofFn x)).getD w false)] =
          step (bef.foldl step (List.ofFn x)) gnot
        rw [wires_eq A]
        change bef.foldl step (List.ofFn x) ++ [!((bef.foldl step (List.ofFn x)).getD w false)] =
          bef.foldl step (List.ofFn x) ++ [gnot.op.eval (gnot.inputs.map fun i => (bef.foldl step (List.ofFn x)).getD i false)]
        congr 2
        rw [hgnot]
        cases hins : gnot.inputs with
        | nil =>
          dsimp only [w]
          rw [hins]
          have hl : (bef.foldl step (List.ofFn x)).length = 10 + bef.length := by
            rw [stepLen, List.length_ofFn]
          rw [List.getD_eq_default _ _ (by rw [hl]; rfl)]
          rfl
        | cons i rest =>
          dsimp only [w]
          rw [hins]
          rfl
      have hABeval : B.eval (A.wires (List.ofFn x) ++ [!A.eval (List.ofFn x)]) = E.eval (List.ofFn x) := by
        change (B.wires (A.wires (List.ofFn x) ++ [!A.eval (List.ofFn x)])).getD 28 false =
          (E.wires (List.ofFn x)).getD 28 false
        rw [wires_eq B, hstep, wires_eq E, hEeq]
        have heq : bef ++ gnot :: aft = (bef ++ [gnot]) ++ aft := by simp
        simp only [heq, List.foldl_append]
        rfl
      rw [hABeval]
      have hpre : ({ gates := [pre], output := 0 } : Circuit).wires (List.ofFn x) = List.ofFn x ++ [x 0 || x j] := by
        change List.ofFn x ++ [(List.ofFn x).getD 0 false || ((List.ofFn x).getD j.val false || false)] = _
        rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simp), Bool.or_false]
        simp only [List.getElem_ofFn]
        rfl
      have hEev : E.eval (List.ofFn x) =
          ((D.wires (List.ofFn x ++ [x 0 || x j])).getD (10 + u1) false ||
           (D.wires (List.ofFn x ++ [x 0 || x j])).getD 27 false) := by
        have hDlen : D.gates.length = 17 := hDsz
        have hev := fullEval pre D.gates (10 + u1) 27 (by omega) (by omega) x
        change (⟨pre :: (D.gates ++ [post]), 11 + D.gates.length⟩ : Circuit).eval (List.ofFn x) = _ at hev
        rw [hDlen] at hev
        change E.eval (List.ofFn x) = _
        rw [hev, hpre, ← wires_eq D]
      rw [hEev]
      exact hDeval x
    · have hge2 : 2 ≤ nc := by omega
      exact multiNot19 j D u1 hj hDfan hDsz hge2 hu1_lo hu1_hi hDeval
