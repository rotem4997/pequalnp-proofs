import PEqualNP.Defs

-- Normalize the free gate by Petersen graph symmetries. The two binary children
-- use fixed edge and nonedge representatives. The other children use one signed
-- raw input or a constant. An unsigned raw alias is redirected to that input.
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 3000 in
theorem PEqualNP.Outside.R_meta_5792_643
    (hEdge : ∀ (a b : Bool) (C : Circuit), FanInTwo C → C.size ≤ 17 →
      11 ≤ C.output → C.output < 11 + C.size →
      (∀ i : Fin 10, ∃ g ∈ C.gates, i.val ∈ g.inputs) →
      ∃ x : Fin 10 → Bool,
        let y := C.eval (List.ofFn x ++ [if a then x 0 && x 1 else x 0 || x 1])
        (if b then !y else y) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (hNonedge : ∀ (a b : Bool) (C : Circuit), FanInTwo C → C.size ≤ 17 →
      11 ≤ C.output → C.output < 11 + C.size →
      (∀ i : Fin 10, ∃ g ∈ C.gates, i.val ∈ g.inputs) →
      ∃ x : Fin 10 → Bool,
        let y := C.eval (List.ofFn x ++ [if a then x 0 && x 2 else x 0 || x 2])
        (if b then !y else y) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (hSigned : ∀ (b : Bool) (C : Circuit), FanInTwo C → C.size ≤ 17 →
      11 ≤ C.output → C.output < 11 + C.size →
      (∀ i : Fin 10, i ≠ 0 → ∃ g ∈ C.gates, i.val ∈ g.inputs) →
      ∃ x : Fin 10 → Bool,
        let y := C.eval (List.ofFn x ++ [!x 0])
        (if b then !y else y) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    (hConst : ∀ (a b : Bool) (C : Circuit), FanInTwo C → C.size ≤ 17 →
      11 ≤ C.output → C.output < 11 + C.size →
      (∀ i : Fin 10, ∃ g ∈ C.gates, i.val ∈ g.inputs) →
      ∃ x : Fin 10 → Bool,
        let y := C.eval (List.ofFn x ++ [a])
        (if b then !y else y) ≠
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5))
    : ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         x2.size = (17 : ℕ) →           have x9 : (Fin (10 : ℕ) → Bool) → Bool := fun (x9 : Fin (10 : ℕ) → Bool) => x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ));           have x10 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x10 : Fin (10 : ℕ) → Bool) (x11 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10))).getD x11 Bool.false;           ∃ (x11 : Fin (10 : ℕ) → Bool), (if x4 = Bool.true then !x10 x11 x3 else x10 x11 x3) ≠ x9 x11 := by
  classical
  intro g C u b hg hC hsize _
  let f (x : Fin 10 → Bool) : Bool :=
    (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
     x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
     x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)
  let rootTable : List (List (Fin 10)) :=
    [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
     [1, 0, 4, 3, 2, 6, 5, 9, 8, 7],
     [2, 1, 0, 4, 3, 7, 6, 5, 9, 8],
     [2, 3, 4, 0, 1, 7, 8, 9, 5, 6],
     [1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
     [1, 2, 3, 8, 6, 0, 7, 4, 5, 9],
     [2, 1, 6, 8, 3, 7, 0, 9, 5, 4],
     [2, 3, 4, 9, 7, 1, 8, 0, 6, 5],
     [2, 3, 8, 5, 7, 1, 4, 6, 0, 9],
     [2, 3, 8, 6, 1, 7, 4, 5, 9, 0]]
  let fixTable : List (List (Fin 10)) :=
    [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
     [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
     [0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
     [0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
     [0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
     [0, 4, 3, 8, 5, 1, 9, 2, 6, 7],
     [0, 1, 6, 8, 5, 4, 2, 9, 3, 7],
     [0, 4, 3, 8, 5, 1, 9, 2, 6, 7],
     [0, 4, 9, 7, 5, 1, 3, 6, 2, 8],
     [0, 4, 9, 6, 1, 5, 3, 7, 8, 2]]
  let root (a i : Fin 10) := (rootTable.getD a.val []).getD i.val 0
  let fix (a i : Fin 10) := (fixTable.getD a.val []).getD i.val 0
  have rootZero : ∀ a, root a a = 0 := by decide +kernel
  have rootInjective : ∀ a, Function.Injective (root a) := by decide +kernel
  have fixZero : ∀ a, fix a 0 = 0 := by decide +kernel
  have fixPair : ∀ a : Fin 10, a ≠ 0 → fix a a = 1 ∨ fix a a = 2 := by decide +kernel
  have rootPreserve : ∀ a (x : Fin 10 → Bool), f (x ∘ root a) = f x := by decide +kernel
  have fixPreserve : ∀ a (x : Fin 10 → Bool), f (x ∘ fix a) = f x := by decide +kernel
  let first (x : Fin 10 → Bool) := g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)
  change ∃ x : Fin 10 → Bool,
    (if b then !((C.wires (List.ofFn x ++ [first x])).getD u false)
      else (C.wires (List.ofFn x ++ [first x])).getD u false) ≠ f x
  by_contra contradiction
  have computes (x : Fin 10 → Bool) :
      (if b then !((C.wires (List.ofFn x ++ [first x])).getD u false)
        else (C.wires (List.ofFn x ++ [first x])).getD u false) = f x :=
    Classical.byContradiction (fun h => contradiction ⟨x,h⟩)
  let step (w : List Bool) (h : Gate) := w ++ [h.op.eval (h.inputs.map fun i => w.getD i false)]
  have wire (w : List Bool) (a : Bool) (i : ℕ) :
      (w ++ [a]).getD i false =
        if i < w.length then w.getD i false else if i = w.length then a else false := by
    rcases lt_trichotomy i w.length with h | h | h
    · simp only [h, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    · subst i
      simp
    · have h1 : ¬ i < w.length := by omega
      have h2 : i ≠ w.length := by omega
      simp only [h1, h2, if_false]
      apply List.getD_eq_default
      simp
      omega
  let mapGate (r : ℕ → ℕ) (h : Gate) : Gate := ⟨h.op,h.inputs.map r⟩
  have mapRun (r : ℕ → ℕ) (large : ∀ i, 11 ≤ i → r i = i)
      (small : ∀ i, i < 11 → r i < 11) :
      ∀ (gs : List Gate) (W W' : List Bool), 11 ≤ W.length → W.length = W'.length →
        (∀ i, W.getD i false = W'.getD (r i) false) →
        ∀ i, (gs.foldl step W).getD i false =
          ((gs.map (mapGate r)).foldl step W').getD (r i) false := by
    intro gs
    induction gs with
    | nil => intro W W' _ _ h i; exact h i
    | cons gate gs ih =>
      intro W W' hmin hlen h i
      rw [List.map_cons,List.foldl_cons,List.foldl_cons]
      let a := gate.op.eval (gate.inputs.map fun i => W.getD i false)
      have ha : (mapGate r gate).op.eval ((mapGate r gate).inputs.map fun i => W'.getD i false) = a := by
        change gate.op.eval ((gate.inputs.map r).map fun i => W'.getD i false) = a
        rw [List.map_map]
        congr 1
        exact List.map_congr_left (fun _ _ => (h _).symm)
      have hs : step W gate = W ++ [a] := rfl
      have hs' : step W' (mapGate r gate) = W' ++ [a] := by
        unfold step
        rw [ha]
      rw [hs,hs']
      apply ih
      · simp; omega
      · simp [hlen]
      · intro j
        rw [wire,wire,← hlen]
        by_cases hj : j < 11
        · have hre := small j hj
          have hx : j < W.length := by omega
          have hy : r j < W.length := by omega
          rw [if_pos hx, if_pos hy]
          exact h j
        · rw [large j (by omega)]
          by_cases hj' : j < W.length
          · rw [if_pos hj',if_pos hj']
            simpa only [large j (by omega)] using h j
          · rw [if_neg hj',if_neg hj']
  have index (x : Fin 10 → Bool) (i : ℕ) :
      (List.ofFn x).getD i false = if h : i < 10 then x ⟨i,h⟩ else false := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn]
    by_cases hi : i < 10
    · rw [dif_pos hi,dif_pos hi]
      rfl
    · rw [dif_neg hi,dif_neg hi]
      rfl
  have atSeed (x : Fin 10 → Bool) (a : Bool) : (List.ofFn x ++ [a]).getD 10 false = a := by
    rw [wire]
    simp
  have atRaw (x : Fin 10 → Bool) (a : Bool) (i : Fin 10) :
      (List.ofFn x ++ [a]).getD i.val false = x i := by
    rw [wire, if_pos (by simpa only [List.length_ofFn] using i.isLt), index, dif_pos i.isLt]
  have stable (gs : List Gate) (W : List Bool) (i : ℕ) (hi : i < W.length) :
      (gs.foldl step W).getD i false = W.getD i false := by
    induction gs generalizing W with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons,ih _ (by simp [step]; omega)]
      change (W ++ [_]).getD i false = _
      rw [wire,if_pos hi]
  have evalLength (gs : List Gate) (W : List Bool) :
      (gs.foldl step W).length = W.length + gs.length := by
    induction gs generalizing W with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons,ih]; simp [step]; omega
  have absentInput (i : ℕ) (gs : List Gate)
      (hgs : ∀ g ∈ gs, i ∉ g.inputs) (W V : List Bool) (hlen : W.length = V.length)
      (heq : ∀ j, j ≠ i → W.getD j false = V.getD j false) (j : ℕ) (hj : j ≠ i) :
      (gs.foldl step W).getD j false = (gs.foldl step V).getD j false := by
    induction gs generalizing W V with
    | nil => exact heq j hj
    | cons g gs ih =>
      rw [List.foldl_cons,List.foldl_cons]
      have hInput : g.inputs.map (fun k => W.getD k false) =
          g.inputs.map (fun k => V.getD k false) :=
        List.map_congr_left (fun k hk => heq k (fun eq => hgs g (List.mem_cons_self) (eq ▸ hk)))
      have hs0 : step W g = W ++ [g.op.eval (g.inputs.map fun k => V.getD k false)] := by
        unfold step
        rw [hInput]
      rw [hs0]
      change (gs.foldl step (W ++ [_])).getD j false = (gs.foldl step (V ++ [_])).getD j false
      apply ih (fun g hg => hgs g (List.mem_cons_of_mem _ hg))
      · simp [hlen]
      · intro k hk
        rw [wire,wire,← hlen]
        by_cases h : k < W.length
        · rw [if_pos h,if_pos h]; exact heq k hk
        · rw [if_neg h,if_neg h]
  let flipped (x : Fin 10 → Bool) (i j : Fin 10) : Bool := if i = j then !x j else x j
  have noConstant : ∀ (a c : Bool), ∃ x : Fin 10 → Bool, (if c then !a else a) ≠ f x := by decide +kernel
  have noRaw : ∀ (i : Fin 10) (c : Bool), ∃ x : Fin 10 → Bool,
      (if c then !x i else x i) ≠ f x := by decide +kernel
  have noSignedRoot : ∀ (c : Bool), ∃ x : Fin 10 → Bool, (if c then x 0 else !x 0) ≠ f x := by decide +kernel
  let seeded (a : Bool) (j : Fin 10) (x : Fin 10 → Bool) := if a then x 0 && x j else x 0 || x j
  have noPair : ∀ (a c : Bool) (j : Fin 10), j = 1 ∨ j = 2 →
      ∃ x : Fin 10 → Bool, (if c then !(seeded a j x) else seeded a j x) ≠ f x := by decide +kernel
  have constantNeeds : ∀ i : Fin 10, ∃ x : Fin 10 → Bool, f x ≠ f (flipped x i) := by decide +kernel
  have signedNeeds : ∀ i : Fin 10, i ≠ 0 → ∃ x : Fin 10 → Bool,
      (!x 0) = !(flipped x i 0) ∧ f x ≠ f (flipped x i) := by decide +kernel
  have pairNeeds : ∀ (a : Bool) (i j : Fin 10), j = 1 ∨ j = 2 →
      ∃ x : Fin 10 → Bool, seeded a j x = seeded a j (flipped x i) ∧ f x ≠ f (flipped x i) := by decide +kernel
  have transfer (σ : Fin 10 → Fin 10) (j : ℕ) (hj : j < 11) (seed : (Fin 10 → Bool) → Bool)
      (hσ : ∀ x, f (x ∘ σ) = f x)
      (hSeed : ∀ x, first (x ∘ σ) = (List.ofFn x ++ [seed x]).getD j false)
      (needed : Fin 10 → Prop)
      (seedIsNotOutput : ∃ x, (if b then !(seed x) else seed x) ≠ f x)
      (mustRead : ∀ i, needed i → ∃ x, seed x = seed (flipped x i) ∧ f x ≠ f (flipped x i))
      (exclusion : ∀ D : Circuit, FanInTwo D → D.size ≤ 17 →
        11 ≤ D.output → D.output < 11 + D.size →
        (∀ i : Fin 10, needed i → ∃ g ∈ D.gates, i.val ∈ g.inputs) →
        ∃ x : Fin 10 → Bool, (if b then !D.eval (List.ofFn x ++ [seed x])
          else D.eval (List.ofFn x ++ [seed x])) ≠ f x) : False := by
    let r (i : ℕ) := if hi : i < 10 then (σ ⟨i,hi⟩).val else if i = 10 then j else i
    have large (i : ℕ) (hi : 11 ≤ i) : r i = i := by
      simp [r,show ¬i < 10 by omega,show i ≠ 10 by omega]
    have small (i : ℕ) (hi : i < 11) : r i < 11 := by
      by_cases h : i < 10
      · have hlt := (σ ⟨i,h⟩).isLt
        simp [r,h,show (σ ⟨i,h⟩).val < 11 by omega]
      · have h10 : i = 10 := by omega
        subst i
        simpa [r] using hj
    let D : Circuit := ⟨C.gates.map (mapGate r),r u⟩
    have legal : FanInTwo D := by
      intro h hh
      obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hh
      obtain ⟨hop,hlen⟩ := hC g' hg'
      exact ⟨hop,by simpa [mapGate] using hlen⟩
    have hDSize : D.size ≤ 17 := by
      change (C.gates.map (mapGate r)).length ≤ 17
      simpa only [List.length_map] using (show C.gates.length ≤ 17 from hsize)
    have correct (x : Fin 10 → Bool) :
        (if b then !D.eval (List.ofFn x ++ [seed x])
          else D.eval (List.ofFn x ++ [seed x])) = f x := by
      let W := List.ofFn (x ∘ σ) ++ [first (x ∘ σ)]
      let W' := List.ofFn x ++ [seed x]
      have hW : W.length = 11 := by simp [W]
      have hW' : W'.length = 11 := by simp [W']
      have hInit (i : ℕ) : W.getD i false = W'.getD (r i) false := by
        by_cases hi : i < 10
        · change W.getD (⟨i,hi⟩ : Fin 10).val false = W'.getD (r i) false
          have hri : r i = (σ ⟨i,hi⟩).val := by simp [r,hi]
          rw [hri]
          rw [atRaw,atRaw]
          rfl
        · by_cases he : i = 10
          · subst i
            rw [show r 10 = j by simp [r]]
            exact (atSeed _ _).trans (hSeed x)
          · have hi11 : 11 ≤ i := by omega
            rw [large i hi11, List.getD_eq_default W false (by omega),
              List.getD_eq_default W' false (by omega)]
      have hEval : (C.wires W).getD u false = D.eval W' :=
        mapRun r large small C.gates W W' (by omega) (by omega) hInit u
      have hGood := computes (x ∘ σ)
      change (if b then !(C.wires W |>.getD u false) else (C.wires W |>.getD u false)) = _ at hGood
      rw [hEval,hσ x] at hGood
      exact hGood
    have outputSomeGate : 11 ≤ D.output := by
      by_contra h
      have same (x : Fin 10 → Bool) :
          D.eval (List.ofFn x ++ [seed x]) = (List.ofFn x ++ [seed x]).getD D.output false :=
        stable D.gates _ _ (by rw [List.length_append,List.length_ofFn]; simp; omega)
      by_cases hi : D.output < 10
      · let i : Fin 10 := ⟨D.output,hi⟩
        obtain ⟨x,hx⟩ := noRaw i b
        have eq := correct x
        rw [same] at eq
        have hc := atRaw x (seed x) i
        change (List.ofFn x ++ [seed x]).getD D.output false = x i at hc
        rw [hc] at eq
        exact hx eq
      · have h10 : D.output = 10 := by omega
        obtain ⟨x,hx⟩ := seedIsNotOutput
        have eq := correct x
        rw [same,h10,atSeed] at eq
        exact hx eq
    have outputExists : D.output < 11 + D.size := by
      by_contra h
      obtain ⟨x,hx⟩ := noConstant false b
      have eq := correct x
      have hLen : (D.wires (List.ofFn x ++ [seed x])).length = 11 + D.size := by
        change (D.gates.foldl step (List.ofFn x ++ [seed x])).length = _
        rw [evalLength]
        have hzero : (List.ofFn x ++ [seed x]).length = 11 := by simp
        rw [hzero]
        rfl
      have hDef : D.eval (List.ofFn x ++ [seed x]) = false :=
        List.getD_eq_default _ _ (by rw [hLen]; omega)
      rw [hDef] at eq
      exact hx eq
    have allRead (i : Fin 10) (hi : needed i) : ∃ g ∈ D.gates, i.val ∈ g.inputs := by
      by_contra noneRead
      obtain ⟨x,hSeedEq,hTargetNe⟩ := mustRead i hi
      let W := List.ofFn x ++ [seed x]
      let V := List.ofFn (flipped x i) ++ [seed (flipped x i)]
      have hW : W.length = 11 := by simp [W]
      have hV : V.length = 11 := by simp [V]
      have he (k : ℕ) (hk : k ≠ i.val) : W.getD k false = V.getD k false := by
        by_cases hRaw : k < 10
        · let k' : Fin 10 := ⟨k,hRaw⟩
          have hek : ¬ i = k' := fun e => hk (congrArg Fin.val e).symm
          change W.getD k'.val false = V.getD k'.val false
          rw [atRaw,atRaw]
          simp [flipped,hek]
        · by_cases hSeedIdx : k = 10
          · subst k
            rw [atSeed,atSeed]
            exact hSeedEq
          · exact (List.getD_eq_default W false (by omega)).trans
              (List.getD_eq_default V false (by omega)).symm
      have hIgnore := absentInput i.val D.gates (fun g hg hread => noneRead ⟨g,hg,hread⟩) W V
        (by omega) he D.output (by have := i.isLt; omega)
      change D.eval W = D.eval V at hIgnore
      have hx := correct x
      have hy := correct (flipped x i)
      change (if b then !D.eval W else D.eval W) = _ at hx
      change (if b then !D.eval V else D.eval V) = _ at hy
      rw [hIgnore,hy] at hx
      exact hTargetNe hx.symm
    obtain ⟨x,hx⟩ := exclusion D legal hDSize outputSomeGate outputExists allRead
    exact hx (correct x)
  have rawOrFalse (i : ℕ) :
      (∃ j : Fin 10, ∀ x : Fin 10 → Bool, (List.ofFn x).getD i false = x j) ∨
      (∀ x : Fin 10 → Bool, (List.ofFn x).getD i false = false) := by
    by_cases hi : i < 10
    · exact Or.inl ⟨⟨i,hi⟩,fun x => by rw [index, dif_pos hi]⟩
    · exact Or.inr (fun x => by rw [index,dif_neg hi])
  let Const := ∃ q : Bool, ∀ x, first x = q
  let Alias := ∃ i : Fin 10, ∀ x, first x = x i
  let Signed := ∃ i : Fin 10, ∀ x, first x = !x i
  let Pair := ∃ i j : Fin 10, i ≠ j ∧ ∃ a : Bool,
    ∀ x, first x = (if a then x i && x j else x i || x j)
  have unary (i : ℕ) (h : ∀ x, first x = (List.ofFn x).getD i false) :
      Const ∨ Alias ∨ Signed ∨ Pair := by
    rcases rawOrFalse i with ⟨j,hj⟩|h0
    · exact Or.inr (Or.inl ⟨j,fun x => (h x).trans (hj x)⟩)
    · exact Or.inl ⟨false,fun x => (h x).trans (h0 x)⟩
  have negated (i : ℕ) (h : ∀ x, first x = !((List.ofFn x).getD i false)) :
      Const ∨ Alias ∨ Signed ∨ Pair := by
    rcases rawOrFalse i with ⟨j,hj⟩|h0
    · exact Or.inr (Or.inr (Or.inl ⟨j,fun x => by rw [h,hj]⟩))
    · exact Or.inl ⟨true,fun x => by rw [h,h0]; rfl⟩
  have binary (a : Bool) (i j : ℕ) (h : ∀ x, first x =
      (if a then (List.ofFn x).getD i false && (List.ofFn x).getD j false
      else (List.ofFn x).getD i false || (List.ofFn x).getD j false)) :
      Const ∨ Alias ∨ Signed ∨ Pair := by
    rcases rawOrFalse i with ⟨s,hs⟩|hs <;> rcases rawOrFalse j with ⟨t,ht⟩|ht
    · by_cases e : s = t
      · subst t
        exact Or.inr (Or.inl ⟨s,fun x => by rw [h,hs,ht]; cases a <;> simp⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨s,t,e,a,fun x => by rw [h,hs,ht]⟩))
    · cases a
      · exact Or.inr (Or.inl ⟨s,fun x => by rw [h,hs,ht]; simp⟩)
      · exact Or.inl ⟨false,fun x => by rw [h,ht]; simp⟩
    · cases a
      · exact Or.inr (Or.inl ⟨t,fun x => by rw [h,hs,ht]; simp⟩)
      · exact Or.inl ⟨false,fun x => by rw [h,hs]; simp⟩
    · exact Or.inl ⟨false,fun x => by rw [h,hs,ht]; cases a <;> rfl⟩
  have gLegal := hg g (List.mem_singleton_self g)
  have gOps : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by simpa using gLegal.1
  have andEval (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have orEval (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
  have notEval (xs : List Bool) : GateOp.not.eval xs = !(xs.headD false) := rfl
  have hClass : Const ∨ Alias ∨ Signed ∨ Pair := by
    cases e : g.inputs with
    | nil =>
      rcases gOps with ho|ho|ho
      · exact Or.inl ⟨true,fun x => by simp [first,ho,e,andEval,orEval,notEval]⟩
      · exact Or.inl ⟨false,fun x => by simp [first,ho,e,andEval,orEval,notEval]⟩
      · exact Or.inl ⟨true,fun x => by simp [first,ho,e,andEval,orEval,notEval]⟩
    | cons i tail =>
      have hTail : tail.length ≤ 1 := by have hL := gLegal.2; rw [e,List.length_cons] at hL; omega
      rcases gOps with ho|ho|ho
      · cases tail with
        | nil => exact unary i (fun x => by simp [first,ho,e,andEval,orEval,notEval])
        | cons j rest =>
          have hz : rest.length = 0 := by simp only [List.length_cons] at hTail; omega
          obtain rfl := List.length_eq_zero_iff.mp hz
          exact binary true i j (fun x => by simp [first,ho,e,andEval,orEval,notEval])
      · cases tail with
        | nil => exact unary i (fun x => by simp [first,ho,e,andEval,orEval,notEval])
        | cons j rest =>
          have hz : rest.length = 0 := by simp only [List.length_cons] at hTail; omega
          obtain rfl := List.length_eq_zero_iff.mp hz
          exact binary false i j (fun x => by simp [first,ho,e,andEval,orEval,notEval])
      · exact negated i (fun x => by simp [first,ho,e,andEval,orEval,notEval])
  rcases hClass with ⟨q,hq⟩|⟨i,hi⟩|⟨i,hi⟩|⟨i,j,hne,a,hab⟩
  · apply transfer id 10 (by decide) (fun _ => q) (fun _ => rfl) _ (fun _ => True) (noConstant q b)
        (fun i _ => (constantNeeds i).imp (fun _ hx => ⟨rfl,hx⟩)) _
    · intro x
      rw [atSeed, hq]
    · intro D hD hs hl hh hRead
      exact hConst q b D hD hs hl hh (fun i => hRead i trivial)
  · apply transfer id i.val (by have := i.isLt; omega) (fun _ => false) (fun _ => rfl) _
        (fun _ => True) (noConstant false b)
        (fun j _ => (constantNeeds j).imp (fun _ hx => ⟨rfl,hx⟩)) _
    · intro x
      rw [atRaw, hi]
      rfl
    · intro D hD hs hl hh hRead
      exact hConst false b D hD hs hl hh (fun i => hRead i trivial)
  · have hNoSeed : ∃ x, (if b then !(!x 0) else !x 0) ≠ f x := by
      simpa only [Bool.not_not] using noSignedRoot b
    apply transfer (root i) 10 (by decide) (fun x => !x 0) (rootPreserve i) _
        (fun j => j ≠ 0) hNoSeed signedNeeds (hSigned b)
    intro x
    rw [hi,atSeed]
    change (!x (root i i)) = (!x 0)
    rw [rootZero]
  · let j' := root i j
    have hj' : j' ≠ 0 := by
      intro hz
      have eq : root i i = root i j := (rootZero i).trans hz.symm
      exact hne (rootInjective i eq)
    let σ := fix j' ∘ root i
    have hs : ∀ x, f (x ∘ σ) = f x := by
      intro x
      change f ((x ∘ fix j') ∘ root i) = f x
      rw [rootPreserve,fixPreserve]
    have hs0 : σ i = 0 := by
      change fix j' (root i i) = 0
      rw [rootZero,fixZero]
    rcases fixPair j' hj' with hj1|hj2
    · apply transfer σ 10 (by decide) (fun x => if a then x 0 && x 1 else x 0 || x 1)
        hs _ (fun _ => True) (noPair a b 1 (Or.inl rfl)) (fun k _ => pairNeeds a k 1 (Or.inl rfl)) _
      · intro x
        rw [hab,atSeed]
        change (if a then x (σ i) && x (fix j' j') else x (σ i) || x (fix j' j')) = _
        rw [hs0,hj1]
      · intro D hD hs hl hh hRead
        exact hEdge a b D hD hs hl hh (fun i => hRead i trivial)
    · apply transfer σ 10 (by decide) (fun x => if a then x 0 && x 2 else x 0 || x 2)
        hs _ (fun _ => True) (noPair a b 2 (Or.inr rfl)) (fun k _ => pairNeeds a k 2 (Or.inr rfl)) _
      · intro x
        rw [hab,atSeed]
        change (if a then x (σ i) && x (fix j' j') else x (σ i) || x (fix j' j')) = _
        rw [hs0,hj2]
      · intro D hD hs hl hh hRead
        exact hNonedge a b D hD hs hl hh (fun i => hRead i trivial)
