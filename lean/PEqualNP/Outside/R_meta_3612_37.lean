import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 12000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_3612_37
    (notZero : ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) →
      circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
        (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      16 ≤ C.size)
    (notFour : ∀ C : Circuit, FanInTwo C →
      (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) →
      circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
        (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) →
      16 ≤ C.size) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : Fin (9 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 ≠ (0 : Fin (9 : ℕ)) → x3 ≠ (6 : Fin (9 : ℕ)) → PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (13 : ℕ) → ∃ (x9 : Fin (9 : ℕ) → Bool), x4.eval ((x2 x9).set ↑x3 !x9 x3) ≠ x1 x9 := by
  classical
  dsimp only
  intro v D hv0 hv6 legal small
  by_contra! agree
  let target (x : Fin 9 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
        (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
        (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  have encodedTarget (x : Fin 9 → Bool) :
      ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List Nat).any
        (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) = target x := by
    simp only [List.any_cons, List.any_nil, Bool.or_false]
    change ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) || ((x 3 && x 8) || ((x 5 && x 7) || ((x 6 && x 8) || ((x 8 && x 5))))))))))))) = target x
    simp only [target]
    ac_rfl
  let reps (j : Fin 9) : Fin 9 := if j = 4 ∨ j = 6 ∨ j = 7 then 4 else 0
  let table : List (List (Fin 9)) :=
    [[0, 1, 2, 3, 4, 5, 6, 7, 8],
      [1, 0, 5, 8, 6, 2, 4, 7, 3],
      [2, 1, 0, 5, 7, 3, 6, 4, 8],
      [3, 2, 1, 0, 4, 8, 7, 6, 5],
      [0, 1, 2, 3, 4, 5, 6, 7, 8],
      [1, 2, 3, 8, 6, 0, 7, 4, 5],
      [1, 0, 5, 8, 6, 2, 4, 7, 3],
      [1, 2, 3, 8, 6, 0, 7, 4, 5],
      [2, 3, 8, 5, 7, 1, 4, 6, 0]]
  let perm (j i : Fin 9) : Fin 9 := (table.getD j.val []).getD i.val 0
  have permRep : ∀ j : Fin 9, perm j j = reps j := by
    intro j
    fin_cases j <;> decide
  have permTarget : ∀ (j : Fin 9) (y : Fin 9 → Bool),
      target (fun i => y (perm j i)) = target y := by
    intro j
    fin_cases j <;> decide +kernel
  let σ := perm v
  let pin (i : ℕ) : ℕ :=
    if hi : i < 9 then if i = v.val then 9 else (σ ⟨i, hi⟩).val else i + 1
  have pinLow (i : ℕ) (hi : i < 9) : pin i < 10 := by
    unfold pin
    rw [dite_eq_left hi]
    split
    · decide
    · exact (σ ⟨i, hi⟩).isLt.trans (by decide)
  have pinHigh (i : ℕ) (hi : 9 ≤ i) : pin i = i + 1 := by
    exact dite_eq_right (Nat.not_lt.mpr hi)
  let moveGate (g : Gate) : Gate := ⟨g.op, g.inputs.map pin⟩
  let negGate : Gate := ⟨.not, [(reps v).val]⟩
  let seedGate : Gate := ⟨.or, [(σ 0).val, (σ 6).val]⟩
  let new : Circuit := ⟨[negGate, seedGate] ++ D.gates.map moveGate, pin D.output⟩
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have atEnd (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl w.length)]
    simp
  have raw (y : Fin 9 → Bool) (i : Fin 9) : (List.ofFn y).getD i.val false = y i := by
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using i.isLt), List.getElem_ofFn]
  let flipped (y : Fin 9 → Bool) := !(y (reps v))
  let seed (y : Fin 9 → Bool) := y (σ 0) || y (σ 6)
  let mid (y : Fin 9 → Bool) := List.ofFn y ++ [flipped y]
  let big (y : Fin 9 → Bool) := mid y ++ [seed y]
  let row (y : Fin 9 → Bool) := List.ofFn (fun i => y (σ i)) ++ [seed y]
  let tiny (y : Fin 9 → Bool) := (row y).set v.val (!(y (σ v)))
  have midLength (y : Fin 9 → Bool) : (mid y).length = 10 := by simp [mid]
  have bigLength (y : Fin 9 → Bool) : (big y).length = 11 := by simp [big, midLength]
  have rowLength (y : Fin 9 → Bool) : (row y).length = 10 := by simp [row]
  have tinyLength (y : Fin 9 → Bool) : (tiny y).length = 10 := by simp [tiny, rowLength]
  have midRaw (y : Fin 9 → Bool) (i : Fin 9) : (mid y).getD i.val false = y i := by
    change (List.ofFn y ++ [flipped y]).getD i.val false = y i
    rw [List.getD_append _ _ _ _ (by simp), raw]
  have bigRaw (y : Fin 9 → Bool) (i : Fin 9) : (big y).getD i.val false = y i := by
    change (mid y ++ [seed y]).getD i.val false = y i
    rw [List.getD_append _ _ _ _ (by rw [midLength]; exact i.isLt.trans (by decide)), midRaw]
  have rowRaw (y : Fin 9 → Bool) (i : Fin 9) : (row y).getD i.val false = y (σ i) := by
    change (List.ofFn (fun j => y (σ j)) ++ [seed y]).getD i.val false = y (σ i)
    rw [List.getD_append _ _ _ _ (by simp), raw]
  have getFlipped (y : Fin 9 → Bool) : (big y).getD 9 false = flipped y := by
    change (mid y ++ [seed y]).getD 9 false = flipped y
    rw [List.getD_append _ _ _ _ (by rw [midLength]; decide)]
    simpa only [List.length_ofFn] using atEnd (List.ofFn y) (flipped y)
  have getSeed (y : Fin 9 → Bool) : (big y).getD 10 false = seed y := by
    simpa only [midLength] using atEnd (mid y) (seed y)
  have rowSeed (y : Fin 9 → Bool) : (row y).getD 9 false = seed y := by
    simpa only [List.length_ofFn] using atEnd (List.ofFn (fun i => y (σ i))) (seed y)
  have setSame (w : List Bool) (i : ℕ) (b : Bool) (hi : i < w.length) :
      (w.set i b).getD i false = b := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hi]
    rfl
  have setOther (w : List Bool) (i j : ℕ) (b : Bool) (h : i ≠ j) :
      (w.set i b).getD j false = w.getD j false := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_set_ne h]
  have pre (y : Fin 9 → Bool) : ([negGate, seedGate].foldl step (List.ofFn y)) = big y := by
    have hmid : step (List.ofFn y) negGate = mid y := by
      change List.ofFn y ++ [!((List.ofFn y).getD (reps v).val false)] = mid y
      rw [raw]
    simp only [List.foldl_cons, List.foldl_nil, hmid]
    change mid y ++ [([(mid y).getD (σ 0).val false, (mid y).getD (σ 6).val false]).any id] = big y
    simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false, midRaw, big, seed]
  have init (y : Fin 9 → Bool) (i : ℕ) :
      (tiny y).getD i false = (big y).getD (pin i) false := by
    by_cases hi : i < 9
    · by_cases hv : i = v.val
      · subst i
        simp only [tiny]
        rw [setSame _ _ _ (by rw [rowLength]; exact v.isLt.trans (by decide))]
        have atV : pin v.val = 9 := by simp [pin, v.isLt]
        rw [atV, getFlipped]
        change (!(y (perm v v))) = !(y (reps v))
        rw [permRep]
      · simp only [tiny]
        rw [setOther _ _ _ _ (Ne.symm hv)]
        simp only [pin, dite_eq_left hi, ite_eq_right hv]
        rw [rowRaw y ⟨i, hi⟩, bigRaw]
    · have hb : 9 ≤ i := Nat.not_lt.mp hi
      rw [pinHigh i hb]
      by_cases h9 : i = 9
      · subst i
        simp only [tiny]
        rw [setOther _ _ _ _ (by have := v.isLt; omega), rowSeed, getSeed]
      · rw [List.getD_eq_default _ _ (by rw [tinyLength]; omega),
          List.getD_eq_default _ _ (by rw [bigLength]; omega)]
  have carry (gs : List Gate) (a b : List Bool) (ha : 10 ≤ a.length)
      (hb : b.length = a.length + 1)
      (equal : ∀ i, a.getD i false = b.getD (pin i) false) :
      ∀ i, (gs.foldl step a).getD i false = ((gs.map moveGate).foldl step b).getD (pin i) false := by
    induction gs generalizing a b with
    | nil => exact equal
    | cons g gs ih =>
      simp only [List.foldl_cons, List.map_cons]
      apply ih
      · simp [step]; omega
      · simp [step]; omega
      · have hv : g.op.eval (g.inputs.map fun i => a.getD i false) =
            (moveGate g).op.eval ((moveGate g).inputs.map fun i => b.getD i false) := by
          simp only [moveGate, List.map_map]
          congr 1
          exact List.map_congr_left (fun i _ => equal i)
        intro i
        change (a ++ [_]).getD i false = (b ++ [_]).getD (pin i) false
        rw [← hv]
        by_cases hi : i < a.length
        · have hpin : pin i < b.length := by
            by_cases hlow : i < 9
            · have := pinLow i hlow
              omega
            · rw [pinHigh i (Nat.not_lt.mp hlow)]
              omega
          rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hpin, equal]
        · by_cases hlen : i = a.length
          · have hpin : pin i = b.length := by rw [pinHigh i (by omega)]; omega
            rw [hlen, atEnd, ← hlen, hpin, atEnd]
          · have hpin : pin i = i + 1 := pinHigh i (by omega)
            rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]
  have legalNew : FanInTwo new := by
    intro g hg
    change g ∈ [negGate, seedGate] ++ D.gates.map moveGate at hg
    rcases List.mem_append.mp hg with hg | hg
    · rcases List.mem_cons.mp hg with rfl | hg
      · simp [negGate]
      · rcases List.mem_cons.mp hg with rfl | hg
        · simp [seedGate]
        · exact (List.not_mem_nil hg).elim
    · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hg
      simpa [moveGate] using legal old hold
  have first (y : Fin 9 → Bool) : (new.wires (List.ofFn y)).getD 9 false = !(y (reps v)) := by
    change (([negGate, seedGate] ++ D.gates.map moveGate).foldl step (List.ofFn y)).getD 9 false =
      !(y (reps v))
    rw [List.foldl_append, pre, keep _ _ _ (by rw [bigLength]; decide)]
    exact getFlipped y
  have correct : circuitFun 9 new = target := by
    funext y
    have h := carry D.gates (tiny y) (big y) (by rw [tinyLength])
      (by rw [tinyLength, bigLength]) (init y) D.output
    have hsim : circuitFun 9 new y = D.eval (tiny y) := by
      change (([negGate, seedGate] ++ D.gates.map moveGate).foldl step (List.ofFn y)).getD
        (pin D.output) false = (D.gates.foldl step (tiny y)).getD D.output false
      rw [List.foldl_append, pre]
      exact h.symm
    have horig : D.eval (tiny y) = target (fun i => y (σ i)) := by
      exact (agree (fun i => y (σ i))).trans (encodedTarget (fun i => y (σ i)))
    rw [hsim, horig]
    exact permTarget v y
  have len : new.size = D.size + 2 := by
    change ([negGate, seedGate] ++ D.gates.map moveGate).length = D.gates.length + 2
    simp
  have repsCases : reps v = 0 ∨ reps v = 4 := by
    unfold reps
    split <;> simp
  rcases repsCases with h0 | h4
  · have lower := notZero new legalNew (fun y => by simpa only [h0] using first y) correct
    omega
  · have lower := notFour new legalNew (fun y => by simpa only [h4] using first y) correct
    omega
