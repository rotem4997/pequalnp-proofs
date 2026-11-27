import Mathlib
import PEqualNP.Defs

-- Reduction of L-meta-5150 to the Petersen graph with vertex 9 removed (on 9 inputs).
-- h1: no circuit of at most 14 gates for it (the statement of L-meta-2012).
-- h2: no circuit of exactly 15 gates for it.
-- The proof: an automorphism of the Petersen graph sends the fixed vertex v to 9; renaming
-- the inputs of a circuit along it (input v to a wire that reads false) gives a circuit on
-- 9 inputs of the same size; a negated output costs one NOT gate.
theorem PEqualNP.Outside.R_meta_5150_1
    (h1 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) x1 (14 : ℕ))
    (h2 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size = (15 : ℕ) → ∃ (x3 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x3) ≠ x1 x3) :
    ∀ (x1 : Fin (10 : ℕ)) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Bool), PEqualNP.MetaComplexity.FanInTwo x2 → (x2.size + if x3 = Bool.true then (1 : ℕ) else (0 : ℕ)) ≤ (15 : ℕ) → ∃ (x6 : Fin (10 : ℕ) → Bool), x6 x1 = Bool.false ∧ (if x3 = Bool.true then !x2.eval (List.ofFn x6) else x2.eval (List.ofFn x6)) ≠ (x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ))) := by
  intro v C b hC hsize
  -- the edge function on 9 inputs, as in h1 and h2
  let f9 : (Fin 9 → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ)))
  let f10 : (Fin 10 → Bool) → Bool := fun x6 => (x6 (0 : Fin (10 : ℕ)) && x6 (1 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (3 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (4 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (0 : Fin (10 : ℕ)) || x6 (0 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)) || x6 (1 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (2 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (3 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (4 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (5 : Fin (10 : ℕ)) && x6 (7 : Fin (10 : ℕ)) || x6 (7 : Fin (10 : ℕ)) && x6 (9 : Fin (10 : ℕ)) || x6 (9 : Fin (10 : ℕ)) && x6 (6 : Fin (10 : ℕ)) || x6 (6 : Fin (10 : ℕ)) && x6 (8 : Fin (10 : ℕ)) || x6 (8 : Fin (10 : ℕ)) && x6 (5 : Fin (10 : ℕ)))
  -- automorphisms: row v sends v to 9
  let tbl : List (List ℕ) := [[9, 4, 0, 1, 6, 7, 3, 5, 2, 8], [4, 9, 6, 1, 0, 3, 7, 8, 2, 5],
    [0, 4, 9, 6, 1, 5, 3, 7, 8, 2], [0, 1, 6, 9, 4, 5, 2, 8, 7, 3], [4, 0, 1, 6, 9, 3, 5, 2, 8, 7],
    [4, 0, 1, 2, 3, 9, 5, 6, 7, 8], [0, 4, 3, 2, 1, 5, 9, 8, 7, 6], [0, 1, 6, 8, 5, 4, 2, 9, 3, 7],
    [0, 1, 2, 7, 5, 4, 6, 3, 9, 8], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]
  let sg : ℕ → ℕ → ℕ := fun a w => (tbl.getD a []).getD w 0
  have hsym : ∀ (a : Fin 10) (y : Fin 9 → Bool),
      f10 (fun w => (List.ofFn y).getD (sg a w) false) = f9 y := by
    decide +kernel
  have hsg : ∀ (a : Fin 10) (w : Fin 10), (sg a w = 9 ↔ w = a) ∧ sg a w ≤ 9 := by
    decide +kernel
  -- the step function of `Circuit.wires`
  let step : List Bool → PEqualNP.CircuitLowerBounds.Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hlen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (W : List Bool),
      (gs.foldl step W).length = W.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro W; simp
    | cons g gs ih => intro W; rw [List.foldl_cons, ih]; simp [step]; omega
  -- the renaming of wires: input `w < 10` to `sg v w` (input `v` to `B`, which reads false),
  -- gate wire `10 + j` to `9 + j`
  let B : ℕ := 10 + C.gates.length
  let φ : ℕ → ℕ := fun w => if w < 10 then (if w = v.val then B else sg v w) else w - 1
  let tr : PEqualNP.CircuitLowerBounds.Gate → PEqualNP.CircuitLowerBounds.Gate :=
    fun g => ⟨g.op, g.inputs.map φ⟩
  have hφ : ∀ w, w < 10 → φ w < 9 ∨ φ w = B := by
    intro w hw
    by_cases hv : w = v.val
    · right; simp [φ, hv]
    · left
      have h := hsg v ⟨w, hw⟩
      have hne : (⟨w, hw⟩ : Fin 10) ≠ v := fun e => hv (by rw [← e])
      have h9 : sg v w ≠ 9 := fun e => hne (h.1.1 e)
      have hle : sg v w ≤ 9 := h.2
      have e1 : φ w = sg v w := by simp only [φ, hw, hv, ↓reduceIte]
      omega
  have getD_app : ∀ (W : List Bool) (a : Bool) (i : ℕ),
      (W ++ [a]).getD i false = if i < W.length then W.getD i false
        else if i = W.length then a else false := by
    intro W a i
    rcases lt_trichotomy i W.length with h | h | h
    · simp only [h, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    · subst h; simp
    · have h1 : ¬ i < W.length := by omega
      have h2 : i ≠ W.length := by omega
      simp only [h1, h2, if_false]
      apply List.getD_eq_default; simp; omega
  have key : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (W W' : List Bool),
      W.length = W'.length + 1 → 10 ≤ W.length → W'.length + gs.length ≤ B →
      (∀ w, W.getD w false = W'.getD (φ w) false) →
      ∀ w, (gs.foldl step W).getD w false = ((gs.map tr).foldl step W').getD (φ w) false := by
    intro gs
    induction gs with
    | nil => intro W W' _ _ _ hinv; simpa using hinv
    | cons g gs ih =>
      intro W W' hl h10 hB hinv
      rw [List.map_cons, List.foldl_cons, List.foldl_cons]
      apply ih
      · simp [step, hl]
      · simp [step]; omega
      · simp [step]; simp at hB; omega
      · have ha : (g.inputs.map fun i => W.getD i false) =
            ((tr g).inputs.map fun i => W'.getD i false) := by
          simp only [tr, List.map_map]
          exact List.map_congr_left (fun i _ => hinv i)
        intro w
        simp only [step]
        rw [getD_app, getD_app, ← ha]
        have hop : (tr g).op = g.op := rfl
        rw [hop]
        simp only [List.length_cons] at hB
        by_cases hw : w < 10
        · have hwl : w < W.length := by omega
          rcases hφ w hw with h | h
          · rw [if_pos hwl, if_pos (by omega : φ w < W'.length)]; exact hinv w
          · rw [if_pos hwl, if_neg (by omega : ¬ φ w < W'.length),
              if_neg (by omega : φ w ≠ W'.length)]
            have := hinv w
            rw [h, List.getD_eq_default (l := W') (d := false) (n := B) (by omega)] at this
            exact this
        · have hφw : φ w = w - 1 := by simp only [φ, hw, ↓reduceIte]
          rw [hφw]
          rcases lt_trichotomy w W.length with h | h | h
          · rw [if_pos h, if_pos (by omega : w - 1 < W'.length)]
            have := hinv w
            rwa [hφw] at this
          · rw [if_neg (by omega : ¬ w < W.length), if_pos h,
              if_neg (by omega : ¬ w - 1 < W'.length), if_pos (by omega : w - 1 = W'.length)]
          · rw [if_neg (by omega : ¬ w < W.length), if_neg (by omega : w ≠ W.length),
              if_neg (by omega : ¬ w - 1 < W'.length), if_neg (by omega : w - 1 ≠ W'.length)]
  -- the renamed circuit on 9 inputs
  let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.map tr, φ C.output⟩
  have hC' : PEqualNP.MetaComplexity.FanInTwo C' := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    obtain ⟨h1', h2'⟩ := hC g0 hg0
    exact ⟨h1', by simpa [tr] using h2'⟩
  have hC'size : C'.size = C.size := by
    show (C.gates.map tr).length = C.gates.length
    exact List.length_map _
  -- every input y on 9 inputs comes from an input x on 10 inputs with x v = false
  have hagree : ∀ y : Fin 9 → Bool,
      let x : Fin 10 → Bool := fun w => (List.ofFn y).getD (sg v w) false
      x v = false ∧ f10 x = f9 y ∧ C'.eval (List.ofFn y) = C.eval (List.ofFn x) := by
    intro y x
    have hxv : x v = false := by
      have := (hsg v v).1.2 rfl
      simp only [x, this]
      apply List.getD_eq_default; simp
    refine ⟨hxv, hsym v y, ?_⟩
    have hinit : ∀ w, (List.ofFn x).getD w false = (List.ofFn y).getD (φ w) false := by
      intro w
      by_cases hw : w < 10
      · rw [List.getD_eq_getElem _ _ (by simpa using hw), List.getElem_ofFn]
        by_cases hv : w = v.val
        · have e : (⟨w, hw⟩ : Fin 10) = v := Fin.ext hv
          rw [show x ⟨w, hw⟩ = x v from by rw [e], hxv]
          have hφB : φ w = B := by
            show (if w < 10 then (if w = v.val then B else sg v w) else w - 1) = B
            rw [if_pos hw, if_pos hv]
          rw [hφB]
          symm; apply List.getD_eq_default; simp only [List.length_ofFn, B]; omega
        · simp [φ, hw, hv, x]
      · have hφw : φ w = w - 1 := by simp [φ, hw]
        rw [hφw, List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp; omega)]
    have := key C.gates (List.ofFn x) (List.ofFn y) (by simp) (by simp)
      (by simp [B]) hinit C.output
    show ((C.gates.map tr).foldl step (List.ofFn y)).getD (φ C.output) false =
      (C.gates.foldl step (List.ofFn x)).getD C.output false
    exact this.symm
  by_contra hne
  push Not at hne
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at hsize hne
    have hD : ∀ y : Fin 9 → Bool, C'.eval (List.ofFn y) = f9 y := by
      intro y
      obtain ⟨hxv, hf, he⟩ := hagree y
      rw [he, ← hf]
      exact hne _ hxv
    rcases Nat.lt_or_ge C.size 15 with hs | hs
    · exact h1 ⟨C', hC', by omega, hD⟩
    · obtain ⟨y, hy⟩ := h2 C' hC' (by omega)
      exact hy (hD y)
  | true =>
    simp only [↓reduceIte] at hsize hne
    let D : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨C'.gates ++ [⟨PEqualNP.CircuitLowerBounds.GateOp.not, [C'.output]⟩], 9 + C'.gates.length⟩
    have hDf : PEqualNP.MetaComplexity.FanInTwo D := by
      intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact hC' g hg
      · simp at hg; subst hg; simp
    have hDsize : D.size = C.size + 1 := by
      show (C'.gates ++ [_]).length = C.gates.length + 1
      simp [C']
    have hDe : ∀ y : Fin 9 → Bool, D.eval (List.ofFn y) = !C'.eval (List.ofFn y) := by
      intro y
      have hl := hlen C'.gates (List.ofFn y)
      rw [List.length_ofFn] at hl
      show ((C'.gates ++ [(⟨PEqualNP.CircuitLowerBounds.GateOp.not, [C'.output]⟩ : PEqualNP.CircuitLowerBounds.Gate)]).foldl step
          (List.ofFn y)).getD (9 + C'.gates.length) false =
        !((C'.gates.foldl step (List.ofFn y)).getD C'.output false)
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
      show ((C'.gates.foldl step (List.ofFn y)) ++ [_]).getD _ false = _
      rw [getD_app, if_neg (by omega), if_pos hl.symm]
      rfl
    have hD : ∀ y : Fin 9 → Bool, D.eval (List.ofFn y) = f9 y := by
      intro y
      obtain ⟨hxv, hf, he⟩ := hagree y
      rw [hDe, he, ← hf]
      exact hne _ hxv
    rcases Nat.lt_or_ge D.size 15 with hs | hs
    · exact h1 ⟨D, hDf, by omega, hD⟩
    · obtain ⟨y, hy⟩ := h2 D hDf (by omega)
      exact hy (hD y)
