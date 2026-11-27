import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_969_1
    (h1 :
      ∃ C1 : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C1 ∧ C1.size ≤ 1 ∧
        ∀ x : Fin 8 → Bool, C1.eval (List.ofFn x) = (x 0 || x 3))
    (h2 :
      ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C2 ∧ C2.size ≤ 10 ∧
        ∀ x : Fin 8 → Bool,
          (C2.eval (List.ofFn x ++ [x 0 || x 3]) = true ↔
            ∃ u v : Fin 8,
              (u.val, v.val) ∈
                ([(0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 3), (2, 6), (3, 7),
                  (4, 5), (4, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧
              x u = true ∧ x v = true)) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 11 ∧ (∀ x : Fin 8 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 8, (u.val, v.val) ∈ ([(0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 3), (2, 6), (3, 7), (4, 5), (4, 6), (5, 7), (6, 7)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  obtain ⟨C1, hC1m, hC1s, hC1e⟩ := h1
  obtain ⟨C2, hC2m, hC2s, hC2e⟩ := h2
  let k : ℕ := C1.gates.length
  let step : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hgetD_left : ∀ (u v : List Bool) (i : ℕ), i < u.length →
      (u ++ v).getD i false = u.getD i false := by
    intro u v i hi
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have hgetD_right : ∀ (u v : List Bool) (i : ℕ), u.length ≤ i →
      (u ++ v).getD i false = v.getD (i - u.length) false := by
    intro u v i hi
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right hi]
  have hgetD_ge : ∀ (u : List Bool) (i : ℕ), u.length ≤ i → u.getD i false = false := by
    intro u i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
    rfl
  have hstep_ext : ∀ (gs : List Gate) (w : List Bool),
      ∃ ext : List Bool, ext.length = gs.length ∧ gs.foldl step w = w ++ ext := by
    intro gs
    induction gs with
    | nil =>
      intro w
      exact ⟨[], rfl, by simp⟩
    | cons g gs ih =>
      intro w
      simp only [List.foldl_cons]
      obtain ⟨ext, hext_len, hext⟩ := ih (step w g)
      refine ⟨[g.op.eval (g.inputs.map fun i => w.getD i false)] ++ ext, ?_, ?_⟩
      · simp [hext_len]
      · rw [hext]; dsimp only [step]; rw [List.append_assoc]
  have hC1out : C1.output < 8 + k := by
    by_contra hge
    have hle : 8 + k ≤ C1.output := Nat.le_of_not_lt hge
    let x1 : Fin 8 → Bool := fun _ => true
    have hev := hC1e x1
    change (C1.gates.foldl step (List.ofFn x1)).getD C1.output false = true at hev
    obtain ⟨mid, hmid_len, hmid⟩ := hstep_ext C1.gates (List.ofFn x1)
    rw [hmid] at hev
    have hlen : (List.ofFn x1 ++ mid).length = 8 + k := by
      rw [List.length_append, List.length_ofFn, hmid_len]
    have hf : (List.ofFn x1 ++ mid).getD C1.output false = false :=
      hgetD_ge (List.ofFn x1 ++ mid) C1.output (by omega)
    rw [hf] at hev
    exact Bool.false_ne_true hev
  let shift : ℕ → ℕ := fun w => if w < 8 then w else if w = 8 then C1.output else w - 1 + k
  let shiftGate : Gate → Gate := fun g => { op := g.op, inputs := g.inputs.map shift }
  let C : Circuit :=
    { gates := C1.gates ++ C2.gates.map shiftGate
      output := shift C2.output }
  have hgetD_shift : ∀ (x mid tail : List Bool) (b : Bool) (i : ℕ),
      x.length = 8 → mid.length = k → (x ++ mid).getD C1.output false = b →
      (x ++ mid ++ tail).getD (shift i) false = (x ++ [b] ++ tail).getD i false := by
    intro x mid tail b i hx hmid hb
    by_cases hlt : i < 8
    · have hs : shift i = i := by simp only [shift, hlt, ↓reduceIte]
      rw [hs, List.append_assoc, List.append_assoc,
          hgetD_left x (mid ++ tail) i (by omega),
          hgetD_left x ([b] ++ tail) i (by omega)]
    · by_cases heq : i = 8
      · have hs : shift i = C1.output := by rw [heq]; rfl
        rw [hs, heq, hgetD_left (x ++ mid) tail C1.output (by rw [List.length_append]; omega), hb,
            hgetD_left (x ++ [b]) tail 8 (by rw [List.length_append, List.length_singleton]; omega),
            hgetD_right x [b] 8 (by omega)]
        have hzero : 8 - x.length = 0 := by omega
        rw [hzero]
        rfl
      · have hs : shift i = i - 1 + k := by simp only [shift, hlt, heq, ↓reduceIte]
        rw [hs,
            hgetD_right (x ++ mid) tail (i - 1 + k) (by rw [List.length_append]; omega),
            hgetD_right (x ++ [b]) tail i (by rw [List.length_append, List.length_singleton]; omega)]
        have hsub : i - 1 + k - (x ++ mid).length = i - (x ++ [b]).length := by
          rw [List.length_append, List.length_append, List.length_singleton]
          omega
        rw [hsub]
  have hstep_shift : ∀ (x mid : List Bool) (b : Bool),
      x.length = 8 → mid.length = k → (x ++ mid).getD C1.output false = b →
      ∀ (gs : List Gate) (tail : List Bool),
        ∃ tail' : List Bool,
          gs.foldl step (x ++ [b] ++ tail) = x ++ [b] ++ tail' ∧
          (gs.map shiftGate).foldl step (x ++ mid ++ tail) = x ++ mid ++ tail' := by
    intro x mid b hx hmid hb gs
    induction gs with
    | nil =>
      intro tail
      exact ⟨tail, rfl, rfl⟩
    | cons g gs ih =>
      intro tail
      simp only [List.map_cons, List.foldl_cons]
      have hmap : ((shiftGate g).inputs.map fun i => (x ++ mid ++ tail).getD i false) =
          g.inputs.map (fun i => (x ++ [b] ++ tail).getD i false) := by
        dsimp only [shiftGate]
        rw [List.map_map]
        apply List.map_congr_left
        intro i _
        exact hgetD_shift x mid tail b i hx hmid hb
      let v : Bool := g.op.eval (g.inputs.map fun i => (x ++ [b] ++ tail).getD i false)
      have hs1 : step (x ++ [b] ++ tail) g = x ++ [b] ++ (tail ++ [v]) := by
        dsimp only [step, v]; rw [List.append_assoc]
      have hs2 : step (x ++ mid ++ tail) (shiftGate g) = x ++ mid ++ (tail ++ [v]) := by
        dsimp only [step, v]; rw [hmap, List.append_assoc]
      rw [hs1, hs2]
      exact ih (tail ++ [v])
  have hCeval : ∀ x : Fin 8 → Bool,
      C.eval (List.ofFn x) = C2.eval (List.ofFn x ++ [x 0 || x 3]) := by
    intro x
    change (C.gates.foldl step (List.ofFn x)).getD C.output false =
      (C2.gates.foldl step (List.ofFn x ++ [x 0 || x 3])).getD C2.output false
    let xs : List Bool := List.ofFn x
    have hxs : xs.length = 8 := List.length_ofFn
    obtain ⟨mid, hmid_len, hC1w⟩ := hstep_ext C1.gates xs
    have hb : (xs ++ mid).getD C1.output false = (x 0 || x 3) := by
      have hev := hC1e x
      change (C1.gates.foldl step xs).getD C1.output false = (x 0 || x 3) at hev
      rw [hC1w] at hev
      exact hev
    obtain ⟨tail', hC2w, hC2w_shift⟩ := hstep_shift xs mid (x 0 || x 3) hxs hmid_len hb C2.gates []
    have hC2w' : C2.gates.foldl step (xs ++ [x 0 || x 3]) = xs ++ [x 0 || x 3] ++ tail' := by
      simpa only [List.append_nil] using hC2w
    have hC2w_shift' : (C2.gates.map shiftGate).foldl step (xs ++ mid) = xs ++ mid ++ tail' := by
      simpa only [List.append_nil] using hC2w_shift
    have hfold : C.gates.foldl step xs = xs ++ mid ++ tail' := by
      dsimp only [C]
      rw [List.foldl_append, hC1w, hC2w_shift']
    rw [hfold, hC2w']
    dsimp only [C]
    exact hgetD_shift xs mid tail' (x 0 || x 3) C2.output hxs hmid_len hb
  have hCm : Monotone2 C := by
    intro g hg
    dsimp only [C] at hg
    rw [List.mem_append] at hg
    rcases hg with hg1 | hg2
    · exact hC1m g hg1
    · rw [List.mem_map] at hg2
      obtain ⟨g0, hg0, rfl⟩ := hg2
      have h0 := hC2m g0 hg0
      exact ⟨h0.1, by dsimp only [shiftGate]; rw [List.length_map]; exact h0.2⟩
  have hCs : C.size ≤ 11 := by
    change C.gates.length ≤ 11
    change C1.gates.length ≤ 1 at hC1s
    change C2.gates.length ≤ 10 at hC2s
    dsimp only [C]
    rw [List.length_append, List.length_map]
    omega
  refine ⟨C, hCm, hCs, ?_⟩
  intro x
  rw [hCeval x]
  exact hC2e x
