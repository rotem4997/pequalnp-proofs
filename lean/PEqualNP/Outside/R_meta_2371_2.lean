import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2371_2
    (h2 : let F := fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5; ∀ (g : PEqualNP.CircuitLowerBounds.Gate) (D : PEqualNP.CircuitLowerBounds.Circuit) (u : ℕ) (b : Bool), PEqualNP.MetaComplexity.FanInTwo ({ gates := [g], output := 0 } : PEqualNP.CircuitLowerBounds.Circuit) → PEqualNP.MetaComplexity.FanInTwo D → D.size = 17 → let W := fun x : Fin 10 → Bool => (D.wires (({ gates := [g], output := 0 } : PEqualNP.CircuitLowerBounds.Circuit).wires (List.ofFn x))).getD u false; (∀ x : Fin 10 → Bool, (if b = true then !W x else W x) = F x) → ∃ (E : PEqualNP.CircuitLowerBounds.Circuit) (u' : ℕ) (b' : Bool), PEqualNP.MetaComplexity.FanInTwo E ∧ E.size ≤ 15 ∧ let V := fun x : Fin 10 → Bool => (E.wires (List.ofFn x)).getD u' false; ∀ x : Fin 10 → Bool, x 9 = false → (if b' = true then !V x else V x) = F x)
    (h3 : let F := fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5; ∀ (E : PEqualNP.CircuitLowerBounds.Circuit) (u' : ℕ) (b' : Bool), PEqualNP.MetaComplexity.FanInTwo E → E.size ≤ 15 → let V := fun x : Fin 10 → Bool => (E.wires (List.ofFn x)).getD u' false; ∃ x : Fin 10 → Bool, x 9 = false ∧ (if b' = true then !V x else V x) ≠ F x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Gate) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo { gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit } →     PEqualNP.MetaComplexity.FanInTwo x2 →       x2.size ≤ (17 : ℕ) →         have x8 : (Fin (10 : ℕ) → Bool) → Bool := fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ));         have x9 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x9 : Fin (10 : ℕ) → Bool) (x10 : ℕ) => (x2.wires ({ gates := [x1], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x9))).getD x10 Bool.false;         ∃ (x10 : Fin (10 : ℕ) → Bool), (if x4 = Bool.true then !x9 x10 x3 else x9 x10 x3) ≠ x8 x10 := by
  intro g D u b hg hD hs
  dsimp only
  by_contra hcon
  push Not at hcon
  obtain ⟨F, hF⟩ : ∃ F : (Fin 10 → Bool) → Bool, F = fun x => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5 := ⟨_, rfl⟩
  obtain ⟨perm, hperm⟩ : ∃ perm : Fin 10 → Fin 10 → Fin 10, perm = ![![9, 6, 8, 5, 7, 4, 1, 3, 0, 2], ![6, 9, 7, 5, 8, 1, 4, 2, 0, 3], ![5, 7, 9, 6, 8, 0, 2, 4, 1, 3], ![5, 8, 6, 9, 7, 0, 3, 1, 4, 2], ![6, 8, 5, 7, 9, 1, 3, 0, 2, 4], ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8], ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6], ![1, 0, 4, 3, 2, 6, 5, 9, 8, 7], ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]] := ⟨_, rfl⟩
  let step : ∀ (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate), List Bool := fun (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) =>
      w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool), List Bool := fun (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool) => gs.foldl step l
  have run_cons : ∀ (g : PEqualNP.CircuitLowerBounds.Gate) (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool), run (g :: gs) l = run gs (step l g) := fun g gs l => rfl
  have run_append : ∀ (gs hs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool), run (gs ++ hs) l = run hs (run gs l) := by
    intro gs hs l
    simp [run, List.foldl_append]
  have run_length : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate), ∀ l : List Bool, (run gs l).length = l.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro l; simp [run]
    | cons g gs ih =>
      intro l
      rw [run_cons, ih]
      simp [step]
      omega
  have run_getD_lt : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate), ∀ (l : List Bool) (i : ℕ), i < l.length → (run gs l).getD i false = l.getD i false := by
    intro gs
    induction gs with
    | nil => intro l i _; rfl
    | cons g gs ih =>
      intro l i h
      rw [run_cons, ih _ _ (by simp [step]; omega)]
      simp only [step]
      rw [List.getD_append _ _ _ _ h]
  have run_getD_ge : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool) (i : ℕ) (h : l.length + gs.length ≤ i), (run gs l).getD i false = false := fun gs l i h =>
      List.getD_eq_default _ _ (by rw [run_length]; exact h)
  have prefix_getD : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool) (p : ℕ) (hp : p ≤ gs.length) (i : ℕ), (run (gs.take p) l).getD i false = if i < l.length + p then (run gs l).getD i false else false := by
    intro gs l p hp i
    have hs : run gs l = run (gs.drop p) (run (gs.take p) l) := by
      rw [← run_append, List.take_append_drop]
    have hl : (run (gs.take p) l).length = l.length + p := by
      rw [run_length]; simp; omega
    split_ifs with h
    · rw [hs, run_getD_lt (gs.drop p) _ _ (by omega)]
    · exact List.getD_eq_default _ _ (by omega)
  have gate_val : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (l : List Bool) (p : ℕ) (hp : p < gs.length), (run gs l).getD (l.length + p) false = gs[p].op.eval (gs[p].inputs.map fun i => (run (gs.take p) l).getD i false) := by
    intro gs l p hp
    have hs : run gs l = run (gs.drop (p + 1)) (step (run (gs.take p) l) gs[p]) := by
      conv_lhs => rw [← List.take_append_drop p gs, List.drop_eq_getElem_cons hp]
      rw [run_append, run_cons]
    have hl : (run (gs.take p) l).length = l.length + p := by
      rw [run_length]; simp; omega
    rw [hs, run_getD_lt _ _ _ (by simp [step]; omega)]
    simp only [step]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have : l.length + p - (run (gs.take p) l).length = 0 := by omega
    rw [this]
    rfl
  let effIns : ∀ (g : PEqualNP.CircuitLowerBounds.Gate), List ℕ := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
      PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) g.op g.inputs g.inputs (g.inputs.take 1)
        (fun _ => g.inputs) g.inputs
  have ev_and : ∀ (l : List Bool), PEqualNP.CircuitLowerBounds.GateOp.and.eval l = l.all id := fun l => rfl
  have ev_or : ∀ (l : List Bool), PEqualNP.CircuitLowerBounds.GateOp.or.eval l = l.any id := fun l => rfl
  have ev_not : ∀ (l : List Bool), PEqualNP.CircuitLowerBounds.GateOp.not.eval l = !(l.headD false) := fun l => rfl
  have eval_congr : ∀ (g : PEqualNP.CircuitLowerBounds.Gate) (f f' : ℕ → Bool) (ρ : ℕ → ℕ) (h : ∀ i ∈ effIns g, f i = f' (ρ i)), g.op.eval (g.inputs.map f) = g.op.eval ((g.inputs.map ρ).map f') := by
    intro g f f' ρ h
    rcases g with ⟨op, ins⟩
    cases op with
    | not =>
      cases ins with
      | nil => rfl
      | cons a rest =>
        have ha : f a = f' (ρ a) := h a (by simp [effIns])
        simp [ev_not, ha]
    | and =>
      have : ins.map f = (ins.map ρ).map f' := by
        rw [List.map_map]; apply List.map_congr_left; intro i hi; exact h i (by simpa [effIns] using hi)
      rw [this]
    | or =>
      have : ins.map f = (ins.map ρ).map f' := by
        rw [List.map_map]; apply List.map_congr_left; intro i hi; exact h i (by simpa [effIns] using hi)
      rw [this]
    | mod m =>
      have : ins.map f = (ins.map ρ).map f' := by
        rw [List.map_map]; apply List.map_congr_left; intro i hi; exact h i (by simpa [effIns] using hi)
      rw [this]
    | maj =>
      have : ins.map f = (ins.map ρ).map f' := by
        rw [List.map_map]; apply List.map_congr_left; intro i hi; exact h i (by simpa [effIns] using hi)
      rw [this]
  have agree : ∀ (B : ℕ → Prop) (gs : List PEqualNP.CircuitLowerBounds.Gate), ∀ (l l' : List Bool), l.length = l'.length → (∀ i, ¬ B i → l.getD i false = l'.getD i false) → (∀ p (hp : p < gs.length), ¬ B (l.length + p) → ∀ i ∈ effIns gs[p], i < l.length + p → ¬ B i) → ∀ i, ¬ B i → (run gs l).getD i false = (run gs l').getD i false := by
    intro B gs
    induction gs with
    | nil => intro l l' _ h0 _ i hi; exact h0 i hi
    | cons g gs ih =>
      intro l l' hlen h0 hg
      rw [run_cons, run_cons]
      apply ih
      · simp [step, hlen]
      · intro i hi
        simp only [step]
        by_cases hil : i < l.length
        · rw [List.getD_append _ _ _ _ hil, List.getD_append _ _ _ _ (by omega)]
          exact h0 i hi
        · by_cases hie : i = l.length
          · subst hie
            rw [List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ (by omega)]
            simp only [Nat.sub_self, hlen]
            simp only [List.getD_cons_zero]
            have := eval_congr g (fun i => l.getD i false) (fun i => l'.getD i false) id (by
              intro j hj
              by_cases hjl : j < l.length
              · have := hg 0 (by simp) (by simpa [hlen] using hi) j (by simpa using hj) (by omega)
                exact h0 j this
              · simp only [id]
                rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)])
            simpa using this
          · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      · intro p hp hB i hi hil
        have := hg (p + 1) (by simp; omega) (by simpa [step, Nat.add_assoc, Nat.add_comm 1 p] using hB) i
          (by simpa using hi) (by simp [step] at hil; omega)
        exact this
  let redir : ∀ (k r i : ℕ), ℕ := fun (k r i : ℕ) => if i = k then r else if k < i then i - 1 else i
  have redir_eq : ∀ (k r : ℕ), redir k r k = r := by
    intro k r
    simp [redir]
  have redir_gt : ∀ (k r i : ℕ) (h : k < i), redir k r i = i - 1 := by
    intro k r i h
    simp [redir, h, Nat.ne_of_gt h]
  have redir_lt : ∀ (k r i : ℕ) (h : i < k), redir k r i = i := by
    intro k r i h
    simp [redir, Nat.ne_of_lt h, Nat.not_lt.mpr h.le]
  let mapG : ∀ (k r : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), PEqualNP.CircuitLowerBounds.Gate := fun (k r : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate) => ⟨g.op, g.inputs.map (redir k r)⟩
  let FT : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate), Prop := fun (gs : List PEqualNP.CircuitLowerBounds.Gate) =>
      ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2
  let reads : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (p w : ℕ), Prop := fun (gs : List PEqualNP.CircuitLowerBounds.Gate) (p w : ℕ) => ∃ hp : p < gs.length, w ∈ effIns gs[p] ∧ w < 10 + p
  let erased : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (m r : ℕ), List PEqualNP.CircuitLowerBounds.Gate := fun (gs : List PEqualNP.CircuitLowerBounds.Gate) (m r : ℕ) =>
      gs.take m ++ (gs.drop (m + 1)).map (mapG (10 + m) r)
  let Comp : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ) (b : Bool) (S : (Fin 10 → Bool) → Prop), Prop := fun (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ) (b : Bool) (S : (Fin 10 → Bool) → Prop) =>
      ∀ x, S x → (if b = true then !((run gs (List.ofFn x)).getD u false)
        else (run gs (List.ofFn x)).getD u false) = F x
  let Rem : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ) (S : (Fin 10 → Bool) → Prop) (m r : ℕ), Prop := fun (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ) (S : (Fin 10 → Bool) → Prop) (m r : ℕ) =>
      m < gs.length ∧ r < 10 + m ∧
        ((∀ x, S x → (run gs (List.ofFn x)).getD r false = (run gs (List.ofFn x)).getD (10 + m) false) ∨
          ((∀ p, ¬ reads gs p (10 + m)) ∧ u ≠ 10 + m))
  have erase_inv : ∀ (k r : ℕ) (A : List Bool) (hA : A.length = k) (val : Bool), ∀ (post : List PEqualNP.CircuitLowerBounds.Gate) (T : List Bool), (∀ g ∈ post, k ∈ effIns g → (r < k ∧ A.getD r false = val) ∨ (k + T.length + post.length ≤ r ∧ val = false)) → run (post.map (mapG k r)) (A ++ T) = (run post (A ++ val :: T)).eraseIdx k := by
    intro k r A hA val
    intro post
    induction post with
    | nil =>
      intro T _
      simp [run, hA, List.eraseIdx_append_of_length_le]
    | cons g post ih =>
      intro T hpost
      have hval : g.op.eval (g.inputs.map fun i => (A ++ val :: T).getD i false) =
          (mapG k r g).op.eval ((mapG k r g).inputs.map fun i => (A ++ T).getD i false) := by
        apply eval_congr g _ _ (redir k r)
        intro i hi
        dsimp only [redir]
        by_cases hik : i = k
        · rw [if_pos hik]
          have hcase := hpost g (List.mem_cons_self) (hik ▸ hi)
          have hL : (A ++ val :: T).getD i false = val := by
            rw [List.getD_append_right _ _ _ _ (by omega)]
            have : i - A.length = 0 := by omega
            rw [this]; rfl
          rw [hL]
          rcases hcase with ⟨hrk, hrv⟩ | ⟨hrbig, hvf⟩
          · rw [List.getD_append _ _ _ _ (by omega), hrv]
          · rw [List.getD_eq_default _ _ (by simp; omega), hvf]
        · by_cases hlt : k < i
          · rw [if_neg hik, if_pos hlt]
            rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
            obtain ⟨j, rfl⟩ : ∃ j, i = k + 1 + j := ⟨i - k - 1, by omega⟩
            have e1 : k + 1 + j - A.length = j + 1 := by omega
            have e2 : k + 1 + j - 1 - A.length = j := by omega
            rw [e1, e2]
            simp
          · rw [if_neg hik, if_neg hlt]
            rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      have hrest := ih (T ++ [g.op.eval (g.inputs.map fun i => (A ++ val :: T).getD i false)]) (by
        intro g' hg' hk'
        rcases hpost g' (List.mem_cons_of_mem _ hg') hk' with h | ⟨h1, h2⟩
        · exact Or.inl h
        · right; refine ⟨?_, h2⟩; simp at h1 ⊢; omega)
      rw [List.map_cons, run_cons, run_cons]
      simp only [step] at hrest ⊢
      rw [← hval]
      simpa [List.append_assoc] using hrest
  have erase_main : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (m r : ℕ) (hm : m < gs.length) (hr : r < 10 + m) (l : List Bool) (hl : l.length = 10) (hcond : (run gs l).getD r false = (run gs l).getD (10 + m) false ∨ ∀ p, ¬ reads gs p (10 + m)), run (erased gs m r) l = (run gs l).eraseIdx (10 + m) := by
    intro gs m r hm hr l hl hcond
    have hA : (run (gs.take m) l).length = 10 + m := by
      rw [run_length]; simp; omega
    have hs : run gs l = run (gs.drop (m + 1)) (run (gs.take m) l ++
        [gs[m].op.eval (gs[m].inputs.map fun i => (run (gs.take m) l).getD i false)]) := by
      conv_lhs => rw [← List.take_append_drop m gs, List.drop_eq_getElem_cons hm]
      rw [run_append, run_cons]
      try rfl
    have hnew : run (erased gs m r) l = run ((gs.drop (m + 1)).map (mapG (10 + m) r)) (run (gs.take m) l) := by
      simp only [erased]
      rw [run_append]
    have key := erase_inv (10 + m) r (run (gs.take m) l) hA
      (gs[m].op.eval (gs[m].inputs.map fun i => (run (gs.take m) l).getD i false)) (gs.drop (m + 1)) [] (by
        intro g hg hk
        rcases hcond with hc | hd
        · left
          refine ⟨hr, ?_⟩
          rw [prefix_getD gs l m hm.le r, if_pos (by omega), hc]
          have := gate_val gs l m hm
          rw [hl] at this
          exact this
        · exfalso
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
          rw [List.getElem_drop] at hk
          exact hd (m + 1 + j) ⟨by simp at hj; omega, hk, by omega⟩)
    rw [hnew, hs]
    simpa using key
  have eraseIdx_getD : ∀ (L : List Bool) (k j : ℕ), (L.eraseIdx k).getD j false = L.getD (if j < k then j else j + 1) false := by
    intro L k j
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eraseIdx]
    split_ifs <;> rfl
  have effIns_mapG : ∀ (k r : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), effIns (mapG k r g) = (effIns g).map (redir k r) := by
    intro k r g
    rcases g with ⟨op, ins⟩
    cases op <;> simp [effIns, mapG, List.map_take]
  have erase_ok : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ) (b : Bool) (S : (Fin 10 → Bool) → Prop) (m r : ℕ) (hFT : FT gs) (hC : Comp gs u b S) (hR : Rem gs u S m r), FT (erased gs m r) ∧ (erased gs m r).length + 1 = gs.length ∧ Comp (erased gs m r) (redir (10 + m) r u) b S ∧ (∀ p w, p ≠ m → w < 10 + m → reads gs p w → reads (erased gs m r) (if p < m then p else p - 1) w) := by
    intro gs u b S m r hFT hC hR
    obtain ⟨hm, hr, hcase⟩ := hR
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [erased, List.mem_append, List.mem_map] at hg
      rcases hg with hg | ⟨g0, hg0, rfl⟩
      · exact hFT g (List.mem_of_mem_take hg)
      · have := hFT g0 (List.mem_of_mem_drop hg0)
        simpa [mapG] using this
    · simp [erased]; omega
    · intro x hx
      have hmain := erase_main gs m r hm hr (List.ofFn x) (by simp) (by
        rcases hcase with hc | ⟨hd, _⟩
        · exact Or.inl (hc x hx)
        · exact Or.inr hd)
      rw [hmain, eraseIdx_getD]
      have hval : (run gs (List.ofFn x)).getD (if redir (10 + m) r u < 10 + m then redir (10 + m) r u
          else redir (10 + m) r u + 1) false = (run gs (List.ofFn x)).getD u false := by
        by_cases hu : u = 10 + m
        · rw [hu, redir_eq, if_pos hr]
          rcases hcase with hc | ⟨_, hne⟩
          · rw [hc x hx]
          · exact absurd hu hne
        · by_cases hlt : 10 + m < u
          · rw [redir_gt _ _ _ hlt, if_neg (by omega)]
            congr 1; omega
          · rw [redir_lt _ _ _ (by omega), if_pos (by omega)]
      rw [hval]
      exact hC x hx
    · intro p w hpm hw hrd
      obtain ⟨hp, hwe, hwl⟩ := hrd
      by_cases hlt : p < m
      · rw [if_pos hlt]
        refine ⟨by simp [erased]; omega, ?_, hwl⟩
        have : (erased gs m r)[p]'(by simp [erased]; omega) = gs[p] := by
          simp only [erased]
          rw [List.getElem_append_left (by simp; omega)]
          simp
        rw [this]; exact hwe
      · rw [if_neg hlt]
        have hpm' : m < p := by omega
        refine ⟨by simp [erased]; omega, ?_, by omega⟩
        have : (erased gs m r)[p - 1]'(by simp [erased]; omega) = mapG (10 + m) r gs[p] := by
          simp only [erased]
          rw [List.getElem_append_right (by simp; omega)]
          simp only [List.getElem_map, List.getElem_drop]
          congr 2
          simp; omega
        rw [this, effIns_mapG]
        have hw' : redir (10 + m) r w = w := by
          exact redir_lt _ _ _ hw
        rw [← hw']
        exact List.mem_map_of_mem hwe
  have gate_shape : ∀ (op : PEqualNP.CircuitLowerBounds.GateOp) (ins : List ℕ) (hop : op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or, PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) (hlen : ins.length ≤ 2) (w : ℕ) (hwe : w ∈ effIns ⟨op, ins⟩), (∃ φ : Bool → Bool, ∀ f : ℕ → Bool, op.eval (ins.map f) = φ (f w)) ∨ (∃ y, y ≠ w ∧ (ins = [w, y] ∨ ins = [y, w]) ∧ ((op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ f : ℕ → Bool, op.eval (ins.map f) = (f w || f y)) ∨ (op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∀ f : ℕ → Bool, op.eval (ins.map f) = (f w && f y)))) := by
    intro op ins hop hlen w hwe
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
      · simp [effIns] at hwe
      · simp [effIns] at hwe; subst hwe
        left; exact ⟨id, fun f => by simp [ev_and, ev_or, ev_not]⟩
      · simp [effIns] at hwe
        by_cases hab : a = b
        · subst hab
          rcases hwe with rfl | rfl <;> (left; exact ⟨id, fun f => by simp [ev_and, ev_or, ev_not]⟩)
        · rcases hwe with rfl | rfl
          · right; exact ⟨b, Ne.symm hab, Or.inl rfl, Or.inr ⟨rfl, fun f => by simp [ev_and, ev_or, ev_not]⟩⟩
          · right; refine ⟨a, hab, Or.inr rfl, Or.inr ⟨rfl, fun f => ?_⟩⟩
            simp [ev_and, Bool.and_comm]
      · simp at hlen
    · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
      · simp [effIns] at hwe
      · simp [effIns] at hwe; subst hwe
        left; exact ⟨id, fun f => by simp [ev_and, ev_or, ev_not]⟩
      · simp [effIns] at hwe
        by_cases hab : a = b
        · subst hab
          rcases hwe with rfl | rfl <;> (left; exact ⟨id, fun f => by simp [ev_and, ev_or, ev_not]⟩)
        · rcases hwe with rfl | rfl
          · right; exact ⟨b, Ne.symm hab, Or.inl rfl, Or.inl ⟨rfl, fun f => by simp [ev_and, ev_or, ev_not]⟩⟩
          · right; refine ⟨a, hab, Or.inr rfl, Or.inl ⟨rfl, fun f => ?_⟩⟩
            simp [ev_or, Bool.or_comm]
      · simp at hlen
    · rcases ins with _ | ⟨a, rest⟩
      · simp [effIns] at hwe
      · simp [effIns] at hwe; subst hwe
        left; exact ⟨fun t => !t, fun f => by simp [ev_and, ev_or, ev_not]⟩
  have step_lemma : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (hFT : FT gs) (S : (Fin 10 → Bool) → Prop) (w : ℕ) (c : Bool) (hw : ∀ x, S x → (run gs (List.ofFn x)).getD w false = c) (p : ℕ) (hp : reads gs p w), (∃ c', ∀ x, S x → (run gs (List.ofFn x)).getD (10 + p) false = c') ∨ (∃ (hp' : p < gs.length) (y : ℕ), y < 10 + p ∧ y ≠ w ∧ (gs[p].inputs = [w, y] ∨ gs[p].inputs = [y, w]) ∧ ((gs[p].op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ c = false) ∨ (gs[p].op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ c = true)) ∧ ∀ x, S x → (run gs (List.ofFn x)).getD (10 + p) false = (run gs (List.ofFn x)).getD y false) := by
    intro gs hFT S w c hw p hp
    obtain ⟨hp', hwe, hwl⟩ := hp
    have hval : ∀ x : Fin 10 → Bool, (run gs (List.ofFn x)).getD (10 + p) false =
        gs[p].op.eval (gs[p].inputs.map fun i =>
          if i < 10 + p then (run gs (List.ofFn x)).getD i false else false) := by
      intro x
      have h1 := gate_val gs (List.ofFn x) p hp'
      simp only [List.length_ofFn] at h1
      rw [h1]
      congr 1
      apply List.map_congr_left
      intro i _
      rw [prefix_getD gs (List.ofFn x) p hp'.le i]
      simp
    obtain ⟨hop, hlen⟩ := hFT gs[p] (List.getElem_mem hp')
    rcases gate_shape gs[p].op gs[p].inputs hop hlen w hwe with ⟨φ, hφ⟩ | ⟨y, hyw, hins, hcase⟩
    · left
      refine ⟨φ c, fun x hx => ?_⟩
      rw [hval x, hφ, if_pos hwl, hw x hx]
    · rcases hcase with ⟨hor, hf⟩ | ⟨hand, hf⟩
      · cases c
        · by_cases hy : y < 10 + p
          · right
            refine ⟨hp', y, hy, hyw, hins, Or.inl ⟨hor, rfl⟩, fun x hx => ?_⟩
            rw [hval x, hf, if_pos hwl, hw x hx, if_pos hy]
            simp
          · left
            refine ⟨false, fun x hx => ?_⟩
            rw [hval x, hf, if_pos hwl, hw x hx, if_neg hy]
            simp
        · left
          refine ⟨true, fun x hx => ?_⟩
          rw [hval x, hf, if_pos hwl, hw x hx]
          simp
      · cases c
        · left
          refine ⟨false, fun x hx => ?_⟩
          rw [hval x, hf, if_pos hwl, hw x hx]
          simp
        · by_cases hy : y < 10 + p
          · right
            refine ⟨hp', y, hy, hyw, hins, Or.inr ⟨hand, rfl⟩, fun x hx => ?_⟩
            rw [hval x, hf, if_pos hwl, hw x hx, if_pos hy]
            simp
          · left
            refine ⟨false, fun x hx => ?_⟩
            rw [hval x, hf, if_pos hwl, hw x hx, if_neg hy]
            simp
  have chain : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (hFT : FT gs) (u : ℕ) (S : (Fin 10 → Bool) → Prop) (hnc : ∃ x x', S x ∧ S x' ∧
      (run gs (List.ofFn x)).getD u false ≠ (run gs (List.ofFn x')).getD u false), ∀ k q c, gs.length - q = k → q < gs.length → (∀ x, S x → (run gs (List.ofFn x)).getD (10 + q) false = c) → ∃ m r, Rem gs u S m r ∧ q ≤ m ∧ (m = q → (∀ p, ¬ reads gs p (10 + q)) ∧ u ≠ 10 + q) := by
    intro gs hFT u S hnc
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro q c hk hq hc
    have hu : u ≠ 10 + q := by
      rintro rfl
      obtain ⟨x, x', hx, hx', hne⟩ := hnc
      exact hne (by rw [hc x hx, hc x' hx'])
    by_cases hrd : ∃ p, reads gs p (10 + q)
    · obtain ⟨p, hp⟩ := hrd
      have hpq : q < p := by obtain ⟨_, _, h⟩ := hp; omega
      rcases step_lemma gs hFT S (10 + q) c hc p hp with ⟨c', hc'⟩ | ⟨hp', y, hy, _, _, _, hcopy⟩
      · obtain ⟨m, r, hR, hpm, _⟩ := ih (gs.length - p) (by omega) p c' rfl hp.1 hc'
        exact ⟨m, r, hR, by omega, fun h => by omega⟩
      · exact ⟨p, y, ⟨hp', hy, Or.inl (fun x hx => (hcopy x hx).symm)⟩, by omega, fun h => by omega⟩
    · push Not at hrd
      exact ⟨q, 0, ⟨hq, by omega, Or.inr ⟨hrd, hu⟩⟩, le_rfl, fun _ => ⟨hrd, hu⟩⟩
  have ofFn_getD : ∀ (x : Fin 10 → Bool) (v : Fin 10), (List.ofFn x).getD v false = x v := by
    intro x v
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [v.isLt]
  have nonconst_of_comp : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ) (b : Bool) (S : (Fin 10 → Bool) → Prop) (hC : Comp gs u b S) (h : ∃ x x', S x ∧ S x' ∧ F x ≠ F x'), ∃ x x', S x ∧ S x' ∧ (run gs (List.ofFn x)).getD u false ≠ (run gs (List.ofFn x')).getD u false := by
    intro gs u b S hC h
    obtain ⟨x, x', hx, hx', hne⟩ := h
    refine ⟨x, x', hx, hx', fun heq => hne ?_⟩
    rw [← hC x hx, ← hC x' hx', heq]
  have PF_edge : ∀ v : Fin 10, ∃ a b : Fin 10, a ≠ v ∧ b ≠ v ∧ F (fun i => decide (i = a) || decide (i = b)) = true := by
    subst hF; decide
  have PF_zero : F (fun _ => false) = false := by
    subst hF; decide
  have PF_noncon : ∀ (v : Fin 10), ∃ x x' : Fin 10 → Bool, x v = false ∧ x' v = false ∧ F x ≠ F x' := by
    intro v
    obtain ⟨a, b, ha, hb, h⟩ := PF_edge v
    refine ⟨fun _ => false, fun i => decide (i = a) || decide (i = b), rfl, ?_, ?_⟩
    · simp [Ne.symm ha, Ne.symm hb]
    · rw [h, PF_zero]; decide
  have single_rem : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (hFT : FT gs) (u : ℕ) (b : Bool) (v : Fin 10) (hC : Comp gs u b (fun x => x v = false)) (p : ℕ) (hp : reads gs p v), ∃ gs' u', FT gs' ∧ gs'.length + 1 = gs.length ∧ Comp gs' u' b (fun x => x v = false) := by
    intro gs hFT u b v hC p hp
    have hnc := nonconst_of_comp gs u b _ hC (PF_noncon v)
    have hwv : ∀ x : Fin 10 → Bool, x v = false → (run gs (List.ofFn x)).getD v false = false := by
      intro x hx
      rw [run_getD_lt _ _ _ (by simp), ofFn_getD, hx]
    obtain ⟨m, r, hR⟩ : ∃ m r, Rem gs u (fun x => x v = false) m r := by
      rcases step_lemma gs hFT _ v false hwv p hp with ⟨c', hc'⟩ | ⟨hp', y, hy, _, _, _, hcopy⟩
      · obtain ⟨m, r, hR, _⟩ := chain gs hFT u _ hnc _ p c' rfl hp.1 hc'
        exact ⟨m, r, hR⟩
      · exact ⟨p, y, hp', hy, Or.inl fun x hx => (hcopy x hx).symm⟩
    obtain ⟨h1, h2, h3, _⟩ := erase_ok gs u b _ m r hFT hC hR
    exact ⟨_, _, h1, h2, h3⟩
  have ofFn_getD' : ∀ (x : Fin 10 → Bool) (i : ℕ), (List.ofFn x).getD i false = if h : i < 10 then x ⟨i, h⟩ else false := by
    intro x i
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    split_ifs <;> simp
  have agree_x : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (B : ℕ → Prop) (x x' : Fin 10 → Bool) (hx : ∀ i : Fin 10, ¬ B i → x i = x' i) (hg : ∀ p i, ¬ B (10 + p) → reads gs p i → ¬ B i) (u : ℕ) (hu : ¬ B u), (run gs (List.ofFn x)).getD u false = (run gs (List.ofFn x')).getD u false := by
    intro gs B x x' hx hg u hu
    apply agree B gs (List.ofFn x) (List.ofFn x') (by simp)
    · intro i hi
      rw [ofFn_getD', ofFn_getD']
      split_ifs with h
      · exact hx ⟨i, h⟩ hi
      · rfl
    · intro p hp hB i hi hil
      simp only [List.length_ofFn] at hB hil
      exact hg p i hB ⟨hp, hi, hil⟩
    · exact hu
  have PF_dep' : ∀ v : Fin 10, ∃ a : Fin 10, a ≠ v ∧ F (fun i => decide (i = v) || decide (i = a)) ≠ F (fun i => decide (i = a)) := by
    subst hF; decide
  have PF_dep : ∀ (v : Fin 10), ∃ x x' : Fin 10 → Bool, (∀ i, i ≠ v → x i = x' i) ∧ F x ≠ F x' := by
    intro v
    obtain ⟨a, _, h⟩ := PF_dep' v
    refine ⟨_, _, fun i hi => ?_, h⟩
    simp [hi]
  have PF_single : ∀ i : Fin 10, F (fun j => decide (j = i)) = false := by
    subst hF; decide
  have PF_or' : ∀ v w : Fin 10, v ≠ w → ∃ a : Fin 10, F (fun i => decide (i = v) || decide (i = a)) ≠ F (fun i => decide (i = w) || decide (i = a)) := by
    subst hF; decide
  have out_ge : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ) (b : Bool) (hC : Comp gs u b (fun _ => True)), 10 ≤ u := by
    intro gs u b hC
    by_contra h
    push Not at h
    have hv : ∀ x : Fin 10 → Bool, (run gs (List.ofFn x)).getD u false = x ⟨u, h⟩ := by
      intro x
      rw [run_getD_lt _ _ _ (by simpa using h), ofFn_getD']
      simp [h]
    cases b
    · have := hC (fun j => decide (j = ⟨u, h⟩)) trivial
      rw [hv, PF_single] at this
      simp at this
    · have := hC (fun _ => false) trivial
      rw [hv, PF_zero] at this
      simp at this
  have has_reader : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (u : ℕ) (b : Bool) (hC : Comp gs u b (fun _ => True)) (v : Fin 10), ∃ p, reads gs p v := by
    intro gs u b hC v
    by_contra h
    push Not at h
    have hu := out_ge gs u b hC
    obtain ⟨x, x', hxx, hne⟩ := PF_dep v
    apply hne
    rw [← hC x trivial, ← hC x' trivial]
    rw [agree_x gs (fun i => i = (v : ℕ)) x x' (fun i hi => hxx i (fun h' => hi (by rw [h'])))
      (fun p i _ hr hi => by rw [hi] at hr; exact h p hr) u (by omega)]
  have one_rem : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (hFT : FT gs) (u : ℕ) (b : Bool) (hC : Comp gs u b (fun _ => True)), ∃ gs' u', FT gs' ∧ gs'.length + 1 = gs.length ∧ Comp gs' u' b (fun x => x 9 = false) := by
    intro gs hFT u b hC
    obtain ⟨p, hp⟩ := has_reader gs u b hC 9
    exact single_rem gs hFT u b 9 (fun x _ => hC x trivial) p hp
  let bad : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (v : ℕ), Prop := fun (gs : List PEqualNP.CircuitLowerBounds.Gate) (v : ℕ) =>
      ∃ r, (∀ p, reads gs p v → p = r) ∧ ∃ hr : r < gs.length, gs[r].op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        ∃ y, y < 10 + r ∧ y ≠ v ∧ (gs[r].inputs = [v, y] ∨ gs[r].inputs = [y, v])
  have good_two : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (hFT : FT gs) (u : ℕ) (b : Bool) (hC : Comp gs u b (fun _ => True)) (v : Fin 10) (hgood : ¬ bad gs v), ∃ gs'' u'', FT gs'' ∧ gs''.length + 2 = gs.length ∧ Comp gs'' u'' b (fun x => x v = false) := by
    intro gs hFT u b hC v hgood
    have hu10 := out_ge gs u b hC
    have hCS : Comp gs u b (fun x => x v = false) := fun x _ => hC x trivial
    have hnc := nonconst_of_comp gs u b _ hCS (PF_noncon v)
    have hwv : ∀ x : Fin 10 → Bool, x v = false → (run gs (List.ofFn x)).getD v false = false := by
      intro x hx
      rw [run_getD_lt _ _ _ (by simp), ofFn_getD, hx]
    suffices H : ∃ m r p, Rem gs u (fun x => x v = false) m r ∧ p ≠ m ∧ reads gs p v by
      obtain ⟨m, r, p, hR, hpm, hp⟩ := H
      obtain ⟨h1, h2, h3, h4⟩ := erase_ok gs u b _ m r hFT hCS hR
      have hp' := h4 p v hpm (by omega) hp
      obtain ⟨gs'', u'', k1, k2, k3⟩ := single_rem _ h1 _ b v h3 _ hp'
      exact ⟨gs'', u'', k1, by omega, k3⟩
    by_cases h2 : ∃ p1 p2, p1 ≠ p2 ∧ reads gs p1 v ∧ reads gs p2 v
    · obtain ⟨p1, p2, hne, hp1, hp2⟩ := h2
      obtain ⟨m, r, hR⟩ : ∃ m r, Rem gs u (fun x => x v = false) m r := by
        rcases step_lemma gs hFT _ v false hwv p1 hp1 with ⟨c', hc'⟩ | ⟨hp', y, hy, _, _, _, hcopy⟩
        · obtain ⟨m, r, hR, _⟩ := chain gs hFT u _ hnc _ p1 c' rfl hp1.1 hc'
          exact ⟨m, r, hR⟩
        · exact ⟨p1, y, hp', hy, Or.inl fun x hx => (hcopy x hx).symm⟩
      by_cases hm : p1 = m
      · exact ⟨m, r, p2, hR, by rw [← hm]; exact Ne.symm hne, hp2⟩
      · exact ⟨m, r, p1, hR, hm, hp1⟩
    · obtain ⟨q, hq⟩ := has_reader gs u b hC v
      have huniq : ∀ p, reads gs p v → p = q := by
        intro p hp
        by_contra hne
        exact h2 ⟨p, q, hne, hp, hq⟩
      rcases step_lemma gs hFT _ v false hwv q hq with ⟨c', hc'⟩ | ⟨hq', y, hy, hyv, hins, hopc, _⟩
      · obtain ⟨m, r, hR, hqm, hdead⟩ := chain gs hFT u _ hnc _ q c' rfl hq.1 hc'
        by_cases hmq : m = q
        · exfalso
          obtain ⟨hnr, hune⟩ := hdead hmq
          obtain ⟨x, x', hxx, hne⟩ := PF_dep v
          apply hne
          rw [← hC x trivial, ← hC x' trivial]
          rw [agree_x gs (fun i => i = (v : ℕ) ∨ i = 10 + q) x x'
            (fun i hi => hxx i (fun h' => hi (Or.inl (by rw [h']))))
            (fun p i hB hr hi => by
              rcases hi with hi | hi
              · rw [hi] at hr
                have := huniq p hr
                exact hB (Or.inr (by rw [this]))
              · rw [hi] at hr
                exact hnr p hr)
            u (by
              rintro (h | h)
              · omega
              · exact hune h)]
        · exact ⟨m, r, q, hR, Ne.symm hmq, hq⟩
      · exfalso
        apply hgood
        refine ⟨q, huniq, hq', ?_, y, hy, hyv, hins⟩
        rcases hopc with ⟨h, _⟩ | ⟨_, h⟩
        · exact h
        · exact absurd h (by decide)
  have first_gate : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (hFT : FT gs) (u : ℕ) (b : Bool) (hC : Comp gs u b (fun _ => True)) (hne : 0 < gs.length) (hbad : ∀ v : Fin 10, bad gs v), ∃ c, ∀ x : Fin 10 → Bool, True → (run gs (List.ofFn x)).getD (10 + 0) false = c := by
    intro gs hFT u b hC hne hbad
    have hu10 := out_ge gs u b hC
    by_cases hrd : ∃ v : Fin 10, reads gs 0 v
    · exfalso
      obtain ⟨v, hv⟩ := hrd
      obtain ⟨r, huniq, hr, hor, y, hy, hyv, hins⟩ := hbad v
      have hr0 : r = 0 := (huniq 0 hv).symm
      subst hr0
      have hy10 : y < 10 := by omega
      have hyr : reads gs 0 y := by
        refine ⟨hr, ?_, by omega⟩
        simp only [effIns, hor]
        rcases hins with h | h <;> rw [h] <;> simp
      obtain ⟨r', huniq', -⟩ := hbad ⟨y, hy10⟩
      have hr'0 : r' = 0 := (huniq' 0 hyr).symm
      subst hr'0
      obtain ⟨a, ha⟩ := PF_or' v ⟨y, hy10⟩ (fun h => hyv (by subst h; rfl))
      set x : Fin 10 → Bool := fun i => decide (i = v) || decide (i = a) with hxdef
      set x' : Fin 10 → Bool := fun i => decide (i = (⟨y, hy10⟩ : Fin 10)) || decide (i = a) with hx'def
      have key : (run gs (List.ofFn x)).getD u false = (run gs (List.ofFn x')).getD u false := by
        obtain ⟨g0, rest, hgs⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hne)
        subst hgs
        simp only [List.getElem_cons_zero] at hor hins
        rw [run_cons, run_cons]
        apply agree (fun i => i = (v : ℕ) ∨ i = y) rest _ _ (by simp [step])
        · intro i hi
          simp only [step]
          by_cases hil : i < 10
          · rw [List.getD_append _ _ _ _ (by simpa using hil), List.getD_append _ _ _ _ (by simpa using hil),
              ofFn_getD', ofFn_getD', dif_pos hil, dif_pos hil]
            have h1 : (⟨i, hil⟩ : Fin 10) ≠ v := fun h => hi (Or.inl (by rw [← h]))
            have h2 : (⟨i, hil⟩ : Fin 10) ≠ ⟨y, hy10⟩ := fun h => hi (Or.inr (by
              have := congrArg Fin.val h; simpa using this))
            simp [hxdef, hx'def, h1, h2]
          · by_cases hi10 : i = 10
            · subst hi10
              rw [List.getD_append_right _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
              simp only [List.length_ofFn, Nat.sub_self, List.getD_cons_zero]
              have e1 : (List.ofFn x).getD v false = true := by rw [ofFn_getD]; simp [hxdef]
              have e2 : (List.ofFn x').getD y false = true := by
                rw [ofFn_getD' x' y, dif_pos hy10]; simp [hx'def]
              rcases hins with h | h <;> rw [h, hor] <;>
                simp only [ev_or, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
                  e1, e2] <;> simp
            · rw [List.getD_eq_default _ _ (by simp; omega),
                List.getD_eq_default _ _ (by simp; omega)]
        · intro p hp hB i hi hil
          rintro (h | h)
          · have := huniq (p + 1) ⟨by simp; omega, by simpa [h] using hi, by simp [step] at hil; omega⟩
            omega
          · have := huniq' (p + 1) ⟨by simp; omega, by simpa [h] using hi, by simp [step] at hil; omega⟩
            omega
        · rintro (h | h) <;> omega
      apply ha
      rw [← hC x trivial, ← hC x' trivial, key]
    · push Not at hrd
      obtain ⟨g0, rest, hgs⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos hne)
      refine ⟨g0.op.eval ((g0.inputs.map id).map fun _ => false), fun x _ => ?_⟩
      have hv := gate_val gs (List.ofFn x) 0 hne
      simp only [List.length_ofFn, List.take_zero] at hv
      rw [hv]
      have hg0 : gs[0] = g0 := by subst hgs; rfl
      rw [hg0]
      apply eval_congr g0 _ _ id
      intro i hi
      have hi10 : ¬ i < 10 := by
        intro hi10
        apply hrd ⟨i, hi10⟩
        exact ⟨hne, by rw [hg0]; exact hi, by simpa using hi10⟩
      simp only [run]
      rw [List.foldl_nil, List.getD_eq_default _ _ (by simp; omega)]
  let rlbl : ∀ (π : Fin 10 → Fin 10) (i : ℕ), ℕ := fun (π : Fin 10 → Fin 10) (i : ℕ) => if h : i < 10 then (π ⟨i, h⟩ : ℕ) else i
  let rlblG : ∀ (π : Fin 10 → Fin 10) (g : PEqualNP.CircuitLowerBounds.Gate), PEqualNP.CircuitLowerBounds.Gate := fun (π : Fin 10 → Fin 10) (g : PEqualNP.CircuitLowerBounds.Gate) => ⟨g.op, g.inputs.map (rlbl π)⟩
  have rlbl_run : ∀ (π : Fin 10 → Fin 10) (gs : List PEqualNP.CircuitLowerBounds.Gate), ∀ (L L' : List Bool), L.length = L'.length → 10 ≤ L.length → (∀ k, L.getD (rlbl π k) false = L'.getD k false) → ∀ k, (run (gs.map (rlblG π)) L).getD (rlbl π k) false = (run gs L').getD k false := by
    intro π gs
    induction gs with
    | nil => intro L L' _ _ h k; exact h k
    | cons g gs ih =>
      intro L L' hlen h10 h
      rw [List.map_cons, run_cons, run_cons]
      apply ih
      · simp [step, hlen]
      · simp [step]; omega
      · intro k
        simp only [step]
        have hval : (rlblG π g).op.eval ((rlblG π g).inputs.map fun i => L.getD i false) =
            g.op.eval (g.inputs.map fun i => L'.getD i false) := by
          symm
          exact eval_congr g _ _ (rlbl π) (fun i _ => (h i).symm)
        rw [hval]
        by_cases hk : k < 10
        · have hr : rlbl π k = π ⟨k, hk⟩ := by simp [rlbl, hk]
          rw [hr, List.getD_append _ _ _ _ (by have := (π ⟨k, hk⟩).isLt; omega),
            List.getD_append _ _ _ _ (by omega), ← hr]
          exact h k
        · have hr : rlbl π k = k := by simp [rlbl, hk]
          rw [hr]
          by_cases hkl : k < L.length
          · rw [List.getD_append _ _ _ _ hkl, List.getD_append _ _ _ _ (by omega)]
            have := h k
            rwa [hr] at this
          · by_cases hke : k = L.length
            · subst hke
              rw [List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ (by omega)]
              simp [hlen]
            · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  have perm9 : ∀ v : Fin 10, perm v v = 9 := by
    subst hperm; decide
  have PF_bits : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Bool, ∀ v : Fin 10, F (![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] ∘ perm v) = F ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9] := by
    subst hF hperm; decide
  have perm_aut : ∀ (v : Fin 10) (x : Fin 10 → Bool), F (x ∘ perm v) = F x := by
    intro v x
    have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := by
      funext i; fin_cases i <;> rfl
    rw [hx]
    exact PF_bits _ _ _ _ _ _ _ _ _ _ v
  have rlbl_comp : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (hFT : FT gs) (u : ℕ) (b : Bool) (v : Fin 10) (hC : Comp gs u b (fun x => x v = false)), FT (gs.map (rlblG (perm v))) ∧ (gs.map (rlblG (perm v))).length = gs.length ∧ Comp (gs.map (rlblG (perm v))) (rlbl (perm v) u) b (fun x => x 9 = false) := by
    intro gs hFT u b v hC
    refine ⟨?_, by simp, ?_⟩
    · intro g hg
      simp only [List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      have := hFT g0 hg0
      simpa [rlblG] using this
    · intro x hx
      have key := rlbl_run (perm v) gs (List.ofFn x) (List.ofFn (x ∘ perm v)) (by simp) (by simp)
        (by
          intro k
          rw [ofFn_getD', ofFn_getD']
          by_cases hk : k < 10
          · have hr : rlbl (perm v) k = perm v ⟨k, hk⟩ := by simp [rlbl, hk]
            rw [hr, dif_pos (perm v ⟨k, hk⟩).isLt, dif_pos hk]
            rfl
          · have hr : rlbl (perm v) k = k := by simp [rlbl, hk]
            rw [hr, dif_neg hk, dif_neg hk]) u
      rw [key, hC (x ∘ perm v) (by simp [perm9, hx]), perm_aut]
  have h1_core : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (hFT : FT gs) (hlen : gs.length ≤ 17) (u : ℕ) (b : Bool) (hC : Comp gs u b (fun _ => True)), ∃ gs' u', FT gs' ∧ gs'.length ≤ 15 ∧ Comp gs' u' b (fun x => x 9 = false) := by
    intro gs hFT hlen u b hC
    by_cases h15 : gs.length ≤ 15
    · exact ⟨gs, u, hFT, h15, fun x _ => hC x trivial⟩
    by_cases h16 : gs.length = 16
    · obtain ⟨gs', u', h1, h2, h3⟩ := one_rem gs hFT u b hC
      exact ⟨gs', u', h1, by omega, h3⟩
    have h17 : gs.length = 17 := by omega
    by_cases hgood : ∃ v : Fin 10, ¬ bad gs v
    · obtain ⟨v, hv⟩ := hgood
      obtain ⟨gs'', u'', k1, k2, k3⟩ := good_two gs hFT u b hC v hv
      obtain ⟨r1, r2, r3⟩ := rlbl_comp gs'' k1 u'' b v k3
      exact ⟨_, _, r1, by omega, r3⟩
    · push Not at hgood
      obtain ⟨c, hc⟩ := first_gate gs hFT u b hC (by omega) hgood
      have hnc := nonconst_of_comp gs u b (fun _ => True) hC (by
        obtain ⟨x, x', _, _, h⟩ := PF_noncon 0
        exact ⟨x, x', trivial, trivial, h⟩)
      obtain ⟨m, r, hR, -⟩ := chain gs hFT u _ hnc _ 0 c rfl (by omega) hc
      obtain ⟨e1, e2, e3, -⟩ := erase_ok gs u b _ m r hFT hC hR
      obtain ⟨gs', u', f1, f2, f3⟩ := one_rem _ e1 _ b e3
      exact ⟨gs', u', f1, by omega, f3⟩

  obtain ⟨E, u', b', hE, hEs, hEq⟩ : ∃ (E : PEqualNP.CircuitLowerBounds.Circuit) (u' : ℕ) (b' : Bool), PEqualNP.MetaComplexity.FanInTwo E ∧ E.size ≤ 15 ∧ ∀ x : Fin 10 → Bool, x 9 = false → (if b' = true then !((E.wires (List.ofFn x)).getD u' false) else (E.wires (List.ofFn x)).getD u' false) = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) := by
    rcases Nat.lt_or_ge D.size 17 with hlt | hge
    · have hFTg : FT (g :: D.gates) := by
        intro g' hg'
        rcases List.mem_cons.mp hg' with h | h
        · rw [h]; exact hg g (List.mem_singleton_self g)
        · exact hD g' h
      have hCg : Comp (g :: D.gates) u b (fun _ => True) := by
        intro x _
        rw [hF]
        exact hcon x
      obtain ⟨gs', u'', k1, k2, k3⟩ := h1_core (g :: D.gates) hFTg (by
        have : D.gates.length ≤ 16 := by
          have : D.gates.length < 17 := hlt
          omega
        simp only [List.length_cons]; omega) u b hCg
      refine ⟨⟨gs', u''⟩, u'', b, k1, k2, fun x hx => ?_⟩
      have := k3 x hx
      rw [hF] at this
      exact this
    · exact h2 g D u b hg hD (by omega) hcon
  obtain ⟨x, hx, hne⟩ := h3 E u' b' hE hEs
  exact hne (hEq x hx)
