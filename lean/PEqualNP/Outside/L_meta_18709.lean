import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18709_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_append_left_lt (a b : List Bool) (i : ℕ) (hi : i < a.length) :
    (a ++ b).getD i false = a.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_eq (a : List Bool) (v : Bool) :
    (a ++ [v]).getD a.length false = v := by
  simp [List.getD_eq_getElem?_getD]

theorem foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl wstep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (wstep w g) (by simp [wstep]; omega)]
    exact getD_append_left_lt w _ i hi

theorem foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl wstep w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl wstep w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      rw [Nat.add_zero, foldl_getD_lt gs (wstep w g) w.length (by simp [wstep])]
      simp only [List.getElem_cons_zero]
      have hws : (wstep w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
        rw [wstep, getD_snoc_eq]
      rw [hws]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi]
        rw [foldl_getD_lt gs (wstep w g) i (by simp [wstep]; omega), wstep, getD_append_left_lt w _ i hi]
      · rw [ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
    | succ j' =>
      have hj' : j' < gs.length := by simpa using hj
      have hlen : (wstep w g).length = w.length + 1 := by simp [wstep]
      have hidx : w.length + (j' + 1) = (wstep w g).length + j' := by omega
      rw [hidx, ih (wstep w g) j' hj']
      simp only [List.getElem_cons_succ]

theorem foldl_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (wx wy : List Bool) (hlen : wx.length = wy.length)
    (hle : ∀ k, wx.getD k false = true → wy.getD k false = true) :
    ∀ k, (gs.foldl wstep wx).getD k false = true → (gs.foldl wstep wy).getD k false = true := by
  induction gs generalizing wx wy with
  | nil => exact hle
  | cons g gs ih =>
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
    · simp [wstep, hlen]
    · intro k hk
      by_cases hlt : k < wx.length
      · rw [wstep, getD_append_left_lt _ _ k (by omega)]
        rw [wstep, getD_append_left_lt _ _ k hlt] at hk
        exact hle k hk
      · by_cases heq : k = wx.length
        · subst heq
          rw [wstep, getD_snoc_eq] at hk
          rw [wstep, hlen, getD_snoc_eq]
          rcases hgs g (List.mem_cons_self ..) with hop | hop
          · rw [hop] at hk ⊢
            simp only [GateOp.eval, List.all_eq_true, List.mem_map] at hk ⊢
            rintro _ ⟨i, hi, rfl⟩
            exact hle i (hk _ ⟨i, hi, rfl⟩)
          · rw [hop] at hk ⊢
            simp only [GateOp.eval, List.any_eq_true, List.mem_map] at hk ⊢
            rcases hk with ⟨_, ⟨i, hi, rfl⟩, htrue⟩
            exact ⟨wy.getD i false, ⟨i, hi, rfl⟩, hle i htrue⟩
        · rw [wstep, List.getD_eq_default _ _ (by simp; omega)] at hk
          cases hk

theorem wires_mono (n : ℕ) (C : Circuit) (hao : IsAO2 n C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ k, (C.wires (List.ofFn x)).getD k false = true → (C.wires (List.ofFn y)).getD k false = true := by
  apply foldl_mono C.gates hao.1
  · simp [List.length_ofFn]
  · intro k hk
    by_cases hlt : k < n
    · rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn] at hk ⊢
      simp only [hlt, dite_true, Option.getD_some] at hk ⊢
      exact hxy ⟨k, hlt⟩ hk
    · rw [List.getD_eq_default _ _ (by simp [List.length_ofFn]; omega)] at hk
      cases hk

theorem main_proof :
    ∀ (n : Nat) (C : Circuit) (j a b : Nat), IsAO2 n C → C.output = n + j →
      C.gates[j]? = some ⟨.and, [a, b]⟩ → ∀ s t : Fin n,
      (C.wires (List.ofFn (fun i : Fin n => decide (i = s)))).getD a false = true →
      (C.wires (List.ofFn (fun i : Fin n => decide (i = t)))).getD b false = true →
      C.eval (List.ofFn (fun i : Fin n => decide (i = s ∨ i = t))) = true := by
  intro n C j a b hao hout hgate s t ha hb
  have hj : j < C.gates.length := by
    by_contra h
    rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hgate
    cases hgate
  have hgj : C.gates[j] = ⟨GateOp.and, [a, b]⟩ := by
    rw [List.getElem?_eq_getElem hj] at hgate
    exact Option.some.inj hgate
  have hgateAt : PEqualNP.MetaComplexity.NestedCover.gateAt C j = ⟨GateOp.and, [a, b]⟩ := by
    simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getElem?_eq_getElem hj, hgj]
  have ha_lt : a < n + j := by
    have := hao.2.1 j hj a (by simp [hgateAt])
    exact this
  have hb_lt : b < n + j := by
    have := hao.2.1 j hj b (by simp [hgateAt])
    exact this
  let xy : Fin n → Bool := fun i => decide (i = s ∨ i = t)
  have ha' : (C.wires (List.ofFn xy)).getD a false = true :=
    wires_mono n C hao _ xy (fun i hi => by simp [xy, of_decide_eq_true hi]) a ha
  have hb' : (C.wires (List.ofFn xy)).getD b false = true :=
    wires_mono n C hao _ xy (fun i hi => by simp [xy, of_decide_eq_true hi]) b hb
  change (C.gates.foldl wstep (List.ofFn xy)).getD C.output false = true
  have hout' : C.output = (List.ofFn xy).length + j := by simp [hout, List.length_ofFn]
  rw [hout', foldl_getD_gate C.gates (List.ofFn xy) j hj, hgj]
  simp only [List.length_ofFn, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true]
  rw [ite_eq_left ha_lt, ite_eq_left hb_lt]
  exact Bool.and_eq_true_iff.mpr ⟨ha', hb'⟩

end PEqualNP.Outside.L_meta_18709_aux

theorem PEqualNP.Outside.L_meta_18709 : (∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 x5 : ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → x2.output = x1 + x3 → x2.gates[x3]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x4, x5] : PEqualNP.CircuitLowerBounds.Gate } → ∀ (x9 x10 : Fin x1), (x2.wires (List.ofFn fun (x11 : Fin x1) => Decidable.decide (x11 = x9))).getD x4 Bool.false = Bool.true → (x2.wires (List.ofFn fun (x12 : Fin x1) => Decidable.decide (x12 = x10))).getD x5 Bool.false = Bool.true → x2.eval (List.ofFn fun (x13 : Fin x1) => Decidable.decide (x13 = x9 ∨ x13 = x10)) = Bool.true)  := by
  exact PEqualNP.Outside.L_meta_18709_aux.main_proof
