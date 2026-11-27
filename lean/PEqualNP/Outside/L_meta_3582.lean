import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3582_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def petFn (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 5 && x 7 ||
  x 6 && x 8 || x 8 && x 5

private def maskFn (m : ℕ) (k : Fin 9) : Bool :=
  m.testBit k.val

private def valAt (x : Fin 9 → Bool) (j : Fin 10) : Bool :=
  if h : j.val < 9 then x ⟨j.val, h⟩ else x 0 || x 2

private def witnessMasks : List ℕ :=
  [1, 2, 4, 5, 8, 9, 10, 16, 18, 20, 32, 34, 36, 40, 48, 64, 65, 68, 128, 129, 130, 136, 144, 256, 257, 260]

private lemma witness_exists :
    ∀ (i : Fin 9) (j : Fin 10) (b0 : Bool),
      i ≠ 0 → i ≠ 2 → i.castSucc ≠ j →
      ∃ m ∈ witnessMasks,
        maskFn m i = false ∧
        valAt (maskFn m) j = b0 ∧
        petFn (maskFn m) ≠ petFn (Function.update (maskFn m) i true) := by
  decide

private lemma petFn_one_hot :
    ∀ i : Fin 9, petFn (fun k : Fin 9 => decide (k = i)) = false := by
  decide

private lemma gate_eval_eq_of_not_contains {h : Gate} {i : ℕ}
    (hop : h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not)
    (hlen : h.inputs.length ≤ 2)
    (hnot : (h.inputs.take (bif h.op.eval [false] then 1 else 2)).contains i = false)
    {w1 w2 : List Bool} (hagree : ∀ k : ℕ, k ≠ i → w1.getD k false = w2.getD k false) :
    h.op.eval (h.inputs.map (fun k => w1.getD k false)) =
      h.op.eval (h.inputs.map (fun k => w2.getD k false)) := by
  rcases hop with hop | hop | hop
  · rw [hop] at hnot ⊢
    have htake : h.inputs.take 2 = h.inputs := List.take_of_length_le hlen
    have hfalse : GateOp.and.eval [false] = false := rfl
    rw [hfalse, Bool.cond_false, htake] at hnot
    congr 1
    apply List.map_congr_left
    intro k hk
    apply hagree k
    intro heq
    subst heq
    have hmem : h.inputs.contains k = true := List.contains_iff_mem.mpr hk
    rw [hmem] at hnot
    exact Bool.noConfusion hnot
  · rw [hop] at hnot ⊢
    have htake : h.inputs.take 2 = h.inputs := List.take_of_length_le hlen
    have hfalse : GateOp.or.eval [false] = false := rfl
    rw [hfalse, Bool.cond_false, htake] at hnot
    congr 1
    apply List.map_congr_left
    intro k hk
    apply hagree k
    intro heq
    subst heq
    have hmem : h.inputs.contains k = true := List.contains_iff_mem.mpr hk
    rw [hmem] at hnot
    exact Bool.noConfusion hnot
  · rw [hop] at hnot ⊢
    have htrue : GateOp.not.eval [false] = true := rfl
    rw [htrue, Bool.cond_true] at hnot
    cases hinp : h.inputs with
    | nil => rfl
    | cons a rest =>
      rw [hinp] at hnot
      have hne : a ≠ i := by
        intro heq
        subst heq
        simp at hnot
      simp only [GateOp.eval, List.map_cons, List.headD]
      rw [hagree a hne]

private lemma append_getD_agree {w1 w2 : List Bool} {b : Bool} {i : ℕ}
    (hlen : w1.length = w2.length)
    (hagree : ∀ k : ℕ, k ≠ i → w1.getD k false = w2.getD k false) :
    ∀ k : ℕ, k ≠ i → (w1 ++ [b]).getD k false = (w2 ++ [b]).getD k false := by
  intro k hki
  by_cases hk : k < w1.length
  · have hk2 : k < w2.length := hlen ▸ hk
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hk, List.getElem?_append_left hk2]
    have h := hagree k hki
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD] at h
    exact h
  · by_cases hkeq : k = w1.length
    · subst hkeq
      have a1 : (w1 ++ [b]).getD w1.length false = b := by simp [List.getD_eq_getElem?_getD]
      have a2 : (w2 ++ [b]).getD w1.length false = b := by
        rw [hlen]; simp [List.getD_eq_getElem?_getD]
      rw [a1, a2]
    · have hge1 : (w1 ++ [b]).length ≤ k := by simp; omega
      have hge2 : (w2 ++ [b]).length ≤ k := by simp; omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none hge1, List.getElem?_eq_none hge2]

private lemma foldl_agree_except (gs : List Gate) (i : ℕ)
    (hfan : ∀ h ∈ gs, (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧ h.inputs.length ≤ 2)
    (hnot : ∀ h ∈ gs, (h.inputs.take (bif h.op.eval [false] then 1 else 2)).contains i = false) :
    ∀ (w1 w2 : List Bool), w1.length = w2.length →
      (∀ k : ℕ, k ≠ i → w1.getD k false = w2.getD k false) →
      (gs.foldl (fun w h => w ++ [h.op.eval (h.inputs.map (fun k => w.getD k false))]) w1).length =
        (gs.foldl (fun w h => w ++ [h.op.eval (h.inputs.map (fun k => w.getD k false))]) w2).length ∧
      (∀ k : ℕ, k ≠ i →
        (gs.foldl (fun w h => w ++ [h.op.eval (h.inputs.map (fun k => w.getD k false))]) w1).getD k false =
        (gs.foldl (fun w h => w ++ [h.op.eval (h.inputs.map (fun k => w.getD k false))]) w2).getD k false) := by
  induction gs with
  | nil => intro w1 w2 hlen hagree; exact ⟨hlen, hagree⟩
  | cons h gs ih =>
    intro w1 w2 hlen hagree
    simp only [List.foldl_cons]
    have hf := hfan h (List.mem_cons_self ..)
    have hn := hnot h (List.mem_cons_self ..)
    have hev := gate_eval_eq_of_not_contains hf.1 hf.2 hn hagree
    rw [hev]
    apply ih
      (fun h' hh' => hfan h' (List.mem_cons_of_mem h hh'))
      (fun h' hh' => hnot h' (List.mem_cons_of_mem h hh'))
    · simp [hlen]
    · exact append_getD_agree hlen hagree

private lemma foldl_getD_lt (gs : List Gate) :
    ∀ (acc : List Bool) (k : ℕ), k < acc.length →
      (gs.foldl (fun w h => w ++ [h.op.eval (h.inputs.map (fun m => w.getD m false))]) acc).getD k false =
        acc.getD k false := by
  induction gs with
  | nil => intro acc k _; rfl
  | cons h gs ih =>
    intro acc k hk
    simp only [List.foldl_cons]
    rw [ih _ k (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

private lemma gate_const_eval {g : Gate} {i j : ℕ} {b0 : Bool}
    (hop : (g.op = GateOp.and ∧ b0 = false) ∨ (g.op = GateOp.or ∧ b0 = true))
    (hinp : g.inputs = [i, j] ∨ g.inputs = [j, i])
    {w : List Bool} (hj : w.getD j false = b0) :
    g.op.eval (g.inputs.map (fun k => w.getD k false)) = b0 := by
  rw [List.getD_eq_getElem?_getD] at hj
  rcases hop with ⟨hg, rfl⟩ | ⟨hg, rfl⟩ <;> rcases hinp with hi | hi <;>
    simp [hg, hi, GateOp.eval, hj]

private lemma ext_inp_getD (x : Fin 9 → Bool) (j : Fin 10) :
    (List.ofFn x ++ [x 0 || x 2]).getD j.val false = valAt x j := by
  unfold valAt
  by_cases hj : j.val < 9
  · simp only [hj, dite_true]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [hj])]
    simp only [List.getElem?_ofFn, hj, dite_true, Option.getD_some]
  · simp only [hj, dite_false]
    have hjeq : j.val = 9 := by omega
    rw [hjeq, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp

end PEqualNP.Outside.L_meta_3582_aux

theorem PEqualNP.Outside.L_meta_3582 :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (9 : ℕ) → Bool), x2.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ))]) = x1 x4) → ∀ (x5 : Fin (9 : ℕ)) (x6 : Fin (10 : ℕ)), x5 ≠ (0 : Fin (9 : ℕ)) → x5 ≠ (2 : Fin (9 : ℕ)) → x5.castSucc ≠ x6 → ∀ x10 ∈ x2.gates, x10.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x10.op = PEqualNP.CircuitLowerBounds.GateOp.or → x10.inputs = [↑x5, ↑x6] ∨ x10.inputs = [↑x6, ↑x5] → (2 : ℕ) ≤ (List.filter (fun (x14 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x14.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x14.inputs).contains ↑x5) x2.gates).length := by
  intro x1 C hfan heval i j hi0 hi2 hij g hg hg_op hg_inp
  open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_3582_aux in
  by_contra hlt
  let p : Gate → Bool := fun h =>
    (h.inputs.take (bif h.op.eval [false] then 1 else 2)).contains i.val
  change ¬ (2 ≤ (C.gates.filter p).length) at hlt
  have hpg : p g = true := by
    rcases hg_op with hop | hop <;> rcases hg_inp with hin | hin <;>
      simp [p, hop, hin, GateOp.eval]
  obtain ⟨pref, suff, hsplit⟩ := List.append_of_mem hg
  have hfilt : (C.gates.filter p).length = (pref.filter p).length + 1 + (suff.filter p).length := by
    rw [hsplit, List.filter_append, List.filter_cons, hpg]
    simp; omega
  have hpref0 : pref.filter p = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hsuff0 : suff.filter p = [] := List.eq_nil_of_length_eq_zero (by omega)
  have hpref_not : ∀ h ∈ pref, p h = false := by
    intro h hh
    by_contra hne
    have hpt : p h = true := by cases hp : p h <;> simp_all
    have hmem : h ∈ pref.filter p := List.mem_filter.mpr ⟨hh, hpt⟩
    rw [hpref0] at hmem
    exact List.not_mem_nil hmem
  have hsuff_not : ∀ h ∈ suff, p h = false := by
    intro h hh
    by_contra hne
    have hpt : p h = true := by cases hp : p h <;> simp_all
    have hmem : h ∈ suff.filter p := List.mem_filter.mpr ⟨hh, hpt⟩
    rw [hsuff0] at hmem
    exact List.not_mem_nil hmem
  have hfan_mem : ∀ h ∈ C.gates,
      (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧ h.inputs.length ≤ 2 := by
    intro h hh
    have hf := hfan h hh
    refine ⟨?_, hf.2⟩
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hf.1
  have hfan_pref : ∀ h ∈ pref,
      (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧ h.inputs.length ≤ 2 :=
    fun h hh => hfan_mem h (by rw [hsplit]; simp [hh])
  have hfan_suff : ∀ h ∈ suff,
      (h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not) ∧ h.inputs.length ≤ 2 :=
    fun h hh => hfan_mem h (by rw [hsplit]; simp [hh])
  -- Rule out C.output = i.val
  have hout_ne : C.output ≠ i.val := by
    intro hout_eq
    let z : Fin 9 → Bool := fun k => decide (k = i)
    have hz := heval z
    have hev1 : C.eval (List.ofFn z ++ [z 0 || z 2]) = true := by
      unfold Circuit.eval Circuit.wires
      rw [hout_eq, foldl_getD_lt C.gates _ i.val (by simp; omega)]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp)]
      simp only [List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some, z, Fin.eta, decide_true]
    have hf0 : x1 z = false := petFn_one_hot i
    rw [hev1, hf0] at hz
    exact Bool.noConfusion hz
  -- Pick b0 so g evaluates constantly to b0 when wire j = b0
  let b0 : Bool := match g.op with | GateOp.and => false | _ => true
  have hb0_spec : (g.op = GateOp.and ∧ b0 = false) ∨ (g.op = GateOp.or ∧ b0 = true) := by
    rcases hg_op with hop | hop
    · exact Or.inl ⟨hop, by simp [b0, hop]⟩
    · exact Or.inr ⟨hop, by simp [b0, hop]⟩
  obtain ⟨m, _, hmi, hmj, hdiff⟩ := witness_exists i j b0 hi0 hi2 hij
  let y1 : Fin 9 → Bool := maskFn m
  let y2 : Fin 9 → Bool := Function.update y1 i true
  let inp1 : List Bool := List.ofFn y1 ++ [y1 0 || y1 2]
  let inp2 : List Bool := List.ofFn y2 ++ [y2 0 || y2 2]
  have hy2_0 : y2 0 = y1 0 := Function.update_of_ne hi0.symm true y1
  have hy2_2 : y2 2 = y1 2 := Function.update_of_ne hi2.symm true y1
  have hinp_len : inp1.length = inp2.length := by simp [inp1, inp2]
  have hinp_agree : ∀ k : ℕ, k ≠ i.val → inp1.getD k false = inp2.getD k false := by
    intro k hki
    by_cases hk9 : k < 9
    · simp only [inp1, inp2, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by simp [hk9] : k < (List.ofFn y1).length),
        List.getElem?_append_left (by simp [hk9] : k < (List.ofFn y2).length)]
      simp only [List.getElem?_ofFn, hk9, dite_true, Option.getD_some]
      have hne : (⟨k, hk9⟩ : Fin 9) ≠ i := fun h => hki (congrArg Fin.val h)
      exact (Function.update_of_ne hne true y1).symm
    · simp only [inp1, inp2, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by simp; omega : (List.ofFn y1).length ≤ k),
        List.getElem?_append_right (by simp; omega : (List.ofFn y2).length ≤ k)]
      simp [hy2_0, hy2_2]
  have hj_ne_i : j.val ≠ i.val := fun h => hij (Fin.ext h.symm)
  have hj1 : inp1.getD j.val false = b0 := by
    simpa [inp1, y1] using (ext_inp_getD y1 j).trans hmj
  have hj2 : inp2.getD j.val false = b0 := by
    rw [← hinp_agree j.val hj_ne_i, hj1]
  have hstep1 := foldl_agree_except pref i.val hfan_pref hpref_not inp1 inp2 hinp_len hinp_agree
  let w1 := pref.foldl (fun w h => w ++ [h.op.eval (h.inputs.map (fun k => w.getD k false))]) inp1
  let w2 := pref.foldl (fun w h => w ++ [h.op.eval (h.inputs.map (fun k => w.getD k false))]) inp2
  have hwlen : w1.length = w2.length := hstep1.1
  have hwag : ∀ k : ℕ, k ≠ i.val → w1.getD k false = w2.getD k false := hstep1.2
  have hw1j : w1.getD j.val false = b0 := by
    rw [foldl_getD_lt pref inp1 j.val (by simp [inp1]), hj1]
  have hw2j : w2.getD j.val false = b0 := by
    rw [foldl_getD_lt pref inp2 j.val (by simp [inp2]), hj2]
  have hg1 : g.op.eval (g.inputs.map (fun k => w1.getD k false)) = b0 :=
    gate_const_eval hb0_spec hg_inp hw1j
  have hg2 : g.op.eval (g.inputs.map (fun k => w2.getD k false)) = b0 :=
    gate_const_eval hb0_spec hg_inp hw2j
  have hmid_len : (w1 ++ [b0]).length = (w2 ++ [b0]).length := by simp [hwlen]
  have hmid_agree : ∀ k : ℕ, k ≠ i.val → (w1 ++ [b0]).getD k false = (w2 ++ [b0]).getD k false :=
    append_getD_agree hwlen hwag
  have hfinal := foldl_agree_except suff i.val hfan_suff hsuff_not (w1 ++ [b0]) (w2 ++ [b0]) hmid_len hmid_agree
  have hev_eq : C.eval inp1 = C.eval inp2 := by
    unfold Circuit.eval Circuit.wires
    rw [hsplit, List.foldl_append, List.foldl_cons, List.foldl_append, List.foldl_cons]
    change (suff.foldl (fun w h => w ++ [h.op.eval (h.inputs.map (fun k => w.getD k false))])
      (w1 ++ [g.op.eval (g.inputs.map (fun k => w1.getD k false))])).getD C.output false =
      (suff.foldl (fun w h => w ++ [h.op.eval (h.inputs.map (fun k => w.getD k false))])
      (w2 ++ [g.op.eval (g.inputs.map (fun k => w2.getD k false))])).getD C.output false
    rw [hg1, hg2]
    exact hfinal.2 C.output hout_ne
  rw [heval y1, heval y2] at hev_eq
  exact hdiff hev_eq
