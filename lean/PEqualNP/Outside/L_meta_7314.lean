import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_7314_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def circuitStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl circuitStep x := rfl

private lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl circuitStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g rest ih => rw [List.foldl_cons, ih]; simp [circuitStep]; omega

private lemma getD_snoc_lt (l : List Bool) (a : Bool) (i : ℕ) (hi : i < l.length) :
    (l ++ [a]).getD i false = l.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq (l : List Bool) (a : Bool) :
    (l ++ [a]).getD l.length false = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

private lemma getD_prefix_foldl (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl circuitStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g rest ih =>
    rw [List.foldl_cons, ih (circuitStep w g) (by simp [circuitStep]; omega)]
    exact getD_snoc_lt w _ i hi

private lemma prepend_not0 (f : (Fin 10 → Bool) → Bool) (C : Circuit)
    (hfan : FanInTwo C) (hsize : C.size ≤ 17)
    (heval : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!x (0 : Fin 10)]) = f x) :
    HasCircuitSize 10 f 18 := by
  let g0 : Gate := ⟨GateOp.not, [0]⟩
  refine ⟨⟨g0 :: C.gates, C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons] at hg
    rcases hg with rfl | h
    · exact ⟨by simp [g0], by simp [g0]⟩
    · exact hfan g h
  · change (g0 :: C.gates).length ≤ 18
    have : C.gates.length ≤ 17 := hsize
    simp; omega
  · intro x
    unfold Circuit.eval
    rw [wires_eq_foldl]
    dsimp only
    rw [List.foldl_cons]
    have hstep : circuitStep (List.ofFn x) g0 = List.ofFn x ++ [!x (0 : Fin 10)] := by
      unfold circuitStep
      simp [g0, GateOp.eval]
    rw [hstep]
    exact heval x

private def remap (k u : ℕ) : ℕ :=
  if u = k then 0 else if k < u then u - 1 else u

private lemma foldl_remap (k : ℕ) (hk : 1 ≤ k) (gs : List Gate) (w1 w2 : List Bool)
    (hlen : w1.length = w2.length + 1) (hge : k ≤ w2.length)
    (hrel : ∀ u : ℕ, w2.getD (remap k u) false = w1.getD u false) :
    ∀ u : ℕ,
      ((gs.map fun h => Gate.mk h.op (h.inputs.map (remap k))).foldl circuitStep w2).getD (remap k u) false =
        (gs.foldl circuitStep w1).getD u false := by
  induction gs generalizing w1 w2 with
  | nil => exact hrel
  | cons g rest ih =>
    simp only [List.map_cons, List.foldl_cons]
    have hval : (Gate.mk g.op (g.inputs.map (remap k))).op.eval
        ((g.inputs.map (remap k)).map fun i => w2.getD i false) =
        g.op.eval (g.inputs.map fun i => w1.getD i false) := by
      congr 1
      rw [List.map_map]
      congr 1
      funext u
      exact hrel u
    have hlen' : (circuitStep w1 g).length = (circuitStep w2 (Gate.mk g.op (g.inputs.map (remap k)))).length + 1 := by
      simp [circuitStep, hlen]
    have hge' : k ≤ (circuitStep w2 (Gate.mk g.op (g.inputs.map (remap k)))).length := by
      simp [circuitStep]; omega
    apply ih (circuitStep w1 g) (circuitStep w2 (Gate.mk g.op (g.inputs.map (remap k)))) hlen' hge'
    intro u
    unfold circuitStep
    rw [hval]
    by_cases hlt : u < w1.length
    · rw [getD_snoc_lt w1 _ u hlt]
      by_cases huk : u = k
      · subst huk
        have hrm : remap u u = 0 := by simp [remap]
        rw [hrm, getD_snoc_lt w2 _ 0 (by omega)]
        simpa [hrm] using hrel u
      · by_cases hku : k < u
        · have hrm : remap k u = u - 1 := by simp [remap, huk, hku]
          rw [hrm, getD_snoc_lt w2 _ (u - 1) (by omega)]
          simpa [hrm] using hrel u
        · have hrm : remap k u = u := by simp [remap, huk, hku]
          rw [hrm, getD_snoc_lt w2 _ u (by omega)]
          simpa [hrm] using hrel u
    · by_cases heq : u = w1.length
      · subst heq
        have hne : w1.length ≠ k := by omega
        have hgt : k < w1.length := by omega
        have hrm : remap k w1.length = w2.length := by simp [remap, hne, hgt]; omega
        rw [hrm, getD_snoc_eq, getD_snoc_eq]
      · have hgt : w1.length < u := by omega
        have hne : u ≠ k := by omega
        have hku : k < u := by omega
        have hrm : remap k u = u - 1 := by simp [remap, hne, hku]
        rw [hrm, List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma main_proof :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ))));
    ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (18 : ℕ) →
      (∀ (x5 : Fin (10 : ℕ) → Bool), x2.eval (List.ofFn x5 ++ [!x5 (0 : Fin (10 : ℕ))]) = x1 x5) →
      (x2.size < (18 : ℕ) ∨ x2.output ≠ (28 : ℕ) ∨ ∃ (x6 : Fin x2.size), (x2.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x2.gates.get x6).inputs.head? = Option.some (10 : ℕ)) →
      PEqualNP.MetaComplexity.HasCircuitSize (10 : ℕ) x1 (18 : ℕ) := by
  intro x1 C hfan hsize heval hdisj
  have hclen : C.gates.length ≤ 18 := hsize
  rcases hdisj with hlt18 | hne28 | ⟨idx, hnot, hhead⟩
  · exact prepend_not0 x1 C hfan (by omega) heval
  · by_cases hlt18 : C.size < 18
    · exact prepend_not0 x1 C hfan (by omega) heval
    · have hlen18 : C.gates.length = 18 := by change ¬ C.gates.length < 18 at hlt18; omega
      by_cases hout_lt : C.output < 28
      · let C' : Circuit := ⟨C.gates.take 17, C.output⟩
        have hfan' : FanInTwo C' := fun g hg => hfan g (List.mem_of_mem_take hg)
        have hsize' : C'.size ≤ 17 := by change (C.gates.take 17).length ≤ 17; simp
        apply prepend_not0 x1 C' hfan' hsize'
        intro x
        rw [← heval x]
        unfold Circuit.eval
        rw [wires_eq_foldl, wires_eq_foldl]
        dsimp only [C']
        have hsplit : C.gates = C.gates.take 17 ++ C.gates.drop 17 := (List.take_append_drop 17 C.gates).symm
        conv_rhs => rw [hsplit, List.foldl_append]
        have hpre_len : ((C.gates.take 17).foldl circuitStep (List.ofFn x ++ [!x (0 : Fin 10)])).length = 28 := by
          rw [foldl_len]; simp [hlen18]
        exact (getD_prefix_foldl (C.gates.drop 17) _ C.output (by omega)).symm
      · exfalso
        have hge29 : 29 ≤ C.output := by omega
        have hf : C.eval (List.ofFn (fun _ : Fin 10 => true) ++ [!true]) = false := by
          unfold Circuit.eval
          rw [wires_eq_foldl]
          apply List.getD_eq_default
          rw [foldl_len]; simp [hlen18]; omega
        have ht : x1 (fun _ : Fin 10 => true) = true := by decide
        have h := heval (fun _ : Fin 10 => true)
        rw [hf, ht] at h
        cases h
  · let i := idx.val
    have hi : i < C.gates.length := idx.isLt
    let pre := C.gates.take i
    let g := C.gates[i]
    let suf := C.gates.drop (i + 1)
    have hsplit : C.gates = pre ++ g :: suf := by
      have h1 := List.take_append_drop i C.gates
      have h2 : C.gates.drop i = g :: suf := List.drop_eq_getElem_cons hi
      rw [h2] at h1
      exact h1.symm
    have hg_op : g.op = GateOp.not := hnot
    have hg_head : g.inputs.head? = some 10 := hhead
    let k := 11 + i
    let C' : Circuit := ⟨pre ++ suf.map (fun h => Gate.mk h.op (h.inputs.map (remap k))), remap k C.output⟩
    have hfan' : FanInTwo C' := by
      intro h hh
      simp only [C', List.mem_append, List.mem_map] at hh
      rcases hh with h1 | ⟨h0, h0mem, rfl⟩
      · exact hfan h (List.mem_of_mem_take h1)
      · have := hfan h0 (List.mem_of_mem_drop h0mem)
        exact ⟨this.1, by simp [this.2]⟩
    have hsize' : C'.size ≤ 17 := by
      change (pre ++ suf.map _).length ≤ 17
      simp only [List.length_append, List.length_map, pre, suf, List.length_take, List.length_drop]
      omega
    apply prepend_not0 x1 C' hfan' hsize'
    intro x
    rw [← heval x]
    let inp := List.ofFn x ++ [!x (0 : Fin 10)]
    have hinp_len : inp.length = 11 := by simp [inp]
    have hinp0 : inp.getD 0 false = x (0 : Fin 10) := by
      dsimp only [inp]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp), List.getElem?_ofFn]
      simp
    have hinp10 : inp.getD 10 false = !x (0 : Fin 10) := by
      dsimp only [inp]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
      simp
    unfold Circuit.eval
    rw [wires_eq_foldl, wires_eq_foldl]
    dsimp only [C']
    conv_rhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, List.foldl_cons]
    let w2 := pre.foldl circuitStep inp
    have hw2_len : w2.length = k := by
      dsimp only [w2, pre, k]
      rw [foldl_len, hinp_len, List.length_take]; omega
    have hw2_0 : w2.getD 0 false = x (0 : Fin 10) := by
      rw [getD_prefix_foldl pre inp 0 (by omega), hinp0]
    have hw2_10 : w2.getD 10 false = !x (0 : Fin 10) := by
      rw [getD_prefix_foldl pre inp 10 (by omega), hinp10]
    have hstep_g : circuitStep w2 g = w2 ++ [x (0 : Fin 10)] := by
      unfold circuitStep
      rcases g with ⟨op, ins⟩
      dsimp only at hg_op hg_head
      subst hg_op
      cases ins with
      | nil => simp at hg_head
      | cons a rest =>
        simp only [List.head?_cons, Option.some.injEq] at hg_head
        subst hg_head
        simp only [GateOp.eval, List.map_cons, List.headD_cons, hw2_10, Bool.not_not]
    rw [hstep_g]
    apply foldl_remap k (by omega) suf (w2 ++ [x (0 : Fin 10)]) w2 (by simp) (by omega)
    intro u
    by_cases huk : u = k
    · rw [huk]
      have hrm : remap k k = 0 := by simp [remap]
      rw [hrm, hw2_0, ← hw2_len, getD_snoc_eq]
    · by_cases hku : k < u
      · have hrm : remap k u = u - 1 := by simp [remap, huk, hku]
        rw [hrm, List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]
      · have hrm : remap k u = u := by simp [remap, huk, hku]
        rw [hrm, getD_snoc_lt w2 _ u (by omega)]

end PEqualNP.Outside.L_meta_7314_aux

theorem PEqualNP.Outside.L_meta_7314 :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => (List.finRange (5 : ℕ)).any fun (x2 : Fin (5 : ℕ)) => x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.castAdd (5 : ℕ) (x2 + (1 : Fin (5 : ℕ)))) || x1 (Fin.castAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) x2) || x1 (Fin.natAdd (5 : ℕ) x2) && x1 (Fin.natAdd (5 : ℕ) (x2 + (2 : Fin (5 : ℕ)))); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → x2.size ≤ (18 : ℕ) → (∀ (x5 : Fin (10 : ℕ) → Bool), x2.eval (List.ofFn x5 ++ [!x5 (0 : Fin (10 : ℕ))]) = x1 x5) → (x2.size < (18 : ℕ) ∨ x2.output ≠ (28 : ℕ) ∨ ∃ (x6 : Fin x2.size), (x2.gates.get x6).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x2.gates.get x6).inputs.head? = Option.some (10 : ℕ)) → PEqualNP.MetaComplexity.HasCircuitSize (10 : ℕ) x1 (18 : ℕ) :=
  PEqualNP.Outside.L_meta_7314_aux.main_proof
