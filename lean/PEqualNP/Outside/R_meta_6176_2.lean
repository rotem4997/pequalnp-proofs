import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.HeptadCover

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_6176_2
    (full : ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧
          x (Fin.natAdd 7 l) = true) → 27 ≤ D.size)
    (punc_le9 : ∀ D : Circuit, D.size ≤ 25 → 1 ≤ D.size → IsAO2 14 D →
      (∀ j < D.size, opnd D j 0 ≠ opnd D j 1) →
      (∀ w < 13 + D.size, ∃ j < D.size, w ∈ (gateAt D j).inputs) →
      D.output = 13 + D.size →
      (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true →
        ∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧
          x (Fin.natAdd 7 l) = true) →
      (∀ p l : Fin 7, p ∈ fanoLines l → (p ≠ 0 ∨ l ≠ 0) →
        D.eval (List.ofFn (pairInput (Fin.castAdd 7 p) (Fin.natAdd 7 l))) = true) →
      D.eval (List.ofFn (pairInput (0 : Fin 14) (7 : Fin 14))) = false →
      ((Finset.range 14).filter fun v : ℕ => ∃ w < 13 + D.size,
        2 ≤ ((Finset.range D.size).filter fun j => w ∈ (gateAt D j).inputs).card ∧
        (D.wires (List.ofFn fun i : Fin 14 => decide (i.val = v))).getD w false = true).card ≤ 9 →
      False)
    (punc_10 : ∀ D : Circuit, D.size ≤ 25 → 1 ≤ D.size → IsAO2 14 D →
      (∀ j < D.size, opnd D j 0 ≠ opnd D j 1) →
      (∀ w < 13 + D.size, ∃ j < D.size, w ∈ (gateAt D j).inputs) →
      D.output = 13 + D.size →
      (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true →
        ∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧
          x (Fin.natAdd 7 l) = true) →
      (∀ p l : Fin 7, p ∈ fanoLines l → (p ≠ 0 ∨ l ≠ 0) →
        D.eval (List.ofFn (pairInput (Fin.castAdd 7 p) (Fin.natAdd 7 l))) = true) →
      D.eval (List.ofFn (pairInput (0 : Fin 14) (7 : Fin 14))) = false →
      ((Finset.range 14).filter fun v : ℕ => ∃ w < 13 + D.size,
        2 ≤ ((Finset.range D.size).filter fun j => w ∈ (gateAt D j).inputs).card ∧
        (D.wires (List.ofFn fun i : Fin 14 => decide (i.val = v))).getD w false = true).card = 10 →
      False)
    (punc_ge11 : ∀ D : Circuit, D.size ≤ 25 → 1 ≤ D.size → IsAO2 14 D →
      (∀ j < D.size, opnd D j 0 ≠ opnd D j 1) →
      (∀ w < 13 + D.size, ∃ j < D.size, w ∈ (gateAt D j).inputs) →
      D.output = 13 + D.size →
      (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true →
        ∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧
          x (Fin.natAdd 7 l) = true) →
      (∀ p l : Fin 7, p ∈ fanoLines l → (p ≠ 0 ∨ l ≠ 0) →
        D.eval (List.ofFn (pairInput (Fin.castAdd 7 p) (Fin.natAdd 7 l))) = true) →
      D.eval (List.ofFn (pairInput (0 : Fin 14) (7 : Fin 14))) = false →
      11 ≤ ((Finset.range 14).filter fun v : ℕ => ∃ w < 13 + D.size,
        2 ≤ ((Finset.range D.size).filter fun j => w ∈ (gateAt D j).inputs).card ∧
        (D.wires (List.ofFn fun i : Fin 14 => decide (i.val = v))).getD w false = true).card →
      False) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and →           have x6 : Finset (Fin (7 : ℕ)) := {(0 : Fin (7 : ℕ)), (1 : Fin (7 : ℕ)), (3 : Fin (7 : ℕ))};           (∀ (x7 x8 : Fin (7 : ℕ)), x7 - x8 ∈ x6 → x1.eval (List.ofFn fun (x10 : Fin (14 : ℕ)) => Decidable.decide (x10 = Fin.castAdd (7 : ℕ) x7 ∨ x10 = Fin.natAdd (7 : ℕ) x8)) = Bool.true) →             (∀ (x8 : Finset (Fin (7 : ℕ))),                 have x9 : Finset (Fin (7 : ℕ)) := {x9 : Fin (7 : ℕ) | ∀ x10 ∈ x8, x10 - x9 ∉ x6};                 (∀ x10 ∉ x8, ∃ x12 ∈ x9, x10 - x12 ∈ x6) → x1.eval (List.ofFn fun (x11 : Fin ((7 : ℕ) + (7 : ℕ))) => Fin.addCases (fun (x12 : Fin (7 : ℕ)) => Decidable.decide (x12 ∈ x8)) (fun (x12 : Fin (7 : ℕ)) => Decidable.decide (x12 ∈ x9)) x11) = Bool.false) →               PEqualNP.ReadK.IsSingleRead x1 (14 : ℕ) (fun (x9 : ℕ) => Decidable.decide ((7 : ℕ) ≤ x9)) [((0 : ℕ), (7 : ℕ))] := by
  intro C hsize hao hdistinct first offsets pos neg
  let Edge (x : Fin 14 → Bool) := ∃ p l : Fin 7, p ∈ fanoLines l ∧
    x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true
  let row (e : Fin 7 × Fin 7) := pairInput (Fin.castAdd 7 e.1) (Fin.natAdd 7 e.2)
  have incidence : ∀ p l : Fin 7, p ∈ fanoLines l ↔ p - l ∈ offsets := by decide
  let st (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have len (gs : List Gate) (w : List Bool) : (gs.foldl st w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => simp only [List.foldl_cons, ih, st, List.length_append, List.length_nil, List.length_cons]; omega
  have opMono (g : Gate) (hg : g.op = .and ∨ g.op = .or) (a b : ℕ → Bool)
      (h : ∀ i, a i = true → b i = true) :
      g.op.eval (g.inputs.map a) = true → g.op.eval (g.inputs.map b) = true := by
    rcases hg with ha | ho
    · rw [ha]
      change (g.inputs.map a).all id = true → (g.inputs.map b).all id = true
      simp only [List.all_eq_true, List.mem_map, id_eq]
      intro hall z hz
      obtain ⟨i, hi, rfl⟩ := hz
      exact h _ (hall _ ⟨i, hi, rfl⟩)
    · rw [ho]
      change (g.inputs.map a).any id = true → (g.inputs.map b).any id = true
      simp only [List.any_eq_true, List.mem_map, id_eq]
      rintro ⟨_, ⟨i, hi, rfl⟩, ha⟩
      exact ⟨b i, ⟨i, hi, rfl⟩, h i ha⟩
  have monoFold (gs : List Gate) (hg : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
      (a b : List Bool) (hl : a.length = b.length)
      (h : ∀ i, a.getD i false = true → b.getD i false = true) :
      ∀ i, (gs.foldl st a).getD i false = true → (gs.foldl st b).getD i false = true := by
    induction gs generalizing a b with
    | nil => exact h
    | cons g gs ih =>
      apply ih (fun g' h' => hg _ (List.mem_cons_of_mem _ h')) (st a g) (st b g) (by simp [st, hl])
      intro i
      by_cases hi : i < a.length
      · simpa only [st, List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hl ▸ hi)] using h i
      · simp only [st, List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hi),
          List.getD_append_right _ _ _ _ (hl ▸ Nat.le_of_not_gt hi), hl]
        cases i - b.length with
        | zero => exact opMono g (hg g (.head _)) _ _ h
        | succ j => simp
  have monoGen (D : Circuit) (hD : ∀ g ∈ D.gates, g.op = .and ∨ g.op = .or)
      (x y : Fin 14 → Bool) (h : ∀ i, x i = true → y i = true) :
      D.eval (List.ofFn x) = true → D.eval (List.ofFn y) = true := by
    apply monoFold D.gates hD _ _ (by simp) _ D.output
    intro i
    by_cases hi : i < 14
    · simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some] using h ⟨i, hi⟩
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]; simp
  have monoC := monoGen C hao.1
  have spec (x : Fin 14 → Bool) : C.eval (List.ofFn x) = true ↔ Edge x := by
    constructor
    · intro hx
      by_contra hn
      let P := Finset.univ.filter fun p : Fin 7 => x (Fin.castAdd 7 p) = true
      let L := Finset.univ.filter fun l : Fin 7 => ∀ p ∈ P, p - l ∉ offsets
      let Q := Finset.univ.filter fun p : Fin 7 => ∀ l ∈ L, p - l ∉ offsets
      have sub : P ⊆ Q := by
        intro p hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun l hl => (Finset.mem_filter.mp hl).2 p hp⟩
      have closed : (Finset.univ.filter fun l : Fin 7 => ∀ p ∈ Q, p - l ∉ offsets) = L := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro he
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun p hp => he _ (sub hp)⟩
        · intro hl p hp
          exact (Finset.mem_filter.mp hp).2 l hl
      have maxQ : ∀ p ∉ Q, ∃ l ∈ L, p - l ∈ offsets := by
        intro p hp
        simpa [Q] using hp
      have hnrow := neg Q
      dsimp only at hnrow
      rw [closed] at hnrow
      specialize hnrow maxQ
      have hy := monoC x (fun i => Fin.addCases (fun p => decide (p ∈ Q)) (fun l => decide (l ∈ L)) i) ?_ hx
      · rw [hnrow] at hy
        contradiction
      · intro i
        refine Fin.addCases (m := 7) (n := 7) (motive := fun k => x k = true →
          Fin.addCases (fun p => decide (p ∈ Q)) (fun l => decide (l ∈ L)) k = true) ?_ ?_ i
        · intro p hp
          simp only [Fin.addCases_left, decide_eq_true_eq]
          exact sub (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)
        · intro l hl
          simp only [Fin.addCases_right, decide_eq_true_eq]
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun p hp hpl => hn ?_⟩
          exact ⟨p, l, (incidence _ _).mpr hpl, (Finset.mem_filter.mp hp).2, hl⟩
    · rintro ⟨p, l, he, hp, hl⟩
      apply monoC (row (p, l)) x _ (pos p l ((incidence _ _).mp he))
      intro i hi
      change decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l) = true at hi
      rcases of_decide_eq_true hi with rfl | rfl <;> assumption
  have wfold_getD_lt : ∀ (gs : List Gate) (xs : List Bool) (r : ℕ),
      r < xs.length → (gs.foldl st xs).getD r false = xs.getD r false := by
    intro gs
    induction gs with
    | nil => intro xs r _; rfl
    | cons g rest ih =>
      intro xs r hr
      simp only [List.foldl_cons]
      have hr' : r < (st xs g).length := by
        simp only [st, List.length_append, List.length_singleton]; omega
      rw [ih (st xs g) r hr']
      simp only [st, List.getD_eq_getElem?_getD, List.getElem?_append_left hr]
  have eval_and : ∀ b1 b2 : Bool, GateOp.and.eval [b1, b2] = (b1 && b2) := by decide
  have eval_or : ∀ b1 b2 : Bool, GateOp.or.eval [b1, b2] = (b1 || b2) := by decide
  have gate_inputs2 : ∀ (D : Circuit), IsAO2 14 D → ∀ j < D.size,
      (gateAt D j).inputs = [opnd D j 0, opnd D j 1] ∧
      ((gateAt D j).op = GateOp.and ∨ (gateAt D j).op = GateOp.or) ∧
      opnd D j 0 < 14 + j ∧ opnd D j 1 < 14 + j := by
    intro D hD j hj
    have hmem : gateAt D j ∈ D.gates := by
      unfold gateAt
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    have hlen : (gateAt D j).inputs.length = 2 := hD.2.2 _ hmem
    obtain ⟨a, b, hab⟩ : ∃ a b, (gateAt D j).inputs = [a, b] := by
      cases h : (gateAt D j).inputs with
      | nil => simp [h] at hlen
      | cons a l1 =>
        cases l1 with
        | nil => simp [h] at hlen
        | cons b l2 =>
          cases l2 with
          | nil => exact ⟨a, b, rfl⟩
          | cons _ _ => simp [h] at hlen
    have ha : opnd D j 0 = a := by unfold opnd; rw [hab]; rfl
    have hb : opnd D j 1 = b := by unfold opnd; rw [hab]; rfl
    refine ⟨by rw [hab, ha, hb], hD.1 _ hmem, ?_, ?_⟩
    · rw [ha]; exact hD.2.1 j hj a (by simp [hab])
    · rw [hb]; exact hD.2.1 j hj b (by simp [hab])
  have wire_input : ∀ (D : Circuit) (x : Fin 14 → Bool) (r : ℕ) (hr : r < 14),
      (D.wires (List.ofFn x)).getD r false = x ⟨r, hr⟩ := by
    intro D x r hr
    change (D.gates.foldl st (List.ofFn x)).getD r false = x ⟨r, hr⟩
    rw [wfold_getD_lt _ _ r (by simpa using hr), List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hr]
  have wire_gate : ∀ (D : Circuit), IsAO2 14 D → ∀ (x : Fin 14 → Bool) (j : ℕ) (hj : j < D.size),
      (D.wires (List.ofFn x)).getD (14 + j) false =
        (gateAt D j).op.eval
          [(D.wires (List.ofFn x)).getD (opnd D j 0) false,
           (D.wires (List.ofFn x)).getD (opnd D j 1) false] := by
    intro D hD x j hj
    have hj' : j < D.gates.length := hj
    obtain ⟨hinp, _, ha, hb⟩ := gate_inputs2 D hD j hj
    have hgj : D.gates[j] = gateAt D j := by
      unfold gateAt; rw [List.getD_eq_getElem _ _ hj']
    have hsplit : D.gates = D.gates.take j ++ gateAt D j :: D.gates.drop (j + 1) := by
      rw [← hgj, ← List.drop_eq_getElem_cons hj', List.take_append_drop]
    let pref := (D.gates.take j).foldl st (List.ofFn x)
    have hpref_len : pref.length = 14 + j := by
      dsimp only [pref]; rw [len, List.length_ofFn, List.length_take]; omega
    have hwires : D.wires (List.ofFn x) =
        (D.gates.drop (j + 1)).foldl st (st pref (gateAt D j)) := by
      change D.gates.foldl st (List.ofFn x) = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hst_len : (st pref (gateAt D j)).length = 14 + j + 1 := by
      simp only [st, List.length_append, List.length_singleton, hpref_len]
    have hpref_get : ∀ i < 14 + j, pref.getD i false = (D.wires (List.ofFn x)).getD i false := by
      intro i hi
      rw [hwires, wfold_getD_lt (D.gates.drop (j + 1)) (st pref (gateAt D j)) i (by omega)]
      simp only [st, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < pref.length)]
    conv_lhs => rw [hwires]
    rw [wfold_getD_lt (D.gates.drop (j + 1)) (st pref (gateAt D j)) (14 + j) (by omega)]
    have hstep_at : (st pref (gateAt D j)).getD (14 + j) false =
        (gateAt D j).op.eval ((gateAt D j).inputs.map fun i => pref.getD i false) := by
      simp only [st, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), hpref_len]; simp
    rw [hstep_at, hinp]
    simp only [List.map_cons, List.map_nil, hpref_get _ ha, hpref_get _ hb]
  let W (x : Fin 14 → Bool) (w : ℕ) := (C.wires (List.ofFn x)).getD w false
  let V (gs : List Gate) (r : Option ℕ) (x : Fin 14 → Bool) :=
    r.elim false (fun w => (Circuit.mk gs w).eval (List.ofFn x))
  let OK (gs : List Gate) (r : Option ℕ) := ∀ k, r = some k → k < 14 + gs.length
  let Relation (y : (Fin 14 → Bool) → Bool) (w : ℕ) (strong : Prop) :=
    (∀ x, y x = true → W x w = true) ∧
    (∀ x, W x 14 = false ∨ strong → y x = W x w)
  let Prefix (j : ℕ) (gs : List Gate) (r : ℕ → Option ℕ) :=
    Monotone2 ⟨gs, 0⟩ ∧ gs.length + 1 ≤ j ∧
    ∀ w < 14 + j, OK gs (r w) ∧
      Relation (V gs (r w)) w (gs.length + 1 = j ∧ (r w).isSome = true)
  have build (j : ℕ) (hj : 1 ≤ j) (hmax : j ≤ C.size) :
      ∃ gs r, Prefix j gs r := by
    induction j with
    | zero => omega
    | succ j ih =>
      by_cases hzero : j = 0
      · subst j
        refine ⟨[], fun w => if w < 14 then some w else none, ?_, by decide, ?_⟩
        · intro g hg; cases hg
        · intro w hw
          by_cases h : w < 14
          · simp only [h, ite_true]
            refine ⟨fun k hk => ?_, ?_, ?_⟩
            · have := Option.some.inj hk
              simpa [← this] using h
            · intro x hx
              change ((Circuit.mk [] 0).wires _).getD w false = true at hx
              change (C.wires _).getD w false = true
              rw [wire_input _ _ _ h] at hx ⊢
              exact hx
            · intro x _
              change ((Circuit.mk [] 0).wires _).getD w false = (C.wires _).getD w false
              rw [wire_input _ _ _ h, wire_input _ _ _ h]
          · have hw' : w = 14 := by omega
            subst w
            simp only [Nat.lt_irrefl, ite_false]
            refine ⟨?_, ?_, ?_⟩
            · intro k hk; cases hk
            · intro x hx; cases hx
            intro x hx
            rcases hx with h | ⟨_, h⟩
            · exact h.symm
            · cases h
      · obtain ⟨gs, r, hmon, hlen, hinv⟩ := ih (by omega) (by omega)
        have hjC : j < C.size := by omega
        let a := opnd C j 0
        let b := opnd C j 1
        let op := (gateAt C j).op
        obtain ⟨_, hop, ha, hb⟩ := gate_inputs2 C hao j hjC
        have wa := hinv a ha
        have wb := hinv b hb
        have step (x) : W x (14 + j) = op.eval [W x a, W x b] := wire_gate C hao x j hjC
        let val := fun x => op.eval [V gs (r a) x, V gs (r b) x]
        have sem : Relation val (14 + j)
            (gs.length + 1 = j ∧ (r a).isSome = true ∧ (r b).isSome = true) := by
          constructor
          · intro x hx
            rw [step]
            have hcomp (s t u v : Bool) (hs : s = true → u = true) (ht : t = true → v = true) :
                op.eval [s, t] = true → op.eval [u, v] = true := by
              change op = .and ∨ op = .or at hop
              rcases hop with h | h <;> rw [h] <;> revert hs ht <;> clear_value op <;> revert s t u v <;> decide
            exact hcomp _ _ _ _ (wa.2.1 x) (wb.2.1 x) hx
          · intro x hx
            rw [step]
            dsimp only [val]
            rw [wa.2.2 x (hx.imp_right fun h => ⟨h.1, h.2.1⟩),
                wb.2.2 x (hx.imp_right fun h => ⟨h.1, h.2.2⟩)]
        have extend (out : List Gate) (nr : Option ℕ) (hm : Monotone2 ⟨out, 0⟩)
            (hlo : gs.length ≤ out.length) (hhi : out.length ≤ gs.length + 1)
            (hok : OK out nr)
            (hold : ∀ w < 14 + j, ∀ x, V out (r w) x = V gs (r w) x)
            (hn : ∀ x, V out nr x = val x)
            (hstrong : out.length + 1 = j + 1 → nr.isSome = true →
              (r a).isSome = true ∧ (r b).isSome = true) :
            ∃ out rr, Prefix (j + 1) out rr := by
          refine ⟨out, fun w => if w = 14 + j then nr else r w, hm, by omega, ?_⟩
          intro w hw
          by_cases he : w = 14 + j
          · subst w
            simp only [ite_true]
            refine ⟨hok, fun x h => sem.1 x ((hn x) ▸ h), ?_⟩
            intro x h
            rw [hn]
            exact sem.2 x (h.imp_right fun h => ⟨by omega, hstrong h.1 h.2⟩)
          · simp only [he, ite_false]
            have hw' : w < 14 + j := by omega
            obtain ⟨ok, le, eq⟩ := hinv w hw'
            refine ⟨fun k hk => by have := ok k hk; omega, fun x h => le x ((hold w hw' x) ▸ h), ?_⟩
            intro x h
            rw [hold w hw' x]
            exact eq x (h.imp_right fun h => ⟨by omega, h.2⟩)
        have skip (nr : Option ℕ) (hok : OK gs nr) (he : ∀ x, V gs nr x = val x) :
            ∃ out rr, Prefix (j + 1) out rr :=
          extend gs nr hmon (by omega) (by omega) hok (fun _ _ _ => rfl) he (by omega)
        have okNone : OK gs none := fun k hk => by cases hk
        cases hA : r a with
        | none =>
          rcases hop with h | h
          · apply skip none okNone
            intro x; simp [val, op, h, hA, V, eval_and]
          · apply skip (r b) wb.1
            intro x; simp [val, op, h, hA, V, eval_or]
        | some u =>
          cases hB : r b with
          | none =>
            rcases hop with h | h
            · apply skip none okNone
              intro x; simp [val, op, h, hB, V, eval_and]
            · apply skip (r a) wa.1
              intro x; simp [val, op, h, hB, V, eval_or]
          | some v =>
            let g : Gate := ⟨op, [u, v]⟩
            let out := gs ++ [g]
            have hout_len : out.length = gs.length + 1 := by simp [out]
            have appended (x : Fin 14 → Bool) :
                (Circuit.mk out 0).wires (List.ofFn x) =
                st ((Circuit.mk gs 0).wires (List.ofFn x)) g := by
              change (gs ++ [g]).foldl st _ = _
              rw [List.foldl_append]; rfl
            have wl (x : Fin 14 → Bool) :
                ((Circuit.mk gs 0).wires (List.ofFn x)).length = 14 + gs.length := by
              change (gs.foldl st _).length = _
              rw [len, List.length_ofFn]
            apply extend out (some (14 + gs.length)) ?_ (by omega) (by omega) ?_ ?_ ?_ ?_
            · intro q hq
              change q ∈ gs ++ [g] at hq
              rcases List.mem_append.mp hq with h | h
              · exact hmon _ h
              · have eq : q = g := List.mem_singleton.mp h
                subst q
                exact ⟨by simpa [g, op] using hop, by simp [g]⟩
            · intro k hk
              have := Option.some.inj hk
              omega
            · intro w hw x
              cases hr : r w with
              | none => rfl
              | some k =>
                have hk := (hinv w hw).1 k hr
                change ((Circuit.mk out 0).wires _).getD k false = ((Circuit.mk gs 0).wires _).getD k false
                rw [appended]
                exact List.getD_append _ _ _ _ (by rw [wl]; exact hk)
            · intro x
              change ((Circuit.mk out 0).wires _).getD (14 + gs.length) false = _
              rw [appended]
              dsimp only [st]
              rw [List.getD_append_right _ _ _ _ (by rw [wl]), wl, Nat.sub_self]
              simp only [val, hA, hB]; rfl
            · simp [hA, hB]
  have hpos : 0 < C.size := by
    by_contra! h
    have hg : C.gates = [] := List.eq_nil_of_length_eq_zero (show C.size = 0 by omega)
    unfold gateAt at first
    rw [hg] at first
    cases first
  have hout : C.output < 14 + C.size := by
    by_contra! h
    have ht := pos 0 0 (by decide)
    change (C.gates.foldl st _).getD C.output false = true at ht
    rw [List.getD_eq_default _ _ (by rw [len, List.length_ofFn]; exact h)] at ht
    contradiction
  obtain ⟨gs, r, hmon, hlen, hrep⟩ := build C.size hpos (by rfl)
  obtain ⟨_, upper, agree⟩ := hrep C.output hout
  obtain ⟨_, _, ha, hb⟩ := gate_inputs2 C hao 0 hpos
  let a : Fin 14 := ⟨opnd C 0 0, ha⟩
  let b : Fin 14 := ⟨opnd C 0 1, hb⟩
  have hab : a ≠ b := fun h => hdistinct 0 hpos (congrArg Fin.val h)
  have value14 (x : Fin 14 → Bool) : W x 14 = (x a && x b) := by
    change W x (14 + 0) = _
    rw [show W x (14 + 0) = _ from wire_gate C hao x 0 hpos, first, eval_and,
      wire_input C _ _ ha, wire_input C _ _ hb]
  let keep := (incidences fanoLines).filter fun e => row e a = false ∨ row e b = false
  have cardinal : ∀ i j : Fin 14, i ≠ j → 20 ≤ ((incidences fanoLines).filter
      fun e => row e i = false ∨ row e j = false).card := by decide +kernel
  have hk : 20 ≤ keep.card := cardinal a b hab
  have hits (e : Fin 7 × Fin 7) (he : e ∈ keep) : V gs (r C.output) (row e) = true := by
    obtain ⟨hedge, hskip⟩ := Finset.mem_filter.mp he
    have h0 : W (row e) 14 = false := by
      rw [value14]
      rcases hskip with h | h <;> simp [h]
    rw [agree _ (Or.inl h0)]
    exact pos _ _ ((incidence _ _).mp (Finset.mem_filter.mp hedge).2)
  exfalso
  cases hr : r C.output with
  | none =>
    have hne : keep.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨e, he⟩ := hne
    have h := hits e he
    rw [hr] at h
    cases h
  | some out =>
    let D0 : Circuit := ⟨gs, out⟩
    have hd0 : Monotone2 D0 := hmon
    have hD0_op : ∀ g ∈ D0.gates, g.op = .and ∨ g.op = .or := fun g hg => by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hd0 g hg).1
    have eqD0 (x) : D0.eval (List.ofFn x) = V gs (r C.output) x := by rw [hr]; rfl
    have sound0 (x : Fin 14 → Bool) (hx : D0.eval (List.ofFn x) = true) : Edge x :=
      (spec x).mp (upper _ ((eqD0 _) ▸ hx))
    by_cases h26 : gs.length = 26
    · have same : gs.length + 1 = C.size := by omega
      have need' : 27 ≤ gs.length := full D0 hd0 (fun x => by
        rw [eqD0, agree _ (Or.inr ⟨same, by simp [hr]⟩)]
        exact spec x)
      omega
    have hD0_size : D0.size ≤ 25 := by change gs.length ≤ 25; omega
    have hmonoD0 := monoGen D0 hD0_op
    -- Either D0 accepts all 21 Fano edges (contradicting full), or it misses one edge e0.
    have hall_or : (∀ p l : Fin 7, p ∈ fanoLines l → D0.eval (List.ofFn (row (p, l))) = true) ∨
        ∃ p0 l0 : Fin 7, p0 ∈ fanoLines l0 ∧ D0.eval (List.ofFn (row (p0, l0))) = false ∧
          ∀ p l : Fin 7, p ∈ fanoLines l → (p ≠ p0 ∨ l ≠ l0) →
            D0.eval (List.ofFn (row (p, l))) = true := by
      by_cases hall : ∀ e ∈ incidences fanoLines, D0.eval (List.ofFn (row e)) = true
      · left
        intro p l hpl
        exact hall (p, l) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩)
      · right
        push Not at hall
        obtain ⟨⟨p0, l0⟩, he0_mem, he0_f⟩ := hall
        have hp0l0 : p0 ∈ fanoLines l0 := (Finset.mem_filter.mp he0_mem).2
        have hfalse : D0.eval (List.ofFn (row (p0, l0))) = false := Bool.eq_false_iff.mpr he0_f
        have hnotkeep : (p0, l0) ∉ keep := fun hkmem => by
          have := (eqD0 _).trans (hits (p0, l0) hkmem)
          rw [this] at hfalse
          exact Bool.false_ne_true hfalse.symm
        have htrue0 : row (p0, l0) a = true ∧ row (p0, l0) b = true := by
          by_contra hcon
          apply hnotkeep
          refine Finset.mem_filter.mpr ⟨he0_mem, ?_⟩
          cases ha' : row (p0, l0) a <;> cases hb' : row (p0, l0) b <;> simp_all
        refine ⟨p0, l0, hp0l0, hfalse, fun p l hpl hne => ?_⟩
        rw [eqD0]
        apply hits (p, l)
        refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩, ?_⟩
        have row_unique : ∀ (e1 e2 : Fin 7 × Fin 7), e1 ≠ e2 →
            row e1 a = true → row e1 b = true → row e2 a = true → row e2 b = true → False := by
          intro e1 e2 he12 h1a h1b h2a h2b
          dsimp only [row, pairInput] at h1a h1b h2a h2b
          simp only [decide_eq_true_eq] at h1a h1b h2a h2b
          have hcn : ∀ (p l : Fin 7), Fin.castAdd 7 p ≠ Fin.natAdd 7 l := fun p l h => by
            have hv := congrArg Fin.val h; simp at hv; omega
          have hci : ∀ (p q : Fin 7), Fin.castAdd 7 p = Fin.castAdd 7 q → p = q := fun p q h =>
            Fin.ext (by simpa using congrArg Fin.val h)
          have hni : ∀ (p q : Fin 7), Fin.natAdd 7 p = Fin.natAdd 7 q → p = q := fun p q h =>
            Fin.ext (by have hv := congrArg Fin.val h; simp at hv; exact hv)
          apply he12
          rcases h1a with h1a | h1a <;> rcases h1b with h1b | h1b
          · exact absurd (h1a.trans h1b.symm) hab
          · rcases h2a with h2a | h2a
            · rcases h2b with h2b | h2b
              · exact absurd (h2a.trans h2b.symm) hab
              · exact Prod.ext (hci _ _ (h1a.symm.trans h2a)) (hni _ _ (h1b.symm.trans h2b))
            · exact absurd (h1a.symm.trans h2a) (hcn _ _)
          · rcases h2a with h2a | h2a
            · exact absurd (h2a.symm.trans h1a) (hcn _ _)
            · rcases h2b with h2b | h2b
              · exact Prod.ext (hci _ _ (h1b.symm.trans h2b)) (hni _ _ (h1a.symm.trans h2a))
              · exact absurd (h2a.trans h2b.symm) hab
          · exact absurd (h1a.trans h1b.symm) hab
        by_contra hno
        have htrue1 : row (p, l) a = true ∧ row (p, l) b = true := by
          cases ha' : row (p, l) a <;> cases hb' : row (p, l) b <;> simp_all
        exact row_unique (p0, l0) (p, l) (fun h => by
          rcases hne with h' | h'
          · exact h' (congrArg Prod.fst h).symm
          · exact h' (congrArg Prod.snd h).symm) htrue0.1 htrue0.2 htrue1.1 htrue1.2
    rcases hall_or with hall | ⟨p0, l0, hp0l0, hmiss, hhit⟩
    · have need : 27 ≤ D0.size := full D0 hd0 (fun x => by
        constructor
        · exact sound0 x
        · rintro ⟨p, l, hpl, hp, hl⟩
          apply hmonoD0 (row (p, l)) x _ (hall p l hpl)
          intro i hi
          change decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l) = true at hi
          rcases of_decide_eq_true hi with rfl | rfl <;> assumption)
      omega
    -- Permute inputs so the missing edge (p0, l0) becomes (0, 0).
    let s1P : Fin 7 → Fin 7 := ![1, 0, 2, 3, 6, 5, 4]
    let s1L : Fin 7 → Fin 7 := ![0, 6, 2, 3, 5, 4, 1]
    let s3P : Fin 7 → Fin 7 := ![1, 3, 2, 0, 5, 6, 4]
    let s3L : Fin 7 → Fin 7 := ![0, 2, 6, 4, 5, 3, 1]
    let sigP (p0 l0 : Fin 7) : Fin 7 → Fin 7 :=
      if p0 - l0 = 0 then fun p => p - l0
      else if p0 - l0 = 1 then fun p => s1P (p - l0)
      else fun p => s3P (p - l0)
    let sigL (p0 l0 : Fin 7) : Fin 7 → Fin 7 :=
      if p0 - l0 = 0 then fun l => l - l0
      else if p0 - l0 = 1 then fun l => s1L (l - l0)
      else fun l => s3L (l - l0)
    have hsig_ok : ∀ p0 l0 : Fin 7, p0 ∈ fanoLines l0 →
        sigP p0 l0 p0 = 0 ∧ sigL p0 l0 l0 = 0 ∧
        (∀ a b, sigP p0 l0 a = sigP p0 l0 b → a = b) ∧
        (∀ a b, sigL p0 l0 a = sigL p0 l0 b → a = b) ∧
        (∀ p l, sigP p0 l0 p ∈ fanoLines (sigL p0 l0 l) ↔ p ∈ fanoLines l) := by
      decide +kernel
    obtain ⟨hsP0, hsL0, hsPinj, hsLinj, hsInc⟩ := hsig_ok p0 l0 hp0l0
    let σ : Fin 14 → Fin 14 := fun i =>
      Fin.addCases (m := 7) (n := 7) (motive := fun _ => Fin 14)
        (fun p => Fin.castAdd 7 (sigP p0 l0 p))
        (fun l => Fin.natAdd 7 (sigL p0 l0 l)) i
    have hσ_inj : Function.Injective σ := by
      intro x y hxy
      refine Fin.addCases (m := 7) (n := 7) (motive := fun x => σ x = σ y → x = y) ?_ ?_ x hxy
      · intro px
        refine Fin.addCases (m := 7) (n := 7) (motive := fun y => σ (Fin.castAdd 7 px) = σ y → Fin.castAdd 7 px = y) ?_ ?_ y
        · intro py h
          simp only [σ, Fin.addCases_left] at h
          have hp : sigP p0 l0 px = sigP p0 l0 py := Fin.ext (by simpa using congrArg Fin.val h)
          rw [hsPinj px py hp]
        · intro ly h
          simp only [σ, Fin.addCases_left, Fin.addCases_right] at h
          have hv := congrArg Fin.val h
          simp at hv; omega
      · intro lx
        refine Fin.addCases (m := 7) (n := 7) (motive := fun y => σ (Fin.natAdd 7 lx) = σ y → Fin.natAdd 7 lx = y) ?_ ?_ y
        · intro py h
          simp only [σ, Fin.addCases_right, Fin.addCases_left] at h
          have hv := congrArg Fin.val h
          simp at hv; omega
        · intro ly h
          simp only [σ, Fin.addCases_right] at h
          have hl : sigL p0 l0 lx = sigL p0 l0 ly := Fin.ext (by have := congrArg Fin.val h; simp at this; exact this)
          rw [hsLinj lx ly hl]
    have hσ_surj : Function.Surjective σ := Finite.injective_iff_surjective.mp hσ_inj
    let mapWire (w : ℕ) : ℕ := if h : w < 14 then (σ ⟨w, h⟩).val else w
    let D1 : Circuit := ⟨D0.gates.map fun g => ⟨g.op, g.inputs.map mapWire⟩, D0.output⟩
    have hd1 : Monotone2 D1 := by
      intro g hg
      simp only [D1, List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      have hm := hd0 g0 hg0
      exact ⟨hm.1, by simp [hm.2]⟩
    have hD1_size : D1.size ≤ 25 := by
      change (D0.gates.map _).length ≤ 25
      rw [List.length_map]
      exact hD0_size
    have hD1_eval (x : Fin 14 → Bool) :
        D1.eval (List.ofFn x) = D0.eval (List.ofFn (fun i => x (σ i))) := by
      have h14 : 14 ≤ D0.output := by
        by_contra! hlt
        have ht : D0.eval (List.ofFn (fun i : Fin 14 => decide (i = ⟨D0.output, hlt⟩))) = true := by
          change (D0.gates.foldl st (List.ofFn _)).getD D0.output false = true
          rw [wfold_getD_lt _ _ D0.output (by simpa using hlt), List.getD_eq_getElem?_getD,
            List.getElem?_ofFn]
          simp [hlt]
        obtain ⟨p, l, _, hp, hl⟩ := sound0 _ ht
        simp only [decide_eq_true_eq] at hp hl
        have hv1 := congrArg Fin.val hp
        have hv2 := congrArg Fin.val hl
        simp at hv1 hv2
        omega
      have hinv : ∀ (gs : List Gate) (w1 w2 : List Bool),
          14 ≤ w1.length → w1.length = w2.length →
          (∀ i, w2.getD i false = w1.getD (mapWire i) false) →
          ∀ i, (gs.foldl st w2).getD i false =
            ((gs.map fun g => ⟨g.op, g.inputs.map mapWire⟩).foldl st w1).getD (mapWire i) false := by
        intro gs
        induction gs with
        | nil =>
          intro w1 w2 _ _ h i
          exact h i
        | cons g gs ih =>
          intro w1 w2 hw1 hlen h i
          simp only [List.map_cons, List.foldl_cons]
          have hbit : g.op.eval (g.inputs.map fun k => w2.getD k false) =
              g.op.eval ((g.inputs.map mapWire).map fun k => w1.getD k false) := by
            congr 1
            rw [List.map_map]
            apply List.map_congr_left
            intro k _
            exact h k
          apply ih (st w1 ⟨g.op, g.inputs.map mapWire⟩) (st w2 g)
          · simp only [st, List.length_append, List.length_singleton]; omega
          · simp only [st, List.length_append, List.length_singleton, hlen]
          · intro k
            by_cases hk : k < w2.length
            · have hk1 : mapWire k < w1.length := by
                dsimp only [mapWire]
                split_ifs with hk14
                · exact lt_of_lt_of_le (σ ⟨k, hk14⟩).isLt hw1
                · omega
              simp only [st, List.getD_append _ _ _ _ hk, List.getD_append _ _ _ _ hk1]
              exact h k
            · have hk14 : ¬ k < 14 := by omega
              have hmk : mapWire k = k := by simp [mapWire, hk14]
              rw [hmk]
              by_cases hkeq : k = w2.length
              · subst hkeq
                simp only [st, List.getD_append_right _ _ _ _ (Nat.le_refl _),
                  List.getD_append_right _ _ _ _ (by omega : w1.length ≤ w2.length), hlen, Nat.sub_self]
                exact hbit
              · have hgt : w2.length < k := by omega
                have hgt1 : w1.length < k := by omega
                simp only [st, List.getD_eq_getElem?_getD]
                rw [List.getElem?_eq_none (by simp [List.length_append]; omega),
                    List.getElem?_eq_none (by simp [List.length_append]; omega)]
      have hm_out : mapWire D0.output = D0.output := by
        simp [mapWire, show ¬ D0.output < 14 by omega]
      change ((D0.gates.map fun g => ⟨g.op, g.inputs.map mapWire⟩).foldl st (List.ofFn x)).getD D0.output false =
        (D0.gates.foldl st (List.ofFn (fun i => x (σ i)))).getD D0.output false
      conv_lhs => rw [← hm_out]
      symm
      apply hinv D0.gates (List.ofFn x) (List.ofFn (fun i => x (σ i))) (by simp) (by simp) _ D0.output
      intro i
      by_cases hi : i < 14
      · have hmw : mapWire i = (σ ⟨i, hi⟩).val := by simp [mapWire, hi]
        rw [hmw, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_ofFn, List.getElem?_ofFn]
        simp [hi, (σ ⟨i, hi⟩).isLt]
      · have hmw : mapWire i = i := by simp [mapWire, hi]
        rw [hmw]
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
    have hD1_upper (x : Fin 14 → Bool) : D1.eval (List.ofFn x) = true → Edge x := by
      intro hx
      rw [hD1_eval] at hx
      obtain ⟨p, l, hpl, hp, hl⟩ := sound0 _ hx
      dsimp only at hp hl
      exact ⟨sigP p0 l0 p, sigL p0 l0 l, (hsInc p l).mpr hpl,
        by simpa only [σ, Fin.addCases_left] using hp,
        by simpa only [σ, Fin.addCases_right] using hl⟩
    have hD1_miss : D1.eval (List.ofFn (pairInput (0 : Fin 14) (7 : Fin 14))) = false := by
      rw [hD1_eval]
      have heq : (fun i : Fin 14 => pairInput (0 : Fin 14) (7 : Fin 14) (σ i)) = row (p0, l0) := by
        funext i
        dsimp only [pairInput, row]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · rintro (h | h)
          · left
            apply hσ_inj
            rw [h]
            simp only [σ, Fin.addCases_left, hsP0]
            rfl
          · right
            apply hσ_inj
            rw [h]
            simp only [σ, Fin.addCases_right, hsL0]
            rfl
        · rintro (rfl | rfl)
          · left; simp only [σ, Fin.addCases_left, hsP0]; rfl
          · right; simp only [σ, Fin.addCases_right, hsL0]; rfl
      rw [heq]
      exact hmiss
    have hD1_hit : ∀ p l : Fin 7, p ∈ fanoLines l → (p ≠ 0 ∨ l ≠ 0) →
        D1.eval (List.ofFn (pairInput (Fin.castAdd 7 p) (Fin.natAdd 7 l))) = true := by
      intro p l hpl hne
      rw [hD1_eval]
      obtain ⟨p', hp'⟩ := (Finite.injective_iff_surjective.mp hsPinj) p
      obtain ⟨l', hl'⟩ := (Finite.injective_iff_surjective.mp hsLinj) l
      have hp'l' : p' ∈ fanoLines l' := (hsInc p' l').mp (by rw [hp', hl']; exact hpl)
      have hne' : p' ≠ p0 ∨ l' ≠ l0 := by
        rcases hne with h | h
        · left; intro e; apply h; rw [← hp', e, hsP0]
        · right; intro e; apply h; rw [← hl', e, hsL0]
      have heq : (fun i : Fin 14 => pairInput (Fin.castAdd 7 p) (Fin.natAdd 7 l) (σ i)) =
          row (p', l') := by
        funext i
        dsimp only [pairInput, row]
        apply Bool.eq_iff_iff.mpr
        simp only [decide_eq_true_eq]
        constructor
        · rintro (h | h)
          · left
            apply hσ_inj
            rw [h]
            simp only [σ, Fin.addCases_left, hp']
          · right
            apply hσ_inj
            rw [h]
            simp only [σ, Fin.addCases_right, hl']
        · rintro (rfl | rfl)
          · left; simp only [σ, Fin.addCases_left, hp']
          · right; simp only [σ, Fin.addCases_right, hl']
      rw [heq]
      exact hhit p' l' hp'l' hne'
    -- Normalize D1 into a strict live binary DAG (adapted from L_meta_971 Block A).
    let gop (t a b : Bool) : Bool := if t then a && b else a || b
    let tag (D : List (Bool × ℕ × ℕ)) (j : ℕ) : Bool := (D.getD j (false, 0, 0)).1
    let opA (D : List (Bool × ℕ × ℕ)) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.1
    let opB (D : List (Bool × ℕ × ℕ)) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.2
    let dwstep (w : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
      w ++ [gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]
    let dwl (D : List (Bool × ℕ × ℕ)) (w : List Bool) : List Bool := D.foldl dwstep w
    let dval (D : List (Bool × ℕ × ℕ)) (x : Fin 14 → Bool) (w : ℕ) : Bool :=
      (dwl D (List.ofFn x)).getD w false
    let dStrict (D : List (Bool × ℕ × ℕ)) : Prop :=
      ∀ j, j < D.length → opA D j < 14 + j ∧ opB D j < 14 + j ∧ opA D j ≠ opB D j
    let dReaders (D : List (Bool × ℕ × ℕ)) (w : ℕ) : Finset ℕ :=
      (Finset.range D.length).filter (fun j => opA D j = w ∨ opB D j = w)
    let dFanout (D : List (Bool × ℕ × ℕ)) (w : ℕ) : ℕ := (dReaders D w).card
    let dLive (D : List (Bool × ℕ × ℕ)) : Prop := ∀ w, w + 1 < 14 + D.length → 1 ≤ dFanout D w
    let dOutW (D : List (Bool × ℕ × ℕ)) : ℕ := 14 + D.length - 1
    have dwl_length (D : List (Bool × ℕ × ℕ)) : ∀ w : List Bool, (dwl D w).length = w.length + D.length := by
      induction D with
      | nil => intro w; simp [dwl]
      | cons g D ih => intro w; change (dwl D (dwstep w g)).length = _; rw [ih]; simp [dwstep]; omega
    have dwstep_getD_lt (w : List Bool) (g : Bool × ℕ × ℕ) (i : ℕ) (h : i < w.length) :
        (dwstep w g).getD i false = w.getD i false := by
      simp [dwstep, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    have dwl_getD_lt (D : List (Bool × ℕ × ℕ)) : ∀ (w : List Bool) (i : ℕ), i < w.length →
        (dwl D w).getD i false = w.getD i false := by
      induction D with
      | nil => intro w i _; rfl
      | cons g D ih =>
        intro w i h
        change (dwl D (dwstep w g)).getD i false = _
        rw [ih _ _ (by simp [dwstep]; omega), dwstep_getD_lt _ _ _ h]
    have dwl_append (D E : List (Bool × ℕ × ℕ)) (w : List Bool) :
        dwl (D ++ E) w = dwl E (dwl D w) := by
      simp [dwl, List.foldl_append]
    have dval_input (D : List (Bool × ℕ × ℕ)) (x : Fin 14 → Bool) (i : ℕ) (h : i < 14) :
        dval D x i = x ⟨i, h⟩ := by
      dsimp only [dval]
      rw [dwl_getD_lt _ _ _ (by simp [h]), List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [h]
    have dval_ge (D : List (Bool × ℕ × ℕ)) (x : Fin 14 → Bool) (w : ℕ) (h : 14 + D.length ≤ w) :
        dval D x w = false := by
      dsimp only [dval]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [dwl_length, List.length_ofFn]; exact h)]
      rfl
    have dval_take (D : List (Bool × ℕ × ℕ)) (x : Fin 14 → Bool) (k w : ℕ) (hw : w < 14 + k)
        (hk : k ≤ D.length) : dval (D.take k) x w = dval D x w := by
      dsimp only [dval]
      have hsplit : D = D.take k ++ D.drop k := by simp
      have hlen' : (dwl (D.take k) (List.ofFn x)).length = 14 + k := by
        rw [dwl_length, List.length_ofFn, List.length_take]; omega
      conv_rhs => rw [hsplit, dwl_append]
      rw [dwl_getD_lt (D.drop k) _ w (by rw [hlen']; exact hw)]
    have dval_gate {D : List (Bool × ℕ × ℕ)} (hS : dStrict D) (x : Fin 14 → Bool) (j : ℕ)
        (hj : j < D.length) :
        dval D x (14 + j) = gop (tag D j) (dval D x (opA D j)) (dval D x (opB D j)) := by
      obtain ⟨ha, hb, -⟩ := hS j hj
      have hsplit : D = D.take j ++ D[j] :: D.drop (j + 1) := by simp
      have hlen' : (dwl (D.take j) (List.ofFn x)).length = 14 + j := by
        rw [dwl_length, List.length_ofFn, List.length_take]; omega
      dsimp only [dval]
      conv_lhs => rw [hsplit, dwl_append]
      change (dwl (D.drop (j + 1)) (dwstep (dwl (D.take j) (List.ofFn x)) D[j])).getD (14 + j) false = _
      rw [dwl_getD_lt _ _ _ (by dsimp only [dwstep]; rw [List.length_append, List.length_singleton, hlen']; omega), ← hlen']
      have hlast : (dwstep (dwl (D.take j) (List.ofFn x)) D[j]).getD
          (dwl (D.take j) (List.ofFn x)).length false =
          gop D[j].1 ((dwl (D.take j) (List.ofFn x)).getD D[j].2.1 false)
            ((dwl (D.take j) (List.ofFn x)).getD D[j].2.2 false) := by
        simp [dwstep, List.getD_eq_getElem?_getD]
      rw [hlast]
      have ht : tag D j = D[j].1 := by simp [tag, List.getD_eq_getElem?_getD, hj]
      have hoA : opA D j = D[j].2.1 := by simp [opA, List.getD_eq_getElem?_getD, hj]
      have hoB : opB D j = D[j].2.2 := by simp [opB, List.getD_eq_getElem?_getD, hj]
      rw [ht, hoA, hoB]
      congr 1
      · rw [← hoA]; exact dval_take D x j (opA D j) ha hj.le
      · rw [← hoB]; exact dval_take D x j (opB D j) hb hj.le
    have dval_unique {D : List (Bool × ℕ × ℕ)} (hS : dStrict D) (x : Fin 14 → Bool) (f : ℕ → Bool)
        (hin : ∀ i (h : i < 14), f i = x ⟨i, h⟩)
        (hg : ∀ j, j < D.length → f (14 + j) = gop (tag D j) (f (opA D j)) (f (opB D j))) :
        ∀ w, w < 14 + D.length → dval D x w = f w := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw
        by_cases hn : w < 14
        · rw [dval_input D x w hn, hin w hn]
        · obtain ⟨j, rfl⟩ : ∃ j, w = 14 + j := ⟨w - 14, by omega⟩
          have hj : j < D.length := by omega
          obtain ⟨ha, hb, -⟩ := hS j hj
          rw [dval_gate hS x j hj, hg j hj, ih _ ha (by omega), ih _ hb (by omega)]
    let refVal (W : List Bool) (v : Bool ⊕ ℕ) : Bool :=
      Sum.casesOn v id (fun k => W.getD k false)
    let na_look (m : List (Bool ⊕ ℕ)) (i : ℕ) : Bool ⊕ ℕ := m.getD i (Sum.inl false)
    let na_comb (t : Bool) (x y : Bool ⊕ ℕ) : (Bool ⊕ ℕ) ⊕ (ℕ × ℕ) :=
      Sum.casesOn x
        (fun a => Sum.inl (if a = t then y else Sum.inl a))
        (fun i => Sum.casesOn y
          (fun b => Sum.inl (if b = t then Sum.inr i else Sum.inl b))
          (fun j => if i = j then Sum.inl (Sum.inr i) else Sum.inr (i, j)))
    let na_isAnd (op : GateOp) : Bool :=
      GateOp.casesOn op true false false (fun _ => false) false
    let na_step (st_ : List (Bool ⊕ ℕ) × List (Bool × ℕ × ℕ)) (g : Gate) :
        List (Bool ⊕ ℕ) × List (Bool × ℕ × ℕ) :=
      List.casesOn g.inputs
        (st_.1 ++ [Sum.inl (na_isAnd g.op)], st_.2)
        (fun a' tail => List.casesOn tail
          (st_.1 ++ [na_look st_.1 a'], st_.2)
          (fun b' _ => Sum.casesOn (na_comb (na_isAnd g.op) (na_look st_.1 a') (na_look st_.1 b'))
            (fun r' => (st_.1 ++ [r'], st_.2))
            (fun p => (st_.1 ++ [Sum.inr (14 + st_.2.length)], st_.2 ++ [(na_isAnd g.op, p.1, p.2)]))))
    let na_ok (B : ℕ) (v : Bool ⊕ ℕ) : Prop :=
      Sum.casesOn v (fun _ => True) (fun k => k < B)
    let na_Good (st_ : List (Bool ⊕ ℕ) × List (Bool × ℕ × ℕ)) : Prop :=
      dStrict st_.2 ∧ ∀ r' ∈ st_.1, na_ok (14 + st_.2.length) r'
    have na_ok_mono {B B' : ℕ} (h : B ≤ B') (r' : Bool ⊕ ℕ) (hr : na_ok B r') : na_ok B' r' := by
      rcases r' with b' | k; exact trivial; exact lt_of_lt_of_le hr h
    have na_look_val (W : List Bool) (m : List (Bool ⊕ ℕ)) (i : ℕ) :
        refVal W (na_look m i) = (m.map (refVal W)).getD i false := by
      simp only [na_look, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases m[i]? <;> rfl
    have na_look_ok (B : ℕ) (m : List (Bool ⊕ ℕ)) (hm : ∀ r' ∈ m, na_ok B r') (i : ℕ) :
        na_ok B (na_look m i) := by
      simp only [na_look, List.getD_eq_getElem?_getD]
      rcases h : m[i]? with _ | r'
      · trivial
      · exact hm r' (List.mem_of_getElem? h)
    have na_comb_inl (t : Bool) (W : List Bool) (a' b' r' : Bool ⊕ ℕ)
        (h : na_comb t a' b' = Sum.inl r') :
        refVal W r' = gop t (refVal W a') (refVal W b') := by
      rcases a' with a' | i
      · dsimp only [na_comb] at h; simp only [Sum.inl.injEq] at h; subst h; cases t <;> cases a' <;> simp [refVal, gop]
      · rcases b' with b' | j
        · dsimp only [na_comb] at h; simp only [Sum.inl.injEq] at h; subst h; cases t <;> cases b' <;> simp [refVal, gop]
        · dsimp only [na_comb] at h; split_ifs at h with hij; simp only [Sum.inl.injEq] at h
          subst h; subst hij; cases t <;> simp [refVal, gop]
    have na_comb_ok (B : ℕ) (t : Bool) (a' b' r' : Bool ⊕ ℕ) (ha' : na_ok B a') (hb' : na_ok B b')
        (h : na_comb t a' b' = Sum.inl r') : na_ok B r' := by
      rcases a' with a' | i
      · dsimp only [na_comb] at h; simp only [Sum.inl.injEq] at h; subst h; split_ifs; exact hb'; trivial
      · rcases b' with b' | j
        · dsimp only [na_comb] at h; simp only [Sum.inl.injEq] at h; subst h; split_ifs; exact ha'; trivial
        · dsimp only [na_comb] at h; split_ifs at h; simp only [Sum.inl.injEq] at h; subst h; exact ha'
    have na_comb_inr (t : Bool) (a' b' : Bool ⊕ ℕ) (p : ℕ × ℕ) (h : na_comb t a' b' = Sum.inr p) :
        a' = Sum.inr p.1 ∧ b' = Sum.inr p.2 ∧ p.1 ≠ p.2 := by
      rcases a' with a' | i
      · dsimp only [na_comb] at h; cases h
      · rcases b' with b' | j
        · dsimp only [na_comb] at h; cases h
        · dsimp only [na_comb] at h; split_ifs at h with hij; cases h; exact ⟨rfl, rfl, hij⟩
    have na_strict_snoc {D : List (Bool × ℕ × ℕ)} (hS : dStrict D) (t : Bool) (i j : ℕ)
        (hi : i < 14 + D.length) (hj : j < 14 + D.length) (hij : i ≠ j) :
        dStrict (D ++ [(t, i, j)]) := by
      intro k hk
      simp only [List.length_append, List.length_singleton] at hk
      by_cases hk' : k < D.length
      · have he : (D ++ [(t, i, j)]).getD k (false, 0, 0) = D.getD k (false, 0, 0) := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk']
        simp only [opA, opB, he]; exact hS k hk'
      · have hkD : k = D.length := by omega
        subst hkD
        have he : (D ++ [(t, i, j)]).getD D.length (false, 0, 0) = (t, i, j) := by
          simp [List.getD_eq_getElem?_getD]
        simp only [opA, opB, he]; exact ⟨hi, hj, hij⟩
    have na_strict_take {D : List (Bool × ℕ × ℕ)} (hS : dStrict D) (k : ℕ) : dStrict (D.take k) := by
      intro j hj
      simp only [List.length_take] at hj
      have hj1 : j < k := by omega
      have hj2 : j < D.length := by omega
      have he : (D.take k).getD j (false, 0, 0) = D.getD j (false, 0, 0) := by
        simp [List.getD_eq_getElem?_getD, hj1]
      simp only [opA, opB, he]; exact hS j hj2
    have na_step_spec (st_ : List (Bool ⊕ ℕ) × List (Bool × ℕ × ℕ)) (g : Gate)
        (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
        (h : na_Good st_) :
        na_Good (na_step st_ g) ∧ (na_step st_ g).2.length ≤ st_.2.length + 1 ∧
        ∀ (x : Fin 14 → Bool) (w : List Bool), st_.1.map (refVal (dwl st_.2 (List.ofFn x))) = w →
          (na_step st_ g).1.map (refVal (dwl (na_step st_ g).2 (List.ofFn x))) =
            w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := by
      obtain ⟨m, D⟩ := st_
      obtain ⟨op, ins⟩ := g
      obtain ⟨hop, hlen'⟩ := hg
      obtain ⟨hS, hok⟩ := h
      have ev0 : op.eval [] = na_isAnd op := by rcases hop with rfl | rfl <;> rfl
      have ev1 : ∀ u, op.eval [u] = u := by intro u; rcases hop with rfl | rfl <;> cases u <;> rfl
      have ev2 : ∀ u v, op.eval [u, v] = gop (na_isAnd op) u v := by
        intro u v; rcases hop with rfl | rfl <;> cases u <;> cases v <;> rfl
      rcases ins with _ | ⟨a', _ | ⟨b', _ | ⟨c', rest⟩⟩⟩
      · refine ⟨⟨hS, ?_⟩, by simp [na_step], fun x w hw => ?_⟩
        · intro r' hr'; simp only [na_step, List.mem_append, List.mem_singleton] at hr'
          rcases hr' with hr' | rfl; exact hok r' hr'; trivial
        · subst hw; simp only [na_step, List.map_append, List.map_cons, List.map_nil, refVal, id_eq, ev0]
      · refine ⟨⟨hS, ?_⟩, by simp [na_step], fun x w hw => ?_⟩
        · intro r' hr'; simp only [na_step, List.mem_append, List.mem_singleton] at hr'
          rcases hr' with hr' | rfl; exact hok r' hr'; exact na_look_ok _ m hok a'
        · subst hw; simp only [na_step, List.map_append, List.map_cons, List.map_nil, ev1, na_look_val]
      · have hla := na_look_ok _ m hok a'
        have hlb := na_look_ok _ m hok b'
        rcases hc : na_comb (na_isAnd op) (na_look m a') (na_look m b') with r' | p
        · refine ⟨⟨by simpa only [na_step, hc] using hS, ?_⟩, by simp [na_step, hc],
            fun x w hw => ?_⟩
          · intro r'' hr'; simp only [na_step, hc, List.mem_append, List.mem_singleton] at hr' ⊢
            rcases hr' with hr' | rfl; exact hok r'' hr'; exact na_comb_ok _ _ _ _ _ hla hlb hc
          · subst hw
            simp only [na_step, hc, List.map_append, List.map_cons, List.map_nil, ev2,
              na_comb_inl _ (dwl D (List.ofFn x)) _ _ _ hc, na_look_val]
        · obtain ⟨ea, eb, hne⟩ := na_comb_inr _ _ _ _ hc
          rw [ea] at hla; rw [eb] at hlb
          have hS' := na_strict_snoc hS (na_isAnd op) p.1 p.2 hla hlb hne
          refine ⟨⟨by simpa only [na_step, hc] using hS', ?_⟩, by simp [na_step, hc],
            fun x w hw => ?_⟩
          · intro r'' hr'
            simp only [na_step, hc, List.mem_append, List.mem_singleton, List.length_append,
              List.length_singleton] at hr' ⊢
            rcases hr' with hr' | rfl
            · exact na_ok_mono (by dsimp only; omega) r'' (hok r'' hr')
            · show 14 + D.length < 14 + (D.length + 1); omega
          · subst hw
            have hWlen : (dwl D (List.ofFn x)).length = 14 + D.length := by
              rw [dwl_length, List.length_ofFn]
            have hW' : dwl (D ++ [(na_isAnd op, p.1, p.2)]) (List.ofFn x) =
                dwstep (dwl D (List.ofFn x)) (na_isAnd op, p.1, p.2) := by
              rw [dwl_append]; rfl
            have h1 : m.map (refVal (dwstep (dwl D (List.ofFn x)) (na_isAnd op, p.1, p.2))) =
                m.map (refVal (dwl D (List.ofFn x))) := by
              apply List.map_congr_left
              intro r'' hr''
              rcases r'' with b'' | k
              · rfl
              · exact dwstep_getD_lt _ _ k (by rw [hWlen]; exact hok (Sum.inr k) hr'')
            have h2 : (dwstep (dwl D (List.ofFn x)) (na_isAnd op, p.1, p.2)).getD (14 + D.length) false =
                gop (na_isAnd op) ((m.map (refVal (dwl D (List.ofFn x)))).getD a' false)
                  ((m.map (refVal (dwl D (List.ofFn x)))).getD b' false) := by
              have hlast : (dwstep (dwl D (List.ofFn x)) (na_isAnd op, p.1, p.2)).getD
                  (dwl D (List.ofFn x)).length false =
                  gop (na_isAnd op) ((dwl D (List.ofFn x)).getD p.1 false)
                    ((dwl D (List.ofFn x)).getD p.2 false) := by
                simp [dwstep, List.getD_eq_getElem?_getD]
              rw [← hWlen, hlast, ← na_look_val, ← na_look_val, ea, eb]
            simp only [na_step, hc, hW', List.map_append, List.map_cons, List.map_nil, h1, refVal,
              h2, ev2]
      · simp at hlen'
    have na_fold_spec (gs : List Gate)
        (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
        ∀ st_ : List (Bool ⊕ ℕ) × List (Bool × ℕ × ℕ), na_Good st_ →
          na_Good (gs.foldl na_step st_) ∧
          (gs.foldl na_step st_).2.length ≤ st_.2.length + gs.length ∧
          ∀ (x : Fin 14 → Bool) (w : List Bool), st_.1.map (refVal (dwl st_.2 (List.ofFn x))) = w →
            (gs.foldl na_step st_).1.map
                (refVal (dwl (gs.foldl na_step st_).2 (List.ofFn x))) =
              gs.foldl st w := by
      induction gs with
      | nil => intro st_ h; exact ⟨h, by simp, fun x w hw => hw⟩
      | cons g gs ih =>
        intro st_ h
        obtain ⟨h1, h2, h3⟩ := na_step_spec st_ g (hgs g (by simp)) h
        obtain ⟨i1, i2, i3⟩ := ih (fun g' hg' => hgs g' (by simp [hg'])) _ h1
        refine ⟨i1, ?_, fun x w hw => ?_⟩
        · simp only [List.foldl_cons, List.length_cons]; omega
        · simp only [List.foldl_cons]; exact i3 x _ (h3 x w hw)
    have hex_strict : ∃ D : List (Bool × ℕ × ℕ), dStrict D ∧ D ≠ [] ∧ D.length ≤ D1.size ∧
        ∀ x : Fin 14 → Bool, dval D x (dOutW D) = D1.eval (List.ofFn x) := by
      have h0 : na_Good ((List.range 14).map Sum.inr, []) := by
        refine ⟨fun j hj => absurd hj (by simp), fun r' hr' => ?_⟩
        simp only [List.mem_map, List.mem_range] at hr'
        obtain ⟨k, hk, rfl⟩ := hr'
        simpa [na_ok] using hk
      obtain ⟨⟨hS, hok⟩, hlen', hsem⟩ := na_fold_spec D1.gates hd1 _ h0
      generalize D1.gates.foldl na_step ((List.range 14).map Sum.inr, ([] : List (Bool × ℕ × ℕ))) = st_
        at hS hok hlen' hsem
      obtain ⟨m, D⟩ := st_
      dsimp only at hS hok hlen' hsem
      have hinit (x : Fin 14 → Bool) :
          ((List.range 14).map Sum.inr).map (refVal (dwl ([] : List (Bool × ℕ × ℕ)) (List.ofFn x))) =
            List.ofFn x := by
        apply List.ext_getElem
        · simp
        · intro i h1 h2
          simp only [List.length_map, List.length_range] at h1
          simp [refVal, dwl, List.getD_eq_getElem?_getD, h1]
      have hev : ∀ x : Fin 14 → Bool,
          D1.eval (List.ofFn x) = refVal (dwl D (List.ofFn x)) (na_look m D1.output) := by
        intro x
        rw [na_look_val, hsem x (List.ofFn x) (hinit x)]
        rfl
      have hk := na_look_ok _ m hok D1.output
      rcases hr' : na_look m D1.output with b' | k
      · cases b'
        · have := hD1_hit 1 0 (by decide) (Or.inl (by decide))
          rw [hev, hr'] at this; simp [refVal] at this
        · have := hD1_miss
          rw [hev, hr'] at this; simp [refVal] at this
      · rw [hr'] at hk
        have hk' : k < 14 + D.length := hk
        by_cases hkn : k < 14
        · have := hD1_upper (fun i : Fin 14 => decide (i = ⟨k, hkn⟩)) (by
            rw [hev, hr']; change (dwl D (List.ofFn _)).getD k false = true
            rw [dwl_getD_lt _ _ k (by simpa using hkn), List.getD_eq_getElem?_getD, List.getElem?_ofFn]
            simp [hkn])
          rcases this with ⟨p, l, _, hp, hl⟩
          simp only [decide_eq_true_eq] at hp hl
          have h1 := congrArg Fin.val hp
          have h2 := congrArg Fin.val hl
          simp at h1 h2; omega
        · have hl : (D.take (k - 14 + 1)).length = k - 14 + 1 := by rw [List.length_take]; omega
          refine ⟨D.take (k - 14 + 1), na_strict_take hS _, ?_, ?_, fun x => ?_⟩
          · intro h; rw [h] at hl; simp at hl
          · rw [hl]; simp only [List.length_nil, Nat.zero_add] at hlen'; change _ ≤ D1.gates.length; omega
          · have ho : dOutW (D.take (k - 14 + 1)) = k := by dsimp only [dOutW]; rw [hl]; omega
            rw [ho, dval_take D x (k - 14 + 1) k (by omega) (by omega), hev x, hr']
    -- Eliminate dead wires from the strict DAG (na_live_aux).
    have hess : ∀ i : Fin 14, ∃ x y : Fin 14 → Bool, (∀ k, k ≠ i → x k = y k) ∧
        D1.eval (List.ofFn x) ≠ D1.eval (List.ofFn y) := by
      have hnb : ∀ i : Fin 14, ∃ a : Fin 14,
          (∃ p l : Fin 7, p ∈ fanoLines l ∧ (p ≠ 0 ∨ l ≠ 0) ∧
            ((i = Fin.castAdd 7 p ∧ a = Fin.natAdd 7 l) ∨
             (i = Fin.natAdd 7 l ∧ a = Fin.castAdd 7 p))) := by
        decide +kernel
      intro i
      obtain ⟨a', p, l, hpl, hne, hpair⟩ := hnb i
      refine ⟨fun k => decide (k = a'), pairInput i a', fun k hk => ?_, ?_⟩
      · dsimp only [pairInput]; simp [hk]
      · have h0 : D1.eval (List.ofFn fun k => decide (k = a')) = false := by
          by_contra hc
          rw [Bool.not_eq_false] at hc
          obtain ⟨p', l', _, hp', hl'⟩ := hD1_upper _ hc
          simp only [decide_eq_true_eq] at hp' hl'
          have h1 := congrArg Fin.val (hp'.trans hl'.symm)
          simp at h1; omega
        have h1 : D1.eval (List.ofFn (pairInput i a')) = true := by
          rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hD1_hit p l hpl hne
          · have heq : pairInput (Fin.natAdd 7 l) (Fin.castAdd 7 p) =
                pairInput (Fin.castAdd 7 p) (Fin.natAdd 7 l) := by
              funext k; dsimp only [pairInput]; simp [or_comm]
            rw [heq]; exact hD1_hit p l hpl hne
        rw [h0, h1]; decide
    have na_no_reader {D : List (Bool × ℕ × ℕ)} {w : ℕ} (h : dFanout D w = 0) (j : ℕ)
        (hj : j < D.length) : opA D j ≠ w ∧ opB D j ≠ w := by
      dsimp only [dFanout, dReaders] at h
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h
      have := h (Finset.mem_range.mpr hj)
      tauto
    let na_sh (c a' : ℕ) : ℕ := if c < a' then a' - 1 else a'
    let na_up (c w : ℕ) : ℕ := if w < c then w else w + 1
    let na_del (j : ℕ) (D : List (Bool × ℕ × ℕ)) : List (Bool × ℕ × ℕ) :=
      (D.eraseIdx j).map (fun g => (g.1, na_sh (14 + j) g.2.1, na_sh (14 + j) g.2.2))
    have na_del_length (j : ℕ) (D : List (Bool × ℕ × ℕ)) (hj : j < D.length) :
        (na_del j D).length = D.length - 1 := by
      simp [na_del, List.length_eraseIdx, hj]
    have na_del_ops (j : ℕ) (D : List (Bool × ℕ × ℕ)) (k : ℕ) (hk : na_up j k < D.length) :
        tag (na_del j D) k = tag D (na_up j k) ∧
        opA (na_del j D) k = na_sh (14 + j) (opA D (na_up j k)) ∧
        opB (na_del j D) k = na_sh (14 + j) (opB D (na_up j k)) := by
      have e : (na_del j D).getD k (false, 0, 0) =
          ((D.getD (na_up j k) (false, 0, 0)).1, na_sh (14 + j) (D.getD (na_up j k) (false, 0, 0)).2.1,
            na_sh (14 + j) (D.getD (na_up j k) (false, 0, 0)).2.2) := by
        simp only [na_del, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eraseIdx]
        dsimp only [na_up] at hk ⊢
        split_ifs at hk ⊢ <;> simp [List.getElem?_eq_getElem hk]
      dsimp only [tag, opA, opB]
      rw [e]
      exact ⟨rfl, rfl, rfl⟩
    have na_del_strict {D : List (Bool × ℕ × ℕ)} (hS : dStrict D) (j : ℕ) (hj : j < D.length)
        (hf : dFanout D (14 + j) = 0) : dStrict (na_del j D) := by
      intro k hk
      rw [na_del_length j D hj] at hk
      have hk' : na_up j k < D.length := by dsimp only [na_up]; split_ifs <;> omega
      obtain ⟨ha', hb', hab'⟩ := hS _ hk'
      obtain ⟨ra, rb⟩ := na_no_reader hf _ hk'
      obtain ⟨-, ea, eb⟩ := na_del_ops j D k hk'
      rw [ea, eb]
      dsimp only [na_up] at ha' hb' hab' ra rb ⊢
      by_cases hkj : k < j
      · simp only [hkj, ite_true] at ha' hb' hab' ra rb ⊢
        refine ⟨?_, ?_, ?_⟩ <;> dsimp only [na_sh] <;> split_ifs <;> omega
      · simp only [hkj, ite_false] at ha' hb' hab' ra rb ⊢
        refine ⟨?_, ?_, ?_⟩ <;> dsimp only [na_sh] <;> split_ifs <;> omega
    have na_del_val {D : List (Bool × ℕ × ℕ)} (hS : dStrict D) (j : ℕ) (hj : j < D.length)
        (hf : dFanout D (14 + j) = 0) (x : Fin 14 → Bool) (w : ℕ) (hw : w < 14 + (D.length - 1)) :
        dval (na_del j D) x w = dval D x (na_up (14 + j) w) := by
      refine dval_unique (na_del_strict hS j hj hf) x (fun u => dval D x (na_up (14 + j) u))
        (fun i hi => ?_) (fun k hk => ?_) w (by rw [na_del_length j D hj]; exact hw)
      · have e : na_up (14 + j) i = i := by dsimp only [na_up]; split_ifs <;> omega
        show dval D x (na_up (14 + j) i) = x ⟨i, hi⟩
        rw [e]; exact dval_input D x i hi
      · rw [na_del_length j D hj] at hk
        have hk' : na_up j k < D.length := by dsimp only [na_up]; split_ifs <;> omega
        obtain ⟨et, ea, eb⟩ := na_del_ops j D k hk'
        obtain ⟨ra, rb⟩ := na_no_reader hf _ hk'
        have e1 : na_up (14 + j) (14 + k) = 14 + na_up j k := by dsimp only [na_up]; split_ifs <;> omega
        have e2 : ∀ a', a' ≠ 14 + j → na_up (14 + j) (na_sh (14 + j) a') = a' := by
          intro a' ha'; dsimp only [na_up, na_sh]; split_ifs <;> omega
        show dval D x (na_up (14 + j) (14 + k)) = gop (tag (na_del j D) k)
          (dval D x (na_up (14 + j) (opA (na_del j D) k)))
          (dval D x (na_up (14 + j) (opB (na_del j D) k)))
        rw [e1, et, ea, eb, e2 _ ra, e2 _ rb]
        exact dval_gate hS x _ hk'
    have na_live_aux : ∀ (s : ℕ) (D : List (Bool × ℕ × ℕ)), D.length = s → dStrict D → D ≠ [] →
        (∀ x : Fin 14 → Bool, dval D x (dOutW D) = D1.eval (List.ofFn x)) →
        ∃ D' : List (Bool × ℕ × ℕ), dStrict D' ∧ dLive D' ∧ D' ≠ [] ∧ D'.length ≤ s ∧
          ∀ x : Fin 14 → Bool, dval D' x (dOutW D') = D1.eval (List.ofFn x) := by
      intro s
      induction s using Nat.strong_induction_on with
      | _ s ih =>
        intro D hlen' hS hne hD
        have hpos' : 0 < D.length := List.length_pos_iff.mpr hne
        by_cases hL : dLive D
        · exact ⟨D, hS, hL, hne, hlen'.le, hD⟩
        · obtain ⟨w, hw, hf0⟩ : ∃ w, w + 1 < 14 + D.length ∧ dFanout D w = 0 := by
            by_contra hcon
            exact hL (fun w hw => by by_contra h0; exact hcon ⟨w, hw, by omega⟩)
          by_cases hwn : w < 14
          · exfalso
            obtain ⟨x, y, hxy, hFne⟩ := hess ⟨w, hwn⟩
            apply hFne
            rw [← hD x, ← hD y]
            have hout' : dOutW D ≠ w := by dsimp only [dOutW]; omega
            have key := dval_unique hS y (fun u => if u = w then y ⟨w, hwn⟩ else dval D x u)
              (fun i hi => by
                by_cases hiw : i = w
                · subst hiw; simp
                · simp only [hiw, ite_false]; rw [dval_input D x i hi]
                  exact hxy ⟨i, hi⟩ (fun h => hiw (congrArg Fin.val h)))
              (fun j hj => by
                obtain ⟨ha', hb'⟩ := na_no_reader hf0 j hj
                have hnj : 14 + j ≠ w := by omega
                simp only [hnj, ha', hb', ite_false]
                exact dval_gate hS x j hj)
              (dOutW D) (by dsimp only [dOutW]; omega)
            simp only [hout', ite_false] at key
            exact key.symm
          · obtain ⟨j, rfl⟩ : ∃ j, w = 14 + j := ⟨w - 14, by omega⟩
            have hj : j < D.length := by omega
            have hl := na_del_length j D hj
            obtain ⟨D', h1, h2, h3, h4, h5⟩ := ih (D.length - 1) (by omega) (na_del j D) hl
              (na_del_strict hS j hj hf0)
              (fun h => by rw [h] at hl; simp at hl; omega)
              (fun x => by
                have ho : dOutW (na_del j D) = 14 + (D.length - 1) - 1 := by dsimp only [dOutW]; rw [hl]
                have hu : na_up (14 + j) (14 + (D.length - 1) - 1) = dOutW D := by
                  dsimp only [na_up, dOutW]; split_ifs <;> omega
                rw [ho, na_del_val hS j hj hf0 x _ (by omega), hu]
                exact hD x)
            exact ⟨D', h1, h2, h3, by omega, h5⟩
    obtain ⟨D_raw, hS_raw, hne_raw, hlen_raw, hev_raw⟩ := hex_strict
    obtain ⟨D_dag, hS_dag, hL_dag, hne_dag, hlen_dag, hev_dag⟩ :=
      na_live_aux D_raw.length D_raw rfl hS_raw hne_raw hev_raw
    have hDag_len1 : 1 ≤ D_dag.length := List.length_pos_iff.mpr hne_dag
    have hDag_len25 : D_dag.length ≤ 25 := le_trans hlen_dag (le_trans hlen_raw hD1_size)
    let toGate (g : Bool × ℕ × ℕ) : Gate := ⟨if g.1 then GateOp.and else GateOp.or, [g.2.1, g.2.2]⟩
    let D2 : Circuit := ⟨D_dag.map toGate, 13 + D_dag.length⟩
    have hD2_size : D2.size = D_dag.length := by dsimp only [D2, Circuit.size]; rw [List.length_map]
    have hD2_wires (x : Fin 14 → Bool) :
        D2.wires (List.ofFn x) = dwl D_dag (List.ofFn x) := by
      change (D_dag.map toGate).foldl st (List.ofFn x) = D_dag.foldl dwstep (List.ofFn x)
      have hgen : ∀ (gs : List (Bool × ℕ × ℕ)) (w : List Bool),
          (gs.map toGate).foldl st w = gs.foldl dwstep w := by
        intro gs
        induction gs with
        | nil => intro w; rfl
        | cons g gs ih =>
          intro w
          simp only [List.map_cons, List.foldl_cons]
          have hstep : st w (toGate g) = dwstep w g := by
            dsimp only [st, dwstep, toGate, gop]
            cases g.1 <;> simp [eval_and, eval_or]
          rw [hstep, ih]
      exact hgen D_dag (List.ofFn x)
    have hD2_eval (x : Fin 14 → Bool) : D2.eval (List.ofFn x) = D1.eval (List.ofFn x) := by
      have ho : dOutW D_dag = 13 + D_dag.length := by dsimp only [dOutW]; omega
      rw [← hev_dag x, ho]
      change (D2.wires (List.ofFn x)).getD (13 + D_dag.length) false =
        (dwl D_dag (List.ofFn x)).getD (13 + D_dag.length) false
      rw [hD2_wires]
    have hD2_ao : IsAO2 14 D2 := by
      refine ⟨?_, ?_, ?_⟩
      · intro g hg
        simp only [D2, List.mem_map] at hg
        obtain ⟨g0, _, rfl⟩ := hg
        cases g0.1 <;> simp [toGate]
      · intro j hj i hi
        change j < D2.size at hj
        rw [hD2_size] at hj
        obtain ⟨ha', hb', -⟩ := hS_dag j hj
        have hgj : gateAt D2 j = toGate (D_dag.getD j (false, 0, 0)) := by
          dsimp only [gateAt, D2]
          simp [List.getD_eq_getElem?_getD, hj]
        rw [hgj] at hi
        dsimp only [toGate] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> assumption
      · intro g hg
        simp only [D2, List.mem_map] at hg
        obtain ⟨g0, _, rfl⟩ := hg
        rfl
    have hD2_dist : ∀ j < D2.size, opnd D2 j 0 ≠ opnd D2 j 1 := by
      intro j hj
      rw [hD2_size] at hj
      have hgj : gateAt D2 j = toGate (D_dag.getD j (false, 0, 0)) := by
        dsimp only [gateAt, D2]
        simp [List.getD_eq_getElem?_getD, hj]
      have ho0 : opnd D2 j 0 = opA D_dag j := by
        dsimp only [opnd, opA]; rw [hgj]; rfl
      have ho1 : opnd D2 j 1 = opB D_dag j := by
        dsimp only [opnd, opB]; rw [hgj]; rfl
      rw [ho0, ho1]
      exact (hS_dag j hj).2.2
    have hD2_live : ∀ w < 13 + D2.size, ∃ j < D2.size, w ∈ (gateAt D2 j).inputs := by
      intro w hw
      rw [hD2_size] at hw
      have h1 : 1 ≤ dFanout D_dag w := hL_dag w (by omega)
      obtain ⟨j, hj⟩ := Finset.card_pos.mp h1
      rw [Finset.mem_filter, Finset.mem_range] at hj
      refine ⟨j, by rw [hD2_size]; exact hj.1, ?_⟩
      have hgj : gateAt D2 j = toGate (D_dag.getD j (false, 0, 0)) := by
        dsimp only [gateAt, D2]
        simp [List.getD_eq_getElem?_getD, hj.1]
      rw [hgj]
      dsimp only [toGate]
      rcases hj.2 with h | h
      · simp only [opA, List.getD_eq_getElem?_getD] at h; simp [h]
      · simp only [opB, List.getD_eq_getElem?_getD] at h; simp [h]
    have hD2_out : D2.output = 13 + D2.size := by rw [hD2_size]
    have hD2_upper : ∀ x : Fin 14 → Bool, D2.eval (List.ofFn x) = true → Edge x := fun x hx =>
      hD1_upper x ((hD2_eval x) ▸ hx)
    have hD2_hit : ∀ p l : Fin 7, p ∈ fanoLines l → (p ≠ 0 ∨ l ≠ 0) →
        D2.eval (List.ofFn (pairInput (Fin.castAdd 7 p) (Fin.natAdd 7 l))) = true :=
      fun p l hpl hne => (hD2_eval _).trans (hD1_hit p l hpl hne)
    have hD2_miss : D2.eval (List.ofFn (pairInput (0 : Fin 14) (7 : Fin 14))) = false :=
      (hD2_eval _).trans hD1_miss
    let k := ((Finset.range 14).filter fun v : ℕ => ∃ w < 13 + D2.size,
      2 ≤ ((Finset.range D2.size).filter fun j => w ∈ (gateAt D2 j).inputs).card ∧
      (D2.wires (List.ofFn fun i : Fin 14 => decide (i.val = v))).getD w false = true).card
    by_cases hk9 : k ≤ 9
    · exact punc_le9 D2 (by rw [hD2_size]; exact hDag_len25) (by rw [hD2_size]; exact hDag_len1)
        hD2_ao hD2_dist hD2_live hD2_out hD2_upper hD2_hit hD2_miss hk9
    · by_cases hk10 : k = 10
      · exact punc_10 D2 (by rw [hD2_size]; exact hDag_len25) (by rw [hD2_size]; exact hDag_len1)
          hD2_ao hD2_dist hD2_live hD2_out hD2_upper hD2_hit hD2_miss hk10
      · exact punc_ge11 D2 (by rw [hD2_size]; exact hDag_len25) (by rw [hD2_size]; exact hDag_len1)
          hD2_ao hD2_dist hD2_live hD2_out hD2_upper hD2_hit hD2_miss (by omega)
