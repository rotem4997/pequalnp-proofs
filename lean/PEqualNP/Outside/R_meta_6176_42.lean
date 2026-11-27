import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.HeptadCover

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
theorem PEqualNP.Outside.R_meta_6176_42
    (full : ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true ↔
        ∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧
          x (Fin.natAdd 7 l) = true) → 27 ≤ D.size)
    (punctured : ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin 14 → Bool, D.eval (List.ofFn x) = true →
        ∃ p l : Fin 7, p ∈ fanoLines l ∧ x (Fin.castAdd 7 p) = true ∧
          x (Fin.natAdd 7 l) = true) →
      20 ≤ ((incidences fanoLines).filter fun e =>
        D.eval (List.ofFn (pairInput (Fin.castAdd 7 e.1) (Fin.natAdd 7 e.2))) = true).card →
      26 ≤ D.size) :
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
      obtain ⟨i,hi,rfl⟩ := hz
      exact h _ (hall _ ⟨i,hi,rfl⟩)
    · rw [ho]
      change (g.inputs.map a).any id = true → (g.inputs.map b).any id = true
      simp only [List.any_eq_true, List.mem_map, id_eq]
      rintro ⟨_,⟨i,hi,rfl⟩,ha⟩
      exact ⟨b i,⟨i,hi,rfl⟩,h i ha⟩
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
  have monoC (x y : Fin 14 → Bool) (h : ∀ i, x i = true → y i = true) :
      C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
    apply monoFold C.gates hao.1 _ _ (by simp) _ C.output
    intro i
    by_cases hi : i < 14
    · simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some] using h ⟨i,hi⟩
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]; simp
  have spec (x : Fin 14 → Bool) : C.eval (List.ofFn x) = true ↔ Edge x := by
    constructor
    · intro hx
      by_contra hn
      let P := Finset.univ.filter fun p : Fin 7 => x (Fin.castAdd 7 p) = true
      let L := Finset.univ.filter fun l : Fin 7 => ∀ p ∈ P, p - l ∉ offsets
      let Q := Finset.univ.filter fun p : Fin 7 => ∀ l ∈ L, p - l ∉ offsets
      have sub : P ⊆ Q := by
        intro p hp
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun l hl => (Finset.mem_filter.mp hl).2 p hp⟩
      have closed : (Finset.univ.filter fun l : Fin 7 => ∀ p ∈ Q, p-l ∉ offsets) = L := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro he
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun p hp => he _ (sub hp)⟩
        · intro hl p hp
          exact (Finset.mem_filter.mp hp).2 l hl
      have maxQ : ∀ p ∉ Q, ∃ l ∈ L, p-l ∈ offsets := by
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
          exact sub (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩)
        · intro l hl
          simp only [Fin.addCases_right, decide_eq_true_eq]
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun p hp hpl => hn ?_⟩
          exact ⟨p,l,(incidence _ _).mpr hpl,(Finset.mem_filter.mp hp).2,hl⟩
    · rintro ⟨p,l,he,hp,hl⟩
      apply monoC (row (p,l)) x _ (pos p l ((incidence _ _).mp he))
      intro i hi
      change decide (i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l) = true at hi
      rcases of_decide_eq_true hi with rfl | rfl <;> assumption
  -- The binary wire recurrence is adapted from the project proof R_meta_2346_2.
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
    have hst_len : (st pref (gateAt D j)).length = 14 + j + 1 := by
      simp only [st, List.length_append, List.length_singleton, hpref_len]
    have hwires : D.wires (List.ofFn x) =
        (D.gates.drop (j + 1)).foldl st (st pref (gateAt D j)) := by
      change D.gates.foldl st (List.ofFn x) = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
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
    Monotone2 ⟨gs,0⟩ ∧ gs.length + 1 ≤ j ∧
    ∀ w < 14+j, OK gs (r w) ∧
      Relation (V gs (r w)) w (gs.length + 1 = j ∧ (r w).isSome = true)
  have build (j : ℕ) (hj : 1 ≤ j) (hmax : j ≤ C.size) :
      ∃ gs r, Prefix j gs r := by
    induction j with
    | zero => omega
    | succ j ih =>
      by_cases hzero : j = 0
      · subst j
        refine ⟨[],fun w => if w < 14 then some w else none,?_,by decide,?_⟩
        · intro g hg
          cases hg
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
              rw [wire_input _ _ _ h,wire_input _ _ _ h]
          · have hw' : w = 14 := by omega
            subst w
            simp only [Nat.lt_irrefl, ite_false]
            refine ⟨?_, ?_, ?_⟩
            · intro k hk
              cases hk
            · intro x hx
              cases hx
            intro x hx
            rcases hx with h | ⟨_,h⟩
            · exact h.symm
            · cases h
      · obtain ⟨gs,r,hmon,hlen,hinv⟩ := ih (by omega) (by omega)
        have hjC : j < C.size := by omega
        let a := opnd C j 0
        let b := opnd C j 1
        let op := (gateAt C j).op
        obtain ⟨_,hop,ha,hb⟩ := gate_inputs2 C hao j hjC
        have wa := hinv a ha
        have wb := hinv b hb
        have step (x) : W x (14+j) = op.eval [W x a,W x b] := wire_gate C hao x j hjC
        let val := fun x => op.eval [V gs (r a) x,V gs (r b) x]
        have sem : Relation val (14+j)
            (gs.length + 1 = j ∧ (r a).isSome = true ∧ (r b).isSome = true) := by
          constructor
          · intro x hx
            rw [step]
            have hcomp (s t u v : Bool) (hs : s = true → u = true) (ht : t = true → v = true) :
                op.eval [s,t] = true → op.eval [u,v] = true := by
              change op = .and ∨ op = .or at hop
              rcases hop with h | h <;> rw [h] <;> revert hs ht <;> clear_value op <;> revert s t u v <;> decide
            exact hcomp _ _ _ _ (wa.2.1 x) (wb.2.1 x) hx
          · intro x hx
            rw [step]
            dsimp only [val]
            rw [wa.2.2 x (hx.imp_right fun h => ⟨h.1,h.2.1⟩),
                wb.2.2 x (hx.imp_right fun h => ⟨h.1,h.2.2⟩)]
        have extend (out : List Gate) (nr : Option ℕ) (hm : Monotone2 ⟨out,0⟩)
            (hlo : gs.length ≤ out.length) (hhi : out.length ≤ gs.length+1)
            (hok : OK out nr)
            (hold : ∀ w < 14+j, ∀ x, V out (r w) x = V gs (r w) x)
            (hn : ∀ x, V out nr x = val x)
            (hstrong : out.length + 1 = j+1 → nr.isSome = true →
              (r a).isSome = true ∧ (r b).isSome = true) :
            ∃ out rr, Prefix (j+1) out rr := by
          refine ⟨out,fun w => if w = 14+j then nr else r w,hm,by omega,?_⟩
          intro w hw
          by_cases he : w = 14+j
          · subst w
            simp only [ite_true]
            refine ⟨hok, fun x h => sem.1 x ((hn x) ▸ h),?_⟩
            intro x h
            rw [hn]
            exact sem.2 x (h.imp_right fun h => ⟨by omega,hstrong h.1 h.2⟩)
          · simp only [he, ite_false]
            have hw' : w < 14+j := by omega
            obtain ⟨ok,le,eq⟩ := hinv w hw'
            refine ⟨fun k hk => by have := ok k hk; omega,fun x h => le x ((hold w hw' x) ▸ h),?_⟩
            intro x h
            rw [hold w hw' x]
            exact eq x (h.imp_right fun h => ⟨by omega,h.2⟩)
        have skip (nr : Option ℕ) (hok : OK gs nr) (he : ∀ x, V gs nr x = val x) :
            ∃ out rr, Prefix (j+1) out rr :=
          extend gs nr hmon (by omega) (by omega) hok (fun _ _ _ => rfl) he (by omega)
        have okNone : OK gs none := fun k hk => by cases hk
        cases hA : r a with
        | none =>
          rcases hop with h | h
          · apply skip none okNone
            intro x
            simp [val,op,h,hA,V,eval_and]
          · apply skip (r b) wb.1
            intro x
            simp [val,op,h,hA,V,eval_or]
        | some u =>
          cases hB : r b with
          | none =>
            rcases hop with h | h
            · apply skip none okNone
              intro x
              simp [val,op,h,hB,V,eval_and]
            · apply skip (r a) wa.1
              intro x
              simp [val,op,h,hB,V,eval_or]
          | some v =>
            let g : Gate := ⟨op,[u,v]⟩
            let out := gs ++ [g]
            have hout : out.length = gs.length+1 := by simp [out]
            have appended (x : Fin 14 → Bool) :
                (Circuit.mk out 0).wires (List.ofFn x) =
                st ((Circuit.mk gs 0).wires (List.ofFn x)) g := by
              change (gs ++ [g]).foldl st _ = _
              rw [List.foldl_append]
              rfl
            have wl (x : Fin 14 → Bool) :
                ((Circuit.mk gs 0).wires (List.ofFn x)).length = 14+gs.length := by
              change (gs.foldl st _).length = _
              rw [len, List.length_ofFn]
            apply extend out (some (14+gs.length)) ?_ (by omega) (by omega) ?_ ?_ ?_ ?_
            · intro q hq
              change q ∈ gs ++ [g] at hq
              rcases List.mem_append.mp hq with h | h
              · exact hmon _ h
              · have eq : q = g := List.mem_singleton.mp h
                subst q
                exact ⟨by simpa [g,op] using hop,by simp [g]⟩
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
              change ((Circuit.mk out 0).wires _).getD (14+gs.length) false = _
              rw [appended]
              dsimp only [st]
              rw [List.getD_append_right _ _ _ _ (by rw [wl]), wl, Nat.sub_self]
              simp only [val,hA,hB]
              rfl
            · simp [hA,hB]
  have hpos : 0 < C.size := by
    by_contra! h
    have hg : C.gates = [] := List.eq_nil_of_length_eq_zero (show C.size = 0 by omega)
    unfold gateAt at first
    rw [hg] at first
    cases first
  have hout : C.output < 14+C.size := by
    by_contra! h
    have ht := pos 0 0 (by decide)
    change (C.gates.foldl st _).getD C.output false = true at ht
    rw [List.getD_eq_default _ _ (by rw [len,List.length_ofFn]; exact h)] at ht
    contradiction
  obtain ⟨gs,r,hmon,hlen,hrep⟩ := build C.size hpos (by rfl)
  obtain ⟨_,upper,agree⟩ := hrep C.output hout
  obtain ⟨_,_,ha,hb⟩ := gate_inputs2 C hao 0 hpos
  let a : Fin 14 := ⟨opnd C 0 0,ha⟩
  let b : Fin 14 := ⟨opnd C 0 1,hb⟩
  have hab : a ≠ b := fun h => hdistinct 0 hpos (congrArg Fin.val h)
  have value14 (x : Fin 14 → Bool) : W x 14 = (x a && x b) := by
    change W x (14+0) = _
    rw [show W x (14+0) = _ from wire_gate C hao x 0 hpos,first,eval_and,
      wire_input C _ _ ha,wire_input C _ _ hb]
  let keep := (incidences fanoLines).filter fun e => row e a = false ∨ row e b = false
  have cardinal : ∀ i j : Fin 14, i ≠ j → 20 ≤ ((incidences fanoLines).filter
      fun e => row e i = false ∨ row e j = false).card := by decide +kernel
  have hk : 20 ≤ keep.card := cardinal a b hab
  have hits (e : Fin 7 × Fin 7) (he : e ∈ keep) : V gs (r C.output) (row e) = true := by
    obtain ⟨hedge,hskip⟩ := Finset.mem_filter.mp he
    have h0 : W (row e) 14 = false := by
      rw [value14]
      rcases hskip with h | h <;> simp [h]
    rw [agree _ (Or.inl h0)]
    exact pos _ _ ((incidence _ _).mp (Finset.mem_filter.mp hedge).2)
  cases hr : r C.output with
  | none =>
    have hne : keep.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨e,he⟩ := hne
    have h := hits e he
    rw [hr] at h
    cases h
  | some out =>
    let D : Circuit := ⟨gs,out⟩
    have hd : Monotone2 D := hmon
    have eqD (x) : D.eval (List.ofFn x) = V gs (r C.output) x := by rw [hr]; rfl
    have sound (x : Fin 14 → Bool) (hx : D.eval (List.ofFn x) = true) : Edge x :=
      (spec x).mp (upper _ ((eqD _) ▸ hx))
    have seen : keep ⊆ (incidences fanoLines).filter fun e =>
        D.eval (List.ofFn (row e)) = true := by
      intro e he
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1,(eqD _) ▸ hits e he⟩
    have need : 26 ≤ gs.length :=
      punctured D hd sound (le_trans hk (Finset.card_le_card seen))
    have same : gs.length + 1 = C.size := by omega
    have need' : 27 ≤ gs.length := full D hd (fun x => by
      rw [eqD,agree _ (Or.inr ⟨same,by simp [hr]⟩)]
      exact spec x)
    omega
