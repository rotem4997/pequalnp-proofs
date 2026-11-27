import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2346_217
    (no_nested :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        C.size ≤ (27 : ℕ) →
        PEqualNP.TopForm.IsAO2 (14 : ℕ) C →
        (∀ j < C.size, PEqualNP.TopForm.opnd C j (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd C j (1 : Fin (2 : ℕ))) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ (x : Fin (14 : ℕ) → Bool),
          C.eval (List.ofFn x) = Bool.true ↔
          ∃ (p : Fin (7 : ℕ)) (l : Fin (7 : ℕ)),
            (p = l ∨ p = l + (1 : Fin (7 : ℕ)) ∨ p = l + (3 : Fin (7 : ℕ))) ∧
            x (Fin.castAdd (7 : ℕ) p) = Bool.true ∧ x (Fin.natAdd (7 : ℕ) l) = Bool.true) →
        (∃ g < C.size, 0 < g ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          let w0 := C.wires (List.ofFn fun i : Fin (14 : ℕ) => Decidable.decide (i = (0 : Fin (14 : ℕ))))
          let w7 := C.wires (List.ofFn fun i : Fin (14 : ℕ) => Decidable.decide (i = (7 : Fin (14 : ℕ))))
          let w07 := C.wires (List.ofFn fun i : Fin (14 : ℕ) => Decidable.decide (i = (0 : Fin (14 : ℕ)) ∨ i = (7 : Fin (14 : ℕ))))
          let a := PEqualNP.TopForm.opnd C g (0 : Fin (2 : ℕ))
          let b := PEqualNP.TopForm.opnd C g (1 : Fin (2 : ℕ))
          w07.getD a Bool.false = Bool.true ∧ w07.getD b Bool.false = Bool.true ∧
          ((w0.getD a Bool.false = Bool.false ∧ w0.getD b Bool.false = Bool.false) ∨
           (w7.getD a Bool.false = Bool.false ∧ w7.getD b Bool.false = Bool.false)) ∧
          ((w0.getD a Bool.false = Bool.false ∧ w7.getD a Bool.false = Bool.false) ∨
           (w0.getD b Bool.false = Bool.false ∧ w7.getD b Bool.false = Bool.false))) →
        False)
    (no_pair_singleton_and :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        C.size ≤ (27 : ℕ) →
        PEqualNP.TopForm.IsAO2 (14 : ℕ) C →
        (∀ j < C.size, PEqualNP.TopForm.opnd C j (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd C j (1 : Fin (2 : ℕ))) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ (x : Fin (14 : ℕ) → Bool),
          C.eval (List.ofFn x) = Bool.true ↔
          ∃ (p : Fin (7 : ℕ)) (l : Fin (7 : ℕ)),
            (p = l ∨ p = l + (1 : Fin (7 : ℕ)) ∨ p = l + (3 : Fin (7 : ℕ))) ∧
            x (Fin.castAdd (7 : ℕ) p) = Bool.true ∧ x (Fin.natAdd (7 : ℕ) l) = Bool.true) →
        (∃ g1 < C.size, ∃ g2 < C.size, 0 < g1 ∧ 0 < g2 ∧ g1 ≠ g2 ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C g1).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          let w0 := C.wires (List.ofFn fun i : Fin (14 : ℕ) => Decidable.decide (i = (0 : Fin (14 : ℕ))))
          let w7 := C.wires (List.ofFn fun i : Fin (14 : ℕ) => Decidable.decide (i = (7 : Fin (14 : ℕ))))
          w7.getD ((14 : ℕ) + g1) Bool.false = Bool.true ∧ w0.getD ((14 : ℕ) + g1) Bool.false = Bool.false ∧
          w0.getD ((14 : ℕ) + g2) Bool.false = Bool.true ∧ w7.getD ((14 : ℕ) + g2) Bool.false = Bool.false) →
        False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.and →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (∀ (x7 : Bool),                 ∃ (x8 : ℕ → Bool),                   have x9 : List Bool := x1.wires (List.ofFn fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = if x7 = Bool.true then (0 : Fin (14 : ℕ)) else (7 : Fin (14 : ℕ))));                   (∀ x10 < (14 : ℕ), x8 x10 = Decidable.decide (x10 = if x7 = Bool.true then (7 : ℕ) else (0 : ℕ))) ∧                     (∀ x10 < x1.size,                         have x12 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10;                         have x13 : ℕ := PEqualNP.TopForm.opnd x1 x10 (0 : Fin (2 : ℕ));                         have x14 : ℕ := PEqualNP.TopForm.opnd x1 x10 (1 : Fin (2 : ℕ));                         (x12.op = PEqualNP.CircuitLowerBounds.GateOp.and → x8 ((14 : ℕ) + x10) = (x9.getD x13 Bool.false && x8 x14 || x8 x13 && x9.getD x14 Bool.false)) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or → x8 ((14 : ℕ) + x10) = (x8 x13 || x8 x14))) ∧                       x8 x1.output = Bool.false) →               False := by
  intro C hsize hAO hdist hgate0 hcomp hdbl
  have hAO_andor := hAO.1
  have hAO_rb := hAO.2.1
  have hAO_len : ∀ g ∈ C.gates, g.inputs.length = 2 := hAO.2.2
  have hfold : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate) (acc : List Bool),
      let res := gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc
      res.length = acc.length + gs.length ∧
      (∀ u < acc.length, res.getD u false = acc.getD u false) ∧
      (∀ j < gs.length,
        (∀ i ∈ (gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, i < acc.length + j) →
        let g := gs.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩
        res.getD (acc.length + j) false = g.op.eval (g.inputs.map fun i => res.getD i false)) := by
    intro gs
    induction gs with
    | nil =>
      intro acc
      refine ⟨by simp, fun u _ => rfl, fun j hj => by simp at hj⟩
    | cons g rest ih =>
      intro acc
      let v := g.op.eval (g.inputs.map fun i => acc.getD i false)
      let acc' := acc ++ [v]
      have hih := ih acc'
      have hlen' : acc'.length = acc.length + 1 := by simp [acc']
      have hget_lt : ∀ u < acc.length, acc'.getD u false = acc.getD u false := by
        intro u hu
        simp [acc', List.getD_eq_getElem?_getD, List.getElem?_append_left hu]
      have hget_eq : acc'.getD acc.length false = v := by
        simp [acc', List.getD_eq_getElem?_getD]
      refine ⟨?_, ?_, ?_⟩
      · change (rest.foldl _ acc').length = acc.length + (rest.length + 1)
        have h1 := hih.1
        omega
      · intro u hu
        change (rest.foldl _ acc').getD u false = acc.getD u false
        rw [hih.2.1 u (by omega), hget_lt u hu]
      · intro j hj hrb
        cases j with
        | zero =>
          change (rest.foldl _ acc').getD (acc.length + 0) false =
            g.op.eval (g.inputs.map fun i => (rest.foldl _ acc').getD i false)
          rw [Nat.add_zero, hih.2.1 acc.length (by omega), hget_eq]
          dsimp only [v]
          congr 1
          apply List.map_congr_left
          intro i hi
          have hi' : i < acc.length := by simpa using hrb i hi
          rw [hih.2.1 i (by omega), hget_lt i hi']
        | succ k =>
          have hk : k < rest.length := by simpa using hj
          have hrb' : ∀ i ∈ (rest.getD k ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, i < acc'.length + k := by
            intro i hi
            have h1 := hrb i (by simpa using hi)
            omega
          have hstep := hih.2.2 k hk hrb'
          have hidx : acc.length + (k + 1) = acc'.length + k := by omega
          simpa [hidx, acc', v] using hstep
  have hgate_mem : ∀ j < C.size, PEqualNP.MetaComplexity.NestedCover.gateAt C j ∈ C.gates := by
    intro j hj
    change C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ ∈ C.gates
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hgate_inputs : ∀ j < C.size,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs =
        [PEqualNP.TopForm.opnd C j 0, PEqualNP.TopForm.opnd C j 1] := by
    intro j hj
    have hl : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 :=
      hAO_len _ (hgate_mem j hj)
    rcases h : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · simp [h] at hl
    · simp [h] at hl
    · have h0 : PEqualNP.TopForm.opnd C j 0 = a := by
        change (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0 = a
        rw [h]; rfl
      have h1 : PEqualNP.TopForm.opnd C j 1 = b := by
        change (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0 = b
        rw [h]; rfl
      rw [h0, h1]
    · simp [h] at hl
  have hopnd_lt : ∀ j < C.size,
      PEqualNP.TopForm.opnd C j 0 < 14 + j ∧ PEqualNP.TopForm.opnd C j 1 < 14 + j := by
    intro j hj
    have hi := hgate_inputs j hj
    have h0 : PEqualNP.TopForm.opnd C j 0 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs := by
      rw [hi]; simp
    have h1 : PEqualNP.TopForm.opnd C j 1 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs := by
      rw [hi]; simp
    exact ⟨hAO_rb j hj _ h0, hAO_rb j hj _ h1⟩
  have hgate_op : ∀ j < C.size,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro j hj
    exact hAO_andor _ (hgate_mem j hj)
  have hwires_spec : ∀ (x : Fin 14 → Bool),
      let w := C.wires (List.ofFn x)
      w.length = 14 + C.size ∧
      (∀ (i : ℕ) (hi : i < 14), w.getD i false = x ⟨i, hi⟩) ∧
      (∀ j < C.size,
        ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
          w.getD (14 + j) false =
            (w.getD (PEqualNP.TopForm.opnd C j 0) false && w.getD (PEqualNP.TopForm.opnd C j 1) false)) ∧
        ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or →
          w.getD (14 + j) false =
            (w.getD (PEqualNP.TopForm.opnd C j 0) false || w.getD (PEqualNP.TopForm.opnd C j 1) false))) := by
    intro x
    have hf := hfold C.gates (List.ofFn x)
    have hlenx : (List.ofFn x).length = 14 := List.length_ofFn
    refine ⟨?_, ?_, ?_⟩
    · change (C.gates.foldl _ (List.ofFn x)).length = 14 + C.gates.length
      rw [hf.1, hlenx]
    · intro i hi
      change (C.gates.foldl _ (List.ofFn x)).getD i false = x ⟨i, hi⟩
      rw [hf.2.1 i (by omega)]
      rw [List.getD_eq_getElem _ _ (by rw [hlenx]; exact hi)]
      exact List.getElem_ofFn (h := by rw [hlenx]; exact hi)
    · intro j hj
      have hrb : ∀ i ∈ (C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs,
          i < (List.ofFn x).length + j := by
        intro i hi
        rw [hlenx]
        exact hAO_rb j hj i hi
      have hstep := hf.2.2 j hj hrb
      rw [hlenx] at hstep
      have hin := hgate_inputs j hj
      change (C.wires (List.ofFn x)).getD (14 + j) false =
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval
          ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.map fun i => (C.wires (List.ofFn x)).getD i false) at hstep
      rw [hin] at hstep
      constructor
      · intro hop
        rw [hstep, hop]
        change ((C.wires (List.ofFn x)).getD (PEqualNP.TopForm.opnd C j 0) false &&
            ((C.wires (List.ofFn x)).getD (PEqualNP.TopForm.opnd C j 1) false && true)) = _
        rw [Bool.and_true]
      · intro hop
        rw [hstep, hop]
        change ((C.wires (List.ofFn x)).getD (PEqualNP.TopForm.opnd C j 0) false ||
            ((C.wires (List.ofFn x)).getD (PEqualNP.TopForm.opnd C j 1) false || false)) = _
        rw [Bool.or_false]
  let e0 : Fin 14 → Bool := fun i => Decidable.decide (i = (0 : Fin 14))
  let e7 : Fin 14 → Bool := fun i => Decidable.decide (i = (7 : Fin 14))
  let e07 : Fin 14 → Bool := fun i => Decidable.decide (i = (0 : Fin 14) ∨ i = (7 : Fin 14))
  let w0 : List Bool := C.wires (List.ofFn e0)
  let w7 : List Bool := C.wires (List.ofFn e7)
  let w07 : List Bool := C.wires (List.ofFn e07)
  have hw0 := hwires_spec e0
  have hw7 := hwires_spec e7
  have hw07 := hwires_spec e07
  have hout07 : w07.getD C.output false = true := by
    change C.eval (List.ofFn e07) = true
    rw [hcomp e07]
    refine ⟨(0 : Fin 7), (0 : Fin 7), Or.inl rfl, ?_, ?_⟩ <;> decide
  have hout0 : w0.getD C.output false = false := by
    change C.eval (List.ofFn e0) = false
    cases h : C.eval (List.ofFn e0)
    · rfl
    · rw [hcomp e0] at h
      rcases h with ⟨p, l, _, _, hl⟩
      have : (Fin.natAdd 7 l : Fin 14) = (0 : Fin 14) := by simpa [e0] using hl
      have hv := congrArg Fin.val this
      simp at hv
  have hout7 : w7.getD C.output false = false := by
    change C.eval (List.ofFn e7) = false
    cases h : C.eval (List.ofFn e7)
    · rfl
    · rw [hcomp e7] at h
      rcases h with ⟨p, l, _, hp, _⟩
      have : (Fin.castAdd 7 p : Fin 14) = (7 : Fin 14) := by simpa [e7] using hp
      have hv := congrArg Fin.val this
      simp at hv
      omega
  have hout_lt : C.output < 14 + C.size := by
    by_contra hge
    have hge' : w07.length ≤ C.output := by
      have hlen : w07.length = 14 + C.size := hw07.1
      omega
    have hnone : w07[C.output]? = none := List.getElem?_eq_none hge'
    have hfalse : w07.getD C.output false = false := by
      rw [List.getD_eq_getElem?_getD, hnone]
      rfl
    rw [hout07] at hfalse
    cases hfalse
  have hfind : ∀ (b : Bool),
      let wbase := if b = true then w0 else w7
      ∃ g < C.size,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        w07.getD (PEqualNP.TopForm.opnd C g 0) false = true ∧
        w07.getD (PEqualNP.TopForm.opnd C g 1) false = true ∧
        wbase.getD (PEqualNP.TopForm.opnd C g 0) false = false ∧
        wbase.getD (PEqualNP.TopForm.opnd C g 1) false = false := by
    intro b
    rcases hdbl b with ⟨f, hf_in, hf_gate, hf_out⟩
    by_contra hno
    have hno' : ∀ g < C.size,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        w07.getD (PEqualNP.TopForm.opnd C g 0) false = true →
        w07.getD (PEqualNP.TopForm.opnd C g 1) false = true →
        (if b = true then w0 else w7).getD (PEqualNP.TopForm.opnd C g 0) false = true ∨
        (if b = true then w0 else w7).getD (PEqualNP.TopForm.opnd C g 1) false = true := by
      intro g hg hop ha07 hb07
      by_contra hboth
      push Not at hboth
      have ha0 : (if b = true then w0 else w7).getD (PEqualNP.TopForm.opnd C g 0) false = false := by
        cases hv : (if b = true then w0 else w7).getD (PEqualNP.TopForm.opnd C g 0) false
        · rfl
        · exact absurd hv hboth.1
      have hb0 : (if b = true then w0 else w7).getD (PEqualNP.TopForm.opnd C g 1) false = false := by
        cases hv : (if b = true then w0 else w7).getD (PEqualNP.TopForm.opnd C g 1) false
        · rfl
        · exact absurd hv hboth.2
      exact hno ⟨g, hg, hop, ha07, hb07, ha0, hb0⟩
    have hind : ∀ u : ℕ, u < 14 + C.size →
        w07.getD u false = true →
        (if b = true then w0 else w7).getD u false = false →
        f u = true := by
      intro u
      induction u using Nat.strong_induction_on with
      | ind u ih =>
        intro hu hu07 hubase
        by_cases hu14 : u < 14
        · have h1 := hw07.2.1 u hu14
          rw [h1] at hu07
          have hfin : (⟨u, hu14⟩ : Fin 14) = (0 : Fin 14) ∨ (⟨u, hu14⟩ : Fin 14) = (7 : Fin 14) := by
            simpa [e07] using hu07
          cases b with
          | true =>
            have h2 := hw0.2.1 u hu14
            simp only [ite_true] at hubase
            rw [h2] at hubase
            have hne0 : (⟨u, hu14⟩ : Fin 14) ≠ (0 : Fin 14) := by simpa [e0] using hubase
            have heq7 : (⟨u, hu14⟩ : Fin 14) = (7 : Fin 14) := hfin.resolve_left hne0
            have hu7 : u = 7 := congrArg Fin.val heq7
            simpa [hu7] using hf_in u hu14
          | false =>
            have h2 := hw7.2.1 u hu14
            simp only [Bool.false_eq_true, ite_false] at hubase
            rw [h2] at hubase
            have hne7 : (⟨u, hu14⟩ : Fin 14) ≠ (7 : Fin 14) := by simpa [e7] using hubase
            have heq0 : (⟨u, hu14⟩ : Fin 14) = (0 : Fin 14) := hfin.resolve_right hne7
            have hu0 : u = 0 := congrArg Fin.val heq0
            simpa [hu0] using hf_in u hu14
        · obtain ⟨j, rfl⟩ : ∃ j, u = 14 + j := ⟨u - 14, by omega⟩
          have hj : j < C.size := by omega
          have hlt := hopnd_lt j hj
          have hg := hf_gate j hj
          rcases hgate_op j hj with hop | hop
          · have h07_step := (hw07.2.2 j hj).1 hop
            rw [h07_step] at hu07
            have ha07 : w07.getD (PEqualNP.TopForm.opnd C j 0) false = true :=
              (Bool.and_eq_true _ _).mp hu07 |>.1
            have hb07 : w07.getD (PEqualNP.TopForm.opnd C j 1) false = true :=
              (Bool.and_eq_true _ _).mp hu07 |>.2
            have hbase_step : (if b = true then w0 else w7).getD (14 + j) false =
                ((if b = true then w0 else w7).getD (PEqualNP.TopForm.opnd C j 0) false &&
                 (if b = true then w0 else w7).getD (PEqualNP.TopForm.opnd C j 1) false) := by
              cases b with
              | true => simp only [ite_true]; exact (hw0.2.2 j hj).1 hop
              | false => simp only [Bool.false_eq_true, ite_false]; exact (hw7.2.2 j hj).1 hop
            rw [hbase_step] at hubase
            have hf_eq : f (14 + j) =
                ((if b = true then w0 else w7).getD (PEqualNP.TopForm.opnd C j 0) false &&
                  f (PEqualNP.TopForm.opnd C j 1) ||
                 f (PEqualNP.TopForm.opnd C j 0) &&
                  (if b = true then w0 else w7).getD (PEqualNP.TopForm.opnd C j 1) false) := by
              cases b with
              | true => simp only [ite_true]; exact hg.1 hop
              | false => simp only [Bool.false_eq_true, ite_false]; exact hg.1 hop
            rcases hno' j hj hop ha07 hb07 with ha_true | hb_true
            · have hb_false : (if b = true then w0 else w7).getD (PEqualNP.TopForm.opnd C j 1) false = false := by
                rw [ha_true] at hubase
                simpa using hubase
              have hfb : f (PEqualNP.TopForm.opnd C j 1) = true :=
                ih (PEqualNP.TopForm.opnd C j 1) hlt.2 (by omega) hb07 hb_false
              rw [hf_eq, ha_true, hfb]
              rfl
            · have ha_false : (if b = true then w0 else w7).getD (PEqualNP.TopForm.opnd C j 0) false = false := by
                rw [hb_true] at hubase
                simpa using hubase
              have hfa : f (PEqualNP.TopForm.opnd C j 0) = true :=
                ih (PEqualNP.TopForm.opnd C j 0) hlt.1 (by omega) ha07 ha_false
              rw [hf_eq, hb_true, hfa]
              simp
          · have h07_step := (hw07.2.2 j hj).2 hop
            rw [h07_step] at hu07
            have hbase_step : (if b = true then w0 else w7).getD (14 + j) false =
                ((if b = true then w0 else w7).getD (PEqualNP.TopForm.opnd C j 0) false ||
                 (if b = true then w0 else w7).getD (PEqualNP.TopForm.opnd C j 1) false) := by
              cases b with
              | true => simp only [ite_true]; exact (hw0.2.2 j hj).2 hop
              | false => simp only [Bool.false_eq_true, ite_false]; exact (hw7.2.2 j hj).2 hop
            rw [hbase_step] at hubase
            have ha_false : (if b = true then w0 else w7).getD (PEqualNP.TopForm.opnd C j 0) false = false :=
              (Bool.or_eq_false_iff.mp hubase).1
            have hb_false : (if b = true then w0 else w7).getD (PEqualNP.TopForm.opnd C j 1) false = false :=
              (Bool.or_eq_false_iff.mp hubase).2
            have hf_eq := hg.2 hop
            rcases Bool.or_eq_true _ _ |>.mp hu07 with ha07 | hb07
            · have hfa := ih (PEqualNP.TopForm.opnd C j 0) hlt.1 (by omega) ha07 ha_false
              rw [hf_eq, hfa]
              rfl
            · have hfb := ih (PEqualNP.TopForm.opnd C j 1) hlt.2 (by omega) hb07 hb_false
              rw [hf_eq, hfb]
              simp
    have hbase_out : (if b = true then w0 else w7).getD C.output false = false := by
      cases b with
      | true => simpa using hout0
      | false => simpa using hout7
    have hf_true := hind C.output hout_lt hout07 hbase_out
    rw [hf_out] at hf_true
    cases hf_true
  rcases hfind true with ⟨g1, hg1, hop1, ha1_07, hb1_07, ha1_0, hb1_0⟩
  simp only [ite_true] at ha1_0 hb1_0
  rcases hfind false with ⟨g2, hg2, hop2, ha2_07, hb2_07, ha2_7, hb2_7⟩
  simp only [Bool.false_eq_true, ite_false] at ha2_7 hb2_7
  have hpos_of_nested : ∀ g < C.size,
      w07.getD (PEqualNP.TopForm.opnd C g 0) false = true →
      w07.getD (PEqualNP.TopForm.opnd C g 1) false = true →
      ((w0.getD (PEqualNP.TopForm.opnd C g 0) false = false ∧ w7.getD (PEqualNP.TopForm.opnd C g 0) false = false) ∨
       (w0.getD (PEqualNP.TopForm.opnd C g 1) false = false ∧ w7.getD (PEqualNP.TopForm.opnd C g 1) false = false)) →
      0 < g := by
    intro g hg ha07 hb07 hnest
    by_contra h0
    have hg0 : g = 0 := by omega
    subst hg0
    have hlt := hopnd_lt 0 hg
    rcases hnest with ⟨h0a, h7a⟩ | ⟨h0b, h7b⟩
    · have ha14 : PEqualNP.TopForm.opnd C 0 0 < 14 := hlt.1
      rw [hw07.2.1 _ ha14] at ha07
      rw [hw0.2.1 _ ha14] at h0a
      rw [hw7.2.1 _ ha14] at h7a
      have hfin : (⟨PEqualNP.TopForm.opnd C 0 0, ha14⟩ : Fin 14) = (0 : Fin 14) ∨
          (⟨PEqualNP.TopForm.opnd C 0 0, ha14⟩ : Fin 14) = (7 : Fin 14) := by simpa [e07] using ha07
      rcases hfin with heq | heq
      · simp [e0, heq] at h0a
      · simp [e7, heq] at h7a
    · have hb14 : PEqualNP.TopForm.opnd C 0 1 < 14 := hlt.2
      rw [hw07.2.1 _ hb14] at hb07
      rw [hw0.2.1 _ hb14] at h0b
      rw [hw7.2.1 _ hb14] at h7b
      have hfin : (⟨PEqualNP.TopForm.opnd C 0 1, hb14⟩ : Fin 14) = (0 : Fin 14) ∨
          (⟨PEqualNP.TopForm.opnd C 0 1, hb14⟩ : Fin 14) = (7 : Fin 14) := by simpa [e07] using hb07
      rcases hfin with heq | heq
      · simp [e0, heq] at h0b
      · simp [e7, heq] at h7b
  cases ha1_7 : w7.getD (PEqualNP.TopForm.opnd C g1 0) false with
  | false =>
    have hpos := hpos_of_nested g1 hg1 ha1_07 hb1_07 (Or.inl ⟨ha1_0, ha1_7⟩)
    exact no_nested C hsize hAO hdist hgate0 hcomp
      ⟨g1, hg1, hpos, hop1, ha1_07, hb1_07, Or.inl ⟨ha1_0, hb1_0⟩, Or.inl ⟨ha1_0, ha1_7⟩⟩
  | true =>
    cases hb1_7 : w7.getD (PEqualNP.TopForm.opnd C g1 1) false with
    | false =>
      have hpos := hpos_of_nested g1 hg1 ha1_07 hb1_07 (Or.inr ⟨hb1_0, hb1_7⟩)
      exact no_nested C hsize hAO hdist hgate0 hcomp
        ⟨g1, hg1, hpos, hop1, ha1_07, hb1_07, Or.inl ⟨ha1_0, hb1_0⟩, Or.inr ⟨hb1_0, hb1_7⟩⟩
    | true =>
      cases ha2_0 : w0.getD (PEqualNP.TopForm.opnd C g2 0) false with
      | false =>
        have hpos := hpos_of_nested g2 hg2 ha2_07 hb2_07 (Or.inl ⟨ha2_0, ha2_7⟩)
        exact no_nested C hsize hAO hdist hgate0 hcomp
          ⟨g2, hg2, hpos, hop2, ha2_07, hb2_07, Or.inr ⟨ha2_7, hb2_7⟩, Or.inl ⟨ha2_0, ha2_7⟩⟩
      | true =>
        cases hb2_0 : w0.getD (PEqualNP.TopForm.opnd C g2 1) false with
        | false =>
          have hpos := hpos_of_nested g2 hg2 ha2_07 hb2_07 (Or.inr ⟨hb2_0, hb2_7⟩)
          exact no_nested C hsize hAO hdist hgate0 hcomp
            ⟨g2, hg2, hpos, hop2, ha2_07, hb2_07, Or.inr ⟨ha2_7, hb2_7⟩, Or.inr ⟨hb2_0, hb2_7⟩⟩
        | true =>
          have hg1_w7 : w7.getD (14 + g1) false = true := by
            rw [(hw7.2.2 g1 hg1).1 hop1, ha1_7, hb1_7]; rfl
          have hg1_w0 : w0.getD (14 + g1) false = false := by
            rw [(hw0.2.2 g1 hg1).1 hop1, ha1_0, hb1_0]; rfl
          have hg2_w0 : w0.getD (14 + g2) false = true := by
            rw [(hw0.2.2 g2 hg2).1 hop2, ha2_0, hb2_0]; rfl
          have hg2_w7 : w7.getD (14 + g2) false = false := by
            rw [(hw7.2.2 g2 hg2).1 hop2, ha2_7, hb2_7]; rfl
          have hne : g1 ≠ g2 := by
            intro heq
            subst heq
            rw [hg1_w0] at hg2_w0
            cases hg2_w0
          have hpos1 : 0 < g1 := by
            by_contra h0
            have hg0 : g1 = 0 := by omega
            subst hg0
            have hlt := hopnd_lt 0 hg1
            rw [hw7.2.1 _ hlt.1] at ha1_7
            rw [hw7.2.1 _ hlt.2] at hb1_7
            have h1f : (⟨PEqualNP.TopForm.opnd C 0 0, hlt.1⟩ : Fin 14) = (7 : Fin 14) := by simpa [e7] using ha1_7
            have h2f : (⟨PEqualNP.TopForm.opnd C 0 1, hlt.2⟩ : Fin 14) = (7 : Fin 14) := by simpa [e7] using hb1_7
            have h1 : PEqualNP.TopForm.opnd C 0 0 = 7 := congrArg Fin.val h1f
            have h2 : PEqualNP.TopForm.opnd C 0 1 = 7 := congrArg Fin.val h2f
            exact hdist 0 hg1 (by omega)
          have hpos2 : 0 < g2 := by
            by_contra h0
            have hg0 : g2 = 0 := by omega
            subst hg0
            have hlt := hopnd_lt 0 hg2
            rw [hw0.2.1 _ hlt.1] at ha2_0
            rw [hw0.2.1 _ hlt.2] at hb2_0
            have h1 : PEqualNP.TopForm.opnd C 0 0 = 0 := by simpa [e0] using ha2_0
            have h2 : PEqualNP.TopForm.opnd C 0 1 = 0 := by simpa [e0] using hb2_0
            exact hdist 0 hg2 (by omega)
          exact no_pair_singleton_and C hsize hAO hdist hgate0 hcomp
            ⟨g1, hg1, g2, hg2, hpos1, hpos2, hne, hop1, hop2, hg1_w7, hg1_w0, hg2_w0, hg2_w7⟩
