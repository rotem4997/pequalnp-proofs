import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1200000 in
theorem PEqualNP.Outside.R_meta_2348_8
  (boundary : ∀ f : (Fin 14 → Bool) → Bool, (∀ x, f x = true ↔ ∃ p l : Fin 7, (p=l ∨ p=l+1 ∨ p=l+3) ∧ x (Fin.castAdd 7 p)=true ∧ x (Fin.natAdd 7 l)=true) ↔ Monotone f ∧ ∀ t : Fin 58, f (fun i => (([16771220242439, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 182572334459126281, 218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114, 270286071509155872, 288160007408582916] : List Nat).getD i.val 0).testBit t.val) = decide (t.val < 21))
  (obstruction : let seed := (([2594090156585648135, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 1911954591369396745, 218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114, 270286071509155872, 288160007408582916] : List Nat).map fun v => fun t : Fin 62 => v.testBit t.val); ¬∃ s : List (Fin 62 → Bool), s.length ≤ 27 ∧ (fun t => decide (t.val < 21)) ∈ s ∧
    ∀ j < s.length, ∃ a b : Nat, a ≠ b ∧ a < 14+j ∧ b < 14+j ∧
      let A := (seed++s).getD a (fun _ => false); let B := (seed++s).getD b (fun _ => false);
      s.getD j (fun _ => false) = (fun t => A t || B t) ∨ 0 < j ∧
      s.getD j (fun _ => false) = (fun t => if t=60 then ((A 58 && B 60) || (A 60 && B 58)) else if t=61 then ((A 59 && B 61) || (A 61 && B 59)) else (A t && B t))) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit),   x1.size ≤ (27 : ℕ) →     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 →       (∀ x4 < x1.size, PEqualNP.TopForm.opnd x1 x4 (0 : Fin (2 : ℕ)) ≠ PEqualNP.TopForm.opnd x1 x4 (1 : Fin (2 : ℕ))) →         (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (0 : ℕ)).op = PEqualNP.CircuitLowerBounds.GateOp.or →           (∀ (x6 : Fin (14 : ℕ) → Bool), x1.eval (List.ofFn x6) = Bool.true ↔ ∃ (x7 : Fin (7 : ℕ)) (x8 : Fin (7 : ℕ)), (x7 = x8 ∨ x7 = x8 + (1 : Fin (7 : ℕ)) ∨ x7 = x8 + (3 : Fin (7 : ℕ))) ∧ x6 (Fin.castAdd (7 : ℕ) x7) = Bool.true ∧ x6 (Fin.natAdd (7 : ℕ) x8) = Bool.true) →             (∀ (x7 : Bool),                 ∃ (x8 : ℕ → Bool),                   have x9 : List Bool := x1.wires (List.ofFn fun (x9 : Fin (14 : ℕ)) => Decidable.decide (x9 = if x7 = Bool.true then (0 : Fin (14 : ℕ)) else (7 : Fin (14 : ℕ))));                   (∀ x10 < (14 : ℕ), x8 x10 = Decidable.decide (x10 = if x7 = Bool.true then (7 : ℕ) else (0 : ℕ))) ∧                     (∀ x10 < x1.size,                         have x12 : PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10;                         have x13 : ℕ := PEqualNP.TopForm.opnd x1 x10 (0 : Fin (2 : ℕ));                         have x14 : ℕ := PEqualNP.TopForm.opnd x1 x10 (1 : Fin (2 : ℕ));                         (x12.op = PEqualNP.CircuitLowerBounds.GateOp.and → x8 ((14 : ℕ) + x10) = (x9.getD x13 Bool.false && x8 x14 || x8 x13 && x9.getD x14 Bool.false)) ∧ (x12.op = PEqualNP.CircuitLowerBounds.GateOp.or → x8 ((14 : ℕ) + x10) = (x8 x13 || x8 x14))) ∧                       x8 x1.output = Bool.false) →               False := by
  intro C cap ao distinct first computes traces
  let wstep : List Bool → Gate → List Bool :=
    fun ws g => ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]
  have wfold_len : ∀ (gs : List Gate) (xs : List Bool),
      (gs.foldl wstep xs).length = xs.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro xs; simp
    | cons g rest ih =>
      intro xs
      simp only [List.foldl_cons, ih, wstep, List.length_append, List.length_cons, List.length_nil]
      omega
  have wfold_getD_lt : ∀ (gs : List Gate) (xs : List Bool) (r : ℕ),
      r < xs.length → (gs.foldl wstep xs).getD r false = xs.getD r false := by
    intro gs
    induction gs with
    | nil => intro xs r _; rfl
    | cons g rest ih =>
      intro xs r hr
      simp only [List.foldl_cons]
      have hr' : r < (wstep xs g).length := by
        simp only [wstep, List.length_append, List.length_singleton]; omega
      rw [ih (wstep xs g) r hr']
      simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hr]
  have eval_and : ∀ b1 b2 : Bool, GateOp.and.eval [b1, b2] = (b1 && b2) := by decide
  have eval_or : ∀ b1 b2 : Bool, GateOp.or.eval [b1, b2] = (b1 || b2) := by decide
  have wireVal_input : ∀ (D : Circuit) (x : Fin 14 → Bool) (r : ℕ) (hr : r < 14),
      wireVal 14 D r x = x ⟨r, hr⟩ := by
    intro D x r hr
    have hlen : (List.ofFn x).length = 14 := List.length_ofFn
    have hlt : r < (List.ofFn x).length := by omega
    change (D.gates.foldl wstep (List.ofFn x)).getD r false = x ⟨r, hr⟩
    rw [wfold_getD_lt D.gates (List.ofFn x) r hlt]
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hr]
  have wireVal_gate : ∀ (D : Circuit) (x : Fin 14 → Bool) (k : ℕ) (g : Gate),
      D.gates[k]? = some g → (∀ i ∈ g.inputs, i < 14 + k) →
      wireVal 14 D (14 + k) x = g.op.eval (g.inputs.map fun i => wireVal 14 D i x) := by
    intro D x k g hgk hlt
    have hk : k < D.gates.length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at hgk
      cases hgk
    have hg_eq : D.gates[k] = g := by
      rw [List.getElem?_eq_getElem hk] at hgk
      exact Option.some.inj hgk
    have hsplit : D.gates = D.gates.take k ++ g :: D.gates.drop (k + 1) := by
      rw [← hg_eq, ← List.drop_eq_getElem_cons hk, List.take_append_drop]
    let pref := (D.gates.take k).foldl wstep (List.ofFn x)
    have hpref_len : pref.length = 14 + k := by
      dsimp only [pref]
      rw [wfold_len, List.length_ofFn, List.length_take]
      omega
    have hwires_eq : D.wires (List.ofFn x) =
        (D.gates.drop (k + 1)).foldl wstep (wstep pref g) := by
      change D.gates.foldl wstep (List.ofFn x) = _
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hpref_get : ∀ i < 14 + k, pref.getD i false = wireVal 14 D i x := by
      intro i hi
      change pref.getD i false = (D.wires (List.ofFn x)).getD i false
      rw [hwires_eq]
      have hi1 : i < (wstep pref g).length := by
        simp only [wstep, List.length_append, List.length_singleton]; omega
      rw [wfold_getD_lt _ _ i hi1]
      have hi0 : i < pref.length := by omega
      simp only [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi0]
    change (D.wires (List.ofFn x)).getD (14 + k) false = _
    rw [hwires_eq]
    have hidx : 14 + k < (wstep pref g).length := by
      simp only [wstep, List.length_append, List.length_singleton]; omega
    rw [wfold_getD_lt _ _ (14 + k) hidx]
    have hstep_at : (wstep pref g).getD (14 + k) false =
        g.op.eval (g.inputs.map fun i => pref.getD i false) := by
      simp only [wstep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), hpref_len]
      simp
    rw [hstep_at]
    congr 1
    exact List.map_congr_left fun i hi => hpref_get i (hlt i hi)
  let base : List Nat := [2594090156585648135, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 1911954591369396745, 218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114, 270286071509155872, 288160007408582916]
  let seed := base.map fun v => fun t : Fin 62 => v.testBit t.val
  let input (t : Fin 62) (i : Fin 14) := (base.getD i.val 0).testBit t.val
  let single (b : Bool) (i : Fin 14) := decide (i = if b=true then 0 else 7)
  have s58 (i : Fin 14) : input 58 i = single true i := by revert i; decide +kernel
  have s59 (i : Fin 14) : input 59 i = single false i := by revert i; decide +kernel
  have s60 (i : Fin 14) : input 60 i = decide (i.val=7) := by revert i; decide +kernel
  have s61 (i : Fin 14) : input 61 i = decide (i.val=0) := by revert i; decide +kernel
  have firstRows : ∀ (t : Fin 62) (k : Fin 58), t.val=k.val → ∀ i : Fin 14,
      input t i = (([16771220242439, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 182572334459126281, 218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114, 270286071509155872, 288160007408582916] : List Nat).getD i.val 0).testBit k.val := by decide +kernel
  have e58 : input 58=single true := funext s58
  have e59 : input 59=single false := funext s59
  choose D hd using traces
  let V (i : Nat) (t : Fin 62) : Bool := if t=60 then D true i else if t=61 then D false i else wireVal 14 C i (input t)
  let seq := List.ofFn (fun j : Fin C.size => V (14+j.val))
  have seqLen : seq.length=C.size := List.length_ofFn
  have seedLen : seed.length=14 := rfl
  have inputV (i : Fin 14) : V i.val = fun t => input t i := by
    funext t
    by_cases h : t=60
    · subst t; simp only [V,ite_true,s60]; simpa using (hd true).1 i.val i.isLt
    by_cases k : t=61
    · subst t; simp only [V,show (61:Fin 62)≠60 by decide,ite_false,ite_true,s61]; simpa using (hd false).1 i.val i.isLt
    · simp only [V,h,k,ite_false]; exact wireVal_input C _ _ i.isLt
  have publicWire (a : Nat) (ha : a<14+C.size) : (seed++seq).getD a (fun _ => false) = V a := by
    by_cases low : a<14
    · let i : Fin 14 := ⟨a,low⟩
      rw [List.getD_append _ _ _ _ (by omega)]
      change seed.getD i.val _ = V i.val
      rw [inputV]
      have hbase : i.val<base.length := i.isLt
      simp only [seed,List.getD_eq_getElem _ _ (show i.val<seed.length by omega), List.getElem_map]
      funext t; simp only [input,List.getD_eq_getElem _ _ hbase]
    · let j : Fin C.size := ⟨a-14,by omega⟩
      have eq : a=14+j.val := by dsimp [j];omega
      simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (show seed.length≤a by omega),seedLen,seq,List.getElem?_ofFn,dif_pos (show a-14<C.size by omega),Option.getD_some]
      congr 1; omega
  have outBound : C.output<14+C.size := by
    by_contra! beyond
    have pos := (computes (fun _ => true)).mpr ⟨0,0,Or.inl rfl,rfl,rfl⟩
    change (C.gates.foldl wstep (List.ofFn (fun _ : Fin 14 => true))).getD C.output false=true at pos
    rw [List.getD_eq_default _ _ (by rw [wfold_len,List.length_ofFn];exact beyond)] at pos
    exact Bool.noConfusion pos
  have outputGate : 14≤C.output := by
    by_contra! low
    let i : Fin 14 := ⟨C.output,low⟩
    let x (v : Fin 14) := decide (v=i)
    have lit : C.eval (List.ofFn x)=true := (wireVal_input C x _ low).trans (by simp [x,i])
    obtain ⟨p,l,_,hp,hl⟩ := (computes x).mp lit
    have bad := congrArg Fin.val ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)
    change p.val=7+l.val at bad;omega
  have outValue : V C.output = fun t => decide (t.val<21) := by
    funext t
    by_cases h60 : t=60
    · subst t; change D true C.output=false; exact (hd true).2.2
    by_cases h61 : t=61
    · subst t; change D false C.output=false; exact (hd false).2.2
    have small : ∀ k : Fin 58, C.eval (List.ofFn (fun i => (([16771220242439, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 182572334459126281, 218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114, 270286071509155872, 288160007408582916] : List Nat).getD i.val 0).testBit k.val))=decide (k.val<21) := ((boundary _).mp computes).2
    by_cases low : t.val<58
    · let k : Fin 58 := ⟨t.val,low⟩
      simp only [V,h60,h61,ite_false]; change C.eval (List.ofFn (input t))=_
      rw [show input t=(fun i => (([16771220242439, 15270196031782968, 58150373818816, 94946423956573696, 54820275478360064, 3870282840506368, 133412159488, 182572334459126281, 218716039641305168, 189725234880873600, 156548607028504576, 229736628137050114, 270286071509155872, 288160007408582916] : List Nat).getD i.val 0).testBit k.val) from funext (firstRows t k rfl)]
      exact small k
    · have options : t=58 ∨ t=59 := by
        have a : t.val≠60 := fun eq => h60 (Fin.ext eq)
        have b : t.val≠61 := fun eq => h61 (Fin.ext eq)
        have d : t.val=58 ∨ t.val=59 := by omega
        exact d.imp (fun v => Fin.ext v) (fun v => Fin.ext v)
      have quiet (b : Bool) : C.eval (List.ofFn (single b))=false := by
        cases eq : C.eval (List.ofFn (single b)) with
        | false => rfl
        | true =>
          obtain ⟨p,l,_,hp,hl⟩ := (computes _).mp eq
          have bad := congrArg Fin.val ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)
          change p.val=7+l.val at bad;omega
      rcases options with rfl|rfl
      · change C.eval (List.ofFn (input 58))=false; rw [e58];exact quiet true
      · change C.eval (List.ofFn (input 59))=false; rw [e59];exact quiet false
  apply obstruction
  refine ⟨seq,seqLen.symm ▸ cap,?_,?_⟩
  · apply List.mem_ofFn.mpr
    refine ⟨⟨C.output-14,by omega⟩,?_⟩
    change V (14+(C.output-14))=_; rwa [Nat.add_sub_of_le outputGate]
  · intro j hj
    have valid : j<C.gates.length := by change j<C.size; omega
    let g := gateAt C j
    have slot : C.gates[j]?=some g := List.getElem?_eq_some_iff.mpr ⟨valid,by change C.gates[j]=C.gates.getD j _; rw [List.getD_eq_getElem _ _ valid]⟩
    have ing := List.mem_of_getElem? slot
    let a := opnd C j 0
    let b := opnd C j 1
    have form : g.inputs=[a,b] := by
      have sz := ao.2.2 g ing
      rcases ins : g.inputs with _ | ⟨u, tail⟩
      · simp [ins] at sz
      · rcases rest : tail with _ | ⟨v,rest'⟩
        · simp [ins,rest] at sz
        · have z : rest'=[] := List.length_eq_zero_iff.mp (by simp only [ins,rest,List.length_cons] at sz; omega)
          change u::v::rest'=[g.inputs.getD 0 0,g.inputs.getD 1 0]; simp [ins,rest,z]
    have early := ao.2.1 j valid
    have ha := early a (by change a∈g.inputs;rw [form];simp)
    have hb := early b (by change b∈g.inputs;rw [form];simp)
    have wire (x : Fin 14→Bool) : wireVal 14 C (14+j) x = g.op.eval [wireVal 14 C a x,wireVal 14 C b x] := by
      rw [wireVal_gate C x j g slot early,form] <;> rfl
    refine ⟨a,b,distinct j valid,ha,hb,?_⟩
    dsimp only
    change (seq.getD j _ = _) ∨ (0<j ∧ seq.getD j _ = _)
    have read : seq.getD j (fun _ => false)=V (14+j) := by simp only [seq,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos (show j<C.size from valid),Option.getD_some]
    rw [read,publicWire a (by omega),publicWire b (by omega)]
    rcases ao.1 g ing with andGate | orGate
    · right
      have pos : 0<j := by
        by_contra! no
        have e : j=0 := by omega
        have gd : g.op=GateOp.or := by change (gateAt C j).op=_; rw [e];exact first
        exact GateOp.noConfusion (andGate.symm.trans gd)
      refine ⟨pos,?_⟩; funext t
      by_cases h : t=60
      · subst t
        change D true (14+j) = ((wireVal 14 C a (input 58) && D true b) || (D true a && wireVal 14 C b (input 58)))
        rw [e58];exact ((hd true).2.1 j valid).1 andGate
      by_cases h' : t=61
      · subst t
        change D false (14+j) = ((wireVal 14 C a (input 59) && D false b) || (D false a && wireVal 14 C b (input 59)))
        rw [e59];exact ((hd false).2.1 j valid).1 andGate
      · simp only [V,h,h',ite_false];exact (wire _).trans (andGate ▸ eval_and _ _)
    · left;funext t
      by_cases h : t=60
      · subst t; change D true (14+j) = (D true a || D true b);exact ((hd true).2.1 j valid).2 orGate
      by_cases h' : t=61
      · subst t; change D false (14+j) = (D false a || D false b);exact ((hd false).2.1 j valid).2 orGate
      · simp only [V,h,h',ite_false]; exact (wire _).trans (orGate ▸ eval_or _ _)
