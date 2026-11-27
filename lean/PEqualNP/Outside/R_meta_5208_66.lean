import PEqualNP.Defs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge

-- PR 9379 establishes the unmarked 65-leaf bound on this incidence function.
-- The two repeated labels force a sixty-sixth leaf in the full output unfolding.
-- Each gate appends its formula, cost, and value to the corresponding wire table.
theorem PEqualNP.Outside.R_meta_5208_66
    (tree : let D : Finset (Fin 13) := {0,1,3,9}; ∀ f : DMFormula 26, (DMFormula.rec (motive := fun _ : DMFormula 26 => Prop)
      (fun _ s => s = true) (fun _ _ a b => a ∧ b) (fun _ _ a b => a ∧ b)) f →
      (∀ x, f.eval x = true ↔ (fun x : Fin 26 → Bool => ∃ p l : Fin 13, p-l ∈ D ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) x) →
      let reads := (fun (v : Fin 26) (ψ : DMFormula 26) => DMFormula.rec (motive := fun _ : DMFormula 26 => Nat)
      (fun w _ => if w = v then 1 else 0) (fun _ _ a b => a+b) (fun _ _ a b => a+b) ψ);
      2 ≤ reads 0 f → 2 ≤ reads 13 f → 66 ≤ f.leaves)
    (shared : let D : Finset (Fin 13) := {0,1,3,9}; ¬∃ C : Circuit,
      let hit (k : Nat) (a : Fin 26) := (gateAt C k).op = GateOp.and ∧
        (26+k = C.output ∨ InCone 26 C k (C.output-26)) ∧
        gateVal 26 C k (pairInput 0 13) = true ∧
        ∀ b : Fin 2, wireVal 26 C (opnd C k b) (pairInput a a) = false;
      C.size ≤ 64 ∧ 66 ≤ (C.gates.foldl (fun (w : List Nat) (g : Gate) => w ++ [(g.inputs.map fun i => w.getD i 0).sum]) (List.replicate 26 1)).getD C.output 0 ∧
      PEqualNP.TopForm.IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧ (∀ x, C.eval (List.ofFn x) = true ↔ (fun x : Fin 26 → Bool => ∃ p l : Fin 13, p-l ∈ D ∧
      x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) x) ∧
      (∃ d < C.gates.length, (gateAt C d).op = GateOp.and ∧ ∃ x, gateVal 26 C d x = true ∧ C.eval (List.ofFn x) = false) ∧
      ∃ j k, InCone 26 C j k ∧ hit j 0 ∧ hit k 13) :
    ¬∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit),     have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};
      have x3 : PEqualNP.CircuitLowerBounds.GateOp := PEqualNP.CircuitLowerBounds.GateOp.and;
      have x4 : ℕ → ℕ → Prop := PEqualNP.EdgeOwnership.InCone (26 : ℕ) x1;
      have x5 : ℕ → (Fin (26 : ℕ) → Bool) → Bool := PEqualNP.EdgeOwnership.gateVal (26 : ℕ) x1;
      have x6 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (0 : Fin (26 : ℕ));
      have x7 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (13 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));
      have x8 : Fin (26 : ℕ) → Bool := PEqualNP.EdgeOwnership.pairInput (0 : Fin (26 : ℕ)) (13 : Fin (26 : ℕ));
      have x9 : ℕ → (Fin (26 : ℕ) → Bool) → Prop := fun (x9 : ℕ) (x10 : Fin (26 : ℕ) → Bool) => (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x9).op = x3 ∧ ((26 : ℕ) + x9 = x1.output ∨ x4 x9 (x1.output - (26 : ℕ))) ∧ x5 x9 x8 = Bool.true ∧ ∀ (x11 : Fin (2 : ℕ)), PEqualNP.CleanedNonEdge.wireVal (26 : ℕ) x1 (PEqualNP.TopForm.opnd x1 x9 x11) x10 = Bool.false;
      x1.size ≤ (64 : ℕ) ∧
      (∀ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x10]? = Option.some x11 → (x11.op = x3 ∨ x11.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x13 : ℕ) (x14 : ℕ), x11.inputs = [x13, x14] ∧ x13 ≠ x14 ∧ x13 < (26 : ℕ) + x10 ∧ x14 < (26 : ℕ) + x10) ∧
      (∀ (x10 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x10) = Bool.true ↔ ∃ (x11 : Fin (13 : ℕ)) (x12 : Fin (13 : ℕ)), x11 - x12 ∈ x2 ∧ x10 (Fin.castAdd (13 : ℕ) x11) = Bool.true ∧ x10 (Fin.natAdd (13 : ℕ) x12) = Bool.true) ∧
      (∃ x10 < x1.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x1 x10).op = x3 ∧ ∃ (x11 : Fin (26 : ℕ) → Bool), x5 x10 x11 = Bool.true ∧ x1.eval (List.ofFn x11) = Bool.false) ∧ ∃ (x10 : ℕ) (x11 : ℕ), x4 x10 x11 ∧ x9 x10 x6 ∧ x9 x11 x7 := by
  rintro ⟨C, h⟩
  dsimp only at h
  obtain ⟨size, shape, computes, dirty, j, k, nested, one, two⟩ := h
  let positive := DMFormula.rec (motive := fun _ : DMFormula 26 => Prop)
      (fun _ s => s = true) (fun _ _ a b => a ∧ b) (fun _ _ a b => a ∧ b)
  let reads := fun (v : Fin 26) (ψ : DMFormula 26) => DMFormula.rec (motive := fun _ : DMFormula 26 => Nat)
      (fun w _ => if w = v then 1 else 0) (fun _ _ a b => a+b) (fun _ _ a b => a+b) ψ
  let weight := fun (w : List Nat) (g : Gate) => w ++ [(g.inputs.map fun i => w.getD i 0).sum]
  let scan {A : Type} (emit : List A → Gate → A) (seed : List A) (gs : List Gate) :=
    gs.foldl (fun w g => w ++ [emit w g]) seed
  have lengthScan {A : Type} (emit : List A → Gate → A) (gs : List Gate) (seed : List A) :
      (scan emit seed gs).length = seed.length + gs.length := by
    induction gs generalizing seed with
    | nil => simp only [scan,List.foldl_nil,List.length_nil,Nat.add_zero]
    | cons g gs ih =>
      change (scan emit (seed ++ [emit seed g]) gs).length = _
      rw [ih]
      simp only [List.length_append,List.length_cons,List.length_nil]
      omega
  have stable {A : Type} (emit : List A → Gate → A) (gs : List Gate) (seed : List A) (d : A) (w : Nat)
      (hw : w < seed.length) : (scan emit seed gs).getD w d = seed.getD w d := by
    induction gs generalizing seed with
    | nil => rfl
    | cons g gs ih =>
      change (scan emit (seed ++ [emit seed g]) gs).getD w d = _
      rw [ih _ (by simp only [List.length_append,List.length_cons,List.length_nil]; omega)]
      exact List.getD_append _ _ _ _ hw
  have step {A : Type} (emit : List A → Gate → A) (gs : List Gate) (seed : List A) (d : A)
      (t : Nat) (ht : t < gs.length) :
      let prior := scan emit seed (gs.take t)
      (scan emit seed gs).getD (seed.length+t) d = emit prior gs[t] ∧
      ∀ a < seed.length+t, (scan emit seed gs).getD a d = prior.getD a d := by
    let pre := scan emit seed (gs.take t)
    have len : pre.length = seed.length+t := by
      simp only [pre,lengthScan,List.length_take,Nat.min_eq_left ht.le]
    have parts : gs.take t ++ gs[t] :: gs.drop (t+1) = gs := by
      rw [← List.drop_eq_getElem_cons ht,List.take_append_drop]
    have decomp : scan emit seed gs = scan emit (pre ++ [emit pre gs[t]]) (gs.drop (t+1)) := by
      conv_lhs => rw [← parts]
      exact List.foldl_append
    dsimp only
    rw [decomp]
    constructor
    · rw [stable _ _ _ _ _ (by simp only [List.length_append,List.length_cons,List.length_nil,len]; omega)]
      rw [List.getD_append_right _ _ _ _ (by omega),len,Nat.sub_self]
      rfl
    · intro a ha
      rw [stable _ _ _ _ _ (by simp only [List.length_append,List.length_cons,List.length_nil,len]; omega)]
      exact List.getD_append _ _ _ _ (by omega)
  let dummy := DMFormula.lit (0 : Fin 26) true
  let make (w : List (DMFormula 26)) (g : Gate) :=
    let lhs := w.getD (g.inputs.getD 0 0) dummy
    let rhs := w.getD (g.inputs.getD 1 0) dummy
    if g.op.eval [false,true] then lhs.or rhs else lhs.and rhs
  let raw := List.ofFn (fun v : Fin 26 => DMFormula.lit v true)
  let f (a : Nat) := (scan make raw C.gates).getD a dummy
  let cost (a : Nat) := (C.gates.foldl weight (List.replicate 26 1)).getD a 0
  let wire (x : Fin 26 → Bool) (a : Nat) := (C.wires (List.ofFn x)).getD a false
  let value (xs : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun a => xs.getD a false)
  let count (xs : List Nat) (g : Gate) := (g.inputs.map fun a => xs.getD a 0).sum
  let combine (b : Bool) (u v : DMFormula 26) := if b then u.or v else u.and v
  have recs (t : Nat) (ht : t < C.gates.length) :
      ∃ a b : Nat, (gateAt C t).inputs = [a,b] ∧ a ≠ b ∧ a < 26+t ∧ b < 26+t ∧
        let isOr := (gateAt C t).op.eval [false,true]
        f (26+t) = combine isOr (f a) (f b) ∧ cost (26+t) = cost a + cost b ∧
        ∀ x, wire x (26+t) = if isOr then wire x a || wire x b else wire x a && wire x b := by
    let g := C.gates[t]
    have eg : gateAt C t = g := List.getD_eq_getElem _ _ ht
    obtain ⟨op,a,b,hargs,ne,ha,hb⟩ := shape t g (by simp only [g,List.getElem?_eq_getElem ht])
    rw [eg]
    refine ⟨a,b,hargs,ne,ha,hb,?_,?_,?_⟩
    · obtain ⟨curr,prev⟩ := step make C.gates raw dummy t ht
      simp only [raw,List.length_ofFn] at curr prev
      change (scan make raw C.gates).getD (26+t) dummy = _
      rw [curr]
      change make (scan make raw (C.gates.take t)) g = _
      dsimp only [make]
      rw [hargs]
      change combine _ ((scan make raw (C.gates.take t)).getD a dummy) ((scan make raw (C.gates.take t)).getD b dummy) = _
      rw [← prev a ha,← prev b hb]
    · obtain ⟨curr,prev⟩ := step count C.gates (List.replicate 26 1) 0 t ht
      simp only [List.length_replicate] at curr prev
      change (scan count (List.replicate 26 1) C.gates).getD (26+t) 0 = _
      rw [curr]
      change ((g.inputs.map fun a => (scan count (List.replicate 26 1) (C.gates.take t)).getD a 0).sum) = _
      rw [hargs]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,← prev a ha,← prev b hb]
      rfl
    · intro x
      obtain ⟨curr,prev⟩ := step value C.gates (List.ofFn x) false t ht
      simp only [List.length_ofFn] at curr prev
      change (scan value (List.ofFn x) C.gates).getD (26+t) false = _
      rw [curr]
      let xs := scan value (List.ofFn x) (C.gates.take t)
      change g.op.eval (g.inputs.map fun z => xs.getD z false) = _
      rw [hargs]
      have ea (o : GateOp) (u v : Bool) (h : o = GateOp.and ∨ o = GateOp.or) :
          o.eval [u,v] = if o.eval [false,true] then u || v else u && v := by
        rcases h with rfl|rfl <;> cases u <;> cases v <;> rfl
      change g.op.eval [xs.getD a false,xs.getD b false] = _
      rw [ea _ _ _ op]
      change (if _ then xs.getD a false || xs.getD b false else xs.getD a false && xs.getD b false) = _
      rw [show xs.getD a false = wire x a from (prev a ha).symm,show xs.getD b false = wire x b from (prev b hb).symm]
  have readLaw (i : Fin 26) (d : Bool) (u v : DMFormula 26) :
      reads i (combine d u v) = reads i u + reads i v := by cases d <;> rfl
  have repr (w : Nat) (hw : w < 26+C.gates.length) :
      positive (f w) ∧ (f w).leaves = cost w ∧ ∀ x, (f w).eval x = wire x w := by
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      by_cases h : w < 26
      · let i : Fin 26 := ⟨w,h⟩
        have eqn : f w = DMFormula.lit i true := by
          change (scan make raw C.gates).getD w dummy = _
          rw [stable _ _ _ _ _ (by simpa only [raw,List.length_ofFn] using h)]
          rw [List.getD_eq_getElem _ _ (by simpa only [raw,List.length_ofFn] using h)]
          exact List.getElem_ofFn ..
        rw [eqn]
        refine ⟨rfl,?_,?_⟩
        · change 1 = (scan count (List.replicate 26 1) C.gates).getD w 0
          rw [stable _ _ _ _ _ (by simpa only [List.length_replicate] using h)]
          rw [List.getD_eq_getElem _ _ (by simpa only [List.length_replicate] using h),List.getElem_replicate]
        · intro x
          change x i = (scan value (List.ofFn x) C.gates).getD w false
          rw [stable _ _ _ _ _ (by simpa only [List.length_ofFn] using h)]
          rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h),List.getElem_ofFn]
      · let t := w-26
        have e : w = 26+t := by dsimp [t]; omega
        have ht : t < C.gates.length := by omega
        obtain ⟨a,b,_,_,ha,hb,ff,cc,ev⟩ := recs t ht
        obtain ⟨pa,ca,va⟩ := ih a (by omega) (by omega)
        obtain ⟨pb,cb,vb⟩ := ih b (by omega) (by omega)
        rw [e,ff,cc]
        cases hi : (gateAt C t).op.eval [false,true] <;> refine ⟨⟨pa,pb⟩,?_,?_⟩
        all_goals first | exact congrArg₂ (·+·) ca cb | (intro x; rw [ev,hi,← va,← vb]; rfl)
  let dep (cs : List (List Nat)) (g : Gate) :=
    (g.inputs.filter (fun w => decide (26 ≤ w ∧ w < 26 + cs.length))).flatMap
      (fun w => (w-26) :: cs.getD (w-26) [])
  have cone (s t : Nat) (h : InCone 26 C s t) :
      t < C.gates.length ∧ ∃ w, w ∈ (gateAt C t).inputs ∧ 26 ≤ w ∧ w < 26+t ∧
        (s = w-26 ∨ InCone 26 C s (w-26)) := by
    change s ∈ (scan dep [] C.gates).getD t [] at h
    have ht : t < C.gates.length := by
      by_contra! bad
      rw [List.getD_eq_default _ _ (by simpa only [lengthScan,List.length_nil,Nat.zero_add] using bad)] at h
      contradiction
    obtain ⟨curr,prev⟩ := step dep C.gates [] [] t ht
    simp only [List.length_nil,Nat.zero_add] at curr prev
    rw [curr] at h
    have here : gateAt C t = C.gates[t] := List.getD_eq_getElem _ _ ht
    rw [← here] at h
    dsimp only [dep] at h
    obtain ⟨w,hw,found⟩ := List.mem_flatMap.mp h
    obtain ⟨member,lo,upper⟩ := List.mem_filter.mp hw |>.imp_right of_decide_eq_true
    have high : w < 26+t := by
      simpa only [lengthScan,List.length_nil,Nat.zero_add,List.length_take,Nat.min_eq_left ht.le] using upper
    refine ⟨ht,w,member,lo,high,?_⟩
    rcases List.mem_cons.mp found with hit | next
    · exact Or.inl hit
    · right
      change s ∈ (scan dep [] C.gates).getD (w-26) []
      rw [prev _ (by omega)]
      exact next
  have grows (v : Fin 26) (s t : Nat) (h : InCone 26 C s t) :
      reads v (f (26+s)) ≤ reads v (f (26+t)) := by
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      obtain ⟨ht,w,member,lo,high,hit⟩ := cone s t h
      obtain ⟨a,b,args,_,_,_,ff,_,_⟩ := recs t ht
      rw [args] at member
      have above : reads v (f (26+s)) ≤ reads v (f (26+(w-26))) :=
        hit.elim (fun e => e ▸ Nat.le_refl _) (ih _ (by omega))
      have eqw : 26+(w-26) = w := by omega
      rw [eqw] at above
      rw [ff,readLaw]
      rcases List.mem_cons.mp member with rfl | rr
      · omega
      · obtain rfl := List.mem_singleton.mp rr
        omega
  have stableEval (φ : DMFormula 26) (v : Fin 26) (x y : Fin 26 → Bool) (agree : ∀ i, i ≠ v → x i = y i)
      (missing : reads v φ = 0) : φ.eval x = φ.eval y := by
    induction φ with
    | lit i s =>
      have ne : i ≠ v := by
        rintro rfl
        change (if i = i then 1 else 0) = (0 : Nat) at missing
        simp only [ite_true] at missing
        contradiction
      change (if s then x i else !x i) = (if s then y i else !y i)
      rw [agree i ne]
    | and u v' ih jh =>
      change reads v u + reads v v' = 0 at missing
      change (u.eval x && v'.eval x) = (u.eval y && v'.eval y)
      rw [ih (by omega),jh (by omega)]
    | or u v' ih jh =>
      change reads v u + reads v v' = 0 at missing
      change (u.eval x || v'.eval x) = (u.eval y || v'.eval y)
      rw [ih (by omega),jh (by omega)]
  have existsGate (t : Nat) (ht : (gateAt C t).op = GateOp.and) : t < C.gates.length := by
    by_contra! h
    change (C.gates.getD t ⟨GateOp.or,[]⟩).op = GateOp.and at ht
    rw [List.getD_eq_default _ _ h] at ht
    contradiction
  have markTwice (t : Nat) (v a : Fin 26)
      (agree : ∀ i : Fin 26, i ≠ v → pairInput (0 : Fin 26) 13 i = pairInput a a i)
      (op : (gateAt C t).op = GateOp.and)
      (live : 26+t = C.output ∨ InCone 26 C t (C.output-26))
      (on : gateVal 26 C t (pairInput 0 13) = true)
      (off : ∀ b : Fin 2, wireVal 26 C (opnd C t b) (pairInput a a) = false) :
      C.output < 26+C.gates.length ∧ 2 ≤ reads v (f C.output) := by
    have ht := existsGate t op
    obtain ⟨u,w,args,_,hu,hw,ff,_,ev⟩ := recs t ht
    have isAnd : (gateAt C t).op.eval [false,true] = false := op ▸ rfl
    have both : wire (pairInput 0 13) u = true ∧ wire (pairInput 0 13) w = true := by
      change wire (pairInput 0 13) (26+t) = true at on
      rw [ev,isAnd] at on
      exact Bool.and_eq_true_iff.mp on
    have opnd0 : opnd C t 0 = u := by change (gateAt C t).inputs.getD 0 0 = u; rw [args]; rfl
    have opnd1 : opnd C t 1 = w := by change (gateAt C t).inputs.getD 1 0 = w; rw [args]; rfl
    have costs (z : Nat) (hz : z < 26+t) (hi : wire (pairInput 0 13) z = true)
        (lo : wire (pairInput a a) z = false) : 1 ≤ reads v (f z) := by
      by_contra! few
      have eqn := stableEval (f z) v _ _ agree (by omega)
      have econ := (repr z (by omega)).2.2
      rw [econ,econ,hi,lo] at eqn
      contradiction
    have lu := costs u hu both.1 (opnd0 ▸ off 0)
    have lw := costs w hw both.2 (opnd1 ▸ off 1)
    have atGate : 2 ≤ reads v (f (26+t)) := by rw [ff,readLaw]; omega
    rcases live with e | follow
    · exact ⟨by omega, e ▸ atGate⟩
    · obtain ⟨lt,w',_,lo,hi,_⟩ := cone t _ follow
      have out := atGate.trans (grows v _ _ follow)
      have eqn : 26+(C.output-26) = C.output := by omega
      exact ⟨by omega,eqn ▸ out⟩
  have p := markTwice k 0 13 (by decide +kernel) two.1 two.2.1 two.2.2.1 two.2.2.2
  have l := markTwice j 13 0 (by decide +kernel) one.1 one.2.1 one.2.2.1 one.2.2.2
  obtain ⟨mono,leaves,values⟩ := repr C.output p.1
  have large := tree (f C.output) mono (fun x => (values x) ▸ computes x) p.2 l.2
  have gates (g : Gate) (hg : g ∈ C.gates) :
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧ g.inputs.Nodup := by
    obtain ⟨t,he⟩ := List.mem_iff_getElem?.mp hg
    obtain ⟨op,a,b,args,ne,_,_⟩ := shape t g he
    exact ⟨op,args ▸ rfl,by rw [args]; simp [ne]⟩
  have ao : IsAO2 26 C := by
    refine ⟨fun g hg => (gates _ hg).1, ?_, fun g hg => (gates _ hg).2.1⟩
    intro t ht u hu
    have hg : C.gates[t]? = some C.gates[t] := List.getElem?_eq_getElem ht
    obtain ⟨_,a,b,args,_,ha,hb⟩ := shape t _ hg
    change u ∈ (C.gates.getD t ⟨GateOp.or,[]⟩).inputs at hu
    rw [List.getD_eq_getElem _ _ ht,args] at hu
    rcases List.mem_cons.mp hu with rfl | uin
    · exact ha
    · exact (List.mem_singleton.mp uin) ▸ hb
  have high : 66 ≤ cost C.output := large.trans leaves.le
  exact shared ⟨C,size,high,ao,fun g hg => (gates _ hg).2.2,computes,dirty,j,k,nested,one,two⟩
