import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.R_meta_3660_1
    (lowerKnown : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) x1 (14 : ℕ))
    (positiveTail : let f := fun x : Fin 9 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      ∀ C : Circuit, Monotone2 C → C.size = 13 → (∀ v ∈ ([9, 10] : List ℕ), ∃ g ∈ C.gates, v ∈ g.inputs) →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!(x 0), !(x 2)]) ≠ f x)
    (negatedTail : let f := fun x : Fin 9 → Bool =>
      (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
      (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
      (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
      ∀ C : Circuit, FanInTwo C → C.size = 13 → (∀ v ∈ ([9, 10] : List ℕ), ∃ g ∈ C.gates, v ∈ g.inputs) →
        (∃ g ∈ C.gates, g.op = GateOp.not) →
        (∀ g ∈ C.gates, g.op = GateOp.not →
          g.inputs.length ≤ 1 ∧ ∀ i ∈ g.inputs, i ∉ ([0, 2, 9, 10] : List ℕ)) →
        ∃ x : Fin 9 → Bool, C.eval (List.ofFn x ++ [!(x 0), !(x 2)]) ≠ f x) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (13 : ℕ) → ∃ (x4 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [!x4 (0 : Fin (9 : ℕ)), !x4 (2 : Fin (9 : ℕ))]) ≠ (x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) := by
  classical
  let f := fun x : Fin 9 → Bool =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  have lower : ¬ HasCircuitSize 9 f 14 := by
    rintro ⟨C,fan,budget,eval⟩
    apply lowerKnown
    refine ⟨C,fan,budget,?_⟩
    intro x
    rw [eval x]
    simp only [f, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc] <;> rfl
  let aug := fun x : Fin 9 → Bool => List.ofFn x ++ [!(x 0), !(x 2)]
  let vGate := fun (w : List Bool) (g : Gate) =>
    g.op.eval (g.inputs.map fun i => w.getD i false)
  let run := fun (gs : List Gate) (w : List Bool) =>
    gs.foldl (fun w g => w ++ [vGate w g]) w
  let mapGate := fun (r : ℕ → ℕ) (g : Gate) => Gate.mk g.op (g.inputs.map r)
  have rCons (g : Gate) (gs : List Gate) (w : List Bool) :
      run (g :: gs) w = run gs (w ++ [vGate w g]) := rfl
  have rAppend (a b : List Gate) (w : List Bool) :
      run (a++b) w = run b (run a w) := List.foldl_append
  have snocElse (w : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ w.length) :
      (w ++ [b]).getD i false = w.getD i false := by
    by_cases hp : i < w.length
    · exact List.getD_append _ _ _ _ hp
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have snocHere (w : List Bool) (b : Bool) :
      (w ++ [b]).getD w.length false = b := by simp
  have rLength (gs : List Gate) (w : List Bool) : (run gs w).length = w.length+gs.length := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [rCons, ih]
      simp
      omega
  have rKeep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
      (run gs w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [rCons, ih _ (by simp; omega)]
      exact snocElse _ _ _ (by omega)
  have rMap (s : ℕ → ℕ) (usable : ℕ → Prop) (gs : List Gate)
      (allowed : ∀ g ∈ gs, ∀ i ∈ g.inputs, usable i) (w v : List Bool)
      (init : ∀ i, usable i → v.getD (s i) false = w.getD i false)
      (future : ∀ k i, s i = v.length+k ↔ i=w.length+k) (i : ℕ) (hi : usable i) :
      (run (gs.map (mapGate s)) v).getD (s i) false = (run gs w).getD i false := by
    induction gs generalizing w v with
    | nil => exact init i hi
    | cons g gs ih =>
      have same : vGate v (mapGate s g) = vGate w g := by
        simp only [vGate,mapGate,List.map_map,Function.comp_def]
        apply congrArg g.op.eval
        apply List.map_congr_left
        intro j hj
        exact init j (allowed g List.mem_cons_self j hj)
      rw [List.map_cons, rCons, rCons, same]
      apply ih (fun a ha => allowed a (List.mem_cons_of_mem _ ha))
      · intro j hj
        by_cases eq : j=w.length
        · have es : s j=v.length := by simpa using (future 0 j).2 (by simpa)
          rw [es,eq,snocHere,snocHere]
        · have es : s j ≠ v.length := by simpa using mt (future 0 j).1 (by simpa)
          rw [snocElse _ _ _ eq,snocElse _ _ _ es,init j hj]
      · intro k j
        simpa [List.length_append,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using future (1+k) j

  let ok := fun g : Gate =>
    g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
  have remapOK (s : ℕ → ℕ) (g : Gate) (h : ok g) : ok (mapGate s g) := by
    simpa only [ok,mapGate,List.length_map] using h
  let n0 : Gate := ⟨GateOp.not,[0]⟩
  let n2 : Gate := ⟨GateOp.not,[2]⟩
  have ok0 : ok n0 := by simp [ok,n0,Set.mem_insert_iff,Set.mem_singleton_iff]
  have ok2 : ok n2 := by simp [ok,n2,Set.mem_insert_iff,Set.mem_singleton_iff]
  have inputRead (x : Fin 9 → Bool) (i : Fin 9) :
      (List.ofFn x).getD i.val false = x i := by
    rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
    simp only [List.getElem_ofFn]
  have n0Bank (x : Fin 9 → Bool) :
      run [n0] (List.ofFn x) = List.ofFn x ++ [!(x 0)] := by
    change List.ofFn x ++ [!((List.ofFn x).getD 0 false)] = _
    rw [show (List.ofFn x).getD 0 false = x 0 from inputRead x 0]
  have n2Bank (x : Fin 9 → Bool) :
      run [n2] (List.ofFn x) = List.ofFn x ++ [!(x 2)] := by
    change List.ofFn x ++ [!((List.ofFn x).getD 2 false)] = _
    rw [show (List.ofFn x).getD 2 false = x 2 from inputRead x 2]
  have bothBank (x : Fin 9 → Bool) : run [n0,n2] (List.ofFn x)=aug x := by
    have h2 : (List.ofFn x ++ [!(x 0)]).getD 2 false = x 2 := by
      rw [snocElse _ _ _ (by simp)]
      exact inputRead x 2
    rw [show [n0,n2] = [n0]++[n2] from rfl,rAppend,n0Bank]
    change (List.ofFn x ++ [!(x 0)]) ++ [!((List.ofFn x ++ [!(x 0)]).getD 2 false)] = _
    rw [h2]
    simp only [aug,List.append_assoc,List.singleton_append]
  have impossibleSmall (pre : List Gate) (C : Circuit)
      (good : ∀ g∈pre, ok g) (fan : FanInTwo C) (bud : pre.length+C.size ≤ 14)
      (computes : ∀ x : Fin 9 → Bool, C.eval (run pre (List.ofFn x)) = f x) : False := by
    let D : Circuit := ⟨pre++C.gates,C.output⟩
    apply lower
    refine ⟨D, ?_, ?_, ?_⟩
    · intro g hg
      change g ∈ pre++C.gates at hg
      rcases List.mem_append.mp hg with hp|hc
      · exact good g hp
      · exact fan g hc
    · change (pre++C.gates).length ≤ 14
      change pre.length+C.gates.length ≤ 14 at bud
      simpa only [List.length_append] using bud
    · intro x
      change (run (pre++C.gates) (List.ofFn x)).getD C.output false = _
      rw [rAppend]
      exact computes x
  have notSmall (C : Circuit) (fan : FanInTwo C) (bud : C.size ≤ 12)
      (computes : ∀ x : Fin 9 → Bool, C.eval (aug x)=f x) : False := by
    refine impossibleSmall [n0,n2] C ?_ fan (by simp; omega) ?_
    · intro g hg
      simp at hg
      rcases hg with rfl|rfl
      · exact ok0
      · exact ok2
    · intro x
      rw [bothBank]
      exact computes x

  let norm := fun g : Gate => if g.op=GateOp.not then Gate.mk g.op (g.inputs.take 1) else g
  have normVal (g : Gate) (w : List Bool) : vGate w (norm g) = vGate w g := by
    by_cases h : g.op=GateOp.not
    · simp only [norm,ite_eq_left h,vGate,h]
      cases g.inputs <;> rfl
    · simp only [norm,ite_eq_right h]
  have normRun (gs : List Gate) (w : List Bool) : run (gs.map norm) w = run gs w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih => rw [List.map_cons,rCons,rCons,normVal,ih]

  change ∀ C : Circuit, FanInTwo C → C.size ≤ 13 → ∃ x : Fin 9 → Bool, C.eval (aug x)≠f x
  intro C fan budget
  by_contra! eval
  let T : Circuit := ⟨C.gates.map norm,C.output⟩
  have goodT : FanInTwo T := by
    intro g hg
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    have h := fan a ha
    by_cases hn : a.op=GateOp.not
    · simpa only [norm,ite_eq_left hn,List.length_take,min_le_iff,true_or,Nat.one_le_ofNat,and_true] using h.1
    · simpa only [norm,ite_eq_right hn] using h
  have evalT (x : Fin 9 → Bool) : T.eval (aug x) = f x := by
    change (run (C.gates.map norm) (aug x)).getD C.output false=_
    rw [normRun]
    exact eval x
  have sizeT : T.size=13 := by
    have hs : T.size=C.size := by
      change (C.gates.map norm).length=C.gates.length
      simp
    by_contra h
    exact notSmall T goodT (by omega) evalT
  have unary (g : Gate) (hg : g∈T.gates) (hn : g.op=GateOp.not) : g.inputs.length ≤ 1 := by
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
    by_cases hn' : a.op=GateOp.not
    · simp only [norm,ite_eq_left hn',List.length_take]
      omega
    · simp only [norm,ite_eq_right hn'] at hn
      exact (hn' hn).elim

  have augLen (x : Fin 9 → Bool) : (aug x).length=11 := by simp [aug]
  have read0 (x : Fin 9 → Bool) : (aug x).getD 0 false=x 0 := by simp [aug]
  have read2 (x : Fin 9 → Bool) : (aug x).getD 2 false=x 2 := by simp [aug]
  have read9 (x : Fin 9 → Bool) : (aug x).getD 9 false= !(x 0) := by simp [aug]
  have read10 (x : Fin 9 → Bool) : (aug x).getD 10 false= !(x 2) := by simp [aug]

  have removeAlias (P Q : List Gate) (g : Gate) (split : T.gates=P++g::Q) (r : ℕ) (hr : r < 11)
      (sameValue : ∀ x : Fin 9 → Bool, vGate (run P (aug x)) g=(aug x).getD r false) :
      False := by
    let atWire := 11+P.length
    let shift := fun i : ℕ => if i=atWire then r else if atWire < i then i-1 else i
    let D : Circuit := ⟨P++Q.map (mapGate shift),shift T.output⟩
    have fD : FanInTwo D := by
      intro a ha
      change a∈P++Q.map (mapGate shift) at ha
      rcases List.mem_append.mp ha with hp|hq
      · exact goodT a (by rw [split]; exact List.mem_append_left _ hp)
      · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hq
        exact remapOK shift b (goodT b (by rw [split]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hb)))
    have sD : D.size ≤ 12 := by
      have n := sizeT
      change T.gates.length=13 at n
      rw [split,List.length_append,List.length_cons] at n
      change (P++Q.map (mapGate shift)).length ≤ 12
      simp only [List.length_append,List.length_map]
      omega
    apply notSmall D fD sD
    intro x
    let w := run P (aug x)
    have len : w.length=atWire := by simp [w,rLength,augLen,atWire]
    let value := vGate w g
    have valueAlias : value=w.getD r false := by
      exact (sameValue x).trans (rKeep P (aug x) r (by rwa [augLen])).symm
    have same (i : ℕ) : w.getD (shift i) false = (w++[value]).getD i false := by
      by_cases h : i=atWire
      · subst i
        have h1 : shift atWire=r := by simp [shift]
        rw [h1,← len,snocHere,valueAlias]
      · rw [snocElse _ _ _ (by omega)]
        by_cases hh : atWire < i
        · simp only [shift,ite_eq_right h,ite_eq_left hh]
          rw [List.getD_eq_default _ _ (by omega),List.getD_eq_default _ _ (by omega)]
        · simp [shift,h,hh]
    have future (k i : ℕ) : shift i=w.length+k ↔ i=(w++[value]).length+k := by
      simp only [len,shift,List.length_append,List.length_singleton]
      split_ifs <;> dsimp only [atWire] at * <;> omega
    have result := rMap shift (fun _ => True) Q (by intros; trivial) (w++[value]) w
      (fun i _ => same i) future T.output trivial
    change (run (P++Q.map (mapGate shift)) (aug x)).getD (shift T.output) false = _
    rw [rAppend]
    change (run (Q.map (mapGate shift)) w).getD (shift T.output) false=f x
    rw [result]
    have h := evalT x
    change (run T.gates (aug x)).getD T.output false=f x at h
    rwa [split,rAppend,rCons] at h

  have noBad (g : Gate) (hg : g∈T.gates) (hn : g.op=GateOp.not) :
      g.inputs.length ≤ 1 ∧ ∀ i ∈g.inputs, i∉([0,2,9,10] : List ℕ) := by
    refine ⟨unary g hg hn,?_⟩
    intro i hi forbidden
    have splitList (gs : List Gate) (has : g∈gs) : ∃ P Q, gs=P++g::Q := by
      induction gs with
      | nil => simp at has
      | cons a as ih =>
        rcases List.mem_cons.mp has with rfl | ha
        · exact ⟨[],as,rfl⟩
        · obtain ⟨P,Q,eq⟩ := ih ha
          exact ⟨a::P,Q,congrArg (List.cons a) eq⟩
    obtain ⟨P,Q,eq⟩ := splitList T.gates hg
    have hPins : g.inputs=[i] := by
      have h := unary g hg hn
      cases he : g.inputs with
      | nil => simp [he] at hi
      | cons a as =>
        have aNil : as=[] := by simpa [he] using h
        simp only [aNil,List.mem_singleton,he] at hi ⊢
        exact congrArg (fun x=>[x]) hi.symm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at forbidden
    have r (x : Fin 9 → Bool) (j : ℕ) (hj : j < 11) :
        (run P (aug x)).getD j false=(aug x).getD j false :=
      rKeep _ _ _ (by rwa [augLen])
    rcases forbidden with rfl|rfl|rfl|rfl
    · apply removeAlias P Q g eq 9 (by decide)
      intro x
      change g.op.eval (g.inputs.map _)=_
      rw [hPins,hn]
      change (!((run P (aug x)).getD 0 false)) = _
      rw [r x 0 (by decide),read0,read9]
    · apply removeAlias P Q g eq 10 (by decide)
      intro x
      change g.op.eval (g.inputs.map _)=_
      rw [hPins,hn]
      change (!((run P (aug x)).getD 2 false)) = _
      rw [r x 2 (by decide),read2,read10]
    · apply removeAlias P Q g eq 0 (by decide)
      intro x
      change g.op.eval (g.inputs.map _)=_
      rw [hPins,hn]
      change (!((run P (aug x)).getD 9 false)) = _
      rw [r x 9 (by decide),read9,read0,Bool.not_not]
    · apply removeAlias P Q g eq 2 (by decide)
      intro x
      change g.op.eval (g.inputs.map _)=_
      rw [hPins,hn]
      change (!((run P (aug x)).getD 10 false)) = _
      rw [r x 10 (by decide),read10,read2,Bool.not_not]

  have needed (j : ℕ) (hj : j∈([9,10] : List ℕ)) : ∃ g∈T.gates, j∈g.inputs := by
    have jCases : j=9 ∨ j=10 := by simpa using hj
    have jb : 9 ≤ j ∧ j ≤ 10 := by rcases jCases with rfl|rfl <;> decide
    by_contra avoid
    let s := fun i : ℕ => if i < j then i else i-1
    let pre := if j=9 then n2 else n0
    let D : Circuit := ⟨T.gates.map (mapGate s),s T.output⟩
    have preOK : ok pre := by
      dsimp [pre]
      split_ifs
      · exact ok2
      · exact ok0
    have fanD : FanInTwo D := by
      intro g hg
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
      exact remapOK s a (goodT a ha)
    have bud : [pre].length+D.size ≤ 14 := by
      have h : D.size=T.size := by
        change (T.gates.map (mapGate s)).length=T.gates.length
        simp
      simp only [List.length_singleton]
      omega
    have out : T.output ≠ j := by
      intro eq
      let x : Fin 9 → Bool := fun _ => false
      have h := evalT x
      change (run T.gates (aug x)).getD T.output false = false at h
      rw [eq, rKeep _ _ _ (by rw [augLen]; omega)] at h
      rcases jCases with rfl|rfl
      · rw [read9] at h
        exact (by decide : true ≠ false) h
      · rw [read10] at h
        exact (by decide : true ≠ false) h
    have goodPre : ∀ g∈[pre], ok g := by
      intro g hg
      have eq := List.mem_singleton.mp hg
      subst g
      exact preOK
    apply impossibleSmall [pre] D goodPre fanD bud
    intro x
    let v := run [pre] (List.ofFn x)
    have vlen : v.length=10 := by simp [v,rLength]
    have same (i : ℕ) (hi : i ≠ j) : v.getD (s i) false=(aug x).getD i false := by
      by_cases h : i < 9
      · have ss : s i=i := by simp [s,show i < j by omega]
        rw [ss]
        change (run [pre] (List.ofFn x)).getD i false = _
        rw [rKeep _ _ _ (by simpa using h)]
        symm
        exact List.getD_append _ _ _ _ (by simpa using h)
      · by_cases hLarge : 11 ≤ i
        · have ss : s i=i-1 := by simp [s,show ¬i < j by omega]
          rw [ss,List.getD_eq_default _ _ (by omega),
            List.getD_eq_default _ _ (by rw [augLen]; omega)]
        · rcases jCases with rfl|rfl
          · have eq : i=10 := by omega
            subst i
            change (run [n2] (List.ofFn x)).getD 9 false=(aug x).getD 10 false
            rw [n2Bank,read10]
            exact snocHere (List.ofFn x) (!(x 2))
          · have eq : i=9 := by omega
            subst i
            change (run [n0] (List.ofFn x)).getD 9 false=(aug x).getD 9 false
            rw [n0Bank,read9]
            exact snocHere (List.ofFn x) (!(x 0))
    have future (k i : ℕ) : s i=v.length+k ↔ i=(aug x).length+k := by
      rw [vlen,augLen]
      simp only [s]
      split_ifs <;> omega
    have permitted (g : Gate) (hg : g∈T.gates) (i : ℕ) (hi : i∈g.inputs) : i ≠ j := by
      intro eq
      subst i
      exact avoid ⟨g,hg,hi⟩
    change (run (T.gates.map (mapGate s)) v).getD (s T.output) false = _
    exact (rMap s (fun i=>i ≠ j) T.gates permitted (aug x) v same future T.output out).trans (evalT x)
  by_cases existsNeg : ∃ g∈T.gates,g.op=GateOp.not
  · obtain ⟨x,hx⟩ := negatedTail T goodT sizeT needed existsNeg noBad
    exact hx (evalT x)
  · have mono : Monotone2 T := by
      intro g hg
      have h := goodT g hg
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h ⊢
      exact ⟨h.1.imp_right (fun ho => ho.resolve_right (fun hn => existsNeg ⟨g,hg,hn⟩)),h.2⟩
    obtain ⟨x,hx⟩ := positiveTail T mono sizeT needed
    exact hx (evalT x)
