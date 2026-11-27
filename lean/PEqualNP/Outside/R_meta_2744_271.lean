import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 2500000 in
set_option maxRecDepth 12000 in
theorem PEqualNP.Outside.R_meta_2744_271
    (normalize :
      let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      let w := fun x : Fin 9 → Bool => List.ofFn x ++ [x 4 || x 6]
      let good (i : ℕ) (g : Gate) := (∀ p ∈ g.inputs, p < 10+i) ∧
        (g.op = .not ∧ g.inputs.length = 1 ∨ (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
      ∀ (gs : List Gate) (o : ℕ), FanInTwo ⟨gs,0⟩ →
        (∀ x, ((Circuit.mk gs 0).wires (w x)).getD o false = f x) →
        ∃ (hs : List Gate) (out : ℕ), hs.length ≤ gs.length ∧ out < 10+hs.length ∧
          (∀ (i : ℕ) (g : Gate), hs[i]? = some g → good i g) ∧
          ∀ x, ((Circuit.mk hs 0).wires (w x)).getD out false = f x)
    (lower :
      let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      ∀ C : Circuit, FanInTwo C → (∀ x, C.eval (List.ofFn x) = f x) →
        15 ≤ C.size ∧ 13 ≤ (C.gates.filter fun g => !(g.op.eval [false,false])).length)
    (readers :
      let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      let read (v : ℕ) (g : Gate) := g.inputs[0]? = some v ∨ g.op ≠ GateOp.not ∧ v ∈ g.inputs
      ∀ C : Circuit, FanInTwo C →
        (∀ x : Fin 9 → Bool, (C.wires (List.ofFn x)).getD 9 false = (x 4 || x 6)) →
        (∀ x, C.eval (List.ofFn x) = f x) → C.size ≤ 15 →
        ∀ v ∈ ([4,6] : List ℕ), ∃! i : Fin (C.gates.drop 1).length, read v ((C.gates.drop 1).get i))
    (search :
      let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
        fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
      let good (i : ℕ) (g : Gate) := (∀ p ∈ g.inputs, p < 10+i) ∧
        (g.op = .not ∧ g.inputs.length = 1 ∨ (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
      ∀ gs : List Gate, gs.length = 14 → (∀ (i : ℕ) (g : Gate), gs[i]? = some g → good i g) →
        (gs.filter fun g => g.op.eval [false,false]).length ≤ 2 →
        (∀ v ∈ ([4,6] : List ℕ), ∃! i : Fin gs.length, v ∈ (gs.get i).inputs) →
        (∀ g ∈ gs, 4 ∈ g.inputs → 6 ∉ g.inputs) →
        (∀ g : Gate, gs[13]? = some g → g.op ≠ GateOp.not) →
        ∃ x : Fin 9 → Bool, ((Circuit.mk gs 0).wires (List.ofFn x ++ [x 4 || x 6])).getD 23 false ≠ f x) :
∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x3)).getD (9 : ℕ) Bool.false = (x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x4 : Fin (9 : ℕ) → Bool) => x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) → (∃ (x5 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[(1 : ℕ)]? = Option.some x5) → (16 : ℕ) ≤ x1.size := by
  intro C legal headWire computes existsSecond
  by_contra! small
  let f := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
    fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))
  let w := fun x : Fin 9 → Bool => List.ofFn x ++ [x 4 || x 6]
  let run (gs : List Gate) (row : List Bool) := (Circuit.mk gs 0).wires row
  have lookup (l : List Bool) (a : Bool) (i : ℕ) (hi : i < l.length) :
      (l ++ [a]).getD i false = l.getD i false := List.getD_append _ _ _ _ hi
  have atEnd (l : List Bool) (a : Bool) : (l ++ [a]).getD l.length false = a := by simp
  have retain (gs : List Gate) (z : List Bool) (i : ℕ) (hi : i < z.length) :
      (run gs z).getD i false = z.getD i false := by
    induction gs generalizing z with
    | nil => rfl
    | cons g gs ih =>
      let bit := g.op.eval (g.inputs.map fun p => z.getD p false)
      change (run gs (z ++ [bit])).getD i false = _
      rw [ih _ (by simp; omega)]
      exact lookup z bit i hi
  have lengthRun (gs : List Gate) (z : List Bool) : (run gs z).length = z.length+gs.length := by
    induction gs generalizing z with
    | nil => simp [run]; rfl
    | cons g gs ih =>
      let bit := g.op.eval (g.inputs.map fun p => z.getD p false)
      change (run gs (z ++ [bit])).length = _
      rw [ih]
      simp
      omega
  have runAppend (gs hs : List Gate) (z : List Bool) : run (gs ++ hs) z = run hs (run gs z) := by
    change List.foldl _ z (gs ++ hs) = List.foldl _ (List.foldl _ z gs) hs
    rw [List.foldl_append]
  have allAgree (x : Fin 9 → Bool) : C.eval (List.ofFn x) = f x := by
    have h := congrFun computes x
    change C.eval (List.ofFn x) = _ at h
    simp only [f,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc] at h ⊢
    exact h
  obtain ⟨gates,o⟩ := C
  rcases gates with _ | ⟨g,tail⟩
  · obtain ⟨g,h⟩ := existsSecond
    cases h
  have budget : tail.length ≤ 14 := by
    change (g :: tail).length < 16 at small
    simp only [List.length_cons] at small
    omega
  have tailFan : FanInTwo ⟨tail,0⟩ := by
    intro j hj
    exact legal j (List.mem_cons_of_mem g hj)
  have peel (x : Fin 9 → Bool) : (run tail (w x)).getD o false = f x := by
    let start := List.ofFn x
    let val := g.op.eval (g.inputs.map fun i => start.getD i false)
    have first := headWire x
    change (run tail (start ++ [val])).getD 9 false = _ at first
    rw [retain _ _ _ (by simp [start])] at first
    have nine : start.length = 9 := by simp [start]
    have atNine : (start ++ [val]).getD 9 false = val := by simpa only [nine] using atEnd start val
    rw [atNine] at first
    have agreement := allAgree x
    change (run tail (start ++ [val])).getD o false = _ at agreement
    rw [first] at agreement
    exact agreement
  obtain ⟨gs,out,cap,valid,clean,agrees⟩ := normalize tail o tailFan peel
  let first : Gate := ⟨.or,[4,6]⟩
  let D : Circuit := ⟨first :: gs,out⟩
  have input_bit_from_list (x : Fin 9 → Bool) (p : Fin 9) :
      (List.ofFn x).getD p.val false = x p := by
    have hi : p.val < (List.ofFn x).length := by simpa using p.isLt
    rw [List.getD_eq_getElem _ _ hi,List.getElem_ofFn]
  have firstEval (x : Fin 9 → Bool) :
      first.op.eval (first.inputs.map fun i => (List.ofFn x).getD i false) = (x 4 || x 6) := by
    change GateOp.or.eval [(List.ofFn x).getD (4:ℕ) false,(List.ofFn x).getD (6:ℕ) false] = _
    have a : (List.ofFn x).getD 4 false = x 4 := input_bit_from_list x 4
    have b : (List.ofFn x).getD 6 false = x 6 := input_bit_from_list x 6
    rw [a,b]
    cases x 4 <;> cases x 6 <;> rfl
  have fan : FanInTwo D := by
    intro h mem
    change h ∈ first :: gs at mem
    rcases List.mem_cons.mp mem with rfl | rest
    · exact ⟨Or.inr (Or.inl rfl),by decide⟩
    · obtain ⟨p,hp⟩ := List.mem_iff_getElem?.mp rest
      rcases (clean p h hp).2 with ⟨op,arity⟩ | ⟨op,arity⟩
      · exact ⟨Or.inr (Or.inr op),by omega⟩
      · exact ⟨op.elim Or.inl (fun h => Or.inr (Or.inl h)),by omega⟩
  have target (x : Fin 9 → Bool) : D.eval (List.ofFn x) = f x := by
    change (run gs (List.ofFn x ++ [first.op.eval _])).getD out false = _
    rw [firstEval]
    exact agrees x
  have seed (x : Fin 9 → Bool) : (D.wires (List.ofFn x)).getD 9 false = (x 4 || x 6) := by
    let raw := List.ofFn x
    change (run gs (raw ++ [first.op.eval _])).getD 9 false = _
    rw [firstEval,retain _ _ _ (by simp [raw])]
    have n : raw.length = 9 := by simp [raw]
    simpa only [n] using atEnd raw (x 4 || x 6)
  have minimum := lower D fan target
  have dsize : D.size = gs.length+1 := rfl
  have exactly : gs.length = 14 := by have := minimum.1; omega
  have atLast : out = 23 := by
    by_contra! notLast
    have bound : out < 23 := by omega
    let k := out+1-9
    let pre := D.gates.take k
    let short : Circuit := ⟨pre,out⟩
    have preLen : pre.length = k := by
      change (D.gates.take k).length = k
      rw [List.length_take]
      change min k (first :: gs).length = k
      apply Nat.min_eq_left
      simp only [List.length_cons]
      dsimp [k]
      omega
    have shortFan : FanInTwo short := fun j hj => fan j (List.mem_of_mem_take hj)
    have shortTarget (x : Fin 9 → Bool) : short.eval (List.ofFn x) = f x := by
      have eq := target x
      change (run D.gates (List.ofFn x)).getD out false = _ at eq
      have split : pre ++ D.gates.drop k = D.gates := List.take_append_drop k D.gates
      rw [← split,runAppend,retain _ _ _ (by rw [lengthRun,preLen,List.length_ofFn]; dsimp [k]; omega)] at eq
      exact eq
    have impossible := (lower short shortFan shortTarget).1
    change 15 ≤ pre.length at impossible
    rw [preLen] at impossible
    dsimp [k] at impossible
    omega
  let isNot (g : Gate) := g.op.eval [false,false]
  have partition (ls : List Gate) : (ls.filter fun g => !isNot g).length + (ls.filter isNot).length = ls.length := by
    induction ls with
    | nil => rfl
    | cons g ls ih => cases h : isNot g <;> simp [h] <;> omega
  have many := minimum.2
  change 13 ≤ ((first :: gs).filter fun g => !isNot g).length at many
  have leading : (!isNot first) = true := rfl
  rw [List.filter_cons,leading] at many
  simp only [List.length_cons,if_true] at many
  have count : (gs.filter isNot).length ≤ 2 := by have tally := partition gs; omega
  have unique (v : ℕ) (hv : v ∈ ([4,6] : List ℕ)) : ∃! i : Fin gs.length, v ∈ (gs.get i).inputs := by
    have only := readers D fan seed target (by rw [dsize,exactly]) v hv
    change ∃! i : Fin gs.length, (gs.get i).inputs[0]? = some v ∨
      (gs.get i).op ≠ GateOp.not ∧ v ∈ (gs.get i).inputs at only
    have equiv (i : Fin gs.length) : ((gs.get i).inputs[0]? = some v ∨
        (gs.get i).op ≠ GateOp.not ∧ v ∈ (gs.get i).inputs) ↔ v ∈ (gs.get i).inputs := by
      constructor
      · rintro (atPin | ⟨_,hm⟩)
        · exact List.mem_of_getElem? atPin
        · exact hm
      · intro mem
        by_cases not : (gs.get i).op = GateOp.not
        · have c := (clean i.val (gs.get i) (by simpa only [List.get_eq_getElem] using List.getElem?_eq_getElem i.isLt)).2
          have arity : (gs.get i).inputs.length = 1 := by
            rcases c with ⟨_,l⟩ | ⟨h | h,_⟩
            · exact l
            · rw [not] at h; cases h
            · rw [not] at h; cases h
          left
          obtain ⟨p,atPin⟩ := List.mem_iff_getElem?.mp mem
          have lt := List.getElem?_eq_some_iff.mp atPin
          obtain ⟨lt,_⟩ := lt
          have eq : p = 0 := by omega
          simpa only [eq] using atPin
        · exact Or.inr ⟨not,mem⟩
    simpa only [equiv] using only
  have separatePins : ∀ g ∈ gs, 4 ∈ g.inputs → 6 ∉ g.inputs := by
    intro g hg h4 h6
    obtain ⟨p,atG⟩ := List.mem_iff_getElem?.mp hg
    obtain ⟨pValid,pIs⟩ := List.getElem?_eq_some_iff.mp atG
    let pinGate : Fin gs.length := ⟨p,pValid⟩
    have pinned : gs.get pinGate = g := pIs
    obtain ⟨i4,_,only4⟩ := unique 4 (by simp)
    obtain ⟨i6,_,only6⟩ := unique 6 (by simp)
    have fixed4 : pinGate = i4 := only4 pinGate (by simpa only [pinned] using h4)
    have fixed6 : pinGate = i6 := only6 pinGate (by simpa only [pinned] using h6)
    let shape (h : Gate) := (h.op = GateOp.and ∨ h.op = GateOp.or) ∧
      (h.inputs = [4,6] ∨ h.inputs = [6,4])
    have bothShape : shape g := by
      have spec := (clean p g atG).2
      let pins := g.inputs
      have length : pins.length ≤ 2 := by rcases spec with ⟨_,h⟩ | ⟨_,h⟩ <;> simpa [pins,h]
      change 4 ∈ pins at h4
      change 6 ∈ pins at h6
      have actual : pins = [4,6] ∨ pins = [6,4] := by
        rcases pins with _ | ⟨a,_ | ⟨b,_ | ⟨c,rest⟩⟩⟩
        · simp at h4
        · simp only [List.mem_singleton] at h4 h6
          omega
        · have p4 : 4 = a ∨ 4 = b := by simpa using h4
          have p6 : 6 = a ∨ 6 = b := by simpa using h6
          rcases p4 with same | same <;> rcases p6 with other | other
          · omega
          · exact Or.inl (by rw [← same,← other])
          · exact Or.inr (by rw [← same,← other])
          · omega
        · simp at length
      change g.inputs = [4,6] ∨ g.inputs = [6,4] at actual
      rcases spec with ⟨_,h⟩ | ⟨op,_⟩
      · rcases actual with pins | pins <;> simp [pins] at h
      · exact ⟨op,actual⟩
    have gateShapes (h : Gate) (hh : h ∈ gs) : shape h ∨ (4 ∉ h.inputs ∧ 6 ∉ h.inputs) := by
      obtain ⟨j,atH⟩ := List.mem_iff_getElem?.mp hh
      obtain ⟨validH,hIs⟩ := List.getElem?_eq_some_iff.mp atH
      let q : Fin gs.length := ⟨j,validH⟩
      have pick : gs.get q = h := hIs
      have agreesWith (eq : q = pinGate) : h = g := pick.symm.trans ((congrArg gs.get eq).trans pinned)
      by_cases hRead4 : 4 ∈ h.inputs
      · have same := only4 q (by simpa only [pick] using hRead4)
        exact Or.inl (agreesWith (same.trans fixed4.symm) ▸ bothShape)
      by_cases hRead6 : 6 ∈ h.inputs
      · have same := only6 q (by simpa only [pick] using hRead6)
        exact Or.inl (agreesWith (same.trans fixed6.symm) ▸ bothShape)
      exact Or.inr ⟨hRead4,hRead6⟩
    let flip (i : ℕ) := if i = 4 then 6 else if i = 6 then 4 else i
    have commutes (op : GateOp) (kind : op = .and ∨ op = .or) (a b : Bool) : op.eval [a,b] = op.eval [b,a] := by
      rcases kind with rfl | rfl <;> cases a <;> cases b <;> rfl
    have flipRun (ls : List Gate) (a b : List Bool)
        (shapeAll : ∀ h ∈ ls, shape h ∨ (4 ∉ h.inputs ∧ 6 ∉ h.inputs))
        (len : a.length = b.length) (large : 10 ≤ a.length)
        (equal : ∀ i, a.getD i false = b.getD (flip i) false) :
        ∀ i, (run ls a).getD i false = (run ls b).getD (flip i) false := by
      induction ls generalizing a b with
      | nil => exact equal
      | cons h ls ih =>
        let x := h.op.eval (h.inputs.map fun i => a.getD i false)
        let y := h.op.eval (h.inputs.map fun i => b.getD i false)
        have calcBit : x = y := by
          rcases shapeAll h List.mem_cons_self with ⟨kind,pins⟩ | ⟨no4,no6⟩
          · have p4 : a.getD 4 false = b.getD 6 false := equal 4
            have p6 : a.getD 6 false = b.getD 4 false := equal 6
            dsimp only [x,y]
            rcases pins with h | h <;> rw [h,List.map_cons,List.map_cons,List.map_nil,p4,p6] <;>
              exact commutes _ kind _ _
          · dsimp only [x,y]
            congr 1
            apply List.map_congr_left
            intro i hm
            have fix4 : i ≠ 4 := by intro eq; exact no4 (eq ▸ hm)
            have fix6 : i ≠ 6 := by intro eq; exact no6 (eq ▸ hm)
            simpa only [flip,if_neg fix4,if_neg fix6] using equal i
        change ∀ i, (run ls (a ++ [x])).getD i false = (run ls (b ++ [y])).getD (flip i) false
        apply ih _ _ (fun h hh => shapeAll h (List.mem_cons_of_mem _ hh)) (by simp [len]) (by simp; omega)
        intro i
        have endSame : i = a.length ↔ flip i = b.length := by
          by_cases b4 : i = 4 <;> by_cases b6 : i = 6 <;> simp [flip,b4,b6,len] <;> omega
        by_cases new : i = a.length
        · have ha : (a ++ [x]).getD i false = x := by rw [new]; exact atEnd a x
          have hb : (b ++ [y]).getD (flip i) false = y := by rw [endSame.mp new]; exact atEnd b y
          rw [ha,hb,calcBit]
        · have atOther : flip i ≠ b.length := fun e => new (endSame.mpr e)
          have preserve (t : List Bool) (v : Bool) (k : ℕ) (different : k ≠ t.length) :
              (t ++ [v]).getD k false = t.getD k false := by
            by_cases there : k < t.length
            · exact lookup t v k there
            · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]
          rw [preserve _ _ _ new,preserve _ _ _ atOther]
          exact equal i
    let a : Fin 9 → Bool := fun t => decide (t = 0 ∨ t = 4)
    let b : Fin 9 → Bool := fun t => decide (t = 0 ∨ t = 6)
    have same : ∀ i, (w a).getD i false = (w b).getD (flip i) false := by
      intro i
      by_cases raw : i < 10
      · interval_cases i <;> rfl
      · have fix : flip i = i := by simp [flip,show i ≠ 4 by omega,show i ≠ 6 by omega]
        rw [fix,List.getD_eq_default _ _ (by simp [w]; omega),List.getD_eq_default _ _ (by simp [w]; omega)]
    have output := flipRun gs (w a) (w b) gateShapes (by simp [w]) (by simp [w]) same 23
    have fixed : flip 23 = 23 := rfl
    rw [fixed] at output
    rw [atLast] at agrees
    have dif : f a ≠ f b := by decide +kernel
    exact dif ((agrees a).symm.trans (output.trans (agrees b)))
  have lastIsBinary : ∀ g, gs[13]? = some g → g.op ≠ GateOp.not := by
    intro last atLastGate lastNot
    obtain ⟨hi,lastAt⟩ := List.getElem?_eq_some_iff.mp atLastGate
    let pre := gs.take 13
    have preLen : pre.length = 13 := by simp [pre,exactly]
    have splitLast : gs = pre ++ [last] := by
      have empty : gs.drop (13+1) = [] := List.drop_eq_nil_iff.mpr (by omega)
      calc
        gs = gs.take 13 ++ (gs[13] :: gs.drop (13+1)) := by
          rw [List.cons_getElem_drop_succ,List.take_append_drop]
        _ = pre ++ [last] := by rw [lastAt,empty]
    have lastUnary : last.inputs.length = 1 := by
      rcases (clean 13 last atLastGate).2 with ⟨_,h⟩ | ⟨k | k,_⟩
      · exact h
      · rw [lastNot] at k; cases k
      · rw [lastNot] at k; cases k
    obtain ⟨finalPin,hpin⟩ : ∃ i, last.inputs = [i] := List.length_eq_one_iff.mp lastUnary
    have finalFlag : isNot last = true := by
      change last.op.eval [false,false] = true
      rw [lastNot]
      rfl
    have allowance : (pre.filter isNot).length ≤ 1 := by
      have h := count
      rw [splitLast,List.filter_append,List.length_append] at h
      simp [finalFlag] at h
      omega
    have boolAnd : ∀ a b c d : Bool, a ≤ c → b ≤ d → (a && b) ≤ (c && d) := by decide
    have boolOr : ∀ a b c d : Bool, a ≤ c → b ≤ d → (a || b) ≤ (c || d) := by decide
    have evalNot (a : Bool) : GateOp.not.eval [a] = !a := by cases a <;> rfl
    have evalMono (op : GateOp) (kind : op = .and ∨ op = .or) (ps : List ℕ) (a b : ℕ → Bool)
        (le : ∀ i ∈ ps, a i ≤ b i) : op.eval (ps.map a) ≤ op.eval (ps.map b) := by
      induction ps with
      | nil => exact le_rfl
      | cons i ps ih =>
        have h := ih (fun p hp => le p (List.mem_cons_of_mem _ hp))
        have first := le i List.mem_cons_self
        rcases kind with rfl | rfl
        · exact boolAnd _ _ _ _ first h
        · exact boolOr _ _ _ _ first h
    have carry (a b : List Bool) (x y : Bool) (len : a.length = b.length)
        (ordered : ∀ k, a.getD k false ≤ b.getD k false) (fresh : x ≤ y) :
        ∀ k, (a ++ [x]).getD k false ≤ (b ++ [y]).getD k false := by
      intro k
      by_cases next : k = a.length
      · have atA : (a ++ [x]).getD k false = x := by rw [next]; exact atEnd a x
        have atB : (b ++ [y]).getD k false = y := by rw [next.trans len]; exact atEnd b y
        rw [atA,atB]
        exact fresh
      by_cases old : k < a.length
      · rw [lookup _ _ _ old,lookup _ _ _ (by omega)]
        exact ordered k
      · rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]
    have monoRun (ls : List Gate) (a b : List Bool) (positive : ∀ g ∈ ls, g.op = .and ∨ g.op = .or)
        (len : a.length=b.length) (ordered : ∀ k, a.getD k false ≤ b.getD k false) :
        ∀ k, (run ls a).getD k false ≤ (run ls b).getD k false := by
      induction ls generalizing a b with
      | nil => exact ordered
      | cons g ls ih =>
        let x := g.op.eval (g.inputs.map fun i => a.getD i false)
        let y := g.op.eval (g.inputs.map fun i => b.getD i false)
        have bit : x ≤ y := evalMono g.op (positive g List.mem_cons_self) g.inputs _ _ (fun i _ => ordered i)
        change ∀ k, (run ls (a ++ [x])).getD k false ≤ (run ls (b ++ [y])).getD k false
        exact ih _ _ (fun g hg => positive g (List.mem_cons_of_mem _ hg)) (by simp [len])
          (carry a b x y len ordered bit)
    have rowLen (x : Fin 9 → Bool) : (w x).length = 10 := by simp [w]
    have monoRow (x y : Fin 9 → Bool) (ordered : x ≤ y) :
        ∀ k, (w x).getD k false ≤ (w y).getD k false := by
      apply carry _ _ _ _ (by simp) ?_ (boolOr _ _ _ _ (ordered 4) (ordered 6))
      intro k
      by_cases raw : k < 9
      · let i : Fin 9 := ⟨k,raw⟩
        change (List.ofFn x).getD i.val false ≤ (List.ofFn y).getD i.val false
        rw [input_bit_from_list,input_bit_from_list]
        exact ordered i
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt raw),
          List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt raw)]
    have tailFan (g : Gate) (hg : g ∈ gs) := fan g (List.mem_cons_of_mem first hg)
    have positive (g : Gate) (hg : g ∈ gs) (absent : isNot g = false) : g.op = .and ∨ g.op = .or := by
      have op : g.op = .and ∨ g.op = .or ∨ g.op = .not := (tailFan g hg).1
      rcases op with k | k | k
      · exact Or.inl k
      · exact Or.inr k
      · have flag : isNot g = true := by
          change g.op.eval [false,false] = true
          rw [k]
          rfl
        cases absent.symm.trans flag
    have splitOne (ls : List Gate) (few : (ls.filter isNot).length ≤ 1) :
        (∀ g ∈ ls, isNot g = false) ∨
        ∃ a h b, ls = a ++ h :: b ∧ isNot h = true ∧
          (∀ g ∈ a, isNot g = false) ∧ ∀ g ∈ b, isNot g = false := by
      induction ls with
      | nil => exact Or.inl (by simp)
      | cons g ls ih =>
        cases choose : isNot g
        · have rest : (ls.filter isNot).length ≤ 1 := by simpa [choose] using few
          rcases ih rest with none | ⟨a,h,b,split,yes,noA,noB⟩
          · exact Or.inl (fun j hj => (List.mem_cons.mp hj).elim (fun eq => eq ▸ choose) (none j))
          · exact Or.inr ⟨g::a,h,b,congrArg (List.cons g) split,yes,
              fun j hj => (List.mem_cons.mp hj).elim (fun eq => eq ▸ choose) (noA j),noB⟩
        · have rest : ls.filter isNot = [] := by
            have length := few
            rw [List.filter_cons,choose] at length
            simp only [if_true,List.length_cons] at length
            exact List.length_eq_zero_iff.mp (by omega)
          refine Or.inr ⟨[],g,ls,rfl,choose,by simp,?_⟩
          intro h hm
          cases avoid : isNot h
          · rfl
          · have existsNow := List.mem_filter.mpr ⟨hm,avoid⟩
            rw [rest] at existsNow
            simp at existsNow
    let q (x : Fin 9 → Bool) := (run pre (w x)).getD finalPin false
    have qResult (x : Fin 9 → Bool) : q x = !(f x) := by
      have result := agrees x
      change (run gs (w x)).getD out false = _ at result
      rw [atLast,splitLast,runAppend] at result
      let start := run pre (w x)
      let v := last.op.eval (last.inputs.map fun i => start.getD i false)
      change (start ++ [v]).getD 23 false = _ at result
      have len : start.length = 23 := by rw [lengthRun,rowLen,preLen]
      have read : (start ++ [v]).getD 23 false = v := by simpa only [len] using atEnd start v
      rw [read] at result
      change last.op.eval (last.inputs.map fun i => start.getD i false) = _ at result
      rw [lastNot,hpin] at result
      change GateOp.not.eval [q x] = f x at result
      rw [evalNot] at result
      exact (by decide : ∀ a b : Bool, (!a) = b → a = !b) _ _ result
    let bottom : Fin 9 → Bool := fun _ => false
    let top : Fin 9 → Bool := fun _ => true
    have fbot : f bottom = false := rfl
    have ftop : f top = true := rfl
    have bot_le (x : Fin 9 → Bool) : bottom ≤ x := fun i => Bool.false_le _
    have le_top (x : Fin 9 → Bool) : x ≤ top := fun i => Bool.le_true _
    have badChange (x y : Fin 9 → Bool) (below : q x ≤ q y) (fx : f x = false) (fy : f y = true) : False := by
      rw [qResult,qResult,fx,fy] at below
      exact (by decide : ¬ true ≤ false) below
    have preSub (h : Gate) (hh : h ∈ pre) : h ∈ gs := List.mem_of_mem_take hh
    rcases splitOne pre allowance with noNot | ⟨a,h,b,split,yes,noA,noB⟩
    · have inc := monoRun pre _ _ (fun g hg => positive g (preSub g hg) (noNot g hg))
        (by simp [rowLen]) (monoRow bottom top (bot_le top)) finalPin
      exact badChange bottom top inc fbot ftop
    have memA (g : Gate) (hg : g ∈ a) : g ∈ gs := preSub g (split.symm ▸ List.mem_append_left _ hg)
    have memB (g : Gate) (hg : g ∈ b) : g ∈ gs := preSub g (split.symm ▸ List.mem_append_right _ (List.mem_cons_of_mem h hg))
    have hMem : h ∈ gs := preSub h (split.symm ▸ List.mem_append_right _ List.mem_cons_self)
    have hnot : h.op = .not := by
      have op : h.op = .and ∨ h.op = .or ∨ h.op = .not := (tailFan h hMem).1
      rcases op with k | k | k
      · have falseFlag : isNot h = false := by
          change h.op.eval [false,false] = false
          rw [k]
          rfl
        cases falseFlag.symm.trans yes
      · have falseFlag : isNot h = false := by
          change h.op.eval [false,false] = false
          rw [k]
          rfl
        cases falseFlag.symm.trans yes
      · exact k
    obtain ⟨p,atP⟩ := List.mem_iff_getElem?.mp hMem
    obtain ⟨tap,hinputs⟩ : ∃ j, h.inputs = [j] := by
      apply List.length_eq_one_iff.mp
      rcases (clean p h atP).2 with ⟨_,arity⟩ | ⟨o | o,_⟩
      · exact arity
      · rw [hnot] at o; cases o
      · rw [hnot] at o; cases o
    let u (x : Fin 9 → Bool) := (run a (w x)).getD tap false
    have before (x y : Fin 9 → Bool) (ordered : x ≤ y) :
        ∀ k, (run a (w x)).getD k false ≤ (run a (w y)).getD k false :=
      monoRun a _ _ (fun g hg => positive g (memA g hg) (noA g hg)) (by simp [rowLen]) (monoRow x y ordered)
    have changeInput (x y : Fin 9 → Bool) (ordered : x ≤ y) (fx : f x = false) (fy : f y = true) : u x ≠ u y := by
      intro same
      have unfoldQ (z : Fin 9 → Bool) : q z = (run b (run a (w z) ++ [!(u z)])).getD finalPin false := by
        change (run pre (w z)).getD finalPin false = _
        rw [split,runAppend]
        change (run b (run a (w z) ++ [h.op.eval (h.inputs.map fun i => (run a (w z)).getD i false)])).getD finalPin false = _
        rw [hnot,hinputs]
        change (run b (run a (w z) ++ [GateOp.not.eval [u z]])).getD finalPin false = _
        rw [evalNot]
      have sameLen : (run a (w x)).length = (run a (w y)).length := by simp [lengthRun,rowLen]
      apply badChange x y ?_ fx fy
      rw [unfoldQ,unfoldQ]
      exact monoRun b _ _ (fun g hg => positive g (memB g hg) (noB g hg)) (by simp [sameLen])
        (carry _ _ _ _ sameLen (before x y ordered) (by rw [same])) finalPin
    have unequal := changeInput bottom top (bot_le top) fbot ftop
    have monoEndpoints := before bottom top (bot_le top) tap
    change u bottom ≤ u top at monoEndpoints
    have ends : u bottom = false ∧ u top = true :=
      (by decide : ∀ a b : Bool, a ≠ b → a ≤ b → a = false ∧ b = true) _ _ unequal monoEndpoints
    have uTarget (x : Fin 9 → Bool) : u x = f x := by
      cases bit : f x
      · have no := changeInput x top (le_top x) bit ftop
        rw [ends.2] at no
        exact (by decide : ∀ a : Bool, a ≠ true → a = false) _ no
      · have yes := changeInput bottom x (bot_le x) fbot bit
        rw [ends.1] at yes
        exact (by decide : ∀ a : Bool, false ≠ a → a = true) _ yes
    let smaller : Circuit := ⟨first :: a,tap⟩
    have smallerFan : FanInTwo smaller := by
      intro g hg
      rcases List.mem_cons.mp hg with rfl | other
      · exact fan first List.mem_cons_self
      · exact tailFan g (memA g other)
    have smallerComputes (x : Fin 9 → Bool) : smaller.eval (List.ofFn x) = f x := by
      change (run a (List.ofFn x ++ [first.op.eval _])).getD tap false = _
      rw [firstEval]
      exact uTarget x
    have tooSmall := (lower smaller smallerFan smallerComputes).1
    change 15 ≤ a.length+1 at tooSmall
    have len := congrArg List.length split
    simp only [List.length_append,List.length_cons,preLen] at len
    omega
  obtain ⟨x,bad⟩ := search gs exactly clean count unique separatePins lastIsBinary
  apply bad
  simpa only [atLast] using agrees x
