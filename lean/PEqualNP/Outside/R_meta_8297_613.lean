import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 20000 in
theorem PEqualNP.Outside.R_meta_8297_613
    (case0 : ∀ (P D : Circuit) (m : Nat), m ∈ ([15, 71, 263] : List Nat) →
      FanInTwo P → P.size = 2 → (∀ g ∈ P.gates, ∀ i ∈ g.inputs, i < 10 → m.testBit i = true) →
      FanInTwo D → D.size ≤ 17 → (∃ g ∈ P.gates ++ D.gates, g.op = GateOp.not) →
      (∃ i ∈ (D.output :: D.gates.flatMap Gate.inputs), i < 10 ∧ m.testBit i = true ∧
        ∃ j ∈ (D.output :: D.gates.flatMap Gate.inputs), j < 10 ∧ m.testBit j = true ∧ i ≠ j) →
      ¬ ∀ x : Fin 10 → Bool, D.eval (P.wires (List.ofFn x)) = ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))))
    (case1 : ∀ (P D : Circuit) (m : Nat), m ∈ ([139, 267, 773] : List Nat) →
      FanInTwo P → P.size = 2 → (∀ g ∈ P.gates, ∀ i ∈ g.inputs, i < 10 → m.testBit i = true) →
      FanInTwo D → D.size ≤ 17 → (∃ g ∈ P.gates ++ D.gates, g.op = GateOp.not) →
      (∃ i ∈ (D.output :: D.gates.flatMap Gate.inputs), i < 10 ∧ m.testBit i = true ∧
        ∃ j ∈ (D.output :: D.gates.flatMap Gate.inputs), j < 10 ∧ m.testBit j = true ∧ i ≠ j) →
      ¬ ∀ x : Fin 10 → Bool, D.eval (P.wires (List.ofFn x)) = ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))) :
    have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → PEqualNP.MetaComplexity.Monotone2 x3 → x2.size + x3.size ≤ (18 : ℕ) → ¬∀ (x7 : Fin (10 : ℕ) → Bool), x3.eval (x2.wires (List.ofFn x7) ++ [!x2.eval (List.ofFn x7)]) = x1 x7 := by
  intro F A B hA hB budget computes
  let gen : Fin 8 → Fin 10 → Fin 10 := ![![9, 6, 1, 0, 4, 7, 8, 2, 5, 3], ![7, 9, 4, 3, 2, 5, 6, 0, 8, 1], ![9, 4, 0, 1, 6, 7, 3, 5, 2, 8], ![9, 7, 2, 1, 6, 4, 5, 3, 0, 8], ![9, 6, 8, 5, 7, 4, 1, 3, 0, 2], ![0, 5, 8, 6, 1, 4, 7, 3, 9, 2], ![3, 4, 9, 6, 8, 2, 0, 7, 1, 5], ![3, 4, 9, 7, 2, 8, 0, 6, 5, 1]]
  let act (w : List (Fin 8)) := w.foldr (fun j (p : Fin 10 → Fin 10) => fun i => gen j (p i)) id
  let words : Array (List (Fin 8)) := #[ [], [0,4,1], [3,2,0], [2,0,1], [0,7], [0,6], [7,7,1], [5,5], [4,2,0], [2,5,0], [0,0,0], [5], [7,0], [1,3], [3,3,1], [7,4], [7,2], [2,0,0], [6,3,0], [1,2], [2,6], [1,4], [7,3], [1,0], [4,4], [5,2], [2,2,0], [4,0], [0,1], [3,5,0], [5,3], [4,3], [5,0], [2,3,0], [5,4], [4,2], [6,5], [5,1], [4,1], [2,6,6], [4,6,1], [1,4,1], [6], [7], [7,5], [0,4], [3,1], [0,0], [7,7,3], [7,1,0], [6,1,0], [2,1,2], [7,1,3], [7,7,0], [2,1,0], [6,7,0], [1,4,0], [6,7,2], [7,7,2], [4,6,0], [6,4], [5,7,0], [6,0], [5,7,4], [4,6], [4,7], [6,3], [7,3,3], [5,1,2], [6,2], [2,1], [1,2,1], [6,3,1], [6,0,0], [5,7], [7,1], [0,1,0], [5,4,1], [6,6], [6,7], [0,7,0], [0,1,3], [5,0,0], [4,7,0], [7,6], [7,7], [2,2,1], [3,1,2], [7,0,0], [7,3,1], [3,1,0], [6,1], [0,6,0], [1], [2,6,0], [7,4,1], [1,2,0], [3,3], [5,5,0], [2,0], [1,3,0], [2,3], [5,4,0], [3,0], [5,0,1], [4,4,0], [2,2], [3,2], [2], [3,5], [5,3,0], [7,5,2], [0], [5,2,0], [7,5,0], [4], [3], [2,5], [6,4,2], [0,5] ]
  let perm (a : Fin 120) := act (words[a.val]?.getD [])
  let zeroMap (i : Fin 10) := Fin.ofNat 120 ((#[0,12,24,28,16,17,26,29,30,31] : Array Nat)[i.val]?.getD 0)
  let pairMap (i : Fin 10) := Fin.ofNat 120 ((#[0,0,0,4,4,5,2,5,7,6] : Array Nat)[i.val]?.getD 0)
  let table : Array Nat := #[0,0,0,0,32,40,1,3,2,5,0,0,0,0,96,97,1,3,2,10,0,0,0,0,32,40,1,8,2,5,0,0,0,0,32,42,18,3,4,33,32,96,32,32,32,97,48,34,35,33,40,97,40,42,97,40,56,40,41,43,1,1,1,18,48,56,1,21,16,24,3,3,8,3,34,40,21,3,41,12,2,2,2,4,35,41,16,41,2,5,5,10,5,33,33,43,24,12,5,5,0,0,0,0,96,97,1,3,2,10,0,0,0,0,96,97,1,3,2,10,0,0,0,0,128,136,1,8,2,10,0,0,0,0,96,122,18,3,4,99,96,96,128,96,96,97,144,114,98,112,97,97,136,122,97,97,152,104,120,106,1,1,1,18,144,152,1,26,16,24,3,3,8,3,114,104,26,3,107,12,2,2,2,4,98,120,16,107,2,19,10,10,10,99,112,106,24,12,19,10,0,0,0,0,32,40,1,8,2,5,0,0,0,0,128,136,1,8,2,10,0,0,0,0,32,40,1,8,2,5,0,0,0,0,32,44,291,834,770,323,32,128,32,32,32,162,131,36,35,90,40,136,40,44,162,40,139,40,82,43,1,1,1,291,131,139,1,299,307,315,8,8,8,834,36,40,299,8,331,778,2,2,2,770,35,82,307,331,2,5,5,10,5,323,90,43,315,778,5,5]
  let code (b : Fin 3) (c d : Fin 10) := table[100*b.val+10*c.val+d.val]?.getD 0
  let last (b : Fin 3) (c d : Fin 10) := Fin.ofNat 120 (code b c d / 8)
  let mask : Fin 6 → Nat := ![15,71,263,139,267,773]
  let packet (b : Fin 3) (c d : Fin 10) := Fin.ofNat 6 (code b c d % 8)
  have toZero : ∀ i, perm (zeroMap i) i = 0 := by decide +kernel
  have toPair : ∀ j, perm (pairMap j) 0 = 0 ∧ (perm (pairMap j) j).val < 3 := by decide +kernel
  have cover4 : ∀ (b : Fin 3) (c d : Fin 10),
      let test := fun i => (mask (packet b c d)).testBit (perm (last b c d) i).val = true
      test 0 ∧ test ⟨b.val, Nat.lt_trans b.isLt (by decide : 3 < 10)⟩ ∧ test c ∧ test d := by
    decide +kernel
  have preservesGen (a : Fin 8) (x : Fin 10 → Bool) : F (fun i => x (gen a i)) = F x := by
    fin_cases a <;> simp [gen,F,Bool.or_assoc,Bool.or_left_comm,Bool.or_comm,Bool.and_comm]
  have acts (w : List (Fin 8)) (x : Fin 10 → Bool) : F (fun i => x (act w i)) = F x := by
    induction w generalizing x with
    | nil => rfl
    | cons a t ih => exact (ih (fun i => x (gen a i))).trans (preservesGen a x)
  let assign (s a : Nat) (p : Fin 11) (i : Fin 10) := if s.testBit i.val then a.testBit i.val else decide (i.val = p.val)
  let rows : Fin 6 → Fin 9 → Nat := ![![0, 1, 2, 3, 4, 5, 8, 9, 10], ![0, 1, 3, 4, 5, 64, 65, 68, 69], ![0, 1, 2, 3, 4, 5, 256, 257, 260], ![0, 1, 2, 3, 8, 9, 10, 128, 129], ![0, 1, 2, 3, 8, 9, 10, 256, 257], ![0, 1, 4, 5, 256, 257, 260, 261, 512]]
  have separates : ∀ (k : Fin 6) (a b : Fin 9), a ≠ b → ∃ p : Fin 11,
      F (assign (mask k) (rows k a) p) ≠ F (assign (mask k) (rows k b) p) := by decide +kernel
  let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have extra (gs : List Gate) (u v : List Bool) (hlen : u.length = v.length)
      (ok : Nat → Prop) (hr : ∀ g ∈ gs, ∀ i ∈ g.inputs, ok i)
      (init : ∀ i, ok i → u.getD i false = v.getD i false) :
      ∃ z : List Bool, gs.foldl step u = u ++ z ∧ gs.foldl step v = v ++ z ∧ z.length = gs.length := by
    induction gs generalizing u v with
    | nil => exact ⟨[], by simp, by simp, rfl⟩
    | cons g gs ih =>
      let val := g.op.eval (g.inputs.map fun i => u.getD i false)
      have hv : g.op.eval (g.inputs.map fun i => v.getD i false) = val := by
        unfold val
        congr 1
        apply List.map_congr_left
        intro i hi
        exact (init i (hr g (by simp) i hi)).symm
      have extend (i : Nat) (hi : ok i) : (u ++ [val]).getD i false = (v ++ [val]).getD i false := by
        by_cases h : i < u.length
        · rw [List.getD_append _ _ _ _ h, List.getD_append _ _ _ _ (hlen ▸ h)]
          exact init i hi
        · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hlen]
      obtain ⟨z,hu,hv',hz⟩ := ih (u ++ [val]) (v ++ [val]) (by simp [hlen])
        (fun g hg => hr g (by simp [hg])) extend
      refine ⟨val :: z, ?_, ?_, by simp [hz]⟩
      · simpa [step,val,List.append_assoc] using hu
      · simpa only [List.foldl_cons,step,hv,List.append_assoc,List.cons_append,List.nil_append] using hv'
  have atRaw (x : Fin 10 → Bool) (i : Nat) (h : i < 10) : (List.ofFn x).getD i false = x ⟨i,h⟩ := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left h]; rfl
  have pastRaw (x : Fin 10 → Bool) (i : Nat) (h : ¬i < 10) : (List.ofFn x).getD i false = false := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_right h]; rfl
  have leak (P D : Circuit) (k : Fin 6) (hp : P.size = 2)
      (support : ∀ g ∈ P.gates, ∀ i ∈ g.inputs, i < 10 → (mask k).testBit i = true)
      (correct : ∀ x : Fin 10 → Bool, D.eval (P.wires (List.ofFn x)) = F x) :
      ∃ i ∈ (D.output :: D.gates.flatMap Gate.inputs), i < 10 ∧ (mask k).testBit i = true ∧
        ∃ j ∈ (D.output :: D.gates.flatMap Gate.inputs), j < 10 ∧ (mask k).testBit j = true ∧ i ≠ j := by
    let used := D.output :: D.gates.flatMap Gate.inputs
    let ok := fun i => i ∈ used ∧ i < 10 ∧ (mask k).testBit i = true
    by_contra impossible
    have unique (i j : Nat) (hi : ok i) (hj : ok j) : i = j := by
      by_contra hn
      exact impossible ⟨i,hi.1,hi.2.1,hi.2.2,j,hj.1,hj.2.1,hj.2.2,hn⟩
    classical
    let r := if ex : ∃ i, ok i then Classical.choose ex else 0
    have only (i : Nat) (hi : ok i) : i = r := by
      have ex : ∃ j, ok j := ⟨i,hi⟩
      simpa [r,ex] using unique i (Classical.choose ex) hi (Classical.choose_spec ex)
    let raw (a : Fin 9) (p : Fin 11) := List.ofFn (assign (mask k) (rows k a) p)
    have pre (a : Fin 9) (p : Fin 11) : ∃ z : List Bool,
        P.wires (raw a 10) = raw a 10 ++ z ∧ P.wires (raw a p) = raw a p ++ z ∧ z.length = 2 := by
      have start (i : Nat) (hi : i < 10 → (mask k).testBit i = true) :
          (raw a 10).getD i false = (raw a p).getD i false := by
        by_cases h : i < 10
        · simp only [raw,atRaw _ _ h,assign,hi h,ite_true]
        · simp only [raw,pastRaw _ _ h]
      obtain ⟨z,hu,hv,hz⟩ := extra P.gates (raw a 10) (raw a p) (by simp [raw]) _ support start
      exact ⟨z,hu,hv,hz.trans hp⟩
    let msg (a : Fin 9) : Bool × Bool × Bool :=
      ((P.wires (raw a 10)).getD 10 false, (P.wires (raw a 10)).getD 11 false, (rows k a).testBit r)
    obtain ⟨a,b,ne,same⟩ := Fintype.exists_ne_map_eq_of_card_lt msg (by decide)
    have c0 := congrArg Prod.fst same
    have c1 := congrArg (fun t : Bool × Bool × Bool => t.2.1) same
    have cr := congrArg (fun t : Bool × Bool × Bool => t.2.2) same
    obtain ⟨p,neq⟩ := separates k a b ne
    obtain ⟨za,za₀,zaₚ,la⟩ := pre a p
    obtain ⟨zb,zb₀,zbₚ,lb⟩ := pre b p
    have eqz : za = zb := by
      change (P.wires (raw a 10)).getD 10 false = (P.wires (raw b 10)).getD 10 false at c0
      change (P.wires (raw a 10)).getD 11 false = (P.wires (raw b 10)).getD 11 false at c1
      rw [za₀,zb₀,List.getD_append_right _ _ _ _ (by simp [raw]),List.getD_append_right _ _ _ _ (by simp [raw])] at c0 c1
      simp [raw] at c0 c1
      obtain ⟨x,y,rfl⟩ := List.length_eq_two.mp la
      obtain ⟨w,z,rfl⟩ := List.length_eq_two.mp lb
      change x = w at c0
      change y = z at c1
      rw [c0,c1]
    subst zb
    have start (i : Nat) (hi : i ∈ used) :
        (raw a p ++ za).getD i false = (raw b p ++ za).getD i false := by
      by_cases h : i < 10
      · rw [List.getD_append _ _ _ _ (by simpa [raw] using h),List.getD_append _ _ _ _ (by simpa [raw] using h)]
        by_cases hs : (mask k).testBit i = true
        · have eqr := only i ⟨hi,h,hs⟩
          change (rows k a).testBit r = (rows k b).testBit r at cr
          simpa only [raw,atRaw _ _ h,assign,hs,ite_true,←eqr] using cr
        · simp only [raw,atRaw _ _ h,assign,ite_eq_right hs]
      · rw [List.getD_append_right _ _ _ _ (by simp [raw]; omega),List.getD_append_right _ _ _ _ (by simp [raw]; omega)]
        simp [raw]
    have rd : ∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ∈ used := by
      intro g hg i hi
      exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨g,hg,hi⟩)
    obtain ⟨z,zu,zv,_⟩ := extra D.gates (raw a p ++ za) (raw b p ++ za) (by simp [raw]) _ rd start
    apply neq
    rw [←correct,←correct]
    change D.eval (P.wires (raw a p)) = D.eval (P.wires (raw b p))
    rw [zaₚ,zbₚ]
    change (D.gates.foldl step _).getD D.output false = (D.gates.foldl step _).getD D.output false
    rw [zu,zv]
    by_cases h : D.output < (raw a p ++ za).length
    · rw [List.getD_append (raw a p ++ za) z false D.output h,List.getD_append (raw b p ++ za) z false D.output (by simpa only [raw,List.length_append,List.length_ofFn] using h)]
      exact start D.output (by simp [used])
    · rw [List.getD_append_right (raw a p ++ za) z false D.output (Nat.le_of_not_gt h),List.getD_append_right (raw b p ++ za) z false D.output (by simpa only [raw,List.length_append,List.length_ofFn] using Nat.le_of_not_gt h)]
      simp [raw]
  let ng : Gate := ⟨.not, [A.output]⟩
  let G := A.gates ++ ng :: B.gates
  let valid (g : Gate) := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2
  have legalG : ∀ g ∈ G, valid g := by
    intro g hg
    rcases List.mem_append.mp hg with h | h
    · exact hA g h
    · rcases List.mem_cons.mp h with rfl | h
      · exact ⟨Or.inr (Or.inr rfl),by simp [ng]⟩
      · obtain ⟨op,len⟩ := hB g h
        exact ⟨by rcases op with e|e; exact Or.inl e; exact Or.inr (Or.inl e),len⟩
  have negG : ∃ g ∈ G, g.op = GateOp.not := ⟨ng,List.mem_append_right _ (by simp),rfl⟩
  have capG : G.length ≤ 19 := by simp [G]; change A.gates.length + B.gates.length ≤ 18 at budget; omega
  let run := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have wiresEq (C : Circuit) (w : List Bool) : C.wires w = C.gates.foldl run w := rfl
  have evalEq (C : Circuit) (w : List Bool) : C.eval w = (C.wires w).getD C.output false := rfl
  have notOp (ls : List Bool) : GateOp.not.eval ls = !(ls.headD false) := rfl
  have outG (x : Fin 10 → Bool) : (G.foldl run (List.ofFn x)).getD B.output false = F x := by
    simpa only [G,List.foldl_append,List.foldl_cons,run,ng,notOp,List.map_cons,List.map_nil,
      List.headD_cons,evalEq,wiresEq] using computes x
  let zero : Gate := ⟨.or,[]⟩
  let H := if G.length < 2 then G ++ [zero,zero] else G
  have capH : 2 ≤ H.length ∧ H.length ≤ 19 := by
    by_cases short : G.length < 2 <;> simp [H,short] <;> omega
  have legal : ∀ g ∈ H, valid g := by
    intro g hg
    by_cases short : G.length < 2
    · simp only [H,short,ite_true,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_self] at hg
      rcases hg with h | rfl
      · exact legalG g h
      · exact ⟨Or.inr (Or.inl rfl),by simp [zero]⟩
    · exact legalG g (by simpa [H,short] using hg)
  have neg : ∃ g ∈ H, g.op = GateOp.not := by
    obtain ⟨g,hg,he⟩ := negG
    exact ⟨g,by by_cases h : G.length < 2 <;> simp [H,h,hg],he⟩
  have out (x : Fin 10 → Bool) : (H.foldl run (List.ofFn x)).getD B.output false = F x := by
    rw [← outG x]
    by_cases short : G.length < 2
    · simp only [H,short,ite_true,List.foldl_append,List.foldl_cons,List.foldl_nil]
      let w := G.foldl run (List.ofFn x)
      change ((w ++ [false]) ++ [false]).getD B.output false = w.getD B.output false
      have pad (v : List Bool) (i : Nat) : (v ++ [false]).getD i false = v.getD i false := by
        by_cases hi : i < v.length
        · exact List.getD_append _ _ _ _ hi
        · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_eq_default v false (show v.length ≤ i by omega)]
          cases i-v.length <;> rfl
      rw [pad,pad]
    · simp [H,short]
  let U := H.take 2
  let T := H.drop 2
  have splitH : U ++ T = H := List.take_append_drop 2 H
  have lenU : U.length = 2 := by simp [U,min_eq_left capH.1]
  have lenT : T.length ≤ 17 := by simp [T]; omega
  have subsetU (g) (hg : g ∈ U) : g ∈ H := splitH ▸ List.mem_append_left _ hg
  have subsetT (g) (hg : g ∈ T) : g ∈ H := splitH ▸ List.mem_append_right _ hg
  let ports := U.flatMap Gate.inputs
  have lenPorts : ports.length ≤ 4 := by
    have bound : ∀ L : List Gate, (∀ g ∈ L, g.inputs.length ≤ 2) → (L.flatMap Gate.inputs).length ≤ 2*L.length := by
      intro L
      induction L with
      | nil => simp
      | cons g gs ih =>
        intro h
        have a := h g (by simp)
        have b := ih (fun z hz => h z (List.mem_cons_of_mem g hz))
        simp only [List.flatMap_cons,List.length_append,List.length_cons]
        omega
    simpa [ports,lenU] using bound U (fun g hg => (legal g (subsetU g hg)).2)
  let pick (n : Nat) := Fin.ofNat 10 (ports.getD n 0)
  let f1 := perm (zeroMap (pick 0))
  let q := f1 (pick 1)
  let f2 i := perm (pairMap q) (f1 i)
  let b : Fin 3 := ⟨(f2 (pick 1)).val, (toPair q).2⟩
  let c := f2 (pick 2)
  let d := f2 (pick 3)
  let l := last b c d
  let k := packet b c d
  let m := mask k
  let p i := perm l (f2 i)
  have kind : m ∈ ([15,71,263,139,267,773] : List Nat) := by
    have fact : ∀ j, mask j ∈ ([15,71,263,139,267,773] : List Nat) := by decide
    exact fact k
  have zeroEq : f2 (pick 0) = 0 := by
    have h : f1 (pick 0) = 0 := toZero _
    change perm (pairMap q) (f1 (pick 0)) = 0
    rw [h]
    exact (toPair q).1
  have marks (v : Nat) (hv : v ∈ ports) (small : v < 10) : m.testBit (p ⟨v,small⟩).val = true := by
    obtain ⟨a,ha,rfl⟩ := List.mem_iff_getElem.mp hv
    have un : pick a = (⟨ports[a],small⟩ : Fin 10) := by
      apply Fin.ext
      simp only [pick,List.getD_eq_getElem _ _ ha,Fin.val_ofNat,Nat.mod_eq_of_lt small]
    rw [← un]
    have spec := cover4 b c d
    change m.testBit (perm l 0).val = true ∧
      m.testBit (p (pick 1)).val = true ∧ m.testBit (p (pick 2)).val = true ∧
      m.testBit (p (pick 3)).val = true at spec
    have lim : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by omega
    rcases lim with h|h|h|h <;> subst a
    · simpa only [p,zeroEq] using spec.1
    · exact spec.2.1
    · exact spec.2.2.1
    · exact spec.2.2.2
  have single (idx : Fin 120) (x : Fin 10 → Bool) : F (fun i => x (perm idx i)) = F x := acts _ x
  have invar (x : Fin 10 → Bool) : F (fun j => x (p j)) = F x :=
    (single (zeroMap (pick 0)) (fun i => x (perm l (perm (pairMap q) i)))).trans
      ((single (pairMap q) (fun i => x (perm l i))).trans (single l x))
  let r := fun i : Nat => if hi : i < 10 then (p ⟨i,hi⟩).val else i
  let gate := fun g : Gate => (⟨g.op,g.inputs.map r⟩ : Gate)
  let P : Circuit := ⟨U.map gate,0⟩
  let D : Circuit := ⟨T.map gate,r B.output⟩
  have libraryOK (V : List Gate) (hV : ∀ g ∈ V, valid g) (o : Nat) : FanInTwo (⟨V.map gate,o⟩ : Circuit) := by
    intro g hg
    change g ∈ V.map gate at hg
    obtain ⟨original,horig,rfl⟩ := List.mem_map.mp hg
    simpa [gate,valid,Set.mem_insert_iff,Set.mem_singleton_iff] using hV original horig
  have pOK : FanInTwo P := libraryOK U (fun g hg => legal g (subsetU g hg)) _
  have dOK : FanInTwo D := libraryOK T (fun g hg => legal g (subsetT g hg)) _
  have sizeEq (C : Circuit) : C.size = C.gates.length := rfl
  have pSize : P.size = 2 := by simpa [P,sizeEq] using lenU
  have dSize : D.size ≤ 17 := by simpa [D,sizeEq] using lenT
  have neg' : ∃ g ∈ P.gates ++ D.gates, g.op = GateOp.not := by
    obtain ⟨g,hg,he⟩ := neg
    refine ⟨gate g,?_,he⟩
    change gate g ∈ U.map gate ++ T.map gate
    rw [← List.map_append,splitH]
    exact List.mem_map.mpr ⟨g,hg,rfl⟩
  have portsOK : ∀ g ∈ P.gates, ∀ i ∈ g.inputs, i < 10 → m.testBit i = true := by
    intro g hg i hi hi10
    change g ∈ U.map gate at hg
    obtain ⟨original,horig,rfl⟩ := List.mem_map.mp hg
    change i ∈ original.inputs.map r at hi
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    have jlt : j < 10 := by
      by_contra bad
      have same : r j = j := by simp [r,bad]
      exact bad (same ▸ hi10)
    have jm : j ∈ ports := List.mem_flatMap.mpr ⟨original,horig,hj⟩
    simpa only [r,jlt,↓reduceDIte] using marks j jm jlt
  have independent (x : Fin 10 → Bool) (tail : List Bool) (i : Nat) :
      (List.ofFn (fun j => x (p j)) ++ tail).getD i false =
      (List.ofFn x ++ tail).getD (r i) false := by
    by_cases hi : i < 10
    · have hi' : r i < 10 := by simp [r,hi]
      rw [List.getD_append _ _ _ _ (by simpa using hi), List.getD_append _ _ _ _ (by simpa using hi')]
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi),
          List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi'),
          List.getElem_ofFn, List.getElem_ofFn]
      congr 1
      apply Fin.ext
      simp [r,hi]
    · rw [show r i = i by simp [r,hi], List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hi),
        List.getD_append_right _ _ _ _ (by simpa using Nat.le_of_not_gt hi)]
      simp
  have traceEq (x : Fin 10 → Bool) (V : List Gate) (z : List Bool) :
      ∃ t : List Bool,
        V.foldl run (List.ofFn (fun j => x (p j)) ++ z) = List.ofFn (fun j => x (p j)) ++ t ∧
        (V.map gate).foldl run (List.ofFn x ++ z) = List.ofFn x ++ t := by
    induction V generalizing z with
    | nil => exact ⟨z,rfl,rfl⟩
    | cons hd tl ih =>
      let b := hd.op.eval (hd.inputs.map fun i => (List.ofFn (fun j => x (p j)) ++ z).getD i false)
      have same : (gate hd).op.eval ((gate hd).inputs.map fun i => (List.ofFn x ++ z).getD i false) = b := by
        change hd.op.eval ((hd.inputs.map r).map _) = hd.op.eval _
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact (independent x z i).symm
      obtain ⟨t, ht, ht'⟩ := ih (z ++ [b])
      refine ⟨t, ?_, ?_⟩
      · simpa only [List.foldl_cons, run, List.append_assoc, b] using ht
      · simpa only [List.map_cons, List.foldl_cons, run, same, List.append_assoc] using ht'
  have compact : ∀ x : Fin 10 → Bool, F x =
    ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))) := by decide +kernel
  have answer : ∀ x : Fin 10 → Bool, D.eval (P.wires (List.ofFn x)) =
        ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10))) := by
    intro x
    obtain ⟨t,told,tnew⟩ := traceEq x H []
    simp only [List.append_nil] at told tnew
    have h := out (fun j => x (p j))
    rw [told,invar] at h
    change ((T.map gate).foldl run ((U.map gate).foldl run _)).getD _ false = _
    rw [← List.foldl_append, ← List.map_append,splitH,tnew,← independent x t B.output,h]
    exact compact x
  have forced := leak P D k pSize portsOK (fun x => (answer x).trans (compact x).symm)
  change m ∈ _ at kind
  rcases List.mem_append.mp (show m ∈ ([15,71,263] : List Nat) ++ [139,267,773] from kind) with h|h
  · exact case0 P D m h pOK pSize portsOK dOK dSize neg' forced answer
  · exact case1 P D m h pOK pSize portsOK dOK dSize neg' forced answer
