import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
theorem PEqualNP.Outside.R_meta_5827_74
  (floor : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x3 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x3) = (x3 (0 : Fin (10 : ℕ)) && x3 (1 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (2 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (3 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (4 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (0 : Fin (10 : ℕ)) || x3 (0 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ)) || x3 (1 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (2 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (3 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (4 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (5 : Fin (10 : ℕ)) && x3 (7 : Fin (10 : ℕ)) || x3 (7 : Fin (10 : ℕ)) && x3 (9 : Fin (10 : ℕ)) || x3 (9 : Fin (10 : ℕ)) && x3 (6 : Fin (10 : ℕ)) || x3 (6 : Fin (10 : ℕ)) && x3 (8 : Fin (10 : ℕ)) || x3 (8 : Fin (10 : ℕ)) && x3 (5 : Fin (10 : ℕ)))) → (17 : ℕ) + PEqualNP.NotBracket.notCount x1 ≤ x1.size))
  (positive : ∀ j : Fin 10, j=1 ∨ j=2 →
    let B := ([0,1073741823,579928113,419987523,608501894,169476364,23364120,201770016,3616832,28839040,834691328,1040194048] : List (BitVec 30)) ++ [if j=1 then 999915635 else 651493559]
    ∀ P : List (BitVec 30), P.length≤17 →
      (∀ i : Fin P.length, let U := B ++ P.take i.val
        ∃ a ∈ U, ∃ b ∈ U, P.get i = a &&& b ∨ P.get i = a ||| b) →
      ∀ a ∈ B ++ P, ∀ b ∈ B ++ P, a ||| b ≠ 32767)
  (signed : let E : List (Fin 10 × Fin 10) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
    ∀ j : Fin 10, j=1 ∨ j=2 →
    let F := (Fin 10 → Bool) → Bool
    let R : List F := ([(fun _ : Fin 10 → Bool => false),(fun _ : Fin 10 → Bool => true)] ++
      List.ofFn (fun (i : Fin 10) (x : Fin 10 → Bool) => x i)) ++
      [fun x : Fin 10 → Bool => x 0 || x j]
    ∀ N P : List F, 1 ≤ N.length → N.length ≤ 2 → P.length + N.length ≤ 17 →
      let A := fun (Q : List F) (w : F) => w ∈ R ++ Q ∨ ∃ h ∈ R ++ Q, h ∈ N ∧ w = (fun x => !(h x))
      (∀ i : Fin P.length, ∃ a b, A (P.take i.val) a ∧ A (P.take i.val) b ∧
        (P.get i = (fun x => a x && b x) ∨ P.get i = (fun x => a x || b x))) →
      ∀ a b, A P a → A P b → ∃ x, (a x || b x) ≠ E.any (fun e => x e.1 && x e.2)) :
  (∀ (x1 x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : Fin (18 : ℕ)),   PEqualNP.MetaComplexity.FanInTwo x3 →     x3.size ≤ (17 : ℕ) →       have x8 : PEqualNP.CircuitLowerBounds.Gate := { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [↑x1, ↑x2] : PEqualNP.CircuitLowerBounds.Gate };       have x9 : (Fin (10 : ℕ) → Bool) → Bool := fun (x9 : Fin (10 : ℕ) → Bool) => x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ));       have x10 : (Fin (10 : ℕ) → Bool) → ℕ → Bool := fun (x10 : Fin (10 : ℕ) → Bool) (x11 : ℕ) => (x3.wires ({ gates := [x8], output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires (List.ofFn x10))).getD x11 Bool.false;       (∃ (x11 : Fin (10 : ℕ) → Bool), x10 x11 ((10 : ℕ) + ↑x4) = Bool.true ∧ x10 x11 ((10 : ℕ) + ↑x5) = Bool.false) → (∃ (x12 : Fin (10 : ℕ) → Bool), x10 x12 ((10 : ℕ) + ↑x4) = Bool.false ∧ x10 x12 ((10 : ℕ) + ↑x5) = Bool.true) → (∀ (x13 : Fin (10 : ℕ) → Bool), x9 x13 = Bool.false → x10 x13 ((10 : ℕ) + ↑x4) = Bool.false ∧ x10 x13 ((10 : ℕ) + ↑x5) = Bool.false) → ∃ (x14 : Fin (10 : ℕ) → Bool), x9 x14 = Bool.true ∧ x10 x14 ((10 : ℕ) + ↑x4) = Bool.false ∧ x10 x14 ((10 : ℕ) + ↑x5) = Bool.false) := by
  have canonical (j : Fin 10) (hj : j=1 ∨ j=2) (C : Circuit) (u v : ℕ)
      (fan : FanInTwo C) (small : C.size≤17) : ∃ x : Fin 10 → Bool,
      let w := C.wires (List.ofFn x ++ [x 0 || x j])
      (w.getD u false || w.getD v false) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)) := by
    by_contra fail
    let X := Fin 10 → Bool
    let F := X → Bool
    let E : List (Fin 10 × Fin 10) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
    let target (x : X) := ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
    have complete (x : X) : let w:=C.wires (List.ofFn x++[x 0 || x j])
        (w.getD u false || w.getD v false)=target x := by
      apply Classical.byContradiction
      intro disagree
      exact fail ⟨x,disagree⟩
    let raw : List F := (List.ofFn fun i : Fin 10 => fun x => x i) ++ [fun x => x 0 || x j]
    let R : List F := [(fun _ => false),(fun _ => true)] ++ raw
    let meet (a b : F) : F := fun x => a x && b x
    let join (a b : F) : F := fun x => a x || b x
    let inv (a : F) : F := fun x => !(a x)
    let A (P N : List F) (w : F) : Prop := w ∈ R ++ P ∨ ∃ h ∈ R ++ P, h ∈ N ∧ w=inv h
    let legal (P N : List F) := ∀ i : Fin P.length, ∃ a b,
      A (P.take i.val) N a ∧ A (P.take i.val) N b ∧ (P.get i=meet a b ∨ P.get i=join a b)
    let zeros : F := fun _ => false
    let ones : F := fun _ => true
    have hz (P N) : A P N zeros := Or.inl (by simp [R,zeros])
    have ho (P N) : A P N ones := Or.inl (by simp [R,ones])
    have expand {P N P' N' : List F} (p : ∀ z∈P, z∈P') (n : ∀ z∈N, z∈N') {z} (h : A P N z) : A P' N' z := by
      have inc {x} (hx : x∈R++P) : x∈R++P' := List.mem_append.mpr ((List.mem_append.mp hx).imp id (p x))
      rcases h with h|⟨s,hs,hn,rfl⟩
      · exact Or.inl (inc h)
      · exact Or.inr ⟨s,inc hs,n _ hn,rfl⟩
    have appendLegal {P N : List F} (h : legal P N) (z : F)
        (make : ∃ a b, A P N a ∧ A P N b ∧ (z=meet a b ∨ z=join a b)) : legal (P++[z]) N := by
      intro i
      by_cases early : i.val<P.length
      · obtain ⟨a,b,ha,hb,eq⟩ := h ⟨i.val,early⟩
        have tk := List.take_append_of_le_length (l₂:=[z]) (Nat.le_of_lt early)
        have atI : (P++[z]).get i=P.get ⟨i.val,early⟩ := List.getElem_append_left early
        rw [tk,atI]
        exact ⟨a,b,ha,hb,eq⟩
      · have last : i.val=P.length := by have s:=i.isLt; simp at s; omega
        have tk : (P++[z]).take i.val=P := by simp [last]
        have atI : (P++[z]).get i=z := by
          change (P++[z])[i.val]=z
          rw [List.getElem_append_right (by omega)]
          simp [last]
        rw [tk,atI]
        exact make
    let readW (ws : List F) (w : ℕ) : F := ws.getD w zeros
    let value (ws : List F) (g : Gate) : F := fun x => g.op.eval (g.inputs.map fun i => readW ws i x)
    let grow (ws : List F) (g : Gate) := ws++[value ws g]
    letI : DecidableEq GateOp := lineDegreeGateOpDecEq
    let isNeg (g : Gate) := decide (g.op = GateOp.not)
    let nc (gs : List Gate) := (gs.filter isNeg).length
    have valNot (bs : List Bool) : GateOp.eval .not bs = !(bs.headD false) := rfl
    have valAnd (bs : List Bool) : GateOp.eval .and bs = bs.all id := rfl
    have valOr (bs : List Bool) : GateOp.eval .or bs = bs.any id := rfl
    have reads {ws P N} (cov : ∀ f∈ws, A P N f) (w : ℕ) : A P N (readW ws w) := by
      by_cases hw : w<ws.length
      · rw [show readW ws w=ws[w] from List.getD_eq_getElem _ _ hw]
        exact cov _ (List.getElem_mem _)
      · rw [show readW ws w=zeros from List.getD_eq_default _ _ (by omega)]
        exact hz _ _
    have program (gs : List Gate) (allowed : ∀ g∈gs, (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2)
        (ws P N : List F) (old : legal P N) (cov : ∀ f∈ws, A P N f) :
        ∃ Q M : List F, legal Q M ∧ Q.length+M.length=P.length+N.length+gs.length ∧
           M.length=N.length+nc gs ∧ ∀ f∈gs.foldl grow ws, A Q M f := by
      induction gs generalizing ws P N with
      | nil => exact ⟨P,N,old,by simp,by simp [nc,isNeg],cov⟩
      | cons g gs ih =>
        obtain ⟨allowedG,arity⟩ := allowed g (by simp)
        have tail := fun h (hm : h∈gs) => allowed h (List.mem_cons_of_mem _ hm)
        by_cases neg : g.op=GateOp.not
        · let t : F := readW ws (g.inputs.headD 0)
          let source : F := if g.inputs=[] then zeros else t
          have hs : A P N source := by
            by_cases e : g.inputs=[]
            · simpa only [source,ite_eq_left e] using hz P N
            · simpa only [source,ite_eq_right e] using reads cov (g.inputs.headD 0)
          have eq : value ws g=inv source := by
            cases h : g.inputs with
            | nil => funext x; simp [value,neg,h,inv,source,t,zeros,valNot]
            | cons a vs => funext x; simp [value,neg,h,inv,source,t,valNot]
          let M := N++[source]
          have widen {p z} (h : A p N z) : A p M z := expand (fun _ h => h) (fun _ h => List.mem_append_left _ h) h
          have ok : legal P M := by
            intro i
            obtain ⟨a,b,ha,hb,h⟩:=old i
            exact ⟨a,b,widen ha,widen hb,h⟩
          have newV : A P M (value ws g) := by
            rw [eq]
            rcases hs with h|⟨a,ha,hn,eq⟩
            · exact Or.inr ⟨source,h,by simp [M],rfl⟩
            · apply Or.inl
              have e : inv source=a := by rw [eq]; funext x; simp [inv]
              simpa only [e] using ha
          have all : ∀ z∈grow ws g, A P M z := by
            intro z mem
            rcases List.mem_append.mp mem with w|single
            · exact widen (cov _ w)
            · exact List.mem_singleton.mp single ▸ newV
          obtain ⟨Q,T,hq,ls,ns,cv⟩:=ih tail (grow ws g) P M ok all
          refine ⟨Q,T,hq,?_,?_,cv⟩
          · simp only [M,List.length_append,List.length_singleton,List.length_cons,List.length_nil] at ls ⊢
            omega
          · simpa [M,nc,isNeg,neg,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ns
        · have ops : g.op=.and ∨ g.op=.or := allowedG.elim Or.inl (fun h => Or.inr (h.resolve_right neg))
          have make : ∃ a b, A P N a ∧ A P N b ∧ (value ws g=meet a b ∨ value ws g=join a b) := by
            obtain ⟨op,ins⟩:=g
            cases ins with
            | nil =>
              rcases ops with e|e <;> change op=_ at e <;> subst op
              · exact ⟨ones,ones,ho _ _,ho _ _,Or.inl rfl⟩
              · exact ⟨zeros,zeros,hz _ _,hz _ _,Or.inr rfl⟩
            | cons a more =>
              cases more with
              | nil =>
                refine ⟨readW ws a,readW ws a,reads cov _,reads cov _,?_⟩
                rcases ops with e|e <;> change op=_ at e <;> subst op
                · left; funext x; simp [value,meet,valAnd]
                · right; funext x; simp [value,join,valOr]
              | cons b more =>
                have emp : more=[] := by
                  apply List.length_eq_zero_iff.mp
                  change (a::b::more).length ≤ 2 at arity
                  simp only [List.length_cons] at arity
                  omega
                subst more
                refine ⟨readW ws a,readW ws b,reads cov _,reads cov _,?_⟩
                rcases ops with e|e <;> change op=_ at e <;> subst op
                · left; funext x; simp [value,meet,valAnd]
                · right; funext x; simp [value,join,valOr]
          let Q := P++[value ws g]
          have all : ∀ z∈grow ws g, A Q N z := by
            intro z mem
            rcases List.mem_append.mp mem with w|single
            · exact expand (fun _ h => List.mem_append_left _ h) (fun _ h => h) (cov _ w)
            · apply Or.inl
              exact List.mem_append_right _ (List.mem_append_right _ single)
          obtain ⟨U,M,ok,ls,ns,cv⟩:=ih tail (grow ws g) Q N (appendLegal old _ make) all
          refine ⟨U,M,ok,?_,?_,cv⟩
          · simp only [Q,List.length_append,List.length_singleton,List.length_cons,List.length_nil] at ls ⊢
            omega
          · simpa [nc,isNeg,neg] using ns
    let actual (w : List Bool) (g : Gate) := w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
    have readEval (ws : List F) (i : ℕ) (x : X) :
        (ws.map (fun f => f x)).getD i false = readW ws i x := by
      by_cases h : i<ws.length
      · rw [List.getD_eq_getElem _ _ (by simpa using h),show readW ws i=ws[i] from List.getD_eq_getElem _ _ h]
        exact List.getElem_map _
      · have out : ws.length ≤ i := by omega
        rw [List.getD_eq_default _ _ (by simpa using out), show readW ws i=zeros from List.getD_eq_default _ _ out]
    have commute (gs : List Gate) (ws : List F) (x : X) :
        (gs.foldl grow ws).map (fun f => f x)=gs.foldl actual (ws.map (fun f => f x)) := by
      induction gs generalizing ws with
      | nil => rfl
      | cons g gs ih =>
        simp only [List.foldl_cons,ih]
        apply congrArg (fun w => gs.foldl actual w)
        simp only [grow,List.map_append,List.map_cons,List.map_nil,value,actual,readEval]
    have rawMap (x : X) : raw.map (fun f => f x)=List.ofFn x++[x 0 || x j] := by simp [raw,List.map_ofFn,Function.comp_def]
    let endW := C.gates.foldl grow raw
    have wire (i : ℕ) (x : X) : readW endW i x=(C.wires (List.ofFn x++[x 0 || x j])).getD i false := by
      rw [←readEval]
      change ((C.gates.foldl grow raw).map _).getD i false=_
      rw [commute,rawMap]
      rfl
    have truth : join (readW endW u) (readW endW v)=target := by
      funext x
      change (readW endW u x || readW endW v x)=_
      rw [wire,wire]
      exact complete x
    let pre : Gate := ⟨.or,[0,j.val]⟩
    let top : Gate := ⟨.or,[u,v]⟩
    let T : Circuit := ⟨pre::(C.gates++[top]),11+C.gates.length⟩
    have Tfan : FanInTwo T := by
      intro g h
      change g∈pre::(C.gates++[top]) at h
      rcases List.mem_cons.mp h with rfl|m
      · simp [pre]
      · rcases List.mem_append.mp m with inner|last
        · exact fan _ inner
        · obtain rfl:=List.mem_singleton.mp last
          simp [top]
    have wirelen (gs : List Gate) (w : List Bool) : (gs.foldl actual w).length=w.length+gs.length := by
      induction gs generalizing w with
      | nil => simp
      | cons g gs ih =>
        rw [List.foldl_cons,ih]
        simp only [actual,List.length_append,List.length_singleton,List.length_cons,List.length_nil]
        omega
    have Tc (x : Fin 10→Bool) : T.eval (List.ofFn x)=target x := by
      let w:=C.wires (List.ofFn x++[x 0 || x j])
      have get (i : Fin 10) : (List.ofFn x).getD i.val false=x i := by
        have hi : i.val<(List.ofFn x).length := by simpa only [List.length_ofFn] using i.isLt
        rw [List.getD_eq_getElem _ _ hi]
        exact List.getElem_ofFn (f:=x) hi
      have init : actual (List.ofFn x) pre=List.ofFn x++[x 0 || x j] := by
        change _++[_]=_++[_]
        simp only [pre,valOr,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false]
        rw [get j,show (List.ofFn x).getD 0 false=x 0 from get 0]
      have sz : w.length=11+C.gates.length := by
        change (C.gates.foldl actual _).length=_
        rw [wirelen]; simp
      change ((pre::(C.gates++[top])).foldl actual (List.ofFn x)).getD (11+C.gates.length) false=_
      rw [List.foldl_cons,List.foldl_append,init]
      change (w++[top.op.eval (top.inputs.map fun i => w.getD i false)]).getD _ false=_
      rw [←sz,List.getD_append_right _ _ _ _ le_rfl,Nat.sub_self]
      change (w.getD u false || (w.getD v false || false))=_
      simp only [Bool.or_false]
      exact complete x
    have nf : PEqualNP.NotBracket.notCount T = nc C.gates := by
      change ((pre::(C.gates++[top])).filter isNeg).length=(C.gates.filter isNeg).length
      simp [List.filter_append,show isNeg pre=false from rfl,show isNeg top=false from rfl]
    have floorN := floor T Tfan Tc
    rw [nf] at floorN
    have szT : T.size=C.size+2 := by
      change (pre::(C.gates++[top])).length=C.gates.length+2
      simp [Nat.add_assoc]
    rw [szT] at floorN
    have fam (g : Gate) (h : g∈C.gates) : (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2 := fan g h
    have baseAll : ∀ f∈raw, A [] [] f := fun f h => Or.inl (by simp [R,h])
    obtain ⟨P,N,hP,hlen,hn,cov⟩:=program C.gates fam raw [] [] (by intro i; exact Fin.elim0 i) baseAll
    simp only [List.length_nil,Nat.zero_add] at hlen hn
    have total : P.length+N.length≤17 := hlen ▸ small
    have cap : N.length≤2 := by omega
    have hu : A P N (readW endW u) := reads cov u
    have hv : A P N (readW endW v) := reads cov v
    by_cases empty : N=[]
    · subst N
      let B := ([0,1073741823,579928113,419987523,608501894,169476364,23364120,201770016,3616832,28839040,834691328,1040194048] : List (BitVec 30)) ++ [if j=1 then 999915635 else 651493559]
      let rows : Array Nat := #[3,6,12,24,17,33,66,132,264,528,160,640,576,320,288,50,69,104,116,138,201,208,276,385,402,521,548,554,770,773]
      let row (i : Fin 30) (t : Fin 10) := rows[i.val]!.testBit t.val
      let obs (z : F) : BitVec 30 := (BitVec.ofBoolListLE (List.ofFn fun i : Fin 30 => z (row i))).cast (by simp)
      have bit (z : F) (i : Fin 30) : (obs z).getLsbD i.val=z (row i) := by
        let bs := List.ofFn fun i : Fin 30 => z (row i)
        have h : i.val<bs.length := by simpa [bs] using i.isLt
        change (BitVec.ofBoolListLE bs).getLsbD i.val=_
        rw [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem _ _ h]
        exact List.getElem_ofFn (f:=fun i : Fin 30 => z (row i)) h
      have obsM (a b) : obs (meet a b)=obs a &&& obs b := by
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        simpa only [meet,BitVec.getLsbD_and,bit a ⟨i,hi⟩,bit b ⟨i,hi⟩] using bit (meet a b) ⟨i,hi⟩
      have obsJ (a b) : obs (join a b)=obs a ||| obs b := by
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        simpa only [join,BitVec.getLsbD_or,bit a ⟨i,hi⟩,bit b ⟨i,hi⟩] using bit (join a b) ⟨i,hi⟩
      have rawEq : R.map obs=B := by rcases hj with rfl|rfl <;> decide +kernel
      have goalEq : obs target=32767 := by decide +kernel
      have lift {Q z} (h : A Q [] z) : obs z∈B++Q.map obs := by
        have old : z∈R++Q := by
          rcases h with present|⟨_,_,bad,_⟩
          · exact present
          · exact False.elim (List.not_mem_nil bad)
        rw [←rawEq,←List.map_append]
        exact List.mem_map_of_mem old
      have run (i : Fin (P.map obs).length) : let U := B++(P.map obs).take i.val
          ∃ a∈U, ∃ b∈U, (P.map obs).get i=a &&& b ∨ (P.map obs).get i=a ||| b := by
        let m : Fin P.length := ⟨i.val,by simpa using i.isLt⟩
        obtain ⟨a,b,ha,hb,op⟩:=hP m
        dsimp only
        rw [←List.map_take]
        refine ⟨obs a,lift ha,obs b,lift hb,?_⟩
        have ix : (P.map obs).get i=obs (P.get m) := List.getElem_map obs
        rw [ix]
        exact op.imp (fun e => (congrArg obs e).trans (obsM a b)) (fun e => (congrArg obs e).trans (obsJ a b))
      have budget : (P.map obs).length≤17 := by simpa using total
      have impossible := positive j hj (P.map obs) budget run _ (lift hu) _ (lift hv)
      apply impossible
      rw [←obsJ,truth,goalEq]
    · have npos : 1≤N.length := by by_contra! h; apply empty; exact List.length_eq_zero_iff.mp (by omega)
      have h := signed j hj N P npos cap total hP (readW endW u) (readW endW v) hu hv
      obtain ⟨x,bad⟩:=h
      apply bad
      have e : (readW endW u x || readW endW v x)=target x := congrFun truth x
      rw [e]
      simp [target,E,List.any_cons,Bool.or_assoc]
  have adjacent := canonical 1 (Or.inl rfl)
  have nonadjacent := canonical 2 (Or.inr rfl)
  clear canonical floor positive signed
  intro a b C u v fan budget
  let target (x : Fin 10 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let generator (g : Bool) (i : Fin 10) : Fin 10 :=
    ((if g then [2, 1, 6, 8, 3, 7, 0, 9, 5, 4] else [1, 0, 4, 3, 2, 6, 5, 9, 8, 7]) : List (Fin 10)).getD i.val 0
  let run (w : List Bool) (i : Fin 10) := w.foldr generator i
  let words : List (List Bool) := [[], [], [], [false, true, false, true, true, true], [false, true, false, true, true, true], [false, true, false], [true, true, true, false, true, true, true, false], [false, true, false], [false, true, true, true, true, false], [true, true, true, false, true, true, false], [], [false], [false], [false, true, false, true, true, true, false], [false, true, false, true, true, true, false], [false], [false, true, true, true], [false, true, true, true, true], [true, true, true, false, true, true], [false, true, true, true, true], [false, true], [false], [true, false, true, true, true, false], [true, false, true, true, true, false], [true, false, true, true, true, false], [true, false, true, false, true, true, false], [true, false, true, false, true, true, false], [false, true, false, true, false, true, true, true, false], [true, true, true, true, true], [false, true, false, true, false, true, true, true, false], [true, false, true, false, true, false, true, false], [false, true, true, true, true, true, false, true, true], [true, false, true, true, true, false], [false, true, false, true, false, true, true], [true, true, true, true, false, true, true], [true, true, true, true, false, true, true], [false, true, false, true, false, true, true], [false, true, false, true, false, true, true], [true, false, true, false, true, false], [true, false, true, false, true], [false, true, false, true, false, true, false, true, false], [true, false, true, false, true, false], [false, true, false, true, false, true, false, true], [false, true, false, true, false, true, true], [true, false, true, true, true], [true, false, true, true, true], [true, false, true, false, true, true], [true, false, true, false, true, true], [true, false, true, true, true], [true, true, false], [false, true, false, true, false, true, true, true], [false, true, false, true, true, true, true, true, false], [false, true, false, true, true, false], [false, true, false, true, false, true, true, true], [true, false, true, true, true], [true, false], [true, false], [false, true, false, true, true, true, true, false], [false, true, true, true, true, false, true, false], [true, true, false, true, true, true], [true, false], [false, true, false, true, false], [false, true, false, true, true, true, true, false], [false, true, false, true, false], [true, true, false, true, true, false, true, true], [true, false], [true], [true], [true, true, false, true, true, true, false], [true, true, false, true, false, true, false], [false, true, false, true, true, true, true], [false, true, false, true], [true], [false, true, true, false, true], [false, true, false, true], [false, true, false, true, true, true, true], [true], [true, false, true, true, true, true, false], [true, false, true, false, true, true, true, false], [true, false, true, false, true, true, true, false], [true, true, true, true, true, false, true, true], [true, false, true, false, true, false, true, true, true], [true, false, true, true, true, true, false], [true, false, true, false, true, true, true, true], [true, false, true, true, true, true, false], [true, true, false, true, false], [true, false, true, false, true, false, true, true, true], [true, false, true, true, true, true, false], [true, false, true, false], [true, false, true], [false, true, false, true, false, true], [false, true, false, true, false, true, false], [false, true, false, true, false, true, false], [true, false, true, false], [true, false, true], [false, true, true, false, true, false, true], [true, false, true, false], [true, true, false, true, true, true, true], [true, false, true, false], [true, false, true, false, true, true, true], [true, false, true, true, true, true], [false, true, false, true, false, true, true, true, true], [true, false, true, false, true, false, true, true], [true, false, true, false, true, true, true], [true, false, true, false, true, true, true, true, false], [true, false, true, true, true, true], [true, false, true, false, true, true, true, true, false], [true, true, false, true], [true, false, true, false, true, true, true], [true, false, true, false, true, true, true], [], [false], [true, false, true, true, true, false], [false, true, false, true, false, true, true], [true, false, true, true, true], [true, false], [true], [true, false, true, true, true, true, false], [true, false, true, false], [true, false, true, false, true, true, true], []]
  let second : List (Fin 10) := [1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  let source : List Nat := [0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 10, 0, 10, 10, 10, 10, 10, 10, 10, 10, 0, 10, 10, 0, 10, 10, 10, 10, 10, 10, 10, 0, 10, 10, 10, 0, 10, 10, 10, 10, 10, 10, 0, 10, 10, 10, 10, 0, 10, 10, 10, 10, 10, 0, 10, 10, 10, 10, 10, 0, 10, 10, 10, 10, 0, 10, 10, 10, 10, 10, 10, 0, 10, 10, 10, 0, 10, 10, 10, 10, 10, 10, 10, 0, 10, 10, 0, 10, 10, 10, 10, 10, 10, 10, 10, 0, 10, 0, 10, 10, 10, 10, 10, 10, 10, 10, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 99]
  let ix (a b : Fin 11) := a.val * 11 + b.val
  let σ (a b : Fin 11) (i : Fin 10) : Fin 10 :=
    run (words.getD (ix a b) []) i
  let k (a b : Fin 11) := second.getD (ix a b) 1
  let src (a b : Fin 11) := source.getD (ix a b) 0
  have choices : ∀ a b : Fin 11, k a b = 1 ∨ k a b = 2 := by decide +kernel
  have kinds : ∀ a b : Fin 11,
      (src a b = 99 ∧ a.val = 10 ∧ b.val = 10) ∨
      (src a b = 0 ∧ (a.val = 10 ∨ σ a b ⟨a.val % 10, Nat.mod_lt _ (by decide)⟩ = 0) ∧
          (b.val = 10 ∨ σ a b ⟨b.val % 10, Nat.mod_lt _ (by decide)⟩ = 0) ∧ (a.val < 10 ∨ b.val < 10)) ∨
      (src a b = 10 ∧ a.val < 10 ∧ b.val < 10 ∧
          σ a b ⟨a.val % 10, Nat.mod_lt _ (by decide)⟩ = 0 ∧
          σ a b ⟨b.val % 10, Nat.mod_lt _ (by decide)⟩ = k a b) := by decide +kernel
  have one (g : Bool) (x : Fin 10 → Bool) : target (x ∘ generator g) = target x := by
    cases g
    · change ((x 1 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (x 3 && x 2) || (x 2 && x 1) || (x 1 && x 6) || (x 0 && x 5) || (x 4 && x 9) || (x 3 && x 8) || (x 2 && x 7) || (x 6 && x 9) || (x 9 && x 7) || (x 7 && x 5) || (x 5 && x 8) || (x 8 && x 6)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
    · change ((x 2 && x 1) || (x 1 && x 6) || (x 6 && x 8) || (x 8 && x 3) || (x 3 && x 2) || (x 2 && x 7) || (x 1 && x 0) || (x 6 && x 9) || (x 8 && x 5) || (x 3 && x 4) || (x 7 && x 9) || (x 9 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 5 && x 7)) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5))
      ac_rfl
  have word (w : List Bool) (x : Fin 10 → Bool) : target (x ∘ run w) = target x := by
    induction w generalizing x with
    | nil => rfl
    | cons g w ih => exact (ih (x ∘ generator g)).trans (one g x)
  have invariant (x : Fin 10 → Bool) : target (x ∘ σ a b) = target x := word _ x
  let ρ (i : Nat) := if h : i < 10 then (σ a b ⟨i,h⟩).val else if i = 10 then src a b else i
  have srcCases : src a b = 99 ∨ src a b = 0 ∨ src a b = 10 := by
    rcases kinds a b with h | h | h
    · exact Or.inl h.1
    · exact Or.inr (Or.inl h.1)
    · exact Or.inr (Or.inr h.1)
  have hρ (n : Nat) (lo : 11 ≤ n) (hi : n ≤ 28) (i : Nat) : ρ i = n ↔ i = n := by
    by_cases h : i < 10
    · simp only [ρ,dite_eq_left h]
      have := (σ a b ⟨i,h⟩).isLt
      omega
    · by_cases e : i = 10
      · simp only [ρ,dite_eq_right h,ite_eq_left e]
        rcases srcCases with s|s|s <;> omega
      · simp [ρ,h,e]
  let raw (x : Fin 10 → Bool) (i : Fin 11) := (List.ofFn (x ∘ σ a b)).getD i.val false
  have rawGood (x : Fin 10 → Bool) (i : Fin 11) (h : i.val < 10) :
      raw x i = x (σ a b ⟨i.val % 10, Nat.mod_lt _ (by decide)⟩) := by
    change (List.ofFn (x ∘ σ a b)).getD i.val false = _
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using h),List.getElem_ofFn]
    simp [Nat.mod_eq_of_lt h]
  have rawBad (x : Fin 10 → Bool) (i : Fin 11) (h : i.val = 10) : raw x i = false := by
    simp [raw,h,List.getD_eq_getElem?_getD]
  let observed (x : Fin 10 → Bool) := List.ofFn x ++ [x 0 || x (k a b)]
  have gift (x : Fin 10 → Bool) : (raw x a || raw x b) = (observed x).getD (src a b) false := by
    rcases kinds a b with ⟨s,ha,hb⟩ | ⟨s,ha,hb,hn⟩ | ⟨s,ha,hb,za,zb⟩
    · rw [rawBad _ _ ha,rawBad _ _ hb,s,List.getD_eq_default _ _ (by simp [observed])]
      rfl
    · have each (i : Fin 11) (hi : i.val = 10 ∨ σ a b ⟨i.val % 10,Nat.mod_lt _ (by decide)⟩ = 0) :
          raw x i = if i.val = 10 then false else x 0 := by
        by_cases e : i.val = 10
        · simp [e,rawBad _ _ e]
        · have lt : i.val < 10 := by have := i.isLt; omega
          simp [e,rawGood _ _ lt,hi.resolve_left e]
      rw [each a ha,each b hb,s,List.getD_append _ _ _ _ (by simp)]
      simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,show 0 < 10 by decide,dite_eq_left,Option.getD_some]
      by_cases ea : a.val = 10 <;> by_cases eb : b.val = 10
      · rcases hn with h|h <;> omega
      · simp [ea,eb]
      · simp [ea,eb]
      · simp [ea,eb]
    · rw [rawGood _ _ ha,rawGood _ _ hb,za,zb,s]
      change _ = (List.ofFn x ++ [x 0 || x (k a b)]).getD 10 false
      rw [List.getD_append_right _ _ _ _ (by simp),List.length_ofFn]
      rfl

  let rg (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩
  have app (w : List Bool) (z : Bool) (i : Nat) :
      (w ++ [z]).getD i false = if i = w.length then z else w.getD i false := by
    by_cases hi : i < w.length
    · rw [List.getD_append _ _ _ _ hi, ite_eq_right (by omega)]
    · by_cases eq : i = w.length
      · subst i
        simp [List.getD_eq_getElem?_getD]
      · rw [ite_eq_right eq, List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by omega)]
  have simulation (gs : List Gate) (xs ys : List Bool)
      (len : xs.length = ys.length) (lower : 11 ≤ xs.length) (cap : xs.length + gs.length ≤ 28)
      (initial : ∀ i, xs.getD i false = ys.getD (ρ i) false) :
      ∀ i, ((⟨gs,0⟩ : Circuit).wires xs).getD i false =
        ((⟨gs.map rg,0⟩ : Circuit).wires ys).getD (ρ i) false := by
    induction gs generalizing xs ys with
    | nil => exact initial
    | cons g gs ih =>
      let z := g.op.eval (g.inputs.map fun i => xs.getD i false)
      have next : (rg g).op.eval ((rg g).inputs.map fun i => ys.getD i false) = z := by
        change g.op.eval _ = g.op.eval _
        congr 1
        simp only [rg,List.map_map,Function.comp_def]
        exact List.map_congr_left fun i _ => (initial i).symm
      change ∀ i, ((⟨gs,0⟩ : Circuit).wires (xs ++ [z])).getD i false =
        ((⟨gs.map rg,0⟩ : Circuit).wires (ys ++ [(rg g).op.eval ((rg g).inputs.map fun i => ys.getD i false)])).getD (ρ i) false
      rw [next]
      apply ih
      · simp [len]
      · simp; omega
      · simp_all only [List.length_cons,List.length_append,List.length_nil]; omega
      · intro i
        simp only [app,←len,hρ _ lower (by omega) i,initial i]
  let D : Circuit := ⟨C.gates.map rg,0⟩
  have newFan : FanInTwo D := by
    intro g hg
    obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hg
    simpa [rg] using fan h hh
  have newCap : D.size ≤ 17 := by
    change (C.gates.map rg).length ≤ 17
    rw [List.length_map]
    exact budget
  have physical (x : Fin 10 → Bool) (i : Nat) :
      (C.wires (List.ofFn (x ∘ σ a b) ++ [raw x a || raw x b])).getD i false =
        (D.wires (observed x)).getD (ρ i) false := by
    apply simulation
    · simp [observed]
    · simp
    · have h : C.gates.length ≤ 17 := budget
      simpa only [List.length_append,List.length_ofFn,List.length_cons,List.length_nil] using (show 10 + (0+1) + C.gates.length ≤ 28 by omega)
    · intro j
      by_cases hj : j < 10
      · simp only [ρ,dite_eq_left hj,observed]
        rw [List.getD_append _ _ _ _ (by simpa using hj), List.getD_append _ _ _ _ (by simp)]
        rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hj),List.getElem_ofFn,
          List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact (σ a b ⟨j,hj⟩).isLt),List.getElem_ofFn]
        rfl
      · by_cases he : j = 10
        · subst j
          simp only [ρ,show ¬ 10 < 10 by decide,ite_eq_left]
          rw [List.getD_append_right _ _ _ _ (by simp),List.length_ofFn]
          exact gift x
        · have high : 11 ≤ j := by omega
          simp only [ρ,dite_eq_right hj,ite_eq_right he]
          rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp [observed]; omega)]
  let I := 10 + u.val
  let J := 10 + v.val
  have miss : ∃ x : Fin 10 → Bool,
      (((D.wires (observed x)).getD (ρ I) false) || ((D.wires (observed x)).getD (ρ J) false)) ≠ target x := by
    rcases choices a b with h | h
    · simpa only [observed,h,target] using adjacent D (ρ I) (ρ J) newFan newCap
    · simpa only [observed,h,target] using nonadjacent D (ρ I) (ρ J) newFan newCap
  obtain ⟨x,hx⟩ := miss
  dsimp only
  intro _ _ sound
  let y := x ∘ σ a b
  let pre := (⟨[⟨.or,[a.val,b.val]⟩],0⟩ : Circuit).wires (List.ofFn y)
  have starter : pre = List.ofFn y ++ [raw x a || raw x b] := by
    change (_ ++ [raw x a || (raw x b || false)]) = _
    simp
  have mismatch : ((C.wires pre).getD I false || (C.wires pre).getD J false) ≠ target y := by
    rw [starter,physical,physical,invariant]
    exact hx
  have zsound : target y = false → (C.wires pre).getD I false = false ∧ (C.wires pre).getD J false = false := sound y
  refine ⟨y,?_⟩
  change target y = true ∧ (C.wires pre).getD I false = false ∧ (C.wires pre).getD J false = false
  cases ht : target y <;> cases hu : (C.wires pre).getD I false <;> cases hv : (C.wires pre).getD J false <;> simp_all only [Bool.false_eq_true, Bool.true_eq_false, Bool.false_or,Bool.true_or,not_true_eq_false, ne_eq, and_self,true_and, and_true]
