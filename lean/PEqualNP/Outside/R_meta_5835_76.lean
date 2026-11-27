import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 32768 in
set_option maxHeartbeats 16000000 in
theorem PEqualNP.Outside.R_meta_5835_76
  (floor : let E : List (Fin 10 × Fin 10) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
    ∀ C : Circuit, FanInTwo C →
    (∀ x : Fin 10 → Bool,
      (x 0 = true ∧ x 1 = false ∧ x 4 = false ∧ x 5 = false) ∨
      ((x 0 || x 1) = true ∧ (List.ofFn x).count true ≤ 2) →
      C.eval (List.ofFn x) = E.any (fun e => x e.1 && x e.2)) →
    12 + PEqualNP.NotBracket.notCount C ≤ C.size)
  (positive : let B := ([0,134217727,78959277,55258451,67371142,26740244,4333592,16910624,1331264,7963008,106962432,125952000] : List (BitVec 27))
    ∀ P : List (BitVec 27), P.length ≤ 17 →
      (∀ i : Fin P.length, let U := B ++ P.take i.val
        ∃ a ∈ U, ∃ b ∈ U, P.get i = a &&& b ∨ P.get i = a ||| b) →
      (131071 : BitVec 27) ∉ B ++ P)
  (signed : let E : List (Fin 10 × Fin 10) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
    let F := (Fin 10 → Bool) → Bool
    let R : List F := [(fun _ : Fin 10 → Bool => false),(fun _ : Fin 10 → Bool => true)] ++
      List.ofFn (fun (i : Fin 10) (x : Fin 10 → Bool) => x i)
    ∀ N P : List F, 1 ≤ N.length → N.length ≤ 5 → P.length + N.length ≤ 17 →
      let A := fun (Q : List F) (w : F) => w ∈ R ++ Q ∨ ∃ h ∈ R ++ Q, h ∈ N ∧ w = (fun x => !(h x))
      (∀ i : Fin P.length, ∃ a b, A (P.take i.val) a ∧ A (P.take i.val) b ∧
        (P.get i = (fun x => a x && b x) ∨ P.get i = (fun x => a x || b x))) →
      ∀ z : F, A P z → ∃ x : Fin 10 → Bool, (x 0 || x 1) = true ∧ z x ≠ E.any (fun e => x e.1 && x e.2)) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (17 : ℕ) → ∃ (x4 : Fin (10 : ℕ) → Bool), (x4 (0 : Fin (10 : ℕ)) || x4 (1 : Fin (10 : ℕ))) = Bool.true ∧ x1.eval (List.ofFn x4) ≠ (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
  intro C fan small
  by_contra fail
  let X := Fin 10 → Bool
  let F := X → Bool
  let E : List (Fin 10 × Fin 10) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
  let target (x : X) := E.any (fun e => x e.1 && x e.2)
  have verified (x : Fin 10 → Bool) (hx : (x 0 || x 1) = true) :
      C.eval (List.ofFn x) = E.any (fun e => x e.1 && x e.2) := by
    by_contra ne
    apply fail
    refine ⟨x,hx,?_⟩
    simpa [E,List.any_cons,Bool.or_assoc] using ne
  let raw : List F := List.ofFn fun (i : Fin 10) (x : X) => x i
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
  have rawMap (x : X) : raw.map (fun f => f x)=List.ofFn x := by simp [raw,List.map_ofFn,Function.comp_def]
  let endW := C.gates.foldl grow raw
  have truth (x : X) (hx : (x 0 || x 1) = true) : readW endW C.output x=target x := by
    rw [← readEval]
    change ((C.gates.foldl grow raw).map _).getD C.output false=_
    rw [commute,rawMap]
    exact verified x hx
  have floorN := floor C fan (fun x hs => verified x (by
    rcases hs with h | h
    · simp [h.1]
    · exact h.1))
  have nf : PEqualNP.NotBracket.notCount C = nc C.gates := rfl
  rw [nf] at floorN
  have fam (g : Gate) (h : g∈C.gates) : (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2 := fan g h
  have baseAll : ∀ f∈raw, A [] [] f := fun f h => Or.inl (by simp [R,h])
  obtain ⟨P,N,hP,hlen,hn,cov⟩:=program C.gates fam raw [] [] (by intro i; exact Fin.elim0 i) baseAll
  simp only [List.length_nil,Nat.zero_add] at hlen hn
  have total : P.length+N.length≤17 := hlen ▸ small
  have cap : N.length≤5 := by omega
  have hu : A P N (readW endW C.output) := reads cov C.output
  by_cases empty : N=[]
  · subst N
    let B := ([0,134217727,78959277,55258451,67371142,26740244,4333592,16910624,1331264,7963008,106962432,125952000] : List (BitVec 27))
    let rows : Array Nat := #[3,6,13,17,26,33,66,133,162,265,266,290,321,530,577,641,642,50,69,138,201,385,402,521,554,770,773]
    let inputs (i : Fin 27) (t : Fin 10) := rows[i.val]!.testBit t.val
    let valid : ∀ i : Fin 27, (inputs i 0 || inputs i 1) = true := by decide +kernel
    let row (i : Fin 27) : X := inputs i
    let obs (z : F) : BitVec 27 := (BitVec.ofBoolListLE (List.ofFn fun i : Fin 27 => z (row i))).cast (by simp)
    have bit (z : F) (i : Fin 27) : (obs z).getLsbD i.val=z (row i) := by
      let bs := List.ofFn fun i : Fin 27 => z (row i)
      have h : i.val<bs.length := by simpa [bs] using i.isLt
      change (BitVec.ofBoolListLE bs).getLsbD i.val=_
      rw [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem _ _ h]
      exact List.getElem_ofFn (f:=fun i : Fin 27 => z (row i)) h
    have obsM (a b) : obs (meet a b)=obs a &&& obs b := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simpa only [meet,BitVec.getLsbD_and,bit a ⟨i,hi⟩,bit b ⟨i,hi⟩] using bit (meet a b) ⟨i,hi⟩
    have obsJ (a b) : obs (join a b)=obs a ||| obs b := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      simpa only [join,BitVec.getLsbD_or,bit a ⟨i,hi⟩,bit b ⟨i,hi⟩] using bit (join a b) ⟨i,hi⟩
    have rawEq : R.map obs=B := by decide +kernel
    have goalEq : obs target=131071 := by decide +kernel
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
    have bad := positive (P.map obs) budget run
    have hit := lift hu
    have same : obs (readW endW C.output) = obs target := by
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      rw [bit _ ⟨k,hk⟩,bit _ ⟨k,hk⟩]
      exact truth _ (valid ⟨k,hk⟩)
    rw [same,goalEq] at hit
    exact bad hit
  · have npos : 1≤N.length := by by_contra! h; apply empty; exact List.length_eq_zero_iff.mp (by omega)
    obtain ⟨x,hx,bad⟩ := signed N P npos cap total hP (readW endW C.output) hu
    exact bad (truth x hx)
