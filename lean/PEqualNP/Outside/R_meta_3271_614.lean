import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The first premise is the checked fourteen-gate lower bound L_meta_2012.
set_option maxRecDepth 6000 in
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_3271_614
    (lower : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); ¬PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) x1 (14 : ℕ))
    (residual : ∀ C : Circuit,
      FanInTwo C → C.size ≤ 14 →
      (C.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1 →
      (∃ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ ∃ j ≥ 9,
        g.inputs = [0,j] ∨ g.inputs = [j,0]) →
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn fun i => if i = 0 then !x 0 else x i) = ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))) → False) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) → (List.filter (fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4.inputs.contains (0 : ℕ)) x1.gates).length ≤ (1 : ℕ) → (∀ (x5 : Fin (9 : ℕ) → Bool), x1.eval (List.ofFn fun (x6 : Fin (9 : ℕ)) => if x6 = (0 : Fin (9 : ℕ)) then !x5 (0 : Fin (9 : ℕ)) else x5 x6) = (x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)))) → False := by
  classical
  intro C fan budget few hfun
  let f (x : Fin 9 → Bool) := x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
    x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 ||
    x 3 && x 8 || x 5 && x 7 || x 6 && x 8 || x 8 && x 5
  let flip (x : Fin 9 → Bool) (i : Fin 9) := if i = 0 then !x 0 else x i
  have target (x : Fin 9 → Bool) : f x = ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) := by
    simp only [f, List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
    rfl
  let val (w : List Bool) (g : Gate) := g.op.eval (g.inputs.map fun i => w.getD i false)
  let step (w : List Bool) (g : Gate) := w ++ [val w g]
  have hAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
  have hOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
  have hNot (xs : List Bool) : GateOp.not.eval xs = !xs.headD false := rfl
  have read (x : Fin 9 → Bool) (i : Fin 9) : (List.ofFn x).getD i.val false = x i := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have retain (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g)]
      · exact List.getD_append _ _ _ _ h
      · simp only [step, List.length_append, List.length_singleton]
        omega
  have out : C.output ≠ 0 := by
    intro eq
    have h := hfun (fun _ => false)
    change (C.gates.foldl step (List.ofFn (flip (fun _ => false)))).getD C.output false = false at h
    rw [eq, retain _ _ _ (by simp)] at h
    change (List.ofFn (flip (fun _ => false))).getD (0 : Fin 9).val false = false at h
    rw [read] at h
    exact Bool.noConfusion h
  have noRead (g : Gate) (w z : List Bool) (noread : 0 ∉ g.inputs)
      (agree : ∀ i ≠ 0, w.getD i false = z.getD i false) : val w g = val z g := by
    change g.op.eval (g.inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => z.getD i false)
    rw [List.map_congr_left (fun i hi => agree i (fun e => noread (e ▸ hi)))]
  have relay (rename : Gate → Gate) (x y : Fin 9 → Bool) (inputEq : ∀ i ≠ 0, x i = y i)
      (same : ∀ g ∈ C.gates, ∀ w z,
        (∀ i ≠ 0, w.getD i false = z.getD i false) →
        (∀ i : Fin 9, w.getD i.val false = x i ∧ z.getD i.val false = y i) →
        val w g = val z (rename g)) :
      C.eval (List.ofFn x) = (Circuit.mk (C.gates.map rename) C.output).eval (List.ofFn y) := by
    have simulate (gs : List Gate) (sub : ∀ g ∈ gs, g ∈ C.gates)
        (w z : List Bool) (len : w.length = z.length) (enough : 9 ≤ w.length)
        (agree : ∀ i ≠ 0, w.getD i false = z.getD i false)
        (raw : ∀ i : Fin 9, w.getD i.val false = x i ∧ z.getD i.val false = y i) :
        ∀ i ≠ 0, (gs.foldl step w).getD i false = ((gs.map rename).foldl step z).getD i false := by
      induction gs generalizing w z with
      | nil => exact agree
      | cons g gs ih =>
        simp only [List.map_cons, List.foldl_cons]
        refine ih (fun g' hg' => sub g' (List.mem_cons_of_mem _ hg')) _ _ ?_ ?_ ?_ ?_
        · simp only [step, List.length_append, List.length_singleton, len]
        · simp only [step, List.length_append, List.length_singleton]
          omega
        · intro i hi
          change (w ++ [_]).getD i false = (z ++ [_]).getD i false
          rw [same g (sub g List.mem_cons_self) w z agree raw]
          by_cases low : i < w.length
          · rw [List.getD_append _ _ _ _ low, List.getD_append _ _ _ _ (by omega)]
            exact agree i hi
          · rw [List.getD_append_right _ _ _ _ (by omega),
              List.getD_append_right _ _ _ _ (by omega), len]
        · intro i
          have h := i.isLt
          exact ⟨(List.getD_append _ _ _ _ (by omega)).trans (raw i).1,
            (List.getD_append _ _ _ _ (by omega)).trans (raw i).2⟩
    apply simulate C.gates (fun _ h => h) (List.ofFn x) (List.ofFn y) (by simp) (by simp)
    · intro i hi
      by_cases low : i < 9
      · let j : Fin 9 := ⟨i,low⟩
        change (List.ofFn x).getD j.val false = (List.ofFn y).getD j.val false
        rw [read,read]
        exact inputEq j (fun e => hi (congrArg (fun k : Fin 9 => k.val) e))
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    · exact fun i => ⟨read x i,read y i⟩
    · exact out
  have atMostOne (L : List Gate) (hlen : L.length ≤ 1) :
      ∀ g ∈ L, ∀ h ∈ L, g = h := by
    cases L with
    | nil => simp
    | cons g rest =>
      have empty : rest = [] := List.length_eq_zero_iff.mp (by
        simp only [List.length_cons] at hlen
        omega)
      subst rest
      intro a ha b hb
      exact (List.mem_singleton.mp ha).trans (List.mem_singleton.mp hb).symm
  have sameReader (a b : Gate) (ha : a ∈ C.gates) (hb : b ∈ C.gates)
      (ra : 0 ∈ a.inputs) (rb : 0 ∈ b.inputs) : a = b :=
    atMostOne _ few a (List.mem_filter.mpr ⟨ha,List.contains_iff_mem.mpr ra⟩)
      b (List.mem_filter.mpr ⟨hb,List.contains_iff_mem.mpr rb⟩)
  by_cases proper : ∃ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ ∃ j ≠ 0,
      g.inputs = [0,j] ∨ g.inputs = [j,0]
  · obtain ⟨g,hg,op,j,nz,pins⟩ := proper
    by_cases high : 9 ≤ j
    · exact residual C fan budget few ⟨g,hg,op,j,high,pins⟩ (fun x => (hfun x).trans (target x))
    have reads : 0 ∈ g.inputs := by rcases pins with p | p <;> simp [p]
    let idx : Fin 9 := ⟨j,by omega⟩
    have nzidx : idx ≠ 0 := fun e => nz (congrArg (fun i : Fin 9 => i.val) e)
    let masks (i : Fin 9) (b : Bool) : ℕ :=
      if b then ![0,2,20,10,16,32,80,130,258] i else ![0,16,2,2,2,2,2,2,2] i
    let row (m : ℕ) : Fin 9 → Bool := fun i => m.testBit i.val
    have witnesses : ∀ i : Fin 9, i ≠ 0 → ∀ b : Bool,
        f (row (masks i b)) ≠ f (row (masks i b + 1)) ∧
        row (masks i b) i = b ∧ row (masks i b + 1) i = b ∧
        (∀ k : Fin 9, k ≠ 0 → row (masks i b) k = row (masks i b + 1) k) := by
      decide
    let bit := if g.op = .or then true else false
    let x := row (masks idx bit)
    let y := row (masks idx bit + 1)
    obtain ⟨ne,bx,by',agree⟩ := witnesses idx nzidx bit
    have agreeInputs (i : Fin 9) (h : i ≠ 0) : flip x i = flip y i := by
      simp only [flip, ite_eq_right h]
      exact agree i h
    apply ne
    have eq := relay id (flip x) (flip y) agreeInputs (by
      intro h hh w z off raw
      change val w h = val z h
      by_cases hr : 0 ∈ h.inputs
      · have eq := sameReader h g hh hg hr reads
        subst h
        have rd := raw idx
        simp only [flip, ite_eq_right nzidx] at rd
        have p : w.getD j false = bit := rd.1.trans bx
        have q : z.getD j false = bit := rd.2.trans by'
        rcases op with ha | ho
        · have endBit : bit = false := by simp [bit,ha]
          rcases pins with hs | hs <;>
            simp only [val,ha,hs,List.map_cons,List.map_nil,hAnd,List.all_cons,List.all_nil,id,
              p,q,endBit,Bool.and_false,Bool.false_and]
        · have endBit : bit = true := by simp [bit,ho]
          rcases pins with hs | hs <;>
            simp only [val,ho,hs,List.map_cons,List.map_nil,hOr,List.any_cons,List.any_nil,id,
              p,q,endBit,Bool.or_true,Bool.true_or]
      · exact noRead h w z hr off)
    have e : C.eval (List.ofFn (flip x)) = C.eval (List.ofFn (flip y)) := by
      simpa only [List.map_id_fun, id_eq] using eq
    exact (hfun x).symm.trans (e.trans (hfun y))
  · let repair (g : Gate) : Gate :=
      if g.op = .not then if g.inputs.head? = some 0 then ⟨.and,[0]⟩ else g
      else if 0 ∈ g.inputs then ⟨.not,[0]⟩ else g
    let D : Circuit := ⟨C.gates.map repair,C.output⟩
    have fanD : FanInTwo D := by
      intro g hg
      change g ∈ C.gates.map repair at hg
      obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hg
      unfold repair
      split_ifs
      · exact ⟨Or.inl rfl,by decide⟩
      · exact fan h hh
      · exact ⟨Or.inr (Or.inr rfl),by decide⟩
      · exact fan h hh
    have shape (g : Gate) (hg : g ∈ C.gates) (op : g.op = .and ∨ g.op = .or)
        (hit : 0 ∈ g.inputs) : g.inputs = [0] ∨ g.inputs = [0,0] := by
      have len := (fan g hg).2
      cases ins : g.inputs with
      | nil => simp [ins] at hit
      | cons i tail =>
        cases tail with
        | nil =>
          have eq : i = 0 := (List.mem_singleton.mp (ins ▸ hit)).symm
          exact Or.inl (by simp [eq])
        | cons j rest =>
          have empty : rest = [] := List.length_eq_zero_iff.mp (by
            rw [ins] at len
            simp only [List.length_cons] at len
            omega)
          subst rest
          have zeros : i = 0 ∨ j = 0 := by simpa [ins, eq_comm] using hit
          rcases zeros with e | e
          · subst i
            have e : j = 0 := Classical.byContradiction (fun nz =>
              proper ⟨g,hg,op,j,nz,Or.inl ins⟩)
            exact Or.inr (by simp [e])
          · subst j
            have e : i = 0 := Classical.byContradiction (fun nz =>
              proper ⟨g,hg,op,i,nz,Or.inr ins⟩)
            exact Or.inr (by simp [e])
    apply lower
    refine ⟨D,fanD,?_ ,?_⟩
    · change (C.gates.map repair).length ≤ 14
      rwa [List.length_map]
    · intro x
      have agreeInputs (i : Fin 9) (h : i ≠ 0) : flip x i = x i := ite_eq_right h
      have eq := relay repair (flip x) x agreeInputs (by
        intro g hg w z off raw
        have rw0 : w.getD 0 false = !x 0 := (raw 0).1
        have rz0 : z.getD 0 false = x 0 := (raw 0).2
        obtain ⟨ops,_⟩ := fan g hg
        change g.op = .and ∨ g.op = .or ∨ g.op = .not at ops
        by_cases hn : g.op = .not
        · cases pins : g.inputs with
          | nil =>
            simp only [val,repair,hn,pins,List.head?_nil,reduceCtorEq,↓reduceIte,List.map_nil,hNot,List.headD_nil]
          | cons i tail =>
            by_cases hz : i = 0
            · subst i
              simp only [val,repair,hn,pins,List.head?_cons,↓reduceIte,List.map_cons,List.map_nil,
                hNot,hAnd,List.headD_cons,List.all_cons,List.all_nil,id,Bool.and_true,rw0,rz0,Bool.not_not]
            · have headNe : (some i : Option ℕ) ≠ some 0 := fun h => hz (Option.some.inj h)
              simp only [val,repair,hn,pins,List.head?_cons,headNe,↓reduceIte,List.map_cons,
                hNot,List.headD_cons,off i hz]
        · have hop : g.op = .and ∨ g.op = .or := ops.elim Or.inl (fun h => h.elim Or.inr (fun e => (hn e).elim))
          by_cases hit : 0 ∈ g.inputs
          · have sh := shape g hg hop hit
            have patch : repair g = ⟨.not,[0]⟩ := by
              unfold repair
              rw [ite_eq_right hn, ite_eq_left hit]
            rcases hop with ho | ho <;> rcases sh with hp | hp <;>
              simp only [val,patch,ho,hp,List.map_cons,List.map_nil,hNot,hAnd,hOr,
                List.headD_cons,List.all_cons,List.all_nil,List.any_cons,List.any_nil,id,rw0,rz0,
                Bool.and_true,Bool.and_self,Bool.or_false,Bool.or_self]
          · simpa only [repair,hn,hit,↓reduceIte] using noRead g w z hit off)
      exact eq.symm.trans ((hfun x).trans (target x))
