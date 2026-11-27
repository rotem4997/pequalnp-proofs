import PEqualNP.Defs

open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_5018_37
    (andCase : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) → (∀ a (p : G.Walk a a), p.IsCycle → 7 ≤ p.length) →
      (∀ a b, G.Adj a b → a ∉ A) → (∃ a b, G.Adj a b) →
      (∀ T : Finset (Fin n), (∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T) → k ≤ T.card) →
      IsMinimalCircuit n C → circuitFun n C = NestedCover.graphFun G A →
      ∀ v ∉ A, ∀ g : Gate,
      C.gates.filter (fun h => (h.inputs.take (bif h.op.eval [false] then 1 else 2)).contains v.val) = [g] →
      g.op = GateOp.and → (∀ u : Fin n, u ≠ v → g.inputs ≠ [v.val,u.val] ∧ g.inputs ≠ [u.val,v.val]) →
      A.card + G.edgeSet.ncard + k ≤ C.size + 1)
    (orCase : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) → (∀ a (p : G.Walk a a), p.IsCycle → 7 ≤ p.length) →
      (∀ a b, G.Adj a b → a ∉ A) → (∃ a b, G.Adj a b) →
      (∀ T : Finset (Fin n), (∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T) → k ≤ T.card) →
      IsMinimalCircuit n C → circuitFun n C = NestedCover.graphFun G A →
      ∀ v ∉ A, ∀ g : Gate,
      C.gates.filter (fun h => (h.inputs.take (bif h.op.eval [false] then 1 else 2)).contains v.val) = [g] →
      g.op = GateOp.or → (∀ u : Fin n, u ≠ v → u ∉ A → g.inputs ≠ [v.val,u.val] ∧ g.inputs ≠ [u.val,v.val]) →
      A.card + G.edgeSet.ncard + k ≤ C.size + 1)
    (notCase : ∀ (n k : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) (C : Circuit),
      (∀ v ∉ A, (G.neighborSet v).ncard = 3) → (∀ a (p : G.Walk a a), p.IsCycle → 7 ≤ p.length) →
      (∀ a b, G.Adj a b → a ∉ A) → (∃ a b, G.Adj a b) →
      (∀ T : Finset (Fin n), (∀ a b, G.Adj a b → a ∈ T ∨ b ∈ T) → k ≤ T.card) →
      IsMinimalCircuit n C → circuitFun n C = NestedCover.graphFun G A →
      ∀ v ∉ A, ∀ g : Gate,
      C.gates.filter (fun h => (h.inputs.take (bif h.op.eval [false] then 1 else 2)).contains v.val) = [g] →
      g.op = GateOp.not → g.inputs.head? = some v.val →
      A.card + G.edgeSet.ncard + k ≤ C.size + 1) :
  ∀ (x1 x2 : ℕ) (x3 : SimpleGraph (Fin x1)) (x4 : Finset (Fin x1)) (x5 : (Fin x1 → Bool) → Bool) (x6 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x7 ∉ x4, (x3.neighborSet x7).ncard = (3 : ℕ)) → (∀ (x8 : Fin x1) (x9 : x3.Walk x8 x8), x9.IsCycle → (7 : ℕ) ≤ x9.length) → (∀ (x9 x10 : Fin x1), x3.Adj x9 x10 → x9 ∉ x4) → (∃ (x10 : Fin x1) (x11 : Fin x1), x3.Adj x10 x11) → (∀ (x11 : Finset (Fin x1)), (∀ (x12 x13 : Fin x1), x3.Adj x12 x13 → x12 ∈ x11 ∨ x13 ∈ x11) → x2 ≤ x11.card) → (∀ (x12 : Fin x1 → Bool), x5 x12 = Bool.true ↔ (∃ x13 ∈ x4, x12 x13 = Bool.true) ∨ ∃ (x13 : Fin x1) (x14 : Fin x1), x3.Adj x13 x14 ∧ x12 x13 = Bool.true ∧ x12 x14 = Bool.true) → PEqualNP.MetaComplexity.FanInTwo x6 → PEqualNP.MetaComplexity.circuitFun x1 x6 = x5 → (∀ (x15 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x5 x15 → x6.size ≤ x15) → (∃ x16 ∉ x4, (List.filter (fun (x17 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x17.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x17.inputs).contains ↑x16) x6.gates).length = (1 : ℕ)) → x4.card + x3.edgeSet.ncard + x2 ≤ x6.size + (1 : ℕ) := by
  -- Holding a second input fixed leaves a sensitive edge at v in the truth table.
  have tests {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
      (f : (Fin n → Bool) → Bool) (v u : Fin n) (hv : v ∉ A) (huv : u ≠ v)
      (hd : (G.neighborSet v).ncard = 3) (hi : ∀ a b, G.Adj a b → a ∉ A)
      (hg : ∀ a (p : G.Walk a a), p.IsCycle → 7 ≤ p.length)
      (spec : ∀ x, f x = true ↔ (∃ a ∈ A, x a = true) ∨ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true)
      (b : Bool) (hu : b = true → u ∉ A) :
      ∃ x y, x u = b ∧ y u = b ∧ (∀ a, a ≠ v → x a = y a) ∧ f x ≠ f y := by
    clear andCase orCase notCase
    classical
    have two : ∃ i ∈ G.neighborSet v, ∃ j ∈ G.neighborSet v, i ≠ j := by
      have h : 1 < (G.neighborSet v).ncard := by omega
      exact (Set.one_lt_ncard (Set.toFinite _)).mp h
    obtain ⟨i,hi',j,hj',hij⟩ := two
    change G.Adj v i at hi'
    change G.Adj v j at hj'
    have witness : ∃ t, G.Adj v t ∧ (if b then t = u ∨ ¬G.Adj u t else t ≠ u) := by
      cases b with
      | false =>
        by_cases h : i = u
        · exact ⟨j,hj',by simpa [← h] using hij.symm⟩
        · exact ⟨i,hi',h⟩
      | true =>
        by_cases h : G.Adj v u
        · exact ⟨u,h,Or.inl rfl⟩
        by_cases e : G.Adj u i
        · refine ⟨j,hj',Or.inr ?_⟩
          intro d
          let p : G.Walk v v := .cons hi' (.cons e.symm (.cons d (.cons hj'.symm .nil)))
          have hp : p.IsCycle := by
            rw [Walk.isCycle_iff_isPath_tail_and_le_length]
            simp [p, Walk.isPath_def, hi'.ne.symm,e.ne.symm,d.ne,
              hj'.ne.symm,hij,huv]
          have hh := hg v p hp
          change 7 ≤ 4 at hh
          omega
        · exact ⟨i,hi',Or.inr e⟩
    obtain ⟨t,ht,htb⟩ := witness
    let x : Fin n → Bool := fun a => decide (a = t ∨ b = true ∧ a = u)
    let y : Fin n → Bool := fun a => decide (a = v ∨ a = t ∨ b = true ∧ a = u)
    refine ⟨x,y,?_,?_,?_,?_⟩
    · cases b with
      | false => simp [x,(show t ≠ u from htb).symm]
      | true => simp [x]
    · cases b with
      | false => simp [y,huv,(show t ≠ u from htb).symm]
      | true => simp [y]
    · intro a ha
      simp [x,y,ha]
    · have hy : f y = true := (spec y).2 (.inr ⟨v,t,ht,by simp [y],by simp [y]⟩)
      rw [hy]
      intro hx
      rcases (spec x).1 hx with ⟨a,ha,hx⟩ | ⟨a,c,hac,ha,hc⟩
      · simp only [x,decide_eq_true_eq] at hx
        rcases hx with rfl | ⟨hb,rfl⟩
        · exact hi _ _ ht.symm ha
        · exact hu hb ha
      · simp only [x,decide_eq_true_eq] at ha hc
        rcases ha with rfl | ⟨hb,rfl⟩ <;> rcases hc with rfl | ⟨hb',rfl⟩
        · exact hac.ne rfl
        · simp [hb'] at htb
          rcases htb with eq | h
          · exact hac.ne eq
          · exact h hac.symm
        · simp [hb] at htb
          rcases htb with eq | h
          · exact hac.ne eq.symm
          · exact h hac
        · exact hac.ne rfl
  -- A masked sole reader preserves agreement at every wire other than v.
  have mask {n : ℕ} (C : Circuit) (v u : Fin n) (b : Bool)
      (fan : FanInTwo C) (out : C.output ≠ v.val)
      (uniq : (C.gates.filter (fun g => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val)).length = 1)
      (g : Gate) (hg : g ∈ C.gates) (op : g.op = (if b then GateOp.or else GateOp.and))
      (pins : g.inputs = [v.val,u.val] ∨ g.inputs = [u.val,v.val])
      (x y : Fin n → Bool) (hx : x u = b) (hy : y u = b) (ha : ∀ i, i ≠ v → x i = y i) :
      circuitFun n C x = circuitFun n C y := by
    clear tests andCase orCase notCase
    classical
    have andEval (bs : List Bool) : GateOp.and.eval bs = bs.all id := rfl
    have orEval (bs : List Bool) : GateOp.or.eval bs = bs.any id := rfl
    have notPin : GateOp.not.eval [false] = true := rfl
    let read := fun (g : Gate) => (g.inputs.take (bif g.op.eval [false] then 1 else 2)).contains v.val
    have rg : read g := by
      rcases pins with h|h <;> cases b <;> simp [read,h,op,andEval,orEval]
    have only (h : Gate) (hm : h ∈ C.gates) (hr : read h) : h = g := by
      obtain ⟨k,hk⟩ := List.length_eq_one_iff.mp uniq
      have hh : h ∈ C.gates.filter read := List.mem_filter.mpr ⟨hm,hr⟩
      have gg : g ∈ C.gates.filter read := List.mem_filter.mpr ⟨hg,rg⟩
      change C.gates.filter read = [k] at hk
      rw [hk,List.mem_singleton] at hh gg
      exact hh.trans gg.symm
    let step := fun (w : List Bool) (k : Gate) => w ++ [k.op.eval (k.inputs.map fun i => w.getD i false)]
    have loop (gs : List Gate) (mem : ∀ h ∈ gs, h ∈ C.gates) (l r : List Bool)
        (len : l.length = r.length) (hu : u.val < l.length)
        (ul : l.getD u.val false = b) (ur : r.getD u.val false = b)
        (same : ∀ i, i ≠ v.val → l.getD i false = r.getD i false) :
        ∀ i, i ≠ v.val → (gs.foldl step l).getD i false = (gs.foldl step r).getD i false := by
      induction gs generalizing l r with
      | nil => exact same
      | cons h gs ih =>
        have hm := mem h List.mem_cons_self
        have eq : h.op.eval (h.inputs.map fun i => l.getD i false) =
                  h.op.eval (h.inputs.map fun i => r.getD i false) := by
          by_cases hr : read h
          · have he := only h hm hr
            subst h
            simp only [List.getD_eq_getElem?_getD] at ul ur
            rcases pins with p|p <;> cases b <;> simp [p,op,andEval,orEval,ul,ur]
          · have hf := fan h hm
            rcases hf.1 with andOp | orOp | notOp
            · change h.op = GateOp.and at andOp
              have htake : h.inputs.take 2 = h.inputs := List.take_of_length_le hf.2
              have miss : v.val ∉ h.inputs := by simpa [read,andOp,andEval,htake] using hr
              rw [List.map_congr_left fun i hi => same i (fun e => miss (e ▸ hi))]
            · change h.op = GateOp.or at orOp
              have htake : h.inputs.take 2 = h.inputs := List.take_of_length_le hf.2
              have miss : v.val ∉ h.inputs := by simpa [read,orOp,orEval,htake] using hr
              rw [List.map_congr_left fun i hi => same i (fun e => miss (e ▸ hi))]
            · change h.op = GateOp.not at notOp
              rw [notOp]
              cases hp : h.inputs with
              | nil => rfl
              | cons i rest =>
                have ne : i ≠ v.val := by intro e; subst i; simp [read,notOp,hp,notPin] at hr
                change (!(l.getD i false)) = (!(r.getD i false))
                rw [same i ne]
        change ∀ i, i ≠ v.val → (gs.foldl step (step l h)).getD i false = _
        refine ih (fun k hk => mem k (List.mem_cons_of_mem _ hk)) _ _ ?_ ?_ ?_ ?_ ?_
        · simp [step,len]
        · simp [step]; omega
        · exact (List.getD_append _ _ _ _ hu).trans ul
        · exact (List.getD_append _ _ _ _ (len ▸ hu)).trans ur
        · intro i hv
          change (l ++ [_]).getD i false = (r ++ [_]).getD i false
          by_cases hi : i < l.length
          · rw [List.getD_append _ _ _ _ hi,List.getD_append _ _ _ _ (len ▸ hi),same i hv]
          · rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,
                List.getElem?_append_right (Nat.le_of_not_gt hi),
                List.getElem?_append_right (len ▸ Nat.le_of_not_gt hi),eq,len]
    have base (z : Fin n → Bool) (i : Fin n) : (List.ofFn z).getD i.val false = z i := by
      rw [List.getD_eq_getElem?_getD]
      simp [i.isLt]
    refine loop C.gates (fun _ h => h) (List.ofFn x) (List.ofFn y) (by simp)
      (by simp) ((base x u).trans hx) ((base y u).trans hy) ?_ _ out
    intro i hi
    by_cases hn : i < n
    · exact (base x ⟨i,hn⟩).trans ((ha _ (fun e => hi (congrArg Fin.val e))).trans (base y ⟨i,hn⟩).symm)
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hn),
          List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hn)]
  intro n k G A f C deg girth iso edge cover spec fan computes least single
  obtain ⟨v,hv,reads⟩ := single
  classical
  have out : C.output ≠ v.val := by
    intro e
    let z : Fin n → Bool := fun i => decide (i = v)
    let step := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have keep (gs : List Gate) (l : List Bool) (lt : v.val < l.length) :
        (gs.foldl step l).getD v.val false = l.getD v.val false := by
      induction gs generalizing l with
      | nil => rfl
      | cons g gs ih =>
        change (gs.foldl step (step l g)).getD v.val false = _
        rw [ih _ (by simp [step]; omega)]
        exact List.getD_append _ _ _ _ lt
    have h : f z = true := by
      rw [← computes]
      change (C.gates.foldl step (List.ofFn z)).getD C.output false = true
      rw [e,keep _ _ (by simp),List.getD_eq_getElem?_getD]
      simp [z]
    rcases (spec z).1 h with ⟨a,ha,za⟩ | ⟨a,b,adj,za,zb⟩
    · have ea : a = v := of_decide_eq_true za
      exact hv (ea ▸ ha)
    · exact adj.ne ((of_decide_eq_true za : a = v).trans (of_decide_eq_true zb : b = v).symm)
  obtain ⟨g,filterEq⟩ := List.length_eq_one_iff.mp reads
  have mem : g ∈ C.gates.filter (fun h => (h.inputs.take (bif h.op.eval [false] then 1 else 2)).contains v.val) := by
    rw [filterEq]
    exact List.mem_singleton_self _
  obtain ⟨hg,rg⟩ := List.mem_filter.mp mem
  have normalized : circuitFun n C = NestedCover.graphFun G A := by
    rw [computes]
    funext x
    apply Bool.eq_iff_iff.mpr
    unfold NestedCover.graphFun
    simpa only [Bool.or_eq_true,decide_eq_true_eq] using spec x
  have minC : IsMinimalCircuit n C := by
    refine ⟨fan,fun D hd he => least D.size ⟨D,hd,le_rfl,?_⟩⟩
    exact fun x => congrFun (he.trans computes) x
  have exclude (b : Bool) (op : g.op = (if b then GateOp.or else GateOp.and))
      (u : Fin n) (huv : u ≠ v) (ub : b = true → u ∉ A) :
      g.inputs ≠ [v.val,u.val] ∧ g.inputs ≠ [u.val,v.val] := by
    obtain ⟨x,y,hx,hy,agree,apart⟩ := tests G A f v u hv huv (deg v hv) iso girth spec b ub
    have bad (pins : g.inputs = [v.val,u.val] ∨ g.inputs = [u.val,v.val]) : False :=
      apart (computes ▸ mask C v u b fan out reads g hg op pins x y hx hy agree)
    exact ⟨fun p => bad (.inl p),fun p => bad (.inr p)⟩
  rcases (fan g hg).1 with h | h | h
  · exact andCase n k G A C deg girth iso edge cover minC normalized v hv g filterEq h
      (fun u huv => exclude false h u huv (by intro e; contradiction))
  · exact orCase n k G A C deg girth iso edge cover minC normalized v hv g filterEq h
      (fun u huv hu => exclude true h u huv (fun _ => hu))
  · change g.op = GateOp.not at h
    apply notCase n k G A C deg girth iso edge cover minC normalized v hv g filterEq h
    cases p : g.inputs with
    | nil => simp [p] at rg
    | cons i tail =>
      have e : GateOp.not.eval [false] = true := rfl
      have hvu : v.val = i := by simpa [h,e,p] using rg
      exact congrArg some hvu.symm
