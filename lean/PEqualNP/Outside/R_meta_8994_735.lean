import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

-- The graph expansion follows the accepted reduction R_meta_8994_219.
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_8994_735
    (boundary : ∀ v : Fin 4, let w := (fun (v : Fin 4) (i : Fin 10) => ((([[573646056668168195, 364018345404547120, 441788239209677572, 6949090793731527712, 17870292703888028160], [141089383624196099, 112520450509160496, 81922481183163140, 1760944013404017696, 18302638278215479809], [14773284572950937603, 183100317730127920, 226037669360026368, 3490326305009570848, 18158523055276569089], [17660091934103814147, 156078716463398960, 235255905995916048, 630540541166883840, 18158523193512440321]] : List (List ℕ)).getD v.val []).getD (i.val / 2) 0 >>> (32*(i.val % 2))) % 4294967296) v
    ∀ F : (Fin 10 → Bool) → Bool,
    (∀ x y, (∀ i, x i=true → y i=true) → F x=true → F y=true) →
    ((∀ x, F x=(fun (v : Fin 4) (z : Fin 10 → Bool) =>
    let y : Fin 11 → Bool := (Fin.ofNat 11 v.val).insertNth false z
    ([9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97] : List ℕ).any fun e => y (Fin.ofNat 11 (e/11)) && y (Fin.ofNat 11 (e%11))) v x) ↔
      ∀ k : Fin 32, F (fun i=>(w i).testBit k.val)=decide (k.val<14)))
    (synthesis : ∀ (v : Fin 4) (gs : List (Bool × ℕ × ℕ)), gs.length≤18 → ∀ o : ℕ,
    let r := (gs.foldl (fun (w : List ℕ) (g : Bool × ℕ × ℕ) =>
    let a := w.getD g.2.1 0
    let b := w.getD g.2.2 0
    w ++ [bif g.1 then a ||| b else a &&& b]) (List.ofFn ((fun (v : Fin 4) (i : Fin 10) => ((([[573646056668168195, 364018345404547120, 441788239209677572, 6949090793731527712, 17870292703888028160], [141089383624196099, 112520450509160496, 81922481183163140, 1760944013404017696, 18302638278215479809], [14773284572950937603, 183100317730127920, 226037669360026368, 3490326305009570848, 18158523055276569089], [17660091934103814147, 156078716463398960, 235255905995916048, 630540541166883840, 18158523193512440321]] : List (List ℕ)).getD v.val []).getD (i.val / 2) 0 >>> (32*(i.val % 2))) % 4294967296) v))).getD o 0
    ∃ k : Fin 32, r.testBit k.val≠decide (k.val<14)) :
    let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), ↑x2 < (4 : ℕ) → PEqualNP.TopForm.IsAO2 (10 : ℕ) x3 → (∀ (x6 : Fin (10 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (10 : ℕ) x3 x6 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ (x2.insertNth Bool.false x6)) → (19 : ℕ) ≤ x3.size := by
  intro G v C hv legal correct
  by_contra! small
  let edges : List (Fin 11 × Fin 11) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),(4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  let edge (x : Fin 11 → Bool) := ([9,10,15,19,27,32,39,40,52,54,63,64,73,76,86,97] : List ℕ).any
    (fun e => x (Fin.ofNat 11 (e / 11)) && x (Fin.ofNat 11 (e % 11)))
  have adj : ∀ a b : Fin 11, G.Adj a b ↔ (a,b) ∈ edges ∨ (b,a) ∈ edges := by decide +kernel
  have graph (x : Fin 11 → Bool) : graphFun G ∅ x = edge x := by
    have val : graphFun G ∅ x = edges.any (fun e => x e.1 && x e.2) := by
      apply Bool.eq_iff_iff.mpr
      delta graphFun
      simp only [Finset.notMem_empty,false_and,exists_false,decide_false,Bool.false_or,
        decide_eq_true_eq,List.any_eq_true,Bool.and_eq_true]
      constructor
      · rintro ⟨a,b,e,ha,hb⟩
        rcases (adj a b).mp e with h | h
        · exact ⟨(a,b),h,ha,hb⟩
        · exact ⟨(b,a),h,hb,ha⟩
      · rintro ⟨⟨a,b⟩,h,ha,hb⟩
        exact ⟨a,b,(adj a b).mpr (Or.inl h),ha,hb⟩
    exact val.trans (by rfl)
  have packing : ∀ (C : Circuit), (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a,b]) → ∀ (w : List ℕ) (k : ℕ),
      C.eval (w.map (fun z => z.testBit k)) = ((C.gates.foldl (fun (w : List ℕ) (g : Gate) =>
        let a := w.getD (g.inputs.getD 0 0) 0
        let b := w.getD (g.inputs.getD 1 0) 0
        w ++ [bif g.op.eval [false,true] then a ||| b else a &&& b]) w).getD C.output 0).testBit k := by
    intro C hC w k
    let packed (w : List ℕ) (g : Gate) : List ℕ :=
          let a := w.getD (g.inputs.getD 0 0) 0
          let b := w.getD (g.inputs.getD 1 0) 0
          w ++ [bif g.op.eval [false,true] then a ||| b else a &&& b]
    let stepB (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    have get (w : List ℕ) (i : ℕ) : (w.map (fun z => z.testBit k)).getD i false = (w.getD i 0).testBit k := by
      simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
      cases w[i]? <;> simp
    have andEval (l : List Bool) : GateOp.and.eval l=l.all id := rfl
    have orEval (l : List Bool) : GateOp.or.eval l=l.any id := rfl
    have step_eq (ws : List ℕ) (g : Gate) (h : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a,b]) :
        stepB (ws.map (fun z => z.testBit k)) g = (packed ws g).map (fun z => z.testBit k) := by
      obtain ⟨op,a,b,ab⟩ := h
      rcases op with op|op <;> simp [stepB,packed,op,ab,andEval,orEval,get,Nat.testBit_and,Nat.testBit_or]
      all_goals cases ws[a]? <;> cases ws[b]? <;> simp
    have run (gs : List Gate) (h : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ a b : ℕ, g.inputs = [a,b]) (ws : List ℕ) :
        gs.foldl stepB (ws.map (fun z => z.testBit k)) = (gs.foldl packed ws).map (fun z => z.testBit k) := by
      induction gs generalizing ws with
      | nil => rfl
      | cons g gs ih =>
        simp only [List.foldl_cons,step_eq ws g (h g List.mem_cons_self)]
        exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) _
    change (C.gates.foldl stepB (w.map (fun z => z.testBit k))).getD C.output false = _
    rw [run C.gates hC w]
    exact get _ _
  let p : Fin 4 := ⟨v.val,hv⟩
  have cast : Fin.ofNat 11 p.val=v := Fin.ext (Nat.mod_eq_of_lt v.isLt)
  let ws := fun (v : Fin 4) (i : Fin 10) => ((([[573646056668168195, 364018345404547120, 441788239209677572, 6949090793731527712, 17870292703888028160], [141089383624196099, 112520450509160496, 81922481183163140, 1760944013404017696, 18302638278215479809], [14773284572950937603, 183100317730127920, 226037669360026368, 3490326305009570848, 18158523055276569089], [17660091934103814147, 156078716463398960, 235255905995916048, 630540541166883840, 18158523193512440321]] : List (List ℕ)).getD v.val []).getD (i.val / 2) 0 >>> (32*(i.val % 2))) % 4294967296
  let f := fun (v : Fin 4) (z : Fin 10 → Bool) =>
    let y : Fin 11 → Bool := (Fin.ofNat 11 v.val).insertNth false z
    ([9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97] : List ℕ).any fun e => y (Fin.ofNat 11 (e/11)) && y (Fin.ofNat 11 (e%11))
  have mono (x y : Fin 10 → Bool) (le : ∀ i,x i=true → y i=true) :
      f p x=true → f p y=true := by
    have ext (i : Fin 11) : ((Fin.ofNat 11 p.val).insertNth false x : Fin 11 → Bool) i=true →
        ((Fin.ofNat 11 p.val).insertNth false y : Fin 11 → Bool) i=true := by
      refine Fin.succAboveCases (Fin.ofNat 11 p.val) ?_ (fun j=>?_) i
      · simp
      · simpa using le j
    intro hit
    obtain ⟨e,he,ab⟩ := List.any_eq_true.mp hit
    simp only [Bool.and_eq_true] at ab
    obtain ⟨a,b⟩ := ab
    apply List.any_eq_true.mpr
    exact ⟨e,he,by simp only [Bool.and_eq_true]; exact ⟨ext _ a,ext _ b⟩⟩
  have tests := (boundary p (f p) mono).mp (fun _=>rfl)
  let enc (g : Gate) : Bool × ℕ × ℕ := (g.op.eval [false,true],g.inputs.getD 0 0,g.inputs.getD 1 0)
  obtain ⟨k,fail⟩ := synthesis p (C.gates.map enc) (by rw [List.length_map]; change C.size≤18; omega) C.output
  have shape (g : Gate) (hg : g∈C.gates) : (g.op=.and ∨ g.op=.or) ∧ ∃ a b : ℕ,g.inputs=[a,b] := by
    refine ⟨legal.1 g hg,?_⟩
    have len := legal.2.2 g hg
    exact List.length_eq_two.mp len
  have sim := packing C shape (List.ofFn (ws p)) k.val
  have rowEq : (List.ofFn (ws p)).map (fun x=>x.testBit k.val)=
      List.ofFn (fun i=>(ws p i).testBit k.val) := by rw [List.map_ofFn]; rfl
  rw [rowEq] at sim
  have yes := correct (fun i=>(ws p i).testBit k.val)
  rw [graph] at yes
  change C.eval _=edge _ at yes
  have raw := tests k
  change edge ((Fin.ofNat 11 p.val).insertNth false (fun i=>(ws p i).testBit k.val))=_ at raw
  rw [cast] at raw
  apply fail
  rw [List.foldl_map]
  exact sim.symm.trans (yes.trans raw)
