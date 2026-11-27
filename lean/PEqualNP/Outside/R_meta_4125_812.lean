import PEqualNP.Defs

-- The packed boundary evaluator is adapted from tacyon52's checked R-meta-4125-52.
-- The first eight gates cover points 0 and 2 and enforce the two rereads.

open PEqualNP.CircuitLowerBounds in
set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_4125_812
    (maximalRows : let F := fun x : Fin 14 → Bool => ∃ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true; ∀ x, ¬ F x → (∀ y, (∀ i, x i = true → y i = true) → x ≠ y → F y) → ∃ j : Fin 37, x = fun i => (([127,244,361,480,595,720,833,1063,1188,1313,1539,2126,2244,2376,2626,3008,3078,4125,4244,4361,4625,5125,5889,6156,7300,8250,8368,8488,8722,9250,9632,10250,11778,12312,12944,14600,16256] : List ℕ).getD j.val 0).testBit i.val)
    (completion :
      let meet (a b : ℕ) := (a &&& b &&& 1729382256910270463) |||
        ((((a <<< 1) &&& b) ||| (a &&& (b <<< 1))) &&& 2882303761517117440)
      let step (w : List ℕ) (g : Bool × ℕ × ℕ) :=
        let a := w.getD g.2.1 0
        let b := w.getD g.2.2 0
        w ++ [if g.1 then a ||| b else meet a b]
      ∃ (tail : List (Bool × ℕ × ℕ)) (o : ℕ), tail.length ≤ 18 ∧
        (∀ i : Fin tail.length, let g := tail.get i
          g.2.1 ≠ g.2.2 ∧ g.2.1 < 22+i.val ∧ g.2.2 < 22+i.val) ∧
        o < 22+tail.length ∧ o ≠ 21 ∧
        455 ||| ((tail.foldl step ([1729399028130512903,15270196031782968,58150373818816,94946423956573696,54820275478360064,3870282840506368,133412159488,2776645719824533521,218716039641317512,189725234880971840,156548607029289472,229736628137037828,270286071509057568,288160007407796482,2862231898204215317,2882303761517117445,3170463768924913927,2305843009213693959,3170473751662051727,2305901159587512775,3170475987293324751,455] : List ℕ)).getD o 0) = 2097151) : have x1 : (Fin (14 : ℕ) → Bool) → Prop := fun (x1 : Fin (14 : ℕ) → Bool) => ∃ (x2 : Fin (7 : ℕ)) (x3 : Fin (7 : ℕ)), (x2 = x3 ∨ x2 = x3 + (1 : Fin (7 : ℕ)) ∨ x2 = x3 + (3 : Fin (7 : ℕ))) ∧ x1 (Fin.castAdd (7 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (7 : ℕ) x3) = Bool.true; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), x2.size ≤ (27 : ℕ) ∧ (∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (14 : ℕ) + x3 ∧ x7 < (14 : ℕ) + x3) ∧ (∀ (x3 x4 : Fin (7 : ℕ)), x3 = x4 ∨ x3 = x4 + (1 : Fin (7 : ℕ)) ∨ x3 = x4 + (3 : Fin (7 : ℕ)) → x2.eval (List.ofFn fun (x6 : Fin (14 : ℕ)) => Decidable.decide (x6 = Fin.castAdd (7 : ℕ) x3 ∨ x6 = Fin.natAdd (7 : ℕ) x4)) = Bool.true) ∧ (∀ (x3 : Fin (14 : ℕ) → Bool), ¬x1 x3 → (∀ (x5 : Fin (14 : ℕ) → Bool), (∀ (x6 : Fin (14 : ℕ)), x3 x6 = Bool.true → x5 x6 = Bool.true) → x3 ≠ x5 → x1 x5) → x2.eval (List.ofFn x3) = Bool.false) ∧ ∀ (x3 : Bool), ((PEqualNP.ReadK.linearParts x2 (fun (x4 : ℕ) => Decidable.decide (x4 = if x3 = Bool.true then (7 : ℕ) else (0 : ℕ))) (List.ofFn fun (x4 : Fin (14 : ℕ)) => Decidable.decide (↑x4 = (0 : ℕ) ∨ ↑x4 = (7 : ℕ)))).getD x2.output (Bool.false, Bool.false)).2 = Bool.false := by
  classical
  dsimp only
  let meet := fun (a b : ℕ) => (a &&& b &&& 1729382256910270463) ||| ((((a <<< 1) &&& b) ||| (a &&& (b <<< 1))) &&& 2882303761517117440)
  let step := fun (w : List ℕ) (g : Bool × ℕ × ℕ) => let a := w.getD g.2.1 0; let b := w.getD g.2.2 0; w ++ [if g.1 then a ||| b else meet a b]
  let initial := ([1729399028130512903,15270196031782968,58150373818816,94946423956573696,54820275478360064,3870282840506368,133412159488,2776645719824533521,218716039641317512,189725234880971840,156548607029289472,229736628137037828,270286071509057568,288160007407796482] : List ℕ)
  let fixedGates : List (Bool × ℕ × ℕ) := [(true, 7, 11), (false, 0, 14), (true, 13, 15), (false, 0, 16), (true, 8, 16), (true, 2, 17), (true, 9, 18), (false, 19, 20)]
  let start : List ℕ := [1729399028130512903,15270196031782968,58150373818816,94946423956573696,54820275478360064,3870282840506368,133412159488,2776645719824533521,218716039641317512,189725234880971840,156548607029289472,229736628137037828,270286071509057568,288160007407796482,2862231898204215317,2882303761517117445,3170463768924913927,2305843009213693959,3170473751662051727,2305901159587512775,3170475987293324751,455]
  have start_eq : fixedGates.foldl step initial = start := by decide +kernel
  have prefixLegal : ∀ i : Fin fixedGates.length, let g := fixedGates.get i
      g.2.1 ≠ g.2.2 ∧ g.2.1 < 14+i.val ∧ g.2.2 < 14+i.val := by decide +kernel
  have start_21 : start.getD 21 0 = 455 := by decide
  have keep (ss : List (Bool × ℕ × ℕ)) (w : List ℕ) (i : ℕ) (hi : i < w.length) :
      (ss.foldl step w).getD i 0 = w.getD i 0 := by
    induction ss generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have len (ss : List (Bool × ℕ × ℕ)) (w : List ℕ) :
      (ss.foldl step w).length = w.length + ss.length := by
    induction ss generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons, ih]
      simp [step]
      omega
  have synthesis : ∃ (gs : List (Bool × ℕ × ℕ)) (o : ℕ), gs.length ≤ 27 ∧
      (∀ i : Fin gs.length, let g := gs.get i
        g.2.1 ≠ g.2.2 ∧ g.2.1 < 14+i.val ∧ g.2.2 < 14+i.val) ∧
      (gs.foldl step initial).getD o 0 = 2097151 := by
    obtain ⟨tail,o,htCard,htGate,ho,hne,hcert⟩ := completion
    change 455 ||| ((tail.foldl step start).getD o 0) = 2097151 at hcert
    let gs := (fixedGates ++ tail) ++ [(true,21,o)]
    refine ⟨gs, 22+tail.length, ?_, ?_, ?_⟩
    · simp [gs, fixedGates]
      omega
    · intro i
      simp only [List.get_eq_getElem]
      have total := i.isLt
      change i.val < ((fixedGates ++ tail) ++ [(true,21,o)]).length at total
      simp only [List.length_append, show fixedGates.length = 8 by rfl,
        List.length_cons, List.length_nil, Nat.zero_add] at total
      by_cases iOld : i.val < (fixedGates ++ tail).length
      · simp only [gs, List.getElem_append_left iOld]
        by_cases iPrefix : i.val < fixedGates.length
        · rw [List.getElem_append_left iPrefix]
          exact prefixLegal ⟨i.val,iPrefix⟩
        · rw [List.getElem_append_right (Nat.le_of_not_gt iPrefix)]
          have jlt : i.val-fixedGates.length < tail.length := by
            have aux : fixedGates.length = 8 := rfl
            simp only [List.length_append,aux] at iOld
            omega
          have hz := htGate ⟨i.val-fixedGates.length, jlt⟩
          simp only [List.get_eq_getElem] at hz
          have sum : 22 + (i.val-fixedGates.length) = 14+i.val := by
            have aux : fixedGates.length = 8 := rfl
            omega
          simpa only [sum] using hz
      · have eq : i.val = (fixedGates ++ tail).length := by
          simp only [List.length_append] at iOld ⊢
          have aux : fixedGates.length = 8 := rfl
          omega
        simp [gs, eq, fixedGates]
        omega
    · rw [show gs = (fixedGates ++ tail) ++ [(true,21,o)] from rfl,
        List.foldl_append, List.foldl_append, start_eq, List.foldl_cons, List.foldl_nil]
      let w := tail.foldl step start
      change (w ++ [w.getD 21 0 ||| w.getD o 0]).getD (22+tail.length) 0 = 2097151
      have hw : w.length = 22 + tail.length := len tail start
      have fixed : w.getD 21 0 = 455 :=
        (keep tail start 21 (by decide)).trans start_21
      rw [← hw, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
      change w.getD 21 0 ||| w.getD o 0 = 2097151
      rw [fixed]
      exact hcert

  let decode := fun (g : Bool × ℕ × ℕ) =>
    (⟨if g.1 then .or else .and,[g.2.1,g.2.2]⟩ : Gate)
  let plain := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let deriv := fun (w : List (Bool × Bool)) (g : Gate) =>
    let ins := g.inputs.map fun i => w.getD i (false,false)
    w ++ [if g.op = .or then (ins.any (·.1),ins.any (·.2))
      else if g.op = .and then ins.foldl (fun (u v : Bool × Bool) =>
          (u.1 && v.1,(u.1 && v.2) || (u.2 && v.1))) (true,false)
      else (false,false)]
  let pair := fun (flag : Bool) (a : ℕ) =>
    if flag then (a.testBit 60,a.testBit 61) else (a.testBit 58,a.testBit 59)
  rcases synthesis with ⟨gs,o,len,legal,result⟩
  change (gs.foldl step initial).getD o 0 = 2097151 at result
  let C : Circuit := ⟨gs.map decode,o⟩
  have atWire {α : Type} (f : ℕ → α) (w : List ℕ) (k : ℕ) :
      (w.map f).getD k (f 0) = f (w.getD k 0) := by
    rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_map,Option.getD_map]
  have simulate {α : Type} (f : ℕ → α) (action : List α → Gate → List α)
      (rule : ∀ w g, (step w g).map f = action (w.map f) (decode g))
      (code : List (Bool × ℕ × ℕ)) (w : List ℕ) :
      ((code.foldl step w).map f) = (code.map decode).foldl action (w.map f) := by
    induction code generalizing w with
    | nil => rfl
    | cons g rest ih =>
      simp only [List.foldl_cons,List.map_cons]
      rw [ih,rule]
  have ordinaryMasks : ∀ k : Fin 58, (1729382256910270463 : ℕ).testBit k.val = true ∧
      (2882303761517117440 : ℕ).testBit k.val = false := by decide +kernel
  have normalBit (k : Fin 58) (a b : ℕ) :
      (meet a b).testBit k.val = (a.testBit k.val && b.testBit k.val) := by
    obtain ⟨lo,hi⟩ := ordinaryMasks k
    simp [meet,Nat.testBit_and,Nat.testBit_or,lo,hi]
  have andTwo (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by cases a <;> cases b <;> rfl
  have orTwo (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> rfl
  have normalRun (k : Fin 58) :
      C.eval (initial.map fun w => w.testBit k.val) = (2097151 : ℕ).testBit k.val := by
    let f := fun (w : ℕ) => w.testBit k.val
    have zero : f 0 = false := by simp [f]
    have rule (w : List ℕ) (g : Bool × ℕ × ℕ) : (step w g).map f = plain (w.map f) (decode g) := by
      rcases g with ⟨op,a,b⟩
      have ra : (w.map f).getD a false = f (w.getD a 0) := zero ▸ atWire f w a
      have rb : (w.map f).getD b false = f (w.getD b 0) := zero ▸ atWire f w b
      simp only [List.getD_eq_getElem?_getD,List.getElem?_map,f] at ra rb
      cases op <;> simp [step,plain,decode,andTwo,orTwo,ra,rb,f,normalBit,Nat.testBit_or]
    have h := simulate f plain rule gs initial
    change ((gs.map decode).foldl plain (initial.map f)).getD o false = _
    rw [← h,← zero,atWire,result]
  have markedJoin (flag : Bool) (a b : ℕ) :
      pair flag (meet a b) =
        ((pair flag a).1 && (pair flag b).1,
         ((pair flag a).1 && (pair flag b).2) || ((pair flag a).2 && (pair flag b).1)) := by
    have low58 : (1729382256910270463 : ℕ).testBit 58 = true := by decide
    have high58 : (2882303761517117440 : ℕ).testBit 58 = false := by decide
    have low59 : (1729382256910270463 : ℕ).testBit 59 = false := by decide
    have high59 : (2882303761517117440 : ℕ).testBit 59 = true := by decide
    have low60 : (1729382256910270463 : ℕ).testBit 60 = true := by decide
    have high60 : (2882303761517117440 : ℕ).testBit 60 = false := by decide
    have low61 : (1729382256910270463 : ℕ).testBit 61 = false := by decide
    have high61 : (2882303761517117440 : ℕ).testBit 61 = true := by decide
    cases flag <;> apply Prod.ext <;>
      simp [pair,meet,Nat.testBit_or,Nat.testBit_and,Nat.testBit_shiftLeft,low58,high58,low59,high59,low60,high60,low61,high61]
  have markedOr (flag : Bool) (a b : ℕ) : pair flag (a ||| b) =
      ((pair flag a).1 || (pair flag b).1,(pair flag a).2 || (pair flag b).2) := by
    cases flag <;> simp [pair,Nat.testBit_or]
  have markedRun (flag : Bool) :
      (((gs.map decode).foldl deriv (initial.map (pair flag))).getD o (false,false)).2 = false := by
    let f := pair flag
    have zero : f 0 = (false,false) := by cases flag <;> decide
    have rule (w : List ℕ) (g : Bool × ℕ × ℕ) : (step w g).map f = deriv (w.map f) (decode g) := by
      rcases g with ⟨op,a,b⟩
      have ra : (w.map f).getD a (false,false) = f (w.getD a 0) := zero ▸ atWire f w a
      have rb : (w.map f).getD b (false,false) = f (w.getD b 0) := zero ▸ atWire f w b
      simp only [List.getD_eq_getElem?_getD,List.getElem?_map,f] at ra rb
      cases op <;> simp [step,deriv,decode,ra,rb,f,markedJoin,markedOr]
    have h := simulate f deriv rule gs initial
    change (((gs.map decode).foldl deriv (initial.map f)).getD o (false,false)).2 = _
    rw [← h,← zero,atWire,result]
    cases flag <;> decide
  refine ⟨C,?_,?_,?_,?_,?_⟩
  · change (gs.map decode).length ≤ 27
    simpa only [List.length_map] using len
  · intro k gate hk
    change (gs.map decode)[k]? = some gate at hk
    rw [List.getElem?_map] at hk
    obtain ⟨g,hg,rfl⟩ := Option.map_eq_some_iff.mp hk
    have bound : k < gs.length := by
      by_contra! h
      rw [List.getElem?_eq_none (by omega)] at hg
      contradiction
    let t : Fin gs.length := ⟨k,bound⟩
    have hget : gs.get t = g := (List.getElem_of_getElem? hg).choose_spec
    have ok := legal t
    rw [hget] at ok
    refine ⟨?_,g.2.1,g.2.2,rfl,ok⟩
    cases hb : g.1 <;> simp [decode,hb]
  · intro p l incident
    have rows : ∀ p l : Fin 7, (p = l ∨ p = l+1 ∨ p = l+3) → ∃ k : Fin 58,
        (2097151 : ℕ).testBit k.val = true ∧
        initial.map (fun w => w.testBit k.val) =
          List.ofFn (fun v : Fin 14 => decide (v = Fin.castAdd 7 p ∨ v = Fin.natAdd 7 l)) := by
      decide +kernel
    obtain ⟨k,bit,ident⟩ := rows p l incident
    rw [← ident,normalRun,bit]
  · intro x independent maximal
    obtain ⟨j,hj⟩ := maximalRows x independent maximal
    have rows : ∀ j : Fin 37, ∃ k : Fin 58, (2097151 : ℕ).testBit k.val = false ∧
        initial.map (fun w => w.testBit k.val) =
          List.ofFn (fun i : Fin 14 => (([127,244,361,480,595,720,833,1063,1188,1313,1539,2126,2244,2376,2626,3008,3078,4125,4244,4361,4625,5125,5889,6156,7300,8250,8368,8488,8722,9250,9632,10250,11778,12312,12944,14600,16256] : List ℕ).getD j.val 0).testBit i.val) := by
      decide +kernel
    obtain ⟨k,bit,ident⟩ := rows j
    rw [hj,← ident,normalRun,bit]
  · intro flag
    have ident : initial.map (pair flag) =
        ((List.ofFn fun v : Fin 14 => decide (v.val = 0 ∨ v.val = 7)).zipIdx.map
          (fun z : Bool × ℕ => if decide (z.2 = if flag = true then 7 else 0) then (false,z.1) else (z.1,false))) := by
      cases flag <;> decide +kernel
    have bridge (x : List Bool) (m : ℕ → Bool) : PEqualNP.ReadK.linearParts C m x =
        (gs.map decode).foldl deriv (x.zipIdx.map fun z : Bool × ℕ => if m z.2 then (false,z.1) else (z.1,false)) := by
      unfold PEqualNP.ReadK.linearParts
      change List.foldl _ _ (gs.map decode) = _
      congr 1
      · funext w gate
        obtain ⟨op,ins⟩ := gate
        cases op <;> simp [deriv]
    rw [bridge,← ident]
    exact markedRun flag
