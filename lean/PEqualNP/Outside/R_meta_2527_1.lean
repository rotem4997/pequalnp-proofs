import Mathlib.Data.List.GetD
import Mathlib.Data.List.Induction
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 9000000 in
set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.R_meta_2527_1
    (anchor :
      ∀ (a b out : Fin 26) (tail : List (Fin 3 × Fin 26 × Fin 26)),
        tail.length ≤ 13 → (a.val = 9 ∨ b.val = 9) →
        a.val ≠ 25 → b.val ≠ 25 →
        (∀ i : ℕ, i < 9 → ∃ g ∈ tail, g.2.1.val = i ∨ g.2.2.val = i) →
        ∃ m : ℕ, m < 512 ∧
          let x : Fin 9 → Bool := fun i => m.testBit i.val
          let read (w : List Bool) (i : Fin 26) := if i.val = 25 then true else w.getD i.val false
          let wires := ((1, a, b) :: tail).foldl (fun w g =>
            w ++ [if g.1.val = 0 then read w g.2.1 && read w g.2.2
              else if g.1.val = 1 then read w g.2.1 || read w g.2.2
              else !read w g.2.1]) (List.ofFn x ++ [x 0 || x 4])
          wires.getD out.val false ≠
            ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
              (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
    (raw :
      ∀ (a b out : Fin 26) (tail : List (Fin 3 × Fin 26 × Fin 26)),
        tail.length ≤ 13 → (a.val ≠ 9 ∧ b.val ≠ 9) →
        a.val ≠ 25 → b.val ≠ 25 →
        (∀ i : ℕ, i < 9 →
          (∃ g ∈ tail, g.2.1.val = i ∨ g.2.2.val = i) ∨
          (a.val = i ∧ (b.val = i ∨ 10 ≤ b.val ∨ (i,b.val) ∈ ([(0,3),(4,1),(4,5)] : List (ℕ × ℕ)))) ∨
          (b.val = i ∧ (a.val = i ∨ 10 ≤ a.val ∨ (i,a.val) ∈ ([(0,3),(4,1),(4,5)] : List (ℕ × ℕ))))) →
        ∃ m : ℕ, m < 512 ∧
          let x : Fin 9 → Bool := fun i => m.testBit i.val
          let read (w : List Bool) (i : Fin 26) := if i.val = 25 then true else w.getD i.val false
          let wires := ((1, a, b) :: tail).foldl (fun w g =>
            w ++ [if g.1.val = 0 then read w g.2.1 && read w g.2.2
              else if g.1.val = 1 then read w g.2.1 || read w g.2.2
              else !read w g.2.1]) (List.ofFn x ++ [x 0 || x 4])
          wires.getD out.val false ≠
            ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
              (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))))
    : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x2 → (∀ (x4 : Fin (9 : ℕ) → Bool), (x2.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x2 = x1 → Option.map (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op) x2.gates[(1 : ℕ)]? = Option.some PEqualNP.CircuitLowerBounds.GateOp.or → (∃ x7 ∈ List.drop (1 : ℕ) x2.gates, (0 : ℕ) ∈ x7.inputs) → (∃ x8 ∈ List.drop (1 : ℕ) x2.gates, (4 : ℕ) ∈ x8.inputs) → (16 : ℕ) ≤ x2.size := by
  dsimp only
  intro C allowed first outputEq second read0 read4
  by_contra! small
  let src (i : ℕ) : Fin 26 := if hi : i < 24 then ⟨i, by omega⟩ else 24
  let firstCode (g : Gate) : Fin 3 := by
    classical
    exact if g.op = .and then 0 else if g.op = .or then 1 else 2
  let code (g : Gate) : Fin 3 × Fin 26 × Fin 26 :=
    let fallback : Fin 26 := by
      classical
      exact if g.op = .and then 25 else 24
    (firstCode g,
      if g.inputs.isEmpty then fallback else src (g.inputs.getD 0 0),
      if g.inputs.isEmpty then fallback
      else if g.inputs.length = 1 then src (g.inputs.getD 0 0)
      else src (g.inputs.getD 1 0))
  let read (w : List Bool) (i : Fin 26) := if i.val = 25 then true else w.getD i.val false
  let step (w : List Bool) (g : Fin 3 × Fin 26 × Fin 26) :=
    w ++ [if g.1.val = 0 then read w g.2.1 && read w g.2.2
      else if g.1.val = 1 then read w g.2.1 || read w g.2.2
      else !read w g.2.1]
  let stepOrig (w : List Bool) (g : Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have srcRead (w : List Bool) (hw : w.length ≤ 24) (i : ℕ) :
      read w (src i) = w.getD i false := by
    by_cases hi : i < 24
    · have ne : i ≠ 25 := by omega
      simp [read,src,hi,ne]
    · have notin := List.getD_eq_default w false (by omega : w.length ≤ i)
      rw [notin]
      simpa [read,src,hi] using (List.getD_eq_default w false hw)
  have constTrue (w : List Bool) : read w 25 = true := by simp [read]
  have constFalse (w : List Bool) (hw : w.length ≤ 24) : read w 24 = false := by
    simpa [read] using List.getD_eq_default w false hw
  have andEval (l : List Bool) : GateOp.and.eval l = l.all id := rfl
  have orEval (l : List Bool) : GateOp.or.eval l = l.any id := rfl
  have notEval (l : List Bool) : GateOp.not.eval l = !(l.headD false) := rfl
  have stepEq (w : List Bool) (hw : w.length ≤ 24) (g : Gate)
      (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      step w (code g) = stepOrig w g := by
    obtain ⟨op,ar⟩ := hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op
    cases h : g.inputs with
    | nil =>
      rcases op with e | e | e
      · simp [step,code,firstCode,stepOrig,h,e,andEval,constTrue]
      · simp [step,code,firstCode,stepOrig,h,e,orEval,constFalse w hw]
      · simp [step,code,firstCode,stepOrig,h,e,notEval,constFalse w hw]
    | cons a rest =>
      cases k : rest with
      | nil =>
        rcases op with e | e | e
        · simp [step,code,firstCode,stepOrig,h,k,e,andEval,srcRead w hw]
        · simp [step,code,firstCode,stepOrig,h,k,e,orEval,srcRead w hw]
        · simp [step,code,firstCode,stepOrig,h,k,e,notEval,srcRead w hw]
      | cons b tail =>
        have bounded : (a :: b :: tail).length ≤ 2 := by
          rw [← k, ← h]
          exact ar
        have nil : tail = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons] at bounded
          omega
        subst tail
        rcases op with e | e | e
        · simp [step,code,firstCode,stepOrig,h,k,e,andEval,srcRead w hw]
        · simp [step,code,firstCode,stepOrig,h,k,e,orEval,srcRead w hw]
        · simp [step,code,firstCode,stepOrig,h,k,e,notEval,srcRead w hw]
  have foldEq (gs : List Gate)
      (ok : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
      (w : List Bool) (hw : w.length + gs.length ≤ 24) :
      (gs.map code).foldl step w = gs.foldl stepOrig w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      have hneed : w.length ≤ 24 := by simp at hw; omega
      have ok' := ok g (by simp)
      have bound : (stepOrig w g).length + gs.length ≤ 24 := by
        simp only [stepOrig, List.length_append, List.length_singleton]
        simp only [List.length_cons] at hw
        omega
      simp only [List.map_cons, List.foldl_cons]
      rw [stepEq w hneed g ok']
      exact ih (fun a ha => ok a (List.mem_cons_of_mem g ha)) _ bound
  have foldLength (gs : List Gate) (w : List Bool) :
      (gs.foldl stepOrig w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      rw [List.foldl_cons,ih]
      simp only [stepOrig,List.length_append,List.length_cons,List.length_nil]
      omega
  have foldRead (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
      (gs.foldl stepOrig w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih _ (by simp [stepOrig]; omega)]
      exact List.getD_append _ _ _ _ h
  have encodeRead (g : Gate) (ar : g.inputs.length ≤ 2) (i : ℕ) (hi : i < 24)
      (h : i ∈ g.inputs) : (code g).2.1.val = i ∨ (code g).2.2.val = i := by
    have src_eq : (src i).val = i := by simp [src,hi]
    cases ls : g.inputs with
    | nil => simp [ls] at h
    | cons a rest =>
      cases rst : rest with
      | nil =>
        have e : i = a := by simpa [ls,rst] using h
        exact Or.inl (by simp [code,ls,← e,src_eq])
      | cons b tail =>
        have bounded : (a :: b :: tail).length ≤ 2 := by
          rw [← rst, ← ls]
          exact ar
        have nil : tail = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons] at bounded
          omega
        subst tail
        simp only [ls,rst,List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with e | e
        · exact Or.inl (by simp [code,ls,← e,src_eq])
        · exact Or.inr (by simp [code,ls,rst,← e,src_eq])
  cases cg : C.gates with
  | nil => simp [cg] at second
  | cons g rest =>
    cases rs : rest with
    | nil => simp [cg,rs] at second
    | cons g2 tail =>
      have all : C.gates = g :: g2 :: tail := cg.trans (congrArg (List.cons g) rs)
      have allowedSuffix (gate : Gate) (hg : gate ∈ g2 :: tail) :=
        allowed gate (by rw [all]; exact List.mem_cons_of_mem g hg)
      have tailBound : tail.length ≤ 13 := by
        change C.gates.length < 16 at small
        rw [all] at small
        simp only [List.length_cons] at small
        omega
      have op2 : g2.op = .or := by simpa [all] using second
      let a := (code g2).2.1
      let b := (code g2).2.2
      let out := src C.output
      let t := tail.map code
      have opCode : (code g2).1 = 1 := by simp [code,firstCode,op2]
      have codeEq : (g2 :: tail).map code = (1,a,b) :: t := by
        simp only [List.map_cons,t]
        congr 1
        exact Prod.ext opCode rfl
      let goalFun (x : Fin 9 → Bool) :=
        ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      let seed (x : Fin 9 → Bool) := List.ofFn x ++ [x 0 || x 4]
      have encodedEval (x : Fin 9 → Bool) :
          (((1,a,b) :: t).foldl step (seed x)).getD out.val false = goalFun x := by
        let w := List.ofFn x
        let after := stepOrig w g
        have wlen : w.length = 9 := by simp [w]
        have secondList : after = w ++ [x 0 || x 4] := by
          have agree : (C.wires w).getD 9 false = after.getD 9 false := by
            change (C.gates.foldl stepOrig w).getD 9 false = _
            rw [all]
            change ((g2 :: tail).foldl stepOrig after).getD 9 false = _
            have bound : 9 < after.length := by simp [after,stepOrig,wlen]
            exact foldRead _ _ _ bound
          have last : after.getD 9 false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
            change (w ++ [_]).getD 9 false = _
            rw [List.getD_append_right _ _ _ _ (by omega),wlen]
            rfl
          have eq : g.op.eval (g.inputs.map fun i => w.getD i false) = (x 0 || x 4) :=
            last.symm.trans (agree.symm.trans (first x))
          change w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] = _
          rw [eq]
        have enough : (w ++ [x 0 || x 4]).length + (g2 :: tail).length ≤ 24 := by
          simp [wlen]
          omega
        have outputAgree : ((g2 :: tail).foldl stepOrig (w ++ [x 0 || x 4])).getD out.val false =
            C.eval w := by
          rw [← secondList]
          change ((g2 :: tail).foldl stepOrig after).getD out.val false =
            (C.gates.foldl stepOrig w).getD C.output false
          rw [all]
          change ((g2 :: tail).foldl stepOrig after).getD out.val false =
            ((g2 :: tail).foldl stepOrig after).getD C.output false
          by_cases le : C.output < 24
          · simp [out,src,le]
          · have limit : ((g2 :: tail).foldl stepOrig after).length ≤ 24 := by
              rw [foldLength,secondList]; exact enough
            rw [show out.val = 24 from by simp [out,src,le],List.getD_eq_default _ _ limit,
              List.getD_eq_default _ _ (by omega : ((g2 :: tail).foldl stepOrig after).length ≤ C.output)]
        have target : C.eval w =
            ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
              (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))) :=
          congrFun outputEq x
        change (((1,a,b) :: t).foldl step (w ++ [x 0 || x 4])).getD out.val false = _
        rw [← codeEq, foldEq _ allowedSuffix _ enough, outputAgree]
        exact target

      let exceptions : List (ℕ × ℕ) := [(0,3),(4,1),(4,5)]
      let allowMiss (i a b : ℕ) :=
        (a = i ∧ (b = i ∨ 10 ≤ b ∨ (i,b) ∈ exceptions)) ∨
        (b = i ∧ (a = i ∨ 10 ≤ a ∨ (i,a) ∈ exceptions))
      let narrow (j : Fin 26) : Fin 11 := if h : j.val < 10 then ⟨j.val, by omega⟩ else 10
      let smallRead (x : Fin 9 → Bool) (p : Fin 11) : Bool :=
        if h : p.val < 9 then x ⟨p.val,h⟩ else if p.val = 9 then x 0 || x 4 else false
      let toggle (x : Fin 9 → Bool) (i : Fin 9) : Fin 9 → Bool := fun j => x j || decide (j=i)
      let input (m : ℕ) : Fin 9 → Bool := fun j => m.testBit j.val
      let witnesses : List (List ℕ) := [
        [0, 18, 20, 0, 16, 48, 80, 144, 272, 16, 0, 18, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 20, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 48, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 80, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 144, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 272, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 0, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16],
        [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 4, 9, 20, 36, 64, 129, 257, 1, 0, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 20, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 36, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 64, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 129, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 257, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1],
        [2, 2, 9, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 9, 2, 0, 8, 18, 34, 72, 128, 258, 9, 0, 2, 2, 8, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 18, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 34, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 72, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 128, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 258, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 9, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 2, 2, 2, 2, 2, 2, 2],
        [4, 4, 4, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 18, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 18, 4, 0, 16, 36, 68, 144, 256, 5, 0, 4, 4, 4, 16, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 36, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 68, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 144, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 256, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 4, 4, 4, 4, 4, 4, 4],
        [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 1, 1, 1, 1, 0, 5, 9, 0, 0, 65, 129, 257, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 65, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 129, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 257, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1],
        [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 130, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 144, 1, 1, 1, 1, 1, 1, 130, 5, 9, 144, 0, 65, 128, 256, 1, 0, 1, 1, 1, 1, 1, 65, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 128, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 256, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1],
        [2, 2, 2, 2, 2, 2, 257, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 260, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 10, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 18, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 34, 2, 2, 2, 2, 257, 2, 260, 10, 18, 34, 0, 130, 256, 18, 0, 2, 2, 2, 2, 2, 2, 130, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 256, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 18, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 2, 2, 2],
        [4, 4, 4, 4, 4, 4, 4, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 34, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 40, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 20, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 32, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 68, 4, 4, 4, 5, 34, 4, 40, 20, 32, 68, 0, 260, 5, 0, 4, 4, 4, 4, 4, 4, 4, 260, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 0, 4, 4, 4],
        [8, 8, 8, 8, 8, 8, 8, 8, 9, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 10, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 36, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 48, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 32, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 64, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 136, 8, 8, 9, 10, 36, 8, 48, 32, 64, 136, 0, 9, 0, 8, 8, 8, 8, 8, 8, 8, 8, 9, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 0, 8, 8]]
      let witness (i : Fin 9) (u v : Fin 11) := (witnesses.getD i.val []).getD (u.val * 11 + v.val) 0
      let missed (i j k : ℕ) : Bool :=
        (j == i && (k == i || decide (10 ≤ k) || exceptions.contains (i,k))) ||
        (k == i && (j == i || decide (10 ≤ j) || exceptions.contains (i,j)))
      have missIff (i j k : ℕ) : missed i j k = true ↔ allowMiss i j k := by
        simp [missed,allowMiss,or_assoc]
      let cell (i : Fin 9) (u v : Fin 11) : Bool :=
        let x := input (witness i u v)
        let z := toggle x i
        missed i.val u.val v.val ||
          (((x 0 || x 4) == (z 0 || z 4)) &&
           (((smallRead x u || smallRead x v) == (smallRead z u || smallRead z v)) &&
            !(goalFun x == goalFun z)))
      have goodCells : ∀ i u v, cell i u v = true := by decide +kernel
      have sampleValid : ∀ (i : Fin 9) (u v : Fin 11), ¬ allowMiss i.val u.val v.val →
          let x := input (witness i u v)
          let z := toggle x i
          (x 0 || x 4) = (z 0 || z 4) ∧
          (smallRead x u || smallRead x v) = (smallRead z u || smallRead z v) ∧
          goalFun x ≠ goalFun z := by
        intro i u v noMiss
        have parsed := goodCells i u v
        simp only [cell,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq] at parsed
        rcases parsed with h | h
        · exact (noMiss ((missIff _ _ _).mp h)).elim
        · rcases h with ⟨a,b,c⟩
          exact ⟨a,b,fun e => by simp [e] at c⟩
      have srcNe (i : ℕ) : (src i).val ≠ 25 := by
        by_cases lt : i < 24
        · simp [src,lt]; omega
        · simp [src,lt]
      have orNeAnd : GateOp.or ≠ GateOp.and := fun h => GateOp.noConfusion h
      have noTrue : a.val ≠ 25 ∧ b.val ≠ 25 := by
        constructor <;> simp only [a,b,code,op2,orNeAnd,ite_false]
        · split
          · decide
          · exact srcNe _
        · split
          · decide
          · split <;> exact srcNe _
      have ofFnRead {n : ℕ} (f : Fin n → Bool) (j : Fin n) :
          (List.ofFn f).getD j.val false = f j := by
        rw [List.getD_eq_getElem _ _ (by simp)]
        simp
      have seedLen (f : Fin 9 → Bool) : (seed f).length = 10 := by simp [seed]
      have seedRaw (f : Fin 9 → Bool) (j : Fin 9) : (seed f).getD j.val false = f j := by
        change (List.ofFn f ++ [_]).getD j.val false = f j
        rw [List.getD_append _ _ _ _ (by simpa only [List.length_ofFn] using j.isLt),ofFnRead]
      have seedLast (f : Fin 9 → Bool) : (seed f).getD 9 false = (f 0 || f 4) := by
        change (List.ofFn f ++ [_]).getD 9 false = _
        rw [List.getD_append_right _ _ _ _ (by simp)]
        simp
      have smallReadEq (x : Fin 9 → Bool) (j : Fin 26) (h : j.val ≠ 25) :
          read (seed x) j = smallRead x (narrow j) := by
        by_cases lt : j.val < 10
        · by_cases raw : j.val < 9
          · simpa only [read,h,ite_false,narrow,lt,smallRead,raw,dite_true] using
              seedRaw x (⟨j.val,raw⟩ : Fin 9)
          · have nine : j.val = 9 := by omega
            have nEq : (narrow j).val = 9 := by simp [narrow,nine]
            change (if j.val = 25 then true else (seed x).getD j.val false) = _
            rw [ite_eq_right h,nine,seedLast]
            simp [smallRead,nEq]
        · have outOfSeed : (seed x).length ≤ j.val := by rw [seedLen]; omega
          change (if j.val=25 then true else (seed x).getD j.val false) = smallRead x (narrow j)
          rw [ite_eq_right h, List.getD_eq_default _ _ outOfSeed]
          simp [narrow,lt,smallRead]
      have missToWide (i : Fin 9) (j k : Fin 26) :
          allowMiss i.val (narrow j).val (narrow k).val → allowMiss i.val j.val k.val := by
        by_cases hj : j.val < 10 <;> by_cases hk : k.val < 10 <;>
          simp only [narrow,hj,hk,dite_true,dite_false,allowMiss] <;>
          simp [exceptions] <;> omega
      have foldOff (i : ℕ) (ls : List (Fin 3 × Fin 26 × Fin 26)) (w z : List Bool)
          (hlen : w.length = z.length)
          (agree : ∀ j, j ≠ i → w.getD j false = z.getD j false)
          (absent : ∀ g ∈ ls, g.2.1.val ≠ i ∧ g.2.2.val ≠ i)
          (j : ℕ) (jne : j ≠ i) :
          (ls.foldl step w).getD j false = (ls.foldl step z).getD j false := by
        induction ls generalizing w z with
        | nil => exact agree j jne
        | cons g ls ih =>
          obtain ⟨ga,gb⟩ := absent g (by simp)
          have eqRead (v : Fin 26) (vne : v.val ≠ i) : read w v = read z v := by
            dsimp [read]
            rw [agree _ vne]
          have next : ∃ bit : Bool, step w g = w ++ [bit] ∧ step z g = z ++ [bit] := by
            refine ⟨_,rfl,?_⟩
            dsimp [step]
            rw [eqRead _ ga,eqRead _ gb]
          obtain ⟨bit,rflw,rflz⟩ := next
          simp only [List.foldl_cons,rflw,rflz]
          apply ih _ _ (by simp [hlen]) ?_ (fun r hr => absent r (List.mem_cons_of_mem _ hr))
          intro k kn
          by_cases lt : k < w.length
          · rw [List.getD_append _ _ _ _ lt,List.getD_append _ _ _ _ (by omega),agree _ kn]
          · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),hlen]
      have noRawOutput (i : Fin 9) : out.val ≠ i.val := by
        intro e
        have cOut : C.output = i.val := by
          by_cases lt : C.output < 24
          · simpa [out,src,lt] using e
          · have below := i.isLt
            simp [out,src,lt] at e
            omega
        let rawTest : Fin 9 → Bool := fun j => decide (j=i)
        have noEdge : ∀ i : Fin 9, goalFun (fun j => decide (j=i)) = false := by decide +kernel
        have calcOut : C.eval (List.ofFn rawTest) = goalFun rawTest := congrFun outputEq rawTest
        change (C.gates.foldl stepOrig (List.ofFn rawTest)).getD C.output false = _ at calcOut
        rw [cOut,foldRead _ _ _ (by simpa only [List.length_ofFn] using i.isLt),noEdge i] at calcOut
        rw [ofFnRead] at calcOut
        simp [rawTest] at calcOut
      have mandatory : ∀ i : ℕ, i < 9 →
          (∃ g ∈ t, g.2.1.val = i ∨ g.2.2.val = i) ∨ allowMiss i a.val b.val := by
        intro i bound
        by_cases allow : allowMiss i a.val b.val
        · exact Or.inr allow
        · apply Or.inl
          by_contra absent
          let p : Fin 9 := ⟨i,bound⟩
          let x := input (witness p (narrow a) (narrow b))
          let z := toggle x p
          have valid : ¬ allowMiss p.val (narrow a).val (narrow b).val :=
            fun h => allow (missToWide p a b h)
          obtain ⟨eqFirst,eqSecond,unequal⟩ := sampleValid p (narrow a) (narrow b) valid
          have secEq : (read (seed x) a || read (seed x) b) = (read (seed z) a || read (seed z) b) := by
            simp only [smallReadEq x a noTrue.1,smallReadEq x b noTrue.2,
              smallReadEq z a noTrue.1,smallReadEq z b noTrue.2]
            exact eqSecond
          let pre (u : Fin 9 → Bool) := step (seed u) (1,a,b)
          have prefixAgree (k : ℕ) (kne : k ≠ i) : (pre x).getD k false = (pre z).getD k false := by
            have form (u : Fin 9 → Bool) : pre u = seed u ++ [read (seed u) a || read (seed u) b] := by
              simp [pre,step]
            rw [form x,form z,secEq]
            let bit := read (seed z) a || read (seed z) b
            change (seed x ++ [bit]).getD k false = (seed z ++ [bit]).getD k false
            by_cases ap : k < 10
            · have before (f : Fin 9 → Bool) :
                  (seed f ++ [bit]).getD k false = (seed f).getD k false :=
                List.getD_append _ _ _ _ (by rw [seedLen]; exact ap)
              rw [before x, before z]
              by_cases raw : k < 9
              · let q : Fin 9 := ⟨k,raw⟩
                change (seed x).getD q.val false = (seed z).getD q.val false
                rw [seedRaw,seedRaw]
                have ne : q ≠ p := fun h => kne (congrArg Fin.val h)
                simp [z,toggle,ne]
              · have nine : k = 9 := by omega
                rw [nine,seedLast,seedLast]
                exact eqFirst
            · have after (f : Fin 9 → Bool) :
                  (seed f ++ [bit]).getD k false = ([bit] : List Bool).getD (k-10) false := by
                rw [List.getD_append_right _ _ _ _ (by rw [seedLen]; omega),seedLen]
              rw [after x,after z]
          have noGate (g : Fin 3 × Fin 26 × Fin 26) (hg : g ∈ t) :
              g.2.1.val ≠ i ∧ g.2.2.val ≠ i :=
            ⟨fun h => absent ⟨g,hg,Or.inl h⟩,fun h => absent ⟨g,hg,Or.inr h⟩⟩
          have same := foldOff i t (pre x) (pre z) (by simp [pre,step,seedLen])
            prefixAgree noGate out.val (noRawOutput p)
          change (((1,a,b) :: t).foldl step (seed x)).getD out.val false =
            (((1,a,b) :: t).foldl step (seed z)).getD out.val false at same
          exact unequal ((encodedEval x).symm.trans (same.trans (encodedEval z)))
      have closed : ∃ m : ℕ, m < 512 ∧
          (((1,a,b) :: t).foldl step (seed (input m))).getD out.val false ≠ goalFun (input m) := by
        by_cases pref : a.val = 9 ∨ b.val = 9
        · have allNine (i : ℕ) (hi : i < 9) : ∃ g ∈ t, g.2.1.val = i ∨ g.2.2.val = i := by
            rcases mandatory i hi with h | h
            · exact h
            · rcases pref with eq | eq
              · simp [allowMiss,exceptions,eq] at h
                omega
              · simp [allowMiss,exceptions,eq] at h
                omega
          exact anchor a b out t (by simpa [t] using tailBound) pref noTrue.1 noTrue.2 allNine
        · have hn : a.val ≠ 9 ∧ b.val ≠ 9 := ⟨fun h => pref (Or.inl h),fun h => pref (Or.inr h)⟩
          exact raw a b out t (by simpa [t] using tailBound) hn noTrue.1 noTrue.2 mandatory
      obtain ⟨m,_,bad⟩ := closed
      exact bad (encodedEval (input m))
