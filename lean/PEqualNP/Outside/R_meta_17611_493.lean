import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_17611_493
    (numeric : have x1 : (Fin (10 : ℕ) → Bool) → Bool := fun (x1 : Fin (10 : ℕ) → Bool) => x1 (0 : Fin (10 : ℕ)) && x1 (1 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (2 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (3 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (4 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (0 : Fin (10 : ℕ)) || x1 (0 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)) || x1 (1 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (2 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (3 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (4 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (5 : Fin (10 : ℕ)) && x1 (7 : Fin (10 : ℕ)) || x1 (7 : Fin (10 : ℕ)) && x1 (9 : Fin (10 : ℕ)) || x1 (9 : Fin (10 : ℕ)) && x1 (6 : Fin (10 : ℕ)) || x1 (6 : Fin (10 : ℕ)) && x1 (8 : Fin (10 : ℕ)) || x1 (8 : Fin (10 : ℕ)) && x1 (5 : Fin (10 : ℕ)); ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : Bool),   PEqualNP.MetaComplexity.FanInTwo x2 →     x2.size ≤ (15 : ℕ) →       have x7 : (Fin (10 : ℕ) → Bool) → Bool := fun (x7 : Fin (10 : ℕ) → Bool) => (x2.wires (List.ofFn x7)).getD x3 Bool.false;       ∃ (x8 : Fin (10 : ℕ) → Bool), x8 (9 : Fin (10 : ℕ)) = Bool.false ∧ (if x4 = Bool.true then !x7 x8 else x7 x8) ≠ x1 x8)
    (extract : let F := fun x : Fin 10 → Bool => x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5;
    ∀ C : Circuit, FanInTwo C → C.size ≤ 17 →
    (∀ x, C.eval (List.ofFn x ++ [x 0 && x 2]) = F x) →
    ∃ (D : Circuit) (u : Nat) (b : Bool), FanInTwo D ∧ D.size ≤ 15 ∧ ∀ x : Fin 10 → Bool, x 9 = false →
      (if b then !(D.wires (List.ofFn x)).getD u false else (D.wires (List.ofFn x)).getD u false) = F x)
    (hNeg : ¬ HasCircuitSize 10 (fun x : Fin 10 → Bool =>
      !(x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) 17) :
    ∀ (x1 x2 : Bool) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.MetaComplexity.FanInTwo x3 →     x3.size ≤ (17 : ℕ) →       (11 : ℕ) ≤ x3.output →         x3.output < (11 : ℕ) + x3.size →           (∀ (x8 : Fin (10 : ℕ)), ∃ x9 ∈ x3.gates, ↑x8 ∈ x9.inputs) →             ∃ (x9 : Fin (10 : ℕ) → Bool),               have x10 : Bool := x3.eval (List.ofFn x9 ++ [x1]);               (if x2 = Bool.true then !x10 else x10) ≠ (x9 (0 : Fin (10 : ℕ)) && x9 (1 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (2 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (3 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (4 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (0 : Fin (10 : ℕ)) || x9 (0 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ)) || x9 (1 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (2 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (3 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (4 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (5 : Fin (10 : ℕ)) && x9 (7 : Fin (10 : ℕ)) || x9 (7 : Fin (10 : ℕ)) && x9 (9 : Fin (10 : ℕ)) || x9 (9 : Fin (10 : ℕ)) && x9 (6 : Fin (10 : ℕ)) || x9 (6 : Fin (10 : ℕ)) && x9 (8 : Fin (10 : ℕ)) || x9 (8 : Fin (10 : ℕ)) && x9 (5 : Fin (10 : ℕ))) := by
  have previous : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (17 : ℕ) → ∃ (x4 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x4 ++ [x4 (0 : Fin (10 : ℕ)) && x4 (2 : Fin (10 : ℕ))]) ≠ (fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) x4 := by
    intro C fan small
    by_contra! good
    obtain ⟨D,u,b,legal,budget,rep⟩ := extract C fan small good
    obtain ⟨x,zero,ne⟩ := numeric D u b legal budget
    exact ne (rep x zero)
  have hPos : ¬ HasCircuitSize 10 (fun x : Fin 10 → Bool =>
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5)) 17 := by
    rintro ⟨C, legal, budget, agrees⟩
    let reg (i : ℕ) := if i < 10 then i else i + 1
    let gate (g : Gate) : Gate := ⟨g.op,g.inputs.map reg⟩
    let D : Circuit := ⟨C.gates.map gate, reg C.output⟩
    have fanD : FanInTwo D := by
      intro g hg
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hg
      exact ⟨(legal q hq).1, (List.length_map reg).symm ▸ (legal q hq).2⟩
    have small : D.size ≤ 17 := (show D.size = C.size from List.length_map gate).symm ▸ budget
    obtain ⟨x,bad⟩ := previous D fanD small
    let a := List.ofFn x
    let b := a ++ [x 0 && x 2]
    have lenA : a.length = 10 := List.length_ofFn
    have lenB : b.length = 11 := by simp [b,lenA]
    have wire (bits : List Bool) (i : ℕ) :
        (b ++ bits).getD (reg i) false = (a ++ bits).getD i false := by
      by_cases h : i < 10
      · change ((a ++ [x 0 && x 2]) ++ bits).getD (if i<10 then i else i+1) false = _
        rw [if_pos h,List.append_assoc,List.getD_append _ _ _ _ (by omega),List.getD_append _ _ _ _ (by omega)]
      · change (b ++ bits).getD (if i<10 then i else i+1) false = _
        rw [if_neg h]
        simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right (by omega : b.length ≤ i+1),
          List.getElem?_append_right (by omega : a.length ≤ i),lenA,lenB,show i+1-11=i-10 by omega]
    let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let run (gs : List Gate) (w : List Bool) := gs.foldl step w
    have replay (gs : List Gate) (bits : List Bool) :
        ∃ z, run gs (a++bits) = a++z ∧ run (gs.map gate) (b++bits) = b++z := by
      induction gs generalizing bits with
      | nil => exact ⟨bits,rfl,rfl⟩
      | cons g gs ih =>
        let bit := g.op.eval (g.inputs.map fun i => (a++bits).getD i false)
        obtain ⟨z,h1,h2⟩ := ih (bits++[bit])
        refine ⟨z,?_,?_⟩
        · simpa only [run,List.foldl_cons,step,bit,List.append_assoc] using h1
        · have h : step (b++bits) (gate g) = b++(bits++[bit]) := by
            simp only [step,gate,List.map_map,Function.comp_def,wire,bit,List.append_assoc]
          change run (gs.map gate) (step (b++bits) (gate g)) = _
          rw [h]
          exact h2
    obtain ⟨z,h1,h2⟩ := replay C.gates []
    simp only [List.append_nil] at h1 h2
    apply bad
    calc
      D.eval (List.ofFn x ++ [x 0 && x 2]) = C.eval (List.ofFn x) := by
        change (run (C.gates.map gate) b).getD (reg C.output) false = (run C.gates a).getD C.output false
        rw [h1,h2,wire]
      _ = _ := agrees x
  classical
  intro seed b C legal budget outlo outhi useRaw
  let index (i : Nat) := if i < 10 then i else i - 1
  let gate (g : Gate) : Gate :=
    let xs := g.inputs
    let ys := (xs.filter (fun i => decide (i ≠ 10))).map index
    let xmap := xs.map index
    GateOp.rec (motive := fun _ => Gate)
      (if seed then ⟨.and,ys⟩ else
        if xs.any (fun i => decide (i = 10)) then ⟨.or,[]⟩ else ⟨.and,xmap⟩)
      (if seed then
        if xs.any (fun i => decide (i = 10)) then ⟨.and,[]⟩ else ⟨.or,xmap⟩
        else ⟨.or,ys⟩)
      (if xs.headD 0 = 10 then ⟨if seed then .or else .and,[]⟩ else ⟨.not,xmap⟩)
      (fun _ => ⟨.or,[]⟩) ⟨.or,[]⟩ g.op
  let D : Circuit := ⟨C.gates.map gate,index C.output⟩
  have AND : GateOp.and ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) := by simp
  have OR : GateOp.or ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) := by simp
  have NOT : GateOp.not ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) := by simp
  have fanD : FanInTwo D := by
    intro g hg
    obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hg
    have hl := (legal h hh).2
    have hf := (List.length_filter_le (fun i : Nat => decide (i ≠ 10)) h.inputs).trans hl
    cases hOp : h.op <;> cases hSeed : seed <;>
      simp only [gate,hOp,hSeed,Bool.false_eq_true,Bool.true_eq,ite_false,ite_true]
    all_goals (try split) <;> constructor <;> try first | exact AND | exact OR | exact NOT
    all_goals simp only [List.length_map,List.length_nil] <;> omega
  have sizeD : D.size = C.size := List.length_map gate
  have and0 : GateOp.and.eval [] = true := rfl
  have or0 : GateOp.or.eval [] = false := rfl
  have not0 : GateOp.not.eval [] = true := rfl
  have and1 (a : Bool) : GateOp.and.eval [a] = a := by cases a <;> rfl
  have or1 (a : Bool) : GateOp.or.eval [a] = a := by cases a <;> rfl
  have not1 (a : Bool) : GateOp.not.eval [a] = !a := rfl
  have and2 (a c : Bool) : GateOp.and.eval [a,c] = (a && c) := by cases a <;> cases c <;> rfl
  have or2 (a c : Bool) : GateOp.or.eval [a,c] = (a || c) := by cases a <;> cases c <;> rfl
  have not2 (a c : Bool) : GateOp.not.eval [a,c] = !a := rfl
  have gateEq (g : Gate) (hg : g ∈ C.gates) (A B : List Bool)
      (hasSeed : A.getD 10 false = seed)
      (agree : ∀ i : Nat, i ≠ 10 → A.getD i false = B.getD (index i) false) :
      g.op.eval (g.inputs.map fun i => A.getD i false) =
        (gate g).op.eval ((gate g).inputs.map fun i => B.getD i false) := by
    have seedValue : A[10]?.getD false = seed := by
      simpa only [List.getD_eq_getElem?_getD] using hasSeed
    have h := legal g hg
    have shape : g.op = .and ∨ g.op = .or ∨ g.op = .not := by simpa using h.1
    rcases ins : g.inputs with _ | ⟨i, _ | ⟨j, _ | ⟨k,ks⟩⟩⟩
    · rcases shape with hOp | hOp | hOp <;> cases seed <;>
        simp [gate,hOp,ins,and0,or0,not0]
    · have vi : i ≠ 10 → A[i]?.getD false = B[index i]?.getD false := by
        simpa only [List.getD_eq_getElem?_getD] using agree i
      have revI : (10 : Nat) = i ↔ i = 10 := eq_comm
      rcases shape with hOp | hOp | hOp <;> cases seed <;> by_cases hI : i = 10 <;>
        simp [gate,hOp,ins,hI,revI,seedValue,vi,and0,or0,not0,and1,or1,not1]
    · have vi : i ≠ 10 → A[i]?.getD false = B[index i]?.getD false := by
        simpa only [List.getD_eq_getElem?_getD] using agree i
      have revI : (10 : Nat) = i ↔ i = 10 := eq_comm
      have vj : j ≠ 10 → A[j]?.getD false = B[index j]?.getD false := by
        simpa only [List.getD_eq_getElem?_getD] using agree j
      have revJ : (10 : Nat) = j ↔ j = 10 := eq_comm
      rcases shape with hOp | hOp | hOp <;> cases seed <;> by_cases hI : i = 10 <;> by_cases hJ : j = 10 <;>
        simp [gate,hOp,ins,hI,hJ,revI,revJ,seedValue,vi,vj,and0,or0,not0,and1,or1,not1,and2,or2,not2]
    · have hl := h.2
      rw [ins] at hl
      simp only [List.length_cons] at hl
      omega
  let run (L : List Gate) (A : List Bool) : List Bool :=
    L.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) A
  have snocEq (A : List Bool) (q : Bool) : (A++[q]).getD A.length false = q := by simp
  have snocNe (A : List Bool) (q : Bool) (i : Nat) (hi : i ≠ A.length) :
      (A++[q]).getD i false = A.getD i false := by
    by_cases h : i < A.length
    · exact List.getD_append _ _ _ _ h
    · have hl : A.length < i := by omega
      rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
  have compose :
      ∀ (L : List Gate), (∀ g ∈ L, g ∈ C.gates) →
      ∀ A B : List Bool, A.length = B.length + 1 → 10 ≤ B.length →
      A.getD 10 false = seed →
      (∀ i : Nat, i ≠ 10 → A.getD i false = B.getD (index i) false) →
      ∀ i : Nat, i ≠ 10 → (run L A).getD i false = (run (L.map gate) B).getD (index i) false := by
    intro L
    induction L with
    | nil => intro _ A B _ _ _ h i hi; exact h i hi
    | cons g rest ih =>
      intro closed A B len bound has eval i hi
      let u := g.op.eval (g.inputs.map fun i => A.getD i false)
      have ev := gateEq g (closed g List.mem_cons_self) A B has eval
      change (run rest (A ++ [u])).getD i false =
        (run (rest.map gate) (B ++ [(gate g).op.eval ((gate g).inputs.map fun i =>
          B.getD i false)])).getD (index i) false
      rw [← ev]
      apply ih (fun g hg => closed g (List.mem_cons_of_mem _ hg))
      · simp [len]
      · simp; omega
      · exact (snocNe A u 10 (by omega)).trans has
      · intro j hj
        by_cases same : j = A.length
        · have hBig : ¬j < 10 := by omega
          have hInd : index j = B.length := by
            simp only [index,ite_eq_right hBig]
            omega
          rw [same,snocEq,← same,hInd,snocEq]
        · have mr : index j ≠ B.length := by
            by_cases qs : j < 10
            · simp only [index,ite_eq_left qs]
              omega
            · simp only [index,ite_eq_right qs]
              omega
          rw [snocNe A u j same,snocNe B u _ mr]
          exact eval j hj
      · exact hi
  have evaluates (x : Fin 10 → Bool) : D.eval (List.ofFn x) = C.eval (List.ofFn x ++ [seed]) := by
    let V := List.ofFn x
    have lengths : V.length = 10 := by simp [V]
    have indexEq (i : Nat) (hi : i ≠ 10) :
        (V++[seed]).getD i false = V.getD (index i) false := by
      by_cases small : i < 10
      · rw [show index i = i by simp [index,small], List.getD_append _ _ _ _ (by omega)]
      · have hBig : 10 < i := by omega
        rw [List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp only [index,ite_eq_right small]; omega)]
    have eq := compose C.gates (fun _ h => h) (V++[seed]) V (by simp) (by omega)
      (by rw [← lengths,snocEq]) indexEq C.output (by omega)
    exact eq.symm
  by_contra! fail
  have dv (x : Fin 10 → Bool) :
      (if b then !(D.eval (List.ofFn x)) else D.eval (List.ofFn x)) =
        (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
         x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
         x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) := by
    rw [evaluates]
    exact Classical.byContradiction (fail x)
  have sz : D.size ≤ 17 := sizeD ▸ budget
  cases b
  · exact hPos ⟨D,fanD,sz,dv⟩
  · apply hNeg
    refine ⟨D,fanD,sz,?_⟩
    intro x
    have eq := congrArg Bool.not (dv x)
    simpa using eq
