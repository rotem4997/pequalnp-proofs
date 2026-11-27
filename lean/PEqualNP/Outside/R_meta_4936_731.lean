import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_4936_731
    (normalize : ∀ C : Circuit, FanInTwo C → (∀ g ∈ C.gates, ∀ w ∈ g.inputs, w ≤ 29) →
      ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧ D.output = C.output ∧
        (∀ g ∈ D.gates, ∀ w ∈ g.inputs, w ≤ 29) ∧
        (∀ g ∈ D.gates, g.inputs.Pairwise (· < ·) ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)) ∧ ∀ x : List Bool, D.eval x = C.eval x)
    (necessary : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → (∀ (x7 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [if x2 = Bool.true then x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) else x7 (0 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ))]) = (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))) x7) → 10 ≤ x1.size)
    (lower : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → 10 ≤ x1.size → x1.size ≤ (18 : ℕ) → x1.output ≤ (29 : ℕ) → (∀ j : Fin x1.gates.length, ∀ i ∈ (x1.gates.get j).inputs, i < 11 + j.val) → (∀ g ∈ x1.gates, g.inputs.Pairwise (· < ·) ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)) → ∃ (x7 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [if x2 = Bool.true then x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) else x7 (0 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ))]) ≠ (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))) x7) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → x1.output ≤ (29 : ℕ) → (∀ x6 ∈ x1.gates, ∀ x8 ∈ x6.inputs, x8 ≤ (29 : ℕ)) → ∃ (x7 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x7 ++ [if x2 = Bool.true then x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) else x7 (0 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ))]) ≠ (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))) x7 := by
  intro C b hC hs ho hi
  obtain ⟨D, hD, hsize, hout, hin, hcanon, he⟩ := normalize C hC hi
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run := fun (gs : List Gate) (w : List Bool) => gs.foldl step w
  have evalAnd (xs : List Bool) : GateOp.and.eval xs=xs.all id := rfl
  have evalOr (xs : List Bool) : GateOp.or.eval xs=xs.any id := rfl
  have evalNot (xs : List Bool) : GateOp.not.eval xs= !(xs.headD false) := rfl
  let sorted (g : Gate) := g.inputs.Pairwise (· < ·) ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)
  -- Forward-read simplification and its wire-table simulation follow R_meta_1673_1.
  have oneGate (g : Gate) (n : ℕ)
      (good : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) (ordered : sorted g) :
      ∃ h : Gate, (h.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ h.inputs.length≤2) ∧
        sorted h ∧ (∀ k∈h.inputs,k<n) ∧ ∀ w : List Bool, w.length=n → step w h=step w g := by
    by_cases valid : ∀ k∈g.inputs,k<n
    · exact ⟨g,good,ordered,valid,fun _ _ => rfl⟩
    have op : g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not := good.1
    rcases op with andOp | orOp | notOp
    · push Not at valid
      obtain ⟨k,hk,big⟩ := valid
      refine ⟨⟨.or,[]⟩,by simp,by simp [sorted],by simp,?_⟩
      intro w len
      have absent : w.getD k false=false := List.getD_eq_default _ _ (by omega)
      have kills : (g.inputs.map fun i => w.getD i false).all id=false := by
        apply Bool.eq_false_iff.mpr
        intro allHit
        have hit := List.all_eq_true.mp allHit false (List.mem_map.mpr ⟨k,hk,absent⟩)
        contradiction
      change w++[false] = w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
      rw [andOp,evalAnd,kills]
    · let live := g.inputs.filter (fun i => decide (i<n))
      refine ⟨⟨.or,live⟩,⟨by simp,(List.length_filter_le _ _).trans good.2⟩,⟨List.Pairwise.filter _ ordered.1, by simp⟩,?_,?_⟩
      · intro k hk
        exact of_decide_eq_true (List.mem_filter.mp hk).2
      intro w len
      apply congrArg (fun b : Bool => w++[b])
      change GateOp.or.eval (live.map _) = g.op.eval (g.inputs.map _)
      rw [orOp]
      apply Bool.eq_iff_iff.mpr
      simp only [evalOr,List.any_map,Function.comp_def,id_eq,List.any_eq_true]
      constructor
      · rintro ⟨k,hk,on⟩
        exact ⟨k,(List.mem_filter.mp hk).1,on⟩
      · rintro ⟨k,hk,on⟩
        have small : k<n := by
          by_contra! big
          rw [List.getD_eq_default _ false (by omega : w.length≤k)] at on
          contradiction
        exact ⟨k,List.mem_filter.mpr ⟨hk,decide_eq_true small⟩,on⟩
    · cases eq : g.inputs with
      | nil => exact ⟨⟨.and,[]⟩,by simp,by simp [sorted],by simp,fun w _ => by simp [step,notOp,eq,evalAnd,evalNot]⟩
      | cons k ks =>
        by_cases ok : k<n
        · exact ⟨⟨.not,[k]⟩,by simp,by simp [sorted],by simpa using ok,fun w _ => by simp [step,notOp,eq,evalNot]⟩
        · refine ⟨⟨.and,[]⟩,by simp,by simp [sorted],by simp,?_⟩
          intro w len
          have missing := List.getD_eq_default w false (by omega : w.length≤k)
          change w++[true] = w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
          rw [notOp,eq]
          change w++[true] = w++[!(w.getD k false)]
          rw [missing]
          rfl
  have canonical (m : List Gate) (n : ℕ) (fan : FanInTwo ⟨m,0⟩) (sort : ∀ g ∈ m, sorted g) :
      ∃ d : List Gate, d.length=m.length ∧ FanInTwo ⟨d,0⟩ ∧ (∀ g ∈ d, sorted g) ∧
        (∀ j : Fin d.length, ∀ i ∈ (d.get j).inputs, i<n+j.val) ∧
        ∀ w : List Bool, w.length=n → run d w=run m w := by
    induction m generalizing n with
    | nil => exact ⟨[],rfl,fan,sort,fun j => Fin.elim0 j,fun _ _ => rfl⟩
    | cons g gs ih =>
      obtain ⟨h,good,ord,pins,sim⟩ := oneGate g n (fan _ (by simp)) (sort _ (by simp))
      obtain ⟨d,len,dfan,dord,dsafe,deq⟩ := ih (n+1) (fun z hz => fan z (by simp [hz])) (fun z hz => sort z (by simp [hz]))
      refine ⟨h::d,by simp [len],?_,?_,?_,?_⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | member
        · exact good
        · exact dfan _ member
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | member
        · exact ord
        · exact dord _ member
      · rintro ⟨j,hj⟩ i hi
        cases j with
        | zero => exact pins i hi
        | succ j =>
          have lj : j<d.length := by simpa using hj
          have low := dsafe ⟨j,lj⟩ i hi
          change i<n+1+j at low
          change i<n+(j+1)
          omega
      · intro w nw
        change run d (step w h)=run gs (step w g)
        rw [sim _ nw]
        apply deq
        simp [step,nw]
  obtain ⟨gs, hlen, hfan, hord, hsafe, hsim⟩ := canonical D.gates 11 hD hcanon
  let E : Circuit := ⟨gs,D.output⟩
  have se : E.size = D.size := hlen
  classical
  by_cases allMatch : ∀ (x7 : Fin (10 : ℕ) → Bool), C.eval (List.ofFn x7 ++ [if b = Bool.true then x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) else x7 (0 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ))]) = (fun (x8 : Fin (10 : ℕ) → Bool) => x8 (0 : Fin (10 : ℕ)) && x8 (1 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (2 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (3 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (4 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (0 : Fin (10 : ℕ)) || x8 (0 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ)) || x8 (1 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (2 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (3 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (4 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (5 : Fin (10 : ℕ)) && x8 (7 : Fin (10 : ℕ)) || x8 (7 : Fin (10 : ℕ)) && x8 (9 : Fin (10 : ℕ)) || x8 (9 : Fin (10 : ℕ)) && x8 (6 : Fin (10 : ℕ)) || x8 (6 : Fin (10 : ℕ)) && x8 (8 : Fin (10 : ℕ)) || x8 (8 : Fin (10 : ℕ)) && x8 (5 : Fin (10 : ℕ))) x7
  · have required := necessary C b hC allMatch
    obtain ⟨x,hx⟩ := lower E b hfan (se ▸ hsize ▸ required) (se ▸ hsize ▸ hs) (hout ▸ ho) hsafe hord
    refine ⟨x, ?_⟩
    let input := List.ofFn x ++ [if b = Bool.true then x 0 && x 1 else x 0 || x 1]
    have inputLen : input.length = 11 := by simp [input]
    have same : E.eval input = D.eval input := congrArg (fun l : List Bool => l.getD D.output false) (hsim input inputLen)
    rw [he] at same
    exact fun h => hx (same.trans h)
  · exact not_forall.mp allMatch
