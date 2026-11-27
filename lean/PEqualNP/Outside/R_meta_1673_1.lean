import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Strip the prescribed first gate, then prove that the last operation uses only middle-gate outputs.
-- Each child has thirteen middle gates and draws its final operands only from their outputs.
-- Each middle gate reads only existing wires. Together they must read all nine raw inputs.
-- The later operand is always placed on the last middle wire.
-- Prefix evaluation and index clipping follow the checked reduction R_meta_1672_1.
theorem PEqualNP.Outside.R_meta_1673_1
  (andSearch : ∀ (middle : List Gate) (a : Fin 13), middle.length = 13 →
    FanInTwo ⟨middle,0⟩ → (∀ j : Fin middle.length, ∀ i ∈ (middle.get j).inputs, i < 10+j.val) →
    (∀ p : Fin 9, ∃ g ∈ middle, p.val ∈ g.inputs) →
    ∃ x : Fin 9 → Bool, let w := (Circuit.mk middle 0).wires (List.ofFn x ++ [x 0 || x 1])
      (w.getD (10+a.val) false && w.getD 22 false) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
  (orSearch : ∀ (middle : List Gate) (a : Fin 13), middle.length = 13 →
    FanInTwo ⟨middle,0⟩ → (∀ j : Fin middle.length, ∀ i ∈ (middle.get j).inputs, i < 10+j.val) →
    (∀ p : Fin 9, ∃ g ∈ middle, p.val ∈ g.inputs) →
    ∃ x : Fin 9 → Bool, let w := (Circuit.mk middle 0).wires (List.ofFn x ++ [x 0 || x 1])
      (w.getD (10+a.val) false || w.getD 22 false) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
  (notSearch : ∀ (middle : List Gate), middle.length = 13 →
    FanInTwo ⟨middle,0⟩ → (∀ j : Fin middle.length, ∀ i ∈ (middle.get j).inputs, i < 10+j.val) →
    (∀ p : Fin 9, ∃ g ∈ middle, p.val ∈ g.inputs) →
    ∃ x : Fin 9 → Bool, let w := (Circuit.mk middle 0).wires (List.ofFn x ++ [x 0 || x 1])
      (!w.getD 22 false) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)))
  : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y 1)) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ C.size := by
  intro circuit fan first correct
  by_contra insufficient
  have sizeLimit : circuit.size ≤ 15 := by omega
  let target := fun x : Fin 9 → Bool =>
    (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
    (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
    (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  let seed := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 1]
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let run := fun (gs : List Gate) (w : List Bool) => gs.foldl step w
  have extend (gs : List Gate) (w : List Bool) :
      ∃ extra, run gs w = w ++ extra ∧ extra.length = gs.length := by
    induction gs generalizing w with
    | nil => exact ⟨[], by simp [run], rfl⟩
    | cons g rest ih =>
      obtain ⟨extra, heq, hlen⟩ := ih (step w g)
      refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: extra, ?_, by simp [hlen]⟩
      change run rest (step w g) = _
      rw [heq]
      simp [step, List.append_assoc]
  have evalAnd (xs : List Bool) : GateOp.and.eval xs=xs.all id := rfl
  have evalOr (xs : List Bool) : GateOp.or.eval xs=xs.any id := rfl
  have evalNot (xs : List Bool) : GateOp.not.eval xs= !(xs.headD false) := rfl
  have runLength (gs : List Gate) (w : List Bool) :
      (run gs w).length = w.length + gs.length := by
    obtain ⟨extra, heq, hlen⟩ := extend gs w
    simp [heq, hlen]
  -- A singleton neighbor and its incident edge distinguish each raw input
  -- even when the forced OR is available. A missing raw input gives a witness immediately.
  have unread (m : List Gate) (omits : ¬∀ p : Fin 9, ∃ g ∈ m, p.val ∈ g.inputs) :
      ∃ x y : Fin 9 → Bool, target x=false ∧ target y=true ∧
      ∀ i : ℕ, 10 ≤ i → (run m (seed x)).getD i false = (run m (seed y)).getD i false := by
    push Not at omits
    obtain ⟨p,missing⟩ := omits
    let neighbor : Fin 9 → ℕ := ![2,1,2,4,8,1,2,4,8]
    let lo (k : Fin 9) := fun b : Fin 9 => (neighbor k).testBit b.val
    let hi (k : Fin 9) := fun b : Fin 9 => ((neighbor k)+2^k.val).testBit b.val
    have data : ∀ k : Fin 9, target (lo k)=false ∧ target (hi k)=true ∧
        ∀ i : Fin 10, i.val  ≠  k.val → (seed (lo k)).getD i.val false = (seed (hi k)).getD i.val false := by decide
    have copyRead (gs : List Gate) (w z : List Bool) (sameLen : w.length=z.length)
        (other : ∀ i : ℕ, i ≠ p.val → w.getD i false=z.getD i false)
        (absent : ∀ g ∈ gs, p.val ∉ g.inputs) :
        ∀ i : ℕ, i ≠ p.val → (run gs w).getD i false=(run gs z).getD i false := by
      induction gs generalizing w z with
      | nil => exact other
      | cons g rest ih =>
        have vals : (g.inputs.map fun i => w.getD i false)=(g.inputs.map fun i => z.getD i false) := by
          apply List.map_congr_left
          intro i hi
          exact other i (fun eq => absent g (by simp) (eq ▸ hi))
        have sameStep : (step w g).length=(step z g).length := by simp [step,sameLen]
        apply ih (step w g) (step z g) sameStep _ (fun u hu => absent u (by simp [hu]))
        intro i ne
        dsimp only [step]
        rw [vals]
        by_cases low : i < w.length
        · rw [List.getD_append _ _ _ _ low,List.getD_append _ _ _ _ (sameLen ▸ low)]
          exact other i ne
        · rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),sameLen]
    obtain ⟨off,on,matchBits⟩ := data p
    refine ⟨lo p,hi p,off,on,?_⟩
    intro i later
    apply copyRead m _ _ (by simp [seed]) _ missing i (by omega)
    intro a ne
    by_cases valid : a < 10
    · exact matchBits ⟨a,valid⟩ ne
    · rw [List.getD_eq_default _ false (by simp [seed]; omega),List.getD_eq_default _ false (by simp [seed]; omega)]
  have andReady : ∀ (middle : List Gate) (a : Fin 13), middle.length = 13 →
    FanInTwo ⟨middle,0⟩ → (∀ j : Fin middle.length, ∀ i ∈ (middle.get j).inputs, i < 10+j.val) →
    ∃ x : Fin 9 → Bool, let w := (Circuit.mk middle 0).wires (List.ofFn x ++ [x 0 || x 1])
      (w.getD (10+a.val) false && w.getD 22 false) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    intro m a sz good safe
    by_cases uses : ∀ p : Fin 9, ∃ g ∈ m, p.val∈g.inputs
    · exact andSearch m a sz good safe uses
    obtain ⟨x,y,off,on,eq⟩ := unread m uses
    by_contra! allEqual
    change ∀ x, ¬ ¬ (((run m (seed x)).getD (10+a.val) false && (run m (seed x)).getD 22 false)=target x) at allEqual
    have atX := not_not.mp (allEqual x)
    have atY := not_not.mp (allEqual y)
    rw [off,eq (10+a.val) (by omega),eq 22 (by omega)] at atX
    rw [on,atX] at atY
    contradiction
  have orReady : ∀ (middle : List Gate) (a : Fin 13), middle.length = 13 →
    FanInTwo ⟨middle,0⟩ → (∀ j : Fin middle.length, ∀ i ∈ (middle.get j).inputs, i < 10+j.val) →
    ∃ x : Fin 9 → Bool, let w := (Circuit.mk middle 0).wires (List.ofFn x ++ [x 0 || x 1])
      (w.getD (10+a.val) false || w.getD 22 false) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    intro m a sz good safe
    by_cases uses : ∀ p : Fin 9, ∃ g ∈ m, p.val∈g.inputs
    · exact orSearch m a sz good safe uses
    obtain ⟨x,y,off,on,eq⟩ := unread m uses
    by_contra! allEqual
    change ∀ x, ¬ ¬ (((run m (seed x)).getD (10+a.val) false || (run m (seed x)).getD 22 false)=target x) at allEqual
    have atX := not_not.mp (allEqual x)
    have atY := not_not.mp (allEqual y)
    rw [off,eq (10+a.val) (by omega),eq 22 (by omega)] at atX
    rw [on,atX] at atY
    contradiction
  have notReady : ∀ (middle : List Gate), middle.length = 13 →
    FanInTwo ⟨middle,0⟩ → (∀ j : Fin middle.length, ∀ i ∈ (middle.get j).inputs, i < 10+j.val) →
    ∃ x : Fin 9 → Bool, let w := (Circuit.mk middle 0).wires (List.ofFn x ++ [x 0 || x 1])
      (!w.getD 22 false) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    intro m sz good safe
    by_cases uses : ∀ p : Fin 9, ∃ g ∈ m, p.val∈g.inputs
    · exact notSearch m sz good safe uses
    obtain ⟨x,y,off,on,eq⟩ := unread m uses
    by_contra! allEqual
    change ∀ x, ¬ ¬ ((!(run m (seed x)).getD 22 false)=target x) at allEqual
    have atX := not_not.mp (allEqual x)
    have atY := not_not.mp (allEqual y)
    rw [off,eq 22 (by omega)] at atX
    rw [on,atX] at atY
    contradiction
  -- Replace forward reads by the constant false they denote, without an extra gate.
  have oneGate (g : Gate) (n : ℕ)
      (good : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
      ∃ h : Gate, (h.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ h.inputs.length≤2) ∧
        (∀ k∈h.inputs,k<n) ∧ ∀ w : List Bool, w.length=n → step w h=step w g := by
    by_cases valid : ∀ k∈g.inputs,k<n
    · exact ⟨g,good,valid,fun _ _ => rfl⟩
    have op : g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not := good.1
    rcases op with andOp | orOp | notOp
    · push Not at valid
      obtain ⟨k,hk,big⟩ := valid
      refine ⟨⟨.or,[]⟩,by simp,by simp,?_⟩
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
      refine ⟨⟨.or,live⟩,⟨by simp,(List.length_filter_le _ _).trans good.2⟩,?_,?_⟩
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
      | nil => exact ⟨⟨.and,[]⟩,by simp,by simp,fun w _ => by simp [step,notOp,eq,evalAnd,evalNot]⟩
      | cons k ks =>
        by_cases ok : k<n
        · exact ⟨⟨.not,[k]⟩,by simp,by simpa using ok,fun w _ => by simp [step,notOp,eq,evalNot]⟩
        · refine ⟨⟨.and,[]⟩,by simp,by simp,?_⟩
          intro w len
          have missing := List.getD_eq_default w false (by omega : w.length≤k)
          change w++[true] = w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
          rw [notOp,eq]
          change w++[true] = w++[!(w.getD k false)]
          rw [missing]
          rfl
  have canonical (m : List Gate) (n : ℕ) (fan : FanInTwo ⟨m,0⟩) :
      ∃ d : List Gate, d.length=m.length ∧ FanInTwo ⟨d,0⟩ ∧
        (∀ j : Fin d.length, ∀ i ∈ (d.get j).inputs, i<n+j.val) ∧
        ∀ w : List Bool, w.length=n → run d w=run m w := by
    induction m generalizing n with
    | nil => exact ⟨[],rfl,fan,fun j => Fin.elim0 j,fun _ _ => rfl⟩
    | cons g gs ih =>
      obtain ⟨h,good,pins,sim⟩ := oneGate g n (fan _ (by simp))
      obtain ⟨d,len,dfan,dsafe,deq⟩ := ih (n+1) (fun z hz => fan z (by simp [hz]))
      refine ⟨h::d,by simp [len],?_,?_,?_⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | member
        · exact good
        · exact dfan _ member
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
  have ready (m : List Gate) (hm : m.length=13) (fan : FanInTwo ⟨m,0⟩) :
      ∃ d : List Gate, d.length=13 ∧ FanInTwo ⟨d,0⟩ ∧
      (∀ j : Fin d.length, ∀ i ∈ (d.get j).inputs, i<10+j.val) ∧
      ∀ x : Fin 9 → Bool, run d (seed x)=run m (seed x) := by
    obtain ⟨d,len,df,ds,de⟩ := canonical m 10 fan
    exact ⟨d,len.trans hm,df,ds,fun x => de _ (by simp [seed])⟩
  have andLast : ∀ (middle : List Gate) (a : Fin 13), middle.length = 13 →
    FanInTwo ⟨middle,0⟩ → (∀ g ∈ middle, ∀ i ∈ g.inputs, i ≤ 23) →
    ∃ x : Fin 9 → Bool, let w := (Circuit.mk middle 0).wires (List.ofFn x ++ [x 0 || x 1])
      (w.getD (10+a.val) false && w.getD 22 false) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    intro m a sz good _
    obtain ⟨d,len,fan,safe,equal⟩ := ready m sz good
    obtain ⟨x,bad⟩ := andReady d a len fan safe
    refine ⟨x,?_⟩
    change ((run d (seed x)).getD (10+a.val) false && (run d (seed x)).getD 22 false) ≠ target x at bad
    change ((run m (seed x)).getD (10+a.val) false && (run m (seed x)).getD 22 false) ≠ target x
    simpa only [equal x] using bad
  have orLast : ∀ (middle : List Gate) (a : Fin 13), middle.length = 13 →
    FanInTwo ⟨middle,0⟩ → (∀ g ∈ middle, ∀ i ∈ g.inputs, i ≤ 23) →
    ∃ x : Fin 9 → Bool, let w := (Circuit.mk middle 0).wires (List.ofFn x ++ [x 0 || x 1])
      (w.getD (10+a.val) false || w.getD 22 false) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    intro m a sz good _
    obtain ⟨d,len,fan,safe,equal⟩ := ready m sz good
    obtain ⟨x,bad⟩ := orReady d a len fan safe
    refine ⟨x,?_⟩
    change ((run d (seed x)).getD (10+a.val) false || (run d (seed x)).getD 22 false) ≠ target x at bad
    change ((run m (seed x)).getD (10+a.val) false || (run m (seed x)).getD 22 false) ≠ target x
    simpa only [equal x] using bad
  have notLast : ∀ (middle : List Gate), middle.length = 13 →
    FanInTwo ⟨middle,0⟩ → (∀ g ∈ middle, ∀ i ∈ g.inputs, i ≤ 23) →
    ∃ x : Fin 9 → Bool, let w := (Circuit.mk middle 0).wires (List.ofFn x ++ [x 0 || x 1])
      (!w.getD 22 false) ≠ ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) := by
    intro m sz good _
    obtain ⟨d,len,fan,safe,equal⟩ := ready m sz good
    obtain ⟨x,bad⟩ := notReady d len fan safe
    refine ⟨x,?_⟩
    change (!(run d (seed x)).getD 22 false) ≠ target x at bad
    change (!(run m (seed x)).getD 22 false) ≠ target x
    simpa only [equal x] using bad
  -- Move the selected later operand to the last wire without adding a gate.
  -- If it is already last, keep the list. Otherwise replace the unused last gate by a copy.
  have moveLast (m : List Gate) (j : Fin 13) (hm : m.length=13) (hf : FanInTwo ⟨m,0⟩)
      (hb : ∀ g ∈ m, ∀ i ∈ g.inputs, i≤23) :
      ∃ d : List Gate, d.length=13 ∧ FanInTwo ⟨d,0⟩ ∧ (∀ g ∈ d, ∀ i ∈ g.inputs, i≤23) ∧
        ∀ x : Fin 9 → Bool, (run d (seed x)).getD 22 false = (run m (seed x)).getD (10+j.val) false ∧
        ∀ a : Fin 13, a≤j → (run d (seed x)).getD (10+a.val) false = (run m (seed x)).getD (10+a.val) false := by
    by_cases last : j.val=12
    · exact ⟨m,hm,hf,hb,fun _ => ⟨by rw [last],fun _ _ => rfl⟩⟩
    let pre := m.take 12
    let copy : Gate := ⟨.or,[10+j.val]⟩
    have len : pre.length=12 := by simp [pre,hm]
    have mem (g : Gate) (h : g∈pre) : g∈m := List.mem_of_mem_take h
    refine ⟨pre++[copy],by simp [len],?_,?_,?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with h | h
      · exact hf g (mem g h)
      · have eq : g=copy := by simpa using h
        subst g
        simp [copy]
    · intro g hg i hi
      rcases List.mem_append.mp hg with h | h
      · exact hb g (mem g h) i hi
      · have eq : g=copy := by simpa using h
        subst g
        have ai : i=10+j.val := by simpa [copy] using hi
        omega
    intro x
    let w := run pre (seed x)
    have n : w.length=22 := by rw [show w.length=(run pre (seed x)).length from rfl,runLength,len]; simp [seed]
    obtain ⟨tail,eq,_⟩ := extend (m.drop 12) w
    have original : run m (seed x)=w++tail := by
      calc
        run m (seed x) = run (pre++m.drop 12) (seed x) := by rw [show pre++m.drop 12=m from List.take_append_drop 12 m]
        _ = _ := by simpa only [run,List.foldl_append] using eq
    have copied : run (pre++[copy]) (seed x)=w++[w.getD (10+j.val) false] := by
      simp only [run,List.foldl_append,List.foldl_cons,List.foldl_nil]
      change w++[GateOp.or.eval [[w.getD (10+j.val) false].headD false]]=_
      simp [evalOr]
    rw [copied,original]
    constructor
    · rw [List.getD_append_right _ _ _ _ (by omega),n,List.getD_append _ _ _ _ (by omega : 10+j.val<w.length)]
      rfl
    · intro a le
      have small : 10+a.val<w.length := by change a.val≤j.val at le; omega
      rw [List.getD_append _ _ _ _ small,List.getD_append _ _ _ _ small]
  have pairs (op : Bool → Bool → Bool) (comm : ∀ a b, op a b=op b a)
      (child : ∀ (m : List Gate) (a : Fin 13), m.length=13 → FanInTwo ⟨m,0⟩ →
        (∀ g ∈ m, ∀ i ∈ g.inputs, i≤23) → ∃ x,
        op ((run m (seed x)).getD (10+a.val) false) ((run m (seed x)).getD 22 false) ≠ target x)
      (m : List Gate) (a b : Fin 13) (hm : m.length=13) (hf : FanInTwo ⟨m,0⟩)
      (hb : ∀ g ∈ m, ∀ i ∈ g.inputs, i≤23) :
      ∃ x, op ((run m (seed x)).getD (10+a.val) false) ((run m (seed x)).getD (10+b.val) false) ≠ target x := by
    have ordered (u v : Fin 13) (le : u ≤ v) : ∃ x,
        op ((run m (seed x)).getD (10+u.val) false) ((run m (seed x)).getD (10+v.val) false) ≠ target x := by
      obtain ⟨d,sz,fan,bd,same⟩ := moveLast m v hm hf hb
      obtain ⟨x,err⟩ := child d u sz fan bd
      exact ⟨x,by simpa only [(same x).1,(same x).2 u le] using err⟩
    rcases le_total a b with le | le
    · exact ordered a b le
    · obtain ⟨x,err⟩ := ordered b a le
      exact ⟨x,by rwa [comm]⟩
  have andCase := pairs Bool.and Bool.and_comm andLast
  have orCase := pairs Bool.or Bool.or_comm orLast
  have notCase (m : List Gate) (a : Fin 13) (hm : m.length=13) (hf : FanInTwo ⟨m,0⟩)
      (hb : ∀ g ∈ m, ∀ i ∈ g.inputs, i≤23) :
      ∃ x, (!(run m (seed x)).getD (10+a.val) false) ≠ target x := by
    obtain ⟨d,sz,fan,bd,same⟩ := moveLast m a hm hf hb
    obtain ⟨x,err⟩ := notLast d sz fan bd
    refine ⟨x,?_⟩
    change (!(run d (seed x)).getD 22 false) ≠ target x at err
    simpa only [(same x).1] using err
  let clip := fun i : ℕ => (⟨min i 23, by omega⟩ : Fin 24)
  have sameRead (w : List Bool) (lengthBound : w.length ≤ 23) (i : ℕ) :
      w.getD (clip i).val false = w.getD i false := by
    by_cases small : i ≤ 23
    · simp [clip, Nat.min_eq_left small]
    · have large : 23 ≤ i := by omega
      change w.getD (min i 23) false = _
      rw [Nat.min_eq_right large, List.getD_eq_default w false lengthBound,
        List.getD_eq_default w false (by omega : w.length ≤ i)]
  let norm := fun g : Gate => Gate.mk g.op (g.inputs.map fun i => (clip i).val)
  have normStep (w : List Bool) (g : Gate) (hw : w.length ≤ 23) :
      step w (norm g) = step w g := by
    simp only [step, norm, List.map_map, Function.comp_def, sameRead w hw]
  have normRun (gs : List Gate) (w : List Bool) (hw : w.length + gs.length ≤ 23) :
      run (gs.map norm) w = run gs w := by
    induction gs generalizing w with
    | nil => rfl
    | cons g rest ih =>
      change run (rest.map norm) (step w (norm g)) = run rest (step w g)
      have hw' : w.length ≤ 23 := by omega
      rw [normStep w g hw']
      apply ih
      simp only [List.length_cons] at hw
      simp [step]
      omega
  have cut (middle : List Gate) (pins : List ℕ) (op : GateOp)
      (hsize : middle.length ≤ 13) (hfan : FanInTwo ⟨middle, 0⟩)
      (hpin : pins.length ≤ 2) (hop : op = .and ∨ op = .or ∨ op = .not) :
      ∃ x, op.eval (pins.map fun i => (run middle (seed x)).getD i false) ≠ target x := by
    let zero : Gate := ⟨.or,[]⟩
    let clean := middle.map norm
    let padded := clean ++ List.replicate (13-middle.length) zero
    have plen : padded.length=13 := by simp [padded,clean]; omega
    have fanP : FanInTwo ⟨padded,0⟩ := by
      intro g hg
      rcases List.mem_append.mp hg with mem | mem
      · obtain ⟨h,hm,rfl⟩ := List.mem_map.mp mem
        exact ⟨(hfan h hm).1,by simpa [norm] using (hfan h hm).2⟩
      · have eq := (List.mem_replicate.mp mem).2
        subst g
        simp [zero]
    have bounded : ∀ g ∈ padded, ∀ i ∈ g.inputs, i ≤ 23 := by
      intro g hg i hi
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨old,_,rfl⟩ := List.mem_map.mp hg
        obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
        exact min_le_right _ _
      · have eq := (List.mem_replicate.mp hg).2
        subst g
        simp [zero] at hi
    let read := fun (x : Fin 9 → Bool) (a : ℕ) => (run middle (seed x)).getD a false
    let tag := fun a : ℕ => (⟨min (a-10) 12,by omega⟩ : Fin 13)
    let inside := fun a : ℕ => 10≤a ∧ a<10+middle.length
    have srcLen (x : Fin 9 → Bool) : (seed x).length=10 := by simp [seed]
    have width (x : Fin 9 → Bool) : (run middle (seed x)).length=10+middle.length :=
      (runLength _ _).trans (by rw [srcLen])
    have lowRead (x : Fin 9 → Bool) (a : ℕ) (ha : a<10) : read x a=(seed x).getD a false := by
      obtain ⟨extra,he,_⟩ := extend middle (seed x)
      unfold read
      rw [he,List.getD_append _ _ _ _ (by rw [srcLen]; omega)]
    have highRead (x : Fin 9 → Bool) (a : ℕ) (ha : 10+middle.length≤a) : read x a=false :=
      List.getD_eq_default _ false (by rw [width]; omega)
    have transfer (x : Fin 9 → Bool) (a : ℕ) (ha : inside a) :
        (run padded (seed x)).getD (10+(tag a).val) false = read x a := by
      have back : 10+(tag a).val=a := by dsimp [tag]; dsimp [inside] at ha; omega
      rw [back]
      have pref : run clean (seed x)=run middle (seed x) :=
        normRun _ _ (by rw [srcLen]; omega)
      have allEq : run padded (seed x)=run (List.replicate (13-middle.length) zero) (run clean (seed x)) := by
        simp only [run,padded,List.foldl_append]
      obtain ⟨extra,ex,_⟩ := extend (List.replicate (13-middle.length) zero) (run clean (seed x))
      rw [allEq,ex,pref,List.getD_append _ _ _ _ (by rw [width]; exact ha.2)]
    let bits := fun (m : ℕ) (i : Fin 9) => Nat.testBit m i.val
    have lowOn : ∀ j : Fin 10,
        let x := bits (if j.val<9 then 2^j.val else 1)
        (seed x).getD j.val false=true ∧ target x=false := by decide
    have lowOff : ∀ j : Fin 10,
        let x := bits (if j.val=0 ∨ j.val=1 ∨ j.val=9 then 12 else 3)
        (seed x).getD j.val false=false ∧ target x=true := by decide
    have noneOn : ∀ j : Fin 10, (seed (bits 0)).getD j.val false=false := by decide
    have zeroF : target (bits 0)=false := by decide
    have edgeF : target (bits 3)=true := by decide
    have below (a : ℕ) (necessary : ∀ x, target x=true → read x a=true) : inside a := by
      constructor
      · by_contra! small
        obtain ⟨off,on⟩ := lowOff ⟨a,small⟩
        have v := necessary _ on
        rw [lowRead _ a small,off] at v
        contradiction
      · by_contra! big
        have v := necessary _ edgeF
        rw [highRead _ _ big] at v
        contradiction
    have above (a : ℕ) (sufficient : ∀ x, read x a=true → target x=true) : 10≤a := by
      by_contra! small
      obtain ⟨on,off⟩ := lowOn ⟨a,small⟩
      have v := sufficient _ ((lowRead _ _ small).trans on)
      rw [off] at v
      contradiction
    have impossibleAnd (a b : ℕ) (ok : ∀ x, (read x a && read x b)=target x) : False := by
      have both (x) (hit : target x=true) := Bool.and_eq_true_iff.mp ((ok x).trans hit)
      have ha := below a (fun x h => (both x h).1)
      have hb := below b (fun x h => (both x h).2)
      obtain ⟨x,err⟩ := andCase padded (tag a) (tag b) plen fanP bounded
      apply err
      rw [transfer x a ha,transfer x b hb]
      exact ok x
    have noTap (a : ℕ) (ok : ∀ x, read x a=target x) : False :=
      impossibleAnd a a (fun x => by simp [ok x])
    have impossibleOr (a b : ℕ) (ok : ∀ x, (read x a || read x b)=target x) : False := by
      have ca := above a (fun x h => by rw [←ok x,h]; rfl)
      have cb := above b (fun x h => by rw [←ok x,h]; simp)
      by_cases ah : 10+middle.length≤a
      · exact noTap b (fun x => by simpa [highRead x a ah] using ok x)
      by_cases bh : 10+middle.length≤b
      · exact noTap a (fun x => by simpa [highRead x b bh] using ok x)
      obtain ⟨x,err⟩ := orCase padded (tag a) (tag b) plen fanP bounded
      apply err
      rw [transfer x a ⟨ca,by omega⟩,transfer x b ⟨cb,by omega⟩]
      exact ok x
    have impossibleNot (a : ℕ) (ok : ∀ x, (!read x a)=target x) : False := by
      have z := ok (bits 0)
      rw [zeroF] at z
      by_cases lo : a<10
      · rw [lowRead _ _ lo,noneOn ⟨a,lo⟩] at z
        contradiction
      by_cases hi : 10+middle.length≤a
      · rw [highRead _ _ hi] at z
        contradiction
      obtain ⟨x,err⟩ := notCase padded (tag a) plen fanP bounded
      apply err
      rw [transfer x a ⟨by omega,by omega⟩]
      exact ok x
    by_contra! eq
    change ∀ x, op.eval (pins.map (read x))=target x at eq
    rcases hop with rfl | rfl | rfl
    · rcases pins with _ | ⟨a,_ | ⟨b,_ | ⟨c,rest⟩⟩⟩
      · simpa [zeroF,evalAnd,evalOr,evalNot] using eq (bits 0)
      · exact noTap a (fun x => by simpa [evalAnd,evalOr,evalNot] using eq x)
      · exact impossibleAnd a b (fun x => by simpa [evalAnd,evalOr,evalNot] using eq x)
      · simp at hpin
    · rcases pins with _ | ⟨a,_ | ⟨b,_ | ⟨c,rest⟩⟩⟩
      · simpa [edgeF,evalAnd,evalOr,evalNot] using eq (bits 3)
      · exact noTap a (fun x => by simpa [evalAnd,evalOr,evalNot] using eq x)
      · exact impossibleOr a b (fun x => by simpa [evalAnd,evalOr,evalNot] using eq x)
      · simp at hpin
    · cases pins with
      | nil => simpa [zeroF,evalAnd,evalOr,evalNot] using eq (bits 0)
      | cons a rest => exact impossibleNot a (fun x => by simpa [evalAnd,evalOr,evalNot] using eq x)
  have tap (middle : List Gate) (out : ℕ) (hs : middle.length ≤ 13)
      (hf : FanInTwo ⟨middle, 0⟩) :
      ∃ x, (run middle (seed x)).getD out false ≠ target x := by
    obtain ⟨x, hx⟩ := cut middle [out] .or hs hf (by simp) (Or.inr (Or.inl rfl))
    have readOne (b : Bool) : GateOp.or.eval [b] = b := by cases b <;> rfl
    change GateOp.or.eval [(run middle (seed x)).getD out false] ≠ target x at hx
    exact ⟨x, by rwa [readOne] at hx⟩
  obtain ⟨gs, out⟩ := circuit
  cases gs with
  | nil =>
    have h := first (fun _ => true)
    change (List.ofFn (fun _ : Fin 9 => true)).getD 9 false = true at h
    rw [List.getD_eq_default _ false (by simp)] at h
    contradiction
  | cons g rest =>
    have firstValue (x : Fin 9 → Bool) :
        g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false) = (x 0 || x 1) := by
      let w := List.ofFn x
      let value := g.op.eval (g.inputs.map fun i => w.getD i false)
      obtain ⟨extra, heq, _⟩ := extend rest (w ++ [value])
      have h := first x
      change (run rest (w ++ [value])).getD 9 false = _ at h
      rw [heq, List.getD_append _ _ false 9 (by simp [w]),
        List.getD_append_right w [value] false 9 (by simp [w])] at h
      simpa [value, w] using h
    have computes (x : Fin 9 → Bool) : (run rest (seed x)).getD out false = target x := by
      have h := congrFun correct x
      change (run rest (List.ofFn x ++
        [g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)])).getD out false = target x at h
      rw [firstValue] at h
      exact h
    obtain hempty | ⟨middle, last, eqRest⟩ := List.eq_nil_or_concat' rest
    · subst rest
      have emptyFan : FanInTwo ⟨[], 0⟩ := by intro a ha; cases ha
      obtain ⟨x, hx⟩ := tap [] out (by decide) emptyFan
      exact hx (computes x)
    · subst rest
      have hs : middle.length ≤ 13 := by
        change (g :: (middle ++ [last])).length ≤ 15 at sizeLimit
        simp only [List.length_cons, List.length_append] at sizeLimit
        omega
      have hf : FanInTwo ⟨middle, 0⟩ := by
        intro a ha
        exact fan a (by simp [ha])
      have lastOK := fan last (by simp)
      let value := fun x : Fin 9 → Bool =>
        last.op.eval (last.inputs.map fun i => (run middle (seed x)).getD i false)
      have atOut (x : Fin 9 → Bool) :
          (run middle (seed x) ++ [value x]).getD out false = target x := by
        simpa only [run, List.foldl_append, List.foldl_cons, List.foldl_nil, step, value]
          using computes x
      have lengthAt (x : Fin 9 → Bool) : (run middle (seed x)).length = 10 + middle.length := by
        rw [runLength]
        simp [seed]
      by_cases endWire : out = 10 + middle.length
      · have hop : last.op = .and ∨ last.op = .or ∨ last.op = .not := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using lastOK.1
        obtain ⟨x, hx⟩ := cut middle last.inputs last.op hs hf lastOK.2 hop
        have h := atOut x
        rw [List.getD_append_right _ _ _ _ (by rw [lengthAt]; omega), lengthAt, endWire] at h
        exact hx (by simpa [value] using h)
      · obtain ⟨x, hx⟩ := tap middle out hs hf
        have h := atOut x
        by_cases early : out < (run middle (seed x)).length
        · rw [List.getD_append _ _ _ _ early] at h
          exact hx h
        · have beyond : (run middle (seed x)).length < out := by rw [lengthAt] at *; omega
          rw [List.getD_eq_default _ false (by simp; omega)] at h
          apply hx
          rw [List.getD_eq_default _ false (by omega)]
          exact h
