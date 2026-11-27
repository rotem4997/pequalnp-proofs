import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- The second search runs on complete truth columns. A step adds a new AND,
-- OR or complement of available columns. The input reflection fixes vertex zero.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_2928_1
    (aliases : ∀ (x1 x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (x1=x2 ∨ x2=10 ∨ (x1=0 ∧ x2=9)) →   x1 ≤ x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x7 : BitVec (9 : ℕ)),           have x8 : Fin (9 : ℕ) → Bool := fun (x8 : Fin (9 : ℕ)) => x7.getLsbD ↑x8;           have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];           x3.eval (x9 ++ [x9.getD (↑x1) Bool.false || x9.getD (↑x2) Bool.false]) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x10 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x8 x10.1 && x8 x10.2)
    (remaining : let raw := fun (i : ℕ) => BitVec.ofNat 512 (((2^512-1)/(2^(2^i)+1)) * 2^(2^i))
    let base := (List.range 9).map raw ++ [~~~(raw 0),0,~~~0]
    let target := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).foldl (fun v e => v ||| (raw (e / 10) &&& raw (e % 10))) 0
    let step := fun (s : List (BitVec 512)) (t : Fin 3 × BitVec 512 × BitVec 512) =>
      let a := t.2.1
      let b := t.2.2
      let w := if t.1=0 then a &&& b else if t.1=1 then a ||| b else ~~~a
      if a∈s ∧ b∈s ∧ w∉s then w::s else s
    ∀ k∈([1,2,3,4,6,13,14,15,16,17,18,19,20,25,26,28,29,30,31,37,39,42,50,53,73,75] : List ℕ), ∀ ts : List (Fin 3 × BitVec 512 × BitVec 512), ts.length ≤ 13 →
      target ∉ ts.foldl step ((base.getD (k / 11) 0 ||| base.getD (k % 11) 0)::base)) :
    ∀ (x1 x2 : Fin (11 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit),   x1 ≤ x2 →     PEqualNP.MetaComplexity.FanInTwo x3 →       x3.size ≤ (13 : ℕ) →         ∃ (x7 : BitVec (9 : ℕ)),           have x8 : Fin (9 : ℕ) → Bool := fun (x8 : Fin (9 : ℕ)) => x7.getLsbD ↑x8;           have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];           x3.eval (x9 ++ [x9.getD (↑x1) Bool.false || x9.getD (↑x2) Bool.false]) ≠ [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x10 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x8 x10.1 && x8 x10.2 := by
  intro i j C order fan cap
  by_cases trivialCase : i=j ∨ j=10 ∨ (i=0 ∧ j=9)
  · exact aliases i j C trivialCase order fan cap
  let raw := fun (i : ℕ) => BitVec.ofNat 512 (((2^512-1)/(2^(2^i)+1)) * 2^(2^i))
  let base := (List.range 9).map raw ++ [~~~(raw 0),0,~~~0]
  let target := ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).foldl (fun v e => v ||| (raw (e / 10) &&& raw (e % 10))) 0
  let step := fun (s : List (BitVec 512)) (t : Fin 3 × BitVec 512 × BitVec 512) =>
      let a := t.2.1
      let b := t.2.2
      let w := if t.1=0 then a &&& b else if t.1=1 then a ||| b else ~~~a
      if a∈s ∧ b∈s ∧ w∉s then w::s else s
  let reps := ([1,2,3,4,6,13,14,15,16,17,18,19,20,25,26,28,29,30,31,37,39,42,50,53,73,75] : List ℕ)
  let e : Bool → Fin 9 → Fin 9 := fun b => if b then ![0,5,8,3,4,1,7,6,2] else id
  let lift : Bool → Fin 11 → Fin 11 := fun b a =>
    if h : a.val<9 then ⟨(e b ⟨a.val,h⟩).val,Nat.lt_trans (e b ⟨a.val,h⟩).isLt (by decide : 9<11)⟩ else a
  let pair (b : Bool) (a d : Fin 11) :=
    min (lift b a).val (lift b d).val * 11 + max (lift b a).val (lift b d).val
  have choices : ∀ a d : Fin 11, a≤d → ¬(a=d ∨ d=10 ∨ (a=0 ∧ d=9)) →
      ∃ b : Bool, pair b a d∈reps := by decide +kernel
  obtain ⟨b,hk⟩ := choices i j order trivialCase
  let k := pair b i j
  let mask (a : Fin 11) := base.getD (lift b a).val 0
  let xs := (List.ofFn (fun a : Fin 9 => raw (e b a).val)) ++ [~~~(raw 0), mask i ||| mask j]
  let seed := (base.getD (k / 11) 0 ||| base.getD (k % 11) 0)::base
  have sortMask : ∀ b : Bool, ∀ a d : Fin 11,
      (base.getD (pair b a d / 11) 0 ||| base.getD (pair b a d % 11) 0) =
      (base.getD (lift b a).val 0 ||| base.getD (lift b d).val 0) := by decide +kernel
  have seedOK : ∀ w∈(0 : BitVec 512)::(~~~0)::xs, w∈seed := by
    intro w hw
    change w∈(_ :: base)
    simp only [List.mem_cons] at hw ⊢
    rcases hw with rfl|rfl|hw
    · right; simp [base]
    · right; simp [base]
    · rcases List.mem_append.mp hw with h|h
      · right
        obtain ⟨a,rfl⟩ := List.mem_ofFn.mp h
        apply List.mem_append_left
        apply List.mem_map.mpr
        exact ⟨(e b a).val,List.mem_range.mpr (e b a).isLt,rfl⟩
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with h|h
        · subst w; right; simp [base]
        · subst w; left; exact (sortMask b i j).symm
  let A (g : Gate) : Fin 3 := if g.op.eval [] then (if g.op.eval [true] then 0 else 2) else 1
  let arg (g : Gate) (w : List (BitVec 512)) (l : ℕ) :=
    if l<g.inputs.length then w.getD (g.inputs.getD l 0) 0
    else if A g=0 then ~~~(0 : BitVec 512) else 0
  let value (g : Gate) (w : List (BitVec 512)) :=
    let u := arg g w 0
    let v := arg g w 1
    if A g=0 then u &&& v else if A g=1 then u ||| v else ~~~u
  let ev (gs : List Gate) (w : List (BitVec 512)) :=
    gs.foldl (fun s g => s++[value g s]) w
  let good (g : Gate) := g.op∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2
  let actual (gs : List Gate) (w : List Bool) := gs.foldl
    (fun s g => s++[g.op.eval (g.inputs.map fun a => s.getD a false)]) w
  have read (w : List (BitVec 512)) (r : Fin 512) (l : ℕ) :
      (w.map (fun a => a.getLsbD r.val)).getD l false=(w.getD l 0).getLsbD r.val := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases w[l]? <;> simp
  have andEval (l : List Bool) : GateOp.and.eval l=l.all id := rfl
  have orEval (l : List Bool) : GateOp.or.eval l=l.any id := rfl
  have notEval (l : List Bool) : GateOp.not.eval l= !(l.headD false) := rfl
  have gateBit (g : Gate) (w : List (BitVec 512)) (r : Fin 512) (ok : good g) :
      (value g w).getLsbD r.val=g.op.eval (g.inputs.map fun a => (w.getD a 0).getLsbD r.val) := by
    obtain ⟨o,ins⟩ := g
    obtain ⟨op,sz⟩ := ok
    change o∈({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) at op
    change ins.length≤2 at sz
    rcases op with h|h|h <;> obtain rfl := h
    all_goals
      have oneB : (~~~(0 : BitVec 512))[r.val] = true := by
        rw [← BitVec.getLsbD_eq_getElem]; simp only [BitVec.getLsbD_not]; simp [r.isLt]
      rcases ins with _|⟨u,_|⟨v,_|⟨z,zs⟩⟩⟩ <;>
        simp [value,arg,A,andEval,orEval,notEval,BitVec.getLsbD_and,BitVec.getLsbD_or,
          BitVec.getLsbD_not,r.isLt,oneB] at * <;> first | omega | exact fun _ => oneB
  have evalBit (gs : List Gate) (ok : ∀ g∈gs, good g) (w : List (BitVec 512)) (r : Fin 512) :
      (ev gs w).map (fun v => v.getLsbD r.val) = actual gs (w.map (fun v => v.getLsbD r.val)) := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change (ev gs (w++[value g w])).map _=actual gs ((w.map _)++[_])
      rw [ih (fun z hz => ok z (List.mem_cons_of_mem _ hz))]
      simp only [List.map_append,List.map_singleton,gateBit _ _ _ (ok _ List.mem_cons_self),read]
  have member (w : List (BitVec 512)) (n : ℕ) : w.getD n 0 ∈ (0 : BitVec 512)::(~~~0)::w := by
    rw [List.getD_eq_getElem?_getD]
    generalize h : w[n]? = opt
    cases opt with
    | none => exact List.mem_cons_self
    | some v =>
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_of_getElem? h))
  have sim (gs : List Gate) (w s : List (BitVec 512)) (hw : ∀ z∈(0 : BitVec 512)::(~~~0)::w,z∈s) :
      ∃ ts : List (Fin 3 × BitVec 512 × BitVec 512), ts.length ≤ gs.length ∧
        ∀ z∈(0 : BitVec 512)::(~~~0)::ev gs w, z∈ts.foldl step s := by
    induction gs generalizing w s with
    | nil => exact ⟨[],le_rfl,hw⟩
    | cons g gs ih =>
      let t : Fin 3 × BitVec 512 × BitVec 512 := (A g,arg g w 0,arg g w 1)
      have pin (l : ℕ) : arg g w l ∈ s := by
        apply hw
        dsimp only [arg]
        split
        · exact member w _
        · split <;> simp
      have keeps (z : BitVec 512) (hz : z∈s) : z∈step s t := by
        change z∈(if arg g w 0∈s ∧ arg g w 1∈s ∧ value g w∉s then value g w::s else s)
        split
        · exact List.mem_cons_of_mem _ hz
        · exact hz
      have put : value g w∈step s t := by
        change value g w ∈ (if arg g w 0∈s ∧ arg g w 1∈s ∧ value g w∉s then value g w::s else s)
        by_cases h : value g w∈s <;> simp [pin,h]
      have next (z : BitVec 512) (hz : z∈(0 : BitVec 512)::(~~~0)::(w++[value g w])) : z∈step s t := by
        simp only [List.mem_cons,List.mem_append,List.mem_singleton,List.not_mem_nil,or_false] at hz
        rcases hz with h|h|h|h
        · exact keeps _ (hw _ (List.mem_cons.mpr (Or.inl h)))
        · exact keeps _ (hw _ (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h)))))
        · exact keeps _ (hw _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)))
        · exact h ▸ put
      obtain ⟨ts,len,res⟩ := ih (w++[value g w]) (step s t) next
      exact ⟨t::ts,Nat.succ_le_succ len,res⟩

  let row (r : Fin 512) := BitVec.ofBoolListLE [(raw (e b 0).val).getLsbD r.val,(raw (e b 1).val).getLsbD r.val,(raw (e b 2).val).getLsbD r.val,(raw (e b 3).val).getLsbD r.val,(raw (e b 4).val).getLsbD r.val,(raw (e b 5).val).getLsbD r.val,(raw (e b 6).val).getLsbD r.val,(raw (e b 7).val).getLsbD r.val,(raw (e b 8).val).getLsbD r.val]
  have rowBit (r : Fin 512) (h : Fin 9) : (row r).getLsbD h.val=(raw (e b h).val).getLsbD r.val := by
    dsimp only [row]
    rw [BitVec.getLsbD_ofBoolListLE]
    fin_cases h <;> rfl
  let rowPins (r : Fin 512) := List.ofFn (fun a : Fin 9 => (row r).getLsbD a.val) ++ [!(row r).getLsbD 0]
  have seedBit (r : Fin 512) (a : Fin 11) : (mask a).getLsbD r.val=(rowPins r).getD a.val false := by
    have hn : (row r).getLsbD 0=(raw 0).getLsbD r.val := by
      change (row r).getLsbD (0 : Fin 9).val=_
      rw [rowBit]; cases b <;> rfl
    dsimp only [rowPins]
    simp only [rowBit,hn]
    fin_cases a <;> cases b <;> simp [mask,base,lift,e,List.ofFn_succ,List.getD_eq_getElem?_getD,
      BitVec.getLsbD_not,r.isLt]
  have bits (r : Fin 512) : xs.map (fun v => v.getLsbD r.val)=
      rowPins r ++ [(rowPins r).getD i.val false || (rowPins r).getD j.val false] := by
    have hn := rowBit r 0
    change (row r).getLsbD 0 = _ at hn
    have e0 : e b 0=0 := by cases b <;> rfl
    rw [e0] at hn
    simp only [xs,List.map_append,List.map_ofFn,List.map_cons,List.map_nil,BitVec.getLsbD_or,
      seedBit,BitVec.getLsbD_not,show decide (r.val<512)=true from decide_eq_true r.isLt,Bool.true_and]
    simp only [rowPins,rowBit,hn,List.append_assoc,List.singleton_append,Function.comp_def,Fin.val_zero]
  have targ (r : Fin 512) : target.getLsbD r.val=([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] : List (Fin 9 × Fin 9)).any (fun a : Fin 9 × Fin 9 =>
      (row r).getLsbD a.1.val && (row r).getLsbD a.2.val) := by
    simp only [target,List.foldl_cons,List.foldl_nil,BitVec.getLsbD_or,BitVec.getLsbD_and,
      List.any_cons,List.any_nil,rowBit]
    have hz : (0 : BitVec 512).getLsbD r.val=false := by simp
    rw [hz]
    have sym0 (v0 v1 v2 v3 v4 v5 v6 v7 v8 : Bool) : ((((((((((((false || (v0 && v1)) || (v1 && v2)) || (v2 && v3)) || (v3 && v4)) || (v4 && v0)) || (v0 && v5)) || (v1 && v6)) || (v2 && v7)) || (v3 && v8)) || (v5 && v7)) || (v6 && v8)) || (v8 && v5))=((v0 && v1) || ((v1 && v2) || ((v2 && v3) || ((v3 && v4) || ((v4 && v0) || ((v0 && v5) || ((v1 && v6) || ((v2 && v7) || ((v3 && v8) || ((v5 && v7) || ((v6 && v8) || ((v8 && v5) || false)))))))))))) := by decide +revert +kernel
    have sym1 (v0 v1 v2 v3 v4 v5 v6 v7 v8 : Bool) : ((((((((((((false || (v0 && v1)) || (v1 && v2)) || (v2 && v3)) || (v3 && v4)) || (v4 && v0)) || (v0 && v5)) || (v1 && v6)) || (v2 && v7)) || (v3 && v8)) || (v5 && v7)) || (v6 && v8)) || (v8 && v5))=((v0 && v5) || ((v5 && v8) || ((v8 && v3) || ((v3 && v4) || ((v4 && v0) || ((v0 && v1) || ((v5 && v7) || ((v8 && v6) || ((v3 && v2) || ((v1 && v6) || ((v7 && v2) || ((v2 && v1) || false)))))))))))) := by decide +revert +kernel
    cases b
    · exact sym0 ((raw 0).getLsbD r.val) ((raw 1).getLsbD r.val) ((raw 2).getLsbD r.val) ((raw 3).getLsbD r.val) ((raw 4).getLsbD r.val) ((raw 5).getLsbD r.val) ((raw 6).getLsbD r.val) ((raw 7).getLsbD r.val) ((raw 8).getLsbD r.val)
    · exact sym1 ((raw 0).getLsbD r.val) ((raw 1).getLsbD r.val) ((raw 2).getLsbD r.val) ((raw 3).getLsbD r.val) ((raw 4).getLsbD r.val) ((raw 5).getLsbD r.val) ((raw 6).getLsbD r.val) ((raw 7).getLsbD r.val) ((raw 8).getLsbD r.val)
  by_contra! noBad
  have out : (ev C.gates xs).getD C.output 0=target := by
    apply BitVec.eq_of_getLsbD_eq
    intro n hn
    let r : Fin 512 := ⟨n,hn⟩
    change ((ev C.gates xs).getD C.output 0).getLsbD r.val=target.getLsbD r.val
    rw [← read,evalBit C.gates fan,bits,targ]
    exact Classical.not_not.mp (noBad (row r))
  obtain ⟨ts,sz,h⟩ := sim C.gates xs seed seedOK
  have witness := h _ (member (ev C.gates xs) C.output)
  rw [out] at witness
  exact remaining k hk ts (sz.trans cap) witness
