import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_4401

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def edge (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
def port (m : Nat) (x : Fin 9 → Bool) := (List.finRange 9).any fun v=>m.testBit v.val && x v
def first (x : Fin 9 → Bool) := List.ofFn x ++ [x 4 || x 6]
def dest (m : Nat) (x : Fin 9 → Bool) := first x ++ [port m x]
def reps : List Nat := [3,5,9,17,33,65,129,257,20,36,132,144,81,84,208]
def symmetry (p : Fin 4) (i : Fin 9) : Fin 9 := (([[0,1,2,3,4,5,6,7,8],[1,0,5,8,6,2,4,7,3],[3,8,5,0,4,2,6,7,1],[8,3,2,1,6,5,4,7,0]] : List (List (Fin 9))).getD p.val []).getD i.val 0
def moved (p : Fin 4) (x : Fin 9 → Bool) := fun i=>x (symmetry p i)
def oldMask (p : Fin 4) (t : Fin 11) :=
  if h : t.val<9 then 1 <<< (symmetry p ⟨t.val,h⟩).val else if t.val=9 then 80 else 0
def newMask (m : Nat) (t : Fin 12) := if t.val<9 then 1 <<< t.val else if t.val=9 then 80 else if t.val=10 then m else 0
abbrev rep (b : Fin 15) := reps.getD b.val 3
def choice (i j : Fin 11) : Fin 4 × Fin 15 × Fin 12 :=
  ([(0,0,0),(0,0,10),(0,1,10),(0,2,10),(0,3,10),(0,4,10),(0,5,10),(0,6,10),(0,7,10),(0,12,10),(0,0,0),(0,0,10),(0,0,1),(1,4,10),(1,7,10),(1,5,10),(1,1,10),(1,3,10),(1,6,10),(1,2,10),(1,12,10),(0,0,1),(0,1,10),(1,4,10),(0,0,2),(2,4,10),(0,8,10),(0,9,10),(3,8,10),(0,10,10),(3,1,10),(0,13,10),(0,0,2),(0,2,10),(1,7,10),(2,4,10),(0,0,3),(2,3,10),(2,1,10),(2,5,10),(2,6,10),(2,0,10),(2,12,10),(0,0,3),(0,3,10),(1,5,10),(0,8,10),(2,3,10),(0,0,4),(2,8,10),(0,0,9),(0,11,10),(3,5,10),(0,0,9),(0,0,4),(0,4,10),(1,1,10),(0,9,10),(2,1,10),(2,8,10),(0,0,5),(1,8,10),(1,10,10),(3,4,10),(1,13,10),(0,0,5),(0,5,10),(1,3,10),(3,8,10),(2,5,10),(0,0,9),(1,8,10),(0,0,6),(1,11,10),(3,3,10),(0,0,9),(0,0,6),(0,6,10),(1,6,10),(0,10,10),(2,6,10),(0,11,10),(1,10,10),(1,11,10),(0,0,7),(3,6,10),(0,14,10),(0,0,7),(0,7,10),(1,2,10),(3,1,10),(2,0,10),(3,5,10),(3,4,10),(3,3,10),(3,6,10),(0,0,8),(3,12,10),(0,0,8),(0,12,10),(1,12,10),(0,13,10),(2,12,10),(0,0,9),(1,13,10),(0,0,9),(0,14,10),(3,12,10),(0,0,9),(0,0,9),(0,0,0),(0,0,1),(0,0,2),(0,0,3),(0,0,4),(0,0,5),(0,0,6),(0,0,7),(0,0,8),(0,0,9),(0,0,11)] : List (Fin 4 × Fin 15 × Fin 12)).getD (11*i.val+j.val) (0,0,0)
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma coverage : ∀ i j : Fin 11, let (p,b,k):=choice i j
    rep b ∈ reps ∧ oldMask p i ||| oldMask p j=newMask (rep b) k := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma graphSym : ∀ (p : Fin 4) (x : Fin 9 → Bool), edge (moved p x)=edge x := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma keepFirst : ∀ (p : Fin 4) (x : Fin 9 → Bool), (moved p x 4 || moved p x 6) = (x 4 || x 6) := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma oldRead : ∀ (p : Fin 4) (t : Fin 11) (x : Fin 9 → Bool),
    (first (moved p x)).getD t.val false=port (oldMask p t) x := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma singles : ∀ (i : Fin 9) (x : Fin 9 → Bool), port (1 <<< i.val) x=x i := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma eighty : ∀ x : Fin 9 → Bool, port 80 x=(x 4 || x 6) := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma empty : ∀ x : Fin 9 → Bool, port 0 x=false := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma newRead (m : Nat) (t : Fin 12) (x : Fin 9 → Bool) :
    (dest m x).getD t.val false=port (newMask m t) x := by
  by_cases h : t.val<9
  · let i : Fin 9:=⟨t.val,h⟩
    rw [show newMask m t=1<<<i.val from by simp [newMask,h,i],singles]
    change ((List.ofFn x ++ [_])++[_]).getD t.val false=x i
    rw [List.getD_append _ _ _ _ (by simp;omega),List.getD_append _ _ _ _ (by simpa using h),
      List.getD_eq_getElem _ _ (by simpa using h),List.getElem_ofFn]
  · have cases' : t=9 ∨ t=10 ∨ t=11 := by have:=t.isLt;omega
    rcases cases' with rfl|rfl|rfl
    · exact (eighty x).symm
    · rfl
    · exact (empty x).symm
set_option maxHeartbeats 0 in
set_option maxRecDepth 24000 in
lemma port_or (a b : Nat) (x : Fin 9 → Bool) : port (a|||b) x = (port a x || port b x) := by
  unfold port
  generalize List.finRange 9 = l
  induction l with
  | nil => rfl
  | cons v tail ih =>
    simp only [List.any_cons]
    rw [ih,Nat.testBit_or]
    cases a.testBit v.val <;> cases b.testBit v.val <;> cases x v <;> simp

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def run (gs : List Gate) (w : List Bool) := gs.foldl (fun a g=>a++[g.op.eval (g.inputs.map fun i=>a.getD i false)]) w
lemma preservePin (gs : List Gate) (w : List Bool) (i : Nat) (hi : i<w.length) :
    (run gs w).getD i false=w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w++[_])).getD i false=_
    rw [ih _ (by simp;omega),List.getD_append _ _ _ _ hi]
def label (r : Fin 11 → Fin 12) (i : Nat) : Nat :=
  if h:i<11 then (if (r ⟨i,h⟩).val<11 then (r ⟨i,h⟩).val else 64) else i
def replace (f : Nat→Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map f⟩
lemma snoc (w : List Bool) (v : Bool) (i : Nat) (h : i≠w.length) :
    (w++[v]).getD i false=w.getD i false := by
  by_cases hi:i<w.length
  · exact List.getD_append _ _ _ _ hi
  · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by omega)]
lemma snocAt (w : List Bool) (v : Bool) : (w++[v]).getD w.length false = v := by simp
lemma renameRun (r : Fin 11→Fin 12) (gs : List Gate) (old new : List Bool)
    (sizes : old.length=new.length) (init : 11≤old.length) (maxSize : old.length+gs.length<64)
    (al : ∀ i,old.getD i false=new.getD (label r i) false) :
    ∀ i,(run gs old).getD i false=(run (gs.map (replace (label r))) new).getD (label r i) false := by
  induction gs generalizing old new with
  | nil => exact al
  | cons g tail ih =>
    let v:=g.op.eval (g.inputs.map fun i=>old.getD i false)
    have same : (replace (label r) g).op.eval ((replace (label r) g).inputs.map fun i=>new.getD i false)=v := by
      simp only [replace,v,List.map_map,Function.comp_def,al]
    change ∀ i, (run tail (old++[v])).getD i false =
      (run (tail.map (replace (label r))) (new++[_])).getD (label r i) false
    rw [same]
    apply ih _ _ (by simp [sizes]) (by simp;omega) (by simp at maxSize ⊢;omega)
    intro i
    by_cases h : i=old.length
    · subst i
      have lab : label r old.length=new.length := by
        simp only [label,dif_neg (show ¬old.length<11 by omega)]
        exact sizes
      rw [lab,snocAt,snocAt]
    · have hn : label r i≠new.length := by
        unfold label
        split_ifs <;> simp at maxSize <;> omega
      rw [snoc _ _ _ h,snoc _ _ _ hn,al]
lemma labeled_fan (gs : List Gate) (out : Nat) (f : Nat→Nat)
    (ok : ∀ g∈gs,g.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp) ∧ g.inputs.length≤2) :
    FanInTwo (⟨gs.map (replace f),out⟩:Circuit) := by
  intro g hg
  obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hg
  simpa [replace] using ok w hw

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def tag (i : Nat) : Fin 11 := ⟨min i 10,by omega⟩
lemma capRead (w : List Bool) (len:w.length=10) (i : Nat) : w.getD (tag i).val false=w.getD i false := by
  by_cases h:i≤10
  · simp [tag,Nat.min_eq_left h]
  · have big : 10 ≤ i := by omega
    rw [List.getD_eq_default _ _ (by simp [tag,len,Nat.min_eq_right big]),
      List.getD_eq_default _ _ (by omega)]
lemma pairEval (g : Gate) (op:g.op=.or) (sz:g.inputs.length≤2) (w : List Bool) (len:w.length=10) :
    g.op.eval (g.inputs.map fun i=>w.getD i false) =
      (w.getD (tag (g.inputs.getD 0 10)).val false || w.getD (tag (g.inputs.getD 1 10)).val false) := by
  rw [capRead w len,capRead w len,op]
  have emptyPin : w.getD 10 false=false := List.getD_eq_default _ _ (by omega)
  cases h:g.inputs with
  | nil => simpa [GateOp.eval,emptyPin] using emptyPin.symm
  | cons a rest =>
    cases rest with
    | nil =>
      change (w.getD a false || false) = (w.getD a false || w.getD 10 false)
      rw [emptyPin]
    | cons b rest =>
      cases rest with
      | nil => simp [GateOp.eval,List.getD_eq_getElem?_getD]
      | cons c tail => simp [h] at sz
def initial (a b : Fin 11) (y : Fin 9→Bool) := first y ++ [(first y).getD a.val false || (first y).getD b.val false]
def route (p : Fin 4) (k : Fin 12) (u : Fin 11) : Fin 12 :=
  if h:u.val<9 then ⟨(symmetry p ⟨u.val,h⟩).val,by omega⟩ else if u.val=9 then 9 else k
lemma rawGet (x : Fin 9→Bool) (extra : List Bool) (i : Fin 9) :
    (List.ofFn x++extra).getD i.val false=x i := by
  rw [List.getD_append _ _ _ _ (by simpa using i.isLt),
    List.getD_eq_getElem _ _ (by simpa using i.isLt),List.getElem_ofFn]
lemma initAlign (a b : Fin 11) (p : Fin 4) (k : Fin 12) (m : Nat)
    (eqMask: oldMask p a ||| oldMask p b = newMask m k) (x : Fin 9→Bool) :
    ∀ i,(initial a b (moved p x)).getD i false=(dest m x).getD (label (route p k) i) false := by
  intro i
  by_cases h:i<11
  · let u : Fin 11 := ⟨i,h⟩
    have selected : (dest m x).getD (label (route p k) i) false=(dest m x).getD (route p k u).val false := by
      by_cases hit:(route p k u).val<11
      · have step : label (route p k) i=(route p k u).val := by
          unfold label
          rw [dif_pos h]
          exact if_pos hit
        rw [step]
      · have z : (route p k u).val=11 := by have:=(route p k u).isLt;omega
        have z' : (route p k ⟨i,h⟩).val=11 := z
        rw [z]
        simp [label,h,z',dest,first]
    rw [selected]
    by_cases low:i<9
    · let j : Fin 9:=⟨i,low⟩
      have rk : (route p k u).val=(symmetry p j).val := by simp [route,u,low,j]
      rw [rk]
      simp only [initial,first,dest,List.append_assoc]
      exact (rawGet (moved p x) _ j).trans (rawGet x _ (symmetry p j)).symm
    have possibilities:i=9 ∨ i=10:=by omega
    rcases possibilities with rfl|rfl
    · change (moved p x 4 || moved p x 6)=(x 4 || x 6)
      exact keepFirst p x
    · change ((first (moved p x)).getD a.val false || (first (moved p x)).getD b.val false)=(dest m x).getD k.val false
      rw [oldRead,oldRead,←port_or,eqMask,newRead]
  · rw [List.getD_eq_default _ _ (by simp [initial,first];omega),
      List.getD_eq_default _ _ (by simp [label,h,dest,first];omega)]

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def appendGate (g : Gate) (w : List Bool) := w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]
lemma headEq (g : Gate) (tail : List Gate) (x : Fin 9→Bool)
    (h : (run (g::tail) (List.ofFn x)).getD 9 false = (x 4||x 6)) :
      appendGate g (List.ofFn x)=first x := by
  let w:=List.ofFn x
  let v:=g.op.eval (g.inputs.map fun i=>w.getD i false)
  change (run tail (w++[v])).getD 9 false=_ at h
  rw [preservePin _ _ _ (by simp [w])] at h
  have snap : (w++[v]).getD 9 false=v := by
    simpa only [w,List.length_ofFn] using snocAt w v
  rw [snap] at h
  change w++[v]=w++[x 4 || x 6]
  rw [h]
lemma firstTwo (head g : Gate) (gs : List Gate) (out : Nat) (fan : FanInTwo (⟨head::g::gs,out⟩:Circuit))
    (firstOk : ∀ x : Fin 9→Bool, (run (head::g::gs) (List.ofFn x)).getD 9 false=(x 4||x 6))
    (correct : ∀ x : Fin 9→Bool, (⟨head::g::gs,out⟩:Circuit).eval (List.ofFn x)=edge x) (op:g.op=.or) :
    ∀ y : Fin 9→Bool, (run gs (initial (tag (g.inputs.getD 0 10)) (tag (g.inputs.getD 1 10)) y)).getD out false=edge y := by
  intro y
  have result:=correct y
  change (run gs (appendGate g (appendGate head (List.ofFn y)))).getD out false=_ at result
  rw [headEq head (g::gs) y (firstOk y)] at result
  have pair:=pairEval g op (fan g (by simp)).2 (first y) (by simp [first])
  simpa only [appendGate,pair,initial] using result
lemma witness (head g : Gate) (gs : List Gate) (out : Nat)
    (fan : FanInTwo (⟨head::g::gs,out⟩:Circuit)) (budget : gs.length≤13)
    (firstOk : ∀ x : Fin 9→Bool, (run (head::g::gs) (List.ofFn x)).getD 9 false=(x 4||x 6))
    (correct : ∀ x : Fin 9→Bool, (⟨head::g::gs,out⟩:Circuit).eval (List.ofFn x)=edge x) (op:g.op=.or) :
    ∃ m ∈ reps, ∃ D : Circuit, FanInTwo D ∧ D.size≤13 ∧ ∀ x, D.eval (dest m x)=edge x := by
  let a:=tag (g.inputs.getD 0 10)
  let b:=tag (g.inputs.getD 1 10)
  rcases hc : choice a b with ⟨p,c,k⟩
  have fromTable:=coverage a b
  rw [hc] at fromTable
  obtain ⟨listed,mask⟩:=fromTable
  let transform:=label (route p k)
  let D : Circuit:=⟨gs.map (replace transform),transform out⟩
  refine ⟨rep c,listed,D,labeled_fan gs (transform out) transform (fun v hv=>fan v (by simp [hv])),?_,?_⟩
  · simpa only [D,Circuit.size,List.length_map] using budget
  intro x
  let y:=moved p x
  have sim:=renameRun (route p k) gs (initial a b y) (dest (rep c) x)
    (by simp [initial,first,dest]) (by simp [initial,first]) (by simp [initial,first];omega)
    (initAlign a b p k (rep c) mask x) out
  have good:=firstTwo head g gs out fan firstOk correct op y
  exact sim.symm.trans (good.trans (graphSym p x))

end PEqualNP.Outside.L_meta_4401

open PEqualNP.Outside.L_meta_4401
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.L_meta_4401 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : ℕ → (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : ℕ) (x3 : Fin (9 : ℕ) → Bool) => List.ofFn x3 ++ [x3 (4 : Fin (9 : ℕ)) || x3 (6 : Fin (9 : ℕ)), (List.finRange (9 : ℕ)).any fun (x4 : Fin (9 : ℕ)) => x2.testBit ↑x4 && x3 x4]; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : PEqualNP.CircuitLowerBounds.Gate), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size ≤ (15 : ℕ) → (∀ (x7 : Fin (9 : ℕ) → Bool), (x3.wires (List.ofFn x7)).getD (9 : ℕ) Bool.false = (x7 (4 : Fin (9 : ℕ)) || x7 (6 : Fin (9 : ℕ)))) → PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 → x3.gates[(1 : ℕ)]? = Option.some x4 → x4.op = PEqualNP.CircuitLowerBounds.GateOp.or → ∃ x11 ∈ [(3 : ℕ), (5 : ℕ), (9 : ℕ), (17 : ℕ), (33 : ℕ), (65 : ℕ), (129 : ℕ), (257 : ℕ), (20 : ℕ), (36 : ℕ), (132 : ℕ), (144 : ℕ), (81 : ℕ), (84 : ℕ), (208 : ℕ)], ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x12 ∧ x12.size ≤ (13 : ℕ) ∧ ∀ (x13 : Fin (9 : ℕ) → Bool), x12.eval (x2 x11 x13) = x1 x13 := by
  dsimp only
  intro C gate fan size firstOk correct atSecond op
  obtain ⟨gs,out⟩:=C
  cases gs with
  | nil => simp at atSecond
  | cons h tail =>
    cases tail with
    | nil => simp at atSecond
    | cons g gs =>
      change some g=some gate at atSecond
      obtain rfl:=Option.some.inj atSecond
      have small:gs.length≤13:=by
        change (h::g::gs).length≤15 at size
        simp only [List.length_cons] at size
        omega
      have eq : ∀x : Fin 9→Bool,(⟨h::g::gs,out⟩:Circuit).eval (List.ofFn x)=edge x :=
        fun x=>congrFun correct x
      exact witness h g gs out fan small firstOk eq op
