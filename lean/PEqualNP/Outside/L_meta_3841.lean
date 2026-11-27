import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_3841

abbrev Pin := Fin 26
abbrev Op := Fin 3 × Pin × Pin
abbrev X (n : ℕ) := Fin n → Bool
abbrev F (n : ℕ) := X n → Bool

def target (x : X 9) : Bool :=
  ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any fun e =>
    x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))

def minor (x : X 8) := target (Fin.insertNth (4 : Fin 9) false x)

def opVal (k : Fin 3) (a b : Bool) :=
  if k.val = 0 then a && b else if k.val = 1 then a || b else !a

def rd (w : List Bool) (i : Pin) :=
  if i.val = 25 then true else w.getD i.val false

def step (w : List Bool) (g : Op) :=
  w ++ [opVal g.1 (rd w g.2.1) (rd w g.2.2)]

def seed (x : X 9) := List.ofFn x ++ [x 0 || x 4]

def start (a b : Pin) (x : X 9) := step (seed x) (1,a,b)

def Agrees (a b o : Pin) (gs : List Op) :=
  ∀ r < 512, let x : X 9 := fun i => r.testBit i.val
    (gs.foldl step (start a b x)).getD o.val false = target x

def Rep (a b : Pin) := a.val < 9 ∧ b.val < 9 ∧ (2305843017923426382 : ℕ).testBit (9*a.val+b.val) = true

theorem all_inputs {a b o : Pin} {gs : List Op} (h : Agrees a b o gs) (x : X 9) :
    (gs.foldl step (start a b x)).getD o.val false = target x := by
  let bits := BitVec.ofBoolListLE (List.ofFn x)
  have lt : bits.toNat < 512 := by simpa [bits] using bits.isLt
  have eq : (fun i : Fin 9 => bits.toNat.testBit i.val) = x := by
    funext i
    change (BitVec.ofBoolListLE (List.ofFn x)).getLsbD i.val = x i
    rw [BitVec.getLsbD_ofBoolListLE]
    fin_cases i <;> rfl
  simpa only [eq] using h bits.toNat lt

-- Constants are free references during compilation. A nonconstant final result must
-- be represented by an actual wire of the constructed circuit.
def cst {n : ℕ} (b : Bool) : F n := fun _ => b
def wires {n : ℕ} (gs : List Gate) (x : X n) := (⟨gs,0⟩ : Circuit).wires (List.ofFn x)
def good (gs : List Gate) := FanInTwo (⟨gs,0⟩ : Circuit)
def real {n : ℕ} (gs : List Gate) (f : F n) :=
  ∃ i < n+gs.length, ∀ x, (wires gs x).getD i false = f x
def haveF {n : ℕ} (gs : List Gate) (f : F n) := (∃ b, f = cst b) ∨ real gs f

theorem wlen {n} (gs : List Gate) (x : X n) : (wires gs x).length = n+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wires,Circuit.wires]
  | append_singleton gs g ih =>
    simp only [wires,Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil,List.length_append,List.length_singleton] at *
    omega

theorem possible {n} (gs : List Gate) (b : Bool) : @haveF n gs (cst b) := Or.inl ⟨b,rfl⟩

def Extend {n : ℕ} (gs : List Gate) (k : ℕ) (f : F n) :=
  ∃ hs : List Gate, good hs ∧ hs.length ≤ gs.length+k ∧
    (∀ t : F n, haveF gs t → haveF hs t) ∧ haveF hs f

theorem known {n} {gs : List Gate} {f : F n} (hg : good gs) (hf : haveF gs f) (k : ℕ) :
    Extend gs k f := ⟨gs,hg,by omega,fun _ h => h,hf⟩

theorem emit {n} (gs : List Gate) (hg : good gs) (g : Gate)
    (ok : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (f : F n) (eq : ∀ x, g.op.eval (g.inputs.map fun i => (wires gs x).getD i false) = f x) :
    Extend gs 1 f := by
  have snoc (x : X n) : wires (gs++[g]) x = wires gs x ++ [f x] := by
    simp only [wires,Circuit.wires,List.foldl_append,List.foldl_cons,List.foldl_nil] at *
    rw [eq]
  refine ⟨gs++[g],?_,by simp,?_,Or.inr ⟨n+gs.length,by simp,?_⟩⟩
  · intro g' hm
    change g' ∈ gs++[g] at hm
    rcases List.mem_append.mp hm with prev | last
    · exact hg g' prev
    · simp only [List.mem_singleton] at last
      subst g'
      exact ok
  · intro t ht
    rcases ht with con | ⟨i,lt,read⟩
    · exact Or.inl con
    · refine Or.inr ⟨i,by simp; omega,fun x => ?_⟩
      rw [snoc,List.getD_append _ _ _ _ (by rw [wlen]; exact lt),read]
  · intro x
    rw [snoc,←wlen gs x]
    simp [List.getD_eq_getElem?_getD]

def bin {n} (d : Bool) (a b : F n) : F n := fun x => if d then a x || b x else a x && b x
def negF {n} (a : F n) : F n := fun x => !a x

theorem bin_left {n} {gs : List Gate} {f : F n} (h : haveF gs f) (d v : Bool) :
    haveF gs (bin d (cst v) f) := by
  have eq : bin d (cst v) f = (if d = v then cst v else f) := by
    funext x
    cases d <;> cases v <;> simp [bin,cst]
  rw [eq]
  split
  · exact possible _ _
  · exact h

theorem bin_right {n} {gs : List Gate} {f : F n} (h : haveF gs f) (d v : Bool) :
    haveF gs (bin d f (cst v)) := by
  have eq : bin d f (cst v) = (if d = v then cst v else f) := by
    funext x
    cases d <;> cases v <;> simp [bin,cst]
  rw [eq]
  split
  · exact possible _ _
  · exact h

theorem build_bin {n} {gs : List Gate} {a b : F n} (hg : good gs) (ha : haveF gs a) (hb : haveF gs b) (d : Bool) :
    Extend gs 1 (bin d a b) := by
  rcases ha with ⟨v,rfl⟩ | ⟨i,_,hi⟩
  · exact known hg (bin_left hb d v) _
  rcases hb with ⟨v,rfl⟩ | ⟨j,_,hj⟩
  · exact known hg (bin_right (Or.inr ⟨i,by assumption,hi⟩) d v) _
  cases d
  · apply emit gs hg ⟨.and,[i,j]⟩ (by simp)
    intro x
    simp only [GateOp.eval,List.map_cons,List.map_nil,List.all_cons,List.all_nil,id_eq,Bool.and_true,hi,hj,bin]
    rfl
  · apply emit gs hg ⟨.or,[i,j]⟩ (by simp)
    intro x
    simp only [GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false,hi,hj,bin,ite_true]

theorem build_neg {n} {gs : List Gate} {a : F n} (hg : good gs) (ha : haveF gs a) :
    Extend gs 1 (negF a) := by
  rcases ha with ⟨v,rfl⟩ | ⟨i,_,hi⟩
  · exact known hg (possible _ (!v)) _
  · apply emit gs hg ⟨.not,[i]⟩ (by simp)
    intro x
    change (!(wires gs x).getD i false) = !(a x)
    rw [hi]

-- NOT reads only the first operand. Under the restriction, using vertex four
-- in an effective position makes the gate a constant or a copy.
def reads4 (g : Op) : Bool := g.2.1 == 4 || (g.1 != 2 && g.2.2 == 4)
def charge (cut : Bool) (g : Op) : Bool := !(cut && reads4 g)
def bank {n} (gs : List Gate) (w : X n → List Bool) :=
  ∀ i, haveF gs (fun x => (w x).getD i false)

theorem operand {n} {gs : List Gate} {w : X n → List Bool} (hw : bank gs w) (i : Pin) :
    haveF gs (fun x => rd (w x) i) := by
  by_cases eq : i.val = 25
  · simp only [rd,ite_eq_left eq]
    exact possible gs true
  · simpa only [rd,ite_eq_right eq] using hw i.val

theorem one {n} {gs : List Gate} (hg : good gs) {w : X n → List Bool} (hw : bank gs w)
    (cut : Bool) (z : cut = true → ∀ x, rd (w x) 4 = false) (g : Op) :
    Extend gs (if charge cut g then 1 else 0)
      (fun x => opVal g.1 (rd (w x) g.2.1) (rd (w x) g.2.2)) := by
  rcases g with ⟨k,a,b⟩
  have ha := operand hw a
  have hb := operand hw b
  by_cases paid : charge cut (k,a,b) = true
  · rw [ite_eq_left paid]
    fin_cases k
    · exact build_bin hg ha hb false
    · exact build_bin hg ha hb true
    · exact build_neg hg ha
  · have cheap : cut = true ∧ (a = 4 ∨ (k ≠ 2 ∧ b = 4)) := by
      simp [charge,reads4] at paid
      tauto
    have eq : (fun x => rd (w x) 4) = cst false := funext (z cheap.1)
    rw [ite_eq_right paid]
    apply known hg
    rcases cheap.2 with rfl | ⟨hn,rfl⟩
    · fin_cases k
      · exact (eq ▸ bin_left hb false false : _)
      · exact (eq ▸ bin_left hb true false : _)
      · change haveF gs (negF (fun x => rd (w x) 4))
        rw [eq]
        exact possible _ true
    · fin_cases k
      · change haveF gs (bin false (fun x => rd (w x) a) (fun x => rd (w x) 4))
        rw [eq]
        exact bin_right ha false false
      · change haveF gs (bin true (fun x => rd (w x) a) (fun x => rd (w x) 4))
        rw [eq]
        exact bin_right ha true false
      · exact (hn rfl).elim

theorem pack {n} (ops : List Op) (cut : Bool) (gs : List Gate) (hg : good gs)
    (w : X n → List Bool) (L : ℕ) (lgt : 4 < L) (len : ∀ x, (w x).length = L)
    (hw : bank gs w) (z : cut = true → ∀ x, rd (w x) 4 = false) :
    ∃ hs : List Gate, good hs ∧ hs.length ≤ gs.length + (ops.filter (charge cut)).length ∧
      bank hs (fun x => ops.foldl step (w x)) := by
  induction ops generalizing gs w L with
  | nil => exact ⟨gs,hg,by simp,hw⟩
  | cons g ops ih =>
    obtain ⟨fs,hf,bound,prev,fresh⟩ := one hg hw cut z g
    let next := fun x => step (w x) g
    have nlen (x) : (next x).length = L+1 := by simp [next,step,len]
    have keep (x) (i : ℕ) (hi : i < L) :
        (next x).getD i false = (w x).getD i false :=
      List.getD_append _ _ _ _ (by rwa [len])
    have bank' : bank fs next := by
      intro i
      by_cases lt : i < L
      · simpa only [funext (fun x => keep x i lt)] using prev _ (hw i)
      · by_cases eq : i = L
        · subst i
          have val (x) : (next x).getD L false = opVal g.1 (rd (w x) g.2.1) (rd (w x) g.2.2) := by
            rw [←len x]
            simp [next,step,List.getD_eq_getElem?_getD]
          simpa only [funext val] using fresh
        · have missing (x) : (next x).getD i false = false := List.getD_eq_default _ _ (by rw [nlen]; omega)
          rw [funext missing]
          exact possible _ false
    have z' : cut = true → ∀ x, rd (next x) 4 = false := by
      intro h x
      exact (keep x 4 lgt).trans (z h x)
    obtain ⟨hs,hg',len',hw'⟩ := ih fs hf next (L+1) (by omega) nlen bank' z'
    refine ⟨hs,hg',?_,hw'⟩
    cases paid : charge cut g <;> simp [paid] at bound ⊢ <;> omega

theorem finish {n} {gs : List Gate} (hg : good gs) (f : F n) (notConst : ∀ b, f ≠ cst b)
    (hf : haveF gs f) {budget : ℕ} (size : gs.length ≤ budget) : HasCircuitSize n f budget := by
  rcases hf with ⟨b,he⟩ | ⟨i,_,eq⟩
  · exact (notConst b he).elim
  · exact ⟨⟨gs,i⟩,hg,size,eq⟩

theorem get_input {n} (x : X n) (i : ℕ) (lt : i<n) :
    (List.ofFn x).getD i false = x ⟨i,lt⟩ := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left lt,Option.getD_some]

theorem raw {n} (i : Fin n) : haveF [] (fun x : X n => x i) :=
  Or.inr ⟨i.val,by simp,fun x => get_input x i.val i.isLt⟩

theorem ofFnBank {n m} {gs : List Gate} (x : X n → X m)
    (hw : ∀ i, haveF gs (fun y => x y i)) : bank gs (fun y => List.ofFn (x y)) := by
  intro i
  by_cases hi : i < m
  · simp only [get_input _ _ hi]
    exact hw ⟨i,hi⟩
  · have eq (y) : (List.ofFn (x y)).getD i false = false :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [funext eq]
    exact possible _ false

theorem appendBank {n} {gs : List Gate} {w : X n → List Bool} (hw : bank gs w)
    (L : ℕ) (len : ∀ y, (w y).length = L) (f : F n) (hf : haveF gs f) :
    bank gs (fun y => w y ++ [f y]) := by
  intro i
  by_cases lt : i<L
  · have eq (y) := List.getD_append (w y) [f y] false i (by rwa [len])
    rw [funext eq]
    exact hw _
  · by_cases eq : i=L
    · subst i
      have atEnd (y) : (w y ++ [f y]).getD L false = f y := by
        rw [←len y]
        simp [List.getD_eq_getElem?_getD]
      rw [funext atEnd]
      exact hf
    · have past (y) : (w y ++ [f y]).getD i false = false :=
        List.getD_eq_default _ _ (by simp [len]; omega)
      rw [funext past]
      exact possible _ false

def pinVar (i : Pin) (x : X 9) := if h : i.val < 9 then x ⟨i.val,h⟩ else false

theorem seedPin (i : Pin) (h9 : i.val ≠ 9) (h25 : i.val ≠ 25) (x : X 9) :
    rd (seed x) i = pinVar i x := by
  simp only [rd,ite_eq_right h25,pinVar,seed]
  split <;> rename_i h
  · rw [List.getD_append _ _ _ _ (by simpa using h),get_input _ _ h]
  · exact List.getD_eq_default _ _ (by simp; omega)

theorem target_nonconst : ∀ b, target ≠ cst b := by
  intro b eq
  cases b with
  | false => have e := congrFun eq (fun _ => true); exact Bool.noConfusion (show true=false from e)
  | true => have e := congrFun eq (fun _ => false); exact Bool.noConfusion (show false=true from e)

theorem minor_nonconst : ∀ b, minor ≠ cst b := by
  intro b eq
  cases b with
  | false => have e := congrFun eq (fun _ => true); exact Bool.noConfusion (show true=false from e)
  | true => have e := congrFun eq (fun _ => false); exact Bool.noConfusion (show false=true from e)

def Deg (a b : Pin) : Prop :=
  9 ≤ a.val ∨ 9 ≤ b.val ∨ a=b ∨ (a=0 ∧ b=4) ∨ (a=4 ∧ b=0)

theorem small9 {a b o : Pin} {tail : List Op} (bound : tail.length ≤ 13)
    (ha9 : a.val ≠ 9) (hb9 : b.val ≠ 9) (ha25 : a.val ≠ 25) (hb25 : b.val ≠ 25)
    (deg : Deg a b) (agree : Agrees a b o tail) : HasCircuitSize 9 target 14 := by
  have empty : good [] := by intro g hg; cases hg
  obtain ⟨gs,hg,len,lift,seedVal⟩ := build_bin empty (raw (0:Fin 9)) (raw (4:Fin 9)) true
  have ins : bank gs (fun x : X 9 => List.ofFn x) := ofFnBank _ (fun i => lift _ (raw i))
  have seedBank : bank gs seed := appendBank ins 9 (by simp) _ seedVal
  let A : F 9 := pinVar a
  let B : F 9 := pinVar b
  have avail (i : Pin) : haveF gs (pinVar i) := by
    by_cases hi : i.val < 9
    · have eq : pinVar i = fun x => x ⟨i.val,hi⟩ := by funext x; simp [pinVar,hi]
      rw [eq]
      exact lift _ (raw _)
    · have eq : pinVar i = cst false := by funext x; simp [pinVar,hi,cst]
      rw [eq]
      exact possible _ _
  have nextVal : haveF gs (bin true A B) := by
    rcases deg with past | past | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · have gone : A = cst false := by funext x; simp [A,pinVar,show ¬ a.val<9 by omega,cst]
      rw [gone]
      exact bin_left (avail b) true false
    · have gone : B = cst false := by funext x; simp [B,pinVar,show ¬ b.val<9 by omega,cst]
      rw [gone]
      exact bin_right (avail a) true false
    · have eq : bin true A B = A := by funext x; simp [A,B,bin]
      rw [eq]
      exact avail _
    · exact seedVal
    · have eq : bin true A B = bin true (fun x : X 9 => x 0) (fun x => x 4) := by
        funext x
        exact Bool.or_comm _ _
      rw [eq]
      exact seedVal
  have eb (x : X 9) : start a b x = seed x ++ [bin true A B x] := by
    change seed x ++ [rd (seed x) a || rd (seed x) b] = _
    rw [seedPin _ ha9 ha25,seedPin _ hb9 hb25]
    rfl
  have bank0 : bank gs (start a b) := by
    rw [funext eb]
    exact appendBank seedBank 10 (by simp [seed]) _ nextVal
  obtain ⟨hs,hm,size,hw⟩ := pack tail false gs hg _ 11 (by decide)
    (by intro x; simp [eb,seed]) bank0 (by intro h; cases h)
  have output := hw o.val
  rw [funext (all_inputs agree)] at output
  apply finish hm target target_nonconst output
  have cnt : (tail.filter (charge false)).length = tail.length := by simp [charge]
  simp only [List.length_nil] at len
  omega

theorem atSnoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w++[b]).getD i false = if i=w.length then b else w.getD i false := by
  by_cases eq : i=w.length
  · subst i
    simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right eq]
    by_cases lt : i<w.length
    · exact List.getD_append _ _ _ _ lt
    · rw [List.getD_eq_default (w++[b]) false (by simp; omega),
          List.getD_eq_default w false (by omega)]

theorem keepOld (tail : List Op) (w : List Bool) (i : ℕ) (lt : i<w.length) :
    (tail.foldl step w).getD i false = w.getD i false := by
  induction tail generalizing w with
  | nil => rfl
  | cons g tail ih =>
    change (tail.foldl step (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ lt

theorem noRead (tail : List Op) (none : ∀ g ∈ tail, reads4 g = false)
    (u v : List Bool) (len : u.length=v.length)
    (same : ∀ i : Pin, i ≠ 4 → u.getD i.val false = v.getD i.val false) :
    ∀ i : Pin, i ≠ 4 → (tail.foldl step u).getD i.val false = (tail.foldl step v).getD i.val false := by
  induction tail generalizing u v with
  | nil => exact same
  | cons g tail ih =>
    have rawEq (i : Pin) (ne : i ≠ 4) : rd u i = rd v i := by simp only [rd,same i ne]
    have unused := none g List.mem_cons_self
    rcases g with ⟨k,a,b⟩
    have val : opVal k (rd u a) (rd u b) = opVal k (rd v a) (rd v b) := by
      fin_cases k <;> simp [reads4] at unused
      · rw [rawEq a unused.1,rawEq b unused.2]
      · rw [rawEq a unused.1,rawEq b unused.2]
      · change (!rd u a) = !rd v a
        rw [rawEq a unused]
    apply ih (fun g hg => none g (List.mem_cons_of_mem _ hg)) _ _ (by simp [step,len])
    intro i ne
    simp only [step,atSnoc,len,val,same i ne]

def Exceptional (b : Pin) : Prop := b ∈ [2,3,6,7,8]
def maskInput (r : ℕ) : X 9 := fun i => r.testBit i.val

-- The two masks differ only at vertex four. Both seed ORs stay fixed,
-- but adding vertex four creates an edge with vertex zero.
set_option maxRecDepth 4096 in
theorem distinguish (b : Pin) (hb : Exceptional b) :
    let x := maskInput (1 + 2^b.val)
    let y := maskInput (17 + 2^b.val)
    target x ≠ target y ∧ ∀ i : Pin, i ≠ 4 →
      (start 4 b x).getD i.val false = (start 4 b y).getD i.val false := by
  simp only [Exceptional,List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem paidLess {b o : Pin} {tail : List Op} (hb : Exceptional b) (ok : Agrees 4 b o tail) :
    (tail.filter (charge true)).length < tail.length := by
  have out : o ≠ 4 := by
    rintro rfl
    have no := all_inputs ok (maskInput 3)
    rw [keepOld _ _ _ (by simp [start,step,seed])] at no
    have value : (start 4 b (maskInput 3)).getD 4 false = false :=
      (List.getD_append _ _ _ _ (show 4 < (seed (maskInput 3)).length by simp [seed])).trans rfl
    change (start 4 b (maskInput 3)).getD 4 false = _ at no
    rw [value] at no
    exact Bool.noConfusion (show false=true from no)
  apply Nat.lt_of_le_of_ne (List.length_filter_le ..)
  intro eq
  have every := List.length_filter_eq_length_iff.mp eq
  have none : ∀ g ∈ tail, reads4 g = false := by
    intro g hg
    simpa [charge] using every g hg
  obtain ⟨diff,same⟩ := distinguish b hb
  have outEq := noRead tail none _ _ (by simp [start,step,seed]) same o out
  rw [all_inputs ok,all_inputs ok] at outEq
  exact diff outEq

def ins4 (x : X 8) : X 9 := Fin.insertNth 4 false x

theorem projection (i : Fin 9) : haveF [] (fun x : X 8 => ins4 x i) := by
  refine Fin.succAboveCases (4:Fin 9) ?_ (fun j => ?_) i
  · have eq : (fun x : X 8 => ins4 x 4) = cst false :=
      funext (fun x => Fin.insertNth_apply_same ..)
    rw [eq]
    exact possible _ _
  · have eq : (fun x : X 8 => ins4 x ((4:Fin 9).succAbove j)) = fun x => x j :=
      funext (fun x => Fin.insertNth_apply_succAbove ..)
    rw [eq]
    exact raw _

theorem small8 {b o : Pin} {tail : List Op} (bound : tail.length ≤ 13)
    (hb : Exceptional b) (ok : Agrees 4 b o tail) : HasCircuitSize 8 minor 12 := by
  have bv : b.val < 9 := by
    simp only [Exceptional,List.mem_cons,List.not_mem_nil,or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> decide
  have bit (x : X 8) : ins4 x 4 = false := Fin.insertNth_apply_same ..
  have seedEq (x : X 8) : seed (ins4 x) = List.ofFn (ins4 x) ++ [ins4 x 0] := by
    simp [seed,bit]
  have seedBank : bank [] (fun x => seed (ins4 x)) := by
    simp only [seedEq]
    exact appendBank (ofFnBank ins4 projection) 9 (by simp) _ (projection 0)
  have startEq (x : X 8) : start 4 b (ins4 x) = seed (ins4 x) ++ [ins4 x ⟨b.val,bv⟩] := by
    change seed (ins4 x) ++ [rd (seed (ins4 x)) 4 || rd (seed (ins4 x)) b] = _
    rw [seedPin 4 (by decide) (by decide),seedPin b (by omega) (by omega)]
    simp [pinVar,bv,bit]
  have bank0 : bank [] (fun x => start 4 b (ins4 x)) := by
    simp only [startEq]
    exact appendBank seedBank 10 (by simp [seed]) _ (projection _)
  have zero4 (x : X 8) : rd (start 4 b (ins4 x)) 4 = false := by
    change (start 4 b (ins4 x)).getD 4 false = false
    rw [startEq,List.getD_append _ _ _ _ (by simp [seed]),seedEq,List.getD_append _ _ _ _ (by simp)]
    exact (get_input _ 4 (by decide)).trans (bit x)
  obtain ⟨hs,hm,size,hw⟩ := pack tail true [] (by intro g hg; cases hg) _ 11 (by decide)
    (by intro x; simp [startEq,seed]) bank0 (fun _ => zero4)
  have output := hw o.val
  have eq : (fun x => (tail.foldl step (start 4 b (ins4 x))).getD o.val false) = minor :=
    funext (fun x => all_inputs ok (ins4 x))
  rw [eq] at output
  have strict := paidLess hb ok
  exact finish hm minor minor_nonconst output (by simp only [List.length_nil] at size; omega)

-- This involution fixes the initial OR and preserves the graph edge function.
def mirror (i : Pin) : Pin := match i.val with
  | 1 => 5
  | 2 => 8
  | 5 => 1
  | 6 => 7
  | 7 => 6
  | 8 => 2
  | _ => i

def mirror9 (i : Fin 9) : Fin 9 := Fin.ofNat 9 (mirror (Fin.ofNat 26 i.val)).val
def mirrorOp (g : Op) : Op := (g.1,mirror g.2.1,mirror g.2.2)

theorem targetMirror (x : X 9) : target (fun i => x (mirror9 i)) = target x := by
  change ((x 0 && x 5) || ((x 5 && x 8) || ((x 8 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 1) || ((x 5 && x 7) || ((x 8 && x 6) || ((x 3 && x 2) || ((x 1 && x 6) || ((x 7 && x 2) || ((x 2 && x 1) || false)))))))))))) = ((x 0 && x 1) || ((x 1 && x 2) || ((x 2 && x 3) || ((x 3 && x 4) || ((x 4 && x 0) || ((x 0 && x 5) || ((x 1 && x 6) || ((x 2 && x 7) || ((x 3 && x 8) || ((x 5 && x 7) || ((x 6 && x 8) || ((x 8 && x 5) || false))))))))))))
  ac_rfl

theorem initialMirror (x : X 9) (i : Pin) :
    (seed (fun j => x (mirror9 j))).getD i.val false = (seed x).getD (mirror i).val false := by
  fin_cases i <;> rfl

theorem mirrorEval (tail : List Op) (u v : List Bool) (len : u.length=v.length)
    (big : 9 ≤ u.length) (old : ∀ i : Pin, u.getD i.val false = v.getD (mirror i).val false) :
    ∀ i : Pin, (tail.foldl step u).getD i.val false =
      ((tail.map mirrorOp).foldl step v).getD (mirror i).val false := by
  induction tail generalizing u v with
  | nil => exact old
  | cons g tail ih =>
    have mask : ∀ i : Pin, (mirror i).val = 25 ↔ i.val = 25 := by decide
    have readEq (i : Pin) : rd u i = rd v (mirror i) := by simp only [rd,mask i,old i]
    have small : ∀ i : Pin, i.val < 9 → (mirror i).val < 9 := by decide
    have fixed : ∀ i : Pin, 9 ≤ i.val → mirror i = i := by decide
    apply ih _ _ (by simp [step,len]) (by simp [step]; omega)
    intro i
    have index : (mirror i).val = v.length ↔ i.val = u.length := by
      by_cases h : i.val < 9
      · have := small i h
        omega
      · rw [fixed i (by omega),len]
    simp only [step,atSnoc,mirrorOp,readEq,old,index]

theorem reflected {a b o : Pin} {tail : List Op} (ok : Agrees a b o tail) :
    Agrees (mirror a) (mirror b) (mirror o) (tail.map mirrorOp) := by
  intro r _
  let x : X 9 := maskInput r
  let y : X 9 := fun i => x (mirror9 i)
  have eq := mirrorEval ((1,a,b)::tail) (seed y) (seed x) (by simp [seed]) (by simp [seed]) (initialMirror x) o
  exact eq.symm.trans ((all_inputs ok y).trans (targetMirror x))

theorem swapped {a b o : Pin} {tail : List Op} (ok : Agrees a b o tail) : Agrees b a o tail := by
  intro r hr
  have eq (x : X 9) : start b a x = start a b x := by
    change seed x ++ [rd (seed x) b || rd (seed x) a] = seed x ++ [rd (seed x) a || rd (seed x) b]
    rw [Bool.or_comm]
  simpa only [eq] using ok r hr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem classes : ∀ a b : Pin, Deg a b ∨ (a=4 ∧ Exceptional b) ∨ (b=4 ∧ Exceptional a) ∨
    Rep a b ∨ Rep b a ∨ Rep (mirror a) (mirror b) ∨ Rep (mirror b) (mirror a) := by
  unfold Deg Exceptional Rep
  decide +kernel

theorem normalize (a b o : Pin) (tail : List Op) (bound : tail.length ≤ 13)
    (a9 : a.val ≠ 9) (b9 : b.val ≠ 9) (a25 : a.val ≠ 25) (b25 : b.val ≠ 25)
    (ok : Agrees a b o tail) : HasCircuitSize 9 target 14 ∨ HasCircuitSize 8 minor 12 ∨
      ∃ i j k t, t.length ≤ 13 ∧ Rep i j ∧ Agrees i j k t := by
  rcases classes a b with d | ⟨rfl,exc⟩ | ⟨rfl,exc⟩ | direct | swap | reflA | reflB
  · exact Or.inl (small9 bound a9 b9 a25 b25 d ok)
  · exact Or.inr (Or.inl (small8 bound exc ok))
  · exact Or.inr (Or.inl (small8 bound exc (swapped ok)))
  · exact Or.inr (Or.inr ⟨a,b,o,tail,bound,direct,ok⟩)
  · exact Or.inr (Or.inr ⟨b,a,o,tail,bound,swap,swapped ok⟩)
  · exact Or.inr (Or.inr ⟨_,_,_,_,by simpa using bound,reflA,reflected ok⟩)
  · exact Or.inr (Or.inr ⟨_,_,_,_,by simpa using bound,reflB,swapped (reflected ok)⟩)

end PEqualNP.Outside.L_meta_3841

theorem PEqualNP.Outside.L_meta_3841 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (8 : ℕ) → Bool) → Bool := fun (x2 : Fin (8 : ℕ) → Bool) => x1 (Fin.insertNth (4 : Fin ((8 : ℕ) + (1 : ℕ))) Bool.false x2); have x3 : Fin (26 : ℕ) → Fin (26 : ℕ) → Fin (26 : ℕ) → List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) → Prop := fun (x3 x4 x5 : Fin (26 : ℕ)) (x6 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))) =>   ∀ x7 < (512 : ℕ),     have x9 : Fin (9 : ℕ) → Bool := fun (x9 : Fin (9 : ℕ)) => x7.testBit ↑x9;     have x10 : List Bool → Fin (26 : ℕ) → Bool := fun (x10 : List Bool) (x11 : Fin (26 : ℕ)) => if ↑x11 = (25 : ℕ) then Bool.true else x10.getD (↑x11) Bool.false;     have x11 : List Bool := List.foldl (fun (x11 : List Bool) (x12 : Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ)) => x11 ++ [if ↑x12.1 = (0 : ℕ) then x10 x11 x12.2.1 && x10 x11 x12.2.2 else if ↑x12.1 = (1 : ℕ) then x10 x11 x12.2.1 || x10 x11 x12.2.2 else !x10 x11 x12.2.1]) (List.ofFn x9 ++ [x9 (0 : Fin (9 : ℕ)) || x9 (4 : Fin (9 : ℕ))]) (((1 : Fin (3 : ℕ)), x3, x4) :: x6);     x11.getD (↑x5) Bool.false = x1 x9; have x4 : Fin (26 : ℕ) → Fin (26 : ℕ) → Prop := fun (x4 x5 : Fin (26 : ℕ)) => ↑x4 < (9 : ℕ) ∧ ↑x5 < (9 : ℕ) ∧ Nat.testBit (2305843017923426382 : ℕ) ((9 : ℕ) * ↑x4 + ↑x5) = Bool.true; ∀ (x5 x6 x7 : Fin (26 : ℕ)) (x8 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))), x8.length ≤ (13 : ℕ) → ↑x5 ≠ (9 : ℕ) → ↑x6 ≠ (9 : ℕ) → ↑x5 ≠ (25 : ℕ) → ↑x6 ≠ (25 : ℕ) → x3 x5 x6 x7 x8 → PEqualNP.MetaComplexity.HasCircuitSize (9 : ℕ) x1 (14 : ℕ) ∨ PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) x2 (12 : ℕ) ∨ ∃ (x15 : Fin (26 : ℕ)) (x16 : Fin (26 : ℕ)) (x17 : Fin (26 : ℕ)) (x18 : List (Fin (3 : ℕ) × Fin (26 : ℕ) × Fin (26 : ℕ))), x18.length ≤ (13 : ℕ) ∧ x4 x15 x16 ∧ x3 x15 x16 x17 x18 :=
  PEqualNP.Outside.L_meta_3841.normalize
