import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.G514

abbrev B := BitVec 228
abbrev Sig := B × B
def top : B := BitVec.allOnes 228
def zero : Sig := (0,0)
def one : Sig := (top,top)
def target : Sig := (top,0)
def neg (a : Sig) : Sig := (~~~a.1,~~~a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1,a.2 ||| b.2) else (a.1 &&& b.1,a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : B :=
  if d then a.1 ^^^ a.2 else a.1 &&& ~~~a.2
def unionSep (d : Bool) : List Sig → B
  | [] => 0
  | a::l => sep d a ||| unionSep d l

def dropped (del v : List Sig) : List Sig := v.filter (fun x => !(del.contains x))

abbrev Cov := B × B × B

def addCov (z : B) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Sig) : Cov :=
  v.foldr (fun a c => addCov (sep d a) c) (0,0,0)

def takeOne (c : Cov) (a : B) : B := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : B) : B :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : B) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : B) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : B) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Sig} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (sep d a)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2

private theorem cov_union (d : Bool) (v : List Sig) : (coverage d v).1=unionSep d v := by
  induction v with
  | nil => rfl
  | cons a v ih => change sep d a ||| (coverage d v).1 = (sep d a ||| unionSep d v); rw [ih]

def tryGate (k t : Nat) (r : List Sig → Bool) (v rest : List Sig) (n : Nat) (c : B) (g : Sig)
    (keep : List (List Sig)) : Bool :=
  let d := decide (0<t)
  let base := sep d g ||| c
  if n=k-t then
    base == top && !(v.contains g) && g != zero && g != one && r (g::rest)
  else keep.any (fun h => decide (n+h.length+1 ≤ k-t+1) &&
    (base ||| unionSep d h == top) && !(v.contains g) && g != zero && g != one && r (g::(h++rest)))

def before (a b : Sig) : Bool :=
  if a.1 = b.1 then decide (a.2.toNat < b.2.toNat) else decide (a.1.toNat < b.1.toNat)


def unaryAt (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a : Sig) : Bool :=
  tryGate k t r v (dropped [a] v) (v.length-1) (takeOne c (sep (decide (0<t)) a)) (neg a) [[],[a]]

def unaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  v.any (unaryAt k t r v (coverage (decide (0<t)) v))

def binarySlow (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a b : Sig) : Bool :=
  before a b &&
    (let rest := dropped [a,b] v
     let keep := [[],[a],[b],[a,b]]
     let mask := takeTwo c (sep (decide (0<t)) a) (sep (decide (0<t)) b)
     tryGate k t r v rest (v.length-2) mask (bin false a b) keep || tryGate k t r v rest (v.length-2) mask (bin true a b) keep)

def tightBinary (r : List Sig → Bool) (v : List Sig) (u : B) (a b : Sig) : Bool :=
  let ua := u &&& sep false a
  let ub := u &&& sep false b
  let rest := dropped [a,b] v
  let use := fun (g : Sig) => !(v.contains g) && g != zero && g != one && r (g::rest)
  ((((ua &&& ~~~b.1) ||| (ub &&& ~~~a.1)) == 0) && use (bin false a b)) ||
    ((((ua &&& b.2) ||| (ub &&& a.2)) == 0) && use (bin true a b))

def binaryAt (k t : Nat) (r : List Sig → Bool) (v : List Sig) (c : Cov) (a b : Sig) : Bool :=
  if t=0 ∧ v.length-2=k then before a b && tightBinary r v c.2.1 a b
  else binarySlow k t r v c a b

private theorem need_unique (c : Cov) (a b : Sig) (op : Bool)
    (h : sep false (bin op a b) ||| takeTwo c (sep false a) (sep false b)=top) :
    ((c.2.1 &&& sep false a) &&& (if op then b.2 else ~~~b.1)) |||
    ((c.2.1 &&& sep false b) &&& (if op then a.2 else ~~~a.1))=0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hh := congrArg (fun z : B => z.getLsbD i) h
  clear h
  cases op <;> simp only [sep,bin,ite_false,ite_true,takeTwo,top,BitVec.getLsbD_allOnes,
    BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,BitVec.getLsbD_zero,
    reduceCtorEq,hi,decide_true,Bool.true_and] at hh ⊢ <;>
    cases ax : a.1.getLsbD i <;> cases ay : a.2.getLsbD i <;>
    cases bx : b.1.getLsbD i <;> cases byy : b.2.getLsbD i <;>
    cases um : c.2.1.getLsbD i <;> simp [ax,ay,bx,byy,um] at hh ⊢

private theorem fast_accept {k t r v c a b}
    (h : binarySlow k t r v c a b=true) : binaryAt k t r v c a b=true := by
  unfold binaryAt
  split
  · rename_i cut
    obtain ⟨rfl,hn⟩ := cut
    obtain ⟨ho,hs⟩ := Bool.and_eq_true_iff.mp h
    apply Bool.and_eq_true_iff.mpr
    refine ⟨ho,?_⟩
    simp only [tryGate,Nat.sub_zero,hn,ite_true,Nat.lt_irrefl,decide_false,Bool.or_eq_true,Bool.and_eq_true,
      beq_iff_eq] at hs
    simp only [tightBinary,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq]
    rcases hs with z | z
    · exact Or.inl ⟨need_unique c a b false z.1.1.1.1,⟨⟨⟨z.1.1.1.2,z.1.1.2⟩,z.1.2⟩,z.2⟩⟩
    · exact Or.inr ⟨need_unique c a b true z.1.1.1.1,⟨⟨⟨z.1.1.1.2,z.1.1.2⟩,z.1.2⟩,z.2⟩⟩
  · exact h

private theorem fast_mono {k t v c a b} {r s : List Sig → Bool}
    (h : ∀ w, r w = true → s w = true)
    (hslow : binarySlow k t r v c a b=true → binarySlow k t s v c a b=true)
    (hr : binaryAt k t r v c a b=true) : binaryAt k t s v c a b=true := by
  by_cases hcut : t=0 ∧ v.length-2=k
  · simp only [binaryAt,if_pos hcut,tightBinary,Bool.and_eq_true,Bool.or_eq_true] at hr ⊢
    obtain ⟨order,z⟩ := hr
    refine ⟨order,?_⟩
    rcases z with ⟨p,hp,hr⟩ | ⟨p,hp,hr⟩
    · exact Or.inl ⟨p,hp,h _ hr⟩
    · exact Or.inr ⟨p,hp,h _ hr⟩
  · simpa only [binaryAt,if_neg hcut] using hslow (by simpa only [binaryAt,if_neg hcut] using hr)

def binaryMoves (k t : Nat) (r : List Sig → Bool) (v : List Sig) : Bool :=
  v.any (fun a => v.any (binaryAt k t r v (coverage (decide (0<t)) v) a))

def search : Nat → Nat → List Sig → Bool
  | 0, _, v => v.contains target
  | k+1,t,v =>
    if t>k+1 ∨ v.length>k+1-t+1 then false else
    v.contains target ||
    (decide (0<t) && unaryMoves k (t-1) (search k (t-1)) v) ||
    binaryMoves k t (search k t) v

private lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]



def raw0 : Sig := (28869614270866295497477574960510434279762608407918417125437601742975,741391289739673512450516123602509305835585338347106797068)
def raw1 : Sig := (57739228540305410968276458151791472568309176889847518125571704897535,171353435628561640190770602454875977561069896067)
def raw2 : Sig := (133312448394939281495493639403052499426697915484595402548947042959232,25472455636532542733997266773601547816317369908656726389653716737080)
def raw3 : Sig := (411195932401990203208141198135215225641619687835220533330187319754752,404399972844025305431735572705670797023471185583691276423080057086790)
def raw4 : Sig := (230212259068935663261509542917720597806484425155819771298040753684480,209801831843043596812443000685004710343122280803738263066465684633)
def raw5 : Sig := (431260418007346786329880949067330871420069253101408642671017583443968,431148523697226528883526032094299177302458656862427445214614360994146)
def raw6 : Sig := (431359145067867600345648485336496895598115575347102919028951027286016,431359145067472192455864653555018340532619734703225252419339078662643)
def raw7 : Sig := (431359146674410236714580942185197767099557867942390336934944543080448,431359146674410236714489553687647727913418850156559694675646919687804)

def raw : List Sig := [raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one

-- A set records the distinct signals needed by the remaining gates.
-- Read backwards, a gate replaces its output with the operand or operands.
inductive Live : Nat → Nat → Finset Sig → Prop
  | stop : Live 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k+1) t (insert a (insert b U))

private lemma target_proper : proper target := by unfold proper target zero one top; decide
private lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop => simpa using target_proper
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

abbrev Index := Fin 228
def rectangle (R : Index → Index → Prop) : Prop :=
  ∀ {i j x y}, R i x → R y j → R i j

def pos (a : Sig) (i : Index) := a.1.getLsbD i.val
def negVal (a : Sig) (j : Index) := a.2.getLsbD j.val
def separates (a : Sig) (i j : Index) : Prop := pos a i=true ∧ negVal a j=false

private lemma sub_row (R : Index → Index → Prop) (p : Index → Prop) (h : rectangle R) :
    rectangle (fun i j => R i j ∧ p i) :=
  fun hx hy => ⟨h hx.1 hy.1,hx.2⟩

private lemma sub_col (R : Index → Index → Prop) (p : Index → Prop) (h : rectangle R) :
    rectangle (fun i j => R i j ∧ p j) :=
  fun hx hy => ⟨h hx.1 hy.1,hy.2⟩

def carries (S : Finset Sig) (F : Index → Index → Sig) : Prop :=
  (∀ i j, F i j ∈ S ∧ separates (F i j) i j) ∧
  (∀ a, rectangle (fun i j => F i j=a))

private lemma split_face {F : Index → Index → Sig} {U : Finset Sig} {a b g : Sig}
    (ha : a ∉ U) (hb : b ∉ U) (hab : a≠b) (car : carries (insert g U) F)
    (pick : Index → Index → Bool)
    (left : rectangle (fun i j => F i j=g ∧ pick i j=true))
    (right : rectangle (fun i j => F i j=g ∧ pick i j=false))
    (ok : ∀ i j, F i j=g → separates (if pick i j then a else b) i j) :
    ∃ H, carries (insert a (insert b U)) H := by
  let H := fun i j => if F i j=g then (if pick i j then a else b) else F i j
  refine ⟨H,?_,?_⟩
  · intro i j
    by_cases e : F i j=g
    · refine ⟨?_,by simpa only [H,if_pos e] using ok i j e⟩
      cases p : pick i j <;> simp [H,e,p]
    · have u : F i j ∈ U := (Finset.mem_insert.mp (car.1 i j).1).resolve_left e
      simpa [H,e,u] using (car.1 i j).2
  · intro v i j x y hix hyj
    have memu (i j) (e : F i j≠g) : F i j ∈ U :=
      (Finset.mem_insert.mp (car.1 i j).1).resolve_left e
    have left_iff (i j) : H i j=a ↔ F i j=g ∧ pick i j=true := by
      by_cases e : F i j=g
      · cases p : pick i j <;> simp [H,e,p,hab.symm]
      · have ne : F i j≠a := fun eq => ha (eq ▸ memu i j e)
        simp [H,e,ne]
    have right_iff (i j) : H i j=b ↔ F i j=g ∧ pick i j=false := by
      by_cases e : F i j=g
      · cases p : pick i j <;> simp [H,e,p,hab]
      · have ne : F i j≠b := fun eq => hb (eq ▸ memu i j e)
        simp [H,e,ne]
    by_cases ea : v=a
    · subst ea; exact (left_iff i j).2 (left ((left_iff i x).1 hix) ((left_iff y j).1 hyj))
    by_cases eb : v=b
    · subst eb; exact (right_iff i j).2 (right ((right_iff i x).1 hix) ((right_iff y j).1 hyj))
    have lift (i j) (hh : H i j=v) : F i j=v ∧ F i j≠g := by
      by_cases e : F i j=g
      · cases p : pick i j
        · exact False.elim (eb (by simpa [H,e,p] using hh.symm))
        · exact False.elim (ea (by simpa [H,e,p] using hh.symm))
      · exact ⟨by simpa [H,e] using hh,e⟩
    have ax := lift i x hix
    have by' := lift y j hyj
    have xy := car.2 v ax.1 by'.1
    have vg : v≠g := ax.1 ▸ ax.2
    simp [H,xy,vg]

private lemma split_gate {F : Index → Index → Sig} {U : Finset Sig} {a b : Sig} {d : Bool}
    (ha : a ∉ U) (hb : b ∉ U) (hab : a≠b) (car : carries (insert (bin d a b) U) F) :
    ∃ H, carries (insert a (insert b U)) H := by
  cases d
  · apply split_face ha hb hab car (fun _ j => !(negVal a j))
    · intro i j x y hx hy; exact ⟨car.2 (bin false a b) hx.1 hy.1,hy.2⟩
    · intro i j x y hx hy; exact ⟨car.2 (bin false a b) hx.1 hy.1,hy.2⟩
    · intro i j e
      have hh := (car.1 i j).2
      rw [e] at hh
      cases pa : a.1.getLsbD i.val <;> cases pb : b.1.getLsbD i.val <;>
        cases na : a.2.getLsbD j.val <;> cases nb : b.2.getLsbD j.val <;>
        simp only [separates,pos,negVal,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_and,pa,pb,na,nb,Bool.not_true,Bool.not_false] at hh ⊢ <;> simp_all only [Bool.and_false,Bool.false_and,Bool.and_true,Bool.true_and,Bool.or_false,Bool.or_true,Bool.false_or,Bool.true_or,reduceCtorEq,and_false,false_and,true_and,and_self,not_false_eq_true]
  · apply split_face ha hb hab car (fun i _ => pos a i)
    · intro i j x y hx hy; exact ⟨car.2 (bin true a b) hx.1 hy.1,hx.2⟩
    · intro i j x y hx hy; exact ⟨car.2 (bin true a b) hx.1 hy.1,hx.2⟩
    · intro i j e
      have hh := (car.1 i j).2
      rw [e] at hh
      cases pa : a.1.getLsbD i.val <;> cases pb : b.1.getLsbD i.val <;>
        cases na : a.2.getLsbD j.val <;> cases nb : b.2.getLsbD j.val <;>
        simp only [separates,pos,negVal,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_or,pa,pb,na,nb,Bool.not_true,Bool.not_false] at hh ⊢ <;> simp_all only [Bool.and_false,Bool.false_and,Bool.and_true,Bool.true_and,Bool.or_false,Bool.or_true,Bool.false_or,Bool.true_or,reduceCtorEq,and_false,false_and,true_and,and_self,not_false_eq_true]

private theorem tight_protocol {k t S} (l : Live k t S) :
    t=0 → S.card=k+1 → ∃ F, carries S F := by
  induction l with
  | stop =>
    intro _ _
    refine ⟨fun _ _ => target,?_,?_⟩
    · intro i j
      refine ⟨Finset.mem_singleton_self _,?_,?_⟩
      · change (BitVec.allOnes 228).getLsbD i.val=true
        simp only [BitVec.getLsbD_allOnes,i.isLt,decide_true]
      · change (0:B).getLsbD j.val=false
        simp
    · intro a i j x y hx hy
      exact hx
  | unary _ _ _ _ => omega
  | @binary k t U a b d _ _ hab fresh tail ih =>
    rintro rfl hc
    have sz := (live_size tail).2
    have nz : bin d a b ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem nz] at sz
    have h1 := Finset.card_insert_le (a:=a) (s:=insert b U)
    have h2 := Finset.card_insert_le b U
    have ha : a ∉ U := by
      intro hm
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem hm)] at hc
      omega
    have hb : b ∉ U := by
      intro hm
      rw [Finset.insert_eq_of_mem hm] at hc
      have h3 := Finset.card_insert_le a U
      omega
    obtain ⟨F,hF⟩ := ih rfl (by rw [Finset.card_insert_of_notMem nz]; omega)
    exact split_gate ha hb hab hF

def forced (v : List Sig) (a : Sig) (i j : Index) : Bool :=
  v.all (fun b => !(pos b i && !(negVal b j)) || b == a)

private lemma owner {v : List Sig} {S : Finset Sig} {F : Index → Index → Sig}
    (hv : v.toFinset=S) (car : carries S F) {a : Sig} {i j : Index}
    (h : forced v a i j=true) : F i j=a := by
  have mem : F i j ∈ v := List.mem_toFinset.mp (hv.symm ▸ (car.1 i j).1)
  have props := (car.1 i j).2
  obtain ⟨hp,hn⟩ := props
  have hh := List.all_eq_true.mp h (F i j) mem
  simpa only [hp,hn,Bool.not_false,Bool.true_and,Bool.not_true,Bool.false_or,beq_iff_eq] using hh

private theorem conflict_impossible {k : Nat} {v : List Sig} {S : Finset Sig}
    (hv : v.toFinset=S) (hc : S.card=k+1) {a b : Sig} (distinct : a≠b)
    {i j x y u z : Index}
    (ax : forced v a i x=true) (ay : forced v a y j=true)
    (bu : forced v b i u=true) (bz : forced v b z j=true) : ¬ Live k 0 S := by
  intro l
  obtain ⟨F,car⟩ := tight_protocol l rfl hc
  have ha := car.2 a (owner hv car ax) (owner hv car ay)
  have hb := car.2 b (owner hv car bu) (owner hv car bz)
  exact distinct (ha.symm.trans hb)

private lemma sep_unary (t : Nat) (a : Sig) (i : Nat)
    (h : (sep (decide (0<t)) (neg a)).getLsbD i = true) :
    (sep true a).getLsbD i = true := by
  by_cases hi : i < 228
  · cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases ht : decide (0<t) <;>
      simp only [sep,neg,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 228 ≤ i)] at h

private lemma sep_binary (t d : Bool) (a b : Sig) (i : Nat)
    (h : (sep t (bin d a b)).getLsbD i = true) :
    (sep t a).getLsbD i = true ∨ (sep t b).getLsbD i = true := by
  by_cases hi : i < 228
  · cases t <;> cases d <;>
      cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
      cases hu : b.1.getLsbD i <;> cases hv : b.2.getLsbD i <;>
      simp only [sep,bin,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,hu,hv] at h ⊢ <;> first | contradiction | decide | exact h
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 228 ≤ i)] at h

private lemma sep_weaken (t : Nat) (a : Sig) (i : Nat) (hi : i < 228)
    (h : (sep (decide (0<t)) a).getLsbD i = true) : (sep true a).getLsbD i = true := by
  cases ht : decide (0<t) <;> cases hx : a.1.getLsbD i <;> cases hy : a.2.getLsbD i <;>
    simp only [sep,ite_true,ite_false,reduceCtorEq,decide_true,BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,hx,hy,ht] at h ⊢ <;> first | contradiction | decide | exact h

private lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 228) :
    ∃ a ∈ S, (sep (decide (0<t)) a).getLsbD i = true := by
  induction h with
  | stop =>
    refine ⟨target,by simp,?_⟩
    change (BitVec.allOnes 228 &&& ~~~(0 : B)).getLsbD i = true
    rw [BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_allOnes (v := 228)] <;> simp [hi]
  | unary ha hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ,decide_true]
    rcases hx with rfl | hU
    · exact ⟨_,Finset.mem_insert_self _ _,sep_unary _ _ _ h⟩
    · exact ⟨x,Finset.mem_insert_of_mem hU,sep_weaken _ _ _ hi h⟩
  | binary ha hb hab hf _ ih =>
    obtain ⟨x,hx,h⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases sep_binary _ _ _ _ _ h with h | h
      · exact ⟨_,Finset.mem_insert_self _ _,h⟩
      · exact ⟨_,Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),h⟩
    · exact ⟨x,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),h⟩
private lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).getLsbD i = true ↔ ∃ a ∈ v, (sep d a).getLsbD i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih => simp only [unionSep,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp] <;> aesop

private lemma live_cover {k t S} {v : List Sig} (h : Live k t S) (he : v.toFinset=S) :
    unionSep (decide (0<t)) v = top := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain ⟨a,hm,ha⟩ := live_sep h i hi
  have hmem : a ∈ v := List.mem_toFinset.mp (he.symm ▸ hm)
  simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using (mem_unionSep _ _ _).2 ⟨a,hmem,ha⟩

private lemma union_append (d : Bool) (l r : List Sig) :
    unionSep d (l++r) = unionSep d l ||| unionSep d r := by
  induction l with
  | nil => simp [unionSep]
  | cons a l ih => simp [unionSep,ih,BitVec.or_assoc]

def keepOf (U : Finset Sig) (del : List Sig) : List Sig := del.filter (fun a => decide (a ∈ U))

private lemma edit_list {v del : List Sig} {U : Finset Sig}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset = del.toFinset ∪ U) :
    (keepOf U del ++ dropped del v).Nodup ∧ (keepOf U del ++ dropped del v).toFinset = U := by
  have memv (x : Sig) : x ∈ v ↔ x ∈ del ∨ x ∈ U := by
    change x ∈ v ↔ _
    rw [← List.mem_toFinset,he]
    simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _,hv.filter _,?_⟩
    intro a ha b hb eq
    subst b
    simp [keepOf] at ha
    simp [dropped] at hb
    exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset,List.mem_append,List.mem_filter,keepOf,dropped,decide_eq_true_eq,
      Bool.not_eq_true',List.contains_eq_mem,memv]
    by_cases h : x ∈ del <;> simp_all

private lemma recover_perm (del v : List Sig) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del, x ∈ v) : v.Perm (del ++ dropped del v) := by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd,hv.filter _,?_⟩
    intro a ha b hb e
    subst b
    simp [dropped] at hb
    exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset,List.mem_append,dropped,List.mem_filter,Bool.not_eq_true',
      List.contains_eq_mem,decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all

private lemma one_rest (d : Bool) {v : List Sig} {a : Sig} (hv : v.Nodup) (ha : a ∈ v) :
    v.length-1=(dropped [a] v).length ∧
      takeOne (coverage d v) (sep d a)=unionSep d (dropped [a] v) := by
  have p := recover_perm [a] v hv (by simp) (by simpa using ha)
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_one _ _).trans (cov_union _ _)

private lemma two_rest (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    v.length-2=(dropped [a,b] v).length ∧
      takeTwo (coverage d v) (sep d a) (sep d b)=unionSep d (dropped [a,b] v) := by
  have p := recover_perm [a,b] v hv (by simp [hab]) (by simp [ha,hb])
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d p]
    exact (cov_two _ _ _).trans (cov_union _ _)

private lemma gate_found {k t m : Nat} {v rest h : List Sig} {g : Sig} {opts : List (List Sig)}
    {S : Finset Sig} {r : List Sig → Bool} (l : Live m t S)
    (hle : m ≤ k) (hp : proper g) (ha : g ∉ v) (hh : h ∈ opts)
    (hn : (g::(h++rest)).Nodup) (he : (g::(h++rest)).toFinset=S)
    (hr : r (g::(h++rest)) = true) : tryGate k t r v rest rest.length (unionSep (decide (0<t)) rest) g opts = true := by
  obtain ⟨ht,hc⟩ := live_size l
  rw [←he,List.toFinset_card_of_nodup hn] at hc
  simp only [List.length_cons,List.length_append] at hc
  have hl : rest.length+h.length+1 ≤ k-t+1 := by omega
  have cv := live_cover l he
  rw [unionSep,union_append] at cv
  have cov : (sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest) ||| unionSep (decide (0<t)) h = top := by
    rw [← cv]; ac_rfl
  by_cases tight : rest.length=k-t
  · have hz : h.length=0 := by omega
    have hem : h=[] := List.length_eq_zero_iff.mp hz
    subst h
    have ok : sep (decide (0<t)) g ||| unionSep (decide (0<t)) rest = top := by
      simpa [unionSep] using cov
    simp [tryGate,tight,ok,ha,hp.1,hp.2,hr] at *
  · simp only [tryGate,if_neg tight,Bool.and_eq_true,bne_iff_ne,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not,
      List.any_eq_true,decide_eq_true_eq,beq_iff_eq]
    exact ⟨h,hh,⟨⟨⟨⟨hl,cov⟩,ha⟩,hp.1⟩,hp.2⟩,hr⟩

private lemma ordered {a b : Sig} (h : a≠b) : before a b = true ∨ before b a = true := by
  by_cases e : a.1=b.1
  · have h2 : a.2.toNat≠b.2.toNat := fun h2 => h (Prod.ext e (BitVec.eq_of_toNat_eq h2))
    simp [before,e]; omega
  · have h1 : a.1.toNat≠b.1.toNat := fun h1 => e (BitVec.eq_of_toNat_eq h1)
    simp [before,e,Ne.symm e]; omega

private lemma unary_found {m t k : Nat} {r : List Sig → Bool} {U : Finset Sig} {a : Sig} {v : List Sig}
    (hv : v.Nodup) (he : v.toFinset = insert a U) (hle : m ≤ k)
    (fresh : neg a ∉ insert a U) (l : Live m t (insert (neg a) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (neg a) U → r v = true) :
    unaryMoves k t r v = true := by
  let h := keepOf U [a]
  let rest := dropped [a] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  obtain ⟨hn,eq⟩ := edit_list (del := [a]) (U := U) hv (by simp) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : neg a ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : neg a ∉ U := fun hm => fresh (Finset.mem_insert_of_mem hm)
  have hnd : (neg a::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (neg a::(h++rest)).toFinset=insert (neg a) U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a]] := by by_cases hm : a ∈ U <;> simp [h,keepOf,hm]
  apply List.any_eq_true.mpr
  refine ⟨a,ah,?_⟩
  unfold unaryAt
  obtain ⟨hlen,hmask⟩ := one_rest (decide (0<t)) hv ah
  rw [hlen,hmask]
  exact gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)

private lemma binary_found {m t k : Nat} {r : List Sig → Bool} {U : Finset Sig} {a b : Sig} {d : Bool} {v : List Sig}
    (hv : v.Nodup) (he : v.toFinset = insert a (insert b U)) (hle : m ≤ k)
    (ord : before a b=true) (hab : a≠b) (fresh : bin d a b ∉ insert a (insert b U))
    (l : Live m t (insert (bin d a b) U))
    (ih : ∀ v : List Sig, v.Nodup → v.toFinset = insert (bin d a b) U → r v = true) :
    binaryMoves k t r v = true := by
  let g := bin d a b
  let h := keepOf U [a,b]
  let rest := dropped [a,b] v
  have ah : a ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
  have bh : b ∈ v := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  obtain ⟨hn,eq⟩ := edit_list (del := [a,b]) (U := U) hv (by simp [hab]) (by simpa using he)
  change (h++rest).Nodup at hn
  change (h++rest).toFinset=U at eq
  have nn : g ∉ v := fun hm => fresh (he ▸ List.mem_toFinset.mpr hm)
  have nz : g ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hnd : (g::(h++rest)).Nodup := List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm),hn⟩
  have e : (g::(h++rest)).toFinset=insert g U := by rw [List.toFinset_cons,eq]
  have opts : h ∈ [[],[a],[b],[a,b]] := by
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U <;> simp [h,keepOf,ha,hb]
  have ok := gate_found l hle (live_proper l _ (Finset.mem_insert_self _ _)) nn opts hnd e (ih _ hnd e)
  apply List.any_eq_true.mpr
  refine ⟨a,ah,List.any_eq_true.mpr ⟨b,bh,fast_accept (Bool.and_eq_true_iff.mpr ⟨ord,?_⟩)⟩⟩
  obtain ⟨hlen,hmask⟩ := two_rest (decide (0<t)) hv ah bh hab
  dsimp only
  rw [hlen,hmask]
  cases d
  · exact Bool.or_eq_true_iff.mpr (Or.inl ok)
  · exact Bool.or_eq_true_iff.mpr (Or.inr ok)

private lemma search_complete {m t S} (l : Live m t S) (K : Nat) (hle : m ≤ K)
    (v : List Sig) (hv : v.Nodup) (he : v.toFinset=S) : search K t v = true := by
  have size := live_size l
  rw [←he,List.toFinset_card_of_nodup hv] at size
  induction l generalizing K v with
  | stop =>
    have ht : v.contains target = true := List.contains_iff_mem.mpr (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
    cases K with
    | zero => exact ht
    | succ k =>
      rw [search,if_neg (by omega),ht]
      rfl
  | @unary m t U a ha hf tail ih =>
    cases K with
    | zero => omega
    | succ k =>
      rw [search,if_neg (by omega)]
      apply Bool.or_eq_true_iff.mpr; left
      apply Bool.or_eq_true_iff.mpr; right
      apply Bool.and_eq_true_iff.mpr
      refine ⟨by simp,unary_found hv he (by omega) hf tail ?_⟩
      intro w hn eq
      have sz := live_size tail
      rw [←eq,List.toFinset_card_of_nodup hn] at sz
      exact ih k (by omega) w hn eq sz
  | @binary m t U a b d ha hb hab hf tail ih =>
    cases K with
    | zero => omega
    | succ k =>
      rw [search,if_neg (by omega)]
      apply Bool.or_eq_true_iff.mpr
      right
      have cont (w : List Sig) (hn : w.Nodup) (eq : w.toFinset=insert (bin d a b) U) : search k t w = true := by
        have sz := live_size tail
        rw [←eq,List.toFinset_card_of_nodup hn] at sz
        exact ih k (by omega) w hn eq sz
      rcases ordered hab with o | o
      · exact binary_found hv he (by omega) o hab hf tail cont
      · rw [Finset.insert_comm a b] at he hf
        rw [bin_comm d a b] at hf tail cont
        exact binary_found hv he (by omega) o hab.symm hf tail cont
open PEqualNP.CircuitLowerBounds

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  obtain ⟨p,n⟩ := a
  simp only [bin,one,zero,top,reduceCtorEq,ite_true,ite_false,BitVec.and_allOnes,BitVec.or_allOnes,BitVec.and_zero,BitVec.or_zero,BitVec.and_self,BitVec.or_self,Prod.mk.injEq,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one,top]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (side : Bool) (i : Fin 228) (a : Sig) : Bool :=
  (if side then a.1 else a.2).getLsbD i.val

private lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit,zero]
private lemma bit_one (s i) : bit s i one = true := by
  cases s <;> change (BitVec.allOnes 228).getLsbD i.val = true <;> rw [BitVec.getLsbD_allOnes] <;> simp
private lemma bit_neg (s i) (a : Sig) : bit s i (neg a) = !(bit s i a) := by
  cases s <;> simp only [bit,neg,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_not,i.isLt,decide_true,Bool.true_and]
private lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp only [bit,bin,reduceCtorEq,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]

private lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl

private lemma run_bit (s i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _ _
    | cons a l ih =>
      change bit s i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _ _
    | cons a l ih =>
      change bit s i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit s i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _ _

private lemma execute_bits (gs : List Gate) (s i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit s i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit s i g w (hg g (by simp))]

def sample (s : Bool) (i : Fin 228) (j : Fin 8) := bit s i (raw.getD j.val zero)
def edgeF (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) ||
  (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 7)

private lemma sample_ok : ∀ (s : Bool) (i : Fin 228), edgeF (sample s i) = s := by decide +kernel
private lemma raw_id : List.ofFn (fun j : Fin 8 => raw.getD j.val zero) = raw := by rfl
private lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 8 => raw.getD j.val zero)).map (bit s i) := by rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]

private lemma circuit_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = edgeF x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have project (s i) : bit s i (w.getD C.output zero) = s := by
    rw [←b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [sample_list,sample_ok] at eq
    exact eq
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project true ⟨i,hi⟩
      change (w.getD C.output zero).1.getLsbD i = true at p
      change _ = (BitVec.allOnes _).getLsbD _
      simpa only [BitVec.getLsbD_allOnes,hi,decide_true] using p
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have p := project false ⟨i,hi⟩
      change (w.getD C.output zero).2.getLsbD i = false at p
      have hz : (0 : B).getLsbD i=false := by simp
      exact p.trans hz.symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

private lemma raw_nd : raw.Nodup := by unfold raw; decide +kernel
private lemma every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true := by decide +kernel

private lemma necessary {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset=S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_,hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain ⟨b,hb,h⟩ := live_sep l i hi
    have ba : b ≠ a := fun he => hn (he ▸ hb)
    have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
    have eq := (mem_unionSep true _ _).mpr ⟨b,hm,sep_weaken _ _ _ hi h⟩
    simpa only [top,BitVec.getLsbD_allOnes,hi,decide_true] using eq
  simp [cov] at fail

private lemma circuit_search (C : Circuit) (hc : C.size ≤ 10)
    (h : PEqualNP.MetaComplexity.FanInTwo C) (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = edgeF x) :
    ∃ t ≤ 3, search 10 t raw = true := by
  obtain ⟨k,t,S,hk,ht,hs⟩ := extract C.gates raw h (circuit_target C h he)
  have eq := necessary ht hs
  have sz := live_size ht
  rw [←eq,List.toFinset_card_of_nodup raw_nd] at sz
  have len : raw.length=8 := rfl
  change C.gates.length ≤ 10 at hc
  exact ⟨t,by omega,search_complete ht 10 (by omega) raw raw_nd eq⟩
-- A finite list of rejected successor states can be reused by the checker.
-- The closed Boolean check verifies that the list covers every enabled move.
def stepTest (k t : Nat) (v : List Sig) (u b : List Sig → Bool) : Bool :=
  if t>k+1 ∨ v.length>k+1-t+1 then false else
  v.contains target || (decide (0<t) && unaryMoves k (t-1) u v) || binaryMoves k t b v

def impossible (K t : Nat) (v : List Sig) : Prop :=
  ∀ {m S}, Live m t S → m ≤ K → v.Nodup → v.toFinset=S → False

private lemma by_search {K t v} (no : search K t v=false) : impossible K t v := by
  intro m S l le nd he
  have hit := search_complete l K le v nd he
  simp [no] at hit

private lemma by_rectangle {K v} {a b : Sig} (len : v.length=K+1) (ab : a≠b)
    {i j x y u z : Index}
    (ax : forced v a i x=true) (ay : forced v a y j=true)
    (bu : forced v b i u=true) (bz : forced v b z j=true) : impossible K 0 v := by
  intro m S l le nd he
  have sc : S.card=v.length := he ▸ List.toFinset_card_of_nodup nd
  have sz := live_size l
  have eq : S.card=m+1 := by omega
  exact conflict_impossible he eq ab ax ay bu bz l

private lemma reject_branch (k t : Nat) (v : List Sig) (U A : List (List Sig))
    (hu : ∀ w ∈ U, impossible k (t-1) w)
    (hb : ∀ w ∈ A, impossible k t w)
    (hc : stepTest k t v (fun w => !(U.contains w)) (fun w => !(A.contains w)) = false) :
    impossible (k+1) t v := by
  intro m S l le nd he
  have pass (n : Nat) (L : List (List Sig)) (hn : ∀ w ∈ L, impossible k n w)
      {j T} (hl : Live j n T) (hj : j≤k) (w : List Sig) (nw : w.Nodup) (ew : w.toFinset=T) :
      !(L.contains w)=true := by
    have hnm : w ∉ L := fun hw => hn w hw hl hj nw ew
    simpa [List.contains_eq_mem] using hnm
  have sz := live_size l
  rw [←he,List.toFinset_card_of_nodup nd] at sz
  unfold stepTest at hc
  rw [if_neg (by omega)] at hc
  apply Bool.noConfusion (show false=true from hc.symm.trans ?_)
  cases l with
  | stop =>
    have hit : v.contains target=true := List.contains_iff_mem.mpr (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
    exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inl hit)))
  | @unary j s T a ha fresh tail =>
    apply Bool.or_eq_true_iff.mpr; left
    apply Bool.or_eq_true_iff.mpr; right
    apply Bool.and_eq_true_iff.mpr
    refine ⟨by simp,unary_found nd he (by omega) fresh tail ?_⟩
    exact pass _ U hu tail (by omega)
  | @binary j s T a b d ha ha' hab fresh tail =>
    apply Bool.or_eq_true_iff.mpr; right
    have cont := pass _ A hb tail (by omega)
    rcases ordered hab with o | o
    · exact binary_found nd he (by omega) o hab fresh tail cont
    · rw [Finset.insert_comm a b] at he fresh
      rw [bin_comm d a b] at fresh tail cont
      exact binary_found nd he (by omega) o hab.symm fresh tail cont

def rectTest (K : Nat) (v : List Sig) (a b : Nat) (i j x y u z : Index) : Bool :=
  let A := v.getD a zero
  let Bv := v.getD b zero
  v.length==K+1 && A != Bv && forced v A i x && forced v A y j && forced v Bv i u && forced v Bv z j

private lemma rectReject (K : Nat) (v : List Sig) (a b : Nat) (i j x y u z : Index)
    (ok : rectTest K v a b i j x y u z=true) : impossible K 0 v := by
  simp only [rectTest,Bool.and_eq_true,beq_iff_eq,bne_iff_ne] at ok
  obtain ⟨⟨⟨⟨⟨len,ne⟩,ax⟩,ay⟩,bu⟩,bz⟩ := ok
  exact by_rectangle len ne ax ay bu bz

private def wire0 : Sig := bin false raw0 raw1

private def wire1 : Sig := bin true raw0 raw1

private def wire2 : Sig := bin false raw0 raw2

private def wire3 : Sig := bin true raw0 raw2

private def wire4 : Sig := bin false raw0 raw3

private def wire5 : Sig := bin true raw0 raw3

private def wire6 : Sig := bin false raw0 raw4

private def wire7 : Sig := bin true raw0 raw4

private def wire8 : Sig := bin false raw0 raw5

private def wire9 : Sig := bin true raw0 raw5

private def wire10 : Sig := bin false raw0 raw6

private def wire11 : Sig := bin true raw0 raw6

private def wire12 : Sig := bin false raw0 raw7

private def wire13 : Sig := bin true raw0 raw7

private def wire14 : Sig := bin false raw1 raw2

private def wire15 : Sig := bin true raw1 raw2

private def wire16 : Sig := bin false raw1 raw3

private def wire17 : Sig := bin true raw1 raw3

private def wire18 : Sig := bin false raw1 raw4

private def wire19 : Sig := bin true raw1 raw4

private def wire20 : Sig := bin false raw1 raw5

private def wire21 : Sig := bin true raw1 raw5

private def wire22 : Sig := bin false raw1 raw6

private def wire23 : Sig := bin true raw1 raw6

private def wire24 : Sig := bin false raw1 raw7

private def wire25 : Sig := bin true raw1 raw7

private def wire26 : Sig := bin false raw2 raw3

private def wire27 : Sig := bin true raw2 raw3

private def wire28 : Sig := bin false raw2 raw4

private def wire29 : Sig := bin true raw2 raw4

private def wire30 : Sig := bin false raw2 raw5

private def wire31 : Sig := bin true raw2 raw5

private def wire32 : Sig := bin false raw2 raw6

private def wire33 : Sig := bin true raw2 raw6

private def wire34 : Sig := bin false raw2 raw7

private def wire35 : Sig := bin true raw2 raw7

private def wire36 : Sig := bin false raw3 raw5

private def wire37 : Sig := bin true raw3 raw5

private def wire38 : Sig := bin false raw3 raw6

private def wire39 : Sig := bin true raw3 raw6

private def wire40 : Sig := bin false raw3 raw7

private def wire41 : Sig := bin true raw3 raw7

private def wire42 : Sig := bin false raw4 raw3

private def wire43 : Sig := bin true raw4 raw3

private def wire44 : Sig := bin false raw4 raw5

private def wire45 : Sig := bin true raw4 raw5

private def wire46 : Sig := bin false raw4 raw6

private def wire47 : Sig := bin true raw4 raw6

private def wire48 : Sig := bin false raw4 raw7

private def wire49 : Sig := bin true raw4 raw7

private def wire50 : Sig := bin false raw5 raw6

private def wire51 : Sig := bin true raw5 raw6

private def wire52 : Sig := bin false raw5 raw7

private def wire53 : Sig := bin true raw5 raw7

private def wire54 : Sig := bin false raw6 raw7

private def wire55 : Sig := bin true raw6 raw7

private def wire56 : Sig := bin false wire0 raw2

private def wire57 : Sig := bin true wire0 raw2

private def wire58 : Sig := bin false wire0 raw3

private def wire59 : Sig := bin true wire0 raw3

private def wire60 : Sig := bin false wire0 raw4

private def wire61 : Sig := bin true wire0 raw4

private def wire62 : Sig := bin false wire0 raw5

private def wire63 : Sig := bin true wire0 raw5

private def wire64 : Sig := bin false wire0 raw6

private def wire65 : Sig := bin true wire0 raw6

private def wire66 : Sig := bin false wire0 raw7

private def wire67 : Sig := bin true wire0 raw7

private def wire68 : Sig := bin false wire1 raw2

private def wire69 : Sig := bin true wire1 raw2

private def wire70 : Sig := bin false wire1 raw3

private def wire71 : Sig := bin true wire1 raw3

private def wire72 : Sig := bin false wire1 raw4

private def wire73 : Sig := bin true wire1 raw4

private def wire74 : Sig := bin false wire1 raw5

private def wire75 : Sig := bin true wire1 raw5

private def wire76 : Sig := bin false wire1 raw6

private def wire77 : Sig := bin true wire1 raw6

private def wire78 : Sig := bin false wire1 raw7

private def wire79 : Sig := bin true wire1 raw7

private def wire80 : Sig := bin false wire3 raw3

private def wire81 : Sig := bin true wire3 raw3

private def wire82 : Sig := bin false wire3 raw4

private def wire83 : Sig := bin true wire3 raw4

private def wire84 : Sig := bin false wire3 raw5

private def wire85 : Sig := bin true wire3 raw5

private def wire86 : Sig := bin false wire3 raw6

private def wire87 : Sig := bin true wire3 raw6

private def wire88 : Sig := bin false wire3 raw7

private def wire89 : Sig := bin true wire3 raw7

private def wire90 : Sig := bin false raw1 wire3

private def wire91 : Sig := bin false wire7 raw3

private def wire92 : Sig := bin true wire7 raw3

private def wire93 : Sig := bin false wire7 raw5

private def wire94 : Sig := bin true wire7 raw5

private def wire95 : Sig := bin false wire7 raw6

private def wire96 : Sig := bin true wire7 raw6

private def wire97 : Sig := bin false wire7 raw7

private def wire98 : Sig := bin true wire7 raw7

private def wire99 : Sig := bin false raw1 wire7

private def wire100 : Sig := bin false raw2 wire7

private def wire101 : Sig := bin true wire8 raw1

private def wire102 : Sig := bin false wire8 raw2

private def wire103 : Sig := bin true wire8 raw2

private def wire104 : Sig := bin false wire8 raw3

private def wire105 : Sig := bin true wire8 raw3

private def wire106 : Sig := bin false wire8 raw4

private def wire107 : Sig := bin true wire8 raw4

private def wire108 : Sig := bin false wire8 raw6

private def wire109 : Sig := bin true wire8 raw6

private def wire110 : Sig := bin false wire8 raw7

private def wire111 : Sig := bin true wire8 raw7

private def wire112 : Sig := bin false wire9 raw6

private def wire113 : Sig := bin true wire9 raw6

private def wire114 : Sig := bin false wire9 raw7

private def wire115 : Sig := bin true wire9 raw7

private def wire116 : Sig := bin false raw1 wire9

private def wire117 : Sig := bin false raw2 wire9

private def wire118 : Sig := bin false raw3 wire9

private def wire119 : Sig := bin true raw3 wire9

private def wire120 : Sig := bin false raw4 wire9

private def wire121 : Sig := bin true wire10 raw1

private def wire122 : Sig := bin false wire10 raw2

private def wire123 : Sig := bin true wire10 raw2

private def wire124 : Sig := bin false wire10 raw3

private def wire125 : Sig := bin true wire10 raw3

private def wire126 : Sig := bin false wire10 raw4

private def wire127 : Sig := bin true wire10 raw4

private def wire128 : Sig := bin true wire10 raw5

private def wire129 : Sig := bin false wire10 raw7

private def wire130 : Sig := bin true wire10 raw7

private def wire131 : Sig := bin false wire121 raw2

private def wire132 : Sig := bin true wire121 raw2

private def wire133 : Sig := bin false wire121 raw3

private def wire134 : Sig := bin true wire121 raw3

private def wire135 : Sig := bin false wire121 raw4

private def wire136 : Sig := bin true wire121 raw4

private def wire137 : Sig := bin false wire121 raw5

private def wire138 : Sig := bin true wire121 raw5

private def wire139 : Sig := bin false wire121 raw7

private def wire140 : Sig := bin true wire121 raw7

private def wire141 : Sig := bin false raw0 wire121

private def wire142 : Sig := bin false wire128 raw7

private def wire143 : Sig := bin true wire128 raw7

private def wire144 : Sig := bin false raw0 wire128

private def wire145 : Sig := bin false raw1 wire128

private def wire146 : Sig := bin false raw2 wire128

private def wire147 : Sig := bin true raw2 wire128

private def wire148 : Sig := bin false raw3 wire128

private def wire149 : Sig := bin true raw3 wire128

private def wire150 : Sig := bin false raw4 wire128

private def wire151 : Sig := bin true raw4 wire128

private def wire152 : Sig := bin true wire24 raw2

private def wire153 : Sig := bin true wire24 raw3

private def wire154 : Sig := bin true wire24 raw4

private def wire155 : Sig := bin true wire24 raw5

private def wire156 : Sig := bin true wire10 wire24

private def wire157 : Sig := bin true raw0 wire24

private def wire158 : Sig := bin false raw1 wire13

private def wire159 : Sig := bin false raw2 wire13

private def wire160 : Sig := bin false raw3 wire13

private def wire161 : Sig := bin true raw3 wire13

private def wire162 : Sig := bin false raw4 wire13

private def wire163 : Sig := bin false raw5 wire13

private def wire164 : Sig := bin false raw6 wire13

private def wire165 : Sig := bin true raw6 wire13

private def wire166 : Sig := bin true wire14 raw0

private def wire167 : Sig := bin false wire14 raw3

private def wire168 : Sig := bin true wire14 raw3

private def wire169 : Sig := bin false wire14 raw4

private def wire170 : Sig := bin true wire14 raw4

private def wire171 : Sig := bin false wire14 raw5

private def wire172 : Sig := bin true wire14 raw5

private def wire173 : Sig := bin false wire14 raw6

private def wire174 : Sig := bin true wire14 raw6

private def wire175 : Sig := bin false wire14 raw7

private def wire176 : Sig := bin true wire14 raw7

private def wire177 : Sig := bin false wire15 raw3

private def wire178 : Sig := bin true wire15 raw3

private def wire179 : Sig := bin false wire15 raw4

private def wire180 : Sig := bin true wire15 raw4

private def wire181 : Sig := bin false wire15 raw5

private def wire182 : Sig := bin true wire15 raw5

private def wire183 : Sig := bin false wire15 raw6

private def wire184 : Sig := bin true wire15 raw6

private def wire185 : Sig := bin false wire15 raw7

private def wire186 : Sig := bin true wire15 raw7

private def wire187 : Sig := bin false raw0 wire15

private def wire188 : Sig := bin false wire17 raw5

private def wire189 : Sig := bin true wire17 raw5

private def wire190 : Sig := bin false wire17 raw6

private def wire191 : Sig := bin true wire17 raw6

private def wire192 : Sig := bin false wire17 raw7

private def wire193 : Sig := bin true wire17 raw7

private def wire194 : Sig := bin false raw0 wire17

private def wire195 : Sig := bin false raw2 wire17

private def wire196 : Sig := bin false raw4 wire17

private def wire197 : Sig := bin true raw4 wire17

private def wire198 : Sig := bin false wire21 raw6

private def wire199 : Sig := bin true wire21 raw6

private def wire200 : Sig := bin false wire21 raw7

private def wire201 : Sig := bin true wire21 raw7

private def wire202 : Sig := bin false raw0 wire21

private def wire203 : Sig := bin false raw2 wire21

private def wire204 : Sig := bin false raw3 wire21

private def wire205 : Sig := bin false raw4 wire21

private def wire206 : Sig := bin true raw4 wire21

private def wire207 : Sig := bin false wire23 raw7

private def wire208 : Sig := bin true wire23 raw7

private def wire209 : Sig := bin false raw2 wire23

private def wire210 : Sig := bin false raw3 wire23

private def wire211 : Sig := bin false raw4 wire23

private def wire212 : Sig := bin true raw4 wire23

private def wire213 : Sig := bin false raw5 wire23

private def wire214 : Sig := bin false wire24 raw3

private def wire215 : Sig := bin false wire24 raw4

private def wire216 : Sig := bin false wire24 raw5

private def wire217 : Sig := bin false wire24 raw6

private def wire218 : Sig := bin true wire24 raw6

private def wire219 : Sig := bin false wire152 raw3

private def wire220 : Sig := bin true wire152 raw3

private def wire221 : Sig := bin false wire152 raw4

private def wire222 : Sig := bin true wire152 raw4

private def wire223 : Sig := bin false wire152 raw5

private def wire224 : Sig := bin true wire152 raw5

private def wire225 : Sig := bin false wire152 raw6

private def wire226 : Sig := bin true wire152 raw6

private def wire227 : Sig := bin false raw1 wire152

private def wire228 : Sig := bin false raw0 wire152

private def wire229 : Sig := bin true raw0 wire152

private def wire230 : Sig := bin false wire157 raw2

private def wire231 : Sig := bin false wire157 raw3

private def wire232 : Sig := bin true wire157 raw3

private def wire233 : Sig := bin false wire157 raw4

private def wire234 : Sig := bin true wire157 raw4

private def wire235 : Sig := bin false wire157 raw5

private def wire236 : Sig := bin true wire157 raw5

private def wire237 : Sig := bin false wire157 raw6

private def wire238 : Sig := bin true wire157 raw6

private def wire239 : Sig := bin false wire26 raw4

private def wire240 : Sig := bin true wire26 raw4

private def wire241 : Sig := bin false wire26 raw5

private def wire242 : Sig := bin true wire26 raw5

private def wire243 : Sig := bin false wire26 raw6

private def wire244 : Sig := bin true wire26 raw6

private def wire245 : Sig := bin false wire26 raw7

private def wire246 : Sig := bin true wire26 raw7

private def wire247 : Sig := bin false raw0 wire26

private def wire248 : Sig := bin true raw0 wire26

private def wire249 : Sig := bin true raw1 wire26

private def wire250 : Sig := bin false wire29 raw3

private def wire251 : Sig := bin true wire29 raw3

private def wire252 : Sig := bin false wire29 raw5

private def wire253 : Sig := bin true wire29 raw5

private def wire254 : Sig := bin false wire29 raw6

private def wire255 : Sig := bin true wire29 raw6

private def wire256 : Sig := bin false wire29 raw7

private def wire257 : Sig := bin true wire29 raw7

private def wire258 : Sig := bin false raw0 wire29

private def wire259 : Sig := bin false raw1 wire29

private def wire260 : Sig := bin true wire250 raw5

private def wire261 : Sig := bin true wire250 raw6

private def wire262 : Sig := bin true wire250 raw7

private def wire263 : Sig := bin true raw2 wire250

private def wire264 : Sig := bin true raw0 wire250

private def wire265 : Sig := bin true raw1 wire250

private def wire266 : Sig := bin false wire29 wire35

private def wire267 : Sig := bin false raw0 wire35

private def wire268 : Sig := bin false raw3 wire35

private def wire269 : Sig := bin true raw3 wire35

private def wire270 : Sig := bin false raw4 wire35

private def wire271 : Sig := bin false raw5 wire35

private def wire272 : Sig := bin true raw5 wire35

private def wire273 : Sig := bin false raw6 wire35

private def wire274 : Sig := bin true raw6 wire35

private def wire275 : Sig := bin true wire227 raw3

private def wire276 : Sig := bin true wire227 raw4

private def wire277 : Sig := bin true wire227 raw5

private def wire278 : Sig := bin true wire227 raw6

private def wire279 : Sig := bin true raw0 wire227

private def wire280 : Sig := bin false wire37 raw6

private def wire281 : Sig := bin true wire37 raw6

private def wire282 : Sig := bin false wire37 raw7

private def wire283 : Sig := bin true wire37 raw7

private def wire284 : Sig := bin false raw0 wire37

private def wire285 : Sig := bin false raw1 wire37

private def wire286 : Sig := bin false raw2 wire37

private def wire287 : Sig := bin true raw2 wire37

private def wire288 : Sig := bin false raw4 wire37

private def wire289 : Sig := bin true raw4 wire37

private def wire290 : Sig := bin false wire37 wire51

private def wire291 : Sig := bin true wire288 raw3

private def wire292 : Sig := bin true wire288 raw5

private def wire293 : Sig := bin true wire288 raw6

private def wire294 : Sig := bin true wire288 raw7

private def wire295 : Sig := bin true raw0 wire288

private def wire296 : Sig := bin true raw1 wire288

private def wire297 : Sig := bin true raw2 wire288

private def wire298 : Sig := bin false wire42 raw5

private def wire299 : Sig := bin false wire42 raw6

private def wire300 : Sig := bin true wire42 raw6

private def wire301 : Sig := bin false wire42 raw7

private def wire302 : Sig := bin true wire42 raw7

private def wire303 : Sig := bin false raw0 wire42

private def wire304 : Sig := bin true raw0 wire42

private def wire305 : Sig := bin false raw1 wire42

private def wire306 : Sig := bin true raw1 wire42

private def wire307 : Sig := bin false wire44 raw6

private def wire308 : Sig := bin true wire44 raw6

private def wire309 : Sig := bin false wire44 raw7

private def wire310 : Sig := bin true wire44 raw7

private def wire311 : Sig := bin true raw0 wire44

private def wire312 : Sig := bin false raw1 wire44

private def wire313 : Sig := bin true raw1 wire44

private def wire314 : Sig := bin false raw2 wire44

private def wire315 : Sig := bin true raw2 wire44

private def wire316 : Sig := bin false wire51 raw7

private def wire317 : Sig := bin true wire51 raw7

private def wire318 : Sig := bin false raw1 wire51

private def wire319 : Sig := bin false raw2 wire51

private def wire320 : Sig := bin true raw2 wire51

private def wire321 : Sig := bin false raw3 wire51

private def wire322 : Sig := bin false raw4 wire51

private def wire323 : Sig := bin true raw4 wire51

private def wire324 : Sig := bin true wire144 raw1

private def wire325 : Sig := bin true wire144 raw2

private def wire326 : Sig := bin true wire144 raw3

private def wire327 : Sig := bin true wire144 raw4

private def wire328 : Sig := bin true wire144 raw7

private def wire329 : Sig := neg raw0

private def wire330 : Sig := neg raw1

private def wire331 : Sig := neg raw2

private def wire332 : Sig := neg raw3

private def wire333 : Sig := neg raw4

private def wire334 : Sig := neg raw5

private def wire335 : Sig := neg raw6

private def wire336 : Sig := neg raw7

private def wire337 : Sig := neg wire10

private def wire338 : Sig := neg wire24

private def st0 : List Sig := [wire56,raw2,raw0,raw1,raw3,raw4,raw5,raw6,raw7]

private theorem node0 : impossible 8 0 st0 := rectReject 8 st0 3 1 7 2 3 0 0 14 (by decide +kernel)

private def st1 : List Sig := [wire57,raw0,raw1,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1 : impossible 8 0 st1 := by_search (by decide +kernel)

private def st2 : List Sig := [wire57,wire0,raw0,raw1,raw3,raw4,raw5,raw6,raw7]

private theorem node2 : impossible 8 0 st2 := rectReject 8 st2 3 0 7 2 3 49 0 14 (by decide +kernel)

private def st3 : List Sig := [wire57,raw2,raw0,raw1,raw3,raw4,raw5,raw6,raw7]

private theorem node3 : impossible 8 0 st3 := rectReject 8 st3 5 4 21 5 1 28 0 14 (by decide +kernel)

private def st4 : List Sig := [wire58,raw3,raw0,raw1,raw2,raw4,raw5,raw6,raw7]

private theorem node4 : impossible 8 0 st4 := rectReject 8 st4 3 2 0 4 2 7 0 42 (by decide +kernel)

private def st5 : List Sig := [wire59,raw0,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node5 : impossible 8 0 st5 := by_search (by decide +kernel)

private def st6 : List Sig := [wire59,wire0,raw0,raw1,raw2,raw4,raw5,raw6,raw7]

private theorem node6 : impossible 8 0 st6 := rectReject 8 st6 4 0 14 0 1 7 3 21 (by decide +kernel)

private def st7 : List Sig := [wire59,raw3,raw0,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node7 : impossible 8 0 st7 := by_search (by decide +kernel)

private def st8 : List Sig := [wire60,raw4,raw0,raw1,raw2,raw3,raw5,raw6,raw7]

private theorem node8 : impossible 8 0 st8 := rectReject 8 st8 3 2 0 4 2 7 0 42 (by decide +kernel)

private def st9 : List Sig := [wire61,raw0,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node9 : impossible 8 0 st9 := by_search (by decide +kernel)

private def st10 : List Sig := [wire61,wire0,raw0,raw1,raw2,raw3,raw5,raw6,raw7]

private theorem node10 : impossible 8 0 st10 := rectReject 8 st10 4 3 7 2 0 14 3 49 (by decide +kernel)

private def st11 : List Sig := [wire61,raw4,raw0,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node11 : impossible 8 0 st11 := by_search (by decide +kernel)

private def st12 : List Sig := [wire62,raw5,raw0,raw1,raw2,raw3,raw4,raw6,raw7]

private theorem node12 : impossible 8 0 st12 := rectReject 8 st12 2 1 35 0 1 0 2 28 (by decide +kernel)

private def st13 : List Sig := [wire63,raw0,raw1,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node13 : impossible 8 0 st13 := by_search (by decide +kernel)

private def st14 : List Sig := [wire63,wire0,raw0,raw1,raw2,raw3,raw4,raw6,raw7]

private theorem node14 : impossible 8 0 st14 := rectReject 8 st14 2 0 35 0 1 42 2 28 (by decide +kernel)

private def st15 : List Sig := [wire63,raw5,raw0,raw1,raw2,raw3,raw4,raw6,raw7]

private theorem node15 : impossible 8 0 st15 := rectReject 8 st15 4 3 7 2 0 14 3 49 (by decide +kernel)

private def st16 : List Sig := [wire64,raw6,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

private theorem node16 : impossible 8 0 st16 := rectReject 8 st16 3 2 0 4 2 7 0 42 (by decide +kernel)

private def st17 : List Sig := [wire65,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node17 : impossible 8 0 st17 := by_search (by decide +kernel)

private def st18 : List Sig := [wire65,wire0,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

private theorem node18 : impossible 8 0 st18 := rectReject 8 st18 4 3 7 2 0 14 3 49 (by decide +kernel)

private def st19 : List Sig := [wire65,raw6,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node19 : impossible 8 0 st19 := by_search (by decide +kernel)

private def st20 : List Sig := [wire66,raw7,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

private theorem node20 : impossible 8 0 st20 := rectReject 8 st20 3 2 0 4 2 7 0 42 (by decide +kernel)

private def st21 : List Sig := [wire67,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node21 : impossible 8 0 st21 := by_search (by decide +kernel)

private def st22 : List Sig := [wire67,wire0,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

private theorem node22 : impossible 8 0 st22 := rectReject 8 st22 4 3 7 2 0 14 3 49 (by decide +kernel)

private def st23 : List Sig := [wire67,raw7,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node23 : impossible 8 0 st23 := by_search (by decide +kernel)

private def st24 : List Sig := [wire10,raw0,wire0,raw1,raw2,raw3,raw4,raw5,raw7]

private theorem node24 : impossible 8 0 st24 := rectReject 8 st24 4 3 7 2 0 14 3 49 (by decide +kernel)

private def st25 : List Sig := [wire13,raw0,wire0,raw1,raw2,raw3,raw4,raw5,raw6]

private theorem node25 : impossible 8 0 st25 := rectReject 8 st25 4 3 7 2 0 14 3 49 (by decide +kernel)

private def st26 : List Sig := [wire23,raw1,wire0,raw0,raw2,raw3,raw4,raw5,raw7]

private theorem node26 : impossible 8 0 st26 := rectReject 8 st26 4 1 7 6 0 14 4 49 (by decide +kernel)

private def st27 : List Sig := [wire24,raw1,wire0,raw0,raw2,raw3,raw4,raw5,raw6]

private theorem node27 : impossible 8 0 st27 := rectReject 8 st27 5 4 14 0 3 21 1 7 (by decide +kernel)

private def st28 : List Sig := [wire35,raw2,wire0,raw0,raw1,raw3,raw4,raw5,raw6]

private theorem node28 : impossible 8 0 st28 := rectReject 8 st28 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st29 : List Sig := [wire51,raw5,wire0,raw0,raw1,raw2,raw3,raw4,raw7]

private theorem node29 : impossible 8 0 st29 := rectReject 8 st29 5 4 7 2 0 14 3 49 (by decide +kernel)

private def st30 : List Sig := [wire0,raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node30 : impossible 9 0 st30 := by
  apply reject_branch 8 0 st30 [] [st0,st1,st2,st3,st4,st5,st6,st7,st8,st9,st10,st11,st12,st13,st14,st15,st16,st17,st18,st19,st20,st21,st22,st23,st24,st25,st26,st27,st28,st29]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node0
    · exact node1
    · exact node2
    · exact node3
    · exact node4
    · exact node5
    · exact node6
    · exact node7
    · exact node8
    · exact node9
    · exact node10
    · exact node11
    · exact node12
    · exact node13
    · exact node14
    · exact node15
    · exact node16
    · exact node17
    · exact node18
    · exact node19
    · exact node20
    · exact node21
    · exact node22
    · exact node23
    · exact node24
    · exact node25
    · exact node26
    · exact node27
    · exact node28
    · exact node29
  · decide +kernel

private def st31 : List Sig := [wire68,raw2,raw0,raw1,raw3,raw4,raw5,raw6,raw7]

private theorem node31 : impossible 8 0 st31 := rectReject 8 st31 3 2 0 4 2 49 0 42 (by decide +kernel)

private def st32 : List Sig := [wire69,raw2,raw0,raw1,raw3,raw4,raw5,raw6,raw7]

private theorem node32 : impossible 8 0 st32 := rectReject 8 st32 3 1 7 2 3 0 0 14 (by decide +kernel)

private def st33 : List Sig := [wire70,raw3,raw0,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node33 : impossible 8 0 st33 := by_search (by decide +kernel)

private def st34 : List Sig := [wire71,raw3,raw0,raw1,raw2,raw4,raw5,raw6,raw7]

private theorem node34 : impossible 8 0 st34 := rectReject 8 st34 3 2 0 6 2 49 0 35 (by decide +kernel)

private def st35 : List Sig := [wire72,raw4,raw0,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node35 : impossible 8 0 st35 := by_search (by decide +kernel)

private def st36 : List Sig := [wire73,raw4,raw0,raw1,raw2,raw3,raw5,raw6,raw7]

private theorem node36 : impossible 8 0 st36 := rectReject 8 st36 3 2 0 4 2 7 0 42 (by decide +kernel)

private def st37 : List Sig := [wire74,raw5,raw0,raw1,raw2,raw3,raw4,raw6,raw7]

private theorem node37 : impossible 8 0 st37 := rectReject 8 st37 3 2 0 4 2 7 0 42 (by decide +kernel)

private def st38 : List Sig := [wire75,raw5,raw0,raw1,raw2,raw3,raw4,raw6,raw7]

private theorem node38 : impossible 8 0 st38 := rectReject 8 st38 2 1 35 0 1 0 2 28 (by decide +kernel)

private def st39 : List Sig := [wire76,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node39 : impossible 8 0 st39 := by_search (by decide +kernel)

private def st40 : List Sig := [wire76,wire1,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

private theorem node40 : impossible 8 0 st40 := rectReject 8 st40 4 3 7 2 0 14 3 0 (by decide +kernel)

private def st41 : List Sig := [wire76,raw6,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node41 : impossible 8 0 st41 := by_search (by decide +kernel)

private def st42 : List Sig := [wire77,raw6,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node42 : impossible 8 0 st42 := by_search (by decide +kernel)

private def st43 : List Sig := [wire78,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node43 : impossible 8 0 st43 := by_search (by decide +kernel)

private def st44 : List Sig := [wire78,wire1,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

private theorem node44 : impossible 8 0 st44 := rectReject 8 st44 4 3 7 2 0 14 3 0 (by decide +kernel)

private def st45 : List Sig := [wire78,raw7,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node45 : impossible 8 0 st45 := by_search (by decide +kernel)

private def st46 : List Sig := [wire79,raw7,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node46 : impossible 8 0 st46 := by_search (by decide +kernel)

private def st47 : List Sig := [wire3,raw2,wire1,raw1,raw3,raw4,raw5,raw6,raw7]

private theorem node47 : impossible 8 0 st47 := rectReject 8 st47 5 4 21 5 1 28 0 14 (by decide +kernel)

private def st48 : List Sig := [wire10,raw0,wire1,raw1,raw2,raw3,raw4,raw5,raw7]

private theorem node48 : impossible 8 0 st48 := rectReject 8 st48 4 3 7 2 0 14 3 0 (by decide +kernel)

private def st49 : List Sig := [wire13,wire1,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node49 : impossible 8 0 st49 := by_search (by decide +kernel)

private def st50 : List Sig := [wire13,raw0,wire1,raw1,raw2,raw3,raw4,raw5,raw6]

private theorem node50 : impossible 8 0 st50 := rectReject 8 st50 4 3 7 2 0 14 3 0 (by decide +kernel)

private def st51 : List Sig := [wire13,raw7,wire1,raw1,raw2,raw3,raw4,raw5,raw6]

private theorem node51 : impossible 8 0 st51 := rectReject 8 st51 4 3 7 2 0 14 3 0 (by decide +kernel)

private def st52 : List Sig := [wire21,raw5,wire1,raw0,raw2,raw3,raw4,raw6,raw7]

private theorem node52 : impossible 8 0 st52 := rectReject 8 st52 4 0 7 2 0 14 3 0 (by decide +kernel)

private def st53 : List Sig := [wire23,wire1,raw0,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node53 : impossible 8 0 st53 := by_search (by decide +kernel)

private def st54 : List Sig := [wire23,raw1,wire1,raw0,raw2,raw3,raw4,raw5,raw7]

private theorem node54 : impossible 8 0 st54 := rectReject 8 st54 5 4 14 0 3 21 1 7 (by decide +kernel)

private def st55 : List Sig := [wire23,raw6,wire1,raw0,raw2,raw3,raw4,raw5,raw7]

private theorem node55 : impossible 8 0 st55 := rectReject 8 st55 4 0 7 2 0 14 3 0 (by decide +kernel)

private def st56 : List Sig := [wire24,raw1,wire1,raw0,raw2,raw3,raw4,raw5,raw6]

private theorem node56 : impossible 8 0 st56 := rectReject 8 st56 4 1 7 2 0 14 3 0 (by decide +kernel)

private def st57 : List Sig := [wire35,raw2,wire1,raw0,raw1,raw3,raw4,raw5,raw6]

private theorem node57 : impossible 8 0 st57 := rectReject 8 st57 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st58 : List Sig := [wire51,raw5,wire1,raw0,raw1,raw2,raw3,raw4,raw7]

private theorem node58 : impossible 8 0 st58 := rectReject 8 st58 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st59 : List Sig := [wire1,raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node59 : impossible 9 0 st59 := by
  apply reject_branch 8 0 st59 [] [st31,st32,st33,st34,st35,st36,st37,st38,st39,st40,st41,st42,st43,st44,st45,st46,st47,st48,st49,st50,st51,st52,st53,st54,st55,st56,st57,st58]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node31
    · exact node32
    · exact node33
    · exact node34
    · exact node35
    · exact node36
    · exact node37
    · exact node38
    · exact node39
    · exact node40
    · exact node41
    · exact node42
    · exact node43
    · exact node44
    · exact node45
    · exact node46
    · exact node47
    · exact node48
    · exact node49
    · exact node50
    · exact node51
    · exact node52
    · exact node53
    · exact node54
    · exact node55
    · exact node56
    · exact node57
    · exact node58
  · decide +kernel

private def st60 : List Sig := [wire2,raw0,raw2,raw1,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node60 : impossible 9 0 st60 := by_search (by decide +kernel)

private def st61 : List Sig := [wire80,raw3,raw0,raw2,raw1,raw4,raw5,raw6,raw7]

private theorem node61 : impossible 8 0 st61 := rectReject 8 st61 4 2 0 4 2 7 0 42 (by decide +kernel)

private def st62 : List Sig := [wire81,raw3,raw0,raw2,raw1,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node62 : impossible 8 0 st62 := by_search (by decide +kernel)

private def st63 : List Sig := [wire82,raw4,raw0,raw2,raw1,raw3,raw5,raw6,raw7]

private theorem node63 : impossible 8 0 st63 := rectReject 8 st63 4 2 0 4 2 7 0 42 (by decide +kernel)

private def st64 : List Sig := [wire83,raw4,raw0,raw2,raw1,raw3,raw5,raw6,raw7]

private theorem node64 : impossible 8 0 st64 := rectReject 8 st64 4 2 0 4 2 7 0 42 (by decide +kernel)

private def st65 : List Sig := [wire84,raw5,raw0,raw2,raw1,raw3,raw4,raw6,raw7]

private theorem node65 : impossible 8 0 st65 := rectReject 8 st65 4 2 0 4 2 7 0 42 (by decide +kernel)

private def st66 : List Sig := [wire85,raw5,raw0,raw2,raw1,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node66 : impossible 8 0 st66 := by_search (by decide +kernel)

private def st67 : List Sig := [wire86,raw0,raw2,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node67 : impossible 8 0 st67 := by_search (by decide +kernel)

private def st68 : List Sig := [wire86,wire3,raw0,raw2,raw1,raw3,raw4,raw5,raw7]

private theorem node68 : impossible 8 0 st68 := rectReject 8 st68 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st69 : List Sig := [wire86,raw6,raw0,raw2,raw1,raw3,raw4,raw5,raw7]

private theorem node69 : impossible 8 0 st69 := rectReject 8 st69 4 2 0 4 2 7 0 42 (by decide +kernel)

private def st70 : List Sig := [wire87,raw6,raw0,raw2,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node70 : impossible 8 0 st70 := by_search (by decide +kernel)

private def st71 : List Sig := [wire88,raw7,raw0,raw2,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node71 : impossible 8 0 st71 := by_search (by decide +kernel)

private def st72 : List Sig := [wire89,raw0,raw2,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node72 : impossible 8 0 st72 := by_search (by decide +kernel)

private def st73 : List Sig := [wire89,wire3,raw0,raw2,raw1,raw3,raw4,raw5,raw6]

private theorem node73 : impossible 8 0 st73 := rectReject 8 st73 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st74 : List Sig := [wire89,raw7,raw0,raw2,raw1,raw3,raw4,raw5,raw6]

private theorem node74 : impossible 8 0 st74 := rectReject 8 st74 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st75 : List Sig := [wire1,raw1,wire3,raw2,raw3,raw4,raw5,raw6,raw7]

private theorem node75 : impossible 8 0 st75 := rectReject 8 st75 5 4 21 5 1 28 0 14 (by decide +kernel)

private def st76 : List Sig := [wire5,raw3,wire3,raw2,raw1,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node76 : impossible 8 0 st76 := by_search (by decide +kernel)

private def st77 : List Sig := [wire10,raw0,wire3,raw2,raw1,raw3,raw4,raw5,raw7]

private theorem node77 : impossible 8 0 st77 := rectReject 8 st77 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st78 : List Sig := [wire13,raw0,wire3,raw2,raw1,raw3,raw4,raw5,raw6]

private theorem node78 : impossible 8 0 st78 := rectReject 8 st78 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st79 : List Sig := [wire26,raw3,wire3,raw0,raw1,raw4,raw5,raw6,raw7]

private theorem node79 : impossible 8 0 st79 := rectReject 8 st79 6 3 35 4 2 28 5 42 (by decide +kernel)

private def st80 : List Sig := [wire29,raw4,wire3,raw0,raw1,raw3,raw5,raw6,raw7]

private theorem node80 : impossible 8 0 st80 := rectReject 8 st80 6 3 35 4 2 28 5 42 (by decide +kernel)

private def st81 : List Sig := [wire31,raw5,wire3,raw0,raw1,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node81 : impossible 8 0 st81 := by_search (by decide +kernel)

private def st82 : List Sig := [wire33,raw6,wire3,raw0,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node82 : impossible 8 0 st82 := by_search (by decide +kernel)

private def st83 : List Sig := [wire35,raw2,wire3,raw0,raw1,raw3,raw4,raw5,raw6]

private theorem node83 : impossible 8 0 st83 := rectReject 8 st83 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st84 : List Sig := [wire90,raw1,raw0,raw2,raw3,raw4,raw5,raw6,raw7]

private theorem node84 : impossible 8 0 st84 := rectReject 8 st84 5 4 21 5 1 28 0 14 (by decide +kernel)

private def st85 : List Sig := [wire69,raw1,raw0,raw2,raw3,raw4,raw5,raw6,raw7]

private theorem node85 : impossible 8 0 st85 := rectReject 8 st85 2 1 0 4 0 42 2 7 (by decide +kernel)

private def st86 : List Sig := [wire15,raw1,wire3,raw0,raw3,raw4,raw5,raw6,raw7]

private theorem node86 : impossible 8 0 st86 := rectReject 8 st86 4 2 14 0 3 21 1 7 (by decide +kernel)

private def st87 : List Sig := [wire23,raw1,wire3,raw0,raw2,raw3,raw4,raw5,raw7]

private theorem node87 : impossible 8 0 st87 := rectReject 8 st87 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st88 : List Sig := [wire24,raw1,wire3,raw0,raw2,raw3,raw4,raw5,raw6]

private theorem node88 : impossible 8 0 st88 := rectReject 8 st88 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st89 : List Sig := [wire51,raw5,wire3,raw0,raw2,raw1,raw3,raw4,raw7]

private theorem node89 : impossible 8 0 st89 := rectReject 8 st89 7 6 21 5 1 28 0 14 (by decide +kernel)

private def st90 : List Sig := [wire3,raw0,raw2,raw1,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node90 : impossible 9 0 st90 := by
  apply reject_branch 8 0 st90 [] [st61,st62,st63,st64,st65,st66,st67,st68,st69,st70,st71,st72,st73,st74,st75,st76,st77,st78,st79,st80,st81,st82,st83,st84,st85,st86,st87,st88,st89]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node61
    · exact node62
    · exact node63
    · exact node64
    · exact node65
    · exact node66
    · exact node67
    · exact node68
    · exact node69
    · exact node70
    · exact node71
    · exact node72
    · exact node73
    · exact node74
    · exact node75
    · exact node76
    · exact node77
    · exact node78
    · exact node79
    · exact node80
    · exact node81
    · exact node82
    · exact node83
    · exact node84
    · exact node85
    · exact node86
    · exact node87
    · exact node88
    · exact node89
  · decide +kernel

private def st91 : List Sig := [wire4,raw0,raw3,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node91 : impossible 9 0 st91 := by_search (by decide +kernel)

private def st92 : List Sig := [wire5,raw0,raw3,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node92 : impossible 9 0 st92 := by_search (by decide +kernel)

private def st93 : List Sig := [wire6,raw0,raw4,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node93 : impossible 9 0 st93 := by_search (by decide +kernel)

private def st94 : List Sig := [wire91,raw3,raw0,raw4,raw1,raw2,raw5,raw6,raw7]

private theorem node94 : impossible 8 0 st94 := rectReject 8 st94 4 2 0 4 2 7 0 42 (by decide +kernel)

private def st95 : List Sig := [wire92,raw3,raw0,raw4,raw1,raw2,raw5,raw6,raw7]

private theorem node95 : impossible 8 0 st95 := rectReject 8 st95 4 2 0 4 2 7 0 42 (by decide +kernel)

private def st96 : List Sig := [wire93,raw0,raw4,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node96 : impossible 8 0 st96 := by_search (by decide +kernel)

private def st97 : List Sig := [wire93,wire7,raw0,raw4,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node97 : impossible 8 0 st97 := by_search (by decide +kernel)

private def st98 : List Sig := [wire93,raw5,raw0,raw4,raw1,raw2,raw3,raw6,raw7]

private theorem node98 : impossible 8 0 st98 := rectReject 8 st98 4 2 0 4 2 7 0 42 (by decide +kernel)

private def st99 : List Sig := [wire94,raw5,raw0,raw4,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node99 : impossible 8 0 st99 := by_search (by decide +kernel)

private def st100 : List Sig := [wire95,raw0,raw4,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node100 : impossible 8 0 st100 := by_search (by decide +kernel)

private def st101 : List Sig := [wire95,wire7,raw0,raw4,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node101 : impossible 8 0 st101 := by_search (by decide +kernel)

private def st102 : List Sig := [wire95,raw6,raw0,raw4,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node102 : impossible 8 0 st102 := by_search (by decide +kernel)

private def st103 : List Sig := [wire96,raw6,raw0,raw4,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node103 : impossible 8 0 st103 := by_search (by decide +kernel)

private def st104 : List Sig := [wire97,raw7,raw0,raw4,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node104 : impossible 8 0 st104 := by_search (by decide +kernel)

private def st105 : List Sig := [wire98,raw7,raw0,raw4,raw1,raw2,raw3,raw5,raw6]

private theorem node105 : impossible 8 0 st105 := rectReject 8 st105 4 2 0 4 2 7 0 42 (by decide +kernel)

private def st106 : List Sig := [wire5,raw3,wire7,raw4,raw1,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node106 : impossible 8 0 st106 := by_search (by decide +kernel)

private def st107 : List Sig := [wire9,raw5,wire7,raw4,raw1,raw2,raw3,raw6,raw7]

private theorem node107 : impossible 8 0 st107 := rectReject 8 st107 4 0 0 4 2 7 0 42 (by decide +kernel)

private def st108 : List Sig := [wire10,raw0,wire7,raw4,raw1,raw2,raw3,raw5,raw7]

private theorem node108 : impossible 8 0 st108 := rectReject 8 st108 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st109 : List Sig := [wire13,raw0,wire7,raw4,raw1,raw2,raw3,raw5,raw6]

private theorem node109 : impossible 8 0 st109 := rectReject 8 st109 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st110 : List Sig := [wire42,raw3,wire7,raw0,raw1,raw2,raw5,raw6,raw7]

private theorem node110 : impossible 8 0 st110 := rectReject 8 st110 4 3 0 4 2 7 0 42 (by decide +kernel)

private def st111 : List Sig := [wire45,raw5,wire7,raw0,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node111 : impossible 8 0 st111 := by_search (by decide +kernel)

private def st112 : List Sig := [wire47,raw6,wire7,raw0,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node112 : impossible 8 0 st112 := by_search (by decide +kernel)

private def st113 : List Sig := [wire99,raw1,raw0,raw4,raw2,raw3,raw5,raw6,raw7]

private theorem node113 : impossible 8 0 st113 := rectReject 8 st113 4 1 7 2 0 14 3 49 (by decide +kernel)

private def st114 : List Sig := [wire73,raw1,raw0,raw4,raw2,raw3,raw5,raw6,raw7]

private theorem node114 : impossible 8 0 st114 := rectReject 8 st114 2 1 0 4 0 42 2 7 (by decide +kernel)

private def st115 : List Sig := [wire19,raw1,wire7,raw0,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node115 : impossible 8 0 st115 := by_search (by decide +kernel)

private def st116 : List Sig := [wire23,raw1,wire7,raw0,raw4,raw2,raw3,raw5,raw7]

private theorem node116 : impossible 8 0 st116 := rectReject 8 st116 5 1 7 6 0 14 4 49 (by decide +kernel)

private def st117 : List Sig := [wire24,raw1,wire7,raw0,raw4,raw2,raw3,raw5,raw6]

private theorem node117 : impossible 8 0 st117 := rectReject 8 st117 3 1 0 4 0 42 2 7 (by decide +kernel)

private def st118 : List Sig := [wire100,raw2,raw0,raw4,raw1,raw3,raw5,raw6,raw7]

private theorem node118 : impossible 8 0 st118 := rectReject 8 st118 4 1 7 2 3 0 0 14 (by decide +kernel)

private def st119 : List Sig := [wire83,raw2,raw0,raw4,raw1,raw3,raw5,raw6,raw7]

private theorem node119 : impossible 8 0 st119 := rectReject 8 st119 4 1 7 2 3 0 0 14 (by decide +kernel)

private def st120 : List Sig := [wire29,raw2,wire7,raw0,raw1,raw3,raw5,raw6,raw7]

private theorem node120 : impossible 8 0 st120 := rectReject 8 st120 4 3 0 4 2 7 0 42 (by decide +kernel)

private def st121 : List Sig := [wire35,raw2,wire7,raw0,raw4,raw1,raw3,raw5,raw6]

private theorem node121 : impossible 8 0 st121 := rectReject 8 st121 5 3 0 4 2 7 0 42 (by decide +kernel)

private def st122 : List Sig := [wire51,raw5,wire7,raw0,raw4,raw1,raw2,raw3,raw7]

private theorem node122 : impossible 8 0 st122 := rectReject 8 st122 5 3 0 4 2 7 0 42 (by decide +kernel)

private def st123 : List Sig := [wire7,raw0,raw4,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node123 : impossible 9 0 st123 := by
  apply reject_branch 8 0 st123 [] [st94,st95,st96,st97,st98,st99,st100,st101,st102,st103,st104,st105,st106,st107,st108,st109,st110,st111,st112,st113,st114,st115,st116,st117,st118,st119,st120,st121,st122]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node94
    · exact node95
    · exact node96
    · exact node97
    · exact node98
    · exact node99
    · exact node100
    · exact node101
    · exact node102
    · exact node103
    · exact node104
    · exact node105
    · exact node106
    · exact node107
    · exact node108
    · exact node109
    · exact node110
    · exact node111
    · exact node112
    · exact node113
    · exact node114
    · exact node115
    · exact node116
    · exact node117
    · exact node118
    · exact node119
    · exact node120
    · exact node121
    · exact node122
  · decide +kernel

private def st124 : List Sig := [wire62,raw1,raw0,raw5,raw2,raw3,raw4,raw6,raw7]

private theorem node124 : impossible 8 0 st124 := rectReject 8 st124 2 1 0 4 0 42 2 7 (by decide +kernel)

private def st125 : List Sig := [wire101,raw0,raw5,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node125 : impossible 8 0 st125 := by_search (by decide +kernel)

private def st126 : List Sig := [wire101,wire8,raw0,raw5,raw2,raw3,raw4,raw6,raw7]

private theorem node126 : impossible 8 0 st126 := rectReject 8 st126 2 0 0 4 0 42 2 7 (by decide +kernel)

private def st127 : List Sig := [wire101,raw1,raw0,raw5,raw2,raw3,raw4,raw6,raw7]

private theorem node127 : impossible 8 0 st127 := rectReject 8 st127 5 4 14 0 3 21 1 7 (by decide +kernel)

private def st128 : List Sig := [wire102,raw2,raw0,raw5,raw1,raw3,raw4,raw6,raw7]

private theorem node128 : impossible 8 0 st128 := rectReject 8 st128 3 2 35 0 2 28 1 0 (by decide +kernel)

private def st129 : List Sig := [wire103,raw0,raw5,raw1,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node129 : impossible 8 0 st129 := by_search (by decide +kernel)

private def st130 : List Sig := [wire103,wire8,raw0,raw5,raw1,raw3,raw4,raw6,raw7]

private theorem node130 : impossible 8 0 st130 := rectReject 8 st130 4 0 7 2 3 0 0 14 (by decide +kernel)

private def st131 : List Sig := [wire103,raw2,raw0,raw5,raw1,raw3,raw4,raw6,raw7]

private theorem node131 : impossible 8 0 st131 := rectReject 8 st131 3 2 35 0 3 28 5 0 (by decide +kernel)

private def st132 : List Sig := [wire104,raw3,raw0,raw5,raw1,raw2,raw4,raw6,raw7]

private theorem node132 : impossible 8 0 st132 := rectReject 8 st132 3 2 35 0 2 28 1 0 (by decide +kernel)

private def st133 : List Sig := [wire105,raw0,raw5,raw1,raw2,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node133 : impossible 8 0 st133 := by_search (by decide +kernel)

private def st134 : List Sig := [wire105,wire8,raw0,raw5,raw1,raw2,raw4,raw6,raw7]

private theorem node134 : impossible 8 0 st134 := rectReject 8 st134 4 2 0 4 2 7 0 42 (by decide +kernel)

private def st135 : List Sig := [wire105,raw3,raw0,raw5,raw1,raw2,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node135 : impossible 8 0 st135 := by_search (by decide +kernel)

private def st136 : List Sig := [wire106,raw4,raw0,raw5,raw1,raw2,raw3,raw6,raw7]

private theorem node136 : impossible 8 0 st136 := rectReject 8 st136 3 1 28 2 0 35 1 21 (by decide +kernel)

private def st137 : List Sig := [wire107,raw0,raw5,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node137 : impossible 8 0 st137 := by_search (by decide +kernel)

private def st138 : List Sig := [wire107,wire8,raw0,raw5,raw1,raw2,raw3,raw6,raw7]

private theorem node138 : impossible 8 0 st138 := rectReject 8 st138 4 2 0 4 2 7 0 42 (by decide +kernel)

private def st139 : List Sig := [wire107,raw4,raw0,raw5,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node139 : impossible 8 0 st139 := by_search (by decide +kernel)

private def st140 : List Sig := [wire108,raw6,raw0,raw5,raw1,raw2,raw3,raw4,raw7]

private theorem node140 : impossible 8 0 st140 := rectReject 8 st140 3 2 35 0 2 28 1 0 (by decide +kernel)

private def st141 : List Sig := [wire109,raw0,raw5,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node141 : impossible 8 0 st141 := by_search (by decide +kernel)

private def st142 : List Sig := [wire109,wire8,raw0,raw5,raw1,raw2,raw3,raw4,raw7]

private theorem node142 : impossible 8 0 st142 := rectReject 8 st142 4 2 0 4 2 7 0 42 (by decide +kernel)

private def st143 : List Sig := [wire109,raw6,raw0,raw5,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node143 : impossible 8 0 st143 := by_search (by decide +kernel)

private def st144 : List Sig := [wire110,raw7,raw0,raw5,raw1,raw2,raw3,raw4,raw6]

private theorem node144 : impossible 8 0 st144 := rectReject 8 st144 3 2 35 0 2 28 1 0 (by decide +kernel)

private def st145 : List Sig := [wire111,raw0,raw5,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node145 : impossible 8 0 st145 := by_search (by decide +kernel)

private def st146 : List Sig := [wire111,wire8,raw0,raw5,raw1,raw2,raw3,raw4,raw6]

private theorem node146 : impossible 8 0 st146 := rectReject 8 st146 4 2 0 4 2 7 0 42 (by decide +kernel)

private def st147 : List Sig := [wire111,raw7,raw0,raw5,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node147 : impossible 8 0 st147 := by_search (by decide +kernel)

private def st148 : List Sig := [wire10,raw0,wire8,raw5,raw1,raw2,raw3,raw4,raw7]

private theorem node148 : impossible 8 0 st148 := rectReject 8 st148 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st149 : List Sig := [wire13,raw0,wire8,raw5,raw1,raw2,raw3,raw4,raw6]

private theorem node149 : impossible 8 0 st149 := rectReject 8 st149 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st150 : List Sig := [wire51,raw5,wire8,raw0,raw1,raw2,raw3,raw4,raw7]

private theorem node150 : impossible 8 0 st150 := rectReject 8 st150 4 3 0 4 2 7 0 42 (by decide +kernel)

private def st151 : List Sig := [wire23,raw1,wire8,raw0,raw5,raw2,raw3,raw4,raw7]

private theorem node151 : impossible 8 0 st151 := rectReject 8 st151 5 1 7 6 0 14 4 49 (by decide +kernel)

private def st152 : List Sig := [wire24,raw1,wire8,raw0,raw5,raw2,raw3,raw4,raw6]

private theorem node152 : impossible 8 0 st152 := rectReject 8 st152 3 1 0 4 0 42 2 7 (by decide +kernel)

private def st153 : List Sig := [wire35,raw2,wire8,raw0,raw5,raw1,raw3,raw4,raw6]

private theorem node153 : impossible 8 0 st153 := rectReject 8 st153 5 3 0 4 2 7 0 42 (by decide +kernel)

private def st154 : List Sig := [wire37,raw3,wire8,raw0,raw1,raw2,raw4,raw6,raw7]

private theorem node154 : impossible 8 0 st154 := rectReject 8 st154 4 3 0 4 2 7 0 42 (by decide +kernel)

private def st155 : List Sig := [wire44,raw4,wire8,raw0,raw1,raw2,raw3,raw6,raw7]

private theorem node155 : impossible 8 0 st155 := rectReject 8 st155 4 3 0 4 2 7 0 42 (by decide +kernel)

private def st156 : List Sig := [wire8,raw0,raw5,raw1,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node156 : impossible 9 0 st156 := by
  apply reject_branch 8 0 st156 [] [st124,st125,st126,st127,st128,st129,st130,st131,st132,st133,st134,st135,st136,st137,st138,st139,st140,st141,st142,st143,st144,st145,st146,st147,st148,st149,st150,st151,st152,st153,st154,st155]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node124
    · exact node125
    · exact node126
    · exact node127
    · exact node128
    · exact node129
    · exact node130
    · exact node131
    · exact node132
    · exact node133
    · exact node134
    · exact node135
    · exact node136
    · exact node137
    · exact node138
    · exact node139
    · exact node140
    · exact node141
    · exact node142
    · exact node143
    · exact node144
    · exact node145
    · exact node146
    · exact node147
    · exact node148
    · exact node149
    · exact node150
    · exact node151
    · exact node152
    · exact node153
    · exact node154
    · exact node155
  · decide +kernel

private def st157 : List Sig := [wire112,raw0,raw5,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node157 : impossible 8 0 st157 := by_search (by decide +kernel)

private def st158 : List Sig := [wire112,wire9,raw0,raw5,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node158 : impossible 8 0 st158 := by_search (by decide +kernel)

private def st159 : List Sig := [wire112,raw6,raw0,raw5,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node159 : impossible 8 0 st159 := by_search (by decide +kernel)

private def st160 : List Sig := [wire113,raw6,raw0,raw5,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node160 : impossible 8 0 st160 := by_search (by decide +kernel)

private def st161 : List Sig := [wire114,raw7,raw0,raw5,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node161 : impossible 8 0 st161 := by_search (by decide +kernel)

private def st162 : List Sig := [wire115,raw7,raw0,raw5,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node162 : impossible 8 0 st162 := by_search (by decide +kernel)

private def st163 : List Sig := [wire7,raw4,wire9,raw5,raw1,raw2,raw3,raw6,raw7]

private theorem node163 : impossible 8 0 st163 := rectReject 8 st163 4 0 0 5 2 7 1 35 (by decide +kernel)

private def st164 : List Sig := [wire10,raw0,wire9,raw5,raw1,raw2,raw3,raw4,raw7]

private theorem node164 : impossible 8 0 st164 := rectReject 8 st164 4 1 0 5 2 7 1 35 (by decide +kernel)

private def st165 : List Sig := [wire13,raw0,wire9,raw5,raw1,raw2,raw3,raw4,raw6]

private theorem node165 : impossible 8 0 st165 := rectReject 8 st165 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st166 : List Sig := [wire51,wire9,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node166 : impossible 8 0 st166 := by_search (by decide +kernel)

private def st167 : List Sig := [wire51,raw5,wire9,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node167 : impossible 8 0 st167 := by_search (by decide +kernel)

private def st168 : List Sig := [wire51,raw6,wire9,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node168 : impossible 8 0 st168 := by_search (by decide +kernel)

private def st169 : List Sig := [wire116,raw1,raw0,raw5,raw2,raw3,raw4,raw6,raw7]

private theorem node169 : impossible 8 0 st169 := rectReject 8 st169 3 2 35 0 2 28 1 42 (by decide +kernel)

private def st170 : List Sig := [wire75,raw1,raw0,raw5,raw2,raw3,raw4,raw6,raw7]

private theorem node170 : impossible 8 0 st170 := rectReject 8 st170 2 1 0 5 0 35 2 7 (by decide +kernel)

private def st171 : List Sig := [wire21,raw1,wire9,raw0,raw2,raw3,raw4,raw6,raw7]

private theorem node171 : impossible 8 0 st171 := rectReject 8 st171 4 1 7 6 0 14 5 49 (by decide +kernel)

private def st172 : List Sig := [wire23,raw1,wire9,raw0,raw5,raw2,raw3,raw4,raw7]

private theorem node172 : impossible 8 0 st172 := rectReject 8 st172 5 1 7 6 0 14 4 49 (by decide +kernel)

private def st173 : List Sig := [wire24,raw1,wire9,raw0,raw5,raw2,raw3,raw4,raw6]

private theorem node173 : impossible 8 0 st173 := rectReject 8 st173 3 1 0 5 1 35 2 7 (by decide +kernel)

private def st174 : List Sig := [wire117,raw2,raw0,raw5,raw1,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node174 : impossible 8 0 st174 := by_search (by decide +kernel)

private def st175 : List Sig := [wire85,raw2,raw0,raw5,raw1,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node175 : impossible 8 0 st175 := by_search (by decide +kernel)

private def st176 : List Sig := [wire35,raw2,wire9,raw0,raw5,raw1,raw3,raw4,raw6]

private theorem node176 : impossible 8 0 st176 := rectReject 8 st176 5 3 0 5 2 7 1 35 (by decide +kernel)

private def st177 : List Sig := [wire118,raw3,raw0,raw5,raw1,raw2,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node177 : impossible 8 0 st177 := by_search (by decide +kernel)

private def st178 : List Sig := [wire119,raw3,raw0,raw5,raw1,raw2,raw4,raw6,raw7]

private theorem node178 : impossible 8 0 st178 := rectReject 8 st178 4 2 0 5 2 7 1 35 (by decide +kernel)

private def st179 : List Sig := [wire120,raw4,raw0,raw5,raw1,raw2,raw3,raw6,raw7]

private theorem node179 : impossible 8 0 st179 := rectReject 8 st179 4 2 0 4 2 7 0 42 (by decide +kernel)

private def st180 : List Sig := [wire94,raw4,raw0,raw5,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node180 : impossible 8 0 st180 := by_search (by decide +kernel)

private def st181 : List Sig := [wire9,raw0,raw5,raw1,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node181 : impossible 9 0 st181 := by
  apply reject_branch 8 0 st181 [] [st157,st158,st159,st160,st161,st162,st163,st164,st165,st166,st167,st168,st169,st170,st171,st172,st173,st174,st175,st176,st177,st178,st179,st180]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node157
    · exact node158
    · exact node159
    · exact node160
    · exact node161
    · exact node162
    · exact node163
    · exact node164
    · exact node165
    · exact node166
    · exact node167
    · exact node168
    · exact node169
    · exact node170
    · exact node171
    · exact node172
    · exact node173
    · exact node174
    · exact node175
    · exact node176
    · exact node177
    · exact node178
    · exact node179
    · exact node180
  · decide +kernel

private def st182 : List Sig := [wire64,wire10,raw1,raw0,raw2,raw3,raw4,raw5,raw7]

private theorem node182 : impossible 8 0 st182 := rectReject 8 st182 3 2 0 5 0 35 2 7 (by decide +kernel)

private def st183 : List Sig := [wire131,wire121,raw2,raw0,raw3,raw4,raw5,raw7]

private theorem node183 : impossible 7 0 st183 := rectReject 7 st183 3 1 0 5 0 35 2 49 (by decide +kernel)

private def st184 : List Sig := [wire132,wire121,raw2,raw0,raw3,raw4,raw5,raw7]

private theorem node184 : impossible 7 0 st184 := rectReject 7 st184 3 1 0 5 0 35 3 7 (by decide +kernel)

private def st185 : List Sig := [wire133,wire121,raw3,raw0,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node185 : impossible 7 0 st185 := by_search (by decide +kernel)

private def st186 : List Sig := [wire134,wire121,raw3,raw0,raw2,raw4,raw5,raw7]

private theorem node186 : impossible 7 0 st186 := rectReject 7 st186 3 1 0 6 0 35 2 49 (by decide +kernel)

private def st187 : List Sig := [wire135,wire121,raw4,raw0,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node187 : impossible 7 0 st187 := by_search (by decide +kernel)

private def st188 : List Sig := [wire136,wire121,raw4,raw0,raw2,raw3,raw5,raw7]

private theorem node188 : impossible 7 0 st188 := rectReject 7 st188 5 4 14 0 3 21 1 7 (by decide +kernel)

private def st189 : List Sig := [wire137,wire121,raw5,raw0,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node189 : impossible 7 0 st189 := by_search (by decide +kernel)

private def st190 : List Sig := [wire138,wire121,raw5,raw0,raw2,raw3,raw4,raw7]

private theorem node190 : impossible 7 0 st190 := rectReject 7 st190 4 1 7 6 0 14 5 49 (by decide +kernel)

private def st191 : List Sig := [wire139,wire121,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node191 : impossible 7 0 st191 := by_search (by decide +kernel)

private def st192 : List Sig := [wire139,wire121,raw7,raw0,raw2,raw3,raw4,raw5]

private theorem node192 : impossible 7 0 st192 := rectReject 7 st192 3 1 0 5 0 35 2 7 (by decide +kernel)

private def st193 : List Sig := [wire140,wire121,raw7,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node193 : impossible 7 0 st193 := by_search (by decide +kernel)

private def st194 : List Sig := [wire141,raw0,wire121,raw2,raw3,raw4,raw5,raw7]

private theorem node194 : impossible 7 0 st194 := rectReject 7 st194 3 2 7 2 0 14 3 49 (by decide +kernel)

private def st195 : List Sig := [wire1,raw0,wire121,raw2,raw3,raw4,raw5,raw7]

private theorem node195 : impossible 7 0 st195 := rectReject 7 st195 3 2 7 2 0 14 3 0 (by decide +kernel)

private def st196 : List Sig := [wire2,raw0,raw2,wire121,raw3,raw4,raw5,raw7]

private theorem node196 : impossible 7 0 st196 := rectReject 7 st196 3 1 0 5 2 7 0 35 (by decide +kernel)

private def st197 : List Sig := [wire3,raw0,raw2,wire121,raw3,raw4,raw5,raw7]

private theorem node197 : impossible 7 0 st197 := rectReject 7 st197 5 4 21 5 1 28 0 14 (by decide +kernel)

private def st198 : List Sig := [wire4,raw0,raw3,wire121,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node198 : impossible 7 0 st198 := by_search (by decide +kernel)

private def st199 : List Sig := [wire5,raw0,raw3,wire121,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node199 : impossible 7 0 st199 := by_search (by decide +kernel)

private def st200 : List Sig := [wire6,raw0,raw4,wire121,raw2,raw3,raw5,raw7]

private theorem node200 : impossible 7 0 st200 := rectReject 7 st200 3 1 0 5 2 7 0 35 (by decide +kernel)

private def st201 : List Sig := [wire7,raw0,raw4,wire121,raw2,raw3,raw5,raw7]

private theorem node201 : impossible 7 0 st201 := rectReject 7 st201 4 3 7 2 0 14 3 0 (by decide +kernel)

private def st202 : List Sig := [wire8,raw0,raw5,wire121,raw2,raw3,raw4,raw7]

private theorem node202 : impossible 7 0 st202 := rectReject 7 st202 4 3 7 2 0 14 3 0 (by decide +kernel)

private def st203 : List Sig := [wire9,raw0,raw5,wire121,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node203 : impossible 7 0 st203 := by_search (by decide +kernel)

private def st204 : List Sig := [wire12,raw0,raw7,wire121,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node204 : impossible 7 0 st204 := by_search (by decide +kernel)

private def st205 : List Sig := [wire13,raw0,wire121,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node205 : impossible 7 0 st205 := by_search (by decide +kernel)

private def st206 : List Sig := [wire13,raw0,raw7,wire121,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node206 : impossible 7 0 st206 := by_search (by decide +kernel)

private def st207 : List Sig := [wire26,raw2,raw3,wire121,raw0,raw4,raw5,raw7]

private theorem node207 : impossible 7 0 st207 := rectReject 7 st207 4 3 0 5 0 35 2 7 (by decide +kernel)

private def st208 : List Sig := [wire27,raw2,raw3,wire121,raw0,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node208 : impossible 7 0 st208 := by_search (by decide +kernel)

private def st209 : List Sig := [wire28,raw2,raw4,wire121,raw0,raw3,raw5,raw7]

private theorem node209 : impossible 7 0 st209 := rectReject 7 st209 3 1 7 2 3 0 0 14 (by decide +kernel)

private def st210 : List Sig := [wire29,raw2,raw4,wire121,raw0,raw3,raw5,raw7]

private theorem node210 : impossible 7 0 st210 := rectReject 7 st210 4 3 0 5 0 35 2 7 (by decide +kernel)

private def st211 : List Sig := [wire30,raw2,raw5,wire121,raw0,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node211 : impossible 7 0 st211 := by_search (by decide +kernel)

private def st212 : List Sig := [wire31,raw2,raw5,wire121,raw0,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node212 : impossible 7 0 st212 := by_search (by decide +kernel)

private def st213 : List Sig := [wire34,raw2,raw7,wire121,raw0,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node213 : impossible 7 0 st213 := by_search (by decide +kernel)

private def st214 : List Sig := [wire35,raw2,wire121,raw0,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node214 : impossible 7 0 st214 := by_search (by decide +kernel)

private def st215 : List Sig := [wire35,raw2,raw7,wire121,raw0,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node215 : impossible 7 0 st215 := by_search (by decide +kernel)

private def st216 : List Sig := [wire36,raw3,raw5,wire121,raw0,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node216 : impossible 7 0 st216 := by_search (by decide +kernel)

private def st217 : List Sig := [wire37,raw3,raw5,wire121,raw0,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node217 : impossible 7 0 st217 := by_search (by decide +kernel)

private def st218 : List Sig := [wire40,raw3,raw7,wire121,raw0,raw2,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node218 : impossible 7 0 st218 := by_search (by decide +kernel)

private def st219 : List Sig := [wire41,raw3,raw7,wire121,raw0,raw2,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node219 : impossible 7 0 st219 := by_search (by decide +kernel)

private def st220 : List Sig := [wire42,raw4,raw3,wire121,raw0,raw2,raw5,raw7]

private theorem node220 : impossible 7 0 st220 := rectReject 7 st220 4 3 0 5 0 35 2 7 (by decide +kernel)

private def st221 : List Sig := [wire43,raw4,raw3,wire121,raw0,raw2,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node221 : impossible 7 0 st221 := by_search (by decide +kernel)

private def st222 : List Sig := [wire44,raw4,raw5,wire121,raw0,raw2,raw3,raw7]

private theorem node222 : impossible 7 0 st222 := rectReject 7 st222 4 3 0 5 0 35 2 7 (by decide +kernel)

private def st223 : List Sig := [wire45,raw4,raw5,wire121,raw0,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node223 : impossible 7 0 st223 := by_search (by decide +kernel)

private def st224 : List Sig := [wire48,raw4,raw7,wire121,raw0,raw2,raw3,raw5]

private theorem node224 : impossible 7 0 st224 := rectReject 7 st224 4 3 0 5 0 35 2 7 (by decide +kernel)

private def st225 : List Sig := [wire49,raw4,raw7,wire121,raw0,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node225 : impossible 7 0 st225 := by_search (by decide +kernel)

private def st226 : List Sig := [wire52,raw5,raw7,wire121,raw0,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node226 : impossible 7 0 st226 := by_search (by decide +kernel)

private def st227 : List Sig := [wire53,raw5,raw7,wire121,raw0,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node227 : impossible 7 0 st227 := by_search (by decide +kernel)

private def st228 : List Sig := [wire121,raw0,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node228 : impossible 8 0 st228 := by
  apply reject_branch 7 0 st228 [] [st183,st184,st185,st186,st187,st188,st189,st190,st191,st192,st193,st194,st195,st196,st197,st198,st199,st200,st201,st202,st203,st204,st205,st206,st207,st208,st209,st210,st211,st212,st213,st214,st215,st216,st217,st218,st219,st220,st221,st222,st223,st224,st225,st226,st227]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node183
    · exact node184
    · exact node185
    · exact node186
    · exact node187
    · exact node188
    · exact node189
    · exact node190
    · exact node191
    · exact node192
    · exact node193
    · exact node194
    · exact node195
    · exact node196
    · exact node197
    · exact node198
    · exact node199
    · exact node200
    · exact node201
    · exact node202
    · exact node203
    · exact node204
    · exact node205
    · exact node206
    · exact node207
    · exact node208
    · exact node209
    · exact node210
    · exact node211
    · exact node212
    · exact node213
    · exact node214
    · exact node215
    · exact node216
    · exact node217
    · exact node218
    · exact node219
    · exact node220
    · exact node221
    · exact node222
    · exact node223
    · exact node224
    · exact node225
    · exact node226
    · exact node227
  · decide +kernel

private def st229 : List Sig := [wire121,wire10,raw0,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node229 : impossible 8 0 st229 := by_search (by decide +kernel)

private def st230 : List Sig := [wire121,raw1,raw0,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node230 : impossible 8 0 st230 := by_search (by decide +kernel)

private def st231 : List Sig := [wire121,wire10,raw1,raw0,raw2,raw3,raw4,raw5,raw7]

private theorem node231 : impossible 8 0 st231 := rectReject 8 st231 5 4 14 0 3 21 1 7 (by decide +kernel)

private def st232 : List Sig := [wire122,wire10,raw2,raw0,raw1,raw3,raw4,raw5,raw7]

private theorem node232 : impossible 8 0 st232 := rectReject 8 st232 4 2 7 2 3 0 0 14 (by decide +kernel)

private def st233 : List Sig := [wire123,wire10,raw0,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node233 : impossible 8 0 st233 := by_search (by decide +kernel)

private def st234 : List Sig := [wire123,wire10,raw2,raw0,raw1,raw3,raw4,raw5,raw7]

private theorem node234 : impossible 8 0 st234 := rectReject 8 st234 4 3 0 5 2 7 0 35 (by decide +kernel)

private def st235 : List Sig := [wire124,wire10,raw3,raw0,raw1,raw2,raw4,raw5,raw7]

private theorem node235 : impossible 8 0 st235 := rectReject 8 st235 4 3 0 5 2 7 0 35 (by decide +kernel)

private def st236 : List Sig := [wire125,wire10,raw0,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node236 : impossible 8 0 st236 := by_search (by decide +kernel)

private def st237 : List Sig := [wire125,wire10,raw3,raw0,raw1,raw2,raw4,raw5,raw7]

private theorem node237 : impossible 8 0 st237 := rectReject 8 st237 4 3 0 5 2 7 0 35 (by decide +kernel)

private def st238 : List Sig := [wire126,wire10,raw4,raw0,raw1,raw2,raw3,raw5,raw7]

private theorem node238 : impossible 8 0 st238 := rectReject 8 st238 4 3 0 5 2 7 0 35 (by decide +kernel)

private def st239 : List Sig := [wire127,wire10,raw0,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node239 : impossible 8 0 st239 := by_search (by decide +kernel)

private def st240 : List Sig := [wire127,wire10,raw4,raw0,raw1,raw2,raw3,raw5,raw7]

private theorem node240 : impossible 8 0 st240 := rectReject 8 st240 4 3 0 5 2 7 0 35 (by decide +kernel)

private def st241 : List Sig := [wire108,wire10,raw5,raw0,raw1,raw2,raw3,raw4,raw7]

private theorem node241 : impossible 8 0 st241 := rectReject 8 st241 3 2 35 0 1 0 2 28 (by decide +kernel)

private def st242 : List Sig := [wire142,wire128,raw7,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node242 : impossible 7 0 st242 := by_search (by decide +kernel)

private def st243 : List Sig := [wire143,wire128,raw7,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node243 : impossible 7 0 st243 := by_search (by decide +kernel)

private def st244 : List Sig := [wire144,raw0,wire128,raw1,raw2,raw3,raw4,raw7]

private theorem node244 : impossible 7 0 st244 := rectReject 7 st244 4 3 7 2 0 14 3 0 (by decide +kernel)

private def st245 : List Sig := [wire9,raw0,wire128,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node245 : impossible 7 0 st245 := by_search (by decide +kernel)

private def st246 : List Sig := [wire0,raw0,raw1,wire128,raw2,raw3,raw4,raw7]

private theorem node246 : impossible 7 0 st246 := rectReject 7 st246 4 2 7 2 0 14 3 49 (by decide +kernel)

private def st247 : List Sig := [wire1,raw0,raw1,wire128,raw2,raw3,raw4,raw7]

private theorem node247 : impossible 7 0 st247 := rectReject 7 st247 3 1 35 0 2 28 1 0 (by decide +kernel)

private def st248 : List Sig := [wire2,raw0,raw2,wire128,raw1,raw3,raw4,raw7]

private theorem node248 : impossible 7 0 st248 := rectReject 7 st248 3 1 35 0 2 28 1 0 (by decide +kernel)

private def st249 : List Sig := [wire3,raw0,raw2,wire128,raw1,raw3,raw4,raw7]

private theorem node249 : impossible 7 0 st249 := rectReject 7 st249 6 3 28 2 1 21 0 35 (by decide +kernel)

private def st250 : List Sig := [wire4,raw0,raw3,wire128,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node250 : impossible 7 0 st250 := by_search (by decide +kernel)

private def st251 : List Sig := [wire5,raw0,raw3,wire128,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node251 : impossible 7 0 st251 := by_search (by decide +kernel)

private def st252 : List Sig := [wire6,raw0,raw4,wire128,raw1,raw2,raw3,raw7]

private theorem node252 : impossible 7 0 st252 := rectReject 7 st252 3 1 35 0 2 28 1 0 (by decide +kernel)

private def st253 : List Sig := [wire7,raw0,raw4,wire128,raw1,raw2,raw3,raw7]

private theorem node253 : impossible 7 0 st253 := rectReject 7 st253 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st254 : List Sig := [wire12,raw0,raw7,wire128,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node254 : impossible 7 0 st254 := by_search (by decide +kernel)

private def st255 : List Sig := [wire13,raw0,wire128,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node255 : impossible 7 0 st255 := by_search (by decide +kernel)

private def st256 : List Sig := [wire13,raw0,raw7,wire128,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node256 : impossible 7 0 st256 := by_search (by decide +kernel)

private def st257 : List Sig := [wire145,raw1,wire128,raw0,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node257 : impossible 7 0 st257 := by_search (by decide +kernel)

private def st258 : List Sig := [wire138,raw1,wire128,raw0,raw2,raw3,raw4,raw7]

private theorem node258 : impossible 7 0 st258 := rectReject 7 st258 4 1 7 6 0 14 5 49 (by decide +kernel)

private def st259 : List Sig := [wire14,raw1,raw2,wire128,raw0,raw3,raw4,raw7]

private theorem node259 : impossible 7 0 st259 := rectReject 7 st259 4 1 0 5 0 35 2 49 (by decide +kernel)

private def st260 : List Sig := [wire15,raw1,raw2,wire128,raw0,raw3,raw4,raw7]

private theorem node260 : impossible 7 0 st260 := rectReject 7 st260 4 1 0 5 0 35 3 7 (by decide +kernel)

private def st261 : List Sig := [wire16,raw1,raw3,wire128,raw0,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node261 : impossible 7 0 st261 := by_search (by decide +kernel)

private def st262 : List Sig := [wire17,raw1,raw3,wire128,raw0,raw2,raw4,raw7]

private theorem node262 : impossible 7 0 st262 := rectReject 7 st262 4 1 0 6 0 35 2 49 (by decide +kernel)

private def st263 : List Sig := [wire18,raw1,raw4,wire128,raw0,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node263 : impossible 7 0 st263 := by_search (by decide +kernel)

private def st264 : List Sig := [wire19,raw1,raw4,wire128,raw0,raw2,raw3,raw7]

private theorem node264 : impossible 7 0 st264 := rectReject 7 st264 4 3 35 0 1 0 2 28 (by decide +kernel)

private def st265 : List Sig := [wire24,raw1,wire128,raw0,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node265 : impossible 7 0 st265 := by_search (by decide +kernel)

private def st266 : List Sig := [wire24,raw1,raw7,wire128,raw0,raw2,raw3,raw4]

private theorem node266 : impossible 7 0 st266 := rectReject 7 st266 4 1 0 5 0 35 2 7 (by decide +kernel)

private def st267 : List Sig := [wire25,raw1,raw7,wire128,raw0,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node267 : impossible 7 0 st267 := by_search (by decide +kernel)

private def st268 : List Sig := [wire146,raw2,wire128,raw0,raw1,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node268 : impossible 7 0 st268 := by_search (by decide +kernel)

private def st269 : List Sig := [wire147,raw2,wire128,raw0,raw1,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node269 : impossible 7 0 st269 := by_search (by decide +kernel)

private def st270 : List Sig := [wire26,raw2,raw3,wire128,raw0,raw1,raw4,raw7]

private theorem node270 : impossible 7 0 st270 := rectReject 7 st270 4 3 35 0 1 0 2 28 (by decide +kernel)

private def st271 : List Sig := [wire27,raw2,raw3,wire128,raw0,raw1,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node271 : impossible 7 0 st271 := by_search (by decide +kernel)

private def st272 : List Sig := [wire28,raw2,raw4,wire128,raw0,raw1,raw3,raw7]

private theorem node272 : impossible 7 0 st272 := rectReject 7 st272 3 2 28 2 0 35 1 21 (by decide +kernel)

private def st273 : List Sig := [wire29,raw2,raw4,wire128,raw0,raw1,raw3,raw7]

private theorem node273 : impossible 7 0 st273 := rectReject 7 st273 4 3 35 0 1 0 2 28 (by decide +kernel)

private def st274 : List Sig := [wire34,raw2,raw7,wire128,raw0,raw1,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node274 : impossible 7 0 st274 := by_search (by decide +kernel)

private def st275 : List Sig := [wire35,raw2,wire128,raw0,raw1,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node275 : impossible 7 0 st275 := by_search (by decide +kernel)

private def st276 : List Sig := [wire35,raw2,raw7,wire128,raw0,raw1,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node276 : impossible 7 0 st276 := by_search (by decide +kernel)

private def st277 : List Sig := [wire148,raw3,wire128,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node277 : impossible 7 0 st277 := by_search (by decide +kernel)

private def st278 : List Sig := [wire149,raw3,wire128,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node278 : impossible 7 0 st278 := by_search (by decide +kernel)

private def st279 : List Sig := [wire40,raw3,raw7,wire128,raw0,raw1,raw2,raw4]

set_option maxRecDepth 10000 in
private theorem node279 : impossible 7 0 st279 := by_search (by decide +kernel)

private def st280 : List Sig := [wire41,raw3,raw7,wire128,raw0,raw1,raw2,raw4]

set_option maxRecDepth 10000 in
private theorem node280 : impossible 7 0 st280 := by_search (by decide +kernel)

private def st281 : List Sig := [wire150,raw4,wire128,raw0,raw1,raw2,raw3,raw7]

private theorem node281 : impossible 7 0 st281 := rectReject 7 st281 4 3 0 5 2 7 0 35 (by decide +kernel)

private def st282 : List Sig := [wire151,raw4,wire128,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node282 : impossible 7 0 st282 := by_search (by decide +kernel)

private def st283 : List Sig := [wire42,raw4,raw3,wire128,raw0,raw1,raw2,raw7]

private theorem node283 : impossible 7 0 st283 := rectReject 7 st283 4 3 35 0 1 0 2 28 (by decide +kernel)

private def st284 : List Sig := [wire43,raw4,raw3,wire128,raw0,raw1,raw2,raw7]

set_option maxRecDepth 10000 in
private theorem node284 : impossible 7 0 st284 := by_search (by decide +kernel)

private def st285 : List Sig := [wire48,raw4,raw7,wire128,raw0,raw1,raw2,raw3]

private theorem node285 : impossible 7 0 st285 := rectReject 7 st285 3 1 28 2 0 35 1 21 (by decide +kernel)

private def st286 : List Sig := [wire49,raw4,raw7,wire128,raw0,raw1,raw2,raw3]

set_option maxRecDepth 10000 in
private theorem node286 : impossible 7 0 st286 := by_search (by decide +kernel)

private def st287 : List Sig := [wire128,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node287 : impossible 8 0 st287 := by
  apply reject_branch 7 0 st287 [] [st242,st243,st244,st245,st246,st247,st248,st249,st250,st251,st252,st253,st254,st255,st256,st257,st258,st259,st260,st261,st262,st263,st264,st265,st266,st267,st268,st269,st270,st271,st272,st273,st274,st275,st276,st277,st278,st279,st280,st281,st282,st283,st284,st285,st286]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node242
    · exact node243
    · exact node244
    · exact node245
    · exact node246
    · exact node247
    · exact node248
    · exact node249
    · exact node250
    · exact node251
    · exact node252
    · exact node253
    · exact node254
    · exact node255
    · exact node256
    · exact node257
    · exact node258
    · exact node259
    · exact node260
    · exact node261
    · exact node262
    · exact node263
    · exact node264
    · exact node265
    · exact node266
    · exact node267
    · exact node268
    · exact node269
    · exact node270
    · exact node271
    · exact node272
    · exact node273
    · exact node274
    · exact node275
    · exact node276
    · exact node277
    · exact node278
    · exact node279
    · exact node280
    · exact node281
    · exact node282
    · exact node283
    · exact node284
    · exact node285
    · exact node286
  · decide +kernel

private def st288 : List Sig := [wire128,wire10,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node288 : impossible 8 0 st288 := by_search (by decide +kernel)

private def st289 : List Sig := [wire128,raw5,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node289 : impossible 8 0 st289 := by_search (by decide +kernel)

private def st290 : List Sig := [wire128,wire10,raw5,raw0,raw1,raw2,raw3,raw4,raw7]

private theorem node290 : impossible 8 0 st290 := rectReject 8 st290 4 3 0 5 2 7 0 35 (by decide +kernel)

private def st291 : List Sig := [wire129,wire10,raw7,raw0,raw1,raw2,raw3,raw4,raw5]

private theorem node291 : impossible 8 0 st291 := rectReject 8 st291 4 3 0 5 2 7 0 35 (by decide +kernel)

private def st292 : List Sig := [wire130,wire10,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node292 : impossible 8 0 st292 := by_search (by decide +kernel)

private def st293 : List Sig := [wire130,wire10,raw7,raw0,raw1,raw2,raw3,raw4,raw5]

private theorem node293 : impossible 8 0 st293 := rectReject 8 st293 4 3 0 5 2 7 0 35 (by decide +kernel)

private def st294 : List Sig := [wire0,raw0,raw1,wire10,raw2,raw3,raw4,raw5,raw7]

private theorem node294 : impossible 8 0 st294 := rectReject 8 st294 4 2 7 2 0 14 3 49 (by decide +kernel)

private def st295 : List Sig := [wire1,raw0,raw1,wire10,raw2,raw3,raw4,raw5,raw7]

private theorem node295 : impossible 8 0 st295 := rectReject 8 st295 4 2 7 2 0 14 3 0 (by decide +kernel)

private def st296 : List Sig := [wire2,raw0,raw2,wire10,raw1,raw3,raw4,raw5,raw7]

private theorem node296 : impossible 8 0 st296 := rectReject 8 st296 4 1 0 5 2 7 0 35 (by decide +kernel)

private def st297 : List Sig := [wire3,raw0,raw2,wire10,raw1,raw3,raw4,raw5,raw7]

private theorem node297 : impossible 8 0 st297 := rectReject 8 st297 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st298 : List Sig := [wire4,raw0,raw3,wire10,raw1,raw2,raw4,raw5,raw7]

private theorem node298 : impossible 8 0 st298 := rectReject 8 st298 4 1 0 5 2 7 0 35 (by decide +kernel)

private def st299 : List Sig := [wire5,raw0,raw3,wire10,raw1,raw2,raw4,raw5,raw7]

private theorem node299 : impossible 8 0 st299 := rectReject 8 st299 4 1 0 6 2 49 1 35 (by decide +kernel)

private def st300 : List Sig := [wire6,raw0,raw4,wire10,raw1,raw2,raw3,raw5,raw7]

private theorem node300 : impossible 8 0 st300 := rectReject 8 st300 4 1 0 5 2 7 0 35 (by decide +kernel)

private def st301 : List Sig := [wire7,raw0,raw4,wire10,raw1,raw2,raw3,raw5,raw7]

private theorem node301 : impossible 8 0 st301 := rectReject 8 st301 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st302 : List Sig := [wire8,raw0,raw5,wire10,raw1,raw2,raw3,raw4,raw7]

private theorem node302 : impossible 8 0 st302 := rectReject 8 st302 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st303 : List Sig := [wire9,raw0,raw5,wire10,raw1,raw2,raw3,raw4,raw7]

private theorem node303 : impossible 8 0 st303 := rectReject 8 st303 4 1 0 5 2 7 1 35 (by decide +kernel)

private def st304 : List Sig := [wire12,raw0,raw7,wire10,raw1,raw2,raw3,raw4,raw5]

private theorem node304 : impossible 8 0 st304 := rectReject 8 st304 4 1 0 5 2 7 0 35 (by decide +kernel)

private def st305 : List Sig := [wire13,raw0,wire10,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node305 : impossible 8 0 st305 := by_search (by decide +kernel)

private def st306 : List Sig := [wire13,raw0,raw7,wire10,raw1,raw2,raw3,raw4,raw5]

private theorem node306 : impossible 8 0 st306 := rectReject 8 st306 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st307 : List Sig := [wire14,raw1,raw2,wire10,raw0,raw3,raw4,raw5,raw7]

private theorem node307 : impossible 8 0 st307 := rectReject 8 st307 4 1 0 5 0 35 2 49 (by decide +kernel)

private def st308 : List Sig := [wire15,raw1,raw2,wire10,raw0,raw3,raw4,raw5,raw7]

private theorem node308 : impossible 8 0 st308 := rectReject 8 st308 4 1 0 5 0 35 3 7 (by decide +kernel)

private def st309 : List Sig := [wire16,raw1,raw3,wire10,raw0,raw2,raw4,raw5,raw7]

private theorem node309 : impossible 8 0 st309 := rectReject 8 st309 4 1 0 5 0 35 2 7 (by decide +kernel)

private def st310 : List Sig := [wire17,raw1,raw3,wire10,raw0,raw2,raw4,raw5,raw7]

private theorem node310 : impossible 8 0 st310 := rectReject 8 st310 4 1 0 6 0 35 2 49 (by decide +kernel)

private def st311 : List Sig := [wire18,raw1,raw4,wire10,raw0,raw2,raw3,raw5,raw7]

private theorem node311 : impossible 8 0 st311 := rectReject 8 st311 4 1 0 5 0 35 2 7 (by decide +kernel)

private def st312 : List Sig := [wire19,raw1,raw4,wire10,raw0,raw2,raw3,raw5,raw7]

private theorem node312 : impossible 8 0 st312 := rectReject 8 st312 6 5 14 0 3 21 1 7 (by decide +kernel)

private def st313 : List Sig := [wire20,raw1,raw5,wire10,raw0,raw2,raw3,raw4,raw7]

private theorem node313 : impossible 8 0 st313 := rectReject 8 st313 4 1 0 5 0 35 2 7 (by decide +kernel)

private def st314 : List Sig := [wire21,raw1,raw5,wire10,raw0,raw2,raw3,raw4,raw7]

private theorem node314 : impossible 8 0 st314 := rectReject 8 st314 5 1 7 6 0 14 5 49 (by decide +kernel)

private def st315 : List Sig := [wire152,raw1,wire10,raw0,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node315 : impossible 7 0 st315 := by_search (by decide +kernel)

private def st316 : List Sig := [wire152,wire24,raw1,wire10,raw0,raw3,raw4,raw5]

private theorem node316 : impossible 7 0 st316 := rectReject 7 st316 2 0 7 2 3 0 0 14 (by decide +kernel)

private def st317 : List Sig := [wire152,raw2,raw1,wire10,raw0,raw3,raw4,raw5]

private theorem node317 : impossible 7 0 st317 := rectReject 7 st317 4 2 0 5 0 35 2 7 (by decide +kernel)

private def st318 : List Sig := [wire153,wire24,raw1,wire10,raw0,raw2,raw4,raw5]

private theorem node318 : impossible 7 0 st318 := rectReject 7 st318 4 2 0 5 0 35 2 7 (by decide +kernel)

private def st319 : List Sig := [wire154,wire24,raw1,wire10,raw0,raw2,raw3,raw5]

private theorem node319 : impossible 7 0 st319 := rectReject 7 st319 4 2 0 5 0 35 2 7 (by decide +kernel)

private def st320 : List Sig := [wire155,wire24,raw1,wire10,raw0,raw2,raw3,raw4]

private theorem node320 : impossible 7 0 st320 := rectReject 7 st320 4 0 35 0 1 0 2 28 (by decide +kernel)

private def st321 : List Sig := [wire156,raw1,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node321 : impossible 7 0 st321 := by_search (by decide +kernel)

private def st322 : List Sig := [wire156,wire10,raw1,raw0,raw2,raw3,raw4,raw5]

private theorem node322 : impossible 7 0 st322 := rectReject 7 st322 3 2 0 5 0 35 2 7 (by decide +kernel)

private def st323 : List Sig := [wire156,wire24,raw1,raw0,raw2,raw3,raw4,raw5]

private theorem node323 : impossible 7 0 st323 := rectReject 7 st323 3 2 0 5 0 35 2 7 (by decide +kernel)

private def st324 : List Sig := [wire121,wire24,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node324 : impossible 7 0 st324 := by_search (by decide +kernel)

private def st325 : List Sig := [wire121,wire10,wire24,raw0,raw2,raw3,raw4,raw5]

private theorem node325 : impossible 7 0 st325 := rectReject 7 st325 3 0 0 5 0 35 2 7 (by decide +kernel)

private def st326 : List Sig := [wire121,raw1,wire24,raw0,raw2,raw3,raw4,raw5]

private theorem node326 : impossible 7 0 st326 := rectReject 7 st326 5 4 14 0 3 21 1 7 (by decide +kernel)

private def st327 : List Sig := [wire123,wire10,wire24,raw1,raw0,raw3,raw4,raw5]

private theorem node327 : impossible 7 0 st327 := rectReject 7 st327 3 0 7 2 3 0 0 14 (by decide +kernel)

private def st328 : List Sig := [wire125,wire10,wire24,raw1,raw0,raw2,raw4,raw5]

private theorem node328 : impossible 7 0 st328 := rectReject 7 st328 4 3 0 5 0 35 2 7 (by decide +kernel)

private def st329 : List Sig := [wire127,wire10,wire24,raw1,raw0,raw2,raw3,raw5]

private theorem node329 : impossible 7 0 st329 := rectReject 7 st329 4 3 0 5 0 35 2 7 (by decide +kernel)

private def st330 : List Sig := [wire128,wire24,raw1,raw0,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node330 : impossible 7 0 st330 := by_search (by decide +kernel)

private def st331 : List Sig := [wire128,wire10,wire24,raw1,raw0,raw2,raw3,raw4]

private theorem node331 : impossible 7 0 st331 := rectReject 7 st331 4 0 35 0 1 0 2 28 (by decide +kernel)

private def st332 : List Sig := [wire128,raw5,wire24,raw1,raw0,raw2,raw3,raw4]

private theorem node332 : impossible 7 0 st332 := rectReject 7 st332 4 3 0 5 0 35 2 7 (by decide +kernel)

private def st333 : List Sig := [wire157,raw1,wire10,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node333 : impossible 7 0 st333 := by_search (by decide +kernel)

private def st334 : List Sig := [wire157,raw0,raw1,wire10,raw2,raw3,raw4,raw5]

private theorem node334 : impossible 7 0 st334 := rectReject 7 st334 4 2 7 2 0 14 3 0 (by decide +kernel)

private def st335 : List Sig := [wire157,wire24,raw1,wire10,raw2,raw3,raw4,raw5]

private theorem node335 : impossible 7 0 st335 := rectReject 7 st335 2 0 0 5 2 7 0 35 (by decide +kernel)

private def st336 : List Sig := [wire24,raw1,wire10,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node336 : impossible 8 0 st336 := by
  apply reject_branch 7 0 st336 [] [st315,st316,st317,st318,st319,st320,st321,st322,st323,st324,st325,st326,st327,st328,st329,st330,st331,st332,st333,st334,st335]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node315
    · exact node316
    · exact node317
    · exact node318
    · exact node319
    · exact node320
    · exact node321
    · exact node322
    · exact node323
    · exact node324
    · exact node325
    · exact node326
    · exact node327
    · exact node328
    · exact node329
    · exact node330
    · exact node331
    · exact node332
    · exact node333
    · exact node334
    · exact node335
  · decide +kernel

private def st337 : List Sig := [wire24,raw1,raw7,wire10,raw0,raw2,raw3,raw4,raw5]

private theorem node337 : impossible 8 0 st337 := rectReject 8 st337 4 1 0 5 0 35 2 7 (by decide +kernel)

private def st338 : List Sig := [wire25,raw1,raw7,wire10,raw0,raw2,raw3,raw4,raw5]

private theorem node338 : impossible 8 0 st338 := rectReject 8 st338 4 1 0 5 0 35 2 7 (by decide +kernel)

private def st339 : List Sig := [wire26,raw2,raw3,wire10,raw0,raw1,raw4,raw5,raw7]

private theorem node339 : impossible 8 0 st339 := rectReject 8 st339 5 4 0 5 2 7 0 35 (by decide +kernel)

private def st340 : List Sig := [wire27,raw2,raw3,wire10,raw0,raw1,raw4,raw5,raw7]

private theorem node340 : impossible 8 0 st340 := rectReject 8 st340 5 1 7 2 3 0 1 14 (by decide +kernel)

private def st341 : List Sig := [wire28,raw2,raw4,wire10,raw0,raw1,raw3,raw5,raw7]

private theorem node341 : impossible 8 0 st341 := rectReject 8 st341 5 1 7 2 3 0 0 14 (by decide +kernel)

private def st342 : List Sig := [wire29,raw2,raw4,wire10,raw0,raw1,raw3,raw5,raw7]

private theorem node342 : impossible 8 0 st342 := rectReject 8 st342 5 4 0 5 2 7 0 35 (by decide +kernel)

private def st343 : List Sig := [wire30,raw2,raw5,wire10,raw0,raw1,raw3,raw4,raw7]

private theorem node343 : impossible 8 0 st343 := rectReject 8 st343 4 2 35 0 1 0 2 28 (by decide +kernel)

private def st344 : List Sig := [wire31,raw2,raw5,wire10,raw0,raw1,raw3,raw4,raw7]

private theorem node344 : impossible 8 0 st344 := rectReject 8 st344 5 1 7 6 3 49 1 14 (by decide +kernel)

private def st345 : List Sig := [wire34,raw2,raw7,wire10,raw0,raw1,raw3,raw4,raw5]

private theorem node345 : impossible 8 0 st345 := rectReject 8 st345 5 1 7 2 3 0 0 14 (by decide +kernel)

private def st346 : List Sig := [wire35,raw2,wire10,raw0,raw1,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node346 : impossible 8 0 st346 := by_search (by decide +kernel)

private def st347 : List Sig := [wire35,raw2,raw7,wire10,raw0,raw1,raw3,raw4,raw5]

private theorem node347 : impossible 8 0 st347 := rectReject 8 st347 5 4 0 5 2 7 0 35 (by decide +kernel)

private def st348 : List Sig := [wire36,raw3,raw5,wire10,raw0,raw1,raw2,raw4,raw7]

private theorem node348 : impossible 8 0 st348 := rectReject 8 st348 4 2 35 0 1 0 2 28 (by decide +kernel)

private def st349 : List Sig := [wire37,raw3,raw5,wire10,raw0,raw1,raw2,raw4,raw7]

private theorem node349 : impossible 8 0 st349 := rectReject 8 st349 5 4 0 5 2 7 0 35 (by decide +kernel)

private def st350 : List Sig := [wire40,raw3,raw7,wire10,raw0,raw1,raw2,raw4,raw5]

private theorem node350 : impossible 8 0 st350 := rectReject 8 st350 5 4 0 5 2 7 0 35 (by decide +kernel)

private def st351 : List Sig := [wire41,raw3,raw7,wire10,raw0,raw1,raw2,raw4,raw5]

private theorem node351 : impossible 8 0 st351 := rectReject 8 st351 5 4 0 5 2 7 0 35 (by decide +kernel)

private def st352 : List Sig := [wire42,raw4,raw3,wire10,raw0,raw1,raw2,raw5,raw7]

private theorem node352 : impossible 8 0 st352 := rectReject 8 st352 5 4 0 5 2 7 0 35 (by decide +kernel)

private def st353 : List Sig := [wire43,raw4,raw3,wire10,raw0,raw1,raw2,raw5,raw7]

private theorem node353 : impossible 8 0 st353 := rectReject 8 st353 5 4 0 5 2 7 0 35 (by decide +kernel)

private def st354 : List Sig := [wire44,raw4,raw5,wire10,raw0,raw1,raw2,raw3,raw7]

private theorem node354 : impossible 8 0 st354 := rectReject 8 st354 5 4 0 5 2 7 0 35 (by decide +kernel)

private def st355 : List Sig := [wire45,raw4,raw5,wire10,raw0,raw1,raw2,raw3,raw7]

private theorem node355 : impossible 8 0 st355 := rectReject 8 st355 4 2 35 0 1 0 3 28 (by decide +kernel)

private def st356 : List Sig := [wire48,raw4,raw7,wire10,raw0,raw1,raw2,raw3,raw5]

private theorem node356 : impossible 8 0 st356 := rectReject 8 st356 5 4 0 5 2 7 0 35 (by decide +kernel)

private def st357 : List Sig := [wire49,raw4,raw7,wire10,raw0,raw1,raw2,raw3,raw5]

private theorem node357 : impossible 8 0 st357 := rectReject 8 st357 5 4 0 5 2 7 0 35 (by decide +kernel)

private def st358 : List Sig := [wire52,raw5,raw7,wire10,raw0,raw1,raw2,raw3,raw4]

private theorem node358 : impossible 8 0 st358 := rectReject 8 st358 4 1 35 0 1 0 2 28 (by decide +kernel)

private def st359 : List Sig := [wire53,raw5,raw7,wire10,raw0,raw1,raw2,raw3,raw4]

private theorem node359 : impossible 8 0 st359 := rectReject 8 st359 5 4 0 5 2 7 0 35 (by decide +kernel)

private def st360 : List Sig := [wire10,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node360 : impossible 9 0 st360 := by
  apply reject_branch 8 0 st360 [] [st182,st228,st229,st230,st231,st232,st233,st234,st235,st236,st237,st238,st239,st240,st241,st287,st288,st289,st290,st291,st292,st293,st294,st295,st296,st297,st298,st299,st300,st301,st302,st303,st304,st305,st306,st307,st308,st309,st310,st311,st312,st313,st314,st336,st337,st338,st339,st340,st341,st342,st343,st344,st345,st346,st347,st348,st349,st350,st351,st352,st353,st354,st355,st356,st357,st358,st359]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node182
    · exact node228
    · exact node229
    · exact node230
    · exact node231
    · exact node232
    · exact node233
    · exact node234
    · exact node235
    · exact node236
    · exact node237
    · exact node238
    · exact node239
    · exact node240
    · exact node241
    · exact node287
    · exact node288
    · exact node289
    · exact node290
    · exact node291
    · exact node292
    · exact node293
    · exact node294
    · exact node295
    · exact node296
    · exact node297
    · exact node298
    · exact node299
    · exact node300
    · exact node301
    · exact node302
    · exact node303
    · exact node304
    · exact node305
    · exact node306
    · exact node307
    · exact node308
    · exact node309
    · exact node310
    · exact node311
    · exact node312
    · exact node313
    · exact node314
    · exact node336
    · exact node337
    · exact node338
    · exact node339
    · exact node340
    · exact node341
    · exact node342
    · exact node343
    · exact node344
    · exact node345
    · exact node346
    · exact node347
    · exact node348
    · exact node349
    · exact node350
    · exact node351
    · exact node352
    · exact node353
    · exact node354
    · exact node355
    · exact node356
    · exact node357
    · exact node358
    · exact node359
  · decide +kernel

private def st361 : List Sig := [wire64,raw1,raw0,raw6,raw2,raw3,raw4,raw5,raw7]

private theorem node361 : impossible 8 0 st361 := rectReject 8 st361 2 1 0 4 0 42 2 7 (by decide +kernel)

private def st362 : List Sig := [wire121,raw0,raw6,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node362 : impossible 8 0 st362 := by_search (by decide +kernel)

private def st363 : List Sig := [wire121,wire10,raw0,raw6,raw2,raw3,raw4,raw5,raw7]

private theorem node363 : impossible 8 0 st363 := rectReject 8 st363 2 0 0 5 0 35 2 7 (by decide +kernel)

private def st364 : List Sig := [wire121,raw1,raw0,raw6,raw2,raw3,raw4,raw5,raw7]

private theorem node364 : impossible 8 0 st364 := rectReject 8 st364 5 4 14 0 3 21 1 7 (by decide +kernel)

private def st365 : List Sig := [wire122,raw2,raw0,raw6,raw1,raw3,raw4,raw5,raw7]

private theorem node365 : impossible 8 0 st365 := rectReject 8 st365 4 1 7 2 3 0 0 14 (by decide +kernel)

private def st366 : List Sig := [wire123,raw0,raw6,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node366 : impossible 8 0 st366 := by_search (by decide +kernel)

private def st367 : List Sig := [wire123,wire10,raw0,raw6,raw1,raw3,raw4,raw5,raw7]

private theorem node367 : impossible 8 0 st367 := rectReject 8 st367 4 0 7 2 3 0 0 14 (by decide +kernel)

private def st368 : List Sig := [wire123,raw2,raw0,raw6,raw1,raw3,raw4,raw5,raw7]

private theorem node368 : impossible 8 0 st368 := rectReject 8 st368 4 2 0 4 2 7 0 42 (by decide +kernel)

private def st369 : List Sig := [wire124,raw3,raw0,raw6,raw1,raw2,raw4,raw5,raw7]

private theorem node369 : impossible 8 0 st369 := rectReject 8 st369 4 2 0 4 2 7 0 42 (by decide +kernel)

private def st370 : List Sig := [wire125,raw0,raw6,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node370 : impossible 8 0 st370 := by_search (by decide +kernel)

private def st371 : List Sig := [wire125,wire10,raw0,raw6,raw1,raw2,raw4,raw5,raw7]

private theorem node371 : impossible 8 0 st371 := rectReject 8 st371 4 2 0 5 2 7 0 35 (by decide +kernel)

private def st372 : List Sig := [wire125,raw3,raw0,raw6,raw1,raw2,raw4,raw5,raw7]

private theorem node372 : impossible 8 0 st372 := rectReject 8 st372 4 2 0 5 2 7 0 35 (by decide +kernel)

private def st373 : List Sig := [wire126,raw4,raw0,raw6,raw1,raw2,raw3,raw5,raw7]

private theorem node373 : impossible 8 0 st373 := rectReject 8 st373 4 2 0 4 2 7 0 42 (by decide +kernel)

private def st374 : List Sig := [wire127,raw0,raw6,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node374 : impossible 8 0 st374 := by_search (by decide +kernel)

private def st375 : List Sig := [wire127,wire10,raw0,raw6,raw1,raw2,raw3,raw5,raw7]

private theorem node375 : impossible 8 0 st375 := rectReject 8 st375 4 2 0 5 2 7 0 35 (by decide +kernel)

private def st376 : List Sig := [wire127,raw4,raw0,raw6,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node376 : impossible 8 0 st376 := by_search (by decide +kernel)

private def st377 : List Sig := [wire108,raw5,raw0,raw6,raw1,raw2,raw3,raw4,raw7]

private theorem node377 : impossible 8 0 st377 := rectReject 8 st377 2 1 35 0 1 0 2 28 (by decide +kernel)

private def st378 : List Sig := [wire128,raw0,raw6,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node378 : impossible 8 0 st378 := by_search (by decide +kernel)

private def st379 : List Sig := [wire128,wire10,raw0,raw6,raw1,raw2,raw3,raw4,raw7]

private theorem node379 : impossible 8 0 st379 := rectReject 8 st379 2 0 35 0 1 0 2 28 (by decide +kernel)

private def st380 : List Sig := [wire128,raw5,raw0,raw6,raw1,raw2,raw3,raw4,raw7]

private theorem node380 : impossible 8 0 st380 := rectReject 8 st380 4 2 0 5 2 7 0 35 (by decide +kernel)

private def st381 : List Sig := [wire129,raw7,raw0,raw6,raw1,raw2,raw3,raw4,raw5]

private theorem node381 : impossible 8 0 st381 := rectReject 8 st381 4 2 0 4 2 7 0 42 (by decide +kernel)

private def st382 : List Sig := [wire130,raw0,raw6,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node382 : impossible 8 0 st382 := by_search (by decide +kernel)

private def st383 : List Sig := [wire130,wire10,raw0,raw6,raw1,raw2,raw3,raw4,raw5]

private theorem node383 : impossible 8 0 st383 := rectReject 8 st383 4 2 0 5 2 7 0 35 (by decide +kernel)

private def st384 : List Sig := [wire130,raw7,raw0,raw6,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node384 : impossible 8 0 st384 := by_search (by decide +kernel)

private def st385 : List Sig := [wire11,raw0,wire10,raw1,raw2,raw3,raw4,raw5,raw7]

private theorem node385 : impossible 8 0 st385 := rectReject 8 st385 3 1 0 5 2 7 0 35 (by decide +kernel)

private def st386 : List Sig := [wire13,raw0,wire10,raw6,raw1,raw2,raw3,raw4,raw5]

private theorem node386 : impossible 8 0 st386 := rectReject 8 st386 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st387 : List Sig := [wire54,raw7,wire10,raw0,raw1,raw2,raw3,raw4,raw5]

private theorem node387 : impossible 8 0 st387 := rectReject 8 st387 4 3 0 5 2 7 0 35 (by decide +kernel)

private def st388 : List Sig := [wire55,raw7,wire10,raw0,raw1,raw2,raw3,raw4,raw5]

private theorem node388 : impossible 8 0 st388 := rectReject 8 st388 4 3 0 5 2 7 0 35 (by decide +kernel)

private def st389 : List Sig := [wire22,raw1,wire10,raw0,raw2,raw3,raw4,raw5,raw7]

private theorem node389 : impossible 8 0 st389 := rectReject 8 st389 3 1 0 5 0 35 2 7 (by decide +kernel)

private def st390 : List Sig := [wire23,raw1,wire10,raw0,raw2,raw3,raw4,raw5,raw7]

private theorem node390 : impossible 8 0 st390 := rectReject 8 st390 4 1 7 6 0 14 4 49 (by decide +kernel)

private def st391 : List Sig := [wire24,raw1,wire10,raw0,raw6,raw2,raw3,raw4,raw5]

private theorem node391 : impossible 8 0 st391 := rectReject 8 st391 3 1 0 5 0 35 2 7 (by decide +kernel)

private def st392 : List Sig := [wire32,raw2,wire10,raw0,raw1,raw3,raw4,raw5,raw7]

private theorem node392 : impossible 8 0 st392 := rectReject 8 st392 4 1 7 2 3 0 0 14 (by decide +kernel)

private def st393 : List Sig := [wire33,raw2,wire10,raw0,raw1,raw3,raw4,raw5,raw7]

private theorem node393 : impossible 8 0 st393 := rectReject 8 st393 4 1 7 6 3 49 0 14 (by decide +kernel)

private def st394 : List Sig := [wire35,raw2,wire10,raw0,raw6,raw1,raw3,raw4,raw5]

private theorem node394 : impossible 8 0 st394 := rectReject 8 st394 5 3 0 5 2 7 0 35 (by decide +kernel)

private def st395 : List Sig := [wire38,raw3,wire10,raw0,raw1,raw2,raw4,raw5,raw7]

private theorem node395 : impossible 8 0 st395 := rectReject 8 st395 4 3 0 5 2 7 0 35 (by decide +kernel)

private def st396 : List Sig := [wire39,raw3,wire10,raw0,raw1,raw2,raw4,raw5,raw7]

private theorem node396 : impossible 8 0 st396 := rectReject 8 st396 4 3 0 5 2 7 0 35 (by decide +kernel)

private def st397 : List Sig := [wire46,raw4,wire10,raw0,raw1,raw2,raw3,raw5,raw7]

private theorem node397 : impossible 8 0 st397 := rectReject 8 st397 4 3 0 5 2 7 0 35 (by decide +kernel)

private def st398 : List Sig := [wire47,raw4,wire10,raw0,raw1,raw2,raw3,raw5,raw7]

private theorem node398 : impossible 8 0 st398 := rectReject 8 st398 4 3 0 5 2 7 0 35 (by decide +kernel)

private def st399 : List Sig := [wire50,raw5,wire10,raw0,raw1,raw2,raw3,raw4,raw7]

private theorem node399 : impossible 8 0 st399 := rectReject 8 st399 3 1 35 0 1 0 2 28 (by decide +kernel)

private def st400 : List Sig := [wire51,raw5,wire10,raw0,raw1,raw2,raw3,raw4,raw7]

private theorem node400 : impossible 8 0 st400 := rectReject 8 st400 4 3 0 5 2 7 0 35 (by decide +kernel)

private def st401 : List Sig := [wire10,raw0,raw6,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node401 : impossible 9 0 st401 := by
  apply reject_branch 8 0 st401 [] [st361,st362,st363,st364,st365,st366,st367,st368,st369,st370,st371,st372,st373,st374,st375,st376,st377,st378,st379,st380,st381,st382,st383,st384,st385,st386,st387,st388,st389,st390,st391,st392,st393,st394,st395,st396,st397,st398,st399,st400]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node361
    · exact node362
    · exact node363
    · exact node364
    · exact node365
    · exact node366
    · exact node367
    · exact node368
    · exact node369
    · exact node370
    · exact node371
    · exact node372
    · exact node373
    · exact node374
    · exact node375
    · exact node376
    · exact node377
    · exact node378
    · exact node379
    · exact node380
    · exact node381
    · exact node382
    · exact node383
    · exact node384
    · exact node385
    · exact node386
    · exact node387
    · exact node388
    · exact node389
    · exact node390
    · exact node391
    · exact node392
    · exact node393
    · exact node394
    · exact node395
    · exact node396
    · exact node397
    · exact node398
    · exact node399
    · exact node400
  · decide +kernel

private def st402 : List Sig := [wire11,raw0,raw6,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node402 : impossible 9 0 st402 := by_search (by decide +kernel)

private def st403 : List Sig := [wire12,raw0,raw7,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node403 : impossible 9 0 st403 := by_search (by decide +kernel)

private def st404 : List Sig := [wire0,raw0,raw1,wire13,raw2,raw3,raw4,raw5,raw6]

private theorem node404 : impossible 8 0 st404 := rectReject 8 st404 4 2 7 2 0 14 3 49 (by decide +kernel)

private def st405 : List Sig := [wire1,raw1,wire13,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node405 : impossible 8 0 st405 := by_search (by decide +kernel)

private def st406 : List Sig := [wire1,raw0,raw1,wire13,raw2,raw3,raw4,raw5,raw6]

private theorem node406 : impossible 8 0 st406 := rectReject 8 st406 4 2 7 2 0 14 3 0 (by decide +kernel)

private def st407 : List Sig := [wire2,raw0,raw2,wire13,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node407 : impossible 8 0 st407 := by_search (by decide +kernel)

private def st408 : List Sig := [wire3,raw0,raw2,wire13,raw1,raw3,raw4,raw5,raw6]

private theorem node408 : impossible 8 0 st408 := rectReject 8 st408 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st409 : List Sig := [wire4,raw0,raw3,wire13,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node409 : impossible 8 0 st409 := by_search (by decide +kernel)

private def st410 : List Sig := [wire5,raw0,raw3,wire13,raw1,raw2,raw4,raw5,raw6]

private theorem node410 : impossible 8 0 st410 := rectReject 8 st410 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st411 : List Sig := [wire6,raw0,raw4,wire13,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node411 : impossible 8 0 st411 := by_search (by decide +kernel)

private def st412 : List Sig := [wire7,raw0,raw4,wire13,raw1,raw2,raw3,raw5,raw6]

private theorem node412 : impossible 8 0 st412 := rectReject 8 st412 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st413 : List Sig := [wire8,raw0,raw5,wire13,raw1,raw2,raw3,raw4,raw6]

private theorem node413 : impossible 8 0 st413 := rectReject 8 st413 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st414 : List Sig := [wire9,raw0,raw5,wire13,raw1,raw2,raw3,raw4,raw6]

private theorem node414 : impossible 8 0 st414 := rectReject 8 st414 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st415 : List Sig := [wire10,raw0,wire13,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node415 : impossible 8 0 st415 := by_search (by decide +kernel)

private def st416 : List Sig := [wire10,raw0,raw6,wire13,raw1,raw2,raw3,raw4,raw5]

private theorem node416 : impossible 8 0 st416 := rectReject 8 st416 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st417 : List Sig := [wire11,raw0,raw6,wire13,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node417 : impossible 8 0 st417 := by_search (by decide +kernel)

private def st418 : List Sig := [wire158,raw1,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node418 : impossible 8 0 st418 := by_search (by decide +kernel)

private def st419 : List Sig := [wire158,raw1,wire13,raw0,raw2,raw3,raw4,raw5,raw6]

private theorem node419 : impossible 8 0 st419 := rectReject 8 st419 5 4 14 0 3 21 1 7 (by decide +kernel)

private def st420 : List Sig := [wire79,raw1,wire13,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node420 : impossible 8 0 st420 := by_search (by decide +kernel)

private def st421 : List Sig := [wire14,raw1,raw2,wire13,raw0,raw3,raw4,raw5,raw6]

private theorem node421 : impossible 8 0 st421 := rectReject 8 st421 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st422 : List Sig := [wire15,raw1,raw2,wire13,raw0,raw3,raw4,raw5,raw6]

private theorem node422 : impossible 8 0 st422 := rectReject 8 st422 5 2 14 0 3 21 1 7 (by decide +kernel)

private def st423 : List Sig := [wire16,raw1,raw3,wire13,raw0,raw2,raw4,raw5,raw6]

private theorem node423 : impossible 8 0 st423 := rectReject 8 st423 5 1 7 2 0 14 3 0 (by decide +kernel)

private def st424 : List Sig := [wire17,raw1,raw3,wire13,raw0,raw2,raw4,raw5,raw6]

private theorem node424 : impossible 8 0 st424 := rectReject 8 st424 7 4 35 4 2 28 5 42 (by decide +kernel)

private def st425 : List Sig := [wire18,raw1,raw4,wire13,raw0,raw2,raw3,raw5,raw6]

private theorem node425 : impossible 8 0 st425 := rectReject 8 st425 5 1 7 2 0 14 3 0 (by decide +kernel)

private def st426 : List Sig := [wire19,raw1,raw4,wire13,raw0,raw2,raw3,raw5,raw6]

private theorem node426 : impossible 8 0 st426 := rectReject 8 st426 6 5 14 0 3 21 1 7 (by decide +kernel)

private def st427 : List Sig := [wire20,raw1,raw5,wire13,raw0,raw2,raw3,raw4,raw6]

private theorem node427 : impossible 8 0 st427 := rectReject 8 st427 4 2 35 4 5 42 2 28 (by decide +kernel)

private def st428 : List Sig := [wire21,raw1,raw5,wire13,raw0,raw2,raw3,raw4,raw6]

private theorem node428 : impossible 8 0 st428 := rectReject 8 st428 5 1 7 6 0 14 5 49 (by decide +kernel)

private def st429 : List Sig := [wire22,raw1,raw6,wire13,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node429 : impossible 8 0 st429 := by_search (by decide +kernel)

private def st430 : List Sig := [wire23,raw1,wire13,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node430 : impossible 8 0 st430 := by_search (by decide +kernel)

private def st431 : List Sig := [wire23,raw1,raw6,wire13,raw0,raw2,raw3,raw4,raw5]

private theorem node431 : impossible 8 0 st431 := rectReject 8 st431 5 1 7 6 0 14 4 49 (by decide +kernel)

private def st432 : List Sig := [wire159,raw2,wire13,raw0,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node432 : impossible 8 0 st432 := by_search (by decide +kernel)

private def st433 : List Sig := [wire89,raw2,raw0,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node433 : impossible 8 0 st433 := by_search (by decide +kernel)

private def st434 : List Sig := [wire89,raw2,wire13,raw0,raw1,raw3,raw4,raw5,raw6]

private theorem node434 : impossible 8 0 st434 := rectReject 8 st434 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st435 : List Sig := [wire26,raw2,raw3,wire13,raw0,raw1,raw4,raw5,raw6]

private theorem node435 : impossible 8 0 st435 := rectReject 8 st435 7 4 35 4 2 28 5 42 (by decide +kernel)

private def st436 : List Sig := [wire27,raw2,raw3,wire13,raw0,raw1,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node436 : impossible 8 0 st436 := by_search (by decide +kernel)

private def st437 : List Sig := [wire28,raw2,raw4,wire13,raw0,raw1,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node437 : impossible 8 0 st437 := by_search (by decide +kernel)

private def st438 : List Sig := [wire29,raw2,raw4,wire13,raw0,raw1,raw3,raw5,raw6]

private theorem node438 : impossible 8 0 st438 := rectReject 8 st438 7 4 35 4 2 28 5 42 (by decide +kernel)

private def st439 : List Sig := [wire30,raw2,raw5,wire13,raw0,raw1,raw3,raw4,raw6]

private theorem node439 : impossible 8 0 st439 := rectReject 8 st439 4 2 35 4 5 42 2 28 (by decide +kernel)

private def st440 : List Sig := [wire31,raw2,raw5,wire13,raw0,raw1,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node440 : impossible 8 0 st440 := by_search (by decide +kernel)

private def st441 : List Sig := [wire32,raw2,raw6,wire13,raw0,raw1,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node441 : impossible 8 0 st441 := by_search (by decide +kernel)

private def st442 : List Sig := [wire33,raw2,raw6,wire13,raw0,raw1,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node442 : impossible 8 0 st442 := by_search (by decide +kernel)

private def st443 : List Sig := [wire160,raw3,wire13,raw0,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node443 : impossible 8 0 st443 := by_search (by decide +kernel)

private def st444 : List Sig := [wire161,raw3,wire13,raw0,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node444 : impossible 8 0 st444 := by_search (by decide +kernel)

private def st445 : List Sig := [wire36,raw3,raw5,wire13,raw0,raw1,raw2,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node445 : impossible 8 0 st445 := by_search (by decide +kernel)

private def st446 : List Sig := [wire37,raw3,raw5,wire13,raw0,raw1,raw2,raw4,raw6]

private theorem node446 : impossible 8 0 st446 := rectReject 8 st446 6 5 7 2 0 14 3 0 (by decide +kernel)

private def st447 : List Sig := [wire38,raw3,raw6,wire13,raw0,raw1,raw2,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node447 : impossible 8 0 st447 := by_search (by decide +kernel)

private def st448 : List Sig := [wire39,raw3,raw6,wire13,raw0,raw1,raw2,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node448 : impossible 8 0 st448 := by_search (by decide +kernel)

private def st449 : List Sig := [wire162,raw4,wire13,raw0,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node449 : impossible 8 0 st449 := by_search (by decide +kernel)

private def st450 : List Sig := [wire98,raw4,wire13,raw0,raw1,raw2,raw3,raw5,raw6]

private theorem node450 : impossible 8 0 st450 := rectReject 8 st450 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st451 : List Sig := [wire42,raw4,raw3,wire13,raw0,raw1,raw2,raw5,raw6]

private theorem node451 : impossible 8 0 st451 := rectReject 8 st451 6 5 7 2 0 14 3 0 (by decide +kernel)

private def st452 : List Sig := [wire43,raw4,raw3,wire13,raw0,raw1,raw2,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node452 : impossible 8 0 st452 := by_search (by decide +kernel)

private def st453 : List Sig := [wire44,raw4,raw5,wire13,raw0,raw1,raw2,raw3,raw6]

private theorem node453 : impossible 8 0 st453 := rectReject 8 st453 6 5 7 2 0 14 3 0 (by decide +kernel)

private def st454 : List Sig := [wire45,raw4,raw5,wire13,raw0,raw1,raw2,raw3,raw6]

set_option maxRecDepth 10000 in
private theorem node454 : impossible 8 0 st454 := by_search (by decide +kernel)

private def st455 : List Sig := [wire46,raw4,raw6,wire13,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node455 : impossible 8 0 st455 := by_search (by decide +kernel)

private def st456 : List Sig := [wire47,raw4,raw6,wire13,raw0,raw1,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node456 : impossible 8 0 st456 := by_search (by decide +kernel)

private def st457 : List Sig := [wire163,raw5,wire13,raw0,raw1,raw2,raw3,raw4,raw6]

private theorem node457 : impossible 8 0 st457 := rectReject 8 st457 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st458 : List Sig := [wire115,raw5,wire13,raw0,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node458 : impossible 8 0 st458 := by_search (by decide +kernel)

private def st459 : List Sig := [wire50,raw5,raw6,wire13,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node459 : impossible 8 0 st459 := by_search (by decide +kernel)

private def st460 : List Sig := [wire51,raw5,wire13,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node460 : impossible 8 0 st460 := by_search (by decide +kernel)

private def st461 : List Sig := [wire51,raw5,raw6,wire13,raw0,raw1,raw2,raw3,raw4]

private theorem node461 : impossible 8 0 st461 := rectReject 8 st461 6 5 7 2 0 14 3 0 (by decide +kernel)

private def st462 : List Sig := [wire164,wire13,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node462 : impossible 8 0 st462 := by_search (by decide +kernel)

private def st463 : List Sig := [wire164,raw6,wire13,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node463 : impossible 8 0 st463 := by_search (by decide +kernel)

private def st464 : List Sig := [wire165,raw6,wire13,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node464 : impossible 8 0 st464 := by_search (by decide +kernel)

private def st465 : List Sig := [wire13,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node465 : impossible 9 0 st465 := by
  apply reject_branch 8 0 st465 [] [st404,st405,st406,st407,st408,st409,st410,st411,st412,st413,st414,st415,st416,st417,st418,st419,st420,st421,st422,st423,st424,st425,st426,st427,st428,st429,st430,st431,st432,st433,st434,st435,st436,st437,st438,st439,st440,st441,st442,st443,st444,st445,st446,st447,st448,st449,st450,st451,st452,st453,st454,st455,st456,st457,st458,st459,st460,st461,st462,st463,st464]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node404
    · exact node405
    · exact node406
    · exact node407
    · exact node408
    · exact node409
    · exact node410
    · exact node411
    · exact node412
    · exact node413
    · exact node414
    · exact node415
    · exact node416
    · exact node417
    · exact node418
    · exact node419
    · exact node420
    · exact node421
    · exact node422
    · exact node423
    · exact node424
    · exact node425
    · exact node426
    · exact node427
    · exact node428
    · exact node429
    · exact node430
    · exact node431
    · exact node432
    · exact node433
    · exact node434
    · exact node435
    · exact node436
    · exact node437
    · exact node438
    · exact node439
    · exact node440
    · exact node441
    · exact node442
    · exact node443
    · exact node444
    · exact node445
    · exact node446
    · exact node447
    · exact node448
    · exact node449
    · exact node450
    · exact node451
    · exact node452
    · exact node453
    · exact node454
    · exact node455
    · exact node456
    · exact node457
    · exact node458
    · exact node459
    · exact node460
    · exact node461
    · exact node462
    · exact node463
    · exact node464
  · decide +kernel

private def st466 : List Sig := [wire13,raw0,raw7,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node466 : impossible 9 0 st466 := by_search (by decide +kernel)

private def st467 : List Sig := [wire56,raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

private theorem node467 : impossible 8 0 st467 := rectReject 8 st467 2 1 0 4 2 7 0 42 (by decide +kernel)

private def st468 : List Sig := [wire166,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node468 : impossible 8 0 st468 := by_search (by decide +kernel)

private def st469 : List Sig := [wire166,wire14,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

private theorem node469 : impossible 8 0 st469 := rectReject 8 st469 2 0 0 4 2 49 0 42 (by decide +kernel)

private def st470 : List Sig := [wire166,raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

private theorem node470 : impossible 8 0 st470 := rectReject 8 st470 5 4 21 5 1 28 0 14 (by decide +kernel)

private def st471 : List Sig := [wire167,raw3,raw1,raw2,raw0,raw4,raw5,raw6,raw7]

private theorem node471 : impossible 8 0 st471 := rectReject 8 st471 3 1 14 0 1 7 3 21 (by decide +kernel)

private def st472 : List Sig := [wire168,raw1,raw2,raw0,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node472 : impossible 8 0 st472 := by_search (by decide +kernel)

private def st473 : List Sig := [wire168,wire14,raw1,raw2,raw0,raw4,raw5,raw6,raw7]

private theorem node473 : impossible 8 0 st473 := rectReject 8 st473 4 2 0 4 0 42 2 49 (by decide +kernel)

private def st474 : List Sig := [wire168,raw3,raw1,raw2,raw0,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node474 : impossible 8 0 st474 := by_search (by decide +kernel)

private def st475 : List Sig := [wire169,raw4,raw1,raw2,raw0,raw3,raw5,raw6,raw7]

private theorem node475 : impossible 8 0 st475 := rectReject 8 st475 3 2 7 2 0 14 3 0 (by decide +kernel)

private def st476 : List Sig := [wire170,raw1,raw2,raw0,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node476 : impossible 8 0 st476 := by_search (by decide +kernel)

private def st477 : List Sig := [wire170,wire14,raw1,raw2,raw0,raw3,raw5,raw6,raw7]

private theorem node477 : impossible 8 0 st477 := rectReject 8 st477 4 2 0 4 0 42 2 49 (by decide +kernel)

private def st478 : List Sig := [wire170,raw4,raw1,raw2,raw0,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node478 : impossible 8 0 st478 := by_search (by decide +kernel)

private def st479 : List Sig := [wire171,raw5,raw1,raw2,raw0,raw3,raw4,raw6,raw7]

private theorem node479 : impossible 8 0 st479 := rectReject 8 st479 3 2 7 2 0 14 3 0 (by decide +kernel)

private def st480 : List Sig := [wire172,raw1,raw2,raw0,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node480 : impossible 8 0 st480 := by_search (by decide +kernel)

private def st481 : List Sig := [wire172,wire14,raw1,raw2,raw0,raw3,raw4,raw6,raw7]

private theorem node481 : impossible 8 0 st481 := rectReject 8 st481 4 0 35 0 1 0 2 28 (by decide +kernel)

private def st482 : List Sig := [wire172,raw5,raw1,raw2,raw0,raw3,raw4,raw6,raw7]

private theorem node482 : impossible 8 0 st482 := rectReject 8 st482 3 2 7 2 1 14 5 0 (by decide +kernel)

private def st483 : List Sig := [wire173,raw6,raw1,raw2,raw0,raw3,raw4,raw5,raw7]

private theorem node483 : impossible 8 0 st483 := rectReject 8 st483 3 2 7 2 0 14 3 0 (by decide +kernel)

private def st484 : List Sig := [wire174,raw1,raw2,raw0,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node484 : impossible 8 0 st484 := by_search (by decide +kernel)

private def st485 : List Sig := [wire174,wire14,raw1,raw2,raw0,raw3,raw4,raw5,raw7]

private theorem node485 : impossible 8 0 st485 := rectReject 8 st485 4 2 0 4 0 42 2 49 (by decide +kernel)

private def st486 : List Sig := [wire174,raw6,raw1,raw2,raw0,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node486 : impossible 8 0 st486 := by_search (by decide +kernel)

private def st487 : List Sig := [wire175,raw7,raw1,raw2,raw0,raw3,raw4,raw5,raw6]

private theorem node487 : impossible 8 0 st487 := rectReject 8 st487 3 2 7 2 0 14 3 0 (by decide +kernel)

private def st488 : List Sig := [wire176,raw1,raw2,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node488 : impossible 8 0 st488 := by_search (by decide +kernel)

private def st489 : List Sig := [wire176,wire14,raw1,raw2,raw0,raw3,raw4,raw5,raw6]

private theorem node489 : impossible 8 0 st489 := rectReject 8 st489 4 2 0 4 0 42 2 49 (by decide +kernel)

private def st490 : List Sig := [wire176,raw7,raw1,raw2,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node490 : impossible 8 0 st490 := by_search (by decide +kernel)

private def st491 : List Sig := [wire23,raw1,wire14,raw2,raw0,raw3,raw4,raw5,raw7]

private theorem node491 : impossible 8 0 st491 := rectReject 8 st491 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st492 : List Sig := [wire24,raw1,wire14,raw2,raw0,raw3,raw4,raw5,raw6]

private theorem node492 : impossible 8 0 st492 := rectReject 8 st492 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st493 : List Sig := [wire26,raw3,wire14,raw1,raw0,raw4,raw5,raw6,raw7]

private theorem node493 : impossible 8 0 st493 := rectReject 8 st493 4 3 0 4 0 42 2 49 (by decide +kernel)

private def st494 : List Sig := [wire29,raw4,wire14,raw1,raw0,raw3,raw5,raw6,raw7]

private theorem node494 : impossible 8 0 st494 := rectReject 8 st494 4 3 0 4 0 42 2 49 (by decide +kernel)

private def st495 : List Sig := [wire35,raw2,wire14,raw1,raw0,raw3,raw4,raw5,raw6]

private theorem node495 : impossible 8 0 st495 := rectReject 8 st495 4 3 0 4 0 42 2 49 (by decide +kernel)

private def st496 : List Sig := [wire10,raw0,wire14,raw1,raw2,raw3,raw4,raw5,raw7]

private theorem node496 : impossible 8 0 st496 := rectReject 8 st496 3 1 0 5 2 49 0 35 (by decide +kernel)

private def st497 : List Sig := [wire13,raw0,wire14,raw1,raw2,raw3,raw4,raw5,raw6]

private theorem node497 : impossible 8 0 st497 := rectReject 8 st497 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st498 : List Sig := [wire51,raw5,wire14,raw1,raw2,raw0,raw3,raw4,raw7]

private theorem node498 : impossible 8 0 st498 := rectReject 8 st498 5 3 0 4 0 42 2 49 (by decide +kernel)

private def st499 : List Sig := [wire14,raw1,raw2,raw0,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node499 : impossible 9 0 st499 := by
  apply reject_branch 8 0 st499 [] [st467,st468,st469,st470,st471,st472,st473,st474,st475,st476,st477,st478,st479,st480,st481,st482,st483,st484,st485,st486,st487,st488,st489,st490,st491,st492,st493,st494,st495,st496,st497,st498]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node467
    · exact node468
    · exact node469
    · exact node470
    · exact node471
    · exact node472
    · exact node473
    · exact node474
    · exact node475
    · exact node476
    · exact node477
    · exact node478
    · exact node479
    · exact node480
    · exact node481
    · exact node482
    · exact node483
    · exact node484
    · exact node485
    · exact node486
    · exact node487
    · exact node488
    · exact node489
    · exact node490
    · exact node491
    · exact node492
    · exact node493
    · exact node494
    · exact node495
    · exact node496
    · exact node497
    · exact node498
  · decide +kernel

private def st500 : List Sig := [wire177,raw3,raw1,raw2,raw0,raw4,raw5,raw6,raw7]

private theorem node500 : impossible 8 0 st500 := rectReject 8 st500 4 2 0 4 0 42 2 7 (by decide +kernel)

private def st501 : List Sig := [wire178,raw3,raw1,raw2,raw0,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node501 : impossible 8 0 st501 := by_search (by decide +kernel)

private def st502 : List Sig := [wire179,raw4,raw1,raw2,raw0,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node502 : impossible 8 0 st502 := by_search (by decide +kernel)

private def st503 : List Sig := [wire180,raw4,raw1,raw2,raw0,raw3,raw5,raw6,raw7]

private theorem node503 : impossible 8 0 st503 := rectReject 8 st503 4 2 0 4 0 42 3 7 (by decide +kernel)

private def st504 : List Sig := [wire181,raw5,raw1,raw2,raw0,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node504 : impossible 8 0 st504 := by_search (by decide +kernel)

private def st505 : List Sig := [wire182,raw5,raw1,raw2,raw0,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node505 : impossible 8 0 st505 := by_search (by decide +kernel)

private def st506 : List Sig := [wire183,raw6,raw1,raw2,raw0,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node506 : impossible 8 0 st506 := by_search (by decide +kernel)

private def st507 : List Sig := [wire184,raw6,raw1,raw2,raw0,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node507 : impossible 8 0 st507 := by_search (by decide +kernel)

private def st508 : List Sig := [wire185,raw1,raw2,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node508 : impossible 8 0 st508 := by_search (by decide +kernel)

private def st509 : List Sig := [wire185,wire15,raw1,raw2,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node509 : impossible 8 0 st509 := by_search (by decide +kernel)

private def st510 : List Sig := [wire185,raw7,raw1,raw2,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node510 : impossible 8 0 st510 := by_search (by decide +kernel)

private def st511 : List Sig := [wire186,raw7,raw1,raw2,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node511 : impossible 8 0 st511 := by_search (by decide +kernel)

private def st512 : List Sig := [wire17,raw3,wire15,raw2,raw0,raw4,raw5,raw6,raw7]

private theorem node512 : impossible 8 0 st512 := rectReject 8 st512 4 0 0 4 0 42 3 7 (by decide +kernel)

private def st513 : List Sig := [wire23,raw1,wire15,raw2,raw0,raw3,raw4,raw5,raw7]

private theorem node513 : impossible 8 0 st513 := rectReject 8 st513 5 3 14 0 3 21 1 7 (by decide +kernel)

private def st514 : List Sig := [wire24,raw1,wire15,raw2,raw0,raw3,raw4,raw5,raw6]

private theorem node514 : impossible 8 0 st514 := rectReject 8 st514 4 1 0 4 0 42 3 7 (by decide +kernel)

private def st515 : List Sig := [wire35,wire15,raw1,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node515 : impossible 8 0 st515 := by_search (by decide +kernel)

private def st516 : List Sig := [wire35,raw2,wire15,raw1,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node516 : impossible 8 0 st516 := by_search (by decide +kernel)

private def st517 : List Sig := [wire35,raw7,wire15,raw1,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node517 : impossible 8 0 st517 := by_search (by decide +kernel)

private def st518 : List Sig := [wire187,raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

private theorem node518 : impossible 8 0 st518 := rectReject 8 st518 3 2 7 2 0 14 3 49 (by decide +kernel)

private def st519 : List Sig := [wire69,raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

private theorem node519 : impossible 8 0 st519 := rectReject 8 st519 2 1 0 4 2 7 0 42 (by decide +kernel)

private def st520 : List Sig := [wire3,raw0,wire15,raw1,raw3,raw4,raw5,raw6,raw7]

private theorem node520 : impossible 8 0 st520 := rectReject 8 st520 4 0 14 0 3 21 1 7 (by decide +kernel)

private def st521 : List Sig := [wire10,raw0,wire15,raw1,raw2,raw3,raw4,raw5,raw7]

private theorem node521 : impossible 8 0 st521 := rectReject 8 st521 3 1 0 5 3 7 0 35 (by decide +kernel)

private def st522 : List Sig := [wire13,raw0,wire15,raw1,raw2,raw3,raw4,raw5,raw6]

private theorem node522 : impossible 8 0 st522 := rectReject 8 st522 5 4 14 0 3 21 1 7 (by decide +kernel)

private def st523 : List Sig := [wire51,raw5,wire15,raw1,raw2,raw0,raw3,raw4,raw7]

private theorem node523 : impossible 8 0 st523 := rectReject 8 st523 5 3 0 4 0 42 3 7 (by decide +kernel)

private def st524 : List Sig := [wire15,raw1,raw2,raw0,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node524 : impossible 9 0 st524 := by
  apply reject_branch 8 0 st524 [] [st500,st501,st502,st503,st504,st505,st506,st507,st508,st509,st510,st511,st512,st513,st514,st515,st516,st517,st518,st519,st520,st521,st522,st523]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node500
    · exact node501
    · exact node502
    · exact node503
    · exact node504
    · exact node505
    · exact node506
    · exact node507
    · exact node508
    · exact node509
    · exact node510
    · exact node511
    · exact node512
    · exact node513
    · exact node514
    · exact node515
    · exact node516
    · exact node517
    · exact node518
    · exact node519
    · exact node520
    · exact node521
    · exact node522
    · exact node523
  · decide +kernel

private def st525 : List Sig := [wire16,raw1,raw3,raw0,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node525 : impossible 9 0 st525 := by_search (by decide +kernel)

private def st526 : List Sig := [wire188,raw5,raw1,raw3,raw0,raw2,raw4,raw6,raw7]

private theorem node526 : impossible 8 0 st526 := rectReject 8 st526 4 1 35 0 1 0 2 28 (by decide +kernel)

private def st527 : List Sig := [wire189,raw5,raw1,raw3,raw0,raw2,raw4,raw6,raw7]

private theorem node527 : impossible 8 0 st527 := rectReject 8 st527 4 1 35 0 1 0 2 28 (by decide +kernel)

private def st528 : List Sig := [wire190,raw6,raw1,raw3,raw0,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node528 : impossible 8 0 st528 := by_search (by decide +kernel)

private def st529 : List Sig := [wire191,raw6,raw1,raw3,raw0,raw2,raw4,raw5,raw7]

private theorem node529 : impossible 8 0 st529 := rectReject 8 st529 4 2 0 4 0 42 2 7 (by decide +kernel)

private def st530 : List Sig := [wire192,raw1,raw3,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node530 : impossible 8 0 st530 := by_search (by decide +kernel)

private def st531 : List Sig := [wire192,wire17,raw1,raw3,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node531 : impossible 8 0 st531 := by_search (by decide +kernel)

private def st532 : List Sig := [wire192,raw7,raw1,raw3,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node532 : impossible 8 0 st532 := by_search (by decide +kernel)

private def st533 : List Sig := [wire193,raw7,raw1,raw3,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node533 : impossible 8 0 st533 := by_search (by decide +kernel)

private def st534 : List Sig := [wire15,raw2,wire17,raw3,raw0,raw4,raw5,raw6,raw7]

private theorem node534 : impossible 8 0 st534 := rectReject 8 st534 4 0 0 6 0 35 2 49 (by decide +kernel)

private def st535 : List Sig := [wire19,raw4,wire17,raw3,raw0,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node535 : impossible 8 0 st535 := by_search (by decide +kernel)

private def st536 : List Sig := [wire23,raw1,wire17,raw3,raw0,raw2,raw4,raw5,raw7]

private theorem node536 : impossible 8 0 st536 := rectReject 8 st536 7 4 35 0 2 28 1 0 (by decide +kernel)

private def st537 : List Sig := [wire24,raw1,wire17,raw3,raw0,raw2,raw4,raw5,raw6]

private theorem node537 : impossible 8 0 st537 := rectReject 8 st537 7 4 35 0 2 28 1 0 (by decide +kernel)

private def st538 : List Sig := [wire37,raw5,wire17,raw1,raw0,raw2,raw4,raw6,raw7]

private theorem node538 : impossible 8 0 st538 := rectReject 8 st538 4 3 0 6 0 35 2 49 (by decide +kernel)

private def st539 : List Sig := [wire41,raw7,wire17,raw1,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node539 : impossible 8 0 st539 := by_search (by decide +kernel)

private def st540 : List Sig := [wire194,raw0,raw1,raw3,raw2,raw4,raw5,raw6,raw7]

private theorem node540 : impossible 8 0 st540 := rectReject 8 st540 4 2 7 2 0 14 3 0 (by decide +kernel)

private def st541 : List Sig := [wire71,raw0,raw1,raw3,raw2,raw4,raw5,raw6,raw7]

private theorem node541 : impossible 8 0 st541 := rectReject 8 st541 2 1 0 6 2 49 0 35 (by decide +kernel)

private def st542 : List Sig := [wire5,raw0,wire17,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node542 : impossible 8 0 st542 := by_search (by decide +kernel)

private def st543 : List Sig := [wire10,raw0,wire17,raw1,raw3,raw2,raw4,raw5,raw7]

private theorem node543 : impossible 8 0 st543 := rectReject 8 st543 3 1 0 6 2 49 0 35 (by decide +kernel)

private def st544 : List Sig := [wire13,raw0,wire17,raw1,raw3,raw2,raw4,raw5,raw6]

private theorem node544 : impossible 8 0 st544 := rectReject 8 st544 7 1 35 4 2 28 5 42 (by decide +kernel)

private def st545 : List Sig := [wire195,raw1,raw3,raw0,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node545 : impossible 8 0 st545 := by_search (by decide +kernel)

private def st546 : List Sig := [wire195,raw2,raw1,raw3,raw0,raw4,raw5,raw6,raw7]

private theorem node546 : impossible 8 0 st546 := rectReject 8 st546 4 2 0 4 0 42 2 49 (by decide +kernel)

private def st547 : List Sig := [wire195,wire17,raw1,raw3,raw0,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node547 : impossible 8 0 st547 := by_search (by decide +kernel)

private def st548 : List Sig := [wire178,raw2,raw1,raw3,raw0,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node548 : impossible 8 0 st548 := by_search (by decide +kernel)

private def st549 : List Sig := [wire27,raw2,wire17,raw1,raw0,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node549 : impossible 8 0 st549 := by_search (by decide +kernel)

private def st550 : List Sig := [wire35,raw2,wire17,raw1,raw3,raw0,raw4,raw5,raw6]

private theorem node550 : impossible 8 0 st550 := rectReject 8 st550 5 3 0 6 0 35 2 49 (by decide +kernel)

private def st551 : List Sig := [wire196,raw4,raw1,raw3,raw0,raw2,raw5,raw6,raw7]

private theorem node551 : impossible 8 0 st551 := rectReject 8 st551 4 2 0 4 0 42 2 7 (by decide +kernel)

private def st552 : List Sig := [wire197,raw4,raw1,raw3,raw0,raw2,raw5,raw6,raw7]

private theorem node552 : impossible 8 0 st552 := rectReject 8 st552 4 2 0 4 0 42 2 7 (by decide +kernel)

private def st553 : List Sig := [wire42,raw4,wire17,raw1,raw0,raw2,raw5,raw6,raw7]

private theorem node553 : impossible 8 0 st553 := rectReject 8 st553 4 3 0 6 0 35 2 49 (by decide +kernel)

private def st554 : List Sig := [wire51,raw5,wire17,raw1,raw3,raw0,raw2,raw4,raw7]

private theorem node554 : impossible 8 0 st554 := rectReject 8 st554 5 3 0 6 0 35 2 49 (by decide +kernel)

private def st555 : List Sig := [wire17,raw1,raw3,raw0,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node555 : impossible 9 0 st555 := by
  apply reject_branch 8 0 st555 [] [st526,st527,st528,st529,st530,st531,st532,st533,st534,st535,st536,st537,st538,st539,st540,st541,st542,st543,st544,st545,st546,st547,st548,st549,st550,st551,st552,st553,st554]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node526
    · exact node527
    · exact node528
    · exact node529
    · exact node530
    · exact node531
    · exact node532
    · exact node533
    · exact node534
    · exact node535
    · exact node536
    · exact node537
    · exact node538
    · exact node539
    · exact node540
    · exact node541
    · exact node542
    · exact node543
    · exact node544
    · exact node545
    · exact node546
    · exact node547
    · exact node548
    · exact node549
    · exact node550
    · exact node551
    · exact node552
    · exact node553
    · exact node554
  · decide +kernel

private def st556 : List Sig := [wire18,raw1,raw4,raw0,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node556 : impossible 9 0 st556 := by_search (by decide +kernel)

private def st557 : List Sig := [wire19,raw1,raw4,raw0,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node557 : impossible 9 0 st557 := by_search (by decide +kernel)

private def st558 : List Sig := [wire20,raw1,raw5,raw0,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node558 : impossible 9 0 st558 := by_search (by decide +kernel)

private def st559 : List Sig := [wire198,raw6,raw1,raw5,raw0,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node559 : impossible 8 0 st559 := by_search (by decide +kernel)

private def st560 : List Sig := [wire199,raw1,raw5,raw0,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node560 : impossible 8 0 st560 := by_search (by decide +kernel)

private def st561 : List Sig := [wire199,wire21,raw1,raw5,raw0,raw2,raw3,raw4,raw7]

private theorem node561 : impossible 8 0 st561 := rectReject 8 st561 5 2 7 6 0 14 5 49 (by decide +kernel)

private def st562 : List Sig := [wire199,raw6,raw1,raw5,raw0,raw2,raw3,raw4,raw7]

private theorem node562 : impossible 8 0 st562 := rectReject 8 st562 5 2 7 6 0 14 4 49 (by decide +kernel)

private def st563 : List Sig := [wire200,raw1,raw5,raw0,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node563 : impossible 8 0 st563 := by_search (by decide +kernel)

private def st564 : List Sig := [wire200,wire21,raw1,raw5,raw0,raw2,raw3,raw4,raw6]

private theorem node564 : impossible 8 0 st564 := rectReject 8 st564 5 2 7 6 0 14 5 49 (by decide +kernel)

private def st565 : List Sig := [wire200,raw7,raw1,raw5,raw0,raw2,raw3,raw4,raw6]

private theorem node565 : impossible 8 0 st565 := rectReject 8 st565 4 2 0 4 0 42 2 7 (by decide +kernel)

private def st566 : List Sig := [wire201,raw7,raw1,raw5,raw0,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node566 : impossible 8 0 st566 := by_search (by decide +kernel)

private def st567 : List Sig := [wire19,raw4,wire21,raw5,raw0,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node567 : impossible 8 0 st567 := by_search (by decide +kernel)

private def st568 : List Sig := [wire23,raw1,wire21,raw5,raw0,raw2,raw3,raw4,raw7]

private theorem node568 : impossible 8 0 st568 := rectReject 8 st568 5 1 7 6 0 14 5 49 (by decide +kernel)

private def st569 : List Sig := [wire24,raw1,wire21,raw5,raw0,raw2,raw3,raw4,raw6]

private theorem node569 : impossible 8 0 st569 := rectReject 8 st569 6 5 14 0 3 21 1 7 (by decide +kernel)

private def st570 : List Sig := [wire51,raw5,wire21,raw1,raw0,raw2,raw3,raw4,raw7]

private theorem node570 : impossible 8 0 st570 := rectReject 8 st570 5 3 7 6 0 14 5 49 (by decide +kernel)

private def st571 : List Sig := [wire53,raw7,wire21,raw1,raw0,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node571 : impossible 8 0 st571 := by_search (by decide +kernel)

private def st572 : List Sig := [wire202,raw0,raw1,raw5,raw2,raw3,raw4,raw6,raw7]

private theorem node572 : impossible 8 0 st572 := rectReject 8 st572 4 2 7 2 0 14 3 49 (by decide +kernel)

private def st573 : List Sig := [wire75,raw0,raw1,raw5,raw2,raw3,raw4,raw6,raw7]

private theorem node573 : impossible 8 0 st573 := rectReject 8 st573 2 1 0 5 2 7 0 35 (by decide +kernel)

private def st574 : List Sig := [wire1,raw0,wire21,raw5,raw2,raw3,raw4,raw6,raw7]

private theorem node574 : impossible 8 0 st574 := rectReject 8 st574 4 0 7 6 0 14 5 49 (by decide +kernel)

private def st575 : List Sig := [wire9,raw0,wire21,raw1,raw2,raw3,raw4,raw6,raw7]

private theorem node575 : impossible 8 0 st575 := rectReject 8 st575 4 3 7 6 0 14 5 49 (by decide +kernel)

private def st576 : List Sig := [wire10,raw0,wire21,raw1,raw5,raw2,raw3,raw4,raw7]

private theorem node576 : impossible 8 0 st576 := rectReject 8 st576 5 3 7 6 0 14 5 49 (by decide +kernel)

private def st577 : List Sig := [wire13,raw0,wire21,raw1,raw5,raw2,raw3,raw4,raw6]

private theorem node577 : impossible 8 0 st577 := rectReject 8 st577 5 3 7 6 0 14 5 49 (by decide +kernel)

private def st578 : List Sig := [wire203,raw2,raw1,raw5,raw0,raw3,raw4,raw6,raw7]

private theorem node578 : impossible 8 0 st578 := rectReject 8 st578 4 2 0 4 0 42 2 49 (by decide +kernel)

private def st579 : List Sig := [wire182,raw2,raw1,raw5,raw0,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node579 : impossible 8 0 st579 := by_search (by decide +kernel)

private def st580 : List Sig := [wire31,raw2,wire21,raw1,raw0,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node580 : impossible 8 0 st580 := by_search (by decide +kernel)

private def st581 : List Sig := [wire35,raw2,wire21,raw1,raw5,raw0,raw3,raw4,raw6]

private theorem node581 : impossible 8 0 st581 := rectReject 8 st581 7 6 21 5 1 28 0 14 (by decide +kernel)

private def st582 : List Sig := [wire204,raw3,raw1,raw5,raw0,raw2,raw4,raw6,raw7]

private theorem node582 : impossible 8 0 st582 := rectReject 8 st582 4 2 0 4 0 42 2 7 (by decide +kernel)

private def st583 : List Sig := [wire189,raw3,raw1,raw5,raw0,raw2,raw4,raw6,raw7]

private theorem node583 : impossible 8 0 st583 := rectReject 8 st583 4 2 0 5 0 35 2 7 (by decide +kernel)

private def st584 : List Sig := [wire37,raw3,wire21,raw1,raw0,raw2,raw4,raw6,raw7]

private theorem node584 : impossible 8 0 st584 := rectReject 8 st584 5 3 7 6 0 14 5 49 (by decide +kernel)

private def st585 : List Sig := [wire205,raw4,raw1,raw5,raw0,raw2,raw3,raw6,raw7]

private theorem node585 : impossible 8 0 st585 := rectReject 8 st585 4 2 0 4 0 42 2 7 (by decide +kernel)

private def st586 : List Sig := [wire206,raw4,raw1,raw5,raw0,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node586 : impossible 8 0 st586 := by_search (by decide +kernel)

private def st587 : List Sig := [wire44,raw4,wire21,raw1,raw0,raw2,raw3,raw6,raw7]

private theorem node587 : impossible 8 0 st587 := rectReject 8 st587 5 3 7 6 0 14 5 49 (by decide +kernel)

private def st588 : List Sig := [wire21,raw1,raw5,raw0,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node588 : impossible 9 0 st588 := by
  apply reject_branch 8 0 st588 [] [st559,st560,st561,st562,st563,st564,st565,st566,st567,st568,st569,st570,st571,st572,st573,st574,st575,st576,st577,st578,st579,st580,st581,st582,st583,st584,st585,st586,st587]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node559
    · exact node560
    · exact node561
    · exact node562
    · exact node563
    · exact node564
    · exact node565
    · exact node566
    · exact node567
    · exact node568
    · exact node569
    · exact node570
    · exact node571
    · exact node572
    · exact node573
    · exact node574
    · exact node575
    · exact node576
    · exact node577
    · exact node578
    · exact node579
    · exact node580
    · exact node581
    · exact node582
    · exact node583
    · exact node584
    · exact node585
    · exact node586
    · exact node587
  · decide +kernel

private def st589 : List Sig := [wire22,raw1,raw6,raw0,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node589 : impossible 9 0 st589 := by_search (by decide +kernel)

private def st590 : List Sig := [wire207,wire23,raw1,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node590 : impossible 8 0 st590 := by_search (by decide +kernel)

private def st591 : List Sig := [wire207,wire23,raw7,raw1,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node591 : impossible 8 0 st591 := by_search (by decide +kernel)

private def st592 : List Sig := [wire208,wire23,raw7,raw1,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node592 : impossible 8 0 st592 := by_search (by decide +kernel)

private def st593 : List Sig := [wire14,raw1,raw2,wire23,raw0,raw3,raw4,raw5,raw7]

private theorem node593 : impossible 8 0 st593 := rectReject 8 st593 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st594 : List Sig := [wire15,raw1,raw2,wire23,raw0,raw3,raw4,raw5,raw7]

private theorem node594 : impossible 8 0 st594 := rectReject 8 st594 5 2 14 0 3 21 1 7 (by decide +kernel)

private def st595 : List Sig := [wire16,raw1,raw3,wire23,raw0,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node595 : impossible 8 0 st595 := by_search (by decide +kernel)

private def st596 : List Sig := [wire17,raw1,raw3,wire23,raw0,raw2,raw4,raw5,raw7]

private theorem node596 : impossible 8 0 st596 := rectReject 8 st596 7 4 35 0 2 28 1 0 (by decide +kernel)

private def st597 : List Sig := [wire18,raw1,raw4,wire23,raw0,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node597 : impossible 8 0 st597 := by_search (by decide +kernel)

private def st598 : List Sig := [wire19,raw1,raw4,wire23,raw0,raw2,raw3,raw5,raw7]

private theorem node598 : impossible 8 0 st598 := rectReject 8 st598 6 5 14 0 3 21 1 7 (by decide +kernel)

private def st599 : List Sig := [wire20,raw1,raw5,wire23,raw0,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node599 : impossible 8 0 st599 := by_search (by decide +kernel)

private def st600 : List Sig := [wire21,raw1,raw5,wire23,raw0,raw2,raw3,raw4,raw7]

private theorem node600 : impossible 8 0 st600 := rectReject 8 st600 5 1 7 6 0 14 5 49 (by decide +kernel)

private def st601 : List Sig := [wire24,raw1,wire23,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node601 : impossible 8 0 st601 := by_search (by decide +kernel)

private def st602 : List Sig := [wire24,raw1,raw7,wire23,raw0,raw2,raw3,raw4,raw5]

private theorem node602 : impossible 8 0 st602 := rectReject 8 st602 6 5 14 0 3 21 1 7 (by decide +kernel)

private def st603 : List Sig := [wire25,raw1,raw7,wire23,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node603 : impossible 8 0 st603 := by_search (by decide +kernel)

private def st604 : List Sig := [wire141,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node604 : impossible 8 0 st604 := by_search (by decide +kernel)

private def st605 : List Sig := [wire141,raw0,wire23,raw1,raw2,raw3,raw4,raw5,raw7]

private theorem node605 : impossible 8 0 st605 := rectReject 8 st605 4 3 7 6 0 14 4 49 (by decide +kernel)

private def st606 : List Sig := [wire77,raw0,wire23,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node606 : impossible 8 0 st606 := by_search (by decide +kernel)

private def st607 : List Sig := [wire0,raw0,raw1,wire23,raw2,raw3,raw4,raw5,raw7]

private theorem node607 : impossible 8 0 st607 := rectReject 8 st607 4 2 7 6 0 14 4 49 (by decide +kernel)

private def st608 : List Sig := [wire1,raw0,wire23,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node608 : impossible 8 0 st608 := by_search (by decide +kernel)

private def st609 : List Sig := [wire1,raw0,raw1,wire23,raw2,raw3,raw4,raw5,raw7]

private theorem node609 : impossible 8 0 st609 := rectReject 8 st609 5 4 14 0 3 21 1 7 (by decide +kernel)

private def st610 : List Sig := [wire2,raw0,raw2,wire23,raw1,raw3,raw4,raw5,raw7]

private theorem node610 : impossible 8 0 st610 := rectReject 8 st610 4 2 7 6 4 49 0 14 (by decide +kernel)

private def st611 : List Sig := [wire3,raw0,raw2,wire23,raw1,raw3,raw4,raw5,raw7]

private theorem node611 : impossible 8 0 st611 := rectReject 8 st611 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st612 : List Sig := [wire4,raw0,raw3,wire23,raw1,raw2,raw4,raw5,raw7]

private theorem node612 : impossible 8 0 st612 := rectReject 8 st612 5 2 14 0 1 7 3 21 (by decide +kernel)

private def st613 : List Sig := [wire5,raw0,raw3,wire23,raw1,raw2,raw4,raw5,raw7]

private theorem node613 : impossible 8 0 st613 := rectReject 8 st613 5 4 7 6 0 14 4 49 (by decide +kernel)

private def st614 : List Sig := [wire6,raw0,raw4,wire23,raw1,raw2,raw3,raw5,raw7]

private theorem node614 : impossible 8 0 st614 := rectReject 8 st614 5 4 7 6 0 14 4 49 (by decide +kernel)

private def st615 : List Sig := [wire7,raw0,raw4,wire23,raw1,raw2,raw3,raw5,raw7]

private theorem node615 : impossible 8 0 st615 := rectReject 8 st615 5 4 7 6 0 14 4 49 (by decide +kernel)

private def st616 : List Sig := [wire8,raw0,raw5,wire23,raw1,raw2,raw3,raw4,raw7]

private theorem node616 : impossible 8 0 st616 := rectReject 8 st616 5 4 7 6 0 14 4 49 (by decide +kernel)

private def st617 : List Sig := [wire9,raw0,raw5,wire23,raw1,raw2,raw3,raw4,raw7]

private theorem node617 : impossible 8 0 st617 := rectReject 8 st617 5 4 7 6 0 14 4 49 (by decide +kernel)

private def st618 : List Sig := [wire12,raw0,raw7,wire23,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node618 : impossible 8 0 st618 := by_search (by decide +kernel)

private def st619 : List Sig := [wire13,raw0,wire23,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node619 : impossible 8 0 st619 := by_search (by decide +kernel)

private def st620 : List Sig := [wire13,raw0,raw7,wire23,raw1,raw2,raw3,raw4,raw5]

private theorem node620 : impossible 8 0 st620 := rectReject 8 st620 5 4 7 6 0 14 4 49 (by decide +kernel)

private def st621 : List Sig := [wire209,raw2,wire23,raw1,raw0,raw3,raw4,raw5,raw7]

private theorem node621 : impossible 8 0 st621 := rectReject 8 st621 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st622 : List Sig := [wire184,raw2,wire23,raw1,raw0,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node622 : impossible 8 0 st622 := by_search (by decide +kernel)

private def st623 : List Sig := [wire26,raw2,raw3,wire23,raw1,raw0,raw4,raw5,raw7]

private theorem node623 : impossible 8 0 st623 := rectReject 8 st623 7 5 35 0 2 28 1 0 (by decide +kernel)

private def st624 : List Sig := [wire27,raw2,raw3,wire23,raw1,raw0,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node624 : impossible 8 0 st624 := by_search (by decide +kernel)

private def st625 : List Sig := [wire28,raw2,raw4,wire23,raw1,raw0,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node625 : impossible 8 0 st625 := by_search (by decide +kernel)

private def st626 : List Sig := [wire29,raw2,raw4,wire23,raw1,raw0,raw3,raw5,raw7]

private theorem node626 : impossible 8 0 st626 := rectReject 8 st626 7 5 35 0 2 28 1 0 (by decide +kernel)

private def st627 : List Sig := [wire30,raw2,raw5,wire23,raw1,raw0,raw3,raw4,raw7]

private theorem node627 : impossible 8 0 st627 := rectReject 8 st627 4 1 7 6 4 49 0 14 (by decide +kernel)

private def st628 : List Sig := [wire31,raw2,raw5,wire23,raw1,raw0,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node628 : impossible 8 0 st628 := by_search (by decide +kernel)

private def st629 : List Sig := [wire34,raw2,raw7,wire23,raw1,raw0,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node629 : impossible 8 0 st629 := by_search (by decide +kernel)

private def st630 : List Sig := [wire35,raw2,wire23,raw1,raw0,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node630 : impossible 8 0 st630 := by_search (by decide +kernel)

private def st631 : List Sig := [wire35,raw2,raw7,wire23,raw1,raw0,raw3,raw4,raw5]

private theorem node631 : impossible 8 0 st631 := rectReject 8 st631 7 6 21 5 1 28 0 14 (by decide +kernel)

private def st632 : List Sig := [wire210,raw3,wire23,raw1,raw0,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node632 : impossible 8 0 st632 := by_search (by decide +kernel)

private def st633 : List Sig := [wire191,raw3,wire23,raw1,raw0,raw2,raw4,raw5,raw7]

private theorem node633 : impossible 8 0 st633 := rectReject 8 st633 5 1 14 0 1 7 4 21 (by decide +kernel)

private def st634 : List Sig := [wire36,raw3,raw5,wire23,raw1,raw0,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node634 : impossible 8 0 st634 := by_search (by decide +kernel)

private def st635 : List Sig := [wire37,raw3,raw5,wire23,raw1,raw0,raw2,raw4,raw7]

private theorem node635 : impossible 8 0 st635 := rectReject 8 st635 6 4 7 6 0 14 4 49 (by decide +kernel)

private def st636 : List Sig := [wire40,raw3,raw7,wire23,raw1,raw0,raw2,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node636 : impossible 8 0 st636 := by_search (by decide +kernel)

private def st637 : List Sig := [wire41,raw3,raw7,wire23,raw1,raw0,raw2,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node637 : impossible 8 0 st637 := by_search (by decide +kernel)

private def st638 : List Sig := [wire211,raw4,wire23,raw1,raw0,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node638 : impossible 8 0 st638 := by_search (by decide +kernel)

private def st639 : List Sig := [wire212,raw4,wire23,raw1,raw0,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node639 : impossible 8 0 st639 := by_search (by decide +kernel)

private def st640 : List Sig := [wire42,raw4,raw3,wire23,raw1,raw0,raw2,raw5,raw7]

private theorem node640 : impossible 8 0 st640 := rectReject 8 st640 6 4 7 6 0 14 4 49 (by decide +kernel)

private def st641 : List Sig := [wire43,raw4,raw3,wire23,raw1,raw0,raw2,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node641 : impossible 8 0 st641 := by_search (by decide +kernel)

private def st642 : List Sig := [wire44,raw4,raw5,wire23,raw1,raw0,raw2,raw3,raw7]

private theorem node642 : impossible 8 0 st642 := rectReject 8 st642 6 4 7 6 0 14 4 49 (by decide +kernel)

private def st643 : List Sig := [wire45,raw4,raw5,wire23,raw1,raw0,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node643 : impossible 8 0 st643 := by_search (by decide +kernel)

private def st644 : List Sig := [wire48,raw4,raw7,wire23,raw1,raw0,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node644 : impossible 8 0 st644 := by_search (by decide +kernel)

private def st645 : List Sig := [wire49,raw4,raw7,wire23,raw1,raw0,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node645 : impossible 8 0 st645 := by_search (by decide +kernel)

private def st646 : List Sig := [wire213,raw5,wire23,raw1,raw0,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node646 : impossible 8 0 st646 := by_search (by decide +kernel)

private def st647 : List Sig := [wire199,raw5,raw1,raw0,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node647 : impossible 8 0 st647 := by_search (by decide +kernel)

private def st648 : List Sig := [wire199,raw5,wire23,raw1,raw0,raw2,raw3,raw4,raw7]

private theorem node648 : impossible 8 0 st648 := rectReject 8 st648 5 3 7 6 0 14 4 49 (by decide +kernel)

private def st649 : List Sig := [wire52,raw5,raw7,wire23,raw1,raw0,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node649 : impossible 8 0 st649 := by_search (by decide +kernel)

private def st650 : List Sig := [wire53,raw5,raw7,wire23,raw1,raw0,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node650 : impossible 8 0 st650 := by_search (by decide +kernel)

private def st651 : List Sig := [wire23,raw1,raw0,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node651 : impossible 9 0 st651 := by
  apply reject_branch 8 0 st651 [] [st590,st591,st592,st593,st594,st595,st596,st597,st598,st599,st600,st601,st602,st603,st604,st605,st606,st607,st608,st609,st610,st611,st612,st613,st614,st615,st616,st617,st618,st619,st620,st621,st622,st623,st624,st625,st626,st627,st628,st629,st630,st631,st632,st633,st634,st635,st636,st637,st638,st639,st640,st641,st642,st643,st644,st645,st646,st647,st648,st649,st650]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node590
    · exact node591
    · exact node592
    · exact node593
    · exact node594
    · exact node595
    · exact node596
    · exact node597
    · exact node598
    · exact node599
    · exact node600
    · exact node601
    · exact node602
    · exact node603
    · exact node604
    · exact node605
    · exact node606
    · exact node607
    · exact node608
    · exact node609
    · exact node610
    · exact node611
    · exact node612
    · exact node613
    · exact node614
    · exact node615
    · exact node616
    · exact node617
    · exact node618
    · exact node619
    · exact node620
    · exact node621
    · exact node622
    · exact node623
    · exact node624
    · exact node625
    · exact node626
    · exact node627
    · exact node628
    · exact node629
    · exact node630
    · exact node631
    · exact node632
    · exact node633
    · exact node634
    · exact node635
    · exact node636
    · exact node637
    · exact node638
    · exact node639
    · exact node640
    · exact node641
    · exact node642
    · exact node643
    · exact node644
    · exact node645
    · exact node646
    · exact node647
    · exact node648
    · exact node649
    · exact node650
  · decide +kernel

private def st652 : List Sig := [wire23,raw1,raw6,raw0,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node652 : impossible 9 0 st652 := by_search (by decide +kernel)

private def st653 : List Sig := [wire175,wire24,raw2,raw1,raw0,raw3,raw4,raw5,raw6]

private theorem node653 : impossible 8 0 st653 := rectReject 8 st653 3 2 7 2 3 0 0 14 (by decide +kernel)

private def st654 : List Sig := [wire219,wire152,raw3,raw1,raw0,raw4,raw5,raw6]

private theorem node654 : impossible 7 0 st654 := rectReject 7 st654 4 3 0 4 0 42 2 7 (by decide +kernel)

private def st655 : List Sig := [wire220,wire152,raw3,raw1,raw0,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node655 : impossible 7 0 st655 := by_search (by decide +kernel)

private def st656 : List Sig := [wire221,wire152,raw4,raw1,raw0,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node656 : impossible 7 0 st656 := by_search (by decide +kernel)

private def st657 : List Sig := [wire222,wire152,raw4,raw1,raw0,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node657 : impossible 7 0 st657 := by_search (by decide +kernel)

private def st658 : List Sig := [wire223,wire152,raw5,raw1,raw0,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node658 : impossible 7 0 st658 := by_search (by decide +kernel)

private def st659 : List Sig := [wire224,wire152,raw5,raw1,raw0,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node659 : impossible 7 0 st659 := by_search (by decide +kernel)

private def st660 : List Sig := [wire225,wire152,raw6,raw1,raw0,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node660 : impossible 7 0 st660 := by_search (by decide +kernel)

private def st661 : List Sig := [wire226,wire152,raw6,raw1,raw0,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node661 : impossible 7 0 st661 := by_search (by decide +kernel)

private def st662 : List Sig := [wire227,raw1,wire152,raw0,raw3,raw4,raw5,raw6]

private theorem node662 : impossible 7 0 st662 := rectReject 7 st662 5 4 21 5 1 28 0 14 (by decide +kernel)

private def st663 : List Sig := [wire15,raw1,wire152,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node663 : impossible 7 0 st663 := by_search (by decide +kernel)

private def st664 : List Sig := [wire16,raw1,raw3,wire152,raw0,raw4,raw5,raw6]

private theorem node664 : impossible 7 0 st664 := rectReject 7 st664 3 1 7 2 0 14 3 0 (by decide +kernel)

private def st665 : List Sig := [wire17,raw1,raw3,wire152,raw0,raw4,raw5,raw6]

private theorem node665 : impossible 7 0 st665 := rectReject 7 st665 6 4 35 0 2 28 1 0 (by decide +kernel)

private def st666 : List Sig := [wire18,raw1,raw4,wire152,raw0,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node666 : impossible 7 0 st666 := by_search (by decide +kernel)

private def st667 : List Sig := [wire19,raw1,raw4,wire152,raw0,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node667 : impossible 7 0 st667 := by_search (by decide +kernel)

private def st668 : List Sig := [wire20,raw1,raw5,wire152,raw0,raw3,raw4,raw6]

private theorem node668 : impossible 7 0 st668 := rectReject 7 st668 3 1 7 2 0 14 3 0 (by decide +kernel)

private def st669 : List Sig := [wire21,raw1,raw5,wire152,raw0,raw3,raw4,raw6]

private theorem node669 : impossible 7 0 st669 := rectReject 7 st669 5 3 14 0 3 21 1 7 (by decide +kernel)

private def st670 : List Sig := [wire22,raw1,raw6,wire152,raw0,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node670 : impossible 7 0 st670 := by_search (by decide +kernel)

private def st671 : List Sig := [wire23,raw1,wire152,raw0,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node671 : impossible 7 0 st671 := by_search (by decide +kernel)

private def st672 : List Sig := [wire23,raw1,raw6,wire152,raw0,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node672 : impossible 7 0 st672 := by_search (by decide +kernel)

private def st673 : List Sig := [wire228,raw0,wire152,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node673 : impossible 7 0 st673 := by_search (by decide +kernel)

private def st674 : List Sig := [wire229,raw0,wire152,raw1,raw3,raw4,raw5,raw6]

private theorem node674 : impossible 7 0 st674 := rectReject 7 st674 5 4 21 5 1 28 0 14 (by decide +kernel)

private def st675 : List Sig := [wire0,raw0,raw1,wire152,raw3,raw4,raw5,raw6]

private theorem node675 : impossible 7 0 st675 := rectReject 7 st675 4 3 14 0 3 21 1 7 (by decide +kernel)

private def st676 : List Sig := [wire1,raw0,raw1,wire152,raw3,raw4,raw5,raw6]

private theorem node676 : impossible 7 0 st676 := rectReject 7 st676 3 2 7 2 0 14 3 0 (by decide +kernel)

private def st677 : List Sig := [wire4,raw0,raw3,wire152,raw1,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node677 : impossible 7 0 st677 := by_search (by decide +kernel)

private def st678 : List Sig := [wire5,raw0,raw3,wire152,raw1,raw4,raw5,raw6]

private theorem node678 : impossible 7 0 st678 := rectReject 7 st678 4 3 7 2 3 0 0 14 (by decide +kernel)

private def st679 : List Sig := [wire6,raw0,raw4,wire152,raw1,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node679 : impossible 7 0 st679 := by_search (by decide +kernel)

private def st680 : List Sig := [wire7,raw0,raw4,wire152,raw1,raw3,raw5,raw6]

private theorem node680 : impossible 7 0 st680 := rectReject 7 st680 4 1 0 4 2 7 0 42 (by decide +kernel)

private def st681 : List Sig := [wire8,raw0,raw5,wire152,raw1,raw3,raw4,raw6]

private theorem node681 : impossible 7 0 st681 := rectReject 7 st681 4 1 0 4 2 7 0 42 (by decide +kernel)

private def st682 : List Sig := [wire9,raw0,raw5,wire152,raw1,raw3,raw4,raw6]

private theorem node682 : impossible 7 0 st682 := rectReject 7 st682 4 1 0 5 2 7 1 35 (by decide +kernel)

private def st683 : List Sig := [wire10,raw0,wire152,raw1,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node683 : impossible 7 0 st683 := by_search (by decide +kernel)

private def st684 : List Sig := [wire10,raw0,raw6,wire152,raw1,raw3,raw4,raw5]

private theorem node684 : impossible 7 0 st684 := rectReject 7 st684 4 1 0 5 2 7 0 35 (by decide +kernel)

private def st685 : List Sig := [wire11,raw0,raw6,wire152,raw1,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node685 : impossible 7 0 st685 := by_search (by decide +kernel)

private def st686 : List Sig := [wire36,raw3,raw5,wire152,raw1,raw0,raw4,raw6]

private theorem node686 : impossible 7 0 st686 := rectReject 7 st686 3 1 14 0 1 7 3 21 (by decide +kernel)

private def st687 : List Sig := [wire37,raw3,raw5,wire152,raw1,raw0,raw4,raw6]

private theorem node687 : impossible 7 0 st687 := rectReject 7 st687 4 3 7 2 3 0 0 14 (by decide +kernel)

private def st688 : List Sig := [wire38,raw3,raw6,wire152,raw1,raw0,raw4,raw5]

private theorem node688 : impossible 7 0 st688 := rectReject 7 st688 3 1 14 0 1 7 3 21 (by decide +kernel)

private def st689 : List Sig := [wire39,raw3,raw6,wire152,raw1,raw0,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node689 : impossible 7 0 st689 := by_search (by decide +kernel)

private def st690 : List Sig := [wire42,raw4,raw3,wire152,raw1,raw0,raw5,raw6]

private theorem node690 : impossible 7 0 st690 := rectReject 7 st690 4 3 7 2 3 0 0 14 (by decide +kernel)

private def st691 : List Sig := [wire43,raw4,raw3,wire152,raw1,raw0,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node691 : impossible 7 0 st691 := by_search (by decide +kernel)

private def st692 : List Sig := [wire44,raw4,raw5,wire152,raw1,raw0,raw3,raw6]

private theorem node692 : impossible 7 0 st692 := rectReject 7 st692 4 3 7 2 3 0 0 14 (by decide +kernel)

private def st693 : List Sig := [wire45,raw4,raw5,wire152,raw1,raw0,raw3,raw6]

set_option maxRecDepth 10000 in
private theorem node693 : impossible 7 0 st693 := by_search (by decide +kernel)

private def st694 : List Sig := [wire46,raw4,raw6,wire152,raw1,raw0,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node694 : impossible 7 0 st694 := by_search (by decide +kernel)

private def st695 : List Sig := [wire47,raw4,raw6,wire152,raw1,raw0,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node695 : impossible 7 0 st695 := by_search (by decide +kernel)

private def st696 : List Sig := [wire50,raw5,raw6,wire152,raw1,raw0,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node696 : impossible 7 0 st696 := by_search (by decide +kernel)

private def st697 : List Sig := [wire51,raw5,wire152,raw1,raw0,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node697 : impossible 7 0 st697 := by_search (by decide +kernel)

private def st698 : List Sig := [wire51,raw5,raw6,wire152,raw1,raw0,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node698 : impossible 7 0 st698 := by_search (by decide +kernel)

private def st699 : List Sig := [wire152,raw1,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node699 : impossible 8 0 st699 := by
  apply reject_branch 7 0 st699 [] [st654,st655,st656,st657,st658,st659,st660,st661,st662,st663,st664,st665,st666,st667,st668,st669,st670,st671,st672,st673,st674,st675,st676,st677,st678,st679,st680,st681,st682,st683,st684,st685,st686,st687,st688,st689,st690,st691,st692,st693,st694,st695,st696,st697,st698]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node654
    · exact node655
    · exact node656
    · exact node657
    · exact node658
    · exact node659
    · exact node660
    · exact node661
    · exact node662
    · exact node663
    · exact node664
    · exact node665
    · exact node666
    · exact node667
    · exact node668
    · exact node669
    · exact node670
    · exact node671
    · exact node672
    · exact node673
    · exact node674
    · exact node675
    · exact node676
    · exact node677
    · exact node678
    · exact node679
    · exact node680
    · exact node681
    · exact node682
    · exact node683
    · exact node684
    · exact node685
    · exact node686
    · exact node687
    · exact node688
    · exact node689
    · exact node690
    · exact node691
    · exact node692
    · exact node693
    · exact node694
    · exact node695
    · exact node696
    · exact node697
    · exact node698
  · decide +kernel

private def st700 : List Sig := [wire152,wire24,raw1,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node700 : impossible 8 0 st700 := by_search (by decide +kernel)

private def st701 : List Sig := [wire152,raw2,raw1,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node701 : impossible 8 0 st701 := by_search (by decide +kernel)

private def st702 : List Sig := [wire152,wire24,raw2,raw1,raw0,raw3,raw4,raw5,raw6]

private theorem node702 : impossible 8 0 st702 := rectReject 8 st702 4 3 0 4 0 42 2 7 (by decide +kernel)

private def st703 : List Sig := [wire214,wire24,raw3,raw1,raw0,raw2,raw4,raw5,raw6]

private theorem node703 : impossible 8 0 st703 := rectReject 8 st703 4 3 0 4 0 42 2 7 (by decide +kernel)

private def st704 : List Sig := [wire153,wire24,raw1,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node704 : impossible 8 0 st704 := by_search (by decide +kernel)

private def st705 : List Sig := [wire153,wire24,raw3,raw1,raw0,raw2,raw4,raw5,raw6]

private theorem node705 : impossible 8 0 st705 := rectReject 8 st705 4 3 0 4 0 42 2 7 (by decide +kernel)

private def st706 : List Sig := [wire215,wire24,raw4,raw1,raw0,raw2,raw3,raw5,raw6]

private theorem node706 : impossible 8 0 st706 := rectReject 8 st706 4 3 0 4 0 42 2 7 (by decide +kernel)

private def st707 : List Sig := [wire154,wire24,raw1,raw0,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node707 : impossible 8 0 st707 := by_search (by decide +kernel)

private def st708 : List Sig := [wire154,wire24,raw4,raw1,raw0,raw2,raw3,raw5,raw6]

private theorem node708 : impossible 8 0 st708 := rectReject 8 st708 4 3 0 4 0 42 2 7 (by decide +kernel)

private def st709 : List Sig := [wire216,wire24,raw5,raw1,raw0,raw2,raw3,raw4,raw6]

private theorem node709 : impossible 8 0 st709 := rectReject 8 st709 4 2 35 0 1 0 2 28 (by decide +kernel)

private def st710 : List Sig := [wire155,wire24,raw1,raw0,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node710 : impossible 8 0 st710 := by_search (by decide +kernel)

private def st711 : List Sig := [wire155,wire24,raw5,raw1,raw0,raw2,raw3,raw4,raw6]

private theorem node711 : impossible 8 0 st711 := rectReject 8 st711 4 3 0 4 0 42 2 7 (by decide +kernel)

private def st712 : List Sig := [wire217,wire24,raw6,raw1,raw0,raw2,raw3,raw4,raw5]

private theorem node712 : impossible 8 0 st712 := rectReject 8 st712 4 3 0 4 0 42 2 7 (by decide +kernel)

private def st713 : List Sig := [wire218,wire24,raw1,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node713 : impossible 8 0 st713 := by_search (by decide +kernel)

private def st714 : List Sig := [wire218,wire24,raw6,raw1,raw0,raw2,raw3,raw4,raw5]

private theorem node714 : impossible 8 0 st714 := rectReject 8 st714 4 3 0 4 0 42 2 7 (by decide +kernel)

private def st715 : List Sig := [wire14,raw1,raw2,wire24,raw0,raw3,raw4,raw5,raw6]

private theorem node715 : impossible 8 0 st715 := rectReject 8 st715 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st716 : List Sig := [wire15,raw1,raw2,wire24,raw0,raw3,raw4,raw5,raw6]

private theorem node716 : impossible 8 0 st716 := rectReject 8 st716 4 1 0 4 0 42 3 7 (by decide +kernel)

private def st717 : List Sig := [wire16,raw1,raw3,wire24,raw0,raw2,raw4,raw5,raw6]

private theorem node717 : impossible 8 0 st717 := rectReject 8 st717 4 1 0 4 0 42 2 7 (by decide +kernel)

private def st718 : List Sig := [wire17,raw1,raw3,wire24,raw0,raw2,raw4,raw5,raw6]

private theorem node718 : impossible 8 0 st718 := rectReject 8 st718 7 4 35 0 2 28 1 0 (by decide +kernel)

private def st719 : List Sig := [wire18,raw1,raw4,wire24,raw0,raw2,raw3,raw5,raw6]

private theorem node719 : impossible 8 0 st719 := rectReject 8 st719 4 1 0 4 0 42 2 7 (by decide +kernel)

private def st720 : List Sig := [wire19,raw1,raw4,wire24,raw0,raw2,raw3,raw5,raw6]

private theorem node720 : impossible 8 0 st720 := rectReject 8 st720 4 1 0 4 0 42 3 7 (by decide +kernel)

private def st721 : List Sig := [wire20,raw1,raw5,wire24,raw0,raw2,raw3,raw4,raw6]

private theorem node721 : impossible 8 0 st721 := rectReject 8 st721 4 1 0 4 0 42 2 7 (by decide +kernel)

private def st722 : List Sig := [wire21,raw1,raw5,wire24,raw0,raw2,raw3,raw4,raw6]

private theorem node722 : impossible 8 0 st722 := rectReject 8 st722 6 5 14 0 3 21 1 7 (by decide +kernel)

private def st723 : List Sig := [wire22,raw1,raw6,wire24,raw0,raw2,raw3,raw4,raw5]

private theorem node723 : impossible 8 0 st723 := rectReject 8 st723 4 1 0 4 0 42 2 7 (by decide +kernel)

private def st724 : List Sig := [wire23,raw1,wire24,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node724 : impossible 8 0 st724 := by_search (by decide +kernel)

private def st725 : List Sig := [wire23,raw1,raw6,wire24,raw0,raw2,raw3,raw4,raw5]

private theorem node725 : impossible 8 0 st725 := rectReject 8 st725 6 5 14 0 3 21 1 7 (by decide +kernel)

private def st726 : List Sig := [wire66,raw0,wire24,raw1,raw2,raw3,raw4,raw5,raw6]

private theorem node726 : impossible 8 0 st726 := rectReject 8 st726 3 1 0 4 2 7 0 42 (by decide +kernel)

private def st727 : List Sig := [wire230,wire157,raw2,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node727 : impossible 7 0 st727 := by_search (by decide +kernel)

private def st728 : List Sig := [wire229,wire157,raw2,raw1,raw3,raw4,raw5,raw6]

private theorem node728 : impossible 7 0 st728 := rectReject 7 st728 5 4 21 5 1 28 0 14 (by decide +kernel)

private def st729 : List Sig := [wire231,wire157,raw3,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node729 : impossible 7 0 st729 := by_search (by decide +kernel)

private def st730 : List Sig := [wire232,wire157,raw3,raw1,raw2,raw4,raw5,raw6]

private theorem node730 : impossible 7 0 st730 := rectReject 7 st730 4 3 7 2 0 14 3 0 (by decide +kernel)

private def st731 : List Sig := [wire233,wire157,raw4,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node731 : impossible 7 0 st731 := by_search (by decide +kernel)

private def st732 : List Sig := [wire234,wire157,raw4,raw1,raw2,raw3,raw5,raw6]

private theorem node732 : impossible 7 0 st732 := rectReject 7 st732 3 1 0 4 2 7 0 42 (by decide +kernel)

private def st733 : List Sig := [wire235,wire157,raw5,raw1,raw2,raw3,raw4,raw6]

private theorem node733 : impossible 7 0 st733 := rectReject 7 st733 3 1 0 4 2 7 0 42 (by decide +kernel)

private def st734 : List Sig := [wire236,wire157,raw5,raw1,raw2,raw3,raw4,raw6]

private theorem node734 : impossible 7 0 st734 := rectReject 7 st734 3 1 0 5 2 7 1 35 (by decide +kernel)

private def st735 : List Sig := [wire237,wire157,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node735 : impossible 7 0 st735 := by_search (by decide +kernel)

private def st736 : List Sig := [wire237,wire157,raw6,raw1,raw2,raw3,raw4,raw5]

private theorem node736 : impossible 7 0 st736 := rectReject 7 st736 3 1 0 5 2 7 0 35 (by decide +kernel)

private def st737 : List Sig := [wire238,wire157,raw6,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node737 : impossible 7 0 st737 := by_search (by decide +kernel)

private def st738 : List Sig := [wire158,raw1,wire157,raw2,raw3,raw4,raw5,raw6]

private theorem node738 : impossible 7 0 st738 := rectReject 7 st738 4 3 14 0 3 21 1 7 (by decide +kernel)

private def st739 : List Sig := [wire1,raw1,wire157,raw2,raw3,raw4,raw5,raw6]

private theorem node739 : impossible 7 0 st739 := rectReject 7 st739 3 1 7 2 0 14 3 0 (by decide +kernel)

private def st740 : List Sig := [wire14,raw1,raw2,wire157,raw3,raw4,raw5,raw6]

private theorem node740 : impossible 7 0 st740 := rectReject 7 st740 5 4 21 5 1 28 0 14 (by decide +kernel)

private def st741 : List Sig := [wire15,raw1,raw2,wire157,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node741 : impossible 7 0 st741 := by_search (by decide +kernel)

private def st742 : List Sig := [wire16,raw1,raw3,wire157,raw2,raw4,raw5,raw6]

private theorem node742 : impossible 7 0 st742 := rectReject 7 st742 3 1 0 4 0 42 2 7 (by decide +kernel)

private def st743 : List Sig := [wire17,raw1,raw3,wire157,raw2,raw4,raw5,raw6]

private theorem node743 : impossible 7 0 st743 := rectReject 7 st743 6 3 35 0 2 28 1 0 (by decide +kernel)

private def st744 : List Sig := [wire18,raw1,raw4,wire157,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node744 : impossible 7 0 st744 := by_search (by decide +kernel)

private def st745 : List Sig := [wire19,raw1,raw4,wire157,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node745 : impossible 7 0 st745 := by_search (by decide +kernel)

private def st746 : List Sig := [wire20,raw1,raw5,wire157,raw2,raw3,raw4,raw6]

private theorem node746 : impossible 7 0 st746 := rectReject 7 st746 3 1 0 4 0 42 2 7 (by decide +kernel)

private def st747 : List Sig := [wire21,raw1,raw5,wire157,raw2,raw3,raw4,raw6]

private theorem node747 : impossible 7 0 st747 := rectReject 7 st747 5 4 14 0 3 21 1 7 (by decide +kernel)

private def st748 : List Sig := [wire22,raw1,raw6,wire157,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node748 : impossible 7 0 st748 := by_search (by decide +kernel)

private def st749 : List Sig := [wire23,raw1,wire157,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node749 : impossible 7 0 st749 := by_search (by decide +kernel)

private def st750 : List Sig := [wire23,raw1,raw6,wire157,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node750 : impossible 7 0 st750 := by_search (by decide +kernel)

private def st751 : List Sig := [wire26,raw2,raw3,wire157,raw1,raw4,raw5,raw6]

private theorem node751 : impossible 7 0 st751 := rectReject 7 st751 4 3 0 4 2 7 0 42 (by decide +kernel)

private def st752 : List Sig := [wire27,raw2,raw3,wire157,raw1,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node752 : impossible 7 0 st752 := by_search (by decide +kernel)

private def st753 : List Sig := [wire28,raw2,raw4,wire157,raw1,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node753 : impossible 7 0 st753 := by_search (by decide +kernel)

private def st754 : List Sig := [wire29,raw2,raw4,wire157,raw1,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node754 : impossible 7 0 st754 := by_search (by decide +kernel)

private def st755 : List Sig := [wire30,raw2,raw5,wire157,raw1,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node755 : impossible 7 0 st755 := by_search (by decide +kernel)

private def st756 : List Sig := [wire31,raw2,raw5,wire157,raw1,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node756 : impossible 7 0 st756 := by_search (by decide +kernel)

private def st757 : List Sig := [wire32,raw2,raw6,wire157,raw1,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node757 : impossible 7 0 st757 := by_search (by decide +kernel)

private def st758 : List Sig := [wire33,raw2,raw6,wire157,raw1,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node758 : impossible 7 0 st758 := by_search (by decide +kernel)

private def st759 : List Sig := [wire36,raw3,raw5,wire157,raw1,raw2,raw4,raw6]

private theorem node759 : impossible 7 0 st759 := rectReject 7 st759 3 2 35 0 1 0 2 28 (by decide +kernel)

private def st760 : List Sig := [wire37,raw3,raw5,wire157,raw1,raw2,raw4,raw6]

private theorem node760 : impossible 7 0 st760 := rectReject 7 st760 4 3 0 4 2 7 0 42 (by decide +kernel)

private def st761 : List Sig := [wire38,raw3,raw6,wire157,raw1,raw2,raw4,raw5]

private theorem node761 : impossible 7 0 st761 := rectReject 7 st761 4 3 0 4 2 7 0 42 (by decide +kernel)

private def st762 : List Sig := [wire39,raw3,raw6,wire157,raw1,raw2,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node762 : impossible 7 0 st762 := by_search (by decide +kernel)

private def st763 : List Sig := [wire42,raw4,raw3,wire157,raw1,raw2,raw5,raw6]

private theorem node763 : impossible 7 0 st763 := rectReject 7 st763 4 3 0 4 2 7 0 42 (by decide +kernel)

private def st764 : List Sig := [wire43,raw4,raw3,wire157,raw1,raw2,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node764 : impossible 7 0 st764 := by_search (by decide +kernel)

private def st765 : List Sig := [wire44,raw4,raw5,wire157,raw1,raw2,raw3,raw6]

private theorem node765 : impossible 7 0 st765 := rectReject 7 st765 4 3 0 4 2 7 0 42 (by decide +kernel)

private def st766 : List Sig := [wire45,raw4,raw5,wire157,raw1,raw2,raw3,raw6]

set_option maxRecDepth 10000 in
private theorem node766 : impossible 7 0 st766 := by_search (by decide +kernel)

private def st767 : List Sig := [wire46,raw4,raw6,wire157,raw1,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node767 : impossible 7 0 st767 := by_search (by decide +kernel)

private def st768 : List Sig := [wire47,raw4,raw6,wire157,raw1,raw2,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node768 : impossible 7 0 st768 := by_search (by decide +kernel)

private def st769 : List Sig := [wire50,raw5,raw6,wire157,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node769 : impossible 7 0 st769 := by_search (by decide +kernel)

private def st770 : List Sig := [wire51,raw5,wire157,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node770 : impossible 7 0 st770 := by_search (by decide +kernel)

private def st771 : List Sig := [wire51,raw5,raw6,wire157,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node771 : impossible 7 0 st771 := by_search (by decide +kernel)

private def st772 : List Sig := [wire157,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node772 : impossible 8 0 st772 := by
  apply reject_branch 7 0 st772 [] [st727,st728,st729,st730,st731,st732,st733,st734,st735,st736,st737,st738,st739,st740,st741,st742,st743,st744,st745,st746,st747,st748,st749,st750,st751,st752,st753,st754,st755,st756,st757,st758,st759,st760,st761,st762,st763,st764,st765,st766,st767,st768,st769,st770,st771]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node727
    · exact node728
    · exact node729
    · exact node730
    · exact node731
    · exact node732
    · exact node733
    · exact node734
    · exact node735
    · exact node736
    · exact node737
    · exact node738
    · exact node739
    · exact node740
    · exact node741
    · exact node742
    · exact node743
    · exact node744
    · exact node745
    · exact node746
    · exact node747
    · exact node748
    · exact node749
    · exact node750
    · exact node751
    · exact node752
    · exact node753
    · exact node754
    · exact node755
    · exact node756
    · exact node757
    · exact node758
    · exact node759
    · exact node760
    · exact node761
    · exact node762
    · exact node763
    · exact node764
    · exact node765
    · exact node766
    · exact node767
    · exact node768
    · exact node769
    · exact node770
    · exact node771
  · decide +kernel

private def st773 : List Sig := [wire157,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node773 : impossible 8 0 st773 := by_search (by decide +kernel)

private def st774 : List Sig := [wire157,wire24,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node774 : impossible 8 0 st774 := by_search (by decide +kernel)

private def st775 : List Sig := [wire157,raw0,wire24,raw1,raw2,raw3,raw4,raw5,raw6]

private theorem node775 : impossible 8 0 st775 := rectReject 8 st775 4 3 7 2 0 14 3 0 (by decide +kernel)

private def st776 : List Sig := [wire0,raw0,raw1,wire24,raw2,raw3,raw4,raw5,raw6]

private theorem node776 : impossible 8 0 st776 := rectReject 8 st776 5 4 14 0 3 21 1 7 (by decide +kernel)

private def st777 : List Sig := [wire1,raw0,raw1,wire24,raw2,raw3,raw4,raw5,raw6]

private theorem node777 : impossible 8 0 st777 := rectReject 8 st777 4 2 7 2 0 14 3 0 (by decide +kernel)

private def st778 : List Sig := [wire2,raw0,raw2,wire24,raw1,raw3,raw4,raw5,raw6]

private theorem node778 : impossible 8 0 st778 := rectReject 8 st778 4 1 0 4 2 7 0 42 (by decide +kernel)

private def st779 : List Sig := [wire3,raw0,raw2,wire24,raw1,raw3,raw4,raw5,raw6]

private theorem node779 : impossible 8 0 st779 := rectReject 8 st779 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st780 : List Sig := [wire4,raw0,raw3,wire24,raw1,raw2,raw4,raw5,raw6]

private theorem node780 : impossible 8 0 st780 := rectReject 8 st780 4 1 0 4 2 7 0 42 (by decide +kernel)

private def st781 : List Sig := [wire5,raw0,raw3,wire24,raw1,raw2,raw4,raw5,raw6]

private theorem node781 : impossible 8 0 st781 := rectReject 8 st781 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st782 : List Sig := [wire6,raw0,raw4,wire24,raw1,raw2,raw3,raw5,raw6]

private theorem node782 : impossible 8 0 st782 := rectReject 8 st782 4 1 0 4 2 7 0 42 (by decide +kernel)

private def st783 : List Sig := [wire7,raw0,raw4,wire24,raw1,raw2,raw3,raw5,raw6]

private theorem node783 : impossible 8 0 st783 := rectReject 8 st783 4 1 0 4 2 7 0 42 (by decide +kernel)

private def st784 : List Sig := [wire8,raw0,raw5,wire24,raw1,raw2,raw3,raw4,raw6]

private theorem node784 : impossible 8 0 st784 := rectReject 8 st784 4 1 0 4 2 7 0 42 (by decide +kernel)

private def st785 : List Sig := [wire9,raw0,raw5,wire24,raw1,raw2,raw3,raw4,raw6]

private theorem node785 : impossible 8 0 st785 := rectReject 8 st785 4 1 0 5 2 7 1 35 (by decide +kernel)

private def st786 : List Sig := [wire156,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node786 : impossible 7 0 st786 := by_search (by decide +kernel)

private def st787 : List Sig := [wire156,wire10,raw0,raw1,raw2,raw3,raw4,raw5]

private theorem node787 : impossible 7 0 st787 := rectReject 7 st787 3 2 0 5 2 7 0 35 (by decide +kernel)

private def st788 : List Sig := [wire156,wire24,raw0,raw1,raw2,raw3,raw4,raw5]

private theorem node788 : impossible 7 0 st788 := rectReject 7 st788 3 2 0 5 2 7 0 35 (by decide +kernel)

private def st789 : List Sig := [wire121,raw0,wire24,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node789 : impossible 7 0 st789 := by_search (by decide +kernel)

private def st790 : List Sig := [wire121,wire10,raw0,wire24,raw2,raw3,raw4,raw5]

private theorem node790 : impossible 7 0 st790 := rectReject 7 st790 2 0 0 5 0 35 2 7 (by decide +kernel)

private def st791 : List Sig := [wire121,raw1,raw0,wire24,raw2,raw3,raw4,raw5]

private theorem node791 : impossible 7 0 st791 := rectReject 7 st791 5 4 14 0 3 21 1 7 (by decide +kernel)

private def st792 : List Sig := [wire123,wire10,raw0,wire24,raw1,raw3,raw4,raw5]

private theorem node792 : impossible 7 0 st792 := rectReject 7 st792 4 0 7 2 3 0 0 14 (by decide +kernel)

private def st793 : List Sig := [wire125,wire10,raw0,wire24,raw1,raw2,raw4,raw5]

private theorem node793 : impossible 7 0 st793 := rectReject 7 st793 4 2 0 5 2 7 0 35 (by decide +kernel)

private def st794 : List Sig := [wire127,wire10,raw0,wire24,raw1,raw2,raw3,raw5]

private theorem node794 : impossible 7 0 st794 := rectReject 7 st794 4 2 0 5 2 7 0 35 (by decide +kernel)

private def st795 : List Sig := [wire128,raw0,wire24,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node795 : impossible 7 0 st795 := by_search (by decide +kernel)

private def st796 : List Sig := [wire128,wire10,raw0,wire24,raw1,raw2,raw3,raw4]

private theorem node796 : impossible 7 0 st796 := rectReject 7 st796 2 0 35 0 1 0 2 28 (by decide +kernel)

private def st797 : List Sig := [wire128,raw5,raw0,wire24,raw1,raw2,raw3,raw4]

private theorem node797 : impossible 7 0 st797 := rectReject 7 st797 4 2 0 5 2 7 0 35 (by decide +kernel)

private def st798 : List Sig := [wire157,wire10,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node798 : impossible 7 0 st798 := by_search (by decide +kernel)

private def st799 : List Sig := [wire157,raw0,wire10,raw1,raw2,raw3,raw4,raw5]

private theorem node799 : impossible 7 0 st799 := rectReject 7 st799 4 3 7 2 0 14 3 0 (by decide +kernel)

private def st800 : List Sig := [wire157,wire24,wire10,raw1,raw2,raw3,raw4,raw5]

private theorem node800 : impossible 7 0 st800 := rectReject 7 st800 3 0 0 5 2 7 0 35 (by decide +kernel)

private def st801 : List Sig := [wire152,wire10,raw0,raw1,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node801 : impossible 7 0 st801 := by_search (by decide +kernel)

private def st802 : List Sig := [wire152,wire24,wire10,raw0,raw1,raw3,raw4,raw5]

private theorem node802 : impossible 7 0 st802 := rectReject 7 st802 4 0 7 2 3 0 0 14 (by decide +kernel)

private def st803 : List Sig := [wire152,raw2,wire10,raw0,raw1,raw3,raw4,raw5]

private theorem node803 : impossible 7 0 st803 := rectReject 7 st803 4 3 0 5 2 7 0 35 (by decide +kernel)

private def st804 : List Sig := [wire153,wire24,wire10,raw0,raw1,raw2,raw4,raw5]

private theorem node804 : impossible 7 0 st804 := rectReject 7 st804 4 3 0 5 2 7 0 35 (by decide +kernel)

private def st805 : List Sig := [wire154,wire24,wire10,raw0,raw1,raw2,raw3,raw5]

private theorem node805 : impossible 7 0 st805 := rectReject 7 st805 4 3 0 5 2 7 0 35 (by decide +kernel)

private def st806 : List Sig := [wire155,wire24,wire10,raw0,raw1,raw2,raw3,raw4]

private theorem node806 : impossible 7 0 st806 := rectReject 7 st806 3 0 35 0 1 0 2 28 (by decide +kernel)

private def st807 : List Sig := [wire10,raw0,wire24,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node807 : impossible 8 0 st807 := by
  apply reject_branch 7 0 st807 [] [st786,st787,st788,st789,st790,st791,st792,st793,st794,st795,st796,st797,st798,st799,st800,st801,st802,st803,st804,st805,st806]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node786
    · exact node787
    · exact node788
    · exact node789
    · exact node790
    · exact node791
    · exact node792
    · exact node793
    · exact node794
    · exact node795
    · exact node796
    · exact node797
    · exact node798
    · exact node799
    · exact node800
    · exact node801
    · exact node802
    · exact node803
    · exact node804
    · exact node805
    · exact node806
  · decide +kernel

private def st808 : List Sig := [wire10,raw0,raw6,wire24,raw1,raw2,raw3,raw4,raw5]

private theorem node808 : impossible 8 0 st808 := rectReject 8 st808 4 1 0 5 2 7 0 35 (by decide +kernel)

private def st809 : List Sig := [wire11,raw0,raw6,wire24,raw1,raw2,raw3,raw4,raw5]

private theorem node809 : impossible 8 0 st809 := rectReject 8 st809 4 1 0 4 2 7 0 42 (by decide +kernel)

private def st810 : List Sig := [wire26,raw2,raw3,wire24,raw1,raw0,raw4,raw5,raw6]

private theorem node810 : impossible 8 0 st810 := rectReject 8 st810 5 4 0 4 0 42 2 7 (by decide +kernel)

private def st811 : List Sig := [wire27,raw2,raw3,wire24,raw1,raw0,raw4,raw5,raw6]

private theorem node811 : impossible 8 0 st811 := rectReject 8 st811 4 1 7 2 3 0 1 14 (by decide +kernel)

private def st812 : List Sig := [wire28,raw2,raw4,wire24,raw1,raw0,raw3,raw5,raw6]

private theorem node812 : impossible 8 0 st812 := rectReject 8 st812 4 1 7 2 3 0 0 14 (by decide +kernel)

private def st813 : List Sig := [wire29,raw2,raw4,wire24,raw1,raw0,raw3,raw5,raw6]

private theorem node813 : impossible 8 0 st813 := rectReject 8 st813 5 4 0 4 0 42 2 7 (by decide +kernel)

private def st814 : List Sig := [wire30,raw2,raw5,wire24,raw1,raw0,raw3,raw4,raw6]

private theorem node814 : impossible 8 0 st814 := rectReject 8 st814 4 1 7 2 3 0 0 14 (by decide +kernel)

private def st815 : List Sig := [wire31,raw2,raw5,wire24,raw1,raw0,raw3,raw4,raw6]

private theorem node815 : impossible 8 0 st815 := rectReject 8 st815 5 2 35 4 1 42 3 28 (by decide +kernel)

private def st816 : List Sig := [wire32,raw2,raw6,wire24,raw1,raw0,raw3,raw4,raw5]

private theorem node816 : impossible 8 0 st816 := rectReject 8 st816 4 1 7 2 3 0 0 14 (by decide +kernel)

private def st817 : List Sig := [wire33,raw2,raw6,wire24,raw1,raw0,raw3,raw4,raw5]

private theorem node817 : impossible 8 0 st817 := rectReject 8 st817 5 4 0 4 0 42 2 7 (by decide +kernel)

private def st818 : List Sig := [wire36,raw3,raw5,wire24,raw1,raw0,raw2,raw4,raw6]

private theorem node818 : impossible 8 0 st818 := rectReject 8 st818 5 2 35 0 1 0 2 28 (by decide +kernel)

private def st819 : List Sig := [wire37,raw3,raw5,wire24,raw1,raw0,raw2,raw4,raw6]

private theorem node819 : impossible 8 0 st819 := rectReject 8 st819 5 4 0 4 0 42 2 7 (by decide +kernel)

private def st820 : List Sig := [wire38,raw3,raw6,wire24,raw1,raw0,raw2,raw4,raw5]

private theorem node820 : impossible 8 0 st820 := rectReject 8 st820 5 4 0 4 0 42 2 7 (by decide +kernel)

private def st821 : List Sig := [wire39,raw3,raw6,wire24,raw1,raw0,raw2,raw4,raw5]

private theorem node821 : impossible 8 0 st821 := rectReject 8 st821 5 4 0 4 0 42 2 7 (by decide +kernel)

private def st822 : List Sig := [wire42,raw4,raw3,wire24,raw1,raw0,raw2,raw5,raw6]

private theorem node822 : impossible 8 0 st822 := rectReject 8 st822 5 4 0 4 0 42 2 7 (by decide +kernel)

private def st823 : List Sig := [wire43,raw4,raw3,wire24,raw1,raw0,raw2,raw5,raw6]

private theorem node823 : impossible 8 0 st823 := rectReject 8 st823 5 4 0 4 0 42 2 7 (by decide +kernel)

private def st824 : List Sig := [wire44,raw4,raw5,wire24,raw1,raw0,raw2,raw3,raw6]

private theorem node824 : impossible 8 0 st824 := rectReject 8 st824 5 4 0 4 0 42 2 7 (by decide +kernel)

private def st825 : List Sig := [wire45,raw4,raw5,wire24,raw1,raw0,raw2,raw3,raw6]

private theorem node825 : impossible 8 0 st825 := rectReject 8 st825 5 2 35 0 1 0 3 28 (by decide +kernel)

private def st826 : List Sig := [wire46,raw4,raw6,wire24,raw1,raw0,raw2,raw3,raw5]

private theorem node826 : impossible 8 0 st826 := rectReject 8 st826 5 4 0 4 0 42 2 7 (by decide +kernel)

private def st827 : List Sig := [wire47,raw4,raw6,wire24,raw1,raw0,raw2,raw3,raw5]

private theorem node827 : impossible 8 0 st827 := rectReject 8 st827 5 4 0 4 0 42 2 7 (by decide +kernel)

private def st828 : List Sig := [wire50,raw5,raw6,wire24,raw1,raw0,raw2,raw3,raw4]

private theorem node828 : impossible 8 0 st828 := rectReject 8 st828 5 1 35 0 1 0 2 28 (by decide +kernel)

private def st829 : List Sig := [wire51,raw5,wire24,raw1,raw0,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node829 : impossible 8 0 st829 := by_search (by decide +kernel)

private def st830 : List Sig := [wire51,raw5,raw6,wire24,raw1,raw0,raw2,raw3,raw4]

private theorem node830 : impossible 8 0 st830 := rectReject 8 st830 5 4 0 4 0 42 2 7 (by decide +kernel)

private def st831 : List Sig := [wire24,raw1,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node831 : impossible 9 0 st831 := by
  apply reject_branch 8 0 st831 [] [st653,st699,st700,st701,st702,st703,st704,st705,st706,st707,st708,st709,st710,st711,st712,st713,st714,st715,st716,st717,st718,st719,st720,st721,st722,st723,st724,st725,st726,st772,st773,st774,st775,st776,st777,st778,st779,st780,st781,st782,st783,st784,st785,st807,st808,st809,st810,st811,st812,st813,st814,st815,st816,st817,st818,st819,st820,st821,st822,st823,st824,st825,st826,st827,st828,st829,st830]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node653
    · exact node699
    · exact node700
    · exact node701
    · exact node702
    · exact node703
    · exact node704
    · exact node705
    · exact node706
    · exact node707
    · exact node708
    · exact node709
    · exact node710
    · exact node711
    · exact node712
    · exact node713
    · exact node714
    · exact node715
    · exact node716
    · exact node717
    · exact node718
    · exact node719
    · exact node720
    · exact node721
    · exact node722
    · exact node723
    · exact node724
    · exact node725
    · exact node726
    · exact node772
    · exact node773
    · exact node774
    · exact node775
    · exact node776
    · exact node777
    · exact node778
    · exact node779
    · exact node780
    · exact node781
    · exact node782
    · exact node783
    · exact node784
    · exact node785
    · exact node807
    · exact node808
    · exact node809
    · exact node810
    · exact node811
    · exact node812
    · exact node813
    · exact node814
    · exact node815
    · exact node816
    · exact node817
    · exact node818
    · exact node819
    · exact node820
    · exact node821
    · exact node822
    · exact node823
    · exact node824
    · exact node825
    · exact node826
    · exact node827
    · exact node828
    · exact node829
    · exact node830
  · decide +kernel

private def st832 : List Sig := [wire175,raw2,raw1,raw7,raw0,raw3,raw4,raw5,raw6]

private theorem node832 : impossible 8 0 st832 := rectReject 8 st832 2 1 7 2 3 0 0 14 (by decide +kernel)

private def st833 : List Sig := [wire152,raw1,raw7,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node833 : impossible 8 0 st833 := by_search (by decide +kernel)

private def st834 : List Sig := [wire152,wire24,raw1,raw7,raw0,raw3,raw4,raw5,raw6]

private theorem node834 : impossible 8 0 st834 := rectReject 8 st834 2 0 7 2 3 0 0 14 (by decide +kernel)

private def st835 : List Sig := [wire152,raw2,raw1,raw7,raw0,raw3,raw4,raw5,raw6]

private theorem node835 : impossible 8 0 st835 := rectReject 8 st835 4 2 0 4 0 42 2 7 (by decide +kernel)

private def st836 : List Sig := [wire214,raw3,raw1,raw7,raw0,raw2,raw4,raw5,raw6]

private theorem node836 : impossible 8 0 st836 := rectReject 8 st836 4 2 0 4 0 42 2 7 (by decide +kernel)

private def st837 : List Sig := [wire153,raw1,raw7,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node837 : impossible 8 0 st837 := by_search (by decide +kernel)

private def st838 : List Sig := [wire153,wire24,raw1,raw7,raw0,raw2,raw4,raw5,raw6]

private theorem node838 : impossible 8 0 st838 := rectReject 8 st838 4 2 0 4 0 42 2 7 (by decide +kernel)

private def st839 : List Sig := [wire153,raw3,raw1,raw7,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node839 : impossible 8 0 st839 := by_search (by decide +kernel)

private def st840 : List Sig := [wire215,raw4,raw1,raw7,raw0,raw2,raw3,raw5,raw6]

private theorem node840 : impossible 8 0 st840 := rectReject 8 st840 4 2 0 4 0 42 2 7 (by decide +kernel)

private def st841 : List Sig := [wire154,raw1,raw7,raw0,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node841 : impossible 8 0 st841 := by_search (by decide +kernel)

private def st842 : List Sig := [wire154,wire24,raw1,raw7,raw0,raw2,raw3,raw5,raw6]

private theorem node842 : impossible 8 0 st842 := rectReject 8 st842 4 2 0 4 0 42 2 7 (by decide +kernel)

private def st843 : List Sig := [wire154,raw4,raw1,raw7,raw0,raw2,raw3,raw5,raw6]

private theorem node843 : impossible 8 0 st843 := rectReject 8 st843 4 2 0 4 0 42 2 7 (by decide +kernel)

private def st844 : List Sig := [wire216,raw5,raw1,raw7,raw0,raw2,raw3,raw4,raw6]

private theorem node844 : impossible 8 0 st844 := rectReject 8 st844 4 1 35 0 1 0 2 28 (by decide +kernel)

private def st845 : List Sig := [wire155,raw1,raw7,raw0,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node845 : impossible 8 0 st845 := by_search (by decide +kernel)

private def st846 : List Sig := [wire155,wire24,raw1,raw7,raw0,raw2,raw3,raw4,raw6]

private theorem node846 : impossible 8 0 st846 := rectReject 8 st846 4 0 35 0 1 0 2 28 (by decide +kernel)

private def st847 : List Sig := [wire155,raw5,raw1,raw7,raw0,raw2,raw3,raw4,raw6]

private theorem node847 : impossible 8 0 st847 := rectReject 8 st847 4 2 0 4 0 42 2 7 (by decide +kernel)

private def st848 : List Sig := [wire217,raw6,raw1,raw7,raw0,raw2,raw3,raw4,raw5]

private theorem node848 : impossible 8 0 st848 := rectReject 8 st848 4 2 0 4 0 42 2 7 (by decide +kernel)

private def st849 : List Sig := [wire218,raw1,raw7,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node849 : impossible 8 0 st849 := by_search (by decide +kernel)

private def st850 : List Sig := [wire218,wire24,raw1,raw7,raw0,raw2,raw3,raw4,raw5]

private theorem node850 : impossible 8 0 st850 := rectReject 8 st850 4 2 0 4 0 42 2 7 (by decide +kernel)

private def st851 : List Sig := [wire218,raw6,raw1,raw7,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node851 : impossible 8 0 st851 := by_search (by decide +kernel)

private def st852 : List Sig := [wire25,raw1,wire24,raw0,raw2,raw3,raw4,raw5,raw6]

private theorem node852 : impossible 8 0 st852 := rectReject 8 st852 3 1 0 4 0 42 2 7 (by decide +kernel)

private def st853 : List Sig := [wire23,raw1,wire24,raw7,raw0,raw2,raw3,raw4,raw5]

private theorem node853 : impossible 8 0 st853 := rectReject 8 st853 6 5 14 0 3 21 1 7 (by decide +kernel)

private def st854 : List Sig := [wire66,raw0,raw1,raw7,raw2,raw3,raw4,raw5,raw6]

private theorem node854 : impossible 8 0 st854 := rectReject 8 st854 2 1 0 4 2 7 0 42 (by decide +kernel)

private def st855 : List Sig := [wire157,raw1,raw7,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node855 : impossible 8 0 st855 := by_search (by decide +kernel)

private def st856 : List Sig := [wire157,raw0,raw1,raw7,raw2,raw3,raw4,raw5,raw6]

private theorem node856 : impossible 8 0 st856 := rectReject 8 st856 4 2 7 2 0 14 3 0 (by decide +kernel)

private def st857 : List Sig := [wire157,wire24,raw1,raw7,raw2,raw3,raw4,raw5,raw6]

private theorem node857 : impossible 8 0 st857 := rectReject 8 st857 2 0 0 4 2 7 0 42 (by decide +kernel)

private def st858 : List Sig := [wire12,raw0,wire24,raw1,raw2,raw3,raw4,raw5,raw6]

private theorem node858 : impossible 8 0 st858 := rectReject 8 st858 3 1 0 4 2 7 0 42 (by decide +kernel)

private def st859 : List Sig := [wire13,raw0,wire24,raw1,raw2,raw3,raw4,raw5,raw6]

private theorem node859 : impossible 8 0 st859 := rectReject 8 st859 4 3 7 2 0 14 3 0 (by decide +kernel)

private def st860 : List Sig := [wire10,raw0,wire24,raw1,raw7,raw2,raw3,raw4,raw5]

private theorem node860 : impossible 8 0 st860 := rectReject 8 st860 3 1 0 5 2 7 0 35 (by decide +kernel)

private def st861 : List Sig := [wire34,raw2,wire24,raw1,raw0,raw3,raw4,raw5,raw6]

private theorem node861 : impossible 8 0 st861 := rectReject 8 st861 3 1 7 2 3 0 0 14 (by decide +kernel)

private def st862 : List Sig := [wire35,raw2,wire24,raw1,raw0,raw3,raw4,raw5,raw6]

private theorem node862 : impossible 8 0 st862 := rectReject 8 st862 4 3 0 4 0 42 2 7 (by decide +kernel)

private def st863 : List Sig := [wire40,raw3,wire24,raw1,raw0,raw2,raw4,raw5,raw6]

private theorem node863 : impossible 8 0 st863 := rectReject 8 st863 4 3 0 4 0 42 2 7 (by decide +kernel)

private def st864 : List Sig := [wire41,raw3,wire24,raw1,raw0,raw2,raw4,raw5,raw6]

private theorem node864 : impossible 8 0 st864 := rectReject 8 st864 4 3 0 4 0 42 2 7 (by decide +kernel)

private def st865 : List Sig := [wire48,raw4,wire24,raw1,raw0,raw2,raw3,raw5,raw6]

private theorem node865 : impossible 8 0 st865 := rectReject 8 st865 4 3 0 4 0 42 2 7 (by decide +kernel)

private def st866 : List Sig := [wire49,raw4,wire24,raw1,raw0,raw2,raw3,raw5,raw6]

private theorem node866 : impossible 8 0 st866 := rectReject 8 st866 4 3 0 4 0 42 2 7 (by decide +kernel)

private def st867 : List Sig := [wire52,raw5,wire24,raw1,raw0,raw2,raw3,raw4,raw6]

private theorem node867 : impossible 8 0 st867 := rectReject 8 st867 4 1 35 0 1 0 2 28 (by decide +kernel)

private def st868 : List Sig := [wire53,raw5,wire24,raw1,raw0,raw2,raw3,raw4,raw6]

private theorem node868 : impossible 8 0 st868 := rectReject 8 st868 4 1 35 4 1 42 2 28 (by decide +kernel)

private def st869 : List Sig := [wire51,raw5,wire24,raw1,raw7,raw0,raw2,raw3,raw4]

private theorem node869 : impossible 8 0 st869 := rectReject 8 st869 5 3 0 4 0 42 2 7 (by decide +kernel)

private def st870 : List Sig := [wire54,raw6,wire24,raw1,raw0,raw2,raw3,raw4,raw5]

private theorem node870 : impossible 8 0 st870 := rectReject 8 st870 4 3 0 4 0 42 2 7 (by decide +kernel)

private def st871 : List Sig := [wire55,raw6,wire24,raw1,raw0,raw2,raw3,raw4,raw5]

private theorem node871 : impossible 8 0 st871 := rectReject 8 st871 4 3 0 4 0 42 2 7 (by decide +kernel)

private def st872 : List Sig := [wire24,raw1,raw7,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node872 : impossible 9 0 st872 := by
  apply reject_branch 8 0 st872 [] [st832,st833,st834,st835,st836,st837,st838,st839,st840,st841,st842,st843,st844,st845,st846,st847,st848,st849,st850,st851,st852,st853,st854,st855,st856,st857,st858,st859,st860,st861,st862,st863,st864,st865,st866,st867,st868,st869,st870,st871]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node832
    · exact node833
    · exact node834
    · exact node835
    · exact node836
    · exact node837
    · exact node838
    · exact node839
    · exact node840
    · exact node841
    · exact node842
    · exact node843
    · exact node844
    · exact node845
    · exact node846
    · exact node847
    · exact node848
    · exact node849
    · exact node850
    · exact node851
    · exact node852
    · exact node853
    · exact node854
    · exact node855
    · exact node856
    · exact node857
    · exact node858
    · exact node859
    · exact node860
    · exact node861
    · exact node862
    · exact node863
    · exact node864
    · exact node865
    · exact node866
    · exact node867
    · exact node868
    · exact node869
    · exact node870
    · exact node871
  · decide +kernel

private def st873 : List Sig := [wire25,raw1,raw7,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node873 : impossible 9 0 st873 := by_search (by decide +kernel)

private def st874 : List Sig := [wire239,raw4,raw2,raw3,raw0,raw1,raw5,raw6,raw7]

private theorem node874 : impossible 8 0 st874 := rectReject 8 st874 3 1 21 5 0 14 1 28 (by decide +kernel)

private def st875 : List Sig := [wire240,raw2,raw3,raw0,raw1,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node875 : impossible 8 0 st875 := by_search (by decide +kernel)

private def st876 : List Sig := [wire240,wire26,raw2,raw3,raw0,raw1,raw5,raw6,raw7]

private theorem node876 : impossible 8 0 st876 := rectReject 8 st876 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st877 : List Sig := [wire240,raw4,raw2,raw3,raw0,raw1,raw5,raw6,raw7]

private theorem node877 : impossible 8 0 st877 := rectReject 8 st877 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st878 : List Sig := [wire241,raw5,raw2,raw3,raw0,raw1,raw4,raw6,raw7]

private theorem node878 : impossible 8 0 st878 := rectReject 8 st878 3 2 14 0 3 21 1 7 (by decide +kernel)

private def st879 : List Sig := [wire242,raw2,raw3,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node879 : impossible 8 0 st879 := by_search (by decide +kernel)

private def st880 : List Sig := [wire242,wire26,raw2,raw3,raw0,raw1,raw4,raw6,raw7]

private theorem node880 : impossible 8 0 st880 := rectReject 8 st880 4 0 35 0 1 0 2 28 (by decide +kernel)

private def st881 : List Sig := [wire242,raw5,raw2,raw3,raw0,raw1,raw4,raw6,raw7]

private theorem node881 : impossible 8 0 st881 := rectReject 8 st881 3 2 14 0 5 21 1 7 (by decide +kernel)

private def st882 : List Sig := [wire243,raw6,raw2,raw3,raw0,raw1,raw4,raw5,raw7]

private theorem node882 : impossible 8 0 st882 := rectReject 8 st882 3 2 14 0 3 21 1 7 (by decide +kernel)

private def st883 : List Sig := [wire244,raw2,raw3,raw0,raw1,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node883 : impossible 8 0 st883 := by_search (by decide +kernel)

private def st884 : List Sig := [wire244,wire26,raw2,raw3,raw0,raw1,raw4,raw5,raw7]

private theorem node884 : impossible 8 0 st884 := rectReject 8 st884 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st885 : List Sig := [wire244,raw6,raw2,raw3,raw0,raw1,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node885 : impossible 8 0 st885 := by_search (by decide +kernel)

private def st886 : List Sig := [wire245,raw7,raw2,raw3,raw0,raw1,raw4,raw5,raw6]

private theorem node886 : impossible 8 0 st886 := rectReject 8 st886 3 2 14 0 3 21 1 7 (by decide +kernel)

private def st887 : List Sig := [wire246,raw2,raw3,raw0,raw1,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node887 : impossible 8 0 st887 := by_search (by decide +kernel)

private def st888 : List Sig := [wire246,wire26,raw2,raw3,raw0,raw1,raw4,raw5,raw6]

private theorem node888 : impossible 8 0 st888 := rectReject 8 st888 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st889 : List Sig := [wire246,raw7,raw2,raw3,raw0,raw1,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node889 : impossible 8 0 st889 := by_search (by decide +kernel)

private def st890 : List Sig := [wire240,wire35,raw3,raw0,raw1,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node890 : impossible 7 0 st890 := by_search (by decide +kernel)

private def st891 : List Sig := [wire240,wire26,wire35,raw3,raw0,raw1,raw5,raw6]

private theorem node891 : impossible 7 0 st891 := rectReject 7 st891 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st892 : List Sig := [wire240,raw4,wire35,raw3,raw0,raw1,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node892 : impossible 7 0 st892 := by_search (by decide +kernel)

private def st893 : List Sig := [wire242,wire26,wire35,raw3,raw0,raw1,raw4,raw6]

private theorem node893 : impossible 7 0 st893 := rectReject 7 st893 4 0 35 0 1 0 2 28 (by decide +kernel)

private def st894 : List Sig := [wire244,wire26,wire35,raw3,raw0,raw1,raw4,raw5]

private theorem node894 : impossible 7 0 st894 := rectReject 7 st894 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st895 : List Sig := [wire37,raw5,wire35,wire26,raw0,raw1,raw4,raw6]

private theorem node895 : impossible 7 0 st895 := rectReject 7 st895 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st896 : List Sig := [wire89,raw0,wire26,raw3,raw1,raw4,raw5,raw6]

private theorem node896 : impossible 7 0 st896 := rectReject 7 st896 6 1 35 4 2 28 5 42 (by decide +kernel)

private def st897 : List Sig := [wire248,wire26,wire35,raw3,raw1,raw4,raw5,raw6]

private theorem node897 : impossible 7 0 st897 := rectReject 7 st897 4 0 0 4 2 7 0 42 (by decide +kernel)

private def st898 : List Sig := [wire10,raw0,wire35,wire26,raw3,raw1,raw4,raw5]

private theorem node898 : impossible 7 0 st898 := rectReject 7 st898 5 1 0 5 2 7 0 35 (by decide +kernel)

private def st899 : List Sig := [wire227,raw1,wire26,raw3,raw0,raw4,raw5,raw6]

private theorem node899 : impossible 7 0 st899 := rectReject 7 st899 6 4 35 0 2 28 1 0 (by decide +kernel)

private def st900 : List Sig := [wire249,wire35,raw3,raw0,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node900 : impossible 7 0 st900 := by_search (by decide +kernel)

private def st901 : List Sig := [wire249,raw1,wire35,raw3,raw0,raw4,raw5,raw6]

private theorem node901 : impossible 7 0 st901 := rectReject 7 st901 6 4 35 0 2 28 1 0 (by decide +kernel)

private def st902 : List Sig := [wire249,wire26,wire35,raw3,raw0,raw4,raw5,raw6]

private theorem node902 : impossible 7 0 st902 := rectReject 7 st902 4 0 0 4 0 42 2 7 (by decide +kernel)

private def st903 : List Sig := [wire23,raw1,wire35,wire26,raw3,raw0,raw4,raw5]

private theorem node903 : impossible 7 0 st903 := rectReject 7 st903 7 5 35 0 2 28 1 0 (by decide +kernel)

private def st904 : List Sig := [wire42,raw4,wire35,wire26,raw0,raw1,raw5,raw6]

private theorem node904 : impossible 7 0 st904 := rectReject 7 st904 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st905 : List Sig := [wire51,raw5,wire35,wire26,raw3,raw0,raw1,raw4]

private theorem node905 : impossible 7 0 st905 := rectReject 7 st905 6 5 0 4 2 7 0 42 (by decide +kernel)

private def st906 : List Sig := [wire35,wire26,raw3,raw0,raw1,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node906 : impossible 8 0 st906 := by
  apply reject_branch 7 0 st906 [] [st890,st891,st892,st893,st894,st895,st896,st897,st898,st899,st900,st901,st902,st903,st904,st905]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node890
    · exact node891
    · exact node892
    · exact node893
    · exact node894
    · exact node895
    · exact node896
    · exact node897
    · exact node898
    · exact node899
    · exact node900
    · exact node901
    · exact node902
    · exact node903
    · exact node904
    · exact node905
  · decide +kernel

private def st907 : List Sig := [wire35,raw2,wire26,raw3,raw0,raw1,raw4,raw5,raw6]

private theorem node907 : impossible 8 0 st907 := rectReject 8 st907 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st908 : List Sig := [wire35,raw7,wire26,raw3,raw0,raw1,raw4,raw5,raw6]

private theorem node908 : impossible 8 0 st908 := rectReject 8 st908 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st909 : List Sig := [wire37,raw5,wire26,raw2,raw0,raw1,raw4,raw6,raw7]

private theorem node909 : impossible 8 0 st909 := rectReject 8 st909 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st910 : List Sig := [wire247,raw0,raw2,raw3,raw1,raw4,raw5,raw6,raw7]

private theorem node910 : impossible 8 0 st910 := rectReject 8 st910 3 2 14 0 3 21 1 7 (by decide +kernel)

private def st911 : List Sig := [wire248,raw2,raw3,raw1,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node911 : impossible 8 0 st911 := by_search (by decide +kernel)

private def st912 : List Sig := [wire248,raw0,raw2,raw3,raw1,raw4,raw5,raw6,raw7]

private theorem node912 : impossible 8 0 st912 := rectReject 8 st912 3 2 14 0 3 21 2 7 (by decide +kernel)

private def st913 : List Sig := [wire248,wire26,raw2,raw3,raw1,raw4,raw5,raw6,raw7]

private theorem node913 : impossible 8 0 st913 := rectReject 8 st913 4 0 0 4 2 7 0 42 (by decide +kernel)

private def st914 : List Sig := [wire3,raw0,wire26,raw3,raw1,raw4,raw5,raw6,raw7]

private theorem node914 : impossible 8 0 st914 := rectReject 8 st914 6 1 35 4 2 28 5 42 (by decide +kernel)

private def st915 : List Sig := [wire10,raw0,wire26,raw2,raw3,raw1,raw4,raw5,raw7]

private theorem node915 : impossible 8 0 st915 := rectReject 8 st915 5 1 0 5 2 7 0 35 (by decide +kernel)

private def st916 : List Sig := [wire13,raw0,wire26,raw2,raw3,raw1,raw4,raw5,raw6]

private theorem node916 : impossible 8 0 st916 := rectReject 8 st916 7 1 35 4 2 28 5 42 (by decide +kernel)

private def st917 : List Sig := [wire167,raw1,raw2,raw3,raw0,raw4,raw5,raw6,raw7]

private theorem node917 : impossible 8 0 st917 := rectReject 8 st917 2 1 7 2 0 14 3 0 (by decide +kernel)

private def st918 : List Sig := [wire249,raw2,raw3,raw0,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node918 : impossible 8 0 st918 := by_search (by decide +kernel)

private def st919 : List Sig := [wire249,raw1,raw2,raw3,raw0,raw4,raw5,raw6,raw7]

private theorem node919 : impossible 8 0 st919 := rectReject 8 st919 6 4 35 0 2 28 1 0 (by decide +kernel)

private def st920 : List Sig := [wire249,wire26,raw2,raw3,raw0,raw4,raw5,raw6,raw7]

private theorem node920 : impossible 8 0 st920 := rectReject 8 st920 4 0 0 4 0 42 2 7 (by decide +kernel)

private def st921 : List Sig := [wire14,raw1,wire26,raw3,raw0,raw4,raw5,raw6,raw7]

private theorem node921 : impossible 8 0 st921 := rectReject 8 st921 4 1 0 4 0 42 2 49 (by decide +kernel)

private def st922 : List Sig := [wire23,raw1,wire26,raw2,raw3,raw0,raw4,raw5,raw7]

private theorem node922 : impossible 8 0 st922 := rectReject 8 st922 7 5 35 0 2 28 1 0 (by decide +kernel)

private def st923 : List Sig := [wire24,raw1,wire26,raw2,raw3,raw0,raw4,raw5,raw6]

private theorem node923 : impossible 8 0 st923 := rectReject 8 st923 5 1 0 4 0 42 2 7 (by decide +kernel)

private def st924 : List Sig := [wire42,raw4,wire26,raw2,raw0,raw1,raw5,raw6,raw7]

private theorem node924 : impossible 8 0 st924 := rectReject 8 st924 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st925 : List Sig := [wire51,raw5,wire26,raw2,raw3,raw0,raw1,raw4,raw7]

private theorem node925 : impossible 8 0 st925 := rectReject 8 st925 6 5 0 4 2 7 0 42 (by decide +kernel)

private def st926 : List Sig := [wire26,raw2,raw3,raw0,raw1,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node926 : impossible 9 0 st926 := by
  apply reject_branch 8 0 st926 [] [st874,st875,st876,st877,st878,st879,st880,st881,st882,st883,st884,st885,st886,st887,st888,st889,st906,st907,st908,st909,st910,st911,st912,st913,st914,st915,st916,st917,st918,st919,st920,st921,st922,st923,st924,st925]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node874
    · exact node875
    · exact node876
    · exact node877
    · exact node878
    · exact node879
    · exact node880
    · exact node881
    · exact node882
    · exact node883
    · exact node884
    · exact node885
    · exact node886
    · exact node887
    · exact node888
    · exact node889
    · exact node906
    · exact node907
    · exact node908
    · exact node909
    · exact node910
    · exact node911
    · exact node912
    · exact node913
    · exact node914
    · exact node915
    · exact node916
    · exact node917
    · exact node918
    · exact node919
    · exact node920
    · exact node921
    · exact node922
    · exact node923
    · exact node924
    · exact node925
  · decide +kernel

private def st927 : List Sig := [wire27,raw2,raw3,raw0,raw1,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node927 : impossible 9 0 st927 := by_search (by decide +kernel)

private def st928 : List Sig := [wire28,raw2,raw4,raw0,raw1,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node928 : impossible 9 0 st928 := by_search (by decide +kernel)

private def st929 : List Sig := [wire260,wire250,raw2,raw4,raw0,raw1,raw6,raw7]

private theorem node929 : impossible 7 0 st929 := rectReject 7 st929 4 0 35 0 1 0 2 28 (by decide +kernel)

private def st930 : List Sig := [wire261,wire250,raw2,raw4,raw0,raw1,raw5,raw7]

private theorem node930 : impossible 7 0 st930 := rectReject 7 st930 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st931 : List Sig := [wire262,wire250,raw2,raw4,raw0,raw1,raw5,raw6]

private theorem node931 : impossible 7 0 st931 := rectReject 7 st931 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st932 : List Sig := [wire263,wire250,raw4,raw0,raw1,raw5,raw6,raw7]

private theorem node932 : impossible 7 0 st932 := rectReject 7 st932 4 3 0 4 2 7 0 42 (by decide +kernel)

private def st933 : List Sig := [wire35,wire250,raw4,raw0,raw1,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node933 : impossible 7 0 st933 := by_search (by decide +kernel)

private def st934 : List Sig := [wire35,raw2,wire250,raw4,raw0,raw1,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node934 : impossible 7 0 st934 := by_search (by decide +kernel)

private def st935 : List Sig := [wire35,raw7,wire250,raw4,raw0,raw1,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node935 : impossible 7 0 st935 := by_search (by decide +kernel)

private def st936 : List Sig := [wire240,wire250,raw2,raw0,raw1,raw5,raw6,raw7]

private theorem node936 : impossible 7 0 st936 := rectReject 7 st936 4 3 0 4 2 7 0 42 (by decide +kernel)

private def st937 : List Sig := [wire44,raw5,wire250,raw2,raw0,raw1,raw6,raw7]

private theorem node937 : impossible 7 0 st937 := rectReject 7 st937 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st938 : List Sig := [wire264,wire250,raw2,raw4,raw1,raw5,raw6,raw7]

private theorem node938 : impossible 7 0 st938 := rectReject 7 st938 4 0 0 4 2 7 0 42 (by decide +kernel)

private def st939 : List Sig := [wire3,raw0,wire250,raw4,raw1,raw5,raw6,raw7]

private theorem node939 : impossible 7 0 st939 := rectReject 7 st939 5 1 35 4 2 28 5 42 (by decide +kernel)

private def st940 : List Sig := [wire7,raw0,wire250,raw2,raw1,raw5,raw6,raw7]

private theorem node940 : impossible 7 0 st940 := rectReject 7 st940 4 1 0 4 2 7 0 42 (by decide +kernel)

private def st941 : List Sig := [wire10,raw0,wire250,raw2,raw4,raw1,raw5,raw7]

private theorem node941 : impossible 7 0 st941 := rectReject 7 st941 5 1 0 5 2 7 0 35 (by decide +kernel)

private def st942 : List Sig := [wire13,raw0,wire250,raw2,raw4,raw1,raw5,raw6]

private theorem node942 : impossible 7 0 st942 := rectReject 7 st942 6 1 35 4 2 28 5 42 (by decide +kernel)

private def st943 : List Sig := [wire265,wire250,raw2,raw4,raw0,raw5,raw6,raw7]

private theorem node943 : impossible 7 0 st943 := rectReject 7 st943 4 0 0 4 0 42 2 7 (by decide +kernel)

private def st944 : List Sig := [wire14,raw1,wire250,raw4,raw0,raw5,raw6,raw7]

private theorem node944 : impossible 7 0 st944 := rectReject 7 st944 4 1 0 4 0 42 2 49 (by decide +kernel)

private def st945 : List Sig := [wire23,raw1,wire250,raw2,raw4,raw0,raw5,raw7]

private theorem node945 : impossible 7 0 st945 := rectReject 7 st945 6 5 35 0 2 28 1 0 (by decide +kernel)

private def st946 : List Sig := [wire24,raw1,wire250,raw2,raw4,raw0,raw5,raw6]

private theorem node946 : impossible 7 0 st946 := rectReject 7 st946 5 1 0 4 0 42 2 7 (by decide +kernel)

private def st947 : List Sig := [wire51,raw5,wire250,raw2,raw4,raw0,raw1,raw7]

private theorem node947 : impossible 7 0 st947 := rectReject 7 st947 6 5 0 4 2 7 0 42 (by decide +kernel)

private def st948 : List Sig := [wire250,raw2,raw4,raw0,raw1,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node948 : impossible 8 0 st948 := by
  apply reject_branch 7 0 st948 [] [st929,st930,st931,st932,st933,st934,st935,st936,st937,st938,st939,st940,st941,st942,st943,st944,st945,st946,st947]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node929
    · exact node930
    · exact node931
    · exact node932
    · exact node933
    · exact node934
    · exact node935
    · exact node936
    · exact node937
    · exact node938
    · exact node939
    · exact node940
    · exact node941
    · exact node942
    · exact node943
    · exact node944
    · exact node945
    · exact node946
    · exact node947
  · decide +kernel

private def st949 : List Sig := [wire250,wire29,raw2,raw4,raw0,raw1,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node949 : impossible 8 0 st949 := by_search (by decide +kernel)

private def st950 : List Sig := [wire250,raw3,raw2,raw4,raw0,raw1,raw5,raw6,raw7]

private theorem node950 : impossible 8 0 st950 := rectReject 8 st950 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st951 : List Sig := [wire251,raw3,raw2,raw4,raw0,raw1,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node951 : impossible 8 0 st951 := by_search (by decide +kernel)

private def st952 : List Sig := [wire252,raw5,raw2,raw4,raw0,raw1,raw3,raw6,raw7]

private theorem node952 : impossible 8 0 st952 := rectReject 8 st952 5 2 7 2 3 0 0 14 (by decide +kernel)

private def st953 : List Sig := [wire253,raw5,raw2,raw4,raw0,raw1,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node953 : impossible 8 0 st953 := by_search (by decide +kernel)

private def st954 : List Sig := [wire254,raw6,raw2,raw4,raw0,raw1,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node954 : impossible 8 0 st954 := by_search (by decide +kernel)

private def st955 : List Sig := [wire255,raw6,raw2,raw4,raw0,raw1,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node955 : impossible 8 0 st955 := by_search (by decide +kernel)

private def st956 : List Sig := [wire256,raw7,raw2,raw4,raw0,raw1,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node956 : impossible 8 0 st956 := by_search (by decide +kernel)

private def st957 : List Sig := [wire257,raw7,raw2,raw4,raw0,raw1,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node957 : impossible 8 0 st957 := by_search (by decide +kernel)

private def st958 : List Sig := [wire27,raw3,wire29,raw4,raw0,raw1,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node958 : impossible 8 0 st958 := by_search (by decide +kernel)

private def st959 : List Sig := [wire31,raw5,wire29,raw4,raw0,raw1,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node959 : impossible 8 0 st959 := by_search (by decide +kernel)

private def st960 : List Sig := [wire266,wire35,raw4,raw0,raw1,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node960 : impossible 7 0 st960 := by_search (by decide +kernel)

private def st961 : List Sig := [wire250,wire35,raw4,raw0,raw1,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node961 : impossible 7 0 st961 := by_search (by decide +kernel)

private def st962 : List Sig := [wire250,wire29,wire35,raw4,raw0,raw1,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node962 : impossible 7 0 st962 := by_search (by decide +kernel)

private def st963 : List Sig := [wire250,raw3,wire35,raw4,raw0,raw1,raw5,raw6]

private theorem node963 : impossible 7 0 st963 := rectReject 7 st963 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st964 : List Sig := [wire43,raw3,wire35,wire29,raw0,raw1,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node964 : impossible 7 0 st964 := by_search (by decide +kernel)

private def st965 : List Sig := [wire44,raw5,wire35,wire29,raw0,raw1,raw3,raw6]

private theorem node965 : impossible 7 0 st965 := rectReject 7 st965 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st966 : List Sig := [wire89,raw0,wire29,raw4,raw1,raw3,raw5,raw6]

private theorem node966 : impossible 7 0 st966 := rectReject 7 st966 6 1 35 4 2 28 5 42 (by decide +kernel)

private def st967 : List Sig := [wire7,raw0,wire35,wire29,raw1,raw3,raw5,raw6]

private theorem node967 : impossible 7 0 st967 := rectReject 7 st967 4 1 0 4 2 7 0 42 (by decide +kernel)

private def st968 : List Sig := [wire10,raw0,wire35,wire29,raw4,raw1,raw3,raw5]

private theorem node968 : impossible 7 0 st968 := rectReject 7 st968 5 1 0 5 2 7 0 35 (by decide +kernel)

private def st969 : List Sig := [wire227,raw1,wire29,raw4,raw0,raw3,raw5,raw6]

private theorem node969 : impossible 7 0 st969 := rectReject 7 st969 6 4 35 0 2 28 1 0 (by decide +kernel)

private def st970 : List Sig := [wire180,raw1,wire35,raw4,raw0,raw3,raw5,raw6]

private theorem node970 : impossible 7 0 st970 := rectReject 7 st970 4 1 0 4 0 42 3 7 (by decide +kernel)

private def st971 : List Sig := [wire19,raw1,wire35,wire29,raw0,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node971 : impossible 7 0 st971 := by_search (by decide +kernel)

private def st972 : List Sig := [wire23,raw1,wire35,wire29,raw4,raw0,raw3,raw5]

private theorem node972 : impossible 7 0 st972 := rectReject 7 st972 7 5 35 0 2 28 1 0 (by decide +kernel)

private def st973 : List Sig := [wire51,raw5,wire35,wire29,raw4,raw0,raw1,raw3]

private theorem node973 : impossible 7 0 st973 := rectReject 7 st973 6 5 0 4 2 7 0 42 (by decide +kernel)

private def st974 : List Sig := [wire35,wire29,raw4,raw0,raw1,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node974 : impossible 8 0 st974 := by
  apply reject_branch 7 0 st974 [] [st960,st961,st962,st963,st964,st965,st966,st967,st968,st969,st970,st971,st972,st973]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node960
    · exact node961
    · exact node962
    · exact node963
    · exact node964
    · exact node965
    · exact node966
    · exact node967
    · exact node968
    · exact node969
    · exact node970
    · exact node971
    · exact node972
    · exact node973
  · decide +kernel

private def st975 : List Sig := [wire35,raw2,wire29,raw4,raw0,raw1,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node975 : impossible 8 0 st975 := by_search (by decide +kernel)

private def st976 : List Sig := [wire35,raw7,wire29,raw4,raw0,raw1,raw3,raw5,raw6]

private theorem node976 : impossible 8 0 st976 := rectReject 8 st976 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st977 : List Sig := [wire43,raw3,wire29,raw2,raw0,raw1,raw5,raw6,raw7]

private theorem node977 : impossible 8 0 st977 := rectReject 8 st977 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st978 : List Sig := [wire44,raw5,wire29,raw2,raw0,raw1,raw3,raw6,raw7]

private theorem node978 : impossible 8 0 st978 := rectReject 8 st978 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st979 : List Sig := [wire258,raw0,raw2,raw4,raw1,raw3,raw5,raw6,raw7]

private theorem node979 : impossible 8 0 st979 := rectReject 8 st979 4 1 0 4 2 7 0 42 (by decide +kernel)

private def st980 : List Sig := [wire83,raw0,raw2,raw4,raw1,raw3,raw5,raw6,raw7]

private theorem node980 : impossible 8 0 st980 := rectReject 8 st980 4 1 0 4 2 7 0 42 (by decide +kernel)

private def st981 : List Sig := [wire3,raw0,wire29,raw4,raw1,raw3,raw5,raw6,raw7]

private theorem node981 : impossible 8 0 st981 := rectReject 8 st981 6 1 35 4 2 28 5 42 (by decide +kernel)

private def st982 : List Sig := [wire7,raw0,wire29,raw2,raw1,raw3,raw5,raw6,raw7]

private theorem node982 : impossible 8 0 st982 := rectReject 8 st982 4 1 0 4 2 7 0 42 (by decide +kernel)

private def st983 : List Sig := [wire10,raw0,wire29,raw2,raw4,raw1,raw3,raw5,raw7]

private theorem node983 : impossible 8 0 st983 := rectReject 8 st983 5 1 0 5 2 7 0 35 (by decide +kernel)

private def st984 : List Sig := [wire13,raw0,wire29,raw2,raw4,raw1,raw3,raw5,raw6]

private theorem node984 : impossible 8 0 st984 := rectReject 8 st984 7 1 35 4 2 28 5 42 (by decide +kernel)

private def st985 : List Sig := [wire259,raw1,raw2,raw4,raw0,raw3,raw5,raw6,raw7]

private theorem node985 : impossible 8 0 st985 := rectReject 8 st985 4 1 0 4 0 42 2 49 (by decide +kernel)

private def st986 : List Sig := [wire180,raw1,raw2,raw4,raw0,raw3,raw5,raw6,raw7]

private theorem node986 : impossible 8 0 st986 := rectReject 8 st986 4 1 0 4 0 42 3 7 (by decide +kernel)

private def st987 : List Sig := [wire14,raw1,wire29,raw4,raw0,raw3,raw5,raw6,raw7]

private theorem node987 : impossible 8 0 st987 := rectReject 8 st987 4 1 0 4 0 42 2 49 (by decide +kernel)

private def st988 : List Sig := [wire19,raw1,wire29,raw2,raw0,raw3,raw5,raw6,raw7]

private theorem node988 : impossible 8 0 st988 := rectReject 8 st988 4 1 0 4 0 42 3 7 (by decide +kernel)

private def st989 : List Sig := [wire23,raw1,wire29,raw2,raw4,raw0,raw3,raw5,raw7]

private theorem node989 : impossible 8 0 st989 := rectReject 8 st989 7 5 35 0 2 28 1 0 (by decide +kernel)

private def st990 : List Sig := [wire24,raw1,wire29,raw2,raw4,raw0,raw3,raw5,raw6]

private theorem node990 : impossible 8 0 st990 := rectReject 8 st990 5 1 0 4 0 42 2 7 (by decide +kernel)

private def st991 : List Sig := [wire51,raw5,wire29,raw2,raw4,raw0,raw1,raw3,raw7]

private theorem node991 : impossible 8 0 st991 := rectReject 8 st991 6 5 0 4 2 7 0 42 (by decide +kernel)

private def st992 : List Sig := [wire29,raw2,raw4,raw0,raw1,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node992 : impossible 9 0 st992 := by
  apply reject_branch 8 0 st992 [] [st948,st949,st950,st951,st952,st953,st954,st955,st956,st957,st958,st959,st974,st975,st976,st977,st978,st979,st980,st981,st982,st983,st984,st985,st986,st987,st988,st989,st990,st991]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node948
    · exact node949
    · exact node950
    · exact node951
    · exact node952
    · exact node953
    · exact node954
    · exact node955
    · exact node956
    · exact node957
    · exact node958
    · exact node959
    · exact node974
    · exact node975
    · exact node976
    · exact node977
    · exact node978
    · exact node979
    · exact node980
    · exact node981
    · exact node982
    · exact node983
    · exact node984
    · exact node985
    · exact node986
    · exact node987
    · exact node988
    · exact node989
    · exact node990
    · exact node991
  · decide +kernel

private def st993 : List Sig := [wire30,raw2,raw5,raw0,raw1,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node993 : impossible 9 0 st993 := by_search (by decide +kernel)

private def st994 : List Sig := [wire31,raw2,raw5,raw0,raw1,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node994 : impossible 9 0 st994 := by_search (by decide +kernel)

private def st995 : List Sig := [wire32,raw2,raw6,raw0,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node995 : impossible 9 0 st995 := by_search (by decide +kernel)

private def st996 : List Sig := [wire33,raw2,raw6,raw0,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node996 : impossible 9 0 st996 := by_search (by decide +kernel)

private def st997 : List Sig := [wire34,raw2,raw7,raw0,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node997 : impossible 9 0 st997 := by_search (by decide +kernel)

private def st998 : List Sig := [wire240,raw3,wire35,raw0,raw1,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node998 : impossible 7 0 st998 := by_search (by decide +kernel)

private def st999 : List Sig := [wire240,wire26,raw3,wire35,raw0,raw1,raw5,raw6]

private theorem node999 : impossible 7 0 st999 := rectReject 7 st999 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1000 : List Sig := [wire240,raw4,raw3,wire35,raw0,raw1,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1000 : impossible 7 0 st1000 := by_search (by decide +kernel)

private def st1001 : List Sig := [wire242,wire26,raw3,wire35,raw0,raw1,raw4,raw6]

private theorem node1001 : impossible 7 0 st1001 := rectReject 7 st1001 4 0 35 0 1 0 2 28 (by decide +kernel)

private def st1002 : List Sig := [wire244,wire26,raw3,wire35,raw0,raw1,raw4,raw5]

private theorem node1002 : impossible 7 0 st1002 := rectReject 7 st1002 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1003 : List Sig := [wire37,raw5,wire26,wire35,raw0,raw1,raw4,raw6]

private theorem node1003 : impossible 7 0 st1003 := rectReject 7 st1003 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1004 : List Sig := [wire248,wire26,raw3,wire35,raw1,raw4,raw5,raw6]

private theorem node1004 : impossible 7 0 st1004 := rectReject 7 st1004 4 0 0 4 2 7 0 42 (by decide +kernel)

private def st1005 : List Sig := [wire10,raw0,wire26,raw3,wire35,raw1,raw4,raw5]

private theorem node1005 : impossible 7 0 st1005 := rectReject 7 st1005 5 1 0 5 2 7 0 35 (by decide +kernel)

private def st1006 : List Sig := [wire249,raw3,wire35,raw0,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1006 : impossible 7 0 st1006 := by_search (by decide +kernel)

private def st1007 : List Sig := [wire249,raw1,raw3,wire35,raw0,raw4,raw5,raw6]

private theorem node1007 : impossible 7 0 st1007 := rectReject 7 st1007 6 4 35 0 2 28 1 0 (by decide +kernel)

private def st1008 : List Sig := [wire249,wire26,raw3,wire35,raw0,raw4,raw5,raw6]

private theorem node1008 : impossible 7 0 st1008 := rectReject 7 st1008 4 0 0 4 0 42 2 7 (by decide +kernel)

private def st1009 : List Sig := [wire23,raw1,wire26,raw3,wire35,raw0,raw4,raw5]

private theorem node1009 : impossible 7 0 st1009 := rectReject 7 st1009 7 5 35 0 2 28 1 0 (by decide +kernel)

private def st1010 : List Sig := [wire42,raw4,wire26,wire35,raw0,raw1,raw5,raw6]

private theorem node1010 : impossible 7 0 st1010 := rectReject 7 st1010 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1011 : List Sig := [wire51,raw5,wire26,raw3,wire35,raw0,raw1,raw4]

private theorem node1011 : impossible 7 0 st1011 := rectReject 7 st1011 6 5 0 4 2 7 0 42 (by decide +kernel)

private def st1012 : List Sig := [wire26,raw3,wire35,raw0,raw1,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1012 : impossible 8 0 st1012 := by
  apply reject_branch 7 0 st1012 [] [st998,st999,st1000,st1001,st1002,st1003,st1004,st896,st1005,st1006,st1007,st1008,st899,st1009,st1010,st1011]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node998
    · exact node999
    · exact node1000
    · exact node1001
    · exact node1002
    · exact node1003
    · exact node1004
    · exact node896
    · exact node1005
    · exact node1006
    · exact node1007
    · exact node1008
    · exact node899
    · exact node1009
    · exact node1010
    · exact node1011
  · decide +kernel

private def st1013 : List Sig := [wire26,raw2,raw3,wire35,raw0,raw1,raw4,raw5,raw6]

private theorem node1013 : impossible 8 0 st1013 := rectReject 8 st1013 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1014 : List Sig := [wire27,raw2,raw3,wire35,raw0,raw1,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1014 : impossible 8 0 st1014 := by_search (by decide +kernel)

private def st1015 : List Sig := [wire28,raw2,raw4,wire35,raw0,raw1,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1015 : impossible 8 0 st1015 := by_search (by decide +kernel)

private def st1016 : List Sig := [wire250,raw4,wire35,raw0,raw1,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1016 : impossible 7 0 st1016 := by_search (by decide +kernel)

private def st1017 : List Sig := [wire250,wire29,raw4,wire35,raw0,raw1,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1017 : impossible 7 0 st1017 := by_search (by decide +kernel)

private def st1018 : List Sig := [wire250,raw3,raw4,wire35,raw0,raw1,raw5,raw6]

private theorem node1018 : impossible 7 0 st1018 := rectReject 7 st1018 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1019 : List Sig := [wire43,raw3,wire29,wire35,raw0,raw1,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1019 : impossible 7 0 st1019 := by_search (by decide +kernel)

private def st1020 : List Sig := [wire44,raw5,wire29,wire35,raw0,raw1,raw3,raw6]

private theorem node1020 : impossible 7 0 st1020 := rectReject 7 st1020 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1021 : List Sig := [wire7,raw0,wire29,wire35,raw1,raw3,raw5,raw6]

private theorem node1021 : impossible 7 0 st1021 := rectReject 7 st1021 4 1 0 4 2 7 0 42 (by decide +kernel)

private def st1022 : List Sig := [wire10,raw0,wire29,raw4,wire35,raw1,raw3,raw5]

private theorem node1022 : impossible 7 0 st1022 := rectReject 7 st1022 5 1 0 5 2 7 0 35 (by decide +kernel)

private def st1023 : List Sig := [wire180,raw1,raw4,wire35,raw0,raw3,raw5,raw6]

private theorem node1023 : impossible 7 0 st1023 := rectReject 7 st1023 4 1 0 4 0 42 3 7 (by decide +kernel)

private def st1024 : List Sig := [wire19,raw1,wire29,wire35,raw0,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1024 : impossible 7 0 st1024 := by_search (by decide +kernel)

private def st1025 : List Sig := [wire23,raw1,wire29,raw4,wire35,raw0,raw3,raw5]

private theorem node1025 : impossible 7 0 st1025 := rectReject 7 st1025 7 5 35 0 2 28 1 0 (by decide +kernel)

private def st1026 : List Sig := [wire51,raw5,wire29,raw4,wire35,raw0,raw1,raw3]

private theorem node1026 : impossible 7 0 st1026 := rectReject 7 st1026 6 5 0 4 2 7 0 42 (by decide +kernel)

private def st1027 : List Sig := [wire29,raw4,wire35,raw0,raw1,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1027 : impossible 8 0 st1027 := by
  apply reject_branch 7 0 st1027 [] [st960,st1016,st1017,st1018,st1019,st1020,st1021,st966,st1022,st1023,st1024,st969,st1025,st1026]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node960
    · exact node1016
    · exact node1017
    · exact node1018
    · exact node1019
    · exact node1020
    · exact node1021
    · exact node966
    · exact node1022
    · exact node1023
    · exact node1024
    · exact node969
    · exact node1025
    · exact node1026
  · decide +kernel

private def st1028 : List Sig := [wire29,raw2,raw4,wire35,raw0,raw1,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1028 : impossible 8 0 st1028 := by_search (by decide +kernel)

private def st1029 : List Sig := [wire30,raw2,raw5,wire35,raw0,raw1,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node1029 : impossible 8 0 st1029 := by_search (by decide +kernel)

private def st1030 : List Sig := [wire31,raw2,raw5,wire35,raw0,raw1,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node1030 : impossible 8 0 st1030 := by_search (by decide +kernel)

private def st1031 : List Sig := [wire32,raw2,raw6,wire35,raw0,raw1,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1031 : impossible 8 0 st1031 := by_search (by decide +kernel)

private def st1032 : List Sig := [wire33,raw2,raw6,wire35,raw0,raw1,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1032 : impossible 8 0 st1032 := by_search (by decide +kernel)

private def st1033 : List Sig := [wire267,raw0,wire35,raw2,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1033 : impossible 8 0 st1033 := by_search (by decide +kernel)

private def st1034 : List Sig := [wire89,raw0,wire35,raw2,raw1,raw3,raw4,raw5,raw6]

private theorem node1034 : impossible 8 0 st1034 := rectReject 8 st1034 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st1035 : List Sig := [wire2,raw0,raw2,wire35,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1035 : impossible 8 0 st1035 := by_search (by decide +kernel)

private def st1036 : List Sig := [wire3,raw0,raw2,wire35,raw1,raw3,raw4,raw5,raw6]

private theorem node1036 : impossible 8 0 st1036 := rectReject 8 st1036 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st1037 : List Sig := [wire0,raw0,raw1,wire35,raw2,raw3,raw4,raw5,raw6]

private theorem node1037 : impossible 8 0 st1037 := rectReject 8 st1037 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st1038 : List Sig := [wire1,raw0,raw1,wire35,raw2,raw3,raw4,raw5,raw6]

private theorem node1038 : impossible 8 0 st1038 := rectReject 8 st1038 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st1039 : List Sig := [wire4,raw0,raw3,wire35,raw2,raw1,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1039 : impossible 8 0 st1039 := by_search (by decide +kernel)

private def st1040 : List Sig := [wire5,raw0,raw3,wire35,raw2,raw1,raw4,raw5,raw6]

private theorem node1040 : impossible 8 0 st1040 := rectReject 8 st1040 5 1 0 6 2 49 1 35 (by decide +kernel)

private def st1041 : List Sig := [wire6,raw0,raw4,wire35,raw2,raw1,raw3,raw5,raw6]

private theorem node1041 : impossible 8 0 st1041 := rectReject 8 st1041 5 1 0 4 2 7 0 42 (by decide +kernel)

private def st1042 : List Sig := [wire7,raw0,raw4,wire35,raw2,raw1,raw3,raw5,raw6]

private theorem node1042 : impossible 8 0 st1042 := rectReject 8 st1042 5 1 0 4 2 7 0 42 (by decide +kernel)

private def st1043 : List Sig := [wire8,raw0,raw5,wire35,raw2,raw1,raw3,raw4,raw6]

private theorem node1043 : impossible 8 0 st1043 := rectReject 8 st1043 5 1 0 4 2 7 0 42 (by decide +kernel)

private def st1044 : List Sig := [wire9,raw0,raw5,wire35,raw2,raw1,raw3,raw4,raw6]

private theorem node1044 : impossible 8 0 st1044 := rectReject 8 st1044 5 1 0 5 2 7 1 35 (by decide +kernel)

private def st1045 : List Sig := [wire10,raw0,wire35,raw2,raw1,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1045 : impossible 8 0 st1045 := by_search (by decide +kernel)

private def st1046 : List Sig := [wire10,raw0,raw6,wire35,raw2,raw1,raw3,raw4,raw5]

private theorem node1046 : impossible 8 0 st1046 := rectReject 8 st1046 5 1 0 5 2 7 0 35 (by decide +kernel)

private def st1047 : List Sig := [wire11,raw0,raw6,wire35,raw2,raw1,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1047 : impossible 8 0 st1047 := by_search (by decide +kernel)

private def st1048 : List Sig := [wire152,raw1,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1048 : impossible 7 0 st1048 := by_search (by decide +kernel)

private def st1049 : List Sig := [wire152,wire227,raw1,raw0,raw3,raw4,raw5,raw6]

private theorem node1049 : impossible 7 0 st1049 := rectReject 7 st1049 5 4 21 5 1 28 0 14 (by decide +kernel)

private def st1050 : List Sig := [wire152,raw2,raw1,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1050 : impossible 7 0 st1050 := by_search (by decide +kernel)

private def st1051 : List Sig := [wire275,wire227,raw1,raw2,raw0,raw4,raw5,raw6]

private theorem node1051 : impossible 7 0 st1051 := rectReject 7 st1051 5 0 21 5 1 28 0 14 (by decide +kernel)

private def st1052 : List Sig := [wire276,wire227,raw1,raw2,raw0,raw3,raw5,raw6]

private theorem node1052 : impossible 7 0 st1052 := rectReject 7 st1052 5 0 21 5 0 14 1 28 (by decide +kernel)

private def st1053 : List Sig := [wire277,wire227,raw1,raw2,raw0,raw3,raw4,raw6]

private theorem node1053 : impossible 7 0 st1053 := rectReject 7 st1053 4 0 35 0 1 0 2 28 (by decide +kernel)

private def st1054 : List Sig := [wire278,wire227,raw1,raw2,raw0,raw3,raw4,raw5]

private theorem node1054 : impossible 7 0 st1054 := rectReject 7 st1054 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st1055 : List Sig := [wire21,raw5,wire227,raw2,raw0,raw3,raw4,raw6]

private theorem node1055 : impossible 7 0 st1055 := rectReject 7 st1055 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st1056 : List Sig := [wire23,wire227,raw2,raw0,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1056 : impossible 7 0 st1056 := by_search (by decide +kernel)

private def st1057 : List Sig := [wire23,raw1,wire227,raw2,raw0,raw3,raw4,raw5]

private theorem node1057 : impossible 7 0 st1057 := rectReject 7 st1057 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st1058 : List Sig := [wire23,raw6,wire227,raw2,raw0,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1058 : impossible 7 0 st1058 := by_search (by decide +kernel)

private def st1059 : List Sig := [wire26,raw3,wire227,raw1,raw0,raw4,raw5,raw6]

private theorem node1059 : impossible 7 0 st1059 := rectReject 7 st1059 6 4 35 0 2 28 1 0 (by decide +kernel)

private def st1060 : List Sig := [wire29,raw4,wire227,raw1,raw0,raw3,raw5,raw6]

private theorem node1060 : impossible 7 0 st1060 := rectReject 7 st1060 6 4 35 0 2 28 1 0 (by decide +kernel)

private def st1061 : List Sig := [wire279,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1061 : impossible 7 0 st1061 := by_search (by decide +kernel)

private def st1062 : List Sig := [wire279,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

private theorem node1062 : impossible 7 0 st1062 := rectReject 7 st1062 5 4 21 5 1 28 0 14 (by decide +kernel)

private def st1063 : List Sig := [wire279,wire227,raw1,raw2,raw3,raw4,raw5,raw6]

private theorem node1063 : impossible 7 0 st1063 := rectReject 7 st1063 5 4 21 5 1 28 0 14 (by decide +kernel)

private def st1064 : List Sig := [wire0,raw0,wire227,raw2,raw3,raw4,raw5,raw6]

private theorem node1064 : impossible 7 0 st1064 := rectReject 7 st1064 5 4 21 5 1 28 0 14 (by decide +kernel)

private def st1065 : List Sig := [wire10,raw0,wire227,raw1,raw2,raw3,raw4,raw5]

private theorem node1065 : impossible 7 0 st1065 := rectReject 7 st1065 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st1066 : List Sig := [wire51,raw5,wire227,raw1,raw2,raw0,raw3,raw4]

private theorem node1066 : impossible 7 0 st1066 := rectReject 7 st1066 7 6 21 5 1 28 0 14 (by decide +kernel)

private def st1067 : List Sig := [wire227,raw1,raw2,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1067 : impossible 8 0 st1067 := by
  apply reject_branch 7 0 st1067 [] [st1048,st1049,st1050,st1051,st1052,st1053,st1054,st1055,st1056,st1057,st1058,st1059,st1060,st1061,st1062,st1063,st1064,st1065,st1066]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node1048
    · exact node1049
    · exact node1050
    · exact node1051
    · exact node1052
    · exact node1053
    · exact node1054
    · exact node1055
    · exact node1056
    · exact node1057
    · exact node1058
    · exact node1059
    · exact node1060
    · exact node1061
    · exact node1062
    · exact node1063
    · exact node1064
    · exact node1065
    · exact node1066
  · decide +kernel

private def st1068 : List Sig := [wire227,raw1,wire35,raw2,raw0,raw3,raw4,raw5,raw6]

private theorem node1068 : impossible 8 0 st1068 := rectReject 8 st1068 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st1069 : List Sig := [wire186,raw1,wire35,raw2,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1069 : impossible 8 0 st1069 := by_search (by decide +kernel)

private def st1070 : List Sig := [wire14,raw1,raw2,wire35,raw0,raw3,raw4,raw5,raw6]

private theorem node1070 : impossible 8 0 st1070 := rectReject 8 st1070 4 1 0 4 0 42 2 49 (by decide +kernel)

private def st1071 : List Sig := [wire15,raw1,wire35,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1071 : impossible 8 0 st1071 := by_search (by decide +kernel)

private def st1072 : List Sig := [wire15,raw1,raw2,wire35,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1072 : impossible 8 0 st1072 := by_search (by decide +kernel)

private def st1073 : List Sig := [wire16,raw1,raw3,wire35,raw2,raw0,raw4,raw5,raw6]

private theorem node1073 : impossible 8 0 st1073 := rectReject 8 st1073 5 1 0 4 0 42 2 7 (by decide +kernel)

private def st1074 : List Sig := [wire17,raw1,raw3,wire35,raw2,raw0,raw4,raw5,raw6]

private theorem node1074 : impossible 8 0 st1074 := rectReject 8 st1074 5 1 0 6 0 35 2 49 (by decide +kernel)

private def st1075 : List Sig := [wire18,raw1,raw4,wire35,raw2,raw0,raw3,raw5,raw6]

private theorem node1075 : impossible 8 0 st1075 := rectReject 8 st1075 5 1 0 4 0 42 2 7 (by decide +kernel)

private def st1076 : List Sig := [wire19,raw1,raw4,wire35,raw2,raw0,raw3,raw5,raw6]

private theorem node1076 : impossible 8 0 st1076 := rectReject 8 st1076 5 1 0 4 0 42 3 7 (by decide +kernel)

private def st1077 : List Sig := [wire20,raw1,raw5,wire35,raw2,raw0,raw3,raw4,raw6]

private theorem node1077 : impossible 8 0 st1077 := rectReject 8 st1077 5 1 0 4 0 42 2 7 (by decide +kernel)

private def st1078 : List Sig := [wire21,raw1,raw5,wire35,raw2,raw0,raw3,raw4,raw6]

private theorem node1078 : impossible 8 0 st1078 := rectReject 8 st1078 7 6 21 5 1 28 0 14 (by decide +kernel)

private def st1079 : List Sig := [wire22,raw1,raw6,wire35,raw2,raw0,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1079 : impossible 8 0 st1079 := by_search (by decide +kernel)

private def st1080 : List Sig := [wire23,raw1,wire35,raw2,raw0,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1080 : impossible 8 0 st1080 := by_search (by decide +kernel)

private def st1081 : List Sig := [wire23,raw1,raw6,wire35,raw2,raw0,raw3,raw4,raw5]

private theorem node1081 : impossible 8 0 st1081 := rectReject 8 st1081 7 6 21 5 1 28 0 14 (by decide +kernel)

private def st1082 : List Sig := [wire268,raw3,wire35,raw2,raw0,raw1,raw4,raw5,raw6]

private theorem node1082 : impossible 8 0 st1082 := rectReject 8 st1082 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1083 : List Sig := [wire269,raw3,wire35,raw2,raw0,raw1,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1083 : impossible 8 0 st1083 := by_search (by decide +kernel)

private def st1084 : List Sig := [wire36,raw3,raw5,wire35,raw2,raw0,raw1,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node1084 : impossible 8 0 st1084 := by_search (by decide +kernel)

private def st1085 : List Sig := [wire37,raw3,raw5,wire35,raw2,raw0,raw1,raw4,raw6]

private theorem node1085 : impossible 8 0 st1085 := rectReject 8 st1085 6 5 0 4 2 7 0 42 (by decide +kernel)

private def st1086 : List Sig := [wire38,raw3,raw6,wire35,raw2,raw0,raw1,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1086 : impossible 8 0 st1086 := by_search (by decide +kernel)

private def st1087 : List Sig := [wire39,raw3,raw6,wire35,raw2,raw0,raw1,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1087 : impossible 8 0 st1087 := by_search (by decide +kernel)

private def st1088 : List Sig := [wire270,raw4,wire35,raw2,raw0,raw1,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1088 : impossible 8 0 st1088 := by_search (by decide +kernel)

private def st1089 : List Sig := [wire257,raw4,wire35,raw2,raw0,raw1,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1089 : impossible 8 0 st1089 := by_search (by decide +kernel)

private def st1090 : List Sig := [wire42,raw4,raw3,wire35,raw2,raw0,raw1,raw5,raw6]

private theorem node1090 : impossible 8 0 st1090 := rectReject 8 st1090 6 5 0 4 2 7 0 42 (by decide +kernel)

private def st1091 : List Sig := [wire43,raw4,raw3,wire35,raw2,raw0,raw1,raw5,raw6]

private theorem node1091 : impossible 8 0 st1091 := rectReject 8 st1091 6 5 0 4 2 7 0 42 (by decide +kernel)

private def st1092 : List Sig := [wire44,raw4,raw5,wire35,raw2,raw0,raw1,raw3,raw6]

private theorem node1092 : impossible 8 0 st1092 := rectReject 8 st1092 6 5 0 4 2 7 0 42 (by decide +kernel)

private def st1093 : List Sig := [wire45,raw4,raw5,wire35,raw2,raw0,raw1,raw3,raw6]

set_option maxRecDepth 10000 in
private theorem node1093 : impossible 8 0 st1093 := by_search (by decide +kernel)

private def st1094 : List Sig := [wire46,raw4,raw6,wire35,raw2,raw0,raw1,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node1094 : impossible 8 0 st1094 := by_search (by decide +kernel)

private def st1095 : List Sig := [wire47,raw4,raw6,wire35,raw2,raw0,raw1,raw3,raw5]

set_option maxRecDepth 10000 in
private theorem node1095 : impossible 8 0 st1095 := by_search (by decide +kernel)

private def st1096 : List Sig := [wire271,raw5,wire35,raw2,raw0,raw1,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node1096 : impossible 8 0 st1096 := by_search (by decide +kernel)

private def st1097 : List Sig := [wire272,raw5,wire35,raw2,raw0,raw1,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node1097 : impossible 8 0 st1097 := by_search (by decide +kernel)

private def st1098 : List Sig := [wire50,raw5,raw6,wire35,raw2,raw0,raw1,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node1098 : impossible 8 0 st1098 := by_search (by decide +kernel)

private def st1099 : List Sig := [wire51,raw5,wire35,raw2,raw0,raw1,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node1099 : impossible 8 0 st1099 := by_search (by decide +kernel)

private def st1100 : List Sig := [wire51,raw5,raw6,wire35,raw2,raw0,raw1,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node1100 : impossible 8 0 st1100 := by_search (by decide +kernel)

private def st1101 : List Sig := [wire273,raw6,wire35,raw2,raw0,raw1,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1101 : impossible 8 0 st1101 := by_search (by decide +kernel)

private def st1102 : List Sig := [wire274,raw6,wire35,raw2,raw0,raw1,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1102 : impossible 8 0 st1102 := by_search (by decide +kernel)

private def st1103 : List Sig := [wire35,raw2,raw0,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1103 : impossible 9 0 st1103 := by
  apply reject_branch 8 0 st1103 [] [st1012,st1013,st1014,st1015,st1027,st1028,st1029,st1030,st1031,st1032,st1033,st72,st1034,st1035,st1036,st1037,st1038,st1039,st1040,st1041,st1042,st1043,st1044,st1045,st1046,st1047,st1067,st1068,st1069,st1070,st1071,st1072,st1073,st1074,st1075,st1076,st1077,st1078,st1079,st1080,st1081,st1082,st1083,st1084,st1085,st1086,st1087,st1088,st1089,st1090,st1091,st1092,st1093,st1094,st1095,st1096,st1097,st1098,st1099,st1100,st1101,st1102]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node1012
    · exact node1013
    · exact node1014
    · exact node1015
    · exact node1027
    · exact node1028
    · exact node1029
    · exact node1030
    · exact node1031
    · exact node1032
    · exact node1033
    · exact node72
    · exact node1034
    · exact node1035
    · exact node1036
    · exact node1037
    · exact node1038
    · exact node1039
    · exact node1040
    · exact node1041
    · exact node1042
    · exact node1043
    · exact node1044
    · exact node1045
    · exact node1046
    · exact node1047
    · exact node1067
    · exact node1068
    · exact node1069
    · exact node1070
    · exact node1071
    · exact node1072
    · exact node1073
    · exact node1074
    · exact node1075
    · exact node1076
    · exact node1077
    · exact node1078
    · exact node1079
    · exact node1080
    · exact node1081
    · exact node1082
    · exact node1083
    · exact node1084
    · exact node1085
    · exact node1086
    · exact node1087
    · exact node1088
    · exact node1089
    · exact node1090
    · exact node1091
    · exact node1092
    · exact node1093
    · exact node1094
    · exact node1095
    · exact node1096
    · exact node1097
    · exact node1098
    · exact node1099
    · exact node1100
    · exact node1101
    · exact node1102
  · decide +kernel

private def st1104 : List Sig := [wire35,raw2,raw7,raw0,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1104 : impossible 9 0 st1104 := by_search (by decide +kernel)

private def st1105 : List Sig := [wire36,raw3,raw5,raw0,raw1,raw2,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1105 : impossible 9 0 st1105 := by_search (by decide +kernel)

private def st1106 : List Sig := [wire280,raw6,raw3,raw5,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1106 : impossible 8 0 st1106 := by_search (by decide +kernel)

private def st1107 : List Sig := [wire281,raw6,raw3,raw5,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1107 : impossible 8 0 st1107 := by_search (by decide +kernel)

private def st1108 : List Sig := [wire282,raw7,raw3,raw5,raw0,raw1,raw2,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node1108 : impossible 8 0 st1108 := by_search (by decide +kernel)

private def st1109 : List Sig := [wire283,raw7,raw3,raw5,raw0,raw1,raw2,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node1109 : impossible 8 0 st1109 := by_search (by decide +kernel)

private def st1110 : List Sig := [wire290,wire51,raw3,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1110 : impossible 7 0 st1110 := by_search (by decide +kernel)

private def st1111 : List Sig := [wire144,raw0,wire37,raw3,raw1,raw2,raw4,raw7]

private theorem node1111 : impossible 7 0 st1111 := rectReject 7 st1111 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st1112 : List Sig := [wire119,raw0,wire51,raw3,raw1,raw2,raw4,raw7]

private theorem node1112 : impossible 7 0 st1112 := rectReject 7 st1112 4 1 0 5 2 7 1 35 (by decide +kernel)

private def st1113 : List Sig := [wire5,raw0,wire51,wire37,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1113 : impossible 7 0 st1113 := by_search (by decide +kernel)

private def st1114 : List Sig := [wire13,raw0,wire51,wire37,raw3,raw1,raw2,raw4]

private theorem node1114 : impossible 7 0 st1114 := rectReject 7 st1114 6 5 7 2 0 14 3 0 (by decide +kernel)

private def st1115 : List Sig := [wire199,raw1,wire37,raw3,raw0,raw2,raw4,raw7]

private theorem node1115 : impossible 7 0 st1115 := rectReject 7 st1115 5 1 7 6 0 14 4 49 (by decide +kernel)

private def st1116 : List Sig := [wire17,raw1,wire51,wire37,raw0,raw2,raw4,raw7]

private theorem node1116 : impossible 7 0 st1116 := rectReject 7 st1116 4 1 0 6 0 35 2 49 (by decide +kernel)

private def st1117 : List Sig := [wire24,raw1,wire51,wire37,raw3,raw0,raw2,raw4]

private theorem node1117 : impossible 7 0 st1117 := rectReject 7 st1117 5 1 0 4 0 42 2 7 (by decide +kernel)

private def st1118 : List Sig := [wire26,raw2,wire51,wire37,raw0,raw1,raw4,raw7]

private theorem node1118 : impossible 7 0 st1118 := rectReject 7 st1118 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1119 : List Sig := [wire35,raw2,wire51,wire37,raw3,raw0,raw1,raw4]

private theorem node1119 : impossible 7 0 st1119 := rectReject 7 st1119 6 5 0 4 2 7 0 42 (by decide +kernel)

private def st1120 : List Sig := [wire288,wire51,raw3,raw0,raw1,raw2,raw7]

set_option maxRecDepth 10000 in
private theorem node1120 : impossible 7 0 st1120 := by_search (by decide +kernel)

private def st1121 : List Sig := [wire288,raw4,wire51,raw3,raw0,raw1,raw2,raw7]

private theorem node1121 : impossible 7 0 st1121 := rectReject 7 st1121 5 4 0 4 2 7 0 35 (by decide +kernel)

private def st1122 : List Sig := [wire288,wire37,wire51,raw3,raw0,raw1,raw2,raw7]

set_option maxRecDepth 10000 in
private theorem node1122 : impossible 7 0 st1122 := by_search (by decide +kernel)

private def st1123 : List Sig := [wire43,raw4,wire51,wire37,raw0,raw1,raw2,raw7]

set_option maxRecDepth 10000 in
private theorem node1123 : impossible 7 0 st1123 := by_search (by decide +kernel)

private def st1124 : List Sig := [wire51,wire37,raw3,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1124 : impossible 8 0 st1124 := by
  apply reject_branch 7 0 st1124 [] [st1110,st1111,st1112,st1113,st1114,st1115,st1116,st1117,st1118,st1119,st1120,st1121,st1122,st1123]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node1110
    · exact node1111
    · exact node1112
    · exact node1113
    · exact node1114
    · exact node1115
    · exact node1116
    · exact node1117
    · exact node1118
    · exact node1119
    · exact node1120
    · exact node1121
    · exact node1122
    · exact node1123
  · decide +kernel

private def st1125 : List Sig := [wire51,raw5,wire37,raw3,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1125 : impossible 8 0 st1125 := by_search (by decide +kernel)

private def st1126 : List Sig := [wire51,raw6,wire37,raw3,raw0,raw1,raw2,raw4,raw7]

private theorem node1126 : impossible 8 0 st1126 := rectReject 8 st1126 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1127 : List Sig := [wire284,raw0,raw3,raw5,raw1,raw2,raw4,raw6,raw7]

private theorem node1127 : impossible 8 0 st1127 := rectReject 8 st1127 4 1 0 4 2 7 0 42 (by decide +kernel)

private def st1128 : List Sig := [wire119,raw0,raw3,raw5,raw1,raw2,raw4,raw6,raw7]

private theorem node1128 : impossible 8 0 st1128 := rectReject 8 st1128 4 1 0 5 2 7 1 35 (by decide +kernel)

private def st1129 : List Sig := [wire5,raw0,wire37,raw5,raw1,raw2,raw4,raw6,raw7]

private theorem node1129 : impossible 8 0 st1129 := rectReject 8 st1129 4 1 0 6 2 49 1 35 (by decide +kernel)

private def st1130 : List Sig := [wire8,raw0,wire37,raw3,raw1,raw2,raw4,raw6,raw7]

private theorem node1130 : impossible 8 0 st1130 := rectReject 8 st1130 4 1 0 4 2 7 0 42 (by decide +kernel)

private def st1131 : List Sig := [wire10,raw0,wire37,raw3,raw5,raw1,raw2,raw4,raw7]

private theorem node1131 : impossible 8 0 st1131 := rectReject 8 st1131 5 1 0 5 2 7 0 35 (by decide +kernel)

private def st1132 : List Sig := [wire13,raw0,wire37,raw3,raw5,raw1,raw2,raw4,raw6]

private theorem node1132 : impossible 8 0 st1132 := rectReject 8 st1132 6 5 7 2 0 14 3 0 (by decide +kernel)

private def st1133 : List Sig := [wire285,raw1,raw3,raw5,raw0,raw2,raw4,raw6,raw7]

private theorem node1133 : impossible 8 0 st1133 := rectReject 8 st1133 4 1 0 4 0 42 2 7 (by decide +kernel)

private def st1134 : List Sig := [wire189,raw1,raw3,raw5,raw0,raw2,raw4,raw6,raw7]

private theorem node1134 : impossible 8 0 st1134 := rectReject 8 st1134 4 1 0 5 0 35 2 7 (by decide +kernel)

private def st1135 : List Sig := [wire17,raw1,wire37,raw5,raw0,raw2,raw4,raw6,raw7]

private theorem node1135 : impossible 8 0 st1135 := rectReject 8 st1135 4 1 0 6 0 35 2 49 (by decide +kernel)

private def st1136 : List Sig := [wire21,raw1,wire37,raw3,raw0,raw2,raw4,raw6,raw7]

private theorem node1136 : impossible 8 0 st1136 := rectReject 8 st1136 5 1 7 6 0 14 5 49 (by decide +kernel)

private def st1137 : List Sig := [wire23,raw1,wire37,raw3,raw5,raw0,raw2,raw4,raw7]

private theorem node1137 : impossible 8 0 st1137 := rectReject 8 st1137 6 1 7 6 0 14 4 49 (by decide +kernel)

private def st1138 : List Sig := [wire24,raw1,wire37,raw3,raw5,raw0,raw2,raw4,raw6]

private theorem node1138 : impossible 8 0 st1138 := rectReject 8 st1138 5 1 0 4 0 42 2 7 (by decide +kernel)

private def st1139 : List Sig := [wire286,raw2,raw3,raw5,raw0,raw1,raw4,raw6,raw7]

private theorem node1139 : impossible 8 0 st1139 := rectReject 8 st1139 4 3 35 0 1 0 2 28 (by decide +kernel)

private def st1140 : List Sig := [wire287,raw2,raw3,raw5,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1140 : impossible 8 0 st1140 := by_search (by decide +kernel)

private def st1141 : List Sig := [wire26,raw2,wire37,raw5,raw0,raw1,raw4,raw6,raw7]

private theorem node1141 : impossible 8 0 st1141 := rectReject 8 st1141 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1142 : List Sig := [wire31,raw2,wire37,raw3,raw0,raw1,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1142 : impossible 8 0 st1142 := by_search (by decide +kernel)

private def st1143 : List Sig := [wire35,raw2,wire37,raw3,raw5,raw0,raw1,raw4,raw6]

private theorem node1143 : impossible 8 0 st1143 := rectReject 8 st1143 6 5 0 4 2 7 0 42 (by decide +kernel)

private def st1144 : List Sig := [wire291,wire288,raw5,raw0,raw1,raw2,raw6,raw7]

private theorem node1144 : impossible 7 0 st1144 := rectReject 7 st1144 4 3 0 4 2 7 0 42 (by decide +kernel)

private def st1145 : List Sig := [wire292,wire288,raw3,raw0,raw1,raw2,raw6,raw7]

private theorem node1145 : impossible 7 0 st1145 := rectReject 7 st1145 4 3 0 4 2 7 0 42 (by decide +kernel)

private def st1146 : List Sig := [wire293,wire288,raw3,raw5,raw0,raw1,raw2,raw7]

private theorem node1146 : impossible 7 0 st1146 := rectReject 7 st1146 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1147 : List Sig := [wire294,wire288,raw3,raw5,raw0,raw1,raw2,raw6]

private theorem node1147 : impossible 7 0 st1147 := rectReject 7 st1147 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1148 : List Sig := [wire51,wire288,raw3,raw0,raw1,raw2,raw7]

set_option maxRecDepth 10000 in
private theorem node1148 : impossible 7 0 st1148 := by_search (by decide +kernel)

private def st1149 : List Sig := [wire51,raw5,wire288,raw3,raw0,raw1,raw2,raw7]

set_option maxRecDepth 10000 in
private theorem node1149 : impossible 7 0 st1149 := by_search (by decide +kernel)

private def st1150 : List Sig := [wire51,raw6,wire288,raw3,raw0,raw1,raw2,raw7]

set_option maxRecDepth 10000 in
private theorem node1150 : impossible 7 0 st1150 := by_search (by decide +kernel)

private def st1151 : List Sig := [wire295,wire288,raw3,raw5,raw1,raw2,raw6,raw7]

private theorem node1151 : impossible 7 0 st1151 := rectReject 7 st1151 4 0 0 4 2 7 0 42 (by decide +kernel)

private def st1152 : List Sig := [wire8,raw0,wire288,raw3,raw1,raw2,raw6,raw7]

private theorem node1152 : impossible 7 0 st1152 := rectReject 7 st1152 4 1 0 4 2 7 0 42 (by decide +kernel)

private def st1153 : List Sig := [wire10,raw0,wire288,raw3,raw5,raw1,raw2,raw7]

private theorem node1153 : impossible 7 0 st1153 := rectReject 7 st1153 5 1 0 5 2 7 0 35 (by decide +kernel)

private def st1154 : List Sig := [wire13,raw0,wire288,raw3,raw5,raw1,raw2,raw6]

private theorem node1154 : impossible 7 0 st1154 := rectReject 7 st1154 6 5 7 2 0 14 3 0 (by decide +kernel)

private def st1155 : List Sig := [wire296,wire288,raw3,raw5,raw0,raw2,raw6,raw7]

private theorem node1155 : impossible 7 0 st1155 := rectReject 7 st1155 4 0 0 4 0 42 2 7 (by decide +kernel)

private def st1156 : List Sig := [wire17,raw1,wire288,raw5,raw0,raw2,raw6,raw7]

private theorem node1156 : impossible 7 0 st1156 := rectReject 7 st1156 4 1 0 6 0 35 2 49 (by decide +kernel)

private def st1157 : List Sig := [wire21,raw1,wire288,raw3,raw0,raw2,raw6,raw7]

private theorem node1157 : impossible 7 0 st1157 := rectReject 7 st1157 5 1 7 6 0 14 5 49 (by decide +kernel)

private def st1158 : List Sig := [wire23,raw1,wire288,raw3,raw5,raw0,raw2,raw7]

private theorem node1158 : impossible 7 0 st1158 := rectReject 7 st1158 6 1 7 6 0 14 4 49 (by decide +kernel)

private def st1159 : List Sig := [wire24,raw1,wire288,raw3,raw5,raw0,raw2,raw6]

private theorem node1159 : impossible 7 0 st1159 := rectReject 7 st1159 5 1 0 4 0 42 2 7 (by decide +kernel)

private def st1160 : List Sig := [wire297,wire288,raw3,raw5,raw0,raw1,raw6,raw7]

private theorem node1160 : impossible 7 0 st1160 := rectReject 7 st1160 5 0 7 2 3 0 0 14 (by decide +kernel)

private def st1161 : List Sig := [wire26,raw2,wire288,raw5,raw0,raw1,raw6,raw7]

private theorem node1161 : impossible 7 0 st1161 := rectReject 7 st1161 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1162 : List Sig := [wire35,raw2,wire288,raw3,raw5,raw0,raw1,raw6]

private theorem node1162 : impossible 7 0 st1162 := rectReject 7 st1162 6 5 0 4 2 7 0 42 (by decide +kernel)

private def st1163 : List Sig := [wire288,raw3,raw5,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1163 : impossible 8 0 st1163 := by
  apply reject_branch 7 0 st1163 [] [st1144,st1145,st1146,st1147,st1148,st1149,st1150,st1151,st1152,st1153,st1154,st1155,st1156,st1157,st1158,st1159,st1160,st1161,st1162]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node1144
    · exact node1145
    · exact node1146
    · exact node1147
    · exact node1148
    · exact node1149
    · exact node1150
    · exact node1151
    · exact node1152
    · exact node1153
    · exact node1154
    · exact node1155
    · exact node1156
    · exact node1157
    · exact node1158
    · exact node1159
    · exact node1160
    · exact node1161
    · exact node1162
  · decide +kernel

private def st1164 : List Sig := [wire288,raw4,raw3,raw5,raw0,raw1,raw2,raw6,raw7]

private theorem node1164 : impossible 8 0 st1164 := rectReject 8 st1164 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1165 : List Sig := [wire288,wire37,raw3,raw5,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1165 : impossible 8 0 st1165 := by_search (by decide +kernel)

private def st1166 : List Sig := [wire289,raw4,raw3,raw5,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1166 : impossible 8 0 st1166 := by_search (by decide +kernel)

private def st1167 : List Sig := [wire43,raw4,wire37,raw5,raw0,raw1,raw2,raw6,raw7]

private theorem node1167 : impossible 8 0 st1167 := rectReject 8 st1167 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1168 : List Sig := [wire45,raw4,wire37,raw3,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1168 : impossible 8 0 st1168 := by_search (by decide +kernel)

private def st1169 : List Sig := [wire37,raw3,raw5,raw0,raw1,raw2,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1169 : impossible 9 0 st1169 := by
  apply reject_branch 8 0 st1169 [] [st1106,st1107,st1108,st1109,st1124,st1125,st1126,st1127,st1128,st1129,st1130,st1131,st1132,st1133,st1134,st1135,st1136,st1137,st1138,st1139,st1140,st1141,st1142,st1143,st1163,st1164,st1165,st1166,st1167,st1168]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node1106
    · exact node1107
    · exact node1108
    · exact node1109
    · exact node1124
    · exact node1125
    · exact node1126
    · exact node1127
    · exact node1128
    · exact node1129
    · exact node1130
    · exact node1131
    · exact node1132
    · exact node1133
    · exact node1134
    · exact node1135
    · exact node1136
    · exact node1137
    · exact node1138
    · exact node1139
    · exact node1140
    · exact node1141
    · exact node1142
    · exact node1143
    · exact node1163
    · exact node1164
    · exact node1165
    · exact node1166
    · exact node1167
    · exact node1168
  · decide +kernel

private def st1170 : List Sig := [wire38,raw3,raw6,raw0,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1170 : impossible 9 0 st1170 := by_search (by decide +kernel)

private def st1171 : List Sig := [wire39,raw3,raw6,raw0,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1171 : impossible 9 0 st1171 := by_search (by decide +kernel)

private def st1172 : List Sig := [wire40,raw3,raw7,raw0,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1172 : impossible 9 0 st1172 := by_search (by decide +kernel)

private def st1173 : List Sig := [wire41,raw3,raw7,raw0,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1173 : impossible 9 0 st1173 := by_search (by decide +kernel)

private def st1174 : List Sig := [wire298,raw5,raw4,raw3,raw0,raw1,raw2,raw6,raw7]

private theorem node1174 : impossible 8 0 st1174 := rectReject 8 st1174 2 1 28 2 1 21 0 35 (by decide +kernel)

private def st1175 : List Sig := [wire292,raw4,raw3,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1175 : impossible 8 0 st1175 := by_search (by decide +kernel)

private def st1176 : List Sig := [wire292,wire42,raw4,raw3,raw0,raw1,raw2,raw6,raw7]

private theorem node1176 : impossible 8 0 st1176 := rectReject 8 st1176 4 0 35 0 1 0 2 28 (by decide +kernel)

private def st1177 : List Sig := [wire292,raw5,raw4,raw3,raw0,raw1,raw2,raw6,raw7]

private theorem node1177 : impossible 8 0 st1177 := rectReject 8 st1177 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1178 : List Sig := [wire299,raw6,raw4,raw3,raw0,raw1,raw2,raw5,raw7]

private theorem node1178 : impossible 8 0 st1178 := rectReject 8 st1178 3 2 21 5 0 14 1 28 (by decide +kernel)

private def st1179 : List Sig := [wire300,raw4,raw3,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1179 : impossible 8 0 st1179 := by_search (by decide +kernel)

private def st1180 : List Sig := [wire300,wire42,raw4,raw3,raw0,raw1,raw2,raw5,raw7]

private theorem node1180 : impossible 8 0 st1180 := rectReject 8 st1180 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1181 : List Sig := [wire300,raw6,raw4,raw3,raw0,raw1,raw2,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1181 : impossible 8 0 st1181 := by_search (by decide +kernel)

private def st1182 : List Sig := [wire301,raw7,raw4,raw3,raw0,raw1,raw2,raw5,raw6]

private theorem node1182 : impossible 8 0 st1182 := rectReject 8 st1182 3 2 21 5 0 14 1 28 (by decide +kernel)

private def st1183 : List Sig := [wire302,raw4,raw3,raw0,raw1,raw2,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1183 : impossible 8 0 st1183 := by_search (by decide +kernel)

private def st1184 : List Sig := [wire302,wire42,raw4,raw3,raw0,raw1,raw2,raw5,raw6]

private theorem node1184 : impossible 8 0 st1184 := rectReject 8 st1184 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1185 : List Sig := [wire302,raw7,raw4,raw3,raw0,raw1,raw2,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1185 : impossible 8 0 st1185 := by_search (by decide +kernel)

private def st1186 : List Sig := [wire44,raw5,wire42,raw3,raw0,raw1,raw2,raw6,raw7]

private theorem node1186 : impossible 8 0 st1186 := rectReject 8 st1186 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1187 : List Sig := [wire303,raw0,raw4,raw3,raw1,raw2,raw5,raw6,raw7]

private theorem node1187 : impossible 8 0 st1187 := rectReject 8 st1187 3 2 21 5 0 14 1 28 (by decide +kernel)

private def st1188 : List Sig := [wire304,raw4,raw3,raw1,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1188 : impossible 8 0 st1188 := by_search (by decide +kernel)

private def st1189 : List Sig := [wire304,raw0,raw4,raw3,raw1,raw2,raw5,raw6,raw7]

private theorem node1189 : impossible 8 0 st1189 := rectReject 8 st1189 3 2 21 5 3 14 2 28 (by decide +kernel)

private def st1190 : List Sig := [wire304,wire42,raw4,raw3,raw1,raw2,raw5,raw6,raw7]

private theorem node1190 : impossible 8 0 st1190 := rectReject 8 st1190 4 0 0 4 2 7 0 42 (by decide +kernel)

private def st1191 : List Sig := [wire7,raw0,wire42,raw3,raw1,raw2,raw5,raw6,raw7]

private theorem node1191 : impossible 8 0 st1191 := rectReject 8 st1191 4 1 0 4 2 7 0 42 (by decide +kernel)

private def st1192 : List Sig := [wire10,raw0,wire42,raw4,raw3,raw1,raw2,raw5,raw7]

private theorem node1192 : impossible 8 0 st1192 := rectReject 8 st1192 5 1 0 5 2 7 0 35 (by decide +kernel)

private def st1193 : List Sig := [wire13,raw0,wire42,raw4,raw3,raw1,raw2,raw5,raw6]

private theorem node1193 : impossible 8 0 st1193 := rectReject 8 st1193 6 5 7 2 0 14 3 0 (by decide +kernel)

private def st1194 : List Sig := [wire305,raw1,raw4,raw3,raw0,raw2,raw5,raw6,raw7]

private theorem node1194 : impossible 8 0 st1194 := rectReject 8 st1194 3 2 21 5 0 14 1 28 (by decide +kernel)

private def st1195 : List Sig := [wire306,raw4,raw3,raw0,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1195 : impossible 8 0 st1195 := by_search (by decide +kernel)

private def st1196 : List Sig := [wire306,raw1,raw4,raw3,raw0,raw2,raw5,raw6,raw7]

private theorem node1196 : impossible 8 0 st1196 := rectReject 8 st1196 3 2 21 5 0 14 1 28 (by decide +kernel)

private def st1197 : List Sig := [wire306,wire42,raw4,raw3,raw0,raw2,raw5,raw6,raw7]

private theorem node1197 : impossible 8 0 st1197 := rectReject 8 st1197 4 0 0 4 0 42 2 7 (by decide +kernel)

private def st1198 : List Sig := [wire17,raw1,wire42,raw4,raw0,raw2,raw5,raw6,raw7]

private theorem node1198 : impossible 8 0 st1198 := rectReject 8 st1198 4 1 0 6 0 35 2 49 (by decide +kernel)

private def st1199 : List Sig := [wire23,raw1,wire42,raw4,raw3,raw0,raw2,raw5,raw7]

private theorem node1199 : impossible 8 0 st1199 := rectReject 8 st1199 6 1 7 6 0 14 4 49 (by decide +kernel)

private def st1200 : List Sig := [wire24,raw1,wire42,raw4,raw3,raw0,raw2,raw5,raw6]

private theorem node1200 : impossible 8 0 st1200 := rectReject 8 st1200 5 1 0 4 0 42 2 7 (by decide +kernel)

private def st1201 : List Sig := [wire239,raw2,raw4,raw3,raw0,raw1,raw5,raw6,raw7]

private theorem node1201 : impossible 8 0 st1201 := rectReject 8 st1201 3 1 14 0 3 21 1 7 (by decide +kernel)

private def st1202 : List Sig := [wire263,raw4,raw3,raw0,raw1,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1202 : impossible 8 0 st1202 := by_search (by decide +kernel)

private def st1203 : List Sig := [wire263,raw2,raw4,raw3,raw0,raw1,raw5,raw6,raw7]

private theorem node1203 : impossible 8 0 st1203 := rectReject 8 st1203 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1204 : List Sig := [wire263,wire42,raw4,raw3,raw0,raw1,raw5,raw6,raw7]

private theorem node1204 : impossible 8 0 st1204 := rectReject 8 st1204 5 0 7 2 3 0 0 14 (by decide +kernel)

private def st1205 : List Sig := [wire26,raw2,wire42,raw4,raw0,raw1,raw5,raw6,raw7]

private theorem node1205 : impossible 8 0 st1205 := rectReject 8 st1205 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1206 : List Sig := [wire35,raw2,wire42,raw4,raw3,raw0,raw1,raw5,raw6]

private theorem node1206 : impossible 8 0 st1206 := rectReject 8 st1206 6 5 0 4 2 7 0 42 (by decide +kernel)

private def st1207 : List Sig := [wire51,raw5,wire42,raw4,raw3,raw0,raw1,raw2,raw7]

private theorem node1207 : impossible 8 0 st1207 := rectReject 8 st1207 6 5 0 4 2 7 0 42 (by decide +kernel)

private def st1208 : List Sig := [wire42,raw4,raw3,raw0,raw1,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1208 : impossible 9 0 st1208 := by
  apply reject_branch 8 0 st1208 [] [st1174,st1175,st1176,st1177,st1178,st1179,st1180,st1181,st1182,st1183,st1184,st1185,st1186,st1187,st1188,st1189,st1190,st1191,st1192,st1193,st1194,st1195,st1196,st1197,st1198,st1199,st1200,st1201,st1202,st1203,st1204,st1205,st1206,st1207]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node1174
    · exact node1175
    · exact node1176
    · exact node1177
    · exact node1178
    · exact node1179
    · exact node1180
    · exact node1181
    · exact node1182
    · exact node1183
    · exact node1184
    · exact node1185
    · exact node1186
    · exact node1187
    · exact node1188
    · exact node1189
    · exact node1190
    · exact node1191
    · exact node1192
    · exact node1193
    · exact node1194
    · exact node1195
    · exact node1196
    · exact node1197
    · exact node1198
    · exact node1199
    · exact node1200
    · exact node1201
    · exact node1202
    · exact node1203
    · exact node1204
    · exact node1205
    · exact node1206
    · exact node1207
  · decide +kernel

private def st1209 : List Sig := [wire43,raw4,raw3,raw0,raw1,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1209 : impossible 9 0 st1209 := by_search (by decide +kernel)

private def st1210 : List Sig := [wire298,raw3,raw4,raw5,raw0,raw1,raw2,raw6,raw7]

private theorem node1210 : impossible 8 0 st1210 := rectReject 8 st1210 2 1 21 5 1 28 0 14 (by decide +kernel)

private def st1211 : List Sig := [wire291,raw4,raw5,raw0,raw1,raw2,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1211 : impossible 8 0 st1211 := by_search (by decide +kernel)

private def st1212 : List Sig := [wire291,wire44,raw4,raw5,raw0,raw1,raw2,raw6,raw7]

private theorem node1212 : impossible 8 0 st1212 := rectReject 8 st1212 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1213 : List Sig := [wire291,raw3,raw4,raw5,raw0,raw1,raw2,raw6,raw7]

private theorem node1213 : impossible 8 0 st1213 := rectReject 8 st1213 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1214 : List Sig := [wire307,raw6,raw4,raw5,raw0,raw1,raw2,raw3,raw7]

private theorem node1214 : impossible 8 0 st1214 := rectReject 8 st1214 3 2 28 2 0 35 1 21 (by decide +kernel)

private def st1215 : List Sig := [wire308,raw4,raw5,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node1215 : impossible 8 0 st1215 := by_search (by decide +kernel)

private def st1216 : List Sig := [wire308,wire44,raw4,raw5,raw0,raw1,raw2,raw3,raw7]

private theorem node1216 : impossible 8 0 st1216 := rectReject 8 st1216 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1217 : List Sig := [wire308,raw6,raw4,raw5,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node1217 : impossible 8 0 st1217 := by_search (by decide +kernel)

private def st1218 : List Sig := [wire309,raw7,raw4,raw5,raw0,raw1,raw2,raw3,raw6]

private theorem node1218 : impossible 8 0 st1218 := rectReject 8 st1218 3 2 28 2 0 35 1 21 (by decide +kernel)

private def st1219 : List Sig := [wire310,raw4,raw5,raw0,raw1,raw2,raw3,raw6]

set_option maxRecDepth 10000 in
private theorem node1219 : impossible 8 0 st1219 := by_search (by decide +kernel)

private def st1220 : List Sig := [wire310,wire44,raw4,raw5,raw0,raw1,raw2,raw3,raw6]

private theorem node1220 : impossible 8 0 st1220 := rectReject 8 st1220 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1221 : List Sig := [wire310,raw7,raw4,raw5,raw0,raw1,raw2,raw3,raw6]

set_option maxRecDepth 10000 in
private theorem node1221 : impossible 8 0 st1221 := by_search (by decide +kernel)

private def st1222 : List Sig := [wire42,raw3,wire44,raw5,raw0,raw1,raw2,raw6,raw7]

private theorem node1222 : impossible 8 0 st1222 := rectReject 8 st1222 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1223 : List Sig := [wire291,wire51,raw4,raw0,raw1,raw2,raw7]

set_option maxRecDepth 10000 in
private theorem node1223 : impossible 7 0 st1223 := by_search (by decide +kernel)

private def st1224 : List Sig := [wire291,wire44,wire51,raw4,raw0,raw1,raw2,raw7]

private theorem node1224 : impossible 7 0 st1224 := rectReject 7 st1224 5 4 0 4 2 7 0 35 (by decide +kernel)

private def st1225 : List Sig := [wire291,raw3,wire51,raw4,raw0,raw1,raw2,raw7]

set_option maxRecDepth 10000 in
private theorem node1225 : impossible 7 0 st1225 := by_search (by decide +kernel)

private def st1226 : List Sig := [wire310,wire44,wire51,raw4,raw0,raw1,raw2,raw3]

private theorem node1226 : impossible 7 0 st1226 := rectReject 7 st1226 5 4 0 4 2 7 0 35 (by decide +kernel)

private def st1227 : List Sig := [wire42,raw3,wire51,wire44,raw0,raw1,raw2,raw7]

private theorem node1227 : impossible 7 0 st1227 := rectReject 7 st1227 5 4 0 4 2 7 0 35 (by decide +kernel)

private def st1228 : List Sig := [wire144,raw0,wire44,raw4,raw1,raw2,raw3,raw7]

private theorem node1228 : impossible 7 0 st1228 := rectReject 7 st1228 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st1229 : List Sig := [wire311,wire51,raw4,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node1229 : impossible 7 0 st1229 := by_search (by decide +kernel)

private def st1230 : List Sig := [wire311,raw0,wire51,raw4,raw1,raw2,raw3,raw7]

private theorem node1230 : impossible 7 0 st1230 := rectReject 7 st1230 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st1231 : List Sig := [wire311,wire44,wire51,raw4,raw1,raw2,raw3,raw7]

private theorem node1231 : impossible 7 0 st1231 := rectReject 7 st1231 4 0 0 4 2 7 0 35 (by decide +kernel)

private def st1232 : List Sig := [wire13,raw0,wire51,wire44,raw4,raw1,raw2,raw3]

private theorem node1232 : impossible 7 0 st1232 := rectReject 7 st1232 6 5 7 2 0 14 3 0 (by decide +kernel)

private def st1233 : List Sig := [wire199,raw1,wire44,raw4,raw0,raw2,raw3,raw7]

private theorem node1233 : impossible 7 0 st1233 := rectReject 7 st1233 5 1 7 6 0 14 4 49 (by decide +kernel)

private def st1234 : List Sig := [wire313,wire44,wire51,raw4,raw0,raw2,raw3,raw7]

private theorem node1234 : impossible 7 0 st1234 := rectReject 7 st1234 4 0 0 4 0 35 2 7 (by decide +kernel)

private def st1235 : List Sig := [wire24,raw1,wire51,wire44,raw4,raw0,raw2,raw3]

private theorem node1235 : impossible 7 0 st1235 := rectReject 7 st1235 5 1 0 4 0 35 2 7 (by decide +kernel)

private def st1236 : List Sig := [wire315,wire44,wire51,raw4,raw0,raw1,raw3,raw7]

private theorem node1236 : impossible 7 0 st1236 := rectReject 7 st1236 5 0 7 2 3 0 0 14 (by decide +kernel)

private def st1237 : List Sig := [wire29,raw2,wire51,wire44,raw0,raw1,raw3,raw7]

private theorem node1237 : impossible 7 0 st1237 := rectReject 7 st1237 5 4 0 4 2 7 0 35 (by decide +kernel)

private def st1238 : List Sig := [wire35,raw2,wire51,wire44,raw4,raw0,raw1,raw3]

private theorem node1238 : impossible 7 0 st1238 := rectReject 7 st1238 6 5 0 4 2 7 0 35 (by decide +kernel)

private def st1239 : List Sig := [wire51,wire44,raw4,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node1239 : impossible 8 0 st1239 := by
  apply reject_branch 7 0 st1239 [] [st1223,st1224,st1225,st1226,st1227,st1228,st1229,st1230,st1231,st1232,st1233,st1234,st1235,st1236,st1237,st1238]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node1223
    · exact node1224
    · exact node1225
    · exact node1226
    · exact node1227
    · exact node1228
    · exact node1229
    · exact node1230
    · exact node1231
    · exact node1232
    · exact node1233
    · exact node1234
    · exact node1235
    · exact node1236
    · exact node1237
    · exact node1238
  · decide +kernel

private def st1240 : List Sig := [wire51,raw5,wire44,raw4,raw0,raw1,raw2,raw3,raw7]

private theorem node1240 : impossible 8 0 st1240 := rectReject 8 st1240 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1241 : List Sig := [wire51,raw6,wire44,raw4,raw0,raw1,raw2,raw3,raw7]

private theorem node1241 : impossible 8 0 st1241 := rectReject 8 st1241 5 4 0 4 2 7 0 35 (by decide +kernel)

private def st1242 : List Sig := [wire106,raw0,raw4,raw5,raw1,raw2,raw3,raw6,raw7]

private theorem node1242 : impossible 8 0 st1242 := rectReject 8 st1242 3 1 35 0 2 28 1 0 (by decide +kernel)

private def st1243 : List Sig := [wire311,raw4,raw5,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1243 : impossible 8 0 st1243 := by_search (by decide +kernel)

private def st1244 : List Sig := [wire311,raw0,raw4,raw5,raw1,raw2,raw3,raw6,raw7]

private theorem node1244 : impossible 8 0 st1244 := rectReject 8 st1244 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st1245 : List Sig := [wire311,wire44,raw4,raw5,raw1,raw2,raw3,raw6,raw7]

private theorem node1245 : impossible 8 0 st1245 := rectReject 8 st1245 4 0 0 4 2 7 0 42 (by decide +kernel)

private def st1246 : List Sig := [wire8,raw0,wire44,raw4,raw1,raw2,raw3,raw6,raw7]

private theorem node1246 : impossible 8 0 st1246 := rectReject 8 st1246 4 1 0 4 2 7 0 42 (by decide +kernel)

private def st1247 : List Sig := [wire10,raw0,wire44,raw4,raw5,raw1,raw2,raw3,raw7]

private theorem node1247 : impossible 8 0 st1247 := rectReject 8 st1247 5 1 0 5 2 7 0 35 (by decide +kernel)

private def st1248 : List Sig := [wire13,raw0,wire44,raw4,raw5,raw1,raw2,raw3,raw6]

private theorem node1248 : impossible 8 0 st1248 := rectReject 8 st1248 6 5 7 2 0 14 3 0 (by decide +kernel)

private def st1249 : List Sig := [wire312,raw1,raw4,raw5,raw0,raw2,raw3,raw6,raw7]

private theorem node1249 : impossible 8 0 st1249 := rectReject 8 st1249 3 2 28 2 0 35 1 21 (by decide +kernel)

private def st1250 : List Sig := [wire313,raw4,raw5,raw0,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1250 : impossible 8 0 st1250 := by_search (by decide +kernel)

private def st1251 : List Sig := [wire313,raw1,raw4,raw5,raw0,raw2,raw3,raw6,raw7]

private theorem node1251 : impossible 8 0 st1251 := rectReject 8 st1251 3 2 28 2 0 35 1 21 (by decide +kernel)

private def st1252 : List Sig := [wire313,wire44,raw4,raw5,raw0,raw2,raw3,raw6,raw7]

private theorem node1252 : impossible 8 0 st1252 := rectReject 8 st1252 4 0 0 4 0 42 2 7 (by decide +kernel)

private def st1253 : List Sig := [wire21,raw1,wire44,raw4,raw0,raw2,raw3,raw6,raw7]

private theorem node1253 : impossible 8 0 st1253 := rectReject 8 st1253 5 1 7 6 0 14 5 49 (by decide +kernel)

private def st1254 : List Sig := [wire23,raw1,wire44,raw4,raw5,raw0,raw2,raw3,raw7]

private theorem node1254 : impossible 8 0 st1254 := rectReject 8 st1254 6 1 7 6 0 14 4 49 (by decide +kernel)

private def st1255 : List Sig := [wire24,raw1,wire44,raw4,raw5,raw0,raw2,raw3,raw6]

private theorem node1255 : impossible 8 0 st1255 := rectReject 8 st1255 5 1 0 4 0 42 2 7 (by decide +kernel)

private def st1256 : List Sig := [wire314,raw2,raw4,raw5,raw0,raw1,raw3,raw6,raw7]

private theorem node1256 : impossible 8 0 st1256 := rectReject 8 st1256 3 2 28 2 0 35 1 21 (by decide +kernel)

private def st1257 : List Sig := [wire315,raw4,raw5,raw0,raw1,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1257 : impossible 8 0 st1257 := by_search (by decide +kernel)

private def st1258 : List Sig := [wire315,raw2,raw4,raw5,raw0,raw1,raw3,raw6,raw7]

private theorem node1258 : impossible 8 0 st1258 := rectReject 8 st1258 3 2 28 2 3 35 5 21 (by decide +kernel)

private def st1259 : List Sig := [wire315,wire44,raw4,raw5,raw0,raw1,raw3,raw6,raw7]

private theorem node1259 : impossible 8 0 st1259 := rectReject 8 st1259 5 0 7 2 3 0 0 14 (by decide +kernel)

private def st1260 : List Sig := [wire29,raw2,wire44,raw5,raw0,raw1,raw3,raw6,raw7]

private theorem node1260 : impossible 8 0 st1260 := rectReject 8 st1260 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1261 : List Sig := [wire35,raw2,wire44,raw4,raw5,raw0,raw1,raw3,raw6]

private theorem node1261 : impossible 8 0 st1261 := rectReject 8 st1261 6 5 0 4 2 7 0 42 (by decide +kernel)

private def st1262 : List Sig := [wire44,raw4,raw5,raw0,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1262 : impossible 9 0 st1262 := by
  apply reject_branch 8 0 st1262 [] [st1210,st1211,st1212,st1213,st1214,st1215,st1216,st1217,st1218,st1219,st1220,st1221,st1222,st1239,st1240,st1241,st1242,st1243,st1244,st1245,st1246,st1247,st1248,st1249,st1250,st1251,st1252,st1253,st1254,st1255,st1256,st1257,st1258,st1259,st1260,st1261]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node1210
    · exact node1211
    · exact node1212
    · exact node1213
    · exact node1214
    · exact node1215
    · exact node1216
    · exact node1217
    · exact node1218
    · exact node1219
    · exact node1220
    · exact node1221
    · exact node1222
    · exact node1239
    · exact node1240
    · exact node1241
    · exact node1242
    · exact node1243
    · exact node1244
    · exact node1245
    · exact node1246
    · exact node1247
    · exact node1248
    · exact node1249
    · exact node1250
    · exact node1251
    · exact node1252
    · exact node1253
    · exact node1254
    · exact node1255
    · exact node1256
    · exact node1257
    · exact node1258
    · exact node1259
    · exact node1260
    · exact node1261
  · decide +kernel

private def st1263 : List Sig := [wire45,raw4,raw5,raw0,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1263 : impossible 9 0 st1263 := by_search (by decide +kernel)

private def st1264 : List Sig := [wire46,raw4,raw6,raw0,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1264 : impossible 9 0 st1264 := by_search (by decide +kernel)

private def st1265 : List Sig := [wire47,raw4,raw6,raw0,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1265 : impossible 9 0 st1265 := by_search (by decide +kernel)

private def st1266 : List Sig := [wire48,raw4,raw7,raw0,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1266 : impossible 9 0 st1266 := by_search (by decide +kernel)

private def st1267 : List Sig := [wire49,raw4,raw7,raw0,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1267 : impossible 9 0 st1267 := by_search (by decide +kernel)

private def st1268 : List Sig := [wire50,raw5,raw6,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1268 : impossible 9 0 st1268 := by_search (by decide +kernel)

private def st1269 : List Sig := [wire316,wire51,raw7,raw5,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node1269 : impossible 8 0 st1269 := by_search (by decide +kernel)

private def st1270 : List Sig := [wire317,wire51,raw7,raw5,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node1270 : impossible 8 0 st1270 := by_search (by decide +kernel)

private def st1271 : List Sig := [wire52,raw5,raw7,wire51,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node1271 : impossible 8 0 st1271 := by_search (by decide +kernel)

private def st1272 : List Sig := [wire53,raw5,raw7,wire51,raw0,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node1272 : impossible 8 0 st1272 := by_search (by decide +kernel)

private def st1273 : List Sig := [wire128,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1273 : impossible 7 0 st1273 := by_search (by decide +kernel)

private def st1274 : List Sig := [wire128,wire144,raw0,raw1,raw2,raw3,raw4,raw7]

private theorem node1274 : impossible 7 0 st1274 := rectReject 7 st1274 4 3 7 2 0 14 3 0 (by decide +kernel)

private def st1275 : List Sig := [wire128,raw5,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1275 : impossible 7 0 st1275 := by_search (by decide +kernel)

private def st1276 : List Sig := [wire324,raw0,raw5,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1276 : impossible 7 0 st1276 := by_search (by decide +kernel)

private def st1277 : List Sig := [wire324,wire144,raw0,raw5,raw2,raw3,raw4,raw7]

private theorem node1277 : impossible 7 0 st1277 := rectReject 7 st1277 4 0 7 2 0 14 3 0 (by decide +kernel)

private def st1278 : List Sig := [wire324,raw1,raw0,raw5,raw2,raw3,raw4,raw7]

private theorem node1278 : impossible 7 0 st1278 := rectReject 7 st1278 5 4 14 0 3 21 1 7 (by decide +kernel)

private def st1279 : List Sig := [wire325,wire144,raw0,raw5,raw1,raw3,raw4,raw7]

private theorem node1279 : impossible 7 0 st1279 := rectReject 7 st1279 4 0 7 2 3 0 0 14 (by decide +kernel)

private def st1280 : List Sig := [wire326,wire144,raw0,raw5,raw1,raw2,raw4,raw7]

private theorem node1280 : impossible 7 0 st1280 := rectReject 7 st1280 5 0 14 0 1 7 3 21 (by decide +kernel)

private def st1281 : List Sig := [wire327,wire144,raw0,raw5,raw1,raw2,raw3,raw7]

private theorem node1281 : impossible 7 0 st1281 := rectReject 7 st1281 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st1282 : List Sig := [wire328,wire144,raw0,raw5,raw1,raw2,raw3,raw4]

private theorem node1282 : impossible 7 0 st1282 := rectReject 7 st1282 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st1283 : List Sig := [wire0,raw1,wire144,raw5,raw2,raw3,raw4,raw7]

private theorem node1283 : impossible 7 0 st1283 := rectReject 7 st1283 4 1 7 2 0 14 3 49 (by decide +kernel)

private def st1284 : List Sig := [wire3,raw2,wire144,raw5,raw1,raw3,raw4,raw7]

private theorem node1284 : impossible 7 0 st1284 := rectReject 7 st1284 6 5 21 5 1 28 0 14 (by decide +kernel)

private def st1285 : List Sig := [wire13,wire144,raw5,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node1285 : impossible 7 0 st1285 := by_search (by decide +kernel)

private def st1286 : List Sig := [wire13,raw0,wire144,raw5,raw1,raw2,raw3,raw4]

private theorem node1286 : impossible 7 0 st1286 := rectReject 7 st1286 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st1287 : List Sig := [wire13,raw7,wire144,raw5,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node1287 : impossible 7 0 st1287 := by_search (by decide +kernel)

private def st1288 : List Sig := [wire24,raw1,wire144,raw0,raw5,raw2,raw3,raw4]

private theorem node1288 : impossible 7 0 st1288 := rectReject 7 st1288 5 1 7 2 0 14 3 0 (by decide +kernel)

private def st1289 : List Sig := [wire35,raw2,wire144,raw0,raw5,raw1,raw3,raw4]

private theorem node1289 : impossible 7 0 st1289 := rectReject 7 st1289 7 6 21 5 1 28 0 14 (by decide +kernel)

private def st1290 : List Sig := [wire37,raw3,wire144,raw0,raw1,raw2,raw4,raw7]

private theorem node1290 : impossible 7 0 st1290 := rectReject 7 st1290 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st1291 : List Sig := [wire44,raw4,wire144,raw0,raw1,raw2,raw3,raw7]

private theorem node1291 : impossible 7 0 st1291 := rectReject 7 st1291 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st1292 : List Sig := [wire144,raw0,raw5,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1292 : impossible 8 0 st1292 := by
  apply reject_branch 7 0 st1292 [] [st1273,st1274,st1275,st1276,st1277,st1278,st1279,st1280,st1281,st1282,st1283,st1284,st1285,st1286,st1287,st1288,st1289,st1290,st1291]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node1273
    · exact node1274
    · exact node1275
    · exact node1276
    · exact node1277
    · exact node1278
    · exact node1279
    · exact node1280
    · exact node1281
    · exact node1282
    · exact node1283
    · exact node1284
    · exact node1285
    · exact node1286
    · exact node1287
    · exact node1288
    · exact node1289
    · exact node1290
    · exact node1291
  · decide +kernel

private def st1293 : List Sig := [wire144,raw0,wire51,raw5,raw1,raw2,raw3,raw4,raw7]

private theorem node1293 : impossible 8 0 st1293 := rectReject 8 st1293 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st1294 : List Sig := [wire113,raw0,wire51,raw5,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1294 : impossible 8 0 st1294 := by_search (by decide +kernel)

private def st1295 : List Sig := [wire8,raw0,raw5,wire51,raw1,raw2,raw3,raw4,raw7]

private theorem node1295 : impossible 8 0 st1295 := rectReject 8 st1295 4 1 0 4 2 7 0 42 (by decide +kernel)

private def st1296 : List Sig := [wire9,raw0,wire51,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1296 : impossible 8 0 st1296 := by_search (by decide +kernel)

private def st1297 : List Sig := [wire9,raw0,raw5,wire51,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1297 : impossible 8 0 st1297 := by_search (by decide +kernel)

private def st1298 : List Sig := [wire0,raw0,raw1,wire51,raw5,raw2,raw3,raw4,raw7]

private theorem node1298 : impossible 8 0 st1298 := rectReject 8 st1298 5 2 7 2 0 14 3 49 (by decide +kernel)

private def st1299 : List Sig := [wire1,raw0,raw1,wire51,raw5,raw2,raw3,raw4,raw7]

private theorem node1299 : impossible 8 0 st1299 := rectReject 8 st1299 5 2 7 2 0 14 3 0 (by decide +kernel)

private def st1300 : List Sig := [wire2,raw0,raw2,wire51,raw5,raw1,raw3,raw4,raw7]

private theorem node1300 : impossible 8 0 st1300 := rectReject 8 st1300 5 1 0 4 2 7 0 42 (by decide +kernel)

private def st1301 : List Sig := [wire3,raw0,raw2,wire51,raw5,raw1,raw3,raw4,raw7]

private theorem node1301 : impossible 8 0 st1301 := rectReject 8 st1301 7 6 21 5 1 28 0 14 (by decide +kernel)

private def st1302 : List Sig := [wire4,raw0,raw3,wire51,raw5,raw1,raw2,raw4,raw7]

private theorem node1302 : impossible 8 0 st1302 := rectReject 8 st1302 5 1 0 4 2 7 0 42 (by decide +kernel)

private def st1303 : List Sig := [wire5,raw0,raw3,wire51,raw5,raw1,raw2,raw4,raw7]

private theorem node1303 : impossible 8 0 st1303 := rectReject 8 st1303 5 1 0 6 2 49 1 35 (by decide +kernel)

private def st1304 : List Sig := [wire6,raw0,raw4,wire51,raw5,raw1,raw2,raw3,raw7]

private theorem node1304 : impossible 8 0 st1304 := rectReject 8 st1304 5 1 0 4 2 7 0 42 (by decide +kernel)

private def st1305 : List Sig := [wire7,raw0,raw4,wire51,raw5,raw1,raw2,raw3,raw7]

private theorem node1305 : impossible 8 0 st1305 := rectReject 8 st1305 5 1 0 4 2 7 0 42 (by decide +kernel)

private def st1306 : List Sig := [wire12,raw0,raw7,wire51,raw5,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node1306 : impossible 8 0 st1306 := by_search (by decide +kernel)

private def st1307 : List Sig := [wire13,raw0,wire51,raw5,raw1,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node1307 : impossible 8 0 st1307 := by_search (by decide +kernel)

private def st1308 : List Sig := [wire13,raw0,raw7,wire51,raw5,raw1,raw2,raw3,raw4]

private theorem node1308 : impossible 8 0 st1308 := rectReject 8 st1308 6 5 7 2 0 14 3 0 (by decide +kernel)

private def st1309 : List Sig := [wire318,raw1,wire51,raw5,raw0,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1309 : impossible 8 0 st1309 := by_search (by decide +kernel)

private def st1310 : List Sig := [wire199,raw1,wire51,raw5,raw0,raw2,raw3,raw4,raw7]

private theorem node1310 : impossible 8 0 st1310 := rectReject 8 st1310 5 1 7 6 0 14 4 49 (by decide +kernel)

private def st1311 : List Sig := [wire20,raw1,raw5,wire51,raw0,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1311 : impossible 8 0 st1311 := by_search (by decide +kernel)

private def st1312 : List Sig := [wire21,raw1,raw5,wire51,raw0,raw2,raw3,raw4,raw7]

private theorem node1312 : impossible 8 0 st1312 := rectReject 8 st1312 5 1 7 6 0 14 5 49 (by decide +kernel)

private def st1313 : List Sig := [wire14,raw1,raw2,wire51,raw5,raw0,raw3,raw4,raw7]

private theorem node1313 : impossible 8 0 st1313 := rectReject 8 st1313 5 1 0 4 0 42 2 49 (by decide +kernel)

private def st1314 : List Sig := [wire15,raw1,raw2,wire51,raw5,raw0,raw3,raw4,raw7]

private theorem node1314 : impossible 8 0 st1314 := rectReject 8 st1314 5 1 0 4 0 42 3 7 (by decide +kernel)

private def st1315 : List Sig := [wire16,raw1,raw3,wire51,raw5,raw0,raw2,raw4,raw7]

private theorem node1315 : impossible 8 0 st1315 := rectReject 8 st1315 5 1 0 4 0 42 2 7 (by decide +kernel)

private def st1316 : List Sig := [wire17,raw1,raw3,wire51,raw5,raw0,raw2,raw4,raw7]

private theorem node1316 : impossible 8 0 st1316 := rectReject 8 st1316 5 1 0 6 0 35 2 49 (by decide +kernel)

private def st1317 : List Sig := [wire18,raw1,raw4,wire51,raw5,raw0,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node1317 : impossible 8 0 st1317 := by_search (by decide +kernel)

private def st1318 : List Sig := [wire19,raw1,raw4,wire51,raw5,raw0,raw2,raw3,raw7]

private theorem node1318 : impossible 8 0 st1318 := rectReject 8 st1318 5 1 0 4 0 42 3 7 (by decide +kernel)

private def st1319 : List Sig := [wire24,raw1,wire51,raw5,raw0,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node1319 : impossible 8 0 st1319 := by_search (by decide +kernel)

private def st1320 : List Sig := [wire24,raw1,raw7,wire51,raw5,raw0,raw2,raw3,raw4]

private theorem node1320 : impossible 8 0 st1320 := rectReject 8 st1320 5 1 0 4 0 42 2 7 (by decide +kernel)

private def st1321 : List Sig := [wire25,raw1,raw7,wire51,raw5,raw0,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node1321 : impossible 8 0 st1321 := by_search (by decide +kernel)

private def st1322 : List Sig := [wire319,raw2,wire51,raw5,raw0,raw1,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1322 : impossible 8 0 st1322 := by_search (by decide +kernel)

private def st1323 : List Sig := [wire320,raw2,wire51,raw5,raw0,raw1,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1323 : impossible 8 0 st1323 := by_search (by decide +kernel)

private def st1324 : List Sig := [wire30,raw2,raw5,wire51,raw0,raw1,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1324 : impossible 8 0 st1324 := by_search (by decide +kernel)

private def st1325 : List Sig := [wire31,raw2,raw5,wire51,raw0,raw1,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1325 : impossible 8 0 st1325 := by_search (by decide +kernel)

private def st1326 : List Sig := [wire26,raw2,raw3,wire51,raw5,raw0,raw1,raw4,raw7]

private theorem node1326 : impossible 8 0 st1326 := rectReject 8 st1326 6 5 0 4 2 7 0 42 (by decide +kernel)

private def st1327 : List Sig := [wire27,raw2,raw3,wire51,raw5,raw0,raw1,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1327 : impossible 8 0 st1327 := by_search (by decide +kernel)

private def st1328 : List Sig := [wire28,raw2,raw4,wire51,raw5,raw0,raw1,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node1328 : impossible 8 0 st1328 := by_search (by decide +kernel)

private def st1329 : List Sig := [wire29,raw2,raw4,wire51,raw5,raw0,raw1,raw3,raw7]

private theorem node1329 : impossible 8 0 st1329 := rectReject 8 st1329 6 5 0 4 2 7 0 42 (by decide +kernel)

private def st1330 : List Sig := [wire34,raw2,raw7,wire51,raw5,raw0,raw1,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node1330 : impossible 8 0 st1330 := by_search (by decide +kernel)

private def st1331 : List Sig := [wire35,raw2,wire51,raw5,raw0,raw1,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node1331 : impossible 8 0 st1331 := by_search (by decide +kernel)

private def st1332 : List Sig := [wire35,raw2,raw7,wire51,raw5,raw0,raw1,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node1332 : impossible 8 0 st1332 := by_search (by decide +kernel)

private def st1333 : List Sig := [wire321,raw3,wire51,raw5,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1333 : impossible 8 0 st1333 := by_search (by decide +kernel)

private def st1334 : List Sig := [wire281,raw3,wire51,raw5,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1334 : impossible 8 0 st1334 := by_search (by decide +kernel)

private def st1335 : List Sig := [wire36,raw3,raw5,wire51,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1335 : impossible 8 0 st1335 := by_search (by decide +kernel)

private def st1336 : List Sig := [wire119,raw0,raw3,wire51,raw1,raw2,raw4,raw7]

private theorem node1336 : impossible 7 0 st1336 := rectReject 7 st1336 4 1 0 5 2 7 1 35 (by decide +kernel)

private def st1337 : List Sig := [wire5,raw0,wire37,wire51,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1337 : impossible 7 0 st1337 := by_search (by decide +kernel)

private def st1338 : List Sig := [wire13,raw0,wire37,raw3,wire51,raw1,raw2,raw4]

private theorem node1338 : impossible 7 0 st1338 := rectReject 7 st1338 6 5 7 2 0 14 3 0 (by decide +kernel)

private def st1339 : List Sig := [wire17,raw1,wire37,wire51,raw0,raw2,raw4,raw7]

private theorem node1339 : impossible 7 0 st1339 := rectReject 7 st1339 4 1 0 6 0 35 2 49 (by decide +kernel)

private def st1340 : List Sig := [wire24,raw1,wire37,raw3,wire51,raw0,raw2,raw4]

private theorem node1340 : impossible 7 0 st1340 := rectReject 7 st1340 5 1 0 4 0 42 2 7 (by decide +kernel)

private def st1341 : List Sig := [wire26,raw2,wire37,wire51,raw0,raw1,raw4,raw7]

private theorem node1341 : impossible 7 0 st1341 := rectReject 7 st1341 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1342 : List Sig := [wire35,raw2,wire37,raw3,wire51,raw0,raw1,raw4]

private theorem node1342 : impossible 7 0 st1342 := rectReject 7 st1342 6 5 0 4 2 7 0 42 (by decide +kernel)

private def st1343 : List Sig := [wire288,raw3,wire51,raw0,raw1,raw2,raw7]

set_option maxRecDepth 10000 in
private theorem node1343 : impossible 7 0 st1343 := by_search (by decide +kernel)

private def st1344 : List Sig := [wire288,raw4,raw3,wire51,raw0,raw1,raw2,raw7]

private theorem node1344 : impossible 7 0 st1344 := rectReject 7 st1344 5 4 0 4 2 7 0 35 (by decide +kernel)

private def st1345 : List Sig := [wire288,wire37,raw3,wire51,raw0,raw1,raw2,raw7]

set_option maxRecDepth 10000 in
private theorem node1345 : impossible 7 0 st1345 := by_search (by decide +kernel)

private def st1346 : List Sig := [wire43,raw4,wire37,wire51,raw0,raw1,raw2,raw7]

set_option maxRecDepth 10000 in
private theorem node1346 : impossible 7 0 st1346 := by_search (by decide +kernel)

private def st1347 : List Sig := [wire37,raw3,wire51,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1347 : impossible 8 0 st1347 := by
  apply reject_branch 7 0 st1347 [] [st1110,st1336,st1337,st1111,st1338,st1339,st1115,st1340,st1341,st1342,st1343,st1344,st1345,st1346]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node1110
    · exact node1336
    · exact node1337
    · exact node1111
    · exact node1338
    · exact node1339
    · exact node1115
    · exact node1340
    · exact node1341
    · exact node1342
    · exact node1343
    · exact node1344
    · exact node1345
    · exact node1346
  · decide +kernel

private def st1348 : List Sig := [wire37,raw3,raw5,wire51,raw0,raw1,raw2,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1348 : impossible 8 0 st1348 := by_search (by decide +kernel)

private def st1349 : List Sig := [wire40,raw3,raw7,wire51,raw5,raw0,raw1,raw2,raw4]

set_option maxRecDepth 10000 in
private theorem node1349 : impossible 8 0 st1349 := by_search (by decide +kernel)

private def st1350 : List Sig := [wire41,raw3,raw7,wire51,raw5,raw0,raw1,raw2,raw4]

set_option maxRecDepth 10000 in
private theorem node1350 : impossible 8 0 st1350 := by_search (by decide +kernel)

private def st1351 : List Sig := [wire322,raw4,wire51,raw5,raw0,raw1,raw2,raw3,raw7]

private theorem node1351 : impossible 8 0 st1351 := rectReject 8 st1351 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1352 : List Sig := [wire323,raw4,wire51,raw5,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node1352 : impossible 8 0 st1352 := by_search (by decide +kernel)

private def st1353 : List Sig := [wire291,raw4,wire51,raw0,raw1,raw2,raw7]

set_option maxRecDepth 10000 in
private theorem node1353 : impossible 7 0 st1353 := by_search (by decide +kernel)

private def st1354 : List Sig := [wire291,wire44,raw4,wire51,raw0,raw1,raw2,raw7]

private theorem node1354 : impossible 7 0 st1354 := rectReject 7 st1354 5 4 0 4 2 7 0 35 (by decide +kernel)

private def st1355 : List Sig := [wire291,raw3,raw4,wire51,raw0,raw1,raw2,raw7]

set_option maxRecDepth 10000 in
private theorem node1355 : impossible 7 0 st1355 := by_search (by decide +kernel)

private def st1356 : List Sig := [wire310,wire44,raw4,wire51,raw0,raw1,raw2,raw3]

private theorem node1356 : impossible 7 0 st1356 := rectReject 7 st1356 5 4 0 4 2 7 0 35 (by decide +kernel)

private def st1357 : List Sig := [wire42,raw3,wire44,wire51,raw0,raw1,raw2,raw7]

private theorem node1357 : impossible 7 0 st1357 := rectReject 7 st1357 5 4 0 4 2 7 0 35 (by decide +kernel)

private def st1358 : List Sig := [wire311,raw4,wire51,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node1358 : impossible 7 0 st1358 := by_search (by decide +kernel)

private def st1359 : List Sig := [wire311,raw0,raw4,wire51,raw1,raw2,raw3,raw7]

private theorem node1359 : impossible 7 0 st1359 := rectReject 7 st1359 5 4 7 2 0 14 3 0 (by decide +kernel)

private def st1360 : List Sig := [wire311,wire44,raw4,wire51,raw1,raw2,raw3,raw7]

private theorem node1360 : impossible 7 0 st1360 := rectReject 7 st1360 4 0 0 4 2 7 0 35 (by decide +kernel)

private def st1361 : List Sig := [wire13,raw0,wire44,raw4,wire51,raw1,raw2,raw3]

private theorem node1361 : impossible 7 0 st1361 := rectReject 7 st1361 6 5 7 2 0 14 3 0 (by decide +kernel)

private def st1362 : List Sig := [wire313,wire44,raw4,wire51,raw0,raw2,raw3,raw7]

private theorem node1362 : impossible 7 0 st1362 := rectReject 7 st1362 4 0 0 4 0 35 2 7 (by decide +kernel)

private def st1363 : List Sig := [wire24,raw1,wire44,raw4,wire51,raw0,raw2,raw3]

private theorem node1363 : impossible 7 0 st1363 := rectReject 7 st1363 5 1 0 4 0 35 2 7 (by decide +kernel)

private def st1364 : List Sig := [wire315,wire44,raw4,wire51,raw0,raw1,raw3,raw7]

private theorem node1364 : impossible 7 0 st1364 := rectReject 7 st1364 5 0 7 2 3 0 0 14 (by decide +kernel)

private def st1365 : List Sig := [wire29,raw2,wire44,wire51,raw0,raw1,raw3,raw7]

private theorem node1365 : impossible 7 0 st1365 := rectReject 7 st1365 5 4 0 4 2 7 0 35 (by decide +kernel)

private def st1366 : List Sig := [wire35,raw2,wire44,raw4,wire51,raw0,raw1,raw3]

private theorem node1366 : impossible 7 0 st1366 := rectReject 7 st1366 6 5 0 4 2 7 0 35 (by decide +kernel)

private def st1367 : List Sig := [wire44,raw4,wire51,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node1367 : impossible 8 0 st1367 := by
  apply reject_branch 7 0 st1367 [] [st1353,st1354,st1355,st1356,st1357,st1358,st1359,st1360,st1228,st1361,st1362,st1233,st1363,st1364,st1365,st1366]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node1353
    · exact node1354
    · exact node1355
    · exact node1356
    · exact node1357
    · exact node1358
    · exact node1359
    · exact node1360
    · exact node1228
    · exact node1361
    · exact node1362
    · exact node1233
    · exact node1363
    · exact node1364
    · exact node1365
    · exact node1366
  · decide +kernel

private def st1368 : List Sig := [wire44,raw4,raw5,wire51,raw0,raw1,raw2,raw3,raw7]

private theorem node1368 : impossible 8 0 st1368 := rectReject 8 st1368 5 4 0 4 2 7 0 42 (by decide +kernel)

private def st1369 : List Sig := [wire45,raw4,raw5,wire51,raw0,raw1,raw2,raw3,raw7]

set_option maxRecDepth 10000 in
private theorem node1369 : impossible 8 0 st1369 := by_search (by decide +kernel)

private def st1370 : List Sig := [wire42,raw4,raw3,wire51,raw5,raw0,raw1,raw2,raw7]

private theorem node1370 : impossible 8 0 st1370 := rectReject 8 st1370 6 5 0 4 2 7 0 42 (by decide +kernel)

private def st1371 : List Sig := [wire43,raw4,raw3,wire51,raw5,raw0,raw1,raw2,raw7]

private theorem node1371 : impossible 8 0 st1371 := rectReject 8 st1371 6 5 0 4 2 7 0 42 (by decide +kernel)

private def st1372 : List Sig := [wire48,raw4,raw7,wire51,raw5,raw0,raw1,raw2,raw3]

set_option maxRecDepth 10000 in
private theorem node1372 : impossible 8 0 st1372 := by_search (by decide +kernel)

private def st1373 : List Sig := [wire49,raw4,raw7,wire51,raw5,raw0,raw1,raw2,raw3]

set_option maxRecDepth 10000 in
private theorem node1373 : impossible 8 0 st1373 := by_search (by decide +kernel)

private def st1374 : List Sig := [wire51,raw5,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1374 : impossible 9 0 st1374 := by
  apply reject_branch 8 0 st1374 [] [st1269,st1270,st1271,st1272,st1292,st1293,st1294,st1295,st1296,st1297,st1298,st1299,st1300,st1301,st1302,st1303,st1304,st1305,st1306,st1307,st1308,st1309,st560,st1310,st1311,st1312,st1313,st1314,st1315,st1316,st1317,st1318,st1319,st1320,st1321,st1322,st1323,st1324,st1325,st1326,st1327,st1328,st1329,st1330,st1331,st1332,st1333,st1334,st1335,st1347,st1348,st1349,st1350,st1351,st1352,st1367,st1368,st1369,st1370,st1371,st1372,st1373]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node1269
    · exact node1270
    · exact node1271
    · exact node1272
    · exact node1292
    · exact node1293
    · exact node1294
    · exact node1295
    · exact node1296
    · exact node1297
    · exact node1298
    · exact node1299
    · exact node1300
    · exact node1301
    · exact node1302
    · exact node1303
    · exact node1304
    · exact node1305
    · exact node1306
    · exact node1307
    · exact node1308
    · exact node1309
    · exact node560
    · exact node1310
    · exact node1311
    · exact node1312
    · exact node1313
    · exact node1314
    · exact node1315
    · exact node1316
    · exact node1317
    · exact node1318
    · exact node1319
    · exact node1320
    · exact node1321
    · exact node1322
    · exact node1323
    · exact node1324
    · exact node1325
    · exact node1326
    · exact node1327
    · exact node1328
    · exact node1329
    · exact node1330
    · exact node1331
    · exact node1332
    · exact node1333
    · exact node1334
    · exact node1335
    · exact node1347
    · exact node1348
    · exact node1349
    · exact node1350
    · exact node1351
    · exact node1352
    · exact node1367
    · exact node1368
    · exact node1369
    · exact node1370
    · exact node1371
    · exact node1372
    · exact node1373
  · decide +kernel

private def st1375 : List Sig := [wire51,raw5,raw6,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1375 : impossible 9 0 st1375 := by_search (by decide +kernel)

private def st1376 : List Sig := [wire52,raw5,raw7,raw0,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node1376 : impossible 9 0 st1376 := by_search (by decide +kernel)

private def st1377 : List Sig := [wire53,raw5,raw7,raw0,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node1377 : impossible 9 0 st1377 := by_search (by decide +kernel)

private def st1378 : List Sig := [wire54,raw6,raw7,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1378 : impossible 9 0 st1378 := by_search (by decide +kernel)

private def st1379 : List Sig := [wire55,raw6,raw7,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1379 : impossible 9 0 st1379 := by_search (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem node1380 : impossible 10 0 raw := by
  apply reject_branch 9 0 raw [] [st30,st59,st60,st90,st91,st92,st93,st123,st156,st181,st360,st401,st402,st403,st465,st466,st499,st524,st525,st555,st556,st557,st558,st588,st589,st651,st652,st831,st872,st873,st926,st927,st928,st992,st993,st994,st995,st996,st997,st1103,st1104,st1105,st1169,st1170,st1171,st1172,st1173,st1208,st1209,st1262,st1263,st1264,st1265,st1266,st1267,st1268,st1374,st1375,st1376,st1377,st1378,st1379]
  · simp
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node30
    · exact node59
    · exact node60
    · exact node90
    · exact node91
    · exact node92
    · exact node93
    · exact node123
    · exact node156
    · exact node181
    · exact node360
    · exact node401
    · exact node402
    · exact node403
    · exact node465
    · exact node466
    · exact node499
    · exact node524
    · exact node525
    · exact node555
    · exact node556
    · exact node557
    · exact node558
    · exact node588
    · exact node589
    · exact node651
    · exact node652
    · exact node831
    · exact node872
    · exact node873
    · exact node926
    · exact node927
    · exact node928
    · exact node992
    · exact node993
    · exact node994
    · exact node995
    · exact node996
    · exact node997
    · exact node1103
    · exact node1104
    · exact node1105
    · exact node1169
    · exact node1170
    · exact node1171
    · exact node1172
    · exact node1173
    · exact node1208
    · exact node1209
    · exact node1262
    · exact node1263
    · exact node1264
    · exact node1265
    · exact node1266
    · exact node1267
    · exact node1268
    · exact node1374
    · exact node1375
    · exact node1376
    · exact node1377
    · exact node1378
    · exact node1379
  · decide +kernel

private def st1381 : List Sig := [wire329,raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1381 : impossible 9 0 st1381 := by_search (by decide +kernel)

private def st1382 : List Sig := [wire330,raw1,raw0,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1382 : impossible 9 0 st1382 := by_search (by decide +kernel)

private def st1383 : List Sig := [wire331,raw2,raw0,raw1,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1383 : impossible 9 0 st1383 := by_search (by decide +kernel)

private def st1384 : List Sig := [wire332,raw3,raw0,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1384 : impossible 9 0 st1384 := by_search (by decide +kernel)

private def st1385 : List Sig := [wire333,raw4,raw0,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1385 : impossible 9 0 st1385 := by_search (by decide +kernel)

private def st1386 : List Sig := [wire334,raw5,raw0,raw1,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1386 : impossible 9 0 st1386 := by_search (by decide +kernel)

private def st1387 : List Sig := [wire335,raw6,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1387 : impossible 9 0 st1387 := by_search (by decide +kernel)

private def st1388 : List Sig := [wire336,raw7,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1388 : impossible 9 0 st1388 := by_search (by decide +kernel)

private def st1389 : List Sig := [wire0,raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1389 : impossible 9 1 st1389 := by_search (by decide +kernel)

private def st1390 : List Sig := [wire1,raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1390 : impossible 9 1 st1390 := by_search (by decide +kernel)

private def st1391 : List Sig := [wire2,raw0,raw2,raw1,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1391 : impossible 9 1 st1391 := by_search (by decide +kernel)

private def st1392 : List Sig := [wire3,raw0,raw2,raw1,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1392 : impossible 9 1 st1392 := by_search (by decide +kernel)

private def st1393 : List Sig := [wire4,raw0,raw3,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1393 : impossible 9 1 st1393 := by_search (by decide +kernel)

private def st1394 : List Sig := [wire5,raw0,raw3,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1394 : impossible 9 1 st1394 := by_search (by decide +kernel)

private def st1395 : List Sig := [wire6,raw0,raw4,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1395 : impossible 9 1 st1395 := by_search (by decide +kernel)

private def st1396 : List Sig := [wire7,raw0,raw4,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1396 : impossible 9 1 st1396 := by_search (by decide +kernel)

private def st1397 : List Sig := [wire8,raw0,raw5,raw1,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1397 : impossible 9 1 st1397 := by_search (by decide +kernel)

private def st1398 : List Sig := [wire9,raw0,raw5,raw1,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1398 : impossible 9 1 st1398 := by_search (by decide +kernel)

private def st1399 : List Sig := [wire337,wire10,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

private theorem node1399 : impossible 8 0 st1399 := rectReject 8 st1399 3 2 0 5 2 7 0 35 (by decide +kernel)

private def st1400 : List Sig := [wire329,raw0,wire10,raw1,raw2,raw3,raw4,raw5,raw7]

private theorem node1400 : impossible 8 0 st1400 := rectReject 8 st1400 3 1 0 5 2 7 0 35 (by decide +kernel)

private def st1401 : List Sig := [wire330,raw1,wire10,raw0,raw2,raw3,raw4,raw5,raw7]

private theorem node1401 : impossible 8 0 st1401 := rectReject 8 st1401 3 1 0 5 0 35 2 7 (by decide +kernel)

private def st1402 : List Sig := [wire331,raw2,wire10,raw0,raw1,raw3,raw4,raw5,raw7]

private theorem node1402 : impossible 8 0 st1402 := rectReject 8 st1402 4 1 7 2 3 0 0 14 (by decide +kernel)

private def st1403 : List Sig := [wire332,raw3,wire10,raw0,raw1,raw2,raw4,raw5,raw7]

private theorem node1403 : impossible 8 0 st1403 := rectReject 8 st1403 4 3 0 5 3 7 0 35 (by decide +kernel)

private def st1404 : List Sig := [wire333,raw4,wire10,raw0,raw1,raw2,raw3,raw5,raw7]

private theorem node1404 : impossible 8 0 st1404 := rectReject 8 st1404 4 3 0 5 2 7 1 35 (by decide +kernel)

private def st1405 : List Sig := [wire334,raw5,wire10,raw0,raw1,raw2,raw3,raw4,raw7]

private theorem node1405 : impossible 8 0 st1405 := rectReject 8 st1405 3 1 35 0 1 0 2 28 (by decide +kernel)

private def st1406 : List Sig := [wire336,raw7,wire10,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1406 : impossible 8 0 st1406 := by_search (by decide +kernel)

private def st1407 : List Sig := [wire121,raw0,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1407 : impossible 8 1 st1407 := by_search (by decide +kernel)

private def st1408 : List Sig := [wire121,wire10,raw0,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1408 : impossible 8 1 st1408 := by_search (by decide +kernel)

private def st1409 : List Sig := [wire121,raw1,raw0,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1409 : impossible 8 1 st1409 := by_search (by decide +kernel)

private def st1410 : List Sig := [wire123,wire10,raw0,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1410 : impossible 8 1 st1410 := by_search (by decide +kernel)

private def st1411 : List Sig := [wire125,wire10,raw0,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1411 : impossible 8 1 st1411 := by_search (by decide +kernel)

private def st1412 : List Sig := [wire127,wire10,raw0,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1412 : impossible 8 1 st1412 := by_search (by decide +kernel)

private def st1413 : List Sig := [wire128,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1413 : impossible 8 1 st1413 := by_search (by decide +kernel)

private def st1414 : List Sig := [wire128,wire10,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1414 : impossible 8 1 st1414 := by_search (by decide +kernel)

private def st1415 : List Sig := [wire128,raw5,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1415 : impossible 8 1 st1415 := by_search (by decide +kernel)

private def st1416 : List Sig := [wire130,wire10,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1416 : impossible 8 1 st1416 := by_search (by decide +kernel)

private def st1417 : List Sig := [wire13,raw0,wire10,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1417 : impossible 8 1 st1417 := by_search (by decide +kernel)

private def st1418 : List Sig := [wire24,raw1,wire10,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1418 : impossible 8 1 st1418 := by_search (by decide +kernel)

private def st1419 : List Sig := [wire35,raw2,wire10,raw0,raw1,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1419 : impossible 8 1 st1419 := by_search (by decide +kernel)

private def st1420 : List Sig := [wire10,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1420 : impossible 9 1 st1420 := by
  apply reject_branch 8 1 st1420 [st1399,st1400,st1401,st1402,st1403,st1404,st1405,st1406] [st1407,st1408,st1409,st1410,st1411,st1412,st1413,st1414,st1415,st1416,st1417,st1418,st1419]
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node1399
    · exact node1400
    · exact node1401
    · exact node1402
    · exact node1403
    · exact node1404
    · exact node1405
    · exact node1406
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node1407
    · exact node1408
    · exact node1409
    · exact node1410
    · exact node1411
    · exact node1412
    · exact node1413
    · exact node1414
    · exact node1415
    · exact node1416
    · exact node1417
    · exact node1418
    · exact node1419
  · decide +kernel

private def st1421 : List Sig := [wire10,raw0,raw6,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1421 : impossible 9 1 st1421 := by_search (by decide +kernel)

private def st1422 : List Sig := [wire11,raw0,raw6,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1422 : impossible 9 1 st1422 := by_search (by decide +kernel)

private def st1423 : List Sig := [wire12,raw0,raw7,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1423 : impossible 9 1 st1423 := by_search (by decide +kernel)

private def st1424 : List Sig := [wire13,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1424 : impossible 9 1 st1424 := by_search (by decide +kernel)

private def st1425 : List Sig := [wire13,raw0,raw7,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1425 : impossible 9 1 st1425 := by_search (by decide +kernel)

private def st1426 : List Sig := [wire14,raw1,raw2,raw0,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1426 : impossible 9 1 st1426 := by_search (by decide +kernel)

private def st1427 : List Sig := [wire15,raw1,raw2,raw0,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1427 : impossible 9 1 st1427 := by_search (by decide +kernel)

private def st1428 : List Sig := [wire16,raw1,raw3,raw0,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1428 : impossible 9 1 st1428 := by_search (by decide +kernel)

private def st1429 : List Sig := [wire17,raw1,raw3,raw0,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1429 : impossible 9 1 st1429 := by_search (by decide +kernel)

private def st1430 : List Sig := [wire18,raw1,raw4,raw0,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1430 : impossible 9 1 st1430 := by_search (by decide +kernel)

private def st1431 : List Sig := [wire19,raw1,raw4,raw0,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1431 : impossible 9 1 st1431 := by_search (by decide +kernel)

private def st1432 : List Sig := [wire20,raw1,raw5,raw0,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1432 : impossible 9 1 st1432 := by_search (by decide +kernel)

private def st1433 : List Sig := [wire21,raw1,raw5,raw0,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1433 : impossible 9 1 st1433 := by_search (by decide +kernel)

private def st1434 : List Sig := [wire22,raw1,raw6,raw0,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1434 : impossible 9 1 st1434 := by_search (by decide +kernel)

private def st1435 : List Sig := [wire23,raw1,raw0,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1435 : impossible 9 1 st1435 := by_search (by decide +kernel)

private def st1436 : List Sig := [wire23,raw1,raw6,raw0,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1436 : impossible 9 1 st1436 := by_search (by decide +kernel)

private def st1437 : List Sig := [wire338,wire24,raw1,raw0,raw2,raw3,raw4,raw5,raw6]

private theorem node1437 : impossible 8 0 st1437 := rectReject 8 st1437 3 2 0 4 0 42 2 7 (by decide +kernel)

private def st1438 : List Sig := [wire330,raw1,wire24,raw0,raw2,raw3,raw4,raw5,raw6]

private theorem node1438 : impossible 8 0 st1438 := rectReject 8 st1438 3 1 0 4 0 42 2 7 (by decide +kernel)

private def st1439 : List Sig := [wire329,raw0,wire24,raw1,raw2,raw3,raw4,raw5,raw6]

private theorem node1439 : impossible 8 0 st1439 := rectReject 8 st1439 3 1 0 4 2 7 0 42 (by decide +kernel)

private def st1440 : List Sig := [wire331,raw2,wire24,raw1,raw0,raw3,raw4,raw5,raw6]

private theorem node1440 : impossible 8 0 st1440 := rectReject 8 st1440 3 1 7 2 3 0 0 14 (by decide +kernel)

private def st1441 : List Sig := [wire332,raw3,wire24,raw1,raw0,raw2,raw4,raw5,raw6]

private theorem node1441 : impossible 8 0 st1441 := rectReject 8 st1441 4 3 0 4 0 42 3 7 (by decide +kernel)

private def st1442 : List Sig := [wire333,raw4,wire24,raw1,raw0,raw2,raw3,raw5,raw6]

private theorem node1442 : impossible 8 0 st1442 := rectReject 8 st1442 4 3 0 5 1 35 2 7 (by decide +kernel)

private def st1443 : List Sig := [wire334,raw5,wire24,raw1,raw0,raw2,raw3,raw4,raw6]

private theorem node1443 : impossible 8 0 st1443 := rectReject 8 st1443 4 1 35 0 1 0 2 28 (by decide +kernel)

private def st1444 : List Sig := [wire335,raw6,wire24,raw1,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1444 : impossible 8 0 st1444 := by_search (by decide +kernel)

private def st1445 : List Sig := [wire152,raw1,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1445 : impossible 8 1 st1445 := by_search (by decide +kernel)

private def st1446 : List Sig := [wire152,wire24,raw1,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1446 : impossible 8 1 st1446 := by_search (by decide +kernel)

private def st1447 : List Sig := [wire152,raw2,raw1,raw0,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1447 : impossible 8 1 st1447 := by_search (by decide +kernel)

private def st1448 : List Sig := [wire153,wire24,raw1,raw0,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1448 : impossible 8 1 st1448 := by_search (by decide +kernel)

private def st1449 : List Sig := [wire154,wire24,raw1,raw0,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1449 : impossible 8 1 st1449 := by_search (by decide +kernel)

private def st1450 : List Sig := [wire155,wire24,raw1,raw0,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node1450 : impossible 8 1 st1450 := by_search (by decide +kernel)

private def st1451 : List Sig := [wire218,wire24,raw1,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1451 : impossible 8 1 st1451 := by_search (by decide +kernel)

private def st1452 : List Sig := [wire23,raw1,wire24,raw0,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1452 : impossible 8 1 st1452 := by_search (by decide +kernel)

private def st1453 : List Sig := [wire157,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1453 : impossible 8 1 st1453 := by_search (by decide +kernel)

private def st1454 : List Sig := [wire157,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1454 : impossible 8 1 st1454 := by_search (by decide +kernel)

private def st1455 : List Sig := [wire157,wire24,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1455 : impossible 8 1 st1455 := by_search (by decide +kernel)

private def st1456 : List Sig := [wire10,raw0,wire24,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1456 : impossible 8 1 st1456 := by_search (by decide +kernel)

private def st1457 : List Sig := [wire51,raw5,wire24,raw1,raw0,raw2,raw3,raw4]

set_option maxRecDepth 10000 in
private theorem node1457 : impossible 8 1 st1457 := by_search (by decide +kernel)

private def st1458 : List Sig := [wire24,raw1,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1458 : impossible 9 1 st1458 := by
  apply reject_branch 8 1 st1458 [st1437,st1438,st1439,st1440,st1441,st1442,st1443,st1444] [st1445,st1446,st1447,st1448,st1449,st1450,st1451,st1452,st1453,st1454,st1455,st1456,st1457]
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node1437
    · exact node1438
    · exact node1439
    · exact node1440
    · exact node1441
    · exact node1442
    · exact node1443
    · exact node1444
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node1445
    · exact node1446
    · exact node1447
    · exact node1448
    · exact node1449
    · exact node1450
    · exact node1451
    · exact node1452
    · exact node1453
    · exact node1454
    · exact node1455
    · exact node1456
    · exact node1457
  · decide +kernel

private def st1459 : List Sig := [wire24,raw1,raw7,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1459 : impossible 9 1 st1459 := by_search (by decide +kernel)

private def st1460 : List Sig := [wire25,raw1,raw7,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1460 : impossible 9 1 st1460 := by_search (by decide +kernel)

private def st1461 : List Sig := [wire26,raw2,raw3,raw0,raw1,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1461 : impossible 9 1 st1461 := by_search (by decide +kernel)

private def st1462 : List Sig := [wire27,raw2,raw3,raw0,raw1,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1462 : impossible 9 1 st1462 := by_search (by decide +kernel)

private def st1463 : List Sig := [wire28,raw2,raw4,raw0,raw1,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1463 : impossible 9 1 st1463 := by_search (by decide +kernel)

private def st1464 : List Sig := [wire29,raw2,raw4,raw0,raw1,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1464 : impossible 9 1 st1464 := by_search (by decide +kernel)

private def st1465 : List Sig := [wire30,raw2,raw5,raw0,raw1,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1465 : impossible 9 1 st1465 := by_search (by decide +kernel)

private def st1466 : List Sig := [wire31,raw2,raw5,raw0,raw1,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1466 : impossible 9 1 st1466 := by_search (by decide +kernel)

private def st1467 : List Sig := [wire32,raw2,raw6,raw0,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1467 : impossible 9 1 st1467 := by_search (by decide +kernel)

private def st1468 : List Sig := [wire33,raw2,raw6,raw0,raw1,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1468 : impossible 9 1 st1468 := by_search (by decide +kernel)

private def st1469 : List Sig := [wire34,raw2,raw7,raw0,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1469 : impossible 9 1 st1469 := by_search (by decide +kernel)

private def st1470 : List Sig := [wire35,raw2,raw0,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1470 : impossible 9 1 st1470 := by_search (by decide +kernel)

private def st1471 : List Sig := [wire35,raw2,raw7,raw0,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1471 : impossible 9 1 st1471 := by_search (by decide +kernel)

private def st1472 : List Sig := [wire36,raw3,raw5,raw0,raw1,raw2,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1472 : impossible 9 1 st1472 := by_search (by decide +kernel)

private def st1473 : List Sig := [wire37,raw3,raw5,raw0,raw1,raw2,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1473 : impossible 9 1 st1473 := by_search (by decide +kernel)

private def st1474 : List Sig := [wire38,raw3,raw6,raw0,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1474 : impossible 9 1 st1474 := by_search (by decide +kernel)

private def st1475 : List Sig := [wire39,raw3,raw6,raw0,raw1,raw2,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1475 : impossible 9 1 st1475 := by_search (by decide +kernel)

private def st1476 : List Sig := [wire40,raw3,raw7,raw0,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1476 : impossible 9 1 st1476 := by_search (by decide +kernel)

private def st1477 : List Sig := [wire41,raw3,raw7,raw0,raw1,raw2,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1477 : impossible 9 1 st1477 := by_search (by decide +kernel)

private def st1478 : List Sig := [wire42,raw4,raw3,raw0,raw1,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1478 : impossible 9 1 st1478 := by_search (by decide +kernel)

private def st1479 : List Sig := [wire43,raw4,raw3,raw0,raw1,raw2,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1479 : impossible 9 1 st1479 := by_search (by decide +kernel)

private def st1480 : List Sig := [wire44,raw4,raw5,raw0,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1480 : impossible 9 1 st1480 := by_search (by decide +kernel)

private def st1481 : List Sig := [wire45,raw4,raw5,raw0,raw1,raw2,raw3,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1481 : impossible 9 1 st1481 := by_search (by decide +kernel)

private def st1482 : List Sig := [wire46,raw4,raw6,raw0,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1482 : impossible 9 1 st1482 := by_search (by decide +kernel)

private def st1483 : List Sig := [wire47,raw4,raw6,raw0,raw1,raw2,raw3,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1483 : impossible 9 1 st1483 := by_search (by decide +kernel)

private def st1484 : List Sig := [wire48,raw4,raw7,raw0,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1484 : impossible 9 1 st1484 := by_search (by decide +kernel)

private def st1485 : List Sig := [wire49,raw4,raw7,raw0,raw1,raw2,raw3,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1485 : impossible 9 1 st1485 := by_search (by decide +kernel)

private def st1486 : List Sig := [wire50,raw5,raw6,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1486 : impossible 9 1 st1486 := by_search (by decide +kernel)

private def st1487 : List Sig := [wire51,raw5,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1487 : impossible 9 1 st1487 := by_search (by decide +kernel)

private def st1488 : List Sig := [wire51,raw5,raw6,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1488 : impossible 9 1 st1488 := by_search (by decide +kernel)

private def st1489 : List Sig := [wire52,raw5,raw7,raw0,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node1489 : impossible 9 1 st1489 := by_search (by decide +kernel)

private def st1490 : List Sig := [wire53,raw5,raw7,raw0,raw1,raw2,raw3,raw4,raw6]

set_option maxRecDepth 10000 in
private theorem node1490 : impossible 9 1 st1490 := by_search (by decide +kernel)

private def st1491 : List Sig := [wire54,raw6,raw7,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1491 : impossible 9 1 st1491 := by_search (by decide +kernel)

private def st1492 : List Sig := [wire55,raw6,raw7,raw0,raw1,raw2,raw3,raw4,raw5]

set_option maxRecDepth 10000 in
private theorem node1492 : impossible 9 1 st1492 := by_search (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem node1493 : impossible 10 1 raw := by
  apply reject_branch 9 1 raw [st1381,st1382,st1383,st1384,st1385,st1386,st1387,st1388] [st1389,st1390,st1391,st1392,st1393,st1394,st1395,st1396,st1397,st1398,st1420,st1421,st1422,st1423,st1424,st1425,st1426,st1427,st1428,st1429,st1430,st1431,st1432,st1433,st1434,st1435,st1436,st1458,st1459,st1460,st1461,st1462,st1463,st1464,st1465,st1466,st1467,st1468,st1469,st1470,st1471,st1472,st1473,st1474,st1475,st1476,st1477,st1478,st1479,st1480,st1481,st1482,st1483,st1484,st1485,st1486,st1487,st1488,st1489,st1490,st1491,st1492]
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node1381
    · exact node1382
    · exact node1383
    · exact node1384
    · exact node1385
    · exact node1386
    · exact node1387
    · exact node1388
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node1389
    · exact node1390
    · exact node1391
    · exact node1392
    · exact node1393
    · exact node1394
    · exact node1395
    · exact node1396
    · exact node1397
    · exact node1398
    · exact node1420
    · exact node1421
    · exact node1422
    · exact node1423
    · exact node1424
    · exact node1425
    · exact node1426
    · exact node1427
    · exact node1428
    · exact node1429
    · exact node1430
    · exact node1431
    · exact node1432
    · exact node1433
    · exact node1434
    · exact node1435
    · exact node1436
    · exact node1458
    · exact node1459
    · exact node1460
    · exact node1461
    · exact node1462
    · exact node1463
    · exact node1464
    · exact node1465
    · exact node1466
    · exact node1467
    · exact node1468
    · exact node1469
    · exact node1470
    · exact node1471
    · exact node1472
    · exact node1473
    · exact node1474
    · exact node1475
    · exact node1476
    · exact node1477
    · exact node1478
    · exact node1479
    · exact node1480
    · exact node1481
    · exact node1482
    · exact node1483
    · exact node1484
    · exact node1485
    · exact node1486
    · exact node1487
    · exact node1488
    · exact node1489
    · exact node1490
    · exact node1491
    · exact node1492
  · decide +kernel

private def st1494 : List Sig := [wire329,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1494 : impossible 9 1 st1494 := by_search (by decide +kernel)

private def st1495 : List Sig := [wire329,raw0,raw1,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1495 : impossible 9 1 st1495 := by_search (by decide +kernel)

private def st1496 : List Sig := [wire330,raw0,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1496 : impossible 9 1 st1496 := by_search (by decide +kernel)

private def st1497 : List Sig := [wire330,raw1,raw0,raw2,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1497 : impossible 9 1 st1497 := by_search (by decide +kernel)

private def st1498 : List Sig := [wire331,raw0,raw1,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1498 : impossible 9 1 st1498 := by_search (by decide +kernel)

private def st1499 : List Sig := [wire331,raw2,raw0,raw1,raw3,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1499 : impossible 9 1 st1499 := by_search (by decide +kernel)

private def st1500 : List Sig := [wire332,raw0,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1500 : impossible 9 1 st1500 := by_search (by decide +kernel)

private def st1501 : List Sig := [wire332,raw3,raw0,raw1,raw2,raw4,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1501 : impossible 9 1 st1501 := by_search (by decide +kernel)

private def st1502 : List Sig := [wire333,raw0,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1502 : impossible 9 1 st1502 := by_search (by decide +kernel)

private def st1503 : List Sig := [wire333,raw4,raw0,raw1,raw2,raw3,raw5,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1503 : impossible 9 1 st1503 := by_search (by decide +kernel)

private def st1504 : List Sig := [wire334,raw0,raw1,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1504 : impossible 9 1 st1504 := by_search (by decide +kernel)

private def st1505 : List Sig := [wire334,raw5,raw0,raw1,raw2,raw3,raw4,raw6,raw7]

set_option maxRecDepth 10000 in
private theorem node1505 : impossible 9 1 st1505 := by_search (by decide +kernel)

private def st1506 : List Sig := [wire335,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1506 : impossible 9 1 st1506 := by_search (by decide +kernel)

private def st1507 : List Sig := [wire335,raw6,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1507 : impossible 9 1 st1507 := by_search (by decide +kernel)

private def st1508 : List Sig := [wire336,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1508 : impossible 9 1 st1508 := by_search (by decide +kernel)

private def st1509 : List Sig := [wire336,raw7,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1509 : impossible 9 1 st1509 := by_search (by decide +kernel)

private def st1510 : List Sig := [wire10,raw0,raw1,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1510 : impossible 9 2 st1510 := by_search (by decide +kernel)

private def st1511 : List Sig := [wire13,raw0,raw1,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1511 : impossible 9 2 st1511 := by_search (by decide +kernel)

private def st1512 : List Sig := [wire23,raw1,raw0,raw2,raw3,raw4,raw5,raw7]

set_option maxRecDepth 10000 in
private theorem node1512 : impossible 9 2 st1512 := by_search (by decide +kernel)

private def st1513 : List Sig := [wire24,raw1,raw0,raw2,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1513 : impossible 9 2 st1513 := by_search (by decide +kernel)

private def st1514 : List Sig := [wire35,raw2,raw0,raw1,raw3,raw4,raw5,raw6]

set_option maxRecDepth 10000 in
private theorem node1514 : impossible 9 2 st1514 := by_search (by decide +kernel)

private def st1515 : List Sig := [wire51,raw5,raw0,raw1,raw2,raw3,raw4,raw7]

set_option maxRecDepth 10000 in
private theorem node1515 : impossible 9 2 st1515 := by_search (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem node1516 : impossible 10 2 raw := by
  apply reject_branch 9 2 raw [st1494,st1495,st1496,st1497,st1498,st1499,st1500,st1501,st1502,st1503,st1504,st1505,st1506,st1507,st1508,st1509] [st1510,st1511,st1512,st1513,st1514,st1515]
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact node1494
    · exact node1495
    · exact node1496
    · exact node1497
    · exact node1498
    · exact node1499
    · exact node1500
    · exact node1501
    · exact node1502
    · exact node1503
    · exact node1504
    · exact node1505
    · exact node1506
    · exact node1507
    · exact node1508
    · exact node1509
  · intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
    · exact node1510
    · exact node1511
    · exact node1512
    · exact node1513
    · exact node1514
    · exact node1515
  · decide +kernel

set_option maxRecDepth 10000 in
private theorem node1517 : impossible 10 3 raw := by_search (by decide +kernel)

private lemma excluded0 : impossible 10 0 raw := node1380

private lemma excluded1 : impossible 10 1 raw := node1493

private lemma excluded2 : impossible 10 2 raw := node1516

private lemma excluded3 : impossible 10 3 raw := node1517

end PEqualNP.Outside.G514

open PEqualNP.Outside.G514

theorem PEqualNP.Outside.L_meta_514 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 7)) s → 11 ≤ s := by
  intro s hs
  by_contra h
  obtain ⟨C,hg,hc,he⟩ := hs
  have bound : C.size ≤ 10 := by omega
  obtain ⟨k,t,S,hk,ht,hs⟩ := extract C.gates raw hg (circuit_target C hg he)
  have eq := necessary ht hs
  have sz := live_size ht
  rw [←eq,List.toFinset_card_of_nodup raw_nd] at sz
  have len : raw.length=8 := rfl
  change C.gates.length ≤ 10 at bound
  have nt : t≤3 := by omega
  have no : impossible 10 t raw := by interval_cases t <;> first | exact excluded0 | exact excluded1 | exact excluded2 | exact excluded3
  exact no ht (by omega) raw_nd eq
