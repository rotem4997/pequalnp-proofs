import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_8457_aux
abbrev Q:=Bool
abbrev K:=Nat×Nat
abbrev J:=List K
abbrev V:=List (Nat×Nat×Nat×Nat)
abbrev M:=List Nat
abbrev I:=List Q
abbrev F (n:Nat):=Fin n->Q
abbrev Z (n:Nat):=F n->Q
abbrev X (n:Nat):=List (Z n×Nat)
open Nat (land lor xor shiftRight shiftLeft add sub mul div mod beq ble blt)
lemma jV:(false=true)=False:=Bool.false_eq_true
lemma jW {b:Q}:(true&&b)=b:=Bool.true_and b
lemma jX {a b:Q}:((a||b)=true)=(a=true\/b=true):=Bool.or_eq_true a b
lemma jY {a b:Q}:((a&&b)=true)=(a=true/\b=true):=Bool.and_eq_true a b
lemma jZ:(!false)=true:=Bool.not_false
lemma kt {b:Q}:((!b)=true)=(b=false):=Bool.not_eq_true' b
lemma kA {α:Type _} (l1 l2 l3:List α):(l1++l2)++l3=l1++(l2++l3):=List.append_assoc l1 l2 l3
lemma kB {α β:Type _} {f : α->β}{a : α}{l:List α}:(a::l).map f=f a::l.map f:=List.map_cons
lemma kC {α:Type _} {a b : α}{l:List α}:a∈b::l↔a=b\/a∈l:=List.mem_cons
lemma kD {α:Type _} {a : α}{l:List α}:(a::l).length=l.length+1:=List.length_cons
lemma kE {α:Type _} {l1 l2:List α}:(l1++l2).length=l1.length+l2.length:=List.length_append
lemma kF {α:Type _} {a : α}{l:List α}:(a::l).reverse=l.reverse++[a]:=List.reverse_cons
lemma kG {α β:Type _} {f : α->β->β}{b : β}{a : α}{l:List α}:(a::l).foldr f b=f a (l.foldr f b):=List.foldr_cons
lemma kH {α:Type _} {p : α->Q}{l:List α}:l.all p=true↔∀x∈l,p x=true:=List.all_eq_true
lemma kJ {α:Type _} {p : α->Q}{l:List α}:l.any p=true↔∃x∈l,p x=true:=List.any_eq_true
lemma kK {n i:Nat}:(2 ^ n - 1).testBit i=decide (i < n):=by simp[Nat.testBit_two_pow_sub_one]
lemma kL {x y:Nat}(h:∀i,x.testBit i=y.testBit i):x=y:=Nat.eq_of_testBit_eq h
lemma kM {x y i:Nat}:(x|||y).testBit i=(x.testBit i||y.testBit i):=by simp[Nat.testBit_or]
lemma kN {x y i:Nat}:(x&&&y).testBit i=(x.testBit i&&y.testBit i):=by simp[Nat.testBit_and]
lemma kP {x y i:Nat}:(x^^^y).testBit i=(x.testBit i ^^ y.testBit i):=by simp[Nat.testBit_xor]
lemma kQ {x k i:Nat}:(x >>> k).testBit i=x.testBit (k+i):=by simp[Nat.testBit_shiftRight]
lemma kR {x y:Nat}:Nat.lor x y=x|||y:=Nat.lor_eq
lemma kS {x y:Nat}:Nat.land x y=x&&&y:=Nat.land_eq
lemma kT {x y:Nat}:Nat.xor x y=x^^^y:=Nat.xor_eq
lemma kU {i:Nat}:(0:Nat).testBit i=false:=Nat.zero_testBit i
lemma kV {α:Type _} [DecidableEq α] {β : α->Sort _} {f:∀a,β a}{a b : α}{v : β a}(h:b≠a):Function.update f a v b=f b:=Function.update_of_ne h v f
lemma kW {α:Type _} [DecidableEq α] {β : α->Sort _} {f:∀a,β a}{a : α}{v : β a}:Function.update f a v a=v:=Function.update_self a v f
lemma kX {α β:Type _} {f : α->β}{l1 l2:List α}:(l1++l2).map f=l1.map f++l2.map f:=List.map_append
lemma kY {α β:Type _} (f : α->β){l:List α}:(l.map f).length=l.length:=List.length_map f
lemma hU {α:Type _} {l:List α}:l++[]=l:=List.append_nil l
lemma kZ {α:Type _} {a : α}{l1 l2:List α}:(a::l1)++l2=a::(l1++l2):=List.cons_append
lemma mE {α:Type _} {a : α} {l₁ l₂:List α}:(l₁++a::l₂).Perm (a::(l₁++l₂)):=List.perm_middle
lemma mF (a b:Nat):a+b=b+a:=Nat.add_comm a b
lemma mG (a b d:Nat):a+b+d=a+(b+d):=Nat.add_assoc a b d
lemma mH {a:Nat}:a+0=a:=Nat.add_zero a
lemma mJ (a:Nat):0<=a:=Nat.zero_le a
lemma hV {a:Q}:(a&&true)=a:=Bool.and_true a
lemma mK {a:Q}:(a ^^ true)=!a:=Bool.bne_true a
lemma mL (n:Nat):0 < 2 ^ n:=Nat.two_pow_pos n
lemma mM {α β:Type _} {f : α->β}{b : β}{l:List α}:b∈l.map f↔∃a∈l,f a=b:=List.mem_map
lemma hW {α β γ:Type _} {g : β->γ}{f : α->β}{l:List α}:(l.map f).map g=l.map (g ∘ f):=List.map_map
lemma mN {α β γ:Type _} (f : β->γ)(g : α->β):f ∘ g=fun x=>f (g x):=Function.comp_def f g
lemma mP {α:Type _} (l:List α):l.Perm l:=List.Perm.refl l
lemma mQ {α:Type _} (l:List α)(d : α){i:Nat}(h:l.length<=i):l.getD i d=d:=List.getD_eq_default l d h
lemma mR {α:Type _} (x : α){l1 l2:List α}(h:l1.Perm l2):(x::l1).Perm (x::l2):=List.Perm.cons x h
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev G:=Gate
abbrev U:=List G
open Sum
open Function (update Bijective Injective bijective_id)
open List (ofFn range finRange)
open Fin (last snoc)
open Prod (fst)
abbrev nV:=HasCircuitSize
lemma jN {a:Nat}{l:M}:(a::l).sum=a+l.sum:=List.sum_cons
lemma jP {A:Type _}{a:A}{l:List A}:a∈a::l:=List.mem_cons_self
lemma jQ {A:Type _}{l:List A}:l.take l.length=l:=List.take_length
lemma jR {a b:Nat}(h:a<=b):min a b=a:=Nat.min_eq_left h
lemma jS {b:Q}:(b||false)=b:=Bool.or_false b
lemma jT {b:Q}:(false&&b)=false:=Bool.false_and b
lemma jU {b:Q}:(b=false)↔¬b=true:=Bool.eq_false_iff
lemma hX {A:Type _}{a:A}(b:A){l:List A}(h:a∈l):a∈b::l:=List.mem_cons_of_mem b h
lemma mS {A B:Type _}{f:A->B}:([]:List A).map f=[]:=List.map_nil
lemma mT {A:Type _}{l:List A}:[]++l=l:=List.nil_append l
lemma mU {A:Type _}{l1 l2:List A}:(l1++l2).reverse=l2.reverse++l1.reverse:=List.reverse_append
lemma mV {A:Type _}:([]:List A).reverse=[]:=List.reverse_nil
lemma mW {A:Type _}{a:A}{l:List A}:[a]++l=a::l:=List.singleton_append
lemma mX {A:Type _}{l1 l2:List A}{i:Nat}(h:i < l1.length):(l1++l2)[i]?=l1[i]?:=List.getElem?_append_left h
lemma mY {A:Type _}{l1 l2:List A}{i:Nat}(h:l1.length<=i):(l1++l2)[i]?=l2[i - l1.length]?:=List.getElem?_append_right h
lemma mZ {A:Type _}{l:List A}{i:Nat}(h:l.length<=i):l[i]?=none:=List.getElem?_eq_none h
lemma nA {a b:Nat}:(ble a b=true)=(a<=b):=Nat.ble_eq
lemma nB {a b:Nat}:(blt a b=true)=(a < b):=Nat.blt_eq
lemma nC {a b:Nat}:(beq a b=true)=(a=b):=Nat.beq_eq
lemma nD {a:Nat}:beq a a=true:=Nat.beq_refl a
lemma nE {a b:Q}:((a||b)=false)↔(a=false/\b=false):=Bool.or_eq_false_iff
lemma nF {a b:Q}:((a&&b)=false)↔(a=false\/b=false):=Bool.and_eq_false_iff
lemma nG {a b c:Q}:((a||b)||c)=(a||(b||c)):=Bool.or_assoc a b c
lemma nH:(!true)=false:=Bool.not_true
lemma nJ {b:Q}:(b&&false)=false:=Bool.and_false b
lemma nK {b:Q}:(false||b)=b:=Bool.false_or b
lemma nL {b:Q}:((!b)=false)=(b=true):=Bool.not_eq_false' b
lemma nM {i:Nat}:(0:Nat).testBit i=false:=Nat.zero_testBit i
lemma nN {a b i:Nat}:(a <<< b).testBit i=(decide (b<=i)&&a.testBit (i - b)):=by simp[Nat.testBit_shiftLeft]
lemma nP (n:Nat):n+1≠0:=Nat.succ_ne_zero n
lemma nQ {a b:Nat}(h:b<=a):a - b+b=a:=Nat.sub_add_cancel h
lemma nR (a b:Nat):a+b - b=a:=Nat.add_sub_cancel a b
lemma nS {p:Prop}(h:¬p->False):p:=Classical.byContradiction h
lemma nT {n i:Nat}:n.testBit i=decide (n / 2 ^ i % 2=1):=Nat.testBit_eq_decide_div_mod_eq
lemma nW {i j:Nat}:(2 ^ i).testBit j=decide (i=j):=Nat.testBit_two_pow
lemma hY {i:Nat}:(2 ^ i).testBit i=true:=Nat.testBit_two_pow_self
lemma hZ {x i:Nat}(h:x < 2 ^ i):x.testBit i=false:=Nat.testBit_eq_false_of_lt h
lemma jA {a b c:Nat}(h:0 < a)(hbc:b<=c):a ^ b<=a ^ c:=Nat.pow_le_pow_right h hbc
lemma jB {x n:Nat}(h:∀i ≥ n,x.testBit i=false):x < 2 ^ n:=Nat.lt_pow_two_of_testBit x h
lemma nX {a b:Nat}:add a b=a+b:=Nat.add_eq
lemma nY {a b:Nat}:sub a b=a - b:=Nat.sub_eq
lemma jC {A:Type _}{a:A}:¬a∈([]:List A):=List.not_mem_nil
lemma jD {A:Type _}{a:A}{l1 l2:List A}:a∈l1++l2↔a∈l1\/a∈l2:=List.mem_append
lemma jE {A:Type _}{n:Nat}{f:Fin n->A}{a:A}:a∈List.ofFn f↔∃i,f i=a:=List.mem_ofFn
lemma jF {n i:Nat}:i∈List.range n↔i < n:=List.mem_range
lemma jG {n:Nat}(i:Fin n):i∈List.finRange n:=List.mem_finRange i
lemma nZ {n:Nat}:(List.range n).length=n:=List.length_range
lemma pA {A:Type _}(l:List A):l.map id=l:=List.map_id l
lemma jH {A B:Type _}{f g:A->B}{l:List A}(h:∀a∈l,f a=g a):l.map f=l.map g:=List.map_congr_left h
lemma jJ {A:Type _}{l:List A}{i:Nat}{a:A}:l[i]?=some a↔∃h:i < l.length,l[i]=a:=List.getElem?_eq_some_iff
lemma jK {A:Type _}{l:List A}{i:Nat}(h:i < l.length):l[i]?=some l[i]:=List.getElem?_eq_getElem h
lemma jL {A:Type _}(l:List A)(d:A){i:Nat}(h:i < l.length):l.getD i d=l[i]:=List.getD_eq_getElem l d h
lemma pB {A:Type _}{i:Nat}{l:List A}:(l.take i).length=min i l.length:=List.length_take
lemma pC {A:Type _}:([]:List A).length=0:=List.length_nil
abbrev u6 (n:Nat):=(Fin n->Bool)->Bool
def q3 (gs:U)(w:I):I:=
 gs.foldl (fun w g=>w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]) w
lemma zd (gs gs':U) (w:I):q3 (gs++gs') w=q3 gs' (q3 gs w):=by simp[q3,List.foldl_append]
lemma y1 (gs:U):∀w:I,∃t:I,q3 gs w=w++t/\t.length=gs.length:=by
 induction gs with
 | nil=>intro w;exact⟨[],by simp[q3],rfl⟩
 | cons g gs ih =>
  intro w;obtain⟨t,b,c⟩:=ih (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]);refine⟨g.op.eval (g.inputs.map fun i=>w.getD i false)::t,?_,by simp[c]⟩
  have:q3 (g::gs) w
   = q3 gs (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]):=rfl
  rw[this,b];simp
lemma qu (gs:U)(w:I):(q3 gs w).length=w.length+gs.length:=by obtain⟨t,b,c⟩:=y1 gs w;rw[b];simp[c]
lemma ve (gs:U)(w:I)(i:Nat)(h:i < w.length):(q3 gs w).getD i false=w.getD i false:=by obtain⟨t,b,_⟩:=y1 gs w;rw[b,List.getD_append _ _ _ _ h]
def Ok (g:G):Prop:=
 g.op∈({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\g.inputs.length<=2
lemma q8 {α:Type} (L:List α)(S d : α)(j:Nat)(h:j≠L.length):(L++[S]).getD j d=L.getD j d:=by
 by_cases b:j < L.length
 . exact List.getD_append _ _ _ _ b
 . rw[mQ _ _ (by simp;omega),mQ _ _ (by omega)]
lemma z0 {α:Type} (L:List α)(S d : α):(L++[S]).getD L.length d=S:=by simp
lemma z2 {α:Type} (L:List α)(S d : α)(k:Nat)(h:L.length=k):(L++[S]).getD k d=S:=by subst h;simp
def yb {n:Nat} (L:List (Finset (Fin n))) (g:G):Finset (Fin n):=
 (g.inputs.map fun a=>L.getD a ∅).foldr (· ∪ ·) ∅
lemma q71 {n:Nat}(l:M) (F:Nat->Finset (Fin n)) (i:Fin n):i∈(l.map F).foldr (· ∪ ·) ∅↔∃a∈l,i∈F a:=by
 induction l with
 | nil=>simp
 | cons b l ih=>simp[ih]
lemma kf {n:Nat} (L:List (Finset (Fin n))) (g:G)(i:Fin n):i∈yb L g↔∃a∈g.inputs,i∈L.getD a ∅:=
 q71 _ _ _
def zb {n:Nat}(gs:U) (L:List (Finset (Fin n))):List (Finset (Fin n)):=
 gs.foldl (fun L g=>L++[yb L g]) L
def qr (n:Nat):List (Finset (Fin n)):=ofFn fun i:Fin n=>{i}
def rc {n:Nat}(x y:F n) (L:List (Finset (Fin n))) (w w':I):Prop:=
 L.length=w.length/\w.length=w'.length /\
  ∀j:Nat,(∀i∈L.getD j ∅,x i=y i)->w.getD j false=w'.getD j false
lemma k6 {n:Nat}(x y:F n)(gs:U):∀(L:List (Finset (Fin n))) (w w':I),rc x y L w w'->rc x y (zb gs L) (q3 gs w) (q3 gs w'):=by
 induction gs with
 | nil=>intro L w w' h;exact h
 | cons g gs ih =>
  intro L w w' h;obtain⟨c,d,e⟩:=h;apply ih (L++[yb L g])
    (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)])
    (w'++[g.op.eval (g.inputs.map fun i=>w'.getD i false)])
  refine⟨by simp[c],by simp[d],?_⟩
  intro j b;by_cases s:j=L.length
  . subst s;rw[z0] at b;rw[c,z0,d,z0]
    congr 1
    apply jH
    intro a t;exact e a (fun i hi=>b i ((kf L g i).2 ⟨a,t,hi⟩))
  . rw[q8 _ _ _ _ s] at b;rw[q8 _ _ _ _ (by omega),q8 _ _ _ _ (by omega)]
    exact e j b
lemma j4 {n:Nat}(x y:F n):rc x y (qr n) (ofFn x) (ofFn y):=by
 refine⟨by simp[qr],by simp,?_⟩
 intro j c;by_cases b:j < n
 . have d:x ⟨j,b⟩=y ⟨j,b⟩:=c _ (by simp[qr,b]);simp[b,d]
 . rw[mQ _ _ (by simp;omega),mQ _ _ (by simp;omega)]
def lv {n:Nat}(t:Nat) (L:List (Finset (Fin n))):Prop:=
 ∀W:Finset Nat,(W.biUnion fun j=>L.getD j ∅).card<=t+W.card
lemma wh {n:Nat}:lv 0 (qr n):=by
 intro W;refine le_trans Finset.card_biUnion_le ?_
 rw[zero_add,Finset.card_eq_sum_ones]
 apply Finset.sum_le_sum
 intro j _;by_cases b:j < n
 . simp[qr,b]
 . rw[mQ _ _ (by simp[qr];omega)];simp
lemma pu {n:Nat}(t:Nat) (L:List (Finset (Fin n))) (g:G)(s:g.inputs.length<=2)(h:lv t L):lv (t+1) (L++[yb L g]):=by
 intro W;by_cases c:L.length∈W
 . have u:(W.biUnion fun j=>(L++[yb L g]).getD j ∅)
      ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j=>L.getD j ∅):=by
    intro i hi;rw[Finset.mem_biUnion] at hi ⊢;obtain⟨j,v,b⟩:=hi;by_cases d:j=L.length
    . subst d;rw[z0] at b;obtain⟨a,x,y⟩:=(kf L g i).1 b;exact⟨a,Finset.mem_union_right _ (List.mem_toFinset.2 x),y⟩
    . rw[q8 _ _ _ _ d] at b;exact⟨j,Finset.mem_union_left _ (Finset.mem_erase.2 ⟨d,v⟩),b⟩
   have hc1:(W.erase L.length ∪ g.inputs.toFinset).card<=(W.card - 1)+2:=by
    refine le_trans (Finset.card_union_le _ _) ?_
    rw[Finset.card_erase_of_mem c]
    exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) s) _
   have hWpos:1<=W.card:=Finset.card_pos.2 ⟨_,c⟩
   have:=h (W.erase L.length ∪ g.inputs.toFinset)
   have:=Finset.card_le_card u
   omega
 . have z:(W.biUnion fun j=>(L++[yb L g]).getD j ∅)
      = (W.biUnion fun j=>L.getD j ∅):=by
    apply Finset.biUnion_congr rfl
    intro j hj;exact q8 _ _ _ _ (fun e=>c (e ▸ hj))
   rw[z]
   have:=h W
   omega
lemma xr {n:Nat}(gs:U):∀(t:Nat) (L:List (Finset (Fin n))),(∀g∈gs,Ok g)->lv t L->lv (t+gs.length) (zb gs L):=by
 induction gs with
 | nil=>intro t L _ h;exact h
 | cons g gs ih =>
  intro t L b h
  have:=ih (t+1) (L++[yb L g]) (fun g' c' => b g' (hX _ c'))
   (pu t L g (b g jP).2 h)
  rw[kD,show t+(gs.length+1)=t+1+gs.length by omega]
  exact this
lemma xt (n:Nat) (f:(F n)->Q) (T:Finset (Fin n)) (d:∀i∈T,∃x:F n,f (update x i (!x i))≠f x) (s:Nat)(h:nV n f s):T.card<=s+1:=by
 obtain⟨C,ok,b,hev⟩:=h;have b':C.gates.length<=s:=b;set S:=(zb C.gates (qr n)).getD C.output ∅ with g
 have j:T ⊆ S:=by
  intro i t;by_contra hi;obtain⟨x,u⟩:=d i t;apply u
  have v:=(k6 (update x i (!x i)) x C.gates _ _ _ (j4 _ _)).2.2 C.output (by
   intro k y
   have:k≠i:=fun e=>hi (e ▸ y)
   simp[kV this])
  rw[<- hev,<- hev]
  exact v
 have c:=xr C.gates 0 (qr n) ok wh {C.output};simp only[Finset.singleton_biUnion,Finset.card_singleton,zero_add] at c;rw[<- g] at c
 have:=Finset.card_le_card j
 omega
def vg (g:G):G:=
 match g.op with
 | GateOp.not=>⟨GateOp.not,g.inputs.take 1⟩
 | _=>g
lemma xz (g:G)(F:Nat->Q):(vg g).op.eval ((vg g).inputs.map F)=g.op.eval (g.inputs.map F):=by
 obtain⟨op,inputs⟩:=g;cases op<;>simp only[vg]
 cases inputs<;>simp[GateOp.eval]
def mc (g:G):Prop:=Ok g/\(g.op=GateOp.not->g.inputs.length<=1)
lemma q45 (g:G)(h:Ok g):mc (vg g):=by
 obtain⟨op,inputs⟩:=g;obtain⟨b,hlen⟩:=h;rcases b with h|h|h
 . have:op=GateOp.and:=h
   subst this;exact⟨⟨Or.inl rfl,hlen⟩,by simp[vg]⟩
 . have:op=GateOp.or:=h
   subst this;exact⟨⟨Or.inr (Or.inl rfl),hlen⟩,by simp[vg]⟩
 . have:op=GateOp.not:=h
   subst this;refine⟨⟨Or.inr (Or.inr rfl),?_⟩,fun _ => ?_⟩<;>simp[vg]<;>omega
lemma jd (gs:U):∀w:I,q3 (gs.map vg) w=q3 gs w:=by
 induction gs with
 | nil=>intro w;rfl
 | cons g gs ih =>
  intro w;have s1:q3 ((g::gs).map vg) w=q3 (gs.map vg)
   (w++[(vg g).op.eval ((vg g).inputs.map fun i=>w.getD i false)]):=rfl
  have b:q3 (g::gs) w
   = q3 gs (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]):=rfl
  rw[s1,b,xz,ih]
abbrev o1:=Sum Bool Nat
def ze (w:I):o1->Q
 | inl c=>c
 | inr j=>w.getD j false
def qn (m:Nat):o1->Prop
 | inl _=>True
 | inr j=>j < m
def wr (m:Nat):List o1->Option G×o1
 | []=>(none,inl true)
 | inl c::_=>(none,inl (!c))
 | inr j::_=>(some ⟨GateOp.not,[j]⟩,inr m)
def ko (m:Nat):List o1->Option G×o1
 | []=>(none,inl true)
 | [inl c]=>(none,inl c)
 | [inr j]=>(none,inr j)
 | [inl c,inl d]=>(none,inl (c&&d))
 | [inl c,inr j]=>(none,bif c then inr j else inl false)
 | [inr j,inl c]=>(none,bif c then inr j else inl false)
 | [inr j,inr k]=>(some ⟨GateOp.and,[j,k]⟩,inr m)
 | _=>(none,inl false)
def ji (m:Nat):List o1->Option G×o1
 | []=>(none,inl false)
 | [inl c]=>(none,inl c)
 | [inr j]=>(none,inr j)
 | [inl c,inl d]=>(none,inl (c||d))
 | [inl c,inr j]=>(none,bif c then inl true else inr j)
 | [inr j,inl c]=>(none,bif c then inl true else inr j)
 | [inr j,inr k]=>(some ⟨GateOp.or,[j,k]⟩,inr m)
 | _=>(none,inl false)
def qg (op:GateOp)(m:Nat)(b:List o1):Option G×o1:=
 match op with
 | GateOp.and=>ko m b
 | GateOp.or=>ji m b
 | GateOp.not=>wr m b
 | _=>(none,inl false)
def cs (m:Nat)(g:G):Prop:=
 (g.op=GateOp.not/\∃j,j < m/\g.inputs=[j]) \/
 ((g.op=GateOp.and\/g.op=GateOp.or)/\∃j k,j < m/\k < m/\g.inputs=[j,k])
lemma j2 {m:Nat}{g:G}(h:cs m g):∀a∈g.inputs,a < m:=by
 rcases h with ⟨_,j,d,c⟩|⟨_,j,k,d,hk,c⟩
 . intro a b;simp[c] at b;omega
 . intro a b;simp[c] at b;rcases b with rfl|rfl<;>omega
def yq (n:Nat)(gs:U):Prop:=
 ∀p g,gs[p]?=some g->cs (n+p) g
lemma xc (op:GateOp)(m:Nat)(e:List o1):∀g∈(qg op m e).1,Ok g:=by
 intro g d;cases op<;>simp only[qg] at d
 . rcases e with _|⟨a,_|⟨b,_|⟨c,l⟩⟩⟩<;>(try cases a)<;>(try cases b) <;>
    simp[ko] at d<;>(subst d;simp[Ok])
 . rcases e with _|⟨a,_|⟨b,_|⟨c,l⟩⟩⟩<;>(try cases a)<;>(try cases b) <;>
    simp[ji] at d<;>(subst d;simp[Ok])
 . rcases e with _|⟨a,l⟩<;>(try cases a) <;>
    simp[wr] at d<;>(subst d;simp[Ok])
 . simp at d
 . simp at d
lemma q80 (op:GateOp)(m:Nat)(e:List o1)(h:∀s∈e,qn m s):∀g∈(qg op m e).1,cs m g:=by
 intro g d;cases op<;>simp only[qg] at d
 . rcases e with _|⟨a,_|⟨b,_|⟨c,l⟩⟩⟩<;>(try cases a)<;>(try cases b) <;>
    simp[ko] at d
   subst d;exact Or.inr ⟨Or.inl rfl,_,_,h (inr _) (by simp),h (inr _) (by simp),rfl⟩
 . rcases e with _|⟨a,_|⟨b,_|⟨c,l⟩⟩⟩<;>(try cases a)<;>(try cases b) <;>
    simp[ji] at d
   subst d;exact Or.inr ⟨Or.inr rfl,_,_,h (inr _) (by simp),h (inr _) (by simp),rfl⟩
 . rcases e with _|⟨a,l⟩<;>(try cases a)<;>simp[wr] at d
   subst d;exact Or.inl ⟨rfl,_,h (inr _) (by simp),rfl⟩
 . simp at d
 . simp at d
lemma jh (op:GateOp)(m:Nat)(e:List o1)(h:op=GateOp.and\/op=GateOp.or\/op=GateOp.not)(hlen:e.length<=2)(i:op=GateOp.not->e.length<=1)(g:∃c,inl c∈e):(qg op m e).1=none:=by
 obtain⟨c,g⟩:=g;rcases h with rfl|rfl|rfl
 . rcases e with _|⟨a,_|⟨b,_|⟨d,l⟩⟩⟩<;>(try cases a)<;>(try cases b) <;>
    simp_all [qg,ko]
 . rcases e with _|⟨a,_|⟨b,_|⟨d,l⟩⟩⟩<;>(try cases a)<;>(try cases b) <;>
    simp_all [qg,ji]
 . have:=i rfl
   rcases e with _|⟨a,_|⟨b,l⟩⟩<;>(try cases a)<;>simp_all [qg,wr]
lemma kn (op:GateOp)(h:op=GateOp.and\/op=GateOp.or\/op=GateOp.not)(w:I)(g:List o1)(hlen:g.length<=2)(hv:∀s∈g,qn w.length s):qn (w.length+(qg op w.length g).1.toList.length) (qg op w.length g).2/\ze (q3 (qg op w.length g).1.toList w) (qg op w.length g).2=op.eval (g.map (ze w)):=by
 rcases h with rfl|rfl|rfl
 . rcases g with _|⟨a,_|⟨b,_|⟨d,l⟩⟩⟩
   . simp[qg,ko,qn,ze,GateOp.eval]
   . cases a<;>simp_all [qg,ko,qn,ze,GateOp.eval,q3]
   . cases a<;>cases b<;>(try rename_i c e;cases c)<;>(try cases e) <;>
      simp_all [qg,ko,qn,ze,GateOp.eval,q3]
   . simp at hlen
 . rcases g with _|⟨a,_|⟨b,_|⟨d,l⟩⟩⟩
   . simp[qg,ji,qn,ze,GateOp.eval]
   . cases a<;>simp_all [qg,ji,qn,ze,GateOp.eval,q3]
   . cases a<;>cases b<;>(try rename_i c e;cases c)<;>(try cases e) <;>
      simp_all [qg,ji,qn,ze,GateOp.eval,q3]
   . simp at hlen
 . rcases g with _|⟨a,l⟩
   . simp[qg,wr,qn,ze,GateOp.eval]
   . cases a<;>simp_all [qg,wr,qn,ze,GateOp.eval,q3]
def qa (n:Nat)(b:List o1×U)(g:G):List o1×U:=
 (b.1++[(qg g.op (n+b.2.length)
   (g.inputs.map fun i=>b.1.getD i (inl false))).2],
  b.2++(qg g.op (n+b.2.length)
   (g.inputs.map fun i=>b.1.getD i (inl false))).1.toList)
def u4 (n:Nat)(gs:U)(b:List o1×U):List o1×U:=
 gs.foldl (qa n) b
lemma k4 (n:Nat)(g:G)(gs:U)(b:List o1×U):u4 n (g::gs) b=u4 n gs (qa n b g):=rfl
lemma jz (n:Nat)(b c:U)(d:List o1×U):u4 n (b++c) d=u4 n c (u4 n b d):=by simp[u4,List.foldl_append]
lemma nh (n:Nat)(gs:U):∀b:List o1×U,(u4 n gs b).1.length=b.1.length+gs.length:=by
 induction gs with
 | nil=>intro b;rfl
 | cons g gs ih =>
  intro b;rw[k4,ih]
  simp only[qa,kE,kD,pC];omega
lemma wy (n k:Nat)(d:o1)(gs:U):∀b:List o1×U,k < b.1.length->(u4 n gs b).1.getD k d=b.1.getD k d:=by
 induction gs with
 | nil=>intro b _;rfl
 | cons g gs ih =>
  intro b hk;rw[k4,ih (qa n b g) (by simp[qa];omega)]
  exact q8 _ _ _ _ (by omega)
lemma y2 {α:Type} (o:Option α):o.toList.length<=1:=by cases o<;>simp
lemma bq (n:Nat)(gs:U):∀b:List o1×U,(∀g∈b.2,Ok g)->∀g∈(u4 n gs b).2,Ok g:=by
 induction gs with
 | nil=>intro b h;exact h
 | cons g gs ih =>
  intro b h;apply ih (qa n b g)
  intro g' d';rcases jD.1 d' with c|c
  . exact h g' c
  . exact xc _ _ _ g' (by simpa using c)
lemma fs (n:Nat)(gs:U):∀b:List o1×U,(u4 n gs b).2.length<=b.2.length+gs.length:=by
 induction gs with
 | nil=>intro b;simp[u4]
 | cons g gs ih =>
  intro b;have h1:=ih (qa n b g);have h2:(qa n b g).2.length<=b.2.length+1:=by
   simp only[qa,kE]
   have:=y2 (qg g.op (n+b.2.length) (g.inputs.map fun i=>b.1.getD i (inl false))).1
   omega
  rw[k4,kD];omega
lemma zt (n k:Nat)(gs:U):∀b:List o1×U,(∀g∈gs,mc g)->k < b.1.length->(∃c,b.1.getD k (inl false)=inl c)->(∃g∈gs,k∈g.inputs)->(u4 n gs b).2.length+1<=b.2.length+gs.length:=by
 induction gs with
 | nil=>intro b _ _ _ h;obtain⟨g,e,_⟩:=h;simp at e
 | cons g gs ih =>
  intro b u j d s;rw[k4,kD]
  by_cases v:k∈g.inputs
  . obtain⟨c,d⟩:=d;have t:=u g jP;have x:(qg g.op (n+b.2.length) (g.inputs.map fun i=>b.1.getD i (inl false))).1=none:=by
     apply jh
     . exact t.1.1
     . simpa using t.1.2
     . intro h;simpa using t.2 h
     . exact⟨c,mM.2 ⟨k,v,d⟩⟩
    have y:(qa n b g).2.length=b.2.length:=by
     show (b.2++(qg g.op (n+b.2.length) (g.inputs.map fun i=>b.1.getD i (inl false))).1.toList).length=_
     rw[x];simp
    have:=fs n gs (qa n b g)
    omega
  . have s':∃g'∈gs,k∈g'.inputs:=by
     obtain⟨g',e',j'⟩:=s;rcases kC.1 e' with rfl|h
     . exact absurd j' v
     . exact⟨g',h,j'⟩
    have h1:=ih (qa n b g) (fun g' e' => u g' (hX _ e'))
     (by simp[qa];omega)
     (by
       obtain⟨c,d⟩:=d;refine⟨c,?_⟩
       simp only[qa];rw[q8 _ _ _ _ (by omega)];exact d)
     s'
    have y:(qa n b g).2.length<=b.2.length+1:=by
     simp only[qa,kE]
     have:=y2 (qg g.op (n+b.2.length) (g.inputs.map fun i=>b.1.getD i (inl false))).1
     omega
    omega
lemma km {m m' : Nat} (h:m<=m'):∀s:o1,qn m s->qn m' s
 | inl _,_=>trivial
 | inr _,hj=>lt_of_lt_of_le hj h
lemma jg (w t:I):∀s:o1,qn w.length s ->
  ze (w++t) s=ze w s
 | inl _,_=>rfl
 | inr _,hj=>List.getD_append _ _ _ _ hj
def tu (n:Nat)(y:I)(w:I)(b:List o1×U):Prop:=
 b.1.length=w.length/\∀i:Nat,
  qn (n+b.2.length) (b.1.getD i (inl false)) /\
  ze (q3 b.2 y) (b.1.getD i (inl false))=w.getD i false
lemma j7 (n:Nat)(y:I)(hy:y.length=n)(gs:U):∀(w:I)(b:List o1×U),(∀g∈gs,Ok g)->tu n y w b->tu n y (q3 gs w) (u4 n gs b):=by
 induction gs with
 | nil=>intro w b _ h;exact h
 | cons g gs ih =>
  intro w b j h;apply ih (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]) (qa n b g)
    (fun g' hg' => j g' (hX _ hg'))
  obtain⟨u,hi⟩:=h;set w':=q3 b.2 y with hw'
  have d':w'.length=n+b.2.length:=(by rw[hw',qu,hy]);set e:=g.inputs.map fun i=>b.1.getD i (inl false) with v
  have x:=j g jP;have c:=kn g.op x.1 w' e (by simpa[v] using x.2)
    (by
     intro s c;obtain⟨a,_,rfl⟩:=mM.1 c;rw[d'];exact (hi a).1)
  rw[d'] at c;set r:=qg g.op (n+b.2.length) e with hr
  have h0:e.map (ze w')=g.inputs.map fun i=>w.getD i false:=by
    rw[v,hW]
    apply jH
    intro a _;exact (hi a).2
  have h1:q3 (b.2++r.1.toList) y=q3 r.1.toList w':=(by rw[zd]);obtain⟨t,ht,_⟩:=y1 r.1.toList w';refine⟨by simp[qa,u],?_⟩
  intro i
  show qn (n+(b.2++r.1.toList).length) ((b.1++[r.2]).getD i (inl false)) /\
    ze (q3 (b.2++r.1.toList) y) ((b.1++[r.2]).getD i (inl false))=_
  rw[h1,kE,<- mG]
  by_cases z:i=b.1.length
  . subst z;rw[z0,u,z0]
    exact⟨c.1,by rw[c.2,h0]⟩
  . rw[q8 _ _ _ _ z,q8 _ _ _ _ (by omega)]
    refine⟨km (by omega) _ (hi i).1,?_⟩
    rw[ht,jg _ _ _ (by rw[d'];exact (hi i).1)]
    exact (hi i).2
lemma rn (n:Nat)(gs:U):∀b:List o1×U,(∀g∈gs,Ok g)->(∀i,qn (n+b.2.length) (b.1.getD i (inl false)))->yq n b.2->yq n (u4 n gs b).2:=by
 induction gs with
 | nil=>intro b _ _ e;exact e
 | cons g gs ih =>
  intro b j h e;have v:=ih (qa n b g) (fun g' x' => j g' (hX _ x'));apply v
  . intro i;set y:=g.inputs.map fun i=>b.1.getD i (inl false) with z
    have t:=j g jP;have d:=kn g.op t.1 (List.replicate (n+b.2.length) false) y
      (by simpa[z] using t.2)
      (by
       intro s d;obtain⟨a,_,rfl⟩:=mM.1 d;simpa using h a)
    simp only[List.length_replicate] at d
    show qn (n+(b.2++_).length) ((b.1++[_]).getD i (inl false))
    rw[kE,<- mG]
    by_cases u:i=b.1.length
    . subst u;rw[z0];exact d.1
    . rw[q8 _ _ _ _ u];exact km (by omega) _ (h i)
  . intro p g' c;simp only[qa] at c;by_cases h0:p < b.2.length
    . rw[mX h0] at c;exact e p g' c
    . rw[mY (by omega)] at c;set r:=qg g.op (n+b.2.length)
       (g.inputs.map fun i=>b.1.getD i (inl false)) with hr
      cases ho:r.1 with
      | none=>simp[ho] at c
      | some g0 =>
       rw[ho] at c;have h1:p - b.2.length=0:=by
        have:=(jJ.1 c).1
        simp at this;omega
       have h2:p=b.2.length:=(by omega);rw[h1] at c;simp at c;subst c;rw[h2]
       exact q80 g.op (n+b.2.length) _ (by
        intro s d;obtain⟨a,_,rfl⟩:=mM.1 d;exact h a) g0 (by rw[<- hr,ho];rfl)
def qd (n:Nat)(b:Q):List o1:=
 ofFn (fun i:Fin n=>inr (i:Nat))++[inl b]
lemma kp (n:Nat)(b:Q):(qd n b).getD n (inl false)=inl b:=
 z2 _ _ _ _ (by simp)
lemma iy (n:Nat)(b:Q)(y:F n):tu n (ofFn y) (ofFn y++[b]) (qd n b,[]):=by
 refine⟨by simp[qd],?_⟩
 intro i;have c:(ofFn (fun i:Fin n=>(inr (i:Nat):o1))).length=n:=by simp
 have d:(ofFn y).length=n:=by simp
 by_cases e:i=n
 . subst e;simp only[qd];rw[z2 _ _ _ _ c,z2 _ _ _ _ d]
   exact⟨trivial,rfl⟩
 . simp only[qd];rw[q8 _ _ _ _ (by omega),q8 _ _ _ _ (by omega)]
   by_cases g:i < n
   . simp[g,qn,ze,q3]
   . rw[mQ _ _ (by omega),mQ _ _ (by omega)]
     exact⟨trivial,rfl⟩
lemma js (n:Nat)(y:F n)(b:Q):ofFn (snoc y b:Fin (n+1)->Q)=ofFn y++[b]:=by
 rw[List.ofFn_succ']
 simp
lemma jr (n:Nat)(gs:U):∀L:List (Finset (Fin (n+1))),(∀g∈gs,n ∉ g.inputs)->(∀j:Nat,j≠n->last n ∉ L.getD j ∅)->∀j:Nat,j≠n->last n ∉ (zb gs L).getD j ∅:=by
 induction gs with
 | nil=>intro L _ h;exact h
 | cons g gs ih =>
  intro L b h;apply ih (L++[yb L g]) (fun g' d' => b g' (hX _ d'))
  intro j i;by_cases c:j=L.length
  . subst c;rw[z0]
    intro s;obtain⟨a,t,u⟩:=(kf L g _).1 s;exact h a (fun e=>b g jP (e ▸ t)) u
  . rw[q8 _ _ _ _ c];exact h j i
lemma q74 (m j:Nat)(h:j < m):(qr m).getD j ∅={⟨j,h⟩}:=by simp[qr,h]
lemma yi (n:Nat):∀j:Nat,j≠n->last n ∉ (qr (n+1)).getD j ∅:=by
 intro j c;by_cases b:j < n+1
 . have e:(qr (n+1)).getD j ∅={⟨j,b⟩}:=q74 (n+1) j b;rw[e,Finset.mem_singleton]
   intro e';exact c (by have:=congrArg Fin.val e';simpa using this.symm)
 . rw[mQ _ _ (by simp[qr];omega)];simp
lemma xu (n:Nat) (f:(Fin (n+1)->Q)->Q) (b:Q)(s:Nat) (h4:∃x:Fin (n+1)->Q,f (update x (last n) (!x (last n)))≠f x) (h5:∃y y':F n,f (snoc y b)≠f (snoc y' b)) (h:nV (n+1) f s):∃s',s'+1<=s/\nV n (fun y:F n=>f (snoc y b)) s':=by
 obtain⟨C,ok,h0,hev⟩:=h;have h0':C.gates.length<=s:=h0;set gs:=C.gates.map vg with h1
 have h2:∀g∈gs,mc g:=by intro g t;obtain⟨g0,h6,rfl⟩:=mM.1 t;exact q45 g0 (ok g0 h6)
 have u:∀x:Fin (n+1)->Q,(q3 gs (ofFn x)).getD C.output false=f x:=by intro x;rw[h1,jd,<- hev x];rfl
 set d:=u4 n gs (qd n b,[]) with h3
 have h7:∀y:F n,
   tu n (ofFn y) (q3 gs (ofFn (snoc y b:Fin (n+1)->Q))) d:=by
  intro y;rw[js]
  exact j7 n _ (by simp) gs _ _ (fun g t=>(h2 g t).1) (iy n b y)
 have v:∀y:F n,
   ze (q3 d.2 (ofFn y)) (d.1.getD C.output (inl false))
     = f (snoc y b):=by
  intro y;rw[((h7 y).2 C.output).2,u]
 cases i:d.1.getD C.output (inl false) with
 | inl c =>
  exfalso;obtain⟨y,y',h8⟩:=h5;apply h8
  rw[<- v y,<- v y',i];rfl
 | inr j =>
  have hlen:d.2.length+1<=s:=by
   by_cases z:∃g∈gs,n∈g.inputs
   . have:=zt n n gs (qd n b,[]) h2 (by simp[qd])
      ⟨b,z2 _ _ _ _ (by simp)⟩ z
     rw[<- h3] at this;have hl:gs.length=C.gates.length:=by simp[h1]
     simp only[pC,zero_add] at this;omega
   . exfalso
     push Not at z
     have h9:C.output≠n:=(by intro e;rw[e,h3,wy n n _ gs _ (by simp[qd])] at i;have hb:(qd n b).getD n (inl false)=inl b:=z2 _ _ _ _ (by simp);rw[show ((qd n b,([]:U))).1=qd n b from rfl,hb] at i;cases i);obtain⟨x,hx⟩:=h4;apply hx
     have x2:=jr n gs (qr (n+1)) z (yi n) C.output h9;have x3:=(k6 (update x (last n) (!x (last n))) x gs _ _ _ (j4 _ _)).2.2 C.output (by
       intro k hk
       have:k≠last n:=fun e=>x2 (e ▸ hk)
       simp[kV this])
     rw[<- u,<- u]
     exact x3
  refine⟨d.2.length,hlen,⟨d.2,j⟩,bq n gs _ (by simp),le_refl _,?_⟩
  intro y
  have:=v y
  rw[i] at this;exact this
lemma q79 (op:GateOp)(m:Nat)(g:List o1)(h:op=GateOp.and\/op=GateOp.or\/op=GateOp.not)(hlen:g.length<=2)(i:op=GateOp.not->g.length<=1)(b:Q)(j:op=GateOp.and->b=false)(s:op=GateOp.or->b=true)(hc:inl b∈g):∃c,(qg op m g).2=inl c:=by
 rcases h with rfl|rfl|rfl
 . have:=j rfl
   subst this;rcases g with _|⟨a,_|⟨d,_|⟨e,l⟩⟩⟩<;>(try cases a)<;>(try cases d) <;>
    simp_all [qg,ko]
 . have:=s rfl
   subst this;rcases g with _|⟨a,_|⟨d,_|⟨e,l⟩⟩⟩<;>(try cases a)<;>(try cases d) <;>
    simp_all [qg,ji]
 . have:=i rfl
   rcases g with _|⟨a,_|⟨d,l⟩⟩<;>(try cases a)<;>simp_all [qg,wr]
lemma vs (n:Nat)(b:List o1×U)(g:G)(d:mc g)(k:Nat)(e:k∈g.inputs)(c:Q) (j:b.1.getD k (inl false)=inl c):(qa n b g).2.length=b.2.length:=by
 have s:(qg g.op (n+b.2.length) (g.inputs.map fun i=>b.1.getD i (inl false))).1=none:=by
  apply jh
  . exact d.1.1
  . simpa using d.1.2
  . intro h;simpa using d.2 h
  . exact⟨c,mM.2 ⟨k,e,j⟩⟩
 show (b.2++(qg g.op (n+b.2.length) (g.inputs.map fun i=>b.1.getD i (inl false))).1.toList).length=_
 rw[s];simp
def wl (g:G):Q:=
 match g.op with
 | GateOp.or=>true
 | _=>false
lemma q90 (n:Nat)(b:List o1×U)(g:G)(d:mc g)(k:Nat)(j:k∈g.inputs) (s:b.1.getD k (inl false)=inl (wl g)):∃c,(qa n b g).1.getD b.1.length (inl false)=inl c:=by
 have e:(qa n b g).1.getD b.1.length (inl false)
    = (qg g.op (n+b.2.length) (g.inputs.map fun i=>b.1.getD i (inl false))).2:=z0 _ _ _
 rw[e]
 apply q79 _ _ _ d.1.1 (by simpa using d.1.2) (fun h=>by simpa using d.2 h)
   (wl g)
 . intro h;simp[wl,h]
 . intro h;simp[wl,h]
 . exact mM.2 ⟨k,j,s⟩
lemma q53 {n:Nat}(b c:U) (L:List (Finset (Fin n))):zb (b++c) L=zb c (zb b L):=by simp[zb,List.foldl_append]
lemma q54 {n:Nat}(gs:U):∀L:List (Finset (Fin n)),(zb gs L).length=L.length+gs.length:=by
 induction gs with
 | nil=>intro L;rfl
 | cons g gs ih =>
  intro L;have h:zb (g::gs) L=zb gs (L++[yb L g]):=rfl;rw[h,ih]
  simp only[kE,kD,pC];omega
lemma xn (n:Nat)(D:Nat->Prop)(gs:U):∀L:List (Finset (Fin (n+1))),(∀g∈gs,∀a∈g.inputs,¬D a)->(∀j:Nat,¬D j->last n ∉ L.getD j ∅)->∀j:Nat,¬D j->last n ∉ (zb gs L).getD j ∅:=by
 induction gs with
 | nil=>intro L _ h;exact h
 | cons g gs ih =>
  intro L b h;apply ih (L++[yb L g]) (fun g' d' => b g' (hX _ d'))
  intro j e;by_cases c:j=L.length
  . subst c;rw[z0]
    intro i;obtain⟨a,s,t⟩:=(kf L g _).1 i;exact h a (b g jP a s) t
  . rw[q8 _ _ _ _ c];exact h j e
lemma vw (n:Nat)(gs:U)(v:∀g∈gs,mc g)(o:Nat) (x:last n∈(zb gs (qr (n+1))).getD o ∅) (h6:∀b c,(u4 n gs (qd n b,[])).1.getD o (inl false)≠inl c):∃b,(u4 n gs (qd n b,[])).2.length+2<=gs.length:=by
 have h7:o≠n:=by
   intro e;apply h6 false false
   rw[e,wy n n _ gs _ (by simp[qd])]
   exact kp n false
 by_cases y:∃g∈gs,n∈g.inputs
 swap
 . exfalso
   push Not at y
   exact jr n gs (qr (n+1)) y (yi n) o h7 x
 obtain⟨g,s,h8⟩:=y;obtain⟨d,i,rfl⟩:=List.append_of_mem s;have h9:mc g:=v g s;have a2:∀g'∈d,mc g':=fun g' h=>v g' (List.mem_append_left _ h)
 have x2:∀g'∈i,mc g':=fun g' h=>v g' (List.mem_append_right _ (hX _ h))
 have u:∀b,u4 n (d++g::i) (qd n b,[])
     = u4 n i (qa n (u4 n d (qd n b,[])) g):=
   fun b=>by rw[jz,k4]
 have z:∀b,(u4 n d (qd n b,[])).1.getD n (inl false)=inl b:=by
   intro b;rw[wy n n _ d _ (by simp[qd])]
   exact kp n b
 have h0:∀b,(u4 n d (qd n b,[])).1.length=n+1+d.length:=by
   intro b;rw[nh]
   simp[qd]
 have x3:∀b,(u4 n d (qd n b,[])).2.length<=0+d.length:=fun b=>fs n d (qd n b,[])
 have h4:=fun b=>vs n (u4 n d (qd n b,[])) g h9 n h8 b (z b)
 have h5:∀b,(qa n (u4 n d (qd n b,[])) g).1.length
     = n+1+d.length+1:=by
   intro b;simp[qa,h0 b]
 have b0:∀b,(qa n (u4 n d (qd n b,[])) g).1.getD n (inl false)
     = inl b:=by
   intro b
   show ((u4 n d (qd n b,[])).1++[_]).getD n _=_
   rw[q8 _ _ _ _ (by rw[h0 b];omega)]
   exact z b
 have hF:=fun b=>fs n i (qa n (u4 n d (qd n b,[])) g)
 have hlen:(d++g::i).length=d.length+i.length+1:=by simp only[kE,kD];omega
 by_cases h1:∃g'∈d,n∈g'.inputs
 . refine⟨false,?_⟩
   have a1:(u4 n d (qd n false,[])).2.length+1<=0+d.length:=
     zt n n d (qd n false,[]) a2 (by simp[qd])
       ⟨false,kp n false⟩ h1
   have:=hF false
   have:=h4 false
   rw[u,hlen]
   omega
 by_cases h2:∃g'∈i,n∈g'.inputs
 . refine⟨false,?_⟩
   have a1:=zt n n i (qa n (u4 n d (qd n false,[])) g) x2
     (by rw[h5];omega) ⟨false,b0 false⟩ h2
   have:=x3 false
   have:=h4 false
   rw[u,hlen]
   omega
 obtain⟨c,hc⟩:=q90 n (u4 n d (qd n (wl g),[])) g h9 n h8
   (z (wl g))
 rw[h0 (wl g)] at hc;refine⟨wl g,?_⟩
 by_cases h3:∃g'∈i,(n+1+d.length)∈g'.inputs
 . have a1:=zt n (n+1+d.length) i
     (qa n (u4 n d (qd n (wl g),[])) g) x2
     (by rw[h5];omega) ⟨c,hc⟩ h3
   have:=x3 (wl g)
   have:=h4 (wl g)
   rw[u,hlen]
   omega
 . exfalso;have b1:o≠n+1+d.length:=by
     intro e;apply h6 (wl g) c
     rw[u,e,wy n _ _ i _ (by rw[h5];omega)]
     exact hc
   push Not at h1 h2 h3
   have hs:zb (d++g::i) (qr (n+1))
       = zb i (zb d (qr (n+1))++[yb (zb d (qr (n+1))) g]):=by
     rw[q53];rfl
   rw[hs] at x;have hL:=jr n d (qr (n+1)) h1 (yi n);have b3:(zb d (qr (n+1))).length=n+1+d.length:=by
     rw[q54]
     simp[qr]
   refine xn n (fun j=>j=n\/j=n+1+d.length) i _ ?_ ?_ o
     (by simp[h7,b1]) x
   . intro g' s' a ha hD;rcases hD with rfl|rfl
     . exact h2 g' s' ha
     . exact h3 g' s' ha
   . intro j t;have t':j≠n/\j≠n+1+d.length:=by
       constructor
       . exact fun e=>t (Or.inl e)
       . exact fun e=>t (Or.inr e)
     rw[q8 _ _ _ _ (by rw[b3];exact t'.2)]
     exact hL j t'.1
lemma xv (n:Nat) (f:(Fin (n+1)->Q)->Q) (s:Nat) (h2:∃x:Fin (n+1)->Q,f (update x (last n) (!x (last n)))≠f x) (h3:∀b:Q,∃y y':F n,f (snoc y b)≠f (snoc y' b)) (h:nV (n+1) f s):∃(b:Q) (s' : Nat),s'+2<=s/\nV n (fun y:F n=>f (snoc y b)) s':=by
 obtain⟨C,ok,v,hev⟩:=h;have v':C.gates.length<=s:=v;set gs:=C.gates.map vg with z
 have hl:gs.length=C.gates.length:=by simp[z]
 have h0:∀g∈gs,mc g:=by intro g i;obtain⟨g0,h4,rfl⟩:=mM.1 i;exact q45 g0 (ok g0 h4)
 have t:∀x:Fin (n+1)->Q,(q3 gs (ofFn x)).getD C.output false=f x:=by intro x;rw[z,jd,<- hev x];rfl
 have h5:∀(b:Q) (y:F n),
   tu n (ofFn y) (q3 gs (ofFn (snoc y b:Fin (n+1)->Q)))
    (u4 n gs (qd n b,[])):=by
  intro b y;rw[js]
  exact j7 n _ (by simp) gs _ _ (fun g i=>(h0 g i).1) (iy n b y)
 have u:∀(b:Q) (y:F n),
   ze (q3 (u4 n gs (qd n b,[])).2 (ofFn y))
    ((u4 n gs (qd n b,[])).1.getD C.output (inl false))=f (snoc y b):=by
  intro b y;rw[((h5 b y).2 C.output).2,t]
 have h1:∀b c,
   (u4 n gs (qd n b,[])).1.getD C.output (inl false)≠inl c:=by
  intro b c d;obtain⟨y,y',h6⟩:=h3 b;apply h6
  rw[<- u b y,<- u b y',d];rfl
 have h7:last n∈(zb gs (qr (n+1))).getD C.output ∅:=by
  by_contra h8;obtain⟨x,hx⟩:=h2;apply hx
  have h9:=(k6 (update x (last n) (!x (last n))) x gs _ _ _ (j4 _ _)).2.2 C.output (by
    intro k hk
    have:k≠last n:=fun e=>h8 (e ▸ hk)
    simp[kV this])
  rw[<- t,<- t]
  exact h9
 obtain⟨b,hb⟩:=vw n gs h0 C.output h7 h1;cases d:(u4 n gs (qd n b,[])).1.getD C.output (inl false) with
 | inl c=>exact absurd d (h1 b c)
 | inr j =>
  refine⟨b,(u4 n gs (qd n b,[])).2.length,by omega,⟨(u4 n gs (qd n b,[])).2,j⟩,bq n gs _ (by simp),le_refl _,?_⟩
  intro y
  have:=u b y
  rw[d] at this;exact this
def sb (n m:Nat) (π:Fin n->Fin m) (w:Nat):Nat:=
 if h:w < n then (π ⟨w,h⟩ : Nat) else w - n+m
def jt (n m:Nat) (π:Fin n->Fin m) (g:G):G:=
 ⟨g.op,g.inputs.map (sb n m π)⟩
def iv (n m:Nat) (π:Fin n->Fin m) (C:Circuit):Circuit:=
 ⟨C.gates.map (jt n m π),sb n m π C.output⟩
def mu (w:I)(g:G):I:=
 w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]
def ls (n m:Nat) (π:Fin n->Fin m) (W W':I):Prop:=
 n<=W.length/\W'.length+n=W.length+m /\
  ∀w:Nat,W'.getD (sb n m π w) false=W.getD w false
lemma qt (n m:Nat) (π:Fin n->Fin m) (W W':I) (g:G)(h:ls n m π W W'):ls n m π (mu W g) (mu W' (jt n m π g)):=by
 obtain⟨h1,h2,c⟩:=h;have d:(jt n m π g).op.eval
    ((jt n m π g).inputs.map fun i=>W'.getD i false)
    = g.op.eval (g.inputs.map fun i=>W.getD i false):=by
   simp only[jt,hW];congr 1
   apply jH
   intro a _;exact c a
 refine⟨by simp[mu];omega,by simp[mu];omega,?_⟩
 intro w;simp only[mu,d];rcases Nat.lt_trichotomy w W.length with b|b|b
 . have e:sb n m π w < W'.length:=by
    unfold sb
    split
    . have:=(π ⟨w,by assumption⟩).2;omega
    . omega
   rw[List.getD_append _ _ _ _ e,List.getD_append _ _ _ _ b]
   exact c w
 . have j:sb n m π w=W'.length:=by
    unfold sb
    split
    . omega
    . omega
   rw[j,b,z0,z0]
 . have hge:W'.length+1<=sb n m π w:=by
    unfold sb
    split
    . omega
    . omega
   rw[mQ _ _ (by simp;omega),mQ _ _ (by simp;omega)]
lemma qh (n m:Nat) (π:Fin n->Fin m) (gs:U):∀W W':I,ls n m π W W'->ls n m π (gs.foldl mu W) ((gs.map (jt n m π)).foldl mu W'):=by
 induction gs with
 | nil=>intro W W' h;exact h
 | cons g gs ih=>intro W W' h;exact ih _ _ (qt n m π W W' g h)
lemma qj (n m:Nat) (π:Fin n->Fin m) (x:F m):ls n m π (ofFn (x ∘ π)) (ofFn x):=by
 refine⟨by simp,by simp;omega,?_⟩
 intro w;unfold sb
 split
 . rename_i b
   rw[jL _ _ (by simp),jL _ _ (by simpa using b)]
   simp
 . rename_i b
   rw[mQ _ _ (by simp),mQ _ _ (by simp;omega)]
lemma yn {n m:Nat} (π:Fin n->Fin m) (h:(F n)->Q) (s:Nat)(c:nV n h s):nV m (fun x=>h (x ∘ π)) s:=by
 obtain⟨C,ok,d,hev⟩:=c;refine⟨iv n m π C,?_,?_,?_⟩
 . intro g e;obtain⟨g0,b,rfl⟩:=mM.1 e;exact⟨(ok g0 b).1,by simpa[jt] using (ok g0 b).2⟩
 . simpa[iv,Circuit.size] using d
 . intro x
   show _=h (x ∘ π)
   rw[<- hev (x ∘ π)]
   have:=(qh n m π C.gates _ _ (qj n m π x)).2.2 C.output
   exact this
lemma ks (n:Nat) (p:Fin (n+1)) (x:Fin (n+1)->Q) (b:Q):(snoc (fun j:Fin n=>x (Equiv.swap p (last n) j.castSucc)) b :Fin (n+1)->Q) ∘ (Equiv.swap p (last n))=update x p b:=by
 funext j;simp only[Function.comp_apply];by_cases c:j=p
 . subst c;rw[Equiv.swap_apply_left,Fin.snoc_last,kW]
 . have g:Equiv.swap p (last n) j≠last n:=by
    intro e;apply c
    have:=congrArg (Equiv.swap p (last n)) e
    rwa[Equiv.swap_apply_self,Equiv.swap_apply_right] at this
   obtain⟨t,d⟩:=Fin.exists_castSucc_eq.2 g;rw[<- d,Fin.snoc_castSucc,d,Equiv.swap_apply_self,kV c]
lemma q70 (n:Nat) (f:(Fin (n+1)->Q)->Q) (p:Fin (n+1)) (b:Q)(s:Nat) (c:∃x:Fin (n+1)->Q,f (update x p (!x p))≠f x) (d:∃x y:Fin (n+1)->Q,f (update x p b)≠f (update y p b)) (h:nV (n+1) f s):∃s' : Nat,s'+1<=s/\nV (n+1) (fun x=>f (update x p b)) s':=by
 set σ:Equiv.Perm (Fin (n+1)):=Equiv.swap p (last n) with hσ
 have g:nV (n+1) (fun x=>f (x ∘ σ)) s:=yn (⇑σ) f s h;have i:∀x:Fin (n+1)->Q,(x ∘ σ) ∘ σ=x:=by intro x;funext j;simp[hσ,Equiv.swap_apply_self]
 have t : σ.symm (last n)=p:=by rw[hσ,Equiv.symm_swap,Equiv.swap_apply_right]
 have c':∃x:Fin (n+1)->Q,
   (fun x=>f (x ∘ σ)) (update x (last n) (!x (last n)))
    ≠ (fun x=>f (x ∘ σ)) x:=by
  obtain⟨x0,u⟩:=c;refine⟨x0 ∘ σ,?_⟩
  simp only;rw[Function.update_comp_equiv,t,i]
  have:(x0 ∘ ⇑σ) (last n)=x0 p:=by simp[hσ,Equiv.swap_apply_right]
  rw[this];exact u
 have d':∃y y':F n,
   (fun x=>f (x ∘ σ)) (snoc y b)≠(fun x=>f (x ∘ σ)) (snoc y' b):=by
  obtain⟨x,y,v⟩:=d;refine⟨fun j=>x (σ j.castSucc),fun j=>y (σ j.castSucc),?_⟩
  simp only;rw[ks,ks]
  exact v
 obtain⟨s',z,h'⟩:=xu n _ b s c' d' g;refine⟨s',z,?_⟩
 have h'':=yn (fun j:Fin n => σ j.castSucc) _ s' h';have e:(fun x:Fin (n+1)->Q =>
   (fun y:F n=>(fun x=>f (x ∘ σ)) (snoc y b))
    (x ∘ fun j:Fin n => σ j.castSucc))
   = fun x=>f (update x p b):=by
  funext x;simp only;exact congrArg f (ks n p x b)
 rw[e] at h'';exact h''
lemma xk (n:Nat) (f:(Fin (n+1)->Q)->Q) (p:Fin (n+1)) (s:Nat) (c:∃x:Fin (n+1)->Q,f (update x p (!x p))≠f x) (d:∀b:Q,∃x y:Fin (n+1)->Q,f (update x p b)≠f (update y p b)) (h:nV (n+1) f s):∃(b:Q) (s' : Nat),s'+2<=s/\nV (n+1) (fun x=>f (update x p b)) s':=by
 set σ:Equiv.Perm (Fin (n+1)):=Equiv.swap p (last n) with hσ
 have g:nV (n+1) (fun x=>f (x ∘ σ)) s:=yn (⇑σ) f s h;have i:∀x:Fin (n+1)->Q,(x ∘ σ) ∘ σ=x:=by intro x;funext j;simp[hσ,Equiv.swap_apply_self]
 have t : σ.symm (last n)=p:=by rw[hσ,Equiv.symm_swap,Equiv.swap_apply_right]
 have c':∃x:Fin (n+1)->Q,
   (fun x=>f (x ∘ σ)) (update x (last n) (!x (last n)))
    ≠ (fun x=>f (x ∘ σ)) x:=by
  obtain⟨x0,u⟩:=c;refine⟨x0 ∘ σ,?_⟩
  simp only;rw[Function.update_comp_equiv,t,i]
  have:(x0 ∘ ⇑σ) (last n)=x0 p:=by simp[hσ,Equiv.swap_apply_right]
  rw[this];exact u
 have d':∀b:Q,∃y y':F n,
   (fun x=>f (x ∘ σ)) (snoc y b)≠(fun x=>f (x ∘ σ)) (snoc y' b):=by
  intro b;obtain⟨x,y,v⟩:=d b;refine⟨fun j=>x (σ j.castSucc),fun j=>y (σ j.castSucc),?_⟩
  simp only;rw[ks,ks]
  exact v
 obtain⟨b,s',z,h'⟩:=xv n _ s c' d' g;refine⟨b,s',z,?_⟩
 have h'':=yn (fun j:Fin n => σ j.castSucc) _ s' h';have e:(fun x:Fin (n+1)->Q =>
   (fun y:F n=>(fun x=>f (x ∘ σ)) (snoc y b))
    (x ∘ fun j:Fin n => σ j.castSucc))
   = fun x=>f (update x p b):=by
  funext x;simp only;exact congrArg f (ks n p x b)
 rw[e] at h'';exact h''
def e5 (gs:U)(n:Nat)(a:Nat):Z n:=
 fun x=>(q3 gs (ofFn x)).getD a false
lemma vx (gs:U)(n:Nat)(i:Fin n):e5 gs n i=fun x=>x i:=by
 funext x;unfold e5;rw[ve _ _ _ (by simp)]
 simp
lemma ra {α:Type} (gs:List α)(p:Nat)(g : α)(b:gs[p]?=some g):∃pre post,gs=pre++g::post/\pre.length=p:=by
 have c:p < gs.length:=(jJ.1 b).1;have d:gs[p]=g:=(jJ.1 b).2;refine⟨gs.take p,gs.drop (p+1),?_,by simp;omega⟩
 have e:gs=gs.take p++gs.drop p:=(List.take_append_drop p gs).symm;have h:gs.drop p=gs[p]::gs.drop (p+1):=List.drop_eq_getElem_cons c;exact e.trans (by rw[h,d])
lemma dn (n:Nat)(gs:U)(p:Nat)(g:G)(e:gs[p]?=some g)(h:∀a∈g.inputs,a < n+p)(x:F n):e5 gs n (n+p) x=g.op.eval (g.inputs.map fun a=>e5 gs n a x):=by
 obtain⟨b,c,rfl,hlen⟩:=ra gs p g e;unfold e5;have j:q3 (b++g::c) (ofFn x)=q3 c
   (q3 b (ofFn x)++[g.op.eval (g.inputs.map fun i=>(q3 b (ofFn x)).getD i false)]):=by
  rw[zd];rfl
 have d:(q3 b (ofFn x)).length=n+p:=by rw[qu];simp[hlen]
 rw[j,ve _ _ _ (by simp[d]),z2 _ _ _ _ d]
 congr 1
 apply jH
 intro a s;have hal:=h a s;have t:=ve c (q3 b (ofFn x)++[g.op.eval (g.inputs.map fun i=>(q3 b (ofFn x)).getD i false)]) a
    (by simp[d];omega)
 rw[t,List.getD_append _ _ _ _ (by omega)]
def vi (n:Nat):List o1:=ofFn fun i:Fin n=>inr (i:Nat)
lemma wj (n:Nat)(y:F n):tu n (ofFn y) (ofFn y) (vi n,[]):=by
 refine⟨by simp[vi],?_⟩
 intro i;by_cases b:i < n
 . simp[vi,b,qn,ze,q3]
 . rw[mQ _ _ (by simp[vi];omega),mQ _ _ (by simp;omega)]
   exact⟨trivial,rfl⟩
lemma q48 (n:Nat)(f:Z n)(s:Nat)(u:∃y y':F n,f y≠f y')(h:nV n f s):∃gs o,yq n gs/\gs.length<=s/\o < n+gs.length/\∀x,e5 gs n o x=f x:=by
 obtain⟨C,ok,v,hev⟩:=h;have v':C.gates.length<=s:=v;set b:=u4 n C.gates (vi n,[]) with h0
 have e:∀y:F n,tu n (ofFn y) (q3 C.gates (ofFn y)) b:=fun y=>j7 n _ (by simp) C.gates _ _ ok (wj n y)
 have hcl:yq n b.2:=by
  apply rn n C.gates (vi n,[]) ok
  . intro i;by_cases h3:i < n
    . simp[vi,h3,qn]
    . rw[mQ _ _ (by simp[vi];omega)];trivial
  . intro p g hp;simp at hp
 have hlen:b.2.length<=s:=by
  have:=fs n C.gates (vi n,[])
  rw[<- h0] at this;simp only[pC,zero_add] at this;omega
 cases t:b.1.getD C.output (inl false) with
 | inl c =>
  exfalso;obtain⟨y,y',h4⟩:=u;apply h4
  have d:=((e y).2 C.output).2;have z:=((e y').2 C.output).2;rw[t] at d z;have h1:(q3 C.gates (ofFn y)).getD C.output false=f y:=hev y;have h2:(q3 C.gates (ofFn y')).getD C.output false=f y':=hev y';rw[<- h1,<- h2,<- d,<- z];rfl
 | inr j =>
  have hj:j < n+b.2.length:=by
    obtain⟨y,_,_⟩:=u
    have:=((e y).2 C.output).1
    rw[t] at this;exact this
  refine⟨b.2,j,hcl,hlen,hj,?_⟩
  intro x;have d:=((e x).2 C.output).2;rw[t] at d;exact d.trans (hev x)
def qk {α:Type} (b:Q)(x : α)(c:List α):List α:=
 if b then x::c else c
def Run {α:Type} (inv : α->α)(meet join : α->α->α)(y : α)(t:Nat)(d:List α):Prop:=
 ∀P:Nat->List α->Prop,P 0 [y] ->
  (∀{s xs zs},List.Perm xs zs->P s xs->P s zs) ->
  (∀{s a r} (neg save:Q),P s ((if neg then inv a else a)::qk save a r) ->
   P (s+1) (a::r)) ->
  (∀{s a b r} (c ka kb:Q),
   P s ((if c then meet a b else join a b)::qk ka a (qk kb b r)) ->
   P (s+1) (a::b::r))->P t d
lemma Run.done {α inv meet join y}: @Run α inv meet join y 0 [y]:=fun _ d _ _ _=>d
lemma Run.perm {α inv meet join y s xs zs} (p:List.Perm xs zs)(h : @Run α inv meet join y s xs):Run inv meet join y s zs:=
 fun P d q u b=>q p (h P d q u b)
lemma Run.one {α inv meet join y s a r} (c e:Q) (h : @Run α inv meet join y s ((if c then inv a else a)::qk e a r)):Run inv meet join y (s+1) (a::r):=fun P d q u b=>u c e (h P d q u b)
lemma Run.two {α inv meet join y s a b r} (c e g:Q) (h : @Run α inv meet join y s ((if c then meet a b else join a b)::qk e a (qk g b r))):Run inv meet join y (s+1) (a::b::r):=fun P d q u v=>v c e g (h P d q u v)
lemma Run.fold {α inv meet join y} {P:∀t ws,@Run α inv meet join y t ws->Prop}(done:P 0 [y] Run.done) (perm:∀{s xs zs} (d:List.Perm xs zs)(h:Run inv meet join y s xs),P s xs h->P s zs (Run.perm d h)) (one:∀{s a r} (e g:Q) (h:Run inv meet join y s ((if e then inv a else a)::qk g a r)),P _ _ h->P _ _ (Run.one e g h)) (two:∀{s a b r} (c i j:Q) (h:Run inv meet join y s ((if c then meet a b else join a b)::qk i a (qk j b r))),P _ _ h->P _ _ (Run.two c i j h)) {t ws} (h:Run inv meet join y t ws):P t ws h:=by
 have u:=h (fun s xs => ∃h':Run inv meet join y s xs,P s xs h')
  ⟨Run.done,done⟩
  (fun d ⟨h',ih⟩ => ⟨Run.perm d h',perm d h' ih⟩)
  (fun n k ⟨h',ih⟩ => ⟨Run.one n k h',one n k h' ih⟩)
  (fun c a b ⟨h',ih⟩ => ⟨Run.two c a b h',two c a b h' ih⟩)
 exact u.elim fun _ d=>d
lemma wd {α β:Type} (e : α->β)(b:Q)(x : α)(c:List α):(qk b x c).map e=qk b (e x) (c.map e):=by cases b<;>simp[qk]
lemma wa {α:Type} (b:Q)(x a : α)(c:List α):a∈qk b x c↔(b=true/\a=x)\/a∈c:=by cases b<;>simp[qk]
lemma fq {α:Type} (b:Q)(x : α)(c:List α)(h:c.Nodup)(d:x ∉ c):(qk b x c).Nodup:=by
 cases b
 . simpa[qk] using h
 . simpa[qk] using And.intro d h
lemma Run.map {α β:Type} (e : α->β){inv : α->α}{meet join : α->α->α} {inv' : β->β} {meet' join' : β->β->β} (hi:∀a,e (inv a)=inv' (e a)) (g:∀a b,e (meet a b)=meet' (e a) (e b)) (i:∀a b,e (join a b)=join' (e a) (e b)) {y : α}{s:Nat}{d:List α}(h:Run inv meet join y s d):Run inv' meet' join' (e y) s (d.map e):=by
 induction h using Run.fold with
 | done=>exact Run.done
 | perm j _ ih=>exact Run.perm (j.map e) ih
 | @one s a rest neg save _ ih =>
  have c:((if neg then inv a else a)::qk save a rest).map e
    = (if neg then inv' (e a) else e a)::qk save (e a) (rest.map e):=by
   cases neg<;>simp[wd,hi]
  rw[c] at ih;exact Run.one neg save ih
 | @two s a b rest conj ka kb _ ih =>
  have c:((if conj then meet a b else join a b)::qk ka a (qk kb b rest)).map e
    = (if conj then meet' (e a) (e b) else join' (e a) (e b))
     :: qk ka (e a) (qk kb (e b) (rest.map e)):=by
   cases conj<;>simp[wd,g,i]
  rw[c] at ih;exact Run.two conj ka kb ih
def wn (n:Nat)(gs:U)(o a:Nat):Prop:=
 ∀P:Nat->Prop,P o ->
  (∀q g,gs[q]?=some g->P (n+q)->∀u∈g.inputs,P u)->P a
lemma pe (n:Nat)(gs:U)(o:Nat):wn n gs o o:=
 fun _ ho _=>ho
lemma ph {n:Nat}{gs:U}{o q u:Nat}{g:G}(b:gs[q]?=some g) (c:wn n gs o (n+q)) (d:u∈g.inputs):wn n gs o u:=
 fun P ho hs=>hs q g b (c P ho hs) u d
lemma q66 {n:Nat}{gs:U}{o a:Nat}(h:wn n gs o a):a=o\/∃q g,gs[q]?=some g/\a∈g.inputs/\wn n gs o (n+q):=by
 apply h (fun x=>x=o\/∃q g,gs[q]?=some g/\x∈g.inputs/\wn n gs o (n+q))
 . exact Or.inl rfl
 . intro q g b c u d;refine Or.inr ⟨q,g,b,d,?_⟩
   rcases c with rfl|⟨q',g',b',e',i'⟩
   . exact pe n gs (n+q)
   . exact ph b' i' e'
def a6 (n:Nat)(gs:U)(o p a:Nat):Prop:=
 a=o\/∃q,p<=q/\∃g,gs[q]?=some g/\a∈g.inputs/\wn n gs o (n+q)
open Classical in
noncomputable def u0 (gs:U)(n o p:Nat):M:=
 (range (n+p)).filter (fun a=>decide (a6 n gs o p a))
lemma qw (gs:U)(n o p a:Nat):a∈u0 gs n o p↔a < n+p/\a6 n gs o p a:=by simp[u0]
lemma vy (gs:U)(n o p:Nat):(u0 gs n o p).Nodup:=
 List.Nodup.filter _ List.nodup_range
abbrev hC {n:Nat}:u6 n->u6 n:=fun a x=>!a x
abbrev hE {n:Nat}:u6 n->u6 n->u6 n:=fun a b x=>a x&&b x
abbrev hG {n:Nat}:u6 n->u6 n->u6 n:=fun a b x=>a x||b x
lemma pb (n:Nat)(gs:U)(o:Nat)(hcl:yq n gs)(p:Nat)(g:G)(b:gs[p]?=some g) (i:wn n gs o (n+p)) (a:Nat):a∈u0 gs n o (p+1)↔a=n+p\/(a∈u0 gs n o p/\(a∈g.inputs->a6 n gs o (p+1) a)):=by
 rw[qw,qw]
 constructor
 . rintro ⟨j,e⟩
   by_cases s:a=n+p
   . exact Or.inl s
   . refine Or.inr ⟨⟨by omega,?_⟩,fun _=>e⟩
     rcases e with h|⟨q,t,g',b',c,d⟩
     . exact Or.inl h
     . exact Or.inr ⟨q,by omega,g',b',c,d⟩
 . rintro (rfl|⟨⟨j,e⟩,u⟩)
   . refine⟨by omega,?_⟩
     rcases q66 i with h|⟨q,g',b',c,d⟩
     . exact Or.inl h
     . refine Or.inr ⟨q,?_,g',b',c,d⟩
       have:=j2 (hcl q g' b') _ c
       omega
   . refine⟨by omega,?_⟩
     rcases e with h|⟨q,t,g',b',c,d⟩
     . exact Or.inl h
     . by_cases v:q=p
       . subst v;rw[b] at b';cases b'
         exact u c
       . exact Or.inr ⟨q,by omega,g',b',c,d⟩
def d9 {n:Nat} (A:List (Fin n)) (E:List (Fin n×Fin n)):Z n:=
 fun x=>A.any (fun a=>x a)||E.any (fun e=>x e.1&&x e.2)
def j9 {α:Type} [BEq α]:List α->List α->List α
 | [],acc=>acc.reverse
 | a::t,acc=>if acc.contains a then j9 t acc else j9 t (a::acc)
def rd {α:Type} [BEq α] (l:List α):List α:=j9 l []
lemma ww {α:Type} [DecidableEq α]:∀(l b:List α) (x : α),
  x∈j9 l b↔x∈l\/x∈b
 | [],b,x=>by simp[j9]
 | a::t,b,x=>by
  simp only[j9]
  by_cases h:b.contains a=true
  . simp only[h,↓reduceIte,ww,kC]
    have e:a∈b:=by simpa using h
    constructor
    . rintro (c|d)
      . exact Or.inl (Or.inr c)
      . exact Or.inr d
    . rintro ((rfl|c)|d)
      . exact Or.inr e
      . exact Or.inl c
      . exact Or.inr d
  . simp only[h,jV,↓reduceIte,ww,kC]
    tauto
lemma nm {α:Type} [DecidableEq α] (l:List α)(x : α):x∈rd l↔x∈l:=by simpa[rd] using ww l [] x
def tq {n:Nat} (A:List (Fin n)) (p:Fin n):List (Fin n):=
 A.filter (·!=p)
def i7 {n:Nat} (E:List (Fin n×Fin n)) (p:Fin n):List (Fin n×Fin n):=
 E.filter (fun e=>e.1!=p&&e.2!=p)
def rr {n:Nat} (E:List (Fin n×Fin n)) (p:Fin n):List (Fin n):=
 E.filterMap (fun e=>if e.1==p then some e.2 else if e.2==p then some e.1 else none)
def n6 {n:Nat} (A:List (Fin n)) (E:List (Fin n×Fin n)) (p:Fin n):List (Fin n):=
 rd (A++rr E p)
def tp {n:Nat} (A:List (Fin n)) (E:List (Fin n×Fin n)) (p:Fin n):List (Fin n×Fin n):=
 let A1:=n6 A E p
 E.filter (fun e=>e.1!=p&&e.2!=p&&!A1.contains e.1&&!A1.contains e.2)
def k1 {n:Nat} (A:List (Fin n)) (E:List (Fin n×Fin n)) (p:Fin n):Q:=
 A.contains p ||
  (E.all (fun e=>e.1!=e.2) &&
   E.any (fun e=>(e.1==p&&!A.contains e.2)||(e.2==p&&!A.contains e.1)))
def og {n k:Nat} (E:List (Fin n×Fin n)) (Eb:List (Fin k×Fin k)) (π:Fin n->Fin k):Q:=
 E.all (fun e=>Eb.any (fun e' => (π e.1==e'.1&&π e.2==e'.2)||(π e.1==e'.2&&π e.2==e'.1))) &&
 Eb.all (fun e' => E.any (fun e=>(π e.1==e'.1&&π e.2==e'.2)||(π e.1==e'.2&&π e.2==e'.1)))
lemma vq {n:Nat} (A:List (Fin n)) (b:A.Nodup):∀s:Nat,nV n (d9 A []) s->A.length - 1<=s:=by
 intro s h;have c:=xt n (d9 A []) A.toFinset (by
  intro i hi;have d:i∈A:=List.mem_toFinset.1 hi;refine⟨fun _=>false,?_⟩
  have e:d9 A [] (fun _=>false)=false:=(by simp[d9]);have g:d9 A [] (update (fun _=>false) i true)=true:=(by simp only[d9,List.any_nil,jS,kJ];exact⟨i,d,by simp⟩);simpa[e,g]) s h
 rw[List.toFinset_card_of_nodup b] at c;omega
lemma fp {n:Nat} (A:List (Fin n)) (E:List (Fin n×Fin n)) (h:(!A.isEmpty||!E.isEmpty)=true):∃x y:F n,d9 A E x≠d9 A E y:=by
 refine⟨fun _=>false,fun _=>true,?_⟩
 have b:d9 A E (fun _=>false)=false:=by simp[d9]
 have c:d9 A E (fun _=>true)=true:=by
  cases A with
  | cons a t=>simp[d9]
  | nil =>
   cases E with
   | nil=>simp at h
   | cons e t=>simp[d9]
 rw[b,c];decide
lemma rg {n:Nat} (A:List (Fin n)) (E:List (Fin n×Fin n)) (p:Fin n)(h:k1 A E p=true):∃x:F n,d9 A E (update x p (!x p))≠d9 A E x:=by
 simp only[k1,jX,jY,List.contains_eq_mem,decide_eq_true_eq,kH,kJ,bne_iff_ne,beq_iff_eq,kt,decide_eq_false_iff_not] at h;rcases h with z|⟨g,⟨e,j,⟨rfl,s⟩|⟨rfl,s⟩⟩⟩
 . refine⟨fun _=>false,?_⟩
   have c:d9 A E (fun _=>false)=false:=(by simp[d9]);have b:d9 A E (update (fun _=>false) p true)=true:=(by simp only[d9,jX,kJ];exact Or.inl ⟨p,z,by simp⟩);simpa[c,b]
 . have d:e.1≠e.2:=g e j;refine⟨fun i=>decide (i=e.2),?_⟩
   have c:d9 A E (fun i=>decide (i=e.2))=false:=by
    simp only[d9,nE,List.any_eq_false,decide_eq_true_eq,jY];refine⟨fun a t u=>s (u ▸ t),fun e' v' => ?_⟩
    intro ⟨b,y⟩
    exact g e' v' (b.trans y.symm)
   have b:d9 A E (update (fun i=>decide (i=e.2)) e.1 (!decide (e.1=e.2)))=true:=by
    simp only[d9,jX,kJ,jY];refine Or.inr ⟨e,j,?_,?_⟩
    . simp[d]
    . simp[kV (Ne.symm d)]
   rw[c,b];decide
 . have d:e.1≠e.2:=g e j;refine⟨fun i=>decide (i=e.1),?_⟩
   have c:d9 A E (fun i=>decide (i=e.1))=false:=by
    simp only[d9,nE,List.any_eq_false,decide_eq_true_eq,jY];refine⟨fun a t u=>s (u ▸ t),fun e' v' => ?_⟩
    intro ⟨b,y⟩
    exact g e' v' (b.trans y.symm)
   have b:d9 A E (update (fun i=>decide (i=e.1)) e.2 (!decide (e.2=e.1)))=true:=by
    simp only[d9,jX,kJ,jY];refine Or.inr ⟨e,j,?_,?_⟩
    . simp[kV d]
    . simp[Ne.symm d]
   rw[c,b];decide
lemma zo {n:Nat} (A:List (Fin n)) (E:List (Fin n×Fin n)) (p:Fin n):(fun x=>d9 A E (update x p false))=d9 (tq A p) (i7 E p):=by
 funext x;apply Bool.eq_iff_iff.2
 simp only[d9,tq,i7,jX,kJ,List.mem_filter,jY,bne_iff_ne];constructor
 . rintro (⟨a,j,i⟩|⟨e,s,b,c⟩)
   . by_cases d:a=p
     . subst d;simp at i
     . exact Or.inl ⟨a,⟨j,d⟩,by simpa[kV d] using i⟩
   . by_cases g:e.1=p
     . rw[g,kW] at b;cases b
     . by_cases h:e.2=p
       . rw[h,kW] at c;cases c
       . exact Or.inr ⟨e,⟨s,g,h⟩,
          by simpa[kV g] using b,
          by simpa[kV h] using c⟩
 . rintro (⟨a,⟨j,d⟩,i⟩|⟨e,⟨s,g,h⟩,b,c⟩)
   . exact Or.inl ⟨a,j,by simpa[kV d] using i⟩
   . exact Or.inr ⟨e,s,
       by simpa[kV g] using b,
       by simpa[kV h] using c⟩
lemma rm {n:Nat} (E:List (Fin n×Fin n)) (p q:Fin n):q∈rr E p↔∃e∈E,(e.1=p/\e.2=q)\/(e.1≠p/\e.2=p/\e.1=q):=by
 simp only[rr,List.mem_filterMap,beq_iff_eq];constructor
 . rintro ⟨e,c,h⟩
   split_ifs at h with b d
   . cases h;exact⟨e,c,Or.inl ⟨b,rfl⟩⟩
   . cases h;exact⟨e,c,Or.inr ⟨b,d,rfl⟩⟩
 . rintro ⟨e,c,⟨b,d⟩|⟨b,d,g⟩⟩
   . exact⟨e,c,by rw[if_pos b,d]⟩
   . exact⟨e,c,by rw[if_neg b,if_pos d,g]⟩
lemma kx {n:Nat} (A:List (Fin n)) (E:List (Fin n×Fin n)) (p:Fin n)(h3 : !A.contains p=true) (h4:E.all (fun e=>e.1!=e.2)=true):(fun x=>d9 A E (update x p true))=d9 (n6 A E p) (tp A E p):=by
 have y:p ∉ A:=by simpa[List.contains_eq_mem] using h3
 have z:∀e∈E,e.1≠e.2:=by simpa[kH,bne_iff_ne] using h4
 funext x;apply Bool.eq_iff_iff.2
 simp only[d9,tp,jX,kJ,jY,List.mem_filter,bne_iff_ne,kt,List.contains_eq_mem,decide_eq_false_iff_not];constructor
 . rintro (⟨a,i,j⟩|⟨e,b,g,s⟩)
   . have v:a≠p:=fun h=>y (h ▸ i)
     refine Or.inl ⟨a,?_,by simpa[kV v] using j⟩
     rw[n6,nm];exact List.mem_append_left _ i
   . by_cases d:e.1=p
     . have c:e.2≠p:=fun h=>z e b (d.trans h.symm)
       refine Or.inl ⟨e.2,?_,by simpa[kV c] using s⟩
       rw[n6,nm];exact List.mem_append_right _ ((rm E p e.2).2 ⟨e,b,Or.inl ⟨d,rfl⟩⟩)
     . by_cases c:e.2=p
       . refine Or.inl ⟨e.1,?_,by simpa[kV d] using g⟩
         rw[n6,nm];exact List.mem_append_right _ ((rm E p e.1).2 ⟨e,b,Or.inr ⟨d,c,rfl⟩⟩)
       . have t:x e.1=true:=(by simpa[kV d] using g);have u:x e.2=true:=(by simpa[kV c] using s);by_cases m1:e.1∈n6 A E p
         . exact Or.inl ⟨e.1,m1,t⟩
         . by_cases m2:e.2∈n6 A E p
           . exact Or.inl ⟨e.2,m2,u⟩
           . exact Or.inr ⟨e,⟨b,⟨⟨d,c⟩,m1⟩,m2⟩,t,u⟩
 . rintro (⟨a,i,j⟩|⟨e,⟨b,⟨⟨d,c⟩,_⟩,_⟩,t,u⟩)
   . rw[n6,nm,jD] at i;rcases i with h0|h5
     . have v:a≠p:=fun h=>y (h ▸ h0)
       exact Or.inl ⟨a,h0,by simpa[kV v] using j⟩
     . obtain⟨e,b,⟨g,rfl⟩|⟨g,s,rfl⟩⟩:=(rm E p a).1 h5
       . have c:e.2≠p:=fun h=>z e b (g.trans h.symm)
         exact Or.inr ⟨e,b,by simp[g],by simpa[kV c] using j⟩
       . exact Or.inr ⟨e,b,by simpa[kV g] using j,by simp[s]⟩
   . exact Or.inr ⟨e,b,
       by simpa[kV d] using t,
       by simpa[kV c] using u⟩
lemma px {n:Nat} (A:List (Fin (n+1))) (E:List (Fin (n+1)×Fin (n+1))) (p:Fin (n+1)) (A':List (Fin (n+1))) (E':List (Fin (n+1)×Fin (n+1))) (k:Nat)(d:k1 A E p=true)(e:A'=tq A p)(g:E'=i7 E p) (b:(!A'.isEmpty||!E'.isEmpty)=true) (i:∀s,nV (n+1) (d9 A' E') s->k<=s):∀s,nV (n+1) (d9 A E) s->k+1<=s:=by
 intro s h;have c:(fun x=>d9 A E (update x p false))=d9 A' E':=by rw[e,g];exact zo A E p
 have b':∃x y,d9 A E (update x p false)≠d9 A E (update y p false):=by obtain⟨x,y,j⟩:=fp A' E' b;exact⟨x,y,by simpa[congrFun c] using j⟩
 obtain⟨s',hs',h'⟩:=q70 n (d9 A E) p false s (rg A E p d) b' h;rw[c] at h'
 have:=i s' h'
 omega
lemma py {n:Nat} (A:List (Fin (n+1))) (E:List (Fin (n+1)×Fin (n+1))) (p:Fin (n+1)) (A':List (Fin (n+1))) (E':List (Fin (n+1)×Fin (n+1))) (k:Nat)(d:k1 A E p=true)(g : !A.contains p=true) (i:E.all (fun e=>e.1!=e.2)=true) (j:A'=n6 A E p)(t:E'=tp A E p) (b:(!A'.isEmpty||!E'.isEmpty)=true) (u:∀s,nV (n+1) (d9 A' E') s->k<=s):∀s,nV (n+1) (d9 A E) s->k+1<=s:=by
 intro s h;have c:(fun x=>d9 A E (update x p true))=d9 A' E':=by rw[j,t];exact kx A E p g i
 have b':∃x y,d9 A E (update x p true)≠d9 A E (update y p true):=by obtain⟨x,y,v⟩:=fp A' E' b;exact⟨x,y,by simpa[congrFun c] using v⟩
 obtain⟨s',hs',h'⟩:=q70 n (d9 A E) p true s (rg A E p d) b' h;rw[c] at h'
 have:=u s' h'
 omega
lemma wu {n:Nat} (A:List (Fin (n+1))) (E:List (Fin (n+1)×Fin (n+1))) (p:Fin (n+1)) (A0:List (Fin (n+1))) (E0:List (Fin (n+1)×Fin (n+1))) (A1:List (Fin (n+1))) (E1:List (Fin (n+1)×Fin (n+1))) (k:Nat)(i:k1 A E p=true)(j : !A.contains p=true) (t:E.all (fun e=>e.1!=e.2)=true) (u:A0=tq A p)(v:E0=i7 E p)(z:A1=n6 A E p)(h0:E1=tp A E p) (h1:(!A0.isEmpty||!E0.isEmpty)=true) (h2:(!A1.isEmpty||!E1.isEmpty)=true) (h3:∀s,nV (n+1) (d9 A0 E0) s->k<=s) (h4:∀s,nV (n+1) (d9 A1 E1) s->k<=s):∀s,nV (n+1) (d9 A E) s->k+2<=s:=by
 intro s h;have d:(fun x=>d9 A E (update x p false))=d9 A0 E0:=by rw[u,v];exact zo A E p
 have g:(fun x=>d9 A E (update x p true))=d9 A1 E1:=by rw[z,h0];exact kx A E p j t
 have h5:∀b:Q,∃x y,d9 A E (update x p b)≠d9 A E (update y p b):=by
  intro b;cases b with
  | false=>obtain⟨x,y,c⟩:=fp A0 E0 h1;exact⟨x,y,by simpa[congrFun d] using c⟩
  | true=>obtain⟨x,y,c⟩:=fp A1 E1 h2;exact⟨x,y,by simpa[congrFun g] using c⟩
 obtain⟨b,s',hs',h'⟩:=xk n (d9 A E) p s (rg A E p i) h5 h;cases b with
 | false=>rw[d] at h';have:=h3 s' h';omega
 | true=>rw[g] at h';have:=h4 s' h';omega
lemma pp {n k:Nat} (E:List (Fin n×Fin n)) (Eb:List (Fin k×Fin k)) (π:Fin n->Fin k) (h:og E Eb π=true):(fun y:F k=>d9 [] E (y ∘ π))=d9 [] Eb:=by
 simp only[og,jY,kH,kJ,jX,beq_iff_eq] at h;obtain⟨i,j⟩:=h;funext y;apply Bool.eq_iff_iff.2
 simp only[d9,List.any_nil,nK,kJ,jY,Function.comp_apply];constructor
 . rintro ⟨e,c,d,g⟩
   obtain⟨e',c',⟨a,b⟩|⟨a,b⟩⟩:=i e c
   . exact⟨e',c',a ▸ d,b ▸ g⟩
   . exact⟨e',c',b ▸ g,a ▸ d⟩
 . rintro ⟨e',c',d,g⟩
   obtain⟨e,c,⟨a,b⟩|⟨a,b⟩⟩:=j e' c'
   . exact⟨e,c,a.symm ▸ d,b.symm ▸ g⟩
   . exact⟨e,c,a.symm ▸ g,b.symm ▸ d⟩
lemma pv {n k e5:Nat} (E:List (Fin n×Fin n)) (Eb:List (Fin k×Fin k)) (π:Fin n->Fin k) (b:og E Eb π=true) (c:∀s:Nat,nV k (d9 [] Eb) s->e5<=s):∀s:Nat,nV n (d9 [] E) s->e5<=s:=by intro s h;have h':=yn π (d9 [] E) s h;rw[pp E Eb π b] at h';exact c s h'
lemma oy {α inv meet join y s xs} (h : @Run α inv meet join y s xs):xs.length<=s+1:=by
 induction h using Run.fold with
 | done=>simp
 | perm b _ ih=>rwa[<- b.length_eq]
 | one neg save h ih=>cases save<;>simp_all [qk]<;>omega
 | two conj ka kb h ih=>cases ka<;>cases kb<;>simp_all [qk]<;>omega
lemma us {m:Nat}{g:G}(h:cs m g):mc g:=by
 rcases h with ⟨c,j,_,d⟩|⟨c,j,k,_,_,d⟩
 . exact⟨⟨by simp[c],by simp[d]⟩,fun _=>by simp[d]⟩
 . refine⟨⟨?_,by simp[d]⟩,fun e => ?_⟩
   . rcases c with b|b<;>simp[b]
   . rcases c with b|b<;>rw[b] at e<;>cases e
lemma ja {n:Nat}{gs:U}(h:yq n gs):∀g∈gs,mc g:=by intro g b;obtain⟨p,c,rfl⟩:=List.getElem_of_mem b;exact us (h p gs[p] (jK c))
lemma wq {n:Nat}{gs:U}(h:yq n gs)(p:Nat):yq n (gs.take p):=by
 intro q g b;have c:q < (gs.take p).length:=(jJ.1 b).1;have d:q < p:=by simp at c;omega
 rw[List.getElem?_take_of_lt d] at b;exact h q g b
def fm (R:Nat->Prop)(n:Nat)(y:I)(w:I)(b:List o1×U):Prop:=
 b.1.length=w.length /\
 (∀i:Nat,qn (n+b.2.length) (b.1.getD i (inl false))) /\
 (∀i:Nat,R i->ze (q3 b.2 y) (b.1.getD i (inl false))=w.getD i false)
lemma vu (R:Nat->Prop)(n:Nat)(y:I)(hy:y.length=n)(gs:U):∀(w:I)(b:List o1×U),(∀g∈gs,Ok g)->(∀q g,gs[q]?=some g->R (b.1.length+q)->∀a∈g.inputs,R a)->fm R n y w b->fm R n y (q3 gs w) (u4 n gs b):=by
 induction gs with
 | nil=>intro w b _ _ h;exact h
 | cons g gs ih =>
  intro w b v x h;apply ih (w++[g.op.eval (g.inputs.map fun i=>w.getD i false)]) (qa n b g)
    (fun g' hg' => v g' (hX _ hg'))
  . intro q g' hq z a e;have hlen:(qa n b g).1.length=b.1.length+1:=by simp[qa]
    rw[hlen] at z;exact x (q+1) g' (by simpa using hq) (by simpa[mG,mF 1 q] using z) a e
  . obtain⟨hl,j,he⟩:=h;set w':=q3 b.2 y with hw'
    have u':w'.length=n+b.2.length:=(by rw[hw',qu,hy]);set h0:=g.inputs.map fun i=>b.1.getD i (inl false) with h1
    have h2:=v g jP;have c:=kn g.op h2.1 w' h0 (by simpa[h1] using h2.2)
      (by
        intro s c;obtain⟨a,_,rfl⟩:=mM.1 c;rw[u'];exact j a)
    rw[u'] at c;set r:=qg g.op (n+b.2.length) h0 with hr
    have h3:q3 (b.2++r.1.toList) y=q3 r.1.toList w':=(by rw[zd]);obtain⟨t,ht,_⟩:=y1 r.1.toList w';refine⟨by simp[qa,hl],?_,?_⟩
    . intro i
      show qn (n+(b.2++r.1.toList).length) ((b.1++[r.2]).getD i (inl false))
      rw[kE,<- mG]
      by_cases d:i=b.1.length
      . subst d;rw[z0];exact c.1
      . rw[q8 _ _ _ _ d];exact km (by omega) _ (j i)
    . intro i hi
      show ze (q3 (b.2++r.1.toList) y) ((b.1++[r.2]).getD i (inl false))=_
      rw[h3]
      by_cases d:i=b.1.length
      . subst d;rw[z0,hl,z0,c.2]
        congr 1
        rw[h1,hW]
        apply jH
        intro a e;exact he a (x 0 g rfl (by simpa using hi) a e)
      . rw[q8 _ _ _ _ d,q8 _ _ _ _ (by omega)]
        rw[ht,jg _ _ _ (by rw[u'];exact j i)]
        exact he i hi
lemma y7 (n:Nat)(f:Z n)(b d:U)(g:G)(o:Nat) (hcl:yq n (b++g::d)) (ho:o < n+(b++g::d).length) (hev:∀x,e5 (b++g::d) n o x=f x) (h9:∃y y':F n,f y≠f y')(st:o1) (b0:qn (n+b.length) st) (b1:(∀x,ze (q3 b (ofFn x)) st=e5 (b++g::d) n (n+b.length) x)\/¬wn n (b++g::d) o (n+b.length)):∃gs' o',yq n gs'/\gs'.length<=b.length+d.length/\o' < n+gs'.length/\∀x,e5 gs' n o' x=f x:=by
 set gs:=b++g::d with h2
 set p:=b.length with hp
 set h:List o1×U:=(vi (n+p)++[st],b) with t
 set s:=u4 n d h with b3
 have h3:∀g'∈d,Ok g':=fun g' hg' =>
  (ja hcl g' (List.mem_append_right _ (hX _ hg'))).1
 have c2:yq n b:=by
  have:b=gs.take p:=by simp[h2,hp]
  rw[this];exact wq hcl p
 have h4:∀i,qn (n+h.2.length) (h.1.getD i (inl false)):=by
  intro i;simp only[t,hp];by_cases h5:i=n+b.length
  . subst h5;rw[z2 _ _ _ _ (by simp[vi])];exact b0
  . rw[q8 _ _ _ _ (by simp[vi];omega)]
    by_cases u:i < n+b.length
    . simp[vi,u,qn]
    . rw[mQ _ _ (by simp[vi];omega)];trivial
 have hcl':yq n s.2:=rn n d h h3 h4 c2;have hlen':s.2.length<=b.length+d.length:=by simpa[b3,t] using fs n d h
 have h0:∀x:F n,
    qn (n+s.2.length) (s.1.getD o (inl false)) /\
    ze (q3 s.2 (ofFn x)) (s.1.getD o (inl false))=f x:=by
  intro x;have h6:q3 gs (ofFn x)=q3 d (q3 (b++[g]) (ofFn x)):=by
    have:gs=(b++[g])++d:=by simp[h2]
    rw[this,zd]
  have x2:(q3 (b++[g]) (ofFn x)).length=n+p+1:=(by rw[qu];simp[hp];omega);have x3:∀i < n+p,(q3 (b++[g]) (ofFn x)).getD i false =
      (q3 b (ofFn x)).getD i false:=by
    intro i hi;rw[zd,ve _ _ _ (by rw[qu];simp;omega)]
  rcases b1 with c3|d1
  . have h7:tu n (ofFn x) (q3 (b++[g]) (ofFn x)) h:=by
      refine⟨by simp[t,vi,x2],?_⟩
      intro i;refine⟨h4 i,?_⟩
      simp only[t];by_cases h5:i=n+p
      . subst h5;rw[z2 _ _ _ _ (by simp[vi])]
        have v:=c3 x;unfold e5 at v;rw[h6,ve _ _ _ (by omega)] at v;exact v
      . rw[q8 _ _ _ _ (by simp[vi];omega)]
        by_cases u:i < n+p
        . simp only[vi,List.getD_eq_getElem?_getD,List.getElem?_ofFn,u,↓reduceDIte,Option.getD_some,ze];exact (x3 i u).symm
        . rw[mQ _ _ (by simp[vi];omega),mQ _ _ (by omega)];rfl
    have z:=j7 n (ofFn x) (by simp) d _ h h3 h7;rw[<- h6] at z;have v:=z.2 o;exact⟨v.1,v.2.trans (hev x)⟩
  . have h7:fm (wn n gs o) n (ofFn x) (q3 (b++[g]) (ofFn x)) h:=by
      refine⟨by simp[t,vi,x2],h4,?_⟩
      intro i hi;simp only[t];have a1:i≠n+p:=fun e=>d1 (e ▸ hi)
      rw[q8 _ _ _ _ (by simp[vi];omega)]
      by_cases u:i < n+p
      . simp only[vi,List.getD_eq_getElem?_getD,List.getElem?_ofFn,u,↓reduceDIte,Option.getD_some,ze];exact (x3 i u).symm
      . rw[mQ _ _ (by simp[vi];omega),mQ _ _ (by omega)];rfl
    have hR:∀q g',d[q]?=some g'->wn n gs o (h.1.length+q)->∀a∈g'.inputs,wn n gs o a:=by
      intro q g' hq a2 a ha;have d2:gs[p+1+q]?=some g':=by
        have:gs=(b++[g])++d:=by simp[h2]
        rw[this,mY (by simp[hp])]
        simpa[hp,Nat.add_sub_cancel_left] using hq
      have e0:h.1.length=n+p+1:=(by simp[t,vi]);rw[e0] at a2;exact ph d2 (by simpa[mG] using a2) ha
    have z:=vu (wn n gs o) n (ofFn x) (by simp) d _ h h3 hR h7;rw[<- h6] at z;exact⟨z.2.1 o,(z.2.2 o (pe n gs o)).trans (hev x)⟩
 cases h8:s.1.getD o (inl false) with
 | inl c =>
  exfalso;obtain⟨y,y',a1⟩:=h9;apply a1
  have e1:=(h0 y).2;have e2:=(h0 y').2;rw[h8] at e1 e2;exact e1.symm.trans e2
 | inr j =>
  obtain⟨y,_,_⟩:=h9;have hj:=(h0 y).1;rw[h8] at hj;refine⟨s.2,j,hcl',hlen',hj,?_⟩
  intro x;have e:=(h0 x).2;rw[h8] at e;exact e
structure gY (n:Nat) (f:Z n) (gs:U) (o:Nat):Prop where
 gP:yq n gs
 ho:o < n+gs.length
 gQ:∀x,e5 gs n o x=f x
 gR:∀p < gs.length,wn n gs o (n+p)
 gS:∀p < gs.length,∀c:Q,e5 gs n (n+p)≠fun _=>c
 gT:∀p < gs.length,∀u < n+p,e5 gs n (n+p)≠e5 gs n u
open Classical in
lemma ng (n:Nat)(f:Z n)(s:Nat)(b:∃y y':F n,f y≠f y')(h:nV n f s):∃gs o,gY n f gs o/\gs.length<=s:=by
 have v:∃k,∃gs o,yq n gs/\gs.length=k/\o < n+gs.length/\∀x,e5 gs n o x=f x:=by obtain⟨gs,o,hcl,hlen,ho,hev⟩:=q48 n f s b h;exact⟨gs.length,gs,o,hcl,rfl,ho,hev⟩
 set k:=Nat.find v with hk
 obtain⟨gs,o,hcl,hlen,ho,hev⟩:=Nat.find_spec v;have hle:k<=s:=by obtain⟨sg,o0,h0,h1,ho0,h2⟩:=q48 n f s b h;exact le_trans (Nat.find_min' v ⟨sg,o0,h0,rfl,ho0,h2⟩) h1
 have z:∀gs' o',yq n gs'->o' < n+gs'.length->(∀x,e5 gs' n o' x=f x)->gs.length<=gs'.length:=by
   intro gs' o' hcl' ho' hev';rw[hlen]
   exact Nat.find_min' v ⟨gs',o',hcl',rfl,ho',hev'⟩
 refine⟨gs,o,⟨hcl,ho,hev,?_,?_,?_⟩,by omega⟩
 . intro p d;by_contra h3;obtain⟨g0,e⟩:∃g0,gs[p]?=some g0:=⟨gs[p],jK d⟩;obtain⟨g,i,j,t⟩:=ra gs p g0 e;subst t;subst j;obtain⟨gs',o',hcl',hlen',ho',hev'⟩:=y7 n f g i g0 o hcl ho hev b (inl false) trivial (Or.inr h3)
   have:=z gs' o' hcl' ho' hev'
   simp at this;omega
 . intro p d c h4;obtain⟨g0,e⟩:∃g0,gs[p]?=some g0:=⟨gs[p],jK d⟩;obtain⟨g,i,j,t⟩:=ra gs p g0 e;subst t;subst j;obtain⟨gs',o',hcl',hlen',ho',hev'⟩:=
    y7 n f g i g0 o hcl ho hev b (inl c) trivial
     (Or.inl fun x=>by rw[h4];rfl)
   have:=z gs' o' hcl' ho' hev'
   simp at this;omega
 . intro p d u hu h5;obtain⟨g0,e⟩:∃g0,gs[p]?=some g0:=⟨gs[p],jK d⟩;obtain⟨g,i,j,t⟩:=ra gs p g0 e;subst t;subst j;obtain⟨gs',o',hcl',hlen',ho',hev'⟩:=
    y7 n f g i g0 o hcl ho hev b (inr u) hu
     (Or.inl fun x=>by
      rw[h5];unfold e5;rw[zd,ve _ _ _ (by rw[qu];simp;omega)];rfl)
   have:=z gs' o' hcl' ho' hev'
   simp at this;omega
def wf (n:Nat)(v:Fin n):List o1:=
 ofFn fun i:Fin n=>if i=v then inl false else inr (i:Nat)
lemma jq (n:Nat)(v:Fin n)(x:F n):tu n (ofFn x) (ofFn (update x v false)) (wf n v,[]):=by
 refine⟨by simp[wf],?_⟩
 intro i;by_cases b:i < n
 . by_cases c:(⟨i,b⟩:Fin n)=v
   . subst c;simp[wf,b,qn,ze]
   . simp[wf,b,c,qn,ze,q3,kV c]
 . rw[mQ _ _ (by simp[wf];omega),mQ _ _ (by simp;omega)]
   exact⟨trivial,rfl⟩
lemma wz (n:Nat)(f:Z n)(gs:U)(o:Nat)(v:Fin n)(B:Nat)(hcl:yq n gs)(hev:∀x,e5 gs n o x=f x) (i:∃x y:F n,f (update x v false)≠f (update y v false)) (t:∀s',nV n (fun x=>f (update x v false)) s'->B<=s'):(∀c,(u4 n gs (wf n v,[])).1.getD o (inl false)≠inl c)/\B<=(u4 n gs (wf n v,[])).2.length:=by
 set b:=u4 n gs (wf n v,[]) with hacc
 have u:∀x,tu n (ofFn x) (q3 gs (ofFn (update x v false))) b:=fun x=>j7 n _ (by simp) gs _ _ (fun g z=>(ja hcl g z).1) (jq n v x)
 have d:∀x,ze (q3 b.2 (ofFn x)) (b.1.getD o (inl false))
   = f (update x v false):=fun x=>((u x).2 o).2.trans (hev _)
 have e:∀c,b.1.getD o (inl false)≠inl c:=by
  intro c hc;obtain⟨x,y,h0⟩:=i;apply h0
  rw[<- d x,<- d y,hc];rfl
 refine⟨e,?_⟩
 cases h:b.1.getD o (inl false) with
 | inl c=>exact absurd h (e c)
 | inr j =>
  apply t b.2.length
  refine⟨⟨b.2,j⟩,bq n gs _ (by simp),le_refl _,?_⟩
  intro x;have:=d x;rw[h] at this;exact this
lemma k3 (n u w:Nat)(gs:U):∀b:List o1×U,(∀g∈gs,mc g)->u < b.1.length->w < b.1.length->(∃cu,b.1.getD u (inl false)=inl cu)->(∃cw,b.1.getD w (inl false)=inl cw)->(∃g₁∈gs,u∈g₁.inputs)->(∃g₂∈gs,w∈g₂.inputs)->(∀g∈gs,¬(u∈g.inputs/\w∈g.inputs))->(u4 n gs b).2.length+2<=b.2.length+gs.length:=by
 induction gs with
 | nil=>intro b _ _ _ _ _ y _ _;obtain⟨g,c,_⟩:=y;simp at c
 | cons g gs ih =>
  intro b h5 s t d e v x h6;rw[k4,kD]
  have h7:mc g:=h5 g jP;have h4:∀g'∈gs,mc g':=fun g' c' => h5 g' (hX _ c')
  by_cases z:u∈g.inputs
  . have h3:w ∉ g.inputs:=fun h=>h6 g jP ⟨z,h⟩
    obtain⟨cu,d⟩:=d;have h0:=vs n b g h7 u z cu d;have x':∃g'∈gs,w∈g'.inputs:=by
      obtain⟨g',c',t'⟩:=x;rcases kC.1 c' with rfl|j
      . exact absurd t' h3
      . exact⟨g',j,t'⟩
    have y:=zt n w gs (qa n b g) h4 (by simp[qa];omega)
      (by obtain⟨cw,e⟩:=e;exact⟨cw,by simp only[qa];rw[q8 _ _ _ _ (by omega)];exact e⟩)
      x'
    omega
  . by_cases h3:w∈g.inputs
    . obtain⟨cw,e⟩:=e;have h0:=vs n b g h7 w h3 cw e;have v':∃g'∈gs,u∈g'.inputs:=by
        obtain⟨g',c',s'⟩:=v;rcases kC.1 c' with rfl|j
        . exact absurd s' z
        . exact⟨g',j,s'⟩
      have y:=zt n u gs (qa n b g) h4 (by simp[qa];omega)
        (by obtain⟨cu,d⟩:=d;exact⟨cu,by simp only[qa];rw[q8 _ _ _ _ (by omega)];exact d⟩)
        v'
      omega
    . have v':∃g'∈gs,u∈g'.inputs:=by
        obtain⟨g',c',s'⟩:=v;rcases kC.1 c' with rfl|j
        . exact absurd s' z
        . exact⟨g',j,s'⟩
      have x':∃g'∈gs,w∈g'.inputs:=by
        obtain⟨g',c',t'⟩:=x;rcases kC.1 c' with rfl|j
        . exact absurd t' h3
        . exact⟨g',j,t'⟩
      have y:=ih (qa n b g) h4 (by simp[qa];omega) (by simp[qa];omega)
        (by obtain⟨cu,d⟩:=d;exact⟨cu,by simp only[qa];rw[q8 _ _ _ _ (by omega)];exact d⟩)
        (by obtain⟨cw,e⟩:=e;exact⟨cw,by simp only[qa];rw[q8 _ _ _ _ (by omega)];exact e⟩)
        v' x' (fun g' c' => h6 g' (hX _ c'))
      have h2:(qa n b g).2.length<=b.2.length+1:=by
        simp only[qa,kE]
        have:=y2 (qg g.op (n+b.2.length) (g.inputs.map fun i=>b.1.getD i (inl false))).1
        omega
      omega
inductive gV {α:Type} (inv : α->α) (meet join : α->α->α) (zero one goal : α):
  Nat->List (α×Nat)->Prop where
 | done (tg:Nat):gV inv meet join zero one goal 0 [(goal,tg)]
 | perm {s xs zs}:List.Perm xs zs ->
   gV inv meet join zero one goal s xs ->
   gV inv meet join zero one goal s zs
 | uNot {s a ta r} (save:Q):
   ta≠1->ta≠2->(ta=3->save=false) ->
   inv a≠zero->inv a≠one->inv a≠a->(∀x∈r,x.1≠inv a) ->
   gV inv meet join zero one goal s
    ((inv a,if ta=3 then 2 else 0)::qk save (a,0) r) ->
   gV inv meet join zero one goal (s+1) ((a,ta)::r)
 | bOr {s a ta b tb r} (ka kb:Q):
   ta≠2->tb≠2->(ta=1->ka=false)->(tb=1->kb=false) ->
   join a b≠zero->join a b≠one ->
   join a b≠a->join a b≠b->(∀x∈r,x.1≠join a b) ->
   gV inv meet join zero one goal s
    ((join a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)) ->
   gV inv meet join zero one goal (s+1) ((a,ta)::(b,tb)::r)
 | bAnd {s a ta b tb r} (ka kb:Q):
   ta≠1->tb≠1->(ta≠0->ka=false)->(tb≠0->kb=false) ->
   meet a b≠zero->meet a b≠one ->
   meet a b≠a->meet a b≠b->(∀x∈r,x.1≠meet a b) ->
   gV inv meet join zero one goal s
    ((meet a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)) ->
   gV inv meet join zero one goal (s+1) ((a,ta)::(b,tb)::r)
lemma gV.toRun {α:Type} {inv : α->α}{meet join : α->α->α}{zero one c : α}{s:Nat}{d:List (α×Nat)}(h:gV inv meet join zero one c s d):Run inv meet join c s (d.map fst):=by
 induction h with
 | done _=>exact Run.done
 | perm g _ ih=>exact Run.perm (g.map fst) ih
 | @uNot s a ta r save _ _ _ _ _ _ _ _ ih =>
  have e:(((inv a,if ta=3 then 2 else 0)::qk save (a,0) r).map fst)
    = (if true then inv a else a)::qk save a (r.map fst):=by
   cases save<;>simp[qk]
  rw[e] at ih;exact Run.one true save ih
 | @bOr s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ ih =>
  have e:(((join a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).map fst)
    = (if false then meet a b else join a b)::qk ka a (qk kb b (r.map fst)):=by
   cases ka<;>cases kb<;>simp[qk]
  rw[e] at ih;exact Run.two false ka kb ih
 | @bAnd s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ ih =>
  have e:(((meet a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)).map fst)
    = (if true then meet a b else join a b)::qk ka a (qk kb b (r.map fst)):=by
   cases ka<;>cases kb<;>simp[qk]
  rw[e] at ih;exact Run.two true ka kb ih
lemma gV.len_le {α:Type} {inv : α->α}{meet join : α->α->α}{zero one c : α}{s:Nat}{b:List (α×Nat)}(h:gV inv meet join zero one c s b):b.length<=s+1:=by
 have:=oy h.toRun
 simpa using this
lemma gV.map {α β:Type} (e : α->β)(c:Injective e){inv : α->α}{meet join : α->α->α}{zero one i : α} {inv' : β->β} {meet' join' : β->β->β} {zero' one' i' : β} (h0:e zero=zero')(h1:e one=one')(hg:e i=i') (hi:∀a,e (inv a)=inv' (e a)) (d:∀a b,e (meet a b)=meet' (e a) (e b)) (g:∀a b,e (join a b)=join' (e a) (e b)) {s:Nat}{ws:List (α×Nat)}(h:gV inv meet join zero one i s ws):gV inv' meet' join' zero' one' i' s (ws.map fun p=>(e p.1,p.2)):=by
 induction h with
 | done tg=>rw[<- hg];exact gV.done tg
 | perm hp _ ih=>exact gV.perm (hp.map _) ih
 | @uNot s a ta r save j t u v z h2 h3 _ ih =>
  have e1:(((inv a,if ta=3 then 2 else 0)::qk save (a,0) r).map fun p=>(e p.1,p.2))
     = (inv' (e a),if ta=3 then 2 else 0)::qk save (e a,0) (r.map fun p=>(e p.1,p.2)):=by
    cases save<;>simp[qk,hi]
  rw[e1] at ih;refine gV.uNot save j t u ?_ ?_ ?_ ?_ ih
  . rw[<- hi,<- h0];exact fun h=>v (c h)
  . rw[<- hi,<- h1];exact fun h=>z (c h)
  . rw[<- hi];exact fun h=>h2 (c h)
  . intro x hx;obtain⟨y,hy,rfl⟩:=mM.1 hx;rw[<- hi];exact fun h=>h3 y hy (c h)
 | @bOr s a ta b tb r ka kb j t u h4 v z h2 h5 h3 _ ih =>
  have e1:(((join a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).map fun p=>(e p.1,p.2))
     = (join' (e a) (e b),0)::qk ka (e a,if ta=3 then 1 else 0) (qk kb (e b,if tb=3 then 1 else 0) (r.map fun p=>(e p.1,p.2))):=by
    cases ka<;>cases kb<;>simp[qk,g]
  rw[e1] at ih;refine gV.bOr ka kb j t u h4 ?_ ?_ ?_ ?_ ?_ ih
  . rw[<- g,<- h0];exact fun h=>v (c h)
  . rw[<- g,<- h1];exact fun h=>z (c h)
  . rw[<- g];exact fun h=>h2 (c h)
  . rw[<- g];exact fun h=>h5 (c h)
  . intro x hx;obtain⟨y,hy,rfl⟩:=mM.1 hx;rw[<- g];exact fun h=>h3 y hy (c h)
 | @bAnd s a ta b tb r ka kb j t u h4 v z h2 h5 h3 _ ih =>
  have e1:(((meet a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)).map fun p=>(e p.1,p.2))
     = (meet' (e a) (e b),if ta=3\/tb=3 then 1 else 0)::qk ka (e a,0) (qk kb (e b,0) (r.map fun p=>(e p.1,p.2))):=by
    cases ka<;>cases kb<;>simp[qk,d]
  rw[e1] at ih;refine gV.bAnd ka kb j t u h4 ?_ ?_ ?_ ?_ ?_ ih
  . rw[<- d,<- h0];exact fun h=>v (c h)
  . rw[<- d,<- h1];exact fun h=>z (c h)
  . rw[<- d];exact fun h=>h2 (c h)
  . rw[<- d];exact fun h=>h5 (c h)
  . intro x hx;obtain⟨y,hy,rfl⟩:=mM.1 hx;rw[<- d];exact fun h=>h3 y hy (c h)
def v3 (n:Nat)(gs:U)(v:Fin n)(p:Nat):List o1×U:=
 u4 n (gs.take p) (wf n v,[])
lemma vb (n:Nat)(gs:U)(v:Fin n)(p:Nat)(b:p<=gs.length):(v3 n gs v p).1.length=n+p:=by
 unfold v3;rw[nh]
 simp[wf,pB,jR b]
lemma rb (n:Nat)(gs:U)(v:Fin n)(p:Nat)(g:G)(b:gs[p]?=some g):v3 n gs v (p+1)=qa n (v3 n gs v p) g:=by
 unfold v3;have c:p < gs.length:=(jJ.1 b).1;have d:gs[p]=g:=(jJ.1 b).2;rw[List.take_succ_eq_append_getElem c,d,jz,k4]
 rfl
lemma zj (n:Nat)(gs:U)(v:Fin n)(p:Nat):u4 n (gs.drop p) (v3 n gs v p)=u4 n gs (wf n v,[]):=by unfold v3;rw[<- jz,List.take_append_drop]
def yf (n:Nat)(gs:U)(f:Z n)(p a tg:Nat):Prop:=
 match tg with
 | 0=>True
 | 1 => ∃v:Fin n,
  (∃x y,f (update x v false)≠f (update y v false)) /\
  (v3 n gs v p).1.getD a (inl false)=inl false /\
  (v3 n gs v p).2.length+(gs.drop p).length<=(u4 n (gs.drop p) (v3 n gs v p)).2.length+1
 | 2 => ∃v:Fin n,
  (∃x y,f (update x v false)≠f (update y v false)) /\
  (v3 n gs v p).1.getD a (inl false)=inl true /\
  (v3 n gs v p).2.length+(gs.drop p).length<=(u4 n (gs.drop p) (v3 n gs v p)).2.length+1
 | 3 => ∃v:Fin n,
  (∃x y,f (update x v false)≠f (update y v false)) /\
  (v3 n gs v p).1.getD a (inl false)=inl false /\
  (v3 n gs v p).2.length+(gs.drop p).length<=(u4 n (gs.drop p) (v3 n gs v p)).2.length+2
 | _=>False
lemma q12 {n:Nat}{gs:U}{f:Z n}{p a tg:Nat}(h:yf n gs f p a tg):tg<=3:=by
 match tg with
 | 0 | 1 | 2 | 3=>omega
 | _+4=>exact False.elim h
lemma vv {n:Nat}{gs:U}{f:Z n}{p a tg:Nat}{g:G}(j:gs[p]?=some g)(ha:a < n+p)(h:yf n gs f p a tg):yf n gs f (p+1) a tg:=by
 have u:p < gs.length:=(jJ.1 j).1;have x:gs[p]=g:=(jJ.1 j).2;have y:gs.drop p=g::gs.drop (p+1):=by rw[List.drop_eq_getElem_cons u,x]
 have s:∀v c B,
    (v3 n gs v p).1.getD a (inl false)=inl c ->
    (v3 n gs v p).2.length+(gs.drop p).length<=(u4 n (gs.drop p) (v3 n gs v p)).2.length+B ->
    (v3 n gs v (p+1)).1.getD a (inl false)=inl c /\
    (v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length <=
     (u4 n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B:=by
  intro v c B b d;have t:=rb n gs v p g j;have hfl:=vb n gs v p (by omega);constructor
  . rw[t];simp only[qa];rw[q8 _ _ _ _ (by omega)];exact b
  . have z:u4 n (gs.drop (p+1)) (v3 n gs v (p+1))=u4 n (gs.drop p) (v3 n gs v p):=(by rw[zj,zj]);have hlen2:(v3 n gs v (p+1)).2.length<=(v3 n gs v p).2.length+1:=by
     rw[t];simp only[qa,kE]
     have:=y2 (qg g.op (n+(v3 n gs v p).2.length) (g.inputs.map fun i=>(v3 n gs v p).1.getD i (inl false))).1
     omega
    have hdl:(gs.drop p).length=(gs.drop (p+1)).length+1:=(by rw[y];simp);rw[z];omega
 match tg with
 | 0=>trivial
 | 1=>obtain⟨v,e,b,d⟩:=h;exact⟨v,e,s v false 1 b d⟩
 | 2=>obtain⟨v,e,b,d⟩:=h;exact⟨v,e,s v true 1 b d⟩
 | 3=>obtain⟨v,e,b,d⟩:=h;exact⟨v,e,s v false 2 b d⟩
 | _+4=>exact False.elim h
lemma zr {n:Nat}{gs:U}{o p u:Nat}{f:Z n}{v:Fin n}{c:Q}(d:gY n f gs o)(j:p<=gs.length)(s:u∈u0 gs n o p) (t:∃x y,f (update x v false)≠f (update y v false)) (z:(v3 n gs v p).1.getD u (inl false)=inl c):∃g'∈gs.drop p,u∈g'.inputs:=by
 have⟨hlt,hl⟩:=(qw gs n o p u).1 s;rcases hl with rfl|⟨q,hq,g',b',h0,_⟩
 . exfalso;have hfl:=vb n gs v p j;have h1:(u4 n gs (wf n v,[])).1.getD u (inl false)=inl c:=by rw[<- zj n gs v p,wy n u _ _ _ (by omega)];exact z
   have e:∀x,tu n (ofFn x) (q3 gs (ofFn (update x v false))) (u4 n gs (wf n v,[])):=fun x=>j7 n _ (by simp) gs _ _ (fun g b=>(ja d.gP g b).1) (jq n v x)
   obtain⟨x,y,h2⟩:=t;apply h2
   have h:=((e x).2 u).2.trans (d.gQ _);have i:=((e y).2 u).2.trans (d.gQ _);rw[h1] at h i;exact h.symm.trans i
 . have hqlt:q < gs.length:=(jJ.1 b').1;have h3:gs[q]=g':=(jJ.1 b').2;refine⟨g',?_,h0⟩
   have:g'=(gs.drop p)[q - p]'(by simp;omega):=by rw[List.getElem_drop];simp[show p+(q - p)=q by omega,h3]
   rw[this]
   exact List.getElem_mem _
lemma q21 {n:Nat}{gs:U}{o p j:Nat}{f:Z n}(v:gY n f gs o)(hp:p < gs.length) (i:∀x,e5 gs n (n+p) x=!(e5 gs n j x)):∀g'∈gs.drop (p+1),¬(j∈g'.inputs/\(n+p)∈g'.inputs):=by
 intro g' hg' ⟨d,h⟩;obtain⟨r,hr,rfl⟩:=List.getElem_of_mem hg';have y:p+1+r < gs.length:=by simp at hr;omega
 have h5:(gs.drop (p+1))[r]=gs[p+1+r]:=List.getElem_drop;rw[h5] at d h;set q:=p+1+r with hq
 have h2:gs[q]?=some gs[q]:=jK y;have h3:=v.gP q gs[q] h2;have h4:=dn n gs q gs[q] h2 (j2 h3);have s:j≠n+p:=by intro e;have z:=i (fun _=>false);rw[e] at z;cases hv:e5 gs n (n+p) (fun _=>false)<;>rw[hv] at z<;>cases z
 rcases h3 with ⟨_,a,_,t⟩|⟨u,a,b,_,_,t⟩
 . rw[t] at d h;simp at d h;exact s (d.trans h.symm)
 . rw[t] at d h;simp at d h;rcases u with u|u
   . apply v.gS q y false
     funext x;rw[h4 x,u,t];simp only[kB,mS,GateOp.eval];rcases d with rfl|rfl<;>rcases h with c|c
     . exact absurd c.symm s
     . rw[<- c,i x];cases e5 gs n j x<;>rfl
     . rw[<- c,i x];cases e5 gs n j x<;>rfl
     . exact absurd c.symm s
   . apply v.gS q y true
     funext x;rw[h4 x,u,t];simp only[kB,mS,GateOp.eval];rcases d with rfl|rfl<;>rcases h with c|c
     . exact absurd c.symm s
     . rw[<- c,i x];cases e5 gs n j x<;>rfl
     . rw[<- c,i x];cases e5 gs n j x<;>rfl
     . exact absurd c.symm s
lemma q22 {n:Nat}{gs:U}{o p j k:Nat}{f:Z n}(u:gY n f gs o)(hp:p < gs.length)(hjlt:j < n+p) (s:∀x,e5 gs n (n+p) x=(e5 gs n j x&&e5 gs n k x)):∀g'∈gs.drop (p+1),¬(j∈g'.inputs/\(n+p)∈g'.inputs):=by
 intro g' hg' ⟨d,e⟩;obtain⟨r,hr,rfl⟩:=List.getElem_of_mem hg';have v:p+1+r < gs.length:=by simp at hr;omega
 have h2:(gs.drop (p+1))[r]=gs[p+1+r]:=List.getElem_drop;rw[h2] at d e;set q:=p+1+r with hq
 have y:gs[q]?=some gs[q]:=jK v;have z:=u.gP q gs[q] y;have h0:=dn n gs q gs[q] y (j2 z);have t:j≠n+p:=by omega
 rcases z with ⟨_,a,_,h⟩|⟨i,a,b,_,_,h⟩
 . rw[h] at d e;simp at d e;omega
 . rw[h] at d e;simp at d e;rcases i with i|i
   . apply u.gT q v (n+p) (by omega)
     funext x;rw[h0 x,i,h];simp only[kB,mS,GateOp.eval];rcases d with rfl|rfl<;>rcases e with c|c
     . exact absurd c.symm t
     . rw[<- c,s x];cases e5 gs n j x<;>cases e5 gs n k x<;>rfl
     . rw[<- c,s x];cases e5 gs n j x<;>cases e5 gs n k x<;>rfl
     . exact absurd c.symm t
   . apply u.gT q v j (by omega)
     funext x;rw[h0 x,i,h];simp only[kB,mS,GateOp.eval];rcases d with rfl|rfl<;>rcases e with c|c
     . exact absurd c.symm t
     . rw[<- c,s x];cases e5 gs n j x<;>cases e5 gs n k x<;>rfl
     . rw[<- c,s x];cases e5 gs n j x<;>cases e5 gs n k x<;>rfl
     . exact absurd c.symm t
lemma it {n:Nat}{gs:U}(hcl:yq n gs)(p:Nat):∀g∈gs.drop p,mc g:=fun g hg=>ja hcl g (List.mem_of_mem_drop hg)
open Classical in
lemma kc (n:Nat)(f:Z n)(gs:U)(o:Nat)(hm:gY n f gs o):∀d p,p+d=gs.length->∀tg:Nat->Nat,(∀a∈u0 gs n o p,yf n gs f p a (tg a))->gV (hC (n:=n)) hE hG (fun _=>false) (fun _=>true) f d ((u0 gs n o p).map fun a=>(e5 gs n a,tg a)):=by
 intro d;induction d with
 | zero =>
  intro p hp tg _;have aP:[o].Perm (u0 gs n o p):=by
   refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (vy _ _ _ _)).2 ?_
   intro a;rw[qw,List.mem_singleton]
   constructor
   . rintro rfl;exact⟨by have:=hm.ho;omega,Or.inl rfl⟩
   . rintro ⟨_,h|⟨q,hq,g',hg',_,_⟩⟩
     . exact h
     . have:=(jJ.1 hg').1;omega
  have hf:e5 gs n o=f:=funext hm.gQ;have t:([(f,tg o)]).Perm ((u0 gs n o p).map fun a=>(e5 gs n a,tg a)):=(by rw[<- hf];exact aP.map (fun a=>(e5 gs n a,tg a)));exact gV.perm t (gV.done (tg o))
 | succ d ih =>
  intro p hp tg h6;have b0:p < gs.length:=by omega
  obtain⟨g,hg⟩:∃g,gs[p]?=some g:=⟨gs[p],jK b0⟩;have hr:wn n gs o (n+p):=hm.gR p b0;have b1:=pb n gs o hm.gP p g hg hr;have t1:∀a∈g.inputs,a∈u0 gs n o p:=fun a ha =>
   (qw _ _ _ _ _).2 ⟨j2 (hm.gP p g hg) a ha,Or.inr ⟨p,le_rfl,g,hg,ha,hr⟩⟩
  have b3:∀a∈u0 gs n o p,a≠n+p:=fun a ha =>
   Nat.ne_of_lt ((qw _ _ _ _ _).1 ha).1
  have j1:=dn n gs p g hg (j2 (hm.gP p g hg));have e2:=vy gs n o p;have v2:gs.drop p=g::gs.drop (p+1):=(by rw[List.drop_eq_getElem_cons b0];have aQ:gs[p]=g:=(jJ.1 hg).2;rw[aQ]);have w0:mc g:=us (hm.gP p g hg);have hb:=it hm.gP (p+1);have aA:e5 gs n (n+p)≠fun _=>false:=hm.gS p b0 false
  have aB:e5 gs n (n+p)≠fun _=>true:=hm.gS p b0 true
  have c2:∀a∈u0 gs n o p,e5 gs n a≠e5 gs n (n+p):=fun a ha e =>
   hm.gT p b0 a ((qw _ _ _ _ _).1 ha).1 e.symm
  rcases hm.gP p g hg with ⟨x2,j,hj,h5⟩|⟨x2,j,k,hj,hk,h5⟩
  .
   have h7:j∈u0 gs n o p:=t1 j (by simp[h5]);have h8:e5 gs n (n+p)=hC (e5 gs n j):=(by funext x;rw[j1 x,x2,h5];simp[GateOp.eval]);have m2:∀v c B,
       (∃x y,f (update x v false)≠f (update y v false)) ->
       (v3 n gs v p).1.getD j (inl false)=inl c ->
       (v3 n gs v p).2.length+(gs.drop p).length<=(u4 n (gs.drop p) (v3 n gs v p)).2.length+B ->
       2<=B /\
       (v3 n gs v (p+1)).1.getD (n+p) (inl false)=inl (!c) /\
       (v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
         (u4 n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B /\
       (a6 n gs o (p+1) j->3<=B):=by
     intro v c B i s z;have a1:=rb n gs v p g hg;have ht:=vb n gs v p (by omega);have aJ:=vb n gs v (p+1) (by omega);have h0:(v3 n gs v (p+1)).2.length=(v3 n gs v p).2.length:=by rw[a1];exact vs n _ g w0 j (by simp[h5]) c s
     have he:(v3 n gs v (p+1)).1.getD (n+p) (inl false)=inl (!c):=by
       rw[a1];simp only[qa];rw[z2 _ _ _ _ ht,x2,h5]
       simp only[kB,mS,s,qg,wr]
     have hv:u4 n (gs.drop (p+1)) (v3 n gs v (p+1))=u4 n (gs.drop p) (v3 n gs v p):=(by rw[zj,zj]);have aK:(gs.drop p).length=(gs.drop (p+1)).length+1:=(by rw[v2];simp);have hn:(v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
         (u4 n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B:=by
       rw[hv,h0];omega
     have hy:n+p∈u0 gs n o (p+1):=(b1 (n+p)).2 (Or.inl rfl);have hc:=zr hm (by omega) hy i he;have m3:=zt n (n+p) (gs.drop (p+1)) (v3 n gs v (p+1)) hb
       (by omega) ⟨!c,he⟩ hc
     refine⟨by omega,he,hn,?_⟩
     intro c3;have aS:j∈u0 gs n o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,c3⟩;have aL:(v3 n gs v (p+1)).1.getD j (inl false)=inl c:=by rw[a1];simp only[qa];rw[q8 _ _ _ _ (by omega)];exact s
     have aT:=zr hm (by omega) aS i aL;have aC:=q21 hm b0 (fun x=>congrFun h8 x);have aU:=k3 n j (n+p) (gs.drop (p+1)) (v3 n gs v (p+1))
       hb (by omega) (by omega) ⟨c,aL⟩ ⟨!c,he⟩ aT hc aC
     omega
   have aV:tg j≠1:=by
     intro t;have b:=h6 j h7;rw[t] at b;obtain⟨v,i,s,z⟩:=b
     have:=(m2 v false 1 i s z).1;omega
   have aW:tg j≠2:=by
     intro h2;have b:=h6 j h7;rw[h2] at b;obtain⟨v,i,s,z⟩:=b
     have:=(m2 v true 1 i s z).1;omega
   have aX:tg j=3->decide (a6 n gs o (p+1) j)=false:=by
     intro h3;simp only[decide_eq_false_iff_not];intro c3;have b:=h6 j h7;rw[h3] at b;obtain⟨v,i,s,z⟩:=b
     have:=(m2 v false 2 i s z).2.2.2 c3;omega
   set tg' : Nat->Nat:=fun a =>
     if a=n+p then (if tg j=3 then 2 else 0)
     else if a=j then 0
     else tg a
   have h6':∀a∈u0 gs n o (p+1),yf n gs f (p+1) a (tg' a):=by
     intro a ha;simp only[tg'];by_cases a2:a=n+p
     . subst a2;simp only[↓reduceIte];by_cases h3:tg j=3
       . simp only[h3,↓reduceIte];have b:=h6 j h7;rw[h3] at b;obtain⟨v,i,s,z⟩:=b;obtain⟨_,he,hn,_⟩:=m2 v false 2 i s z;exact⟨v,i,he,by omega⟩
       . simp only[h3,↓reduceIte];trivial
     . simp only[a2,↓reduceIte];by_cases h9:a=j
       . simp only[h9,↓reduceIte];trivial
       . simp only[h9,↓reduceIte];have d1:a∈u0 gs n o p:=by
           rcases (b1 a).1 ha with rfl|⟨t,_⟩
           . exact absurd rfl a2
           . exact t
         exact vv hg ((qw _ _ _ _ _).1 d1).1 (h6 a d1)
   have IH:=ih (p+1) (by omega) tg' h6';have p0:(u0 gs n o p).Perm (j::(u0 gs n o p).erase j):=List.perm_cons_erase h7;have p1:((u0 gs n o p).erase j).Nodup:=e2.erase j;have r2:(u0 gs n o (p+1)).Perm
       ((n+p)::qk (decide (a6 n gs o (p+1) j)) j ((u0 gs n o p).erase j)):=by
     refine (List.perm_ext_iff_of_nodup (vy _ _ _ _) ?_).2 ?_
     . refine List.nodup_cons.2 ⟨?_,fq _ _ _ p1 (by simp[e2.mem_erase_iff])⟩
       rw[wa];rintro (⟨_,h⟩|h)
       . exact b3 j h7 h.symm
       . exact b3 _ (List.mem_of_mem_erase h) rfl
     . intro a;rw[b1 a,kC,wa,e2.mem_erase_iff,h5,List.mem_singleton]
       simp only[decide_eq_true_eq];constructor
       . rintro (h|⟨t,h2⟩)
         . exact Or.inl h
         . by_cases h9:a=j
           . exact Or.inr (Or.inl ⟨h9 ▸ h2 h9,h9⟩)
           . exact Or.inr (Or.inr ⟨h9,t⟩)
       . rintro (h|⟨t,rfl⟩|⟨t,h2⟩)
         . exact Or.inl h
         . exact Or.inr ⟨h7,fun _=>t⟩
         . exact Or.inr ⟨h2,fun h=>absurd h t⟩
   have hz:((u0 gs n o p).erase j).map (fun a=>(e5 gs n a,tg' a)) =
       ((u0 gs n o p).erase j).map (fun a=>(e5 gs n a,tg a)):=by
     apply jH
     intro a ha;have t:a≠j:=(e2.mem_erase_iff.1 ha).1;have h2:a≠n+p:=b3 a (List.mem_of_mem_erase ha);simp[tg',t,h2]
   have xi:(qk (decide (a6 n gs o (p+1) j)) j ((u0 gs n o p).erase j)).map (fun a=>(e5 gs n a,tg' a)) =
       qk (decide (a6 n gs o (p+1) j)) (e5 gs n j,0) (((u0 gs n o p).erase j).map fun a=>(e5 gs n a,tg a)):=by
     rw[wd,hz]
     have xs:j≠n+p:=(by omega);simp[tg',xs]
   have IH':=gV.perm (r2.map fun a=>(e5 gs n a,tg' a)) IH;rw[kB,xi,h8] at IH';have f2:tg' (n+p)=(if tg j=3 then 2 else 0):=(by simp[tg']);rw[f2] at IH';refine gV.perm (p0.map fun a=>(e5 gs n a,tg a)).symm ?_
   refine gV.uNot (decide (a6 n gs o (p+1) j)) aV aW aX
     (h8 ▸ aA) (h8 ▸ aB) (fun e=>c2 j h7 (h8 ▸ e.symm)) ?_ IH'
   intro x hx;obtain⟨a,ha,rfl⟩:=mM.1 hx;exact h8 ▸ c2 a (List.mem_of_mem_erase ha)
  .
   have aD:j≠k:=by
     intro e;subst e;apply hm.gT p b0 j hj
     funext x;rw[j1 x,h5]
     rcases x2 with x2|x2<;>rw[x2]<;>simp[GateOp.eval]
   have h7:=t1 j (by simp[h5]);have x3:=t1 k (by simp[h5]);have aY:k∈(u0 gs n o p).erase j:=(e2.mem_erase_iff).2 ⟨fun e=>aD e.symm,x3⟩;have p1:((u0 gs n o p).erase j).Nodup:=e2.erase j;have aZ:(((u0 gs n o p).erase j).erase k).Nodup:=p1.erase k;have p0:(u0 gs n o p).Perm (j::k::((u0 gs n o p).erase j).erase k):=(List.perm_cons_erase h7).trans ((List.perm_cons_erase aY).cons j);have d2:∀a,a∈((u0 gs n o p).erase j).erase k↔a≠k/\a≠j/\a∈u0 gs n o p:=(by intro a;rw[p1.mem_erase_iff,e2.mem_erase_iff]);have r2:(u0 gs n o (p+1)).Perm
       ((n+p)::qk (decide (a6 n gs o (p+1) j)) j (qk (decide (a6 n gs o (p+1) k)) k (((u0 gs n o p).erase j).erase k))):=by
     refine (List.perm_ext_iff_of_nodup (vy _ _ _ _) ?_).2 ?_
     . refine List.nodup_cons.2 ⟨?_,fq _ _ _ (fq _ _ _ aZ ?_) ?_⟩
       . rw[wa,wa]
         rintro (⟨_,h⟩|⟨_,h⟩|h)
         . exact b3 j h7 h.symm
         . exact b3 k x3 h.symm
         . exact b3 _ ((d2 _).1 h).2.2 rfl
       . rw[d2];simp
       . rw[wa,d2]
         rintro (⟨_,h⟩|h)
         . exact aD h
         . exact h.2.1 rfl
     . intro a;rw[b1 a,kC,wa,wa,d2 a]
       simp only[decide_eq_true_eq,h5,kC,jC,or_false];constructor
       . rintro (h|⟨t,h2⟩)
         . exact Or.inl h
         . by_cases h9:a=j
           . exact Or.inr (Or.inl ⟨h9 ▸ h2 (Or.inl h9),h9⟩)
           . by_cases hd:a=k
             . exact Or.inr (Or.inr (Or.inl ⟨hd ▸ h2 (Or.inr hd),hd⟩))
             . exact Or.inr (Or.inr (Or.inr ⟨hd,h9,t⟩))
       . rintro (h|⟨t,rfl⟩|⟨t,rfl⟩|⟨t,h2,h3⟩)
         . exact Or.inl h
         . exact Or.inr ⟨h7,fun _=>t⟩
         . exact Or.inr ⟨x3,fun _=>t⟩
         . exact Or.inr ⟨h3,fun h=>by rcases h with h|h<;>contradiction⟩
   rcases x2 with x2|x2
   .
     have h8:e5 gs n (n+p)=hE (e5 gs n j) (e5 gs n k):=(by funext x;rw[j1 x,x2,h5];simp[GateOp.eval]);have e0:∀(u w_other:Nat) (hu:u∈g.inputs) (r3:u < n+p)
         (hval_u:∀x,e5 gs n (n+p) x=(e5 gs n u x&&e5 gs n w_other x))
         (v:Fin n) (c:Q) (B:Nat),
         (∃x y,f (update x v false)≠f (update y v false)) ->
         (v3 n gs v p).1.getD u (inl false)=inl c ->
         (v3 n gs v p).2.length+(gs.drop p).length<=(u4 n (gs.drop p) (v3 n gs v p)).2.length+B ->
         (v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
           (u4 n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B /\
         (c=false->2<=B/\(v3 n gs v (p+1)).1.getD (n+p) (inl false)=inl false/\(a6 n gs o (p+1) u->3<=B)) /\
         (c=true->a6 n gs o (p+1) u->2<=B):=by
       intro u wo hu r3 bA v c B i s z;have a1:=rb n gs v p g hg;have ht:=vb n gs v p (by omega);have aJ:=vb n gs v (p+1) (by omega);have h0:(v3 n gs v (p+1)).2.length=(v3 n gs v p).2.length:=by rw[a1];exact vs n _ g w0 u hu c s
       have hv:u4 n (gs.drop (p+1)) (v3 n gs v (p+1))=u4 n (gs.drop p) (v3 n gs v p):=(by rw[zj,zj]);have aK:(gs.drop p).length=(gs.drop (p+1)).length+1:=(by rw[v2];simp);have hn:(v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
           (u4 n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B:=by
         rw[hv,h0];omega
       have e1:(v3 n gs v (p+1)).1.getD u (inl false)=inl c:=(by rw[a1];simp only[qa];rw[q8 _ _ _ _ (by omega)];exact s);refine⟨hn,?_,?_⟩
       . intro aE;subst aE;have r4:(v3 n gs v (p+1)).1.getD (n+p) (inl false)=inl false:=by
           rw[a1];simp only[qa];rw[z2 _ _ _ _ ht,x2,h5]
           rw[h5] at hu;simp only[kC,jC,or_false] at hu;rcases hu with rfl|rfl
           . simp only[kB,mS,s,qg];cases (v3 n gs v p).1.getD k (inl false)<;>simp[ko]
           . simp only[kB,mS,s,qg];cases (v3 n gs v p).1.getD j (inl false)<;>simp[ko]
         have hy:n+p∈u0 gs n o (p+1):=(b1 (n+p)).2 (Or.inl rfl);have hc:=zr hm (by omega) hy i r4;have m3:=zt n (n+p) (gs.drop (p+1)) (v3 n gs v (p+1)) hb
           (by omega) ⟨false,r4⟩ hc
         refine⟨by omega,r4,?_⟩
         intro g0;have g1:u∈u0 gs n o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,g0⟩;have g2:=zr hm (by omega) g1 i e1;have aC:=q22 hm b0 r3 bA;have aU:=k3 n u (n+p) (gs.drop (p+1)) (v3 n gs v (p+1))
           hb (by omega) (by omega) ⟨false,e1⟩ ⟨false,r4⟩ g2 hc aC
         omega
       . intro aF g0;subst aF;have g1:u∈u0 gs n o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,g0⟩;have g2:=zr hm (by omega) g1 i e1;have m3:=zt n u (gs.drop (p+1)) (v3 n gs v (p+1)) hb
           (by omega) ⟨true,e1⟩ g2
         omega
     have g3:∀x,e5 gs n (n+p) x=(e5 gs n j x&&e5 gs n k x):=fun x=>congrFun h8 x
     have r5:∀x,e5 gs n (n+p) x=(e5 gs n k x&&e5 gs n j x):=fun x=>by
       rw[g3 x,Bool.and_comm]
     have s2:tg j≠1:=by
       intro t;have b:=h6 j h7;rw[t] at b;obtain⟨v,i,s,z⟩:=b
       have:=(e0 j k (by simp[h5]) hj g3 v false 1 i s z).2.1 rfl
       omega
     have s6:tg k≠1:=by
       intro t;have b:=h6 k x3;rw[t] at b;obtain⟨v,i,s,z⟩:=b
       have:=(e0 k j (by simp[h5]) hk r5 v false 1 i s z).2.1 rfl
       omega
     have bB:tg j=1\/tg j=2\/tg j=3->decide (a6 n gs o (p+1) j)=false:=by
       intro aG;simp only[decide_eq_false_iff_not];intro c3;rcases aG with t|h2|h3
       . exact s2 t
       . have b:=h6 j h7;rw[h2] at b;obtain⟨v,i,s,z⟩:=b
         have:=(e0 j k (by simp[h5]) hj g3 v true 1 i s z).2.2 rfl c3;omega
       . have b:=h6 j h7;rw[h3] at b;obtain⟨v,i,s,z⟩:=b
         have:=((e0 j k (by simp[h5]) hj g3 v false 2 i s z).2.1 rfl).2.2 c3;omega
     have bC:tg k=1\/tg k=2\/tg k=3->decide (a6 n gs o (p+1) k)=false:=by
       intro aG;simp only[decide_eq_false_iff_not];intro t0;rcases aG with t|h2|h3
       . exact s6 t
       . have b:=h6 k x3;rw[h2] at b;obtain⟨v,i,s,z⟩:=b
         have:=(e0 k j (by simp[h5]) hk r5 v true 1 i s z).2.2 rfl t0;omega
       . have b:=h6 k x3;rw[h3] at b;obtain⟨v,i,s,z⟩:=b
         have:=((e0 k j (by simp[h5]) hk r5 v false 2 i s z).2.1 rfl).2.2 t0;omega
     set tg' : Nat->Nat:=fun a =>
       if a=n+p then (if tg j=3\/tg k=3 then 1 else 0)
       else if a=j\/a=k then 0
       else tg a
     have h6':∀a∈u0 gs n o (p+1),yf n gs f (p+1) a (tg' a):=by
       intro a ha;simp only[tg'];by_cases a2:a=n+p
       . subst a2;simp only[↓reduceIte];by_cases h3:tg j=3\/tg k=3
         . simp only[h3,↓reduceIte];rcases h3 with g4|j0
           . have b:=h6 j h7;rw[g4] at b;obtain⟨v,i,s,z⟩:=b;have hh:=e0 j k (by simp[h5]) hj g3 v false 2 i s z;exact⟨v,i,(hh.2.1 rfl).2.1,by omega⟩
           . have b:=h6 k x3;rw[j0] at b;obtain⟨v,i,s,z⟩:=b;have hh:=e0 k j (by simp[h5]) hk r5 v false 2 i s z;exact⟨v,i,(hh.2.1 rfl).2.1,by omega⟩
         . simp only[h3,↓reduceIte];trivial
       . simp only[a2,↓reduceIte];by_cases aM:a=j\/a=k
         . simp only[aM,↓reduceIte];trivial
         . simp only[aM,↓reduceIte];have d1:a∈u0 gs n o p:=by
             rcases (b1 a).1 ha with rfl|⟨t,_⟩
             . exact absurd rfl a2
             . exact t
           exact vv hg ((qw _ _ _ _ _).1 d1).1 (h6 a d1)
     have IH:=ih (p+1) (by omega) tg' h6';have hz:(((u0 gs n o p).erase j).erase k).map (fun a=>(e5 gs n a,tg' a)) =
         (((u0 gs n o p).erase j).erase k).map (fun a=>(e5 gs n a,tg a)):=by
       apply jH
       intro a ha;have⟨t,h2,h3⟩:=(d2 a).1 ha;have h4:a≠n+p:=b3 a h3;simp[tg',t,h2,h4]
     have xi:(qk (decide (a6 n gs o (p+1) j)) j (qk (decide (a6 n gs o (p+1) k)) k (((u0 gs n o p).erase j).erase k))).map
           (fun a=>(e5 gs n a,tg' a)) =
         qk (decide (a6 n gs o (p+1) j)) (e5 gs n j,0)
           (qk (decide (a6 n gs o (p+1) k)) (e5 gs n k,0) ((((u0 gs n o p).erase j).erase k).map fun a=>(e5 gs n a,tg a))):=by
       rw[wd,wd,hz]
       have xs:j≠n+p:=(by omega);have aH:k≠n+p:=(by omega);simp[tg',xs,aH]
     have IH':=gV.perm (r2.map fun a=>(e5 gs n a,tg' a)) IH;rw[kB,xi,h8] at IH';have f2:tg' (n+p)=(if tg j=3\/tg k=3 then 1 else 0):=(by simp[tg']);rw[f2] at IH';have hjle3:=q12 (h6 j h7);have hkle3:=q12 (h6 k x3);refine gV.perm (p0.map fun a=>(e5 gs n a,tg a)).symm ?_
     refine gV.bAnd (decide (a6 n gs o (p+1) j)) (decide (a6 n gs o (p+1) k))
       s2 s6 (fun h=>bB (by omega)) (fun h=>bC (by omega))
       (h8 ▸ aA) (h8 ▸ aB)
       (fun e=>c2 j h7 (h8 ▸ e.symm)) (fun e=>c2 k x3 (h8 ▸ e.symm)) ?_ IH'
     intro x hx;obtain⟨a,ha,rfl⟩:=mM.1 hx;exact h8 ▸ c2 a ((d2 a).1 ha).2.2
   .
     have h8:e5 gs n (n+p)=hG (e5 gs n j) (e5 gs n k):=(by funext x;rw[j1 x,x2,h5];simp[GateOp.eval]);have hs:∀(u:Nat) (hu:u∈g.inputs) (r3:u < n+p)
         (v:Fin n) (c:Q) (B:Nat),
         (∃x y,f (update x v false)≠f (update y v false)) ->
         (v3 n gs v p).1.getD u (inl false)=inl c ->
         (v3 n gs v p).2.length+(gs.drop p).length<=(u4 n (gs.drop p) (v3 n gs v p)).2.length+B ->
         (v3 n gs v (p+1)).1.getD u (inl false)=inl c /\
         (v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
           (u4 n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B /\
         (c=true->2<=B) /\
         (c=false->a6 n gs o (p+1) u->2<=B):=by
       intro u hu r3 v c B i s z;have a1:=rb n gs v p g hg;have ht:=vb n gs v p (by omega);have aJ:=vb n gs v (p+1) (by omega);have h0:(v3 n gs v (p+1)).2.length=(v3 n gs v p).2.length:=by rw[a1];exact vs n _ g w0 u hu c s
       have hv:u4 n (gs.drop (p+1)) (v3 n gs v (p+1))=u4 n (gs.drop p) (v3 n gs v p):=(by rw[zj,zj]);have aK:(gs.drop p).length=(gs.drop (p+1)).length+1:=(by rw[v2];simp);have hn:(v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
           (u4 n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B:=by
         rw[hv,h0];omega
       have e1:(v3 n gs v (p+1)).1.getD u (inl false)=inl c:=(by rw[a1];simp only[qa];rw[q8 _ _ _ _ (by omega)];exact s);refine⟨e1,hn,?_,?_⟩
       . intro aF;subst aF;have aN:(v3 n gs v (p+1)).1.getD (n+p) (inl false)=inl true:=by
           rw[a1];simp only[qa];rw[z2 _ _ _ _ ht,x2,h5]
           rw[h5] at hu;simp only[kC,jC,or_false] at hu;rcases hu with rfl|rfl
           . simp only[kB,mS,s,qg];cases (v3 n gs v p).1.getD k (inl false)<;>simp[ji]
           . simp only[kB,mS,s,qg];cases (v3 n gs v p).1.getD j (inl false)<;>simp[ji]
         have hy:n+p∈u0 gs n o (p+1):=(b1 (n+p)).2 (Or.inl rfl);have hc:=zr hm (by omega) hy i aN;have m3:=zt n (n+p) (gs.drop (p+1)) (v3 n gs v (p+1)) hb
           (by omega) ⟨true,aN⟩ hc
         omega
       . intro aE g0;subst aE;have g1:u∈u0 gs n o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,g0⟩;have g2:=zr hm (by omega) g1 i e1;have m3:=zt n u (gs.drop (p+1)) (v3 n gs v (p+1)) hb
           (by omega) ⟨false,e1⟩ g2
         omega
     have bD:tg j≠2:=by
       intro h2;have b:=h6 j h7;rw[h2] at b;obtain⟨v,i,s,z⟩:=b
       have:=(hs j (by simp[h5]) hj v true 1 i s z).2.2.1 rfl;omega
     have bE:tg k≠2:=by
       intro h2;have b:=h6 k x3;rw[h2] at b;obtain⟨v,i,s,z⟩:=b
       have:=(hs k (by simp[h5]) hk v true 1 i s z).2.2.1 rfl;omega
     have s2:tg j=1->decide (a6 n gs o (p+1) j)=false:=by
       intro t;simp only[decide_eq_false_iff_not];intro c3;have b:=h6 j h7;rw[t] at b;obtain⟨v,i,s,z⟩:=b
       have:=(hs j (by simp[h5]) hj v false 1 i s z).2.2.2 rfl c3;omega
     have s6:tg k=1->decide (a6 n gs o (p+1) k)=false:=by
       intro t;simp only[decide_eq_false_iff_not];intro t0;have b:=h6 k x3;rw[t] at b;obtain⟨v,i,s,z⟩:=b
       have:=(hs k (by simp[h5]) hk v false 1 i s z).2.2.2 rfl t0;omega
     set tg' : Nat->Nat:=fun a =>
       if a=n+p then 0
       else if a=j then (if tg j=3 then 1 else 0)
       else if a=k then (if tg k=3 then 1 else 0)
       else tg a
     have h6':∀a∈u0 gs n o (p+1),yf n gs f (p+1) a (tg' a):=by
       intro a ha;simp only[tg'];by_cases a2:a=n+p
       . simp[a2,yf]
       . simp only[a2,↓reduceIte];by_cases h9:a=j
         . rw[h9];simp only[↓reduceIte];by_cases g4:tg j=3
           . simp only[g4,↓reduceIte];have b:=h6 j h7;rw[g4] at b;obtain⟨v,i,s,z⟩:=b;have hh:=hs j (by simp[h5]) hj v false 2 i s z;exact⟨v,i,hh.1,by omega⟩
           . simp only[g4,↓reduceIte];trivial
         . simp only[h9,↓reduceIte];by_cases hd:a=k
           . rw[hd];simp only[↓reduceIte];by_cases j0:tg k=3
             . simp only[j0,↓reduceIte];have b:=h6 k x3;rw[j0] at b;obtain⟨v,i,s,z⟩:=b;have hh:=hs k (by simp[h5]) hk v false 2 i s z;exact⟨v,i,hh.1,by omega⟩
             . simp only[j0,↓reduceIte];trivial
           . simp only[hd,↓reduceIte];have d1:a∈u0 gs n o p:=by
               rcases (b1 a).1 ha with rfl|⟨t,_⟩
               . exact absurd rfl a2
               . exact t
             exact vv hg ((qw _ _ _ _ _).1 d1).1 (h6 a d1)
     have IH:=ih (p+1) (by omega) tg' h6';have hz:(((u0 gs n o p).erase j).erase k).map (fun a=>(e5 gs n a,tg' a)) =
         (((u0 gs n o p).erase j).erase k).map (fun a=>(e5 gs n a,tg a)):=by
       apply jH
       intro a ha;have⟨t,h2,h3⟩:=(d2 a).1 ha;have h4:a≠n+p:=b3 a h3;simp[tg',t,h2,h4]
     have xi:(qk (decide (a6 n gs o (p+1) j)) j (qk (decide (a6 n gs o (p+1) k)) k (((u0 gs n o p).erase j).erase k))).map
           (fun a=>(e5 gs n a,tg' a)) =
         qk (decide (a6 n gs o (p+1) j)) (e5 gs n j,if tg j=3 then 1 else 0)
           (qk (decide (a6 n gs o (p+1) k)) (e5 gs n k,if tg k=3 then 1 else 0) ((((u0 gs n o p).erase j).erase k).map fun a=>(e5 gs n a,tg a))):=by
       rw[wd,wd,hz]
       have xs:j≠n+p:=(by omega);have aH:k≠n+p:=(by omega);have bF:k≠j:=fun e=>aD e.symm
       simp[tg',xs,aH,bF]
     have IH':=gV.perm (r2.map fun a=>(e5 gs n a,tg' a)) IH;rw[kB,xi,h8] at IH';have f2:tg' (n+p)=0:=(by simp[tg']);rw[f2] at IH';refine gV.perm (p0.map fun a=>(e5 gs n a,tg a)).symm ?_
     refine gV.bOr (decide (a6 n gs o (p+1) j)) (decide (a6 n gs o (p+1) k))
       bD bE s2 s6
       (h8 ▸ aA) (h8 ▸ aB)
       (fun e=>c2 j h7 (h8 ▸ e.symm)) (fun e=>c2 k x3 (h8 ▸ e.symm)) ?_ IH'
     intro x hx;obtain⟨a,ha,rfl⟩:=mM.1 hx;exact h8 ▸ c2 a ((d2 a).1 ha).2.2
lemma rh {n:Nat}{gs:U}{o:Nat}{f:Z n}(hev:∀x,e5 gs n o x=f x)(v:Fin n) (z:∃x:F n,f (update x v (!x v))≠f x):(v:Nat)∈u0 gs n o 0:=by
 rw[qw]
 refine⟨by omega,?_⟩
 by_contra j;have h0:¬wn n gs o (v:Nat):=by
  intro b;rcases q66 b with h1|⟨q,g,hg,h2,h3⟩
  . exact j (Or.inl h1)
  . exact j (Or.inr ⟨q,mJ q,g,hg,h2,h3⟩)
 obtain⟨x,s⟩:=z;apply s
 rw[<- hev,<- hev]
 have h4:∀(p:Nat),∀i < n+p,wn n gs o i ->
    (q3 (gs.take p) (ofFn (update x v (!x v)))).getD i false =
    (q3 (gs.take p) (ofFn x)).getD i false:=by
  intro p;induction p with
  | zero =>
    intro i hi b;simp only[List.take_zero,q3,List.foldl_nil];have c:i < n:=by omega
    have h5:(⟨i,c⟩:Fin n)≠v:=fun e=>h0 (by simpa[<- e] using b)
    simp[c,kV h5]
  | succ p ih =>
    intro i hi b;by_cases t:p < gs.length
    . have d:gs.take (p+1)=gs.take p++[gs[p]]:=List.take_succ_eq_append_getElem t;rw[d,zd,zd]
      have h6:(q3 (gs.take p) (ofFn (update x v (!x v)))).length=n+p:=(by rw[qu];simp[pB,jR (by omega:p<=gs.length)]);have h7:(q3 (gs.take p) (ofFn x)).length=n+p:=(by rw[qu];simp[pB,jR (by omega:p<=gs.length)]);by_cases h8:i=n+p
      . subst h8
        show (q3 (gs.take p) _++[_]).getD (n+p) false=(q3 (gs.take p) _++[_]).getD (n+p) false
        rw[z2 _ _ _ _ h6,z2 _ _ _ _ h7]
        congr 1
        apply jH
        intro a ha;have h9:wn n gs o a:=ph (jK t) b ha;by_cases x2:a < n+p
        . exact ih a x2 h9
        . rw[mQ _ _ (by omega),mQ _ _ (by omega)]
      . show (q3 (gs.take p) _++[_]).getD i false=(q3 (gs.take p) _++[_]).getD i false
        rw[q8 _ _ _ _ (by omega),q8 _ _ _ _ (by omega)]
        exact ih i (by omega) b
    . have d:gs.take (p+1)=gs.take p:=(by rw[List.take_of_length_le (by omega),List.take_of_length_le (by omega)]);rw[d]
      by_cases c:i < n+p
      . exact ih i c b
      . have hl1:(q3 (gs.take p) (ofFn (update x v (!x v)))).length=n+gs.length:=(by rw[qu,List.take_of_length_le (by omega)];simp);have hl2:(q3 (gs.take p) (ofFn x)).length=n+gs.length:=(by rw[qu,List.take_of_length_le (by omega)];simp);rw[mQ _ _ (by omega),mQ _ _ (by omega)]
 have x3:o < n+gs.length:=by
  by_contra hge;have u:∀y:F n,e5 gs n o y=false:=fun y =>
    mQ _ _ (by rw[qu];simp;omega)
  exact s (by rw[<- hev,<- hev,u,u])
 have h:=h4 gs.length o x3 (pe n gs o);rw[jQ] at h;exact h
open Classical in
lemma q88 {n:Nat}(f:Z n)(d:Nat)(c:Fin n->Nat)(h4:∃y y':F n,f y≠f y') (h5:∀v:Fin n,∃x:F n,f (update x v (!x v))≠f x) (h6:∀v:Fin n,c v=0\/(c v=1/\(∃x y,f (update x v false)≠f (update y v false))/\∀s',nV n (fun x=>f (update x v false)) s'->d - 1<=s')\/(c v=3/\(∃x y,f (update x v false)≠f (update y v false))/\∀s',nV n (fun x=>f (update x v false)) s'->d - 2<=s')) (s:Nat)(hs:s<=d)(hc:nV n f s):∃s',s'<=d/\gV (hC (n:=n)) hE hG (fun _=>false) (fun _=>true) f s' (ofFn fun i:Fin n=>((fun x:F n=>x i),c i)):=by
 obtain⟨gs,o,e,hlen⟩:=ng n f s h4 hc;have u:u0 gs n o 0=range n:=by
  have z:=(List.filter_sublist (l:=range (n+0)) (p:=fun a=>decide (a6 n gs o 0 a)));simp only[mH] at z;refine List.Sublist.eq_of_length z ?_
  have h7:(range n).Perm (u0 gs n o 0):=by
    refine (List.perm_ext_iff_of_nodup List.nodup_range (vy gs n o 0)).2 ?_
    intro a;rw[jF]
    constructor
    . intro b;exact rh e.gQ ⟨a,b⟩ (h5 ⟨a,b⟩)
    . intro b;exact by simpa using ((qw gs n o 0 a).1 b).1
  exact h7.length_eq.symm
 set tg:Nat->Nat:=fun a=>if h:a < n then c ⟨a,h⟩ else 0
 have h8:∀a∈u0 gs n o 0,yf n gs f 0 a (tg a):=by
  intro a b;rw[u,jF] at b;have h9:tg a=c ⟨a,b⟩:=by simp[tg,b]
  rw[h9]
  rcases h6 ⟨a,b⟩ with h0|⟨h1,g,j⟩|⟨h3,g,j⟩
  . rw[h0];trivial
  . rw[h1]
    have x2:=(wz n f gs o ⟨a,b⟩ (d - 1) e.gP e.gQ g j).2;refine⟨⟨a,b⟩,g,?_,?_⟩
    . simp[v3,u4,wf,b]
    . simp only[v3,List.take_zero,List.drop_zero,pC,zero_add];have t:u4 n [] (wf n ⟨a,b⟩,[])=(wf n ⟨a,b⟩,[]):=rfl;rw[t];simp only[pC,zero_add];omega
  . rw[h3]
    have x2:=(wz n f gs o ⟨a,b⟩ (d - 2) e.gP e.gQ g j).2;refine⟨⟨a,b⟩,g,?_,?_⟩
    . simp[v3,u4,wf,b]
    . simp only[v3,List.take_zero,List.drop_zero,pC,zero_add];have t:u4 n [] (wf n ⟨a,b⟩,[])=(wf n ⟨a,b⟩,[]):=rfl;rw[t];simp only[pC,zero_add];omega
 have x3:=kc n f gs o e gs.length 0 (by omega) tg h8;refine⟨gs.length,by omega,?_⟩
 have a1:(u0 gs n o 0).map (fun a=>(e5 gs n a,tg a)) =
    ofFn fun i:Fin n=>((fun x:F n=>x i),c i):=by
  rw[u]
  apply List.ext_getElem
  . simp
  . intro i h1 h2;have hi:i < n:=by simpa using h2
    simp only[List.getElem_map,List.getElem_range,List.getElem_ofFn];exact Prod.ext (vx gs n ⟨i,hi⟩) (by simp[tg,hi])
 rw[<- a1]
 exact x3
def zm {α:Type} (x:Nat)(f:Nat->α): α:=
 match x with
 | 0=>f 0
 | n+1=>f (Nat.succ n)
lemma v5 {α:Type} (x:Nat)(f:Nat->α):zm x f=f x:=by cases x<;>rfl
structure Cfg where
 k:Nat
 fE:Nat
 fF:Nat
 fH:Nat
 fJ:Nat
 fK:Nat
 fL:Nat
 fM:Nat
 m0:Nat
 fN:Nat
 fP:Nat
 m1:Nat
 fQ:Nat
 fR:Nat
 fS:Nat
def pa (b:Nat×Nat×Nat×Nat)(w:Nat):Nat:=
 let (d,m01,m10,mEq):=b
 lor (lor (land w mEq) (shiftRight (land w m01) d))
  (shiftLeft (land w m10) d)
def ym:V->Nat->Nat
 | [],w=>w
 | sw::rest,w=>ym rest (pa sw w)
def bn (sh:Nat):J->J
 | []=>[]
 | (w,tg)::rest=>zm (shiftRight w sh) fun v=>(v,tg)::bn sh rest
def wx (g:V):J->J
 | []=>[]
 | (w,tg)::rest=>zm (ym g w) fun v=>(v,tg)::wx g rest
def M128:Nat:=0x9e3779b97f4a7c15f39cc0605cedc835
def pj:Nat:=0x517cc1b727220a95b3650d1e9a87c3f1
def pk:Nat:=0xbf58476d1ce4e5b994d049bb133111eb
def pm:Nat:=0x2545f4914f6cdd1d6c62272e07bb0142
def pn (b w tg:Nat):Nat:=
 let s:=match tg with
  | 0=>b
  | 1=>xor b pj
  | 2=>xor b pk
  | _=>xor b pm
 zm (xor (xor w (shiftRight w 61)) s) fun x =>
 shiftRight (mul x (xor x M128)) 104
def ir (salt:Nat):Nat->J->Nat
 | acc,[]=>acc
 | acc,(w,tg)::rest=>zm (add acc (pn salt w tg)) fun acc' => ir salt acc' rest
def gz (salt:Nat)(ws:J):Nat:=land (ir salt 0 ws) 0xFFFFFF
def cj (T i:Nat):Nat:=land (shiftRight T (mul 24 i)) 0xFFFFFF
def au (T i:Nat):Nat:=land (shiftRight T (mul 32 i)) 0xFFFFFFFF
def av (T h:Nat):Nat->Nat->Nat->Nat
 | 0,lo,_=>lo
 | fuel+1,lo,hi =>
  if ble (add lo 2) hi then
   zm (div (add lo hi) 2) fun mid =>
   if ble (cj T mid) h then av T h fuel mid hi else av T h fuel lo mid
  else lo
def ar (NN FL HT:Nat->Nat)(s h:Nat):Nat:=
 let n:=NN s
 if beq n 0 then 999999
 else
  let b:=HT s
  zm (av b h (FL s) 0 n) fun j =>
  if beq (cj b j) h then j else 999999
def ce (a b:K):Q:=beq a.1 b.1&&beq a.2 b.2
def jy (x:K):J->Option (J)
 | []=>none
 | a::rest =>
  if ce x a then some rest
  else match jy x rest with
   | none=>none
   | some r=>some (a::r)
def jk:J->J->Q
 | [],[]=>true
 | a::as,bs=>match jy a bs with
  | none=>false
  | some bs' => jk as bs'
 | _,_=>false
def fy (a b:K):Q:=
 if beq a.1 b.1 then blt a.2 b.2 else blt a.1 b.1
def ly (x:K):J->J
 | []=>[x]
 | a::rest=>if fy x a then x::a::rest else a::ly x rest
def bu:J->J
 | []=>[]
 | a::rest=>ly a (bu rest)
def iz:J->J->Q
 | [],_=>false
 | _,[]=>false
 | a::as,b::bs =>
  if ce a b then iz as bs else fy a b
def ij (g:V)(b:J):J:=
 let b':=bu (wx g b)
 if iz b' b then b' else b
def fr:List (V)->J->J
 | [],ws=>ws
 | g::rest,ws=>fr rest (ij g ws)
def cn (b:List (V)) (c:J):J:=
 let s0:=bu c
 match b with
 | []=>s0
 | [g]=>ij g s0
 | _=>fr b (fr b s0)
def qi (m0 d:Nat):Nat:=
 zm (land d m0) fun a =>
 zm (land (shiftRight d 1) m0) fun b =>
 zm (land (shiftRight d 2) m0) fun c =>
 zm (xor m0 (land (shiftRight d 3) m0)) fun nd =>
 zm (xor m0 (land (shiftRight d 4) m0)) fun ne =>
 zm (xor m0 (land (shiftRight d 5) m0)) fun nf =>
 sub (add (add (land nd b) (land nd c)) (add (land a ne) (land a nf)))
  (land (land a nd) (land (lor b c) (lor ne nf)))
def yg (sh1 m1 m12 w:Nat):Nat:=
 zm (shiftRight w sh1) fun w0 =>
 zm (land w0 m1) fun a =>
 zm (land (shiftRight w0 1) m1) fun b =>
 zm (land (shiftRight w0 2) m1) fun c =>
 zm (land (shiftRight w0 3) m1) fun d =>
 zm (land (shiftRight w0 4) m1) fun e =>
 zm (land (shiftRight w0 5) m1) fun f =>
 zm (xor m1 d) fun nd =>
 zm (xor m1 e) fun ne =>
 zm (xor m1 f) fun nf =>
 zm (xor m1 a) fun na =>
 zm (xor m1 b) fun nb =>
 zm (xor m1 c) fun nc =>
 zm (sub (add (add (land nd b) (land nd c)) (add (land a ne) (land a nf)))
  (land (land a nd) (land (lor b c) (lor ne nf)))) fun v1 =>
 zm (sub (add (add (land d nb) (land d nc)) (add (land na e) (land na f)))
  (land (land na d) (land (lor nb nc) (lor e f)))) fun v2 =>
 zm (lor v1 v2) fun u =>
 zm (land u m12) fun hi =>
 lor hi (lor (lor (land v1 (shiftRight v1 1)) (land v2 (shiftRight v2 1)))
   (land (land u m1) (xor m1 (shiftRight hi 1))))
def qb (c:Cfg)(b d:Nat):Q:=
 beq (land (add (add b d) c.fN) c.fP) c.fP
def z3 (c:Cfg)(b:Nat):Q:=
 beq (land (add b c.fR) c.fS) c.fS
def ik (b:Nat):Nat->Nat->K
 | 0,j=>(0,j)
 | fuel+1,j =>
  let t:=div (mul (add j 1) j) 2
  if ble t b then ik b fuel (add j 1)
  else (sub b (div (mul j (sub j 1)) 2),j)
def jw:Nat->J->K
 | _,[]=>(0,0)
 | 0,a::_=>a
 | k+1,_::rest=>jw k rest
def cg:Nat->J->J
 | _,[]=>[]
 | 0,_::rest=>rest
 | k+1,a::rest=>a::cg k rest
def re (all1v g:Nat)(d:J):J:=
 if ble g 32 then
  zm (sub g 1) fun c =>
  zm (shiftRight c 1) fun i =>
  let u:=beq (land c 1) 1
  let (a,ta):=jw i d
  let e:=if beq ta 3 then 2 else 0
  zm (xor a all1v) fun w =>
  let r:=cg i d
  if u then (w,e)::(a,0)::r else (w,e)::r
 else
  zm (sub g 33) fun rem =>
  let s:=beq (land rem 1) 1
  let t:=beq (land (shiftRight rem 1) 1) 1
  let v:=beq (land (shiftRight rem 2) 1) 1
  let (i,j):=ik (shiftRight rem 3) 16 1
  let (a,ta):=jw i d
  let (b,tb):=jw j d
  let r:=cg i (cg j d)
  if v then
   let e:=if beq ta 3||beq tb 3 then 1 else 0
   zm (land a b) fun w =>
   let r1:=if s then (b,0)::r else r
   let h:=if t then (a,0)::r1 else r1
   (w,e)::h
  else
   zm (lor a b) fun w =>
   let r1:=if s then (b,if beq tb 3 then 1 else 0)::r else r
   let h:=if t then (a,if beq ta 3 then 1 else 0)::r1 else r1
   (w,0)::h
def cx (all1v:Nat) (xs:J) (PT:Nat->Nat):Nat->Nat->Nat->J
 | 0,_,_=>xs
 | d+1,s,j =>
  zm (au (PT s) j) fun e =>
  zm (land e 1023) fun code =>
  if beq code 0 then xs
  else zm (land (shiftRight e 10) 8191) fun pidx =>
   re all1v code (cx all1v xs PT d (add s 1) pidx)
def c8 (all1v b:Nat)(c:J)(PT:Nat->Nat)(s j:Nat):J:=
 cx all1v c PT (sub b s) s j
def uh (shTT c:Nat)(Rtt:Nat->Nat->J)(NN FL HT:Nat->Nat)(s:Nat)(d:J):Q:=
 let b:=bn shTT d
 zm (gz c b) fun h =>
 zm (ar NN FL HT s h) fun j =>
 !(beq j 999999)&&jk b (Rtt s j)
def p5 (shTT c:Nat)(e:V)(Rtt:Nat->Nat->J)(NN FL HT:Nat->Nat)(s:Nat)(g:J):Q:=
 let b:=bn shTT g
 zm (gz c b) fun h0 =>
 zm (ar NN FL HT s h0) fun j0 =>
 if !(beq j0 999999)&&jk b (Rtt s j0) then true
 else
  let d:=wx e b
  zm (gz c d) fun h1 =>
  zm (ar NN FL HT s h1) fun j1 =>
  !(beq j1 999999)&&jk d (Rtt s j1)
def vm (salt:Nat) (Rtt:Nat->Nat->J) (NN FL HT:Nat->Nat)
  (s:Nat):List (V)->J->Q
 | [],ztt =>
  zm (gz salt ztt) fun h =>
  zm (ar NN FL HT s h) fun j =>
  !(beq j 999999)&&jk ztt (Rtt s j)
 | g::rest,ztt =>
  zm (gz salt ztt) fun h =>
  zm (ar NN FL HT s h) fun j =>
  if !(beq j 999999)&&jk ztt (Rtt s j) then true
  else vm salt Rtt NN FL HT s rest (wx g ztt)
def i9 (shTT b:Nat) (c:List (V)) (Rtt:Nat->Nat->J)(NN FL HT:Nat->Nat)(s:Nat)(d:J):Q:=
 vm b Rtt NN FL HT s c (bn shTT d)
def f8 (shTT c:Nat) (d:List (V)) (e:Nat->V)(Rtt:Nat->Nat->J)(NN FL HT PT:Nat->Nat)(s:Nat)(g:J):Q:=
 let b:=cn d (bn shTT g)
 zm (gz c b) fun h =>
 zm (ar NN FL HT s h) fun j =>
 if beq j 999999 then false
 else
  zm (shiftRight (au (PT s) j) 23) fun aidx =>
  jk b (wx (e aidx) (Rtt s j))
structure WF where
 w:Nat
 tg:Nat
 lo:Nat
 hi:Nat
 cv:Nat
 uv:Nat
 a0:Nat
 v0:Nat
 v1:Nat
 sC:Nat
 sU:Nat
 s0:Nat
 s1:Nat
def e4 (c:Cfg):J->Nat×Nat×Nat×Nat×List WF
 | []=>(0,0,0,0,[])
 | (w,tg)::rest =>
  let (sC,sU,s0,s1,rs):=e4 c rest
  zm (land w c.fL) fun lo =>
  zm (land (shiftRight w c.k) c.fL) fun hi =>
  zm (xor lo hi) fun cv =>
  zm (land cv hi) fun uv =>
  zm (land (shiftRight w c.fE) c.fM) fun a0 =>
  zm (qi c.m0 a0) fun v0 =>
  zm (yg c.fF c.m1 c.fQ w) fun v1 =>
  zm (lor uv sU) fun nU =>
  (lor cv sC,nU,add v0 s0,add v1 s1,
   ⟨w,tg,lo,hi,cv,uv,a0,v0,v1,sC,sU,s0,s1⟩::rs)
def p4 (z:Nat):J->Q
 | []=>false
 | (w,_)::rest=>beq w z||p4 z rest
def x5 (c:Cfg)(b:J)(w:Nat):Q:=
 beq w 0||beq w c.fJ||p4 w b
def k5 (c:Cfg)(d e i g j s:Nat)(t:Q)(u v:Unit->Nat)(b:Unit->Q):Q:=
 if blt (add d 1) e then true
 else if beq d 0 then b ()
 else if !(beq i c.fL) then true
 else if ble e 11 then
  let h:=sub (add d 1) e
  if beq h 0 then
   if !(beq g c.fL) then true
   else if !(qb c j (u ())) then true
   else b ()
  else if beq h 1 then
   if beq g c.fL then b ()
   else if t then true
   else if z3 c (add s (v ())) then b ()
   else true
  else b ()
 else b ()
def k9 (pre:J):List WF->J
 | []=>pre
 | x::xs=>(x.w,x.tg)::k9 pre xs
def v7 (c:Cfg)(d e:Nat)(h8:J)(x:J->Q)(h9 isOr:Q)(v:Nat)(a:WF)(y:Nat)(b:WF)(h0:Nat)(g h i j:Nat)(h1 h2:Q)(h3:J)(h4:List WF):Q:=
 zm (if isOr then lor a.lo b.lo else land a.lo b.lo) fun zlo =>
 zm (if isOr then lor a.hi b.hi else land a.hi b.hi) fun zhi =>
 zm (xor zlo zhi) fun cz =>
 zm (land cz zhi) fun uz =>
 let s:Unit->Nat:=fun ()=>qi c.m0 (if isOr then lor a.a0 b.a0 else land a.a0 b.a0)
 let h5:Unit->Nat:=fun ()=>if isOr then lor a.w b.w else land a.w b.w
 let t:Unit->Nat:=fun ()=>yg c.fF c.m1 c.fQ (h5 ())
 let u (extra:J):Q:=
  zm (h5 ()) fun z =>
  if x5 c h8 z then true
  else if beq d 0 then
   match (z,v)::extra++k9 h3 h4 with
   | [(w,_)]=>if beq w c.fK then x [(w,v)] else true
   | _=>true
  else x ((z,v)::extra++k9 h3 h4)
 let x2:=k5 c d (sub e 1) (lor cz g) (lor uz h) i j h9 s t (fun ()=>u [])
 if !x2 then false
 else if blt (add d 1) e then true
 else
  let h6:=if h2 then
   k5 c d e (lor cz (lor b.cv g)) (lor uz (lor b.uv h)) (add i b.v0) (add j b.v1) false s t (fun ()=>u [(b.w,h0)])
   else true
  let h7:=if h6&&h1 then
   k5 c d e (lor cz (lor a.cv g)) (lor uz (lor a.uv h)) (add i a.v0) (add j a.v1) false s t (fun ()=>u [(a.w,y)])
   else h6
  if h7&&h1&&h2&&ble (add e 1) (add d 1) then
   k5 c d (add e 1) (lor cz (lor a.cv (lor b.cv g))) (lor uz (lor a.uv (lor b.uv h)))
    (add i (add a.v0 b.v0)) (add j (add a.v1 b.v1)) false s t (fun ()=>u [(a.w,y),(b.w,h0)])
  else h7
def b8 (c:Cfg)(b e sl:Nat)(h0:J)(g:J->Q)(forG:Q)(a:WF)(h i j s:Nat)(t:J)(u:List WF):Q:=
 if (if forG then beq a.tg 0||beq a.tg 3 else !(beq a.tg 1)&&!(beq a.tg 2)) then
  zm a.cv fun cz =>
  zm (land a.cv a.lo) fun uz =>
  let d:=if beq a.tg 3 then 2 else 0
  let v:Unit->Nat:=fun ()=>qi c.m0 (xor a.a0 c.fM)
  let x:Unit->Nat:=fun ()=>a.v1
  let y (extra:J):Q:=
   zm (xor a.w c.fJ) fun z =>
   if x5 c h0 z then true
   else if beq b 0 then
    match (z,d)::extra++k9 t u with
    | [(w,_)]=>if beq w c.fK then g [(w,d)] else true
    | _=>true
   else g ((z,d)::extra++k9 t u)
  let h1:=k5 c b e (lor cz h) (lor uz i) j s false v x (fun ()=>y [])
  if !h1 then false
  else if (if forG then beq a.tg 0 else !(beq a.tg 3))&&ble 2 sl then
   k5 c b (add e 1) (lor cz (lor a.cv h)) (lor uz (lor a.uv i))
    (add j a.v0) (add s a.v1) false v x (fun ()=>y [(a.w,0)])
  else true
 else true
def b7 (nf:WF->Nat->Nat->Nat->Nat->J->List WF->Q)
  (preC preU preV0 preV1:Nat) (pre:J):List WF->Q
 | []=>true
 | a::suf =>
  nf a (lor preC a.sC) (lor preU a.sU) (add preV0 a.s0) (add preV1 a.s1) pre suf &&
  b7 nf (lor preC a.cv) (lor preU a.uv) (add preV0 a.v0) (add preV1 a.v1) ((a.w,a.tg)::pre) suf
def k2 (c:Cfg)(d e:Nat)(g:J)(h:J->Q)(i:Q)(a b:WF)(j s t u:Nat)(v:J)(x:List WF):Q:=
 let y:=
  if !(beq a.tg 2)&&!(beq b.tg 2) then
   v7 c d e g h i true 0 a (cond (beq a.tg 3) 1 0) b (cond (beq b.tg 3) 1 0)
    j s t u (!(beq a.tg 1)) (!(beq b.tg 1)) v x
  else true
 if !y then false
 else if !(beq a.tg 1)&&!(beq b.tg 1) then
  v7 c d e g h i false (cond (beq a.tg 3||beq b.tg 3) 1 0) a 0 b 0
   j s t u (beq a.tg 0) (beq b.tg 0) v x
 else true
def t9 (pf:WF->WF->Nat->Nat->Nat->Nat->J->List WF->Q)
  (a:WF) (pmC pmU pmV0 pmV1:Nat) (pre:J):List WF->Q
 | []=>true
 | b::suf =>
  pf a b (lor pmC b.sC) (lor pmU b.sU) (add pmV0 b.s0) (add pmV1 b.s1) pre suf &&
  t9 pf a (lor pmC b.cv) (lor pmU b.uv) (add pmV0 b.v0) (add pmV1 b.v1) ((b.w,b.tg)::pre) suf
def a4 (pf:WF->WF->Nat->Nat->Nat->Nat->J->List WF->Q)
  (preC preU preV0 preV1:Nat) (pre:J):List WF->Q
 | []=>true
 | a::suf =>
  t9 pf a preC preU preV0 preV1 pre suf &&
  a4 pf (lor preC a.cv) (lor preU a.uv) (add preV0 a.v0) (add preV1 a.v1) ((a.w,a.tg)::pre) suf
def b9 (c:Cfg) (totV0:Nat):List WF->Q
 | []=>false
 | a::rest=>qb c totV0 a.v0||b9 c totV0 rest
def x8 (forG isOr:Q)(ta b:Nat):Q:=
 if isOr then
  if forG then !(beq ta 2)&&!(beq b 2)&&!(beq ta 7)&&!(beq b 7) &&
   !((beq ta 4&&beq b 6)||(beq ta 6&&beq b 4))
  else !(beq ta 2)&&!(beq b 2)
 else
  if forG then !(beq ta 1)&&!(beq b 1)&&!(beq ta 4)&&!(beq b 4)&&!(beq ta 8)&&!(beq b 8) &&
   !((beq ta 6&&!(beq b 7))||(beq b 6&&!(beq ta 7)))
  else !(beq ta 1)&&!(beq b 1)
def sq (forG isOr:Q)(ta b:Nat):Nat:=
 if isOr then (if forG then cond (beq ta 4||beq b 4) 7 0 else 0)
 else (if forG then cond (beq ta 6||beq b 6) 8 (cond (beq ta 3||beq b 3) 1 0)
  else cond (beq ta 3||beq b 3) 1 0)
def sz (c:Cfg)(d:J)(e:J->Q)(forG:Q)(a b:WF)(g:Nat)(h:J)(i:List WF):Q:=
 let j:=
  if x8 forG true a.tg b.tg then
   zm (lor a.lo b.lo) fun zlo =>
   zm (lor a.hi b.hi) fun zhi =>
   if beq (lor (land (xor zlo zhi) zhi) g) c.fL then
    zm (lor a.w b.w) fun z =>
    if x5 c d z then true
    else e ((z,sq forG true a.tg b.tg)::k9 h i)
   else true
  else true
 if !j then false
 else if x8 forG false a.tg b.tg then
  zm (land a.lo b.lo) fun zlo =>
  zm (land a.hi b.hi) fun zhi =>
  if beq (lor (land (xor zlo zhi) zhi) g) c.fL then
   zm (land a.w b.w) fun z =>
   if x5 c d z then true
   else e ((z,sq forG false a.tg b.tg)::k9 h i)
  else true
 else true
def d0 (c:Cfg) (allWs:J) (onS:J->Q) (forG:Q)
  (a:WF) (pmU:Nat) (pre:J):List WF->Q
 | []=>true
 | b::suf =>
  zm (lor pmU b.sU) fun rU =>
  sz c allWs onS forG a b rU pre suf &&
  zm (lor pmU b.uv) fun nU =>
  d0 c allWs onS forG a nU ((b.w,b.tg)::pre) suf
def d5 (c:Cfg) (allWs:J) (onS:J->Q) (forG:Q)
  (preU:Nat) (pre:J):List WF->Q
 | []=>true
 | a::suf =>
  d0 c allWs onS forG a preU pre suf &&
  zm (lor preU a.uv) fun nU =>
  d5 c allWs onS forG nU ((a.w,a.tg)::pre) suf
def uq (c:Cfg)(i:J->Q)(e:Nat)(d:J):Q:=
 let b:=d.length
 let g:=sub (add e 2) b
 let (_,totU,totV0,totV1,wfs):=e4 c d
 let h:=ble b 11&&beq g 1&&!(z3 c totV1)
 if (ble b 11&&beq g 0||h)&&!(beq totU c.fL) then true
 else if h&&ble b 10&&!(beq e 0)&&!(zm totV0 fun fn=>b9 c fn wfs) then
  d5 c d i false 0 [] wfs
 else
  (if ble 1 g&&!h then b7 (b8 c e b g d i false) 0 0 0 0 [] wfs else true) &&
  a4 (k2 c e b d i h) 0 0 0 0 [] wfs
def m7 (c:Cfg):Nat->J->Q
 | 0,ws=>match ws with | [(w,_)]=>!(beq w c.fK) | _=>true
 | ns+1,ws=>uq c (fun _=>false) ns ws
def bar (c:Cfg) (findFn:Nat->J->Q) (R:Nat->Nat->J):Nat->Nat->Q
 | 0,i=>match R 0 i with | [(w,_)]=>!(beq w c.fK) | _=>true
 | ns+1,i =>
  uq c (fun nxt =>
   if findFn ns nxt then true
   else if beq ns 0 then false
   else m7 c ns nxt) ns (R (ns+1) i)
def jM (f:Nat->Q):Nat->Nat->Q
 | 0,_=>true
 | n+1,i=>f i&&jM f n (add i 1)
def q1 (n r:Nat):F n:=fun i=>r.testBit i.val
def ur {n:Nat}(x:F n):Nat:=
 (finRange n).foldr (fun i acc=>if x i then acc|||(1 <<< i.val) else acc) 0
lemma qp {m:Nat}(hm:m≠0):(1:Nat).testBit m=false:=by
 cases m with
 | zero=>contradiction
 | succ k=>simp[Nat.testBit_succ]
lemma z7 {x m:Nat}(h:x.testBit m=true):(x / 2 ^ m) % 2=1:=by rw[nT] at h;exact of_decide_eq_true h
lemma z5 {x m:Nat}(h:x.testBit m=false):(x / 2 ^ m) % 2=0:=by
 rw[nT] at h
 have:=of_decide_eq_false h
 omega
lemma zg {x m:Nat}(h:x.testBit m=true):2 ^ m<=x:=by
 have b:=z7 h;have c:1<=x / 2 ^ m:=by generalize x / 2 ^ m=q at b ⊢;omega
 have h3:=Nat.mul_le_mul_right (2 ^ m) c;have h4:=Nat.div_mul_le_self x (2 ^ m);omega
lemma vz {y m:Nat}(h:y.testBit m=false):y % 2 ^ (m+1) < 2 ^ m:=by
 have b:(y / 2 ^ m) % 2=0:=z5 h;have c:y % 2 ^ (m+1) / 2 ^ m=(y / 2 ^ m) % 2:=by rw[Nat.pow_succ,Nat.mod_mul_right_div_self]
 have d:y % 2 ^ (m+1) / 2 ^ m=0:=by rw[c,b]
 exact (Nat.div_eq_zero_iff.1 d).resolve_left (Nat.ne_of_gt (mL m))
lemma vk {y m:Nat}(h:y.testBit m=false)(k:Nat):(y+2 ^ m).testBit k=if k=m then true else y.testBit k:=by
 by_cases c:k=m
 . subst c;have h0:=z5 h;rw[nT,Nat.add_div_right _ (mL k)]
   simp;omega
 . simp only[c,↓reduceIte];by_cases d:k < m
   . have e:2 ^ m=2 ^ k*2 ^ (m - k):=(by rw[<- Nat.pow_add,Nat.add_sub_cancel' (le_of_lt d)]);have b:1<=m - k:=(by omega);have hev:2 ^ (m - k) % 2=0:=(by obtain⟨q,g⟩:=Nat.exists_eq_add_of_le' b;rw[g,Nat.pow_succ];omega);rw[nT,nT,e,Nat.mul_comm (2 ^ k),Nat.add_mul_div_right _ _ (mL k)]
     have:(y / 2 ^ k+2 ^ (m - k)) % 2=(y / 2 ^ k) % 2:=by omega
     rw[this]
   . have b:m+1<=k:=(by omega);have i:y % 2 ^ (m+1)+2 ^ m < 2 ^ (m+1):=(by have hltm:=vz h;have hpw:2 ^ (m+1)=2 ^ m*2:=Nat.pow_succ 2 m;omega);have j:(y+2 ^ m) / 2 ^ (m+1)=y / 2 ^ (m+1):=by
      have s:y=2 ^ (m+1)*(y / 2 ^ (m+1))+y % 2 ^ (m+1):=(Nat.div_add_mod y (2 ^ (m+1))).symm;conv_lhs=>rw[s,mG]
      rw[Nat.mul_add_div (mL (m+1)),Nat.div_eq_of_lt i,mH]
     have t:2 ^ k=2 ^ (m+1)*2 ^ (k - (m+1)):=(by rw[<- Nat.pow_add,Nat.add_sub_cancel' b]);rw[nT,nT,t,<- Nat.div_div_eq_div_mul,<- Nat.div_div_eq_div_mul,j]
lemma qs {y m:Nat}(h:y.testBit m=false):y+2 ^ m=y^^^2 ^ m:=by
 apply kL;intro k;rw[vk h,kP,nW]
 by_cases b:k=m
 . subst b;simp[h]
 . simp[b,Ne.symm b]
lemma jl {n:Nat}(x:F n)(k:Nat):(ur x).testBit k=if h:k < n then x ⟨k,h⟩ else false:=by
 have s:∀(l:List (Fin n)),l.Nodup ->
   (l.foldr (fun i acc=>if x i then acc|||(1 <<< i.val) else acc) 0).testBit k =
   if h:k < n then (if ⟨k,h⟩∈l then x ⟨k,h⟩ else false) else false:=by
  intro l u;induction l with
  | nil=>simp
  | cons a t ih =>
   obtain⟨v,y⟩:=List.nodup_cons.1 u;simp only[kG];have g:=ih y;by_cases d:x a=true
   . simp only[d,↓reduceIte,kM,nN,g];by_cases b:k < n
     . simp only[b,↓reduceDIte,kC];by_cases c:(⟨k,b⟩:Fin n)=a
       . subst c;simp[d]
       . have z:k≠a.val:=fun e=>c (Fin.ext e)
         have h0:(decide (a.val<=k)&&(1:Nat).testBit (k - a.val))=false:=by
          cases j:decide (a.val<=k)
          . simp
          . have j':a.val<=k:=of_decide_eq_true j;simp[qp (by omega:k - a.val≠0)]
         simp[c,h0]
     . have z:a.val < k:=(by omega);simp[b,qp (by omega:k - a.val≠0)]
   . simp only[d,jV,↓reduceIte,g];by_cases b:k < n
     . simp only[b,↓reduceDIte,kC];by_cases c:(⟨k,b⟩:Fin n)=a
       . rw[c];simp[v,d]
       . simp[c]
     . simp[b]
 have h:=s (finRange n) (List.nodup_finRange n);simpa[ur,jG] using h
lemma vf {n:Nat}(x:F n):ur x < 2 ^ n:=by
 apply jB
 intro k hk;rw[jl]
 simp[show ¬k < n by omega]
lemma q57 {n:Nat}(x:F n):q1 n (ur x)=x:=by funext i;simp[q1,jl,i.isLt]
def s8 {n:Nat}(b:M)(f:Z n):Nat:=
 b.foldr (fun r acc=>acc*2+if f (q1 n r) then 1 else 0) 0
def u9 (n:Nat)(f:Z n):Nat:=s8 (range (2 ^ n)) f
lemma z8 {n:Nat}(c:M)(f:Z n)(i:Nat):(s8 c f).testBit i=match c[i]? with | some r=>f (q1 n r) | none=>false:=by
 induction c generalizing i with
 | nil=>simp[s8]
 | cons r b ih =>
  have d:s8 (r::b) f=s8 b f*2+if f (q1 n r) then 1 else 0:=rfl
  rw[d]
  cases i with
  | zero=>cases h:f (q1 n r)<;>simp[h,Nat.testBit_zero]
  | succ k =>
   rw[Nat.testBit_succ]
   have e:(s8 b f*2+if f (q1 n r) then 1 else 0) / 2=s8 b f:=(by cases h:f (q1 n r)<;>simp only[h,↓reduceIte,jV]<;>omega);rw[e]
   exact ih k
lemma im {n:Nat}(b:M):s8 (n:=n) b (fun _=>false)=0:=by apply kL;intro i;rw[z8];cases b[i]?<;>simp
lemma rf {n:Nat}(b:M):s8 (n:=n) b (fun _=>true)=2 ^ b.length - 1:=by
 apply kL;intro i;rw[z8,kK]
 by_cases hi:i < b.length
 . rw[jK hi];simp[hi]
 . rw[mZ (by omega)];simp[hi]
lemma ix {n:Nat}(b:M)(f:Z n):s8 b (hC f)=xor (s8 b f) (2 ^ b.length - 1):=by
 apply kL;intro i;rw[kT,kP,z8,z8,kK]
 by_cases hi:i < b.length
 . rw[jK hi];simp[hi,hC]
 . rw[mZ (by omega)];simp[hi]
lemma xh {n:Nat}(b:M)(f g:Z n):s8 b (hE f g)=land (s8 b f) (s8 b g):=by
 apply kL;intro i;rw[kS,kN,z8,z8,z8]
 cases b[i]?<;>simp[hE]
lemma xg {n:Nat}(b:M)(f g:Z n):s8 b (hG f g)=lor (s8 b f) (s8 b g):=by
 apply kL;intro i;rw[kR,kM,z8,z8,z8]
 cases b[i]?<;>simp[hG]
lemma vr {n:Nat}(f:Z n)(r:Nat):(u9 n f).testBit r=if r < 2 ^ n then f (q1 n r) else false:=by
 unfold u9;rw[z8]
 by_cases b:r < 2 ^ n
 . rw[jK (by simp[b])];simp[b]
 . rw[mZ (by simp;omega)];simp[b]
lemma yc {n:Nat}:Injective (u9 n):=by intro f g h;funext x;have b:=congrArg (fun m=>m.testBit (ur x)) h;rw[vr,vr] at b;simp only[vf x,↓reduceIte,q57] at b;exact b
lemma cy {n:Nat}(b:M)(f:Z n):shiftRight (s8 (b++range (2 ^ n)) f) b.length=u9 n f:=by
 apply kL;intro i;change ((s8 (b++range (2 ^ n)) f) >>> b.length).testBit i=(u9 n f).testBit i;rw[Nat.shiftRight_eq_div_pow,Nat.testBit_div_two_pow,z8,vr]
 rw[mY (by omega),nR]
 by_cases hi:i < 2 ^ n
 . rw[jK (by simp[hi])];simp[hi]
 . rw[mZ (by simp;omega)];simp[hi]
lemma nz {n:Nat}(b:M):Injective (s8 (n:=n) (b++range (2 ^ n))):=by
 intro f g h;apply yc
 rw[<- cy b f,<- cy b g,h]
def yh {n:Nat}(i j:Fin n)(x:F n):F n:=
 fun k=>x (if k=i then j else if k=j then i else k)
lemma yd {n:Nat}(i j:Fin n)(x:F n):yh i j (yh i j x)=x:=by
 funext k;unfold yh;by_cases c:k=i
 . rw[c];by_cases b:j=i<;>simp[b]
 . by_cases b:k=j
   . rw[b];simp[Ne.symm c]
   . simp[c,b]
def yu (i j r:Nat):Nat:=
 let b:=r.testBit i
 let c:=r.testBit j
 if b==c then r else xor r (lor (1 <<< i) (1 <<< j))
lemma wk {n i j r:Nat}(hi:i < n)(hj:j < n)(b:r < 2 ^ n):yu i j r < 2 ^ n:=by
 unfold yu;dsimp only
 split
 . exact b
 . apply jB
   intro k c;rw[kT,kP,kR,kM,nN,nN]
   have d:r.testBit k=false:=Nat.testBit_lt_two_pow (lt_of_lt_of_le b (jA (by omega) c));simp[d,qp (by omega:k - i≠0),qp (by omega:k - j≠0)]
lemma z9 {n i j r:Nat}(hi:i < n)(g:j < n):q1 n (yu i j r)=yh ⟨i,hi⟩ ⟨j,g⟩ (q1 n r):=by
 funext k;simp only[q1,yh,yu];by_cases d:r.testBit i=r.testBit j
 . simp only[d,beq_self_eq_true,↓reduceIte];by_cases b:k=⟨i,hi⟩
   . rw[b];simp[d]
   . by_cases c:k=⟨j,g⟩
     . rw[c];split<;>simp[d]
     . simp[b,c]
 . have v:(r.testBit i==r.testBit j)=false:=beq_false_of_ne d;simp only[v,jV,↓reduceIte,kT,kP,kR,kM,nN];by_cases b:k=⟨i,hi⟩
   . subst b;simp only[↓reduceIte,Nat.le_refl,decide_true,Nat.sub_self,Nat.testBit_one_zero];cases h:r.testBit i<;>cases s:r.testBit j<;>simp_all
   . by_cases c:k=⟨j,g⟩
     . subst c;simp only[b,↓reduceIte,Nat.le_refl,decide_true,Nat.sub_self,Nat.testBit_one_zero];cases h:r.testBit i<;>cases s:r.testBit j<;>simp_all
     . have h:k.val≠i:=fun e=>b (Fin.ext e)
       have s:k.val≠j:=fun e=>c (Fin.ext e)
       have t:∀m,k.val≠m->(decide (m<=k.val)&&(1:Nat).testBit (k.val - m))=false:=by
        intro m hne;cases u:decide (m<=k.val)
        . simp
        . have u':m<=k.val:=of_decide_eq_true u;simp[qp (by omega:k.val - m≠0)]
       simp[b,c,t i h,t j s]
def w9 (n i j:Nat):Nat×Nat×Nat×Nat:=
 let d:=2 ^ j - 2 ^ i
 let N:=2 ^ n
 let b:=(range N).foldr (fun x acc=>acc*2+if !(x.testBit i)&&x.testBit j then 1 else 0) 0
 let c:=(range N).foldr (fun x acc=>acc*2+if x.testBit i&&!(x.testBit j) then 1 else 0) 0
 let e:=(range N).foldr (fun x acc=>acc*2+if x.testBit i==x.testBit j then 1 else 0) 0
 (d,b,c,e)
lemma jx (N:Nat)(P:Nat->Q)(r:Nat):((range N).foldr (fun x acc=>acc*2+if P x then 1 else 0) 0).testBit r=if r < N then P r else false:=by
 have c:∀(l:M) (r:Nat),
    (l.foldr (fun x acc=>acc*2+if P x then 1 else 0) 0).testBit r =
    match l[r]? with | some x=>P x | none=>false:=by
   intro l;induction l with
   | nil=>intro r;simp
   | cons a t ih =>
    intro r;simp only[kG];cases r with
    | zero=>cases h:P a<;>simp[h,Nat.testBit_zero]
    | succ k =>
     rw[Nat.testBit_succ]
     have d:((t.foldr (fun x acc=>acc*2+if P x then 1 else 0) 0)*2+if P a then 1 else 0) / 2
       = t.foldr (fun x acc=>acc*2+if P x then 1 else 0) 0:=by
      cases P a<;>simp only[↓reduceIte,jV]<;>omega
     rw[d];exact ih k
 rw[c]
 by_cases b:r < N
 . rw[jK (by simp[b])];simp[b]
 . rw[mZ (by simp;omega)];simp[b]
lemma j3 {n i j:Nat}(h6:i < j)(s:j < n)(g:Z n):pa (w9 n i j) (u9 n g)=u9 n (fun x=>g (yh ⟨i,by omega⟩ ⟨j,s⟩ x)):=by
 have hi:i < n:=by omega
 have hpow:2 ^ i < 2 ^ j:=Nat.pow_lt_pow_right (by omega) h6;have hc:∀x m,x.testBit m=true->x - 2 ^ m+2 ^ m=x/\(x - 2 ^ m).testBit m=false:=by
   intro x m hm;have h:2 ^ m<=x:=zg hm;refine⟨nQ h,?_⟩
   rw[nT]
   have hd:(x - 2 ^ m) / 2 ^ m=x / 2 ^ m - 1:=(by have u:x=(x - 2 ^ m)+2 ^ m:=(nQ h).symm;have t:((x - 2 ^ m)+2 ^ m) / 2 ^ m=(x - 2 ^ m) / 2 ^ m+1:=Nat.add_div_right (x - 2 ^ m) (mL m);rw[<- u] at t;rw[t];simp);have c3:=z7 hm;rw[hd];simp;generalize x / 2 ^ m=q at c3 ⊢;omega
 have hw:∀(a b:Nat),a < b->b < n->∀x < 2 ^ n,
     (x.testBit a=false->x.testBit b=true->x - (2 ^ b - 2 ^ a)=yu a b x) /\
     (x.testBit a=true->x.testBit b=false->x+(2 ^ b - 2 ^ a)=yu a b x):=by
   intro a b d1 hbn x _;have he:2 ^ a < 2 ^ b:=Nat.pow_lt_pow_right (by omega) d1;have b0:∀(m k:Nat),(decide (m<=k)&&(1:Nat).testBit (k - m))=decide (m=k):=by
     intro m k;by_cases d2:m=k
     . subst d2;simp
     . cases h:decide (m<=k)
       . simp[d2]
       . have h':m<=k:=of_decide_eq_true h;simp[d2,qp (by omega:k - m≠0)]
   constructor
   . intro hf hg;have⟨h4,h7⟩:=hc x b hg;have hx:(x - 2 ^ b).testBit a=false:=by have t:=qs h7;rw[h4] at t;have h5:=congrArg (fun z=>z.testBit a) t;rw[kP,nW,hf] at h5;have hy:b≠a:=(by omega);simp[hy] at h5;exact h5
     have t:x - (2 ^ b - 2 ^ a)=(x - 2 ^ b)+2 ^ a:=by
       conv_lhs=>rw[<- h4]
       rw[Nat.add_sub_assoc (Nat.sub_le _ _),Nat.sub_sub_self (le_of_lt he)]
     rw[t]
     apply kL;intro k;have u:x=(x - 2 ^ b)^^^2 ^ b:=by rw[<- qs h7,h4]
     have h3:(x - 2 ^ b)+2 ^ a=(x - 2 ^ b)^^^2 ^ a:=qs hx;unfold yu;dsimp only;simp only[hf,hg];change ((x - 2 ^ b)+2 ^ a).testBit k=(xor x (lor (1 <<< a) (1 <<< b))).testBit k;rw[h3]
     conv_rhs=>rw[u]
     rw[kT,kR,kP,kP,kP,kM,nN,nN,nW,nW,b0 a k,b0 b k]
     by_cases h8:a=k<;>by_cases h9:b=k<;>try omega
     . subst h8;simp[show b≠a by omega]
     . subst h9;simp[show a≠b by omega]
     . simp[h8,h9]
   . intro hh hj;have⟨h4,h7⟩:=hc x a hh;have xi:(x - 2 ^ a).testBit b=false:=by have t:=qs h7;rw[h4] at t;have h5:=congrArg (fun z=>z.testBit b) t;rw[kP,nW,hj] at h5;have d1':a≠b:=(by omega);simp[d1'] at h5;exact h5
     have t:x+(2 ^ b - 2 ^ a)=(x - 2 ^ a)+2 ^ b:=by
       conv_lhs=>rw[<- h4]
       rw[mG,Nat.add_sub_cancel' (le_of_lt he)]
     rw[t]
     apply kL;intro k;have u:x=(x - 2 ^ a)^^^2 ^ a:=by rw[<- qs h7,h4]
     have h3:(x - 2 ^ a)+2 ^ b=(x - 2 ^ a)^^^2 ^ b:=qs xi;unfold yu;dsimp only;simp only[hh,hj];change ((x - 2 ^ a)+2 ^ b).testBit k=(xor x (lor (1 <<< a) (1 <<< b))).testBit k;rw[h3]
     conv_rhs=>rw[u]
     rw[kT,kR,kP,kP,kP,kM,nN,nN,nW,nW,b0 a k,b0 b k]
     by_cases h8:a=k<;>by_cases h9:b=k<;>try omega
     . subst h8;simp[show b≠a by omega]
     . subst h9;simp[show a≠b by omega]
     . simp[h8,h9]
 have hn:(2 ^ (j - i) - 1) % 2=1:=by have hp:1<=j - i:=(by omega);have hev:2 ^ (j - i) % 2=0:=(by obtain⟨m,hm⟩:=Nat.exists_eq_add_of_le' hp;rw[hm,Nat.pow_succ];omega);have xs:2<=2 ^ (j - i):=(by have:=jA (by omega:0 < 2) hp;simpa using this);omega
 have hs:∀r,(r+(2 ^ j - 2 ^ i)).testBit i=!(r.testBit i):=by
   intro r;have b1:2 ^ j - 2 ^ i=2 ^ i*(2 ^ (j - i) - 1):=by rw[Nat.mul_sub,Nat.mul_one,<- Nat.pow_add,Nat.add_sub_cancel' (le_of_lt h6)]
   have u:(r+(2 ^ j - 2 ^ i)) / 2 ^ i=r / 2 ^ i+(2 ^ (j - i) - 1):=(by rw[b1,Nat.mul_comm,Nat.add_mul_div_right _ _ (mL i)]);rw[nT,nT,u]
   generalize r / 2 ^ i=q;generalize 2 ^ (j - i) - 1=c at hn ⊢
   cases hq:decide (q % 2=1)
   . have:q % 2=0:=by have:=of_decide_eq_false hq;omega
     simp;omega
   . have:q % 2=1:=of_decide_eq_true hq
     simp;omega
 have e0:∀r,2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit i=!(r.testBit i):=by
   intro r h;have b1:2 ^ j - 2 ^ i=2 ^ i*(2 ^ (j - i) - 1):=by rw[Nat.mul_sub,Nat.mul_one,<- Nat.pow_add,Nat.add_sub_cancel' (le_of_lt h6)]
   have u:(r - (2 ^ j - 2 ^ i)) / 2 ^ i=r / 2 ^ i - (2 ^ (j - i) - 1):=by
     have t:r=(r - (2 ^ j - 2 ^ i))+(2 ^ j - 2 ^ i):=(nQ h).symm;have h3:((r - (2 ^ j - 2 ^ i))+2 ^ i*(2 ^ (j - i) - 1)) / 2 ^ i
         = (r - (2 ^ j - 2 ^ i)) / 2 ^ i+(2 ^ (j - i) - 1):=by
       rw[Nat.mul_comm (2 ^ i),Nat.add_mul_div_right _ _ (mL i)]
     rw[<- b1,<- t] at h3;rw[h3,nR]
   have b3:2 ^ (j - i) - 1<=r / 2 ^ i:=(by rw[b1] at h;exact (Nat.le_div_iff_mul_le (mL i)).2 (by rw[Nat.mul_comm];exact h));rw[nT,nT,u]
   generalize r / 2 ^ i=q at b3 ⊢;generalize 2 ^ (j - i) - 1=c at hn b3 ⊢
   cases hq:decide (q % 2=1)
   . have:q % 2=0:=by have:=of_decide_eq_false hq;omega
     simp;omega
   . have:q % 2=1:=of_decide_eq_true hq
     simp;omega
 have f2:∀(x d k:Nat),(shiftLeft x d).testBit k=(decide (d<=k)&&x.testBit (k - d)):=by intro x d k;change (x <<< d).testBit k=_;rw[nN]
 apply kL
 intro r;unfold pa w9;simp only[kR,kS,Nat.shiftRight_eq,Nat.shiftRight_eq_div_pow,kM,kN,Nat.testBit_div_two_pow,f2,jx,vr];by_cases hr:r < 2 ^ n
 . simp only[hr,↓reduceIte];have ht:=hw i j h6 s r hr;cases v:r.testBit i<;>cases y:r.testBit j
   .
     have g0:yh ⟨i,hi⟩ ⟨j,s⟩ (q1 n r)=q1 n r:=(by rw[<- z9 hi s];unfold yu;simp[v,y]);rw[g0]
     have g1:(r+(2 ^ j - 2 ^ i)).testBit i=true:=(by rw[hs,v];rfl);have x2:2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit i=true:=(by intro h;rw[e0 r h,v];rfl);have e1:2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit j=true:=by
       intro h;have u:(r - (2 ^ j - 2 ^ i))+2 ^ j=r+2 ^ i:=by omega
       have b3:1<=r / 2 ^ j:=by
         have g2:r / 2 ^ j≠0:=by
          intro hz;have hu:r < 2 ^ j:=(Nat.div_eq_zero_iff.1 hz).resolve_left (Nat.ne_of_gt (mL j));have x3:r - (2 ^ j - 2 ^ i) < 2 ^ i:=by omega
          have g3:(r - (2 ^ j - 2 ^ i)).testBit i=false:=Nat.testBit_lt_two_pow x3
          have:=x2 h;rw[g3] at this;cases this
         generalize r / 2 ^ j=q at g2 ⊢;omega
       have g4:(r - (2 ^ j - 2 ^ i)) / 2 ^ j=r / 2 ^ j - 1:=by
         have t:(r+2 ^ i) / 2 ^ j=r / 2 ^ j:=by
          have j0:r % 2 ^ j+2 ^ i < 2 ^ j:=by
           have hm0:(r % 2 ^ j).testBit i=false:=(by rw[Nat.testBit_mod_two_pow];simp[h6,v]);have j1:r % 2 ^ j < 2 ^ j:=Nat.mod_lt r (mL j);apply jB;intro k hk;rw[vk hm0]
           have m2:k≠i:=(by omega);simp only[m2,↓reduceIte];exact Nat.testBit_lt_two_pow (lt_of_lt_of_le j1 (jA (by omega) hk))
          have hv:r=2 ^ j*(r / 2 ^ j)+r % 2 ^ j:=(Nat.div_add_mod r (2 ^ j)).symm;conv_lhs=>rw[hv,mG]
          rw[Nat.mul_add_div (mL j),Nat.div_eq_of_lt j0,mH]
         have h3:((r - (2 ^ j - 2 ^ i))+2 ^ j) / 2 ^ j=(r - (2 ^ j - 2 ^ i)) / 2 ^ j+1:=Nat.add_div_right _ (mL j);rw[u,t] at h3;omega
       have m3:=z5 y;rw[nT,g4];simp
       generalize r / 2 ^ j=q at b3 m3 ⊢;omega
     have a1:((if r+(2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r+(2 ^ j - 2 ^ i))) else false)&&(if r+(2 ^ j - 2 ^ i) < 2 ^ n then !((r+(2 ^ j - 2 ^ i)).testBit i)&&(r+(2 ^ j - 2 ^ i)).testBit j else false))=false:=(by split<;>simp[g1]);have a2:(decide (2 ^ j - 2 ^ i<=r)&&((if r - (2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r - (2 ^ j - 2 ^ i))) else false)&&(if r - (2 ^ j - 2 ^ i) < 2 ^ n then (r - (2 ^ j - 2 ^ i)).testBit i&&!((r - (2 ^ j - 2 ^ i)).testBit j) else false)))=false:=by
       by_cases h:2 ^ j - 2 ^ i<=r
       . simp[h,show r - (2 ^ j - 2 ^ i) < 2 ^ n by omega,e1 h]
       . simp[h]
     rw[a1,a2];simp
   .
     have p0:2 ^ j<=r:=zg y;have h:2 ^ j - 2 ^ i<=r:=le_trans (Nat.sub_le _ _) p0;have h0:r - (2 ^ j - 2 ^ i)=yu i j r:=ht.1 v y;have e2:r - (2 ^ j - 2 ^ i) < 2 ^ n:=(by omega);have ha:(r - (2 ^ j - 2 ^ i)).testBit i=true:=by
       rw[h0];have:=congrFun (z9 hi s (r:=r)) ⟨i,hi⟩
       simpa[q1,yh,y] using this
     have hb:(r - (2 ^ j - 2 ^ i)).testBit j=false:=by
       rw[h0];have:=congrFun (z9 hi s (r:=r)) ⟨j,s⟩
       simpa[q1,yh,show (⟨j,s⟩:Fin n)≠⟨i,hi⟩ by intro e;have:=congrArg Fin.val e;simp at this;omega,v] using this
     have p1:(r+(2 ^ j - 2 ^ i)).testBit i=true:=(by rw[hs,v];rfl);have a1:((if r+(2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r+(2 ^ j - 2 ^ i))) else false)&&(if r+(2 ^ j - 2 ^ i) < 2 ^ n then !((r+(2 ^ j - 2 ^ i)).testBit i)&&(r+(2 ^ j - 2 ^ i)).testBit j else false))=false:=(by split<;>simp[p1]);rw[a1]
     simp[h,e2,ha,hb]
     rw[h0,z9 hi s]
   .
     have h0:r+(2 ^ j - 2 ^ i)=yu i j r:=ht.2 v y;have e2:r+(2 ^ j - 2 ^ i) < 2 ^ n:=(by rw[h0];exact wk hi s hr);have ha:(r+(2 ^ j - 2 ^ i)).testBit i=false:=by
       rw[h0];have:=congrFun (z9 hi s (r:=r)) ⟨i,hi⟩
       simpa[q1,yh,y] using this
     have hb:(r+(2 ^ j - 2 ^ i)).testBit j=true:=by
       rw[h0];have:=congrFun (z9 hi s (r:=r)) ⟨j,s⟩
       simpa[q1,yh,show (⟨j,s⟩:Fin n)≠⟨i,hi⟩ by intro e;have:=congrArg Fin.val e;simp at this;omega,v] using this
     have x2:2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit i=false:=(by intro h;rw[e0 r h,v];rfl);have a2:(decide (2 ^ j - 2 ^ i<=r)&&((if r - (2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r - (2 ^ j - 2 ^ i))) else false)&&(if r - (2 ^ j - 2 ^ i) < 2 ^ n then (r - (2 ^ j - 2 ^ i)).testBit i&&!((r - (2 ^ j - 2 ^ i)).testBit j) else false)))=false:=by
       by_cases h:2 ^ j - 2 ^ i<=r
       . simp[h,show r - (2 ^ j - 2 ^ i) < 2 ^ n by omega,x2 h]
       . simp[h]
     rw[a2]
     simp[e2,ha,hb]
     rw[h0,z9 hi s]
   .
     have r2:yh ⟨i,hi⟩ ⟨j,s⟩ (q1 n r)=q1 n r:=(by rw[<- z9 hi s];unfold yu;simp[v,y]);rw[r2]
     have r3:(r+(2 ^ j - 2 ^ i)).testBit j=false:=by
       have hle_i:2 ^ i<=r:=zg v;have r4:(r - 2 ^ i) / 2 ^ j=r / 2 ^ j:=(by have c3:(r % 2 ^ j).testBit i=true:=(by rw[Nat.testBit_mod_two_pow];simp[h6,v]);have hmod_i:2 ^ i<=r % 2 ^ j:=zg c3;have hv:r=2 ^ j*(r / 2 ^ j)+r % 2 ^ j:=(Nat.div_add_mod r (2 ^ j)).symm;have r5:r - 2 ^ i=2 ^ j*(r / 2 ^ j)+(r % 2 ^ j - 2 ^ i):=(by omega);have hu:r % 2 ^ j - 2 ^ i < 2 ^ j:=lt_of_le_of_lt (Nat.sub_le _ _) (Nat.mod_lt r (mL j));rw[r5,Nat.mul_add_div (mL j),Nat.div_eq_of_lt hu,mH]);have u:r+(2 ^ j - 2 ^ i)=(r - 2 ^ i)+2 ^ j:=(by omega);rw[nT,u,Nat.add_div_right _ (mL j),r4]
       have hr1:=z7 y;simp;omega
     have x2:2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit i=false:=(by intro h;rw[e0 r h,v];rfl);have a1:((if r+(2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r+(2 ^ j - 2 ^ i))) else false)&&(if r+(2 ^ j - 2 ^ i) < 2 ^ n then !((r+(2 ^ j - 2 ^ i)).testBit i)&&(r+(2 ^ j - 2 ^ i)).testBit j else false))=false:=(by split<;>simp[r3]);have a2:(decide (2 ^ j - 2 ^ i<=r)&&((if r - (2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r - (2 ^ j - 2 ^ i))) else false)&&(if r - (2 ^ j - 2 ^ i) < 2 ^ n then (r - (2 ^ j - 2 ^ i)).testBit i&&!((r - (2 ^ j - 2 ^ i)).testBit j) else false)))=false:=by
       by_cases h:2 ^ j - 2 ^ i<=r
       . simp[h,show r - (2 ^ j - 2 ^ i) < 2 ^ n by omega,x2 h]
       . simp[h]
     rw[a1,a2];simp
 .
   have c2:¬(r+(2 ^ j - 2 ^ i) < 2 ^ n):=(by omega);simp only[hr,c2,↓reduceIte,nJ,nK];by_cases h:2 ^ j - 2 ^ i<=r
   . by_cases x3:r - (2 ^ j - 2 ^ i) < 2 ^ n
     . have e1:(r - (2 ^ j - 2 ^ i)).testBit j=true:=by
         have hge_q:2 ^ (n - j) - 1<=(r - (2 ^ j - 2 ^ i)) / 2 ^ j:=(by have u:2 ^ j*(2 ^ (n - j) - 1)=2 ^ n - 2 ^ j:=(by rw[Nat.mul_sub,Nat.mul_one,<- Nat.pow_add,Nat.add_sub_cancel' (le_of_lt s)]);have t:2 ^ n - 2 ^ j<=r - (2 ^ j - 2 ^ i):=le_trans (Nat.sub_le_sub_left (Nat.sub_le _ _) _) (Nat.sub_le_sub_right (by omega:2 ^ n<=r) _);exact (Nat.le_div_iff_mul_le (mL j)).2 (by rw[Nat.mul_comm,u];exact t));have hlt_q:(r - (2 ^ j - 2 ^ i)) / 2 ^ j < 2 ^ (n - j):=(by have u:2 ^ n=2 ^ j*2 ^ (n - j):=(by rw[<- Nat.pow_add,Nat.add_sub_cancel' (le_of_lt s)]);exact (Nat.div_lt_iff_lt_mul (mL j)).2 (by rw[Nat.mul_comm,<- u];exact x3));have s2:(r - (2 ^ j - 2 ^ i)) / 2 ^ j=2 ^ (n - j) - 1:=(by omega);rw[nT,s2]
         have c2' : 1<=n - j:=(by omega);have hev:2 ^ (n - j) % 2=0:=(by obtain⟨m,hm⟩:=Nat.exists_eq_add_of_le' c2';rw[hm,Nat.pow_succ];omega);have xs:2<=2 ^ (n - j):=(by have:=jA (by omega:0 < 2) c2';simpa using this);simp;omega
       simp[h,x3,e1]
     . simp[h,x3]
   . simp[h]
def mw (n:Nat)(b:J):V:=
 b.map fun p=>w9 n p.1 p.2
def kq (n:Nat)(b:J):Q:=
 b.all fun p=>decide (p.1 < p.2)&&decide (p.2 < n)
def zc {n:Nat}:J->(F n)->(F n)
 | [],x=>x
 | (i,j)::rest,x =>
  if h:i < n/\j < n then yh ⟨i,h.1⟩ ⟨j,h.2⟩ (zc rest x)
  else zc rest x
lemma wv {n:Nat}(c:J)(x:F n):zc c.reverse (zc c x)=x:=by
 have d:∀(a b:J) (y:F n),
    zc (a++b) y=zc a (zc b y):=by
  intro a;induction a with
  | nil=>intro b y;rfl
  | cons p t ih =>
    intro b y;rcases p with ⟨i,j⟩
    simp only[kZ,zc];split<;>rw[ih]
 induction c generalizing x with
 | nil=>rfl
 | cons p t ih =>
  rcases p with ⟨i,j⟩
  simp only[kF,d,zc]
  split
  . rename_i h
    rw[yd,ih]
  . exact ih x
lemma jm {n:Nat}(b:J)(c:kq n b=true)(g:Z n):ym (mw n b) (u9 n g)=u9 n (fun x=>g (zc b x)):=by
 induction b generalizing g with
 | nil=>rfl
 | cons p d ih =>
  rcases p with ⟨i,j⟩
  simp only[kq,List.all_cons,jY,decide_eq_true_eq] at c;obtain⟨⟨e,h⟩,s⟩:=c;change ym (w9 n i j::mw n d) (u9 n g)=_;simp only[ym];rw[j3 e h g,ih s]
  congr 1;funext x;have hlt:i < n/\j < n:=by omega
  simp only[zc]
  split
  . rfl
  . contradiction
def vh {n:Nat}(f:Z n)(b:V):Prop:=
 ∃π:(F n)->(F n),
  Bijective π/\(∀x,f (π x)=f x) /\
  ∀g:Z n,ym b (u9 n g)=u9 n (fun x=>g (π x))
lemma kw {n:Nat}(f:Z n)(b:J)(c:kq n b=true) (d:ym (mw n b) (u9 n f)=u9 n f):vh f (mw n b):=by
 refine⟨zc b,?_,?_,fun g=>jm b c g⟩
 . constructor
   . intro x y h
     have:=congrArg (zc b.reverse) h
     simpa[wv] using this
   . intro y;refine⟨zc b.reverse y,?_⟩
     have:=wv b.reverse y
     simpa using this
 . intro x;rw[jm b c f] at d;exact congrFun (yc d) x
lemma xm {n:Nat}(f:Z n):vh f []:=
 ⟨id,bijective_id,fun _=>rfl,fun _=>rfl⟩
lemma wp {n:Nat}{f:Z n}{s:Nat}{b:X n} (π:(F n)->(F n)) (c:Bijective π) (d:∀x,f (π x)=f x) (h:gV (hC (n:=n)) hE hG (fun _=>false) (fun _=>true) f s b):gV (hC (n:=n)) hE hG (fun _=>false) (fun _=>true) f s (b.map fun p=>((fun x=>p.1 (π x)),p.2)):=by
 let φ:Z n->Z n:=fun g x=>g (π x)
 have hφ:Injective φ:=by intro g1 g2 e;funext y;obtain⟨x,rfl⟩:=c.2 y;exact congrFun e x
 exact @gV.map (Z n) (Z n) φ hφ
  hC hE hG (fun _=>false) (fun _=>true) f
  hC hE hG (fun _=>false) (fun _=>true) f
  rfl rfl (funext d) (fun _=>rfl) (fun _ _=>rfl) (fun _ _=>rfl) s b h
def z6 (x i:Nat):Nat:=(x / 64 ^ i) % 64
lemma qf (i:Nat):64 ^ i=2 ^ (6*i):=by rw[show (64:Nat)=2 ^ 6 by decide,<- Nat.pow_mul]
lemma qo (x i k:Nat):(z6 x i).testBit k=if k < 6 then x.testBit (6*i+k) else false:=by
 unfold z6;rw[qf,show (64:Nat)=2 ^ 6 by decide,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
 by_cases b:k < 6
 . simp[b,mF]
 . simp[b]
lemma wg {x y:Nat}(h:∀i,z6 x i=z6 y i):x=y:=by apply kL;intro k;have b:=congrArg (fun z=>z.testBit (k % 6)) (h (k / 6));have c:k % 6 < 6:=Nat.mod_lt k (by decide);rw[qo,qo] at b;simp only[c,↓reduceIte,Nat.div_add_mod] at b;exact b
lemma z1 (x i:Nat):z6 (x / 64) i=z6 x (i+1):=by unfold z6;rw[Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm (64 ^ i) 64]
lemma q24:∀{x y:Nat},(∀i,z6 y i<=z6 x i)->y<=x:=by
 intro x y h;induction hn:x+y using Nat.strong_induction_on generalizing x y with
 | _ n ih =>
  have h0:y % 64<=x % 64:=(by simpa[z6] using h 0);by_cases hq:x / 64+y / 64 < x+y
  . have hdiv:y / 64<=x / 64:=ih (x / 64+y / 64) (by omega) (fun i=>by rw[z1,z1];exact h (i+1)) rfl;omega
  . omega
lemma iq {x y:Nat}(h:∀j,z6 x j+z6 y j < 64)(i:Nat):z6 (x+y) i=z6 x i+z6 y i:=by
 induction i generalizing x y with
 | zero=>have b:x % 64+y % 64 < 64:=(by simpa[z6] using h 0);simp only[z6,Nat.pow_zero,Nat.div_one];omega
 | succ i ih =>
  have b:x % 64+y % 64 < 64:=(by simpa[z6] using h 0);have c:(x+y) / 64=x / 64+y / 64:=(by omega);rw[<- z1,c,<- z1,<- z1]
  exact ih (fun j=>by rw[z1,z1];exact h (j+1))
lemma pz {x y:Nat}(h:∀j,z6 y j<=z6 x j)(i:Nat):z6 (x - y) i=z6 x i - z6 y i:=by
 induction i generalizing x y with
 | zero=>have b:y % 64<=x % 64:=(by simpa[z6] using h 0);have c:y<=x:=q24 h;simp only[z6,Nat.pow_zero,Nat.div_one];omega
 | succ i ih =>
  have b:y % 64<=x % 64:=(by simpa[z6] using h 0);have c:y<=x:=q24 h;have d:(x - y) / 64=x / 64 - y / 64:=(by omega);rw[<- z1,d,<- z1,<- z1]
  exact ih (fun j=>by rw[z1,z1];exact h (j+1))
lemma v9 (x y i:Nat):z6 (land x y) i=land (z6 x i) (z6 y i):=by
 apply kL;intro k;rw[kS,kS,kN,qo,qo,qo]
 by_cases b:k < 6<;>simp[b,kN]
lemma wb (x y i:Nat):z6 (lor x y) i=lor (z6 x i) (z6 y i):=by
 apply kL;intro k;rw[kR,kR,kM,qo,qo,qo]
 by_cases b:k < 6<;>simp[b,kM]
lemma rj (x y i:Nat):z6 (xor x y) i=xor (z6 x i) (z6 y i):=by
 apply kL;intro k;rw[kT,kT,kP,qo,qo,qo]
 by_cases b:k < 6<;>simp[b,kP]
def qe (m e5:Nat):Nat:=
 match m with
 | 0=>0
 | m'+1=>e5+64*qe m' e5
lemma v0 (m e5 i:Nat)(hv:e5 < 64):z6 (qe m e5) i=if i < m then e5 else 0:=by
 induction m generalizing i with
 | zero=>simp[qe,z6]
 | succ m ih =>
  cases i with
  | zero=>simp only[qe,z6,Nat.pow_zero,Nat.div_one,Nat.zero_lt_succ,↓reduceIte];omega
  | succ k =>
   rw[<- z1]
   have b:qe (m+1) e5 / 64=qe m e5:=(by simp only[qe];omega);rw[b,ih k]
   by_cases h:k < m<;>simp[h,show k+1 < m+1↔k < m by omega]
def v6 (a b c d e f:Q):Nat:=
 let g:=!d;let h:=!e;let i:=!f
 (if g&&b then 1 else 0)+(if g&&c then 1 else 0) +
 (if a&&h then 1 else 0)+(if a&&i then 1 else 0) -
 (if (a&&g)&&((b||c)&&(h||i)) then 1 else 0)
def zq (a b c d e f:Q):Nat:=
 max (v6 a b c d e f) (v6 (!a) (!b) (!c) (!d) (!e) (!f))
lemma xp:v6 true true true false false false=3:=by decide
lemma yr:∀a b c d e f:Q,v6 a b c d e f<=3:=by decide
lemma q52:∀a b c d e f:Q,zq a b c d e f<=3:=by decide
lemma k7:∀a b c d e f:Q,v6 a b c d e f<=zq a b c d e f:=by decide
lemma jp:∀a b c d e f:Q,zq (!a) (!b) (!c) (!d) (!e) (!f)=zq a b c d e f:=by decide
lemma w4:∀a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2:Q,v6 (a1||a2) (b1||b2) (c1||c2) (d1||d2) (e1||e2) (f1||f2)<=v6 a1 b1 c1 d1 e1 f1+v6 a2 b2 c2 d2 e2 f2:=by decide
lemma kl:∀a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2:Q,v6 (a1&&a2) (b1&&b2) (c1&&c2) (d1&&d2) (e1&&e2) (f1&&f2)<=v6 a1 b1 c1 d1 e1 f1+v6 a2 b2 c2 d2 e2 f2:=by decide
lemma q14 (b c c1 d e f1 g b2 h i j s:Q):zq (b||g) (c||b2) (c1||h) (d||i) (e||j) (f1||s)<=zq b c c1 d e f1+zq g b2 h i j s:=by unfold zq;have h1:=w4 b c c1 d e f1 g b2 h i j s;have h2:=kl (!b) (!c) (!c1) (!d) (!e) (!f1) (!g) (!b2) (!h) (!i) (!j) (!s);simp only[Bool.not_or];omega
lemma je (b c c1 d e f1 g b2 h i j s:Q):zq (b&&g) (c&&b2) (c1&&h) (d&&i) (e&&j) (f1&&s)<=zq b c c1 d e f1+zq g b2 h i j s:=by unfold zq;have h1:=kl b c c1 d e f1 g b2 h i j s;have h2:=w4 (!b) (!c) (!c1) (!d) (!e) (!f1) (!g) (!b2) (!h) (!i) (!j) (!s);simp only[Bool.not_and];omega
lemma wc (w s m i:Nat):z6 (land (shiftRight w s) (qe m 1)) i=if i < m then (if w.testBit (6*i+s) then 1 else 0) else 0:=by
 rw[v9,v0 m 1 i (by decide)]
 by_cases hi:i < m
 . simp only[hi,↓reduceIte];apply kL;intro k;rw[kS,kN,qo]
   cases k with
   | zero =>
    simp only[Nat.zero_lt_succ,↓reduceIte,mH,Nat.testBit_one_zero,hV];change (w >>> s).testBit (6*i)=_;rw[kQ,mF s (6*i)]
    cases h:w.testBit (6*i+s)<;>simp[h]
   | succ k' =>
    rw[qp (by omega),nJ]
    cases w.testBit (6*i+s)<;>simp[qp (by omega:k'+1≠0)]
 . simp[hi,kS]
lemma yy (m d i:Nat):z6 (qi (qe m 1) d) i=if i < m then v6 (d.testBit (6*i)) (d.testBit (6*i+1)) (d.testBit (6*i+2)) (d.testBit (6*i+3)) (d.testBit (6*i+4)) (d.testBit (6*i+5)) else 0:=by
 unfold qi;simp only[v5];have y:∀s j,z6 (land (shiftRight d s) (qe m 1)) j =
     if j < m then (if d.testBit (6*j+s) then 1 else 0) else 0:=fun s j=>wc d s m j
 have h3:∀j,z6 (land d (qe m 1)) j =
     if j < m then (if d.testBit (6*j) then 1 else 0) else 0:=fun j=>by
   have:=y 0 j;simpa using this
 have x:∀s j,z6 (xor (qe m 1) (land (shiftRight d s) (qe m 1))) j =
     if j < m then (if !(d.testBit (6*j+s)) then 1 else 0) else 0:=by
   intro s j;rw[rj,v0 m 1 j (by decide),y s j]
   by_cases e:j < m
   . simp only[e,↓reduceIte];cases d.testBit (6*j+s)<;>decide
   . simp[e]
 set a:=land d (qe m 1);set b:=land (shiftRight d 1) (qe m 1);set c:=land (shiftRight d 2) (qe m 1);set g:=xor (qe m 1) (land (shiftRight d 3) (qe m 1));set h:=xor (qe m 1) (land (shiftRight d 4) (qe m 1));set t:=xor (qe m 1) (land (shiftRight d 5) (qe m 1));have z:∀u v:Q,
     land (if u then 1 else 0) (if v then 1 else 0)=if u&&v then 1 else 0:=by
   intro u v;cases u<;>cases v<;>decide
 have h8:∀u v:Q,
     lor (if u then 1 else 0) (if v then 1 else 0)=if u||v then 1 else 0:=by
   intro u v;cases u<;>cases v<;>decide
 have hL:∀j,z6 (land g b) j=if j < m then (if !(d.testBit (6*j+3))&&d.testBit (6*j+1) then 1 else 0) else 0:=by
   intro j;rw[v9,x 3 j,y 1 j];by_cases e:j < m
   . simp only[e,↓reduceIte];exact z _ _
   . simp[e]
 have h0:∀j,z6 (land g c) j=if j < m then (if !(d.testBit (6*j+3))&&d.testBit (6*j+2) then 1 else 0) else 0:=by
   intro j;rw[v9,x 3 j,y 2 j];by_cases e:j < m
   . simp only[e,↓reduceIte];exact z _ _
   . simp[e]
 have h1:∀j,z6 (land a h) j=if j < m then (if d.testBit (6*j)&&!(d.testBit (6*j+4)) then 1 else 0) else 0:=by
   intro j;rw[v9,h3 j,x 4 j];by_cases e:j < m
   . simp only[e,↓reduceIte];exact z _ _
   . simp[e]
 have h2:∀j,z6 (land a t) j=if j < m then (if d.testBit (6*j)&&!(d.testBit (6*j+5)) then 1 else 0) else 0:=by
   intro j;rw[v9,h3 j,x 5 j];by_cases e:j < m
   . simp only[e,↓reduceIte];exact z _ _
   . simp[e]
 have h4:∀j,z6 (land (land a g) (land (lor b c) (lor h t))) j =
     if j < m then (if (d.testBit (6*j)&&!(d.testBit (6*j+3)))&&((d.testBit (6*j+1)||d.testBit (6*j+2))&&(!(d.testBit (6*j+4))||!(d.testBit (6*j+5)))) then 1 else 0) else 0:=by
   intro j;rw[v9 (land a g),v9 a g,v9 (lor b c),wb b c,wb h t,h3 j,x 3 j,y 1 j,y 2 j,x 4 j,x 5 j]
   by_cases e:j < m
   . simp only[e,↓reduceIte,z,h8]
   . simp[e]
 have h5:∀j,z6 (add (land g b) (land g c)) j =
     z6 (land g b) j+z6 (land g c) j:=fun j =>
   iq (fun l=>by rw[hL l,h0 l];by_cases hl:l < m<;>simp[hl]<;>split<;>split<;>omega) j
 have h6:∀j,z6 (add (land a h) (land a t)) j =
     z6 (land a h) j+z6 (land a t) j:=fun j =>
   iq (fun l=>by rw[h1 l,h2 l];by_cases hl:l < m<;>simp[hl]<;>split<;>split<;>omega) j
 have h7:∀j,z6 (add (add (land g b) (land g c)) (add (land a h) (land a t))) j =
     z6 (land g b) j+z6 (land g c) j+(z6 (land a h) j+z6 (land a t) j):=by
   intro j;have h9:∀l,z6 (add (land g b) (land g c)) l+z6 (add (land a h) (land a t)) l < 64:=by
     intro l;rw[h5 l,h6 l,hL l,h0 l,h1 l,h2 l]
     by_cases hl:l < m<;>simp[hl]<;>split<;>split<;>split<;>split<;>omega
   change z6 (_+_) j=_;rw[iq h9 j,h5 j,h6 j]
 have x2:∀j,z6 (land (land a g) (land (lor b c) (lor h t))) j <=
     z6 (add (add (land g b) (land g c)) (add (land a h) (land a t))) j:=by
   intro j;rw[h7 j,h4 j,hL j,h0 j,h1 j,h2 j]
   by_cases e:j < m
   . simp only[e,↓reduceIte];cases d.testBit (6*j)<;>cases d.testBit (6*j+1)<;>cases d.testBit (6*j+2) <;>
      cases d.testBit (6*j+3)<;>cases d.testBit (6*j+4)<;>cases d.testBit (6*j+5)<;>decide
   . simp[e]
 change z6 (_ - _) i=_;rw[pz x2 i,h7 i,h4 i,hL i,h0 i,h1 i,h2 i]
 by_cases hi:i < m
 . simp only[hi,↓reduceIte,v6];omega
 . simp[hi]
lemma q51:∀v1 b:Nat,v1<=3->b<=3 ->
  let u:=lor v1 b
  let hi:=land u 2
  lor hi (lor (lor (land v1 (shiftRight v1 1)) (land b (shiftRight b 1)))
   (land (land u 1) (xor 1 (shiftRight hi 1))))=max v1 b:=by
 intro v1 b h1 h2
 interval_cases v1<;>interval_cases b<;>decide
lemma ya {v:Nat}(d:∀j,z6 v j<=3)(i:Nat):z6 (land v (shiftRight v 1)) i=land (z6 v i) (shiftRight (z6 v i) 1):=by
 apply kL;intro k;rw[kS,kS,kN,qo,qo]
 by_cases c:k < 6
 . simp only[c,↓reduceIte,kN];change (v.testBit (6*i+k)&&(v >>> 1).testBit (6*i+k)) =
     (v.testBit (6*i+k)&&((z6 v i) >>> 1).testBit k)
   rw[kQ,kQ,qo]
   by_cases hk5:k < 5
   . have e:1+k < 6:=(by omega);simp only[e,↓reduceIte]
     have:1+(6*i+k)=6*i+(1+k):=by omega
     rw[this]
   . have g:k=5:=(by omega);subst g;have h:z6 v i < 4:=(by have:=d i;omega);have b:(z6 v i).testBit 5=false:=Nat.testBit_lt_two_pow (lt_of_lt_of_le h (by decide));rw[qo] at b;simp only[show 5 < 6 by decide,↓reduceIte] at b;simp[b]
 . simp[c]
lemma jv {hi:Nat}(c:∀j,z6 hi j=0\/z6 hi j=2)(i:Nat):z6 (land (shiftRight hi 1) (qe m 1)) i=if i < m then shiftRight (z6 hi i) 1 else 0:=by
 rw[v9,v0 m 1 i (by decide)]
 by_cases b:i < m
 . simp only[b,↓reduceIte];apply kL;intro k;rw[kS,kN,qo]
   cases k with
   | zero =>
    simp only[Nat.zero_lt_succ,↓reduceIte,mH,Nat.testBit_one_zero,hV];change (hi >>> 1).testBit (6*i)=((z6 hi i) >>> 1).testBit 0;rw[kQ,kQ,qo]
    simp[mF]
   | succ k' =>
    rw[qp (by omega),nJ]
    rcases c i with d|e
    . rw[d];simp
    . rw[e];change false=((2 >>> 1:Nat).testBit (k'+1));simp[qp (by omega:k'+1≠0)]
 . simp[b,kS]
lemma kh (sh1 m w i:Nat):z6 (yg sh1 (qe m 1) (qe m 2) w) i=if i < m then zq (w.testBit (sh1+6*i)) (w.testBit (sh1+6*i+1)) (w.testBit (sh1+6*i+2)) (w.testBit (sh1+6*i+3)) (w.testBit (sh1+6*i+4)) (w.testBit (sh1+6*i+5)) else 0:=by
 unfold yg;simp only[v5];set g:=shiftRight w sh1;have h9:∀k,g.testBit k=w.testBit (sh1+k):=fun k=>by
   change (w >>> sh1).testBit k=_;rw[kQ,mF]
 set a:=land g (qe m 1);set b:=land (shiftRight g 1) (qe m 1);set c:=land (shiftRight g 2) (qe m 1);set d:=land (shiftRight g 3) (qe m 1);set e:=land (shiftRight g 4) (qe m 1);set f:=land (shiftRight g 5) (qe m 1);set nd:=xor (qe m 1) d;set ne:=xor (qe m 1) e;set nf:=xor (qe m 1) f;set na:=xor (qe m 1) a;set nb:=xor (qe m 1) b;set nc:=xor (qe m 1) c;set v1:=sub (add (add (land nd b) (land nd c)) (add (land a ne) (land a nf)))
         (land (land a nd) (land (lor b c) (lor ne nf)))
 set h:=sub (add (add (land d nb) (land d nc)) (add (land na e) (land na f)))
         (land (land na d) (land (lor nb nc) (lor e f)))
 have x2:v1=qi (qe m 1) g:=by unfold qi;simp only[v5];rfl
 have h0:∀j,z6 v1 j=if j < m then
     v6 (g.testBit (6*j)) (g.testBit (6*j+1)) (g.testBit (6*j+2))
        (g.testBit (6*j+3)) (g.testBit (6*j+4)) (g.testBit (6*j+5)) else 0:=by
   intro j;rw[x2,yy]
 have x3:h=qi (qe m 1) (xor g (2 ^ (6*m) - 1)):=by
   have v:∀s,s < 6->land (shiftRight (xor g (2 ^ (6*m) - 1)) s) (qe m 1) =
       xor (qe m 1) (land (shiftRight g s) (qe m 1)):=by
     intro s hs;apply wg;intro j;rw[wc,rj,v0 m 1 j (by decide),wc]
     by_cases t:j < m
     . have a1:6*j+s < 6*m:=(by omega);simp only[t,↓reduceIte,kT,kP,kK,a1,decide_true];cases g.testBit (6*j+s)<;>decide
     . simp[t]
   have a2:land (xor g (2 ^ (6*m) - 1)) (qe m 1) =
       xor (qe m 1) (land g (qe m 1)):=by
     have:=v 0 (by decide);simpa using this
   have h3:∀x,xor (qe m 1) (xor (qe m 1) x)=x:=by
     intro x;apply kL;intro k;rw[kT,kT,kP,kP]
     cases (qe m 1).testBit k<;>cases x.testBit k<;>decide
   unfold qi;simp only[v5];rw[a2,v 1 (by decide),v 2 (by decide),v 3 (by decide),v 4 (by decide),v 5 (by decide),h3,h3,h3]
 have h4:∀j,z6 h j=if j < m then
     v6 (!(g.testBit (6*j))) (!(g.testBit (6*j+1))) (!(g.testBit (6*j+2)))
        (!(g.testBit (6*j+3))) (!(g.testBit (6*j+4))) (!(g.testBit (6*j+5))) else 0:=by
   intro j;rw[x3,yy]
   by_cases t:j < m
   . simp only[t,↓reduceIte,kT,kP,kK];simp only[show 6*j < 6*m by omega,show 6*j+1 < 6*m by omega,show 6*j+2 < 6*m by omega,show 6*j+3 < 6*m by omega,show 6*j+4 < 6*m by omega,show 6*j+5 < 6*m by omega,decide_true,mK]
   . simp[t]
 have h5:∀j,z6 v1 j<=3:=fun j=>by
   rw[h0 j];split;exact yr _ _ _ _ _ _;omega
 have h6:∀j,z6 h j<=3:=fun j=>by
   rw[h4 j];split;exact yr _ _ _ _ _ _;omega
 set u:=lor v1 h;set hi:=land u (qe m 2);have h7:∀j,z6 hi j=if j < m then land (lor (z6 v1 j) (z6 h j)) 2 else 0:=by
   intro j;rw[v9,wb,v0 m 2 j (by decide)]
   by_cases t:j < m<;>simp[t,kS]
 have b0:∀j,z6 hi j=0\/z6 hi j=2:=by
   intro j;rw[h7 j]
   split
   . have h1:=h5 j;have h2:=h6 j;generalize z6 v1 j=x at h1;generalize z6 h j=y at h2
     interval_cases x<;>interval_cases y<;>decide
   . left;rfl
 have b1:z6 (land (land u (qe m 1)) (xor (qe m 1) (shiftRight hi 1))) i =
     if i < m then land (land (lor (z6 v1 i) (z6 h i)) 1) (xor 1 (shiftRight (z6 hi i) 1)) else 0:=by
   have b3:land (land u (qe m 1)) (xor (qe m 1) (shiftRight hi 1)) =
       land (land u (qe m 1)) (xor (qe m 1) (land (shiftRight hi 1) (qe m 1))):=by
     apply kL;intro k;simp only[kS,kT,kN,kP];cases (qe m 1).testBit k<;>simp
   rw[b3,v9,v9,wb,rj,v0 m 1 i (by decide),jv (m:=m) b0 i]
   by_cases z:i < m<;>simp[z,kS]
 rw[wb,wb,wb,ya h5 i,ya h6 i,b1,h7 i]
 by_cases z:i < m
 . simp only[z,↓reduceIte];have h8:=q51 (z6 v1 i) (z6 h i) (h5 i) (h6 i);simp only at h8;rw[h8,h0 i,h4 i]
   simp only[z,↓reduceIte,h9,zq];have c2:sh1+(6*i+1)=sh1+6*i+1:=by omega
   have c3:sh1+(6*i+2)=sh1+6*i+2:=(by omega);have d1:sh1+(6*i+3)=sh1+6*i+3:=(by omega);have d2:sh1+(6*i+4)=sh1+6*i+4:=(by omega);have e0:sh1+(6*i+5)=sh1+6*i+5:=(by omega);rw[c2,c3,d1,d2,e0]
 . simp only[z,↓reduceIte,h0 i,h4 i];decide
lemma q47 {α:Type} (f : α->Nat)(m:Nat) (e:∀x i,z6 (f x) i<=(if i < m then 3 else 0)) (b:List α)(hlen:b.length<=11)(i:Nat):z6 (b.foldr (fun x acc=>add (f x) acc) 0) i=(b.map fun x=>z6 (f x) i).sum/\(b.map fun x=>z6 (f x) i).sum<=if i < m then 3*b.length else 0:=by
 induction b generalizing i with
 | nil=>simp[z6]
 | cons a t ih =>
  simp only[kD] at hlen;have g:∀j,z6 (t.foldr (fun x acc=>add (f x) acc) 0) j =
     (t.map fun x=>z6 (f x) j).sum /\
     (t.map fun x=>z6 (f x) j).sum<=if j < m then 3*t.length else 0:=
    fun j=>ih (by omega) j
  have h:∀j,z6 (f a) j+z6 (t.foldr (fun x acc=>add (f x) acc) 0) j < 64:=by
    intro j;have s:=e a j;have⟨c,d⟩:=g j;rw[c]
    by_cases u:j < m<;>simp only[u,↓reduceIte] at s d<;>omega
  simp only[kG,kB,jN,kD];have v:=iq h i;have y:=e a i;have⟨c,d⟩:=g i;refine⟨?_,?_⟩
  . change z6 (_+_) i=_;rw[v,c]
  . by_cases hi:i < m<;>simp only[hi,↓reduceIte] at y d ⊢<;>omega
lemma ky (S m:Nat)(c:∀i,z6 S i<=if i < m then 33 else 0)(d:∀i < m,3<=z6 S i):beq (land (add S (qe m 29)) (qe m 32)) (qe m 32)=true:=by
 rw[nC]
 apply wg;intro i;have e:∀j,z6 S j+z6 (qe m 29) j < 64:=by
   intro j;rw[v0 m 29 j (by decide)]
   have b:=c j;by_cases g:j < m<;>simp only[g,↓reduceIte] at b ⊢<;>omega
 rw[v9]
 change land (z6 (S+qe m 29) i) (z6 (qe m 32) i)=z6 (qe m 32) i;rw[iq e i,v0 m 29 i (by decide),v0 m 32 i (by decide)]
 by_cases hi:i < m
 . simp only[hi,↓reduceIte];have b:=c i;simp only[hi,↓reduceIte] at b;have hge:=d i hi;have h:32<=z6 S i+29:=by omega
   have s:z6 S i+29 < 64:=(by omega);generalize z6 S i+29=v at h s
   interval_cases v<;>decide
 . simp[hi,kS]
def j5 (n c:Nat):Nat->Nat->M
 | 0,_=>[]
 | m+1,idx =>
  let b:=if ble n 7 then 7 else 8
  let d:=if ble n 7 then 127 else 255
  land (shiftRight c (mul b idx)) d::j5 n c m (add idx 1)
lemma q32 (n c m b:Nat):(j5 n c m b).length=m:=by
 induction m generalizing b with
 | zero=>rfl
 | succ m ih=>simp[j5,ih]
def ee (n b shTT:Nat):M:=j5 n b shTT 0
def e8 (n b shTT:Nat):M:=ee n b shTT++range (2 ^ n)
lemma jj (n b shTT:Nat):(ee n b shTT).length=shTT:=
 q32 n b shTT 0
lemma zl (n b shTT:Nat):(e8 n b shTT).length=shTT+2 ^ n:=by simp[e8,jj]
structure gX (n:Nat) (f:Z n) (rp:Nat) (c:Cfg):Prop where
 fT:c.fE=2*c.k
 fU:c.fE<=c.fF
 fV:c.fF<=c.fH
 fW:(c.fF - c.fE) % 6=0
 fX:(c.fH - c.fF) % 6=0
 fY:c.fJ=2 ^ (c.fH+2 ^ n) - 1
 fZ:c.fK=s8 (e8 n rp c.fH) f
 gA:c.fL=2 ^ c.k - 1
 gB:c.fM=2 ^ (6*((c.fF - c.fE) / 6)) - 1
 gC:c.m0=qe ((c.fF - c.fE) / 6) 1
 gD:c.fN=qe ((c.fF - c.fE) / 6) 29
 gE:c.fP=qe ((c.fF - c.fE) / 6) 32
 gF:c.m1=qe ((c.fH - c.fF) / 6) 1
 gH:c.fQ=qe ((c.fH - c.fF) / 6) 2
 gJ:c.fR=qe ((c.fH - c.fF) / 6) 29
 gK:c.fS=qe ((c.fH - c.fF) / 6) 32
 gL:∀i < c.k,
  f (q1 n ((e8 n rp c.fH).getD i 0))=false /\
  f (q1 n ((e8 n rp c.fH).getD (c.k+i) 0))=true
 gM:∀i < (c.fF - c.fE) / 6,
  f (q1 n ((e8 n rp c.fH).getD (c.fE+6*i) 0))=true /\
  f (q1 n ((e8 n rp c.fH).getD (c.fE+6*i+1) 0))=true /\
  f (q1 n ((e8 n rp c.fH).getD (c.fE+6*i+2) 0))=true /\
  f (q1 n ((e8 n rp c.fH).getD (c.fE+6*i+3) 0))=false /\
  f (q1 n ((e8 n rp c.fH).getD (c.fE+6*i+4) 0))=false /\
  f (q1 n ((e8 n rp c.fH).getD (c.fE+6*i+5) 0))=false
 gN:∀i < (c.fH - c.fF) / 6,
  f (q1 n ((e8 n rp c.fH).getD (c.fF+6*i) 0))=true /\
  f (q1 n ((e8 n rp c.fH).getD (c.fF+6*i+1) 0))=true /\
  f (q1 n ((e8 n rp c.fH).getD (c.fF+6*i+2) 0))=true /\
  f (q1 n ((e8 n rp c.fH).getD (c.fF+6*i+3) 0))=false /\
  f (q1 n ((e8 n rp c.fH).getD (c.fF+6*i+4) 0))=false /\
  f (q1 n ((e8 n rp c.fH).getD (c.fF+6*i+5) 0))=false
def w3 (n:Nat)(f:Z n)(e:Nat)(c:Cfg):Q:=
 let d:=(c.fF - c.fE) / 6
 let b:=(c.fH - c.fF) / 6
 beq c.fE (2*c.k) &&
 ble c.fE c.fF &&
 ble c.fF c.fH &&
 beq ((c.fF - c.fE) % 6) 0 &&
 beq ((c.fH - c.fF) % 6) 0 &&
 beq c.fJ (2 ^ (c.fH+2 ^ n) - 1) &&
 beq c.fK (s8 (e8 n e c.fH) f) &&
 beq c.fL (2 ^ c.k - 1) &&
 beq c.fM (2 ^ (6*d) - 1) &&
 beq c.m0 (qe d 1) &&
 beq c.fN (qe d 29) &&
 beq c.fP (qe d 32) &&
 beq c.m1 (qe b 1) &&
 beq c.fQ (qe b 2) &&
 beq c.fR (qe b 29) &&
 beq c.fS (qe b 32) &&
 beq (land c.fK c.fL) 0 &&
 beq (land (shiftRight c.fK c.k) c.fL) c.fL &&
 beq (land (shiftRight c.fK c.fE) c.fM) (qe d 7) &&
 beq (land (shiftRight c.fK c.fF) (2 ^ (6*b) - 1)) (qe b 7)
lemma qm {n:Nat}(b:M)(f:Z n){c:Nat}(h:c < b.length):(s8 b f).testBit c=f (q1 n (b.getD c 0)):=by rw[z8,jK h,jL _ _ h]
lemma jn (n:Nat)(f:Z n)(d:Nat)(c:Cfg)(h:w3 n f d c=true):gX n f d c:=by
 unfold w3 at h;simp only[jY,nC,nA] at h;rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h3,h4⟩,h5⟩,h6⟩,h7⟩,h8⟩,x⟩,t⟩,y⟩,hm0⟩,h9⟩,x2⟩,x3⟩,a1⟩,a2⟩,b0⟩,b1⟩,b3⟩,c2⟩,c3⟩
 have hlen:(e8 n d c.fH).length=c.fH+2 ^ n:=zl n d c.fH;have u:∀v < c.fH,c.fK.testBit v=f (q1 n ((e8 n d c.fH).getD v 0)):=by intro v d1;rw[x,qm _ _ (by rw[hlen];exact Nat.lt_add_right (2 ^ n) d1)]
 have h0:∀(e m:Nat),e+6*m<=c.fH ->
     land (shiftRight c.fK e) (2 ^ (6*m) - 1)=qe m 7 ->
     ∀i < m,
      f (q1 n ((e8 n d c.fH).getD (e+6*i) 0))=true /\
      f (q1 n ((e8 n d c.fH).getD (e+6*i+1) 0))=true /\
      f (q1 n ((e8 n d c.fH).getD (e+6*i+2) 0))=true /\
      f (q1 n ((e8 n d c.fH).getD (e+6*i+3) 0))=false /\
      f (q1 n ((e8 n d c.fH).getD (e+6*i+4) 0))=false /\
      f (q1 n ((e8 n d c.fH).getD (e+6*i+5) 0))=false:=by
   intro e m hbound d2 i hi;have j:∀g < 6,f (q1 n ((e8 n d c.fH).getD (e+6*i+g) 0))=(7:Nat).testBit g:=by
     intro g e0;have b:=congrArg (fun z=>z6 z i) d2;rw[v0 m 7 i (by decide)] at b;simp only[hi,↓reduceIte] at b;have s:=congrArg (fun z=>z.testBit g) b;rw[qo] at s;simp only[e0,↓reduceIte,kS,kN,kK,show 6*i+g < 6*m by omega,decide_true,hV] at s;change (c.fK >>> e).testBit (6*i+g)=_ at s;rw[kQ,<- mG] at s;rw[<- u (e+6*i+g) (by omega)]
     exact s
   exact⟨by simpa using j 0 (by decide),j 1 (by decide),j 2 (by decide),j 3 (by decide),j 4 (by decide),j 5 (by decide)⟩
 refine⟨h3,h4,h5,h6,h7,h8,x,t,y,hm0,h9,x2,x3,a1,a2,b0,?_,?_,?_⟩
 . intro i hi;constructor
   . have b:=congrArg (fun z=>z.testBit i) b1;rw[kS,kN,t,kK,kU] at b;simp only[hi,decide_true,hV] at b;rw[<- u i (by omega)];exact b
   . have b:=congrArg (fun z=>z.testBit i) b3;rw[kS,kN,t,kK] at b;simp only[hi,decide_true,hV] at b;change (c.fK >>> c.k).testBit i=true at b;rw[kQ] at b;rw[<- u (c.k+i) (by omega)];exact b
 . apply h0 c.fE ((c.fF - c.fE) / 6) (by omega)
   rw[<- y];exact c2
 . apply h0 c.fF ((c.fH - c.fF) / 6) (by omega) c3
def gW {α:Type} (b:List (α×Nat)):Prop:=∀p∈b,p.2<=3
lemma gW.perm {α:Type} {b c:List (α×Nat)}(d:b.Perm c)(h:gW b):gW c:=
 fun p hm=>h p (d.symm.subset hm)
lemma gV.inv_zero {α:Type} {inv : α->α}{meet join : α->α->α}{zero one c : α}{d:List (α×Nat)}(h:gV inv meet join zero one c 0 d):∃tg,d=[(c,tg)]:=by
 generalize b:(0:Nat)=s at h
 induction h with
 | done tg=>exact⟨tg,rfl⟩
 | perm e _ ih=>obtain⟨tg,rfl⟩:=ih b;exact⟨tg,List.perm_singleton.1 e.symm⟩
 | uNot _ _ _ _ _ _ _ _ _=>cases b
 | bOr _ _ _ _ _ _ _ _ _ _ _ _=>cases b
 | bAnd _ _ _ _ _ _ _ _ _ _ _ _=>cases b
lemma gV.inv_succ {α:Type} {inv : α->α}{meet join : α->α->α}{zero one x2 : α}{s:Nat}{ws:List (α×Nat)} (h:gV inv meet join zero one x2 (s+1) ws):(∃a ta r d,ws.Perm ((a,ta)::r)/\ta≠1/\ta≠2/\(ta=3->d=false)/\inv a≠zero/\inv a≠one/\inv a≠a/\(∀x∈r,x.1≠inv a)/\gV inv meet join zero one x2 s ((inv a,if ta=3 then 2 else 0)::qk d (a,0) r))\/(∃a ta b tb r ka kb,ws.Perm ((a,ta)::(b,tb)::r)/\ta≠2/\tb≠2/\(ta=1->ka=false)/\(tb=1->kb=false)/\join a b≠zero/\join a b≠one/\join a b≠a/\join a b≠b/\(∀x∈r,x.1≠join a b)/\gV inv meet join zero one x2 s ((join a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)))\/(∃a ta b tb r ka kb,ws.Perm ((a,ta)::(b,tb)::r)/\ta≠1/\tb≠1/\(ta≠0->ka=false)/\(tb≠0->kb=false)/\meet a b≠zero/\meet a b≠one/\meet a b≠a/\meet a b≠b/\(∀x∈r,x.1≠meet a b)/\gV inv meet join zero one x2 s ((meet a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r))):=by
 generalize e:s+1=s' at h
 induction h with
 | done _=>cases e
 | perm c _ ih =>
  rcases ih e with ⟨a,ta,r,d,c',g⟩|⟨a,ta,b,tb,r,ka,kb,c',g⟩|⟨a,ta,b,tb,r,ka,kb,c',g⟩
  . exact Or.inl ⟨a,ta,r,d,c.symm.trans c',g⟩
  . exact Or.inr (Or.inl ⟨a,ta,b,tb,r,ka,kb,c.symm.trans c',g⟩)
  . exact Or.inr (Or.inr ⟨a,ta,b,tb,r,ka,kb,c.symm.trans c',g⟩)
 | @uNot s0 a ta r d i j t u v y z h0 _ =>
  cases e
  exact Or.inl ⟨a,ta,r,d,mP _,i,j,t,u,v,y,z,h0⟩
 | @bOr s0 a ta b tb r ka kb i j t u v y z h8 h9 h0 _ =>
  cases e
  exact Or.inr (Or.inl ⟨a,ta,b,tb,r,ka,kb,mP _,i,j,t,u,v,y,z,h8,h9,h0⟩)
 | @bAnd s0 a ta b tb r ka kb i j t u v y z h8 h9 h0 _ =>
  cases e
  exact Or.inr (Or.inr ⟨a,ta,b,tb,r,ka,kb,mP _,i,j,t,u,v,y,z,h8,h9,h0⟩)
lemma pc {α:Type} {d:List α}{a : α}{r:List α} (e:d.Perm (a::r)):∃b c,d=b++a::c/\r.Perm (b++c):=by
 have h:a∈d:=e.symm.subset (by simp);obtain⟨b,c,g⟩:=List.append_of_mem h;refine⟨b,c,g,?_⟩
 rw[g] at e;exact (List.perm_cons a).1 (e.symm.trans mE)
lemma lx {α:Type} {h:List α}{a b : α}{r:List α} (u:h.Perm (a::b::r)):(∃d c e,h=d++a::c++b::e/\r.Perm (d++c++e))\/(∃d c e,h=d++b::c++a::e/\r.Perm (d++c++e)):=by
 obtain⟨p1,s1,j,g⟩:=pc u;have v:b∈p1++s1:=g.subset (by simp);rcases jD.1 v with x|y
 . obtain⟨d,c,s⟩:=List.append_of_mem x;right;refine⟨d,c,s1,by rw[j,s,kA,kZ],?_⟩
   rw[s,kA] at g;have i:(d++b::(c++s1)).Perm (b::(d++(c++s1))):=mE;have z:=(List.perm_cons b).1 (g.trans i);simpa[kA] using z
 . obtain⟨c,e,t⟩:=List.append_of_mem y;left;refine⟨p1,c,e,by simp[j,t,kA],?_⟩
   rw[t] at g;have i:((p1++c)++b::e).Perm (b::((p1++c)++e)):=mE;rw[<- kA] at g;exact (List.perm_cons b).1 (g.trans i)
lemma z4 {α:Type} (k:Q)(a : α)(r:List α)(x : α):x∈qk k a r↔(k=true/\x=a)\/x∈r:=by cases k<;>simp[qk]
abbrev aR (n b:Nat)(c:Cfg):=e8 n b c.fH
abbrev TR {n:Nat}(f:u6 n):=gV (hC (n:=n)) hE hG (fun _=>false) (fun _=>true) f
lemma TR.toRun {n s:Nat}{f:Z n}{c:X n}(h:TR f s c):Run (hC (n:=n)) hE hG f s (c.map fst):=by
 induction h with
 | done _=>exact Run.done
 | perm d _ ih=>exact Run.perm (d.map fst) ih
 | @uNot _ a ta r save _ _ _ _ _ _ _ _ ih =>
  have e:(((hC a,if ta=3 then 2 else 0)::qk save (a,0) r).map fst) =
    (if true then hC a else a)::qk save a (r.map fst):=by cases save<;>simp[qk]
  rw[e] at ih;exact Run.one true save ih
 | @bOr _ a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ ih =>
  have e:(((hG a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).map fst) =
    (if false then hE a b else hG a b)::qk ka a (qk kb b (r.map fst)):=by
   cases ka<;>cases kb<;>simp[qk]
  rw[e] at ih;exact Run.two false ka kb ih
 | @bAnd _ a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ ih =>
  have e:(((hE a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)).map fst) =
    (if true then hE a b else hG a b)::qk ka a (qk kb b (r.map fst)):=by
   cases ka<;>cases kb<;>simp[qk]
  rw[e] at ih;exact Run.two true ka kb ih
lemma sx {n:Nat}{f:Z n}{c:List (Z n)} (d:Run (hC (n:=n)) hE hG f 0 c):c=[f]:=by
 generalize b:0=s at d
 induction d using Run.fold with
 | done=>rfl
 | perm e _ ih=>exact List.perm_singleton.1 ((ih b) ▸ e.symm)
 | one _ _ _ _=>cases b
 | two _ _ _ _ _=>cases b
lemma ux {n:Nat}{f:Z n}{s:Nat}{j:List (Z n)} (t:Run (hC (n:=n)) hE hG f s j) {x y:F n} (hsep:f x≠f y):∃g∈j,g x≠g y:=by
 induction t using Run.fold with
 | done=>exact⟨f,by simp,hsep⟩
 | perm u _ ih=>obtain⟨g,c,d⟩:=ih;exact⟨g,u.mem_iff.1 c,d⟩
 | @one _ a r neg save _ ih =>
  obtain⟨g,c,d⟩:=ih;rcases kC.1 c with rfl|c
  . refine⟨a,by simp,fun v=>d ?_⟩;cases neg<;>simp[hC,v]
  . rcases (z4 _ _ _ _).1 c with ⟨_,e⟩|c
    . exact⟨g,by simp[e],d⟩
    . exact⟨g,hX _ c,d⟩
 | @two _ a b r conj ka kb _ ih =>
  obtain⟨g,c,d⟩:=ih;rcases kC.1 c with rfl|c
  . by_cases h:a x≠a y
    . exact⟨a,by simp,h⟩
    . by_cases i:b x≠b y
      . exact⟨b,hX _ (by simp),i⟩
      . push Not at h i;exfalso;apply d;cases conj<;>simp[hE,hG,h,i]
  . rcases (z4 _ _ _ _).1 c with ⟨_,e⟩|z
    . exact⟨g,by simp[e],d⟩
    . rcases (z4 _ _ _ _).1 z with ⟨_,h0⟩|h1
      . exact⟨g,hX _ (by simp[h0]),d⟩
      . exact⟨g,hX _ (hX _ h1),d⟩
lemma su {n:Nat}{a b:Z n}{r:List (Z n)}{e i j:Q}{u v:F n} (h:∃g∈(if e then hE a b else hG a b)::qk i a (qk j b r),g u=false/\g v=true):∃g∈a::b::r,g u=false/\g v=true:=by
 obtain⟨g,s,c,d⟩:=h;rcases kC.1 s with rfl|t
 . cases e
   . simp only[jV,↓reduceIte,hG,nE,jX] at c d;rcases d with x|y
     . exact⟨a,by simp,c.1,x⟩
     . exact⟨b,by simp,c.2,y⟩
   . simp only[↓reduceIte,hE,nF,jY] at c d;rcases c with z|h0
     . exact⟨a,by simp,z,d.1⟩
     . exact⟨b,by simp,h0,d.2⟩
 . rcases (z4 _ _ _ _).1 t with ⟨_,h1⟩|h2
   . exact⟨g,by simp[h1],c,d⟩
   . rcases (z4 _ _ _ _).1 h2 with ⟨_,h3⟩|h4
     . exact⟨g,by simp[h3],c,d⟩
     . exact⟨g,by simp[h4],c,d⟩
lemma sv {n:Nat}{f:Z n}{s:Nat}{d:List (Z n)} (j:Run (hC (n:=n)) hE hG f s d) (hlen:d.length=s+1):∀u v:F n,f u=false->f v=true->∃g∈d,g u=false/\g v=true:=by
 induction j using Run.fold with
 | done=>intro u v b c;exact⟨f,by simp,b,c⟩
 | perm i _ ih=>intro u v b c;obtain⟨g,t,x,y⟩:=ih (by rw[i.length_eq];exact hlen) u v b c;exact⟨g,i.mem_iff.1 t,x,y⟩
 | one neg save e _=>have h:=oy e;cases save<;>simp[qk] at hlen h<;>omega
 | two conj ka kb e ih =>
  have h:=oy e;cases ka<;>cases kb<;>simp[qk] at hlen h<;>try omega
  intro u v b c;exact su (ih (by simp[qk];omega) u v b c)
lemma dm {n:Nat}{f:Z n}{s:Nat}{c:List (Z n)} (j:Run (hC (n:=n)) hE hG f s c) (hlen:c.length=s+1) (r0 r1 r2 r3 r4 r5:F n) (h0:f r0=true) (h1:f r1=true) (h2:f r2=true) (h3:f r3=false) (h4:f r4=false) (h5:f r5=false):3<=(c.map fun g=>v6 (g r0) (g r1) (g r2) (g r3) (g r4) (g r5)).sum:=by
 induction j using Run.fold with
 | done=>simp[h0,h1,h2,h3,h4,h5,xp]
 | perm h _ ih=>rw[<- (h.map _).sum_eq];exact ih (by rw[h.length_eq];exact hlen)
 | one neg save d _=>have e:=oy d;cases save<;>simp[qk] at hlen e<;>omega
 | @two s a b r conj ka kb d ih =>
  have e:=oy d;cases ka<;>cases kb<;>simp[qk] at hlen e<;>try omega
  have i:=ih (by simp[qk];omega);cases conj
  . simp only[qk,jV,↓reduceIte,kB,jN,hG] at i ⊢
    have:=w4 (a r0) (a r1) (a r2) (a r3) (a r4) (a r5) (b r0) (b r1) (b r2) (b r3) (b r4) (b r5);omega
  . simp only[qk,jV,↓reduceIte,kB,jN,hE] at i ⊢
    have:=kl (a r0) (a r1) (a r2) (a r3) (a r4) (a r5) (b r0) (b r1) (b r2) (b r3) (b r4) (b r5);omega
lemma aj {n:Nat}{f:Z n}{s:Nat}{ws:List (Z n)} (hr:Run (hC (n:=n)) hE hG f s ws) (hlen:ws.length=s):(∀u v:F n,f u=false->f v=true->∃g∈ws,g u=false/\g v=true)\/(∀r0 r1 c d e h:F n,f r0=true->f r1=true->f c=true->f d=false->f e=false->f h=false->3<=(ws.map fun g=>zq (g r0) (g r1) (g c) (g d) (g e) (g h)).sum):=by
 induction hr using Run.fold with
 | done=>simp at hlen
 | perm hp _ ih =>
  rcases ih (by rw[hp.length_eq];exact hlen) with h7|h8
  . left;intro u v y j;obtain⟨g,hm,i,z⟩:=h7 u v y j;exact⟨g,hp.mem_iff.1 hm,i,z⟩
  . right;intro r0 r1 c d e h h0 i z h3 h4 h5;rw[<- (hp.map _).sum_eq];exact h8 r0 r1 c d e h h0 i z h3 h4 h5
 | @one s a r neg save h6 _ =>
  have h9:=oy h6;cases save
  . right;intro r0 r1 c d e h h0 i z h3 h4 h5;have j:=dm h6 (by simp[qk] at hlen ⊢;omega) r0 r1 c d e h h0 i z h3 h4 h5;have x2:∀l:List (Z n),
        (l.map fun g=>v6 (g r0) (g r1) (g c) (g d) (g e) (g h)).sum <=
        (l.map fun g=>zq (g r0) (g r1) (g c) (g d) (g e) (g h)).sum:=by
      intro l;induction l with
      | nil=>simp
      | cons x t iht=>simp only[kB,jN];have:=k7 (x r0) (x r1) (x c) (x d) (x e) (x h);omega
    have hs:=le_trans j (x2 _);cases neg<;>simp only[qk,jV,↓reduceIte,kB,jN,hC,jp] at hs ⊢<;>exact hs
  . simp[qk] at hlen h9;omega
 | @two s a b r conj ka kb h6 ih =>
  have h9:=oy h6;cases ka<;>cases kb
  . rcases ih (by simp[qk] at hlen ⊢;omega) with h7|h8
    . left;intro u v y j;exact su (h7 u v y j)
    . right;intro r0 r1 c d e h h0 i z h3 h4 h5;have i:=h8 r0 r1 c d e h h0 i z h3 h4 h5;cases conj
      . simp only[qk,jV,↓reduceIte,kB,jN,hG] at i ⊢
        have:=q14 (a r0) (a r1) (a c) (a d) (a e) (a h) (b r0) (b r1) (b c) (b d) (b e) (b h);omega
      . simp only[qk,jV,↓reduceIte,kB,jN,hE] at i ⊢
        have:=je (a r0) (a r1) (a c) (a d) (a e) (a h) (b r0) (b r1) (b c) (b d) (b e) (b h);omega
  . left;intro u v y j;exact su (sv h6 (by simp[qk] at hlen ⊢;omega) u v y j)
  . left;intro u v y j;exact su (sv h6 (by simp[qk] at hlen ⊢;omega) u v y j)
  . simp[qk] at hlen h9;omega
lemma qz {a b:Nat}(h:a=b):beq a b=true:=Eq.mpr nC h
lemma q0 (a:Nat):beq a a=true:=Eq.mpr nC rfl
lemma q2 {a b:Nat}(h:a≠b):beq a b=false:=by
 cases c:beq a b
 . rfl
 . exact absurd (Eq.mp nC c) h
lemma y3 {a b:Nat}(h:beq a b=false):a≠b:=
 fun e=>by subst e;rw[q0] at h;cases h
lemma zh {a b:Nat}:(beq a b=false)↔a≠b:=
 ⟨y3,q2⟩
lemma q4 {b e:Q}(h:e=true):(if b=true then true else e)=true:=by cases b<;>simp[h]
lemma q5 {b e:Q}(h:b=true):(if b=true then true else e)=true:=by rw[h];rfl
lemma v8 (a b:Nat):add a b=a+b:=rfl
def e6 {n:Nat}(b:M)(c:X n):J:=
 c.map fun p=>(s8 b p.1,p.2)
abbrev eW {n:Nat}(b:Nat)(c:Cfg) (d:List (u6 n×Nat)):=e6 (aR n b c) d
abbrev eL {n:Nat}(b:Nat)(c:Cfg)(g:u6 n):=s8 (aR n b c) g
def u2 (n:Nat)(b:X n):J:=
 b.map fun p=>(u9 n p.1,p.2)
lemma qy {n:Nat}(b:M)(p:Z n×Nat)(c:X n):e6 b (p::c)=(s8 b p.1,p.2)::e6 b c:=rfl
lemma pd {n:Nat}(p:Z n×Nat)(b:X n):u2 n (p::b)=(u9 n p.1,p.2)::u2 n b:=rfl
lemma qc {n:Nat}(c:M)(a b:Z n):s8 c (hG a b)=lor (s8 c a) (s8 c b):=xg c a b
lemma q9 {n:Nat}(c:M)(a b:Z n):s8 c (hE a b)=land (s8 c a) (s8 c b):=xh c a b
lemma jf {n:Nat}(b:M)(a:Z n):s8 b (hC a)=xor (s8 b a) (2 ^ b.length - 1):=ix b a
lemma qv {n:Nat}{f:Z n}{b:Nat}{c:Cfg}(d:gX n f b c)(a:Z n):eL b c (hC a)=xor (eL b c a) c.fJ:=by unfold eL;rw[ix,zl,<- d.fY]
def wi (c:Cfg)(w:Nat):Nat:=land w c.fL
def tx (c:Cfg)(w:Nat):Nat:=land (shiftRight w c.k) c.fL
def wC (c:Cfg)(w:Nat):Nat:=xor (wi c w) (tx c w)
def wU (c:Cfg)(w:Nat):Nat:=land (wC c w) (tx c w)
def sc (c:Cfg)(w:Nat):Nat:=land (shiftRight w c.fE) c.fM
def th (c:Cfg)(w:Nat):Nat:=qi c.m0 (sc c w)
def dg (c:Cfg)(w:Nat):Nat:=yg c.fF c.m1 c.fQ w
def yx (c:Cfg)(b:J):Nat:=b.foldr (fun p acc=>lor (wC c p.1) acc) 0
def v4 (c:Cfg)(b:J):Nat:=b.foldr (fun p acc=>lor (wU c p.1) acc) 0
def zf (c:Cfg)(b:J):Nat:=b.foldr (fun p acc=>add (th c p.1) acc) 0
def va (c:Cfg)(b:J):Nat:=b.foldr (fun p acc=>add (dg c p.1) acc) 0
lemma qq (a b d:Nat):lor (lor a b) d=lor a (lor b d):=by apply kL;intro i;simp[kR,kM,nG]
lemma q7 (a b:Nat):lor a b=lor b a:=by apply kL;intro i;simp[kR,kM,Bool.or_comm]
lemma q46 (a:Nat):lor 0 a=a:=by apply kL;intro i;simp[kR,kM]
lemma yp (c:Cfg)(p:K)(b:J):yx c (p::b)=lor (wC c p.1) (yx c b):=rfl
lemma vo (c:Cfg)(p:K)(b:J):v4 c (p::b)=lor (wU c p.1) (v4 c b):=rfl
lemma k0 (c:Cfg)(p:K)(b:J):zf c (p::b)=add (th c p.1) (zf c b):=rfl
lemma w1 (c:Cfg)(p:K)(b:J):va c (p::b)=add (dg c p.1) (va c b):=rfl
lemma vc (c:Cfg)(b d:J):yx c (b++d)=lor (yx c b) (yx c d):=by induction b with|nil=>simp[yx,q46]|cons a t ih=>simp only[kZ,yx,kG] at ih ⊢;rw[ih,qq]
lemma zu (c:Cfg)(b d:J):v4 c (b++d)=lor (v4 c b) (v4 c d):=by induction b with|nil=>simp[v4,q46]|cons a t ih=>simp only[kZ,v4,kG] at ih ⊢;rw[ih,qq]
lemma zy (c:Cfg)(b d:J):zf c (b++d)=add (zf c b) (zf c d):=by induction b with|nil=>simp[zf,v8]|cons a t ih=>simp only[kZ,zf,kG,v8] at ih ⊢;omega
lemma y6 (c:Cfg)(b d:J):va c (b++d)=add (va c b) (va c d):=by induction b with|nil=>simp[va,v8]|cons a t ih=>simp only[kZ,va,kG,v8] at ih ⊢;omega
lemma xe (c:Cfg)(b:J)(i:Nat):(yx c b).testBit i=b.any (fun p=>(wC c p.1).testBit i):=by
 induction b with
 | nil=>simp[yx]
 | cons _ _ ih=>simp only[yx,kG,kR,kM,List.any_cons] at ih ⊢;rw[ih]
lemma xf (c:Cfg)(b:J)(i:Nat):(v4 c b).testBit i=b.any (fun p=>(wU c p.1).testBit i):=by
 induction b with
 | nil=>simp[v4]
 | cons _ _ ih=>simp only[v4,kG,kR,kM,List.any_cons] at ih ⊢;rw[ih]
lemma zw {n:Nat}{f:Z n}{b:Nat}{c:Cfg}(d:gX n f b c)(w i:Nat):(wi c w).testBit i=if i < c.k then w.testBit i else false:=by
 unfold wi;rw[kS,kN,d.gA,kK]
 by_cases hi:i < c.k<;>simp[hi]
lemma vl {n:Nat}{f:Z n}{b:Nat}{c:Cfg}(d:gX n f b c)(w i:Nat):(tx c w).testBit i=if i < c.k then w.testBit (c.k+i) else false:=by
 unfold tx;rw[kS,kN,d.gA,kK]
 change ((w >>> c.k).testBit i&&decide (i < c.k))=_;rw[kQ];by_cases hi:i < c.k<;>simp[hi]
lemma vp {n:Nat}{f:Z n}{d:Nat}{c:Cfg}(b:gX n f d c)(w i:Nat):(wC c w).testBit i=if i < c.k then (w.testBit i ^^ w.testBit (c.k+i)) else false:=by
 unfold wC;rw[kT,kP,zw b,vl b]
 by_cases hi:i < c.k<;>simp[hi]
lemma vd {n:Nat}{f:Z n}{d:Nat}{c:Cfg}(b:gX n f d c)(w i:Nat):(wU c w).testBit i=if i < c.k then (!(w.testBit i)&&w.testBit (c.k+i)) else false:=by
 unfold wU;rw[kS,kN,vp b,vl b]
 by_cases hi:i < c.k
 . simp only[hi,↓reduceIte];cases w.testBit i<;>cases w.testBit (c.k+i)<;>decide
 . simp[hi]
lemma cm {n:Nat}{f:Z n}{d:Nat}{c:Cfg}(b:gX n f d c)(a:Nat):wC c (xor a c.fJ)=wC c a:=by
 have h2n:=mL n;have hk_le:2*c.k<=c.fH+2 ^ n:=by have:=b.fT;have:=b.fU;have:=b.fV;omega
 apply kL;intro i;rw[vp b,vp b]
 by_cases hi:i < c.k
 . simp only[hi,↓reduceIte,kT,kP,b.fY,kK,show i < c.fH+2 ^ n by omega,show c.k+i < c.fH+2 ^ n by omega,decide_true,mK];cases a.testBit i<;>cases a.testBit (c.k+i)<;>decide
 . simp[hi]
lemma cq {n:Nat}{f:Z n}{d:Nat}{c:Cfg}(b:gX n f d c)(a:Nat):wU c (xor a c.fJ)=land (wC c a) (wi c a):=by
 have h2n:=mL n;have hk_le:2*c.k<=c.fH+2 ^ n:=by have:=b.fT;have:=b.fU;have:=b.fV;omega
 apply kL;intro i;rw[vd b,kS,kN,vp b,zw b]
 by_cases hi:i < c.k
 . simp only[hi,↓reduceIte,kT,kP,b.fY,kK,show i < c.fH+2 ^ n by omega,show c.k+i < c.fH+2 ^ n by omega,decide_true,mK];cases a.testBit i<;>cases a.testBit (c.k+i)<;>decide
 . simp[hi]
lemma iw {n:Nat}{f:Z n}{e:Nat}{c:Cfg}(d:gX n f e c)(a b:Nat):wC c (lor a b)=xor (lor (wi c a) (wi c b)) (lor (tx c a) (tx c b)):=by
 apply kL;intro i;rw[vp d,kT,kR,kR,kR,kP,kM,kM,kM,kM,zw d,zw d,vl d,vl d]
 by_cases hi:i < c.k<;>simp[hi]
lemma kd {n:Nat}{f:Z n}{e:Nat}{c:Cfg}(d:gX n f e c)(a b:Nat):wC c (land a b)=xor (land (wi c a) (wi c b)) (land (tx c a) (tx c b)):=by
 apply kL;intro i;rw[vp d,kT,kS,kS,kS,kP,kN,kN,kN,kN,zw d,zw d,vl d,vl d]
 by_cases hi:i < c.k<;>simp[hi]
lemma cp {n:Nat}{f:Z n}{d:Nat}{c:Cfg}(b:gX n f d c)(a:Nat):sc c (xor a c.fJ)=xor (sc c a) c.fM:=by
 have h2n:=mL n;have hbound:c.fE+6*((c.fF - c.fE) / 6)<=c.fH+2 ^ n:=by have:=b.fU;have:=b.fV;have:=b.fW;omega
 apply kL;intro i;unfold sc;simp only[kS,kT,kN,kP,b.gB,kK];change (((a^^^c.fJ) >>> c.fE).testBit i&&decide (i < 6*((c.fF - c.fE) / 6))) =
   (((a >>> c.fE).testBit i&&decide (i < 6*((c.fF - c.fE) / 6))) ^^ decide (i < 6*((c.fF - c.fE) / 6)))
 rw[kQ,kQ,kP,b.fY,kK]
 by_cases hi:i < 6*((c.fF - c.fE) / 6)
 . simp[hi,show c.fE+i < c.fH+2 ^ n by omega]
 . simp[hi]
lemma pq (c:Cfg)(a b:Nat):sc c (lor a b)=lor (sc c a) (sc c b):=by
 apply kL;intro i;unfold sc;simp only[kS,kR,kN,kM];change (((a|||b) >>> c.fE).testBit i&&c.fM.testBit i) =
  (((a >>> c.fE).testBit i&&c.fM.testBit i)||((b >>> c.fE).testBit i&&c.fM.testBit i))
 rw[kQ,kQ,kQ,kM]
 cases a.testBit (c.fE+i)<;>cases b.testBit (c.fE+i)<;>cases c.fM.testBit i<;>decide
lemma we (c:Cfg)(a b:Nat):sc c (land a b)=land (sc c a) (sc c b):=by
 apply kL;intro i;unfold sc;simp only[kS,kN];change (((a&&&b) >>> c.fE).testBit i&&c.fM.testBit i) =
  (((a >>> c.fE).testBit i&&c.fM.testBit i)&&((b >>> c.fE).testBit i&&c.fM.testBit i))
 rw[kQ,kQ,kQ,kN]
 cases a.testBit (c.fE+i)<;>cases b.testBit (c.fE+i)<;>cases c.fM.testBit i<;>decide
lemma ck {n:Nat}{f:Z n}{d:Nat}{c:Cfg}(b:gX n f d c)(a:Nat):dg c (xor a c.fJ)=dg c a:=by
 have h2n:=mL n;have hbound:c.fF+6*((c.fH - c.fF) / 6)<=c.fH+2 ^ n:=by have:=b.fV;have:=b.fX;omega
 apply wg;intro i;unfold dg;rw[b.gF,b.gH,kh,kh]
 by_cases hi:i < (c.fH - c.fF) / 6
 . simp only[hi,↓reduceIte,kT,kP,b.fY,kK,show c.fF+6*i < c.fH+2 ^ n by omega,show c.fF+6*i+1 < c.fH+2 ^ n by omega,show c.fF+6*i+2 < c.fH+2 ^ n by omega,show c.fF+6*i+3 < c.fH+2 ^ n by omega,show c.fF+6*i+4 < c.fH+2 ^ n by omega,show c.fF+6*i+5 < c.fH+2 ^ n by omega,decide_true,mK,jp]
 . simp[hi]
lemma zz {n:Nat}{f:Z n}{d:Nat}{c:Cfg}(b:gX n f d c){e:X n}(j:∀u v:F n,f u=false->f v=true->∃p∈e,p.1 u≠p.1 v):yx c (eW d c e)=c.fL:=by
 have h2n:=mL n;have hlen:=zl n d c.fH;have hk_le:2*c.k<=c.fH:=by have:=b.fT;have:=b.fU;have:=b.fV;omega
 apply kL;intro i;rw[xe,b.gA,kK]
 by_cases hi:i < c.k
 . simp only[hi,decide_true,kJ];obtain⟨s,t⟩:=b.gL i hi;obtain⟨p,x,hne⟩:=j _ _ s t;refine⟨(eL d c p.1,p.2),mM.2 ⟨p,x,rfl⟩,?_⟩
   rw[vp b,if_pos hi,qm _ _ (by rw[hlen];omega),qm _ _ (by rw[hlen];omega)]
   cases h1:p.1 (q1 n ((aR n d c).getD i 0)) <;>
    cases h2:p.1 (q1 n ((aR n d c).getD (c.k+i) 0))<;>simp_all
 . simp only[hi,decide_false];rw[jU];intro h;obtain⟨q,_,g⟩:=kJ.1 h;rw[vp b,if_neg hi] at g;cases g
lemma q6 {n:Nat}{f:Z n}{d:Nat}{c:Cfg}(b:gX n f d c){e:X n}(j:∀u v:F n,f u=false->f v=true->∃p∈e,p.1 u=false/\p.1 v=true):v4 c (eW d c e)=c.fL:=by
 have h2n:=mL n;have hlen:=zl n d c.fH;have hk_le:2*c.k<=c.fH:=by have:=b.fT;have:=b.fU;have:=b.fV;omega
 apply kL;intro i;rw[xf,b.gA,kK]
 by_cases hi:i < c.k
 . simp only[hi,decide_true,kJ];obtain⟨s,t⟩:=b.gL i hi;obtain⟨p,x,y,z⟩:=j _ _ s t;refine⟨(eL d c p.1,p.2),mM.2 ⟨p,x,rfl⟩,?_⟩
   rw[vd b,if_pos hi,qm _ _ (by rw[hlen];omega),qm _ _ (by rw[hlen];omega),y,z];rfl
 . simp only[hi,decide_false];rw[jU];intro h;obtain⟨q,_,g⟩:=kJ.1 h;rw[vd b,if_neg hi] at g;cases g
lemma xx {n:Nat} {f:Z n} {b:Nat} {c:Cfg} (h:gX n f b c) (g:Z n) (i:Nat):
   z6 (th c (eL b c g)) i =
    if i < (c.fF - c.fE) / 6 then
     let d:=aR n b c
     v6 (g (q1 n (d.getD (c.fE+6*i) 0)))
      (g (q1 n (d.getD (c.fE+6*i+1) 0)))
      (g (q1 n (d.getD (c.fE+6*i+2) 0)))
      (g (q1 n (d.getD (c.fE+6*i+3) 0)))
      (g (q1 n (d.getD (c.fE+6*i+4) 0)))
      (g (q1 n (d.getD (c.fE+6*i+5) 0)))
    else 0:=by
 have h2n:=mL n
 have hlen:=zl n b c.fH
 have hbound:c.fE+6*((c.fF - c.fE) / 6)<=c.fH:=by
   have:=h.fU;have:=h.fV;have:=h.fW;omega
 unfold th;rw[h.gC,yy]
 by_cases hi:i < (c.fF - c.fE) / 6
 . simp only[hi,↓reduceIte]
   have e:∀j < 6,(sc c (eL b c g)).testBit (6*i+j) =
     g (q1 n ((aR n b c).getD (c.fE+6*i+j) 0)):=by
    intro j hoff;unfold sc
    rw[kS,kN,h.gB,kK]
    simp only[show 6*i+j < 6*((c.fF - c.fE) / 6) by omega,decide_true,hV]
    change ((eL b c g) >>> c.fE).testBit (6*i+j)=_
    rw[kQ,<- mG,qm _ _ (by rw[hlen];omega)]
   rw[show 6*i=6*i+0 by omega,e 0 (by decide),e 1 (by decide),e 2 (by decide),
     e 3 (by decide),e 4 (by decide),e 5 (by decide)]
   simp only[mH]
 . simp[hi]
lemma xy {n:Nat} {f:Z n} {d:Nat} {c:Cfg} (e:gX n f d c) (g:Z n) (i:Nat):
   z6 (dg c (eL d c g)) i =
    if i < (c.fH - c.fF) / 6 then
     let b:=aR n d c
     zq (g (q1 n (b.getD (c.fF+6*i) 0)))
      (g (q1 n (b.getD (c.fF+6*i+1) 0)))
      (g (q1 n (b.getD (c.fF+6*i+2) 0)))
      (g (q1 n (b.getD (c.fF+6*i+3) 0)))
      (g (q1 n (b.getD (c.fF+6*i+4) 0)))
      (g (q1 n (b.getD (c.fF+6*i+5) 0)))
    else 0:=by
 have h2n:=mL n
 have hlen:=zl n d c.fH
 have hbound:c.fF+6*((c.fH - c.fF) / 6)<=c.fH:=by
   have:=e.fV;have:=e.fX;omega
 unfold dg;rw[e.gF,e.gH,kh]
 by_cases hi:i < (c.fH - c.fF) / 6
 . simp only[hi,↓reduceIte]
   rw[qm _ _ (by rw[hlen];omega),qm _ _ (by rw[hlen];omega),
     qm _ _ (by rw[hlen];omega),qm _ _ (by rw[hlen];omega),
     qm _ _ (by rw[hlen];omega),qm _ _ (by rw[hlen];omega)]
 . simp[hi]
lemma vt {n:Nat}{f:Z n}{j:Nat}{c:Cfg}(e:gX n f j c){d:X n}(hlen:d.length<=11) (t:∀r0 r1 r2 r3 r4 r5:F n,f r0=true->f r1=true->f r2=true->f r3=false->f r4=false->f r5=false->3<=(d.map fun p=>zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum):z3 c (va c (eW j c d))=true:=by
 set b:=aR n j c;set m:=(c.fH - c.fF) / 6;unfold z3;rw[e.gJ,e.gK]
 have u:∀(p:K) (i:Nat),z6 (dg c p.1) i<=if i < m then 3 else 0:=by intro p i;unfold dg;rw[e.gF,e.gH,kh];split;exact q52 _ _ _ _ _ _;omega
 have s:=fun i=>q47 (fun p:K=>dg c p.1) m u (e6 b d) (by rw[e6,kY];omega) i
 apply ky _ m
 . intro i;have⟨g,h⟩:=s i;change z6 ((e6 b d).foldr (fun p acc=>add (dg c p.1) acc) 0) i<=_;have v:(e6 b d).length=d.length:=kY _;rw[g];rw[v] at h;by_cases hi:i < m<;>simp only[hi,↓reduceIte] at h ⊢<;>omega
 . intro i hi;have⟨g,_⟩:=s i;change 3<=z6 ((e6 b d).foldr (fun p acc=>add (dg c p.1) acc) 0) i;rw[g]
   have x:((e6 b d).map fun p=>z6 (dg c p.1) i) =
     d.map fun p =>
      zq (p.1 (q1 n (b.getD (c.fF+6*i) 0)))
       (p.1 (q1 n (b.getD (c.fF+6*i+1) 0)))
       (p.1 (q1 n (b.getD (c.fF+6*i+2) 0)))
       (p.1 (q1 n (b.getD (c.fF+6*i+3) 0)))
       (p.1 (q1 n (b.getD (c.fF+6*i+4) 0)))
       (p.1 (q1 n (b.getD (c.fF+6*i+5) 0))):=by
    simp only[e6,hW];apply jH
    intro p _;dsimp only[Function.comp];rw[xy e p.1 i,if_pos hi]
   rw[x]
   obtain⟨y,g',h',z',h4',h5'⟩:=e.gN i hi;exact t _ _ _ _ _ _ y g' h' z' h4' h5'
def ki {n:Nat}:Nat->X n->Z n×Nat
 | _,[]=>((fun _=>false),0)
 | 0,a::_=>a
 | k+1,_::rest=>ki k rest
def yl {n:Nat}:Nat->X n->X n
 | _,[]=>[]
 | 0,_::rest=>rest
 | k+1,a::rest=>a::yl k rest
def bt {n:Nat}(h:Nat)(d:X n):X n:=
 if ble h 32 then
  let c:=sub h 1;let i:=shiftRight c 1;let v:=beq (land c 1) 1
  let (a,ta):=ki i d;let e:=if beq ta 3 then 2 else 0
  let w:=hC a;let r:=yl i d
  if v then (w,e)::(a,0)::r else (w,e)::r
 else
  let g:=sub h 33
  let t:=beq (land g 1) 1
  let u:=beq (land (shiftRight g 1) 1) 1
  let x:=beq (land (shiftRight g 2) 1) 1
  let (i,j):=ik (shiftRight g 3) 16 1
  let (a,ta):=ki i d;let (b,tb):=ki j d
  let r:=yl i (yl j d)
  if x then
   let e:=if beq ta 3||beq tb 3 then 1 else 0
   let r1:=if t then (b,0)::r else r
   let s:=if u then (a,0)::r1 else r1
   (hE a b,e)::s
  else
   let r1:=if t then (b,if beq tb 3 then 1 else 0)::r else r
   let s:=if u then (a,if beq ta 3 then 1 else 0)::r1 else r1
   (hG a b,0)::s
def ip {n:Nat} (b:X n) (PT:Nat->Nat):Nat->Nat->Nat->X n
 | 0,_,_=>b
 | d+1,s,j =>
  let e:=au (PT s) j;let c:=land e 1023
  if beq c 0 then b
  else bt c (ip b PT d (add s 1) (land (shiftRight e 10) 8191))
def ts {n:Nat}(b:Nat)(c:X n)(PT:Nat->Nat)(s j:Nat):X n:=
 ip c PT (sub b s) s j
lemma nk {n:Nat}(c:M)(i:Nat)(b:X n):jw i (e6 c b)=(s8 c (ki i b).1,(ki i b).2):=by
 induction i generalizing b with
 | zero=>cases b with | nil=>simp[jw,ki,e6,im] | cons _ _=>rfl
 | succ k ih=>cases b with | nil=>simp[jw,ki,e6,im] | cons _ t=>exact ih t
lemma nj {n:Nat}(c:M)(i:Nat)(b:X n):cg i (e6 c b)=e6 c (yl i b):=by
 induction i generalizing b with
 | zero=>cases b<;>rfl
 | succ k ih=>cases b with | nil=>rfl | cons p t=>simp only[qy,cg,yl,ih]
lemma xa {n:Nat}(c:M)(b:Nat)(d:X n):re (2 ^ c.length - 1) b (e6 c d)=e6 c (bt b d):=by
 unfold re bt;simp only[v5]
 split
 . simp only[nk,nj];split<;>simp[e6,jf]
 . simp only[nk,nj]
   split
   . cases beq (land (sub b 33) 1) 1<;>cases beq (land (shiftRight (sub b 33) 1) 1) 1<;>simp[e6,q9]
   . cases beq (land (sub b 33) 1) 1<;>cases beq (land (shiftRight (sub b 33) 1) 1) 1<;>simp[e6,qc]
lemma xq {n:Nat}(b:M)(c:X n)(PT:Nat->Nat)(d s j:Nat):cx (2 ^ b.length - 1) (e6 b c) PT d s j=e6 b (ip c PT d s j):=by
 induction d generalizing s j with
 | zero=>rfl
 | succ d ih=>simp only[cx,ip,v5];split;rfl;rw[ih,xa]
lemma ke {n:Nat}(b:M)(c:Nat)(d:X n)(PT:Nat->Nat)(s j:Nat):c8 (2 ^ b.length - 1) c (e6 b d) PT s j=e6 b (ts c d PT s j):=
 xq b d PT (sub c s) s j
lemma xd {n:Nat}(b:Nat)(c:X n)(PT:Nat->Nat)(s j:Nat):c8 (2 ^ (2 ^ n) - 1) b (u2 n c) PT s j=u2 n (ts b c PT s j):=by have hlen:(range (2 ^ n)).length=2 ^ n:=nZ;simpa[u2,e6,u9,hlen] using ke (range (2 ^ n)) b c PT s j
lemma wm {n:Nat}(i:Nat)(b:X n):(yl i b).Sublist b:=by
 induction i generalizing b with
 | zero=>cases b with | nil=>exact List.Sublist.slnil | cons a t=>exact List.Sublist.cons a (List.Sublist.refl t)
 | succ k ih=>cases b with | nil=>exact List.Sublist.slnil | cons a t=>exact List.Sublist.cons_cons a (ih t)
lemma vj {α:Type} (b:Q)(x : α×Nat) (l:List (α×Nat)) (e:x.2<=3)(c:gW l):gW (if b then x::l else l):=by
 intro p d;cases b
 . exact c p d
 . rcases kC.1 d with rfl|h'
   . exact e
   . exact c p h'
lemma vn {α:Type} (x : α×Nat) (l:List (α×Nat)) (b:x.2<=3)(c:gW l):gW (x::l):=by intro p d;rcases kC.1 d with rfl|h';exact b;exact c p h'
lemma q43 {n:Nat}(g:Nat){b:X n}(h:gW b):gW (bt g b):=by
 unfold bt;have c:∀i,gW (yl i b):=fun i p d=>h p ((wm i b).subset d)
 have e:∀i j,gW (yl i (yl j b)):=fun i j p d=>c j p ((wm i _).subset d)
 split
 . dsimp only;split
   . exact vn _ _ (by split<;>omega) (vn _ _ (by omega) (c _))
   . exact vn _ _ (by split<;>omega) (c _)
 . dsimp only;split
   . exact vn _ _ (by split<;>omega)
      (vj _ _ _ (by omega) (vj _ _ _ (by omega) (e _ _)))
   . exact vn _ _ (by omega)
      (vj _ _ _ (by split<;>omega) (vj _ _ _ (by split<;>omega) (e _ _)))
lemma q59 {n:Nat}(b:Nat){c:X n}(h:gW c)(PT:Nat->Nat)(s j:Nat):gW (ts b c PT s j):=by
 unfold ts;generalize sub b s=d
 induction d generalizing s j with
 | zero=>exact h
 | succ d ih=>simp only[ip];split;exact h;exact q43 _ (ih _ _)
lemma pt (T h b lo hi:Nat)(c:lo < hi):av T h b lo hi < hi:=by
 induction b generalizing lo hi with
 | zero=>exact c
 | succ b ih =>
  simp only[av,v5];split
  . rename_i d;have d':lo+2<=hi:=Eq.mp nA d;have e:div (add lo hi) 2=(lo+hi) / 2:=rfl;have g:div (add lo hi) 2 < hi:=by rw[e];omega
    have i:lo < div (add lo hi) 2:=by rw[e];omega
    split;exact ih _ hi g;exact lt_trans (ih lo _ i) g
  . exact c
lemma j8 (NN FL HT:Nat->Nat)(s h:Nat)(b:ar NN FL HT s h≠999999):ar NN FL HT s h < NN s:=by
 unfold ar at b ⊢;simp only[v5] at b ⊢;cases c:beq (NN s) 0
 . rw[c] at b;simp only[jV,↓reduceIte] at b ⊢;have d:0 < NN s:=by have:=y3 c;omega
   cases e:beq (cj (HT s) (av (HT s) h (FL s) 0 (NN s))) h
   . rw[e] at b;simp only[jV,↓reduceIte] at b;exact absurd rfl b
   . simp only[↓reduceIte];exact pt (HT s) h (FL s) 0 (NN s) d
 . rw[c] at b;exact absurd rfl b
lemma qx (a b:K):ce a b=true↔a=b:=by rcases a with ⟨a1,a2⟩;rcases b with ⟨b1,b2⟩;simp[ce,nC]
lemma xj (x:K) (b b':J) (h:jy x b=some b'):b.Perm (x::b'):=by
 induction b generalizing b' with
 | nil=>simp[jy] at h
 | cons a t ih =>
  simp only[jy] at h;split at h
  . rename_i d;cases h;rw[(qx x a).1 d]
  . cases c:jy x t with
    | none=>rw[c] at h;cases h
    | some r=>rw[c] at h;cases h;exact (mR a (ih r c)).trans (List.Perm.swap x a r)
lemma y5 (c b:J)(h:jk c b=true):c.Perm b:=by
 induction c generalizing b with
 | nil=>cases b with | nil=>exact List.Perm.nil | cons _ _=>simp[jk] at h
 | cons a t ih =>
  simp only[jk] at h;cases d:jy a b with
  | none=>rw[d] at h;cases h
  | some b' => rw[d] at h;exact (mR a (ih b' h)).trans (xj a b b' d).symm
lemma xw (x:K)(b:J):(ly x b).Perm (x::b):=by induction b with|nil=>exact mP _|cons a t ih=>simp only[ly];split;exact mP _;exact (mR a ih).trans (List.Perm.swap x a t)
lemma q64 (b:J):(bu b).Perm b:=by induction b with|nil=>exact List.Perm.nil|cons a t ih=>exact (xw a (bu t)).trans (mR a ih)
lemma kg {n:Nat}(b shTT:Nat)(c:X n):bn shTT (e6 (e8 n b shTT) c)=u2 n c:=by
 induction c with
 | nil=>rfl
 | cons p t ih =>
  rcases p with ⟨g,tg⟩;simp only[qy,pd,bn,v5,ih]
  have d:=cy (n:=n) (ee n b shTT) g;rw[jj n b shTT] at d;rw[e8,d]
lemma yk {n:Nat}{f:Z n}{g:V}(c:vh f g)(b:X n):∃π:(F n)->(F n),Bijective π/\(∀x,f (π x)=f x)/\wx g (u2 n b)=u2 n (b.map fun p=>((fun x=>p.1 (π x)),p.2)):=by
 obtain⟨π,d,e,i⟩:=c;refine⟨π,d,e,?_⟩
 induction b with|nil=>rfl|cons p t ih=>rcases p with ⟨h,tg⟩;simp only[pd,kB,wx,v5,i,ih]
lemma yv {α β:Type} {f : α->β} (d:Injective f):
  ∀{c b:List α},(c.map f).Perm (b.map f)->c.Perm b
 | [],b,hp=>by cases b with | nil=>exact List.Perm.nil | cons _ _=>exact absurd hp.length_eq (by simp)
 | x::c,b,hp=>by
  have e:f x∈b.map f:=hp.subset (by simp)
  obtain⟨y,hy,g⟩:=mM.1 e
  have h:y=x:=d g;subst h
  obtain⟨l1,l2,rfl⟩:=List.append_of_mem hy
  have i:(f y::c.map f).Perm (f y::(l1++l2).map f):=
   hp.trans (by simpa[kX] using (mE (a:=f y) (l₁:=l1.map f) (l₂:=l2.map f)))
  exact (mR y (yv d (List.Perm.cons_inv i))).trans mE.symm
lemma zv {n:Nat}(c d:X n):(u2 n c).Perm (u2 n d)↔c.Perm d:=by
 constructor
 . intro b;have g:Injective (fun p:Z n×Nat=>(u9 n p.1,p.2)):=fun ⟨_,_⟩ ⟨_,_⟩ e=>by
    simp only[Prod.mk.injEq] at e;exact Prod.ext (yc e.1) e.2
   exact yv g b
 . exact fun b=>b.map _
lemma q19 {n:Nat}{f:Z n}{g:V}(h:vh f g)(c:J)(b:X n) (d:c.Perm (u2 n b)):∃π:(F n)->(F n),Bijective π/\(∀x,f (π x)=f x)/\(ij g c).Perm (u2 n (b.map fun p=>((fun x=>p.1 (π x)),p.2))):=by
 unfold ij;dsimp only;split
 . obtain⟨π,i,j,s⟩:=yk h b;refine⟨π,i,j,?_⟩
   have e:∀l,wx g l=l.map (fun p=>(ym g p.1,p.2)):=fun l=>by
    induction l with|nil=>rfl|cons p t ih=>simp[wx,v5,ih]
   have u:(wx g c).Perm (wx g (u2 n b)):=(by rw[e,e];exact d.map _);exact (q64 _).trans (u.trans (by rw[s]))
 . exact⟨id,bijective_id,fun _=>rfl,by simpa using d⟩
lemma q20 {n:Nat}{f:Z n} (d:List (V)) (e:∀g∈d,vh f g)(b:J)(c:X n) (h:b.Perm (u2 n c)):∃π:(F n)->(F n),Bijective π/\(∀x,f (π x)=f x)/\(fr d b).Perm (u2 n (c.map fun p=>((fun x=>p.1 (π x)),p.2))):=by
 induction d generalizing b c with
 | nil=>exact⟨id,bijective_id,fun _=>rfl,by simpa[fr] using h⟩
 | cons g rest ih=>obtain⟨π1,i,j,s⟩:=q19 (e g (by simp)) b c h;obtain⟨π2,t,u,v⟩:=ih (fun g' y=>e g' (hX g y)) (ij g b) _ s;exact⟨π1 ∘ π2,i.comp t,fun x=>by simp[j,u],by simpa[fr,hW,mN] using v⟩
lemma xb {n:Nat}{f:Z n} (c:List (V)) (d:∀g∈c,vh f g)(b:X n):∃π:(F n)->(F n),Bijective π/\(∀x,f (π x)=f x)/\(cn c (u2 n b)).Perm (u2 n (b.map fun p=>((fun x=>p.1 (π x)),p.2))):=by
 unfold cn;have e:=q64 (u2 n b);cases c with
 | nil=>exact⟨id,bijective_id,fun _=>rfl,by simpa using e⟩
 | cons g i =>
  cases i with
  | nil=>exact q19 (d g (by simp)) _ b e
  | cons g2 h=>obtain⟨π1,j,s,t⟩:=q20 (g::g2::h) d _ b e;obtain⟨π2,u,v,y⟩:=q20 (g::g2::h) d _ _ t;exact⟨π1 ∘ π2,j.comp u,fun x=>by simp[s,v],by simpa[hW,mN] using y⟩
def w2 {n:Nat}(f:Z n)(b:M)(NN:Nat->Nat)(R_bfn:Nat->Nat->X n)(c:Nat->J->Q):Prop:=
 ∀s zs_b,c s (e6 b zs_b)=true ->
  ∃j < NN s,∃π:(F n)->(F n),
   Bijective π/\(∀x,f (π x)=f x) /\
   (zs_b.map fun p=>((fun x=>p.1 (π x)),p.2)).Perm (R_bfn s j)
lemma q87 {n:Nat}(f:Z n)(c shTT d:Nat)(NN FL HT:Nat->Nat)(R_bfn:Nat->Nat->X n)(Rtt:Nat->Nat->J) (e:∀s j,Rtt s j=u2 n (R_bfn s j)):w2 f (e8 n c shTT) NN R_bfn (uh shTT d Rtt NN FL HT):=by
 intro s g h;unfold uh at h;simp only[v5,kg,jY,kt,zh] at h;obtain⟨i,b⟩:=h;rw[e] at b;exact⟨_,j8 NN FL HT s _ i,id,bijective_id,fun _=>rfl,
  by simpa using (zv g (R_bfn s _)).1 (y5 _ _ b)⟩
lemma q86 {n:Nat}(f:Z n)(t shTT u:Nat)(d:V)(v:vh f d)(NN FL HT:Nat->Nat)(R_bfn:Nat->Nat->X n)(Rtt:Nat->Nat->J) (e:∀s j,Rtt s j=u2 n (R_bfn s j)):w2 f (e8 n t shTT) NN R_bfn (p5 shTT u d Rtt NN FL HT):=by
 intro s g h;unfold p5 at h;simp only[v5,kg] at h
 split at h
 . rename_i i;simp only[jY,kt,zh] at i;obtain⟨c,b⟩:=i;rw[e] at b;exact⟨_,j8 NN FL HT s _ c,id,bijective_id,fun _=>rfl,
    by simpa using (zv g (R_bfn s _)).1 (y5 _ _ b)⟩
 . simp only[jY,kt,zh] at h;obtain⟨c,b⟩:=h;obtain⟨π,x,y,z⟩:=yk v g;rw[z] at c b;rw[e] at b;exact⟨_,j8 NN FL HT s _ c,π,x,y,(zv _ _).1 (y5 _ _ b)⟩
lemma q37 {n:Nat}(f:Z n)(y shTT i:Nat) (d:List (V)) (z:∀g∈d,vh f g)(NN FL HT:Nat->Nat)(R_bfn:Nat->Nat->X n)(Rtt:Nat->Nat->J) (t:∀s j,Rtt s j=u2 n (R_bfn s j)):w2 f (e8 n y shTT) NN R_bfn (i9 shTT i d Rtt NN FL HT):=by
 have h1:∀p:List (V),(∀g∈p,vh f g)->∀s (b:X n),
   vm i Rtt NN FL HT s p (u2 n b)=true ->
   ∃j < NN s,∃π:(F n)->(F n),Bijective π/\(∀x,f (π x)=f x) /\
     (b.map fun q=>((fun x=>q.1 (π x)),q.2)).Perm (R_bfn s j):=by
  intro p;induction p with
  | nil =>
   intro _ s b h;simp only[vm,v5,jY,kt,zh] at h;obtain⟨e,c⟩:=h;rw[t] at c;exact⟨_,j8 NN FL HT s _ e,id,bijective_id,fun _=>rfl,
     by simpa using (zv b (R_bfn s _)).1 (y5 _ _ c)⟩
  | cons g rest ih =>
   intro u s b h;simp only[vm,v5] at h
   split at h
   . rename_i v;simp only[jY,kt,zh] at v;obtain⟨e,c⟩:=v;rw[t] at c;exact⟨_,j8 NN FL HT s _ e,id,bijective_id,fun _=>rfl,
      by simpa using (zv b (R_bfn s _)).1 (y5 _ _ c)⟩
   . obtain⟨π1,h2,h3,h4⟩:=yk (u g (by simp)) b;rw[h4] at h;obtain⟨j,hj,π2,h5,h6,h7⟩:=ih (fun g' hm=>u g' (hX g hm)) s _ h;exact⟨j,hj,π1 ∘ π2,h2.comp h5,fun x=>by simp[h3,h6],by simpa[hW,mN] using h7⟩
 intro s b h;unfold i9 at h;rw[kg] at h;exact h1 d z s b h
lemma q55 {n:Nat}(f:Z n)(u shTT d:Nat) (b:List (V)) (v:∀g∈b,vh f g)(e:Nat->V) (y:∀k,vh f (e k)) (NN FL HT PT:Nat->Nat)(R_bfn:Nat->Nat->X n)(Rtt:Nat->Nat->J) (z:∀s j,Rtt s j=u2 n (R_bfn s j)):w2 f (e8 n u shTT) NN R_bfn (f8 shTT d b e Rtt NN FL HT PT):=by
 intro s i h;unfold f8 at h;simp only[v5,kg] at h
 split at h;. cases h
 . rename_i h0
   have h1:=y3 (jU.2 h0);set j:=ar NN FL HT s (gz d (cn b (u2 n i)));have hj:j < NN s:=j8 NN FL HT s _ h1;set h2:=shiftRight (au (PT s) j) 23;obtain⟨π1,h3,h4,h5⟩:=xb b v i;obtain⟨π2,h6,h7,h8⟩:=yk (y h2) (R_bfn s j);rw[z,h8] at h;have h9:=(zv _ _).1 (h5.symm.trans (y5 _ _ h));obtain⟨π2_inv,x2,c⟩:=Function.bijective_iff_has_inverse.1 h6;have x3:Bijective π2_inv:=Function.bijective_iff_has_inverse.2 ⟨π2,c,x2⟩;have a1:∀x,f (π2_inv x)=f x:=fun x=>by have:=h7 (π2_inv x);rw[c x] at this;exact this.symm
   refine⟨j,hj,π1 ∘ π2_inv,h3.comp x3,fun x=>by simp[h4,a1],?_⟩
   have t:=h9.map (fun p:Z n×Nat=>((fun x=>p.1 (π2_inv x)),p.2));have a2:(((R_bfn s j).map fun p=>((fun x=>p.1 (π2 x)),p.2)).map fun p=>((fun x=>p.1 (π2_inv x)),p.2))=R_bfn s j:=by
    rw[hW]
    have b0:((fun p:Z n×Nat=>((fun x=>p.1 (π2_inv x)),p.2)) ∘ fun p:Z n×Nat=>((fun x=>p.1 (π2 x)),p.2))=id:=(by funext ⟨g,tg⟩;simp only[mN,id];congr 1;funext x;exact congrArg g (c x));rw[b0,pA]
   rw[a2] at t;simpa[hW,mN] using t
lemma hH (P:Nat->Q)(c b:Nat)(h:jM P c b=true):∀i,b<=i->i < b+c->P i=true:=by
 induction c generalizing b with
 | zero=>intro i d e;omega
 | succ m ih =>
  simp only[jM,jY] at h;intro i d e;by_cases g:i=b
  . subst g;exact h.1
  . exact ih (b+1) h.2 i (by omega) (by omega)
def k8 (c:Cfg)(w tg sC sU s0 s1:Nat):WF:=
 ⟨w,tg,wi c w,tx c w,wC c w,wU c w,sc c w,th c w,dg c w,sC,sU,s0,s1⟩
lemma dd (c:Cfg)(w tg sC sU s0 s1:Nat):(k8 c w tg sC sU s0 s1).tg=tg:=rfl
def ov {n:Nat}(f:Z n)(b:X n):Prop:=
 ∀r0 r1 r2 r3 r4 r5:F n,f r0=true->f r1=true->f r2=true ->
  f r3=false->f r4=false->f r5=false ->
  3<=(b.map fun p=>zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum
lemma n9 (c:Cfg) (b:J):
  let t:=e4 c b
  t.1=yx c b/\t.2.1=v4 c b/\t.2.2.1=zf c b/\t.2.2.2.1=va c b:=by
 induction b with
 | nil=>simp[e4,yx,v4,zf,va]
 | cons p d ih =>
  rcases p with ⟨w,tg⟩;obtain⟨e,g,h,i⟩:=ih;dsimp only;unfold e4
  rw[show e4 c d=(yx c d,v4 c d,zf c d,va c d,(e4 c d).2.2.2.2) from
   Prod.ext e (Prod.ext g (Prod.ext h (Prod.ext i rfl)))]
  simp only[v5,yp,vo,k0,w1,wC,wU,wi,tx,th,sc,dg,and_self]
lemma o4 (c:Cfg)(w tg:Nat)(b:J):(e4 c ((w,tg)::b)).2.2.2.2=k8 c w tg (yx c b) (v4 c b) (zf c b) (va c b)::(e4 c b).2.2.2.2:=by
 obtain⟨d,e,g,h⟩:=n9 c b;conv_lhs=>unfold e4
 rw[show e4 c b=(yx c b,v4 c b,zf c b,va c b,(e4 c b).2.2.2.2) from Prod.ext d (Prod.ext e (Prod.ext g (Prod.ext h rfl)))]
 simp only[v5,k8,wi,tx,wC,wU,sc,th,dg]
lemma d8 (c:Cfg)(d b:J):k9 d (e4 c b).2.2.2.2=b++d:=by
 induction b with
 | nil=>rfl
 | cons p rest ih=>rcases p with ⟨w,tg⟩;rw[o4,k9,ih];rfl
lemma ek (z:Nat)(b:J):p4 z b=false↔∀p∈b,p.1≠z:=by
 induction b with
 | nil=>simp[p4]
 | cons a t ih=>rcases a with ⟨w,tg⟩;simp only[p4,nE,zh,ih,kC,forall_eq_or_imp]
lemma oq {n b:Nat}{c:Cfg}{g:Z n}{d:X n}(h:∀p∈d,p.1≠g):p4 (eL b c g) (eW b c d)=false:=by
 rw[ek];intro p i;rcases mM.1 i with ⟨q,j,rfl⟩
 exact fun e=>h q j (nz (ee n b c.fH) e)
lemma ad {n b:Nat}{c:Cfg}{g:Z n}(d:g≠fun _=>false):eL b c g≠0:=by intro e;rw[<- im (n:=n) (aR n b c)] at e;exact d (nz (ee n b c.fH) e)
lemma mn {n b:Nat}{f:Z n}{c:Cfg}(d:gX n f b c){g:Z n}(h:g≠fun _=>true):eL b c g≠c.fJ:=by intro e;have hlen:=zl n b c.fH;rw[d.fY,<- hlen,<- rf (n:=n) (aR n b c)] at e;exact h (nz (ee n b c.fH) e)
lemma f4 {n b:Nat}{f:Z n}{c:Cfg}(e:gX n f b c){g:Z n}{d:X n}(h:g≠fun _=>false)(i:g≠fun _=>true)(j:∀p∈d,p.1≠g):x5 c (eW b c d) (eL b c g)=false:=by unfold x5;simp[q2 (ad h),q2 (mn e i),oq j]
lemma bk {n e:Nat}{f:Z n}{c:Cfg}(d:gX n f e c)(a b:Nat):wU c (lor a b)=land (wC c (lor a b)) (lor (tx c a) (tx c b)):=by
 unfold wU;congr 1;apply kL;intro i;rw[vl d,kR,kM,kR,kM,vl d,vl d]
 by_cases hi:i < c.k<;>simp[hi]
lemma ag {n e:Nat}{f:Z n}{c:Cfg}(d:gX n f e c)(a b:Nat):wU c (land a b)=land (wC c (land a b)) (land (tx c a) (tx c b)):=by
 unfold wU;congr 1;apply kL;intro i;rw[vl d,kS,kN,kS,kN,vl d,vl d]
 by_cases hi:i < c.k<;>simp[hi]
lemma ox {n j:Nat}{f:Z n}{c:Cfg}(e:gX n f j c){d:X n}(hlen:d.length<=11) (t:∀r0 r1 r2 r3 r4 r5:F n,f r0=true->f r1=true->f r2=true->f r3=false->f r4=false->f r5=false->3<=(d.map fun p=>v6 (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum):qb c (zf c (eW j c d)) 0=true:=by
 set b:=aR n j c;set m:=(c.fF - c.fE) / 6;unfold qb;simp only[v8,mH];rw[e.gD,e.gE]
 have u:∀(p:K) (i:Nat),z6 (th c p.1) i<=if i < m then 3 else 0:=by intro p i;unfold th;rw[e.gC,yy];split;exact yr _ _ _ _ _ _;omega
 have s:=fun i=>q47 (fun p:K=>th c p.1) m u (e6 b d) (by rw[e6,kY];omega) i
 apply ky _ m
 . intro i;have⟨g,h⟩:=s i;change z6 ((e6 b d).foldr (fun p acc=>add (th c p.1) acc) 0) i<=_;have v:(e6 b d).length=d.length:=kY _;rw[g];rw[v] at h;by_cases hi:i < m<;>simp only[hi,↓reduceIte] at h ⊢<;>omega
 . intro i hi;have⟨g,_⟩:=s i;change 3<=z6 ((e6 b d).foldr (fun p acc=>add (th c p.1) acc) 0) i;rw[g]
   have x:((e6 b d).map fun p=>z6 (th c p.1) i) =
     d.map fun p =>
      v6 (p.1 (q1 n (b.getD (c.fE+6*i) 0))) (p.1 (q1 n (b.getD (c.fE+6*i+1) 0)))
       (p.1 (q1 n (b.getD (c.fE+6*i+2) 0))) (p.1 (q1 n (b.getD (c.fE+6*i+3) 0)))
       (p.1 (q1 n (b.getD (c.fE+6*i+4) 0))) (p.1 (q1 n (b.getD (c.fE+6*i+5) 0))):=by
    simp only[e6,hW];apply jH
    intro p _;dsimp only[Function.comp];rw[xx e p.1 i,if_pos hi]
   rw[x];obtain⟨y,g',h',z',h4',h5'⟩:=e.gM i hi;exact t _ _ _ _ _ _ y g' h' z' h4' h5'
lemma tj (c:Cfg)(a b:Nat) (h:qb c (add b a) 0=true):qb c a b=true:=by
 unfold qb at h ⊢;have d:add (add a b) c.fN=add (add (add b a) 0) c.fN:=by simp only[v8];omega
 rw[d];exact h
lemma sp {n d:Nat}{f:Z n}{c:Cfg}(e:gX n f d c){s:Nat}{b:X n} (h:Run (hC (n:=n)) hE hG f s (b.map fst)) (heq:b.length=s+1):v4 c (eW d c b)=c.fL:=
 q6 e fun u v hu hv=>by
  obtain⟨g,hg,h1,h2⟩:=sv h (by simp[heq]) u v hu hv
  obtain⟨p,hp,rfl⟩:=mM.1 hg;exact⟨p,hp,h1,h2⟩
lemma aq {n d:Nat}{f:Z n}{c:Cfg}(e:gX n f d c){s:Nat}{b:X n} (g:Run (hC (n:=n)) hE hG f s (b.map fst)) (hlen11:b.length<=11) (heq:b.length=s+1):qb c (zf c (eW d c b)) 0=true:=
 ox e hlen11 fun r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5=>by
  have:=dm g (by simp[heq]) r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5;rwa[hW] at this
lemma ue {n h:Nat}{f:Z n}{c:Cfg}(i:gX n f h c){s:Nat}{b:X n} (j:Run (hC (n:=n)) hE hG f s (b.map fst)) (heq:b.length=s):v4 c (eW h c b)=c.fL\/ov f b:=by
 rcases aj j (by simp[heq]) with t|x
 . left;exact q6 i fun u v d e=>by
    obtain⟨g,y,z,hb⟩:=t u v d e;obtain⟨p,hp,rfl⟩:=mM.1 y;exact⟨p,hp,z,hb⟩
 . right;intro r0 r1 r2 r3 r4 r5 h0 d e h3 h4 h5
   have:=x r0 r1 r2 r3 r4 r5 h0 d e h3 h4 h5;rwa[hW] at this
lemma y4 {n:Nat}{f:Z n}{h:Nat}{g r:X n}{a:Z n}{ta zt:Nat} (i:g.Perm ((a,ta)::r)) (hlen:g.length=h+1) (u:Run (hC (n:=n)) hE hG f h (((hC a,zt)::r).map fst)):ov f g:=by
 have v:∀(l:X n) (r0 r1 b c d e:F n),
   (l.map fun p=>v6 (p.1 r0) (p.1 r1) (p.1 b) (p.1 c) (p.1 d) (p.1 e)).sum <=
   (l.map fun p=>zq (p.1 r0) (p.1 r1) (p.1 b) (p.1 c) (p.1 d) (p.1 e)).sum:=by
  intro l r0 r1 b c d e;induction l with
  | nil=>simp
  | cons x t iht=>simp only[kB,jN];have:=k7 (x.1 r0) (x.1 r1) (x.1 b) (x.1 c) (x.1 d) (x.1 e);omega
 intro r0 r1 b c d e y z h2 h3 h4 h5;have j:=dm u (by have:=i.length_eq;simp at this ⊢;omega) r0 r1 b c d e y z h2 h3 h4 h5;rw[hW] at j;have s:=le_trans j (v _ r0 r1 b c d e);simp only[kB,jN,hC,jp] at s;rw[(i.map _).sum_eq];exact s
lemma i4 {n:Nat}{f:Z n}{isOr:Q}{i r:X n}{a b:Z n}{ta j s:Nat} (t:i.Perm ((a,ta)::(b,j)::r)) (u:ov f ((if isOr then hG a b else hE a b,s)::r)):ov f i:=by
 intro r0 r1 c d e g v h x y z h5;have h:=u r0 r1 c d e g v h x y z h5;rw[(t.map _).sum_eq];simp only[kB,jN] at h ⊢;cases isOr
 . simp only[jV,↓reduceIte,hE] at h
   have:=je (a r0) (a r1) (a c) (a d) (a e) (a g) (b r0) (b r1) (b c) (b d) (b e) (b g);omega
 . simp only[↓reduceIte,hG] at h
   have:=q14 (a r0) (a r1) (a c) (a d) (a e) (a g) (b r0) (b r1) (b c) (b d) (b e) (b g);omega
lemma p3 {n e:Nat}{f:Z n}{c:Cfg}(g:gX n f e c){d:Nat}{b:X n} (i:Run (hC (n:=n)) hE hG f (d+1) (b.map fst)):((ble b.length 11&&beq (sub (add d 2) b.length) 0||ble b.length 11&&beq (sub (add d 2) b.length) 1&&!(z3 c (va c (eW e c b))))&&!(beq (v4 c (eW e c b)) c.fL))=false:=by
 have hlen_le:b.length<=d+2:=by have:=oy i;simpa using this
 rw[jU];intro h;simp only[jY,jX,kt,zh,nA,nC,nY,nX] at h;obtain⟨h1|⟨⟨t,hsub1⟩,j⟩,s⟩:=h
 . exact s (sp g i (by omega))
 . rcases ue g i (by omega) with u|v
   . exact s u
   . rw[vt g t v] at j;cases j
lemma o3 {n e:Nat}{f:Z n}{c:Cfg}(i:gX n f e c){d b h1 t x h2:Nat}{y:Q}{z h3:Unit->Nat}{h7:Unit->Q}{z_b:Z n}{z_t:Nat}{rem_b:X n}(hlen_eq:b=rem_b.length+1) (x2:h1=yx c (eW e c ((z_b,z_t)::rem_b))) (h8:t=v4 c (eW e c ((z_b,z_t)::rem_b))) (x3:add (z ()) x=zf c (eW e c ((z_b,z_t)::rem_b))) (a1:add h2 (h3 ())=va c (eW e c ((z_b,z_t)::rem_b))) (a2:y=true->¬ov f ((z_b,z_t)::rem_b)) (j:Run (hC (n:=n)) hE hG f d (((z_b,z_t)::rem_b).map fst)) (hinc:k5 c d b h1 t x h2 y z h3 h7=true):h7 ()=true:=by
 have hlen_le:rem_b.length+1<=d+1:=by have:=oy j;simpa using this
 unfold k5 at hinc;have b0:blt (add d 1) b=false:=by rw[jU];intro h;rw[nB] at h;change d+1 < b at h;omega
 simp only[b0,jV,↓reduceIte] at hinc;cases d with
 | zero=>simp only[nD,↓reduceIte] at hinc;exact hinc
 | succ s' =>
  have b1:beq (s'+1) 0=false:=q2 (nP s');have b3:h1=c.fL:=x2.trans (zz i fun u v hu hv=>by
    obtain⟨g,hg,c2⟩:=ux j (show f u≠f v by rw[hu,hv];decide);obtain⟨p,hp,rfl⟩:=mM.1 hg;exact⟨p,hp,c2⟩)
  simp only[b1,b3,nD,nH,jV,↓reduceIte] at hinc;cases h4:ble b 11
  . simp only[h4,jV,↓reduceIte] at hinc;exact hinc
  . simp only[h4,↓reduceIte] at hinc;have h9:((z_b,z_t)::rem_b).length<=11:=by rw[nA] at h4;simp;omega
    by_cases h5:sub (add (s'+1) 1) b=0
    . have h0:((z_b,z_t)::rem_b).length=(s'+1)+1:=(by change (s'+1)+1 - b=0 at h5;simp;omega);have c3' : t=c.fL:=h8.trans (sp i j h0);have d1' : qb c x (z ())=true:=tj c x (z ()) (x3.symm ▸ aq i j h9 h0);simp only[qz h5,c3',nD,nH,jV,↓reduceIte,d1'] at hinc;exact hinc
    . simp only[q2 h5,jV,↓reduceIte] at hinc;by_cases h6' : sub (add (s'+1) 1) b=1
      . have h0:((z_b,z_t)::rem_b).length=s'+1:=(by change (s'+1)+1 - b=1 at h6';simp;omega);simp only[qz h6',↓reduceIte] at hinc;rcases ue i j h0 with hu|hs
        . simp only[h8.trans hu,nD,↓reduceIte] at hinc;exact hinc
        . have d2:y=false:=(by cases h:y;rfl;exact absurd hs (a2 h));have e0:z3 c (add h2 (h3 ()))=true:=a1.symm ▸ vt i h9 hs;by_cases e1:beq t c.fL=true<;>simp only[e1,d2,jV,↓reduceIte,e0] at hinc<;>exact hinc
      . simp only[q2 h6',jV,↓reduceIte] at hinc;exact hinc
lemma o7 {b c:Q} (h:(if !b then false else c)=true):b=true/\c=true:=by cases b<;>simp_all
lemma eu (b b2 c c1 d e:Q)
  (h:(let g:=if b2 then c1 else true
   let i:=if g&&b then d else g
   if i&&b&&b2&&c then e else i)=true):
  (b2=true->c1=true)/\(b=true->d=true)/\(b=true->b2=true->c=true->e=true):=by
 cases b<;>cases b2<;>cases c<;>cases c1<;>cases d<;>cases e<;>simp_all
lemma o6 {n b:Nat}{f:Z n}{c:Cfg}(i:gX n f b c){e:Nat}{j:X n}{g:J->Q}{z_b:Z n}{d:Nat}{rem_b:X n}(t:z_b≠fun _=>false)(u:z_b≠fun _=>true)(v:∀p∈j,p.1≠z_b) (x:Run (hC (n:=n)) hE hG f e (((z_b,d)::rem_b).map fst)) (hrun:(if x5 c (eW b c j) (eL b c z_b) then true else if beq e 0 then match eW b c ((z_b,d)::rem_b) with | [(w,_)]=>if beq w c.fK then g [(w,d)] else true | _=>true else g (eW b c ((z_b,d)::rem_b)))=true):g (eW b c ((z_b,d)::rem_b))=true:=by
 rw[f4 i t u v] at hrun;simp only[jV,↓reduceIte] at hrun;cases e with
 | zero =>
  have h:=sx x;cases rem_b with
  | nil =>
   simp only[kB,mS,List.cons.injEq] at h;rcases h with ⟨rfl,_⟩
   simp only[nD,↓reduceIte,eW,e6,kB,mS,i.fZ] at hrun ⊢;exact hrun
  | cons _ _=>simp at h
 | succ s' => simp only[q2 (nP s'),jV,↓reduceIte] at hrun;exact hrun
lemma ey {α : Type _} {c d:Q}{z a b : α} {r r' : List α} (h:r.Perm r'):(z::qk c a (qk d b r)).Perm (z::qk c a (qk d b r')):=
 mR z (by cases c<;>cases d<;>simp[qk,h,mR])
lemma i0 {α : Type _} {c d:Q}{z a b : α} {r r' : List α} (h:r.Perm r'):(z::qk c a (qk d b r)).Perm (z::qk d b (qk c a r')):=
 mR z (by
  cases c<;>cases d<;>simp only[qk,↓reduceIte,jV]
  . exact h
  . exact mR b h
  . exact mR a h
  . exact (List.Perm.swap b a r).trans (mR b (mR a h)))
lemma o2 {α : Type _} (b c:List α):(b++c).Perm (c++b.reverse):=
 List.perm_append_comm.trans (List.Perm.append_left c (List.reverse_perm b).symm)
lemma bv {α : Type _} (c d e:List α)(a b : α):(c++a::d++b::e).Perm (a::b::(c++d++e)):=
 ((mE (l₁:=c++a::d) (a:=b) (l₂:=e)).trans
  (mR b (by simpa[kA] using mE (l₁:=c) (a:=a) (l₂:=d++e)))).trans
  (List.Perm.swap a b _)
lemma y0 {n b:Nat}{c:Cfg}(l:X n):(eW b c l).reverse=eW b c l.reverse:=by simp[eW,e6,List.map_reverse]
lemma es {n b:Nat}{c:Cfg}(d e:X n):eW b c d++eW b c e=eW b c (d++e):=by simp[eW,e6,kX]
lemma er {n b:Nat}{c:Cfg}(d e:X n):(eW b c e).reverse++(eW b c d).reverse=eW b c (d++e).reverse:=by rw[mU,y0,y0,es]
lemma s5 {n b:Nat}{c:Cfg}(d e g:X n):eW b c g++(eW b c e).reverse++(eW b c d).reverse=eW b c (g++(d++e).reverse):=by rw[kA,er,es]
lemma s3 {α : Type _} {g c d e:List α}{a b : α}(h:g=c++a::d++b::e):g.Perm (a::b::(e++(c++d).reverse)):=by rw[h];exact (bv c d e _ _).trans (mR _ (mR _ (o2 (c++d) e)))
lemma l4 {a b:Nat}(h:b<=a):blt a b=false:=by rw[jU];intro c;rw[nB] at c;omega
lemma t4 {n b:Nat}{c:Cfg}(g:Z n)(t:Nat)(l:X n):eW b c ((g,t)::l)=(eL b c g,t)::eW b c l:=rfl
lemma mq (a b x y:Nat):cond (beq a b) x y=(if a=b then x else y):=by by_cases h:a=b<;>simp[h,q2]
lemma b6 (a b k x y:Nat):cond (beq a k||beq b k) x y=(if a=k\/b=k then x else y):=by by_cases c:a=k<;>by_cases d:b=k<;>simp[c,d,q2]
lemma uu (c:Cfg)(d:Nat)(b:J) (h:b9 c d (e4 c b).2.2.2.2=false):∀p∈b,qb c d (th c p.1)=false:=by
 induction b with
 | nil=>simp
 | cons x t ih =>
  rcases x with ⟨w,tg⟩
  rw[o4,b9,nE] at h;intro p e;rcases kC.1 e with rfl|g;exact h.1;exact ih h.2 p g
lemma uc {n g:Nat}{f:Z n}{c:Cfg}(y:gX n f g c){t:Nat}{isOr:Q}{e j:X n}{b d h:Z n}{ta z u s:Nat} (v:e.Perm ((b,ta)::(d,z)::j)) (hlen10:e.length<=10)(hlen:e.length=t+1) (hr:Run (hC (n:=n)) hE hG f t (((if isOr then hG b d else hE b d,u)::(h,s)::j).map fst)) (hqb:qb c (zf c (eW g c e)) (th c (eL g c h))=false):False:=by
 have h6:((if isOr then hG b d else hE b d,u)::(h,s)::j).length=t+1:=by have:=v.length_eq;simp at this ⊢;omega
 have h7:((h,s)::e).length<=11:=by simp;omega
 have x:qb c (zf c (eW g c ((h,s)::e))) 0=true:=
  ox y h7 fun r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5=>by
   have i:=dm hr (by simpa using h6) r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5;rw[hW] at i;simp only[kB,jN,mN] at i ⊢;change 3<=_+(_+(j.map fun p=>v6 (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum) at i;rw[(v.map _).sum_eq];simp only[kB,jN];cases isOr
   . simp only[jV,↓reduceIte,hE] at i
     have:=kl (b r0) (b r1) (b r2) (b r3) (b r4) (b r5) (d r0) (d r1) (d r2) (d r3) (d r4) (d r5)
     omega
   . simp only[↓reduceIte,hG] at i
     have:=w4 (b r0) (b r1) (b r2) (b r3) (b r4) (b r5) (d r0) (d r1) (d r2) (d r3) (d r4) (d r5)
     omega
 rw[t4,k0] at x
 have:=tj c (zf c (eW g c e)) (th c (eL g c h)) x
 rw[hqb] at this;cases this
lemma p8 (c:Cfg)(s:J)(t:J->Q)(forG:Q)(u:WF)(e g d:J)(b i:Nat) (h:d0 c s t forG u (v4 c e) e (e4 c (g++(b,i)::d)).2.2.2.2=true):sz c s t forG u (k8 c b i (yx c d) (v4 c d) (zf c d) (va c d)) (v4 c (d++g.reverse++e)) (g.reverse++e) (e4 c d).2.2.2.2=true:=by
 induction g generalizing e with
 | nil=>simp only[mT,mV,hU,o4] at h ⊢;unfold d0 at h;simp only[v5] at h;have v:=(Eq.mp (jY) h).1;rwa[show (k8 c b i (yx c d) (v4 c d) (zf c d) (va c d)).sU=v4 c d from rfl,show lor (v4 c e) (v4 c d)=v4 c (d++e) by rw[zu,q7]] at v
 | cons p rest ih =>
  rcases p with ⟨w,tg⟩;simp only[kZ,o4] at h
  unfold d0 at h;simp only[v5] at h;have j:=(Eq.mp (jY) h).2;dsimp only[k8] at j;rw[show lor (v4 c e) (wU c w)=v4 c ((w,tg)::e) by rw[vo,q7]] at j;simpa[kF,kA] using ih ((w,tg)::e) j
lemma et (c:Cfg)(t:J)(u:J->Q)(forG:Q)(e j g d:J)(a ta b i:Nat) (h:d5 c t u forG (v4 c e) e (e4 c (j++(a,ta)::g++(b,i)::d)).2.2.2.2=true):sz c t u forG (k8 c a ta (yx c (g++(b,i)::d)) (v4 c (g++(b,i)::d)) (zf c (g++(b,i)::d)) (va c (g++(b,i)::d))) (k8 c b i (yx c d) (v4 c d) (zf c d) (va c d)) (v4 c (d++g.reverse++j.reverse++e)) (g.reverse++j.reverse++e) (e4 c d).2.2.2.2=true:=by
 induction j generalizing e with
 | nil=>simp only[mT,mV,hU,kZ,o4] at h ⊢;unfold d5 at h;exact p8 c t u forG _ e g d b i (Eq.mp (jY) h).1
 | cons p rest ih =>
  rcases p with ⟨w,tg⟩;simp only[kZ,o4] at h
  unfold d5 at h;have s:=(Eq.mp (jY) h).2;simp only[v5] at s;dsimp only[k8] at s;rw[show lor (v4 c e) (wU c w)=v4 c ((w,tg)::e) by rw[vo,q7]] at s;simpa[kF,kA] using ih ((w,tg)::e) s
lemma c9 {n b:Nat}{f:Z n}{c:Cfg}(h:gX n f b c){y:Nat}{isOr forG ka kb:Q}{g i j s:X n}{h9:J->Q}{d e:Z n}{ta u z x3 a1:Nat} (h4:g=i++(d,ta)::j++(e,u)::s) (h5:(ble g.length 11&&beq (sub (add y 2) g.length) 1&&!(z3 c (va c (eW b c g)))&&ble g.length 10&&!(beq y 0)&&!(b9 c (zf c (eW b c g)) (e4 c (eW b c g)).2.2.2.2))=true) (h6:x8 forG isOr ta u=true)(h7:z=sq forG isOr ta u) (h0:(if isOr then hG d e else hE d e)≠fun _=>false) (h1:(if isOr then hG d e else hE d e)≠fun _=>true) (h8:∀p∈g,p.1≠if isOr then hG d e else hE d e) (t:Run (hC (n:=n)) hE hG f y (((if isOr then hG d e else hE d e,z)::qk ka (d,x3) (qk kb (e,a1) (s++(i++j).reverse))).map fst)) (hchk:d5 c (eW b c g) h9 forG 0 [] (e4 c (eW b c g)).2.2.2.2=true):h9 (eW b c ((if isOr then hG d e else hE d e,z)::qk ka (d,x3) (qk kb (e,a1) (s++(i++j).reverse))))=true:=by
 have h5':=h5;simp only[jY,kt,nA,nC,nY,nX] at h5';obtain⟨⟨⟨⟨⟨c3,hsub1⟩,a2⟩,b0⟩,_⟩,d1⟩:=h5';have b1:g.length=y+1:=by have x2:=oy t;have hp:=(s3 h4).length_eq;cases ka<;>cases kb<;>simp[qk] at x2 hp<;>omega
 have d2:¬ov f g:=fun hs=>by rw[vt h c3 hs] at a2;cases a2
 have v:=s3 h4;have b3:∀p∈g,qb c (zf c (eW b c g)) (th c (eL b c p.1))=false:=fun p hp' =>
   uu c _ _ d1 (eL b c p.1,p.2) (mM.2 ⟨p,hp',rfl⟩)
 cases ka<;>cases kb
 . simp only[qk,jV,↓reduceIte] at t ⊢;have e0:eW b c g=eW b c i++(eL b c d,ta)::eW b c j++(eL b c e,u)::eW b c s:=by rw[h4];simp[eW,e6,kA]
   have c2:=et c (eW b c g) h9 forG [] (eW b c i) (eW b c j) (eW b c s)
     (eL b c d) ta (eL b c e) u (by rw[<- e0];exact hchk)
   unfold sz at c2;have⟨h2,h3⟩:=o7 c2;have e1:((if isOr then hG d e else hE d e,z)::(s++(i++j).reverse)).length=y:=by have:=congrArg List.length h4;simp at this ⊢;omega
   have x:v4 c (eW b c ((if isOr then hG d e else hE d e,z)::(s++(i++j).reverse)))=c.fL:=by rcases ue h t e1 with x|hs;exact x;exact absurd (i4 v hs) d2
   cases isOr
   . simp only[jV,↓reduceIte] at h6 h7 h0 h1 h8 x ⊢;dsimp only[k8] at h3;simp only[v5,h6,↓reduceIte,hU] at h3;rw[s5,er,<- kd h,<- ag h,show land (eL b c d) (eL b c e)=eL b c (hE d e) from (q9 _ d e).symm,show lor (wU c (eL b c (hE d e))) (v4 c (eW b c (s++(i++j).reverse)))=c.fL from x,f4 h h0 h1 h8,d8,es,<- h7] at h3;simp only[nD,jV,↓reduceIte] at h3;exact h3
   . simp only[↓reduceIte] at h6 h7 h0 h1 h8 x ⊢;dsimp only[k8] at h2;simp only[v5,h6,↓reduceIte,hU] at h2;rw[s5,er,<- iw h,<- bk h,show lor (eL b c d) (eL b c e)=eL b c (hG d e) from (qc _ d e).symm,show lor (wU c (eL b c (hG d e))) (v4 c (eW b c (s++(i++j).reverse)))=c.fL from x,f4 h h0 h1 h8,d8,es,<- h7] at h2;simp only[nD,jV,↓reduceIte] at h2;exact h2
 . simp only[qk,jV,↓reduceIte] at t;exact (uc h (isOr:=isOr) v b0 b1 t (b3 (e,u) (v.symm.subset (by simp)))).elim
 . simp only[qk,jV,↓reduceIte] at t;exact (uc h (isOr:=isOr) v b0 b1 t (b3 (d,ta) (v.symm.subset (by simp)))).elim
 . have x2:=oy t;have hp:=v.length_eq;simp[qk] at x2 hp;omega
lemma g8 {n b:Nat}{f:Z n}{c:Cfg}(i:gX n f b c){s t:Nat}{a1 pre_b suf_b:X n}{a2:J->Q}{b0 isOr:Q}{u ta tb x y:Nat}{d e:Z n}{ka kb b1 b3:Q}{rC rU c2 c3 e0 e1 e2 ha hb hd he hf:Nat}(hlen:t=pre_b.length+suf_b.length+2)(d1:ka=true->b1=true)(d2:kb=true->b3=true) (h3:rC=yx c (eW b c (suf_b++pre_b))) (h5:rU=v4 c (eW b c (suf_b++pre_b))) (h6:c2=zf c (eW b c (suf_b++pre_b))) (h7:c3=va c (eW b c (suf_b++pre_b))) (hg:b0=true->¬ov f ((if isOr then hG d e else hE d e,u)::(suf_b++pre_b))) (h0:(if isOr then hG d e else hE d e)≠fun _=>false) (h1:(if isOr then hG d e else hE d e)≠fun _=>true) (h8:∀p∈a1,p.1≠if isOr then hG d e else hE d e) (g:Run (hC (n:=n)) hE hG f s (((if isOr then hG d e else hE d e,u)::qk ka (d,x) (qk kb (e,y) (suf_b++pre_b))).map fst)) (h4:v7 c s t (eW b c a1) a2 b0 isOr u (k8 c (eL b c d) ta e0 e1 e2 ha) x (k8 c (eL b c e) tb hb hd he hf) y rC rU c2 c3 b1 b3 (eW b c pre_b) (e4 c (eW b c suf_b)).2.2.2.2=true):a2 (eW b c ((if isOr then hG d e else hE d e,u)::qk ka (d,x) (qk kb (e,y) (suf_b++pre_b))))=true:=by
 set z_b:=if isOr then hG d e else hE d e
 have v:(if isOr=true then lor (eL b c d) (eL b c e) else land (eL b c d) (eL b c e))=eL b c z_b:=by cases isOr<;>simp[z_b,eL,qc,q9]
 have hh:xor (if isOr=true then lor (wi c (eL b c d)) (wi c (eL b c e)) else land (wi c (eL b c d)) (wi c (eL b c e)))
     (if isOr=true then lor (tx c (eL b c d)) (tx c (eL b c e)) else land (tx c (eL b c d)) (tx c (eL b c e)))=wC c (eL b c z_b):=by
   cases isOr<;>simp only[↓reduceIte,jV,z_b]
   . rw[show eL b c (hE d e)=land (eL b c d) (eL b c e) from q9 _ d e,kd i]
   . rw[show eL b c (hG d e)=lor (eL b c d) (eL b c e) from qc _ d e,iw i]
 have hj:land (wC c (eL b c z_b))
     (if isOr=true then lor (tx c (eL b c d)) (tx c (eL b c e)) else land (tx c (eL b c d)) (tx c (eL b c e)))=wU c (eL b c z_b):=by
   cases isOr<;>simp only[↓reduceIte,jV,z_b]
   . rw[show eL b c (hE d e)=land (eL b c d) (eL b c e) from q9 _ d e,ag i]
   . rw[show eL b c (hG d e)=lor (eL b c d) (eL b c e) from qc _ d e,bk i]
 have h9:qi c.m0 (if isOr=true then lor (sc c (eL b c d)) (sc c (eL b c e)) else land (sc c (eL b c d)) (sc c (eL b c e)))=th c (eL b c z_b):=by
   cases isOr<;>simp only[↓reduceIte,jV,z_b,th]
   . rw[show eL b c (hE d e)=land (eL b c d) (eL b c e) from q9 _ d e,we]
   . rw[show eL b c (hG d e)=lor (eL b c d) (eL b c e) from qc _ d e,pq]
 have x2:k9 (eW b c pre_b) (e4 c (eW b c suf_b)).2.2.2.2=eW b c (suf_b++pre_b):=by rw[d8,es]
 unfold v7 at h4;dsimp only[k8] at h4;simp only[v5] at h4;rw[hh,hj] at h4;have⟨hk,z⟩:=o7 h4;have x3:(qk ka (d,x) (qk kb (e,y) (suf_b++pre_b))).length+1<=s+1:=by have:=oy g;simpa using this
 cases ka<;>cases kb
 . simp only[qk,jV,↓reduceIte] at g ⊢;have j:=o3 i (rem_b:=suf_b++pre_b) (z_b:=z_b) (z_t:=u)
     (by simp;omega) (by rw[h3];rfl) (by rw[h5];rfl)
     (by rw[h9,h6];rfl) (by rw[v,h7];simp only[eW,e6,eL,kB,w1,dg,v8];omega) hg g hk
   rw[v,x2] at j;simp only[mW] at j;exact o6 i h0 h1 h8 g j
 . have h2:blt (add s 1) t=false:=l4 (by simp[qk] at x3;change t<=s+1;omega);simp only[h2,jV,↓reduceIte] at z;have hm:=(eu _ _ _ _ _ _ z).1 (d2 rfl);simp only[qk,jV,↓reduceIte] at g ⊢;have j:=o3 i (rem_b:=(e,y)::(suf_b++pre_b)) (z_b:=z_b) (z_t:=u)
     (by simp;omega) (by rw[h3];rfl) (by rw[h5];rfl)
     (by rw[h9,h6];simp only[eW,e6,eL,kB,k0,v8];omega)
     (by rw[v,h7];simp only[eW,e6,eL,kB,w1,dg,v8];omega) (fun h=>by cases h) g hm
   rw[v,x2] at j;exact o6 i h0 h1 h8 g j
 . have h2:blt (add s 1) t=false:=l4 (by simp[qk] at x3;change t<=s+1;omega);simp only[h2,jV,↓reduceIte] at z;have hn:=(eu _ _ _ _ _ _ z).2.1 (d1 rfl);simp only[qk,jV,↓reduceIte] at g ⊢;have j:=o3 i (rem_b:=(d,x)::(suf_b++pre_b)) (z_b:=z_b) (z_t:=u)
     (by simp;omega) (by rw[h3];rfl) (by rw[h5];rfl)
     (by rw[h9,h6];simp only[eW,e6,eL,kB,k0,v8];omega)
     (by rw[v,h7];simp only[eW,e6,eL,kB,w1,dg,v8];omega) (fun h=>by cases h) g hn
   rw[v,x2] at j;exact o6 i h0 h1 h8 g j
 . have h2:blt (add s 1) t=false:=l4 (by simp[qk] at x3;change t<=s+1;omega);have hp:ble (add t 1) (add s 1)=true:=(by rw[nA];simp[qk] at x3;change t+1<=s+1;omega);simp only[h2,jV,↓reduceIte] at z;have hq:=(eu _ _ _ _ _ _ z).2.2 (d1 rfl) (d2 rfl) hp;simp only[qk,↓reduceIte] at g ⊢;have j:=o3 i (rem_b:=(d,x)::(e,y)::(suf_b++pre_b)) (z_b:=z_b) (z_t:=u)
     (by simp;omega) (by rw[h3];rfl) (by rw[h5];rfl)
     (by rw[h9,h6];simp only[eW,e6,eL,kB,k0,v8];omega)
     (by rw[v,h7];simp only[eW,e6,eL,kB,w1,dg,v8];omega) (fun h=>by cases h) g hq
   rw[v,x2] at j;exact o6 i h0 h1 h8 g j
lemma n7 (c:Cfg)(i:WF->Nat->Nat->Nat->Nat->J->List WF->Q)(b e d:J)(a ta:Nat) (h:b7 i (yx c b) (v4 c b) (zf c b) (va c b) b (e4 c (e++(a,ta)::d)).2.2.2.2=true):i (k8 c a ta (yx c d) (v4 c d) (zf c d) (va c d)) (yx c (d++e.reverse++b)) (v4 c (d++e.reverse++b)) (zf c (d++e.reverse++b)) (va c (d++e.reverse++b)) (e.reverse++b) (e4 c d).2.2.2.2=true:=by
 induction e generalizing b with
 | nil =>
  simp only[mT,mV,hU,o4] at h ⊢;unfold b7 at h;have j:=(Eq.mp (jY) h).1;dsimp only[k8] at j ⊢;rw[vc,zu,zy,y6,q7 (yx c d),q7 (v4 c d)]
  simp only[v8] at j ⊢;rwa[mF (zf c d),mF (va c d)]
 | cons p rest ih =>
  rcases p with ⟨w,tg⟩;simp only[kZ,o4] at h
  unfold b7 at h;have g:=(Eq.mp (jY) h).2;dsimp only[k8] at g;rw[show lor (yx c b) (wC c w)=yx c ((w,tg)::b) by rw[yp,q7],show lor (v4 c b) (wU c w)=v4 c ((w,tg)::b) by rw[vo,q7],show add (zf c b) (th c w)=zf c ((w,tg)::b) by rw[k0];simp only[v8];omega,show add (va c b) (dg c w)=va c ((w,tg)::b) by rw[w1];simp only[v8];omega] at g;simpa[kF,kA] using ih ((w,tg)::b) g
lemma p7 (c:Cfg)(j:WF->WF->Nat->Nat->Nat->Nat->J->List WF->Q)(s:WF)(d g e:J)(b t:Nat) (h:t9 j s (yx c d) (v4 c d) (zf c d) (va c d) d (e4 c (g++(b,t)::e)).2.2.2.2=true):j s (k8 c b t (yx c e) (v4 c e) (zf c e) (va c e)) (yx c (e++g.reverse++d)) (v4 c (e++g.reverse++d)) (zf c (e++g.reverse++d)) (va c (e++g.reverse++d)) (g.reverse++d) (e4 c e).2.2.2.2=true:=by
 induction g generalizing d with
 | nil =>
  simp only[mT,mV,hU,o4] at h ⊢;unfold t9 at h;have u:=(Eq.mp (jY) h).1;dsimp only[k8] at u ⊢;rw[vc,zu,zy,y6,q7 (yx c e),q7 (v4 c e)]
  simp only[v8] at u ⊢;rwa[mF (zf c e),mF (va c e)]
 | cons p rest ih =>
  rcases p with ⟨w,tg⟩;simp only[kZ,o4] at h
  unfold t9 at h;have i:=(Eq.mp (jY) h).2;dsimp only[k8] at i;rw[show lor (yx c d) (wC c w)=yx c ((w,tg)::d) by rw[yp,q7],show lor (v4 c d) (wU c w)=v4 c ((w,tg)::d) by rw[vo,q7],show add (zf c d) (th c w)=zf c ((w,tg)::d) by rw[k0];simp only[v8];omega,show add (va c d) (dg c w)=va c ((w,tg)::d) by rw[w1];simp only[v8];omega] at i;simpa[kF,kA] using ih ((w,tg)::d) i
lemma d4 (c:Cfg)(s:WF->WF->Nat->Nat->Nat->Nat->J->List WF->Q)(d i g e:J)(a ta b j:Nat) (h:a4 s (yx c d) (v4 c d) (zf c d) (va c d) d (e4 c (i++(a,ta)::g++(b,j)::e)).2.2.2.2=true):s (k8 c a ta (yx c (g++(b,j)::e)) (v4 c (g++(b,j)::e)) (zf c (g++(b,j)::e)) (va c (g++(b,j)::e))) (k8 c b j (yx c e) (v4 c e) (zf c e) (va c e)) (yx c (e++g.reverse++i.reverse++d)) (v4 c (e++g.reverse++i.reverse++d)) (zf c (e++g.reverse++i.reverse++d)) (va c (e++g.reverse++i.reverse++d)) (g.reverse++i.reverse++d) (e4 c e).2.2.2.2=true:=by
 induction i generalizing d with
 | nil=>simp only[mT,mV,hU,kZ,o4] at h ⊢;unfold a4 at h;exact p7 c s _ d g e b j (Eq.mp (jY) h).1
 | cons p rest ih =>
  rcases p with ⟨w,tg⟩;simp only[kZ,o4] at h
  unfold a4 at h;have t:=(Eq.mp (jY) h).2;dsimp only[k8] at t;rw[show lor (yx c d) (wC c w)=yx c ((w,tg)::d) by rw[yp,q7],show lor (v4 c d) (wU c w)=v4 c ((w,tg)::d) by rw[vo,q7],show add (zf c d) (th c w)=zf c ((w,tg)::d) by rw[k0];simp only[v8];omega,show add (va c d) (dg c w)=va c ((w,tg)::d) by rw[w1];simp only[v8];omega] at t;simpa[kF,kA] using ih ((w,tg)::d) t
lemma ua {n d:Nat}{f:Z n}{c:Cfg}(t:gX n f d c){z:Nat}{b0:J->Q}{g:X n} (h4:uq c b0 z (eW d c g)=true) (hf:TR f (z+1) g):∃nxt_b,TR f z nxt_b/\b0 (eW d c nxt_b)=true:=by
 have hd:=n9 c (eW d c g);have hz:(eW d c g).length=g.length:=kY _;unfold uq at h4;rw[show e4 c (eW d c g)=(yx c (eW d c g),v4 c (eW d c g),zf c (eW d c g),va c (eW d c g),(e4 c (eW d c g)).2.2.2.2) from Prod.ext hd.1 (Prod.ext hd.2.1 (Prod.ext hd.2.2.1 (Prod.ext hd.2.2.2 rfl)))] at h4;dsimp only at h4;rw[hz,p3 t hf.toRun] at h4;simp only[jV,↓reduceIte,v5] at h4;set b1:=ble g.length 11&&beq (sub (add z 2) g.length) 1&&!(z3 c (va c (eW d c g)));have hg:b1=true->¬ov f g:=fun h6 hs=>by
   simp only[b1,jY,kt,nA] at h6;rw[vt t h6.1.1 hs] at h6;cases h6.2
 set he:=b1&&ble g.length 10&&!(beq z 0) &&
   !(b9 c (zf c (eW d c g)) (e4 c (eW d c g)).2.2.2.2)
 rcases hf.inv_succ with
   ⟨a,ta,r,d1,hp,b3,c2,xi,h0,v',d2,e0,s⟩ |
   ⟨a,ta,b,tb,r,ka,kb,hp,c2,e1,h9,x2,h0,v',d2,hh,e0,s⟩ |
   ⟨a,ta,b,tb,r,ka,kb,hp,b3,e2,h9,x2,h0,v',d2,hh,e0,s⟩
 . have hq:b1=false:=by
     rw[jU];intro h6;have xs:g.length=z+1:=by have hle:=hf.len_le;simp only[b1,jY,nC,nY,nX] at h6;omega
     cases d1
     . simp only[qk,jV,↓reduceIte] at s;exact hg h6 (y4 hp xs s.toRun)
     . have f2:=s.len_le;have g0:=hp.length_eq;simp[qk] at f2 g0;omega
   have g1:he=false:=(by simp only[he,hq,jT]);simp only[g1,jV,↓reduceIte,jY] at h4;have hr:=h4.1;obtain⟨i,j,y,x3⟩:=pc hp;have s' : TR f z ((hC a,if ta=3 then 2 else 0)::qk d1 (a,0) (j++i.reverse)):=gV.perm (mR _ (by cases d1<;>simp[qk,x3.trans (o2 i j)])) s;have ht:=s'.len_le;have hu:g.length=i.length+j.length+1:=(by have:=congrArg List.length y;simp at this;omega);have g2:ble 1 (sub (add z 2) g.length)=true:=(by rw[nA];change 1<=z+2 - g.length;cases d1<;>simp[qk] at ht<;>omega);simp only[g2,hq,jZ,jW,↓reduceIte] at hr;have ha:eW d c g=eW d c i++(eL d c a,ta)::eW d c j:=(by rw[y];simp[eW,e6]);have h7:=n7 c (b8 c z g.length (sub (add z 2) g.length) (eW d c g) b0 false)
     [] (eW d c i) (eW d c j) (eL d c a) ta (by rw[<- ha];exact hr)
   unfold b8 at h7;dsimp only[k8] at h7;have h5:∀p∈g,p.1≠hC a:=fun p hb=>by
     rcases kC.1 (hp.subset hb) with rfl|g3;exact d2.symm;exact e0 p g3
   simp only[jV,q2 b3,q2 c2,jZ,jW,↓reduceIte,v5,hU] at h7;have⟨g4,hv⟩:=o7 h7;have a1:eW d c j++(eW d c i).reverse=eW d c (j++i.reverse):=by rw[y0,es]
   have hw:k9 (eW d c i).reverse (e4 c (eW d c j)).2.2.2.2=eW d c (j++i.reverse):=(by rw[d8,a1]);cases d1
   . simp only[qk,jV,↓reduceIte] at s';have h8:=o3 t (rem_b:=j++i.reverse) (z_b:=hC a) (z_t:=if ta=3 then 2 else 0)
       (by rw[hu];simp;omega)
       (by rw[a1,t4,yp,qv t,cm t]) (by rw[a1,t4,vo,qv t,cq t])
       (by rw[a1,t4,k0,th,qv t,cp t])
       (by rw[a1,t4,w1,qv t,ck t];simp only[v8];omega) (fun h=>by cases h) s'.toRun g4
     rw[<- qv t,hw] at h8;simp only[mW] at h8;by_cases h3:ta=3
     . subst h3;simp only[nD,↓reduceIte] at h8 s';exact⟨_,s',o6 t h0 v' h5 s'.toRun h8⟩
     . simp only[q2 h3,jV,h3,↓reduceIte] at h8 s';exact⟨_,s',o6 t h0 v' h5 s'.toRun h8⟩
   . have hj:ta≠3:=fun e=>by have:=xi e;cases this
     have j0:ble 2 (sub (add z 2) g.length)=true:=(by rw[nA];change 2<=z+2 - g.length;simp[qk] at ht;omega);simp only[q2 hj,jZ,j0,jW,↓reduceIte] at hv;simp only[qk,hj,↓reduceIte] at s';have h8:=o3 t (rem_b:=(a,0)::(j++i.reverse)) (z_b:=hC a) (z_t:=0)
       (by rw[hu];simp;omega)
       (by rw[a1,t4,t4,yp,yp,qv t,cm t]) (by rw[a1,t4,t4,vo,vo,qv t,cq t])
       (by rw[a1];simp only[t4,k0,th,qv t,cp t,v8];omega)
       (by rw[a1];simp only[t4,w1,qv t,ck t,v8];omega) (fun h=>by cases h) s'.toRun hv
     rw[<- qv t,hw] at h8;simp only[q2 hj,jV,↓reduceIte] at h8;exact⟨_,s',o6 t h0 v' h5 s'.toRun h8⟩
 . have hx:∀(a' : Z n) (ta' : Nat) (b' : Z n) (tb' : Nat) (ka' kb' : Q) (i u j:X n),
       g=i++(a',ta')::u++(b',tb')::j->ta'≠2->tb'≠2->(ta'=1->ka'=false)->(tb'=1->kb'=false) ->
       hG a' b'≠(fun _=>false)->hG a' b'≠(fun _=>true)->(∀p∈g,p.1≠hG a' b') ->
       TR f z ((hG a' b',0)::qk ka' (a',if ta'=3 then 1 else 0) (qk kb' (b',if tb'=3 then 1 else 0) (j++(i++u).reverse))) ->
       ∃nxt_b,TR f z nxt_b/\b0 (eW d c nxt_b)=true:=by
     intro a' ta' b' tb' ka' kb' i u j y c2' e1' h9' x2' h0' v'' h5 s';cases c3:he
     . simp only[c3,jV,↓reduceIte,jY] at h4;have ha:eW d c g=eW d c i++(eL d c a',ta')::eW d c u++(eL d c b',tb')::eW d c j:=by rw[y];simp[eW,e6,kA]
       have h7:=d4 c (k2 c z g.length (eW d c g) b0 b1)
        [] (eW d c i) (eW d c u) (eW d c j) (eL d c a') ta' (eL d c b') tb' (by rw[<- ha];exact h4.2)
       unfold k2 at h7;have hk:=(o7 h7).1;simp only[dd,q2 c2',q2 e1',jZ,jW,↓reduceIte,hU,mq] at hk;rw[er] at hk;refine⟨_,s',g8 t (isOr:=true) (pre_b:=(i++u).reverse) (suf_b:=j) (by rw[y];simp;omega) (fun h=>by rw[q2 (fun e=>by have:=h9' e;rw[h] at this;cases this)];rfl) (fun h=>by rw[q2 (fun e=>by have:=x2' e;rw[h] at this;cases this)];rfl) (by rw[s5]) (by rw[s5]) (by rw[s5]) (by rw[s5]) (fun h6 hs=>hg h6 (i4 (s3 y) hs)) h0' v'' h5 s'.toRun hk⟩
     . simp only[c3,↓reduceIte] at h4;exact⟨_,s',c9 t (isOr:=true) (forG:=false) y c3 (by simp[x8,q2 c2',q2 e1']) rfl h0' v'' h5 s'.toRun h4⟩
   have h5:∀p∈g,p.1≠hG a b:=fun p hb=>by
     rcases kC.1 (hp.subset hb) with rfl|v'';exact d2.symm
     rcases kC.1 v'' with rfl|h2';exact hh.symm;exact e0 p h2'
   rcases lx hp with ⟨i,u,j,y,x3⟩|⟨i,u,j,y,x3⟩
   . exact hx a ta b tb ka kb i u j y c2 e1 h9 x2 h0 v' h5
       (gV.perm (ey (x3.trans (o2 (i++u) j))) s)
   . have a2:hG b a=hG a b:=(by funext x;exact Bool.or_comm _ _);exact hx b tb a ta kb ka i u j y e1 c2 x2 h9 (a2 ▸ h0) (a2 ▸ v')
       (fun p hp' => a2 ▸ h5 p hp')
       (a2 ▸ gV.perm (i0 (x3.trans (o2 (i++u) j))) s)
 . have hy:∀(a' : Z n) (ta' : Nat) (b' : Z n) (tb' : Nat) (ka' kb' : Q) (i u j:X n),
       g=i++(a',ta')::u++(b',tb')::j->ta'≠1->tb'≠1->(ta'≠0->ka'=false)->(tb'≠0->kb'=false) ->
       hE a' b'≠(fun _=>false)->hE a' b'≠(fun _=>true)->(∀p∈g,p.1≠hE a' b') ->
       TR f z ((hE a' b',if ta'=3\/tb'=3 then 1 else 0)::qk ka' (a',0) (qk kb' (b',0) (j++(i++u).reverse))) ->
       ∃nxt_b,TR f z nxt_b/\b0 (eW d c nxt_b)=true:=by
     intro a' ta' b' tb' ka' kb' i u j y b3' e2' h9' x2' h0' v'' h5 s';cases c3:he
     . simp only[c3,jV,↓reduceIte,jY] at h4;have ha:eW d c g=eW d c i++(eL d c a',ta')::eW d c u++(eL d c b',tb')::eW d c j:=by rw[y];simp[eW,e6,kA]
       have h7:=d4 c (k2 c z g.length (eW d c g) b0 b1)
        [] (eW d c i) (eW d c u) (eW d c j) (eL d c a') ta' (eL d c b') tb' (by rw[<- ha];exact h4.2)
       unfold k2 at h7;have hm:=(o7 h7).2;simp only[dd,q2 b3',q2 e2',jZ,jW,↓reduceIte,hU,b6] at hm;rw[er] at hm;refine⟨_,s',g8 t (isOr:=false) (pre_b:=(i++u).reverse) (suf_b:=j) (by rw[y];simp;omega) (fun h=>qz (nS fun hn=>by have:=h9' hn;rw[h] at this;cases this)) (fun h=>qz (nS fun hn=>by have:=x2' hn;rw[h] at this;cases this)) (by rw[s5]) (by rw[s5]) (by rw[s5]) (by rw[s5]) (fun h6 hs=>hg h6 (i4 (s3 y) hs)) h0' v'' h5 s'.toRun hm⟩
     . simp only[c3,↓reduceIte] at h4;exact⟨_,s',c9 t (isOr:=false) (forG:=false) y c3 (by simp[x8,q2 b3',q2 e2']) (by simp[sq,b6]) h0' v'' h5 s'.toRun h4⟩
   have h5:∀p∈g,p.1≠hE a b:=fun p hb=>by
     rcases kC.1 (hp.subset hb) with rfl|v'';exact d2.symm
     rcases kC.1 v'' with rfl|h2';exact hh.symm;exact e0 p h2'
   rcases lx hp with ⟨i,u,j,y,x3⟩|⟨i,u,j,y,x3⟩
   . exact hy a ta b tb ka kb i u j y b3 e2 h9 x2 h0 v' h5
       (gV.perm (ey (x3.trans (o2 (i++u) j))) s)
   . have a2:hE b a=hE a b:=(by funext x;exact Bool.and_comm _ _);have j1:(if tb=3\/ta=3 then 1 else 0)=(if ta=3\/tb=3 then 1 else 0):=(by by_cases v'' : ta=3<;>by_cases h2'' : tb=3<;>simp[v'',h2'']);exact hy b tb a ta kb ka i u j y e2 b3 x2 h9 (a2 ▸ h0) (a2 ▸ v')
       (fun p hp' => a2 ▸ h5 p hp')
       (a2 ▸ j1 ▸ gV.perm (i0 (x3.trans (o2 (i++u) j))) s)
lemma f9 {n d:Nat}{f:Z n}{c:Cfg}(e:gX n f d c){s:Nat}{g:X n} (b:m7 c s (eW d c g)=true) (h:TR f s g):False:=by
 cases s with
 | zero=>obtain⟨tg,rfl⟩:=h.inv_zero;simp only[m7,eW,e6,kB,mS,e.fZ,nD] at b;cases b
 | succ ns=>obtain⟨_,_,i⟩:=ua e b h;cases i
lemma iu {n:Nat}{f:Z n}{d:Nat}{c:Cfg}(h:gX n f d c)(e:Nat)(_hcap:e<=11)(NN:Nat->Nat)(R_bfn:Nat->Nat->X n)(R:Nat->Nat->J) (v:∀s j,R s j=eW d c (R_bfn s j)) (_hTags:∀s j,gW (R_bfn s j)) (t:Nat->J->Q) (h0:w2 f (aR n d c) NN R_bfn t) (x:∀s≤ e,∀i < NN s,bar c t R s i=true):∀s≤ e,∀i < NN s,¬TR f s (R_bfn s i):=by
 intro s;induction s with
 | zero=>intro _ i hi u;have b:=x 0 (mJ e) i hi;obtain⟨tg,h1⟩:=u.inv_zero;simp only[bar,v,h1,eW,e6,kB,mS,h.fZ,nD] at b;cases b
 | succ ns ih =>
  intro hs i hi u;have h2:=ih (by omega);have b:=x (ns+1) hs i hi;simp only[bar,v8,v] at b;obtain⟨y,z,g⟩:=ua h b u;cases hf:t ns (eW d c y)
  . simp only[hf,jV,↓reduceIte] at g;cases ns with
    | zero=>simp at g
    | succ s' => simp only[q2 (nP s'),jV,↓reduceIte] at g;exact f9 h g z
  . obtain⟨j,hj,π,h3,h4,h5⟩:=h0 ns y hf;exact h2 j hj (gV.perm h5 (wp π h3 h4 z))
def d6 (n:Nat) (f:Z n):List (V)->List (J)->Q
 | [],[]=>true
 | sw::sws,ps::pss =>
  kq n ps&&(mw n ps==sw)&&(ym sw (u9 n f)==u9 n f)&&d6 n f sws pss
 | _,_=>false
lemma ye (n:Nat)(f:Z n) (b:List (V)) (c:List (J)) (h:d6 n f b c=true):∀sw∈b,vh f sw:=by
 induction b generalizing c with
 | nil=>intro _ e;cases e
 | cons sw sws ih =>
  cases c with
  | nil=>simp[d6] at h
  | cons ps i =>
   simp only[d6,jY,beq_iff_eq] at h;obtain⟨⟨⟨j,s⟩,d⟩,t⟩:=h;intro g u;rcases kC.1 u with rfl|v
   . rw[<- s] at d ⊢;exact kw f ps j d
   . exact ih i t g v
def dw (n:Nat)(f:Z n)(b:Nat->V) (c:List (J)):Q:=
 (range c.length).all fun i =>
  let d:=c.getD i []
  kq n d&&(mw n d==b i)&&(ym (b i) (u9 n f)==u9 n f)
lemma q58 (n:Nat)(f:Z n)(c:Nat->V) (b:List (J)) (h:dw n f c b=true)(g:∀i≥ b.length,c i=[]):∀i,vh f (c i):=by
 intro i;by_cases hi:i < b.length
 . have d:=kH.1 h i (jF.2 hi);simp only[jY,beq_iff_eq] at d;obtain⟨⟨j,s⟩,e⟩:=d;rw[<- s] at e ⊢;exact kw f (b.getD i []) j e
 . rw[g i (by omega)];exact xm f
def w8 (n:Nat)(f:Z n):Q:=
 let t:=u9 n f;!(beq t 0)&&!(beq t (2 ^ (2 ^ n) - 1))
lemma ju (n:Nat)(f:Z n)(h:w8 n f=true):∃y y':F n,f y≠f y':=by
 unfold w8 at h;simp only[jY,kt,zh] at h;obtain⟨d,e⟩:=h;have g:∃r < 2 ^ n,f (q1 n r)=true:=by by_contra b;push Not at b;apply d;apply kL;intro r;rw[vr,kU];split;exact jU.2 (b r ‹_›);rfl
 have i:∃r < 2 ^ n,f (q1 n r)=false:=by
  by_contra b;push Not at b;apply e;apply kL;intro r;rw[vr,kK];split
  . rename_i c;have:f (q1 n r)=true:=by cases j:f (q1 n r);exact absurd j (b r c);rfl
    simp[c,this]
  . rename_i c;simp[c]
 obtain⟨r1,_,s⟩:=g;obtain⟨r0,_,t⟩:=i;exact⟨q1 n r1,q1 n r0,by rw[s,t];decide⟩
def q77 (n:Nat)(f:Z n):Q:=
 (finRange n).all fun v =>
  (range (2 ^ n)).any fun r=>let x:=q1 n r;f (update x v (!x v))!=f x
lemma q44 (n:Nat)(f:Z n)(h:q77 n f=true):∀v:Fin n,∃x:F n,f (update x v (!x v))≠f x:=by intro v;have b:=kH.1 h v (jG v);obtain⟨r,_,c⟩:=kJ.1 b;exact⟨q1 n r,bne_iff_ne.1 c⟩
def jc (c:Cfg)(d:Nat->J->Q)(b:J)(s0:Nat):Q:=
 d s0 b||(!(beq s0 0)&&m7 c s0 b)
def r9 (n b:Nat)(f:Z n)(d:Nat)(c:Cfg)(e:Fin n->Nat)(g j:J)(s:Nat->J->Q):Q:=
 let t:=aR n d c
 let h:=ofFn fun i:Fin n=>((fun x:F n=>x i),e i)
 ble b 11&&w3 n f d c&&w8 n f&&q77 n f &&
 ((finRange n).all fun i=>ble (e i) 3) &&
 (g==e6 t h)&&(j==u2 n h) &&
 ((range (b+1)).all fun s0=>blt (add s0 1) n||jc c s g s0)
lemma x4 {n b:Nat}(f:Z n)(e:Nat)(c:Cfg)(d:Fin n->Nat)(g h8:J)(NN PT:Nat->Nat)(h:Nat->J->Q)(z:r9 n b f e c d g h8 h=true) (h3:w2 f (aR n e c) NN (ts b (ofFn fun i:Fin n=>((fun x:F n=>x i),d i)) PT) h) (h9:∀s≤ b,∀i < NN s,bar c h (c8 c.fJ b g PT) s i=true) (x2:∀v:Fin n,d v=0\/(d v=1/\(∃x y,f (update x v false)≠f (update y v false))/\∀s',nV n (fun x=>f (update x v false)) s'->b - 1<=s')\/(d v=3/\(∃x y,f (update x v false)≠f (update y v false))/\∀s',nV n (fun x=>f (update x v false)) s'->b - 2<=s')):∀t:Nat,nV n f t->b+1<=t:=by
 unfold r9 at z;simp only[jY,nA,beq_iff_eq] at z;rcases z with ⟨⟨⟨⟨⟨⟨⟨x3,a1⟩,a2⟩,b0⟩,b1⟩,h0⟩,hxstt⟩,b3⟩
 have hc:=jn n f e c a1;have c2:=ju n f a2;have c3:=q44 n f b0;set u:X n:=ofFn fun i:Fin n=>((fun x:F n=>x i),d i)
 have d1:gW u:=fun p hp=>by
   rw[jE] at hp;obtain⟨i,rfl⟩:=hp;exact Eq.mp nA (kH.1 b1 i (jG i))
 have d2:=zl n e c.fH;have hR:∀s j,c8 c.fJ b g PT s j=eW e c (ts b u PT s j):=fun s j=>by
   rw[h0,hc.fY,<- d2,ke]
 have e0:=iu hc b x3 NN (ts b u PT) (c8 c.fJ b g PT) hR
   (fun s j=>q59 b d1 PT s j) h h3 h9
 intro t e1;by_contra hlt;have e2:t<=b:=by omega
 obtain⟨s0,ha,h1⟩:=q88 f b d c2 c3 x2 t e2 e1;have h4:=kH.1 b3 s0 (jF.2 (by omega));simp only[jX] at h4;rcases h4 with hb|h2
 . have hlt_n:s0+1 < n:=(by simpa[nB,v8] using hb);have htr_len:n<=s0+1:=(by simpa using h1.len_le);omega
 . unfold jc at h2;simp only[jX] at h2;rcases h2 with h5|h6
   . rw[h0] at h5;obtain⟨j,hj,π,hd,he,hf⟩:=h3 s0 u h5;exact e0 s0 ha j hj (gV.perm hf (wp π hd he h1))
   . simp only[jY,kt,zh] at h6;obtain⟨_,h7⟩:=h6;rw[h0] at h7;exact f9 hc h7 h1
lemma b5 {n d b:Nat}(g:d=2 ^ 2 ^ n - 1)(c:X n)(e:J)(h:e=u2 n c)(PT:Nat->Nat)(s j:Nat):c8 d b e PT s j=u2 n (ts b c PT s j):=by rw[g,h];exact xd b c PT s j
lemma s9 {P:Nat->Nat->Q}{b:Nat}{NN:Nat->Nat} (h:(range (b+1)).all (fun s=>jM (P s) (NN s) 0)=true):∀s≤ b,∀i < NN s,P s i=true:=fun s hs i hi =>
 hH (P s) (NN s) 0 (kH.1 h s (jF.2 (by omega))) i (mJ _) (by omega)
lemma y8 {n:Nat}(f g:Z n) (h:beq (u9 n f) (u9 n g)=true):f=g:=
 yc (Eq.mp nC h)
lemma mf {n b g:Nat}(f:Z n)(h j:Nat)(c:Cfg)(d:Fin n->Nat)(u e:J)(NN FL HT PT:Nat->Nat)(z:g=2 ^ 2 ^ n - 1) (h0:e=u2 n (ofFn fun i:Fin n=>((fun x:F n=>x i),d i))) (h1:r9 n b f h c d u e (uh c.fH j (c8 g b e PT) NN FL HT)=true) (h2:∀s≤ b,∀i < NN s,bar c (uh c.fH j (c8 g b e PT) NN FL HT) (c8 c.fJ b u PT) s i=true) (h3:∀v:Fin n,d v=0\/(d v=1/\(∃x y,f (update x v false)≠f (update y v false))/\∀s',nV n (fun x=>f (update x v false)) s'->b - 1<=s')\/(d v=3/\(∃x y,f (update x v false)≠f (update y v false))/\∀s',nV n (fun x=>f (update x v false)) s'->b - 2<=s')):∀t:Nat,nV n f t->b+1<=t:=
 x4 f h c d u e NN PT _ h1
  (q87 f h c.fH j NN FL HT _ _ (b5 z _ e h0 PT)) h2 h3
lemma tk {n b h:Nat}(f:Z n)(j u:Nat)(c:Cfg)(d:Fin n->Nat)(z e:J)(g:V)(h0:J)(NN FL HT PT:Nat->Nat)(h1:h=2 ^ 2 ^ n - 1) (h2:e=u2 n (ofFn fun i:Fin n=>((fun x:F n=>x i),d i))) (h3:d6 n f [g] [h0]=true) (h4:r9 n b f j c d z e (p5 c.fH u g (c8 h b e PT) NN FL HT)=true) (h5:∀s≤ b,∀i < NN s,bar c (p5 c.fH u g (c8 h b e PT) NN FL HT) (c8 c.fJ b z PT) s i=true) (h6:∀v:Fin n,d v=0\/(d v=1/\(∃x y,f (update x v false)≠f (update y v false))/\∀s',nV n (fun x=>f (update x v false)) s'->b - 1<=s')\/(d v=3/\(∃x y,f (update x v false)≠f (update y v false))/\∀s',nV n (fun x=>f (update x v false)) s'->b - 2<=s')):∀t:Nat,nV n f t->b+1<=t:=
 x4 f j c d z e NN PT _ h4
  (q86 f j c.fH u g (ye n f [g] [h0] h3 g (by simp))
   NN FL HT _ _ (b5 h1 _ e h2 PT)) h5 h6
lemma dp {n b j:Nat}(f:Z n)(u z:Nat)(c:Cfg)(d:Fin n->Nat)(xs e:J) (h0 h:List (V)) (h1:List (J)) (NN FL HT PT:Nat->Nat)(h2:j=2 ^ 2 ^ n - 1) (h3:e=u2 n (ofFn fun i:Fin n=>((fun x:F n=>x i),d i))) (h4:d6 n f h0 h1=true) (h5:h.all (fun g=>h0.contains g)=true) (h6:r9 n b f u c d xs e (i9 c.fH z h (c8 j b e PT) NN FL HT)=true) (h7:∀s≤ b,∀i < NN s,bar c (i9 c.fH z h (c8 j b e PT) NN FL HT) (c8 c.fJ b xs PT) s i=true) (h8:∀v:Fin n,d v=0\/(d v=1/\(∃x y,f (update x v false)≠f (update y v false))/\∀s',nV n (fun x=>f (update x v false)) s'->b - 1<=s')\/(d v=3/\(∃x y,f (update x v false)≠f (update y v false))/\∀s',nV n (fun x=>f (update x v false)) s'->b - 2<=s')):∀t:Nat,nV n f t->b+1<=t:=by
 have hg:=ye n f h0 h1 h4;have hp:∀g∈h,vh f g:=fun g h9 =>
  hg g (List.contains_iff_mem.1 (kH.1 h5 g h9))
 exact x4 f u c d xs e NN PT _ h6
  (q37 f u c.fH z h hp NN FL HT _ _ (b5 h2 _ e h3 PT)) h7 h8
lemma uy {n b j:Nat}(f:Z n)(u z:Nat)(c:Cfg)(d:Fin n->Nat)(xs e:J) (h:List (V)) (h1:List (J)) (g:Nat->V) (h0:List (J)) (NN FL HT PT:Nat->Nat)(h2:j=2 ^ 2 ^ n - 1) (h3:e=u2 n (ofFn fun i:Fin n=>((fun x:F n=>x i),d i))) (h4:d6 n f h h1=true)(h5:dw n f g h0=true)(h6:∀i≥ h0.length,g i=[]) (h7:r9 n b f u c d xs e (f8 c.fH z h g (c8 j b e PT) NN FL HT PT)=true) (h8:∀s≤ b,∀i < NN s,bar c (f8 c.fH z h g (c8 j b e PT) NN FL HT PT) (c8 c.fJ b xs PT) s i=true) (h9:∀v:Fin n,d v=0\/(d v=1/\(∃x y,f (update x v false)≠f (update y v false))/\∀s',nV n (fun x=>f (update x v false)) s'->b - 1<=s')\/(d v=3/\(∃x y,f (update x v false)≠f (update y v false))/\∀s',nV n (fun x=>f (update x v false)) s'->b - 2<=s')):∀t:Nat,nV n f t->b+1<=t:=
 x4 f u c d xs e NN PT _ h7
  (q55 f u c.fH z h (ye n f h h1 h4)
   g (q58 n f g h0 h5 h6) NN FL HT PT _ _ (b5 h2 _ e h3 PT)) h8 h9
structure hA where
 k:Nat
 E:List (Fin k×Fin k)
 lb:Nat
def c4 (c:List hA):Prop:=
 ∀b∈c,∀s:Nat,nV b.k (d9 [] b.E) s->b.lb<=s
def lz {n:Nat}:List (Fin n)->Q
 | []=>true
 | a::t=>!t.contains a&&lz t
lemma q83 {n:Nat} (l:List (Fin n)) (h:lz l=true):l.Nodup:=by
 induction l with
 | nil=>exact List.nodup_nil
 | cons a t ih=>simp only[lz,jY,kt] at h;exact List.nodup_cons.2 ⟨by simpa[List.contains_eq_mem] using h.1,ih h.2⟩
inductive hB (n:Nat) where
 | emp
 | base (idx:Nat) (π:M)
 | f0 (p:Fin n) (t:hB n)
 | f1 (p:Fin n) (t:hB n)
 | b2 (p:Fin n) (t0 t1:hB n)
def t6 (d:List hA) (n:Nat)
  (A:List (Fin (n+1))) (E:List (Fin (n+1)×Fin (n+1))) (c:Nat):hB (n+1)->Q
 | hB.emp=>E.isEmpty&&lz A&&ble c (A.length - 1)
 | hB.base idx π =>
  match d[idx]? with
  | none=>false
  | some b =>
   if h:0 < b.k then
    A.isEmpty&&ble c b.lb &&
    og E b.E (fun i=>⟨π.getD i.1 0 % b.k,Nat.mod_lt _ h⟩)
   else false
 | hB.f0 p t =>
  let A':=tq A p;let E':=i7 E p
  k1 A E p&&(!A'.isEmpty||!E'.isEmpty)&&t6 d n A' E' (c - 1) t
 | hB.f1 p t =>
  let A':=n6 A E p;let E':=tp A E p
  k1 A E p&&!A.contains p&&E.all (fun e=>e.1!=e.2) &&
   (!A'.isEmpty||!E'.isEmpty)&&t6 d n A' E' (c - 1) t
 | hB.b2 p t0 t1 =>
  let A0:=tq A p;let E0:=i7 E p
  let A1:=n6 A E p;let E1:=tp A E p
  k1 A E p&&!A.contains p&&E.all (fun e=>e.1!=e.2) &&
   (!A0.isEmpty||!E0.isEmpty)&&(!A1.isEmpty||!E1.isEmpty) &&
   t6 d n A0 E0 (c - 2) t0&&t6 d n A1 E1 (c - 2) t1
lemma p9 (g:List hA)(h3:c4 g){n:Nat} (t:hB (n+1)) (A:List (Fin (n+1))) (E:List (Fin (n+1)×Fin (n+1))) (d:Nat)(h:t6 g n A E d t=true):∀s:Nat,nV (n+1) (d9 A E) s->d<=s:=by
 induction t generalizing A E d with
 | emp =>
  simp only[t6,jY,List.isEmpty_iff] at h;rcases h with ⟨⟨rfl,h4⟩,u⟩
  intro s c;have j:=vq A (q83 A h4) s c;have h2:d<=A.length - 1:=Eq.mp nA u;omega
 | base idx π =>
  unfold t6 at h;cases v:g[idx]? with
  | none=>rw[v] at h;cases h
  | some b =>
   rw[v] at h;dsimp only at h
   split at h
   . rename_i hk
     simp only[jY,List.isEmpty_iff] at h;rcases h with ⟨⟨rfl,u⟩,h5⟩
     have h6:b∈g:=List.mem_of_getElem? v;intro s c;have j:=pv E b.E (fun i=>⟨π.getD i.1 0 % b.k,Nat.mod_lt _ hk⟩) h5 (h3 b h6) s c;have h2:d<=b.lb:=Eq.mp nA u;omega
   . cases h
 | f0 p t ih =>
  simp only[t6,jY] at h;rcases h with ⟨⟨e,x⟩,y⟩
  intro s c;have j:=px A E p (tq A p) (i7 E p) (d - 1) e rfl rfl x (ih _ _ _ y) s c;omega
 | f1 p t ih =>
  simp only[t6,jY] at h;rcases h with ⟨⟨⟨⟨e,z⟩,h0⟩,x⟩,y⟩
  intro s c;have j:=py A E p (n6 A E p) (tp A E p) (d - 1) e z h0 rfl rfl x (ih _ _ _ y) s c;omega
 | b2 p t0 t1 ih0 ih1 =>
  simp only[t6,jY] at h;rcases h with ⟨⟨⟨⟨⟨⟨e,z⟩,h0⟩,h7⟩,h8⟩,h9⟩,x2⟩
  intro s c;have j:=wu A E p (tq A p) (i7 E p) (n6 A E p) (tp A E p) (d - 2)
   e z h0 rfl rfl rfl rfl h7 h8 (ih0 _ _ _ h9) (ih1 _ _ _ x2) s c;omega
def bc (b:List hA)(n c:Nat) (E:List (Fin (n+1)×Fin (n+1))) (e:Fin (n+1)->Nat) (g:List (hB (n+1))):Q:=
 (finRange (n+1)).all fun v =>
  let tg:=e v
  let E0:=i7 E v
  let d:=g.getD v.1 hB.emp
  beq tg 0 ||
  (beq tg 1&&!E0.isEmpty&&t6 b n [] E0 (c - 1) d) ||
  (beq tg 3&&!E0.isEmpty&&t6 b n [] E0 (c - 2) d)
lemma l0 (e:List hA)(z:c4 e){n c:Nat} (f:u6 (n+1)) (E:List (Fin (n+1)×Fin (n+1))) (g:Fin (n+1)->Nat) (h2:List (hB (n+1))) (hf:beq (u9 (n+1) f) (u9 (n+1) (d9 [] E))=true) (h:bc e n c E g h2=true):∀v:Fin (n+1),g v=0\/(g v=1/\(∃x y,f (update x v false)≠f (update y v false))/\∀s',nV (n+1) (fun x=>f (update x v false)) s'->c - 1<=s')\/(g v=3/\(∃x y,f (update x v false)≠f (update y v false))/\∀s',nV (n+1) (fun x=>f (update x v false)) s'->c - 2<=s'):=by
 have i:f=d9 [] E:=y8 _ _ hf;intro v;have hv:=kH.1 h v (jG v);simp only[jX,jY] at hv;rcases hv with (h0|⟨⟨h1,j⟩,t⟩)|⟨⟨h3,j⟩,t⟩
 . exact Or.inl (Eq.mp nC h0)
 . refine Or.inr (Or.inl ⟨Eq.mp nC h1,?_,?_⟩)
   . have b:(fun x=>f (update x v false))=d9 [] (i7 E v):=(by rw[i];exact zo [] E v);obtain⟨x,y,u⟩:=fp [] (i7 E v) (by simp[j]);exact⟨x,y,by simpa[congrFun b] using u⟩
   . intro s' d';have b:(fun x=>f (update x v false))=d9 [] (i7 E v):=by rw[i];exact zo [] E v
     rw[b] at d';exact p9 e z _ [] (i7 E v) (c - 1) t s' d'
 . refine Or.inr (Or.inr ⟨Eq.mp nC h3,?_,?_⟩)
   . have b:(fun x=>f (update x v false))=d9 [] (i7 E v):=(by rw[i];exact zo [] E v);obtain⟨x,y,u⟩:=fp [] (i7 E v) (by simp[j]);exact⟨x,y,by simpa[congrFun b] using u⟩
   . intro s' d';have b:(fun x=>f (update x v false))=d9 [] (i7 E v):=by rw[i];exact zo [] E v
     rw[b] at d';exact p9 e z _ [] (i7 E v) (c - 2) t s' d'
lemma g9 (b:hA)(c:List hA) (d:∀s:Nat,nV b.k (d9 [] b.E) s->b.lb<=s) (e:c4 c):c4 (b::c):=fun x hx=>by
 rcases kC.1 hx with rfl|g;exact d;exact e x g
lemma dz {k lb:Nat}(f:Z k) (E:List (Fin k×Fin k)) (b:beq (u9 k f) (u9 k (d9 [] E))=true) (h:∀s:Nat,nV k f s->lb<=s):∀s:Nat,nV k (d9 [] E) s->lb<=s:=by rw[<- y8 _ _ b];exact h
def a1t3:=0xff
def a1t5:=0xffffffff
def l5:=0xffffffffffffffff
def lr:=0xffffffffffffffffffffffffffffffff
def fn:=0xaaaaaaaaaaaaaaaa
def tv1:=0xcccccccccccccccc
def tv2:=0xf0f0f0f0f0f0f0f0
def tv3:=0xff00ff00ff00ff00
def tv4:=0xffff0000ffff0000
def tv5:=0xffffffff00000000
def tv6:=0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def tv7:=0xcccccccccccccccccccccccccccccccc
def tv8:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def tv9:=0xff00ff00ff00ff00ff00ff00ff00ff00
def ib:=0xffff0000ffff0000ffff0000ffff0000
def ia:=0xffffffff00000000ffffffff00000000
def fz:=0xffffffffffffffff0000000000000000
def sw0:Nat×Nat×Nat×Nat:=(2,0x30,0xc,0xc3)
def sw1:Nat×Nat×Nat×Nat:=(1,0x44,0x22,0x99)
def sw2:Nat×Nat×Nat×Nat:=(4,0xf000f00,0xf000f0,0xf00ff00f)
def sw3:Nat×Nat×Nat×Nat:=(14,0x33330000,0xcccc,0xcccc3333)
def sw4:Nat×Nat×Nat×Nat:=(12,0xf0f0000,0xf0f0,0xf0f00f0f)
def sw5:Nat×Nat×Nat×Nat:=(1,0x44444444,0x22222222,0x99999999)
def ca:Nat×Nat×Nat×Nat:=(16,0xffff00000000,0xffff0000,0xffff00000000ffff)
def sf:Nat×Nat×Nat×Nat:=(2,0x3030303030303030,0xc0c0c0c0c0c0c0c,0xc3c3c3c3c3c3c3c3)
def ny:Nat×Nat×Nat×Nat:=(8,0xff000000ff0000,0xff000000ff00,0xff0000ffff0000ff)
def nx:Nat×Nat×Nat×Nat:=(1,0x4444444444444444,0x2222222222222222,0x9999999999999999)
def se:Nat×Nat×Nat×Nat:=(28,0xf0f0f0f00000000,0xf0f0f0f0,0xf0f0f0f00f0f0f0f)
def dk:Nat×Nat×Nat×Nat:=(7,0x5500550055005500,0xaa00aa00aa00aa,0xaa55aa55aa55aa55)
def sd:Nat×Nat×Nat×Nat:=(14,0x3333000033330000,0xcccc0000cccc,0xcccc3333cccc3333)
def nw:Nat×Nat×Nat×Nat:=(12,0xf0f00000f0f0000,0xf0f00000f0f0,0xf0f00f0ff0f00f0f)
def nv:Nat×Nat×Nat×Nat:=(30,0x3333333300000000,0xcccccccc,0xcccccccc33333333)
def nu:Nat×Nat×Nat×Nat:=(7,0x55005500550055005500550055005500,0xaa00aa00aa00aa00aa00aa00aa00aa,0xaa55aa55aa55aa55aa55aa55aa55aa55)
def nt:Nat×Nat×Nat×Nat:=(60,0xf0f0f0f0f0f0f0f0000000000000000,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f)
def nr:Nat×Nat×Nat×Nat:=(30,0x33333333000000003333333300000000,0xcccccccc00000000cccccccc,0xcccccccc33333333cccccccc33333333)
def be:=0x9e3779b97f4a7c15f39cc0605cedc835
def mk1:=0x3fffffffff
def mk2:=0x1ff
def mk3:=0x3f
def mk4:=0x1
def zp:=0x1d
def zk:=0x20
def mk7:=0x2
def mk8:=0xffffffffffffffffffffffffffffffffffffffffff
def mk9:=0x3ffffffffffff
def lk:=0x3fffffff
def lf:=0x1041041
def ld:=0x1d75d75d
def lc:=0x20820820
def mk25:=0xffffffffffffffffff
def mk27:=0x1041041041041
def mk28:=0x1d75d75d75d75d
def mk29:=0x20820820820820
def rt:=0x3fffffffffffffffffffffffff
def mk34:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def mk35:=0xffffffffffffffffffffff
def la:=0x1041
def kz:=0x2082
def kv:=0x1d75d
def ku:=0x20820
def mk40:=0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def mk41:=0x41041041041041041
def mk42:=0x75d75d75d75d75d75d
def zx:=0x820820820820820820
def kr:=0x1041041041041041041041041
def kk:=0x1d75d75d75d75d75d75d75d75d
def kj:=0x20820820820820820820820820
def zn:=0x7fffffffffffffffffffffffffffffffffff
def za:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def yz:=0x41041041041041
def yw:=0x82082082082082
def yt:=0x75d75d75d75d75d
def yj:=0x820820820820820
def lj:=0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def lh:=0x1ffffffffffffffffffffffffffffffffffffff
def lg:=0x2082082082082
def E0:List (Fin 3×Fin 3):=[(0,1),(0,2),(1,2)]
abbrev f0:=d9 [] E0
def r0:=0x101081828304042060a0c1850c18286061418404041010804202
def x0:=[(0x2a934f2e54,0),(0x332596daa1,0),(0x3c0e39f50a,0)]
def xt0:=[(0xaa,0),(0xcc,0),(0xf0,0)]
def c0:Cfg:=⟨9,18,24,30,mk1,0x3a071ffe00,mk2,mk3,mk4,zp,zk,mk4,mk7,zp,zk⟩
def N0:Nat->Nat
 | 3=>1
 | _=>0
def L0:Nat->Nat
 | 3=>0
 | _=>0
def H0:Nat->Nat
 | 3=>0x790df1
 | _=>0
def P0:Nat->Nat
 | 3=>0x0
 | _=>0
def gc:=[sw0]
def rx:=[sw1]
def sg:=[gc,rx]
def pa0:=[gc,rx,gc,rx,gc]
lemma lq:(range 4).all (fun s=>jM ((bar c0 (i9 c0.fH be pa0 (c8 a1t3 3 xt0 P0) N0 L0 H0) (c8 c0.fJ 3 x0 P0)) s) (N0 s) 0)=true:=by decide +kernel
lemma lb0:∀t,nV 3 f0 t->4<=t:=dp f0 r0 be c0 (fun _=>0) x0 xt0 sg pa0 [[(1,2)],[(0,1)]] N0 L0 H0 P0 rfl (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (s9 lq) (fun _=>Or.inl rfl)
def E1:List (Fin 5×Fin 5):=[(0,1),(0,4),(1,2),(2,3),(3,4)]
abbrev f1:=d9 [] E1
def r1:=0x404a162a0c8080a446180404a110c0c404246030c20045180644282123018622606060644c0c0c0c8981818191303030322606060668c982a44e1a30346161c346062c2c3860654991160ca142850a122448912142850a142448912242850a1428a1220281284880508485091008a090a100942440502
def x1:=[(0xaaaaaaaa4cc5404ea8c6318ac446fc0007feb111a0,0),(0xcccccccc9408ca29318c631c119fac1ff80104640b,0),(0xf0f0f0f038a293025318c630a7fb43e0003e2982d0,0),(0xff00ff0001302530c6318c673ee40800ffc1c03902,0),(0xffff00003a530c940c6318c7f90873ff00000e421c,0)]
def xt1:=[(0xaaaaaaaa,0),(0xcccccccc,0),(0xf0f0f0f0,0),(0xff00ff00,0),(0xffff0000,0)]
def c1:Cfg:=⟨50,100,130,136,mk8,0xffeaf8c81c71c71c7ffffffffffffc000000000000,mk9,lk,lf,ld,lc,mk4,mk7,zp,zk⟩
def N1:Nat->Nat
 | 5=>1
 | 6=>1
 | _=>0
def L1:Nat->Nat
 | 5=>0
 | 6=>0
 | _=>0
def H1:Nat->Nat
 | 5=>0x6ed0be
 | 6=>0x6ed0be
 | _=>0
def P1:Nat->Nat
 | 5=>0x0
 | 6=>0x0
 | _=>0
def gs1:=[[sw2,sw3],[sw4,sw5]]
def au1:Nat->V
 | 0=>[]
 | _=>[]
def ap1:List (J):=[[]]
lemma lp:(range 7).all (fun s=>jM ((bar c1 (f8 c1.fH be gs1 au1 (c8 a1t5 6 xt1 P1) N1 L1 H1 P1) (c8 c1.fJ 6 x1 P1)) s) (N1 s) 0)=true:=by decide +kernel
lemma lb1:∀t,nV 5 f1 t->7<=t:=uy f1 r1 be c1 (fun _=>0) x1 xt1 gs1 [[(2,3),(1,4)],[(2,4),(0,1)]] au1 ap1 N1 L1 H1 P1 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 1<=i from hi) with ⟨k,rfl⟩;rw[mF];rfl) (by decide +kernel) (s9 lp) (fun _=>Or.inl rfl)
def E6:List (Fin 6×Fin 6):=[(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,5)]
abbrev f6:=d9 [] E6
def r6:=0x804106061500822c4ca820090b1464820202141861804506061501014a093040208b012a1121481828360a090612141b050483090a0d828241848506c14120c2428360a090612141b050483090a0de3868c582c54a1a3262c0d1258a94a832253252a383054c8cf1a2c4c90e0c0d2a33a64a8d162428348912244891222448912244890a142850a14270e1c3870e1c2244891224488a142850a1428e18284480c1421222428050248890a0220512122281014884e18284480c08052223860a0c1420202
def x6:=[(0xaaaaaaaaaaaaaaaa4ce38e4c02930e1c3870e1c4082d9447ff0003f80fe004082d944400,0),(0xcccccccccccccccc3804d338a0253264c993264093426ffd0901fc00001fc09342600109,0),(0xf0f0f0f0f0f0f0f094002594000e142850a142a92083fa9ab2fe0007f0002920800a9ab2,0),(0xff00ff00ff00ff00013000a0c4c0489122448931c2fc4310dc000007f01ff1c2004310dc,0),(0xffff0000ffff000000e940013300a142850a143e3f0883e0e0000007ffe03e000883e0e0,0),(0xffffffff00000000025380025978c183060c183ffcf30c0300fffff80000003cf30c0300,0)]
def xt6:=[(fn,0),(tv1,0),(tv2,0),(tv3,0),(tv4,0),(tv5,0)]
def c6:Cfg:=⟨88,176,206,224,mk34,0xffffffe8eeeceae81c71c71c71c7ffffffffffffffffffffff0000000000000000000000,mk35,lk,lf,ld,lc,la,kz,kv,ku⟩
def N6:Nat->Nat
 | 6=>1
 | 7=>14
 | 8=>1
 | _=>0
def L6:Nat->Nat
 | 6=>0
 | 7=>4
 | 8=>0
 | _=>0
def H6:Nat->Nat
 | 6=>0x3a0f39
 | 7=>0xfebd69fa694af58505f36e68e0d75cb6bc27974b798d306b4aeee2418be33aef8a3a85243a0f39001f92
 | 8=>0x3a0f39
 | _=>0
def P6:Nat->Nat
 | 6=>0x0
 | 7=>0x5000000040000000280000000700000030000000900000006c000000740000007000000005000000010000000b0000000000000024
 | 8=>0x0
 | _=>0
def g6:=[ny,nx]
lemma ln:(range 9).all (fun s=>jM ((bar c6 (p5 c6.fH be g6 (c8 l5 8 xt6 P6) N6 L6 H6) (c8 c6.fJ 8 x6 P6)) s) (N6 s) 0)=true:=by decide +kernel
lemma lb6:∀t,nV 6 f6 t->9<=t:=tk f6 r6 be c6 (fun _=>0) x6 xt6 g6 [(3,4),(0,1)] N6 L6 H6 P6 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (s9 ln) (fun _=>Or.inl rfl)
def fb:List hA:=[⟨3,E0,4⟩,⟨5,E1,7⟩,⟨6,E6,9⟩]
lemma hT1:c4 fb:=g9 _ _ lb0 (g9 _ _ lb1 (g9 _ _ lb6 (fun _ h=>by cases h)))
def E7:List (Fin 6×Fin 6):=[(0,1),(0,2),(0,3),(1,2),(3,4),(3,5),(4,5)]
def f7:Z 6:=fun x=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 2)||(x 3&&x 4)||(x 3&&x 5)||(x 4&&x 5)
def r7:=0x10108182830808085061890a44c951a2208a060a0d201441818514046060a0c60114181852228918062490128182832421130506100820c0c280808085061908a44a01892804906061501010a0c3060a0c0612141b050603090a0d828301848506c14180c2428360a0c0612141b050603090a0d828301848506c14180c2428368c98b058a943464c581c346162a52a0e1a32604a64a58a8e0c153232c4c706069519526345890a0d22448912244889122448912242850a142850942850a142850912244891224448912244891183060c183060a142850a1428a12224060a1091121403050848890a02848890028909222281014884a1118100a4445090c1420202
def x7:=[(0x2aaaaaaaaaaaaaaa933808d34d38d30003a34c00e1c3870e1c38720408aa54ffc000fe0007f000081022a95200,0),(0x3333333333333333254ff54e94e6a5a004da380122448912244894489115bfaa407f0003f8001fd122445600a9,3),(0x3c3c3c3c3c3c3c3c0e9403a53a500e000940940142850a142850a891221feb54bf8001fc000fe022448800ad52,3),(0x3fc03fc03fc03fc000013000a285404d301500e68d1a3468d1a340e1ffe1020700000000000fffc3870004081c,0),(0x3fffc0003fffc00000025a00000b2894e000a13a142850a142850f1fc3c60c18000001fffff0003c000f183060,3),(0x3fffffffc00000000000e0280000003a502c025c183060c183060ffe3c1830603ffffe000000000078f060c180,3)]
def xt7:=[(fn,0),(tv1,3),(tv2,3),(tv3,0),(tv4,3),(tv5,3)]
def c7:Cfg:=⟨102,204,276,294,mk40,0x3ffffffa3ffa3aba071c71c71c71c71c71c71c7fffffffffffffffffffffffffc0000000000000000000000000,rt,mk25,mk41,mk42,zx,la,kz,kv,ku⟩
def N7:Nat->Nat
 | 5=>2
 | 6=>8
 | 7=>29
 | 8=>10
 | 9=>1
 | _=>0
def L7:Nat->Nat
 | 5=>1
 | 6=>3
 | 7=>5
 | 8=>4
 | 9=>0
 | _=>0
def H7:Nat->Nat
 | 5=>0xdb6fbcb59fba
 | 6=>0xff4208b8920aa522bf75dad66127d83e4ab5329e30073865
 | 7=>0xf6a0f1cdee20cc92b8cb3eaabe18aeb8920aabab409e48b08bb10987d58b7fd1897e822678ec1b73bbc36127d854ce3551601750a3d94acccc477f9a42f4983e088739321e2aff512322a72181e91a87070e618f0260cc
 | 8=>0xf6a0f1be18ae9f3eed73bbc36127d842f49840121b2181e91a870713d354
 | 9=>0x6127d8
 | _=>0
def P7:Nat->Nat
 | 5=>0x1c3d01000839
 | 6=>0x1801c4a01000c3900002c3d0080542d000000000000043d0080489900805441
 | 7=>0x145c00800c7a000000720080105601001403010008390000107200801042000010520180104a00801876008018a20100083b008014540000000000801c720000243e000008010200184a01001001000014240180103d0000003e0000083a010024a20000144000801401010010620080189a
 | 8=>0x5c01000003008000020080005400000000000000240000003c000000400080000100000034
 | 9=>0x0
 | _=>0
def tg7:Fin 6->Nat|0=>0|1=>3|2=>3|3=>0|4=>3|5=>3
def gs7:=[[ca],[sf],[se,sd,dk]]
def au7:Nat->V
 | 0=>[]
 | 1=>[se,sd,dk]
 | 2=>[nw,nv,dk]
 | 3=>[sf]
 | 4=>[ca]
 | _=>[]
def ap7:List (J):=[[],[(2,5),(1,4),(0,3)],[(2,4),(1,5),(0,3)],[(1,2)],[(4,5)]]
lemma lm:(range 10).all (fun s=>jM ((bar c7 (f8 c7.fH be gs7 au7 (c8 l5 9 xt7 P7) N7 L7 H7 P7) (c8 c7.fJ 9 x7 P7)) s) (N7 s) 0)=true:=by decide +kernel
lemma lb7:∀t,nV 6 f7 t->10<=t:=uy f7 r7 be c7 tg7 x7 xt7 gs7 [[(4,5)],[(1,2)],[(2,5),(1,4),(0,3)]] au7 ap7 N7 L7 H7 P7 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 5<=i from hi) with ⟨k,rfl⟩;rw[mF];rfl) (by decide +kernel) (s9 lm) (l0 fb hT1 f7 E7 tg7 [.emp,.b2 2 (.f0 0 (.base 0 [0,0,0,0,1,2])) (.f0 0 (.base 0 [0,0,0,0,1,2])),.b2 1 (.f0 0 (.base 0 [0,0,0,0,1,2])) (.f0 0 (.base 0 [0,0,0,0,1,2])),.emp,.b2 5 (.f0 3 (.base 0 [0,1,2])) (.f0 3 (.base 0 [0,1,2])),.b2 4 (.f0 3 (.base 0 [0,1,2])) (.f0 3 (.base 0 [0,1,2]))] (by decide +kernel) (by decide))
def fa:List hA:=[⟨6,E7,10⟩]++fb
lemma hT2:c4 fa:=g9 _ _ (dz f7 E7 (by decide +kernel) lb7) hT1
def E12:List (Fin 7×Fin 7):=[(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(3,6),(4,5)]
def gf:Z 7:=fun x=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 2)||(x 1&&x 4)||(x 3&&x 5)||(x 3&&x 6)||(x 4&&x 5)
def r12:=0x88061460614101489928344852264a0c1013068c83404052a34c0202021418640208b132a02010418185100522c4a2480248d131240208b012a1084441818544052060a0d20144181852228c12120c20202141861406148062488ca9202891804506061501014a093022090b0064a121c81828348090850619208a9218283046a480a26201841818528092300c4984850483090a0d84850483090a0d84850483090a0d84850483090a0d84850483090a0d84850483090a0d84850483090a0ee58992a474e3c1e3868c582c54a3a72e3c293464c581a25b3569d172cd8992a4c858a94a83227365ab1a2a64a547060b9b1d6a74a3434c8cf1a2c4c90e0c0f2e3ab161a54674c951a2c4850793264c993264c98b162c58b162c5870e1c3870e1c352a54a952a54a9468d1a3468d1a270e1c3870e1c382850a142850a1470c0c1422a51a070c14224060a1193161c1092224280502c98b0e0a94684485060244485011038b0d185051212228101c986a51a1120a44270c142240604039315489092223860a0c1420202
def x12:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa4d34d300e3934c02a34d38ce4e34c0a933804d3001c1c1c1c1c1c1c0840841222daca9447fff80007f807f800001081082445b5952888000,0),(0xcccccccccccccccccccccccccccccccc3a596539300e01300e94e553a8038a4e54c000e4c64646464646464400929a0442537fffd284807f800000007f880125340884a600002509,0),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f094e38002502538e0153a502501a94000e9682a5a82828282828282a92921044883ffd2a9ad597f80007f807f8052524208910000a5535ab2,3),(0xff00ff00ff00ff00ff00ff00ff00ff0000000e3804c09404c0000680955a0c0000159400191919191919193e31c017fffc020031006e00000000007ffffc638020000004006200dc,0),(0xffff0000ffff0000ffff0000ffff000000000e4c0380025300000b0002801394000ae0096424242424242431fe3ff87008841c3e08700000007fffff8063fc0000e01108387c10e0,3),(0xffffffff00000000ffffffff0000000000ef8094094038e968a28000000025318a2300032828282828282801fffde780f31860c031807fffff8000000000007bcf01e630c1806300,3),(0xffffffffffffffff0000000000000000b0000000000000000000000030c00002800c3280101010101010103fc03e07ff03e07f003e007fffffffff800003807c0ffe07c0fe007c00,1)]
def fw:=[(tv6,0),(tv7,0),(tv8,3),(tv9,0),(ib,3),(ia,3),(fz,1)]
def np:Cfg:=⟨143,286,388,448,za,0xffffffe8ffecffe8ffffffe8eeeceae81c71c71c71c71c71c71c71c71c71c71c71c71c71ffffffffffffffffffffffffffffffffffff800000000000000000000000000000000000,zn,rt,kr,kk,kj,yz,yw,yt,yj⟩
def N12:Nat->Nat
 | 5=>1
 | 6=>14
 | 7=>62
 | 8=>185
 | 9=>30
 | 10=>1
 | _=>0
def L12:Nat->Nat
 | 5=>0
 | 6=>4
 | 7=>6
 | 8=>8
 | 9=>5
 | 10=>0
 | _=>0
def H12:Nat->Nat
 | 5=>0xabbcf4
 | 6=>0xfd9644ee0520ec3af6b8f06bb1c310961b578dd4be8b46ef5c6eed55edfd398e2e3566be1db5880c21de
 | 7=>0xea85b8ea4027dd9b21d8badfd87400d63ce8d42c6dd17089cec13acc90dbcafdd7c842e0c615b3bd0202b82e8aaf909eae483da3908c9d60bf9535d293b7f08ff8168f18c587ff2b7deb467c13767bd65a7a8bab79253773df616bd79268deb867f68c644e2d6314315c6eed5bef72547c6e4b87c14a7bcb43e1cd3fde703b62eb3aea473a3df8353cfb3188722d19e12c43922687f623ec91223f3f1f454319a49a17f8d814444f12a39312a1d11234420b600109cd9e046e43
 | 8=>0xfd37a4fbcbdffb7fb6f9dddbf8acdef62538f59073f4144af270aff20ddaf10b1deeb900eb2050ea841eea4027ea2f7eea0ca4e817c4e7c76ee6b6e2e62416e6167ee2148fe0c41adf7d9cdee409deb6abde25c4dc2b13dbfe4cdb2f80db2421da840dda6e41d97758d88031d51216d4ff0fd458cad33db8d18d10d17089d160f1d05bb1d04610cf82facf0a82cea0e8ce82edcdcd3ecbfe65cac509c9dca2c71080c66292c49434c45b10c378ccc3718ac30567c2e63bc19e5bbe5cbabdf320ba490aba3e97b9b4b4b865feb82e8ab6a424b6002bb5df20b35495b1eca7afa00cae483daa0651a8afaba70c53a6febba3f93da34f68a2a034a065d99fef519e14f19d8b649bbd4d9744e893932a91ecaa8db26e8ae37788e66888c23287f4ba87945184403183ce7881440880832b7ffb537d6ff77c11e27aed3b79bb6e785eed77d11575775d741c8c73333a72d17c6c93646c8d496c47216b7da86a72b26a5d296a0c0f65b7c564df9961f8dc610fc060e43a5f62d15efd095d5b375a4104586e49585f78568c7b5604c9547c6e50827d500b4a4fae134f733f4e2b974cdecb4cac034c05fa475df44637d34590cc437f47422c4540fdd540cc3e3fcabe3dc85d3d72f839df8c37af9137325b36157f353cfb35130d318872304f372687f625ab6a2469812271e121f2431fe0891ef2a71bebe51b03ca188cb7159dfa157d0f14444f13d51013aced13a228136ba30e7a390d39eb0b19370a93f30a8a4309bb22097d9f057a55031c98
 | 9=>0xf270afe3f118db2f80d9e775c71080c38c44c2e63bbfbd01baa831ba3e97b6002bafa00caa1aa3a9bc56a651c89e1055872eee84403179bb6e785d59781fd6741c8c5d5b37568c7b42dea63fcabe3e12a0353cfb31887205aeb5
 | 10=>0x318872
 | _=>0
def P12:Nat->Nat
 | 5=>0x3075
 | 6=>0x509d0000684a000064510000682b0000ac7a000068230000943d0000683b0000b4750000489d00000c76000068730000685300008c51
 | 7=>0x2609d0001f0760000649b0001e43d000260d10000649a0002242d000268d10001f855000224d10002a89b00004cc90002503d000218550001dcd900009451000090c90001b4820000649900006453000158550002a8530002389d0002a83a00014cd10000f8cd0000d0760002a839000298c30001b4760001e83d000264c9000104560000643b00011c2d0001b4750000b0550000d8d90000b02d00026cc900016c3d0001b44a000088d10000647a0000642b00006c9b000000000000647300025451000074560002a83b00028c9b00017c5100000c550000e4cd0000d89d00003026000154c3000034a90000882d0002a8730002a82b
 | 8=>0x89c0000103e0000007600003c9a0000207a000074d30000585200004c56000004400000200100004c3b00001cfb0000604a0000702e00005c7600004ccb000054620000603e0000745100001caa00007471000074990000183e0000589a000074c900006cd30000189f0000205600000c3e00006ca20000043c000010760000549a000018010000143e0000583e000058820000705200001c010000543e00004c7100006cd10000104a0000608200000c4a000020720000548200001ca20000503e0000540100005494000064db00000802000004080000740100005c40000060a2000028720000084c0000209a000004c300004c9a00000864000008bc0000642a0000048c00004cd300000056000050d9000034720000042800006062000048a30000082c00000407000010c90000086800007453000074730000749b00005c020000203d0000204a000074cb0000209400002052000020620000285600001862000014560000489b0000287a000034d300000c6200004c99000030a300004c5300000403000074fb0000743900001062000054a2000034d10000086c000008010000040100001c9d000020d30000085800000424000020420000643e00004c3900006cfb00005c78000018aa0000246200000c560000649a00004cc90000643a000010cb000008940000705600005c3c00003c3a0000046c000008ac000064fb00006c010000047c00004c73000018d9000028a20000349a00001482000060760000642e00006c4a0000608c000054fb00004cfb00006c3e00004c01000010d30000743b000048c30000283e000004740000003e000024a200006c7200003cfb0000243e000014760000049b000010820000000000005c2c0000085600001876000068560000683e00005c01000028010000749a00000830000014a2000034fb000030c30000689e0000189d000064c900000c72000050010000547200001c3e00004c9b00002cc300006c6200001c56000028fb000024fb000020fb00004c51
 | 9=>0x40000000040000003c000000940000000800000054000000c300000034000000440000008c0000002800000007000000050000000b00000048000000090000000200000003000000010000004c0000005c000000240000006c0000007c00000064000000740000002c0000009b0000000000000084
 | 10=>0x0
 | _=>0
def ie:Fin 7->Nat|0=>0|1=>0|2=>3|3=>0|4=>3|5=>3|6=>1
lemma fd:(range 11).all (fun s=>jM ((bar np (uh np.fH be (c8 lr 10 fw P12) N12 L12 H12) (c8 np.fJ 10 x12 P12)) s) (N12 s) 0)=true:=by decide +kernel
lemma lb12:∀t,nV 7 gf t->11<=t:=mf gf r12 be np ie x12 fw N12 L12 H12 P12 rfl (by decide +kernel) (by decide +kernel) (s9 fd) (l0 fa hT2 gf E12 ie [.emp,.emp,.f0 6 (.base 2 [0,1,0,4,2,3]),.emp,.f0 5 (.b2 6 (.f0 3 (.base 1 [0,1,2])) (.f0 3 (.base 1 [0,1,2]))),.f0 4 (.b2 6 (.f0 3 (.base 1 [0,1,2])) (.f0 3 (.base 1 [0,1,2]))),.base 3 [0,1,2,3,4,5]] (by decide +kernel) (by decide))
def E20:List (Fin 7×Fin 7):=[(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(3,6),(4,5),(5,6)]
def ry:Z 7:=fun x=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 2)||(x 1&&x 4)||(x 3&&x 5)||(x 3&&x 6)||(x 4&&x 5)||(x 5&&x 6)
def r20:=0x202225418648890a546982020214186100522c4a2480242c519220092344c4a008418144848851264695010858a93088061060615121481828342212280a26008418144808088920a18202021418685062060a0e08843804c82222a480a26242821418618045090c16208498144822090b006492214418185404052824c110a858a52a28092300c4b03090a090612141e061214120c24283c0c24282418485078184850483090a0f03090a090612141e061214120c24283c0c24282418485078184850483090a0f262c382e58992a474e3c3262c381e3868c582c54a293464c581a2572cd8992a4c858a94a83226ac68a992951c182d6a74a3434c8cf1a2c4c90e0c0eac5869519d325468b12141d4a952a54a952a54a3468d1a3468d1a30a142850a1428509224489122448912224489122448912242850a142850a14270e1c3870e1c387050a142850a1428524448501c3030508a946844850601c3050890182844248890a0140aa51a112141809112140440d185051212228101a946844829109c305089018100d489092223860a0c1420202
def x20:=[(0x2aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8e38e4ce0004c04d38c028e4ea8ce540a93000000e070381c0e070381c8088404222eb29447ffe00ff8000000ff8000040442021117594a22000,0),(0x33333333333333333333333333333333134d30134c038e3a50005539400132804ce2bf4c32190c86432190c86504100a984414dfffca1200007fc01ff00003fe8208054c220a60000509,0),(0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c2596538038094094e2808e53802a58e8025000a8140a05028140a0502a29229104883ff2a9b565ff00003fe00007fc011491488244000954dab2,3),(0x3fc03fc03fc03fc03fc03fc03fc03fc000000940013000000553000013540b1300031300c86432190c864321903e031c17ffc0803101b800000000000007fffe1f018e080000401880dc,0),(0x3fffc0003fffc0003fffc0003fffc0000c000025940013000000300000a000009404c09520904824120904824031c3e3ff00a11c3e21c1ffff8000000007fc0018e1f00380508e1f10e0,1),(0x3fffffffc00000003fffffffc000000000fc038e38efe5038b0e00000c00000e3389653341a0d068341a0d0683c1fffde00f0600c006000000003ffffff80001e00000f0078300600300,0),(0x3fffffffffffffffc0000000000000000000000002500ea00025000e2533802500000e028140a05028140a0503fffc0207f0381f003801ffffffc0000000000000fe0103f81c0f801c00,3)]
def fv:=[(tv6,0),(tv7,0),(tv8,3),(tv9,0),(ib,1),(ia,0),(fz,3)]
def nn:Cfg:=⟨153,306,408,462,lj,0x3ffffffffffb3ffa3ffffffa3bbb3aba071c71c71c71c71c71c71c71c71c71c71c71c71ffffffffffffffffffffffffffffffffffffffe00000000000000000000000000000000000000,lh,rt,kr,kk,kj,mk27,lg,mk28,mk29⟩
def bd:Nat->Nat
 | 6=>1
 | 7=>51
 | 8=>557
 | 9=>410
 | 10=>19
 | 11=>1
 | _=>0
def L20:Nat->Nat
 | 6=>0
 | 7=>6
 | 8=>10
 | 9=>9
 | 10=>5
 | 11=>0
 | _=>0
def H20:Nat->Nat
 | 6=>0xa42216
 | 7=>0xf516ddf3d698f3b005ef2d88ef296dec3ef7e16af5dac726d875c4cfaf00cbee06ca61babe5151bba5feb88817b15ee4b07008b008d0a860e9a1a97d9f95879b582c800dd478105a72a6956d10426ab7766655f663c4b9604d3a60096c55fd9f5544855101a64b7aac411bdc38e87e32dd1431e16028d5d72515fa21f0eb1e016f1ab779168c3610bf0810a6890b76a30a4dfd08ccdf07c914
 | 8=>0xff685cff5216ff0ad8fe2f92fdb975fc3e2cfbb49ffb9938fb937cfa5699fa2f5ff9f2a7f9b957f9a091f94e2af8b624f842bcf83bccf724cbf6262ef5938cf52b62f5275af516ddf4c749f46d38f441e4f3e634f334b2f32c8af2c99df29fe5f29ceaf1b87df185e9f180e0f1640bf15542f0fea8f00069ef296def07adef0623ee81c9ee2129ee0febed95d0ed331ded0541ed01e4eccbcaea706be7f1c1e7a100e78497e74fc3e6953fe68025e4ca19e4c4f3e47cc3e4734ee3c687e38b28e2d928e1ee0be1df9ee17396e04f8adfb725df95daddec46dde6dedd364bdc85c9dbfe57dabde3d9b5f8d98160d9180ed90713d8e425d7ff38d794c6d77473d77233d75052d73b4fd59ce5d5795fd54188d52279d47a8bd446aad40458d3db94d3b9ebd3a916d396a6d2dffad1fcf6d1cdfad17648d164fcd139c3cffefacff265cfdbb1ce8aa1ce7a52ccd9b9cc502ccb7d46cb6aabcb66dacb0f9ccaf976cacb81ca54ecca3468ca2998ca1e98c9c1e7c955dbc94ac1c9164ec8e865c8c647c8b151c8a19ac80bdbc77833c74bbfc6fa90c5e5b9c5de98c5aa60c52214c4f355c4c196c42305c3d1dbc377d8c2e192c2d7f7c2b03cc1d951c1051ec0e5e8c0a75abebcb6be48f4be3bbabc8344bc0d67bbe807bb4706bb3bc2bb0b38bab9b6ba7fb8ba48abb9eab3b8ce66b85a99b7ab30b6ebe4b6e0c5b6d6ebb66270b65919b647aab63bddb6371cb5e572b5445fb510b1b4bed5b49842b49233b42eb8b42640b3be8fb35943b341dab304f9b150c3b0e950b05e5ab03167afb85eaf7b04af6086af573caf307aaecacfaea15cadc0c7ad8218ad2734ab6656aaacaeaa16bea97513a8d44ea8d348a8b59aa88036a668a4a64576a643ffa63f3ea55c51a44eada30978a2eb0fa2e154a2dd36a2008ba1f802a1ef869f849f9f29f19deaaa9d47be9d234b9cec8d9bf9249b85819b03ef9afee799a8559921f197388296c20c94b4b1947de693fe82939b0992fc6d92a5ab9299989232be90d61e90a3a8904d1f8fe90a8fe5e08fa9028f9d6f8f22948ee9918d8d598ced928ce5578cd87f8c40cd8b49f78a34e989d00e898348897fa989720c895bcf8787dc875c4d8665fb861ee585e15b8564ef84991f83a7c482d2b58281ff8224cb808650808003804ae8801a157f94d77ee5727eb1827e6c877cc3227c962c7c786c7c25d17bba547b54917a7b2c7a2b9f7a145c79b84578d2b378b64778a7a8788c94784e517827be77fcca77d99c778e5376018d75b15075732274fc9b74f3c174a8aa74757a74559474313d73b56f73725772a6957294a87288ed7278ce715c0f7102a270f10d70b6b06f8d6f6f2a1b6db44f6d17a56cd7686c94f46c32b26bddbe6a90e66a8faa6a23e76a007969fab369eec469ce666943f568f76868f39a68a7c968a1e567ccf066c3df6570e86485ac648505647f27640ef9640e7964015a63178d63015362fe0962495c6091f2608554604d3a5f23bb5ebf325e78525e38c85e31915de4045dd4f35db8b05d66005d50fb5c96445c40695b33ef5b255d5b085a5ac4f15a80d35a6cd059205058117a56cc11568be95670a755c3a35542b9553b24532f7951be16519a5a51828050d0ef50a09a505eba50496d5002704ffc104fac374ed9734de47e4dc0d24c951a4b01b84ac4784a5d2e49e27749e1ca4971aa48cbc6483d904811f1475340468e5746849e46242b45e9ba44e2f0442dab4422d4441ac34418754406444346e342c0b24265c5423fb34102bd4014fd3fe5ee3fab7b3e3d5f3e17223dfe443d72643c09943aab7f3a562a3a37cd39f202399cd438e85237231a36dd09369cc2366ab235f94535c4ea35872c35513f34de4a34827d348089342b7233fef03276de3225e431dcff2fdffe2fdbaf2f249f2ecba22cd8a22ccc202ca71b2ca31a2c27262ba30b2b3de52b2f652b145b2b027e2ad2112a8f88295a7b2947d7278a25273009271fad27191d26292325abc82536e925254e24cbef24980b2490f4245423243e652435b02414d022d91222b4d422adbe22998922892821e0b221df9c21357720e10820d2a21fcfe51fca2b1fafef1f58181e9fbe1e50781c9ad81c3e221bd16e1b64001aa7681a75361a472c19b1e419117118e64f18c2e017ce0817446c172c5e16d09616a483169f7d15bb5314ccfb142c1613fdd913e1e113d423134c8a12e9a91011100ec9ed0e20070deace0de10a0cea8c0bdfb70aefdb0a5a88094b7007def207b9290744f907386e06c33806aaf00699e10665f50616a30606a405af4c03f97203bcf00346ff03000e02253d0184e301259900f5b10038a8
 | 9=>0xff0ad8fdb133fcc89dfb37f5fa5875f9d9e0f8cd4df887d0f842bcf7bfadf6e301f5f727f59913f5275af4d0f0f4b35cf3d698f18a60f14f21f03db3ef551def12edee81c9ed6843ed0cf3ecfb84eba7d3eb22aceb1450ea706bea4c2de9b63be6c4c8e4c4f3e4c15ce4182ee3d54ae3c14fe395fbe37165e358abe260c1e1a0bee19f6de12971de9c43de7035de2178dd283cdd2197dc8127dbe84fdb46d3da1874d9ce8cd9cc9cd9c84dd8df6bd88f5bd857eed82a2cd77babd77473d6a4aed639c7d56931d51664d4f1ced4e616d466a4d3b9ebd39e1dd33d78d21430d164fcd105ccd0a1f4cffefacf79b4cdc98dccd9b9cca9d3cc96eecc502ccc3036cbb18ccb4ef5cae46ecadc85cab08fc955dbc8c647c7a826c6667fc5458cc28d5dc27de4bf8f27bebcb6bda4e7bcdae1bc5ceeba48abb8fa36b8f425b7ab30b728cfb65919b647aab62c7db60f97b5f3b6b50a64b4f735b42b2cb36c11b312dfb304f9b0e24db0bdb7b0b031b03167b008d0b0050eaf6b82af6a06af573caf503baf374faea15cad149dac617eab4737a9be1ea88e92a88036a8587aa83053a80ab7a750cba72577a71adea700e1a6cf61a668a4a5ad30a387aba2f6fea2e154a23268a1f802a1dcbba0ea6f9f75999f38d49dd3b79d5e089d1d989c4a9e9c3dd99c1dbe9bd59f9b582c99c7a8996c719921f19875929834d59828d7977714973882972d9996abbc95d1769595fb95781d9425b593d61b92dd87927ae591da388ff2248fa9028ead988e6c018d926f8d79a28d75ee8c4a768c40cd8be4848aa29e89309088c72f88049d877f368724408665fb83df2283af9983a7c48311fa82bf4482b1728193ba80f06580ba0680a97e80661280026e7fb3177d77557cc3227c0df77a1f8d79e4e17913b878543a784e51782fa477f8d0778e5376dbf37680c7766ba275657d7540e774fc9b74f65d74559473ed367339ed72f98272f292723f977173b470f10d6e8ccb6de4b26d53b06cd7686c71616c37b26c00a56b9e0e6b75926ae0ba6abc246a8faa6a20496a007969a4556982a5696873695e0f685c5c683968680a90679f3066b598665c426633ed6541d8651d4263c9916366bc6307db62c38a622ae961aade61194b605b20604d3a5f9ac45eff705e59895e1b235d57245d1a6d5cac075c30d55b7a695b54af5ae8dc5ad2c059a9bf598e49598ac758096e5691f3567b965629ab5549fa5481d753ee075303f252274450ff4a50496d4f7ea64d23ce4c88624b7bc44ae9214951d44786ba467a874511f64428454399af426fa24230ae4211a84139884102bd40dba540da583fd1a13fc4b23f13753e4d2a3e08443c472c3c24b83a6b6f37cf72377cb23749c436b4c5366211351a1834827d31e160319ff53115e330cb4e2fbcf92f884c2f13562ddf022dbfa52cf7ef2c998f2c58802c27262c01132b99da2b972a2abf962abd0c2a61762a0c9b27ce4f27590d2697d025707d243e6522d91222adbe22a9522289282214cc21f0eb21357721126720d2a22088071fcfe51f400e1ea3a91d53001d498c1c9ad81c75ea1c0a431be5ad1b73851a91fc1a492f19e58d19b1e41948e618e64f17aaaa168c36167e7614a84a13fdd913d42312b5e00fb9b70f6dd30cea8c0c12650b192c0aefdb0ad1b909f44809515a09381208ab75086d9e08096107c9140744f907292b0703e306804803c3d70350cd
 | 10=>0xee81c9e4c4f3d8df6bb5f3b6b304f9a88036a2e15482b1726cd768604d3a59a9bf2abf9622adbe22892821357718e64f13fdd912b5e009f448
 | 11=>0x604d3a
 | _=>0
def P20:Nat->Nat
 | 6=>0xb02f
 | 7=>0x80c90007c47100011899000068d10002189d000118510003cc390001dc510003a47a0003cc230005c027000118c90007402e0008109b0003a46a0003cc3b000810730000fc390001b8510003cc9b000000cd0007c4390002ac790003cc5300061c3d0007e83d0003cc730002ec5500046cd1000000000001bc55000154790007cc510001b8710001b8c90003cc3a000030490002acd10007c4510008102b000154590007c499000810530003a4270000fc510002c0550008103b0002aca10007403a000154d10007c4c9
 | 8=>0x46ccb0005d0990002a44a0000bc54000428c90005245a0005185a00046cca000018c0000314d20002d05200064d0500013401000544d20003285600056cd30003383e000270390003ec5100007c350003d49a00038c9e0000b801000054c9000284520005283500013480000364560003ecc90004843d0001a43600046c730001b8510004ac750003b4710004bc290000a85b0002f476000154510005307600017c9d0000343d000524ca000224340004dc8a00014c390003b501000624880006242800038c3600040c5a00006c3e00006440000624980003447a0004dc2d0000fc55000064280003342900022428000438d10005dc5600025451000110390000bc60000474610005bc710000a8a30000142b0003f03d0004808a0000e0510001a49e000480ca000014c90004c90900001471000070560003887a0005d0790000387300002028000280290004407a0000b8530005183d000004ca0003285a0001e4a20004c899000038cb0001389b00040c410002ccc90003645a0002d0ca0000c4ce0002d03f000134280000208c0002cc9900026c3d0000149b0004144a0003507a0000583e0004c9010001a4d20002f4320004f88a00041452000414620003288a0004289900040c6a000478560005d0a10001fc9a0004390900003899000018a80000643c000270c90000b87300017c0100049c7600063052000058d2000018600000389e0002fca6000270990000a8d3000428510000843d000540900006305700046c9900030c8a00003c760002450100040c2d000284d2000438990004f85a00001453000244c900036c320003ec990003bc8a000030d20006248400046c0100042839000488550002d03a0003b4c900053c2e00029c29000470550002a0cd0000c43e0000449e0004dc5a0005fc3d0002a462000228760001c85a0003b451000438a10005e0530000f43e0000d09b000624800004807a0004103d000388d2000624600005d0c900064ccd0001903d0001bc5a0000b09e0000a87b00025051000224030004a0560005c05100046cc9000030a20003b0760001347800064c59000058760000b0560000d0530000f4010001483d000410550005d0710004ac790004ec3d0004785a000340d20006303a0006243c00043c9e000224010005e09b0001e4520004ccce0003b89900047cc40000d83d0004a00100047c3c000224240001e45a0003dc3c000414420000385300015c760003bcca000624300004aca1000038430003bc5a00057c390003b05a0004207100064c750000d09e0002a4560004149a000038010003dc8800009c560002847a00025071000540480003103d0002405d0002b4d300033c3d00042871000070360002b4a30002743d00005056000624580003dc900002d09a00038c530000d0cb000420990005bc510005e0cb0005d1010004789e0001c8d20002d0cf0004603e000018580003448a00015471000094d20000c4620003ec7100030c760004c8c900014c510000f4d20001bc0100005473000064010005b4cd0003b4990001083d0004c03e00056c7b0002b4a600005c5e0001e4d200006c6200013853000054010006443b0004ac5500030c5600004ca20004c03f000110510001bc8a00023cc90001a45a00053c2d0000e8360005e073000438c90004b8a30001343c00006c76000568cd000038a2000004320000303e0001f43d00014c990000e0710005e00100030c5a0003bc01000624780004c03d0005343500060436000014520000bc58000544560000b83b000438710000a8a60000945200003871000018a00002242c0000bc010002ec710001fc320005943d0000584a00011099000338560005e83d000038c9000014990002cc51000054ca000088510001709a00004cd20005249a000388760005445a0000747a0000e0c90000fc3d00023d010000d43200003cd200058c3d00036c560003c43d0000103d0005183f0003d02e000000000001fc2e000270510003dc010003885600038c510000a85e0004b8d30003dc800006240100047c01000150360003dc480005404c0002cc71000014510000204000014cc900022832000244710004cc2e0001983d000540380005dc5a0000386a0001c8760006383d00004c5200047c280000545300043c36000544a20002707100000051000414ca00008039000110c90006303f00043901000424d30003b85100001801000244990000d0010000e1010004b87b00006061000328ca0000200100046c530003405600048c3d00014c710001e45600018c3200064c790004ac59000014cb0002d09f0005d10900064c550002390100043c9a00052401000014730003dc40000058ca000074d20003642e0003bc7600004c5a00005c6a0000140100003841000110710006246c0003b4390003442d0002fca300003c5a0001c8ce000100550000049a000038510000e09900064cd10002cc390000389b000054cb000664520005e09e0004205100040c42000360510001c87a0005c071000304c900043451000094ce0000382b0002183d0004c8710002d89e0003ec390004f87a00006cce0003d432000134880005a8510003d0730006449b0004703d0002d0570004c05a000290560000542b0002b45b0001bc760002d49e000188290001a4a60001387300009c9e0006343d000138010000903d0005903d0004a89a0003142d0000382e0005e05600017032000224780004dc7a0002249c0004806a00038c42000224400003885a000414010005e03b0002fcd3000138cb0004f86a000018280001e49e0000c44a0002f4ca00064d090003643200018c2e0001e83d0005f43d000058620002b47b000224a400050c3d0006643e0003b0d20005449e00004c9e000440560005f09b0003b07e0003407600046c9b000224740004787a0000c476000214010004883d0003d03b00038c73000134740000549b0003607100041456000064c40002a43e0006643d0002405100064ca1000350ce00060c3e00053c520004805a0003dc3000017c9e00040c2e0004b8a6000421010002ec51000350d2000420c9000038560003dc280000887100032876000018b00000d0730005408c
 | 9=>0x284a00003c5800003c6c0000340300002c010000384c0000440200003c3400002c3e00003c0e000018400000286c00000432000010010000380c000008cc000044710000187800004444000034400000344c00003c5400002434000020010000049e000014e4000010b4000030a000003c3200000c3e0000340c0000306c00002002000024280000285200003cbc000048fc00001040000010a8000010d400001cd400003840000028700000343c0000388c000038240000084c000044b0000004a40000289e0000443c0000382c000018e4000044fc000010e40000309c00002c5800002405000044c000003ce400002840000044cc000010530000348c000008d4000038ac000004b0000004dc000010a4000000b4000014ce00000468000010520000303d0000304a000030bc0000103c0000083e00001801000044540000305200004090000008e400003062000000d400000430000004d4000034ac000000380000387400001073000008d200003037000004ac000030e4000000e400003c4400003834000000d2000000a400000c78000004640000143e000044a0000048a400002862000014020000445300001c3e00000454000010020000240200003c420000489a0000203a000000370000389c000024030000186c0000146c000004ec000000a200001039000018ca000030440000106c0000087600003cb0000044ac00001c0100000874000004a600003cfc00003cc00000309e00002401000038c40000187200003c5600004458000044a8000048d4000044d4000038900000449b000044600000342c00004856000024240000086c000030420000348000000444000004a00000143c000034c4000044dc0000088c00003490000030b0000014ec0000045c000044390000404800003c5200002856000044a4000030fc0000006c000018900000309a00000438000030c00000449a00000c3c00003c2c0000105400000801000030cc00000cec00001802000014cc00000456000018520000445c000008640000400d00003c30000004b4000044cb0000042a0000349c0000043a000008900000342400000460000000010000146200003c0d0000084000001cd200002052000044ec000024ac00000c020000380b00001c400000289a00003cac0000342800003ca0000004a200000c62000020ec000028ca00003c9c00001c0200003ca80000447300003cd40000049a00000c7600003c600000003c0000340b00003880000038a40000003e000028010000440100003848000048540000444c0000347c0000347800000cd00000103b00003cdc00004464000030ac0000242c000034740000480200003828000004d2000048ca00003ca600003cd20000084a00002c0200002c5600003ca40000189400003c5e0000149400003c060000140100002c400000380d0000387c00002858000028b8000030a8000030d400003060000030020000087800001478000028fc00001c3c000034a4000004ca0000000000003c5c0000489e000044b40000303a000040380000340d0000384400003ca2000030dc00003c3a000034040000089400002480000044680000046c0000443a000030a40000383c00004840000004340000040e00003cec000044ca00003c5a000038b4000030ca0000305800001cec0000305c00003c0a0000083c0000445200000802000034b4000018ec00003c4c000010ec00003cca000028020000045800000442000008ca000030ec000004bc00003c2a0000387800003c640000042c0000340800000c010000045a00003c3800003c2e00000436000028b400003434000008ec000004e40000449e00004451000034440000304c0000000200000c4000003cb4000028d4000020400000286000003c3600003884000000ec00000cce000030640000446c000038050000247c00003c680000049c00003c9e0000045e0000303800003407000028e400003c9a0000445600002478000014d00000249c0000348400004499000024400000340500003001000028a40000443b0000044c0000004000004801000034480000144a000030b400001850000014e800004034000010b80000449c00003036000008620000042e000024a400003068000010510000285c0000303f0000247400001476000024040000103a0000305400003056000004a80000183a0000283e000028ec0000243c000008dc0000144000003c0500001071000004fc000044c90000483e000044e40000408c000004c000000452000000b8
 | 10=>0x34000000280000000500000002000000030000000100000024000000ac0000002c00000000000000800000007c000000780000009c00000040000000a400000074000000040000003c
 | 11=>0x0
 | _=>0
def ic:Fin 7->Nat|0=>0|1=>0|2=>3|3=>0|4=>1|5=>0|6=>3
def g20:=[nt,nr,nu]
abbrev hM:=bar nn (p5 nn.fH be g20 (c8 lr 11 fv P20) bd L20 H20) (c8 nn.fJ 11 x20 P20)
lemma b20_sm:([6,7,10,11]).all (fun s=>jM (hM s) (bd s) 0)=true:=by decide +kernel
abbrev S:=jM
lemma pD {P:Nat->Q}{b:Nat}(h:S P b 0=true):∀i < b,P i=true:=fun i hi=>hH P b 0 h i (mJ _) (by omega)
lemma pE {P:Nat->Q}{a b:Nat}(h1:∀i < a,P i=true)(h2:S P b a=true):∀i < a+b,P i=true:=fun i hi=>by by_cases h:i < a;exact h1 i h;exact hH P b a h2 i (by omega) (by omega)
abbrev B8:=hM 8
lemma b8_0:S B8 186 0=true:=by decide +kernel
lemma b8_1:S B8 186 186=true:=by decide +kernel
lemma b8_2:S B8 185 372=true:=by decide +kernel
abbrev B9:=hM 9
lemma b9_0:S B9 103 0=true:=by decide +kernel
lemma b9_1:S B9 103 103=true:=by decide +kernel
lemma b9_2:S B9 102 206=true:=by decide +kernel
lemma b9_3:S B9 102 308=true:=by decide +kernel
lemma lb20:∀t,nV 7 ry t->12<=t:=tk ry r20 be nn ic x20 fv g20 [(2,6),(1,5),(0,3)] bd L20 H20 P20 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun s hs=>match s,hs with | 0,_=>fun i hi=>by simp[bd] at hi | 1,_=>fun i hi=>by simp[bd] at hi | 2,_=>fun i hi=>by simp[bd] at hi | 3,_=>fun i hi=>by simp[bd] at hi | 4,_=>fun i hi=>by simp[bd] at hi | 5,_=>fun i hi=>by simp[bd] at hi | 6,_=>fun i hi=>hH (hM 6) (bd 6) 0 (kH.1 b20_sm 6 (by decide)) i (mJ _) (by omega) | 7,_=>fun i hi=>hH (hM 7) (bd 7) 0 (kH.1 b20_sm 7 (by decide)) i (mJ _) (by omega) | 8,_=>fun i hi=>(pE (pE (pD b8_0) b8_1) b8_2) i (by dsimp[bd] at hi;omega) | 9,_=>fun i hi=>(pE (pE (pE (pD b9_0) b9_1) b9_2) b9_3) i (by dsimp[bd] at hi;omega) | 10,_=>fun i hi=>hH (hM 10) (bd 10) 0 (kH.1 b20_sm 10 (by decide)) i (mJ _) (by omega) | 11,_=>fun i hi=>hH (hM 11) (bd 11) 0 (kH.1 b20_sm 11 (by decide)) i (mJ _) (by omega) | _+12,hs=>by omega) (l0 fa hT2 ry E20 ic [.emp,.emp,.base 3 [3,5,0,0,4,1,2],.emp,.base 0 [0,1,2,3,0,4,5],.emp,.base 3 [0,1,2,3,4,5]] (by decide +kernel) (by decide))
def gy:Nat:=0xf39cc0605cedc835
def ap:Nat:=0xffffffe8ffe8eae8
def fk:Nat:=0x162956a956a9a854
def fj:Nat:=0x3f1680c180c1c196
def fh:Nat:=0x559515fc15fc00e8
def fg:Nat:=0x161616fe16fefc00
def ff:Nat:=0x8040000000000201
def n2 : List (Nat × Nat × Nat × Nat) := [(0x0,0x10200010410010000200400000000000000000000000000000000000000000000000810200,0x20400400000000000400000000000000000000000000000000000000000000000000020001,0x1080042042081000082080020408102040810000000008040000000000000000000000000),(0x8800000000000000800000000000000000000000000000000000000000000000000000402,0x2100081081002000100040040810204081020000000400080000000000000000000000000,0x4040104104004000040100102040810204080000000810000000000000000000000000000,0x0),(0x410000008000000000000000000000000000000000000000008100000004,0x40000001000081020408102040000020000100000000000000000000000000,0x1000080840000001000000000000000000000000000000000000000001fc10200040008,0x200000000000000000000000000),(0x220000000000000000000000000000000000000000000000000fe0020400000810,0x400000000000000000000000000,0x1020000000000000000000000000000,0x0),(0x8000010000000000000000000000000000000000000000040001000000,0x80000080000000000000000000000000000000000000000000007f000080002081000,0x20000000220800000200000000000000000000000000000000003f80000100004100020,0x40800000000000000000000000000),(0x2000000080000008000000000000000000000000000000001fc000000200008002040,0x2001000000000000000000000000000,0x4080000000000000000000000000000,0x0),(0x100042000002204081020408100004040000000000000000000000000000000,0x80000000000000000000000000000000,0x1000000000000000000000000000000000008100000000000000000000000000000000,0x0),(0x10200000000000000000000000000000000,0x0,0x0,0x0),(0x20000020000000000000000000000000000000000000000000810000000,0x2000000000000000000000000000000000fe00000000001020204000,0x80080000002000080000000000000000000000000000007f0000000000002040400080,0x102000000000000000000000000000),(0x2000000000000000000000000000000000000000003f800000000000004080008100,0x8004000000000000000000000000000,0x10200000000000000000000000000000,0x0),(0x81004004408102040810200200400000000000000000000000000000000,0x800000000000000000000000000000000,0x2000000000000000000000000000000000401000000000000000000000000000000000,0x0),(0x802000000000000000000000000000000000,0x0,0x0,0x0),(0x104000001810204081020401020000000000000000000000000000000000,0x2040000000000000000000000000000000000,0x4000000000000000000000000000000004080000000000000000000000000000000000,0x0),(0x8100000000000000000000000000000000000,0x0,0x0,0x0)]
def hJ:Nat->Nat
 | 4=>10
 | 5=>204
 | 6=>490
 | 7=>686
 | 8=>298
 | 9=>10
 | _=>0
def Lf7:Nat->Nat
 | 4=>5
 | 5=>9
 | 6=>10
 | 7=>11
 | 8=>10
 | 9=>5
 | _=>0
def lu:Nat->Nat
 | 4=>0xfb8f44ea0b47e8cc71cf7f83addd5753e0484c171224793d23d66c1de2d3
 | 5 => 0xfff9a5ff5734ff31a4fe3c34fd5e67fb8f07faaa39fa3c7af8a324f796edf47ee8f429f7f37054f2bcadf29e79f266e2f1748cf10a3ff00ca9efd806ef34cbeeda7eee5457ed9618eb611be9ef29e9996fe9760de928f9e4de86e4cea4e3801ee34599e25647e1df24e15830de4092dce545db60c9db150fd82b59d801e6d75713d509a6d487ddcf6e5ccec46ecceae8cc7ab5cc1e73cbcacdcb6d0aca11d0c96e8ec7378fc67ea9c5c03ac4ac96c45aabc3b27bc2666dc1adefc13460c0c93ebe3b2fbcce85bb6463bb3726b8c9a3b89e4db765c3b76497b66b1eb56d55b15d3eb03fbbaf21adaee075ae42e0add830aac121aa0729a9d1aca59158a4fb1ea20865a1a5eea118a6a044509f496a9ddaae9dc7d19db2b49a0ff197d74f97c08695a70091b2999036228f41ad8f14638d72c48c65b48bccf78bc5698b89a7865161821dc08194748069557df8377d9f337c831d799b6278fb6577979876c96d75213c725c2e7073c56c8f566c74196c2f206babae6ab40a693d0e679f91673d16670742669acb6687c66647c265d26a65390c64eb9f6352c85cec1f5ca66a5a8f845a14b55954ab566e2d55adac535ff0524fb450d5834f7bb24c4a3c4b1f6d4b009e4a446f498e44472c8545b29443b39842c0ae42b46140df8540b6423d07473bcde53b0a8c38050f359f4e3152f63074d82f316c2e11af2e11af2d3ca32cc89f2c09612bf2162b82ef2a689329f2d329231a27602626c62825cb2b25b35e2448ea21aa65209bf9208a9c1e97f41e586a1d639d1acba71a092917a3b615b43310a2e90eeb7c0e23f20bb9be07ffef059fad058d650494ee044d7d030ac102a95d0088bc
 | 6 => 0xff921aff429bff1ec3fe99edfe731efe60c4fd7e62fcfa53fc975afc76f8fbda5dfbd267fb79c4fb0f73fae8f2fa95f1fa7327fa6a04fa20aaf8dd7df8b84af883aff85980f6637ff60b33f5d96df5d325f510fbf4d304f466d0f3af26f3ad3bf34021f3142bf2f2b1f278dbf24e38f21fa3f19fd6f161b5f15a00f143bef10740f08397f079cbf0764ef04dc4effcbbef621bef1b9ceeb180ee03b6ed84d3eccd50ebf674eb90ffeb6e35e851f8e82f1de7fc42e6bfe5e6ad1ce51cbee40826e3cabce3c590e39385e2f171e2e78ae284d9e25916e23ba4e1819be1682ae08ecde08301dfc706ddc765dd7aefdd7974dd6670dc960adc4ef4da97c8da283ad96d21d82580d7bd32d7a4c3d7332cd634d5d5b3e5d59f96d4e844d49772d42f30d42cd4d42724d35696d1dc21d1dc20d12993d06a00cf4816cf1df9cf1b29cea411cde5a2ccc725cc9bd1cbfb36c8101ec804e0c804bac7dcf1c76d61c70d48c6ce61c64c5ac5c97cc52036c28a0fc28a0fc2258cc1ff1cc0b4a7bffebdbff254be05e5bd0f9fbc6353bc0c1cbba334badd1aba6d12ba587cba35b0b96a97b8afa3b8afa2b88d12b87624b7f302b7715ab704cfb6fea0b6c5aab62e13b5b9ceb5813bb5246eb34745b28cbbb27216b17ed8b1115fb08d69aef6fbace75eabd0c6ab3284ab166baafcd0aa9a68a99310a91809a7aa9da79e95a7968ea6c943a68ce5a61339a6086ba51b05a3a338a2fcada280e3a136e3a12a00a07e1fa00a869ff6239f2bea9eaee09ea5f29e9ec69e8c2c9d41db9d0cf09c97469c23ff9b8a7a9b498a9a8b8b99e48599aaa7998ffe98aacb988de8983b7a97c62a974d1e96a03795236d946c3794350693a7b3935b7f922c8991d23c9181bc9158ca90f93390ea3790dc5190abcd90977890912e9059489011798de23b8dc0d88d931c8d52948d336b8d2c018ca2bd8c72bc8c21b089ee3089ee2189a3ee89760987e21687a9b886b21e86ad428690de866cee862313860f3685dfe983bc6883576c83445f8318c982991381aa39818c558186348083e8807c858052227ef56f7ce7c57cad717b39aa7a956f7970347920ba78c0cf77dafe77373e76addd7616157545a474599e740e0673f68c73ed6173627673544772d5ef723db771c69771c2fc70ce5370a8ee709b7c705cf67023506fbff46fba696e57446e35e76ddf5f6c71c46bebe66ba17e6b755c6b5e006b24a06b11ad6a675869d62c697a7b6932c068bbff68771b67f10d67c5ca678772675d396539636407876397416123c3611ad8607ebd604c8a5e5dbb5e1ddb5d75195d30e45c3e4f5bdca75bc2985b4b3e5b3d865b20ef5b024c5ad49a5aa1b85a95ce5a5d705a08f559f7f859c47b58ffd65718ca567bee5638ca56265e556fce550706542d9f53c23e532bfb52416a522416507e50505932502fd4500d8f4fc3524d0ae24cceba4c1a9e4c117d4bdad94b88c54aeaae49f2d24995d948519b4672484602e7458d7744f13743b1f542779c421ecf4217b0412eab40c6d340a4cc4092f53faad13f732d3f4b993e99903dedeb3de6f93dcef83d9b0f3d485f3c7b4c3c1b023c04e83bfbfd3a2353390c1e373523371f4836771d364f6e35a36a35a2e635889734f567330e79322b4732041930fad5308dc13074d0306d6530475c2fdc5c2fc9f42fc9f22f27b22f1bb32e7ad22d48d02d1ac12c86472c6a652c162a2bb9672bb7192bb20c2b9d4b2a436129ef9e295dbd2954ac29424628f6b62879a6286f52285ee927db8926fd7d26b1fb2557e623b448237997236e4522939622653820c75b20947820679a2058c41ff9351fa9a01e33d41e320c1dbe6c1d2b1e1bb41d1a98ad1a3981191b5d18766617a73a15d3ed147beb136e90135c37132b4a1263a311e5b410e8951055640f6d470ebfb60e7e880e1de40bad9e0ad85a0acf0b0ab280097a310976cb08e5d508009507d11f0676060630db05d3c505c6db056ddf050d1b0454690439c504336603cd840363d903487402f1f202b5d2026bf7021a7101c6e5019d1901213f00da83009fae
 | 7 => 0xffd443ff848dfedc30fecf3ffe60c4fe162efdebd5fdda88fd6096fd4169fd0b5dfcd705fcd5ecfc520bfbfb0bfb65c5fb3bf5fb3bf5fad563fad093fab7cbfa8bd9fa6a04fa63c5fa07a2f9dad8f982f7f97680f95335f93ca1f92140f8ef20f86164f85a5df81674f7fea5f730fcf6e3bdf6d49af6b470f6464cf631fdf5ae99f5aa91f549ebf53e78f4c7b6f4af33f43e79f326baf30756f2c0a3f25346f230a8f1e616f1a2a0f192d9f0dbbdf072b1f06af8f04ac9ee5307ee2523edbc43ed5b1eed3195ed25dbecb85cebbce5ebb953eab659ea02d3e945b7e91acee8507ce76a02e736a0e71a2ee6eba2e5ac45e58339e57e63e55fefe53ed8e524dee4425ae42f1ee3d527e3b4cfe35d2fe30e98e2e5d1e2e1a2e25c87e24388e18c49e16677e0bc85e077f7e058f9e024c3de55a9ddc5b5dd6a67dca07adc917adc8c6fdc530ddb9871db596ddb3bbadafc41dad570da0e6fd9f816d9d070d9ae07d90d4bd90d4bd782afd6aae7d682bcd63d29d634d5d62cd9d6271ad5d339d58447d4dafad499c0d499bfd43c52d43aa2d414b5d3e204d3b820d3b113d38534d372a7d28722d1e5f5d1a14bd10a66d0ad2bd0a698cf7a2fcf2160cf1a0fcefc76cece90cdea33cd3365cd2ed2ccd398ccbe7dcb5f8aca9173ca43dcca40d3c9d133c9a4fdc994aac80174c7c827c7787cc66d4bc62bbac586ffc5661cc50b01c43c26c3dfffc39fa2c337a8c297b9c26495c18adcc12ddec038f9c00fadbfbdd1bfa32fbf77abbf1e43beb72fbe8a0ebe4c01be4c01be0c41bdfc91bd3c00bc9816bafe70bae798bab83ab9be22b98020b91577b8b681b893b1b8210ab81201b792abb776eeb741f1b5b0b6b5976fb546a0b52474b503a8b4de50b402a2b3fa82b3f8c1b3f432b3f386b3b742b314eab2b369b2732ab26d0cb1cf83b1aa87b16107b10f7db10694b0f4feb0991eb0032caf7acbaf60fdaf091aaed55cae976badeb10ad6e30ad6b1fad6ae8ad366bad0f4cacecffabec2babca07aab540aaad74a9bd90a7968ea786cfa782f2a7525ba74490a6c943a64eb7a63e2ea62f59a5efffa5e937a597fca4d719a49867a47f78a47e53a47819a3ee4da3a402a37d44a34111a2a7d9a29112a274efa219ada1ca37a0223b9ffcc29ff53a9f5e1c9f29329e53919e3ca69d9d3a9d326a9d2ce19d1bc89cbb199c16b19c03349b3d169b08c39ae5099a2a6d99dabb99270a98f732986eb997ced39731c696e4ab969cc695d384959ae1959ae195685595538494a9f793ee5a93e36e93464e92f6be92cb0192b03f92258791858c9171389141b7912a988f5fd78ef5328ecc458ea6f18dcdc48dc7bd8c3eee8beb478b87db8aaf338a93328a38a68a188d8a188c8a12358930908918d6888caa882fbd87fce987e05387dae287bb02878650876f6887021886c9da869bd2866cee860f3685f65085dfe9851e5084cc9a84c05d845f3384383684121e83ea6d8242aa82396f82215a81d47e8183a0817c0e8164758156e1806cea7fd4027fb13a7ecd1c7ebbf07e44737e402e7dbbed7d62957d196d7cd4127bfc5d7af6577a835c7a50dc7a0ade79703477a55b7717e376d3d87657a3761325760a6a74c0a474b9e074771473cec672e21c7284fd727f98706a9c7040ee6f56666eb7f36e1edb6d455d6cc84a6c44896bf0c96bcf246b2c736af7696af7696ac9846a4a156a1f0c69f3ea69b3db69aaa9697d20695623683ce068281368276167a3c96701e166926165d01c65851c64d0f864c5326406506397416347a4632d1b62ceae62bf50624b7262195e61cfbf61b1846042466024895f74905f4b935edffe5e5dfb5e52705e10325d21805c52685c2c3e5c04385b7c285b133e5a664d59f7f8590f0b58d7d758b6b058a50e56e7a3553353552da35499a3549186540cf2535f4152fe3752cdd45226ef5205a751b11c514b8a51154e506038502e034fb44e4ee8de4e58ea4df1ad4d05c94c9daa4c59e64c1a9e4bbba04bb7de4b79094b1e954aa3df4a2b9a4a21f44a122349b9f14968c24959bf48da7447e198477a624737cf46987f465e4a4612b845ec6245a50e456f7c456699454df84523e943f820431c2e4250c741bcc2417555415b7e4115b14092f5405804402ad63fd7883f729e3f2f873ef08f3e86ee3e4fc43e35163dfcd23dc54a3db88f3cf0e83c5b143c3a363c32303c2faf3bb39d3b30c73a82513989003985883928c938f06c38cd46383ced380a1f37ed7637d69837c04d36d51936be1b36915336909f35c54f35920b34d7e934b52e34800b345789340e4933997133267132d9c832a7e3328f0932432e31586130d190309bbd3095722fc5a92f9c432e54bb2e4bd02dda6a2d5aa52cdb312c3c702ba92f2b97332b1a712ac1172a78962a231b2a16fa29fd0029519d29466529151d2873fc280f90275f8d2698c126864e25bd3324f49e24284a2414cc23c82422c65f22bfab22be4b2259d922117022117021ec5c21b7a12115d420679a1ee9dd1ed4171e54181d84251d749c1d72631d302a1d30131d20211cfa221cf48b1cc9361c6b561c01e41bd44b1b1c8f1ae4a81a576f195484193b2118726e18521a17f33417e8e61768f016163015080514da5714456d13cae013bf7813745a13588712a10e12252212040811f7b811c33f11be17119ae1119844117dd8116f0c114afe11448310bf631094d6105f550fce860fa6620f7a150f00fe0e01c00de5440d4de60c975c0bf0eb0ba3400b07e90af6110ae1e70ac62b0a809d0a7a2b099d8209201a09201908fe9a08f73808c2a1085de30801e007e29407d78c0709d306cd5d069d07051d0604300303b4a103931402d0ed023249021a7101db3d01183000e6e5
 | 8 => 0xffc6e9ff5a38fee31efe6a24fe22a8fd1ee9fceabefa8295fa521cf8a5f6f84f0ef73786f6b470f3f7d1f3f3f5f3e146f3163ff2e077f0ee03f078b2ee6718ee499cec69dfec4a6bec3c5eebf6bceb7618ea5dd8e52614e40431e3c301e3b4cfe36a0ee155dde14994e13aabe0bc85e0297ede377ede0e16de0494ddeb5fdd3f0fdbf72bdbd3c2db6782db0d36da263dd9e8f7d94e2fd90d4bd89c39d74aa9d62cd9d5a1bed499c0d4352fd23122d1c776cefe55cefc76ce4cc7cc9972cbe878cbaca8cb319acb0ff3ca9173c8fa37c8554fc7c827c7c639c77a0dc5efe7c456d5c25815bf163bbef123bedb0dbe346cbdb46abc2edcbb9d43ba7c3db8cd44b893b1b7e1c0b78d52b4ced5b3f386af4bf6aed55caebabbae3953adff52ad6ae8ad0f4caab540a9b8cfa9ac9da80889a585d5a49867a366cda2fd13a22ec9a154f4a0ef8c9f87869f86079f29329e9e009cbb199c55f89be0a39bbcbd9b08c398c67a9731c696f520963f8295f27194ce81931f6e91848c8ef1cd8db2d68cbc988c7ae78a9b948a3bfd87be938776d687531086be19869bd285631a8544af8537d8850213839bf88344db8295938205e581afc17fb5a37f92f87f611d7cd4127c765d7b6f9e7aea7579408e78fa3f7645d875f56d7543d274004d73f9d772d1b972757870883870385a6fcf886f55796de3906dce026d444d6d35136c79ab6c31c46ab1196a38ec6958d768cc7d689ade67fbd46705d3667f46657b026384806347a4631c3c60e9e460e03b6024895de2925c35265c049c59841c58901a586b725861a957eebb56e1fb5620eb55bc2151c2a94eeb204ee9374e61bc4b5cf24a5bbc49811c49187748fb9b48cd6347c896477dc7469077468a1b45a50e4444f24093153dd3983d833a3d2a963c08423bd8ff3b37773aa6ac3a32823a31ed396992396985391bed37447b3584e3353a3c32f7c1322a333206263167c530d1903037852f5e1e2e477d2d15662bb1df2b693129c88229a7d829389b283a11280f90280a7927cf4927407a26e15826089824d55123ee83232b7522c65f227d16205e5a1f12fa1ed4171e39fa1db19d1daae01d7fa81d72b11cc0831c12841a03681947e818cbee17e8e615b53f14c240131a4d13154312bcdc11c70c11bbac11542c103d19101e120fbe000f7a150e8d7f0e44230cf5740c85880b2c280b07e90af6110a91240a809d09439408afad08ace907e29407ad5203e74301adcd011830
 | 9=>0xcefc76c456d5c2581581afc14eeb2049811c2e477d22c65f101e1207e294
 | _=>0
def rz : Nat := 0xddddddddddddddddfcfcccccfcfccccc0f0f0f0f0f0f0f0ff0f00000f0f00000afafafafafafafafaaaaaaaafffffffff0f0f0f0000000000f0f0f0fffffffffffff0000ffffffff0055005500550055fcccfcccfcccfccccccccc00cccccc00aaffaaffaaffaaffcccccccccccc0000ffff00ffffff00ff0000ffff0000fffff000f000f000f0000fff0fff0fff0fff5555555555555555ccccccccffffffff00000000aa00aa008888888888880000000000000000aaaa0fff0fffffffffffc0c0c0c0ffffffff0000000000aa00aaeeccaa00eeccaa0000c000c000c000c0cccccccc0000000000000000ccccccccaaaaa8a8aaaaa8a8dfdfdfdfdfdfdfdf8f8f8f8f8f8f8f8feca0eca0eca0eca0fcf0fcf0fcf0fcf0f5f5f5f5f5f5f5f5aaaaaa00aaaaaa00ccccc000ccccc000c8c88888c8c88888ffccf0c0ffccf0c0ffffccffffffccffddffddffddffddffeeeaeeeaeeeaeeeafffffffff8f8f8f8eeeecccceeeecccc0f0fffffffffffffeeaaeeaaeeaaeeaa0000000000cc00cca8a80000a8a80000cccc0000c0c00000aa008800aa008800000000000a0a0a0affffffff55555555feeefeeefeeefeee000000005f5f5f5fffaacc88ffaacc8800ff00ff55ff55fffefeeeeefefeeeeeffff0000aaaa0000eeeeeeeeffffffffcfcfcfcfcfcfcfcfaaaa8888aaaa0000ffaaff00ff00ff00aa00aa00aaaaaaaa00000000ffffaaaa888088808880888000000000000000ff0000000055ff55ffcceecceecceecceeffccff00ff00ff00cccc000000000000aaaa0000aa00000000000000000f000fffc0ff00ffc0ff00c0ccc0ccc0ccc0cc88ff88ff88ff88fffffffffffcfcfcfcaaffaaffffffffffaaaaaaaa0000000000ff0000ffff0000cccc8888cccc0000aa00aa00ffffffffccc0cc00ccc0cc0000aa00aaaaaaaaaaeaeac0c0eaeac0c000000000c0c0c0c0eeeee0e0eeeee0e0ffffffff0000aaaaaaaaaaaaaaaa0000000000000f0f0f0fffff00ff00ff00ffffeaffeaffeaffeaaaaa00008888000000cc00ccccccccccffff0000ffffaaaa88000000880000000055005555555555fcfcf0f0fcfcf0f0cccc8080cccc8080ccccc0c0cccc0000ffffffffffcccccccccc8800cccc880055ff55ff55ff55fffcfcfcfcffffffffffffffeeffffffeeff00ff0000000000ffffffffaa000000c0c0c000c0c0c0000000000000005555c080c080c080c080ccc00000ccc0000088888888aaaaaaaaffffffff0f0f0f0fffffffffc0c00000c0c00000c0c00000ff0fff0fff0fff0faaaa8800aaaa8800eeffeeffeeffeeffa8a88888a8a88888ececa0a0ececa0a0fffff0c0fffff0c0fffafffafffafffaccffccffccffccff00ff00ff00ffffff00000000ff000000ffffececffffecec8888000000000000c8c80000c8c8000000000000ff00ff00c0c0000000000000eeeeececeeeeecec88888888ffffffffff55ff55ff55ff55fff00000fff00000ff00ff00ffffffffccffccffffffffff00ff000000ff0000cfffcfffcfffcfff8888808088888080a800a800a800a8000000000000ffffffcc00cc00cc00cc00aaaaaa00aaaa00000000000055555555f8f0f8f0f8f0f8f0ffaaffaaaaaaaaaacc880000cc8800003fff3fff3fff3fffaa88aa00aa88aa00c0c0c0c0c0c00000cccccc00cccc0000efefefefefefefefeeeeaaaaeeeeaaaaffffffffffffeeeef1f1f1f1f1f1f1f1ffccff00ffccff00fcfc0000fcfc0000fefefefefefefefeeecceecceecceeccfff0fff0f0f0f0f0aaaa0000aaaaaaaa000000ffffffffff0000000000ff00ff00aa00aa00aa00aafafaf0f0f0f0f0f0aaaa00000000000000000000ffffff00ff88ff00ff88ff0055ff55ffffffffff8080000080800000800080008000800044cc44cc44cc44cc0000ffffffffffff0000000000550055fffffffcfffffffcff00f000ff00f0000088008800880088ff008800ff008800aa880000aa880000fffffffffafafafaffffffff88880000ff00cc00ff00cc008800880088008800ffaaff00ffaaff00a888a888a888a8888888880088888800ffffffffcc00cc00eee0eee0eee0eee0ccc8ccc8ccc8ccc8aaaa0000aaaa0000c0ffc0ffc0ffc0ffffffffffffccffcc8080808080808080f8f8f0f0f8f8f0f08888000088880000ffffffff0000ffffcc88cc00cc88cc00fffffffffffff0f0000000008888888800ff00ffffffffffcccc0000cccc0000c0c08080c0c08080c888c888c888c88800000000aaaaaaaaffffffff88008800000000000000ccccffffff00aaaaaa00ffccccccff888888faf8f8f8faf8f8f8ffffffffaa888888ffeeffeeffeeffeeaaa0aaa0aaa0aaa0fcfca8a8fcfca8a8ffeeaaaaffeeaaaaffffaa00aa00aa00f0a0f0a0f0a0f0a0ffffffffeeeeeeee00000000ffff0000ccc0ccc0ccc0ccc0ffccffccffccccccaa88aa88aa888888fffffafafffffafaccccc8c8ccccc8c8ffaa0000ffaa0000ff00ff00ff000000fff0f8f0fff0f8f0ffffffffcccc0000ffc80000ffc80000ffff0000ffaa0000ffff0000ff880000fca8fca8fca8fca800fc00fc00fc00fcffffffaaffffffaaffeeccccffeeccccffffffffffffccccffffffff00ff00ffc8c8c0c0c8c8c0c0ffecffecffecffecffffa8a8ffffa8a8ff000000ff00000000000000fffffffffffffffafffffffaffffff0088888800ffffffffaaaa0000ffffffffff880000ffffffffff008800ffccccccffc0c0c0ffff0000fff00000ffffffffffeeeeeeffc0ffc0ffc0ffc0eeeeeaeaeeeeeaea00ff000000000000fdfdfdfdfdfdfdfdff88ff88ff888888ff88f888ff88f888fffffcfcfffffcfcffff0000f0f00000fefcfefcfefcfefccc888888cc888888fff0aaa0fff0aaa0ffffaa00ffffaa00aaaaaa88aaaaaa88fcfcececfcfcececcc88cc88cc88cc88ffffffffa0a0a0a0ffffa0a0ffffa0a0fffffffffffffafafffffff0fffffff0ffffffffff888888ffffffffa8a8a8a8ccccc0c0ccccc0c0aaaa8888aaaa8888ffffffffffc8ffc8ffa0a0a0ffa0a0a0ffffcc00cc00cc00ffffccccffffcccc00cc00cc00cc00ccfaf8faf8faf8faf8ffffffc8ffffffc8fcecfcecfcecfcecffffaa88ffffaa88fffffffff0f0f0f0ffccccccffccccccaa888888aa888888ffffffffccccccccfffff0f0fffff0f0ffffc0c0ffffc0c0fffcfffcfffcfffcffaaffaaffaaffaa000000000000ffffccfcccfcccfcccfc00ff00ff00ff00ffff880000ff880000fffff0f0f8f8f0f0fff8fff8fff8fff8fffceeecfffceeecececececececececffffffffff88aa88ffa00000ffa00000ffcc0000ffcc0000ffffffffffc80000ffccffc0ffc0ffc0ffffff00aa00aa00cccc8888cccc8888eae0eae0eae0eae0ffffffffff00c800fff8faf8fff8faf8ffccaa88ffccaa88ffeeeeeeffeeeeeeccc8c0c0ccc8c0c0ffeaaaaaffeaaaaafff0fff0fff0f0f0ccc0ccc0ccc0c0c0faf0faf0faf0faf0eeeaeaeaeeeaeaeafff8f8f8fff8f8f8ffffffc0c0c0c0c0fffffcfcfffcfcfcfffffff0fff0fff0fffffff0f0f0f0f0ffe8ffe8ffe8ffe8e8e8e8e8e8e8e8e8ffff0000c8c80000fffcfefcfffcfefcffecececffecececfffffff0fff0f0f0ffff000088880000ccc0c0c0ccc0c0c0ffffffffaaaaaaaaffffaaaaffffaaaaffffeeeeffffeeeeccccc0c0ccc0c0c0fffff0f0f0f0f0f0ffa80000ffa80000ffaaffaaffaaaaaafffff0f0fff0f0f0ffffffffffa80000ffffffffaaa8aaa8ffe00000ffe00000ffffff00ffffaa00ffcceeccffcceeccffffff00c8c8c800eeeeeeeeeeeeeeeef0e0e0e0f0e0e0e0ffffffffff00ff00ffffffffffffaaaaffff8888ffff8888ffffffff88888888ffffff88ff88ff88fff0fff0fff0faf0ffccffccffcceeccffff0000ffc80000ffa8ffa8ffa8ffa8cccc8888cc888888ffffffffc0c0c0c0ffffffccffffffccffffffffaa00aa00fff0f0f0fff0f0f0ffffffffffe0ffe0ffffff88ffffff88ffffaaaaaaaaaaaaffffc8c8ffffc8c8ffffffffff88ff88c8c0c8c0c8c0c8c0ffffffffff00aa00fff0faf0fff0faf0ffffc0c0c0c0c0c0ffffff00ff88ff00f8f8f8f8f8f8f8f8aa88aa88aa88aa88ffeaeaeaffeaeaeaffffff00ffffff00ffc0c0c0ffc0c0c0ffffe0e0ffffe0e0ffffccccffccccccffffaaaaffaaaaaaaaaa8888aa888888ffccffccffccffccfffcfcfcfffcfcfcffffffccccccccccffffffffff000000fff8f0f0fff8f0f0ffffffffaaa0aaa0ffffff00ff000000aa00aa00aa00aa00ffffffe0ffffffe0ffffffffc8c8c8c8fff0fff0fff0fff0ffc8ffc8ffc8ffc8ff88ff88ff88ff88aaa8aaa8aaa8aaa8ffffffffffff8888ffffffffffffaa00ffa8a8a8ffa8a8a8ffff0000ff000000ffe0e0e0ffe0e0e0eac0eac0eac0eac0a8a8a8a8a8a8a8a8ffffffffffa00000ffa0ffa0ffa0ffa0fafafafafafafafaffffff0000000000ff888888ff888888ffffffffffaaaaaaffffffffffc8c8c8ffaaaaaaffaaaaaae0e0e0e0e0e0e0e08888888888888888ffffff00ffff0000ffff888888888888ffffffaaffffaaaaffffffffaa88aa88ffff000000000000ffffffffffff0000ffffffc8ffc8ffc8ffffffaaaaaaaaaaffffff00ff00ff00fcfcfcfcfcfcfcfcc0c0c0c0c0c0c0c0ffffe0e0e0e0e0e0ff00ff00ff00ff00ffffffffffffc8c8ffffff00ffc8ff00c8c8c8c8c8c8c8c8ffffffff00000000eaeaeaeaeaeaeaeaffffffaaffaaaaaaf0f0f0f0f0f0f0f0fffffff0fff0faf0ffffff00ff00aa00ffffffffffffe0e0ffff0000e0e00000ffe0ffe0ffe0ffe0ffffffffe0e0e0e0ffffffe0ffe0ffe0ffff0000ffff0000ccccccccccccccccaaaaaaaaaaaaaaaa
def gv:Nat->Nat
 | 4=>49
 | 5=>58
 | 6=>67
 | 7=>76
 | 8=>76
 | 9=>67
 | _=>0
def Df7C:Nat->Nat
 | 4=>0x2c150105026a0004820020040002c100a00a034060206005408030100400a180b8281c0050384822010028401e0a0700140e190280400a070301402005
 | 5 => 0x68547c0a009518002d0a828020051c930220a070018000d01044522850c05414010007981a024704426006198ac220a0700181a0228044be44636854d814050058301918114020060680840112f07981a661f844003d60003404110f91143a150517c02006068545645008018961d18028020060003404050f91147202088501c006020d00411008018720208850260060c99c220a0087980e0d01014020060693404321e04d85c6f1802802006068084c8b070018ba1d08914020063c808220a0080181a460111402006068080a2a008018722b088502600644808620a0700181a0228044181e61c8082214370018000d01154262f50c054145f0080181a2b190f0260060c0ac220a07001848230882802006001900411098bd408020298c020063b05804110087981a150111402006138084c010980187202089141c00624908d60a0080181a02208440028606808a0113d87981a02280c02600606855040a008018da1536028021e6020d08011008018000d010c0262f50c0ac2214098018000420044001e536854d80a0084d81a77010f0260060e870220a0080181a781584426006000d8cc110080142073088281c00606808e2110980181a12010140200606808e411098018000d01098180e5369a4d8110087981a401504402006000882a3e050054081201044020061c8ac220a07001872020884c002862d164b60a008018720213094020062e874600a008018a652010c878006068ac22140980183a150a02802006068085411000798000d011d4e8005001900455050054300d0101418016068fc7c11050f58005c0a8280200500010803c088014000d01160ae005001743a7c0080141a0224044be1e606808fe310503981a02338c014016038100405008018004921120020050c1cc220a07001872020887c001e606854400a008798000d21120c20050200832050080185c4605004001e60680840110f87980033010981c005068087030098018304605004001e61c808220a060798b4460111402006068090211051118003605004003551705414010007981a0220898020060680886110507981a4e100c01401619a400411070018000d010c41c2f51c8084c01098018ec3a01044001e60680870304000181a02190f0401360c17484450080180037010984a015000602a7c008014300420044020060006804110f911400151b0280200546008220a008018005d310280200503810801100801834150102802006069080405060058000401014001e52d164040a0080183a1505004001e60006c2a0a00801472022a8280200606908403005005800493102802005068ac620a0700183019188281c00630008220a0700186656088281c0060014404110f8794000d01044262f5069340431050398da1536028be016138084c250080181a47010c87800617064600a008018000d01014180e50b054040a0087981a6615a20020060680858110980181a400298c020060012484200500541a34010141801606808fc3c3e80181a02450443e4460021c560a00801400220a880140151d05804110507981a2b088281c006000cc043218801400620a828020051c808620a07001872021d844260062e8100405008018b41501114020060e864600a0080181a02418c002006020080c0500801872021d844dc006000340411070bd4083401014020062781004050080185c1c088280200606808f411370018000d01044942f50685c040a0700181a02190f082006000340411428794720208a342600632808aa0a0080181a022a9a0260060003404050607941a56088281c0061b04414010007981a5901114020061c808643c0980184202088281c0060003404750700141a021c0c41c006069987e11350018482008828021e606808a0303700183019190f0260062496c220a0080181a56188281c00642130220a0700181a0f010281c00624908140143001800701b044020050001004110f9114000d010c03e445069a40431070018660f010281c0060b054040a0084d81a021009802136000cc048f18801400510104426285
 | 6 => 0x53010c92a0100303404a408804260070003480020280400c5c06808789505005c001a4e8441401003034042008828021e7000cc04320880400c2e2d008224500801c000d010455e13003169200208804001e74c9b42a020500400e0069854040a008018000d011548a010031746602088281c0071c808a011008003ce0d011c8220a00801c000d010c878a70030001a020885026006068093630050003ce392d844140100079cb4cd010441401003834043808804001e7068084030050043ce3901044280a00801c000d01044284a0030015a0213004260065480846110500400e000c055440a00801800000e8541401002835a01105004001e75496804110500400ec101044140100079c000d010e0600100303484021802802007068089011008003ce0d011f8220100079c000d01044280c0f30e40411050042600717168b6110500400e390126c220a00079c005a010443e000f30348402190f0260070680840110504c3ce180c844140100079c1a3f1584414001eb8001a02190f01c0060687404300500400e0d0126c401105269c1a98010c8220e00383404304891402007369a4043c0880400e390104414016d801c32116a82802000f38340419188281c0070003404bc0503002c0d1f808220a00079c009c4c808643c0030001a024984c009261c808600a008003ce0054808220a008018000d010144a0100314d30021904402007000340411500045ec182e908140100079c000d010c0140117b034048110044141e706808e6110503800e182d008224500801c000d010c4280e00300000042004402005000602a0a0080124c00540082213000a181a022804426000f383404e008828021e7000340413002499cc000680822130033985c190882802000f383404b70882802007000e42a020500400c5a0108c220a00801c302b0882802000f3925446c08828020070003404551280400c000680860a0008018722b0882802000f3800b44601028020060003404110607c3cc2e2e808220a00801c660239844140e003835200208804001e70003404110a03800c9c06a60041107001c000d010ec226e003000da150102802006001743a0a008006ac000c054320a0080181a0245044140e0038e4041105004002871cb7404110500400e000c1082a0a008018005d2107414010030601a02188281c007528cc04110503800e002d008220a060798005a01044281300300030a30882802006000e42a2b0500400c0028808220a070018b45b0e0441401003834046708828021e7001b42a2b0500400c0d011f8225f00801c000d011406001003034b63011828020070003404300517c88c0d1f8ac220a00079c000d01080600a00b0343a11050054e00706854040a008003ce0d21008224507001c720228044026e0038001a02089f0be1e60014404110517c3cc0d0ab18140100079c1ac401044140e0038601a02088281c007068090211050003ce0d15844140109801c000d0ab581401003000a6025e028020062d07004110500400e0006808221f070018005101044281300300030df0882802006000e404112280400c3901080220a00879c000d010ec221300300030150882802006001682a020500400c00068540450008018720208828be01003974da5b08828020070c03404321e04c00e0065054040a008018300d010c08a0100380030154a828020060e864220a008003ce000005414010025141a02590440213003834049b08914001e70012404110500400c0d158c8780a00801c965a010c014010038342a2b05004001e700054482b0500400c0006808229e098018000d010c8780c09b12cb40208914020070003404110517c88c0d01358220a07001c1a0228044be000f3834049b08828004470003404320883800c24010441401002c1c005d36908d80a00b034d8024b044260070680832302280400e00068082245538018003301044140e0030e4041105004001e706808a03c089b800e00068084c010980180033010448a0e003174b40208914020070003404110503142c000680822140624981a42118441401003834048108828009a71c808220a008014ce0006808220e000a181a025f84414010038e4043b0882802007259b404110500400e0d01141361137001cba0d210088a01003834563c4a828020072d118040a008003ce180c844140100299c000d010c0140e003000b85d21028020060680890110084c00e1819808220a07001c00534b8441401003034047a08804001e70680970110500400e000680864950600587202190f014010038001a0208a4c260060003404110523488c000680864310700180033010c8220e00300150c70882802006369b03211050043ce5a010c1220a00801c1a021322c4a010038001a0202894be0160c17404112280400e0d010c8788a09801c000d01044140c0f3175500208828020072d13804110500400e0006808221f1a87981a024d845ca004d3834b65008804001e70001004110f8003cc0d010c9361109801c1a022826c22004d38e404500880426007000342a0a00801b8c00068082245008bd8da0d36008600a00b800340208a80020060680890112f80400e00068080a01098018725a01044140100380034021802802006000340431050301cc3a0b008220a00801c000d01014180100309004110500400a672d054040a008003ce5c2d008220a00801c00ad010451a13003001805b0882802006002b558111280400c00568084c25008018000d010459e130030e4042308828020070003404321e04c00c0006808aa0a0080181a022804402000f3800305d2102802006069b004324a80426e182d16c220a00801c1a9f01044140e003800660218828020060680914110517c88e00020086411008018da15010f014010038348402088281c0072d1a40411008003ce1837844140100079c1a024d880220a0f38340450089b8001e700034041109b883cc000b054040a0080181a421004414010f3968042008828021e7068093611050003ce0d01080224500879c006401044140117b000006d0a9b014015068088211050003ce0d21008620a07001c005d7380814010030001a02190f01800606b3404110503800e0019808620a070018001d0a8441401003174b4021802802007068087030008003ce00068084c8d0980181a02388441401003834044108828020070003404116f03800c00068086014098018203301044140e003974340208828020072d340220a008003ce002e874220a0080181aa2010c878130038b8de1105004001e75e8e404110500400e0d0a8ac145f00801c1a9f010c4140e003835b002190441c007000340411050045ec0d2d88c220a00801c000d011404c010030e4041105004dc0070003404c80884c00c5a15844140100079c1a02280c002000f3800b402089141c006068084c8b0084c00e0d21208220a00801c1a3e1584414010f38015aac08804260060003404110980050c1806808221407001c1a97010c878130038e40411050055c007068ac220a008003ce0006808228500801800392114022010030001a151582802006069985611008003ce0d0a808145f00801c1a690104402000f38001a0208ae426006000e404300500400c00298086411008018b44d0104414010f3800a60208850260060006804110517c88c0006808227c008bd81a660104402000f3834a402190f0260070680860230500400e0d01238220a00801c1a021c0c0140100386032321e02802007120458c0a008003ce0d01348220a07001c1a98010c8220117b8001a4601028020060003404310503800c000c0441401002e981a2b0882802001eb83404cc08828001e70003404960884c00c000014c04321e001586020882802000f38001a1534808020060003404050f8003ccc02d844140100079c00c20a80814010030e404500897c020071703404300500400e0006808643c060058000006808280c492834b69b08828009a71c808220a0080134ea901044140100079c72024084414010038e4561105004260071c808220a098003ce0d0108c220a00801c00495884414010031b41a6c012f01401706aa804110503800e00068091e30098018b44e2d8441401003834843048828020070003404114684c00c0006808220a5d8798000d0104414db17b034042008828be1e706808a0300500400e0006808fc3c00801800510104414011431d8740208828020070003404115a12800c5a01064600a00801c1a5201044145f223aac1a02088281c007000342a020500400c0d0126c600a00269c000d01044f80e003174da021e254140170001004050880400c0d1f008220a00879c302b0882802130038001a02478441c0062d008a011008003ce00068086495070019c8024d84414004d380150022a828020060003404964a84c00c0006854cc2b0080181a4e010c08a01003834046108828001e706918040a008003ce000680822146480181a1d0882802005338340419190f026007069b004321e04c00e0060808600a008018000d010984a8d0030001a020884c6a28606ad804960884c00e0006808221f0007981a022a9a014010038003015050040035606808a020088043ce000000822140631541a0228044f6010038348402181140200700034041122b5c00c0006854047c00801800510a8081401003000084001044020061c80878950500400e39010448a0100079c1a5b6a04402000f3800664c08828020061990804110503800e0d01141361109801c305d21028be01003b00041105004001e7000001a020283002a000680862450700180051010448a010030e4043008828020070003404261297c02c000680822b4098018000d01258220e003000301515828020062d008de300500400e0d26808220a00879c1a4c010c8220e003834b63048828020073685544020500400e180c8f12a0a00801c000d010444a0117b0e40411052340200706809b411050003ce00068086411060798ba1d0882802000f38001a025e050260060003404310503002c0d0c880220a00879c720271844140100380000180a8280200506af8220a008003ce5a0126c220a00079cb44e010c014010038001a0208914181e60696c4011050043ce0d01398220a00801c7202088280286003834045008830020071c80936110500134e0006808aa0a008bd8000d010984a01003304043005004001e70003404115003800c00068082214370018000d010c860130030e5446c08828020070003404117084c00c00658602a0a008018000d010c08a0e003000da1536028020060014c04321e04c00c0d68844140100079c1a02100c01401003800301536028020060803404110503800e1806808224507001c1a77010f01401003800721d08828020060696d3611050003ce2e2d008600a00801c1aa20125822130038001a97010c878006000cc98110503800c0d01141361100079c1a026a04402000f3834d2021e25402007000342a8a0500400c3901044140159801c1a025a844140e00383456110500400a670003404300529c00c0d21008221407001c1a1501028020053383404da0882800d97000342a660100400c00540082214098018000d0123c620e003000725b08828020060699856110084c00e0006808140c492858000d010448a0e003000000401014020050680862d20503800e0d0e844140143001c003301044280e0030e404110517c001e7
 | 7 => 0x2b5440208828020074e264041105004015c806808643c4502802008000340411054b00200700034042008828021e70003404117a004001e7000340411050059200700000660208828020060003404110557c020074e1b544020882802008001b5e4020882802007000340411050046b12700034041105005ae0070003404321e0940200700000720208828020060003404e3050040092700034054c050040135700034041105006ceea70003404110558402007000340411050063e007000342a020500400927000001a4d0102802926000001a020885026006000369a02088280200700170ba020882802007000342aa201028020070003404950882802ea7000e4041105005da007000e4049b08828020070016804110517c0200700060720208828020070680860c605004001e80003404324a804260070003404bc05005da00700034041105004010d706808609105004001e82d008de1105004001e800068043c088280200700144041105004009270003404110500400ee7000340495088502600706a8804321e02802008000340411055ac009270003404110517c001e7000002a020500400c5678034043c088280200800034040a2f80124a170003404110a029b6007000001a023e0040092606808323c4a8280200800034050e05004001e700034041105006ca007000342a020c828020074e26404950882802008003a404110500400ff7000340411050040175700034043005005da007000340411c900426007000001b5b01028020060003404110a3b426007000340411050006b0a70003404118d97c020070003404500897c02007069b0049508828021e80034cda0208828020070003404110517e501e7000340411be028020070003404110517c1c007001741a027f028020070003404500880400f87000012e110500400c56000e4da020882802007001758402088280200700034049b08828009a70680823000500400a682e83484020517c02008000340411050066c007000001a0205004016a6000007242010280200600034041105004019c70014c04110500400357000340411228041c00700034041105650020070000056110500400c5606ad8049608828020080003404110500720007002658402088280200700034049508829f200700034049b0882802007000343a110500400c5700168041122804001e7002b4043c0882802007000340411050029f0a70006032110500400c5700144041105004001e70003404110500401217000340411050071e0070003404110500400a670000864111280400c57000340411128040028700034041105004013a7000340411050040028700168d80208828020072d108041105004001e800034041105004dc00700144041105004014f706808a09b088280200800034041105004004470003404113e004940070003404110a04c001e700034053c1e028020070003404c80882802007000e404110500400c5700034041105005e200700034041105005d600700034046108828020070680af61105004001e8000340411050054e007000340411aa004260070016804110500400ff74c9b4d802088280200800000041105004017260003404110523402007000001a02088501c006000340411050042600700168043005004001e70003404110a4642600700034045008804dc0070c03404110500400a6800034041105005b6007000340411c98042600700034220a00801dd667000340411055c4020070014c041105005da007000340432180280200700034041105474021e70680822c60504c001e800000041105004017f617034041105004001e80003404110545c00ff700034041105006a4007000340411055e802007000354402088281c0070003404110a17c2600706808a01105004001e8000340411054b80200700174041105004012670003404110504c00a1700034041105004003570c17404110a02802008000342a0215828020070014404113e0040035706ad8049508828020080003404328d0280200706808de1105004001e80003404110517c00a17001741a42010280200700034057005006de0070051004110500686007000e4d8020882802007000340411050040183700000a60208828020060012cb402088280200700034041105004014f7001680411050040035706908043c4a828020084e264043c08828020080014c04950882802007000001a021882802006000001a0218114020060003404110500646007002a004110a02802007000342a02050040035706808649b08828020080000005240882802c56000360e0208828020070003404300500400f3700174b40208828020072e968041105004001e800034043c180280200700034041105038003570003404500880426007000340411228281c0070003404110550002007000353002190f00200700034041105038009270003404110500708007000340411050064000700000041105004011460003530021925402007000001a0208829ae006000340411228040028736834049b088280200800270b402088280200700034049598828020070003404110529c001e700034041105004018570016804110a02802007069b0043c4a82802008002713202088280200700000b402089140200606908041105005b6008000000411050073a00600034041192804001e7001747202088280200706a60043208805b60082e9b4043c08828020080003405240882802ee700034041105004010b7000348402050040135700034041105004019e70003404112280400ff70003404114f028020070000004bc0500400c5606d3404110517c0200800034d60208828020070003404964a82802007069b004320880426008000340411a6028036270003404110545c004470680936950882802008002b404110517c0200700034041105030020070003432110500400dc7002a00411050040028700034041105005dd627000340411050068e00700034043005004001e7000340411052b826007000340432088054e00706a60043c4a82802008002b40411052340200700034041105004011370003404bc05004260070003404110500401097000001a0205005ee006000343a110500400ee70003404110a02802007000887202088280200700000b402088280200600034041112828be1e70003404118c050260070003530021802802007000340411050068600700034041105005c41e70000162110500400c56000006602088281c0060003404110500400f570003404117a00400f372e264da0208828020080000034020882802006000e4041105004001e700060b40208828020070003404110a004260070000004113e00400c5606808321105004001e80003670020882802007000340411054f8020070696c230405004001e8000340411050040110700034056c0500686007000340411053e80200700034041105478020070016804110517c001e70003404112280400f87000340411053b41c007003a4041105004001e70003404321e029b6007000001a02050300292625968041105004001e800174da42010280200700409320208828020070001004110517c0200706874041105004001e800271f6020882802007000340411050a40200700060ba0208828020070003404e3088295c00700034d6020500400927069ac049508828020080016804110500426007000340432088042600706808461105004001e800034043c4a82802007000340431128281c00700034043c0885026007000348415010280200700168041105004001e7000340411050301c00700264b4020882802007000340411050040146700002bc02088280200600034043005004003570003404110563002007000349802088281c0070003404110500400ff700034043c7f028020070690804110500400a680690804110517c0200800034041105004010370003404110500400fc70003404050517c0200700060321105004015d700270da02190440200700000b45b08828020062e9b544020882802008000340411050040182700000b4021802802006000340411056580200706809ac1105004001e8002713298010440200700060a202088280200706809221105004001e8000000411050040129600174a202088280200700034041112829ae0070000004112280400c560003404300a028020070c034043c4a828020082d00822c605004001e800034041105004015970052c0411050040035700034049508828024472ea64da020882802008000340432a102802007000356c020885026007000001a02280040092600060321105004009270003404110a04c009270016804110504c001e700034042605234020070003404113e17c0200700009c6110500400c57000340411a70280200700034040a0980124a17000342a020500400f8706908d811050050c00800034041105004017470003404260517c02007000001a020a04c009260003404300882802007000009a020882802c560003404110500401917000001a02190f02600600034045008804001e700060ba42010280200700000305d21028020060014c0411050040092700034041105004016e7000340411050040139700035b002088281c0070003404324a8940200700034041105004017870016804110500400f57003ecda02088280200706aa8041105004001e806a6004320880426008000cc0411050041c0070003404110517c6a1e706a88043c08828001e8000001a02088040195600034041105038001e70003404110524c02007000b4a202088280200700034041105004016d706a600432088054e0082d008321105004001e800034041105004012a70003404110500401147000340431088281c0070000004110a04c00c567803404110517c020080003404110517c020070003404110503a6c007000001a020882ad6006000340411050040197700034041188804011070000004300500400c5600034049b08828001e7000340495088281c00700034041105006d000706938041105004001e80003404110a04c00357000001a02088281c006000001a2b05004009260003404115782802007003d8da020882802007000342a024a8280200700168041105005da007000340411055e4001e70003404110500401a0700060ba420882802007000340411054a000a1700000b4020500400926000e4049508828020070003404110545c001e700034041105005f2007000001a0208829f20060040404110500400f3706b60043c088280200806b3404110517c0200800034041105004015670000072020500400926000340432128040092700174da0205004009274e035300208804001e800034b6110500400f370690822c605004001e800034041105664019870c03404321e0280200806808230605004001e80003404116782802007000340411050040115700034041105004018872e834840205004001e800034041105030029270000004110500401646000342a0205005da007000003019050040092606a8804320880426008000340482088280200700034043c088281c00765834041105004001e80003404110500400ef7000001a151582802006000340411050055c007005447202088280200700090041105004019170003404115a028020070003404119280400ff70003404113e00400ff700034234c05004016670003404110a0294e0070003404113e00426007000340411050050c0070003404110500400fd700034041105004013770000005160880400c560000032110500400946000340411050041c00700061e402088280200706a5c04950882802008000340481088280200700002ae110500400c56000e40411050040129700034041105005ee00700034041105004017670680832110500400a68000001a02188281c00606808230405004001e8000340411050040149706809361105004009a8001741a028d0280200700145621105004003570003404110500401277000340411129141c0071c80822c605004001e800034041105218260070680822d505004001e80003404110a04c00f8700000d2020880400c56000601a1105004012d700034041122804001e706a60043208804001e800034043022804001e706808401105004001e8000340411054cc020070003404320084c00927000340411052ec02007000001a0218028020060014c04110500426007000b8b402088280200700034041105004012270003404300500400ff70000004110503800c560c174041105004001e80003404230882802007001b7020208828020070003404321e044260070c17404110517c020080003404110a0041c00700168043008828020070003484110500400dc717168041105004001e8000cc0411128281c0074e1b4043c088280200800034041105624001e706908041105004001e800034053c088281c0070c03404110517c02008000340411050046a28700000a60205004009260003404112280400f3706a60043c088294e0080014404110500400ff7000353002088281c00700264da02088280200706809361105004001e8000340431050041c007000340411050066800706808230005004001e80003404110561c021e700034041122838001e7005a4da0208828020070694804321e0280200800034041105004019a72e034043c0882802008000340411a602801587000001a15010280200606a88049608828020080c034041105004001e8000340431088280200706809141105004001e80003404320884c001e7000340411c0028020070003404110500400ba700090041105004011470006032110500400f870000864110084c00c57000340411050069400700001500208828020060003404110503002f87000340411054ec00a17000340411050040173700034041105006c6007069b00461088280200878034041105004001e8000e404200882802007002b4041105004001e70003404110a0941c0070680832321e02802008001741a151582802007000345611050040092706b34041105004001e80c168041105004001e800034041105005d80070003404110536c001e700000a202050040092636834d80208828021e800034d2020880400f8700034041105004010870690804110500400b0800034058e08828020070003404200882802c57000001a0208828035560009004110500400c5700404041105004001e70003498020882802007002728a0208828020070696c0430088280200800000041105004010f60016804110500400f87000371a02088280200700034040a0080124ce700068041105004004470003404110a04c00c5700034048f18028020070680822c605004001e800034041105006900078e03404110517c020080003404110500566007000340411050040186700034561105004016e7001741a02978280200700168b6020882802007000340577050040110700264a20208828020070003405160880400ee700034041105004012b70000004500880400c5600034050e0500400f3700034055a088280200700174da0208828020070003404321e0042600700034043b0882802007000e532020882802007000340411050040141700034041105004013f7003a4041105004003574e264d802088280200806a60043c0882802008000003a110500400c56000e404110500400927001440411050042600700035440208850260070003422c605004012d70003404110500401607000342a020500400c570680a601105004001e8000001a0205004009260000004200882802c560003404110500400b070003404110500401a172eb74da0208828020087b174da02088280200800034041105004019f74c9b4049508828020082e83404110500400a6800000005d0e828020050003404115c8280200700034041105004001e706cf4043c0882802008001741a421582802007000e40411050040035700034041105006a60070003404bc4a8280200700034040a498040092700034041105004017d700168b61105004001e700034d8021e2541401700175a60208828020070003404da08828020070003404110517d5c0070003404110562c02007068096a1105004001e8000345611050040113700034041105004009a7069b004321e02802008000340411050049400706808a0110517c020080027132021904402007000001a0205038009260003404321e028020070003404110500400ce70003404110504c001e7001759402088280200700034041105001dd587001b4b402088280200700034051a4a8280200700000b6110500400c560003404113e004001e706a6004320897c0200806a88043c088280044800168049508828020070003404bc05004003570003404110566c02007000340420088280292700034041112829f200700034043c088294e00700628b402088280200700034057e0882802007000e5440208828020070003404110a0281c00700061f6020882802007000001a690100400926001ac04110500400c5706a600430088280200800034041105004010c7000e404110500400f870003404110500400f370014404110517c02007000001a02055ac009260014404110a028020070003404300500400f870690804321e028020080003404110500400e8706a88043c0882800a680003404110500400ea70003404e3088280200700174054c0500400c57000001a022280400926000340411054ec020074c835440208828001e80696c22c605004001e800034049608829b600700034d602088290c0070003404960882802007000340411708280200700034043005004004470016804110500400f3700034b60218028020070000004110500400c5600264a602088280200700060321105004009470003456110500400f8700271a602088280200700034041105006a00070000004110503002c560003404110517d0c007000001a02100280292600034043048828020070003404110500401057000001a02089141c006000000411050040132600144041105004003570003404110503002c57
 | 8 => 0x8220a008003cc57006b404110500400c5706808220a00bb6860080696c041105004001e8069b004110500400c58000340411da028020070000832110500400c5706808220a00e6400c580003404110545c02007000374e02050040092700034040a2f8040092706808220a008006aff80003404110500400ee70680823180a0280200800034040a0084c0092700034040a00801f092706a614402088280200806808234c0500400c5806808220a00e6400f880010804110500400c5706808220a00ea40092806a8804110517c0200800034043c050040092706ad804110a028020080680864110517c0200806808220a008006a1e80003404110500401ac706808220a0080124a1806808220a2f80400f88000001a6c0882802f8606808220a0084c0092800034049b088280200706a60041105004001e8068092a110517c0200806808220a00bb400c580c03404110500400c580003404110500400a6700008220a0080366c5706808220a008018b35806808220ad9004001e800034040a00bb40092700008220a00802cec5706a8804110500400c580c03404110500400f880028804110500400c57068082214050040035800034043c08828020070003404118c0280200706a88041105004260084c83404110500400c58000340411050054e00706808220a2f805da00806808220ad100400c580003404110500426007000340411054740200700034041105005b600706808220a00801f0f3806808220a00ca000928068092a1105004001e800008220a008018b987000340411050040035700034041105004012670003404110561c0200700034040a9d804009270003404110500400a1700008220ad100400c5706808220a00e65da008001741a420102802007068092a11050055c00806a880495088280200800034041105004014f700000a20208828020060006004110500400c5706808220a008018aea8000340411050040092700034041105005da007000340411050040198700008220a00ca000c5706808781105004001e80680822250517c0200800008220a008018aea70003404110500400dc7000340411055e402007068092a110500400c58000356c020882802007002713202088280200706808220a008003cc58069ac04110517c0200806808220ad780401ae800034d602088280200706808220a0080124c58000340411050040113706808234c0500400ee806808220a00bb4001e800034040a008003c9270003404110a0280200700000b40208828020060003404110500686007068082214050040092806808220a8b804003580c0340411050075000806808220a008018b98800034041105004011070680832110500400f8806808643c088280200806808220ad2804001e800034040a00ca00092706a88041105004001e80003484020500400927069080411050040092800060ba020882802007000354402050040092700034043c4a8280200706808220a00801f01e8000601a020500400927000092a110500400c5700168041105004001e706808220a008034cc580003404110500400ff700008220a00bb400c5706808220a00801f0358069b0041105004009280003404110500754007000001a0205007469263683404110500400c5806809c695088280200800034040a0080124c570680822c60500400c5800034040a008006a9270c0340411050040092806808641105005da0080680a5e110500400c5800008220a008006ac57068092a11050042600806808220a00bb426008000340411050040191706808220a00ca000f88069080411050040191800034041105007520072e8340411050040113806808220a008006a92800034040a0080125127000340411056880200700008220a008018adc70003404110500400f8706809c6110517c0200806808220a00bb40092806808220a00801f0c580003404110517c0200706808221405004001e8068092a1105004003580003404110517c021e7068092a1105005da00806808220a00ca0001e806808222505005da00800034041105004012d74e034041105005da0080690804110500400f8806808220a00ca000c5806808220a00bb4003580680832110500400c5806808220a0080346c580003404110500746c5736834041105004012680680822c60500400928000340411050040135706948043c0882802008001b004110500400c5706808222505004001e800034d80205004009270000004110080366c5606808220a9d80400928000340411d58280200706808220a008006b4f806808220a008003cff8000340411050040112706808641105005b600806a600411050054e00800008220a00ec000c570000878110500400c5706808220a0080366c58000340411050055c007069b0043c088280200806808220a0084c00f880003404950500400357000340411050050c00706808220a2f804003580000822140500400c5700034040a00801252d700008220a2f80400c5700008220a00801f0c574e034041105004015c806808641105004001e8069b00411050050c00806a6004110517c02008000340411050040094706808220a00802cec580690804110500400c58000340495088280200700008220a008018b3570680878110500400f88000340411050075000700034041105004015d7000001a020882802006068083211050040092806a880411050040035800034040a0080124a1706808220a00bb400f8806908041105007540080003404110562402007068092a110a0280200800264da020882802007000001a0208828be1e606808221405005da00806808220a008006ac5806808220a00801f0928001b404110500400c5700034041105007620070000a5e110500400c5706808220a00802cef8806eb404110500400c58000340411050076000706808220a008003c9284c83404110500400f8800008234c0500400c5706808220ad280401a480000004110500746c560680822140517c020080680823180517c020080003404c6050040092706808220a00bb400f38000340411056d4020072e83404110500400f880680822c605004001e80680878110a0280200806808220a0084c00358000354402088280200706a8804110500400a68000340414050040092706a88043c088280200800008220a0080124c5706e9c04110500400928068087811050040035806a880411050040092806a60043c0882802008068092a11050040092806808789508828020080017404110500400c57000340495050040092706808220a008034692806808220a00801251280000822c60500400c5700008220a0084c00c57000001a0205004009262e83404110500400c5800008220a008034cc570003404110500401ae700034041105004001e70003404110500401a4700034040a008034692700000040a0080124c560680822140500400c580c034041105004009480026404110500400c570680822140500400f8800034041905004009270680878110500400c5806808220a00ec000c580003404321e028020070c034041105004015d806808220a008003cf3806808220a00801252d806808220a00ca000ff806808220a2f80400c5806ad9440208828020084e0354402088280200806808220a008018adc800034041105004015c70003404110500400c5706808220a0084c00c580003404110500400f37068087811050040092806a8804110a02802008068092a110500401ac8069ad4402088280200800034040a00ea4009270003404110500400ea70003404e3088280200706808220ad7805da008000340411054ec0200706808220a00801f110806808220a2f8040092800008220a0080346c570000004110500400c5600008220a00e6400c5706809c63c088280200800000220a008034cc560014404110500400357
 | 9=>0x1a020882802001ab8340411050040092706808220a00bb400e0d010441401003e1c1a024a84414010038001a02088280200606a8804110500400e000680814010024981a0208828020062b80004110500400c56
 | _=>0
def gx (x0:Nat):Nat:=
 zm (land (mul x0 0xff51afd7ed558ccd) l5) fun x1 =>
 zm (xor x1 (shiftRight x1 33)) fun x2 =>
 zm (land (mul x2 0xc4ceb9fe1a85ec53) l5) fun x3 =>
 land (xor x3 (shiftRight x3 33)) 0xFFFFFF
def ex (packed:Nat):Nat->J
 | 0=>[]
 | k+1 =>
  (land (shiftRight rz (mul 64 (land packed 511))) l5,0)::
  ex (shiftRight packed 9) k
def i2 (s j:Nat):J:=
 zm (shiftRight (Df7C s) (mul (gv s) j)) fun sl =>
 ex (shiftRight sl 4) (land sl 15)
def rq (v c0 c1 b c:Nat):Nat:=
 if beq v 0 then 0
 else
  lor
   (lor (if beq (land v 1) 0 then 0 else c0)
    (if beq (land v 2) 0 then 0 else c1))
   (lor (if beq (land v 4) 0 then 0 else b)
    (if beq (land v 8) 0 then 0 else c))
def n5:Nat->V->Nat
 | _,[]=>0
 | tt,(c0,c1,c2,c3)::rest =>
  lor (rq (land tt 15) c0 c1 c2 c3) (n5 (shiftRight tt 4) rest)
def t3 (b:Nat):Nat:=
 lor (n5 b n2) (shiftLeft (land b l5) c7.fH)
def hQ (s j:Nat):J:=
 (i2 s j).map fun p=>(t3 p.1,0)
def mg (w:Nat):Nat:=
 zm (sub w (land (shiftRight w 1) 0x5555555555555555)) fun w1 =>
 zm (add (land w1 0x3333333333333333) (land (shiftRight w1 2) 0x3333333333333333)) fun w2 =>
 zm (land (add w2 (shiftRight w2 4)) 0x0f0f0f0f0f0f0f0f) fun w3 =>
 land (shiftRight (mul w3 0x0101010101010101) 56) 63
def ah:Nat->Nat->Nat->J->Nat×Nat×Nat
 | b0,b1,b2,[]=>(b0,b1,b2)
 | b0,b1,b2,(w,_)::rest =>
  zm (land b0 w) fun c0=>zm (xor b0 w) fun b0' =>
  zm (land b1 c0) fun c1=>zm (xor b1 c0) fun b1' =>
  ah b0' b1' (xor b2 c1) rest
def mh (mA mB mC mD:Nat):Nat->J->Nat
 | acc,[]=>acc
 | acc,(w,_)::rest =>
  zm (land w ff) fun f =>
  zm (xor (xor (xor (xor (xor
   (shiftLeft (mg (land w mA)) 24)
   (shiftLeft (mg (land w mB)) 18))
   (shiftLeft (mg (land w mC)) 12))
   (shiftLeft (mg (land w mD)) 6))
   (mg w)) (xor f (shiftRight f 31))) fun key =>
  zm (shiftRight (mul (xor key 0x9e3779b9) 0xbf58476d1ce4e5b9) 32) fun term =>
  mh mA mB mC mD (add acc term) rest
def gk (ws:J):Nat:=
 let (b0,b1,b2):=ah 0 0 0 ws
 land (mh (xor b0 fk) (xor b1 fj) (xor (lor b0 b2) fh) (xor (xor b1 b2) fg) 0 ws) 0xFFFFFF
def gj (w:Nat):J->Q
 | []=>false
 | (a,_)::rest=>beq w a||gj w rest
def de:List (V×V):=
 [([],[]),([ca],[ca]),([sf],[sf]),([ca,sf],[ca,sf]),
  ([se,sd,dk],[se,sd,dk]),
  ([ca,se,sd,dk],[sf,se,sd,dk]),
  ([sf,se,sd,dk],[ca,se,sd,dk]),
  ([ca,sf,se,sd,dk],[ca,sf,se,sd,dk])]
def i5 (ztt T:J) (t0:Nat):
  List (V×V)->Q
 | []=>false
 | (g,gInv)::rest=>(gj (ym gInv t0) ztt&&jk (wx g ztt) T)||i5 ztt T t0 rest
def ma (b T:J):Q:=
 match T with
 | []=>match b with | []=>true | _=>false
 | (t0,_)::_=>i5 b T t0 de
def w5 (T h s:Nat) (ztt:J):Nat->Nat->Q
 | 0,_=>false
 | fuel+1,j =>
  if beq (cj T j) h then
   if ma ztt (i2 s j) then true
   else if beq j 0 then false
   else w5 T h s ztt fuel (sub j 1)
  else false
def i8 (s:Nat)(b:J):Q:=
 zm (gk b) fun h =>
 zm (ar hJ Lf7 lu s h) fun j =>
 !(beq j 999999)&&w5 (lu s) h s b 4 j
def hS (s:Nat)(b:J):Q:=
 i8 s (bn c7.fH b)
lemma ct {n r:Nat}(c:r < 2 ^ n):ur (q1 n r)=r:=by
 apply kL;intro k;rw[jl]
 by_cases b:k < n
 . simp[q1,b]
 . simp only[b,↓reduceDIte];have d:2 ^ n<=2 ^ k:=jA (by omega) (by omega);exact (hZ (Nat.lt_of_lt_of_le c d)).symm
lemma a3 {n w:Nat} (c:w < 2 ^ (2 ^ n)):u9 n (fun x=>w.testBit (ur x))=w:=by
 apply kL;intro r;rw[vr]
 by_cases b:r < 2 ^ n
 . simp only[b,↓reduceIte,ct b]
 . simp only[b,↓reduceIte];have d:2 ^ (2 ^ n)<=2 ^ r:=jA (by omega) (by omega);exact (hZ (Nat.lt_of_lt_of_le c d)).symm
def a7:V->Nat->Nat
 | [],_=>0
 | (c0,c1,c2,c3)::rest,m =>
  if m < 4 then match m with | 0=>c0 | 1=>c1 | 2=>c2 | _=>c3
  else a7 rest (m - 4)
lemma ev:n2.length=14:=rfl
lemma fc:(range 56).all (fun m=>beq (shiftRight (a7 n2 m) 294) 0)=true:=by decide +kernel
lemma mr:(range 294).all (fun idx =>
 let r:=(ee 6 r7 294).getD idx 0
 blt r 56&&(range 56).all (fun m=>(a7 n2 m).testBit idx == beq m r))=true:=by decide +kernel
lemma oc (a b:Nat):beq a b=decide (a=b):=by
 cases h:beq a b
 . symm;rw[decide_eq_false_iff_not];intro c;rw[c,nD] at h;cases h
 . symm;rw[decide_eq_true_eq];exact nC.mp h
lemma dy {m b:Nat}(c:m < 56)(hidx:294<=b):(a7 n2 m).testBit b=false:=by
 have d:shiftRight (a7 n2 m) 294=0:=by simpa[nC] using kH.1 fc m (jF.2 c)
 have e:(a7 n2 m).testBit (294+(b - 294))=false:=by rw[<- kQ];change (shiftRight (a7 n2 m) 294).testBit (b - 294)=false;rw[d];simp
 rwa[show 294+(b - 294)=b by omega] at e
lemma dx {m b:Nat}(e:m < 56)(g:b < 294):(a7 n2 m).testBit b=decide (m=(ee 6 r7 294).getD b 0):=by have c:=kH.1 mr b (jF.2 g);simp only[jY] at c;have d:=kH.1 c.2 m (jF.2 e);rw[beq_iff_eq,oc] at d;exact d
lemma mv {b:Nat}(d:b < 294):(ee 6 r7 294).getD b 0 < 56:=by have c:=kH.1 mr b (jF.2 d);simp only[jY] at c;exact of_decide_eq_true (by simpa[nB] using c.1)
lemma t8 (v b m a c:Nat)(s:m=2 ^ b):(if beq (land v m) 0 then 0 else a).testBit c=(v.testBit b&&a.testBit c):=by
 subst s;by_cases d:v.testBit b=true
 . have t:land v (2 ^ b)≠0:=fun u=>by
    have e:=congrArg (fun z=>z.testBit b) u;rw[kS,kN,d,hY] at e;simp at e
   rw[if_neg (by rw[nC];exact t),d,jW]
 . have g:v.testBit b=false:=(by cases h:v.testBit b<;>simp_all);have x:land v (2 ^ b)=0:=by
    apply kL;intro j;rw[kS,kN,nW]
    by_cases i:b=j
    . subst i;simp[g]
    . simp[i]
   rw[if_pos (by rw[nC];exact x),g,jT,nM]
lemma ob (v c0 c1 c d b:Nat):(rq v c0 c1 c d).testBit b=((v.testBit 0&&c0.testBit b)||(v.testBit 1&&c1.testBit b)||(v.testBit 2&&c.testBit b)||(v.testBit 3&&d.testBit b)):=by
 unfold rq;by_cases e:v=0
 . subst e;simp
 . rw[if_neg (by rw[nC];exact e)];simp only[kR,kM];rw[t8 v 0 1 c0 b rfl,t8 v 1 2 c1 b rfl,t8 v 2 4 c b rfl,t8 v 3 8 d b rfl];simp only[nG]
lemma g5 (c b:Nat)(hb:b < 4):(land c 15).testBit b=c.testBit b:=by
 rw[kS,kN];have d:(15:Nat).testBit b=true:=by interval_cases b<;>decide
 rw[d,hV]
lemma i6 (l:V)(d b:Nat) (c:∀m < 4*l.length,(a7 l m).testBit b=false):(n5 d l).testBit b=false:=by
 induction l generalizing d with
 | nil=>simp[n5]
 | cons q rest ih =>
  rcases q with ⟨c0,c1,c2,c3⟩;unfold n5;rw[kR,kM,ob]
  rw[show c0.testBit b=false by simpa[a7] using c 0 (by rw[kD];omega),show c1.testBit b=false by simpa[a7] using c 1 (by rw[kD];omega),show c2.testBit b=false by simpa[a7] using c 2 (by rw[kD];omega),show c3.testBit b=false by simpa[a7] using c 3 (by rw[kD];omega),ih (shiftRight d 4) (fun m hm=>by simpa[a7,show ¬m+4 < 4 by omega] using c (m+4) (by rw[kD];omega))]
  simp
lemma ut (l:V)(b c r:Nat) (d:∀m < 4*l.length,(a7 l m).testBit c=decide (m=r)):(n5 b l).testBit c=(decide (r < 4*l.length)&&b.testBit r):=by
 induction l generalizing b r with
 | nil=>simp[n5]
 | cons q e ih =>
  rcases q with ⟨c0,c1,c2,c3⟩;unfold n5;rw[kR,kM,ob]
  rw[g5 b 0 (by omega),g5 b 1 (by omega),g5 b 2 (by omega),g5 b 3 (by omega),show c0.testBit c=decide (0=r) by simpa[a7] using d 0 (by rw[kD];omega),show c1.testBit c=decide (1=r) by simpa[a7] using d 1 (by rw[kD];omega),show c2.testBit c=decide (2=r) by simpa[a7] using d 2 (by rw[kD];omega),show c3.testBit c=decide (3=r) by simpa[a7] using d 3 (by rw[kD];omega)]
  by_cases hr4:r < 4
  . rw[i6 e (shiftRight b 4) c (fun m g=>by
     simpa[a7,show ¬m+4 < 4 by omega,show m+4≠r by omega] using d (m+4) (by rw[kD];omega)),
     jS,show decide (r < 4*((c0,c1,c2,c3)::e).length)=true by simp[kD];omega,jW]
    interval_cases r<;>simp
  . rw[ih (shiftRight b 4) (r - 4) (fun m g=>by
     have:=d (m+4) (by rw[kD];omega)
     simp only[a7,show ¬m+4 < 4 by omega,↓reduceIte,nR] at this;rw[this];exact decide_eq_decide.mpr (by omega))]
    simp only[show (0:Nat)≠r by omega,show (1:Nat)≠r by omega,show (2:Nat)≠r by omega,show (3:Nat)≠r by omega,decide_false,nJ,nK];rw[show (shiftRight b 4).testBit (r - 4)=b.testBit r by change (b >>> 4).testBit (r - 4)=b.testBit r;rw[kQ,show 4+(r - 4)=r by omega]]
    congr 1;exact decide_eq_decide.mpr (by rw[kD];omega)
lemma ea (g:Z 6):t3 (u9 6 g)=s8 (aR 6 r7 c7) g:=by
 apply kL;intro b;unfold t3 aR e8;have i:c7.fH=294:=rfl;rw[kR,kM,i]
 have s:land (u9 6 g) l5=u9 6 g:=by
   apply kL;intro j;rw[kS,kN,vr];have t:l5=2 ^ 64 - 1:=by decide
   rw[t,kK];by_cases u:j < 64<;>simp[u]
 rw[s,z8];by_cases d:b < 294
 . rw[ut n2 (u9 6 g) b ((ee 6 r7 294).getD b 0) (fun m c=>dx (by rw[ev] at c;omega) d)]
   have hr:=mv d;simp only[ev,show (ee 6 r7 294).getD b 0 < 4*14 by omega,decide_true,jW];rw[show (shiftLeft (u9 6 g) 294).testBit b=false by change (u9 6 g <<< 294).testBit b=false;rw[nN];simp[show ¬294<=b by omega],jS,vr]
   simp only[show (ee 6 r7 294).getD b 0 < 2 ^ 6 by omega,↓reduceIte];have e:(ee 6 r7 294).length=294:=jj 6 r7 294;rw[mX (by omega),jK (by omega),jL _ _ (by omega)]
 . rw[i6 n2 (u9 6 g) b (fun m c=>dy (by rw[ev] at c;omega) (by omega)),nK]
   change (u9 6 g <<< 294).testBit b=_;rw[nN]
   simp only[show 294<=b by omega,decide_true,jW,vr];have e:(ee 6 r7 294).length=294:=jj 6 r7 294;rw[mY (by omega),e]
   by_cases h:b - 294 < 64
   . rw[jK (by simp;omega)];simp[h]
   . rw[mZ (by simp;omega)];simp[h]
def s7 (s j:Nat):X 6:=
 (i2 s j).map fun p=>((fun x=>p.1.testBit (ur x)),0)
lemma ud (c k:Nat):∀p∈ex c k,p.1 < 2 ^ 64/\p.2=0:=by
 induction k generalizing c with
 | zero=>intro p b;simp[ex] at b
 | succ k ih =>
  intro p b;simp only[ex,kC] at b;rcases b with rfl|b'
  . refine⟨?_,rfl⟩
    rw[kS];have d:l5=2 ^ 64 - 1:=by decide
    rw[d];exact Nat.lt_of_le_of_lt Nat.and_le_right (by omega)
  . exact ih _ p b'
lemma ac (s j:Nat):i2 s j=u2 6 (s7 s j):=by
 unfold s7 u2;rw[hW]
 have b:∀p∈i2 s j,p.1 < 2 ^ 64/\p.2=0:=by unfold i2;simp only[v5];exact ud _ _
 conv_lhs=>rw[<- pA (i2 s j)]
 apply jH
 intro p c;obtain⟨d,e⟩:=b p c;simp only[Function.comp,id,a3 (n:=6) d];exact Prod.ext rfl e
lemma mj (s j:Nat):hQ s j=eW r7 c7 (s7 s j):=by
 unfold hQ s7 eW e6;rw[hW]
 have b:∀p∈i2 s j,p.1 < 2 ^ 64/\p.2=0:=by unfold i2;simp only[v5];exact ud _ _
 apply jH
 intro p c;obtain⟨d,_⟩:=b p c;simp only[Function.comp];rw[<- ea,a3 (n:=6) d]
lemma ga (s j:Nat):gW (s7 s j):=by intro p b;unfold s7 at b;rcases mM.1 b with ⟨_,_,rfl⟩;omega
lemma ow (T h s:Nat)(d:J):∀c j,j < hJ s->w5 T h s d c j=true->∃j' < hJ s,ma d (i2 s j')=true:=by
 intro c;induction c with
 | zero=>intro _ _ e;cases e
 | succ f ih =>
  intro j g b;unfold w5 at b
  split at b
  . split at b
    . exact⟨j,g,‹_›⟩
    . split at b
      . cases b
      . exact ih (sub j 1) (by rw[nY];omega) b
  . cases b
lemma mt {n:Nat}{c:V} {π : (F n)->(F n)} (d:∀g:Z n,ym c (u9 n g)=u9 n (fun x=>g (π x))) (b:X n):wx c (u2 n b)=u2 n (b.map fun p=>((fun x=>p.1 (π x)),p.2)):=by
 induction b with
 | nil=>rfl
 | cons p rest ih=>rcases p with ⟨g,tg⟩;simp only[u2,kB,wx,v5,d];exact congrArg _ ih
lemma ay:∀p∈de,vh f7 p.1:=by
 have h:=ye 6 f7 (de.map fst)
  [[],[(4,5)],[(1,2)],[(4,5),(1,2)],[(2,5),(1,4),(0,3)],[(4,5),(2,5),(1,4),(0,3)],[(1,2),(2,5),(1,4),(0,3)],[(4,5),(1,2),(2,5),(1,4),(0,3)]] (by decide +kernel)
 intro p b;exact h p.1 (List.mem_map_of_mem b)
lemma od {d T_b:X 6}{i:Nat}{b:List (V×V)}(e:∀p∈b,vh f7 p.1) (c:i5 (u2 6 d) (u2 6 T_b) i b=true):∃π : (F 6)->(F 6),Bijective π/\(∀x,f7 (π x)=f7 x)/\(d.map fun p=>((fun x=>p.1 (π x)),p.2)).Perm T_b:=by
 induction b with
 | nil=>cases c
 | cons p rest ih =>
  rcases p with ⟨g,j⟩;unfold i5 at c
  rcases Bool.or_eq_true_iff.1 c with s|t
  . obtain⟨_,h⟩:=Eq.mp (jY) s;obtain⟨π,u,v,y⟩:=e (g,j) jP;rw[mt y] at h;exact⟨π,u,v,(zv _ _).1 (y5 _ _ h)⟩
  . exact ih (fun q z=>e q (hX _ z)) t
lemma ss:∀s (c:X 6),i8 s (u2 6 c)=true->∃j < hJ s,∃π : (F 6)->(F 6),Bijective π/\(∀x,f7 (π x)=f7 x)/\(c.map fun p=>((fun x=>p.1 (π x)),p.2)).Perm (s7 s j):=by
 intro s c h;unfold i8 at h;simp only[v5,jY,kt,zh] at h;obtain⟨i,t⟩:=h;have u:ar hJ Lf7 lu s (gk (u2 6 c)) < hJ s:=j8 hJ Lf7 lu s _ i;obtain⟨j,e,b⟩:=ow (lu s) _ s _ 4 _ u t;rw[ac s j] at b;unfold ma at b;cases d:u2 6 (s7 s j) with
 | nil =>
  rw[d] at b;cases g:u2 6 c with
  | nil=>have v:c=[]:=(by cases c<;>simp[u2] at g ⊢);have y:s7 s j=[]:=(by cases z:s7 s j<;>simp[z,u2] at d ⊢);exact⟨j,e,id,bijective_id,fun _=>rfl,by simp[v,y]⟩
  | cons _ _=>rw[g] at b;cases b
 | cons p0 rest0 =>
  rw[d] at b;rcases p0 with ⟨t0,_⟩
  have b' : i5 (u2 6 c) (u2 6 (s7 s j)) t0 de=true:=(by rw[d];exact b);obtain⟨π,h0,h1,h2⟩:=od ay b';exact⟨j,e,π,h0,h1,h2⟩
lemma gb:w2 f7 (aR 6 r7 c7) hJ s7 hS:=by intro s b h;unfold hS at h;change i8 s (bn c7.fH (eW r7 c7 b))=true at h;rw[eW,aR,kg] at h;exact ss s b h
lemma rv:gX 6 f7 r7 c7:=jn 6 f7 r7 c7 (by decide +kernel)
lemma dc (b:∀s≤ 9,∀i < hJ s,bar c7 hS hQ s i=true):∀s≤ 9,∀i < hJ s,¬TR f7 s (s7 s i):=
 iu rv 9 (by omega) hJ s7 hQ mj ga hS gb b
lemma up:c7.fL=2 ^ 102 - 1:=by decide
lemma gn (w:Nat):wC c7 w < 2 ^ 102:=by
 apply jB;intro i hi;unfold wC wi tx;rw[kT,kP,kS,kS,kN,kN,up,kK]
 have b:¬(i < 102):=by omega
 simp[b]
lemma df (b:J):yx c7 b < 2 ^ 102:=by
 induction b with
 | nil=>simp[yx]
 | cons p rest ih =>
  rw[yp]
  apply jB;intro i hi;rw[kR,kM,hZ (Nat.lt_of_lt_of_le (gn p.1) (jA (by omega) hi)),hZ (Nat.lt_of_lt_of_le ih (jA (by omega) hi))]
  rfl
lemma n3 (b:J)(i:Nat):(yx c7 b).testBit i=b.any (fun p=>(wC c7 p.1).testBit i):=by
 induction b with
 | nil=>simp[yx]
 | cons p rest ih=>rw[yp,kR,kM,ih];simp
def u3 (b:M):J:=b.map fun w=>(t3 w,0)
lemma y9 (L0:List (Z 6)):u3 (L0.map (u9 6))=eW r7 c7 (L0.map (·,0)):=by unfold u3 eW e6;simp only[hW];apply jH;intro g _;simp[Function.comp,ea]
lemma ub {a b:M}(h:a.Sublist b)(i:Nat):(yx c7 (u3 a)).testBit i=true->(yx c7 (u3 b)).testBit i=true:=by
 rw[n3,n3,kJ,kJ]
 rintro ⟨p,c,d⟩
 exact⟨p,(h.map _).subset c,d⟩
lemma md {s:Nat}{L0:List (Z 6)} (b:TR f7 s (L0.map (·,0))):yx c7 (u3 (L0.map (u9 6)))=c7.fL:=by
 rw[y9]
 apply zz rv
 intro u v c d;have e:Run (hC (n:=6)) hE hG f7 s L0:=by have h:=b.toRun;have i:(L0.map (·,0)).map fst=L0:=(by rw[hW];exact pA L0);rwa[i] at h
 obtain⟨g,j,t⟩:=ux e (show f7 u≠f7 v by rw[c,d];decide);exact⟨(g,0),mM.2 ⟨g,j,rfl⟩,t⟩
lemma m6 {a b c:Nat}(e:a < 2 ^ 102)(g:c < 2 ^ 102)(h:∀i,b.testBit i=true->c.testBit i=true)(j:lor a b=c7.fL):lor a c=c7.fL:=by
 apply kL;intro i;rw[kR,kM,up,kK]
 by_cases hi:i < 102
 . simp only[hi,decide_true];have d:=congrArg (fun z=>z.testBit i) j;rw[kR,kM,up,kK] at d;simp only[hi,decide_true] at d;cases e' : a.testBit i
   . simp only[e',nK] at d ⊢;exact h i d
   . simp
 . simp only[hi,decide_false];rw[hZ (Nat.lt_of_lt_of_le e (jA (by omega) (by omega))),hZ (Nat.lt_of_lt_of_le g (jA (by omega) (by omega)))]
   rfl
def t7:M->Nat×List (Nat×Nat×Nat×Nat×Nat×Nat×Nat)
 | []=>(0,[])
 | w::rest =>
  let (sC,rs):=t7 rest
  zm (t3 w) fun ew =>
  zm (land ew c7.fL) fun elo =>
  zm (land (shiftRight ew c7.k) c7.fL) fun ehi =>
  zm (xor elo ehi) fun cw =>
  zm (land cw ehi) fun uw =>
  zm (qi c7.m0 (land (shiftRight ew c7.fE) c7.fM)) fun v0w =>
  zm (yg c7.fF c7.m1 c7.fQ ew) fun v1w =>
  (lor cw sC,(w,ew,cw,uw,v0w,v1w,sC)::rs)
lemma eb (b:M):(t7 b).1=yx c7 (u3 b):=by
 induction b with
 | nil=>rfl
 | cons w rest ih=>simp[t7,u3,yx,wC,wi,tx,v5,ih]
def f5 (b e g h i:Nat)(c d:J):Q:=
 match c with
 | []=>true
 | _ =>
  if beq b 0 then
   match c with
   | [(w,_)]=>!(beq w ap)
   | _=>true
  else if beq e (add b 1) then
   if !(beq g c7.fL)||!(qb c7 h 0) then true
   else i8 b c||m7 c7 b d
  else if beq e b then
   if !(beq g c7.fL)&&!(z3 c7 i) then true
   else i8 b c||m7 c7 b d
  else
   i8 b c||m7 c7 b d
def m9 (b:Nat):List (Nat×Nat×Nat×Nat×Nat×Nat×Nat)->Nat->Nat->Nat->Nat->Nat->J->J->Q
 | [],len,cc,cu,sv0,sv1,curTT,curEnc =>
  !(beq cc c7.fL)||f5 b len cu sv0 sv1 curTT curEnc
 | (w,ew,cw,uw,v0w,v1w,sC)::rest,len,cc,cu,sv0,sv1,curTT,curEnc =>
  if beq len (add b 1) then
   !(beq cc c7.fL)||f5 b len cu sv0 sv1 curTT curEnc
  else
   let c:=
    zm (lor cw cc) fun cc1 =>
    if beq (lor cc1 sC) c7.fL then
     m9 b rest (add len 1) cc1 (lor uw cu) (add v0w sv0) (add v1w sv1) ((w,0)::curTT) ((ew,0)::curEnc)
    else true
   if !c then false
   else if beq (lor cc sC) c7.fL then
    m9 b rest len cc cu sv0 sv1 curTT curEnc
   else true
lemma da (g:Nat)(i:M):∀(b sub:M),sub.Sublist i->b.length+sub.length<=g+1->lor (yx c7 (u3 b)) (yx c7 (u3 sub))=c7.fL->m9 g (t7 i).2 b.length (yx c7 (u3 b)) (v4 c7 (u3 b)) (zf c7 (u3 b)) (va c7 (u3 b)) (b.map (·,0)) (u3 b)=true->∃L',L'.Perm (sub++b)/\f5 g L'.length (v4 c7 (u3 L')) (zf c7 (u3 L')) (va c7 (u3 L')) (L'.map (·,0)) (u3 L')=true:=by
 induction i with
 | nil =>
  intro b sub c _ d e;cases c
  rw[show yx c7 (u3 [])=0 from rfl,kR,Nat.or_zero] at d;simp only[t7,m9,d,nD,nH,nK] at e;exact⟨b,mP _,e⟩
 | cons w j ih =>
  intro b sub c hlen d e;simp only[t7,v5,eb] at e;unfold m9 at e;by_cases u:b.length=g+1
  . have y:sub=[]:=List.eq_nil_of_length_eq_zero (by omega);subst y;rw[show yx c7 (u3 [])=0 from rfl,kR,Nat.or_zero] at d;have s:beq b.length (add g 1)=true:=(by rw[nC];exact u);simp only[s,↓reduceIte,d,nD,nH,nK] at e;exact⟨b,mP _,e⟩
  . have s:beq b.length (add g 1)=false:=q2 u;simp only[s,jV,↓reduceIte] at e;obtain⟨h,v⟩:=o7 e;cases c with
    | cons _ c' => have t:lor (yx c7 (u3 b)) (yx c7 (u3 j))=c7.fL:=m6 (df _) (df _) (ub c') d;simp only[t,nD,↓reduceIte] at v;exact ih b sub c' hlen d v
    | cons_cons _ c' =>
     rename_i sub'
     have x:lor (yx c7 (u3 (w::b))) (yx c7 (u3 sub'))=c7.fL:=(by simp only[u3,kB,yx,kG,kR] at d ⊢;rw[Nat.or_comm (wC c7 (t3 w)),Nat.or_assoc];exact d);have t:lor (yx c7 (u3 (w::b))) (yx c7 (u3 j))=c7.fL:=m6 (df _) (df _) (ub c') x;have z:lor (xor (land (t3 w) c7.fL) (land (shiftRight (t3 w) c7.k) c7.fL)) (yx c7 (u3 b)) =
       yx c7 (u3 (w::b)):=rfl
     have h0:lor (land (xor (land (t3 w) c7.fL) (land (shiftRight (t3 w) c7.k) c7.fL)) (land (shiftRight (t3 w) c7.k) c7.fL)) (v4 c7 (u3 b))=v4 c7 (u3 (w::b)):=rfl;have h1:add (qi c7.m0 (land (shiftRight (t3 w) c7.fE) c7.fM)) (zf c7 (u3 b))=zf c7 (u3 (w::b)):=rfl;have h2:add (yg c7.fF c7.m1 c7.fQ (t3 w)) (va c7 (u3 b))=va c7 (u3 (w::b)):=rfl;simp only[v5,z,t,nD,↓reduceIte,h0,h1,h2] at h;have hlen' : (w::b).length+sub'.length<=g+1:=(by simp at hlen ⊢;omega);have h' : m9 g (t7 j).2 (w::b).length (yx c7 (u3 (w::b)))
       (v4 c7 (u3 (w::b))) (zf c7 (u3 (w::b))) (va c7 (u3 (w::b)))
       ((w::b).map (·,0)) (u3 (w::b))=true:=by
      simpa[kD,nX,u3] using h
     obtain⟨L',h3,h4⟩:=ih (w::b) sub' c' hlen' x h';exact⟨L',h3.trans mE,h4⟩
lemma mm:u9 6 f7=ap:=by decide +kernel
lemma tc (c2:∀s≤ 9,∀i < hJ s,bar c7 hS hQ s i=true){z:Nat}(c3:z<=9){L0:List (Z 6)} {L' : M} (h7:L'.Perm (L0.map (u9 6))) (b:f5 z L'.length (v4 c7 (u3 L')) (zf c7 (u3 L')) (va c7 (u3 L')) (L'.map (·,0)) (u3 L')=true):¬TR f7 z (L0.map (·,0)):=by
 intro c;have d1:L0≠[]:=by intro h8;subst h8;have a1:=md c;rw[show yx c7 (u3 ([].map (u9 6)))=0 from rfl,up] at a1;exact absurd a1 (by decide)
 have d2:L'≠[]:=by intro h8;subst h8;have hlen:=h7.length_eq;simp at hlen;exact d1 (List.eq_nil_of_length_eq_zero hlen.symm)
 have e0:∃L0' : List (Z 6),L0'.Perm L0/\L0'.map (u9 6)=L':=by
  have a2:∀w∈L',w < 2 ^ 64:=by
    intro w hw;rcases mM.1 (h7.mem_iff.1 hw) with ⟨g,_,rfl⟩
    apply jB;intro r hr;rw[vr,if_neg (by omega)]
  refine⟨L'.map (fun w (x:F 6)=>w.testBit (ur x)),?_,?_⟩
  . have e1:(L'.map (fun w (x:F 6)=>w.testBit (ur x))).map (u9 6)=L':=by
      rw[hW];conv_rhs=>rw[<- pA L']
      apply jH;intro w hw;simp[Function.comp,a3 (n:=6) (a2 w hw)]
    have e2:(u2 6 ((L'.map (fun w (x:F 6)=>w.testBit (ur x))).map (·,0))).Perm
              (u2 6 (L0.map (·,0))):=by
      have d:=(show ((L'.map (fun w (x:F 6)=>w.testBit (ur x))).map (u9 6)).Perm (L0.map (u9 6)) by rw[e1];exact h7).map (fun w=>(w,0));have hL:u2 6 ((L'.map (fun w (x:F 6)=>w.testBit (ur x))).map (·,0)) =
          ((L'.map (fun w (x:F 6)=>w.testBit (ur x))).map (u9 6)).map (fun w=>(w,0)):=by
        unfold u2;simp[hW,Function.comp]
      have hR:u2 6 (L0.map (·,0))=(L0.map (u9 6)).map (fun w=>(w,0)):=(by unfold u2;simp[hW,Function.comp]);rw[hL,hR];exact d
    have hc:=((zv _ _).1 e2).map fst;have h9:((L'.map (fun w (x:F 6)=>w.testBit (ur x))).map (·,0)).map fst =
        L'.map (fun w (x:F 6)=>w.testBit (ur x)):=by rw[hW];exact pA _
    have hd:(L0.map (·,0)).map fst=L0:=(by rw[hW];exact pA _);rwa[h9,hd] at hc
  . rw[hW];conv_rhs=>rw[<- pA L']
    apply jH;intro w hw;simp[Function.comp,a3 (n:=6) (a2 w hw)]
 obtain⟨L0',he,e⟩:=e0;have c' : TR f7 z (L0'.map (·,0)):=gV.perm (he.symm.map (·,0)) c;cases z with
 | zero =>
  obtain⟨tg,h⟩:=c'.inv_zero;have hf' : L0'=[f7]:=by
    have:=congrArg (List.map fst) h
    have h9:(L0'.map (·,0)).map fst=L0':=(by rw[hW];exact pA _);simpa[h9] using this
  rw[hf'] at e;simp only[kB,mS,mm] at e;rw[<- e] at b;simp[f5] at b
 | succ s' =>
  cases hL' : L' with
  | nil=>exact absurd hL' d2
  | cons w0 t =>
    rw[hL'] at b e;have hh:(w0::t).map (fun w=>(w,0))=u2 6 (L0'.map (·,0)):=by rw[<- e];unfold u2;simp[hW,Function.comp]
    have hk:u3 (w0::t)=eW r7 c7 (L0'.map (·,0)):=(by rw[<- e];exact y9 L0');have hlenL:(w0::t).length=L0'.length:=(by rw[<- e];simp);have b0:(L0'.map (·,0)).length<=11:=(by have:=c'.len_le;simp at this ⊢;omega);have x2' : Run (hC (n:=6)) hE hG f7 (s'+1) ((L0'.map (·,0)).map fst):=c'.toRun;have h6:(L0'.map (·,0)).map fst=L0':=(by rw[hW];exact pA _);simp only[f5,kB,nC,nP,↓reduceIte,hk] at b;have b1:(i8 (s'+1) ((w0::t).map (·,0))||m7 c7 (s'+1) (eW r7 c7 (L0'.map (·,0))))=true:=by
      by_cases d:(w0::t).length=s'+1+1
      . have h:((L0'.map (·,0)).map fst).length=(s'+1)+1:=(by rw[h6];omega);have x3:v4 c7 (eW r7 c7 (L0'.map (·,0)))=c7.fL:=q6 rv fun u v hu hv=>by
          obtain⟨g,hg,ha,hb⟩:=sv x2' h u v hu hv;rw[h6] at hg;exact⟨(g,0),mM.2 ⟨g,hg,rfl⟩,ha,hb⟩
        have hm:qb c7 (zf c7 (eW r7 c7 (L0'.map (·,0)))) 0=true:=ox rv b0 fun r0 r1 r2 r3 r4 r5 h0 d' y h3 h4 h5=>by
          have:=dm x2' h r0 r1 r2 r3 r4 r5 h0 d' y h3 h4 h5;rwa[hW] at this
        simp only[d,nX,↓reduceIte,x3,nD,nH,hm,Bool.or_self,jV] at b;exact b
      . simp only[d,nX,↓reduceIte] at b;by_cases y:(w0::t).length=s'+1
        . have h:((L0'.map (·,0)).map fst).length=s'+1:=(by rw[h6];omega);have hn:(!(beq (v4 c7 (eW r7 c7 (L0'.map (·,0)))) c7.fL)&&!(z3 c7 (va c7 (eW r7 c7 (L0'.map (·,0))))))=false:=by
           rcases aj x2' h with hu|hs
           . have x3:v4 c7 (eW r7 c7 (L0'.map (·,0)))=c7.fL:=q6 rv fun u v ha hb=>by
               obtain⟨g,hg,hq,ht⟩:=hu u v ha hb;rw[h6] at hg;exact⟨(g,0),mM.2 ⟨g,hg,rfl⟩,hq,ht⟩
             simp[x3]
           . have hx:z3 c7 (va c7 (eW r7 c7 (L0'.map (·,0))))=true:=vt rv b0 fun r0 r1 r2 r3 r4 r5 h0 d' y' h3 h4 h5=>by
               have:=hs r0 r1 r2 r3 r4 r5 h0 d' y' h3 h4 h5;rwa[hW] at this
             simp[hx]
          simp only[y,↓reduceIte,hn,jV] at b;exact b
        . simp only[y,↓reduceIte] at b;exact b
    rw[jX] at b1;rcases b1 with b3|hy
    . rw[hh] at b3;obtain⟨j,hj,π,hz,xi,hp⟩:=ss (s'+1) (L0'.map (·,0)) b3;exact dc c2 (s'+1) c3 j hj (gV.perm hp (wp π hz xi c'))
    . exact f9 rv hy c'
lemma dq (h5:∀s≤ 9,∀i < hJ s,bar c7 hS hQ s i=true){e:Nat}(h6:e<=9)(b:M)(h7:b.Nodup) (y : !(beq (t7 b).1 c7.fL)||m9 e (t7 b).2 0 0 0 0 0 [] []=true) {L0:List (Z 6)}(h8:L0.Nodup)(h9:∀g∈L0,u9 6 g∈b):¬TR f7 e (L0.map (·,0)):=by
 intro t;let d:=L0.map (u9 6);have x2:d.Nodup:=h8.map (fun _ _ h=>yc h);let sub:=b.filter (fun w=>decide (w∈d));have z:sub.Sublist b:=List.filter_sublist;have x3:sub.Nodup:=h7.filter _;have u:sub.Perm d:=by
   refine (List.perm_ext_iff_of_nodup x3 x2).2 ?_
   intro w;simp only[sub,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp];intro hw;rcases mM.1 hw with ⟨g,hg,rfl⟩
   exact h9 g hg
 have a1:yx c7 (u3 d)=c7.fL:=md t;have h0:yx c7 (u3 sub)=c7.fL:=by
   apply kL;intro i;rw[n3,<- a1,n3]
   have h3:(u3 sub).Perm (u3 d):=u.map _;cases h:(u3 sub).any (fun p=>(wC c7 p.1).testBit i)
   . symm;rw[jU];intro j;rw[kJ] at j;rcases j with ⟨p,c,v⟩
     have:(u3 sub).any (fun p=>(wC c7 p.1).testBit i)=true:=kJ.2 ⟨p,h3.mem_iff.2 c,v⟩
     rw[h] at this;cases this
   . symm;rw[kJ] at h ⊢;rcases h with ⟨p,c,v⟩
     exact⟨p,h3.mem_iff.1 c,v⟩
 simp only[jX,kt,eb] at y;rcases y with h4|a2
 . have b0:yx c7 (u3 b)=c7.fL:=by
     have x:=m6 (a:=0) (by decide) (df _) (ub z)
      (by simpa[kR] using h0)
     simpa[kR] using x
   rw[b0,nD] at h4;cases h4
 . have hlen:([]:M).length+sub.length<=e+1:=(by have x:=t.len_le;have j:=u.length_eq;simp[d] at x j ⊢;omega);obtain⟨L',c',b1⟩:=da e b [] sub z hlen
     (by simpa[u3,yx,kR] using h0) a2
   have c'' : L'.Perm (L0.map (u9 6)):=(by simpa using c'.trans (by simpa using u));exact tc h5 h6 c'' b1 t
def fG:Z 8:=fun x:F 8 =>
 (x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 2)||(x 1&&x 4) ||
 (x 3&&x 5)||(x 3&&x 6)||(x 4&&x 5)||(x 4&&x 7)||(x 5&&x 6)
def a9 (x:F 6):F 8
 | ⟨0,_⟩ => x 0
 | ⟨1,_⟩ => x 1
 | ⟨2,_⟩ => x 2
 | ⟨3,_⟩ => x 3
 | ⟨4,_⟩ => false
 | ⟨5,_⟩ => x 4
 | ⟨6,_⟩ => x 5
 | ⟨7,_⟩ => true
def eh (x:F 6):F 8
 | ⟨0,_⟩ => x 0
 | ⟨1,_⟩ => x 1
 | ⟨2,_⟩ => x 2
 | ⟨3,_⟩ => x 3
 | ⟨4,_⟩ => false
 | ⟨5,_⟩ => x 4
 | ⟨6,_⟩ => x 5
 | ⟨7,_⟩ => false
def a8 (g:Z 8):Z 6:=fun x=>g (a9 x)
def u5:List o1:=
 [inr 0,inr 1,inr 2,inr 3,inl false,inr 4,inr 5,inl true]
def c5:List o1:=
 [inr 0,inr 1,inr 2,inr 3,inl false,inr 4,inr 5,inl false]
def d3:List o1:=
 [inr 0,inr 1,inr 2,inr 3,inr 4,inr 5,inr 6,inl true]
def l6:List o1:=
 [inr 0,inr 1,inr 2,inr 3,inr 4,inr 5,inr 6,inl false]
def l9 (x:F 7):F 8
 | ⟨0,_⟩ => x 0
 | ⟨1,_⟩ => x 1
 | ⟨2,_⟩ => x 2
 | ⟨3,_⟩ => x 3
 | ⟨4,_⟩ => x 4
 | ⟨5,_⟩ => x 5
 | ⟨6,_⟩ => x 6
 | ⟨7,_⟩ => false
def cd:List o1:=
 [inr 4,inr 5,inl false,inr 1,inr 3,inr 0,inr 2,inr 6]
def eg (x:F 7):F 8
 | ⟨0,_⟩ => x 4
 | ⟨1,_⟩ => x 5
 | ⟨2,_⟩ => false
 | ⟨3,_⟩ => x 1
 | ⟨4,_⟩ => x 3
 | ⟨5,_⟩ => x 0
 | ⟨6,_⟩ => x 2
 | ⟨7,_⟩ => x 6
def cb:List o1:=
 [inr 1,inr 0,inr 2,inr 4,inr 3,inr 5,inl false,inr 6]
def ef (x:F 7):F 8
 | ⟨0,_⟩ => x 1
 | ⟨1,_⟩ => x 0
 | ⟨2,_⟩ => x 2
 | ⟨3,_⟩ => x 4
 | ⟨4,_⟩ => x 3
 | ⟨5,_⟩ => x 5
 | ⟨6,_⟩ => false
 | ⟨7,_⟩ => x 6
lemma j6 (x:F 6):fG (a9 x)=f7 x:=by simp only[fG,a9,f7,nJ,jT,jS,nK]
lemma te (x:F 6):fG (eh x)=f7 x:=by simp only[fG,eh,f7,nJ,jT,jS,nK]
lemma p6 (x:F 7):fG (l9 x)=ry x:=by simp only[fG,l9,ry,nJ,jS]
lemma bb (x:F 7):fG (eg x)=gf x:=by simp only[fG,eg,gf];cases x 0<;>cases x 1<;>cases x 2<;>cases x 3<;>cases x 4<;>cases x 5<;>cases x 6<;>rfl
lemma ba (x:F 7):fG (ef x)=gf x:=by simp only[fG,ef,gf];cases x 0<;>cases x 1<;>cases x 2<;>cases x 3<;>cases x 4<;>cases x 5<;>cases x 6<;>rfl
lemma b4 (x:F 6):tu 6 (ofFn x) (ofFn (a9 x)) (u5,[]):=by
 refine⟨by rfl,?_⟩;intro i;rcases Nat.lt_or_ge i 8 with hi|hi
 . interval_cases i<;>simp[u5,a9,qn,ze,q3]
 . rw[mQ _ _ (by simp[u5];omega),mQ _ _ (by simp;omega)];exact⟨trivial,rfl⟩
lemma dt (x:F 6):tu 6 (ofFn x) (ofFn (eh x)) (c5,[]):=by
 refine⟨by rfl,?_⟩;intro i;rcases Nat.lt_or_ge i 8 with hi|hi
 . interval_cases i<;>simp[c5,eh,qn,ze,q3]
 . rw[mQ _ _ (by simp[c5];omega),mQ _ _ (by simp;omega)];exact⟨trivial,rfl⟩
lemma um (x:F 8):tu 8 (ofFn x) (ofFn (update x 7 true)) (d3,[]):=by
 refine⟨by rfl,?_⟩;intro i;rcases Nat.lt_or_ge i 8 with hi|hi
 . interval_cases i<;>simp[d3,qn,ze,q3,update]
 . rw[mQ _ _ (by simp[d3];omega),mQ _ _ (by simp;omega)];exact⟨trivial,rfl⟩
lemma uf (x:F 7):tu 7 (ofFn x) (ofFn (l9 x)) (l6,[]):=by
 refine⟨by rfl,?_⟩;intro i;rcases Nat.lt_or_ge i 8 with hi|hi
 . interval_cases i<;>simp[l6,l9,qn,ze,q3]
 . rw[mQ _ _ (by simp[l6];omega),mQ _ _ (by simp;omega)];exact⟨trivial,rfl⟩
lemma bz (x:F 7):tu 7 (ofFn x) (ofFn (eg x)) (cd,[]):=by
 refine⟨by rfl,?_⟩;intro i;rcases Nat.lt_or_ge i 8 with hi|hi
 . interval_cases i<;>simp[cd,eg,qn,ze,q3]
 . rw[mQ _ _ (by simp[cd];omega),mQ _ _ (by simp;omega)];exact⟨trivial,rfl⟩
lemma bw (x:F 7):tu 7 (ofFn x) (ofFn (ef x)) (cb,[]):=by
 refine⟨by rfl,?_⟩;intro i;rcases Nat.lt_or_ge i 8 with hi|hi
 . interval_cases i<;>simp[cb,ef,qn,ze,q3]
 . rw[mQ _ _ (by simp[cb];omega),mQ _ _ (by simp;omega)];exact⟨trivial,rfl⟩
lemma n0:∃x y:F 6,f7 x≠f7 y:=
 ⟨fun _=>false,fun _=>true,by decide⟩
lemma an:∃x y:F 7,gf x≠gf y:=
 ⟨fun _=>false,fun _=>true,by decide⟩
lemma om:∃x y:F 7,ry x≠ry y:=
 ⟨fun _=>false,fun _=>true,by decide⟩
lemma ru:∃x y:F 8,fG x≠fG y:=
 ⟨fun _=>false,fun _=>true,by decide⟩
lemma t5 {n m B:Nat}{f:Z n}{g:Z m}{gs:U}{o:Nat}(init:List o1) (d:(F m)->(F n)) (hcl:yq n gs)(hev:∀x,e5 gs n o x=f x) (t:∀x,tu m (ofFn x) (ofFn (d x)) (init,[])) (u:∀x,f (d x)=g x) (v:∃x y,g x≠g y)(z:∀s',nV m g s'->B<=s'):(∀c,(u4 m gs (init,[])).1.getD o (inl false)≠inl c)/\B<=(u4 m gs (init,[])).2.length:=by
 set b:=u4 m gs (init,[]);have h0:∀x,tu m (ofFn x) (q3 gs (ofFn (d x))) b:=fun x=>j7 m _ (by simp) gs _ _ (fun g' hg' => (ja hcl g' hg').1) (t x)
 have e:∀x,ze (q3 b.2 (ofFn x)) (b.1.getD o (inl false))=g x:=fun x=>((h0 x).2 o).2.trans ((hev (d x)).trans (u x))
 have h:∀c,b.1.getD o (inl false)≠inl c:=by
  intro c hc;obtain⟨x,y,h1⟩:=v;apply h1
  rw[<- e x,<- e y,hc];rfl
 refine⟨h,?_⟩
 cases i:b.1.getD o (inl false) with
 | inl c=>exact absurd i (h c)
 | inr j =>
  apply z b.2.length
  refine⟨⟨b.2,j⟩,bq m gs _ (by simp),le_refl _,?_⟩
  intro x;have:=e x;rw[i] at this;exact this
lemma s4 {n m s:Nat}{f:Z n}{g:Z m}(init:List o1) (d:(F m)->(F n)) (z:∀x,tu m (ofFn x) (ofFn (d x)) (init,[])) (e:∀x,f (d x)=g x) (i:∃x y,g x≠g y)(hc:nV n f s):nV m g s:=by
 have h0:∃x y,f x≠f y:=by obtain⟨x,y,t⟩:=i;exact⟨d x,d y,by rwa[e,e]⟩
 obtain⟨gs,o,u,hlen⟩:=ng n f s h0 hc;set b:=u4 m gs (init,[]);have h2:∀x,tu m (ofFn x) (q3 gs (ofFn (d x))) b:=fun x=>j7 m _ (by simp) gs _ _ (fun g' hg' => (ja u.gP g' hg').1) (z x)
 have h:∀x,ze (q3 b.2 (ofFn x)) (b.1.getD o (inl false))=g x:=fun x=>((h2 x).2 o).2.trans ((u.gQ (d x)).trans (e x))
 cases v:b.1.getD o (inl false) with
 | inl c =>
  exfalso;obtain⟨x,y,t⟩:=i;apply t
  rw[<- h x,<- h y,v];rfl
 | inr j =>
  have h3:b.2.length<=s:=(by have h1:b.2.length<=gs.length:=(by simpa[b] using fs m gs (init,[]));omega);refine⟨⟨b.2,j⟩,bq m gs _ (by simp),h3,?_⟩
  intro x;have:=h x;rw[v] at this;exact this
lemma ax:∀s,nV 8 (fun x=>fG (update x 2 false)) s->11<=s:=by
 intro s b;apply lb12 s
 apply s4 cd eg bz _ an b
 intro x
 have:update (eg x) 2 false=eg x:=by funext i;fin_cases i<;>rfl
 rw[this];exact bb x
lemma aw:∀s,nV 8 (fun x=>fG (update x 6 false)) s->11<=s:=by
 intro s b;apply lb12 s
 apply s4 cb ef bw _ an b
 intro x
 have:update (ef x) 6 false=ef x:=by funext i;fin_cases i<;>rfl
 rw[this];exact ba x
lemma sr:∀s,nV 8 (fun x=>fG (update x 7 true)) s->11<=s:=by
 intro s e;have j:∃x y:F 8,fG (update x 7 true)≠fG (update y 7 true):=⟨fun _=>false,fun _=>true,by decide⟩;obtain⟨gs,o,b,hlen⟩:=ng 8 _ s j e;have t:(4:Nat)∈u0 gs 8 o 0:=rh b.gQ 4 ⟨fun _=>false,by decide⟩;have u:(4:Nat)≠o:=by
  intro v;have c:=b.gQ (fun i:Fin 8=>i=0||i=1);rw[<- v] at c;have z:e5 gs 8 4 (fun i:Fin 8=>i=0||i=1)=false:=by unfold e5;rw[ve _ _ _ (by simp)];simp
  rw[z] at c;revert c;decide
 have h0:∃g∈gs,(4:Nat)∈g.inputs:=by
  rcases ((qw gs 8 o 0 4).1 t).2 with h|⟨q,_,g,d,h3,_⟩
  . exact absurd h u
  . exact⟨g,List.mem_of_getElem? d,h3⟩
 have hlb10:=(t5 u5 a9 b.gP b.gQ b4 (fun x=>by
    have:update (a9 x) 7 true=a9 x:=by funext i;fin_cases i<;>rfl
    rw[this];exact j6 x)
  n0 lb7).2
 have h4:=zt 6 4 gs (u5,[]) (fun g d=>ja b.gP g d) (by simp[u5])
  ⟨false,by simp[u5]⟩ h0
 simp at h4;omega
lemma dr {n:Nat}{f:Z n}{gs:U}{o:Nat}(hcl:yq n gs)(ho:o < n+gs.length)(hev:∀x,e5 gs n o x=f x)(t:∃x y,f x≠f y)(z:∀s,nV n f s->gs.length<=s):gY n f gs o:=by
 have v:∀gs' o',yq n gs'->o' < n+gs'.length->(∀x,e5 gs' n o' x=f x) ->
    gs.length<=gs'.length:=by
   intro gs' o' hcl' ho' hev';apply z gs'.length
   exact⟨⟨gs',o'⟩,fun g hg=>(ja hcl' g hg).1,le_refl _,hev'⟩
 refine⟨hcl,ho,hev,?_,?_,?_⟩
 . intro p b;by_contra h0;obtain⟨g0,d⟩ : ∃g0,gs[p]?=some g0:=⟨gs[p],jK b⟩;obtain⟨e,h,i,j⟩:=ra gs p g0 d;subst j;subst i;obtain⟨gs',o',hcl',hlen',ho',hev'⟩:=y7 n f e h g0 o hcl ho hev t (inl false) trivial (Or.inr h0)
   have:=v gs' o' hcl' ho' hev';simp at this;omega
 . intro p b c h1;obtain⟨g0,d⟩ : ∃g0,gs[p]?=some g0:=⟨gs[p],jK b⟩;obtain⟨e,h,i,j⟩:=ra gs p g0 d;subst j;subst i;obtain⟨gs',o',hcl',hlen',ho',hev'⟩:=y7 n f e h g0 o hcl ho hev t (inl c) trivial (Or.inl fun x=>by rw[h1];rfl)
   have:=v gs' o' hcl' ho' hev';simp at this;omega
 . intro p b u hu h2;obtain⟨g0,d⟩ : ∃g0,gs[p]?=some g0:=⟨gs[p],jK b⟩;obtain⟨e,h,i,j⟩:=ra gs p g0 d;subst j;subst i;obtain⟨gs',o',hcl',hlen',ho',hev'⟩:=
    y7 n f e h g0 o hcl ho hev t (inr u) hu
     (Or.inl fun x=>by
      rw[h2];unfold e5;rw[zd,ve _ _ _ (by rw[qu];simp;omega)];rfl)
   have:=v gs' o' hcl' ho' hev';simp at this;omega
def u1 (m:Nat)(gs:U)(init:List o1)(p:Nat):List o1×U:=
 u4 m (gs.take p) (init,[])
lemma sn (m:Nat)(gs:U)(init:List o1)(p:Nat)(b:p<=gs.length):(u1 m gs init p).1.length=init.length+p:=by unfold u1;rw[nh,pB,jR b]
lemma f3 (m:Nat)(gs:U)(init:List o1)(p:Nat)(g:G)(b:gs[p]?=some g):u1 m gs init (p+1)=qa m (u1 m gs init p) g:=by unfold u1;have c:p < gs.length:=(jJ.1 b).1;have d:gs[p]=g:=(jJ.1 b).2;rw[List.take_succ_eq_append_getElem c,d,jz,k4];rfl
lemma dh (m:Nat)(gs:U)(init:List o1)(p:Nat):u4 m (gs.drop p) (u1 m gs init p)=u4 m gs (init,[]):=by unfold u1;rw[<- jz,List.take_append_drop]
lemma tf {m:Nat}{gs:U}{o p u:Nat}(init:List o1) (b:(F m)->(F 8)) {d:Z m}(e:gY 8 fG gs o)(hinit_len:init.length=8) (v:∀x,tu m (ofFn x) (ofFn (b x)) (init,[])) (i:∀x,fG (b x)=d x) (z:∃x y,d x≠d y)(hp:p<=gs.length)(h0:u∈u0 gs 8 o p){c:Q} (h1:(u1 m gs init p).1.getD u (inl false)=inl c):∃q,p<=q/\∃g',gs[q]?=some g'/\u∈g'.inputs:=by
 have⟨hlt,hl⟩:=(qw gs 8 o p u).1 h0;rcases hl with rfl|⟨q,hq,g',h',h2,_⟩
 . exfalso;have hfl:=sn m gs init p hp;have h3:(u4 m gs (init,[])).1.getD u (inl false)=inl c:=by rw[<- dh m gs init p,wy m u _ _ _ (by omega)];exact h1
   have j:∀x,tu m (ofFn x) (q3 gs (ofFn (b x))) (u4 m gs (init,[])):=fun x=>j7 m _ (by simp) gs _ _ (fun g h=>(ja e.gP g h).1) (v x)
   obtain⟨x,y,h4⟩:=z;apply h4
   have s:=(((j x).2 u).2.trans (e.gQ _)).trans (i x);have t:=(((j y).2 u).2.trans (e.gQ _)).trans (i y);rw[h3] at s t;exact s.symm.trans t
 . exact⟨q,hq,g',h',h2⟩
lemma e7 {m:Nat}{gs:U}{init:List o1}{p:Nat}{g:G}(b:gs[p]?=some g)(d:mc g){u:Nat}(e:u∈g.inputs){c:Q} (h:(u1 m gs init p).1.getD u (inl false)=inl c):(u1 m gs init (p+1)).2.length=(u1 m gs init p).2.length:=by rw[f3 m gs init p g b];exact vs m _ g d u e c h
lemma n8 {m:Nat}{gs:U}{init:List o1}{p:Nat}{g:G}(b:gs[p]?=some g):(u1 m gs init (p+1)).2.length<=(u1 m gs init p).2.length+1:=by
 rw[f3 m gs init p g b];simp only[qa,kE]
 have:=y2 (qg g.op (m+(u1 m gs init p).2.length) (g.inputs.map fun i=>(u1 m gs init p).1.getD i (inl false))).1
 omega
lemma sj (m:Nat)(gs:U)(init:List o1):∀k≤ gs.length,(u1 m gs init k).2.length+((range k).filter (fun q=>decide ((u1 m gs init (q+1)).2.length=(u1 m gs init q).2.length))).length=k:=by
 intro k;induction k with
 | zero=>intro _;simp[u1,u4]
 | succ k ih =>
  intro hk;have hih:=ih (by omega);have d:k < gs.length:=by omega
  obtain⟨g,b⟩ : ∃g,gs[k]?=some g:=⟨gs[k],jK d⟩;have hstep_le:=n8 (m:=m) (init:=init) b;have hstep_ge:(u1 m gs init k).2.length<=(u1 m gs init (k+1)).2.length:=by rw[f3 m gs init k g b];simp[qa]
  rw[List.range_succ,List.filter_append,kE]
  simp only[List.filter_cons,List.filter_nil];by_cases c:(u1 m gs init (k+1)).2.length=(u1 m gs init k).2.length
  . simp only[c,decide_true,↓reduceIte,List.length_singleton];omega
  . simp only[c,decide_false,jV,↓reduceIte,pC];omega
lemma e9 {m:Nat}{gs:U}{init:List o1}(S:M)(g:S.Nodup) (h:∀q∈S,q < gs.length/\(u1 m gs init (q+1)).2.length=(u1 m gs init q).2.length):(u4 m gs (init,[])).2.length+S.length<=gs.length:=by
 have i:=sj m gs init gs.length le_rfl;have j:u1 m gs init gs.length=u4 m gs (init,[]):=by unfold u1;rw[jQ]
 rw[j] at i;set F:=(range gs.length).filter (fun q=>decide ((u1 m gs init (q+1)).2.length=(u1 m gs init q).2.length));have s:∀q∈S,q∈F:=by intro q t;simp only[F,List.mem_filter,jF,decide_eq_true_eq];exact h q t
 have hle:S.length<=F.length:=by
  have u:∀(A B:M),A.Nodup->(∀x∈A,x∈B)->A.length<=B.length:=by
   intro A;induction A with
   | nil=>intro _ _ _;simp
   | cons a v ih =>
    intro B y b;obtain⟨z,h0⟩:=List.nodup_cons.1 y;have h3:a∈B:=b a (jP ..);have c:=List.perm_cons_erase h3;have h4:∀x∈v,x∈B.erase a:=by
     intro x d;have h5:x≠a:=fun e=>z (e ▸ d)
     have h6:x∈B:=b x (hX _ d);exact (kC.1 (c.mem_iff.1 h6)).resolve_left h5
    have h1:=ih (B.erase a) h0 h4;have h2:=c.length_eq;simp at h2 ⊢;omega
  exact u S F g s
 omega
lemma i3 {gs:U}{o b:Nat}(d:gY 8 fG gs o)(hpg_lt:b < gs.length) (s:∀x:F 8,x 7=true->e5 gs 8 (8+b) x=true) (B:Nat->Prop)(h0:B 4) (hBpg:¬B (8+b)) (h3:∀q < gs.length,∀g,gs[q]?=some g->(∃u∈g.inputs,B u)->q=b\/B (8+q)) (h4:¬B o):False:=by
 let x0:F 8:=fun i=>i=7
 let x1:F 8:=fun i=>i=7||i=4
 have h5:fG x0=false:=by decide
 have h6:fG x1=true:=by decide
 have h7:∀p≤ gs.length,∀i < 8+p,¬B i ->
   (q3 (gs.take p) (ofFn x0)).getD i false =
   (q3 (gs.take p) (ofFn x1)).getD i false:=by
  intro p;induction p with
  | zero =>
   intro _ i hi e;simp only[List.take_zero,q3,List.foldl_nil];have hne4:i≠4:=fun h=>e (h ▸ h0)
   interval_cases i<;>simp[x0,x1] at *
  | succ p ih =>
   intro hp i hi e;have j:p < gs.length:=by omega
   have t:gs.take (p+1)=gs.take p++[gs[p]]:=List.take_succ_eq_append_getElem j;rw[t,zd,zd]
   have h8:(q3 (gs.take p) (ofFn x0)).length=8+p:=(by rw[qu];simp[pB,jR (by omega:p<=gs.length)]);have h9:(q3 (gs.take p) (ofFn x1)).length=8+p:=(by rw[qu];simp[pB,jR (by omega:p<=gs.length)]);by_cases x2:i=8+p
   . subst x2;by_cases v:p=b
     . subst v;have y:(q3 (gs.take (p+1)) (ofFn x0)).getD (8+p) false=e5 gs 8 (8+p) x0:=by
        unfold e5;conv_rhs=>rw[<- List.take_append_drop (p+1) gs,zd]
        symm;exact ve (gs.drop (p+1)) _ (8+p) (by rw[qu];simp[pB,jR (by omega:p+1<=gs.length)])
       have z:(q3 (gs.take (p+1)) (ofFn x1)).getD (8+p) false=e5 gs 8 (8+p) x1:=by
        unfold e5;conv_rhs=>rw[<- List.take_append_drop (p+1) gs,zd]
        symm;exact ve (gs.drop (p+1)) _ (8+p) (by rw[qu];simp[pB,jR (by omega:p+1<=gs.length)])
       rw[t,zd] at y z;rw[y,z,s x0 (by decide),s x1 (by decide)]
     . show (q3 (gs.take p) (ofFn x0)++[_]).getD (8+p) false =
           (q3 (gs.take p) (ofFn x1)++[_]).getD (8+p) false
       rw[z2 _ _ _ _ h8,z2 _ _ _ _ h9]
       congr 1
       apply jH
       intro u hu;have x3:u < 8+p:=j2 (d.gP p gs[p] (jK j)) u hu;have a1:¬B u:=by
        intro a2;rcases h3 p j gs[p] (jK j) ⟨u,hu,a2⟩ with c|h2
        . exact v c
        . exact e h2
       exact ih (by omega) u x3 a1
   . show (q3 (gs.take p) (ofFn x0)++[_]).getD i false =
          (q3 (gs.take p) (ofFn x1)++[_]).getD i false
     rw[q8 _ _ _ _ (by omega),q8 _ _ _ _ (by omega)]
     exact ih (by omega) i (by omega) e
 have c:=h7 gs.length le_rfl o d.ho h4;rw[jQ] at c;have e0:e5 gs 8 o x0=fG x0:=d.gQ x0;have e1:e5 gs 8 o x1=fG x1:=d.gQ x1;unfold e5 at e0 e1;rw[e0,e1,h5,h6] at c;cases c
lemma u8 {m:Nat}{gs:U}{init:List o1}{p q a:Nat}(b:p<=q)(hq:q<=gs.length)(c:a < init.length+p):(u1 m gs init q).1.getD a (inl false)=(u1 m gs init p).1.getD a (inl false):=by
 have d:(gs.take q).take p=gs.take p:=by rw[List.take_take,jR b]
 have e:gs.take q=gs.take p++(gs.take q).drop p:=by rw[<- d];exact (List.take_append_drop p (gs.take q)).symm
 unfold u1;conv_lhs=>rw[e,jz]
 apply wy
 rw[nh,pB,jR (by omega)]
 exact c
lemma u7 {m:Nat}{gs:U}{init:List o1}{p:Nat}{g:G}(c:init.length=8)(b:gs[p]?=some g):(u1 m gs init (p+1)).1.getD (8+p) (inl false)=(qg g.op (m+(u1 m gs init p).2.length) (g.inputs.map fun i=>(u1 m gs init p).1.getD i (inl false))).2:=by
 have hlt:p < gs.length:=(jJ.1 b).1;rw[f3 m gs init p g b]
 simp only[qa];have d:(u1 m gs init p).1.length=8+p:=by rw[sn m gs init p (by omega),c]
 rw[z2 _ _ _ _ d]
lemma m5 (b:Nat)(s:o1):(qg GateOp.and b [inl false,s]).2=inl false:=by cases s<;>rfl
lemma m4 (c:Nat)(s:o1):(qg GateOp.and c [s,inl false]).2=inl false:=by cases s with|inl b=>cases b<;>rfl|inr _=>rfl
lemma n4 (b:Nat)(c:Q):(qg GateOp.and b [inl true,inl c]).2=inl c/\(qg GateOp.and b [inl c,inl true]).2=inl c:=by cases c<;>exact⟨rfl,rfl⟩
lemma w7 (c:Nat)(s:o1):(qg GateOp.or c [inl true,s]).2=inl true:=by cases s with|inl b=>cases b<;>rfl|inr _=>rfl
lemma w6 (c:Nat)(s:o1):(qg GateOp.or c [s,inl true]).2=inl true:=by cases s with|inl b=>cases b<;>rfl|inr _=>rfl
lemma e3 {m:Nat}{gs:U}{o p u:Nat}(init:List o1) (d:(F m)->(F 8)) {e:Z m}(h:gY 8 fG gs o)(v:init.length=8) (z:∀x,tu m (ofFn x) (ofFn (d x)) (init,[])) (h0:∀x,fG (d x)=e x) (h1:∃x y,e x≠e y)(hp:p<=gs.length)(i:u∈u0 gs 8 o p){c:Q} (j:(u1 m gs init p).1.getD u (inl false)=inl c):∃q,p<=q/\q < gs.length/\∃g',gs[q]?=some g'/\u∈g'.inputs/\(u1 m gs init (q+1)).2.length=(u1 m gs init q).2.length:=by
 obtain⟨q,s,g',b',t⟩:=tf init d h v z h0 h1 hp i j;have h2:q < gs.length:=(jJ.1 b').1;have hult:u < 8+p:=((qw gs 8 o p u).1 i).1;have h3:(u1 m gs init q).1.getD u (inl false)=inl c:=by rw[u8 s (by omega) (by omega)];exact j
 exact⟨q,s,h2,g',b',t,e7 b' (us (h.gP q g' b')) t h3⟩
lemma t2 {n:Nat}{f:Z n}{gs:U}{o p:Nat}(b:gY n f gs o)(c:p < gs.length):n+p∈u0 gs n o (p+1):=by obtain⟨g,d⟩ : ∃g,gs[p]?=some g:=⟨gs[p],jK c⟩;exact (pb n gs o b.gP p g d (b.gR p c) (n+p)).2 (Or.inl rfl)
lemma x9 {gs:U}{o:Nat}(b:gY 8 fG gs o)(v:Fin 8) (c:∃x:F 8,fG (update x v (!x v))≠fG x):(v:Nat)∈u0 gs 8 o 0:=
 rh b.gQ v c
structure gZ (gs:U) (o:Nat):Type where
 ak:gs.length=13
 pg:Nat
 pr:Nat
 pw:Nat
 bj:Q
 bx:pg < 13
 cf:pr < 13
 eD:pw < 13
 eE:pg < pr
 eF:pw≠pg
 eG:pw≠pr
 eH:bj=true->pr < pw
 eJ:o≠7
 eK:o≠4
 eM:o≠8+pg
 eN:bj=true->o≠8+pr
 eP:∀q g,gs[q]?=some g->(7:Nat)∈g.inputs->q=pg
 eQ:∃g h,gs[pg]?=some g/\g.op=GateOp.or/\(g.inputs=[7,h]\/g.inputs=[h,7])/\h≠7/\h≠4
 eR:∀q g,gs[q]?=some g->8+pg∈g.inputs->q=pr
 eS:∃g u,gs[pr]?=some g/\g.op=GateOp.and/\(g.inputs=[8+pg,u]\/g.inputs=[u,8+pg])/\u≠8+pg/\(bj=true↔u=4)
 eT:∀q g,gs[q]?=some g->(4:Nat)∈g.inputs->q=if bj then pr else pw
 eU:bj=true->∀q g,gs[q]?=some g->8+pr∈g.inputs->q=pw
 eV:∃g v,gs[pw]?=some g/\g.op=GateOp.or /\
  (let src:=if bj then 8+pr else 4
   (g.inputs=[src,v]\/g.inputs=[v,src])/\v≠src)
 eX:(u4 6 gs (u5,[])).2.length=10
 eY:∀q < 13,
  (u1 6 gs u5 (q+1)).2.length=(u1 6 gs u5 q).2.length↔(q=pg\/q=pr\/q=pw)
 eZ:∀p≤ 13,(u1 6 gs u5 p).1.getD 7 (inl false)=inl true
 ft:∀p≤ 13,(u1 6 gs u5 p).1.getD 4 (inl false)=inl false
 fA:∀p≤ 13,pg < p->(u1 6 gs u5 p).1.getD (8+pg) (inl false)=inl true
 fB:bj=true->∀p≤ 13,pr < p->(u1 6 gs u5 p).1.getD (8+pr) (inl false)=inl false
 o0:Nat
 fC:(u4 6 gs (u5,[])).1.getD o (inl false)=inr o0
 fD:gY 6 f7 (u4 6 gs (u5,[])).2 o0
lemma sk {gs:U}{o:Nat}(e:gY 8 fG gs o)(hle:gs.length<=13):Nonempty (gZ gs o):=by
 have hlb_70:12<=(u4 7 gs (l6,[])).2.length:=(t5 l6 l9 e.gP e.gQ uf p6 om lb20).2;have hlb_71:11<=(u4 8 gs (d3,[])).2.length:=(t5 d3 (fun x=>update x 7 true) e.gP e.gQ um (fun _=>rfl) ⟨fun _=>false,fun _=>true,by decide⟩ sr).2;have b1:=t5 u5 a9 e.gP e.gQ b4 j6 n0 lb7;have aJ:=t5 c5 eh e.gP e.gQ dt te n0 lb7;have bJ:(7:Nat)∈u0 gs 8 o 0:=x9 e 7 ⟨fun i=>i=4,by decide⟩;have bK:(u1 7 gs l6 0).1.getD 7 (inl false)=inl false:=rfl;obtain⟨pg,_,h5,gg,h6,c2,m2⟩:=e3 l6 l9 e rfl uf p6 om (by omega) bJ bK;have aK:gs.length=13:=by have h4:=e9 (m:=7) (init:=l6) [pg] (by simp) (fun x b=>by simp at b;subst b;exact⟨h5,m2⟩);simp at h4;omega
 have hpg_lt:pg < 13:=by omega
 have ho_ne_7:o≠7:=by
  intro h8;have m3:=(t5 l6 l9 e.gP e.gQ uf p6 om lb20).1 false;have ha:(u4 7 gs (l6,[])).1.getD 7 (inl false)=inl false:=by
    have:=u8 (m:=7) (gs:=gs) (init:=l6) (p:=0) (q:=gs.length) (a:=7) (by omega) le_rfl (by simp[l6])
    unfold u1 at this;rw[jQ] at this;exact this
  exact m3 (h8 ▸ ha)
 have h7_read:∀q g,gs[q]?=some g->(7:Nat)∈g.inputs->q=pg:=by
  intro q g h0 bL;by_contra hy;have b0:q < gs.length:=(jJ.1 h0).1;have bM:(u1 7 gs l6 q).1.getD 7 (inl false)=inl false:=u8 (p:=0) (by omega) (by omega) (by simp[l6]);have a1:=e7 h0 (us (e.gP q g h0)) bL bM;have h4:=e9 (m:=7) (init:=l6) [pg,q] (by simp[Ne.symm hy])
    (by
        intro x b;rcases kC.1 b with rfl|b
        . exact⟨h5,m2⟩
        . simp at b;subst b;exact⟨b0,a1⟩)
  simp at h4;omega
 have bN:∃h,gg.op=GateOp.or/\(gg.inputs=[7,h]\/gg.inputs=[h,7])/\h≠7:=by
  have p0:(u1 7 gs l6 pg).1.getD 7 (inl false)=inl false:=u8 (p:=0) (by omega) (by omega) (by simp[l6]);have hz:∀c:Q,(u1 7 gs l6 (pg+1)).1.getD (8+pg) (inl false)≠inl c:=by
    intro c hc;have bP:8+pg∈u0 gs 8 o (pg+1):=t2 e h5;obtain⟨q,bQ,b0,gq,hh,c3,a1⟩:=e3 l6 l9 e rfl uf p6 om (by omega) bP hc;have h4:=e9 (m:=7) (init:=l6) [pg,q] (by simp;omega)
      (by
          intro x b;rcases kC.1 b with rfl|b
          . exact⟨h5,m2⟩
          . simp at b;subst b;exact⟨b0,a1⟩)
    simp at h4;omega
  rcases e.gP pg gg h6 with ⟨t,j,hj,d⟩|⟨t,j,k,hj,hk,d⟩
  . have bR:j=7:=(by simp[d] at c2;exact c2.symm);exfalso;apply hz true
    have h3:=u7 (m:=7) (init:=l6) rfl h6;rw[h3,t,d,bR];simp only[kB,mS,p0];rfl
  . have p1:j≠k:=by
      intro h8;subst h8;apply e.gT pg h5 j hj
      funext x;rw[dn 8 gs pg gg h6 (j2 (e.gP pg gg h6)) x,d]
      rcases t with t|t<;>rw[t]<;>simp[GateOp.eval]
    rcases t with t|t
    . exfalso;apply hz false
      have h3:=u7 (m:=7) (init:=l6) rfl h6;rw[h3,t,d];simp only[kB,mS];rw[d] at c2;simp only[kC,jC,or_false] at c2;rcases c2 with z|z
      . rw[<- z,p0];exact m5 _ _
      . rw[<- z,p0];exact m4 _ _
    . rw[d] at c2;simp only[kC,jC,or_false] at c2;rcases c2 with z|z
      . exact⟨k,t,Or.inl (by rw[z];exact d),by omega⟩
      . exact⟨j,t,Or.inr (by rw[z];exact d),by omega⟩
 obtain⟨aL,hn,he,bS⟩:=bN;have aM:(u1 8 gs d3 (pg+1)).2.length=(u1 8 gs d3 pg).2.length:=by have r2:(u1 8 gs d3 pg).1.getD 7 (inl false)=inl true:=u8 (p:=0) (by omega) (by omega) (by simp[d3]);exact e7 h6 (us (e.gP pg gg h6)) c2 r2
 have g2:(u1 8 gs d3 (pg+1)).1.getD (8+pg) (inl false)=inl true:=by
  have r2:(u1 8 gs d3 pg).1.getD 7 (inl false)=inl true:=u8 (p:=0) (by omega) (by omega) (by simp[d3]);have h3:=u7 (m:=8) (init:=d3) rfl h6;rw[h3,hn]
  rcases he with d|d<;>rw[d]<;>simp only[kB,mS,r2]
  . exact w7 _ _
  . exact w6 _ _
 have r3:∃x y:F 8,fG (update x 7 true)≠fG (update y 7 true):=⟨fun _=>false,fun _=>true,by decide⟩;obtain⟨pr,hpr_ge,h9,gr,x2,d1,aN⟩:=
  e3 d3 (fun x=>update x 7 true) e rfl um (fun _=>rfl) r3
    (by omega) (t2 e h5) g2
 have hpr_lt:pr < 13:=by omega
 have hpg_pr:pg < pr:=by omega
 have ho_ne_pg:o≠8+pg:=by
  intro h8;have m3:=(t5 d3 (fun x=>update x 7 true) e.gP e.gQ um (fun _=>rfl) r3 sr).1 true;have ha:(u4 8 gs (d3,[])).1.getD (8+pg) (inl false)=inl true:=by
    have:=u8 (m:=8) (gs:=gs) (init:=d3) (p:=pg+1) (q:=gs.length)
      (a:=8+pg) (by omega) le_rfl (by simp[d3])
    unfold u1 at this;rw[jQ] at this;rw[this];exact g2
  exact m3 (h8 ▸ ha)
 have hpg_read:∀q g,gs[q]?=some g->8+pg∈g.inputs->q=pr:=by
  intro q g h0 c3;by_contra hy;have b0:q < gs.length:=(jJ.1 h0).1;have aP:pg < q:=by have:=j2 (e.gP q g h0) (8+pg) c3;omega
  have bT:(u1 8 gs d3 q).1.getD (8+pg) (inl false)=inl true:=(by rw[u8 (p:=pg+1) (by omega) (by omega) (by simp[d3])];exact g2);have a1:=e7 h0 (us (e.gP q g h0)) c3 bT;have h4:=e9 (m:=8) (init:=d3) [pg,pr,q]
    (by simp;omega)
    (by
        intro x b;rcases kC.1 b with rfl|b;. exact⟨h5,aM⟩
        rcases kC.1 b with rfl|b;. exact⟨h9,aN⟩
        simp at b;subst b;exact⟨b0,a1⟩)
  simp at h4;omega
 have bU:∃u,gr.op=GateOp.and/\(gr.inputs=[8+pg,u]\/gr.inputs=[u,8+pg])/\u≠8+pg:=by
  have hf:(u1 8 gs d3 pr).1.getD (8+pg) (inl false)=inl true:=(by rw[u8 (p:=pg+1) (by omega) (by omega) (by simp[d3])];exact g2);have hz:∀c:Q,(u1 8 gs d3 (pr+1)).1.getD (8+pr) (inl false)≠inl c:=by
    intro c hc;obtain⟨q,bQ,b0,gq,hh,c3,a1⟩:=
      e3 d3 (fun x=>update x 7 true) e rfl um (fun _=>rfl) r3
        (by omega) (t2 e h9) hc
    have h4:=e9 (m:=8) (init:=d3) [pg,pr,q] (by simp;omega)
      (by
          intro x b;rcases kC.1 b with rfl|b;. exact⟨h5,aM⟩
          rcases kC.1 b with rfl|b;. exact⟨h9,aN⟩
          simp at b;subst b;exact⟨b0,a1⟩)
    simp at h4;omega
  rcases e.gP pr gr x2 with ⟨t,j,hj,d⟩|⟨t,j,k,hj,hk,d⟩
  . have r4:j=8+pg:=(by simp[d] at d1;exact d1.symm);exfalso;apply hz false
    have h3:=u7 (m:=8) (init:=d3) rfl x2;rw[h3,t,d,r4];simp only[kB,mS,hf];rfl
  . have p1:j≠k:=by
      intro h8;subst h8;apply e.gT pr h9 j hj
      funext x;rw[dn 8 gs pr gr x2 (j2 (e.gP pr gr x2)) x,d]
      rcases t with t|t<;>rw[t]<;>simp[GateOp.eval]
    rcases t with t|t
    . rw[d] at d1;simp only[kC,jC,or_false] at d1;rcases d1 with z|z
      . exact⟨k,t,Or.inl (by rw[z];exact d),by omega⟩
      . exact⟨j,t,Or.inr (by rw[z];exact d),by omega⟩
    . exfalso;apply hz true
      have h3:=u7 (m:=8) (init:=d3) rfl x2;rw[h3,t,d];simp only[kB,mS];rw[d] at d1;simp only[kC,jC,or_false] at d1;rcases d1 with z|z
      . rw[<- z,hf];exact w7 _ _
      . rw[<- z,hf];exact w6 _ _
 obtain⟨xi,xs,hd,bV⟩:=bU;have aQ:∀x:F 8,x 7=true->e5 gs 8 (8+pg) x=true:=by
  intro x bW;rw[dn 8 gs pg gg h6 (j2 (e.gP pg gg h6)) x,hn]
  have bX:e5 gs 8 7 x=true:=(by unfold e5;rw[ve _ _ _ (by simp)];simp[bW]);rcases he with d|d<;>rw[d]<;>simp[GateOp.eval,bX]
 have ho_ne_4:o≠4:=by
  intro h8;have ha:(u4 6 gs (u5,[])).1.getD 4 (inl false)=inl false:=by
    have:=u8 (m:=6) (gs:=gs) (init:=u5) (p:=0) (q:=gs.length) (a:=4) (by omega) le_rfl (by simp[u5])
    unfold u1 at this;rw[jQ] at this;exact this
  exact b1.1 false (h8 ▸ ha)
 have r5:aL≠4:=by
  intro bY;subst bY;have aS:(u1 6 gs c5 pg).1.getD 7 (inl false)=inl false:=u8 (p:=0) (by omega) (by omega) (by simp[c5]);have j0:∀p≤ 13,(u1 6 gs c5 p).1.getD 4 (inl false)=inl false:=fun p hp=>u8 (p:=0) (by omega) (by omega) (by simp[c5])
  have aT:(u1 6 gs c5 (pg+1)).2.length=(u1 6 gs c5 pg).2.length:=e7 h6 (us (e.gP pg gg h6)) c2 aS;have bZ:(u1 6 gs c5 (pg+1)).1.getD (8+pg) (inl false)=inl false:=by
    have h3:=u7 (m:=6) (init:=c5) rfl h6;rw[h3,hn]
    rcases he with d|d<;>rw[d]<;>simp only[kB,mS,aS,j0 pg (by omega)]<;>rfl
  have aU:(u1 6 gs c5 pr).1.getD (8+pg) (inl false)=inl false:=(by rw[u8 (p:=pg+1) (by omega) (by omega) (by simp[c5])];exact bZ);have aV:(u1 6 gs c5 (pr+1)).2.length=(u1 6 gs c5 pr).2.length:=e7 x2 (us (e.gP pr gr x2)) d1 aU;have aW:(u1 6 gs c5 (pr+1)).1.getD (8+pr) (inl false)=inl false:=by
    have h3:=u7 (m:=6) (init:=c5) rfl x2;rw[h3,xs]
    rcases hd with d|d<;>rw[d]<;>simp only[kB,mS,aU]
    . exact m5 _ _
    . exact m4 _ _
  obtain⟨q3,hq3_ge,s2,g3,s6,hr,aX⟩:=
    e3 c5 eh e rfl dt te n0
      (by omega) (t2 e h9) aW
  have cA:∃q4 < 13,q4≠pg/\∃g4,gs[q4]?=some g4/\(4:Nat)∈g4.inputs:=by
    by_contra aY;push Not at aY
    apply i3 e h5 aQ (fun i=>i=4) rfl (by omega) _ ho_ne_4
    intro q hq g h0 ⟨u,hu,t0⟩;subst t0;by_cases hs:q=pg
    . exact Or.inl hs
    . exact absurd hu (aY q (by omega) hs g h0)
  obtain⟨q4,ht,hq4_ne_pg,g4,hv,hb⟩:=cA;have hq4_ne_pr:q4≠pr:=by
    intro h8;rw[h8,x2] at hv;cases hv
    have f2:xi=4:=by rcases hd with d|d<;>rw[d] at hb<;>simp only[kC,jC,or_false] at hb<;>omega
    apply e.gT pr h9 4 (by omega)
    funext x;have cB:e5 gs 8 (8+pg) x=(e5 gs 8 7 x||e5 gs 8 4 x):=by
      rw[dn 8 gs pg gg h6 (j2 (e.gP pg gg h6)) x,hn]
      rcases he with d|d<;>rw[d]<;>simp[GateOp.eval,Bool.or_comm]
    rw[dn 8 gs pr gr x2 (j2 (e.gP pr gr x2)) x,xs]
    rcases hd with d|d<;>rw[d,f2] <;>
      (simp only[kB,mS,GateOp.eval,cB];cases e5 gs 8 7 x<;>cases e5 gs 8 4 x<;>rfl)
  have cC:(u1 6 gs c5 (q4+1)).2.length=(u1 6 gs c5 q4).2.length:=e7 hv (us (e.gP q4 g4 hv)) hb (j0 q4 (by omega));by_cases cD:q4=q3
  . subst cD;rw[s6] at hv;cases hv
    have aZ:(u1 6 gs c5 q4).1.getD (8+pr) (inl false)=inl false:=(by rw[u8 (p:=pr+1) (by omega) (by omega) (by simp[c5])];exact aW);have cE:(u1 6 gs c5 (q4+1)).1.getD (8+q4) (inl false)=inl false:=by
      have h3:=u7 (m:=6) (init:=c5) rfl s6;rw[h3]
      rcases e.gP q4 g3 s6 with ⟨t,j,_,d⟩|⟨t,j,k,_,_,d⟩
      . rw[d] at hr hb;simp at hr hb;omega
      . rw[d] at hr hb;simp only[kC,jC,or_false] at hr hb;have t1:(u1 6 gs c5 q4).1.getD j (inl false)=inl false:=by
          rcases hr with z|z
          . rw[<- z];exact aZ
          . rcases hb with h2|h2
            . rw[<- h2];exact j0 q4 (by omega)
            . omega
        have v2:(u1 6 gs c5 q4).1.getD k (inl false)=inl false:=by
          rcases hr with z|z
          . rcases hb with h2|h2
            . omega
            . rw[<- h2];exact j0 q4 (by omega)
          . rw[<- z];exact aZ
        rw[d];simp only[kB,mS,t1,v2];rcases t with t|t<;>rw[t]<;>rfl
    obtain⟨q5,hq5_ge,cF,_,_,_,cH⟩:=
      e3 c5 eh e rfl dt te n0
        (by omega) (t2 e s2) cE
    have h4:=e9 (m:=6) (init:=c5) [pg,pr,q4,q5] (by simp;omega)
      (by
          intro x b;rcases kC.1 b with rfl|b;. exact⟨h5,aT⟩
          rcases kC.1 b with rfl|b;. exact⟨h9,aV⟩
          rcases kC.1 b with rfl|b;. exact⟨s2,aX⟩
          simp at b;subst b;exact⟨cF,cH⟩)
    have:=aJ.2;simp at h4;omega
  . have h4:=e9 (m:=6) (init:=c5) [pg,pr,q3,q4] (by simp;omega)
      (by
          intro x b;rcases kC.1 b with rfl|b;. exact⟨h5,aT⟩
          rcases kC.1 b with rfl|b;. exact⟨h9,aV⟩
          rcases kC.1 b with rfl|b;. exact⟨s2,aX⟩
          simp at b;subst b;exact⟨by omega,cC⟩)
    have:=aJ.2;simp at h4;omega
 have h10_7:∀p≤ 13,(u1 6 gs u5 p).1.getD 7 (inl false)=inl true:=fun p hp=>u8 (p:=0) (by omega) (by omega) (by simp[u5])
 have h10_4:∀p≤ 13,(u1 6 gs u5 p).1.getD 4 (inl false)=inl false:=fun p hp=>u8 (p:=0) (by omega) (by omega) (by simp[u5])
 have d2:(u1 6 gs u5 (pg+1)).2.length=(u1 6 gs u5 pg).2.length:=e7 h6 (us (e.gP pg gg h6)) c2 (h10_7 pg (by omega));have cJ:(u1 6 gs u5 (pg+1)).1.getD (8+pg) (inl false)=inl true:=by
  have h3:=u7 (m:=6) (init:=u5) rfl h6;rw[h3,hn]
  rcases he with d|d<;>rw[d]<;>simp only[kB,mS,h10_7 pg (by omega)]
  . exact w7 _ _
  . exact w6 _ _
 have h10_pg:∀p≤ 13,pg < p->(u1 6 gs u5 p).1.getD (8+pg) (inl false)=inl true:=by intro p hp cK;rw[u8 (p:=pg+1) (by omega) (by omega) (by simp[u5])];exact cJ
 have e0:(u1 6 gs u5 (pr+1)).2.length=(u1 6 gs u5 pr).2.length:=e7 x2 (us (e.gP pr gr x2)) d1 (h10_pg pr (by omega) hpg_pr);have w0:∀g,gs[pg]?=some g->(4:Nat) ∉ g.inputs:=by
  intro g h0 h7;rw[h6] at h0;cases h0
  rcases he with d|d<;>rw[d] at h7<;>simp at h7
  . exact r5 h7.symm
  . exact r5 h7.symm
 have bA:∀(pw:Nat) (caseA:Q),
    pw < 13->pw≠pg->pw≠pr->(caseA=true->pr < pw) ->
    (caseA=true->o≠8+pr) ->
    (caseA=true↔xi=4) ->
    (∀q g,gs[q]?=some g->(4:Nat)∈g.inputs->q=if caseA then pr else pw) ->
    (caseA=true->∀q g,gs[q]?=some g->8+pr∈g.inputs->q=pw) ->
    (∃g v,gs[pw]?=some g/\g.op=GateOp.or/\(let aA:=if caseA then 8+pr else 4
      (g.inputs=[aA,v]\/g.inputs=[v,aA])/\v≠aA)) ->
    (u1 6 gs u5 (pw+1)).2.length=(u1 6 gs u5 pw).2.length ->
    (caseA=true->∀p≤ 13,pr < p->(u1 6 gs u5 p).1.getD (8+pr) (inl false)=inl false) ->
    Nonempty (gZ gs o):=by
  intro pw caseA hpw_lt cL cM hcaseA_lt ho_ne_pr cN hw aB hpw_or aC h10_pr;have cP:=e9 (m:=6) (init:=u5) [pg,pr,pw] (by simp;omega)
    (by
        intro x b;rcases kC.1 b with rfl|b;. exact⟨h5,d2⟩
        rcases kC.1 b with rfl|b;. exact⟨h9,e0⟩
        simp at b;subst b;exact⟨by omega,aC⟩)
  have h10_len:(u4 6 gs (u5,[])).2.length=10:=(by have:=b1.2;simp at cP;omega);have h10_elim_iff:∀q < 13,
      (u1 6 gs u5 (q+1)).2.length=(u1 6 gs u5 q).2.length↔(q=pg\/q=pr\/q=pw):=by
    intro q hq;constructor
    . intro cQ;by_contra cR;push Not at cR
      have cS:=e9 (m:=6) (init:=u5) [pg,pr,pw,q] (by simp;omega)
        (by
            intro x b;rcases kC.1 b with rfl|b;. exact⟨h5,d2⟩
            rcases kC.1 b with rfl|b;. exact⟨h9,e0⟩
            rcases kC.1 b with rfl|b;. exact⟨by omega,aC⟩
            simp at b;subst b;exact⟨by omega,cQ⟩)
      simp at cS;omega
    . rintro (rfl|rfl|rfl)
      . exact d2
      . exact e0
      . exact aC
  cases j1:(u4 6 gs (u5,[])).1.getD o (inl false) with
  | inl c=>exact absurd j1 (b1.1 c)
  | inr o0 =>
    have bB:∀x,tu 6 (ofFn x) (q3 gs (ofFn (a9 x))) (u4 6 gs (u5,[])):=fun x=>j7 6 _ (by simp) gs _ _ (fun g hg=>(ja e.gP g hg).1) (b4 x)
    have cT:o0 < 6+(u4 6 gs (u5,[])).2.length:=(by have:=((bB (fun _=>false)).2 o).1;rw[j1] at this;exact this);have cU:yq 6 (u4 6 gs (u5,[])).2:=by
      apply rn 6 gs (u5,[]) (fun g hg=>(ja e.gP g hg).1) _ (fun p g hp=>by simp at hp)
      intro i;exact ((b4 (fun _=>false)).2 i).1
    have cV:∀x,e5 (u4 6 gs (u5,[])).2 6 o0 x=f7 x:=by
      intro x
      have:=((bB x).2 o).2.trans ((e.gQ (a9 x)).trans (j6 x))
      rw[j1] at this;exact this
    have hm0:gY 6 f7 (u4 6 gs (u5,[])).2 o0:=dr cU cT cV n0 (fun s hc=>by rw[h10_len];exact lb7 s hc);exact⟨⟨aK,pg,pr,pw,caseA,hpg_lt,hpr_lt,hpw_lt,hpg_pr,cL,cM,hcaseA_lt,ho_ne_7,ho_ne_4,ho_ne_pg,ho_ne_pr,h7_read,⟨gg,aL,h6,hn,he,bS,r5⟩,hpg_read,⟨gr,xi,x2,xs,hd,bV,cN⟩,hw,aB,hpw_or,h10_len,h10_elim_iff,h10_7,h10_4,h10_pg,h10_pr,o0,j1,hm0⟩⟩
 by_cases f2:xi=4
 .
  have bC:(u1 6 gs u5 (pr+1)).1.getD (8+pr) (inl false)=inl false:=by
    have h3:=u7 (m:=6) (init:=u5) rfl x2;rw[h3,xs]
    rcases hd with d|d<;>rw[d,f2]<;>simp only[kB,mS,h10_4 pr (by omega)]
    . exact m4 _ _
    . exact m5 _ _
  have h10_pr:∀p≤ 13,pr < p->(u1 6 gs u5 p).1.getD (8+pr) (inl false)=inl false:=(by intro p hp cK;rw[u8 (p:=pr+1) (by omega) (by omega) (by simp[u5])];exact bC);have ho_ne_pr:o≠8+pr:=by
    intro h8;have ha:(u4 6 gs (u5,[])).1.getD (8+pr) (inl false)=inl false:=by
      have:=h10_pr 13 le_rfl (by omega)
      unfold u1 at this;rw[<- aK,jQ] at this;exact this
    exact b1.1 false (h8 ▸ ha)
  obtain⟨pw,hpw_ge,b3,gw,x3,a2,e1⟩:=
    e3 u5 a9 e rfl b4 j6 n0
      (by omega) (t2 e h9) bC
  have hpw_lt:pw < 13:=(by omega);have aB:∀q g,gs[q]?=some g->8+pr∈g.inputs->q=pw:=by
    intro q g h0 c3;by_contra hy;have b0:q < gs.length:=(jJ.1 h0).1;have aP:pr < q:=by have:=j2 (e.gP q g h0) (8+pr) c3;omega
    have a1:=e7 h0 (us (e.gP q g h0)) c3 (h10_pr q (by omega) aP);have h4:=e9 (m:=6) (init:=u5) [pg,pr,pw,q] (by simp;omega)
      (by
          intro x b;rcases kC.1 b with rfl|b;. exact⟨h5,d2⟩
          rcases kC.1 b with rfl|b;. exact⟨h9,e0⟩
          rcases kC.1 b with rfl|b;. exact⟨b3,e1⟩
          simp at b;subst b;exact⟨b0,a1⟩)
    have:=b1.2;simp at h4;omega
  have hw:∀q g,gs[q]?=some g->(4:Nat)∈g.inputs->q=pr:=by
    intro q g h0 h7;by_contra hy;have b0:q < gs.length:=(jJ.1 h0).1;have cW:q≠pg:=fun h=>w0 g (h ▸ h0) h7
    have a1:=e7 h0 (us (e.gP q g h0)) h7 (h10_4 q (by omega));by_cases cX:q=pw
    . rw[cX,x3] at h0;cases h0
      have cY:(u1 6 gs u5 (pw+1)).1.getD (8+pw) (inl false)=inl false:=by
        have h3:=u7 (m:=6) (init:=u5) rfl x3;rw[h3]
        rcases e.gP pw gw x3 with ⟨t,j,_,d⟩|⟨t,j,k,_,_,d⟩
        . rw[d] at a2 h7;simp at a2 h7;omega
        . rw[d] at a2 h7;simp only[kC,jC,or_false] at a2 h7;have t1:(u1 6 gs u5 pw).1.getD j (inl false)=inl false:=by
            rcases a2 with z|z
            . rw[<- z];exact h10_pr pw (by omega) (by omega)
            . rcases h7 with h2|h2
              . rw[<- h2];exact h10_4 pw (by omega)
              . omega
          have v2:(u1 6 gs u5 pw).1.getD k (inl false)=inl false:=by
            rcases a2 with z|z
            . rcases h7 with h2|h2
              . omega
              . rw[<- h2];exact h10_4 pw (by omega)
            . rw[<- z];exact h10_pr pw (by omega) (by omega)
          rw[d];simp only[kB,mS,t1,v2];rcases t with t|t<;>rw[t]<;>rfl
      obtain⟨q4,bD,ht,_,_,_,g0⟩:=
        e3 u5 a9 e rfl b4 j6 n0
          (by omega) (t2 e b3) cY
      have h4:=e9 (m:=6) (init:=u5) [pg,pr,pw,q4] (by simp;omega)
        (by
            intro x b;rcases kC.1 b with rfl|b;. exact⟨h5,d2⟩
            rcases kC.1 b with rfl|b;. exact⟨h9,e0⟩
            rcases kC.1 b with rfl|b;. exact⟨b3,e1⟩
            simp at b;subst b;exact⟨ht,g0⟩)
      have:=b1.2;simp at h4;omega
    . have h4:=e9 (m:=6) (init:=u5) [pg,pr,pw,q] (by simp;omega)
        (by
            intro x b;rcases kC.1 b with rfl|b;. exact⟨h5,d2⟩
            rcases kC.1 b with rfl|b;. exact⟨h9,e0⟩
            rcases kC.1 b with rfl|b;. exact⟨b3,e1⟩
            simp at b;subst b;exact⟨b0,a1⟩)
      have:=b1.2;simp at h4;omega
  have hpw_or:∃v,gw.op=GateOp.or/\(gw.inputs=[8+pr,v]\/gw.inputs=[v,8+pr])/\v≠8+pr:=by
    have g1:∀c:Q,(u1 6 gs u5 (pw+1)).1.getD (8+pw) (inl false)≠inl c:=by
      intro c hc;obtain⟨q4,bD,ht,_,_,_,g0⟩:=
        e3 u5 a9 e rfl b4 j6 n0
          (by omega) (t2 e b3) hc
      have h4:=e9 (m:=6) (init:=u5) [pg,pr,pw,q4] (by simp;omega)
        (by
            intro x b;rcases kC.1 b with rfl|b;. exact⟨h5,d2⟩
            rcases kC.1 b with rfl|b;. exact⟨h9,e0⟩
            rcases kC.1 b with rfl|b;. exact⟨b3,e1⟩
            simp at b;subst b;exact⟨ht,g0⟩)
      have:=b1.2;simp at h4;omega
    have hf:=h10_pr pw (by omega) (by omega);rcases e.gP pw gw x3 with ⟨t,j,_,d⟩|⟨t,j,k,hj,hk,d⟩
    . have r4:j=8+pr:=(by simp[d] at a2;exact a2.symm);exfalso;apply g1 true
      have h3:=u7 (m:=6) (init:=u5) rfl x3;rw[h3,t,d,r4];simp only[kB,mS,hf];rfl
    . have p1:j≠k:=by
        intro h8;subst h8;apply e.gT pw b3 j hj
        funext x;rw[dn 8 gs pw gw x3 (j2 (e.gP pw gw x3)) x,d]
        rcases t with t|t<;>rw[t]<;>simp[GateOp.eval]
      rcases t with t|t
      . exfalso;apply g1 false
        have h3:=u7 (m:=6) (init:=u5) rfl x3;rw[h3,t,d];simp only[kB,mS];rw[d] at a2;simp only[kC,jC,or_false] at a2;rcases a2 with z|z
        . rw[<- z,hf];exact m5 _ _
        . rw[<- z,hf];exact m4 _ _
      . rw[d] at a2;simp only[kC,jC,or_false] at a2;rcases a2 with z|z
        . exact⟨k,t,Or.inl (by rw[z];exact d),by omega⟩
        . exact⟨j,t,Or.inr (by rw[z];exact d),by omega⟩
  obtain⟨aD,aE,aF,aG⟩:=hpw_or;exact bA pw true hpw_lt (by omega) (by omega) (fun _=>by omega) (fun _=>ho_ne_pr)
    (by simp[f2]) (by simpa using hw) (fun _=>aB)
    ⟨gw,aD,x3,aE,aF,aG⟩ e1 (fun _=>h10_pr)
 .
  have bE:(4:Nat) ∉ gr.inputs:=by intro h7;rcases hd with d|d<;>rw[d] at h7<;>simp only[kC,jC,or_false] at h7<;>omega
  have cZ:(4:Nat)∈u0 gs 8 o 0:=x9 e 4 ⟨fun i=>i=7,by decide⟩;obtain⟨pw,_,b3,gw,x3,e2,e1⟩:=
    e3 u5 a9 e rfl b4 j6 n0
      (by omega) cZ (h10_4 0 (by omega))
  have hpw_lt:pw < 13:=(by omega);have hpw_ne_pg:pw≠pg:=fun h=>w0 gw (h ▸ x3) e2
  have hpw_ne_pr:pw≠pr:=fun h=>bE (by rw[h,x2] at x3;cases x3;exact e2)
  have hw:∀q g,gs[q]?=some g->(4:Nat)∈g.inputs->q=pw:=by
    intro q g h0 h7;by_contra hy;have b0:q < gs.length:=(jJ.1 h0).1;have cW:q≠pg:=fun h=>w0 g (h ▸ h0) h7
    have hq_ne_pr:q≠pr:=fun h=>bE (by rw[h,x2] at h0;cases h0;exact h7)
    have a1:=e7 h0 (us (e.gP q g h0)) h7 (h10_4 q (by omega));have h4:=e9 (m:=6) (init:=u5) [pg,pr,pw,q] (by simp;omega)
      (by
          intro x b;rcases kC.1 b with rfl|b;. exact⟨h5,d2⟩
          rcases kC.1 b with rfl|b;. exact⟨h9,e0⟩
          rcases kC.1 b with rfl|b;. exact⟨b3,e1⟩
          simp at b;subst b;exact⟨b0,a1⟩)
    have:=b1.2;simp at h4;omega
  have hpw_or:∃v,gw.op=GateOp.or/\(gw.inputs=[4,v]\/gw.inputs=[v,4])/\v≠4:=by
    have g1:∀c:Q,(u1 6 gs u5 (pw+1)).1.getD (8+pw) (inl false)≠inl c:=by
      intro c hc;have dA:∀q < 13,pw < q->q≠pg->∀gq,gs[q]?=some gq->8+pw∈gq.inputs->False:=by
        intro q hq bF hs gq hh c3;have bG:(u1 6 gs u5 q).1.getD (8+pw) (inl false)=inl c:=by rw[u8 (p:=pw+1) (by omega) (by omega) (by simp[u5])];exact hc
        by_cases bH:q=pr
        . rw[bH,x2] at hh;cases hh
          have dB:xi=8+pw:=by rcases hd with d|d<;>rw[d] at c3<;>simp only[kC,jC,or_false] at c3<;>omega
          have dC:(u1 6 gs u5 (pr+1)).1.getD (8+pr) (inl false)=inl c:=by
            have h3:=u7 (m:=6) (init:=u5) rfl x2;rw[h3,xs]
            rcases hd with d|d<;>rw[d,dB] <;>
              simp only[kB,mS,h10_pg pr (by omega) hpg_pr,bH ▸ bG]
            . exact (n4 _ c).1
            . exact (n4 _ c).2
          obtain⟨q4,bD,ht,_,_,_,g0⟩:=
            e3 u5 a9 e rfl b4 j6 n0
              (by omega) (t2 e h9) dC
          have h4:=e9 (m:=6) (init:=u5) [pg,pr,pw,q4] (by simp;omega)
            (by
                intro x b;rcases kC.1 b with rfl|b;. exact⟨h5,d2⟩
                rcases kC.1 b with rfl|b;. exact⟨h9,e0⟩
                rcases kC.1 b with rfl|b;. exact⟨b3,e1⟩
                simp at b;subst b;exact⟨ht,g0⟩)
          have:=b1.2;simp at h4;omega
        . have a1:=e7 hh (us (e.gP q gq hh)) c3 bG;have h4:=e9 (m:=6) (init:=u5) [pg,pr,pw,q] (by simp;omega)
            (by
                intro x b;rcases kC.1 b with rfl|b;. exact⟨h5,d2⟩
                rcases kC.1 b with rfl|b;. exact⟨h9,e0⟩
                rcases kC.1 b with rfl|b;. exact⟨b3,e1⟩
                simp at b;subst b;exact⟨by omega,a1⟩)
          have:=b1.2;simp at h4;omega
      have dD:o≠8+pw:=by
        intro h8;have ha:(u4 6 gs (u5,[])).1.getD (8+pw) (inl false)=inl c:=by
          have:=u8 (m:=6) (gs:=gs) (init:=u5) (p:=pw+1) (q:=gs.length)
            (a:=8+pw) (by omega) le_rfl (by simp[u5])
          unfold u1 at this;rw[jQ] at this;rw[this];exact hc
        exact b1.1 c (h8 ▸ ha)
      apply i3 e h5 aQ (fun i=>i=4\/i=8+pw)
        (Or.inl rfl) (by omega) _ (by rintro (h|h);exact ho_ne_4 h;exact dD h)
      intro q hq g h0 ⟨u,hu,t0⟩;rcases t0 with rfl|rfl
      . exact Or.inr (Or.inr (by rw[hw q g h0 hu]))
      . by_cases hs:q=pg
        . exact Or.inl hs
        . have bF:pw < q:=(by have:=j2 (e.gP q g h0) (8+pw) hu;omega);exact False.elim (dA q (by omega) bF hs g h0 hu)
    have aH:=h10_4 pw (by omega);rcases e.gP pw gw x3 with ⟨t,j,_,d⟩|⟨t,j,k,hj,hk,d⟩
    . have dE:j=4:=(by simp[d] at e2;exact e2.symm);exfalso;apply g1 true
      have h3:=u7 (m:=6) (init:=u5) rfl x3;rw[h3,t,d,dE];simp only[kB,mS,aH];rfl
    . have p1:j≠k:=by
        intro h8;subst h8;apply e.gT pw b3 j hj
        funext x;rw[dn 8 gs pw gw x3 (j2 (e.gP pw gw x3)) x,d]
        rcases t with t|t<;>rw[t]<;>simp[GateOp.eval]
      rcases t with t|t
      . exfalso;apply g1 false
        have h3:=u7 (m:=6) (init:=u5) rfl x3;rw[h3,t,d];simp only[kB,mS];rw[d] at e2;simp only[kC,jC,or_false] at e2;rcases e2 with z|z
        . rw[<- z,aH];exact m5 _ _
        . rw[<- z,aH];exact m4 _ _
      . rw[d] at e2;simp only[kC,jC,or_false] at e2;rcases e2 with z|z
        . exact⟨k,t,Or.inl (by rw[z];exact d),by omega⟩
        . exact⟨j,t,Or.inr (by rw[z];exact d),by omega⟩
  obtain⟨aD,aE,aF,aG⟩:=hpw_or;exact bA pw false hpw_lt hpw_ne_pg hpw_ne_pr (by simp) (by simp)
    (by simp[f2]) (by simpa using hw) (by simp)
    ⟨gw,aD,x3,aE,aF,aG⟩ e1 (by simp)
lemma ez (op:GateOp)(i:Nat)(e:List o1) (g' : G) (r:o1) (h:qg op i e=(some g',r)):r=inr i/\∀b∈g'.inputs,inr b∈e:=by
 cases op with
 | not =>
  match e with
  | []=>simp[qg,wr] at h
  | inl c::tl=>simp[qg,wr] at h
  | inr j::tl=>simp only[qg,wr,Prod.mk.injEq,Option.some.injEq] at h;obtain⟨rfl,rfl⟩:=h;exact⟨rfl,fun b d=>by simp at d;subst d;simp⟩
 | and =>
  match e with
  | []=>simp[qg,ko] at h
  | [inl _] | [inr _]=>simp[qg,ko] at h
  | [inl _,inl _] | [inl _,inr _] | [inr _,inl _]=>simp[qg,ko] at h
  | [inr j1,inr j2]=>simp only[qg,ko,Prod.mk.injEq,Option.some.injEq] at h;obtain⟨rfl,rfl⟩:=h;exact⟨rfl,fun b d=>by simp at d;rcases d with rfl|rfl<;>simp⟩
  | _::_::_::_=>simp[qg,ko] at h
 | or =>
  match e with
  | []=>simp[qg,ji] at h
  | [inl _] | [inr _]=>simp[qg,ji] at h
  | [inl _,inl _] | [inl _,inr _] | [inr _,inl _]=>simp[qg,ji] at h
  | [inr j1,inr j2]=>simp only[qg,ji,Prod.mk.injEq,Option.some.injEq] at h;obtain⟨rfl,rfl⟩:=h;exact⟨rfl,fun b d=>by simp at d;rcases d with rfl|rfl<;>simp⟩
  | _::_::_::_=>simp[qg,ji] at h
 | mod | maj=>simp[qg] at h
lemma me (op:GateOp)(e:Nat)(d:List o1)(b:Nat) (h:qg op e d=(none,inr b)):inr b∈d:=by
 cases op with
 | not =>
  match d with
  | [] | inl _::_ | inr _::_=>simp[qg,wr] at h
 | and =>
  match d with
  | [] | [inl _] | [inl _,inl _] | [inr _,inr _] | _::_::_::_=>simp[qg,ko] at h
  | [inr j]=>simp[qg,ko] at h;subst h;simp
  | [inl c,inr j]=>cases c<;>simp[qg,ko] at h;subst h;simp
  | [inr j,inl c]=>cases c<;>simp[qg,ko] at h;subst h;simp
 | or =>
  match d with
  | [] | [inl _] | [inl _,inl _] | [inr _,inr _] | _::_::_::_=>simp[qg,ji] at h
  | [inr j]=>simp[qg,ji] at h;subst h;simp
  | [inl c,inr j]=>cases c<;>simp[qg,ji] at h;subst h;simp
  | [inr j,inl c]=>cases c<;>simp[qg,ji] at h;subst h;simp
 | mod | maj=>simp[qg] at h
lemma l7 (m:Nat)(gs:U)(init:List o1):∀p≤ gs.length,∃t,(u4 m gs (init,[])).2=(u1 m gs init p).2++t:=by
 intro p _;have c:=(dh m gs init p).symm;have d:∀(l:U) (b:List o1×U),∃t,(u4 m l b).2=b.2++t:=by
  intro l;induction l with
  | nil=>intro b;exact⟨[],by simp[u4]⟩
  | cons g rest ih =>
   intro b;rw[k4]
   obtain⟨t,e⟩:=ih (qa m b g);exact⟨(qg g.op (m+b.2.length) (g.inputs.map fun i=>b.1.getD i (inl false))).1.toList++t,
    by rw[e];simp[qa,kA]⟩
 rw[c];exact d (gs.drop p) (u1 m gs init p)
lemma p2 (m:Nat)(gs:U)(init:List o1){p q:Nat}(hpq:p<=q):(u1 m gs init p).2.length<=(u1 m gs init q).2.length:=by
 induction q with
 | zero=>have b:p=0:=(by omega);subst b;exact le_rfl
 | succ q ih =>
  by_cases h:p=q+1
  . subst h;exact le_rfl
  . have c:=ih (by omega);by_cases d:q < gs.length
    . obtain⟨g,e⟩ : ∃g,gs[q]?=some g:=⟨gs[q],jK d⟩;have hstep:(u1 m gs init q).2.length<=(u1 m gs init (q+1)).2.length:=by rw[f3 m gs init q g e];simp only[qa,kE];omega
      omega
    . have:gs.take (q+1)=gs.take q:=by rw[List.take_of_length_le (by omega),List.take_of_length_le (by omega)]
      have i:u1 m gs init (q+1)=u1 m gs init q:=(by unfold u1;rw[this]);rw[i];exact c
lemma du {gs:U}{p j:Nat}{z:G}(hp:p<=gs.length) (hj_ge:(u1 6 gs u5 p).2.length<=j) (b:(u4 6 gs (u5,[])).2[j]?=some z):∃q,p<=q/\q < gs.length/\(u1 6 gs u5 q).2.length=j/\∃g,gs[q]?=some g/\(qg g.op (6+j) (g.inputs.map fun i=>(u1 6 gs u5 q).1.getD i (inl false))).1=some z:=by
 have h0:j < (u4 6 gs (u5,[])).2.length:=(jJ.1 b).1;have h5:(u1 6 gs u5 gs.length).2=(u4 6 gs (u5,[])).2:=by unfold u1;rw[jQ]
 have h6:∃q,p<=q/\q < gs.length/\(u1 6 gs u5 q).2.length=j /\
   (u1 6 gs u5 (q+1)).2.length=j+1:=by
  suffices ∀k,p+k<=gs.length->j < (u1 6 gs u5 (p+k)).2.length ->
     ∃q,p<=q/\q < p+k/\(u1 6 gs u5 q).2.length=j /\
     (u1 6 gs u5 (q+1)).2.length=j+1 by
   obtain⟨q,s,h2,u,v⟩:=this (gs.length - p) (by omega)
     (by rw[show p+(gs.length - p)=gs.length by omega,h5];exact h0)
   exact⟨q,s,by omega,u,v⟩
  intro k;induction k with
  | zero=>intro _ c;simp at c;omega
  | succ k ih =>
   intro hpk c;by_cases h7:j < (u1 6 gs u5 (p+k)).2.length
   . obtain⟨q,s,h2,u,v⟩:=ih (by omega) h7;exact⟨q,s,by omega,u,v⟩
   . have d:p+k < gs.length:=(by omega);obtain⟨g,e⟩ : ∃g,gs[p+k]?=some g:=⟨gs[p+k],jK d⟩;have hle:=n8 (m:=6) (init:=u5) e;have c' : j < (u1 6 gs u5 (p+k+1)).2.length:=(by simpa[mG] using c);have h8:(u1 6 gs u5 (p+k)).2.length=j:=(by omega);have h9:(u1 6 gs u5 (p+k+1)).2.length=j+1:=(by omega);exact⟨p+k,by omega,by omega,h8,h9⟩
 obtain⟨q,x2,d,x,h⟩:=h6;obtain⟨g,e⟩ : ∃g,gs[q]?=some g:=⟨gs[q],jK d⟩;refine⟨q,x2,d,x,g,e,?_⟩
 have x3:=f3 6 gs u5 q g e;obtain⟨t,ht⟩:=l7 6 gs u5 (q+1) (by omega);rw[ht,mX (by omega)] at b;rw[x3] at b h;simp only[qa] at b h;cases y:(qg g.op (6+(u1 6 gs u5 q).2.length) (g.inputs.map fun i=>(u1 6 gs u5 q).1.getD i (inl false))).1 with
 | none=>rw[y] at h;simp at h;omega
 | some g' => rw[y] at b;rw[mY (by omega),x,Nat.sub_self] at b;simp at b;subst b;rw[<- x];exact y
lemma bh:u5.length=8:=rfl
lemma o9 {gs:U}{p a:Nat}(c:p<=gs.length)(d:a < 8+p):(u4 6 gs (u5,[])).1.getD a (inl false)=(u1 6 gs u5 p).1.getD a (inl false):=by
 have b:=u8 (m:=6) (gs:=gs) (init:=u5) (p:=p) (q:=gs.length) (a:=a)
  c le_rfl (by rw[bh];exact d)
 unfold u1 at b;rw[jQ] at b;exact b
lemma ds {gs:U}{o p b:Nat}(d:gY 8 fG gs o)(S:gZ gs o)(hp:p<=13) (hb:b∈u0 (u4 6 gs (u5,[])).2 6 S.o0 (u1 6 gs u5 p).2.length):∃a∈u0 gs 8 o p,(u1 6 gs u5 p).1.getD a (inl false)=inr b:=by
 have hlen13:=S.ak;have hblt:b < 6+(u1 6 gs u5 p).2.length:=((qw _ _ _ _ _).1 hb).1;have h7:a6 6 (u4 6 gs (u5,[])).2 S.o0 (u1 6 gs u5 p).2.length b:=((qw _ _ _ _ _).1 hb).2;have h8:∃a' < 8+13,a6 8 gs o p a'/\(u4 6 gs (u5,[])).1.getD a' (inl false)=inr b:=by
  rcases h7 with rfl|⟨j,h9,g0,x2,x3,_⟩
  . exact⟨o,by have:=d.ho;omega,Or.inl rfl,S.fC⟩
  . obtain⟨q,h,s,hlenq,g,c,a1⟩:=du (by omega) h9 x2;have u:=ez g.op (6+j) _ g0 _ (Prod.ext a1 rfl);have v:inr b∈g.inputs.map (fun i=>(u1 6 gs u5 q).1.getD i (inl false)):=u.2 b x3;obtain⟨a',h0,x⟩:=mM.1 v;have h4:a' < 8+q:=j2 (d.gP q g c) a' h0;have a2:(u4 6 gs (u5,[])).1.getD a' (inl false)=inr b:=by rw[o9 (by omega) h4];exact x
    exact⟨a',by omega,Or.inr ⟨q,h,g,c,h0,d.gR q s⟩,a2⟩
 suffices ∀n a',a'<=n->a' < 8+13->a6 8 gs o p a' ->
    (u4 6 gs (u5,[])).1.getD a' (inl false)=inr b ->
    ∃a∈u0 gs 8 o p,(u1 6 gs u5 p).1.getD a (inl false)=inr b by
  obtain⟨a',h1,h2,h3⟩:=h8;exact this a' a' le_rfl h1 h2 h3
 intro n;induction n with
 | zero =>
  intro a' ha'0 _ y t;have e:a' < 8+p:=by omega
  exact⟨a',(qw gs 8 o p a').2 ⟨e,y⟩,by rw[<- o9 (by omega) e];exact t⟩
 | succ n ih =>
  intro a' ha'n h4 y t;by_cases e:a' < 8+p
  . exact⟨a',(qw gs 8 o p a').2 ⟨e,y⟩,by rw[<- o9 (by omega) e];exact t⟩
  . set q:=a' - 8;have h:p<=q:=(by omega);have s:q < gs.length:=(by omega);have x:a'=8+q:=(by omega);obtain⟨g,c⟩ : ∃g,gs[q]?=some g:=⟨gs[q],jK s⟩;have b0:(u1 6 gs u5 (q+1)).1.getD (8+q) (inl false)=inr b:=(by rw[<- o9 (by omega) (by omega),<- x];exact t);have z:=u7 (m:=6) (init:=u5) rfl c;rw[b0] at z;cases h5:(qg g.op (6+(u1 6 gs u5 q).2.length) (g.inputs.map fun i=>(u1 6 gs u5 q).1.getD i (inl false))).1 with
    | some g' => have u:=ez _ _ _ g' _ (Prod.ext h5 z.symm);have hbeq:b=6+(u1 6 gs u5 q).2.length:=(by cases u.1;rfl);have hmono:=p2 6 gs u5 h;omega
    | none=>have v:inr b∈g.inputs.map (fun i=>(u1 6 gs u5 q).1.getD i (inl false)):=me _ _ _ b (Prod.ext h5 z.symm);obtain⟨a'',h6,b1⟩:=mM.1 v;have b3:a'' < 8+q:=j2 (d.gP q g c) a'' h6;have c2:(u4 6 gs (u5,[])).1.getD a'' (inl false)=inr b:=(by rw[o9 (by omega) b3];exact b1);exact ih a'' (by omega) (by omega) (Or.inr ⟨q,h,g,c,h6,d.gR q s⟩) c2
lemma oz {gs:U}{o p a b:Nat}(c:gY 8 fG gs o)(d:p<=gs.length)(e:a < 8+p) (h:(u1 6 gs u5 p).1.getD a (inl false)=inr b):a8 (e5 gs 8 a)=e5 (u4 6 gs (u5,[])).2 6 b:=by funext x;have i:tu 6 (ofFn x) (q3 gs (ofFn (a9 x))) (u4 6 gs (u5,[])):=j7 6 _ (by simp) gs _ _ (fun g j=>(ja c.gP g j).1) (b4 x);have hev:=((i.2 a).2).symm;rw[o9 d e,h] at hev;exact hev
lemma m8 {n:Nat}(gs:U){a:Nat}(b:a < n)(x:F n):e5 gs n a x=x ⟨a,b⟩:=by
 unfold e5;rw[ve gs (ofFn x) a (by simp[b])]
 simp[b]
lemma td {n:Nat}{f:Z n}{gs:U}{o:Nat}(j:gY n f gs o){a b:Nat}(ha:a < n+gs.length)(hb:b < n+gs.length)(d:e5 gs n a=e5 gs n b):a=b:=by
 by_contra e;rcases Nat.lt_or_gt_of_ne e with hlt|hgt
 . by_cases g:b < n
   . have h:a < n:=(by omega);have c:=congrFun d (fun i:Fin n=>decide (i.val=a));rw[m8 gs h,m8 gs g] at c;simp at c;exact e c.symm
   . exact j.gT (b - n) (by omega) a (by omega) (by rw[show n+(b - n)=b by omega];exact d.symm)
 . by_cases h:a < n
   . have g:b < n:=(by omega);have c:=congrFun d (fun i:Fin n=>decide (i.val=b));rw[m8 gs h,m8 gs g] at c;simp at c;exact e c
   . exact j.gT (a - n) (by omega) b (by omega) (by rw[show n+(a - n)=a by omega];exact d)
lemma r8 {n:Nat}{f:Z n}{gs:U}{o:Nat}(d:gY n f gs o){a:Nat}(ha:a < n+gs.length)(c:Q):e5 gs n a≠fun _=>c:=by
 by_cases e:a < n
 . intro g;have b:=congrFun g (fun _:Fin n=>!c);rw[m8 gs e] at b;cases c<;>cases b
 . have:=d.gS (a - n) (by omega) c
   rwa[show n+(a - n)=a by omega] at this
def o5 {α : Type}:List (α×Nat)->Nat
 | []=>0
 | (_,tg)::rest =>
  (if tg=4 then 2 else if tg=6\/tg=7\/tg=8 then 1 else 0)+o5 rest
lemma sy {α : Type} {b c:List (α×Nat)}(h:b.Perm c):o5 b=o5 c:=by
 induction h with
 | nil=>rfl
 | cons x _ ih=>simp[o5,ih]
 | swap x y l=>simp[o5];omega
 | trans _ _ ih1 ih2=>exact ih1.trans ih2
lemma tv {α β : Type} (f : α->β) (b:List (α×Nat)):o5 (b.map fun p=>(f p.1,p.2))=o5 b:=by
 induction b with
 | nil=>rfl
 | cons p rest ih=>simp[o5,ih]
def F7Ok (s:Nat)(b:X 8):Prop:=
 o5 b<=s /\
 ∃L0:List (Z 6),
  L0.Nodup /\
  (∀g∈L0,g≠(fun _=>false)/\g≠(fun _=>true)) /\
  (∀g∈L0,∃p∈b,p.2≠4/\p.2≠6/\p.2≠7/\p.2≠8/\a8 p.1=g) /\
  TR f7 (s - o5 b) (L0.map (·,0))
lemma F7Ok.perm {s:Nat}{b c:X 8}(d:b.Perm c)(h:F7Ok s b):F7Ok s c:=by
 obtain⟨e,L0,j,t,u,i⟩:=h;rw[sy d] at e i;refine⟨e,L0,j,t,?_,i⟩
 intro g v;obtain⟨p,x,y,z,h7,h8,h0⟩:=u g v;exact⟨p,d.mem_iff.1 x,y,z,h7,h8,h0⟩
inductive gU:Nat->X 8->Prop where
 | done (tg:Nat):
  F7Ok 0 [(fG,tg)] ->
  gU 0 [(fG,tg)]
 | perm {s xs zs}:xs.Perm zs->gU s xs->gU s zs
 | uNot {s a ta r} (save:Q):
  F7Ok (s+1) ((a,ta)::r) ->
  (ta=0\/ta=3)->(ta=3->save=false) ->
  hC a≠(fun _=>false)->hC a≠(fun _=>true) ->
  hC a≠a->(∀x∈r,x.1≠hC a) ->
  gU s ((hC a,if ta=3 then 2 else 0)::qk save (a,0) r) ->
  gU (s+1) ((a,ta)::r)
 | bOr {s a ta b tb r} (ka kb:Q):
  F7Ok (s+1) ((a,ta)::(b,tb)::r) ->
  ta≠2->tb≠2->ta≠7->tb≠7 ->
  ¬(ta=4/\tb=6)->¬(ta=6/\tb=4) ->
  (ka=true->ta=0\/ta=3)->(kb=true->tb=0\/tb=3) ->
  hG a b≠(fun _=>false)->hG a b≠(fun _=>true) ->
  hG a b≠a->hG a b≠b->(∀x∈r,x.1≠hG a b) ->
  gU s ((hG a b,if ta=4\/tb=4 then 7 else 0)::
   qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)) ->
  gU (s+1) ((a,ta)::(b,tb)::r)
 | bAnd {s a ta b tb r} (ka kb:Q):
  F7Ok (s+1) ((a,ta)::(b,tb)::r) ->
  ta≠1->tb≠1->ta≠4->tb≠4->ta≠8->tb≠8 ->
  (ta=6->tb=7)->(tb=6->ta=7) ->
  (ka=true->ta=0)->(kb=true->tb=0) ->
  hE a b≠(fun _=>false)->hE a b≠(fun _=>true) ->
  hE a b≠a->hE a b≠b->(∀x∈r,x.1≠hE a b) ->
  gU s ((hE a b,if ta=6\/tb=6 then 8 else if ta=3\/tb=3 then 1 else 0)::
   qk ka (a,0) (qk kb (b,0) r)) ->
  gU (s+1) ((a,ta)::(b,tb)::r)
lemma gU.f7Ok {s:Nat}{c:X 8}(h:gU s c):F7Ok s c:=by
 induction h with
 | done _ b=>exact b
 | perm d _ ih=>exact ih.perm d
 | uNot _ b _ _ _ _ _ _ _ _=>exact b
 | bOr _ _ b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _=>exact b
 | bAnd _ _ b _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _=>exact b
lemma gU.toRun {s:Nat}{c:X 8}(h:gU s c):Run (hC (n:=8)) hE hG fG s (c.map fst):=by
 induction h with
 | done _ _=>exact Run.done
 | perm d _ ih=>exact Run.perm (d.map fst) ih
 | @uNot s a ta r save _ _ _ _ _ _ _ _ ih =>
  have e:(((hC a,if ta=3 then 2 else 0)::qk save (a,0) r).map fst) =
    (if true then hC a else a)::qk save a (r.map fst):=by cases save<;>simp[qk]
  rw[e] at ih;exact Run.one true save ih
 | @bOr s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
  have e:(((hG a b,if ta=4\/tb=4 then 7 else 0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).map fst) =
    (if false then hE a b else hG a b)::qk ka a (qk kb b (r.map fst)):=by
   cases ka<;>cases kb<;>simp[qk]
  rw[e] at ih;exact Run.two false ka kb ih
 | @bAnd s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih =>
  have e:(((hE a b,if ta=6\/tb=6 then 8 else if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)).map fst) =
    (if true then hE a b else hG a b)::qk ka a (qk kb b (r.map fst)):=by
   cases ka<;>cases kb<;>simp[qk]
  rw[e] at ih;exact Run.two true ka kb ih
lemma gU.len_le {s:Nat}{b:X 8}(h:gU s b):b.length<=s+1:=by have:=oy h.toRun;simpa using this
lemma gU.inv_zero {c:X 8}(h:gU 0 c):∃tg,c=[(fG,tg)]:=by
 generalize b:0=s at h
 induction h with
 | done tg _=>exact⟨tg,rfl⟩
 | perm d _ ih=>obtain⟨tg,rfl⟩:=ih b;exact⟨tg,List.perm_singleton.1 d.symm⟩
 | uNot _ _ _ _ _ _ _ _ _ _=>cases b
 | bOr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _=>cases b
 | bAnd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _=>cases b
def d7 (x:F 8):F 8
 | ⟨0,_⟩ => x 3
 | ⟨1,_⟩ => x 5
 | ⟨2,_⟩ => x 6
 | ⟨3,_⟩ => x 0
 | ⟨4,_⟩ => x 4
 | ⟨5,_⟩ => x 1
 | ⟨6,_⟩ => x 2
 | ⟨7,_⟩ => x 7
def ed (x:F 6):F 6
 | ⟨0,_⟩ => x 3
 | ⟨1,_⟩ => x 4
 | ⟨2,_⟩ => x 5
 | ⟨3,_⟩ => x 0
 | ⟨4,_⟩ => x 1
 | ⟨5,_⟩ => x 2
lemma ec (x:F 8):d7 (d7 x)=x:=by funext i;fin_cases i<;>rfl
lemma l8 (x:F 6):ed (ed x)=x:=by funext i;fin_cases i<;>rfl
lemma bm:Bijective ed:=
 Function.bijective_iff_has_inverse.2 ⟨ed,l8,l8⟩
lemma gd (x:F 8):fG (d7 x)=fG x:=by
 simp only[fG,d7];cases x 0<;>cases x 1<;>cases x 2<;>cases x 3 <;>
 cases x 4<;>cases x 5<;>cases x 6<;>cases x 7<;>rfl
lemma ge (x:F 6):f7 (ed x)=f7 x:=by simp only[f7,ed];cases x 0<;>cases x 1<;>cases x 2<;>cases x 3<;>cases x 4<;>cases x 5<;>rfl
lemma aa (x:F 6):a9 (ed x)=d7 (a9 x):=by funext i;fin_cases i<;>rfl
lemma tz (g:Z 8):a8 (fun x=>g (d7 x))=(fun x=>a8 g (ed x)):=by funext x;simp[a8,aa]
lemma F7Ok.map_sig8 {s:Nat}{c:X 8}(h:F7Ok s c):F7Ok s (c.map fun p=>((fun x=>p.1 (d7 x)),p.2)):=by
 obtain⟨t,L0,u,v,y,d⟩:=h;unfold F7Ok;rw[tv (fun g x=>g (d7 x)) c]
 refine⟨t,L0.map (fun g x=>g (ed x)),?_,?_,?_,?_⟩
 . refine u.map ?_
   intro a b z;funext x
   have:=congrFun z (ed x);dsimp only at this;rwa[l8] at this
 . intro g e;rcases mM.1 e with ⟨g0,i,rfl⟩
   obtain⟨hf,ht⟩:=v g0 i;constructor
   . intro j;apply hf;funext x;have:=congrFun j (ed x);rwa[l8] at this
   . intro j;apply ht;funext x;have:=congrFun j (ed x);rwa[l8] at this
 . intro g e;rcases mM.1 e with ⟨g0,i,rfl⟩
   obtain⟨p,hp,h4,h6,h7,h8,h0⟩:=y g0 i;refine⟨((fun x=>p.1 (d7 x)),p.2),mM.2 ⟨p,hp,rfl⟩,h4,h6,h7,h8,?_⟩
   rw[tz,h0]
 . have d':=wp ed bm ge d;have h1:((L0.map (·,0)).map fun p=>((fun x=>p.1 (ed x)),p.2)) =
      (L0.map (fun g x=>g (ed x))).map (·,0):=by
     simp[hW,Function.comp]
   rwa[h1] at d'
lemma gU.map_sig8 {s:Nat}{ws:X 8}(h:gU s ws):gU s (ws.map fun p=>((fun x=>p.1 (d7 x)),p.2)):=by
 have d:∀a b:Z 8,(fun x=>a (d7 x))=(fun x=>b (d7 x))->a=b:=by intro a b x2;funext x;have:=congrFun x2 (d7 x);rwa[ec] at this
 induction h with
 | done tg c=>have hf:(fun x=>fG (d7 x))=fG:=funext gd;have c':=c.map_sig8;simp only[kB,mS,hf] at c' ⊢;exact gU.done tg c'
 | perm g _ ih=>exact gU.perm (g.map _) ih
 | @uNot s a ta r save c x3 a1 i j t u _ ih =>
  have c':=c.map_sig8;simp only[kB] at c' ih ⊢;have a2:(fun x=>hC a (d7 x))=hC (fun x=>a (d7 x)):=rfl;have v:(qk save (a,0) r).map (fun p=>((fun x=>p.1 (d7 x)),p.2)) =
    qk save ((fun x=>a (d7 x)),0) (r.map fun p=>((fun x=>p.1 (d7 x)),p.2)):=by
   cases save<;>simp[qk]
  rw[a2,v] at ih;refine gU.uNot save c' x3 a1
   (fun e=>i (d _ _ e)) (fun e=>j (d _ _ e))
   (fun e=>t (d _ _ e)) ?_ ih
  intro x y;rcases mM.1 y with ⟨p,g,rfl⟩
  exact fun e=>u p g (d _ _ e)
 | @bOr s a ta b tb r ka kb c z h2 h3 h4 h5 h6 h7 h8 i j t h0 u _ ih =>
  have c':=c.map_sig8;simp only[kB] at c' ih ⊢;have b0:(fun x=>hG a b (d7 x))=hG (fun x=>a (d7 x)) (fun x=>b (d7 x)):=rfl;have v:(qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).map
    (fun p=>((fun x=>p.1 (d7 x)),p.2)) =
    qk ka ((fun x=>a (d7 x)),if ta=3 then 1 else 0)
     (qk kb ((fun x=>b (d7 x)),if tb=3 then 1 else 0) (r.map fun p=>((fun x=>p.1 (d7 x)),p.2))):=by
   cases ka<;>cases kb<;>simp[qk]
  rw[b0,v] at ih;refine gU.bOr ka kb c' z h2 h3 h4 h5 h6 h7 h8
   (fun e=>i (d _ _ e)) (fun e=>j (d _ _ e))
   (fun e=>t (d _ _ e)) (fun e=>h0 (d _ _ e)) ?_ ih
  intro x y;rcases mM.1 y with ⟨p,g,rfl⟩
  exact fun e=>u p g (d _ _ e)
 | @bAnd s a ta b tb r ka kb c z h2 h3 h4 h5 h6 h7 h8 h9 b1 i j t h0 u _ ih =>
  have c':=c.map_sig8;simp only[kB] at c' ih ⊢;have b3:(fun x=>hE a b (d7 x))=hE (fun x=>a (d7 x)) (fun x=>b (d7 x)):=rfl;have v:(qk ka (a,0) (qk kb (b,0) r)).map
    (fun p=>((fun x=>p.1 (d7 x)),p.2)) =
    qk ka ((fun x=>a (d7 x)),0)
     (qk kb ((fun x=>b (d7 x)),0) (r.map fun p=>((fun x=>p.1 (d7 x)),p.2))):=by
   cases ka<;>cases kb<;>simp[qk]
  rw[b3,v] at ih;refine gU.bAnd ka kb c' z h2 h3 h4 h5 h6 h7 h8 h9 b1
   (fun e=>i (d _ _ e)) (fun e=>j (d _ _ e))
   (fun e=>t (d _ _ e)) (fun e=>h0 (d _ _ e)) ?_ ih
  intro x y;rcases mM.1 y with ⟨p,g,rfl⟩
  exact fun e=>u p g (d _ _ e)
def un (i:Fin 8):Nat:=
 match i.val with
 | 2=>3
 | 4=>6
 | 6=>3
 | 7=>4
 | _=>0
def i1:X 8:=
 ofFn fun i:Fin 8=>((fun x:F 8=>x i),un i)
def af {gs:U}{o:Nat}(S:gZ gs o)(p:Nat)(tg:Nat->Nat):Prop:=
 (∀a∈u0 gs 8 o p,
  match tg a with
  | 0 | 1 | 2 | 3 =>
   yf 8 gs fG p a (tg a)/\a≠7/\a≠4/\a≠8+S.pg/\(S.bj=true->a≠8+S.pr)
  | 4=>a=7
  | 6=>a=4
  | 7=>a=8+S.pg
  | 8=>S.bj=true/\a=8+S.pr
  | _=>False) /\
 (7∈u0 gs 8 o p->tg 7=4) /\
 (4∈u0 gs 8 o p->tg 4=6) /\
 (8+S.pg∈u0 gs 8 o p->tg (8+S.pg)=7) /\
 (S.bj=true->8+S.pr∈u0 gs 8 o p->tg (8+S.pr)=8)
lemma my {gs:U}{o p:Nat}(c:gY 8 fG gs o)(S:gZ gs o):7∈u0 gs 8 o p↔p<=S.pg:=by
 rw[qw];constructor
 . rintro ⟨_,h|⟨q,b,g,d,e,_⟩⟩
   . exact absurd h.symm S.eJ
   . rw[S.eP q g d e] at b;exact b
 . intro i;obtain⟨g,h_in,j,_,s,_,_⟩:=S.eQ;have t:(7:Nat)∈g.inputs:=by rcases s with h|h<;>rw[h]<;>simp
   exact⟨by omega,Or.inr ⟨S.pg,i,g,j,t,c.gR S.pg (by rw[S.ak];exact S.bx)⟩⟩
lemma tn {gs:U}{o p:Nat}(c:gY 8 fG gs o)(S:gZ gs o):8+S.pg∈u0 gs 8 o p↔S.pg < p/\p<=S.pr:=by
 rw[qw];constructor
 . rintro ⟨hlt,h|⟨q,d,g,e,b,_⟩⟩
   . exact absurd h.symm S.eM
   . rw[S.eR q g e b] at d;omega
 . rintro ⟨h1,i⟩
   obtain⟨g,u,j,_,s,_,_⟩:=S.eS;have b:8+S.pg∈g.inputs:=by rcases s with h|h<;>rw[h]<;>simp
   exact⟨by omega,Or.inr ⟨S.pr,i,g,j,b,c.gR S.pr (by rw[S.ak];exact S.cf)⟩⟩
lemma mz {gs:U}{o p:Nat}(i:gY 8 fG gs o)(S:gZ gs o):4∈u0 gs 8 o p↔p<=(if S.bj then S.pr else S.pw):=by
 rw[qw];constructor
 . rintro ⟨_,h|⟨q,j,g,s,b,_⟩⟩
   . exact absurd h.symm S.eK
   . rw[S.eT q g s b] at j;exact j
 . intro c;cases d:S.bj
   . simp only[d,jV,↓reduceIte] at c;obtain⟨g,v,t,_,e,_⟩:=S.eV;simp only[d,jV,↓reduceIte] at e;have b:(4:Nat)∈g.inputs:=by rcases e with h|h<;>rw[h]<;>simp
     exact⟨by omega,Or.inr ⟨S.pw,c,g,t,b,i.gR S.pw (by rw[S.ak];exact S.eD)⟩⟩
   . simp only[d,↓reduceIte] at c;obtain⟨g,u,x,_,e,_,y⟩:=S.eS;have z:u=4:=y.1 d;have b:(4:Nat)∈g.inputs:=by rcases e with h|h<;>rw[h,z]<;>simp
     exact⟨by omega,Or.inr ⟨S.pr,c,g,x,b,i.gR S.pr (by rw[S.ak];exact S.cf)⟩⟩
lemma tm {gs:U}{o p:Nat}(e:gY 8 fG gs o)(S:gZ gs o)(b:S.bj=true):8+S.pr∈u0 gs 8 o p↔S.pr < p/\p<=S.pw:=by
 rw[qw];constructor
 . rintro ⟨hlt,h|⟨q,i,g,j,c,_⟩⟩
   . exact absurd h.symm (S.eN b)
   . rw[S.eU b q g j c] at i;omega
 . rintro ⟨h1,s⟩
   obtain⟨g,v,t,_,d,_⟩:=S.eV;simp only[b,↓reduceIte] at d;have c:8+S.pr∈g.inputs:=by rcases d with h|h<;>rw[h]<;>simp
   exact⟨by omega,Or.inr ⟨S.pw,s,g,t,c,e.gR S.pw (by rw[S.ak];exact S.eD)⟩⟩
lemma tw {gs:U}{o p:Nat}(s:gY 8 fG gs o)(S:gZ gs o){tg:Nat->Nat}(h2:af S p tg):o5 ((u0 gs 8 o p).map fun a=>(e5 gs 8 a,tg a))=(if p<=S.pg then 1 else 0)+(if p<=S.pr then 1 else 0)+(if p<=S.pw then 1 else 0):=by
 let L:=u0 gs 8 o p;have i:L.Nodup:=vy gs 8 o p;let w:Nat->Nat:=fun a =>
   (if a=7 then 2 else 0) +
   (if a=8+S.pg then 1 else 0) +
   (if a=4 then 1 else 0) +
   (if a=8+S.pr then (if S.bj then 1 else 0) else 0)
 have hpg_pr:=S.eE;have h3:∀(b:M),(∀a∈b,a∈L) ->
    o5 (b.map fun a=>(e5 gs 8 a,tg a))=(b.map w).sum:=by
   intro b h1;induction b with
   | nil=>rfl
   | cons a h5 ih =>
    simp only[kB,o5,jN,ih (fun x hx=>h1 x (hX _ hx))];congr 1
    have h6:a∈L:=h1 a (jP ..);have hi:=h2.1 a h6
    match g:tg a with
    | 0 | 1 | 2 | 3 =>
      rw[g] at hi;obtain⟨_,t,j,u,y⟩:=hi;have h8:(if a=8+S.pr then (if S.bj=true then 1 else 0) else 0)=0:=by
       split_ifs with h9 d
       . exact absurd h9 (y d)
       . rfl
       . rfl
      dsimp only[w];rw[if_neg t,if_neg u,if_neg j,h8]
      decide
    | 4 =>
      rw[g] at hi;subst hi;dsimp only[w]
      split_ifs<;>omega
    | 6 =>
      rw[g] at hi;subst hi;dsimp only[w]
      split_ifs<;>omega
    | 7 =>
      rw[g] at hi;subst hi;dsimp only[w]
      split_ifs<;>omega
    | 8=>rw[g] at hi;obtain⟨d,rfl⟩:=hi;dsimp only[w];simp[d];omega
    | 5=>rw[g] at hi;exact False.elim hi
    | _+9=>rw[g] at hi;exact False.elim hi
 rw[h3 L (fun _ h=>h)]
 have v:∀(b:M) (x:Nat) (c:Nat),b.Nodup ->
    (b.map fun a=>if a=x then c else 0).sum=if x∈b then c else 0:=by
   intro b x c i';induction b with
   | nil=>simp
   | cons a h5 ih =>
    obtain⟨ha,x2⟩:=List.nodup_cons.1 i';simp only[kB,jN,ih x2,kC];by_cases z:a=x
    . subst z;simp[ha]
    . have x3:x≠a:=fun e=>z e.symm
      simp[z,x3]
 have h0:∀(f1 f2:Nat->Nat) (b:M),
    (b.map fun a=>f1 a+f2 a).sum=(b.map f1).sum+(b.map f2).sum:=by
   intro f1 f2 b;induction b with|nil=>simp|cons _ _ ih=>simp[ih];omega
 dsimp only[w];rw[h0,h0,h0,v L 7 2 i,v L (8+S.pg) 1 i,v L 4 1 i,v L (8+S.pr) (if S.bj then 1 else 0) i]
 have t:(7∈L)↔p<=S.pg:=my (p:=p) s S;have u:(8+S.pg∈L)↔S.pg < p/\p<=S.pr:=tn (p:=p) s S;have j:(4∈L)↔p<=(if S.bj then S.pr else S.pw):=mz (p:=p) s S;cases d:S.bj
 . simp only[d,jV,↓reduceIte] at j ⊢;simp only[t,u,j];split_ifs<;>omega
 . have y:(8+S.pr∈L)↔S.pr < p/\p<=S.pw:=tm (p:=p) s S d;have hpr_pw:=S.eH d;simp only[d,↓reduceIte] at j ⊢;simp only[t,u,j,y];split_ifs<;>omega
lemma dj {gs:U}{o:Nat}(S:gZ gs o):∀p≤ 13,(u1 6 gs u5 p).2.length+((if S.pg < p then 1 else 0)+(if S.pr < p then 1 else 0)+(if S.pw < p then 1 else 0))=p:=by
 intro p;induction p with
 | zero=>intro _;simp[u1,u4]
 | succ p ih =>
  intro hp;have c:=ih (by omega);have e:p < gs.length:=by rw[S.ak];omega
  obtain⟨g,i⟩ : ∃g,gs[p]?=some g:=⟨gs[p],jK e⟩;have hle:=n8 (m:=6) (init:=u5) i;have hge:(u1 6 gs u5 p).2.length<=(u1 6 gs u5 (p+1)).2.length:=p2 6 gs u5 (by omega);have d:=S.eY p (by omega);have h1:=S.eE;have h2:=S.eF;have h3:=S.eG;by_cases b:p=S.pg\/p=S.pr\/p=S.pw
  . have heq:=d.2 b;rcases b with rfl|rfl|rfl<;>(split_ifs at c ⊢<;>omega)
  . have hne:(u1 6 gs u5 (p+1)).2.length≠(u1 6 gs u5 p).2.length:=fun h=>b (d.1 h)
    have hsucc:(u1 6 gs u5 (p+1)).2.length=(u1 6 gs u5 p).2.length+1:=by omega
    push Not at b
    split_ifs at c ⊢<;>omega
lemma ot {gs:U}{o p:Nat}(h:gY 8 fG gs o)(S:gZ gs o)(d:p<=13){tg:Nat->Nat}(i:af S p tg):F7Ok (13 - p) ((u0 gs 8 o p).map fun a=>(e5 gs 8 a,tg a)):=by
 have u:=tw h S i;have v:=dj S p d;have hpg_lt:=S.bx;have hpr_lt:=S.cf;have hpw_lt:=S.eD;set sg:=(u4 6 gs (u5,[])).2;set kp:=(u1 6 gs u5 p).2.length;have hgs0_len:sg.length=10:=S.eX;have hkp_le:kp<=sg.length:=by obtain⟨t,ht⟩:=l7 6 gs u5 p (by rw[S.ak];exact d);change kp<=sg.length;rw[show sg=(u1 6 gs u5 p).2++t from ht];simp[kp]
 have hkp_le10:(u1 6 gs u5 p).2.length<=10:=by change kp<=10;omega
 have h3:o5 ((u0 gs 8 o p).map fun a=>(e5 gs 8 a,tg a))<=13 - p:=by rw[u];split_ifs at v ⊢<;>omega
 have h5:13 - p - o5 ((u0 gs 8 o p).map fun a=>(e5 gs 8 a,tg a)) =
     10 - kp:=by
   rw[u];change 13 - p - _=10 - (u1 6 gs u5 p).2.length
   split_ifs at v ⊢<;>omega
 let L0:=(u0 sg 6 S.o0 kp).map (e5 sg 6);refine⟨h3,L0,?_,?_,?_,?_⟩
 . have h9:=vy sg 6 S.o0 kp;refine h9.map_on ?_
   intro x x2 b2 x3 a1;have h1:=((qw sg 6 S.o0 kp x).1 x2).1;have h2:=((qw sg 6 S.o0 kp b2).1 x3).1;exact td S.fD (by change x < 6+sg.length;omega) (by change b2 < 6+sg.length;omega) a1
 . intro g j;rcases mM.1 j with ⟨b,s,rfl⟩
   have hblt:=((qw sg 6 S.o0 kp b).1 s).1;exact⟨r8 S.fD (by change b < 6+sg.length;omega) false,r8 S.fD (by change b < 6+sg.length;omega) true⟩
 . intro g j;rcases mM.1 j with ⟨b,s,rfl⟩
   obtain⟨a,e,c⟩:=ds h S d s;have a2:=((qw gs 8 o p a).1 e).1;have b0:=oz h (by rw[S.ak];exact d) a2 c;refine⟨(e5 gs 8 a,tg a),mM.2 ⟨a,e,rfl⟩,?_,?_,?_,?_,b0⟩
   . intro y;simp only at y;have hi:=i.1 a e;rw[y] at hi;subst hi;rw[S.eZ p d] at c;cases c
   . intro z;simp only at z;have hi:=i.1 a e;rw[z] at hi;subst hi;rw[S.ft p d] at c;cases c
   . intro h7;simp only at h7;have hi:=i.1 a e;rw[h7] at hi;subst hi;have b3:S.pg < p:=((tn h S).1 e).1;rw[S.fA p d b3] at c;cases c
   . intro h8;simp only at h8;have hi:=i.1 a e;rw[h8] at hi;obtain⟨h0,rfl⟩:=hi;have c2:S.pr < p:=((tm h S h0).1 e).1;rw[S.fB h0 p d c2] at c;cases c
 . rw[h5]
   have c3:=kc 6 f7 sg S.o0 S.fD (10 - kp) kp (by omega) (fun _=>0) (fun _ _=>trivial);have d1:((u0 sg 6 S.o0 kp).map fun a=>(e5 sg 6 a,0))=L0.map (·,0):=(by simp[L0,hW,Function.comp]);rwa[d1] at c3
open Classical in
lemma em {gs:U}{o:Nat}(hm:gY 8 fG gs o)(S:gZ gs o):∀d p,p+d=13->∀tg:Nat->Nat,af S p tg->gU d ((u0 gs 8 o p).map fun a=>(e5 gs 8 a,tg a)):=by
 intro d;induction d with
 | zero =>
  intro p hp tg i;have cW:p=13:=by omega
  subst cW;have cX:[o].Perm (u0 gs 8 o 13):=by
   refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (vy _ _ _ _)).2 ?_
   intro a;rw[qw,List.mem_singleton]
   constructor
   . rintro rfl;exact⟨by have:=hm.ho;rw[S.ak] at this;exact this,Or.inl rfl⟩
   . rintro ⟨_,h|⟨q,hq,g',b',_,_⟩⟩
     . exact h
     . have:=(jJ.1 b').1;rw[S.ak] at this;omega
  have hf:e5 gs 8 o=fG:=funext hm.gQ;have s:[(fG,tg o)].Perm ((u0 gs 8 o 13).map fun a=>(e5 gs 8 a,tg a)):=(by rw[<- hf];exact cX.map (fun a=>(e5 gs 8 a,tg a)));have g0:F7Ok 0 [(fG,tg o)]:=(ot hm S le_rfl i).perm s.symm;exact gU.perm s (gU.done (tg o) g0)
 | succ d ih =>
  intro p hp tg i;have f2:p < gs.length:=by rw[S.ak];omega
  obtain⟨g,b⟩ : ∃g,gs[p]?=some g:=⟨gs[p],jK f2⟩;have hr:wn 8 gs o (8+p):=hm.gR p f2;have s6:=pb 8 gs o hm.gP p g b hr;have d2:∀u,u≠8+p->u∈u0 gs 8 o (p+1)->u∈u0 gs 8 o p:=fun u cY hu=>((s6 u).1 hu).resolve_left cY |>.1
  have hc:∀a∈g.inputs,a∈u0 gs 8 o p:=fun a ha =>
   (qw _ _ _ _ _).2 ⟨j2 (hm.gP p g b) a ha,Or.inr ⟨p,le_rfl,g,b,ha,hr⟩⟩
  have g1:∀a∈u0 gs 8 o p,a≠8+p:=fun a ha =>
   Nat.ne_of_lt ((qw _ _ _ _ _).1 ha).1
  have aV:=dn 8 gs p g b (j2 (hm.gP p g b));have m3:=vy gs 8 o p;have bG:gs.drop p=g::gs.drop (p+1):=(by rw[List.drop_eq_getElem_cons f2];have cZ:gs[p]=g:=(jJ.1 b).2;rw[cZ]);have bH:mc g:=us (hm.gP p g b);have p0:=it hm.gP (p+1);have bJ:e5 gs 8 (8+p)≠fun _=>false:=hm.gS p f2 false
  have bK:e5 gs 8 (8+p)≠fun _=>true:=hm.gS p f2 true
  have g2:∀a∈u0 gs 8 o p,e5 gs 8 a≠e5 gs 8 (8+p):=fun a ha e =>
   hm.gT p f2 a ((qw _ _ _ _ _).1 ha).1 e.symm
  have cD:F7Ok (d+1) ((u0 gs 8 o p).map fun a=>(e5 gs 8 a,tg a)):=by
   have:=ot hm S (by omega) i
   rwa[show 13 - p=d+1 by omega] at this
  have hv:∀a∈u0 gs 8 o p,tg a<=3->yf 8 gs fG p a (tg a):=by
   intro a ha hle;have hi:=i.1 a ha
   match ht:tg a with
   | 0 | 1 | 2 | 3=>rw[ht] at hi;exact hi.1
   | _+4=>omega
  have aC:∀u,(∀q g',gs[q]?=some g'->u∈g'.inputs->q=p)->u≠o ->
     ¬a6 8 gs o (p+1) u:=by
   intro u dA dB dC;rcases dC with h|⟨q,hq,g',b',hc',_⟩
   . exact dB h
   . have:=dA q g' b' hc';omega
  rcases hm.gP p g b with ⟨b0,j,hj,h5⟩|⟨b0,j,k,hj,hk,h5⟩
  .
   have a1:j∈u0 gs 8 o p:=hc j (by simp[h5]);have b3:e5 gs 8 (8+p)=hC (e5 gs 8 j):=(by funext x;rw[aV x,b0,h5];simp[GateOp.eval]);have g3:tg j<=3:=by
     have hi:=i.1 j a1
     match ht:tg j with
     | 0 | 1 | 2 | 3=>omega
     | 4=>rw[ht] at hi;subst hi;have t:=S.eP p g b (by simp[h5]);obtain⟨gg,_,c3,z,_,_,_⟩:=S.eQ;rw[t,c3] at b;cases b;rw[b0] at z;cases z
     | 6 =>
       rw[ht] at hi;subst hi;have t:=S.eT p g b (by simp[h5]);cases x3:S.bj
       . simp only[x3,jV,↓reduceIte] at t;obtain⟨gw,_,hd,z,_⟩:=S.eV;rw[t,hd] at b;cases b;rw[b0] at z;cases z
       . simp only[x3,↓reduceIte] at t;obtain⟨gr,_,c2,z,_⟩:=S.eS;rw[t,c2] at b;cases b;rw[b0] at z;cases z
     | 7=>rw[ht] at hi;subst hi;have t:=S.eR p g b (by simp[h5]);obtain⟨gr,_,c2,z,_⟩:=S.eS;rw[t,c2] at b;cases b;rw[b0] at z;cases z
     | 8=>rw[ht] at hi;obtain⟨x3,rfl⟩:=hi;have t:=S.eU x3 p g b (by simp[h5]);obtain⟨gw,_,hd,z,_⟩:=S.eV;rw[t,hd] at b;cases b;rw[b0] at z;cases z
     | 5=>rw[ht] at hi;exact False.elim hi
     | _+9=>rw[ht] at hi;exact False.elim hi
   have aW:∀v c B,
       (∃x y,fG (update x v false)≠fG (update y v false)) ->
       (v3 8 gs v p).1.getD j (inl false)=inl c ->
       (v3 8 gs v p).2.length+(gs.drop p).length<=(u4 8 (gs.drop p) (v3 8 gs v p)).2.length+B ->
       2<=B /\
       (v3 8 gs v (p+1)).1.getD (8+p) (inl false)=inl (!c) /\
       (v3 8 gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
         (u4 8 (gs.drop (p+1)) (v3 8 gs v (p+1))).2.length+B /\
       (a6 8 gs o (p+1) j->3<=B):=by
     intro v c B h9 x2 a2;have he:=rb 8 gs v p g b;have aD:=vb 8 gs v p (by omega);have cE:=vb 8 gs v (p+1) (by omega);have h0:(v3 8 gs v (p+1)).2.length=(v3 8 gs v p).2.length:=by rw[he];exact vs 8 _ g bH j (by simp[h5]) c x2
     have t0:(v3 8 gs v (p+1)).1.getD (8+p) (inl false)=inl (!c):=(by rw[he];simp only[qa];rw[z2 _ _ _ _ aD,b0,h5];simp only[kB,mS,x2,qg,wr]);have aE:u4 8 (gs.drop (p+1)) (v3 8 gs v (p+1))=u4 8 (gs.drop p) (v3 8 gs v p):=(by rw[zj,zj]);have cF:(gs.drop p).length=(gs.drop (p+1)).length+1:=(by rw[bG];simp);have t1:(v3 8 gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
         (u4 8 (gs.drop (p+1)) (v3 8 gs v (p+1))).2.length+B:=by rw[aE,h0];omega
     have aF:8+p∈u0 gs 8 o (p+1):=(s6 (8+p)).2 (Or.inl rfl);have p1:=zr hm (by omega) aF h9 t0;have aX:=zt 8 (8+p) (gs.drop (p+1)) (v3 8 gs v (p+1)) p0 (by omega) ⟨!c,t0⟩ p1;refine⟨by omega,t0,t1,?_⟩
     intro bL;have dD:j∈u0 gs 8 o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,bL⟩;have cH:(v3 8 gs v (p+1)).1.getD j (inl false)=inl c:=by rw[he];simp only[qa];rw[q8 _ _ _ _ (by omega)];exact x2
     have dE:=zr hm (by omega) dD h9 cH;have bM:=q21 hm f2 (fun x=>congrFun b3 x);have dF:=k3 8 j (8+p) (gs.drop (p+1)) (v3 8 gs v (p+1))
       p0 (by omega) (by omega) ⟨c,cH⟩ ⟨!c,t0⟩ dE p1 bM
     omega
   have ht1:tg j≠1:=(by intro s;have hw:=hv j a1 g3;rw[s] at hw;obtain⟨v,h9,x2,a2⟩:=hw;have:=(aW v false 1 h9 x2 a2).1;omega);have ht2:tg j≠2:=(by intro h2;have hw:=hv j a1 g3;rw[h2] at hw;obtain⟨v,h9,x2,a2⟩:=hw;have:=(aW v true 1 h9 x2 a2).1;omega);have aY:tg j=0\/tg j=3:=(by omega);have dG:tg j=3->decide (a6 8 gs o (p+1) j)=false:=(by intro h3;simp only[decide_eq_false_iff_not];intro bL;have hw:=hv j a1 g3;rw[h3] at hw;obtain⟨v,h9,x2,a2⟩:=hw;have:=(aW v false 2 h9 x2 a2).2.2.2 bL;omega);have dH:p≠S.pg:=(by intro g4;obtain⟨gg,_,c3,z,_,_,_⟩:=S.eQ;rw[g4,c3] at b;cases b;rw[b0] at z;cases z);have dJ:p≠S.pr:=(by intro g4;obtain⟨gr,_,c2,z,_⟩:=S.eS;rw[g4,c2] at b;cases b;rw[b0] at z;cases z);set tg' : Nat->Nat:=fun a =>
     if a=8+p then (if tg j=3 then 2 else 0)
     else if a=j then 0
     else tg a
   have i' : af S (p+1) tg':=by
     refine⟨?_,?_,?_,?_,?_⟩
     . intro a ha;simp only[tg'];by_cases hn:a=8+p
       . subst hn;simp only[↓reduceIte];by_cases h3:tg j=3
         . simp only[h3,↓reduceIte];have hw:=hv j a1 g3;rw[h3] at hw;obtain⟨v,h9,x2,a2⟩:=hw;obtain⟨_,t0,t1,_⟩:=aW v false 2 h9 x2 a2;exact⟨⟨v,h9,t0,by omega⟩,by omega,by omega,by omega,fun _=>by omega⟩
         . simp only[h3,↓reduceIte];exact⟨trivial,by omega,by omega,by omega,fun _=>by omega⟩
       . simp only[hn,↓reduceIte];by_cases e0:a=j
         . subst e0;simp only[↓reduceIte];have aZ:=i.1 a a1;rcases aY with h0|h3
           . rw[h0] at aZ;exact⟨trivial,aZ.2⟩
           . rw[h3] at aZ;exact⟨trivial,aZ.2⟩
         . simp only[e0,↓reduceIte];have j0:a∈u0 gs 8 o p:=d2 a hn ha;have hi:=i.1 a j0
           match ht:tg a with
           | 0 | 1 | 2 | 3=>rw[ht] at hi;exact⟨vv b ((qw _ _ _ _ _).1 j0).1 hi.1,hi.2⟩
           | 4 | 6 | 7 | 8=>rw[ht] at hi;exact hi
           | 5=>rw[ht] at hi;exact False.elim hi
           | _+9=>rw[ht] at hi;exact False.elim hi
     . intro h7;have hy:=d2 7 (by omega) h7;have r2:(7:Nat)≠j:=by intro e;rw[<- e,i.2.1 hy] at g3;omega
       simp only[tg',show (7:Nat)≠8+p by omega,r2,↓reduceIte];exact i.2.1 hy
     . intro h4;have hz:=d2 4 (by omega) h4;have r2:(4:Nat)≠j:=by intro e;rw[<- e,i.2.2.1 hz] at g3;omega
       simp only[tg',show (4:Nat)≠8+p by omega,r2,↓reduceIte];exact i.2.2.1 hz
     . intro r3;have xi:=d2 (8+S.pg) (by omega) r3;have r2:8+S.pg≠j:=by intro e;rw[<- e,i.2.2.2.1 xi] at g3;omega
       simp only[tg',show 8+S.pg≠8+p by omega,r2,↓reduceIte];exact i.2.2.2.1 xi
     . intro x3 r4;have xs:=d2 (8+S.pr) (by omega) r4;have r2:8+S.pr≠j:=by intro e;rw[<- e,i.2.2.2.2 x3 xs] at g3;omega
       simp only[tg',show 8+S.pr≠8+p by omega,r2,↓reduceIte];exact i.2.2.2.2 x3 xs
   have IH:=ih (p+1) (by omega) tg' i';have v2:(u0 gs 8 o p).Perm (j::(u0 gs 8 o p).erase j):=List.perm_cons_erase a1;have bA:((u0 gs 8 o p).erase j).Nodup:=m3.erase j;have bB:(u0 gs 8 o (p+1)).Perm
       ((8+p)::qk (decide (a6 8 gs o (p+1) j)) j ((u0 gs 8 o p).erase j)):=by
     refine (List.perm_ext_iff_of_nodup (vy _ _ _ _) ?_).2 ?_
     . refine List.nodup_cons.2 ⟨?_,fq _ _ _ bA (by simp[m3.mem_erase_iff])⟩
       rw[wa];rintro (⟨_,h⟩|h)
       . exact g1 j a1 h.symm
       . exact g1 _ (List.mem_of_mem_erase h) rfl
     . intro a;rw[s6 a,kC,wa,m3.mem_erase_iff]
       simp only[decide_eq_true_eq,h5,kC,jC,or_false];constructor
       . rintro (h|⟨s,h2⟩)
         . exact Or.inl h
         . by_cases e0:a=j
           . exact Or.inr (Or.inl ⟨e0 ▸ h2 e0,e0⟩)
           . exact Or.inr (Or.inr ⟨e0,s⟩)
       . rintro (h|⟨s,rfl⟩|⟨s,h2⟩)
         . exact Or.inl h
         . exact Or.inr ⟨a1,fun _=>s⟩
         . exact Or.inr ⟨h2,fun h=>absurd h s⟩
   have aG:((u0 gs 8 o p).erase j).map (fun a=>(e5 gs 8 a,tg' a)) =
       ((u0 gs 8 o p).erase j).map (fun a=>(e5 gs 8 a,tg a)):=by
     apply jH;intro a ha;have s:a≠j:=(m3.mem_erase_iff.1 ha).1;have h2:a≠8+p:=g1 a (List.mem_of_mem_erase ha);simp[tg',s,h2]
   have aH:(qk (decide (a6 8 gs o (p+1) j)) j ((u0 gs 8 o p).erase j)).map (fun a=>(e5 gs 8 a,tg' a)) =
       qk (decide (a6 8 gs o (p+1) j)) (e5 gs 8 j,0) (((u0 gs 8 o p).erase j).map fun a=>(e5 gs 8 a,tg a)):=by
     rw[wd,aG];simp[tg',show j≠8+p by omega]
   have IH':=gU.perm (bB.map fun a=>(e5 gs 8 a,tg' a)) IH;rw[kB,aH,b3] at IH';have aJ:tg' (8+p)=(if tg j=3 then 2 else 0):=(by simp[tg']);rw[aJ] at IH';have g0':=cD.perm (v2.map fun a=>(e5 gs 8 a,tg a));rw[kB] at g0';refine gU.perm (v2.map fun a=>(e5 gs 8 a,tg a)).symm ?_
   refine gU.uNot (decide (a6 8 gs o (p+1) j)) g0' aY dG
     (b3 ▸ bJ) (b3 ▸ bK) (fun e=>g2 j a1 (b3 ▸ e.symm)) ?_ IH'
   intro x hx;obtain⟨a,ha,rfl⟩:=mM.1 hx;exact b3 ▸ g2 a (List.mem_of_mem_erase ha)
  .
   have bN:j≠k:=by
     intro e;subst e;apply hm.gT p f2 j hj
     funext x;rw[aV x,h5]
     rcases b0 with b0|b0<;>rw[b0]<;>simp[GateOp.eval]
   have a1:=hc j (by simp[h5]);have b1:=hc k (by simp[h5]);have dK:k∈(u0 gs 8 o p).erase j:=(m3.mem_erase_iff).2 ⟨fun e=>bN e.symm,b1⟩;have bA:((u0 gs 8 o p).erase j).Nodup:=m3.erase j;have dL:(((u0 gs 8 o p).erase j).erase k).Nodup:=bA.erase k;have v2:(u0 gs 8 o p).Perm (j::k::((u0 gs 8 o p).erase j).erase k):=(List.perm_cons_erase a1).trans ((List.perm_cons_erase dK).cons j);have j1:∀a,a∈((u0 gs 8 o p).erase j).erase k↔a≠k/\a≠j/\a∈u0 gs 8 o p:=(by intro a;rw[bA.mem_erase_iff,m3.mem_erase_iff]);have bB:(u0 gs 8 o (p+1)).Perm
       ((8+p)::qk (decide (a6 8 gs o (p+1) j)) j (qk (decide (a6 8 gs o (p+1) k)) k (((u0 gs 8 o p).erase j).erase k))):=by
     refine (List.perm_ext_iff_of_nodup (vy _ _ _ _) ?_).2 ?_
     . refine List.nodup_cons.2 ⟨?_,fq _ _ _ (fq _ _ _ dL ?_) ?_⟩
       . rw[wa,wa];rintro (⟨_,h⟩|⟨_,h⟩|h)
         . exact g1 j a1 h.symm
         . exact g1 k b1 h.symm
         . exact g1 _ ((j1 _).1 h).2.2 rfl
       . rw[j1];simp
       . rw[wa,j1];rintro (⟨_,h⟩|h)
         . exact bN h
         . exact h.2.1 rfl
     . intro a;rw[s6 a,kC,wa,wa,j1 a]
       simp only[decide_eq_true_eq,h5,kC,jC,or_false];constructor
       . rintro (h|⟨s,h2⟩)
         . exact Or.inl h
         . by_cases e0:a=j
           . exact Or.inr (Or.inl ⟨e0 ▸ h2 (Or.inl e0),e0⟩)
           . by_cases r5:a=k
             . exact Or.inr (Or.inr (Or.inl ⟨r5 ▸ h2 (Or.inr r5),r5⟩))
             . exact Or.inr (Or.inr (Or.inr ⟨r5,e0,s⟩))
       . rintro (h|⟨s,rfl⟩|⟨s,rfl⟩|⟨s,h2,h3⟩)
         . exact Or.inl h
         . exact Or.inr ⟨a1,fun _=>s⟩
         . exact Or.inr ⟨b1,fun _=>s⟩
         . exact Or.inr ⟨h3,fun h=>by rcases h with h|h<;>contradiction⟩
   have g0':=cD.perm (v2.map fun a=>(e5 gs 8 a,tg a));rw[kB,kB] at g0';rcases b0 with b0|b0
   .
     have b3:e5 gs 8 (8+p)=hE (e5 gs 8 j) (e5 gs 8 k):=(by funext x;rw[aV x,b0,h5];simp[GateOp.eval]);have s2:∀(u w_other:Nat) (hu:u∈g.inputs) (hs:u < 8+p)
         (hval_u:∀x,e5 gs 8 (8+p) x=(e5 gs 8 u x&&e5 gs 8 w_other x))
         (v:Fin 8) (c:Q) (B:Nat),
         (∃x y,fG (update x v false)≠fG (update y v false)) ->
         (v3 8 gs v p).1.getD u (inl false)=inl c ->
         (v3 8 gs v p).2.length+(gs.drop p).length<=(u4 8 (gs.drop p) (v3 8 gs v p)).2.length+B ->
         (v3 8 gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
           (u4 8 (gs.drop (p+1)) (v3 8 gs v (p+1))).2.length+B /\
         (c=false->2<=B/\(v3 8 gs v (p+1)).1.getD (8+p) (inl false)=inl false/\(a6 8 gs o (p+1) u->3<=B)) /\
         (c=true->a6 8 gs o (p+1) u->2<=B):=by
       intro u wo hu hs aK v c B h9 x2 a2;have he:=rb 8 gs v p g b;have aD:=vb 8 gs v p (by omega);have cE:=vb 8 gs v (p+1) (by omega);have h0:(v3 8 gs v (p+1)).2.length=(v3 8 gs v p).2.length:=by rw[he];exact vs 8 _ g bH u hu c x2
       have aE:u4 8 (gs.drop (p+1)) (v3 8 gs v (p+1))=u4 8 (gs.drop p) (v3 8 gs v p):=(by rw[zj,zj]);have cF:(gs.drop p).length=(gs.drop (p+1)).length+1:=(by rw[bG];simp);have t1:(v3 8 gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
           (u4 8 (gs.drop (p+1)) (v3 8 gs v (p+1))).2.length+B:=by rw[aE,h0];omega
       have m2:(v3 8 gs v (p+1)).1.getD u (inl false)=inl c:=(by rw[he];simp only[qa];rw[q8 _ _ _ _ (by omega)];exact x2);refine⟨t1,?_,?_⟩
       . intro bP;subst bP;have bC:(v3 8 gs v (p+1)).1.getD (8+p) (inl false)=inl false:=by
           rw[he];simp only[qa];rw[z2 _ _ _ _ aD,b0,h5]
           rw[h5] at hu;simp only[kC,jC,or_false] at hu;rcases hu with rfl|rfl
           . simp only[kB,mS,x2,qg];cases (v3 8 gs v p).1.getD k (inl false)<;>simp[ko]
           . simp only[kB,mS,x2,qg];cases (v3 8 gs v p).1.getD j (inl false)<;>simp[ko]
         have aF:8+p∈u0 gs 8 o (p+1):=(s6 (8+p)).2 (Or.inl rfl);have p1:=zr hm (by omega) aF h9 bC;have aX:=zt 8 (8+p) (gs.drop (p+1)) (v3 8 gs v (p+1)) p0 (by omega) ⟨false,bC⟩ p1;refine⟨by omega,bC,?_⟩
         intro e1;have aL:u∈u0 gs 8 o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,e1⟩;have aM:=zr hm (by omega) aL h9 m2;have bM:=q22 hm f2 hs aK;have dF:=k3 8 u (8+p) (gs.drop (p+1)) (v3 8 gs v (p+1))
           p0 (by omega) (by omega) ⟨false,m2⟩ ⟨false,bC⟩ aM p1 bM
         omega
       . intro bQ e1;subst bQ;have aL:u∈u0 gs 8 o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,e1⟩;have aM:=zr hm (by omega) aL h9 m2;have aX:=zt 8 u (gs.drop (p+1)) (v3 8 gs v (p+1)) p0 (by omega) ⟨true,m2⟩ aM;omega
     have bD:∀x,e5 gs 8 (8+p) x=(e5 gs 8 j x&&e5 gs 8 k x):=fun x=>congrFun b3 x
     have bR:∀x,e5 gs 8 (8+p) x=(e5 gs 8 k x&&e5 gs 8 j x):=fun x=>by rw[bD x,Bool.and_comm]
     have dM:tg j≠1:=(by intro s;have hw:=hv j a1 (by omega);rw[s] at hw;obtain⟨v,h9,x2,a2⟩:=hw;have:=(s2 j k (by simp[h5]) hj bD v false 1 h9 x2 a2).2.1 rfl;omega);have dN:tg k≠1:=(by intro s;have hw:=hv k b1 (by omega);rw[s] at hw;obtain⟨v,h9,x2,a2⟩:=hw;have:=(s2 k j (by simp[h5]) hk bR v false 1 h9 x2 a2).2.1 rfl;omega);have cJ:tg j≠4:=(by intro h4;have hi:=i.1 j a1;rw[h4] at hi;subst hi;have t:=S.eP p g b (by simp[h5]);obtain⟨gg,_,c3,z,_,_,_⟩:=S.eQ;rw[t,c3] at b;cases b;rw[b0] at z;cases z);have cK:tg k≠4:=(by intro h4;have hi:=i.1 k b1;rw[h4] at hi;subst hi;have t:=S.eP p g b (by simp[h5]);obtain⟨gg,_,c3,z,_,_,_⟩:=S.eQ;rw[t,c3] at b;cases b;rw[b0] at z;cases z);have cL:tg j≠8:=(by intro h8;have hi:=i.1 j a1;rw[h8] at hi;obtain⟨x3,rfl⟩:=hi;have t:=S.eU x3 p g b (by simp[h5]);obtain⟨gw,_,hd,z,_⟩:=S.eV;rw[t,hd] at b;cases b;rw[b0] at z;cases z);have cM:tg k≠8:=(by intro h8;have hi:=i.1 k b1;rw[h8] at hi;obtain⟨x3,rfl⟩:=hi;have t:=S.eU x3 p g b (by simp[h5]);obtain⟨gw,_,hd,z,_⟩:=S.eV;rw[t,hd] at b;cases b;rw[b0] at z;cases z);have w0:∀u w,u∈u0 gs 8 o p->w∈u0 gs 8 o p ->
         (g.inputs=[u,w]\/g.inputs=[w,u])->tg u=6 ->
         S.bj=true/\p=S.pr/\w=8+S.pg/\tg w=7:=by
       intro u w aN dP cN h6;have hi:=i.1 u aN;rw[h6] at hi;subst hi;have d1:(4:Nat)∈g.inputs:=by rcases cN with h|h<;>rw[h]<;>simp
       have t:=S.eT p g b d1;cases x3:S.bj
       . simp only[x3,jV,↓reduceIte] at t;obtain⟨gw,_,hd,z,_⟩:=S.eV;rw[t,hd] at b;cases b;rw[b0] at z;cases z
       . simp only[x3,↓reduceIte] at t;obtain⟨gr,bS,c2,_,bT,_,bU⟩:=S.eS;rw[t,c2] at b;cases b
         have bV:bS=4:=bU.1 x3;have dQ:w=8+S.pg:=by rcases cN with s|s<;>rcases bT with h2|h2<;>rw[s,bV] at h2<;>simp at h2<;>omega
         subst dQ;exact⟨rfl,t,rfl,i.2.2.2.1 dP⟩
     have dR:tg j=6->tg k=7:=fun h6=>(w0 j k a1 b1 (Or.inl h5) h6).2.2.2
     have dS:tg k=6->tg j=7:=fun h6=>(w0 k j b1 a1 (Or.inr h5) h6).2.2.2
     have cP:∀u w,u∈u0 gs 8 o p->u < 8+p->u∈g.inputs ->
         (∀x,e5 gs 8 (8+p) x=(e5 gs 8 u x&&e5 gs 8 w x)) ->
         decide (a6 8 gs o (p+1) u)=true->tg u=0:=by
       intro u w aN hs d1 aK bW;have e1:a6 8 gs o (p+1) u:=of_decide_eq_true bW;have hi:=i.1 u aN
       match ht:tg u with
       | 0=>rfl
       | 1 =>
         rw[ht] at hi;obtain⟨v,h9,x2,a2⟩:=hi.1
         have:=(s2 u w d1 hs aK v false 1 h9 x2 a2).2.1 rfl;omega
       | 2 =>
         rw[ht] at hi;obtain⟨v,h9,x2,a2⟩:=hi.1
         have:=(s2 u w d1 hs aK v true 1 h9 x2 a2).2.2 rfl e1;omega
       | 3 =>
         rw[ht] at hi;obtain⟨v,h9,x2,a2⟩:=hi.1
         have:=((s2 u w d1 hs aK v false 2 h9 x2 a2).2.1 rfl).2.2 e1;omega
       | 4=>rw[ht] at hi;subst hi;have t:=S.eP p g b d1;obtain⟨gg,_,c3,z,_,_,_⟩:=S.eQ;rw[t,c3] at b;cases b;rw[b0] at z;cases z
       | 6 =>
         rw[ht] at hi;subst hi;have t:=S.eT p g b d1;cases x3:S.bj
         . simp only[x3,jV,↓reduceIte] at t;obtain⟨gw,_,hd,z,_⟩:=S.eV;rw[t,hd] at b;cases b;rw[b0] at z;cases z
         . simp only[x3,↓reduceIte] at t;exfalso;apply aC 4 _ S.eK.symm e1
           intro q' g' b' dT';rw[S.eT q' g' b' dT'];simp[x3,t]
       | 7 =>
         rw[ht] at hi;subst hi;have t:=S.eR p g b d1;exfalso;apply aC (8+S.pg) _ S.eM.symm e1
         intro q' g' b' hc';rw[S.eR q' g' b' hc'];exact t.symm
       | 8=>rw[ht] at hi;obtain⟨x3,rfl⟩:=hi;have t:=S.eU x3 p g b d1;obtain⟨gw,_,hd,z,_⟩:=S.eV;rw[t,hd] at b;cases b;rw[b0] at z;cases z
       | 5=>rw[ht] at hi;exact False.elim hi
       | _+9=>rw[ht] at hi;exact False.elim hi
     have bE:decide (a6 8 gs o (p+1) j)=true->tg j=0:=cP j k a1 hj (by simp[h5]) bD;have bF:decide (a6 8 gs o (p+1) k)=true->tg k=0:=cP k j b1 hk (by simp[h5]) bR;have dH:p≠S.pg:=(by intro g4;obtain⟨gg,_,c3,z,_,_,_⟩:=S.eQ;rw[g4,c3] at b;cases b;rw[b0] at z;cases z);have cQ:S.bj=true->(p=S.pr↔tg j=6\/tg k=6):=by
       intro x3;constructor
       . intro t;obtain⟨gr,bS,c2,_,bT,_,bU⟩:=S.eS;have bV:bS=4:=bU.1 x3;rw[t,c2] at b;cases b
         have bX:(4:Nat)∈g.inputs:=by rcases bT with h|h<;>rw[h,bV]<;>simp
         rw[h5] at bX;simp only[kC,jC,or_false] at bX;rcases bX with h|h
         . exact Or.inl (h ▸ i.2.2.1 (h ▸ a1))
         . exact Or.inr (h ▸ i.2.2.1 (h ▸ b1))
       . rintro (h6|h6)
         . exact (w0 j k a1 b1 (Or.inl h5) h6).2.1
         . exact (w0 k j b1 a1 (Or.inr h5) h6).2.1
     set tg' : Nat->Nat:=fun a =>
       if a=8+p then (if tg j=6\/tg k=6 then 8 else if tg j=3\/tg k=3 then 1 else 0)
       else if a=j\/a=k then 0
       else tg a
     have i' : af S (p+1) tg':=by
       refine⟨?_,?_,?_,?_,?_⟩
       . intro a ha;simp only[tg'];by_cases hn:a=8+p
         . subst hn;simp only[↓reduceIte];by_cases h6:tg j=6\/tg k=6
           . simp only[h6,↓reduceIte];rcases h6 with dU|dV
             . obtain⟨x3,t,_,_⟩:=w0 j k a1 b1 (Or.inl h5) dU;exact⟨x3,by omega⟩
             . obtain⟨x3,t,_,_⟩:=w0 k j b1 a1 (Or.inr h5) dV;exact⟨x3,by omega⟩
           . simp only[h6,↓reduceIte];have cR:S.bj=true->8+p≠8+S.pr:=by intro x3 g4;exact h6 ((cQ x3).1 (by omega))
             by_cases h3:tg j=3\/tg k=3
             . simp only[h3,↓reduceIte];refine⟨?_,by omega,by omega,by omega,cR⟩
               rcases h3 with dW|dX
               . have hw:=hv j a1 (by omega);rw[dW] at hw;obtain⟨v,h9,x2,a2⟩:=hw;have hh:=s2 j k (by simp[h5]) hj bD v false 2 h9 x2 a2;exact⟨v,h9,(hh.2.1 rfl).2.1,by omega⟩
               . have hw:=hv k b1 (by omega);rw[dX] at hw;obtain⟨v,h9,x2,a2⟩:=hw;have hh:=s2 k j (by simp[h5]) hk bR v false 2 h9 x2 a2;exact⟨v,h9,(hh.2.1 rfl).2.1,by omega⟩
             . simp only[h3,↓reduceIte];exact⟨trivial,by omega,by omega,by omega,cR⟩
         . simp only[hn,↓reduceIte];by_cases bY:a=j\/a=k
           . simp only[bY,↓reduceIte];have aA:a6 8 gs o (p+1) a:=((qw _ _ _ _ _).1 ha).2;rcases bY with rfl|rfl
             . have bZ:=bE (decide_eq_true aA);have hi:=i.1 a a1;rw[bZ] at hi;exact⟨trivial,hi.2⟩
             . have bZ:=bF (decide_eq_true aA);have hi:=i.1 a b1;rw[bZ] at hi;exact⟨trivial,hi.2⟩
           . simp only[bY,↓reduceIte];have j0:=d2 a hn ha;have hi:=i.1 a j0
             match ht:tg a with
             | 0 | 1 | 2 | 3=>rw[ht] at hi;exact⟨vv b ((qw _ _ _ _ _).1 j0).1 hi.1,hi.2⟩
             | 4 | 6 | 7 | 8=>rw[ht] at hi;exact hi
             | 5=>rw[ht] at hi;exact False.elim hi
             | _+9=>rw[ht] at hi;exact False.elim hi
       . intro h7;have hy:=d2 7 (by omega) h7;have e2:(7:Nat)≠j:=fun e=>cJ (e ▸ i.2.1 hy)
         have hb:(7:Nat)≠k:=fun e=>cK (e ▸ i.2.1 hy)
         simp only[tg',show (7:Nat)≠8+p by omega,e2,hb,or_self,↓reduceIte];exact i.2.1 hy
       . intro h4;have hz:=d2 4 (by omega) h4;have e2:(4:Nat)≠j:=by intro e;have s:=bE (decide_eq_true ((qw _ _ _ _ _).1 (e ▸ h4)).2);rw[<- e,i.2.2.1 hz] at s;cases s
         have hb:(4:Nat)≠k:=(by intro e;have s:=bF (decide_eq_true ((qw _ _ _ _ _).1 (e ▸ h4)).2);rw[<- e,i.2.2.1 hz] at s;cases s);simp only[tg',show (4:Nat)≠8+p by omega,e2,hb,or_self,↓reduceIte];exact i.2.2.1 hz
       . intro r3;have xi:=d2 (8+S.pg) (by omega) r3;have e2:8+S.pg≠j:=by intro e;have s:=bE (decide_eq_true ((qw _ _ _ _ _).1 (e ▸ r3)).2);rw[<- e,i.2.2.2.1 xi] at s;cases s
         have hb:8+S.pg≠k:=(by intro e;have s:=bF (decide_eq_true ((qw _ _ _ _ _).1 (e ▸ r3)).2);rw[<- e,i.2.2.2.1 xi] at s;cases s);simp only[tg',show 8+S.pg≠8+p by omega,e2,hb,or_self,↓reduceIte];exact i.2.2.2.1 xi
       . intro x3 r4;by_cases t:p=S.pr
         . subst t;have h6:=(cQ x3).1 rfl;simp only[tg',h6,↓reduceIte]
         . have xs:=d2 (8+S.pr) (by omega) r4;have e2:8+S.pr≠j:=fun e=>cL (e ▸ i.2.2.2.2 x3 xs)
           have hb:8+S.pr≠k:=fun e=>cM (e ▸ i.2.2.2.2 x3 xs)
           simp only[tg',show 8+S.pr≠8+p by omega,e2,hb,or_self,↓reduceIte];exact i.2.2.2.2 x3 xs
     have IH:=ih (p+1) (by omega) tg' i';have aG:(((u0 gs 8 o p).erase j).erase k).map (fun a=>(e5 gs 8 a,tg' a)) =
         (((u0 gs 8 o p).erase j).erase k).map (fun a=>(e5 gs 8 a,tg a)):=by
       apply jH;intro a ha;have⟨s,h2,h3⟩:=(j1 a).1 ha;have h4:=g1 a h3;simp[tg',s,h2,h4]
     have aH:(qk (decide (a6 8 gs o (p+1) j)) j (qk (decide (a6 8 gs o (p+1) k)) k (((u0 gs 8 o p).erase j).erase k))).map (fun a=>(e5 gs 8 a,tg' a)) =
         qk (decide (a6 8 gs o (p+1) j)) (e5 gs 8 j,0)
           (qk (decide (a6 8 gs o (p+1) k)) (e5 gs 8 k,0) ((((u0 gs 8 o p).erase j).erase k).map fun a=>(e5 gs 8 a,tg a))):=by
       rw[wd,wd,aG];simp[tg',show j≠8+p by omega,show k≠8+p by omega]
     have IH':=gU.perm (bB.map fun a=>(e5 gs 8 a,tg' a)) IH;rw[kB,aH,b3] at IH';have aJ:tg' (8+p)=(if tg j=6\/tg k=6 then 8 else if tg j=3\/tg k=3 then 1 else 0):=(by simp[tg']);rw[aJ] at IH';refine gU.perm (v2.map fun a=>(e5 gs 8 a,tg a)).symm ?_
     refine gU.bAnd (decide (a6 8 gs o (p+1) j)) (decide (a6 8 gs o (p+1) k)) g0'
       dM dN cJ cK cL cM dR dS bE bF
       (b3 ▸ bJ) (b3 ▸ bK) (fun e=>g2 j a1 (b3 ▸ e.symm)) (fun e=>g2 k b1 (b3 ▸ e.symm)) ?_ IH'
     intro x hx;obtain⟨a,ha,rfl⟩:=mM.1 hx;exact b3 ▸ g2 a ((j1 a).1 ha).2.2
   .
     have b3:e5 gs 8 (8+p)=hG (e5 gs 8 j) (e5 gs 8 k):=(by funext x;rw[aV x,b0,h5];simp[GateOp.eval]);have aB:∀(u:Nat) (hu:u∈g.inputs) (hs:u < 8+p) (v:Fin 8) (c:Q) (B:Nat),
         (∃x y,fG (update x v false)≠fG (update y v false)) ->
         (v3 8 gs v p).1.getD u (inl false)=inl c ->
         (v3 8 gs v p).2.length+(gs.drop p).length<=(u4 8 (gs.drop p) (v3 8 gs v p)).2.length+B ->
         (v3 8 gs v (p+1)).1.getD u (inl false)=inl c /\
         (v3 8 gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
           (u4 8 (gs.drop (p+1)) (v3 8 gs v (p+1))).2.length+B /\
         (c=true->2<=B)/\(c=false->a6 8 gs o (p+1) u->2<=B):=by
       intro u hu hs v c B h9 x2 a2;have he:=rb 8 gs v p g b;have aD:=vb 8 gs v p (by omega);have cE:=vb 8 gs v (p+1) (by omega);have h0:(v3 8 gs v (p+1)).2.length=(v3 8 gs v p).2.length:=by rw[he];exact vs 8 _ g bH u hu c x2
       have aE:u4 8 (gs.drop (p+1)) (v3 8 gs v (p+1))=u4 8 (gs.drop p) (v3 8 gs v p):=(by rw[zj,zj]);have cF:(gs.drop p).length=(gs.drop (p+1)).length+1:=(by rw[bG];simp);have t1:(v3 8 gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
           (u4 8 (gs.drop (p+1)) (v3 8 gs v (p+1))).2.length+B:=by rw[aE,h0];omega
       have m2:(v3 8 gs v (p+1)).1.getD u (inl false)=inl c:=(by rw[he];simp only[qa];rw[q8 _ _ _ _ (by omega)];exact x2);refine⟨m2,t1,?_,?_⟩
       . intro bQ;subst bQ;have cS:(v3 8 gs v (p+1)).1.getD (8+p) (inl false)=inl true:=by
           rw[he];simp only[qa];rw[z2 _ _ _ _ aD,b0,h5]
           rw[h5] at hu;simp only[kC,jC,or_false] at hu;rcases hu with rfl|rfl
           . simp only[kB,mS,x2,qg];cases (v3 8 gs v p).1.getD k (inl false)<;>simp[ji]
           . simp only[kB,mS,x2,qg];cases (v3 8 gs v p).1.getD j (inl false)<;>simp[ji]
         have aF:8+p∈u0 gs 8 o (p+1):=(s6 (8+p)).2 (Or.inl rfl);have p1:=zr hm (by omega) aF h9 cS;have aX:=zt 8 (8+p) (gs.drop (p+1)) (v3 8 gs v (p+1)) p0 (by omega) ⟨true,cS⟩ p1;omega
       . intro bP e1;subst bP;have aL:u∈u0 gs 8 o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,e1⟩;have aM:=zr hm (by omega) aL h9 m2;have aX:=zt 8 u (gs.drop (p+1)) (v3 8 gs v (p+1)) p0 (by omega) ⟨false,m2⟩ aM;omega
     have dY:tg j≠2:=(by intro h2;have hw:=hv j a1 (by omega);rw[h2] at hw;obtain⟨v,h9,x2,a2⟩:=hw;have:=(aB j (by simp[h5]) hj v true 1 h9 x2 a2).2.2.1 rfl;omega);have dZ:tg k≠2:=(by intro h2;have hw:=hv k b1 (by omega);rw[h2] at hw;obtain⟨v,h9,x2,a2⟩:=hw;have:=(aB k (by simp[h5]) hk v true 1 h9 x2 a2).2.2.1 rfl;omega);have cT:tg j≠7:=(by intro h7;have hi:=i.1 j a1;rw[h7] at hi;subst hi;have t:=S.eR p g b (by simp[h5]);obtain⟨gr,_,c2,z,_⟩:=S.eS;rw[t,c2] at b;cases b;rw[b0] at z;cases z);have cU:tg k≠7:=(by intro h7;have hi:=i.1 k b1;rw[h7] at hi;subst hi;have t:=S.eR p g b (by simp[h5]);obtain⟨gr,_,c2,z,_⟩:=S.eS;rw[t,c2] at b;cases b;rw[b0] at z;cases z);have eA:¬(tg j=4/\tg k=6):=by
       rintro ⟨h4,h6⟩
       have aP:=i.1 j a1;rw[h4] at aP;subst aP;have aQ:=i.1 k b1;rw[h6] at aQ;subst aQ;have t:=S.eP p g b (by simp[h5]);obtain⟨gg,eB,c3,_,aS,_,cA⟩:=S.eQ;rw[t,c3] at b;cases b
       rcases aS with s|s<;>rw[h5] at s<;>simp at s
       exact cA s.symm
     have eC:¬(tg j=6/\tg k=4):=by
       rintro ⟨h6,h4⟩
       have aP:=i.1 j a1;rw[h6] at aP;subst aP;have aQ:=i.1 k b1;rw[h4] at aQ;subst aQ;have t:=S.eP p g b (by simp[h5]);obtain⟨gg,eB,c3,_,aS,_,cA⟩:=S.eQ;rw[t,c3] at b;cases b
       rcases aS with s|s<;>rw[h5] at s<;>simp at s
       exact cA s.symm
     have cV:∀u,u∈u0 gs 8 o p->u < 8+p->u∈g.inputs ->
         decide (a6 8 gs o (p+1) u)=true->tg u=0\/tg u=3:=by
       intro u aN hs d1 bW;have e1:a6 8 gs o (p+1) u:=of_decide_eq_true bW;have hi:=i.1 u aN
       match ht:tg u with
       | 0=>exact Or.inl rfl
       | 3=>exact Or.inr rfl
       | 1 =>
         rw[ht] at hi;obtain⟨v,h9,x2,a2⟩:=hi.1
         have:=(aB u d1 hs v false 1 h9 x2 a2).2.2.2 rfl e1;omega
       | 2 =>
         rw[ht] at hi;obtain⟨v,h9,x2,a2⟩:=hi.1
         have:=(aB u d1 hs v true 1 h9 x2 a2).2.2.1 rfl;omega
       | 4 =>
         rw[ht] at hi;subst hi;have t:=S.eP p g b d1;exfalso;apply aC 7 _ S.eJ.symm e1
         intro q' g' b' hc';rw[S.eP q' g' b' hc'];exact t.symm
       | 6 =>
         rw[ht] at hi;subst hi;have t:=S.eT p g b d1;cases x3:S.bj
         . simp only[x3,jV,↓reduceIte] at t;exfalso;apply aC 4 _ S.eK.symm e1
           intro q' g' b' hc';rw[S.eT q' g' b' hc'];simp[x3,t]
         . simp only[x3,↓reduceIte] at t;obtain⟨gr,_,c2,z,_⟩:=S.eS;rw[t,c2] at b;cases b;rw[b0] at z;cases z
       | 7=>rw[ht] at hi;subst hi;have t:=S.eR p g b d1;obtain⟨gr,_,c2,z,_⟩:=S.eS;rw[t,c2] at b;cases b;rw[b0] at z;cases z
       | 8 =>
         rw[ht] at hi;obtain⟨x3,rfl⟩:=hi;have t:=S.eU x3 p g b d1;exfalso;apply aC (8+S.pr) _ (S.eN x3).symm e1
         intro q' g' b' hc';rw[S.eU x3 q' g' b' hc'];exact t.symm
       | 5=>rw[ht] at hi;exact False.elim hi
       | _+9=>rw[ht] at hi;exact False.elim hi
     have aT:decide (a6 8 gs o (p+1) j)=true->tg j=0\/tg j=3:=cV j a1 hj (by simp[h5]);have aU:decide (a6 8 gs o (p+1) k)=true->tg k=0\/tg k=3:=cV k b1 hk (by simp[h5]);have dJ:p≠S.pr:=(by intro g4;obtain⟨gr,_,c2,z,_⟩:=S.eS;rw[g4,c2] at b;cases b;rw[b0] at z;cases z);have cB:p=S.pg↔tg j=4\/tg k=4:=by
       constructor
       . intro t;obtain⟨gg,_,c3,_,aS,_,_⟩:=S.eQ;rw[t,c3] at b;cases b
         have cC:(7:Nat)∈g.inputs:=by rcases aS with h|h<;>rw[h]<;>simp
         rw[h5] at cC;simp only[kC,jC,or_false] at cC;rcases cC with h|h
         . exact Or.inl (h ▸ i.2.1 (h ▸ a1))
         . exact Or.inr (h ▸ i.2.1 (h ▸ b1))
       . rintro (h4|h4)
         . have hi:=i.1 j a1;rw[h4] at hi;subst hi;exact S.eP p g b (by simp[h5])
         . have hi:=i.1 k b1;rw[h4] at hi;subst hi;exact S.eP p g b (by simp[h5])
     set tg' : Nat->Nat:=fun a =>
       if a=8+p then (if tg j=4\/tg k=4 then 7 else 0)
       else if a=j then (if tg j=3 then 1 else 0)
       else if a=k then (if tg k=3 then 1 else 0)
       else tg a
     have i' : af S (p+1) tg':=by
       refine⟨?_,?_,?_,?_,?_⟩
       . intro a ha;simp only[tg'];by_cases hn:a=8+p
         . subst hn;simp only[↓reduceIte];by_cases h4:tg j=4\/tg k=4
           . simp only[h4,↓reduceIte];have:=cB.2 h4;omega
           . simp only[h4,↓reduceIte];have hne_pg:p≠S.pg:=fun e=>h4 (cB.1 e)
             exact⟨trivial,by omega,by omega,by omega,fun _=>by omega⟩
         . simp only[hn,↓reduceIte];by_cases e0:a=j
           . subst e0;simp only[↓reduceIte];have aA:=((qw _ _ _ _ _).1 ha).2;have aY:=aT (decide_eq_true aA);by_cases h3:tg a=3
             . simp only[h3,↓reduceIte];have hi:=i.1 a a1;rw[h3] at hi;obtain⟨v,h9,x2,a2⟩:=hi.1;have hh:=aB a (by simp[h5]) hj v false 2 h9 x2 a2;exact⟨⟨v,h9,hh.1,by omega⟩,hi.2⟩
             . simp only[h3,↓reduceIte];have h0:tg a=0:=by omega
               have hi:=i.1 a a1;rw[h0] at hi;exact⟨trivial,hi.2⟩
           . simp only[e0,↓reduceIte];by_cases r5:a=k
             . subst r5;simp only[↓reduceIte];have aA:=((qw _ _ _ _ _).1 ha).2;have aY:=aU (decide_eq_true aA);by_cases h3:tg a=3
               . simp only[h3,↓reduceIte];have hi:=i.1 a b1;rw[h3] at hi;obtain⟨v,h9,x2,a2⟩:=hi.1;have hh:=aB a (by simp[h5]) hk v false 2 h9 x2 a2;exact⟨⟨v,h9,hh.1,by omega⟩,hi.2⟩
               . simp only[h3,↓reduceIte];have h0:tg a=0:=by omega
                 have hi:=i.1 a b1;rw[h0] at hi;exact⟨trivial,hi.2⟩
             . simp only[r5,↓reduceIte];have j0:=d2 a hn ha;have hi:=i.1 a j0
               match ht:tg a with
               | 0 | 1 | 2 | 3=>rw[ht] at hi;exact⟨vv b ((qw _ _ _ _ _).1 j0).1 hi.1,hi.2⟩
               | 4 | 6 | 7 | 8=>rw[ht] at hi;exact hi
               | 5=>rw[ht] at hi;exact False.elim hi
               | _+9=>rw[ht] at hi;exact False.elim hi
       . intro h7;have hy:=d2 7 (by omega) h7;have e2:(7:Nat)≠j:=by intro e;have s:=aT (decide_eq_true ((qw _ _ _ _ _).1 (e ▸ h7)).2);rw[<- e,i.2.1 hy] at s;omega
         have hb:(7:Nat)≠k:=(by intro e;have s:=aU (decide_eq_true ((qw _ _ _ _ _).1 (e ▸ h7)).2);rw[<- e,i.2.1 hy] at s;omega);simp only[tg',show (7:Nat)≠8+p by omega,e2,hb,↓reduceIte];exact i.2.1 hy
       . intro h4;have hz:=d2 4 (by omega) h4;have e2:(4:Nat)≠j:=by intro e;have s:=aT (decide_eq_true ((qw _ _ _ _ _).1 (e ▸ h4)).2);rw[<- e,i.2.2.1 hz] at s;omega
         have hb:(4:Nat)≠k:=(by intro e;have s:=aU (decide_eq_true ((qw _ _ _ _ _).1 (e ▸ h4)).2);rw[<- e,i.2.2.1 hz] at s;omega);simp only[tg',show (4:Nat)≠8+p by omega,e2,hb,↓reduceIte];exact i.2.2.1 hz
       . intro r3;by_cases t:p=S.pg
         . subst t;have h4:=cB.1 rfl;simp only[tg',h4,↓reduceIte]
         . have xi:=d2 (8+S.pg) (by omega) r3;have e2:8+S.pg≠j:=fun e=>cT (e ▸ i.2.2.2.1 xi)
           have hb:8+S.pg≠k:=fun e=>cU (e ▸ i.2.2.2.1 xi)
           simp only[tg',show 8+S.pg≠8+p by omega,e2,hb,↓reduceIte];exact i.2.2.2.1 xi
       . intro x3 r4;have xs:=d2 (8+S.pr) (by omega) r4;have e2:8+S.pr≠j:=by intro e;have s:=aT (decide_eq_true ((qw _ _ _ _ _).1 (e ▸ r4)).2);rw[<- e,i.2.2.2.2 x3 xs] at s;omega
         have hb:8+S.pr≠k:=(by intro e;have s:=aU (decide_eq_true ((qw _ _ _ _ _).1 (e ▸ r4)).2);rw[<- e,i.2.2.2.2 x3 xs] at s;omega);simp only[tg',show 8+S.pr≠8+p by omega,e2,hb,↓reduceIte];exact i.2.2.2.2 x3 xs
     have IH:=ih (p+1) (by omega) tg' i';have aG:(((u0 gs 8 o p).erase j).erase k).map (fun a=>(e5 gs 8 a,tg' a)) =
         (((u0 gs 8 o p).erase j).erase k).map (fun a=>(e5 gs 8 a,tg a)):=by
       apply jH;intro a ha;have⟨s,h2,h3⟩:=(j1 a).1 ha;have h4:=g1 a h3;simp[tg',s,h2,h4]
     have aH:(qk (decide (a6 8 gs o (p+1) j)) j (qk (decide (a6 8 gs o (p+1) k)) k (((u0 gs 8 o p).erase j).erase k))).map (fun a=>(e5 gs 8 a,tg' a)) =
         qk (decide (a6 8 gs o (p+1) j)) (e5 gs 8 j,if tg j=3 then 1 else 0)
           (qk (decide (a6 8 gs o (p+1) k)) (e5 gs 8 k,if tg k=3 then 1 else 0) ((((u0 gs 8 o p).erase j).erase k).map fun a=>(e5 gs 8 a,tg a))):=by
       rw[wd,wd,aG];simp[tg',show j≠8+p by omega,show k≠8+p by omega,bN.symm]
     have IH':=gU.perm (bB.map fun a=>(e5 gs 8 a,tg' a)) IH;rw[kB,aH,b3] at IH';have aJ:tg' (8+p)=(if tg j=4\/tg k=4 then 7 else 0):=(by simp[tg']);rw[aJ] at IH';refine gU.perm (v2.map fun a=>(e5 gs 8 a,tg a)).symm ?_
     refine gU.bOr (decide (a6 8 gs o (p+1) j)) (decide (a6 8 gs o (p+1) k)) g0'
       dY dZ cT cU eA eC aT aU
       (b3 ▸ bJ) (b3 ▸ bK) (fun e=>g2 j a1 (b3 ▸ e.symm)) (fun e=>g2 k b1 (b3 ▸ e.symm)) ?_ IH'
     intro x hx;obtain⟨a,ha,rfl⟩:=mM.1 hx;exact b3 ▸ g2 a ((j1 a).1 ha).2.2
open Classical in
lemma ou {t:Nat}(v:nV 8 fG t)(ht:t<=13):gU 13 i1:=by
 obtain⟨gs,o,c,hlen⟩:=ng 8 fG t ru v;obtain⟨S⟩:=sk c (by omega);have z:∀i:Fin 8,(i:Nat)∈u0 gs 8 o 0:=by
  intro i;apply x9 c i
  fin_cases i
  . exact⟨fun j=>j=1,by decide⟩
  . exact⟨fun j=>j=0,by decide⟩
  . exact⟨fun j=>j=0,by decide⟩
  . exact⟨fun j=>j=0,by decide⟩
  . exact⟨fun j=>j=7,by decide⟩
  . exact⟨fun j=>j=3,by decide⟩
  . exact⟨fun j=>j=3,by decide⟩
  . exact⟨fun j=>j=4,by decide⟩
 have g:u0 gs 8 o 0=range 8:=by
  unfold u0;simp only[mH];rw[List.filter_eq_self]
  intro a e;simp only[jF] at e;exact decide_eq_true ((qw gs 8 o 0 a).1 (z ⟨a,e⟩)).2
 let d:Nat->Nat:=fun a=>if h:a < 8 then un ⟨a,h⟩ else 0
 have h8:af S 0 d:=by
  refine⟨?_,?_,?_,?_,?_⟩
  . intro a e;rw[g,jF] at e
    interval_cases a
    . exact⟨trivial,by omega,by omega,by omega,fun _=>by omega⟩
    . exact⟨trivial,by omega,by omega,by omega,fun _=>by omega⟩
    . have s:∃x y:F 8,fG (update x 2 false)≠fG (update y 2 false):=⟨fun _=>false,fun _=>true,by decide⟩;have h9:=(wz 8 fG gs o 2 11 c.gP c.gQ s ax).2;refine⟨⟨2,s,by simp[v3,u4,wf],?_⟩,by omega,by omega,by omega,fun _=>by omega⟩
      simp only[v3,List.take_zero,List.drop_zero,show u4 8 [] (wf 8 2,[])=(wf 8 2,[]) from rfl,pC,Nat.zero_add];rw[S.ak];omega
    . exact⟨trivial,by omega,by omega,by omega,fun _=>by omega⟩
    . simp[d,un]
    . exact⟨trivial,by omega,by omega,by omega,fun _=>by omega⟩
    . have u:∃x y:F 8,fG (update x 6 false)≠fG (update y 6 false):=⟨fun _=>false,fun _=>true,by decide⟩;have h9:=(wz 8 fG gs o 6 11 c.gP c.gQ u aw).2;refine⟨⟨6,u,by simp[v3,u4,wf],?_⟩,by omega,by omega,by omega,fun _=>by omega⟩
      simp only[v3,List.take_zero,List.drop_zero,show u4 8 [] (wf 8 6,[])=(wf 8 6,[]) from rfl,pC,Nat.zero_add];rw[S.ak];omega
    . simp[d,un]
  . intro _;rfl
  . intro _;rfl
  . intro x2;have:=((qw gs 8 o 0 (8+S.pg)).1 x2).1;omega
  . intro _ x3;have:=((qw gs 8 o 0 (8+S.pr)).1 x3).1;omega
 have a1:=em c S 13 0 (by omega) d h8;have a2:(u0 gs 8 o 0).map (fun a=>(e5 gs 8 a,d a))=i1:=by
  rw[g]
  have b:∀(i:Fin 8),e5 gs 8 i.val=fun x=>x i:=fun i=>funext (m8 gs i.isLt)
  have b0:range 8=[0,1,2,3,4,5,6,7]:=(by decide);rw[b0]
  have h0:e5 gs 8 0=fun x=>x 0:=b 0
  have h1:e5 gs 8 1=fun x=>x 1:=b 1
  have h2:e5 gs 8 2=fun x=>x 2:=b 2
  have h3:e5 gs 8 3=fun x=>x 3:=b 3
  have h4:e5 gs 8 4=fun x=>x 4:=b 4
  have h5:e5 gs 8 5=fun x=>x 5:=b 5
  have h6:e5 gs 8 6=fun x=>x 6:=b 6
  have h7:e5 gs 8 7=fun x=>x 7:=b 7
  simp only[i1,List.ofFn_succ,List.ofFn_zero,kB,mS,h0,h1,h2,h3,h4,h5,h6,h7];rfl
 rwa[a2] at a1
def rG : Nat := 0x801222a23090201181a1903084020602848180a8c9c8e1a2111c1e1d1310c2444644c2c241c8c2c94340201181a1903082124280509140211051206a1a2a4a6a5a30a0142480309a2c28acaaae28aa2c2e2caaa41444246434520180a2812301851545815191102213003120c4424642c4c1c0a8c980e1a2151c1619131e4d4ccc6c5e2d2cac6c3e1d1c9c5c3e0d0c8e4b4aca6a5e2b2aaa6a3e1b1a9a5a3e0b0a8ccac9c8e8dcaaa9a8e8bc8a898899486859286839189858390d4745c5655d171595553d0705852644c464562524a464361494543604864342c262562322a262361312925236030289c5c3c1e1d9858381a199434161591311915139030124c2c0e0d4a2a1a0e0b4828090605120603090503c4c4c4c4c4c2c2c2c2c2c1c1c1c1c1c0c0c0a4a4a4a4a4a2a2a2a2a2a1a1a1a1a1a0a0a08c8c8c8c8c8a8a8a8a8a88888888848484828282818181818054545454545151515151505050504444444442424242424141414140402424242424222222222221212121212020201c1c1c1c1c18181818181414141411111111111010100c0c0c0c0a0a0a0a0a0808080404020202010101
def cG : Cfg := ⟨150,300,396,426,0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3ffffffffffffffa3ffffffa3ffffaba3ffffffffffb3ffa3ffffffa3bbb3aba071c71c71c71c71c71c71c71c71c71c7fffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000000,0x3fffffffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffff,0x41041041041041041041041,0x75d75d75d75d75d75d75d75d,0x820820820820820820820820,0x1041041,0x2082082,0x1d75d75d,0x20820820⟩
def xG : List (Nat × Nat) := [(0x2aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa934c003f0004d33234c0023013a8003f087e021f808449f07e021f021f80847e04253c00f8003e000003c0f8003c003e0000f800007,0),(0x33333333333333333333333333333333333333333333333333333333333333330e9404c00009404d5abffce2804c04c017c205f0817c17108225f105f08108824be2e41f0007c001f01c000007c007c00000000f838,0),(0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c00000380fff00a94e00001500a03fa80f8843e210f883a27c41e223e210f83c43c434be000f8003e00e01f007800f8003e0f00f00c0,3),(0x3fc03fc03fc03fc03fc03fc03fc03fc03fc03fc03fc03fc03fc03fc03fc03fc0253a3fc08dc3a500094e8c0725023fc0210848421fffc04108484448421ffc083ffc10000000003fff000000000000003ff000fff00,0),(0x3fffc0003fffc0003fffc0003fffc0003fffc0003fffc0003fffc0003fffc00000380953013380a800000004ff940953421090842210a48fffe08010842fffffc08080000000000000001fff800000003fffff00000,6),(0x3fffffffc00000003fffffffc00000003fffffffc00000003fffffffc00000000e00e02556501c03f02354094030e02584213ffff4210002109108bffff211109108000000ffffc0000000000000ffffc0000000000,0),(0x3fffffffffffffffc0000000000000003fffffffffffffffc0000000000000000001500e3800000003153bf01c01501cffffe10848420007ffffffe108442000221003ffff00000000001fffffff000000000000000,3),(0x3fffffffffffffffffffffffffffffffc00000000000000000000000000000000000038e00a00003f03ffc000000030afffffffffffffffc2100000000084221000003ffffffffffffffe0000000000000000000000,4)]
def nq : List (Nat × Nat) := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0),(0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,3),(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0),(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,6),(0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0),(0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,3),(0xffffffffffffffffffffffffffffffff00000000000000000000000000000000,4)]
def gu:Nat×Nat×Nat×Nat:=(7,0x5500550055005500550055005500550055005500550055005500550055005500,0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa,0xaa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55)
def gt:Nat×Nat×Nat×Nat:=(30,0x3333333300000000333333330000000033333333000000003333333300000000,0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc,0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333)
def gp:Nat×Nat×Nat×Nat:=(60,0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000,0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f00f0f0f0f0f0f0f0ff0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f)
def gG:V:=[gu,gt,gp]
def hK:Nat->Nat
 | 5=>2
 | 6=>31
 | 7=>140
 | 8=>396
 | 9=>558
 | 10=>316
 | 11=>59
 | 12=>7
 | 13=>1
 | _=>0
def LG:Nat->Nat
 | 5=>2
 | 6=>6
 | 7=>9
 | 8=>10
 | 9=>11
 | 10=>10
 | 11=>7
 | 12=>4
 | 13=>1
 | _=>0
def HG:Nat->Nat
 | 5=>0xbf794e9f6cbc
 | 6=>0xf61ca4ecf4a1e73467df6b26dd565bd356cfc97a04c63fbdbd49c9bd1887babedab196d7ae7220a08dde9c9fee97fd388cefd77c8307744d0e6dbbb36ac9266530145726244d9ecc48599e484e14455e1c3d77242500df0ed1f206160e
 | 7 => 0xfbaf52fb9f0df6c5daf6c13af5efd0f5cf38f51be2f1c155f034c4ef0422edc079ebc163e774dde6a89de49876e291e0e146eadfc0e3de8cefdd671cd8d535d70efbd4ea29d4df48d17e2cd09ef4d079b0cf1902cb17fdc9fd84c9527fc7e9e2c688c5c5821dc1657cc099cac04143bfeb50bf000ebde392bca762bbf60ebae8a0b9bef0b85afbb7f613b7c462b6fd3bb69f1ab262afb20802b0fb6aae31d0aa598faa5793a93aaca8ca97a7263da034b1a01e679f0e6e9ea75c9e97559c52849acbb99a45b09a175799207698b7719831b3957b0194fcfc9443c3934012928b099151368cd15f898c5082f1897f8ad67f63ca7c935c7b8b0679a36478a1ac7501a76ed6246be62c6a912169a89368506b67e51f67446f655f88639eb4626cfb62359c5f6def5f43e55d68a85cd3e95c9e055ac87c542c105314535090b74d0b444a9aff444adf3ff1e93fed6c3eb31f3d1eb93d01f13bc68a3337722c98132b448629532927889e2596c023ee5d22abec2288f11e3d121e2c1f1ddaf01ca4b41a01ba15935a1508e514e25a13b06e13986d0c37820949ec08ee6407ebc70675c705f336
 | 8 => 0xff8f9cfefceafe6cf3fe6959fd8704fceca2fc8ac8fc79d5fa529cf91bb2f89542f87e42f7fdaff7063cf69b56f6943df4c39ef17f9ef0c79bef659def1effee3fd1ee0dafed195cecafb0ec34d4ec2172eba5cbeb52d7eb0af3ea5404e97e49e8ed06e8de1ee83a6ce6ffc1e52287e4a92be3c122e23d29e1eb57e1c087e1623ae0d5afded781de94b1dc2cf6dc1558dbfd92da3a56da17c3d8fbbad8dab8d871dfd806cad7fc48d7dec2d6c4f0d65ed7d60bc2d5fe63d5c58ad579e4d5451dd4dc06d393b7d34f5cd30b60d0b872d03ec0cfcaafcf851ecf4f81cd9116cb3f43ca8347ca5fc5c99385c987f7c945d1c7b4e7c6f97fc5e66bc5a3c4c56eddc5440dc3da0ac3c8f9c2cccdc1274bc0e64dc03c39c01e69bfdcd5bf9cfcbdf4e4bcdc73bcb9c2bc6ad6bbf565bb8e24ba8985b9f002b6d5f1b6d319b66465b49c9eb4545ab44a6fb3de15b28c75b28aecb12a4eb0c925afeec9af99e8af3ff0af1520ae3357ae32e8ae0cb1ad66b8aca059ac3d67abebadabc755aaaa01aa5373aa177fa9fce5a96e0fa8e4caa892d7a74c7fa72787a68ad5a672b1a66289a63798a5c678a49bf7a489e3a40e60a3a1efa371e9a195d3a14a78a14183a13c0ba0b7aaa0b13ea05e65a04f1ca035789d45839c5bff9b45e39a99b999a55d998a02991312982f1a97d2a7977d1196e2f1963b2a92b5dd911d92911cb8904b3f900dba8fe0568fa1668f6f338f1cc98e122b8dd6f98dd2938d73028d1ed68c90ca8bb57f8b62908b1b8b8b0f0a8a682c8a2ede88a745889cb0855c7c83f50982a84e81f95681a3ba81924481201e8061967f28667ec59d7e6c1d7d032f7c905e7c0b5e7ba2597b75257b15ea7aa8967a830679f65879176178436477e7e477c55c77a80c774832772eab75f493743c1e737f4871fbae718c6e7037667018cc6dc4586d86da6c77386c12716bb8b06a401d68bc046896b06714c566fa646669f265f12d651d3f6454e963f06463438f60eb8460932d605bd46055515f7e445f3fdf5f21015e99705e75ee5dc39d5daaca5c8e4c5b4af15a10c459e9df5973cc5829cc5722bf56ba0e56748d54fc7654e39b5488b95452625432c753f25853dc4552fe1751c10c5198c1518d2e5148475023294fc2404f570e4ed1144e049f4df2014daa5e4c71b04c45714b6c804a266448fcf1488b3248825d486a834860984839fa4818bd47ff2f47fa6947f6494794b04788ba45e2ba45bb5f43e44e43e1d7431e0742a82f42a19a41e83a413491408b214053904001d63db3643d09743cf7523ca9003b195a38c48138bf3637d5b236740436447f353d9334dbb9337be5335a5832b044320dc231d04231a851312de430b5312ff62c2fb3cd2f6de52f21932f10f32f01182ecfe92dc9822ccdbb2c4e612b2a1f28f6c9275ea026d7d226c865245612243be823e7da23d2e023855c22959421e38d21527220fcc7209c021eb1721cff6b1c88451c393b1bded51b60eb1b5c3e1afef71a791f1a1cbf16a251152bd715227a151c5e14ca88148de613afe412fa0111c5a80f458b0e2aa20dcde90cc9620c74a60c54d70c53e10c533a0b83d80acf8d0a35940a08a409ceeb099a980964df0886d70881a807f3b40573d9053bec04c3220435b700ee5400ddba00bdc30082f1
 | 9 => 0xff8fc1fefdaffe511bfd8a16fd011dfc5ad2fc4cb8fbdf21fbd69bfbb472fb7326fb275dfb168efaf86dfaccf6fa78b5f9429df94031f8f8f7f86a98f816bff7bda5f7b803f778cef72714f6e8a8f621e7f49870f46c33f3ce3ef2e7e7f1d1acf13f9af1253cf1157df0b8d1f07462f054a8ef7a1def3fbfeeb3adee9a0aedb5b5ed8518ed74a3ed286dec4fc7ec3454eba549eb51d0eaad8aeaac83ea17e4e91868e8df0ee76faee61dcbe53c02e53861e50dd6e4f870e4a2c6e449c8e3ac8ce313b0e31144e2d000e29ec1e26b85e15441e10d9ce0bed7e092eee03e29dff2fadf9b82df6a58ded45cde9017de8accde0348dda2f6daee5cdaaa9adaa897d9f124d994c3d95c7dd94b30d8fa83d8e8b9d84fa6d849ebd82213d81bf6d757c7d7562bd74fc1d66b4fd60567d5b5a0d3f7e8d3e8f7d25904d21a7bd16e9bd14fcad0cf73d031f7d01e8acf5b99cf288fcf1392ce3dbfccdb41cc6931cc36afcb847ecadeafcad33eca8feaca8ae6c94aaec8612ac8232fc80114c7f6cac73430c6e34fc6aa11c4f9c1c4bf6fc47badc45c66c450f6c365d6c35694c32d90c30b8fc27602c1ed09c1c269c01b97bfaff0bf51fdbf1d2cbe7ec1be2c1dbdc8fbbd02abbbe6a2bb7d0cbb1bd7bab2b3ba2220b93398b8f6aab87951b8748bb7d1d5b7d007b6965db65cdcb607c2b5cbe8b5838bb44e37b3d9c4b3a210b38869b2df1fb2c9e3b27dd0b23a69b19698b07bfeb0507baff20faec5bfaec28dae8fd9adbef7ad7174ad6e2facdca2ac7993ac72dfab7583ab6af5ab31a9aa1ebaa9ecaaa93ea3a87d47a82ef5a7fd30a75e79a6ca3ea6a031a637c2a5f988a578e3a4eceaa4bc0ba3f17aa39ff4a32721a31a26a2d937a287e4a27627a26d91a23dcfa1a8069fa4aa9f9cfb9f1d129f00929ee04d9ead679e36399de9ab9db1b49d8f649d73239d597c9ced4b9cb71e9cb0329b12ea9a218e99fead98e5c59895d7985312981d7a9735579660a296572196488a962c2394c12f941bc893054992a3b1928a4e924e5a91427d8fca9b8fc40a8fbf2a8f16db8ef9098d94e98d7d388d23a18d222b8ca3818c3ea48b27b08afb038a94fd8a377f89e5ad8966c988d1a588b69788074c872b7886d1d7868cd7868831865cd185a5f9853b6584b3098481df815a338124e28031b57efef47ebf467e63397e2e0d7e12137dbfe07cd65c7c74c47c694b7c67487c5b617c316d7b91207b14527b139079daa779d66979b0da79898d78ca1c77bf8376be957473e574121f73ee4d73b1ab73829d734790730410725a1b71d9c97140da70fd1370fc8b70a52470a2ea7056e16ee37b6eab366d88616d69336bf3836a6bd96973ed695cc06844a968368f68056567ff2067f3af67ec85677d0067452c66ebb7663a5e6630a4655826653dc0650df16434b363d66663c4aa63abba63a77c635aa063570c6256e961a7f85feace5f5a025f15f85f0d035ece375e87d15d6dee5d5bb55d18a35cd5235cb10d5cae825b85155b80f15a85425a28a159f86b5972b058df7b587c4958728f586539573a4657153156661d5476405422e853a760536f615303b45288fb524db25207a251d67850d0a450af405035104f96634f952a4f89ab4d79ee4cf7734c8f7a4be63049bbe14990294975dc48e70b48dc15488b664817f048082747b8394761694685e4464e3645e94b45dcb745cd7645986d45423d453fd944cae644c9ca445655440bea43f9b4438582437e15435b684343c343403943111941dd7141dad54191454184584132943ee8303e988e3e429c3cfbac3c1ec53c1bce3bc7fa3ba8963b74a23afd693aceb43a317b39a4f638c5183807a3373d4a372ae6372a0836c886360c8135e8ff35be2f345f25326aaa326282323d5d323b2831894c317ddb30584f30171e2fdae42fac842ed2a52e9add2e5fd92d33e42c6f872bc5732ba45e2b741a2b4b802b07032aad222a4412296cd128cda2284e6c26de87266673263d16255e5b249fc7247d1324028e237ffc23050e22d033216d622130ba20fbf91fe23a1fdd941eb7041e31d21deee91da26f1d23701c7c7a1b7a4b1b799e1b2f131aaf96195eec193c9c18c93218a3b817c6a11774e717580417546316658515beae15bcab159b2c15705c15452d148d67141c111418cc13ab9f133de413300a121f7f12159211e35f11c49a11bad10f7bc30f5e8d0f2f6e0f27e40f0f1b0dec920d17950d03dc0c21b40bf31c0b62470b3de50b1cd00b1b710b01cd0a448109d382084cc908244b08009907bffc077382073f8d067564067044064d8d06008d0586b805002604e29a0215fa01a4ff0180bd00dc77
 | 10 => 0xff732bfd56a3fac2a2f8f1eef8a996f87045f7a59af74bf9f625d7f5e31ff56285f1f7cdf085bcf03c43f0027def5bbfef2ce1eea82fee21d7edc80fed3c93ed2f69ece36decc420ec9e3dec7361ec0540eb0b6feae6dbeaaabbea54c9ea508bea03afe98b9be727b6e64f87e5cb38e55fa3e493b5e3c1b2e37e32e2c301e28590e27e2ee1abb2e16eccdf37a0df2558dde355dc99ebdc597bdbc8e0daeef0d935b3d8b0b1d87f87d69533d623e5d47bced444cbd3bfc9d33f90d2ae64d064f0d0209acf901acf30b6cd5fcccaff64cad318caa2c3ca06f6c9ecd2c99a8cc8e850c7b2cbc72cb8c601b4c5a287c373dfc2c7d4c2aa12c0fb39bfc515be8ffabe840cbe3bb6be15debd9582bd90dcbd7195bb0cfbba7bcfb89befb8325bb831b4b758e3b543ecb36ff3b0fdcbb0e352b0171dafd2c7ad63eaab48d6aaab9da99628a8d6cda8551fa7e449a7a508a74d12a70b60a6d426a686a3a48ab2a32833a26d029f4cc79d23c29d09b29bee3c9b3d5e9ab46599e6f398c88e97e4889734fd96f37995d87d95ca0792123a91aadc90dc738f3a1b8ed8cb8e690b8e4c518e1c918df4708d32b78cf69c8ba9358ae8d88a7d198a57ac880e38875735869256868a6d8686538638d084c891843cdf83aa2c825d8181eb7a816d9d80c48c807a4c7fa2067f6f167ec0e47e66b47d91b77be34d7bdbc47a535a7a21c279992078a9de787abb75c1db758aaa755cbc74b9eb7428bf73757671fadf71df4b715699714504705b806fcdc36d9f346d4bdc6cc6da6c51b16ba17f6b53156af2d76ad8b86a09d969bcbf69ba536940296891f768868667c065669c096441e464246d635c5962ad09621c76620fae5ff43f5f54335dff3a5cae765c845c5b42e15a9206593624584ad155ecfb53daec52a623523c035191785187be5138f94f0a394cb5c34b939e4b687e4b53364b24bc4b21774a707d4a0ee549d69f496c80491e3d48961846308f459db84513f444720a42241c421be44173983efe7a3e5af83df8713de0153cb0d13c5d983af32436065a3385b133616f31cb0a3139eb3095b93001a22f6ecb2ea63f2db65b2b95f92a6f44284845282c0b27c98426f6d22665a626460a26286325a03a242437241c3224028b238b7623594122820021639b20ca9d20094b1f9e401eb0a71ea6191d92421c16811b9c1d1a15ce18f7691878121673aa1583c614aec912e7b310e65d0ff9760ff1640fee050f7ab40eb05b0e586c0d31400c53130b34ae0ad98709b8e607273506dac40450c403e3ec03ce5f037f6b031dd303047002cc0102342d01bc9f0115c800d9d1
 | 11=>0xff52edfb62fafad1cef8885af7048ff4c9a1efe938ef3b06eacd7ce3ef98db935dda83fbd83a87cf2ecacbbd03c8c4f3bf16e3b8ffddb6aab1b617daaed51aae7293a8e7f6a2452c9f0eb79b98e096a28592fc2291ddbd88dfca8569f374cae672ae4f718fea6dd0c56b3cc4696c10667e626271ef5d3e425b24dd56c9a955d9c5504f7544beed4439eb37a6da367bd631755b303f372efe2e291611215d741dde0c1950ef1785820af88e076d9b028c5c
 | 12=>0xdf64b6d6f8847b72b03fa8ec2f91050f88d90c1302
 | 13=>0x4fded8
 | _=>0
def PG:Nat->Nat
 | 5=>0x142600003829
 | 6=>0x1147b000228a10001a83100005ca100019ca90000c459000088510001d4a100009451000050a1000008a100019ca1000228a9000184a90000e83b0000dc3900022c5500010c590001ac71000184a1000178a10000f0a1000128590000b861000058a900011479000104a100004871000008a90001148b00005431
 | 7 => 0x3ac6a0003603b0000bc550001c49900055cd10005e071000554d9000190510002c4d100024c75000360a30005e8260004fce10004f8d90003609b000618d1000200a3000288bb0002582500002055000260bb0000d4d10002883b000230d100022471000464d100022cbb0004e02d000200bb0000a499000440e1000404410000d82d000340990002582d00018cd10002003b00040899000590410002889b000580390003bcd100047451000160d10003bcd900046051000510810000782d0003b0e100062cd100053041000388d100038ce1000340310001f0710002009b000358e10003e026000164390003104100005c75000324d900039851000300d1000474610001e89900010459000304d9000300d9000474d9000360390002e0e10000503b0001c0c9000344510000fc3900037c750002a8e1000030bb0002602b000144260005bc55000250e10005bc570002042600059475000200a100002c510002609b0001a041000104990005343900001439000474d100048cc9000460d1000308d10002d0590003d0d100016ce10002d0d10001f0990004f475000134d1000544d10000e0260000503a000358d10003389b000360a1000388590000a47100026831000344d10000b0e1000224310000d451000300590002249900033873000024d90000902d000368d100001ce100061431000610410003407100062cd900005053000600d10000e83d0001a4710005bc5600039cd10001e8590005c8d90005e09900062c51000360bb0005a8d9
 | 8 => 0x65c3f000470f300021c250007a1110003b83900081853000678c900021851000818cb00020d0900024c260002847100057909000761190006f05600015d09000370d3000708d10003f9090001e82e00013c2e00001c79000330f30006e90900031c39000200550000804100001d0900048c6a00077d010003d4f30006e911000045090002fc510003c0f30002ccda000640530003910900045c92000080c90000bd09000648aa0006783100005c55000680d1000860c90002545100029cd30000982e0001d42d0006611100065cd1000284390000650900027851000830a1000330eb000218990006d8c9000645090005dc820006ccd10001287500008051000314db0001402d000304f3000238e3000210eb00083109000518730003c0cb000601190005f9110000d4260005d9190001bca20007a079000380920006e42e00087c510007a1090008609900050c410001bcdb0005ad190006b09d0008590900028cbb00054899000178a200057d190008410900026cf3000570d100074909000238f300055d110001e42e00054d110005c026000210f3000508c9000779090002d42600014cf30004c42e0001e8fb00048cac0003d02e0003c03f00077c99000060530004c84100072c5300028c300001bcf30001b8d300019d090004707a0002e0260005842d0000a5090000d8a20000d4da00074cc90004c1190007751900028c9b00006073000194bb0000e8d30000acaa0000d8db00026ccb00017cf30007449900052c3d0003a4c9000178f30006f855000304d30008447900047d19000420560006cd0900008cf3000040d10004f0c900082c7900045441000178530000509900013109000224a100012cdb00068053000009090007203d0003d47a00048c260000f509000040f30005c45500002cc9000194300000e8f30000d8f30006007100072c2b00088ccd000790790001b89a0003e11900066ccb0003d4d90008aceb00066c730000acf300028c2f000374790000d8530003dcc900008ceb0003a4410000809900026c3f0005605600038d0900063c3900002d090000e50900082875000040eb0005703f00056471000178cb0003189900080875000218c9000541090003c05b0006e8790006803b0001b85a0002ccaa000304d100048cbc0003c0d300007c3d0003dc990002b8790002e9090008acdb000380260008182b0002fd1100008829000390c9000674750000d099000630530002d1090002b9190003c4cd0004c07100046ca10000d8cb0004bc310004f051000818f3000254c900049c4100072c29000285090002791100046d0900022909000218410006bd0900048cc40004bcc9000229110006f0550005c8260007a511000215190001bc7a00088892000508710006f0570004290900020111000794f30004b9090004cc510003c0590001dd110001b8560001787a000678990003c0d10001d1190003b07900074c99000425090001bcd9000680390003b10900027c3d000680d30001946000072cf30006403f0007fc3900077c710001502e000648da000548c9000210d300065cd3000708f30005a03d0004842e00070c390006f4d300048c840006e10900014841000640d300000105000050c90006f0f30006d909000155110002809d000390510006d0f30006282e0004082e00045c260005dcaa000794cb0006b8f30000d87a0000d4aa0005cc7500019cc9000119190000ac82000680f300077cc9000778a100066cdb0000e8d10001909900065cf30000d8d90003045b000064790000bd19000570d3000640fb000375090000a919000630730008182a00062cf300007c2d0006642d00029c3f000824250005387500014ccb000050410005605a0007c42e0006f49a00029c53000210d10005dcf3000868490007943f000205090000d0c9000025190005b4db0001947c00028c9400072ccb00088026000858790002b90900065ccb0006f42e000570f3000708d300022509000560fb00080049000470a200026026000865110002ac71000845090007dc410008591900003d41000868cd00082d090000949d000310750005c0920007202d0004cd0900042055000680cb00031c710008882e000254710003d9090001c8c90005189b00030459000420570004bc990002fc71000194940003d4a2000774e10003ec750004f039000791090006d03e000040d30003d4db
 | 9 => 0x29133000044b4000450cd000118ac0002853b00006cc9000435590000b0c40000ad490002813b0000b0740001fcd30002dd0900042d1100021ccf0001f52b0001e90b0000a0fc00026d33000324740002e4710001389d0002c94900004c3b0001610b00025d330001d0eb000010f40004d03c0004947b00009901000241330004ecbc000470730002cc530002c4920000b959000074fc0001b52b0001ac55000235330000a8520004bccd0002b0920002dd0b0003249c0001ac570001a91b0003b82e0002251300021d130003b0e100019d230004d0a4000050a2000184c90002050b0001d94900019c82000044c40001fcf30000dd490001f52300006c990001e9330001e50b00005901000409010004d49c0001043c00017d23000299010003d45100025c530001d0e3000160da000370e100003871000398c00001743b0003b1050003c0710001691b00038d59000010fc00004c520001552b000151130001b5230002cd03000374760003d4730000bc75000074ac000460f4000130c90001ad330004ecc40003cc550001a9330003d5030001352300019d3b00036909000324a40002d50100008c750004d053000334aa000320dc0000a9030004d0c40003247a0001fc6a0000447c0001e853000114db0001d85100017d13000284ce000179130004d03a0001749b0001751300025d030003e9030000c4cb0002cc510003343e000204ca0004dd4900016933000161330002f8ac00006899000155230004814900015133000104e3000010ac0001453b000368550000f52300041476000018940004ec8400017439000460fc000135330002e4990001043a0004ad490000e11b00004d0300017452000495090000f4520004707100021ccd0000b09c0000a8d20000102600025c51000114f30000c52b000260720001e9030004d4940000b5230000b0db0002e55100049c710002047a00007c550003490300000099000398ec0003c099000290aa0000b4820002a0a10004394900029079000078d2000104f30003b4a1000150920004310900017cca0002c511000408710000f533000174990000791300026ca20000e90b000418990004504a00011454000314cb000071230002b4d20000e1330003b549000050da0002014900004cd200016873000309030001e851000174ca0000651b00004430000044a20004b4990000c5230004887500027d590002e43900017c3e00004d130002609b00044d0900010c920000b53b0000b0f30004104a00026d110000a933000098c900009d3b0003ec2e0004950b0002dd03000050d20003a8550001fcac000398fc000320ec0004402e0002610300021c3700036c4100029941000018eb0000152b0000793300000923000071130003b159000144ce000185010004ece300026c3f000204760002907b0002350b00005549000065330004310b000058c9000008da00036d0100038d4900020159000051330001fcd100004d330004d4eb0001e9090001b0a1000044f30001ac560000a851000260730004b91200037159000494da0001510900002d0b00013101000468c9000324c40004a92300044d0b0002190900001d13000018e30001b159000320fc0000153b0001a87b000174cb0000746a000009330002a4ec0004710b0003542e00046d2b0004ecf300019101000169030001a90b0001d90100018441000160aa000060920004512300044d2b00042cd20003843e0003e8cb00004c510004d4fb0002f8c40004d0f3000070ca0001043b000431230003cc5600042d130000f45300022503000118dc0002809e000278c900015d59000411230004a91300009cce0002cc7300034c940001710500015111000495330003247c0000a85300026099000038c9000320ac00013041000444990004753b0004713b00046d3b0004147a00034c9c0002cc520002a4fc0001510b0003e92b0001d0cb0004c5490002b4d10001fcbc00031d490004511300044d230003cc5700037c3d000174c900031494000298990003d5230004d03b0001114900036856000431330002f8840001b50300042d3300025c73000198cd00023509000208c90002a14900046d090003d452000291090003ad2b0004153b0004113b00025c5200004c53000450cf0002789900024c550000448c0000687100038523000260710000a8a20003f10b00021949000104390003e923000110750004a8ca000284420003685700037523000175030000f451000148cd000249490002b50900046d0b0004083900002c9e000480d1000241090003690b0003dd13000074dc0003d5330001a8790001fcc40001cd490003cd330001e873000174530004d0cb0002395900019c76000078a2000104530002b4d3000104cb0000f4730001e8520003ad23000334da0001a9090000f50300020899000324a200034ceb0003492b00000071000044a4000050aa00004ca200007d590000709e0003853b0000791100004c710000447a0004a88200016ca100036cc90004c5090002910b00037513000474ce000408c90004d0390000c83d00032912000314eb00036933000010dc00025c710000a82900004d110001b1490003092b0001fc840004ecac00016d490000a8730002fd230004b4710002f8e300046cd1000469010002b50b0002e92300034ce30002410b0003314900046cd2000174510001d094000470720002dd2b000335330004dca1000324f30000c50300016509000001510002c51300041d010002b91b00019071000055010002b52b000290da0001e87100046cd30004b8da0003090900004c39000161090004d080000039010004aca10004dd59000118fc00004c73000494aa0003090b000114c40004947900026cd2000224cb0002fd33000285230002f8f3000374ca000281230003e8c900027075000178530004a8760002e93300026d1300049d010002610b0004b551000280aa0000a82b0004602e000104c4000468410003c5010000b4760002c951000074ec0004709b0001d09b0003a546000241230002cd330002c533000410ce00030d4900042ca20002b9330003d453000165490002b5230002351b000471030001b4cb0002252b000398bc
 | 10 => 0xb8790000616b00005d6b000059230000a07300009cbc000050990000c83d00002cac00005caa000060cb00005123000081020000350300004c570000d943000034540000207c00006d5300009477000098ce0000e4ec0000343b00004d4b0000e0d4000024940000697b0000d85300006533000049630000dcb4000030550000509b0000009e00006183000044db000048aa0000411300005d8300007874000024cb0000591b0000947600002d0b00009cdc0000bca30000a0d20000b87b0000a0990000c8d4000080aa0000513b00006cce00003057000034d20000789c00004d7b00009cc0000049830000395b0000a1510000e4fc0000e0fc0000dcc4000044f30000589e000041330000c12c0000d8510000250300008c3e0000b8ec00009c6a00006143000058a000008c400000314b00002d1b000040540000649c0000d1010000c8fc0000b52c0000252300007cdc000020db000051030000397b0000a09b00003533000078a40000e4ac0000e0ac00001d6b0000dc7c000064cc0000809e0000204c0000c13c000031830000a92c0000b8fc00002d330000155300002499000061010000251b000054f4000020f300009cec0000343a000061020000b53c0000bd49000034510000b9090000d10300001d63000050c9000064dc00006103000050ca0000c0dc00001983000068a1000064790000b8ac0000157b0000a93c0000443c00009c5000000163000050cb00000d4b00001cce0000e96b0000c83e000050cc0000149900009cfc000000aa000040520000249b0000e50b0000d1430000e11b0000dcdb0000343c000034bc000054f80000bd4b0000345300007cec0000b90b0000e0d2000044a40000a072000030560000054b000014920000a0510000d16b0000cd630000b0550000c83f000001830000387200004d4900008cfc000068a30000e9530000647b00009cac00002c54000040730000e5330000e1330000853c00006ccd0000dcf30000208c0000d8cb0000d953000034d4000041030000b057000034a20000149b0000e47100006ccf0000d0c900007cfc0000bd6300004c55000078c40000d1630000cd53000019060000b91b0000589d0000389b0000c9330000bd120000a1430000d85200002cdc0000589f0000a0530000e46a00004053000039430000b14b000020a40000e9020000552c00000cce0000bd7b00007cac00005c9e0000b9330000787c0000d8c9000020900000e09c00003873000094750000d0cb000034730000a10a0000d902000024ca0000e473000064fc0000cd02000044bc0000a15300009d1b00007494000044540000489e0000ad830000e0cc000069490000553c0000955b000065090000407100009c6c00001551000034ec00008c3d0000154300008d23000064ac00008c3f0000a17b00009d33000044c4000040fc00003899000024cc00002cf40000994b0000957b0000e4dc0000e0dc00001ccd000081630000589400002c740000dca4000040510000d90300009c4f00007d1b000078db000020b40000e89e00001ccf0000694b000050940000650b000034fc00008d330000a0520000a0710000e5090000447c0000b0560000c840000038710000e503000081530000cc9e0000ad06000034520000203800002cfc0000343900007d33000078f30000c8a80000d1020000c114000020c400006d6b000034a40000b8dc0000d901000024c9000060c900002d09000069630000bca10000651b00004c56
 | 11=>0xca400000c3e0000085200000839000014c00000113b00000478000008a400001462000000fc00000903000008540000083b00000d1b0000046c000014ec0000091300000d33000014380000143f000014fc000000540000093300000c620000051b0000010b000014a40000083a000008510000051300000133000010cc0000083c000008530000107800000cd4000004ca000015130000107600001464000008d4000008710000003e0000153300000040000014370000106c0000087300000cec000004760000143d000004cc000008ec00000c40000014bc00000cfc0000111b000008fc000014d4
 | 12=>0xd3000000240000009c0000002c000000280000007400000034
 | 13=>0x0
 | _=>0
lemma ej:gX 8 fG rG cG:=jn 8 fG rG cG (by decide +kernel)
def fe:Nat:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def bp (all1v g:Nat)(e:J):J:=
 if ble g 32 then
  zm (sub g 1) fun c =>
  zm (shiftRight c 1) fun i =>
  let u:=beq (land c 1) 1
  let (a,ta):=jw i e
  let d:=if beq ta 3 then 2 else 0
  zm (xor a all1v) fun w =>
  let r:=cg i e
  if u then (w,d)::(a,0)::r else (w,d)::r
 else
  zm (sub g 33) fun rem =>
  let s:=beq (land rem 1) 1
  let t:=beq (land (shiftRight rem 1) 1) 1
  let v:=beq (land (shiftRight rem 2) 1) 1
  let (i,j):=ik (shiftRight rem 3) 16 1
  let (a,ta):=jw i e
  let (b,tb):=jw j e
  let r:=cg i (cg j e)
  if v then
   let d:=if beq ta 6||beq tb 6 then 8 else if beq ta 3||beq tb 3 then 1 else 0
   zm (land a b) fun w =>
   let r1:=if s then (b,0)::r else r
   let h:=if t then (a,0)::r1 else r1
   (w,d)::h
  else
   let d:=if beq ta 4||beq tb 4 then 7 else 0
   zm (lor a b) fun w =>
   let r1:=if s then (b,if beq tb 3 then 1 else 0)::r else r
   let h:=if t then (a,if beq ta 3 then 1 else 0)::r1 else r1
   (w,d)::h
def am (all1v:Nat) (xs:J) (PT:Nat->Nat):Nat->Nat->Nat->J
 | 0,_,_=>xs
 | d+1,s,j =>
  zm (au (PT s) j) fun e =>
  zm (land e 1023) fun code =>
  if beq code 0 then xs
  else zm (land (shiftRight e 10) 8191) fun pidx =>
   bp all1v code (am all1v xs PT d (add s 1) pidx)
def sa (all1v:Nat)(b:J)(s j:Nat):J:=
 am all1v b PG (sub 13 s) s j
def az (salt w tg:Nat):Nat:=
 zm (land w l5) fun w0 =>
 zm (land (shiftRight w 64) l5) fun w1 =>
 zm (land (shiftRight w 128) l5) fun w2 =>
 zm (land (shiftRight w 192) l5) fun w3 =>
 zm (land (mul w1 0x9e3779b97f4a7c15) l5) fun m1 =>
 zm (land (mul w2 0xbf58476d1ce4e5b9) l5) fun m2 =>
 zm (land (mul w3 0x94d049bb133111eb) l5) fun m3 =>
 zm (xor (xor w0 m1) (xor m2 m3)) fun wf =>
 zm (xor salt (land (mul tg 0x517cc1b727220a95) l5)) fun s =>
 gx (xor (xor wf (shiftRight wf 33)) s)
def ug (salt:Nat):Nat->J->Nat
 | acc,[]=>acc
 | acc,(w,tg)::rest=>zm (add acc (az salt w tg)) fun acc' => ug salt acc' rest
def ab (salt:Nat)(ws:J):Nat:=
 land (ug salt 0 ws) 0xFFFFFF
def dv (s:Nat)(b:J):Q:=
 zm (ab gy b) fun h =>
 zm (ar hK LG HG s h) fun j =>
 !(beq j 999999)&&jk b (sa fe nq s j)
def oa (tt:Nat):Nat:=
 lor
  (lor (land (shiftRight tt 128) 0xFFFF)
   (shiftLeft (land (shiftRight tt 160) 0xFFFF) 16))
  (lor (shiftLeft (land (shiftRight tt 192) 0xFFFF) 32)
   (shiftLeft (land (shiftRight tt 224) 0xFFFF) 48))
def g7 (w:Nat):M->M
 | []=>[w]
 | a::rest =>
  if beq w a then a::rest
  else if blt w a then w::a::rest
  else a::g7 w rest
def o8:J->Nat×M
 | []=>(0,[])
 | (w,tg)::rest =>
  let (rk,acc):=o8 rest
  if beq tg 4 then (add rk 2,acc)
  else if beq tg 6||beq tg 7||beq tg 8 then (add rk 1,acc)
  else
   zm (oa w) fun p =>
   if beq p 0||beq p l5 then (rk,acc)
   else (rk,g7 p acc)
def uk (s:Nat)(b:J):Q:=
 let (rk,cl):=o8 b
 if blt s rk then true
 else
  zm (sub s rk) fun s6 =>
  if ble 10 s6 then false
  else
   let (stot,items):=t7 cl
   if !(beq stot c7.fL) then true
   else m9 s6 items 0 0 0 0 0 [] []
def uj (b:Nat)(d:J):Q:=
 let c:=bn cG.fH d
 if dv b c then true
 else if uk b c then true
 else dv b (wx gG c)
def n1 (c d:Nat)(e:J)(g:Q)(a b:WF)(h i j s:Nat)(t:J)(u:List WF):Q:=
 let v:=uj c
 let x:=
  if !(beq a.tg 2)&&!(beq b.tg 2)&&!(beq a.tg 7)&&!(beq b.tg 7) &&
    !((beq a.tg 4&&beq b.tg 6)||(beq a.tg 6&&beq b.tg 4)) then
   v7 cG c d e v g true (cond (beq a.tg 4||beq b.tg 4) 7 0)
     a (cond (beq a.tg 3) 1 0) b (cond (beq b.tg 3) 1 0)
     h i j s (beq a.tg 0||beq a.tg 3) (beq b.tg 0||beq b.tg 3) t u
  else true
 if !x then false
 else if !(beq a.tg 1)&&!(beq b.tg 1)&&!(beq a.tg 4)&&!(beq b.tg 4)&&!(beq a.tg 8)&&!(beq b.tg 8) &&
      !((beq a.tg 6&&!(beq b.tg 7))||(beq b.tg 6&&!(beq a.tg 7))) then
  v7 cG c d e v g false
   (cond (beq a.tg 6||beq b.tg 6) 8 (cond (beq a.tg 3||beq b.tg 3) 1 0))
   a 0 b 0 h i j s (beq a.tg 0) (beq b.tg 0) t u
 else true
def hP:Nat->Nat->Q
 | 0,i=>match sa cG.fJ xG 0 i with | [(w,_)]=>!(beq w cG.fK) | _=>true
 | ns+1,i =>
  let c:=sa cG.fJ xG (ns+1) i
  let b:=c.length
  let d:=sub (add ns 2) b
  let (_,totU,totV0,totV1,wfs):=e4 cG c
  let e:=ble b 11&&beq d 1&&!(z3 cG totV1)
  if (ble b 11&&beq d 0||e)&&!(beq totU cG.fL) then true
  else if e&&ble b 10&&!(beq ns 0)&&!(zm totV0 fun fn=>b9 cG fn wfs) then
   d5 cG c (uj ns) true 0 [] wfs
  else
   (if ble 1 d&&!e then b7 (b8 cG ns b d c (uj ns) true) 0 0 0 0 [] wfs else true) &&
   a4 (n1 ns b c e) 0 0 0 0 [] wfs
lemma gU.inv_succ {s:Nat}{ws:X 8} (h:gU (s+1) ws):(∃a ta r d,ws.Perm ((a,ta)::r)/\(ta=0\/ta=3)/\(ta=3->d=false)/\hC a≠(fun _=>false)/\hC a≠(fun _=>true)/\hC a≠a/\(∀x∈r,x.1≠hC a)/\gU s ((hC a,if ta=3 then 2 else 0)::qk d (a,0) r))\/(∃a ta b tb r ka kb,ws.Perm ((a,ta)::(b,tb)::r)/\ta≠2/\tb≠2/\ta≠7/\tb≠7/\¬(ta=4/\tb=6)/\¬(ta=6/\tb=4)/\(ka=true->ta=0\/ta=3)/\(kb=true->tb=0\/tb=3)/\hG a b≠(fun _=>false)/\hG a b≠(fun _=>true)/\hG a b≠a/\hG a b≠b/\(∀x∈r,x.1≠hG a b)/\gU s ((hG a b,if ta=4\/tb=4 then 7 else 0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)))\/(∃a ta b tb r ka kb,ws.Perm ((a,ta)::(b,tb)::r)/\ta≠1/\tb≠1/\ta≠4/\tb≠4/\ta≠8/\tb≠8/\(ta=6->tb=7)/\(tb=6->ta=7)/\(ka=true->ta=0)/\(kb=true->tb=0)/\hE a b≠(fun _=>false)/\hE a b≠(fun _=>true)/\hE a b≠a/\hE a b≠b/\(∀x∈r,x.1≠hE a b)/\gU s ((hE a b,if ta=6\/tb=6 then 8 else if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r))):=by
 generalize e:s+1=s' at h
 induction h with
 | done _ _=>cases e
 | perm c _ ih =>
  rcases ih e with ⟨a,ta,r,d,c',g⟩|⟨a,ta,b,tb,r,ka,kb,c',g⟩|⟨a,ta,b,tb,r,ka,kb,c',g⟩
  . exact Or.inl ⟨a,ta,r,d,c.symm.trans c',g⟩
  . exact Or.inr (Or.inl ⟨a,ta,b,tb,r,ka,kb,c.symm.trans c',g⟩)
  . exact Or.inr (Or.inr ⟨a,ta,b,tb,r,ka,kb,c.symm.trans c',g⟩)
 | @uNot s0 a ta r d _ i j t u v y z _ =>
  cases e
  exact Or.inl ⟨a,ta,r,d,mP _,i,j,t,u,v,y,z⟩
 | @bOr s0 a ta b tb r ka kb _ i j t u v y h7 h8 h9 h0 x2 x3 a1 z _ =>
  cases e
  exact Or.inr (Or.inl ⟨a,ta,b,tb,r,ka,kb,mP _,i,j,t,u,v,y,h7,h8,h9,h0,x2,x3,a1,z⟩)
 | @bAnd s0 a ta b tb r ka kb _ i j t u v y h7 h8 h9 h0 x2 x3 a1 a2 b0 z _ =>
  cases e
  exact Or.inr (Or.inr ⟨a,ta,b,tb,r,ka,kb,mP _,i,j,t,u,v,y,h7,h8,h9,h0,x2,x3,a1,a2,b0,z⟩)
lemma mb:∀r:Fin 64,a9 (q1 6 r.val)=q1 8 (128+r.val % 16+32*(r.val / 16)):=by decide
lemma oe {r:Nat}(b:r < 64):a9 (q1 6 r)=q1 8 (128+r % 16+32*(r / 16)):=
 mb ⟨r,b⟩
lemma mx (g:Z 8):oa (u9 8 g)=u9 6 (a8 g):=by
 apply kL;intro r;unfold oa;simp only[kR,kM];have t:(0xFFFF:Nat)=2 ^ 16 - 1:=by decide
 rw[t]
 have s:∀(e k:Nat),
     (shiftLeft (land (shiftRight (u9 8 g) e) (2 ^ 16 - 1)) k).testBit r =
     (decide (k<=r)&&decide (r - k < 16)&&(u9 8 g).testBit (e+(r - k))):=by
   intro e k;change (((u9 8 g >>> e) &&& (2 ^ 16 - 1)) <<< k).testBit r=_;rw[nN,kN,kK,kQ]
   by_cases b:k<=r<;>by_cases i:r - k < 16<;>simp[b,i]
 have u :
     (land (shiftRight (u9 8 g) 128) (2 ^ 16 - 1)).testBit r =
     (decide (r < 16)&&(u9 8 g).testBit (128+r)):=by
   change ((u9 8 g >>> 128) &&& (2 ^ 16 - 1)).testBit r=_;rw[kN,kK,kQ];by_cases h:r < 16<;>simp[h]
 rw[u,s 160 16,s 192 32,s 224 48,vr]
 by_cases b:r < 16
 . have i:¬16<=r:=(by omega);have j:¬32<=r:=(by omega);have d:¬48<=r:=(by omega);have c:r < 2 ^ 6:=(by omega);simp only[b,i,j,d,c,decide_true,decide_false,jW,jT,jS,↓reduceIte,vr,show 128+r < 2 ^ 8 by omega,a8];rw[oe (by omega:r < 64)]
   congr 2;omega
 . by_cases i:r < 32
   . have j:¬32<=r:=(by omega);have d:¬48<=r:=(by omega);have c:r < 2 ^ 6:=(by omega);simp only[b,show 16<=r by omega,show r - 16 < 16 by omega,j,d,c,decide_true,decide_false,jW,jT,nK,jS,↓reduceIte,vr,show 160+(r - 16) < 2 ^ 8 by omega,a8];rw[oe (by omega:r < 64)]
     congr 2;omega
   . by_cases j:r < 48
     . have d:¬48<=r:=(by omega);have c:r < 2 ^ 6:=(by omega);simp only[b,show ¬r - 16 < 16 by omega,show 32<=r by omega,show r - 32 < 16 by omega,d,c,decide_true,decide_false,jW,jT,nJ,nK,jS,↓reduceIte,vr,show 192+(r - 32) < 2 ^ 8 by omega,a8];rw[oe (by omega:r < 64)]
       congr 2;omega
     . by_cases d:r < 64
       . have c:r < 2 ^ 6:=(by omega);simp only[b,show ¬r - 16 < 16 by omega,show ¬r - 32 < 16 by omega,show 48<=r by omega,show r - 48 < 16 by omega,c,decide_true,decide_false,jW,jT,nJ,nK,jS,↓reduceIte,vr,show 224+(r - 48) < 2 ^ 8 by omega,a8];rw[oe (by omega:r < 64)]
         congr 2;omega
       . simp only[b,show ¬r - 16 < 16 by omega,show ¬r - 32 < 16 by omega,show ¬r - 48 < 16 by omega,decide_false,jT,nJ,jS,vr,show ¬r < 2 ^ 6 by omega,↓reduceIte]
lemma oj (w x:Nat)(b:M):x∈g7 w b↔x=w\/x∈b:=by
 induction b with
 | nil=>simp[g7]
 | cons a rest ih =>
  unfold g7;by_cases c:w=a
  . subst c;simp[nD]
  . simp only[q2 c,jV,↓reduceIte];by_cases d:blt w a=true
    . simp only[d,↓reduceIte,kC]
    . simp only[d,jV,↓reduceIte,kC,ih];tauto
lemma oh (w:Nat){d:M} (h:d.Pairwise (· < ·)):(g7 w d).Pairwise (· < ·):=by
 induction d with
 | nil=>simp[g7]
 | cons a s ih =>
  rcases List.pairwise_cons.1 h with ⟨e,g⟩
  unfold g7;by_cases i:w=a
  . subst i;simpa[nD] using h
  . simp only[q2 i,jV,↓reduceIte];by_cases c:blt w a=true
    . have j:w < a:=(by simpa[nB] using c);simp only[c,↓reduceIte,List.pairwise_cons,kC];refine⟨?_,e,g⟩
      rintro x (rfl|b)
      . exact j
      . exact Nat.lt_trans j (e x b)
    . have t:a < w:=by
        have:¬w < a:=fun u=>c (by simpa[nB] using u)
        omega
      simp only[c,jV,↓reduceIte,List.pairwise_cons];refine⟨?_,ih g⟩
      intro x b;rcases (oj w x s).1 b with rfl|b'
      . exact t
      . exact e x b'
lemma en (g:Z 6):u9 6 g=0↔g=(fun _=>false):=by
 constructor
 . intro h;rw[<- im (n:=6) (range (2 ^ 6))] at h;exact yc h
 . rintro rfl;exact im (n:=6) (range (2 ^ 6))
lemma ep (g:Z 6):u9 6 g=l5↔g=(fun _=>true):=by
 have b:l5=2 ^ (range (2 ^ 6)).length - 1:=by decide
 constructor
 . intro h;rw[b,<- rf (n:=6) (range (2 ^ 6))] at h;exact yc h
 . rintro rfl;rw[b];exact rf (n:=6) (range (2 ^ 6))
lemma ty (u:X 8):(o8 (u2 8 u)).1=o5 u/\(o8 (u2 8 u)).2.Pairwise (· < ·)/\(∀p∈u,p.2≠4->p.2≠6->p.2≠7->p.2≠8->a8 p.1≠(fun _=>false)->a8 p.1≠(fun _=>true)->u9 6 (a8 p.1)∈(o8 (u2 8 u)).2):=by
 induction u with
 | nil=>simp[u2,o8,o5]
 | cons p e ih =>
  rcases p with ⟨g,tg⟩
  obtain⟨h7,v,x⟩:=ih;have h8:o8 (u2 8 ((g,tg)::e)) =
      let y:=o5 e;let z:=(o8 (u2 8 e)).2
      if beq tg 4 then (add y 2,z)
      else if beq tg 6||beq tg 7||beq tg 8 then (add y 1,z)
      else
        zm (oa (u9 8 g)) fun p =>
        if beq p 0||beq p l5 then (y,z)
        else (y,g7 p z):=by
    change o8 ((u9 8 g,tg)::u2 8 e)=_;conv_lhs=>unfold o8
    rw[show o8 (u2 8 e)=(o5 e,(o8 (u2 8 e)).2) from Prod.ext h7 rfl]
  rw[h8]
  simp only[o5];by_cases h4:tg=4
  . subst h4;simp only[nD,↓reduceIte,v8,kC];refine⟨by omega,v,?_⟩
    intro q h b i j s c d;rcases h with rfl|t
    . exact absurd rfl b
    . exact x q t b i j s c d
  . simp only[q2 h4,h4,jV,↓reduceIte];by_cases h2:tg=6\/tg=7\/tg=8
    . have h3:(beq tg 6||beq tg 7||beq tg 8)=true:=by rcases h2 with rfl|rfl|rfl<;>decide
      simp only[h3,h2,↓reduceIte,v8,kC];refine⟨by omega,v,?_⟩
      intro q h b i j s c d;rcases h with rfl|t
      . rcases h2 with rfl|rfl|rfl<;>contradiction
      . exact x q t b i j s c d
    . have h3:(beq tg 6||beq tg 7||beq tg 8)=false:=(by simp[nE,zh];tauto);simp only[h3,h2,jV,↓reduceIte,v5];have h9:oa (u9 8 g)=u9 6 (a8 g):=(by exact mx g);rw[h9]
      by_cases h6:u9 6 (a8 g)=0\/u9 6 (a8 g)=l5
      . have h5:(beq (u9 6 (a8 g)) 0||beq (u9 6 (a8 g)) l5)=true:=by
          rcases h6 with h0|h1
          . simp[qz h0]
          . simp[qz h1]
        simp only[h5,↓reduceIte,kC];refine⟨by omega,v,?_⟩
        intro q h b i j s c d;rcases h with rfl|t
        . rcases h6 with h0|h1
          . exact absurd ((en _).1 h0) c
          . exact absurd ((ep _).1 h1) d
        . exact x q t b i j s c d
      . have h5:(beq (u9 6 (a8 g)) 0||beq (u9 6 (a8 g)) l5)=false:=(by simp[nE,zh];tauto);simp only[h5,jV,↓reduceIte,kC];refine⟨by omega,oh _ v,?_⟩
        intro q h b i j s c d;rw[oj]
        rcases h with rfl|t
        . exact Or.inl rfl
        . exact Or.inr (x q t b i j s c d)
lemma db (v:∀s≤ 9,∀i < hJ s,bar c7 hS hQ s i=true){c:Nat}{b:X 8}(x:F7Ok c b) (d:uk c (u2 8 b)=true):False:=by
 obtain⟨hle,L0,y,z,h0,h1⟩:=x;obtain⟨h2,h3,h5⟩:=ty b;unfold uk at d;rw[show o8 (u2 8 b)=(o5 b,(o8 (u2 8 b)).2) from Prod.ext h2 rfl] at d;have h9:blt c (o5 b)=false:=by rw[jU];intro hc;rw[nB] at hc;omega
 simp only[h9,jV,↓reduceIte,v5] at d;cases j:ble 10 (sub c (o5 b))
 . simp only[j,jV,↓reduceIte] at d;have x2:c - o5 b<=9:=by
    by_contra hlt;have x3:10<=c - o5 b:=by omega
    have ht:ble 10 (sub c (o5 b))=true:=Eq.mpr nA x3;rw[ht] at j;cases j
   set e:=(o8 (u2 8 b)).2;have a1:e.Nodup:=h3.imp (fun h=>Nat.ne_of_lt h);have a2:(!(beq (t7 e).1 c7.fL)||m9 (c - o5 b) (t7 e).2 0 0 0 0 0 [] [])=true:=by
    cases t:beq (t7 e).1 c7.fL
    . simp
    . simp only[t,nH,jV,↓reduceIte] at d;simpa[t] using d
   have b0:∀g∈L0,u9 6 g∈e:=(by intro g u;obtain⟨p,hp,h4,h6,h7,h8,rfl⟩:=h0 g u;obtain⟨b1,b3⟩:=z (a8 p.1) u;exact h5 p hp h4 h6 h7 h8 b1 b3);exact dq v x2 e a1 a2 y b0 h1
 . simp only[j,↓reduceIte] at d;cases d
def br {n:Nat}(h:Nat)(e:X n):X n:=
 if ble h 32 then
  let c:=sub h 1;let i:=shiftRight c 1;let v:=beq (land c 1) 1
  let (a,ta):=ki i e;let d:=if beq ta 3 then 2 else 0
  let w:=hC a;let r:=yl i e
  if v then (w,d)::(a,0)::r else (w,d)::r
 else
  let g:=sub h 33
  let t:=beq (land g 1) 1
  let u:=beq (land (shiftRight g 1) 1) 1
  let x:=beq (land (shiftRight g 2) 1) 1
  let (i,j):=ik (shiftRight g 3) 16 1
  let (a,ta):=ki i e;let (b,tb):=ki j e
  let r:=yl i (yl j e)
  if x then
   let d:=if beq ta 6||beq tb 6 then 8 else if beq ta 3||beq tb 3 then 1 else 0
   let r1:=if t then (b,0)::r else r
   let s:=if u then (a,0)::r1 else r1
   (hE a b,d)::s
  else
   let d:=if beq ta 4||beq tb 4 then 7 else 0
   let r1:=if t then (b,if beq tb 3 then 1 else 0)::r else r
   let s:=if u then (a,if beq ta 3 then 1 else 0)::r1 else r1
   (hG a b,d)::s
def ch {n:Nat} (b:X n) (PT:Nat->Nat):Nat->Nat->Nat->X n
 | 0,_,_=>b
 | d+1,s,j =>
  let e:=au (PT s) j;let c:=land e 1023
  if beq c 0 then b
  else br c (ch b PT d (add s 1) (land (shiftRight e 10) 8191))
def a5 (s j:Nat):X 8:=
 ch i1 PG (sub 13 s) s j
lemma jb {n:Nat}(c:M)(b:Nat)(d:X n):bp (2 ^ c.length - 1) b (e6 c d)=e6 c (br b d):=by
 unfold bp br;simp only[v5]
 split
 . simp only[nk,nj];split<;>simp[e6,jf]
 . simp only[nk,nj]
   split
   . cases beq (land (sub b 33) 1) 1 <;>
     cases beq (land (shiftRight (sub b 33) 1) 1) 1 <;>
     simp[e6,q9]
   . cases beq (land (sub b 33) 1) 1 <;>
     cases beq (land (shiftRight (sub b 33) 1) 1) 1 <;>
     simp[e6,qc]
lemma gh {n:Nat}(b:M)(c:X n)(PT:Nat->Nat)(d s j:Nat):am (2 ^ b.length - 1) (e6 b c) PT d s j=e6 b (ch c PT d s j):=by
 induction d generalizing s j with
 | zero=>rfl
 | succ d ih=>simp only[am,ch,v5];split;rfl;rw[ih,jb]
lemma fx:xG=eW rG cG i1:=by decide +kernel
lemma gm:nq=u2 8 i1:=by decide +kernel
lemma ms (s j:Nat):sa cG.fJ xG s j=eW rG cG (a5 s j):=by
 unfold sa a5;have b:cG.fJ=2 ^ (aR 8 rG cG).length - 1:=by rw[zl,ej.fY]
 rw[b,fx]
 exact gh (aR 8 rG cG) i1 PG (sub 13 s) s j
lemma sm (s j:Nat):sa fe nq s j=u2 8 (a5 s j):=by
 unfold sa a5;have b:fe=2 ^ (range (2 ^ 8)).length - 1:=by rw[nZ];decide
 rw[b,gm]
 exact gh (range (2 ^ 8)) i1 PG (sub 13 s) s j
lemma cr:mw 8 [(0,3),(1,5),(2,6)]=gG:=by decide +kernel
lemma fu (x:F 8):zc [(0,3),(1,5),(2,6)] x=d7 x:=by funext i;fin_cases i<;>rfl
lemma bf (g:Z 8):ym gG (u9 8 g)=u9 8 (fun x=>g (d7 x)):=by
 rw[<- cr,jm [(0,3),(1,5),(2,6)] (by decide) g]
 congr 1;funext x;rw[fu]
lemma bg (b:X 8):wx gG (u2 8 b)=u2 8 (b.map fun p=>((fun x=>p.1 (d7 x)),p.2)):=by
 induction b with
 | nil=>rfl
 | cons p t ih=>rcases p with ⟨h,tg⟩;simp only[pd,kB,wx,v5,bf,ih]
lemma os {s:Nat}{b:X 8} (h:dv s (u2 8 b)=true):∃j < hK s,b.Perm (a5 s j):=by unfold dv at h;simp only[v5,jY,kt,zh] at h;obtain⟨d,c⟩:=h;rw[sm] at c;exact⟨_,j8 hK LG HG s _ d,(zv _ _).1 (y5 _ _ c)⟩
lemma ae (s2:∀s≤ 9,∀i < hJ s,bar c7 hS hQ s i=true)(g4:∀s≤ 13,∀i < hK s,hP s i=true):∀s≤ 13,∀i < hK s,¬gU s (a5 s i):=by
 intro s;induction s with
 | zero=>intro _ i hi d2;have y:=g4 0 (mJ 13) i hi;obtain⟨tg,s6⟩:=d2.inv_zero;simp only[hP,ms,s6,eW,e6,kB,mS,ej.fZ,nD] at y;cases y
 | succ ns ih =>
  intro hs i hi d2;have j0:∀j < hK ns,¬gU ns (a5 ns j):=ih (by omega);have b3:∀c2:X 8,
      gU ns c2->uj ns (eW rG cG c2)=true->False:=by
    intro c2 c b0;unfold uj at b0;dsimp only at b0;have hq:bn cG.fH (eW rG cG c2)=u2 8 c2:=by rw[eW,aR,kg]
    rw[hq] at b0;cases t:dv ns (u2 8 c2)
    . rw[t] at b0;simp only[jV,↓reduceIte] at b0;cases b1:uk ns (u2 8 c2)
      . rw[b1] at b0;simp only[jV,↓reduceIte,bg] at b0;obtain⟨j,hj,f2⟩:=os b0;exact j0 j hj (gU.perm f2 c.map_sig8)
      . exact db s2 c.f7Ok b1
    . obtain⟨j,hj,f2⟩:=os t;exact j0 j hj (gU.perm f2 c)
  have y:=g4 (ns+1) hs i hi;set g:=a5 (ns+1) i;have he:=n9 cG (eW rG cG g);have t0:(eW rG cG g).length=g.length:=kY _;dsimp only[hP] at y;rw[ms] at y;rw[show e4 cG (eW rG cG g)=(yx cG (eW rG cG g),v4 cG (eW rG cG g),zf cG (eW rG cG g),va cG (eW rG cG g),(e4 cG (eW rG cG g)).2.2.2.2) from Prod.ext he.1 (Prod.ext he.2.1 (Prod.ext he.2.2.1 (Prod.ext he.2.2.2 rfl)))] at y;dsimp only at y;rw[t0,p3 ej d2.toRun] at y;simp only[jV,↓reduceIte,v5] at y;set c3:=ble g.length 11&&beq (sub (add ns 2) g.length) 1&&!(z3 cG (va cG (eW rG cG g)));have g0:c3=true->¬ov fG g:=fun h7 hs' => by
    simp only[c3,jY,kt,nA] at h7;rw[vt ej h7.1.1 hs'] at h7;cases h7.2
  set hf:=c3&&ble g.length 10&&!(beq ns 0) &&
    !(b9 cG (zf cG (eW rG cG g)) (e4 cG (eW rG cG g)).2.2.2.2)
  rcases d2.inv_succ with
    ⟨a,ta,r,e0,hp,j1,t1,z,t,e1,b1,c⟩ |
    ⟨a,ta,b,tb,r,ka,kb,hp,hg,hh,hk,hm,hn,hr,x2,x3,z,t,e1,g1,b1,c⟩ |
    ⟨a,ta,b,tb,r,ka,kb,hp,ht,hu,hv,hw,hx,hy,hz,xi,x2,x3,z,t,e1,g1,b1,c⟩
  . have m2:c3=false:=by
      rw[jU];intro h7;have v2:g.length=ns+1:=by have hle:=d2.len_le;simp only[c3,jY,nC,nY,nX] at h7;omega
      cases e0
      . simp only[qk,jV,↓reduceIte] at c;exact g0 h7 (y4 hp v2 c.toRun)
      . have w0:=c.len_le;have aA:=hp.length_eq;simp[qk] at w0 aA;omega
    have aB:hf=false:=(by simp only[hf,m2,jT]);simp only[aB,jV,↓reduceIte,jY] at y;have m3:=y.1;obtain⟨d,e,v,h8⟩:=pc hp;have h8' : r.Perm (e++d.reverse):=h8.trans (o2 d e);have c' : gU ns ((hC a,if ta=3 then 2 else 0)::qk e0 (a,0) (e++d.reverse)):=gU.perm (mR _ (by cases e0<;>simp[qk,h8'])) c;have p0:=c'.len_le;have p1:g.length=d.length+e.length+1:=(by have:=congrArg List.length v;simp at this;omega);have aC:ble 1 (sub (add ns 2) g.length)=true:=(by rw[nA,nY,nX];cases e0<;>simp[qk] at p0<;>omega);simp only[aC,m2,jZ,jW,↓reduceIte] at m3;have e2:eW rG cG g=eW rG cG d++(eL rG cG a,ta)::eW rG cG e:=(by rw[v];simp[eW,e6]);have xs:=n7 cG (b8 cG ns g.length (sub (add ns 2) g.length) (eW rG cG g) (uj ns) true)
      [] (eW rG cG d) (eW rG cG e) (eL rG cG a) ta (by rw[<- e2];exact m3)
    unfold b8 at xs;dsimp only[k8] at xs;have aD:(beq ta 0||beq ta 3)=true:=by rcases j1 with rfl|rfl<;>decide
    have h5:∀p∈g,p.1≠hC a:=fun p ha=>by
      rcases kC.1 (hp.subset ha) with rfl|aE;exact e1.symm;exact b1 p aE
    simp only[aD,↓reduceIte,v5,hU] at xs;have⟨aF,r2⟩:=o7 xs;have a1:eW rG cG e++(eW rG cG d).reverse=eW rG cG (e++d.reverse):=by rw[y0,es]
    have r3:k9 (eW rG cG d).reverse (e4 cG (eW rG cG e)).2.2.2.2=eW rG cG (e++d.reverse):=(by rw[d8,a1]);cases e0
    . simp only[qk,jV,↓reduceIte] at c';have h9:=o3 ej (rem_b:=e++d.reverse) (z_b:=hC a) (z_t:=if ta=3 then 2 else 0)
        (by rw[p1];simp;omega)
        (by rw[a1,t4,yp,qv ej,cm ej])
        (by rw[a1,t4,vo,qv ej,cq ej])
        (by rw[a1,t4,k0,th,qv ej,cp ej])
        (by rw[a1,t4,w1,qv ej,ck ej];simp only[v8];omega) (fun h=>by cases h) c'.toRun aF
      rw[<- qv ej,r3] at h9;simp only[mW] at h9;by_cases h3:ta=3
      . subst h3;simp only[nD,↓reduceIte] at h9 c';exact b3 _ c' (o6 ej z t h5 c'.toRun h9)
      . simp only[q2 h3,jV,h3,↓reduceIte] at h9 c';exact b3 _ c' (o6 ej z t h5 c'.toRun h9)
    . have aG:ta=0:=by rcases j1 with h|h;exact h;exact absurd (t1 h) (by decide)
      subst aG;have aH:ble 2 (sub (add ns 2) g.length)=true:=by rw[nA,nY,nX];simp[qk] at p0;omega
      simp only[nD,aH,jW,↓reduceIte] at r2;simp only[qk,↓reduceIte] at c';have h9:=o3 ej (rem_b:=(a,0)::(e++d.reverse)) (z_b:=hC a) (z_t:=0)
        (by rw[p1];simp;omega)
        (by rw[a1,t4,t4,yp,yp,qv ej,cm ej])
        (by rw[a1,t4,t4,vo,vo,qv ej,cq ej])
        (by rw[a1];simp only[t4,k0,th,qv ej,cp ej,v8];omega)
        (by rw[a1];simp only[t4,w1,qv ej,ck ej,v8];omega) (fun h=>by cases h) c'.toRun r2
      rw[<- qv ej,r3] at h9;simp only[show beq 0 3=false from rfl,jV,↓reduceIte] at h9;exact b3 _ c' (o6 ej z t h5 c'.toRun h9)
  . have r4:∀a' ta' b' tb' ka' kb' d u e,
        g=d++(a',ta')::u++(b',tb')::e ->
        ta'≠2->tb'≠2->ta'≠7->tb'≠7 ->
        ¬(ta'=4/\tb'=6)->¬(ta'=6/\tb'=4) ->
        (ka'=true->ta'=0\/ta'=3)->(kb'=true->tb'=0\/tb'=3) ->
        hG a' b'≠(fun _=>false)->hG a' b'≠(fun _=>true) ->
        (∀p∈g,p.1≠hG a' b') ->
        gU ns ((hG a' b',if ta'=4\/tb'=4 then 7 else 0)::qk ka' (a',if ta'=3 then 1 else 0) (qk kb' (b',if tb'=3 then 1 else 0) (e++(d++u).reverse))) ->
        False:=by
      intro a' ta' b' tb' ka' kb' d u e v hg' hh' hk' hm' hn' hr' x2' x3' z' t' h5 c';have hc:(!(beq ta' 2)&&!(beq tb' 2)&&!(beq ta' 7)&&!(beq tb' 7)&&!((beq ta' 4&&beq tb' 6)||(beq ta' 6&&beq tb' 4)))=true:=by
        simp only[jY,kt,nE,nF,zh];refine⟨⟨⟨⟨hg',hh'⟩,hk'⟩,hm'⟩,?_,?_⟩
        . by_cases h4:ta'=4;right;intro h6;exact hn' ⟨h4,h6⟩;left;exact h4
        . by_cases h6:ta'=6;right;intro h4;exact hr' ⟨h6,h4⟩;left;exact h6
      cases d1:hf
      . simp only[d1,jV,↓reduceIte,jY] at y;have e2:eW rG cG g =
           eW rG cG d++(eL rG cG a',ta')::eW rG cG u++(eL rG cG b',tb')::eW rG cG e:=by
          rw[v];simp[eW,e6,kA]
        have hd:=d4 cG (n1 ns g.length (eW rG cG g) c3) []
          (eW rG cG d) (eW rG cG u) (eW rG cG e) (eL rG cG a') ta' (eL rG cG b') tb' (by rw[<- e2];exact y.2)
        unfold n1 at hd;have g2:=(o7 hd).1;simp only[dd,hc,↓reduceIte,hU,b6,mq] at g2;rw[er] at g2;exact b3 _ c' (g8 ej (isOr:=true) (pre_b:=(d++u).reverse) (suf_b:=e) (by rw[v];simp;omega) (fun h=>by rcases x2' h with rfl|rfl<;>decide) (fun h=>by rcases x3' h with rfl|rfl<;>decide) (by rw[s5]) (by rw[s5]) (by rw[s5]) (by rw[s5]) (fun h7 hs' => g0 h7 (i4 (s3 v) hs')) z' t' h5 c'.toRun g2)
      . simp only[d1,↓reduceIte] at y;exact b3 _ c' (c9 ej (isOr:=true) (forG:=true) v d1 (by simpa[x8] using hc) (by simp[sq,b6]) z' t' h5 c'.toRun y)
    have h5:∀p∈g,p.1≠hG a b:=fun p ha=>by
      rcases kC.1 (hp.subset ha) with rfl|t';exact e1.symm
      rcases kC.1 t' with rfl|h2';exact g1.symm;exact b1 p h2'
    rcases lx hp with ⟨d,u,e,v,h8⟩|⟨d,u,e,v,h8⟩
    . exact r4 a ta b tb ka kb d u e v hg hh hk hm hn hr x2 x3 z t h5
        (gU.perm (ey (h8.trans (o2 (d++u) e))) c)
    . have a2:hG b a=hG a b:=(by funext x;exact Bool.or_comm _ _);have aJ:(if tb=4\/ta=4 then 7 else 0)=(if ta=4\/tb=4 then 7 else 0):=(by by_cases t' : ta=4<;>by_cases h2' : tb=4<;>simp[t',h2']);exact r4 b tb a ta kb ka d u e v hh hg hm hk
        (fun ⟨t',h2'⟩ => hr ⟨h2',t'⟩) (fun ⟨t',h2'⟩ => hn ⟨h2',t'⟩) x3 x2
        (a2 ▸ z) (a2 ▸ t) (fun p hp' => a2 ▸ h5 p hp')
        (a2 ▸ aJ ▸ gU.perm (i0 (h8.trans (o2 (d++u) e))) c)
  . have r5:∀a' ta' b' tb' ka' kb' d u e,
        g=d++(a',ta')::u++(b',tb')::e ->
        ta'≠1->tb'≠1->ta'≠4->tb'≠4->ta'≠8->tb'≠8 ->
        (ta'=6->tb'=7)->(tb'=6->ta'=7) ->
        (ka'=true->ta'=0)->(kb'=true->tb'=0) ->
        hE a' b'≠(fun _=>false)->hE a' b'≠(fun _=>true) ->
        (∀p∈g,p.1≠hE a' b') ->
        gU ns ((hE a' b',if ta'=6\/tb'=6 then 8 else if ta'=3\/tb'=3 then 1 else 0)::qk ka' (a',0) (qk kb' (b',0) (e++(d++u).reverse))) ->
        False:=by
      intro a' ta' b' tb' ka' kb' d u e v ht' hu' hv' hw' hx' hy' hz' xi' x2' x3' z' t' h5 c';have hc:(!(beq ta' 1)&&!(beq tb' 1)&&!(beq ta' 4)&&!(beq tb' 4)&&!(beq ta' 8)&&!(beq tb' 8)&&!((beq ta' 6&&!(beq tb' 7))||(beq tb' 6&&!(beq ta' 7))))=true:=by
        simp only[jY,kt,nE,nF,nL,nC,zh];refine⟨⟨⟨⟨⟨⟨ht',hu'⟩,hv'⟩,hw'⟩,hx'⟩,hy'⟩,?_,?_⟩
        . by_cases h6:ta'=6;right;exact hz' h6;left;exact h6
        . by_cases h6:tb'=6;right;exact xi' h6;left;exact h6
      cases d1:hf
      . simp only[d1,jV,↓reduceIte,jY] at y;have e2:eW rG cG g =
           eW rG cG d++(eL rG cG a',ta')::eW rG cG u++(eL rG cG b',tb')::eW rG cG e:=by
          rw[v];simp[eW,e6,kA]
        have hd:=d4 cG (n1 ns g.length (eW rG cG g) c3) []
          (eW rG cG d) (eW rG cG u) (eW rG cG e) (eL rG cG a') ta' (eL rG cG b') tb' (by rw[<- e2];exact y.2)
        unfold n1 at hd;have g3:=(o7 hd).2;simp only[dd,hc,↓reduceIte,hU,b6] at g3;rw[er] at g3;exact b3 _ c' (g8 ej (isOr:=false) (pre_b:=(d++u).reverse) (suf_b:=e) (by rw[v];simp;omega) (fun h=>qz (x2' h)) (fun h=>qz (x3' h)) (by rw[s5]) (by rw[s5]) (by rw[s5]) (by rw[s5]) (fun h7 hs' => g0 h7 (i4 (s3 v) hs')) z' t' h5 c'.toRun g3)
      . simp only[d1,↓reduceIte] at y;exact b3 _ c' (c9 ej (isOr:=false) (forG:=true) v d1 (by simpa[x8] using hc) (by simp[sq,b6]) z' t' h5 c'.toRun y)
    have h5:∀p∈g,p.1≠hE a b:=fun p ha=>by
      rcases kC.1 (hp.subset ha) with rfl|t';exact e1.symm
      rcases kC.1 t' with rfl|h2';exact g1.symm;exact b1 p h2'
    rcases lx hp with ⟨d,u,e,v,h8⟩|⟨d,u,e,v,h8⟩
    . exact r5 a ta b tb ka kb d u e v ht hu hv hw hx hy hz xi x2 x3 z t h5
        (gU.perm (ey (h8.trans (o2 (d++u) e))) c)
    . have a2:hE b a=hE a b:=(by funext x;exact Bool.and_comm _ _);have aK:(if tb=6\/ta=6 then 8 else if tb=3\/ta=3 then 1 else 0) =
          (if ta=6\/tb=6 then 8 else if ta=3\/tb=3 then 1 else 0):=by
        by_cases t' : ta=6<;>by_cases h2' : tb=6 <;>
        by_cases h3' : ta=3<;>by_cases h4' : tb=3<;>simp[t',h2',h3',h4']
      exact r5 b tb a ta kb ka d u e v hu ht hw hv hy hx xi hz x3 x2
        (a2 ▸ z) (a2 ▸ t) (fun p hp' => a2 ▸ h5 p hp')
        (a2 ▸ aK ▸ gU.perm (i0 (h8.trans (o2 (d++u) e))) c)
lemma hT (c:∀s≤ 9,∀i < hJ s,bar c7 hS hQ s i=true)(d:∀s≤ 13,∀i < hK s,hP s i=true):∀t:Nat,nV 8 fG t->14<=t:=by
 intro t e;by_contra hlt;have g:t<=13:=by omega
 have b:gU 13 i1:=ou e g;have h:a5 13 0=i1:=rfl;rw[<- h] at b;exact ae c d 13 le_rfl 0 (by decide) b
abbrev hN:=bar c7 hS hQ
lemma f7_49:([4,9]).all (fun s=>S (hN s) (hJ s) 0)=true:=by decide +kernel
lemma f5_0:S (hN 5) 204 0=true:=by decide +kernel
abbrev F6:=hN 6
lemma f6_0:S F6 245 0=true:=by decide +kernel
lemma f6_1:S F6 245 245=true:=by decide +kernel
abbrev F7:=hN 7
lemma f7_0:S F7 172 0=true:=by decide +kernel
lemma f7_1:S F7 172 172=true:=by decide +kernel
lemma f7_2:S F7 171 344=true:=by decide +kernel
lemma f7_3:S F7 171 515=true:=by decide +kernel
abbrev F8:=hN 8
lemma f8_0:S F8 100 0=true:=by decide +kernel
lemma f8_1:S F8 99 100=true:=by decide +kernel
lemma f8_2:S F8 99 199=true:=by decide +kernel
lemma pF:∀s ≤ 9,∀i < hJ s,hN s i=true:=fun s hs=>match s,hs with | 0,_=>fun i hi=>by simp[hJ] at hi | 1,_=>fun i hi=>by simp[hJ] at hi | 2,_=>fun i hi=>by simp[hJ] at hi | 3,_=>fun i hi=>by simp[hJ] at hi | 4,_=>fun i hi=>hH (hN 4) (hJ 4) 0 (kH.1 f7_49 4 (by decide)) i (mJ _) (by omega) | 5,_=>fun i hi=>pD f5_0 i (by dsimp[hJ] at hi;omega) | 6,_=>fun i hi=>(pE (pD f6_0) f6_1) i (by dsimp[hJ] at hi;omega) | 7,_=>fun i hi=>(pE (pE (pE (pD f7_0) f7_1) f7_2) f7_3) i (by dsimp[hJ] at hi;omega) | 8,_=>fun i hi=>(pE (pE (pD f8_0) f8_1) f8_2) i (by dsimp[hJ] at hi;omega) | 9,_=>fun i hi=>hH (hN 9) (hJ 9) 0 (kH.1 f7_49 9 (by decide)) i (mJ _) (by omega) | _+10,hs=>by omega
lemma g_sm:([5,6,12,13]).all (fun s=>S (hP s) (hK s) 0)=true:=by decide +kernel
lemma g7_0:S (hP 7) 140 0=true:=by decide +kernel
abbrev G8:=hP 8
lemma g8_0:S G8 198 0=true:=by decide +kernel
lemma g8_1:S G8 198 198=true:=by decide +kernel
abbrev G9:=hP 9
lemma g9_0:S G9 140 0=true:=by decide +kernel
lemma g9_1:S G9 140 140=true:=by decide +kernel
lemma g9_2:S G9 139 280=true:=by decide +kernel
lemma g9_3:S G9 139 419=true:=by decide +kernel
abbrev G10:=hP 10
lemma g10_0:S G10 79 0=true:=by decide +kernel
lemma g10_1:S G10 79 79=true:=by decide +kernel
lemma g10_2:S G10 79 158=true:=by decide +kernel
lemma g10_3:S G10 79 237=true:=by decide +kernel
abbrev G11:=hP 11
lemma g11_0:S G11 20 0=true:=by decide +kernel
lemma g11_1:S G11 20 20=true:=by decide +kernel
lemma g11_2:S G11 19 40=true:=by decide +kernel
lemma pG:∀s ≤ 13,∀i < hK s,hP s i=true:=fun s hs=>match s,hs with | 0,_=>fun i hi=>by simp[hK] at hi | 1,_=>fun i hi=>by simp[hK] at hi | 2,_=>fun i hi=>by simp[hK] at hi | 3,_=>fun i hi=>by simp[hK] at hi | 4,_=>fun i hi=>by simp[hK] at hi | 5,_=>fun i hi=>hH (hP 5) (hK 5) 0 (kH.1 g_sm 5 (by decide)) i (mJ _) (by omega) | 6,_=>fun i hi=>hH (hP 6) (hK 6) 0 (kH.1 g_sm 6 (by decide)) i (mJ _) (by omega) | 7,_=>fun i hi=>pD g7_0 i (by dsimp[hK] at hi;omega) | 8,_=>fun i hi=>(pE (pD g8_0) g8_1) i (by dsimp[hK] at hi;omega) | 9,_=>fun i hi=>(pE (pE (pE (pD g9_0) g9_1) g9_2) g9_3) i (by dsimp[hK] at hi;omega) | 10,_=>fun i hi=>(pE (pE (pE (pD g10_0) g10_1) g10_2) g10_3) i (by dsimp[hK] at hi;omega) | 11,_=>fun i hi=>(pE (pE (pD g11_0) g11_1) g11_2) i (by dsimp[hK] at hi;omega) | 12,_=>fun i hi=>hH (hP 12) (hK 12) 0 (kH.1 g_sm 12 (by decide)) i (mJ _) (by omega) | 13,_=>fun i hi=>hH (hP 13) (hK 13) 0 (kH.1 g_sm 13 (by decide)) i (mJ _) (by omega) | _+14,hs=>by omega
lemma main_8457:∀t:ℕ,HasCircuitSize 8 fG t->14<=t:=hT pF pG
end PEqualNP.Outside.L_meta_8457_aux
theorem PEqualNP.Outside.L_meta_8457 :
    ∀t : ℕ,PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 2)||(x 1&&x 4)||(x 3&&x 5)||(x 3&&x 6)||(x 4&&x 5)||(x 4&&x 7)||(x 5&&x 6)) t → 14 ≤ t:=
  PEqualNP.Outside.L_meta_8457_aux.main_8457
