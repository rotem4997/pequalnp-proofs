import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_982_aux
lemma bFT:(false=true)=False:=Bool.false_eq_true
lemma bTA {b:Bool}:(true&&b)=b:=Bool.true_and b
lemma bOT {a b:Bool}:((a||b)=true)=(a=true\/b=true):=Bool.or_eq_true a b
lemma bAT {a b:Bool}:((a&&b)=true)=(a=true/\b=true):=Bool.and_eq_true a b
lemma bNF:(!false)=true:=Bool.not_false
lemma bNT {b:Bool}:((!b)=true)=(b=false):=Bool.not_eq_true' b
lemma lAA {α:Type _} (l1 l2 l3:List α):(l1++l2)++l3=l1++(l2++l3):=List.append_assoc l1 l2 l3
lemma lMC {α β:Type _} {f : α->β} {a : α} {l:List α}:(a::l).map f=f a::l.map f:=List.map_cons
lemma lMM {α:Type _} {a b : α} {l:List α}:a ∈ b::l ↔ a=b\/a ∈ l:=List.mem_cons
lemma lLC {α:Type _} {a : α} {l:List α}:(a::l).length=l.length+1:=List.length_cons
lemma lLA {α:Type _} {l1 l2:List α}:(l1++l2).length=l1.length+l2.length:=List.length_append
lemma lRC {α:Type _} {a : α} {l:List α}:(a::l).reverse=l.reverse++[a]:=List.reverse_cons
lemma lFC {α β:Type _} {f : α->β->β} {b : β} {a : α} {l:List α}:(a::l).foldr f b=f a (l.foldr f b):=List.foldr_cons
lemma lAL {α:Type _} {p : α->Bool} {l:List α}:l.all p=true ↔ ∀ x ∈ l,p x=true:=List.all_eq_true
lemma lAN {α:Type _} {p : α->Bool} {l:List α}:l.any p=true ↔ ∃ x ∈ l,p x=true:=List.any_eq_true
lemma nTB {n i:Nat}:(2 ^ n - 1).testBit i=decide (i < n):=by simp [Nat.testBit_two_pow_sub_one]
lemma nEQ {x y:Nat} (h:∀ i,x.testBit i=y.testBit i):x=y:=Nat.eq_of_testBit_eq h
lemma nTO {x y i:Nat}:(x|||y).testBit i=(x.testBit i||y.testBit i):=by simp [Nat.testBit_or]
lemma nTA {x y i:Nat}:(x&&&y).testBit i=(x.testBit i&&y.testBit i):=by simp [Nat.testBit_and]
lemma nTX {x y i:Nat}:(x^^^y).testBit i=(x.testBit i ^^ y.testBit i):=by simp [Nat.testBit_xor]
lemma nTS {x k i:Nat}:(x >>> k).testBit i=x.testBit (k+i):=by simp [Nat.testBit_shiftRight]
lemma nLO {x y:Nat}:Nat.lor x y=x|||y:=Nat.lor_eq
lemma nLA {x y:Nat}:Nat.land x y=x&&&y:=Nat.land_eq
lemma nXO {x y:Nat}:Nat.xor x y=x^^^y:=Nat.xor_eq
lemma nZT {i:Nat}:(0:Nat).testBit i=false:=Nat.zero_testBit i
lemma fUN {α:Type _} [DecidableEq α] {β : α->Sort _} {f:∀ a,β a} {a b : α} {v : β a} (h:b≠a):Function.update f a v b=f b:=Function.update_of_ne h v f
lemma fUS {α:Type _} [DecidableEq α] {β : α->Sort _} {f:∀ a,β a} {a : α} {v : β a}:Function.update f a v a=v:=Function.update_self a v f
lemma lMA {α β:Type _} {f : α->β} {l1 l2:List α}:(l1++l2).map f=l1.map f++l2.map f:=List.map_append
lemma lLM {α β:Type _} (f : α->β) {l:List α}:(l.map f).length=l.length:=List.length_map f
lemma lRR {α:Type _} {l:List α}:l.reverse.reverse=l:=List.reverse_reverse l
lemma lANil {α:Type _} {l:List α}:l++[]=l:=List.append_nil l
lemma lSA {α:Type _} {a : α} {l:List α} : [a]++l=a::l:=List.singleton_append
lemma lCA {α:Type _} {a : α} {l1 l2:List α}:(a::l1)++l2=a::(l1++l2):=List.cons_append
lemma lPM {α:Type _} {a : α} {l₁ l₂:List α}:(l₁++a::l₂).Perm (a::(l₁++l₂)):=List.perm_middle
lemma nAC (a b:Nat):a+b=b+a:=Nat.add_comm a b
lemma nAA (a b d:Nat):a+b+d=a+(b+d):=Nat.add_assoc a b d
lemma nAZ {a:Nat}:a+0=a:=Nat.add_zero a
lemma nZL (a:Nat) : 0<=a:=Nat.zero_le a
lemma bOS {a:Bool}:(a||a)=a:=Bool.or_self a
lemma bOTR {a:Bool}:(a||true)=true:=Bool.or_true a
lemma bTOR {a:Bool}:(true||a)=true:=Bool.true_or a
lemma bATR {a:Bool}:(a&&true)=a:=Bool.and_true a
lemma bBT {a:Bool}:(a ^^ true)=!a:=Bool.bne_true a
lemma dTR {p:Prop} [Decidable p] (h:p):decide p=true:=decide_eq_true h
lemma n2P (n:Nat) : 0 < 2 ^ n:=Nat.two_pow_pos n
lemma lMp {α β:Type _} {f : α->β} {b : β} {l:List α}:b ∈ l.map f ↔ ∃ a ∈ l,f a=b:=List.mem_map
lemma lMMp {α β γ:Type _} {g : β->γ} {f : α->β} {l:List α}:(l.map f).map g=l.map (g ∘ f):=List.map_map
lemma fCD {α β γ:Type _} (f : β->γ) (g : α->β):f ∘ g=fun x => f (g x):=Function.comp_def f g
lemma lPR {α:Type _} (l:List α):l.Perm l:=List.Perm.refl l
lemma lGD {α:Type _} (l:List α) (d : α) {i:Nat} (h:l.length<=i):l.getD i d=d:=List.getD_eq_default l d h
lemma lPC {α:Type _} (x : α) {l1 l2:List α} (h:l1.Perm l2):(x::l1).Perm (x::l2):=List.Perm.cons x h
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
abbrev BFn (n : ℕ):=(Fin n->Bool)->Bool
def q3 (gs:List Gate) (w:List Bool):List Bool :=
 gs.foldl (fun w g => w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) w
lemma zd (gs gs':List Gate) (w:List Bool) :
   q3 (gs++gs') w=q3 gs' (q3 gs w):=by
 simp [q3,List.foldl_append]
lemma y1 (gs:List Gate):∀ w:List Bool,
   ∃ t:List Bool,q3 gs w=w++t/\t.length=gs.length:=by
 induction gs with
 | nil => intro w;exact ⟨[],by simp [q3],rfl⟩
 | cons g gs ih =>
   intro w
   obtain ⟨t,ht,hl⟩:=ih (w++[g.op.eval (g.inputs.map fun i => w.getD i false)])
   refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false)::t,?_,by simp [hl]⟩
   have:q3 (g::gs) w
       = q3 gs (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]):=rfl
   rw [this,ht];simp
lemma qu (gs:List Gate) (w:List Bool) :
   (q3 gs w).length=w.length+gs.length:=by
 obtain ⟨t,ht,hl⟩:=y1 gs w
 rw [ht];simp [hl]
lemma ve (gs:List Gate) (w:List Bool) (i : ℕ) (h:i < w.length) :
   (q3 gs w).getD i false=w.getD i false:=by
 obtain ⟨t,ht,_⟩:=y1 gs w
 rw [ht,List.getD_append _ _ _ _ h]
def Ok (g:Gate):Prop :=
 g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\g.inputs.length<=2
lemma q8 {α:Type} (L:List α) (S d : α) (j : ℕ) (h:j≠L.length) :
   (L++[S]).getD j d=L.getD j d:=by
 by_cases hj:j < L.length
 . exact List.getD_append _ _ _ _ hj
 . rw [lGD _ _ (by simp;omega),lGD _ _ (by omega)]
lemma z0 {α:Type} (L:List α) (S d : α):(L++[S]).getD L.length d=S:=by
 simp
lemma z2 {α:Type} (L:List α) (S d : α) (k : ℕ) (h:L.length=k) :
   (L++[S]).getD k d=S:=by
 subst h;simp
def yb {n : ℕ} (L:List (Finset (Fin n))) (g:Gate):Finset (Fin n) :=
 (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅
lemma q71 {n : ℕ} (l:List ℕ) (F : ℕ->Finset (Fin n)) (i:Fin n) :
   i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l,i ∈ F a:=by
 induction l with
 | nil => simp
 | cons b l ih => simp [ih]
lemma kf {n : ℕ} (L:List (Finset (Fin n))) (g:Gate) (i:Fin n) :
   i ∈ yb L g ↔ ∃ a ∈ g.inputs,i ∈ L.getD a ∅ :=
 q71 _ _ _
def zb {n : ℕ} (gs:List Gate) (L:List (Finset (Fin n))):List (Finset (Fin n)) :=
 gs.foldl (fun L g => L++[yb L g]) L
def qr (n : ℕ):List (Finset (Fin n)):=List.ofFn fun i:Fin n => {i}
def q207 {n : ℕ} (x y:Fin n->Bool) (L:List (Finset (Fin n))) (w w':List Bool):Prop :=
 L.length=w.length/\w.length=w'.length /\
   ∀ j : ℕ,(∀ i ∈ L.getD j ∅,x i=y i)->w.getD j false=w'.getD j false
lemma k6 {n : ℕ} (x y:Fin n->Bool) (gs:List Gate) :
   ∀ (L:List (Finset (Fin n))) (w w':List Bool),q207 x y L w w' ->
     q207 x y (zb gs L) (q3 gs w) (q3 gs w'):=by
 induction gs with
 | nil => intro L w w' h;exact h
 | cons g gs ih =>
   intro L w w' h
   obtain ⟨h1,h2,h3⟩:=h
   apply ih (L++[yb L g])
     (w++[g.op.eval (g.inputs.map fun i => w.getD i false)])
     (w'++[g.op.eval (g.inputs.map fun i => w'.getD i false)])
   refine ⟨by simp [h1],by simp [h2],?_⟩
   intro j hj
   by_cases hjl:j=L.length
   . subst hjl
     rw [z0] at hj
     rw [h1,z0,h2,z0]
     congr 1
     apply List.map_congr_left
     intro a ha
     exact h3 a (fun i hi => hj i ((kf L g i).2 ⟨a,ha,hi⟩))
   . rw [q8 _ _ _ _ hjl] at hj
     rw [q8 _ _ _ _ (by omega),q8 _ _ _ _ (by omega)]
     exact h3 j hj
lemma j4 {n : ℕ} (x y:Fin n->Bool) :
   q207 x y (qr n) (List.ofFn x) (List.ofFn y):=by
 refine ⟨by simp [qr],by simp,?_⟩
 intro j hj
 by_cases hjn:j < n
 . have hx:x ⟨j,hjn⟩=y ⟨j,hjn⟩:=hj _ (by simp [qr,hjn])
   simp [hjn,hx]
 . rw [lGD _ _ (by simp;omega),lGD _ _ (by simp;omega)]
def Cnt {n : ℕ} (t : ℕ) (L:List (Finset (Fin n))):Prop :=
 ∀ W:Finset ℕ,(W.biUnion fun j => L.getD j ∅).card<=t+W.card
lemma q166 {n : ℕ}:Cnt 0 (qr n):=by
 intro W
 refine le_trans Finset.card_biUnion_le ?_
 rw [zero_add,Finset.card_eq_sum_ones]
 apply Finset.sum_le_sum
 intro j _
 by_cases hjn:j < n
 . simp [qr,hjn]
 . rw [lGD _ _ (by simp [qr];omega)];simp
lemma q194 {n : ℕ} (t : ℕ) (L:List (Finset (Fin n))) (g:Gate) (hg:g.inputs.length<=2)
   (h:Cnt t L):Cnt (t+1) (L++[yb L g]):=by
 intro W
 by_cases hW:L.length ∈ W
 . have hsub:(W.biUnion fun j => (L++[yb L g]).getD j ∅)
       ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅):=by
     intro i hi
     rw [Finset.mem_biUnion] at hi ⊢
     obtain ⟨j,hjW,hij⟩:=hi
     by_cases hjl:j=L.length
     . subst hjl
       rw [z0] at hij
       obtain ⟨a,ha,hia⟩:=(kf L g i).1 hij
       exact ⟨a,Finset.mem_union_right _ (List.mem_toFinset.2 ha),hia⟩
     . rw [q8 _ _ _ _ hjl] at hij
       exact ⟨j,Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl,hjW⟩),hij⟩
   have hc1:(W.erase L.length ∪ g.inputs.toFinset).card<=(W.card - 1)+2:=by
     refine le_trans (Finset.card_union_le _ _) ?_
     rw [Finset.card_erase_of_mem hW]
     exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
   have hWpos : 1<=W.card:=Finset.card_pos.2 ⟨_,hW⟩
   have:=h (W.erase L.length ∪ g.inputs.toFinset)
   have:=Finset.card_le_card hsub
   omega
 . have heq:(W.biUnion fun j => (L++[yb L g]).getD j ∅)
       = (W.biUnion fun j => L.getD j ∅):=by
     apply Finset.biUnion_congr rfl
     intro j hj
     exact q8 _ _ _ _ (fun e => hW (e ▸ hj))
   rw [heq]
   have:=h W
   omega
lemma q118 {n : ℕ} (gs:List Gate):∀ (t : ℕ) (L:List (Finset (Fin n))),
   (∀ g ∈ gs,Ok g)->Cnt t L->Cnt (t+gs.length) (zb gs L):=by
 induction gs with
 | nil => intro t L _ h;exact h
 | cons g gs ih =>
   intro t L hok h
   have:=ih (t+1) (L++[yb L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
     (q194 t L g (hok g List.mem_cons_self).2 h)
   rw [lLC,show t+(gs.length+1)=t+1+gs.length by omega]
   exact this
lemma q117 (n : ℕ) (f:(Fin n->Bool)->Bool) (T:Finset (Fin n))
   (hdep:∀ i ∈ T,∃ x:Fin n->Bool,f (Function.update x i (!x i))≠f x)
   (s : ℕ) (h:HasCircuitSize n f s):T.card<=s+1:=by
 obtain ⟨C,ok,hsz,hev⟩:=h
 have hsz':C.gates.length<=s:=hsz
 set S:=(zb C.gates (qr n)).getD C.output ∅ with hS
 have hall:T ⊆ S:=by
   intro i hiT
   by_contra hi
   obtain ⟨x,hx⟩:=hdep i hiT
   apply hx
   have hag:=(k6 (Function.update x i (!x i)) x C.gates _ _ _
     (j4 _ _)).2.2 C.output (by
       intro k hk
       have:k≠i:=fun e => hi (e ▸ hk)
       simp [fUN this])
   rw [← hev,← hev]
   exact hag
 have hc:=q118 C.gates 0 (qr n) ok q166 {C.output}
 simp only [Finset.singleton_biUnion,Finset.card_singleton,zero_add] at hc
 rw [← hS] at hc
 have:=Finset.card_le_card hall
 omega
def vg (g:Gate):Gate :=
 match g.op with
 | GateOp.not => ⟨GateOp.not,g.inputs.take 1⟩
 | _ => g
lemma q107 (g:Gate) (F : ℕ->Bool) :
   (vg g).op.eval ((vg g).inputs.map F)=g.op.eval (g.inputs.map F):=by
 obtain ⟨op,inputs⟩:=g
 cases op <;> simp only [vg]
 cases inputs <;> simp [GateOp.eval]
def NOk (g:Gate):Prop:=Ok g/\(g.op=GateOp.not->g.inputs.length<=1)
lemma q45 (g:Gate) (h:Ok g):NOk (vg g):=by
 obtain ⟨op,inputs⟩:=g
 obtain ⟨hop,hlen⟩:=h
 rcases hop with h | h | h
 . have:op=GateOp.and:=h
   subst this;exact ⟨⟨Or.inl rfl,hlen⟩,by simp [vg]⟩
 . have:op=GateOp.or:=h
   subst this;exact ⟨⟨Or.inr (Or.inl rfl),hlen⟩,by simp [vg]⟩
 . have:op=GateOp.not:=h
   subst this
   refine ⟨⟨Or.inr (Or.inr rfl),?_⟩,fun _ => ?_⟩ <;> simp [vg] <;> omega
lemma jd (gs:List Gate):∀ w:List Bool,
   q3 (gs.map vg) w=q3 gs w:=by
 induction gs with
 | nil => intro w;rfl
 | cons g gs ih =>
   intro w
   have s1:q3 ((g::gs).map vg) w=q3 (gs.map vg)
       (w++[(vg g).op.eval ((vg g).inputs.map fun i => w.getD i false)]):=rfl
   have s2:q3 (g::gs) w
       = q3 gs (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]):=rfl
   rw [s1,s2,q107,ih]
abbrev Stat:=Sum Bool ℕ
def ze (w:List Bool):Stat->Bool
 | Sum.inl c => c
 | Sum.inr j => w.getD j false
def qn (m : ℕ):Stat->Prop
 | Sum.inl _ => True
 | Sum.inr j => j < m
def wr (m : ℕ):List Stat->Option Gate × Stat
 | [] => (none,Sum.inl true)
 | Sum.inl c::_ => (none,Sum.inl (!c))
 | Sum.inr j::_ => (some ⟨GateOp.not,[j]⟩,Sum.inr m)
def ko (m : ℕ):List Stat->Option Gate × Stat
 | [] => (none,Sum.inl true)
 | [Sum.inl c] => (none,Sum.inl c)
 | [Sum.inr j] => (none,Sum.inr j)
 | [Sum.inl c,Sum.inl d] => (none,Sum.inl (c&&d))
 | [Sum.inl c,Sum.inr j] => (none,bif c then Sum.inr j else Sum.inl false)
 | [Sum.inr j,Sum.inl c] => (none,bif c then Sum.inr j else Sum.inl false)
 | [Sum.inr j,Sum.inr k] => (some ⟨GateOp.and,[j,k]⟩,Sum.inr m)
 | _ => (none,Sum.inl false)
def ji (m : ℕ):List Stat->Option Gate × Stat
 | [] => (none,Sum.inl false)
 | [Sum.inl c] => (none,Sum.inl c)
 | [Sum.inr j] => (none,Sum.inr j)
 | [Sum.inl c,Sum.inl d] => (none,Sum.inl (c||d))
 | [Sum.inl c,Sum.inr j] => (none,bif c then Sum.inl true else Sum.inr j)
 | [Sum.inr j,Sum.inl c] => (none,bif c then Sum.inl true else Sum.inr j)
 | [Sum.inr j,Sum.inr k] => (some ⟨GateOp.or,[j,k]⟩,Sum.inr m)
 | _ => (none,Sum.inl false)
def qg (op:GateOp) (m : ℕ) (ins:List Stat):Option Gate × Stat :=
 match op with
 | GateOp.and => ko m ins
 | GateOp.or => ji m ins
 | GateOp.not => wr m ins
 | _ => (none,Sum.inl false)
def q161 (m : ℕ) (g:Gate):Prop :=
 (g.op=GateOp.not/\∃ j,j < m/\g.inputs=[j]) \/
 ((g.op=GateOp.and\/g.op=GateOp.or)/\∃ j k,j < m/\k < m/\g.inputs=[j,k])
lemma j2 {m : ℕ} {g:Gate} (h:q161 m g):∀ a ∈ g.inputs,a < m:=by
 rcases h with ⟨_,j,hj,hin⟩ | ⟨_,j,k,hj,hk,hin⟩
 . intro a ha;simp [hin] at ha;omega
 . intro a ha;simp [hin] at ha;rcases ha with rfl | rfl <;> omega
def yq (n : ℕ) (gs:List Gate):Prop :=
 ∀ p g,gs[p]?=some g->q161 (n+p) g
lemma q151 (op:GateOp) (m : ℕ) (ins:List Stat) :
   ∀ g ∈ (qg op m ins).1,Ok g:=by
 intro g hg
 cases op <;> simp only [qg] at hg
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp [ko] at hg <;> (subst hg;simp [Ok])
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp [ji] at hg <;> (subst hg;simp [Ok])
 . rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;>
     simp [wr] at hg <;> (subst hg;simp [Ok])
 . simp at hg
 . simp at hg
lemma q80 (op:GateOp) (m : ℕ) (ins:List Stat)
   (hv:∀ s ∈ ins,qn m s) :
   ∀ g ∈ (qg op m ins).1,q161 m g:=by
 intro g hg
 cases op <;> simp only [qg] at hg
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp [ko] at hg
   subst hg
   exact Or.inr ⟨Or.inl rfl,_,_,hv (Sum.inr _) (by simp),hv (Sum.inr _) (by simp),rfl⟩
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp [ji] at hg
   subst hg
   exact Or.inr ⟨Or.inr rfl,_,_,hv (Sum.inr _) (by simp),hv (Sum.inr _) (by simp),rfl⟩
 . rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;> simp [wr] at hg
   subst hg
   exact Or.inl ⟨rfl,_,hv (Sum.inr _) (by simp),rfl⟩
 . simp at hg
 . simp at hg
lemma jh (op:GateOp) (m : ℕ) (ins:List Stat)
   (hop:op=GateOp.and\/op=GateOp.or\/op=GateOp.not) (hlen:ins.length<=2)
   (hnot:op=GateOp.not->ins.length<=1) (hc:∃ c,Sum.inl c ∈ ins) :
   (qg op m ins).1=none:=by
 obtain ⟨c,hc⟩:=hc
 rcases hop with rfl | rfl | rfl
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp_all [qg,ko]
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp_all [qg,ji]
 . have:=hnot rfl
   rcases ins with _ | ⟨a,_ | ⟨b,l⟩⟩ <;> (try cases a) <;> simp_all [qg,wr]
lemma kn (op:GateOp) (hop:op=GateOp.and\/op=GateOp.or\/op=GateOp.not)
   (w:List Bool) (ins:List Stat) (hlen:ins.length<=2)
   (hv:∀ s ∈ ins,qn w.length s) :
   qn (w.length+(qg op w.length ins).1.toList.length) (qg op w.length ins).2 /\
   ze (q3 (qg op w.length ins).1.toList w) (qg op w.length ins).2
     = op.eval (ins.map (ze w)):=by
 rcases hop with rfl | rfl | rfl
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
   . simp [qg,ko,qn,ze,GateOp.eval]
   . cases a <;> simp_all [qg,ko,qn,ze,GateOp.eval,q3]
   . cases a <;> cases b <;> (try rename_i c e;cases c) <;> (try cases e) <;>
       simp_all [qg,ko,qn,ze,GateOp.eval,q3]
   . simp at hlen
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
   . simp [qg,ji,qn,ze,GateOp.eval]
   . cases a <;> simp_all [qg,ji,qn,ze,GateOp.eval,q3]
   . cases a <;> cases b <;> (try rename_i c e;cases c) <;> (try cases e) <;>
       simp_all [qg,ji,qn,ze,GateOp.eval,q3]
   . simp at hlen
 . rcases ins with _ | ⟨a,l⟩
   . simp [qg,wr,qn,ze,GateOp.eval]
   . cases a <;> simp_all [qg,wr,qn,ze,GateOp.eval,q3]
def qa (n : ℕ) (acc:List Stat × List Gate) (g:Gate):List Stat × List Gate :=
 (acc.1++[(qg g.op (n+acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
   acc.2++(qg g.op (n+acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)
def elim (n : ℕ) (gs:List Gate) (acc:List Stat × List Gate):List Stat × List Gate :=
 gs.foldl (qa n) acc
lemma k4 (n : ℕ) (g:Gate) (gs:List Gate) (acc:List Stat × List Gate) :
   elim n (g::gs) acc=elim n gs (qa n acc g):=rfl
lemma jz (n : ℕ) (pre post:List Gate) (acc:List Stat × List Gate) :
   elim n (pre++post) acc=elim n post (elim n pre acc):=by
 simp [elim,List.foldl_append]
lemma q50 (n : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (elim n gs acc).1.length=acc.1.length+gs.length:=by
 induction gs with
 | nil => intro acc;rfl
 | cons g gs ih =>
   intro acc
   rw [k4,ih]
   simp only [qa,lLA,lLC,List.length_nil]
   omega
lemma wy (n k : ℕ) (d:Stat) (gs:List Gate):∀ acc:List Stat × List Gate,
   k < acc.1.length->(elim n gs acc).1.getD k d=acc.1.getD k d:=by
 induction gs with
 | nil => intro acc _;rfl
 | cons g gs ih =>
   intro acc hk
   rw [k4,ih (qa n acc g) (by simp [qa];omega)]
   exact q8 _ _ _ _ (by omega)
lemma y2 {α:Type} (o:Option α):o.toList.length<=1:=by
 cases o <;> simp
lemma q156 (n : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (∀ g ∈ acc.2,Ok g)->∀ g ∈ (elim n gs acc).2,Ok g:=by
 induction gs with
 | nil => intro acc h;exact h
 | cons g gs ih =>
   intro acc h
   apply ih (qa n acc g)
   intro g' hg'
   rcases List.mem_append.1 hg' with h1 | h1
   . exact h g' h1
   . exact q151 _ _ _ g' (by simpa using h1)
lemma q29 (n : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (elim n gs acc).2.length<=acc.2.length+gs.length:=by
 induction gs with
 | nil => intro acc;simp [elim]
 | cons g gs ih =>
   intro acc
   have h1:=ih (qa n acc g)
   have h2:(qa n acc g).2.length<=acc.2.length+1:=by
     simp only [qa,lLA]
     have:=y2 (qg g.op (n+acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
     omega
   rw [k4,lLC];omega
lemma zt (n k : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (∀ g ∈ gs,NOk g)->k < acc.1.length->(∃ c,acc.1.getD k (Sum.inl false)=Sum.inl c) ->
   (∃ g ∈ gs,k ∈ g.inputs)->(elim n gs acc).2.length+1<=acc.2.length+gs.length:=by
 induction gs with
 | nil => intro acc _ _ _ h;obtain ⟨g,hg,_⟩:=h;simp at hg
 | cons g gs ih =>
   intro acc hok hk hc hex
   rw [k4,lLC]
   by_cases hkg:k ∈ g.inputs
   . obtain ⟨c,hc⟩:=hc
     have hnok:=hok g List.mem_cons_self
     have hnone:(qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1=none:=by
       apply jh
       . exact hnok.1.1
       . simpa using hnok.1.2
       . intro h;simpa using hnok.2 h
       . exact ⟨c,List.mem_map.2 ⟨k,hkg,hc⟩⟩
     have h2:(qa n acc g).2.length=acc.2.length:=by
       show (acc.2++(qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length=_
       rw [hnone];simp
     have:=q29 n gs (qa n acc g)
     omega
   . have hex':∃ g' ∈ gs,k ∈ g'.inputs:=by
       obtain ⟨g',hg',hk'⟩:=hex
       rcases List.mem_cons.1 hg' with rfl | h
       . exact absurd hk' hkg
       . exact ⟨g',h,hk'⟩
     have h1:=ih (qa n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
       (by simp [qa];omega)
       (by
         obtain ⟨c,hc⟩:=hc
         refine ⟨c,?_⟩
         simp only [qa]
         rw [q8 _ _ _ _ (by omega)];exact hc)
       hex'
     have h2:(qa n acc g).2.length<=acc.2.length+1:=by
       simp only [qa,lLA]
       have:=y2 (qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
       omega
     omega
lemma km {m m' : ℕ} (h:m<=m'):∀ s:Stat,qn m s->qn m' s
 | Sum.inl _,_ => trivial
 | Sum.inr _,hj => lt_of_lt_of_le hj h
lemma jg (w t:List Bool):∀ s:Stat,qn w.length s ->
   ze (w++t) s=ze w s
 | Sum.inl _,_ => rfl
 | Sum.inr _,hj => List.getD_append _ _ _ _ hj
def Inv (n : ℕ) (y:List Bool) (w:List Bool) (acc:List Stat × List Gate):Prop :=
 acc.1.length=w.length/\∀ i : ℕ,
   qn (n+acc.2.length) (acc.1.getD i (Sum.inl false)) /\
   ze (q3 acc.2 y) (acc.1.getD i (Sum.inl false))=w.getD i false
lemma j7 (n : ℕ) (y:List Bool) (hy:y.length=n) (gs:List Gate) :
   ∀ (w:List Bool) (acc:List Stat × List Gate),(∀ g ∈ gs,Ok g)->Inv n y w acc ->
     Inv n y (q3 gs w) (elim n gs acc):=by
 induction gs with
 | nil => intro w acc _ h;exact h
 | cons g gs ih =>
   intro w acc hok h
   apply ih (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) (qa n acc g)
     (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
   obtain ⟨hl,hi⟩:=h
   set w':=q3 acc.2 y with hw'
   have lw':w'.length=n+acc.2.length:=by rw [hw',qu,hy]
   set ins:=g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
   have hgok:=hok g List.mem_cons_self
   have hs:=kn g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
     (by
       intro s hs
       obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
       rw [lw'];exact (hi a).1)
   rw [lw'] at hs
   set r:=qg g.op (n+acc.2.length) ins with hr
   have hvals:ins.map (ze w')=g.inputs.map fun i => w.getD i false:=by
     rw [hins,lMMp]
     apply List.map_congr_left
     intro a _
     exact (hi a).2
   have hnew:q3 (acc.2++r.1.toList) y=q3 r.1.toList w':=by
     rw [zd]
   obtain ⟨t,ht,_⟩:=y1 r.1.toList w'
   refine ⟨by simp [qa,hl],?_⟩
   intro i
   show qn (n+(acc.2++r.1.toList).length) ((acc.1++[r.2]).getD i (Sum.inl false)) /\
     ze (q3 (acc.2++r.1.toList) y) ((acc.1++[r.2]).getD i (Sum.inl false))=_
   rw [hnew,lLA,← nAA]
   by_cases hil:i=acc.1.length
   . subst hil
     rw [z0,hl,z0]
     exact ⟨hs.1,by rw [hs.2,hvals]⟩
   . rw [q8 _ _ _ _ hil,q8 _ _ _ _ (by omega)]
     refine ⟨km (by omega) _ (hi i).1,?_⟩
     rw [ht,jg _ _ _ (by rw [lw'];exact (hi i).1)]
     exact (hi i).2
lemma q100 (n : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (∀ g ∈ gs,Ok g)->(∀ i,qn (n+acc.2.length) (acc.1.getD i (Sum.inl false))) ->
   yq n acc.2->yq n (elim n gs acc).2:=by
 induction gs with
 | nil => intro acc _ _ hc;exact hc
 | cons g gs ih =>
   intro acc hok hv hc
   have hstep:=ih (qa n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
   apply hstep
   . intro i
     set ins:=g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
     have hgok:=hok g List.mem_cons_self
     have hs:=kn g.op hgok.1 (List.replicate (n+acc.2.length) false) ins
       (by simpa [hins] using hgok.2)
       (by
         intro s hs
         obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
         simpa using hv a)
     simp only [List.length_replicate] at hs
     show qn (n+(acc.2++_).length) ((acc.1++[_]).getD i (Sum.inl false))
     rw [lLA,← nAA]
     by_cases hil:i=acc.1.length
     . subst hil;rw [z0];exact hs.1
     . rw [q8 _ _ _ _ hil];exact km (by omega) _ (hv i)
   . intro p g' hp
     simp only [qa] at hp
     by_cases hlt:p < acc.2.length
     . rw [List.getElem?_append_left hlt] at hp
       exact hc p g' hp
     . rw [List.getElem?_append_right (by omega)] at hp
       set r:=qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
       cases ho:r.1 with
       | none => simp [ho] at hp
       | some g0 =>
         rw [ho] at hp
         have hp0:p - acc.2.length=0:=by
           have:=(List.getElem?_eq_some_iff.1 hp).1
           simp at this;omega
         have hpeq:p=acc.2.length:=by omega
         rw [hp0] at hp
         simp at hp
         subst hp
         rw [hpeq]
         exact q80 g.op (n+acc.2.length) _ (by
           intro s hs
           obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
           exact hv a) g0 (by rw [← hr,ho];rfl)
def qd (n : ℕ) (b:Bool):List Stat :=
 List.ofFn (fun i:Fin n => Sum.inr (i : ℕ))++[Sum.inl b]
lemma kp (n : ℕ) (b:Bool) :
   (qd n b).getD n (Sum.inl false)=Sum.inl b :=
 z2 _ _ _ _ (by simp)
lemma q159 (n : ℕ) (b:Bool) (y:Fin n->Bool) :
   Inv n (List.ofFn y) (List.ofFn y++[b]) (qd n b,[]):=by
 refine ⟨by simp [qd],?_⟩
 intro i
 have l1:(List.ofFn (fun i:Fin n => (Sum.inr (i : ℕ):Stat))).length=n:=by simp
 have l2:(List.ofFn y).length=n:=by simp
 by_cases hin:i=n
 . subst hin
   simp only [qd]
   rw [z2 _ _ _ _ l1,z2 _ _ _ _ l2]
   exact ⟨trivial,rfl⟩
 . simp only [qd]
   rw [q8 _ _ _ _ (by omega),q8 _ _ _ _ (by omega)]
   by_cases hlt:i < n
   . simp [hlt,qn,ze,q3]
   . rw [lGD _ _ (by omega),lGD _ _ (by omega)]
     exact ⟨trivial,rfl⟩
lemma q134 (n : ℕ) (y:Fin n->Bool) (b:Bool) :
   List.ofFn (Fin.snoc y b:Fin (n+1)->Bool)=List.ofFn y++[b]:=by
 rw [List.ofFn_succ']
 simp
lemma jr (n : ℕ) (gs:List Gate):∀ L:List (Finset (Fin (n+1))),
   (∀ g ∈ gs,n ∉ g.inputs)->(∀ j : ℕ,j≠n->Fin.last n ∉ L.getD j ∅) ->
   ∀ j : ℕ,j≠n->Fin.last n ∉ (zb gs L).getD j ∅:=by
 induction gs with
 | nil => intro L _ h;exact h
 | cons g gs ih =>
   intro L hno h
   apply ih (L++[yb L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
   intro j hj
   by_cases hjl:j=L.length
   . subst hjl
     rw [z0]
     intro hmem
     obtain ⟨a,ha,hia⟩:=(kf L g _).1 hmem
     exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
   . rw [q8 _ _ _ _ hjl];exact h j hj
lemma q74 (m j : ℕ) (h:j < m) :
   (qr m).getD j ∅={⟨j,h⟩}:=by
 simp [qr,h]
lemma yi (n : ℕ):∀ j : ℕ,j≠n ->
   Fin.last n ∉ (qr (n+1)).getD j ∅:=by
 intro j hj
 by_cases hlt:j < n+1
 . have e:(qr (n+1)).getD j ∅={⟨j,hlt⟩}:=q74 (n+1) j hlt
   rw [e,Finset.mem_singleton]
   intro e'
   exact hj (by have:=congrArg Fin.val e';simpa using this.symm)
 . rw [lGD _ _ (by simp [qr];omega)];simp
lemma q115 (n : ℕ) (f:(Fin (n+1)->Bool)->Bool) (b:Bool) (s : ℕ)
   (hdep:∃ x:Fin (n+1)->Bool,f (Function.update x (Fin.last n) (!x (Fin.last n)))≠f x)
   (hnc:∃ y y':Fin n->Bool,f (Fin.snoc y b)≠f (Fin.snoc y' b))
   (h:HasCircuitSize (n+1) f s) :
   ∃ s',s'+1<=s/\HasCircuitSize n (fun y:Fin n->Bool => f (Fin.snoc y b)) s':=by
 obtain ⟨C,ok,hsz,hev⟩:=h
 have hsz':C.gates.length<=s:=hsz
 set gs:=C.gates.map vg with hgs
 have hnok:∀ g ∈ gs,NOk g:=by
   intro g hg
   obtain ⟨g0,hg0,rfl⟩:=List.mem_map.1 hg
   exact q45 g0 (ok g0 hg0)
 have hevg:∀ x:Fin (n+1)->Bool,(q3 gs (List.ofFn x)).getD C.output false=f x:=by
   intro x
   rw [hgs,jd,← hev x];rfl
 set acc:=elim n gs (qd n b,[]) with hacc
 have hinv:∀ y:Fin n->Bool,
     Inv n (List.ofFn y) (q3 gs (List.ofFn (Fin.snoc y b:Fin (n+1)->Bool))) acc:=by
   intro y
   rw [q134]
   exact j7 n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (q159 n b y)
 have hval:∀ y:Fin n->Bool,
     ze (q3 acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
       = f (Fin.snoc y b):=by
   intro y
   rw [((hinv y).2 C.output).2,hevg]
 cases hst:acc.1.getD C.output (Sum.inl false) with
 | inl c =>
   exfalso
   obtain ⟨y,y',hne⟩:=hnc
   apply hne
   rw [← hval y,← hval y',hst];rfl
 | inr j =>
   have hlen:acc.2.length+1<=s:=by
     by_cases hread:∃ g ∈ gs,n ∈ g.inputs
     . have:=zt n n gs (qd n b,[]) hnok (by simp [qd])
         ⟨b,z2 _ _ _ _ (by simp)⟩ hread
       rw [← hacc] at this
       have hl:gs.length=C.gates.length:=by simp [hgs]
       simp only [List.length_nil,zero_add] at this
       omega
     . exfalso
       push Not at hread
       have hout:C.output≠n:=by
         intro e
         rw [e,hacc,wy n n _ gs _ (by simp [qd])] at hst
         have hb:(qd n b).getD n (Sum.inl false)=Sum.inl b :=
           z2 _ _ _ _ (by simp)
         rw [show ((qd n b,([]:List Gate))).1=qd n b from rfl,hb] at hst
         cases hst
       obtain ⟨x,hx⟩:=hdep
       apply hx
       have hns:=jr n gs (qr (n+1)) hread (yi n) C.output hout
       have hag:=(k6 (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
         (j4 _ _)).2.2 C.output (by
           intro k hk
           have:k≠Fin.last n:=fun e => hns (e ▸ hk)
           simp [fUN this])
       rw [← hevg,← hevg]
       exact hag
   refine ⟨acc.2.length,hlen,⟨acc.2,j⟩,q156 n gs _ (by simp),le_refl _,?_⟩
   intro y
   have:=hval y
   rw [hst] at this
   exact this
lemma q79 (op:GateOp) (m : ℕ) (ins:List Stat)
   (hop:op=GateOp.and\/op=GateOp.or\/op=GateOp.not) (hlen:ins.length<=2)
   (hnot:op=GateOp.not->ins.length<=1) (b:Bool)
   (hand:op=GateOp.and->b=false) (hor:op=GateOp.or->b=true)
   (hc:Sum.inl b ∈ ins):∃ c,(qg op m ins).2=Sum.inl c:=by
 rcases hop with rfl | rfl | rfl
 . have:=hand rfl
   subst this
   rcases ins with _ | ⟨a,_ | ⟨d,_ | ⟨e,l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
     simp_all [qg,ko]
 . have:=hor rfl
   subst this
   rcases ins with _ | ⟨a,_ | ⟨d,_ | ⟨e,l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
     simp_all [qg,ji]
 . have:=hnot rfl
   rcases ins with _ | ⟨a,_ | ⟨d,l⟩⟩ <;> (try cases a) <;> simp_all [qg,wr]
lemma vs (n : ℕ) (acc:List Stat × List Gate) (g:Gate) (hg:NOk g) (k : ℕ)
   (hk:k ∈ g.inputs) (c:Bool) (hc:acc.1.getD k (Sum.inl false)=Sum.inl c) :
   (qa n acc g).2.length=acc.2.length:=by
 have hnone:(qg g.op (n+acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1=none:=by
   apply jh
   . exact hg.1.1
   . simpa using hg.1.2
   . intro h;simpa using hg.2 h
   . exact ⟨c,List.mem_map.2 ⟨k,hk,hc⟩⟩
 show (acc.2++(qg g.op (n+acc.2.length)
   (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length=_
 rw [hnone];simp
def wl (g:Gate):Bool :=
 match g.op with
 | GateOp.or => true
 | _ => false
lemma q90 (n : ℕ) (acc:List Stat × List Gate) (g:Gate) (hg:NOk g) (k : ℕ)
   (hk:k ∈ g.inputs) (hc:acc.1.getD k (Sum.inl false)=Sum.inl (wl g)) :
   ∃ c,(qa n acc g).1.getD acc.1.length (Sum.inl false)=Sum.inl c:=by
 have e:(qa n acc g).1.getD acc.1.length (Sum.inl false)
     = (qg g.op (n+acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2:=z0 _ _ _
 rw [e]
 apply q79 _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
   (wl g)
 . intro h;simp [wl,h]
 . intro h;simp [wl,h]
 . exact List.mem_map.2 ⟨k,hk,hc⟩
lemma q53 {n : ℕ} (pre post:List Gate) (L:List (Finset (Fin n))) :
   zb (pre++post) L=zb post (zb pre L):=by
 simp [zb,List.foldl_append]
lemma q54 {n : ℕ} (gs:List Gate):∀ L:List (Finset (Fin n)),
   (zb gs L).length=L.length+gs.length:=by
 induction gs with
 | nil => intro L;rfl
 | cons g gs ih =>
   intro L
   have h:zb (g::gs) L=zb gs (L++[yb L g]):=rfl
   rw [h,ih]
   simp only [lLA,lLC,List.length_nil]
   omega
lemma q124 (n : ℕ) (D : ℕ->Prop) (gs:List Gate) :
   ∀ L:List (Finset (Fin (n+1))),
   (∀ g ∈ gs,∀ a ∈ g.inputs,¬ D a)->(∀ j : ℕ,¬ D j->Fin.last n ∉ L.getD j ∅) ->
   ∀ j : ℕ,¬ D j->Fin.last n ∉ (zb gs L).getD j ∅:=by
 induction gs with
 | nil => intro L _ h;exact h
 | cons g gs ih =>
   intro L hno h
   apply ih (L++[yb L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
   intro j hj
   by_cases hjl:j=L.length
   . subst hjl
     rw [z0]
     intro hmem
     obtain ⟨a,ha,hia⟩:=(kf L g _).1 hmem
     exact h a (hno g List.mem_cons_self a ha) hia
   . rw [q8 _ _ _ _ hjl];exact h j hj
lemma q173 (n : ℕ) (gs:List Gate) (hnok:∀ g ∈ gs,NOk g) (o : ℕ)
   (hdep:Fin.last n ∈ (zb gs (qr (n+1))).getD o ∅)
   (hout:∀ b c,(elim n gs (qd n b,[])).1.getD o (Sum.inl false)≠Sum.inl c) :
   ∃ b,(elim n gs (qd n b,[])).2.length+2<=gs.length:=by
 have hon:o≠n:=by
   intro e
   apply hout false false
   rw [e,wy n n _ gs _ (by simp [qd])]
   exact kp n false
 by_cases hread:∃ g ∈ gs,n ∈ g.inputs
 swap
 . exfalso
   push Not at hread
   exact jr n gs (qr (n+1)) hread (yi n) o hon hdep
 obtain ⟨g,hg,hng⟩:=hread
 obtain ⟨pre,post,rfl⟩:=List.append_of_mem hg
 have hgn:NOk g:=hnok g hg
 have hpren:∀ g' ∈ pre,NOk g':=fun g' h => hnok g' (List.mem_append_left _ h)
 have hpostn:∀ g' ∈ post,NOk g' :=
   fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
 have hsplit:∀ b,elim n (pre++g::post) (qd n b,[])
     = elim n post (qa n (elim n pre (qd n b,[])) g) :=
   fun b => by rw [jz,k4]
 have hAn:∀ b,(elim n pre (qd n b,[])).1.getD n (Sum.inl false)=Sum.inl b:=by
   intro b
   rw [wy n n _ pre _ (by simp [qd])]
   exact kp n b
 have hAl:∀ b,(elim n pre (qd n b,[])).1.length=n+1+pre.length:=by
   intro b
   rw [q50]
   simp [qd]
 have hA2:∀ b,(elim n pre (qd n b,[])).2.length<=0+pre.length :=
   fun b => q29 n pre (qd n b,[])
 have hB2:=fun b => vs n (elim n pre (qd n b,[])) g hgn n hng b (hAn b)
 have hBl:∀ b,(qa n (elim n pre (qd n b,[])) g).1.length
     = n+1+pre.length+1:=by
   intro b
   simp [qa,hAl b]
 have hBn:∀ b,(qa n (elim n pre (qd n b,[])) g).1.getD n (Sum.inl false)
     = Sum.inl b:=by
   intro b
   show ((elim n pre (qd n b,[])).1++[_]).getD n _=_
   rw [q8 _ _ _ _ (by rw [hAl b];omega)]
   exact hAn b
 have hF:=fun b => q29 n post (qa n (elim n pre (qd n b,[])) g)
 have hlen:(pre++g::post).length=pre.length+post.length+1:=by
   simp only [lLA,lLC];omega
 by_cases h1:∃ g' ∈ pre,n ∈ g'.inputs
 . refine ⟨false,?_⟩
   have a1:(elim n pre (qd n false,[])).2.length+1<=0+pre.length :=
     zt n n pre (qd n false,[]) hpren (by simp [qd])
       ⟨false,kp n false⟩ h1
   have:=hF false
   have:=hB2 false
   rw [hsplit,hlen]
   omega
 by_cases h2:∃ g' ∈ post,n ∈ g'.inputs
 . refine ⟨false,?_⟩
   have a1:=zt n n post (qa n (elim n pre (qd n false,[])) g) hpostn
     (by rw [hBl];omega) ⟨false,hBn false⟩ h2
   have:=hA2 false
   have:=hB2 false
   rw [hsplit,hlen]
   omega
 obtain ⟨c,hc⟩:=q90 n (elim n pre (qd n (wl g),[])) g hgn n hng
   (hAn (wl g))
 rw [hAl (wl g)] at hc
 refine ⟨wl g,?_⟩
 by_cases h3:∃ g' ∈ post,(n+1+pre.length) ∈ g'.inputs
 . have a1:=zt n (n+1+pre.length) post
     (qa n (elim n pre (qd n (wl g),[])) g) hpostn
     (by rw [hBl];omega) ⟨c,hc⟩ h3
   have:=hA2 (wl g)
   have:=hB2 (wl g)
   rw [hsplit,hlen]
   omega
 . exfalso
   have hom:o≠n+1+pre.length:=by
     intro e
     apply hout (wl g) c
     rw [hsplit,e,wy n _ _ post _ (by rw [hBl];omega)]
     exact hc
   push Not at h1 h2 h3
   have hs:zb (pre++g::post) (qr (n+1))
       = zb post (zb pre (qr (n+1))
         ++ [yb (zb pre (qr (n+1))) g]):=by
     rw [q53];rfl
   rw [hs] at hdep
   have hL:=jr n pre (qr (n+1)) h1 (yi n)
   have hLl:(zb pre (qr (n+1))).length=n+1+pre.length:=by
     rw [q54]
     simp [qr]
   refine q124 n (fun j => j=n\/j=n+1+pre.length) post _ ?_ ?_ o
     (by simp [hon,hom]) hdep
   . intro g' hg' a ha hD
     rcases hD with rfl | rfl
     . exact h2 g' hg' ha
     . exact h3 g' hg' ha
   . intro j hj
     have hj':j≠n/\j≠n+1+pre.length:=by
       constructor
       . exact fun e => hj (Or.inl e)
       . exact fun e => hj (Or.inr e)
     rw [q8 _ _ _ _ (by rw [hLl];exact hj'.2)]
     exact hL j hj'.1
lemma q114 (n : ℕ) (f:(Fin (n+1)->Bool)->Bool) (s : ℕ)
   (hdep:∃ x:Fin (n+1)->Bool,f (Function.update x (Fin.last n) (!x (Fin.last n)))≠f x)
   (hnc:∀ b:Bool,∃ y y':Fin n->Bool,f (Fin.snoc y b)≠f (Fin.snoc y' b))
   (h:HasCircuitSize (n+1) f s) :
   ∃ (b:Bool) (s' : ℕ),s'+2<=s /\
     HasCircuitSize n (fun y:Fin n->Bool => f (Fin.snoc y b)) s':=by
 obtain ⟨C,ok,hsz,hev⟩:=h
 have hsz':C.gates.length<=s:=hsz
 set gs:=C.gates.map vg with hgs
 have hl:gs.length=C.gates.length:=by simp [hgs]
 have hnok:∀ g ∈ gs,NOk g:=by
   intro g hg
   obtain ⟨g0,hg0,rfl⟩:=List.mem_map.1 hg
   exact q45 g0 (ok g0 hg0)
 have hevg:∀ x:Fin (n+1)->Bool,(q3 gs (List.ofFn x)).getD C.output false=f x:=by
   intro x
   rw [hgs,jd,← hev x];rfl
 have hinv:∀ (b:Bool) (y:Fin n->Bool),
     Inv n (List.ofFn y) (q3 gs (List.ofFn (Fin.snoc y b:Fin (n+1)->Bool)))
       (elim n gs (qd n b,[])):=by
   intro b y
   rw [q134]
   exact j7 n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (q159 n b y)
 have hval:∀ (b:Bool) (y:Fin n->Bool),
     ze (q3 (elim n gs (qd n b,[])).2 (List.ofFn y))
       ((elim n gs (qd n b,[])).1.getD C.output (Sum.inl false))=f (Fin.snoc y b):=by
   intro b y
   rw [((hinv b y).2 C.output).2,hevg]
 have hout:∀ b c,
     (elim n gs (qd n b,[])).1.getD C.output (Sum.inl false)≠Sum.inl c:=by
   intro b c hst
   obtain ⟨y,y',hne⟩:=hnc b
   apply hne
   rw [← hval b y,← hval b y',hst];rfl
 have hsupp:Fin.last n ∈ (zb gs (qr (n+1))).getD C.output ∅:=by
   by_contra hns
   obtain ⟨x,hx⟩:=hdep
   apply hx
   have hag:=(k6 (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
     (j4 _ _)).2.2 C.output (by
       intro k hk
       have:k≠Fin.last n:=fun e => hns (e ▸ hk)
       simp [fUN this])
   rw [← hevg,← hevg]
   exact hag
 obtain ⟨b,hb⟩:=q173 n gs hnok C.output hsupp hout
 cases hst:(elim n gs (qd n b,[])).1.getD C.output (Sum.inl false) with
 | inl c => exact absurd hst (hout b c)
 | inr j =>
   refine ⟨b,(elim n gs (qd n b,[])).2.length,by omega,
     ⟨(elim n gs (qd n b,[])).2,j⟩,q156 n gs _ (by simp),le_refl _,?_⟩
   intro y
   have:=hval b y
   rw [hst] at this
   exact this
def wmap (n m : ℕ) (π:Fin n->Fin m) (w : ℕ) : ℕ :=
 if h:w < n then (π ⟨w,h⟩ : ℕ) else w - n+m
def jt (n m : ℕ) (π:Fin n->Fin m) (g:Gate):Gate :=
 ⟨g.op,g.inputs.map (wmap n m π)⟩
def q174 (n m : ℕ) (π:Fin n->Fin m) (C:Circuit):Circuit :=
 ⟨C.gates.map (jt n m π),wmap n m π C.output⟩
def step (w:List Bool) (g:Gate):List Bool :=
 w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
def Rel (n m : ℕ) (π:Fin n->Fin m) (W W':List Bool):Prop :=
 n<=W.length/\W'.length+n=W.length+m /\
   ∀ w : ℕ,W'.getD (wmap n m π w) false=W.getD w false
lemma q182 (n m : ℕ) (π:Fin n->Fin m) (W W':List Bool) (g:Gate)
   (h:Rel n m π W W'):Rel n m π (step W g) (step W' (jt n m π g)):=by
 obtain ⟨h1,h2,h3⟩:=h
 have hv:(jt n m π g).op.eval
     ((jt n m π g).inputs.map fun i => W'.getD i false)
     = g.op.eval (g.inputs.map fun i => W.getD i false):=by
   simp only [jt,lMMp]
   congr 1
   apply List.map_congr_left
   intro a _
   exact h3 a
 refine ⟨by simp [step];omega,by simp [step];omega,?_⟩
 intro w
 simp only [step,hv]
 rcases Nat.lt_trichotomy w W.length with hw | hw | hw
 . have hlt:wmap n m π w < W'.length:=by
     unfold wmap
     split
     . have:=(π ⟨w,by assumption⟩).2;omega
     . omega
   rw [List.getD_append _ _ _ _ hlt,List.getD_append _ _ _ _ hw]
   exact h3 w
 . have he:wmap n m π w=W'.length:=by
     unfold wmap
     split
     . omega
     . omega
   rw [he,hw,z0,z0]
 . have hge:W'.length+1<=wmap n m π w:=by
     unfold wmap
     split
     . omega
     . omega
   rw [lGD _ _ (by simp;omega),lGD _ _ (by simp;omega)]
lemma q184 (n m : ℕ) (π:Fin n->Fin m) (gs:List Gate) :
   ∀ W W':List Bool,Rel n m π W W' ->
     Rel n m π (gs.foldl step W) ((gs.map (jt n m π)).foldl step W'):=by
 induction gs with
 | nil => intro W W' h;exact h
 | cons g gs ih =>
   intro W W' h
   exact ih _ _ (q182 n m π W W' g h)
lemma q183 (n m : ℕ) (π:Fin n->Fin m) (x:Fin m->Bool) :
   Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x):=by
 refine ⟨by simp,by simp;omega,?_⟩
 intro w
 unfold wmap
 split
 . rename_i hw
   rw [List.getD_eq_getElem _ _ (by simp),List.getD_eq_getElem _ _ (by simpa using hw)]
   simp
 . rename_i hw
   rw [lGD _ _ (by simp),lGD _ _ (by simp;omega)]
lemma yn {n m : ℕ} (π:Fin n->Fin m) (h:(Fin n->Bool)->Bool) (s : ℕ)
   (hc:HasCircuitSize n h s):HasCircuitSize m (fun x => h (x ∘ π)) s:=by
 obtain ⟨C,ok,hsz,hev⟩:=hc
 refine ⟨q174 n m π C,?_,?_,?_⟩
 . intro g hg
   obtain ⟨g0,hg0,rfl⟩:=List.mem_map.1 hg
   exact ⟨(ok g0 hg0).1,by simpa [jt] using (ok g0 hg0).2⟩
 . simpa [q174,Circuit.size] using hsz
 . intro x
   show _=h (x ∘ π)
   rw [← hev (x ∘ π)]
   have:=(q184 n m π C.gates _ _ (q183 n m π x)).2.2 C.output
   exact this
lemma ks (n : ℕ) (p:Fin (n+1)) (x:Fin (n+1)->Bool) (b:Bool) :
   (Fin.snoc (fun j:Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
       Fin (n+1)->Bool) ∘ (Equiv.swap p (Fin.last n))
     = Function.update x p b:=by
 funext j
 simp only [Function.comp_apply]
 by_cases hj:j=p
 . subst hj
   rw [Equiv.swap_apply_left,Fin.snoc_last,fUS]
 . have hl:Equiv.swap p (Fin.last n) j≠Fin.last n:=by
     intro e
     apply hj
     have:=congrArg (Equiv.swap p (Fin.last n)) e
     rwa [Equiv.swap_apply_self,Equiv.swap_apply_right] at this
   obtain ⟨t,ht⟩:=Fin.exists_castSucc_eq.2 hl
   rw [← ht,Fin.snoc_castSucc,ht,Equiv.swap_apply_self,fUN hj]
lemma q70 (n : ℕ) (f:(Fin (n+1)->Bool)->Bool) (p:Fin (n+1)) (b:Bool) (s : ℕ)
   (hdep:∃ x:Fin (n+1)->Bool,f (Function.update x p (!x p))≠f x)
   (hnc:∃ x y:Fin (n+1)->Bool,
     f (Function.update x p b)≠f (Function.update y p b))
   (h:HasCircuitSize (n+1) f s) :
   ∃ s' : ℕ,s'+1<=s /\
     HasCircuitSize (n+1) (fun x => f (Function.update x p b)) s':=by
 set σ:Equiv.Perm (Fin (n+1)):=Equiv.swap p (Fin.last n) with hσ
 have hg:HasCircuitSize (n+1) (fun x => f (x ∘ σ)) s:=yn (⇑σ) f s h
 have hss:∀ x:Fin (n+1)->Bool,(x ∘ σ) ∘ σ=x:=by
   intro x;funext j;simp [hσ,Equiv.swap_apply_self]
 have hsl : σ.symm (Fin.last n)=p:=by
   rw [hσ,Equiv.symm_swap,Equiv.swap_apply_right]
 have hdep':∃ x:Fin (n+1)->Bool,
     (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
       ≠ (fun x => f (x ∘ σ)) x:=by
   obtain ⟨x0,hx0⟩:=hdep
   refine ⟨x0 ∘ σ,?_⟩
   simp only
   rw [Function.update_comp_equiv,hsl,hss]
   have:(x0 ∘ ⇑σ) (Fin.last n)=x0 p:=by simp [hσ,Equiv.swap_apply_right]
   rw [this];exact hx0
 have hnc':∃ y y':Fin n->Bool,
     (fun x => f (x ∘ σ)) (Fin.snoc y b)≠(fun x => f (x ∘ σ)) (Fin.snoc y' b):=by
   obtain ⟨x,y,hxy⟩:=hnc
   refine ⟨fun j => x (σ j.castSucc),fun j => y (σ j.castSucc),?_⟩
   simp only
   rw [ks,ks]
   exact hxy
 obtain ⟨s',hs,h'⟩:=q115 n _ b s hdep' hnc' hg
 refine ⟨s',hs,?_⟩
 have h'':=yn (fun j:Fin n => σ j.castSucc) _ s' h'
 have e:(fun x:Fin (n+1)->Bool =>
     (fun y:Fin n->Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
       (x ∘ fun j:Fin n => σ j.castSucc))
     = fun x => f (Function.update x p b):=by
   funext x
   simp only
   exact congrArg f (ks n p x b)
 rw [e] at h''
 exact h''
lemma q141 (n : ℕ) (f:(Fin (n+1)->Bool)->Bool) (p:Fin (n+1)) (s : ℕ)
   (hdep:∃ x:Fin (n+1)->Bool,f (Function.update x p (!x p))≠f x)
   (hnc:∀ b:Bool,∃ x y:Fin (n+1)->Bool,
     f (Function.update x p b)≠f (Function.update y p b))
   (h:HasCircuitSize (n+1) f s) :
   ∃ (b:Bool) (s' : ℕ),s'+2<=s /\
     HasCircuitSize (n+1) (fun x => f (Function.update x p b)) s':=by
 set σ:Equiv.Perm (Fin (n+1)):=Equiv.swap p (Fin.last n) with hσ
 have hg:HasCircuitSize (n+1) (fun x => f (x ∘ σ)) s:=yn (⇑σ) f s h
 have hss:∀ x:Fin (n+1)->Bool,(x ∘ σ) ∘ σ=x:=by
   intro x;funext j;simp [hσ,Equiv.swap_apply_self]
 have hsl : σ.symm (Fin.last n)=p:=by
   rw [hσ,Equiv.symm_swap,Equiv.swap_apply_right]
 have hdep':∃ x:Fin (n+1)->Bool,
     (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
       ≠ (fun x => f (x ∘ σ)) x:=by
   obtain ⟨x0,hx0⟩:=hdep
   refine ⟨x0 ∘ σ,?_⟩
   simp only
   rw [Function.update_comp_equiv,hsl,hss]
   have:(x0 ∘ ⇑σ) (Fin.last n)=x0 p:=by simp [hσ,Equiv.swap_apply_right]
   rw [this];exact hx0
 have hnc':∀ b:Bool,∃ y y':Fin n->Bool,
     (fun x => f (x ∘ σ)) (Fin.snoc y b)≠(fun x => f (x ∘ σ)) (Fin.snoc y' b):=by
   intro b
   obtain ⟨x,y,hxy⟩:=hnc b
   refine ⟨fun j => x (σ j.castSucc),fun j => y (σ j.castSucc),?_⟩
   simp only
   rw [ks,ks]
   exact hxy
 obtain ⟨b,s',hs,h'⟩:=q114 n _ s hdep' hnc' hg
 refine ⟨b,s',hs,?_⟩
 have h'':=yn (fun j:Fin n => σ j.castSucc) _ s' h'
 have e:(fun x:Fin (n+1)->Bool =>
     (fun y:Fin n->Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
       (x ∘ fun j:Fin n => σ j.castSucc))
     = fun x => f (Function.update x p b):=by
   funext x
   simp only
   exact congrArg f (ks n p x b)
 rw [e] at h''
 exact h''
def val (gs:List Gate) (n : ℕ) (a : ℕ):BFn n :=
 fun x => (q3 gs (List.ofFn x)).getD a false
lemma q172 (gs:List Gate) (n : ℕ) (i:Fin n):val gs n i=fun x => x i:=by
 funext x
 unfold val
 rw [ve _ _ _ (by simp)]
 simp
lemma q60 {α:Type} (gs:List α) (p : ℕ) (g : α) (hp:gs[p]?=some g) :
   ∃ pre post,gs=pre++g::post/\pre.length=p:=by
 have hlt:p < gs.length:=(List.getElem?_eq_some_iff.1 hp).1
 have hget:gs[p]=g:=(List.getElem?_eq_some_iff.1 hp).2
 refine ⟨gs.take p,gs.drop (p+1),?_,by simp;omega⟩
 have h1:gs=gs.take p++gs.drop p:=(List.take_append_drop p gs).symm
 have h2:gs.drop p=gs[p]::gs.drop (p+1):=List.drop_eq_getElem_cons hlt
 exact h1.trans (by rw [h2,hget])
lemma q103 (n : ℕ) (gs:List Gate) (p : ℕ) (g:Gate) (hp:gs[p]?=some g)
   (hlt:∀ a ∈ g.inputs,a < n+p) (x:Fin n->Bool) :
   val gs n (n+p) x=g.op.eval (g.inputs.map fun a => val gs n a x):=by
 obtain ⟨pre,post,rfl,hlen⟩:=q60 gs p g hp
 unfold val
 have h1:q3 (pre++g::post) (List.ofFn x)=q3 post
     (q3 pre (List.ofFn x) ++
       [g.op.eval (g.inputs.map fun i => (q3 pre (List.ofFn x)).getD i false)]):=by
   rw [zd];rfl
 have hl:(q3 pre (List.ofFn x)).length=n+p:=by
   rw [qu];simp [hlen]
 rw [h1,ve _ _ _ (by simp [hl]),z2 _ _ _ _ hl]
 congr 1
 apply List.map_congr_left
 intro a ha
 have hal:=hlt a ha
 have e1:=ve post (q3 pre (List.ofFn x) ++
       [g.op.eval (g.inputs.map fun i => (q3 pre (List.ofFn x)).getD i false)]) a
       (by simp [hl];omega)
 rw [e1,List.getD_append _ _ _ _ (by omega)]
def vi (n : ℕ):List Stat:=List.ofFn fun i:Fin n => Sum.inr (i : ℕ)
lemma q165 (n : ℕ) (y:Fin n->Bool) :
   Inv n (List.ofFn y) (List.ofFn y) (vi n,[]):=by
 refine ⟨by simp [vi],?_⟩
 intro i
 by_cases hlt:i < n
 . simp [vi,hlt,qn,ze,q3]
 . rw [lGD _ _ (by simp [vi];omega),
       lGD _ _ (by simp;omega)]
   exact ⟨trivial,rfl⟩
lemma q48 (n : ℕ) (f:BFn n) (s : ℕ)
   (hnc:∃ y y':Fin n->Bool,f y≠f y') (h:HasCircuitSize n f s) :
   ∃ gs o,yq n gs/\gs.length<=s/\o < n+gs.length/\∀ x,val gs n o x=f x:=by
 obtain ⟨C,ok,hsz,hev⟩:=h
 have hsz':C.gates.length<=s:=hsz
 set acc:=elim n C.gates (vi n,[]) with hacc
 have hinv:∀ y:Fin n->Bool,Inv n (List.ofFn y) (q3 C.gates (List.ofFn y)) acc :=
   fun y => j7 n _ (by simp) C.gates _ _ ok (q165 n y)
 have hcl:yq n acc.2:=by
   apply q100 n C.gates (vi n,[]) ok
   . intro i
     by_cases hlt:i < n
     . simp [vi,hlt,qn]
     . rw [lGD _ _ (by simp [vi];omega)];trivial
   . intro p g hp;simp at hp
 have hlen:acc.2.length<=s:=by
   have:=q29 n C.gates (vi n,[])
   rw [← hacc] at this
   simp only [List.length_nil,zero_add] at this
   omega
 cases hst:acc.1.getD C.output (Sum.inl false) with
 | inl c =>
   exfalso
   obtain ⟨y,y',hne⟩:=hnc
   apply hne
   have e1:=((hinv y).2 C.output).2
   have e2:=((hinv y').2 C.output).2
   rw [hst] at e1 e2
   have h1:(q3 C.gates (List.ofFn y)).getD C.output false=f y:=hev y
   have h2:(q3 C.gates (List.ofFn y')).getD C.output false=f y':=hev y'
   rw [← h1,← h2,← e1,← e2];rfl
 | inr j =>
   have hj:j < n+acc.2.length:=by
     obtain ⟨y,_,_⟩:=hnc
     have:=((hinv y).2 C.output).1
     rw [hst] at this
     exact this
   refine ⟨acc.2,j,hcl,hlen,hj,?_⟩
   intro x
   have e1:=((hinv x).2 C.output).2
   rw [hst] at e1
   exact e1.trans (hev x)
def qk {α:Type} (b:Bool) (x : α) (xs:List α):List α :=
 if b then x::xs else xs
def Run {α:Type} (inv : α->α) (meet join : α->α->α) (y : α) (t : ℕ) (ws:List α):Prop :=
 ∀ P : ℕ->List α->Prop,P 0 [y] ->
   (∀ {s xs zs},List.Perm xs zs->P s xs->P s zs) ->
   (∀ {s a r} (neg save:Bool),P s ((if neg then inv a else a)::qk save a r) ->
     P (s+1) (a::r)) ->
   (∀ {s a b r} (c ka kb:Bool),
     P s ((if c then meet a b else join a b)::qk ka a (qk kb b r)) ->
     P (s+1) (a::b::r))->P t ws
lemma Run.done {α inv meet join y} : @Run α inv meet join y 0 [y]:=fun _ d _ _ _ => d
lemma Run.perm {α inv meet join y s xs zs} (p:List.Perm xs zs)
   (h : @Run α inv meet join y s xs):Run inv meet join y s zs :=
 fun P d q u b => q p (h P d q u b)
lemma Run.one {α inv meet join y s a r} (neg save:Bool)
   (h : @Run α inv meet join y s ((if neg then inv a else a)::qk save a r)) :
   Run inv meet join y (s+1) (a::r):=fun P d q u b => u neg save (h P d q u b)
lemma Run.two {α inv meet join y s a b r} (c ka kb:Bool)
   (h : @Run α inv meet join y s ((if c then meet a b else join a b)::qk ka a (qk kb b r))) :
   Run inv meet join y (s+1) (a::b::r):=fun P d q u v => v c ka kb (h P d q u v)
lemma Run.fold {α inv meet join y} {P:∀ t ws,@Run α inv meet join y t ws->Prop}
   (done:P 0 [y] Run.done)
   (perm:∀ {s xs zs} (hp:List.Perm xs zs) (h:Run inv meet join y s xs),
     P s xs h->P s zs (Run.perm hp h))
   (one:∀ {s a r} (neg save:Bool)
     (h:Run inv meet join y s ((if neg then inv a else a)::qk save a r)),
     P _ _ h->P _ _ (Run.one neg save h))
   (two:∀ {s a b r} (c ka kb:Bool)
     (h:Run inv meet join y s ((if c then meet a b else join a b)::qk ka a (qk kb b r))),
     P _ _ h->P _ _ (Run.two c ka kb h))
   {t ws} (h:Run inv meet join y t ws):P t ws h:=by
 have hex:=h (fun s xs => ∃ h':Run inv meet join y s xs,P s xs h')
   ⟨Run.done,done⟩
   (fun hp ⟨h',ih⟩ => ⟨Run.perm hp h',perm hp h' ih⟩)
   (fun n k ⟨h',ih⟩ => ⟨Run.one n k h',one n k h' ih⟩)
   (fun c a b ⟨h',ih⟩ => ⟨Run.two c a b h',two c a b h' ih⟩)
 exact hex.elim fun _ hp => hp
lemma wd {α β:Type} (e : α->β) (b:Bool) (x : α) (xs:List α) :
   (qk b x xs).map e=qk b (e x) (xs.map e):=by cases b <;> simp [qk]
lemma wa {α:Type} (b:Bool) (x a : α) (xs:List α) :
   a ∈ qk b x xs ↔ (b=true/\a=x)\/a ∈ xs:=by cases b <;> simp [qk]
lemma q36 {α:Type} (b:Bool) (x : α) (xs:List α) (h:xs.Nodup) (hx:x ∉ xs) :
   (qk b x xs).Nodup:=by
 cases b
 . simpa [qk] using h
 . simpa [qk] using And.intro hx h
lemma Run.map {α β:Type} (e : α->β) {inv : α->α} {meet join : α->α->α}
   {inv' : β->β} {meet' join' : β->β->β}
   (hi:∀ a,e (inv a)=inv' (e a)) (hm:∀ a b,e (meet a b)=meet' (e a) (e b))
   (hj:∀ a b,e (join a b)=join' (e a) (e b))
   {y : α} {s : ℕ} {ws:List α} (h:Run inv meet join y s ws) :
   Run inv' meet' join' (e y) s (ws.map e):=by
 induction h using Run.fold with
 | done => exact Run.done
 | perm hp _ ih => exact Run.perm (hp.map e) ih
 | @one s a rest neg save _ ih =>
   have e1:((if neg then inv a else a)::qk save a rest).map e
       = (if neg then inv' (e a) else e a)::qk save (e a) (rest.map e):=by
     cases neg <;> simp [wd,hi]
   rw [e1] at ih
   exact Run.one neg save ih
 | @two s a b rest conj ka kb _ ih =>
   have e1:((if conj then meet a b else join a b)::qk ka a (qk kb b rest)).map e
       = (if conj then meet' (e a) (e b) else join' (e a) (e b))
           :: qk ka (e a) (qk kb (e b) (rest.map e)):=by
     cases conj <;> simp [wd,hm,hj]
   rw [e1] at ih
   exact Run.two conj ka kb ih
def wn (n : ℕ) (gs:List Gate) (o a : ℕ):Prop :=
 ∀ P : ℕ->Prop,P o ->
   (∀ q g,gs[q]?=some g->P (n+q)->∀ u ∈ g.inputs,P u)->P a
lemma q34 (n : ℕ) (gs:List Gate) (o : ℕ):wn n gs o o :=
 fun _ ho _ => ho
lemma q33 {n : ℕ} {gs:List Gate} {o q u : ℕ} {g:Gate}
   (hq:gs[q]?=some g) (hr:wn n gs o (n+q)) (hu:u ∈ g.inputs) :
   wn n gs o u :=
 fun P ho hs => hs q g hq (hr P ho hs) u hu
lemma q66 {n : ℕ} {gs:List Gate} {o a : ℕ} (h:wn n gs o a) :
   a=o\/∃ q g,gs[q]?=some g/\a ∈ g.inputs/\wn n gs o (n+q):=by
 apply h (fun x => x=o\/∃ q g,gs[q]?=some g/\x ∈ g.inputs/\wn n gs o (n+q))
 . exact Or.inl rfl
 . intro q g hq hP u hu
   refine Or.inr ⟨q,g,hq,hu,?_⟩
   rcases hP with rfl | ⟨q',g',hq',hin',hr'⟩
   . exact q34 n gs (n+q)
   . exact q33 hq' hr' hin'
def q11 (n : ℕ) (gs:List Gate) (o p a : ℕ):Prop :=
 a=o\/∃ q,p<=q/\∃ g,gs[q]?=some g/\a ∈ g.inputs/\wn n gs o (n+q)
open Classical in
noncomputable def liveList (gs:List Gate) (n o p : ℕ):List ℕ :=
 (List.range (n+p)).filter (fun a => decide (q11 n gs o p a))
lemma qw (gs:List Gate) (n o p a : ℕ) :
   a ∈ liveList gs n o p ↔ a < n+p/\q11 n gs o p a:=by
 simp [liveList]
lemma vy (gs:List Gate) (n o p : ℕ):(liveList gs n o p).Nodup :=
 List.Nodup.filter _ List.nodup_range
abbrev invF {n : ℕ}:BFn n->BFn n:=fun a x => !a x
abbrev meetF {n : ℕ}:BFn n->BFn n->BFn n:=fun a b x => a x&&b x
abbrev joinF {n : ℕ}:BFn n->BFn n->BFn n:=fun a b x => a x||b x
lemma q73 (n : ℕ) (gs:List Gate) (o : ℕ) (hcl:yq n gs)
   (p : ℕ) (g:Gate) (hg:gs[p]?=some g) (hr:wn n gs o (n+p)) (a : ℕ) :
   a ∈ liveList gs n o (p+1) ↔
     a=n+p\/(a ∈ liveList gs n o p/\(a ∈ g.inputs->q11 n gs o (p+1) a)):=by
 rw [qw,qw]
 constructor
 . rintro ⟨hlt,hl⟩
   by_cases ha:a=n+p
   . exact Or.inl ha
   . refine Or.inr ⟨⟨by omega,?_⟩,fun _ => hl⟩
     rcases hl with h | ⟨q,hq,g',hg',hin,hrq⟩
     . exact Or.inl h
     . exact Or.inr ⟨q,by omega,g',hg',hin,hrq⟩
 . rintro (rfl | ⟨⟨hlt,hl⟩,himp⟩)
   . refine ⟨by omega,?_⟩
     rcases q66 hr with h | ⟨q,g',hg',hin,hrq⟩
     . exact Or.inl h
     . refine Or.inr ⟨q,?_,g',hg',hin,hrq⟩
       have:=j2 (hcl q g' hg') _ hin
       omega
   . refine ⟨by omega,?_⟩
     rcases hl with h | ⟨q,hq,g',hg',hin,hrq⟩
     . exact Or.inl h
     . by_cases hqp:q=p
       . subst hqp
         rw [hg] at hg'
         cases hg'
         exact himp hin
       . exact Or.inr ⟨q,by omega,g',hg',hin,hrq⟩
def gfn {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)):BFn n :=
 fun x => A.any (fun a => x a)||E.any (fun e => x e.1&&x e.2)
def j9 {α:Type} [BEq α]:List α->List α->List α
 | [],acc => acc.reverse
 | a::t,acc => if acc.contains a then j9 t acc else j9 t (a::acc)
def q206 {α:Type} [BEq α] (l:List α):List α:=j9 l []
lemma ww {α:Type} [DecidableEq α]:∀ (l acc:List α) (x : α),
   x ∈ j9 l acc ↔ x ∈ l\/x ∈ acc
 | [],acc,x => by simp [j9]
 | a::t,acc,x => by
   simp only [j9]
   by_cases h:acc.contains a=true
   . simp only [h,↓reduceIte,ww,lMM]
     have ha:a ∈ acc:=by simpa using h
     constructor
     . rintro (ht | hacc)
       . exact Or.inl (Or.inr ht)
       . exact Or.inr hacc
     . rintro ((rfl | ht) | hacc)
       . exact Or.inr ha
       . exact Or.inl ht
       . exact Or.inr hacc
   . simp only [h,bFT,↓reduceIte,ww,lMM]
     tauto
lemma q23 {α:Type} [DecidableEq α] (l:List α) (x : α) :
   x ∈ q206 l ↔ x ∈ l:=by
 simpa [q206] using ww l [] x
def fix0A {n : ℕ} (A:List (Fin n)) (p:Fin n):List (Fin n) :=
 A.filter (·!=p)
def fix0E {n : ℕ} (E:List (Fin n × Fin n)) (p:Fin n):List (Fin n × Fin n) :=
 E.filter (fun e => e.1!=p&&e.2!=p)
def nbrs {n : ℕ} (E:List (Fin n × Fin n)) (p:Fin n):List (Fin n) :=
 E.filterMap (fun e => if e.1==p then some e.2 else if e.2==p then some e.1 else none)
def fix1A {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)) (p:Fin n):List (Fin n) :=
 q206 (A++nbrs E p)
def fix1E {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)) (p:Fin n):List (Fin n × Fin n) :=
 let A1:=fix1A A E p
 E.filter (fun e => e.1!=p&&e.2!=p&&!A1.contains e.1&&!A1.contains e.2)
def depCheck {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)) (p:Fin n):Bool :=
 A.contains p ||
   (E.all (fun e => e.1!=e.2) &&
     E.any (fun e => (e.1==p&&!A.contains e.2)||(e.2==p&&!A.contains e.1)))
def isoCheck {n k : ℕ} (E:List (Fin n × Fin n)) (Eb:List (Fin k × Fin k)) (π:Fin n->Fin k):Bool :=
 E.all (fun e => Eb.any (fun e' => (π e.1==e'.1&&π e.2==e'.2)||(π e.1==e'.2&&π e.2==e'.1))) &&
 Eb.all (fun e' => E.any (fun e => (π e.1==e'.1&&π e.2==e'.2)||(π e.1==e'.2&&π e.2==e'.1)))
lemma q216 {n val1 val2 : ℕ} {f:BFn n} (hle:val1<=val2)
   (h:∀ s,HasCircuitSize n f s->val2<=s):∀ s,HasCircuitSize n f s->val1<=s :=
 fun s hs => le_trans hle (h s hs)
lemma q176 {n : ℕ} (A:List (Fin n)) (hnd:A.Nodup) :
   ∀ s : ℕ,HasCircuitSize n (gfn A []) s->A.length - 1<=s:=by
 intro s h
 have hd:=q117 n (gfn A []) A.toFinset (by
   intro i hi
   have hiA:i ∈ A:=List.mem_toFinset.1 hi
   refine ⟨fun _ => false,?_⟩
   have h0:gfn A [] (fun _ => false)=false:=by simp [gfn]
   have h1:gfn A [] (Function.update (fun _ => false) i true)=true:=by
     simp only [gfn,List.any_nil,Bool.or_false,lAN]
     exact ⟨i,hiA,by simp⟩
   simpa [h0,h1]) s h
 rw [List.toFinset_card_of_nodup hnd] at hd
 omega
lemma q99 {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n))
   (h:(!A.isEmpty||!E.isEmpty)=true) :
   ∃ x y:Fin n->Bool,gfn A E x≠gfn A E y:=by
 refine ⟨fun _ => false,fun _ => true,?_⟩
 have h0:gfn A E (fun _ => false)=false:=by simp [gfn]
 have h1:gfn A E (fun _ => true)=true:=by
   cases A with
   | cons a t => simp [gfn]
   | nil =>
     cases E with
     | nil => simp at h
     | cons e t => simp [gfn]
 rw [h0,h1];decide
lemma q154 {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)) (p:Fin n)
   (h:depCheck A E p=true) :
   ∃ x:Fin n->Bool,gfn A E (Function.update x p (!x p))≠gfn A E x:=by
 simp only [depCheck,bOT,bAT,List.contains_eq_mem,decide_eq_true_eq,
   lAL,lAN,bne_iff_ne,beq_iff_eq,bNT,
   decide_eq_false_iff_not] at h
 rcases h with hpA | ⟨hloop,⟨e,heE,⟨rfl,hqA⟩ | ⟨rfl,hqA⟩⟩⟩
 . refine ⟨fun _ => false,?_⟩
   have h0:gfn A E (fun _ => false)=false:=by simp [gfn]
   have h1:gfn A E (Function.update (fun _ => false) p true)=true:=by
     simp only [gfn,bOT,lAN]
     exact Or.inl ⟨p,hpA,by simp⟩
   simpa [h0,h1]
 . have hne:e.1≠e.2:=hloop e heE
   refine ⟨fun i => decide (i=e.2),?_⟩
   have h0:gfn A E (fun i => decide (i=e.2))=false:=by
     simp only [gfn,Bool.or_eq_false_iff,List.any_eq_false,decide_eq_true_eq,bAT]
     refine ⟨fun a ha hEq => hqA (hEq ▸ ha),fun e' he' => ?_⟩
     intro ⟨h1,h2⟩
     exact hloop e' he' (h1.trans h2.symm)
   have h1:gfn A E (Function.update (fun i => decide (i=e.2)) e.1 (!decide (e.1=e.2)))=true:=by
     simp only [gfn,bOT,lAN,bAT]
     refine Or.inr ⟨e,heE,?_,?_⟩
     . simp [hne]
     . simp [fUN (Ne.symm hne)]
   rw [h0,h1];decide
 . have hne:e.1≠e.2:=hloop e heE
   refine ⟨fun i => decide (i=e.1),?_⟩
   have h0:gfn A E (fun i => decide (i=e.1))=false:=by
     simp only [gfn,Bool.or_eq_false_iff,List.any_eq_false,decide_eq_true_eq,bAT]
     refine ⟨fun a ha hEq => hqA (hEq ▸ ha),fun e' he' => ?_⟩
     intro ⟨h1,h2⟩
     exact hloop e' he' (h1.trans h2.symm)
   have h1:gfn A E (Function.update (fun i => decide (i=e.1)) e.2 (!decide (e.2=e.1)))=true:=by
     simp only [gfn,bOT,lAN,bAT]
     refine Or.inr ⟨e,heE,?_,?_⟩
     . simp [fUN hne]
     . simp [Ne.symm hne]
   rw [h0,h1];decide
lemma zo {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)) (p:Fin n) :
   (fun x => gfn A E (Function.update x p false))=gfn (fix0A A p) (fix0E E p):=by
 funext x
 apply Bool.eq_iff_iff.2
 simp only [gfn,fix0A,fix0E,bOT,lAN,List.mem_filter,
   bAT,bne_iff_ne]
 constructor
 . rintro (⟨a,ha,hxa⟩ | ⟨e,he,h1,h2⟩)
   . by_cases hap:a=p
     . subst hap;simp at hxa
     . exact Or.inl ⟨a,⟨ha,hap⟩,by simpa [fUN hap] using hxa⟩
   . by_cases h1p:e.1=p
     . rw [h1p,fUS] at h1;cases h1
     . by_cases h2p:e.2=p
       . rw [h2p,fUS] at h2;cases h2
       . exact Or.inr ⟨e,⟨he,h1p,h2p⟩,
           by simpa [fUN h1p] using h1,
           by simpa [fUN h2p] using h2⟩
 . rintro (⟨a,⟨ha,hap⟩,hxa⟩ | ⟨e,⟨he,h1p,h2p⟩,h1,h2⟩)
   . exact Or.inl ⟨a,ha,by simpa [fUN hap] using hxa⟩
   . exact Or.inr ⟨e,he,
       by simpa [fUN h1p] using h1,
       by simpa [fUN h2p] using h2⟩
lemma q109 {n : ℕ} (E:List (Fin n × Fin n)) (p q:Fin n) :
   q ∈ nbrs E p ↔ ∃ e ∈ E,(e.1=p/\e.2=q)\/(e.1≠p/\e.2=p/\e.1=q):=by
 simp only [nbrs,List.mem_filterMap,beq_iff_eq]
 constructor
 . rintro ⟨e,he,h⟩
   split_ifs at h with h1 h2
   . cases h;exact ⟨e,he,Or.inl ⟨h1,rfl⟩⟩
   . cases h;exact ⟨e,he,Or.inr ⟨h1,h2,rfl⟩⟩
 . rintro ⟨e,he,⟨h1,h2⟩ | ⟨h1,h2,h3⟩⟩
   . exact ⟨e,he,by rw [if_pos h1,h2]⟩
   . exact ⟨e,he,by rw [if_neg h1,if_pos h2,h3]⟩
lemma kx {n : ℕ} (A:List (Fin n)) (E:List (Fin n × Fin n)) (p:Fin n)
   (hpA : !A.contains p=true) (hloop:E.all (fun e => e.1!=e.2)=true) :
   (fun x => gfn A E (Function.update x p true))=gfn (fix1A A E p) (fix1E A E p):=by
 have hpnot:p ∉ A:=by simpa [List.contains_eq_mem] using hpA
 have hne:∀ e ∈ E,e.1≠e.2:=by simpa [lAL,bne_iff_ne] using hloop
 funext x
 apply Bool.eq_iff_iff.2
 simp only [gfn,fix1E,bOT,lAN,bAT,List.mem_filter,
   bne_iff_ne,bNT,List.contains_eq_mem,decide_eq_false_iff_not]
 constructor
 . rintro (⟨a,ha,hxa⟩ | ⟨e,he,h1,h2⟩)
   . have hap:a≠p:=fun h => hpnot (h ▸ ha)
     refine Or.inl ⟨a,?_,by simpa [fUN hap] using hxa⟩
     rw [fix1A,q23];exact List.mem_append_left _ ha
   . by_cases h1p:e.1=p
     . have h2p:e.2≠p:=fun h => hne e he (h1p.trans h.symm)
       refine Or.inl ⟨e.2,?_,by simpa [fUN h2p] using h2⟩
       rw [fix1A,q23];exact List.mem_append_right _ ((q109 E p e.2).2 ⟨e,he,Or.inl ⟨h1p,rfl⟩⟩)
     . by_cases h2p:e.2=p
       . refine Or.inl ⟨e.1,?_,by simpa [fUN h1p] using h1⟩
         rw [fix1A,q23];exact List.mem_append_right _ ((q109 E p e.1).2 ⟨e,he,Or.inr ⟨h1p,h2p,rfl⟩⟩)
       . have hx1:x e.1=true:=by simpa [fUN h1p] using h1
         have hx2:x e.2=true:=by simpa [fUN h2p] using h2
         by_cases m1:e.1 ∈ fix1A A E p
         . exact Or.inl ⟨e.1,m1,hx1⟩
         . by_cases m2:e.2 ∈ fix1A A E p
           . exact Or.inl ⟨e.2,m2,hx2⟩
           . exact Or.inr ⟨e,⟨he,⟨⟨h1p,h2p⟩,m1⟩,m2⟩,hx1,hx2⟩
 . rintro (⟨a,ha,hxa⟩ | ⟨e,⟨he,⟨⟨h1p,h2p⟩,_⟩,_⟩,hx1,hx2⟩)
   . rw [fix1A,q23,List.mem_append] at ha
     rcases ha with haA | han
     . have hap:a≠p:=fun h => hpnot (h ▸ haA)
       exact Or.inl ⟨a,haA,by simpa [fUN hap] using hxa⟩
     . obtain ⟨e,he,⟨h1,rfl⟩ | ⟨h1,h2,rfl⟩⟩:=(q109 E p a).1 han
       . have h2p:e.2≠p:=fun h => hne e he (h1.trans h.symm)
         exact Or.inr ⟨e,he,by simp [h1],by simpa [fUN h2p] using hxa⟩
       . exact Or.inr ⟨e,he,by simpa [fUN h1] using hxa,by simp [h2]⟩
   . exact Or.inr ⟨e,he,
       by simpa [fUN h1p] using hx1,
       by simpa [fUN h2p] using hx2⟩
lemma q190 {n : ℕ} (A:List (Fin (n+1))) (E:List (Fin (n+1) × Fin (n+1)))
   (p:Fin (n+1)) (A':List (Fin (n+1))) (E':List (Fin (n+1) × Fin (n+1))) (k : ℕ)
   (hdep:depCheck A E p=true)
   (hA:A'=fix0A A p) (hE:E'=fix0E E p)
   (hnc:(!A'.isEmpty||!E'.isEmpty)=true)
   (ih:∀ s,HasCircuitSize (n+1) (gfn A' E') s->k<=s) :
   ∀ s,HasCircuitSize (n+1) (gfn A E) s->k+1<=s:=by
 intro s h
 have hres:(fun x => gfn A E (Function.update x p false))=gfn A' E':=by
   rw [hA,hE];exact zo A E p
 have hnc':∃ x y,gfn A E (Function.update x p false)≠gfn A E (Function.update y p false):=by
   obtain ⟨x,y,hxy⟩:=q99 A' E' hnc
   exact ⟨x,y,by simpa [congrFun hres] using hxy⟩
 obtain ⟨s',hs',h'⟩:=q70 n (gfn A E) p false s (q154 A E p hdep) hnc' h
 rw [hres] at h'
 have:=ih s' h'
 omega
lemma q189 {n : ℕ} (A:List (Fin (n+1))) (E:List (Fin (n+1) × Fin (n+1)))
   (p:Fin (n+1)) (A':List (Fin (n+1))) (E':List (Fin (n+1) × Fin (n+1))) (k : ℕ)
   (hdep:depCheck A E p=true)
   (hpA : !A.contains p=true) (hloop:E.all (fun e => e.1!=e.2)=true)
   (hA:A'=fix1A A E p) (hE:E'=fix1E A E p)
   (hnc:(!A'.isEmpty||!E'.isEmpty)=true)
   (ih:∀ s,HasCircuitSize (n+1) (gfn A' E') s->k<=s) :
   ∀ s,HasCircuitSize (n+1) (gfn A E) s->k+1<=s:=by
 intro s h
 have hres:(fun x => gfn A E (Function.update x p true))=gfn A' E':=by
   rw [hA,hE];exact kx A E p hpA hloop
 have hnc':∃ x y,gfn A E (Function.update x p true)≠gfn A E (Function.update y p true):=by
   obtain ⟨x,y,hxy⟩:=q99 A' E' hnc
   exact ⟨x,y,by simpa [congrFun hres] using hxy⟩
 obtain ⟨s',hs',h'⟩:=q70 n (gfn A E) p true s (q154 A E p hdep) hnc' h
 rw [hres] at h'
 have:=ih s' h'
 omega
lemma q155 {n : ℕ} (A:List (Fin (n+1))) (E:List (Fin (n+1) × Fin (n+1)))
   (p:Fin (n+1))
   (A0:List (Fin (n+1))) (E0:List (Fin (n+1) × Fin (n+1)))
   (A1:List (Fin (n+1))) (E1:List (Fin (n+1) × Fin (n+1))) (k : ℕ)
   (hdep:depCheck A E p=true)
   (hpA : !A.contains p=true) (hloop:E.all (fun e => e.1!=e.2)=true)
   (hA0:A0=fix0A A p) (hE0:E0=fix0E E p)
   (hA1:A1=fix1A A E p) (hE1:E1=fix1E A E p)
   (hnc0:(!A0.isEmpty||!E0.isEmpty)=true)
   (hnc1:(!A1.isEmpty||!E1.isEmpty)=true)
   (ih0:∀ s,HasCircuitSize (n+1) (gfn A0 E0) s->k<=s)
   (ih1:∀ s,HasCircuitSize (n+1) (gfn A1 E1) s->k<=s) :
   ∀ s,HasCircuitSize (n+1) (gfn A E) s->k+2<=s:=by
 intro s h
 have hres0:(fun x => gfn A E (Function.update x p false))=gfn A0 E0:=by
   rw [hA0,hE0];exact zo A E p
 have hres1:(fun x => gfn A E (Function.update x p true))=gfn A1 E1:=by
   rw [hA1,hE1];exact kx A E p hpA hloop
 have hnc:∀ b:Bool,∃ x y,gfn A E (Function.update x p b)≠gfn A E (Function.update y p b):=by
   intro b
   cases b with
   | false =>
     obtain ⟨x,y,hxy⟩:=q99 A0 E0 hnc0
     exact ⟨x,y,by simpa [congrFun hres0] using hxy⟩
   | true =>
     obtain ⟨x,y,hxy⟩:=q99 A1 E1 hnc1
     exact ⟨x,y,by simpa [congrFun hres1] using hxy⟩
 obtain ⟨b,s',hs',h'⟩:=q141 n (gfn A E) p s (q154 A E p hdep) hnc h
 cases b with
 | false => rw [hres0] at h';have:=ih0 s' h';omega
 | true => rw [hres1] at h';have:=ih1 s' h';omega
lemma q204 {n k : ℕ} (E:List (Fin n × Fin n)) (Eb:List (Fin k × Fin k))
   (π:Fin n->Fin k) (hiso:isoCheck E Eb π=true) :
   (fun y:Fin k->Bool => gfn [] E (y ∘ π))=gfn [] Eb:=by
 simp only [isoCheck,bAT,lAL,lAN,
   bOT,beq_iff_eq] at hiso
 obtain ⟨h1,h2⟩:=hiso
 funext y
 apply Bool.eq_iff_iff.2
 simp only [gfn,List.any_nil,Bool.false_or,lAN,bAT,Function.comp_apply]
 constructor
 . rintro ⟨e,he,hy1,hy2⟩
   obtain ⟨e',he',⟨a,b⟩ | ⟨a,b⟩⟩:=h1 e he
   . exact ⟨e',he',a ▸ hy1,b ▸ hy2⟩
   . exact ⟨e',he',b ▸ hy2,a ▸ hy1⟩
 . rintro ⟨e',he',hy1,hy2⟩
   obtain ⟨e,he,⟨a,b⟩ | ⟨a,b⟩⟩:=h2 e' he'
   . exact ⟨e,he,a.symm ▸ hy1,b.symm ▸ hy2⟩
   . exact ⟨e,he,a.symm ▸ hy2,b.symm ▸ hy1⟩
lemma q191 {n k val : ℕ} (E:List (Fin n × Fin n)) (Eb:List (Fin k × Fin k))
   (π:Fin n->Fin k) (hiso:isoCheck E Eb π=true)
   (hb:∀ s : ℕ,HasCircuitSize k (gfn [] Eb) s->val<=s) :
   ∀ s : ℕ,HasCircuitSize n (gfn [] E) s->val<=s:=by
 intro s h
 have h':=yn π (gfn [] E) s h
 rw [q204 E Eb π hiso] at h'
 exact hb s h'
lemma q202 {α inv meet join y s xs} (h : @Run α inv meet join y s xs) :
   xs.length<=s+1:=by
 induction h using Run.fold with
 | done => simp
 | perm hp _ ih => rwa [← hp.length_eq]
 | one neg save h ih => cases save <;> simp_all [qk] <;> omega
 | two conj ka kb h ih => cases ka <;> cases kb <;> simp_all [qk] <;> omega
lemma q101 {m : ℕ} {g:Gate} (h:q161 m g):NOk g:=by
 rcases h with ⟨hop,j,_,hin⟩ | ⟨hop,j,k,_,_,hin⟩
 . exact ⟨⟨by simp [hop],by simp [hin]⟩,fun _ => by simp [hin]⟩
 . refine ⟨⟨?_,by simp [hin]⟩,fun hnot => ?_⟩
   . rcases hop with h1 | h1 <;> simp [h1]
   . rcases hop with h1 | h1 <;> rw [h1] at hnot <;> cases hnot
lemma ja {n : ℕ} {gs:List Gate} (h:yq n gs):∀ g ∈ gs,NOk g:=by
 intro g hg
 obtain ⟨p,hp,rfl⟩:=List.getElem_of_mem hg
 exact q101 (h p gs[p] (List.getElem?_eq_getElem hp))
lemma q157 {n : ℕ} {gs:List Gate} (h:yq n gs) (p : ℕ):yq n (gs.take p):=by
 intro q g hq
 have hlt:q < (gs.take p).length:=(List.getElem?_eq_some_iff.1 hq).1
 have hqp:q < p:=by simp at hlt;omega
 rw [List.getElem?_take_of_lt hqp] at hq
 exact h q g hq
def InvR (R : ℕ->Prop) (n : ℕ) (y:List Bool) (w:List Bool) (acc:List Stat × List Gate):Prop :=
 acc.1.length=w.length /\
 (∀ i : ℕ,qn (n+acc.2.length) (acc.1.getD i (Sum.inl false))) /\
 (∀ i : ℕ,R i->ze (q3 acc.2 y) (acc.1.getD i (Sum.inl false))=w.getD i false)
lemma q175 (R : ℕ->Prop) (n : ℕ) (y:List Bool) (hy:y.length=n) (gs:List Gate) :
   ∀ (w:List Bool) (acc:List Stat × List Gate),(∀ g ∈ gs,Ok g) ->
     (∀ q g,gs[q]?=some g->R (acc.1.length+q)->∀ a ∈ g.inputs,R a) ->
     InvR R n y w acc ->
     InvR R n y (q3 gs w) (elim n gs acc):=by
 induction gs with
 | nil => intro w acc _ _ h;exact h
 | cons g gs ih =>
   intro w acc hok hR h
   apply ih (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) (qa n acc g)
     (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
   . intro q g' hq hRq a ha
     have hlen:(qa n acc g).1.length=acc.1.length+1:=by simp [qa]
     rw [hlen] at hRq
     exact hR (q+1) g' (by simpa using hq) (by simpa [nAA,nAC 1 q] using hRq) a ha
   . obtain ⟨hl,hv,he⟩:=h
     set w':=q3 acc.2 y with hw'
     have lw':w'.length=n+acc.2.length:=by rw [hw',qu,hy]
     set ins:=g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
     have hgok:=hok g List.mem_cons_self
     have hs:=kn g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
       (by
         intro s hs
         obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
         rw [lw'];exact hv a)
     rw [lw'] at hs
     set r:=qg g.op (n+acc.2.length) ins with hr
     have hnew:q3 (acc.2++r.1.toList) y=q3 r.1.toList w':=by
       rw [zd]
     obtain ⟨t,ht,_⟩:=y1 r.1.toList w'
     refine ⟨by simp [qa,hl],?_,?_⟩
     . intro i
       show qn (n+(acc.2++r.1.toList).length) ((acc.1++[r.2]).getD i (Sum.inl false))
       rw [lLA,← nAA]
       by_cases hil:i=acc.1.length
       . subst hil;rw [z0];exact hs.1
       . rw [q8 _ _ _ _ hil];exact km (by omega) _ (hv i)
     . intro i hi
       show ze (q3 (acc.2++r.1.toList) y) ((acc.1++[r.2]).getD i (Sum.inl false))=_
       rw [hnew]
       by_cases hil:i=acc.1.length
       . subst hil
         rw [z0,hl,z0,hs.2]
         congr 1
         rw [hins,lMMp]
         apply List.map_congr_left
         intro a ha
         exact he a (hR 0 g rfl (by simpa using hi) a ha)
       . rw [q8 _ _ _ _ hil,q8 _ _ _ _ (by omega)]
         rw [ht,jg _ _ _ (by rw [lw'];exact hv i)]
         exact he i hi
lemma y7 (n : ℕ) (f:BFn n) (pre post:List Gate) (g:Gate) (o : ℕ)
   (hcl:yq n (pre++g::post)) (ho:o < n+(pre++g::post).length)
   (hev:∀ x,val (pre++g::post) n o x=f x)
   (hnc:∃ y y':Fin n->Bool,f y≠f y')
   (st:Stat) (hstV:qn (n+pre.length) st)
   (hcond:(∀ x,ze (q3 pre (List.ofFn x)) st=val (pre++g::post) n (n+pre.length) x) \/
            ¬ wn n (pre++g::post) o (n+pre.length)) :
   ∃ gs' o',yq n gs'/\gs'.length<=pre.length+post.length /\
     o' < n+gs'.length/\∀ x,val gs' n o' x=f x:=by
 set gs:=pre++g::post with hgs
 set p:=pre.length with hp
 set acc0:List Stat × List Gate:=(vi (n+p)++[st],pre) with hacc0
 set acc:=elim n post acc0 with hacc
 have hok_post:∀ g' ∈ post,Ok g':=fun g' hg' =>
   (ja hcl g' (List.mem_append_right _ (List.mem_cons_of_mem _ hg'))).1
 have hcl_pre:yq n pre:=by
   have:pre=gs.take p:=by simp [hgs,hp]
   rw [this];exact q157 hcl p
 have hv0:∀ i,qn (n+acc0.2.length) (acc0.1.getD i (Sum.inl false)):=by
   intro i
   simp only [hacc0,hp]
   by_cases hip:i=n+pre.length
   . subst hip;rw [z2 _ _ _ _ (by simp [vi])];exact hstV
   . rw [q8 _ _ _ _ (by simp [vi];omega)]
     by_cases hlt:i < n+pre.length
     . simp [vi,hlt,qn]
     . rw [lGD _ _ (by simp [vi];omega)];trivial
 have hcl':yq n acc.2:=q100 n post acc0 hok_post hv0 hcl_pre
 have hlen':acc.2.length<=pre.length+post.length:=by
   simpa [hacc,hacc0] using q29 n post acc0
 have hinv_all:∀ x:Fin n->Bool,
     qn (n+acc.2.length) (acc.1.getD o (Sum.inl false)) /\
     ze (q3 acc.2 (List.ofFn x)) (acc.1.getD o (Sum.inl false))=f x:=by
   intro x
   have hsplit:q3 gs (List.ofFn x)=q3 post (q3 (pre++[g]) (List.ofFn x)):=by
     have:gs=(pre++[g])++post:=by simp [hgs]
     rw [this,zd]
   have hl1:(q3 (pre++[g]) (List.ofFn x)).length=n+p+1:=by
     rw [qu];simp [hp];omega
   have hval_lt:∀ i < n+p,(q3 (pre++[g]) (List.ofFn x)).getD i false =
       (q3 pre (List.ofFn x)).getD i false:=by
     intro i hi
     rw [zd,ve _ _ _ (by rw [qu];simp;omega)]
   rcases hcond with hval_eq | hdead
   . have hinv0:Inv n (List.ofFn x) (q3 (pre++[g]) (List.ofFn x)) acc0:=by
       refine ⟨by simp [hacc0,vi,hl1],?_⟩
       intro i
       refine ⟨hv0 i,?_⟩
       simp only [hacc0]
       by_cases hip:i=n+p
       . subst hip
         rw [z2 _ _ _ _ (by simp [vi])]
         have h1:=hval_eq x
         unfold val at h1
         rw [hsplit,ve _ _ _ (by omega)] at h1
         exact h1
       . rw [q8 _ _ _ _ (by simp [vi];omega)]
         by_cases hlt:i < n+p
         . simp only [vi,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hlt,↓reduceDIte,
             Option.getD_some,ze]
           exact (hval_lt i hlt).symm
         . rw [lGD _ _ (by simp [vi];omega),
               lGD _ _ (by omega)];rfl
     have hres:=j7 n (List.ofFn x) (by simp) post _ acc0 hok_post hinv0
     rw [← hsplit] at hres
     have h1:=hres.2 o
     exact ⟨h1.1,h1.2.trans (hev x)⟩
   . have hinv0:InvR (wn n gs o) n (List.ofFn x) (q3 (pre++[g]) (List.ofFn x)) acc0:=by
       refine ⟨by simp [hacc0,vi,hl1],hv0,?_⟩
       intro i hi
       simp only [hacc0]
       have hne:i≠n+p:=fun e => hdead (e ▸ hi)
       rw [q8 _ _ _ _ (by simp [vi];omega)]
       by_cases hlt:i < n+p
       . simp only [vi,List.getD_eq_getElem?_getD,List.getElem?_ofFn,hlt,↓reduceDIte,
           Option.getD_some,ze]
         exact (hval_lt i hlt).symm
       . rw [lGD _ _ (by simp [vi];omega),
             lGD _ _ (by omega)];rfl
     have hR:∀ q g',post[q]?=some g'->wn n gs o (acc0.1.length+q)->∀ a ∈ g'.inputs,wn n gs o a:=by
       intro q g' hq hRq a ha
       have hidx:gs[p+1+q]?=some g':=by
         have:gs=(pre++[g])++post:=by simp [hgs]
         rw [this,List.getElem?_append_right (by simp [hp])]
         simpa [hp,Nat.add_sub_cancel_left] using hq
       have hlen0:acc0.1.length=n+p+1:=by simp [hacc0,vi]
       rw [hlen0] at hRq
       exact q33 hidx (by simpa [nAA] using hRq) ha
     have hres:=q175 (wn n gs o) n (List.ofFn x) (by simp) post _ acc0 hok_post hR hinv0
     rw [← hsplit] at hres
     exact ⟨hres.2.1 o,(hres.2.2 o (q34 n gs o)).trans (hev x)⟩
 cases hst:acc.1.getD o (Sum.inl false) with
 | inl c =>
   exfalso
   obtain ⟨y,y',hne⟩:=hnc
   apply hne
   have e1:=(hinv_all y).2
   have e2:=(hinv_all y').2
   rw [hst] at e1 e2
   exact e1.symm.trans e2
 | inr j =>
   obtain ⟨y,_,_⟩:=hnc
   have hj:=(hinv_all y).1
   rw [hst] at hj
   refine ⟨acc.2,j,hcl',hlen',hj,?_⟩
   intro x
   have e:=(hinv_all x).2
   rw [hst] at e
   exact e
structure MinClean (n : ℕ) (f:BFn n) (gs:List Gate) (o : ℕ):Prop where
 hcl:yq n gs
 ho:o < n+gs.length
 hev:∀ x,val gs n o x=f x
 hreach:∀ p < gs.length,wn n gs o (n+p)
 hncG:∀ p < gs.length,∀ c:Bool,val gs n (n+p)≠fun _ => c
 hndup:∀ p < gs.length,∀ u < n+p,val gs n (n+p)≠val gs n u
open Classical in
lemma q56 (n : ℕ) (f:BFn n) (s : ℕ)
   (hnc:∃ y y':Fin n->Bool,f y≠f y') (h:HasCircuitSize n f s) :
   ∃ gs o,MinClean n f gs o/\gs.length<=s:=by
 have hex:∃ k,∃ gs o,yq n gs/\gs.length=k/\o < n+gs.length/\∀ x,val gs n o x=f x:=by
   obtain ⟨gs,o,hcl,hlen,ho,hev⟩:=q48 n f s hnc h
   exact ⟨gs.length,gs,o,hcl,rfl,ho,hev⟩
 set k:=Nat.find hex with hk
 obtain ⟨gs,o,hcl,hlen,ho,hev⟩:=Nat.find_spec hex
 have hle:k<=s:=by
   obtain ⟨gs0,o0,hcl0,hlen0,ho0,hev0⟩:=q48 n f s hnc h
   exact le_trans (Nat.find_min' hex ⟨gs0,o0,hcl0,rfl,ho0,hev0⟩) hlen0
 have hmin:∀ gs' o',yq n gs'->o' < n+gs'.length->(∀ x,val gs' n o' x=f x)->gs.length<=gs'.length:=by
   intro gs' o' hcl' ho' hev'
   rw [hlen]
   exact Nat.find_min' hex ⟨gs',o',hcl',rfl,ho',hev'⟩
 refine ⟨gs,o,⟨hcl,ho,hev,?_,?_,?_⟩,by omega⟩
 . intro p hp
   by_contra hnr
   obtain ⟨g0,hg0⟩:∃ g0,gs[p]?=some g0:=⟨gs[p],List.getElem?_eq_getElem hp⟩
   obtain ⟨pre,post,hgs,hpl⟩:=q60 gs p g0 hg0
   subst hpl;subst hgs
   obtain ⟨gs',o',hcl',hlen',ho',hev'⟩ :=
     y7 n f pre post g0 o hcl ho hev hnc (Sum.inl false) trivial (Or.inr hnr)
   have:=hmin gs' o' hcl' ho' hev'
   simp at this;omega
 . intro p hp c heqc
   obtain ⟨g0,hg0⟩:∃ g0,gs[p]?=some g0:=⟨gs[p],List.getElem?_eq_getElem hp⟩
   obtain ⟨pre,post,hgs,hpl⟩:=q60 gs p g0 hg0
   subst hpl;subst hgs
   obtain ⟨gs',o',hcl',hlen',ho',hev'⟩ :=
     y7 n f pre post g0 o hcl ho hev hnc (Sum.inl c) trivial
       (Or.inl fun x => by rw [heqc];rfl)
   have:=hmin gs' o' hcl' ho' hev'
   simp at this;omega
 . intro p hp u hu hequ
   obtain ⟨g0,hg0⟩:∃ g0,gs[p]?=some g0:=⟨gs[p],List.getElem?_eq_getElem hp⟩
   obtain ⟨pre,post,hgs,hpl⟩:=q60 gs p g0 hg0
   subst hpl;subst hgs
   obtain ⟨gs',o',hcl',hlen',ho',hev'⟩ :=
     y7 n f pre post g0 o hcl ho hev hnc (Sum.inr u) hu
       (Or.inl fun x => by
         rw [hequ];unfold val
         rw [zd,ve _ _ _ (by rw [qu];simp;omega)];rfl)
   have:=hmin gs' o' hcl' ho' hev'
   simp at this;omega
def wf (n : ℕ) (v:Fin n):List Stat :=
 List.ofFn fun i:Fin n => if i=v then Sum.inl false else Sum.inr (i : ℕ)
lemma q139 (n : ℕ) (v:Fin n) (x:Fin n->Bool) :
   Inv n (List.ofFn x) (List.ofFn (Function.update x v false)) (wf n v,[]):=by
 refine ⟨by simp [wf],?_⟩
 intro i
 by_cases hlt:i < n
 . by_cases hiv:(⟨i,hlt⟩:Fin n)=v
   . subst hiv;simp [wf,hlt,qn,ze]
   . simp [wf,hlt,hiv,qn,ze,q3,fUN hiv]
 . rw [lGD _ _ (by simp [wf];omega),
       lGD _ _ (by simp;omega)]
   exact ⟨trivial,rfl⟩
lemma wz (n : ℕ) (f:BFn n) (gs:List Gate) (o : ℕ) (v:Fin n) (B : ℕ)
   (hcl:yq n gs) (hev:∀ x,val gs n o x=f x)
   (hnc0:∃ x y:Fin n->Bool,f (Function.update x v false)≠f (Function.update y v false))
   (hlb:∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->B<=s') :
   (∀ c,(elim n gs (wf n v,[])).1.getD o (Sum.inl false)≠Sum.inl c) /\
   B<=(elim n gs (wf n v,[])).2.length:=by
 set acc:=elim n gs (wf n v,[]) with hacc
 have hinv:∀ x,Inv n (List.ofFn x) (q3 gs (List.ofFn (Function.update x v false))) acc :=
   fun x => j7 n _ (by simp) gs _ _ (fun g hg => (ja hcl g hg).1) (q139 n v x)
 have hval:∀ x,ze (q3 acc.2 (List.ofFn x)) (acc.1.getD o (Sum.inl false))
     = f (Function.update x v false):=fun x => ((hinv x).2 o).2.trans (hev _)
 have hno:∀ c,acc.1.getD o (Sum.inl false)≠Sum.inl c:=by
   intro c hc
   obtain ⟨x,y,hne⟩:=hnc0
   apply hne
   rw [← hval x,← hval y,hc];rfl
 refine ⟨hno,?_⟩
 cases hst:acc.1.getD o (Sum.inl false) with
 | inl c => exact absurd hst (hno c)
 | inr j =>
   apply hlb acc.2.length
   refine ⟨⟨acc.2,j⟩,q156 n gs _ (by simp),le_refl _,?_⟩
   intro x;have:=hval x;rw [hst] at this;exact this
lemma k3 (n u w : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (∀ g ∈ gs,NOk g)->u < acc.1.length->w < acc.1.length ->
   (∃ cu,acc.1.getD u (Sum.inl false)=Sum.inl cu) ->
   (∃ cw,acc.1.getD w (Sum.inl false)=Sum.inl cw) ->
   (∃ g₁ ∈ gs,u ∈ g₁.inputs) ->
   (∃ g₂ ∈ gs,w ∈ g₂.inputs) ->
   (∀ g ∈ gs,¬ (u ∈ g.inputs/\w ∈ g.inputs)) ->
   (elim n gs acc).2.length+2<=acc.2.length+gs.length:=by
 induction gs with
 | nil => intro acc _ _ _ _ _ h1 _ _;obtain ⟨g,hg,_⟩:=h1;simp at hg
 | cons g gs ih =>
   intro acc hok hu hw hcu hcw hg1 hg2 hdisj
   rw [k4,lLC]
   have hgn:NOk g:=hok g List.mem_cons_self
   have hgsn:∀ g' ∈ gs,NOk g':=fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')
   by_cases hug:u ∈ g.inputs
   . have hwg:w ∉ g.inputs:=fun h => hdisj g List.mem_cons_self ⟨hug,h⟩
     obtain ⟨cu,hcu⟩:=hcu
     have h0:=vs n acc g hgn u hug cu hcu
     have hg2':∃ g' ∈ gs,w ∈ g'.inputs:=by
       obtain ⟨g',hg',hw'⟩:=hg2
       rcases List.mem_cons.1 hg' with rfl | hmem
       . exact absurd hw' hwg
       . exact ⟨g',hmem,hw'⟩
     have h1:=zt n w gs (qa n acc g) hgsn (by simp [qa];omega)
       (by obtain ⟨cw,hcw⟩:=hcw;exact ⟨cw,by simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hcw⟩)
       hg2'
     omega
   . by_cases hwg:w ∈ g.inputs
     . obtain ⟨cw,hcw⟩:=hcw
       have h0:=vs n acc g hgn w hwg cw hcw
       have hg1':∃ g' ∈ gs,u ∈ g'.inputs:=by
         obtain ⟨g',hg',hu'⟩:=hg1
         rcases List.mem_cons.1 hg' with rfl | hmem
         . exact absurd hu' hug
         . exact ⟨g',hmem,hu'⟩
       have h1:=zt n u gs (qa n acc g) hgsn (by simp [qa];omega)
         (by obtain ⟨cu,hcu⟩:=hcu;exact ⟨cu,by simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hcu⟩)
         hg1'
       omega
     . have hg1':∃ g' ∈ gs,u ∈ g'.inputs:=by
         obtain ⟨g',hg',hu'⟩:=hg1
         rcases List.mem_cons.1 hg' with rfl | hmem
         . exact absurd hu' hug
         . exact ⟨g',hmem,hu'⟩
       have hg2':∃ g' ∈ gs,w ∈ g'.inputs:=by
         obtain ⟨g',hg',hw'⟩:=hg2
         rcases List.mem_cons.1 hg' with rfl | hmem
         . exact absurd hw' hwg
         . exact ⟨g',hmem,hw'⟩
       have h1:=ih (qa n acc g) hgsn (by simp [qa];omega) (by simp [qa];omega)
         (by obtain ⟨cu,hcu⟩:=hcu;exact ⟨cu,by simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hcu⟩)
         (by obtain ⟨cw,hcw⟩:=hcw;exact ⟨cw,by simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hcw⟩)
         hg1' hg2' (fun g' hg' => hdisj g' (List.mem_cons_of_mem _ hg'))
       have h2:(qa n acc g).2.length<=acc.2.length+1:=by
         simp only [qa,lLA]
         have:=y2 (qg g.op (n+acc.2.length)
           (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
         omega
       omega
inductive TagRun {α:Type} (inv : α->α) (meet join : α->α->α) (zero one goal : α) :
   ℕ->List (α × ℕ)->Prop where
 | done (tg : ℕ):TagRun inv meet join zero one goal 0 [(goal,tg)]
 | perm {s xs zs}:List.Perm xs zs ->
     TagRun inv meet join zero one goal s xs ->
     TagRun inv meet join zero one goal s zs
 | uNot {s a ta r} (save:Bool) :
     ta≠1->ta≠2->(ta=3->save=false) ->
     inv a≠zero->inv a≠one->inv a≠a->(∀ x ∈ r,x.1≠inv a) ->
     TagRun inv meet join zero one goal s
       ((inv a,if ta=3 then 2 else 0)::qk save (a,0) r) ->
     TagRun inv meet join zero one goal (s+1) ((a,ta)::r)
 | bOr {s a ta b tb r} (ka kb:Bool) :
     ta≠2->tb≠2->(ta=1->ka=false)->(tb=1->kb=false) ->
     join a b≠zero->join a b≠one ->
     join a b≠a->join a b≠b->(∀ x ∈ r,x.1≠join a b) ->
     TagRun inv meet join zero one goal s
       ((join a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)) ->
     TagRun inv meet join zero one goal (s+1) ((a,ta)::(b,tb)::r)
 | bAnd {s a ta b tb r} (ka kb:Bool) :
     ta≠1->tb≠1->(ta≠0->ka=false)->(tb≠0->kb=false) ->
     meet a b≠zero->meet a b≠one ->
     meet a b≠a->meet a b≠b->(∀ x ∈ r,x.1≠meet a b) ->
     TagRun inv meet join zero one goal s
       ((meet a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)) ->
     TagRun inv meet join zero one goal (s+1) ((a,ta)::(b,tb)::r)
lemma TagRun.toRun {α:Type} {inv : α->α} {meet join : α->α->α} {zero one goal : α}
   {s : ℕ} {ws:List (α × ℕ)} (h:TagRun inv meet join zero one goal s ws) :
   Run inv meet join goal s (ws.map Prod.fst):=by
 induction h with
 | done _ => exact Run.done
 | perm hp _ ih => exact Run.perm (hp.map Prod.fst) ih
 | @uNot s a ta r save _ _ _ _ _ _ _ _ ih =>
   have e:(((inv a,if ta=3 then 2 else 0)::qk save (a,0) r).map Prod.fst)
       = (if true then inv a else a)::qk save a (r.map Prod.fst):=by
     cases save <;> simp [qk]
   rw [e] at ih
   exact Run.one true save ih
 | @bOr s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ ih =>
   have e:(((join a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).map Prod.fst)
       = (if false then meet a b else join a b)::qk ka a (qk kb b (r.map Prod.fst)):=by
     cases ka <;> cases kb <;> simp [qk]
   rw [e] at ih
   exact Run.two false ka kb ih
 | @bAnd s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ ih =>
   have e:(((meet a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)).map Prod.fst)
       = (if true then meet a b else join a b)::qk ka a (qk kb b (r.map Prod.fst)):=by
     cases ka <;> cases kb <;> simp [qk]
   rw [e] at ih
   exact Run.two true ka kb ih
lemma TagRun.len_le {α:Type} {inv : α->α} {meet join : α->α->α} {zero one goal : α}
   {s : ℕ} {ws:List (α × ℕ)} (h:TagRun inv meet join zero one goal s ws) :
   ws.length<=s+1:=by
 have:=q202 h.toRun
 simpa using this
lemma TagRun.map {α β:Type} (e : α->β) (hinj:Function.Injective e)
   {inv : α->α} {meet join : α->α->α} {zero one goal : α}
   {inv' : β->β} {meet' join' : β->β->β} {zero' one' goal' : β}
   (h0:e zero=zero') (h1:e one=one') (hg:e goal=goal')
   (hi:∀ a,e (inv a)=inv' (e a))
   (hm:∀ a b,e (meet a b)=meet' (e a) (e b))
   (hj:∀ a b,e (join a b)=join' (e a) (e b))
   {s : ℕ} {ws:List (α × ℕ)} (h:TagRun inv meet join zero one goal s ws) :
   TagRun inv' meet' join' zero' one' goal' s (ws.map fun p => (e p.1,p.2)):=by
 induction h with
 | done tg => rw [← hg];exact TagRun.done tg
 | perm hp _ ih => exact TagRun.perm (hp.map _) ih
 | @uNot s a ta r save h1t h2t h3t hnz hno hna hnr _ ih =>
   have e1:(((inv a,if ta=3 then 2 else 0)::qk save (a,0) r).map fun p => (e p.1,p.2))
       = (inv' (e a),if ta=3 then 2 else 0)::qk save (e a,0) (r.map fun p => (e p.1,p.2)):=by
     cases save <;> simp [qk,hi]
   rw [e1] at ih
   refine TagRun.uNot save h1t h2t h3t ?_ ?_ ?_ ?_ ih
   . rw [← hi,← h0];exact fun h => hnz (hinj h)
   . rw [← hi,← h1];exact fun h => hno (hinj h)
   . rw [← hi];exact fun h => hna (hinj h)
   . intro x hx
     obtain ⟨y,hy,rfl⟩:=List.mem_map.1 hx
     rw [← hi];exact fun h => hnr y hy (hinj h)
 | @bOr s a ta b tb r ka kb h1t h2t h3t h4t hnz hno hna hnb hnr _ ih =>
   have e1:(((join a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).map fun p => (e p.1,p.2))
       = (join' (e a) (e b),0)::qk ka (e a,if ta=3 then 1 else 0) (qk kb (e b,if tb=3 then 1 else 0) (r.map fun p => (e p.1,p.2))):=by
     cases ka <;> cases kb <;> simp [qk,hj]
   rw [e1] at ih
   refine TagRun.bOr ka kb h1t h2t h3t h4t ?_ ?_ ?_ ?_ ?_ ih
   . rw [← hj,← h0];exact fun h => hnz (hinj h)
   . rw [← hj,← h1];exact fun h => hno (hinj h)
   . rw [← hj];exact fun h => hna (hinj h)
   . rw [← hj];exact fun h => hnb (hinj h)
   . intro x hx
     obtain ⟨y,hy,rfl⟩:=List.mem_map.1 hx
     rw [← hj];exact fun h => hnr y hy (hinj h)
 | @bAnd s a ta b tb r ka kb h1t h2t h3t h4t hnz hno hna hnb hnr _ ih =>
   have e1:(((meet a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)).map fun p => (e p.1,p.2))
       = (meet' (e a) (e b),if ta=3\/tb=3 then 1 else 0)::qk ka (e a,0) (qk kb (e b,0) (r.map fun p => (e p.1,p.2))):=by
     cases ka <;> cases kb <;> simp [qk,hm]
   rw [e1] at ih
   refine TagRun.bAnd ka kb h1t h2t h3t h4t ?_ ?_ ?_ ?_ ?_ ih
   . rw [← hm,← h0];exact fun h => hnz (hinj h)
   . rw [← hm,← h1];exact fun h => hno (hinj h)
   . rw [← hm];exact fun h => hna (hinj h)
   . rw [← hm];exact fun h => hnb (hinj h)
   . intro x hx
     obtain ⟨y,hy,rfl⟩:=List.mem_map.1 hx
     rw [← hm];exact fun h => hnr y hy (hinj h)
def v3 (n : ℕ) (gs:List Gate) (v:Fin n) (p : ℕ):List Stat × List Gate :=
 elim n (gs.take p) (wf n v,[])
lemma vb (n : ℕ) (gs:List Gate) (v:Fin n) (p : ℕ) (hp:p<=gs.length) :
   (v3 n gs v p).1.length=n+p:=by
 unfold v3
 rw [q50]
 simp [wf,List.length_take,Nat.min_eq_left hp]
lemma q30 (n : ℕ) (gs:List Gate) (v:Fin n) (p : ℕ) (g:Gate) (hg:gs[p]?=some g) :
   v3 n gs v (p+1)=qa n (v3 n gs v p) g:=by
 unfold v3
 have hlt:p < gs.length:=(List.getElem?_eq_some_iff.1 hg).1
 have hge:gs[p]=g:=(List.getElem?_eq_some_iff.1 hg).2
 rw [List.take_succ_eq_append_getElem hlt,hge,jz,k4]
 rfl
lemma zj (n : ℕ) (gs:List Gate) (v:Fin n) (p : ℕ) :
   elim n (gs.drop p) (v3 n gs v p)=elim n gs (wf n v,[]):=by
 unfold v3
 rw [← jz,List.take_append_drop]
def yf (n : ℕ) (gs:List Gate) (f:BFn n) (p a tg : ℕ):Prop :=
 match tg with
 | 0 => True
 | 1 => ∃ v:Fin n,
     (∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
     (v3 n gs v p).1.getD a (Sum.inl false)=Sum.inl false /\
     (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+1
 | 2 => ∃ v:Fin n,
     (∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
     (v3 n gs v p).1.getD a (Sum.inl false)=Sum.inl true /\
     (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+1
 | 3 => ∃ v:Fin n,
     (∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
     (v3 n gs v p).1.getD a (Sum.inl false)=Sum.inl false /\
     (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+2
 | _ => False
lemma q12 {n : ℕ} {gs:List Gate} {f:BFn n} {p a tg : ℕ}
   (h:yf n gs f p a tg):tg<=3:=by
 match tg with
 | 0 | 1 | 2 | 3 => omega
 | _+4 => exact False.elim h
lemma vv {n : ℕ} {gs:List Gate} {f:BFn n} {p a tg : ℕ} {g:Gate}
   (hg:gs[p]?=some g) (ha:a < n+p) (h:yf n gs f p a tg) :
   yf n gs f (p+1) a tg:=by
 have hlt:p < gs.length:=(List.getElem?_eq_some_iff.1 hg).1
 have hge:gs[p]=g:=(List.getElem?_eq_some_iff.1 hg).2
 have hdrop:gs.drop p=g::gs.drop (p+1):=by rw [List.drop_eq_getElem_cons hlt,hge]
 have step_aux:∀ v c B,
     (v3 n gs v p).1.getD a (Sum.inl false)=Sum.inl c ->
     (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+B ->
     (v3 n gs v (p+1)).1.getD a (Sum.inl false)=Sum.inl c /\
     (v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length <=
       (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B:=by
   intro v c B hget hbd
   have hsucc:=q30 n gs v p g hg
   have hfl:=vb n gs v p (by omega)
   constructor
   . rw [hsucc];simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hget
   . have heq:elim n (gs.drop (p+1)) (v3 n gs v (p+1))=elim n (gs.drop p) (v3 n gs v p):=by
       rw [zj,zj]
     have hlen2:(v3 n gs v (p+1)).2.length<=(v3 n gs v p).2.length+1:=by
       rw [hsucc];simp only [qa,lLA]
       have:=y2 (qg g.op (n+(v3 n gs v p).2.length)
         (g.inputs.map fun i => (v3 n gs v p).1.getD i (Sum.inl false))).1
       omega
     have hdl:(gs.drop p).length=(gs.drop (p+1)).length+1:=by rw [hdrop];simp
     rw [heq];omega
 match tg with
 | 0 => trivial
 | 1 => obtain ⟨v,hnc,hget,hbd⟩:=h;exact ⟨v,hnc,step_aux v false 1 hget hbd⟩
 | 2 => obtain ⟨v,hnc,hget,hbd⟩:=h;exact ⟨v,hnc,step_aux v true 1 hget hbd⟩
 | 3 => obtain ⟨v,hnc,hget,hbd⟩:=h;exact ⟨v,hnc,step_aux v false 2 hget hbd⟩
 | _+4 => exact False.elim h
lemma zr {n : ℕ} {gs:List Gate} {o p u : ℕ} {f:BFn n} {v:Fin n} {c:Bool}
   (hm:MinClean n f gs o) (hp:p<=gs.length)
   (hlive:u ∈ liveList gs n o p)
   (hnc:∃ x y,f (Function.update x v false)≠f (Function.update y v false))
   (hconst:(v3 n gs v p).1.getD u (Sum.inl false)=Sum.inl c) :
   ∃ g' ∈ gs.drop p,u ∈ g'.inputs:=by
 have ⟨hlt,hl⟩:=(qw gs n o p u).1 hlive
 rcases hl with rfl | ⟨q,hq,g',hg',hin,_⟩
 . exfalso
   have hfl:=vb n gs v p hp
   have heq:(elim n gs (wf n v,[])).1.getD u (Sum.inl false)=Sum.inl c:=by
     rw [← zj n gs v p,wy n u _ _ _ (by omega)];exact hconst
   have hinv:∀ x,Inv n (List.ofFn x) (q3 gs (List.ofFn (Function.update x v false))) (elim n gs (wf n v,[])) :=
     fun x => j7 n _ (by simp) gs _ _ (fun g hg => (ja hm.hcl g hg).1) (q139 n v x)
   obtain ⟨x,y,hne⟩:=hnc
   apply hne
   have e1:=((hinv x).2 u).2.trans (hm.hev _)
   have e2:=((hinv y).2 u).2.trans (hm.hev _)
   rw [heq] at e1 e2
   exact e1.symm.trans e2
 . have hqlt:q < gs.length:=(List.getElem?_eq_some_iff.1 hg').1
   have hqeq:gs[q]=g':=(List.getElem?_eq_some_iff.1 hg').2
   refine ⟨g',?_,hin⟩
   have:g'=(gs.drop p)[q - p]'(by simp;omega):=by
     rw [List.getElem_drop];simp [show p+(q - p)=q by omega,hqeq]
   rw [this]
   exact List.getElem_mem _
lemma q21 {n : ℕ} {gs:List Gate} {o p j : ℕ} {f:BFn n}
   (hm:MinClean n f gs o) (hp:p < gs.length)
   (hval:∀ x,val gs n (n+p) x=!(val gs n j x)) :
   ∀ g' ∈ gs.drop (p+1),¬ (j ∈ g'.inputs/\(n+p) ∈ g'.inputs):=by
 intro g' hg' ⟨hj,hnp⟩
 obtain ⟨r,hr,rfl⟩:=List.getElem_of_mem hg'
 have hrlt:p+1+r < gs.length:=by simp at hr;omega
 have hge:(gs.drop (p+1))[r]=gs[p+1+r]:=List.getElem_drop
 rw [hge] at hj hnp
 set q:=p+1+r with hq
 have hqg:gs[q]?=some gs[q]:=List.getElem?_eq_getElem hrlt
 have hcg:=hm.hcl q gs[q] hqg
 have hvg:=q103 n gs q gs[q] hqg (j2 hcg)
 have hne:j≠n+p:=by
   intro e;have h0:=hval (fun _ => false);rw [e] at h0
   cases hv:val gs n (n+p) (fun _ => false) <;> rw [hv] at h0 <;> cases h0
 rcases hcg with ⟨_,a,_,hin⟩ | ⟨hop,a,b,_,_,hin⟩
 . rw [hin] at hj hnp;simp at hj hnp;exact hne (hj.trans hnp.symm)
 . rw [hin] at hj hnp;simp at hj hnp
   rcases hop with hop | hop
   . apply hm.hncG q hrlt false
     funext x;rw [hvg x,hop,hin];simp only [lMC,List.map_nil,GateOp.eval]
     rcases hj with rfl | rfl <;> rcases hnp with h1 | h1
     . exact absurd h1.symm hne
     . rw [← h1,hval x];cases val gs n j x <;> rfl
     . rw [← h1,hval x];cases val gs n j x <;> rfl
     . exact absurd h1.symm hne
   . apply hm.hncG q hrlt true
     funext x;rw [hvg x,hop,hin];simp only [lMC,List.map_nil,GateOp.eval]
     rcases hj with rfl | rfl <;> rcases hnp with h1 | h1
     . exact absurd h1.symm hne
     . rw [← h1,hval x];cases val gs n j x <;> rfl
     . rw [← h1,hval x];cases val gs n j x <;> rfl
     . exact absurd h1.symm hne
lemma q22 {n : ℕ} {gs:List Gate} {o p j k : ℕ} {f:BFn n}
   (hm:MinClean n f gs o) (hp:p < gs.length) (hjlt:j < n+p)
   (hval:∀ x,val gs n (n+p) x=(val gs n j x&&val gs n k x)) :
   ∀ g' ∈ gs.drop (p+1),¬ (j ∈ g'.inputs/\(n+p) ∈ g'.inputs):=by
 intro g' hg' ⟨hj,hnp⟩
 obtain ⟨r,hr,rfl⟩:=List.getElem_of_mem hg'
 have hrlt:p+1+r < gs.length:=by simp at hr;omega
 have hge:(gs.drop (p+1))[r]=gs[p+1+r]:=List.getElem_drop
 rw [hge] at hj hnp
 set q:=p+1+r with hq
 have hqg:gs[q]?=some gs[q]:=List.getElem?_eq_getElem hrlt
 have hcg:=hm.hcl q gs[q] hqg
 have hvg:=q103 n gs q gs[q] hqg (j2 hcg)
 have hne:j≠n+p:=by omega
 rcases hcg with ⟨_,a,_,hin⟩ | ⟨hop,a,b,_,_,hin⟩
 . rw [hin] at hj hnp;simp at hj hnp;omega
 . rw [hin] at hj hnp;simp at hj hnp
   rcases hop with hop | hop
   . apply hm.hndup q hrlt (n+p) (by omega)
     funext x;rw [hvg x,hop,hin];simp only [lMC,List.map_nil,GateOp.eval]
     rcases hj with rfl | rfl <;> rcases hnp with h1 | h1
     . exact absurd h1.symm hne
     . rw [← h1,hval x];cases val gs n j x <;> cases val gs n k x <;> rfl
     . rw [← h1,hval x];cases val gs n j x <;> cases val gs n k x <;> rfl
     . exact absurd h1.symm hne
   . apply hm.hndup q hrlt j (by omega)
     funext x;rw [hvg x,hop,hin];simp only [lMC,List.map_nil,GateOp.eval]
     rcases hj with rfl | rfl <;> rcases hnp with h1 | h1
     . exact absurd h1.symm hne
     . rw [← h1,hval x];cases val gs n j x <;> cases val gs n k x <;> rfl
     . rw [← h1,hval x];cases val gs n j x <;> cases val gs n k x <;> rfl
     . exact absurd h1.symm hne
lemma q193 {n : ℕ} {gs:List Gate} (hcl:yq n gs) (p : ℕ) :
   ∀ g ∈ gs.drop p,NOk g:=fun g hg => ja hcl g (List.mem_of_mem_drop hg)
open Classical in
lemma q123 (n : ℕ) (f:BFn n) (gs:List Gate) (o : ℕ) (hm:MinClean n f gs o) :
   ∀ d p,p+d=gs.length ->
     ∀ tg : ℕ->ℕ,(∀ a ∈ liveList gs n o p,yf n gs f p a (tg a)) ->
       TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f d
         ((liveList gs n o p).map fun a => (val gs n a,tg a)):=by
 intro d
 induction d with
 | zero =>
   intro p hp tg _
   have hperm : [o].Perm (liveList gs n o p):=by
     refine (List.perm_ext_iff_of_nodup (List.nodup_singleton o) (vy _ _ _ _)).2 ?_
     intro a
     rw [qw,List.mem_singleton]
     constructor
     . rintro rfl;exact ⟨by have:=hm.ho;omega,Or.inl rfl⟩
     . rintro ⟨_,h | ⟨q,hq,g',hg',_,_⟩⟩
       . exact h
       . have:=(List.getElem?_eq_some_iff.1 hg').1;omega
   have hf:val gs n o=f:=funext hm.hev
   have h1:([(f,tg o)]).Perm ((liveList gs n o p).map fun a => (val gs n a,tg a)):=by
     rw [← hf];exact hperm.map (fun a => (val gs n a,tg a))
   exact TagRun.perm h1 (TagRun.done (tg o))
 | succ d ih =>
   intro p hp tg hok
   have hplt:p < gs.length:=by omega
   obtain ⟨g,hg⟩:∃ g,gs[p]?=some g:=⟨gs[p],List.getElem?_eq_getElem hplt⟩
   have hr:wn n gs o (n+p):=hm.hreach p hplt
   have hstep:=q73 n gs o hm.hcl p g hg hr
   have hin:∀ a ∈ g.inputs,a ∈ liveList gs n o p:=fun a ha =>
     (qw _ _ _ _ _).2 ⟨j2 (hm.hcl p g hg) a ha,Or.inr ⟨p,le_rfl,g,hg,ha,hr⟩⟩
   have hnew:∀ a ∈ liveList gs n o p,a≠n+p:=fun a ha =>
     Nat.ne_of_lt ((qw _ _ _ _ _).1 ha).1
   have hvg:=q103 n gs p g hg (j2 (hm.hcl p g hg))
   have hnd0:=vy gs n o p
   have hdrop:gs.drop p=g::gs.drop (p+1):=by
     rw [List.drop_eq_getElem_cons hplt];have hge:gs[p]=g:=(List.getElem?_eq_some_iff.1 hg).2;rw [hge]
   have hgn:NOk g:=q101 (hm.hcl p g hg)
   have hdrop_nok:=q193 hm.hcl (p+1)
   have hnz:val gs n (n+p)≠fun _ => false:=hm.hncG p hplt false
   have hno:val gs n (n+p)≠fun _ => true:=hm.hncG p hplt true
   have hnd:∀ a ∈ liveList gs n o p,val gs n a≠val gs n (n+p):=fun a ha e =>
     hm.hndup p hplt a ((qw _ _ _ _ _).1 ha).1 e.symm
   rcases hm.hcl p g hg with ⟨hop,j,hj,hinp⟩ | ⟨hop,j,k,hj,hk,hinp⟩
   ·
     have hjm:j ∈ liveList gs n o p:=hin j (by simp [hinp])
     have hval:val gs n (n+p)=invF (val gs n j):=by
       funext x;rw [hvg x,hop,hinp];simp [GateOp.eval]
     have hsave_not:∀ v c B,
         (∃ x y,f (Function.update x v false)≠f (Function.update y v false)) ->
         (v3 n gs v p).1.getD j (Sum.inl false)=Sum.inl c ->
         (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+B ->
         2<=B /\
         (v3 n gs v (p+1)).1.getD (n+p) (Sum.inl false)=Sum.inl (!c) /\
         (v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
           (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B /\
         (q11 n gs o (p+1) j->3<=B):=by
       intro v c B hncv hget hbd
       have hsucc:=q30 n gs v p g hg
       have hfl:=vb n gs v p (by omega)
       have hfl1:=vb n gs v (p+1) (by omega)
       have h0:(v3 n gs v (p+1)).2.length=(v3 n gs v p).2.length:=by
         rw [hsucc];exact vs n _ g hgn j (by simp [hinp]) c hget
       have hout_c:(v3 n gs v (p+1)).1.getD (n+p) (Sum.inl false)=Sum.inl (!c):=by
         rw [hsucc];simp only [qa]
         rw [z2 _ _ _ _ hfl,hop,hinp]
         simp only [lMC,List.map_nil,hget,qg,wr]
       have heq_e:elim n (gs.drop (p+1)) (v3 n gs v (p+1))=elim n (gs.drop p) (v3 n gs v p):=by
         rw [zj,zj]
       have hdl:(gs.drop p).length=(gs.drop (p+1)).length+1:=by rw [hdrop];simp
       have hbd1:(v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
           (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B:=by
         rw [heq_e,h0];omega
       have hnp_live:n+p ∈ liveList gs n o (p+1):=(hstep (n+p)).2 (Or.inl rfl)
       have hread_np:=zr hm (by omega) hnp_live hncv hout_c
       have hkill1:=zt n (n+p) (gs.drop (p+1)) (v3 n gs v (p+1)) hdrop_nok
         (by omega) ⟨!c,hout_c⟩ hread_np
       refine ⟨by omega,hout_c,hbd1,?_⟩
       intro hjlive
       have hj_live1:j ∈ liveList gs n o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,hjlive⟩
       have hj_c1:(v3 n gs v (p+1)).1.getD j (Sum.inl false)=Sum.inl c:=by
         rw [hsucc];simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hget
       have hread_j:=zr hm (by omega) hj_live1 hncv hj_c1
       have hdisj:=q21 hm hplt (fun x => congrFun hval x)
       have hkill2:=k3 n j (n+p) (gs.drop (p+1)) (v3 n gs v (p+1))
         hdrop_nok (by omega) (by omega) ⟨c,hj_c1⟩ ⟨!c,hout_c⟩ hread_j hread_np hdisj
       omega
     have ht1:tg j≠1:=by
       intro h1;have hw:=hok j hjm;rw [h1] at hw
       obtain ⟨v,hncv,hget,hbd⟩:=hw
       have:=(hsave_not v false 1 hncv hget hbd).1;omega
     have ht2:tg j≠2:=by
       intro h2;have hw:=hok j hjm;rw [h2] at hw
       obtain ⟨v,hncv,hget,hbd⟩:=hw
       have:=(hsave_not v true 1 hncv hget hbd).1;omega
     have ht3:tg j=3->decide (q11 n gs o (p+1) j)=false:=by
       intro h3;simp only [decide_eq_false_iff_not];intro hjlive
       have hw:=hok j hjm;rw [h3] at hw
       obtain ⟨v,hncv,hget,hbd⟩:=hw
       have:=(hsave_not v false 2 hncv hget hbd).2.2.2 hjlive;omega
     set tg' : ℕ->ℕ:=fun a =>
       if a=n+p then (if tg j=3 then 2 else 0)
       else if a=j then 0
       else tg a
     have hok':∀ a ∈ liveList gs n o (p+1),yf n gs f (p+1) a (tg' a):=by
       intro a ha
       simp only [tg']
       by_cases hanp:a=n+p
       . subst hanp;simp only [↓reduceIte]
         by_cases h3:tg j=3
         . simp only [h3,↓reduceIte]
           have hw:=hok j hjm;rw [h3] at hw
           obtain ⟨v,hncv,hget,hbd⟩:=hw
           obtain ⟨_,hout_c,hbd1,_⟩:=hsave_not v false 2 hncv hget hbd
           exact ⟨v,hncv,hout_c,by omega⟩
         . simp only [h3,↓reduceIte];trivial
       . simp only [hanp,↓reduceIte]
         by_cases haj:a=j
         . simp only [haj,↓reduceIte];trivial
         . simp only [haj,↓reduceIte]
           have ha0:a ∈ liveList gs n o p:=by
             rcases (hstep a).1 ha with rfl | ⟨h1,_⟩
             . exact absurd rfl hanp
             . exact h1
           exact vv hg ((qw _ _ _ _ _).1 ha0).1 (hok a ha0)
     have IH:=ih (p+1) (by omega) tg' hok'
     have hp1:(liveList gs n o p).Perm (j::(liveList gs n o p).erase j):=List.perm_cons_erase hjm
     have hnr:((liveList gs n o p).erase j).Nodup:=hnd0.erase j
     have hp2:(liveList gs n o (p+1)).Perm
         ((n+p)::qk (decide (q11 n gs o (p+1) j)) j ((liveList gs n o p).erase j)):=by
       refine (List.perm_ext_iff_of_nodup (vy _ _ _ _) ?_).2 ?_
       . refine List.nodup_cons.2 ⟨?_,q36 _ _ _ hnr (by simp [hnd0.mem_erase_iff])⟩
         rw [wa];rintro (⟨_,h⟩ | h)
         . exact hnew j hjm h.symm
         . exact hnew _ (List.mem_of_mem_erase h) rfl
       . intro a
         rw [hstep a,lMM,wa,hnd0.mem_erase_iff,hinp,List.mem_singleton]
         simp only [decide_eq_true_eq]
         constructor
         . rintro (h | ⟨h1,h2⟩)
           . exact Or.inl h
           . by_cases haj:a=j
             . exact Or.inr (Or.inl ⟨haj ▸ h2 haj,haj⟩)
             . exact Or.inr (Or.inr ⟨haj,h1⟩)
         . rintro (h | ⟨h1,rfl⟩ | ⟨h1,h2⟩)
           . exact Or.inl h
           . exact Or.inr ⟨hjm,fun _ => h1⟩
           . exact Or.inr ⟨h2,fun h => absurd h h1⟩
     have hmap_rest:((liveList gs n o p).erase j).map (fun a => (val gs n a,tg' a)) =
         ((liveList gs n o p).erase j).map (fun a => (val gs n a,tg a)):=by
       apply List.map_congr_left
       intro a ha
       have h1:a≠j:=(hnd0.mem_erase_iff.1 ha).1
       have h2:a≠n+p:=hnew a (List.mem_of_mem_erase ha)
       simp [tg',h1,h2]
     have hmap_kept:(qk (decide (q11 n gs o (p+1) j)) j ((liveList gs n o p).erase j)).map (fun a => (val gs n a,tg' a)) =
         qk (decide (q11 n gs o (p+1) j)) (val gs n j,0) (((liveList gs n o p).erase j).map fun a => (val gs n a,tg a)):=by
       rw [wd,hmap_rest]
       have hjne:j≠n+p:=by omega
       simp [tg',hjne]
     have IH':=TagRun.perm (hp2.map fun a => (val gs n a,tg' a)) IH
     rw [lMC,hmap_kept,hval] at IH'
     have htgnp:tg' (n+p)=(if tg j=3 then 2 else 0):=by simp [tg']
     rw [htgnp] at IH'
     refine TagRun.perm (hp1.map fun a => (val gs n a,tg a)).symm ?_
     refine TagRun.uNot (decide (q11 n gs o (p+1) j)) ht1 ht2 ht3
       (hval ▸ hnz) (hval ▸ hno) (fun e => hnd j hjm (hval ▸ e.symm)) ?_ IH'
     intro x hx
     obtain ⟨a,ha,rfl⟩:=List.mem_map.1 hx
     exact hval ▸ hnd a (List.mem_of_mem_erase ha)
   ·
     have hjk:j≠k:=by
       intro e;subst e
       apply hm.hndup p hplt j hj
       funext x;rw [hvg x,hinp]
       rcases hop with hop | hop <;> rw [hop] <;> simp [GateOp.eval]
     have hjm:=hin j (by simp [hinp])
     have hkm:=hin k (by simp [hinp])
     have hke:k ∈ (liveList gs n o p).erase j:=(hnd0.mem_erase_iff).2 ⟨fun e => hjk e.symm,hkm⟩
     have hnr:((liveList gs n o p).erase j).Nodup:=hnd0.erase j
     have hnr2:(((liveList gs n o p).erase j).erase k).Nodup:=hnr.erase k
     have hp1:(liveList gs n o p).Perm (j::k::((liveList gs n o p).erase j).erase k) :=
       (List.perm_cons_erase hjm).trans ((List.perm_cons_erase hke).cons j)
     have hmr:∀ a,a ∈ ((liveList gs n o p).erase j).erase k ↔ a≠k/\a≠j/\a ∈ liveList gs n o p:=by
       intro a;rw [hnr.mem_erase_iff,hnd0.mem_erase_iff]
     have hp2:(liveList gs n o (p+1)).Perm
         ((n+p)::qk (decide (q11 n gs o (p+1) j)) j
           (qk (decide (q11 n gs o (p+1) k)) k
             (((liveList gs n o p).erase j).erase k))):=by
       refine (List.perm_ext_iff_of_nodup (vy _ _ _ _) ?_).2 ?_
       . refine List.nodup_cons.2 ⟨?_,q36 _ _ _ (q36 _ _ _ hnr2 ?_) ?_⟩
         . rw [wa,wa]
           rintro (⟨_,h⟩ | ⟨_,h⟩ | h)
           . exact hnew j hjm h.symm
           . exact hnew k hkm h.symm
           . exact hnew _ ((hmr _).1 h).2.2 rfl
         . rw [hmr];simp
         . rw [wa,hmr]
           rintro (⟨_,h⟩ | h)
           . exact hjk h
           . exact h.2.1 rfl
       . intro a
         rw [hstep a,lMM,wa,wa,hmr a]
         simp only [decide_eq_true_eq,hinp,lMM,List.not_mem_nil,or_false]
         constructor
         . rintro (h | ⟨h1,h2⟩)
           . exact Or.inl h
           . by_cases haj:a=j
             . exact Or.inr (Or.inl ⟨haj ▸ h2 (Or.inl haj),haj⟩)
             . by_cases hak:a=k
               . exact Or.inr (Or.inr (Or.inl ⟨hak ▸ h2 (Or.inr hak),hak⟩))
               . exact Or.inr (Or.inr (Or.inr ⟨hak,haj,h1⟩))
         . rintro (h | ⟨h1,rfl⟩ | ⟨h1,rfl⟩ | ⟨h1,h2,h3⟩)
           . exact Or.inl h
           . exact Or.inr ⟨hjm,fun _ => h1⟩
           . exact Or.inr ⟨hkm,fun _ => h1⟩
           . exact Or.inr ⟨h3,fun h => by rcases h with h | h <;> contradiction⟩
     rcases hop with hop | hop
     ·
       have hval:val gs n (n+p)=meetF (val gs n j) (val gs n k):=by
         funext x;rw [hvg x,hop,hinp];simp [GateOp.eval]
       have hand_const:∀ (u w_other : ℕ) (hu:u ∈ g.inputs) (hult:u < n+p)
           (hval_u:∀ x,val gs n (n+p) x=(val gs n u x&&val gs n w_other x))
           (v:Fin n) (c:Bool) (B : ℕ),
           (∃ x y,f (Function.update x v false)≠f (Function.update y v false)) ->
           (v3 n gs v p).1.getD u (Sum.inl false)=Sum.inl c ->
           (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+B ->
           (v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
             (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B /\
           (c=false ->
             2<=B /\
             (v3 n gs v (p+1)).1.getD (n+p) (Sum.inl false)=Sum.inl false /\
             (q11 n gs o (p+1) u->3<=B)) /\
           (c=true->q11 n gs o (p+1) u->2<=B):=by
         intro u wo hu hult hvalu v c B hncv hget hbd
         have hsucc:=q30 n gs v p g hg
         have hfl:=vb n gs v p (by omega)
         have hfl1:=vb n gs v (p+1) (by omega)
         have h0:(v3 n gs v (p+1)).2.length=(v3 n gs v p).2.length:=by
           rw [hsucc];exact vs n _ g hgn u hu c hget
         have heq_e:elim n (gs.drop (p+1)) (v3 n gs v (p+1))=elim n (gs.drop p) (v3 n gs v p):=by
           rw [zj,zj]
         have hdl:(gs.drop p).length=(gs.drop (p+1)).length+1:=by rw [hdrop];simp
         have hbd1:(v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
             (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B:=by
           rw [heq_e,h0];omega
         have hu_c1:(v3 n gs v (p+1)).1.getD u (Sum.inl false)=Sum.inl c:=by
           rw [hsucc];simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hget
         refine ⟨hbd1,?_,?_⟩
         . intro hcf;subst hcf
           have hout_f:(v3 n gs v (p+1)).1.getD (n+p) (Sum.inl false)=Sum.inl false:=by
             rw [hsucc];simp only [qa];rw [z2 _ _ _ _ hfl,hop,hinp]
             rw [hinp] at hu;simp only [lMM,List.not_mem_nil,or_false] at hu
             rcases hu with rfl | rfl
             . simp only [lMC,List.map_nil,hget,qg]
               cases (v3 n gs v p).1.getD k (Sum.inl false) <;> simp [ko]
             . simp only [lMC,List.map_nil,hget,qg]
               cases (v3 n gs v p).1.getD j (Sum.inl false) <;> simp [ko]
           have hnp_live:n+p ∈ liveList gs n o (p+1):=(hstep (n+p)).2 (Or.inl rfl)
           have hread_np:=zr hm (by omega) hnp_live hncv hout_f
           have hkill1:=zt n (n+p) (gs.drop (p+1)) (v3 n gs v (p+1)) hdrop_nok
             (by omega) ⟨false,hout_f⟩ hread_np
           refine ⟨by omega,hout_f,?_⟩
           intro hulive
           have hu_live1:u ∈ liveList gs n o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,hulive⟩
           have hread_u:=zr hm (by omega) hu_live1 hncv hu_c1
           have hdisj:=q22 hm hplt hult hvalu
           have hkill2:=k3 n u (n+p) (gs.drop (p+1)) (v3 n gs v (p+1))
             hdrop_nok (by omega) (by omega) ⟨false,hu_c1⟩ ⟨false,hout_f⟩ hread_u hread_np hdisj
           omega
         . intro hct hulive;subst hct
           have hu_live1:u ∈ liveList gs n o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,hulive⟩
           have hread_u:=zr hm (by omega) hu_live1 hncv hu_c1
           have hkill1:=zt n u (gs.drop (p+1)) (v3 n gs v (p+1)) hdrop_nok
             (by omega) ⟨true,hu_c1⟩ hread_u
           omega
       have hval_j:∀ x,val gs n (n+p) x=(val gs n j x&&val gs n k x):=fun x => congrFun hval x
       have hval_k:∀ x,val gs n (n+p) x=(val gs n k x&&val gs n j x):=fun x => by
         rw [hval_j x,Bool.and_comm]
       have hta1:tg j≠1:=by
         intro h1;have hw:=hok j hjm;rw [h1] at hw
         obtain ⟨v,hncv,hget,hbd⟩:=hw
         have:=(hand_const j k (by simp [hinp]) hj hval_j v false 1 hncv hget hbd).2.1 rfl
         omega
       have htb1:tg k≠1:=by
         intro h1;have hw:=hok k hkm;rw [h1] at hw
         obtain ⟨v,hncv,hget,hbd⟩:=hw
         have:=(hand_const k j (by simp [hinp]) hk hval_k v false 1 hncv hget hbd).2.1 rfl
         omega
       have hta_save:tg j=1\/tg j=2\/tg j=3->decide (q11 n gs o (p+1) j)=false:=by
         intro h123;simp only [decide_eq_false_iff_not];intro hjlive
         rcases h123 with h1 | h2 | h3
         . exact hta1 h1
         . have hw:=hok j hjm;rw [h2] at hw
           obtain ⟨v,hncv,hget,hbd⟩:=hw
           have:=(hand_const j k (by simp [hinp]) hj hval_j v true 1 hncv hget hbd).2.2 rfl hjlive;omega
         . have hw:=hok j hjm;rw [h3] at hw
           obtain ⟨v,hncv,hget,hbd⟩:=hw
           have:=((hand_const j k (by simp [hinp]) hj hval_j v false 2 hncv hget hbd).2.1 rfl).2.2 hjlive;omega
       have htb_save:tg k=1\/tg k=2\/tg k=3->decide (q11 n gs o (p+1) k)=false:=by
         intro h123;simp only [decide_eq_false_iff_not];intro hklive
         rcases h123 with h1 | h2 | h3
         . exact htb1 h1
         . have hw:=hok k hkm;rw [h2] at hw
           obtain ⟨v,hncv,hget,hbd⟩:=hw
           have:=(hand_const k j (by simp [hinp]) hk hval_k v true 1 hncv hget hbd).2.2 rfl hklive;omega
         . have hw:=hok k hkm;rw [h3] at hw
           obtain ⟨v,hncv,hget,hbd⟩:=hw
           have:=((hand_const k j (by simp [hinp]) hk hval_k v false 2 hncv hget hbd).2.1 rfl).2.2 hklive;omega
       set tg' : ℕ->ℕ:=fun a =>
         if a=n+p then (if tg j=3\/tg k=3 then 1 else 0)
         else if a=j\/a=k then 0
         else tg a
       have hok':∀ a ∈ liveList gs n o (p+1),yf n gs f (p+1) a (tg' a):=by
         intro a ha
         simp only [tg']
         by_cases hanp:a=n+p
         . subst hanp;simp only [↓reduceIte]
           by_cases h3:tg j=3\/tg k=3
           . simp only [h3,↓reduceIte]
             rcases h3 with hj3 | hk3
             . have hw:=hok j hjm;rw [hj3] at hw
               obtain ⟨v,hncv,hget,hbd⟩:=hw
               have hh:=hand_const j k (by simp [hinp]) hj hval_j v false 2 hncv hget hbd
               exact ⟨v,hncv,(hh.2.1 rfl).2.1,by omega⟩
             . have hw:=hok k hkm;rw [hk3] at hw
               obtain ⟨v,hncv,hget,hbd⟩:=hw
               have hh:=hand_const k j (by simp [hinp]) hk hval_k v false 2 hncv hget hbd
               exact ⟨v,hncv,(hh.2.1 rfl).2.1,by omega⟩
           . simp only [h3,↓reduceIte];trivial
         . simp only [hanp,↓reduceIte]
           by_cases hajk:a=j\/a=k
           . simp only [hajk,↓reduceIte];trivial
           . simp only [hajk,↓reduceIte]
             have ha0:a ∈ liveList gs n o p:=by
               rcases (hstep a).1 ha with rfl | ⟨h1,_⟩
               . exact absurd rfl hanp
               . exact h1
             exact vv hg ((qw _ _ _ _ _).1 ha0).1 (hok a ha0)
       have IH:=ih (p+1) (by omega) tg' hok'
       have hmap_rest:(((liveList gs n o p).erase j).erase k).map (fun a => (val gs n a,tg' a)) =
           (((liveList gs n o p).erase j).erase k).map (fun a => (val gs n a,tg a)):=by
         apply List.map_congr_left
         intro a ha
         have ⟨h1,h2,h3⟩:=(hmr a).1 ha
         have h4:a≠n+p:=hnew a h3
         simp [tg',h1,h2,h4]
       have hmap_kept:(qk (decide (q11 n gs o (p+1) j)) j
           (qk (decide (q11 n gs o (p+1) k)) k (((liveList gs n o p).erase j).erase k))).map
             (fun a => (val gs n a,tg' a)) =
           qk (decide (q11 n gs o (p+1) j)) (val gs n j,0)
             (qk (decide (q11 n gs o (p+1) k)) (val gs n k,0)
               ((((liveList gs n o p).erase j).erase k).map fun a => (val gs n a,tg a))):=by
         rw [wd,wd,hmap_rest]
         have hjne:j≠n+p:=by omega
         have hkne:k≠n+p:=by omega
         simp [tg',hjne,hkne]
       have IH':=TagRun.perm (hp2.map fun a => (val gs n a,tg' a)) IH
       rw [lMC,hmap_kept,hval] at IH'
       have htgnp:tg' (n+p)=(if tg j=3\/tg k=3 then 1 else 0):=by simp [tg']
       rw [htgnp] at IH'
       have hjle3:=q12 (hok j hjm)
       have hkle3:=q12 (hok k hkm)
       refine TagRun.perm (hp1.map fun a => (val gs n a,tg a)).symm ?_
       refine TagRun.bAnd (decide (q11 n gs o (p+1) j)) (decide (q11 n gs o (p+1) k))
         hta1 htb1 (fun h => hta_save (by omega)) (fun h => htb_save (by omega))
         (hval ▸ hnz) (hval ▸ hno)
         (fun e => hnd j hjm (hval ▸ e.symm)) (fun e => hnd k hkm (hval ▸ e.symm)) ?_ IH'
       intro x hx
       obtain ⟨a,ha,rfl⟩:=List.mem_map.1 hx
       exact hval ▸ hnd a ((hmr a).1 ha).2.2
     ·
       have hval:val gs n (n+p)=joinF (val gs n j) (val gs n k):=by
         funext x;rw [hvg x,hop,hinp];simp [GateOp.eval]
       have hor_const:∀ (u : ℕ) (hu:u ∈ g.inputs) (hult:u < n+p)
           (v:Fin n) (c:Bool) (B : ℕ),
           (∃ x y,f (Function.update x v false)≠f (Function.update y v false)) ->
           (v3 n gs v p).1.getD u (Sum.inl false)=Sum.inl c ->
           (v3 n gs v p).2.length+(gs.drop p).length<=(elim n (gs.drop p) (v3 n gs v p)).2.length+B ->
           (v3 n gs v (p+1)).1.getD u (Sum.inl false)=Sum.inl c /\
           (v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
             (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B /\
           (c=true->2<=B) /\
           (c=false->q11 n gs o (p+1) u->2<=B):=by
         intro u hu hult v c B hncv hget hbd
         have hsucc:=q30 n gs v p g hg
         have hfl:=vb n gs v p (by omega)
         have hfl1:=vb n gs v (p+1) (by omega)
         have h0:(v3 n gs v (p+1)).2.length=(v3 n gs v p).2.length:=by
           rw [hsucc];exact vs n _ g hgn u hu c hget
         have heq_e:elim n (gs.drop (p+1)) (v3 n gs v (p+1))=elim n (gs.drop p) (v3 n gs v p):=by
           rw [zj,zj]
         have hdl:(gs.drop p).length=(gs.drop (p+1)).length+1:=by rw [hdrop];simp
         have hbd1:(v3 n gs v (p+1)).2.length+(gs.drop (p+1)).length+1 <=
             (elim n (gs.drop (p+1)) (v3 n gs v (p+1))).2.length+B:=by
           rw [heq_e,h0];omega
         have hu_c1:(v3 n gs v (p+1)).1.getD u (Sum.inl false)=Sum.inl c:=by
           rw [hsucc];simp only [qa];rw [q8 _ _ _ _ (by omega)];exact hget
         refine ⟨hu_c1,hbd1,?_,?_⟩
         . intro hct;subst hct
           have hout_t:(v3 n gs v (p+1)).1.getD (n+p) (Sum.inl false)=Sum.inl true:=by
             rw [hsucc];simp only [qa];rw [z2 _ _ _ _ hfl,hop,hinp]
             rw [hinp] at hu;simp only [lMM,List.not_mem_nil,or_false] at hu
             rcases hu with rfl | rfl
             . simp only [lMC,List.map_nil,hget,qg]
               cases (v3 n gs v p).1.getD k (Sum.inl false) <;> simp [ji]
             . simp only [lMC,List.map_nil,hget,qg]
               cases (v3 n gs v p).1.getD j (Sum.inl false) <;> simp [ji]
           have hnp_live:n+p ∈ liveList gs n o (p+1):=(hstep (n+p)).2 (Or.inl rfl)
           have hread_np:=zr hm (by omega) hnp_live hncv hout_t
           have hkill1:=zt n (n+p) (gs.drop (p+1)) (v3 n gs v (p+1)) hdrop_nok
             (by omega) ⟨true,hout_t⟩ hread_np
           omega
         . intro hcf hulive;subst hcf
           have hu_live1:u ∈ liveList gs n o (p+1):=(qw _ _ _ _ _).2 ⟨by omega,hulive⟩
           have hread_u:=zr hm (by omega) hu_live1 hncv hu_c1
           have hkill1:=zt n u (gs.drop (p+1)) (v3 n gs v (p+1)) hdrop_nok
             (by omega) ⟨false,hu_c1⟩ hread_u
           omega
       have hta2:tg j≠2:=by
         intro h2;have hw:=hok j hjm;rw [h2] at hw
         obtain ⟨v,hncv,hget,hbd⟩:=hw
         have:=(hor_const j (by simp [hinp]) hj v true 1 hncv hget hbd).2.2.1 rfl;omega
       have htb2:tg k≠2:=by
         intro h2;have hw:=hok k hkm;rw [h2] at hw
         obtain ⟨v,hncv,hget,hbd⟩:=hw
         have:=(hor_const k (by simp [hinp]) hk v true 1 hncv hget hbd).2.2.1 rfl;omega
       have hta1:tg j=1->decide (q11 n gs o (p+1) j)=false:=by
         intro h1;simp only [decide_eq_false_iff_not];intro hjlive
         have hw:=hok j hjm;rw [h1] at hw
         obtain ⟨v,hncv,hget,hbd⟩:=hw
         have:=(hor_const j (by simp [hinp]) hj v false 1 hncv hget hbd).2.2.2 rfl hjlive;omega
       have htb1:tg k=1->decide (q11 n gs o (p+1) k)=false:=by
         intro h1;simp only [decide_eq_false_iff_not];intro hklive
         have hw:=hok k hkm;rw [h1] at hw
         obtain ⟨v,hncv,hget,hbd⟩:=hw
         have:=(hor_const k (by simp [hinp]) hk v false 1 hncv hget hbd).2.2.2 rfl hklive;omega
       set tg' : ℕ->ℕ:=fun a =>
         if a=n+p then 0
         else if a=j then (if tg j=3 then 1 else 0)
         else if a=k then (if tg k=3 then 1 else 0)
         else tg a
       have hok':∀ a ∈ liveList gs n o (p+1),yf n gs f (p+1) a (tg' a):=by
         intro a ha
         simp only [tg']
         by_cases hanp:a=n+p
         . simp [hanp,yf]
         . simp only [hanp,↓reduceIte]
           by_cases haj:a=j
           . rw [haj];simp only [↓reduceIte]
             by_cases hj3:tg j=3
             . simp only [hj3,↓reduceIte]
               have hw:=hok j hjm;rw [hj3] at hw
               obtain ⟨v,hncv,hget,hbd⟩:=hw
               have hh:=hor_const j (by simp [hinp]) hj v false 2 hncv hget hbd
               exact ⟨v,hncv,hh.1,by omega⟩
             . simp only [hj3,↓reduceIte];trivial
           . simp only [haj,↓reduceIte]
             by_cases hak:a=k
             . rw [hak];simp only [↓reduceIte]
               by_cases hk3:tg k=3
               . simp only [hk3,↓reduceIte]
                 have hw:=hok k hkm;rw [hk3] at hw
                 obtain ⟨v,hncv,hget,hbd⟩:=hw
                 have hh:=hor_const k (by simp [hinp]) hk v false 2 hncv hget hbd
                 exact ⟨v,hncv,hh.1,by omega⟩
               . simp only [hk3,↓reduceIte];trivial
             . simp only [hak,↓reduceIte]
               have ha0:a ∈ liveList gs n o p:=by
                 rcases (hstep a).1 ha with rfl | ⟨h1,_⟩
                 . exact absurd rfl hanp
                 . exact h1
               exact vv hg ((qw _ _ _ _ _).1 ha0).1 (hok a ha0)
       have IH:=ih (p+1) (by omega) tg' hok'
       have hmap_rest:(((liveList gs n o p).erase j).erase k).map (fun a => (val gs n a,tg' a)) =
           (((liveList gs n o p).erase j).erase k).map (fun a => (val gs n a,tg a)):=by
         apply List.map_congr_left
         intro a ha
         have ⟨h1,h2,h3⟩:=(hmr a).1 ha
         have h4:a≠n+p:=hnew a h3
         simp [tg',h1,h2,h4]
       have hmap_kept:(qk (decide (q11 n gs o (p+1) j)) j
           (qk (decide (q11 n gs o (p+1) k)) k (((liveList gs n o p).erase j).erase k))).map
             (fun a => (val gs n a,tg' a)) =
           qk (decide (q11 n gs o (p+1) j)) (val gs n j,if tg j=3 then 1 else 0)
             (qk (decide (q11 n gs o (p+1) k)) (val gs n k,if tg k=3 then 1 else 0)
               ((((liveList gs n o p).erase j).erase k).map fun a => (val gs n a,tg a))):=by
         rw [wd,wd,hmap_rest]
         have hjne:j≠n+p:=by omega
         have hkne:k≠n+p:=by omega
         have hkj:k≠j:=fun e => hjk e.symm
         simp [tg',hjne,hkne,hkj]
       have IH':=TagRun.perm (hp2.map fun a => (val gs n a,tg' a)) IH
       rw [lMC,hmap_kept,hval] at IH'
       have htgnp:tg' (n+p)=0:=by simp [tg']
       rw [htgnp] at IH'
       refine TagRun.perm (hp1.map fun a => (val gs n a,tg a)).symm ?_
       refine TagRun.bOr (decide (q11 n gs o (p+1) j)) (decide (q11 n gs o (p+1) k))
         hta2 htb2 hta1 htb1
         (hval ▸ hnz) (hval ▸ hno)
         (fun e => hnd j hjm (hval ▸ e.symm)) (fun e => hnd k hkm (hval ▸ e.symm)) ?_ IH'
       intro x hx
       obtain ⟨a,ha,rfl⟩:=List.mem_map.1 hx
       exact hval ▸ hnd a ((hmr a).1 ha).2.2
lemma q133 {n : ℕ} {gs:List Gate} {o : ℕ} {f:BFn n}
   (hev:∀ x,val gs n o x=f x) (v:Fin n)
   (hdep:∃ x:Fin n->Bool,f (Function.update x v (!x v))≠f x) :
   (v : ℕ) ∈ liveList gs n o 0:=by
 rw [qw]
 refine ⟨by omega,?_⟩
 by_contra hnl
 have hnr : ¬ wn n gs o (v : ℕ):=by
   intro hr
   rcases q66 hr with heq | ⟨q,g,hg,hin,hrq⟩
   . exact hnl (Or.inl heq)
   . exact hnl (Or.inr ⟨q,nZL q,g,hg,hin,hrq⟩)
 obtain ⟨x,hx⟩:=hdep
 apply hx
 rw [← hev,← hev]
 have hagree:∀ (p : ℕ),∀ i < n+p,wn n gs o i ->
     (q3 (gs.take p) (List.ofFn (Function.update x v (!x v)))).getD i false =
     (q3 (gs.take p) (List.ofFn x)).getD i false:=by
   intro p
   induction p with
   | zero =>
     intro i hi hr
     simp only [List.take_zero,q3,List.foldl_nil]
     have hlt:i < n:=by omega
     have hne:(⟨i,hlt⟩:Fin n)≠v:=fun e => hnr (by simpa [← e] using hr)
     simp [hlt,fUN hne]
   | succ p ih =>
     intro i hi hr
     by_cases hp:p < gs.length
     . have htake:gs.take (p+1)=gs.take p++[gs[p]]:=List.take_succ_eq_append_getElem hp
       rw [htake,zd,zd]
       have hlen1:(q3 (gs.take p) (List.ofFn (Function.update x v (!x v)))).length=n+p:=by
         rw [qu];simp [List.length_take,Nat.min_eq_left (by omega:p<=gs.length)]
       have hlen2:(q3 (gs.take p) (List.ofFn x)).length=n+p:=by
         rw [qu];simp [List.length_take,Nat.min_eq_left (by omega:p<=gs.length)]
       by_cases hip:i=n+p
       . subst hip
         show (q3 (gs.take p) _++[_]).getD (n+p) false=(q3 (gs.take p) _++[_]).getD (n+p) false
         rw [z2 _ _ _ _ hlen1,z2 _ _ _ _ hlen2]
         congr 1
         apply List.map_congr_left
         intro a ha
         have hra:wn n gs o a:=q33 (List.getElem?_eq_getElem hp) hr ha
         by_cases halt:a < n+p
         . exact ih a halt hra
         . rw [lGD _ _ (by omega),lGD _ _ (by omega)]
       . show (q3 (gs.take p) _++[_]).getD i false=(q3 (gs.take p) _++[_]).getD i false
         rw [q8 _ _ _ _ (by omega),q8 _ _ _ _ (by omega)]
         exact ih i (by omega) hr
     . have htake:gs.take (p+1)=gs.take p:=by
         rw [List.take_of_length_le (by omega),List.take_of_length_le (by omega)]
       rw [htake]
       by_cases hlt:i < n+p
       . exact ih i hlt hr
       . have hl1:(q3 (gs.take p) (List.ofFn (Function.update x v (!x v)))).length=n+gs.length:=by
           rw [qu,List.take_of_length_le (by omega)];simp
         have hl2:(q3 (gs.take p) (List.ofFn x)).length=n+gs.length:=by
           rw [qu,List.take_of_length_le (by omega)];simp
         rw [lGD _ _ (by omega),lGD _ _ (by omega)]
 have ho_lt:o < n+gs.length:=by
   by_contra hge
   have hfalse:∀ y:Fin n->Bool,val gs n o y=false:=fun y =>
     lGD _ _ (by rw [qu];simp;omega)
   exact hx (by rw [← hev,← hev,hfalse,hfalse])
 have h:=hagree gs.length o ho_lt (q34 n gs o)
 rw [List.take_length] at h
 exact h
open Classical in
lemma q88 {n : ℕ} (f:BFn n) (cap : ℕ) (initTags:Fin n->ℕ)
   (hnc:∃ y y':Fin n->Bool,f y≠f y')
   (hdep:∀ v:Fin n,∃ x:Fin n->Bool,f (Function.update x v (!x v))≠f x)
   (htag:∀ v:Fin n,initTags v=0 \/
     (initTags v=1/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 1<=s') \/
     (initTags v=3/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 2<=s'))
   (s : ℕ) (hs:s<=cap) (hc:HasCircuitSize n f s) :
   ∃ s',s'<=cap /\
     TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s'
       (List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)):=by
 obtain ⟨gs,o,hm,hlen⟩:=q56 n f s hnc hc
 have hlive0:liveList gs n o 0=List.range n:=by
   have hsub:=(List.filter_sublist (l:=List.range (n+0)) (p:=fun a => decide (q11 n gs o 0 a)))
   simp only [nAZ] at hsub
   refine List.Sublist.eq_of_length hsub ?_
   have hperm:(List.range n).Perm (liveList gs n o 0):=by
     refine (List.perm_ext_iff_of_nodup List.nodup_range (vy gs n o 0)).2 ?_
     intro a
     rw [List.mem_range]
     constructor
     . intro ha;exact q133 hm.hev ⟨a,ha⟩ (hdep ⟨a,ha⟩)
     . intro ha;exact by simpa using ((qw gs n o 0 a).1 ha).1
   exact hperm.length_eq.symm
 set tg : ℕ->ℕ:=fun a => if h:a < n then initTags ⟨a,h⟩ else 0
 have hok0:∀ a ∈ liveList gs n o 0,yf n gs f 0 a (tg a):=by
   intro a ha
   rw [hlive0,List.mem_range] at ha
   have hta:tg a=initTags ⟨a,ha⟩:=by simp [tg,ha]
   rw [hta]
   rcases htag ⟨a,ha⟩ with h0 | ⟨h1,hnc0,hlb⟩ | ⟨h3,hnc0,hlb⟩
   . rw [h0];trivial
   . rw [h1]
     have hbd:=(wz n f gs o ⟨a,ha⟩ (cap - 1) hm.hcl hm.hev hnc0 hlb).2
     refine ⟨⟨a,ha⟩,hnc0,?_,?_⟩
     . simp [v3,elim,wf,ha]
     . simp only [v3,List.take_zero,List.drop_zero,List.length_nil,zero_add]
       have hzero:elim n [] (wf n ⟨a,ha⟩,[])=(wf n ⟨a,ha⟩,[]):=rfl
       rw [hzero];simp only [List.length_nil,zero_add];omega
   . rw [h3]
     have hbd:=(wz n f gs o ⟨a,ha⟩ (cap - 2) hm.hcl hm.hev hnc0 hlb).2
     refine ⟨⟨a,ha⟩,hnc0,?_,?_⟩
     . simp [v3,elim,wf,ha]
     . simp only [v3,List.take_zero,List.drop_zero,List.length_nil,zero_add]
       have hzero:elim n [] (wf n ⟨a,ha⟩,[])=(wf n ⟨a,ha⟩,[]):=rfl
       rw [hzero];simp only [List.length_nil,zero_add];omega
 have htr:=q123 n f gs o hm gs.length 0 (by omega) tg hok0
 refine ⟨gs.length,by omega,?_⟩
 have heq:(liveList gs n o 0).map (fun a => (val gs n a,tg a)) =
     List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i):=by
   rw [hlive0]
   apply List.ext_getElem
   . simp
   . intro i h1 h2
     have hi:i < n:=by simpa using h2
     simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
     exact Prod.ext (q172 gs n ⟨i,hi⟩) (by simp [tg,hi])
 rw [← heq]
 exact htr
def zm {α:Type} (x:Nat) (f:Nat->α) : α :=
 match x with
 | 0 => f 0
 | n+1 => f (Nat.succ n)
lemma v5 {α:Type} (x:Nat) (f:Nat->α):zm x f=f x:=by
 cases x <;> rfl
structure Cfg where
 k:Nat
 sh0:Nat
 sh1:Nat
 shTT:Nat
 all1v:Nat
 goalv:Nat
 lok:Nat
 m0all:Nat
 m0:Nat
 a29_0:Nat
 b5_0:Nat
 m1:Nat
 m12:Nat
 a29_1:Nat
 b5_1:Nat
def q76 (sw:Nat × Nat × Nat × Nat) (w:Nat):Nat :=
 let (d,m01,m10,mEq):=sw
 Nat.lor (Nat.lor (Nat.land w mEq) (Nat.shiftRight (Nat.land w m01) d))
         (Nat.shiftLeft (Nat.land w m10) d)
def ym:List (Nat × Nat × Nat × Nat)->Nat->Nat
 | [],w => w
 | sw::rest,w => ym rest (q76 sw w)
def q72 (sh:Nat):List (Nat × Nat)->List (Nat × Nat)
 | [] => []
 | (w,tg)::rest => zm (Nat.shiftRight w sh) fun v => (v,tg)::q72 sh rest
def wx (g:List (Nat × Nat × Nat × Nat)):List (Nat × Nat)->List (Nat × Nat)
 | [] => []
 | (w,tg)::rest => zm (ym g w) fun v => (v,tg)::wx g rest
def M128:Nat:=0x9e3779b97f4a7c15f39cc0605cedc835
def q211:Nat:=0x517cc1b727220a95b3650d1e9a87c3f1
def q210:Nat:=0xbf58476d1ce4e5b994d049bb133111eb
def q209:Nat:=0x2545f4914f6cdd1d6c62272e07bb0142
def q208 (salt w tg:Nat):Nat :=
 let s:=match tg with
   | 0 => salt
   | 1 => Nat.xor salt q211
   | 2 => Nat.xor salt q210
   | _ => Nat.xor salt q209
 zm (Nat.xor (Nat.xor w (Nat.shiftRight w 61)) s) fun x =>
 Nat.shiftRight (Nat.mul x (Nat.xor x M128)) 104
def q199 (salt:Nat):Nat->List (Nat × Nat)->Nat
 | acc,[] => acc
 | acc,(w,tg)::rest => zm (Nat.add acc (q208 salt w tg)) fun acc' => q199 salt acc' rest
def q75 (salt:Nat) (ws:List (Nat × Nat)):Nat:=Nat.land (q199 salt 0 ws) 0xFFFFFF
def q205 (T i:Nat):Nat:=Nat.land (Nat.shiftRight T (Nat.mul 24 i)) 0xFFFFFF
def q192 (T i:Nat):Nat:=Nat.land (Nat.shiftRight T (Nat.mul 32 i)) 0xFFFFFFFF
def q167 (T h:Nat):Nat->Nat->Nat->Nat
 | 0,lo,_ => lo
 | fuel+1,lo,hi =>
   if Nat.ble (Nat.add lo 2) hi then
     zm (Nat.div (Nat.add lo hi) 2) fun mid =>
     if Nat.ble (q205 T mid) h then q167 T h fuel mid hi else q167 T h fuel lo mid
   else lo
def q85 (NN FL HT:Nat->Nat) (s h:Nat):Nat :=
 let n:=NN s
 if Nat.beq n 0 then 999999
 else
   let ht:=HT s
   zm (q167 ht h (FL s) 0 n) fun j =>
   if Nat.beq (q205 ht j) h then j else 999999
def twEq (a b:Nat × Nat):Bool:=Nat.beq a.1 b.1&&Nat.beq a.2 b.2
def jy (x:Nat × Nat):List (Nat × Nat)->Option (List (Nat × Nat))
 | [] => none
 | a::rest =>
   if twEq x a then some rest
   else match jy x rest with
     | none => none
     | some r => some (a::r)
def jk:List (Nat × Nat)->List (Nat × Nat)->Bool
 | [],[] => true
 | a::as,bs => match jy a bs with
   | none => false
   | some bs' => jk as bs'
 | _,_ => false
def twLt (a b:Nat × Nat):Bool :=
 if Nat.beq a.1 b.1 then Nat.blt a.2 b.2 else Nat.blt a.1 b.1
def q62 (x:Nat × Nat):List (Nat × Nat)->List (Nat × Nat)
 | [] => [x]
 | a::rest => if twLt x a then x::a::rest else a::q62 x rest
def q125:List (Nat × Nat)->List (Nat × Nat)
 | [] => []
 | a::rest => q62 a (q125 rest)
def q158:List (Nat × Nat)->List (Nat × Nat)->Bool
 | [],_ => false
 | _,[] => false
 | a::as,b::bs =>
   if twEq a b then q158 as bs else twLt a b
def q69 (g:List (Nat × Nat × Nat × Nat)) (ws:List (Nat × Nat)):List (Nat × Nat) :=
 let ws':=q125 (wx g ws)
 if q158 ws' ws then ws' else ws
def q35:List (List (Nat × Nat × Nat × Nat))->List (Nat × Nat)->List (Nat × Nat)
 | [],ws => ws
 | g::rest,ws => q35 rest (q69 g ws)
def q186 (gens:List (List (Nat × Nat × Nat × Nat))) (ws:List (Nat × Nat)):List (Nat × Nat) :=
 let s0:=q125 ws
 match gens with
 | [] => s0
 | [g] => q69 g s0
 | _ => q35 gens (q35 gens s0)
def qi (m0 w0:Nat):Nat :=
 zm (Nat.land w0 m0) fun a =>
 zm (Nat.land (Nat.shiftRight w0 1) m0) fun b =>
 zm (Nat.land (Nat.shiftRight w0 2) m0) fun c =>
 zm (Nat.xor m0 (Nat.land (Nat.shiftRight w0 3) m0)) fun nd =>
 zm (Nat.xor m0 (Nat.land (Nat.shiftRight w0 4) m0)) fun ne =>
 zm (Nat.xor m0 (Nat.land (Nat.shiftRight w0 5) m0)) fun nf =>
 Nat.sub (Nat.add (Nat.add (Nat.land nd b) (Nat.land nd c)) (Nat.add (Nat.land a ne) (Nat.land a nf)))
         (Nat.land (Nat.land a nd) (Nat.land (Nat.lor b c) (Nat.lor ne nf)))
def yg (sh1 m1 m12 w:Nat):Nat :=
 zm (Nat.shiftRight w sh1) fun w0 =>
 zm (Nat.land w0 m1) fun a =>
 zm (Nat.land (Nat.shiftRight w0 1) m1) fun b =>
 zm (Nat.land (Nat.shiftRight w0 2) m1) fun c =>
 zm (Nat.land (Nat.shiftRight w0 3) m1) fun d =>
 zm (Nat.land (Nat.shiftRight w0 4) m1) fun e =>
 zm (Nat.land (Nat.shiftRight w0 5) m1) fun f =>
 zm (Nat.xor m1 d) fun nd =>
 zm (Nat.xor m1 e) fun ne =>
 zm (Nat.xor m1 f) fun nf =>
 zm (Nat.xor m1 a) fun na =>
 zm (Nat.xor m1 b) fun nb =>
 zm (Nat.xor m1 c) fun nc =>
 zm (Nat.sub (Nat.add (Nat.add (Nat.land nd b) (Nat.land nd c)) (Nat.add (Nat.land a ne) (Nat.land a nf)))
                (Nat.land (Nat.land a nd) (Nat.land (Nat.lor b c) (Nat.lor ne nf)))) fun v1 =>
 zm (Nat.sub (Nat.add (Nat.add (Nat.land d nb) (Nat.land d nc)) (Nat.add (Nat.land na e) (Nat.land na f)))
                (Nat.land (Nat.land na d) (Nat.land (Nat.lor nb nc) (Nat.lor e f)))) fun v2 =>
 zm (Nat.lor v1 v2) fun u =>
 zm (Nat.land u m12) fun hi =>
 Nat.lor hi (Nat.lor (Nat.lor (Nat.land v1 (Nat.shiftRight v1 1)) (Nat.land v2 (Nat.shiftRight v2 1)))
                     (Nat.land (Nat.land u m1) (Nat.xor m1 (Nat.shiftRight hi 1))))
inductive PList where
 | nil:PList
 | cons (w tg alo ahi nahi cw uw a0 v0w v1w postC postU postV0 postV1:Nat) (tail:PList):PList
def kt (c:Cfg):List (Nat × Nat)->Nat × Nat × Nat × Nat × PList
 | [] => (0,0,0,0,PList.nil)
 | (w,tg)::rest =>
   let (pC,pU,pV0,pV1,tl):=kt c rest
   let alo:=Nat.land w c.lok
   let ahi:=Nat.land (Nat.shiftRight w c.k) c.lok
   let nahi:=Nat.xor c.lok ahi
   let cw:=Nat.xor alo ahi
   let uw:=Nat.land cw ahi
   let a0:=Nat.land (Nat.shiftRight w c.sh0) c.m0all
   let v0w:=qi c.m0 a0
   let v1w:=yg c.sh1 c.m1 c.m12 w
   (Nat.lor cw pC,Nat.lor uw pU,Nat.add v0w pV0,Nat.add v1w pV1,
    PList.cons w tg alo ahi nahi cw uw a0 v0w v1w pC pU pV0 pV1 tl)
def q164:List (Nat × Nat)->Nat
 | [] => 0
 | _::rest => Nat.add 1 (q164 rest)
def yz (x:Nat):List (Nat × Nat)->Bool
 | [] => false
 | (a,_)::rest => if Nat.beq x a then true else yz x rest
def qx:List (Nat × Nat)->List (Nat × Nat)->List (Nat × Nat)
 | [],ys => ys
 | a::xs,ys => qx xs (a::ys)
def pToList:PList->List (Nat × Nat)
 | PList.nil => []
 | PList.cons w tg _ _ _ _ _ _ _ _ _ _ _ _ tl => (w,tg)::pToList tl
def qj (all1v:Nat) (ws:List (Nat × Nat)) (w:Nat):Bool :=
 !(Nat.beq w 0)&&!(Nat.beq w all1v)&&!(yz w ws)
def qb (c:Cfg) (v0Acc v0w:Nat):Bool :=
 Nat.beq (Nat.land (Nat.add (Nat.add v0Acc v0w) c.a29_0) c.b5_0) c.b5_0
def z3 (c:Cfg) (v1Tot:Nat):Bool :=
 Nat.beq (Nat.land (Nat.add v1Tot c.a29_1) c.b5_1) c.b5_1
def ke (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (a ta alo nahi a0:Nat) (pre:List (Nat × Nat)):Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,PList.nil => false
 | pmU,pmV0,mid,PList.cons b tb blo _ nbhi _ ub b0 v0b _ _ postU postV0 _ post =>
   let missU:=Nat.xor c.lok (Nat.lor pmU postU)
   let orHit :=
     !(Nat.beq ta 2)&&!(Nat.beq tb 2) &&
     Nat.beq (Nat.land missU (Nat.lor alo blo)) 0 &&
     qb c (Nat.add pmV0 postV0) (qi c.m0 (Nat.lor a0 b0)) &&
     (let w:=Nat.lor a b;qj c.all1v ws w&&onSurv ((w,0)::qx pre (qx mid (pToList post))))
   if orHit then true
   else
     let andHit :=
       !(Nat.beq ta 1)&&!(Nat.beq tb 1) &&
       Nat.beq (Nat.land missU (Nat.lor nahi nbhi)) 0 &&
       qb c (Nat.add pmV0 postV0) (qi c.m0 (Nat.land a0 b0)) &&
       (let w:=Nat.land a b;let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0;
        qj c.all1v ws w&&onSurv ((w,wt)::qx pre (qx mid (pToList post))))
     if andHit then true
     else ke c ws onSurv a ta alo nahi a0 pre
       (Nat.lor pmU ub) (Nat.add pmV0 v0b) ((b,tb)::mid) post
def q98 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool) :
   Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,PList.nil => false
 | preU,preV0,pre,PList.cons a ta alo _ nahi _ ua a0 v0a _ _ _ _ _ suf =>
   if ke c ws onSurv a ta alo nahi a0 pre preU preV0 [] suf then true
   else q98 c ws onSurv (Nat.lor preU ua) (Nat.add preV0 v0a) ((a,ta)::pre) suf
def vx (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (a ta alo nahi a0 v0a:Nat) (pre:List (Nat × Nat)):Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,PList.nil => false
 | pmU,pmV0,mid,PList.cons b tb blo _ nbhi _ ub b0 v0b _ _ postU postV0 _ post =>
   let missU:=Nat.xor c.lok (Nat.lor pmU postU)
   let orHit :=
     if Nat.beq ta 2||Nat.beq tb 2 then false
     else
       let okOrA:=Nat.beq (Nat.land missU alo) 0
       let okOrB:=Nat.beq (Nat.land missU blo) 0
       if okOrA then
         let w:=Nat.lor a b
         let rV0:=Nat.add pmV0 postV0
         let v0w:=qi c.m0 (Nat.lor a0 b0)
         if okOrB&&qj c.all1v ws w&&onSurv ((w,0)::qx pre (qx mid (pToList post))) then true
         else if !(Nat.beq ta 1)&&qb c (Nat.add rV0 v0a) v0w&&qj c.all1v ws w &&
                 onSurv ((w,0)::(a,if Nat.beq ta 3 then 1 else 0)::qx pre (qx mid (pToList post))) then true
         else !(Nat.beq tb 1)&&okOrB&&qb c (Nat.add rV0 v0b) v0w&&qj c.all1v ws w &&
              onSurv ((w,0)::(b,if Nat.beq tb 3 then 1 else 0)::qx pre (qx mid (pToList post)))
       else if okOrB&&!(Nat.beq tb 1) then
         let w:=Nat.lor a b
         let rV0:=Nat.add pmV0 postV0
         qb c (Nat.add rV0 v0b) (qi c.m0 (Nat.lor a0 b0))&&qj c.all1v ws w &&
         onSurv ((w,0)::(b,if Nat.beq tb 3 then 1 else 0)::qx pre (qx mid (pToList post)))
       else false
   if orHit then true
   else
     let andHit :=
       if Nat.beq ta 1||Nat.beq tb 1 then false
       else
         let okAndA:=Nat.beq (Nat.land missU nahi) 0
         let okAndB:=Nat.beq (Nat.land missU nbhi) 0
         if okAndA then
           let w:=Nat.land a b
           let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0
           let rV0:=Nat.add pmV0 postV0
           let v0w:=qi c.m0 (Nat.land a0 b0)
           if okAndB&&qj c.all1v ws w&&onSurv ((w,wt)::qx pre (qx mid (pToList post))) then true
           else if Nat.beq ta 0&&qb c (Nat.add rV0 v0a) v0w&&qj c.all1v ws w &&
                   onSurv ((w,wt)::(a,0)::qx pre (qx mid (pToList post))) then true
           else Nat.beq tb 0&&okAndB&&qb c (Nat.add rV0 v0b) v0w&&qj c.all1v ws w &&
                onSurv ((w,wt)::(b,0)::qx pre (qx mid (pToList post)))
         else if okAndB&&Nat.beq tb 0 then
           let w:=Nat.land a b
           let wt:=if Nat.beq ta 3 then 1 else 0
           let rV0:=Nat.add pmV0 postV0
           qb c (Nat.add rV0 v0b) (qi c.m0 (Nat.land a0 b0))&&qj c.all1v ws w &&
           onSurv ((w,wt)::(b,0)::qx pre (qx mid (pToList post)))
         else false
     if andHit then true
     else vx c ws onSurv a ta alo nahi a0 v0a pre
       (Nat.lor pmU ub) (Nat.add pmV0 v0b) ((b,tb)::mid) post
def js (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool) :
   Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,PList.nil => false
 | preU,preV0,pre,PList.cons a ta alo _ nahi _ ua a0 v0a _ _ _ _ _ suf =>
   if vx c ws onSurv a ta alo nahi a0 v0a pre preU preV0 [] suf then true
   else js c ws onSurv (Nat.lor preU ua) (Nat.add preV0 v0a) ((a,ta)::pre) suf
def we (c:Cfg) (ws:List (Nat × Nat))
   (a ta alo nahi a0 v0a:Nat):Nat->Nat->PList->Bool
 | _,_,PList.nil => false
 | pmU,pmV0,PList.cons b tb blo _ nbhi _ ub b0 v0b _ _ postU postV0 _ post =>
   let missU:=Nat.xor c.lok (Nat.lor pmU postU)
   let orHit :=
     if Nat.beq ta 2||Nat.beq tb 2 then false
     else
       let okOrA:=Nat.beq (Nat.land missU alo) 0
       let okOrB:=Nat.beq (Nat.land missU blo) 0
       if okOrA then
         let w:=Nat.lor a b
         let rV0:=Nat.add pmV0 postV0
         let v0w:=qi c.m0 (Nat.lor a0 b0)
         (okOrB&&qj c.all1v ws w) ||
         (!(Nat.beq ta 1)&&qb c (Nat.add rV0 v0a) v0w&&qj c.all1v ws w) ||
         (!(Nat.beq tb 1)&&okOrB&&qb c (Nat.add rV0 v0b) v0w&&qj c.all1v ws w)
       else if okOrB&&!(Nat.beq tb 1) then
         qb c (Nat.add (Nat.add pmV0 postV0) v0b) (qi c.m0 (Nat.lor a0 b0))&&qj c.all1v ws (Nat.lor a b)
       else false
   if orHit then true
   else
     let andHit :=
       if Nat.beq ta 1||Nat.beq tb 1 then false
       else
         let okAndA:=Nat.beq (Nat.land missU nahi) 0
         let okAndB:=Nat.beq (Nat.land missU nbhi) 0
         if okAndA then
           let w:=Nat.land a b
           let rV0:=Nat.add pmV0 postV0
           let v0w:=qi c.m0 (Nat.land a0 b0)
           (okAndB&&qj c.all1v ws w) ||
           (Nat.beq ta 0&&qb c (Nat.add rV0 v0a) v0w&&qj c.all1v ws w) ||
           (Nat.beq tb 0&&okAndB&&qb c (Nat.add rV0 v0b) v0w&&qj c.all1v ws w)
         else if okAndB&&Nat.beq tb 0 then
           qb c (Nat.add (Nat.add pmV0 postV0) v0b) (qi c.m0 (Nat.land a0 b0))&&qj c.all1v ws (Nat.land a b)
         else false
     if andHit then true
     else we c ws a ta alo nahi a0 v0a (Nat.lor pmU ub) (Nat.add pmV0 v0b) post
def q26 (c:Cfg) (ws:List (Nat × Nat)):Nat->Nat->PList->Bool
 | _,_,PList.nil => false
 | preU,preV0,PList.cons a ta alo _ nahi _ ua a0 v0a _ _ _ _ _ suf =>
   if we c ws a ta alo nahi a0 v0a preU preV0 suf then true
   else q26 c ws (Nat.lor preU ua) (Nat.add preV0 v0a) suf
def w7 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool) :
   Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,PList.nil => false
 | preU,preV0,pre,PList.cons a ta alo _ _ cw ua a0 v0a _ _ postU postV0 _ suf =>
   let hit :=
     !(Nat.beq ta 1)&&!(Nat.beq ta 2) &&
     (let uw:=Nat.land cw alo;
      Nat.beq (Nat.lor (Nat.lor preU postU) uw) c.lok &&
      qb c (Nat.add preV0 postV0) (qi c.m0 (Nat.xor a0 c.m0all)) &&
      (let w:=Nat.xor a c.all1v;let wt:=if Nat.beq ta 3 then 2 else 0;
       qj c.all1v ws w&&onSurv ((w,wt)::qx pre (pToList suf))))
   if hit then true
   else w7 c ws onSurv (Nat.lor preU ua) (Nat.add preV0 v0a) ((a,ta)::pre) suf
def kd (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (onSurv:List (Nat × Nat)->Bool)
   (a ta alo ahi nahi a0 v0a:Nat) (pre:List (Nat × Nat)) :
   Nat->Nat->Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,_,_,PList.nil => false
 | pmC,pmU,pmV0,pmV1,mid,PList.cons b tb blo bhi nbhi cb ub b0 v0b v1b postC postU postV0 postV1 post =>
   let rC:=Nat.lor pmC postC
   let rV1:=Nat.add pmV1 postV1
   let missU:=Nat.xor c.lok (Nat.lor pmU postU)
   let orHit :=
     if Nat.beq ta 2||Nat.beq tb 2 then false
     else
       let w:=Nat.lor a b
       let cw:=Nat.xor (Nat.lor alo blo) (Nat.lor ahi bhi)
       if hasUp then
         let okA:=Nat.beq (Nat.land missU alo) 0
         let okB:=Nat.beq (Nat.land missU blo) 0
         let rV0:=Nat.add pmV0 postV0
         let v0w:=qi c.m0 (Nat.lor a0 b0)
         if Nat.beq (Nat.lor rC cw) c.lok&&((okA&&okB)||z3 c (Nat.add rV1 (yg c.sh1 c.m1 c.m12 w))) &&
            qj c.all1v ws w&&onSurv ((w,0)::qx pre (qx mid (pToList post))) then true
         else if !(Nat.beq ta 1)&&okA&&qb c (Nat.add rV0 v0a) v0w&&qj c.all1v ws w &&
                 onSurv ((w,0)::(a,if Nat.beq ta 3 then 1 else 0)::qx pre (qx mid (pToList post))) then true
         else !(Nat.beq tb 1)&&okB&&qb c (Nat.add rV0 v0b) v0w&&qj c.all1v ws w &&
              onSurv ((w,0)::(b,if Nat.beq tb 3 then 1 else 0)::qx pre (qx mid (pToList post)))
       else
         Nat.beq (Nat.lor rC cw) c.lok&&z3 c (Nat.add rV1 (yg c.sh1 c.m1 c.m12 w)) &&
         qj c.all1v ws w&&onSurv ((w,0)::qx pre (qx mid (pToList post)))
   if orHit then true
   else
     let andHit :=
       if Nat.beq ta 1||Nat.beq tb 1 then false
       else
         let w:=Nat.land a b
         let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0
         let cw:=Nat.xor (Nat.land alo blo) (Nat.land ahi bhi)
         if hasUp then
           let okA:=Nat.beq (Nat.land missU nahi) 0
           let okB:=Nat.beq (Nat.land missU nbhi) 0
           let rV0:=Nat.add pmV0 postV0
           let v0w:=qi c.m0 (Nat.land a0 b0)
           if Nat.beq (Nat.lor rC cw) c.lok&&((okA&&okB)||z3 c (Nat.add rV1 (yg c.sh1 c.m1 c.m12 w))) &&
              qj c.all1v ws w&&onSurv ((w,wt)::qx pre (qx mid (pToList post))) then true
           else if Nat.beq ta 0&&okA&&qb c (Nat.add rV0 v0a) v0w&&qj c.all1v ws w &&
                   onSurv ((w,wt)::(a,0)::qx pre (qx mid (pToList post))) then true
           else Nat.beq tb 0&&okB&&qb c (Nat.add rV0 v0b) v0w&&qj c.all1v ws w &&
                onSurv ((w,wt)::(b,0)::qx pre (qx mid (pToList post)))
         else
           Nat.beq (Nat.lor rC cw) c.lok&&z3 c (Nat.add rV1 (yg c.sh1 c.m1 c.m12 w)) &&
           qj c.all1v ws w&&onSurv ((w,wt)::qx pre (qx mid (pToList post)))
     if andHit then true
     else kd c ws hasUp onSurv a ta alo ahi nahi a0 v0a pre
       (Nat.lor pmC cb) (Nat.lor pmU ub) (Nat.add pmV0 v0b) (Nat.add pmV1 v1b) ((b,tb)::mid) post
def q96 (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (onSurv:List (Nat × Nat)->Bool) :
   Nat->Nat->Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,_,_,PList.nil => false
 | preC,preU,preV0,preV1,pre,PList.cons a ta alo ahi nahi ca ua a0 v0a v1a _ _ _ _ suf =>
   if kd c ws hasUp onSurv a ta alo ahi nahi a0 v0a pre preC preU preV0 preV1 [] suf then true
   else q96 c ws hasUp onSurv (Nat.lor preC ca) (Nat.lor preU ua) (Nat.add preV0 v0a) (Nat.add preV1 v1a) ((a,ta)::pre) suf
def w6 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool) :
   Nat->Nat->Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,_,_,PList.nil => false
 | preC,preU,preV0,preV1,pre,PList.cons a ta alo _ _ ca ua a0 v0a v1a postC postU postV0 postV1 suf =>
   let hit :=
     if Nat.beq ta 1||Nat.beq ta 2 then false
     else
       let w:=Nat.xor a c.all1v
       let wt:=if Nat.beq ta 3 then 2 else 0
       let uw:=Nat.land ca alo
       let rC:=Nat.lor preC postC
       let rU:=Nat.lor preU postU
       let rV0:=Nat.add preV0 postV0
       let rV1:=Nat.add preV1 postV1
       (Nat.beq (Nat.lor rC ca) c.lok &&
        (Nat.beq (Nat.lor rU uw) c.lok||z3 c (Nat.add rV1 v1a)) &&
        qj c.all1v ws w&&onSurv ((w,wt)::qx pre (pToList suf))) ||
       (Nat.beq ta 0&&Nat.beq (Nat.lor rU ca) c.lok &&
        qb c (Nat.add rV0 v0a) (qi c.m0 (Nat.xor a0 c.m0all)) &&
        qj c.all1v ws w&&onSurv ((w,0)::(a,0)::qx pre (pToList suf)))
   if hit then true
   else w6 c ws onSurv (Nat.lor preC ca) (Nat.lor preU ua) (Nat.add preV0 v0a) (Nat.add preV1 v1a) ((a,ta)::pre) suf
def kc (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (totV0:Nat) (onSurv:List (Nat × Nat)->Bool)
   (a ta alo ahi nahi ca a0 v1a:Nat) (pre:List (Nat × Nat)) :
   Nat->Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,_,PList.nil => false
 | pmC,pmU,pmV1,mid,PList.cons b tb blo bhi nbhi cb ub b0 _ v1b postC postU _ postV1 post =>
   let rC:=Nat.lor pmC postC
   let rV1:=Nat.add pmV1 postV1
   let missU:=Nat.xor c.lok (Nat.lor pmU postU)
   let rest:=qx pre (qx mid (pToList post))
   let orHit :=
     if Nat.beq ta 2||Nat.beq tb 2 then false
     else
       let w:=Nat.lor a b
       let cw:=Nat.xor (Nat.lor alo blo) (Nat.lor ahi bhi)
       let v1w:=yg c.sh1 c.m1 c.m12 w
       let ta':=if Nat.beq ta 3 then 1 else 0
       let tb':=if Nat.beq tb 3 then 1 else 0
       if hasUp then
         let okA:=Nat.beq (Nat.land missU alo) 0
         let okB:=Nat.beq (Nat.land missU blo) 0
         (Nat.beq (Nat.lor rC cw) c.lok&&qj c.all1v ws w&&onSurv ((w,0)::rest)) ||
         (!(Nat.beq ta 1)&&Nat.beq (Nat.lor (Nat.lor rC ca) cw) c.lok&&(okA||z3 c (Nat.add (Nat.add rV1 v1a) v1w))&&qj c.all1v ws w&&onSurv ((w,0)::(a,ta')::rest)) ||
         (!(Nat.beq tb 1)&&Nat.beq (Nat.lor (Nat.lor rC cb) cw) c.lok&&(okB||z3 c (Nat.add (Nat.add rV1 v1b) v1w))&&qj c.all1v ws w&&onSurv ((w,0)::(b,tb')::rest)) ||
         (!(Nat.beq ta 1)&&!(Nat.beq tb 1)&&qb c totV0 (qi c.m0 (Nat.lor a0 b0))&&qj c.all1v ws w&&onSurv ((w,0)::(a,ta')::(b,tb')::rest))
       else
         (Nat.beq (Nat.lor rC cw) c.lok&&qj c.all1v ws w&&onSurv ((w,0)::rest)) ||
         (!(Nat.beq ta 1)&&Nat.beq (Nat.lor (Nat.lor rC ca) cw) c.lok&&z3 c (Nat.add (Nat.add rV1 v1a) v1w)&&qj c.all1v ws w&&onSurv ((w,0)::(a,ta')::rest)) ||
         (!(Nat.beq tb 1)&&Nat.beq (Nat.lor (Nat.lor rC cb) cw) c.lok&&z3 c (Nat.add (Nat.add rV1 v1b) v1w)&&qj c.all1v ws w&&onSurv ((w,0)::(b,tb')::rest))
   if orHit then true
   else
     let andHit :=
       if Nat.beq ta 1||Nat.beq tb 1 then false
       else
         let w:=Nat.land a b
         let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0
         let cw:=Nat.xor (Nat.land alo blo) (Nat.land ahi bhi)
         let v1w:=yg c.sh1 c.m1 c.m12 w
         if hasUp then
           let okA:=Nat.beq (Nat.land missU nahi) 0
           let okB:=Nat.beq (Nat.land missU nbhi) 0
           (Nat.beq (Nat.lor rC cw) c.lok&&qj c.all1v ws w&&onSurv ((w,wt)::rest)) ||
           (Nat.beq ta 0&&Nat.beq (Nat.lor (Nat.lor rC ca) cw) c.lok&&(okA||z3 c (Nat.add (Nat.add rV1 v1a) v1w))&&qj c.all1v ws w&&onSurv ((w,wt)::(a,0)::rest)) ||
           (Nat.beq tb 0&&Nat.beq (Nat.lor (Nat.lor rC cb) cw) c.lok&&(okB||z3 c (Nat.add (Nat.add rV1 v1b) v1w))&&qj c.all1v ws w&&onSurv ((w,wt)::(b,0)::rest)) ||
           (Nat.beq ta 0&&Nat.beq tb 0&&qb c totV0 (qi c.m0 (Nat.land a0 b0))&&qj c.all1v ws w&&onSurv ((w,0)::ws))
         else
           (Nat.beq (Nat.lor rC cw) c.lok&&qj c.all1v ws w&&onSurv ((w,wt)::rest)) ||
           (Nat.beq ta 0&&Nat.beq (Nat.lor (Nat.lor rC ca) cw) c.lok&&z3 c (Nat.add (Nat.add rV1 v1a) v1w)&&qj c.all1v ws w&&onSurv ((w,wt)::(a,0)::rest)) ||
           (Nat.beq tb 0&&Nat.beq (Nat.lor (Nat.lor rC cb) cw) c.lok&&z3 c (Nat.add (Nat.add rV1 v1b) v1w)&&qj c.all1v ws w&&onSurv ((w,wt)::(b,0)::rest))
     if andHit then true
     else kc c ws hasUp totV0 onSurv a ta alo ahi nahi ca a0 v1a pre
       (Nat.lor pmC cb) (Nat.lor pmU ub) (Nat.add pmV1 v1b) ((b,tb)::mid) post
def q94 (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (totV0:Nat) (onSurv:List (Nat × Nat)->Bool) :
   Nat->Nat->Nat->List (Nat × Nat)->PList->Bool
 | _,_,_,_,PList.nil => false
 | preC,preU,preV1,pre,PList.cons a ta alo ahi nahi ca ua a0 _ v1a _ _ _ _ suf =>
   if kc c ws hasUp totV0 onSurv a ta alo ahi nahi ca a0 v1a pre preC preU preV1 [] suf then true
   else q94 c ws hasUp totV0 onSurv (Nat.lor preC ca) (Nat.lor preU ua) (Nat.add preV1 v1a) ((a,ta)::pre) suf
def w5 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool) :
   Nat->List (Nat × Nat)->PList->Bool
 | _,_,PList.nil => false
 | preC,pre,PList.cons a ta _ _ _ ca _ _ _ _ postC _ _ _ suf =>
   let hit :=
     !(Nat.beq ta 1)&&!(Nat.beq ta 2) &&
     (let w:=Nat.xor a c.all1v;let wt:=if Nat.beq ta 3 then 2 else 0;
      qj c.all1v ws w &&
      ((Nat.beq (Nat.lor (Nat.lor preC postC) ca) c.lok&&onSurv ((w,wt)::qx pre (pToList suf))) ||
       (Nat.beq ta 0&&onSurv ((w,0)::ws))))
   if hit then true
   else w5 c ws onSurv (Nat.lor preC ca) ((a,ta)::pre) suf
def k9 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (a ta alo ahi ca:Nat) (pre:List (Nat × Nat)):Nat->List (Nat × Nat)->PList->Bool
 | _,_,PList.nil => false
 | pmC,mid,PList.cons b tb blo bhi _ cb _ _ _ _ postC _ _ _ post =>
   let rC:=Nat.lor pmC postC
   let rest:=qx pre (qx mid (pToList post))
   let orHit :=
     !(Nat.beq ta 2)&&!(Nat.beq tb 2) &&
     (let w:=Nat.lor a b
      let cw:=Nat.xor (Nat.lor alo blo) (Nat.lor ahi bhi)
      let ta':=if Nat.beq ta 3 then 1 else 0
      let tb':=if Nat.beq tb 3 then 1 else 0
      qj c.all1v ws w &&
      ((Nat.beq (Nat.lor rC cw) c.lok&&onSurv ((w,0)::rest)) ||
       (!(Nat.beq ta 1)&&Nat.beq (Nat.lor (Nat.lor rC ca) cw) c.lok&&onSurv ((w,0)::(a,ta')::rest)) ||
       (!(Nat.beq tb 1)&&Nat.beq (Nat.lor (Nat.lor rC cb) cw) c.lok&&onSurv ((w,0)::(b,tb')::rest)) ||
       (!(Nat.beq ta 1)&&!(Nat.beq tb 1)&&onSurv ((w,0)::(a,ta')::(b,tb')::rest))))
   if orHit then true
   else
     let andHit :=
       !(Nat.beq ta 1)&&!(Nat.beq tb 1) &&
       (let w:=Nat.land a b
        let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0
        let cw:=Nat.xor (Nat.land alo blo) (Nat.land ahi bhi)
        qj c.all1v ws w &&
        ((Nat.beq (Nat.lor rC cw) c.lok&&onSurv ((w,wt)::rest)) ||
         (Nat.beq ta 0&&Nat.beq (Nat.lor (Nat.lor rC ca) cw) c.lok&&onSurv ((w,wt)::(a,0)::rest)) ||
         (Nat.beq tb 0&&Nat.beq (Nat.lor (Nat.lor rC cb) cw) c.lok&&onSurv ((w,wt)::(b,0)::rest)) ||
         (Nat.beq ta 0&&Nat.beq tb 0&&onSurv ((w,0)::ws))))
     if andHit then true
     else k9 c ws onSurv a ta alo ahi ca pre (Nat.lor pmC cb) ((b,tb)::mid) post
def q92 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool) :
   Nat->List (Nat × Nat)->PList->Bool
 | _,_,PList.nil => false
 | preC,pre,PList.cons a ta alo ahi _ ca _ _ _ _ _ _ _ _ suf =>
   if k9 c ws onSurv a ta alo ahi ca pre preC [] suf then true
   else q92 c ws onSurv (Nat.lor preC ca) ((a,ta)::pre) suf
def j6 (c:Cfg) (ws:List (Nat × Nat)):Bool :=
 match ws with
 | [(a,_)] => Nat.beq (Nat.xor a c.all1v) c.goalv
 | [(a,_),(b,_)] => Nat.beq (Nat.lor a b) c.goalv||Nat.beq (Nat.land a b) c.goalv
 | _ => false
def scanAll (c:Cfg) (s:Nat) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool):Bool :=
 if Nat.beq s 0 then j6 c ws
 else
   let len:=q164 ws
   let slack:=Nat.sub (Nat.add s 2) len
   let (_,totU,totV0,totV1,pl):=kt c ws
   let hasUp:=Nat.beq totU c.lok
   match slack with
   | 0 => hasUp&&q98 c ws onSurv 0 0 [] pl
   | 1 =>
     let hasSym1:=z3 c totV1
     if hasSym1 then w7 c ws onSurv 0 0 [] pl||q96 c ws hasUp onSurv 0 0 0 0 [] pl
     else hasUp&&js c ws onSurv 0 0 [] pl
   | 2 => w6 c ws onSurv 0 0 0 0 [] pl||q94 c ws hasUp totV0 onSurv 0 0 0 [] pl
   | _ => w5 c ws onSurv 0 [] pl||q92 c ws onSurv 0 [] pl
def scanInline (c:Cfg) (s:Nat) (ws:List (Nat × Nat)):Bool :=
 if Nat.beq s 0 then j6 c ws
 else
   let len:=q164 ws
   let slack:=Nat.sub (Nat.add s 2) len
   let (_,totU,totV0,totV1,pl):=kt c ws
   let hasUp:=Nat.beq totU c.lok
   match slack with
   | 0 => hasUp&&q98 c ws (fun _ => true) 0 0 [] pl
   | 1 =>
     let hasSym1:=z3 c totV1
     if hasSym1 then w7 c ws (fun _ => true) 0 0 [] pl||q96 c ws hasUp (fun _ => true) 0 0 0 0 [] pl
     else hasUp&&q26 c ws 0 0 pl
   | 2 => w6 c ws (fun _ => true) 0 0 0 0 [] pl||q94 c ws hasUp totV0 (fun _ => true) 0 0 0 [] pl
   | _ => w5 c ws (fun _ => true) 0 [] pl||q92 c ws (fun _ => true) 0 [] pl
def q42 (pid:Nat):Nat->Nat->Nat × Nat
 | 0,j => (0,j)
 | fuel+1,j =>
   let t:=Nat.div (Nat.mul (Nat.add j 1) j) 2
   if Nat.ble t pid then q42 pid fuel (Nat.add j 1)
   else (Nat.sub pid (Nat.div (Nat.mul j (Nat.sub j 1)) 2),j)
def jw:Nat->List (Nat × Nat)->Nat × Nat
 | _,[] => (0,0)
 | 0,a::_ => a
 | k+1,_::rest => jw k rest
def q38:Nat->List (Nat × Nat)->List (Nat × Nat)
 | _,[] => []
 | 0,_::rest => rest
 | k+1,a::rest => a::q38 k rest
def q203 (all1v code:Nat) (ws:List (Nat × Nat)):List (Nat × Nat) :=
 if Nat.ble code 32 then
   zm (Nat.sub code 1) fun c =>
   zm (Nat.shiftRight c 1) fun i =>
   let save:=Nat.beq (Nat.land c 1) 1
   let (a,ta):=jw i ws
   let wt:=if Nat.beq ta 3 then 2 else 0
   zm (Nat.xor a all1v) fun w =>
   let r:=q38 i ws
   if save then (w,wt)::(a,0)::r else (w,wt)::r
 else
   zm (Nat.sub code 33) fun rem =>
   let kb:=Nat.beq (Nat.land rem 1) 1
   let ka:=Nat.beq (Nat.land (Nat.shiftRight rem 1) 1) 1
   let conj:=Nat.beq (Nat.land (Nat.shiftRight rem 2) 1) 1
   let (i,j):=q42 (Nat.shiftRight rem 3) 16 1
   let (a,ta):=jw i ws
   let (b,tb):=jw j ws
   let r:=q38 i (q38 j ws)
   if conj then
     let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0
     zm (Nat.land a b) fun w =>
     let r1:=if kb then (b,0)::r else r
     let r2:=if ka then (a,0)::r1 else r1
     (w,wt)::r2
   else
     zm (Nat.lor a b) fun w =>
     let r1:=if kb then (b,if Nat.beq tb 3 then 1 else 0)::r else r
     let r2:=if ka then (a,if Nat.beq ta 3 then 1 else 0)::r1 else r1
     (w,0)::r2
def q120 (all1v:Nat) (xs:List (Nat × Nat)) (PT:Nat->Nat):Nat->Nat->Nat->List (Nat × Nat)
 | 0,_,_ => xs
 | d+1,s,j =>
   zm (q192 (PT s) j) fun e =>
   zm (Nat.land e 1023) fun code =>
   if Nat.beq code 0 then xs
   else zm (Nat.land (Nat.shiftRight e 10) 8191) fun pidx =>
     q203 all1v code (q120 all1v xs PT d (Nat.add s 1) pidx)
def Rgen (all1v cap:Nat) (xs:List (Nat × Nat)) (PT:Nat->Nat) (s j:Nat):List (Nat × Nat) :=
 q120 all1v xs PT (Nat.sub cap s) s j
def findAut1 (shTT salt:Nat) (Rtt:Nat->Nat->List (Nat × Nat)) (NN FL HT:Nat->Nat)
   (s:Nat) (zs:List (Nat × Nat)):Bool :=
 let ztt:=q72 shTT zs
 zm (q75 salt ztt) fun h =>
 zm (q85 NN FL HT s h) fun j =>
 !(Nat.beq j 999999)&&jk ztt (Rtt s j)
def findAut2 (shTT salt:Nat) (g0:List (Nat × Nat × Nat × Nat))
   (Rtt:Nat->Nat->List (Nat × Nat)) (NN FL HT:Nat->Nat)
   (s:Nat) (zs:List (Nat × Nat)):Bool :=
 let ztt:=q72 shTT zs
 zm (q75 salt ztt) fun h0 =>
 zm (q85 NN FL HT s h0) fun j0 =>
 if !(Nat.beq j0 999999)&&jk ztt (Rtt s j0) then true
 else
   let ztt1:=wx g0 ztt
   zm (q75 salt ztt1) fun h1 =>
   zm (q85 NN FL HT s h1) fun j1 =>
   !(Nat.beq j1 999999)&&jk ztt1 (Rtt s j1)
def vm (salt:Nat) (Rtt:Nat->Nat->List (Nat × Nat)) (NN FL HT:Nat->Nat)
   (s:Nat):List (List (Nat × Nat × Nat × Nat))->List (Nat × Nat)->Bool
 | [],ztt =>
   zm (q75 salt ztt) fun h =>
   zm (q85 NN FL HT s h) fun j =>
   !(Nat.beq j 999999)&&jk ztt (Rtt s j)
 | g::rest,ztt =>
   zm (q75 salt ztt) fun h =>
   zm (q85 NN FL HT s h) fun j =>
   if !(Nat.beq j 999999)&&jk ztt (Rtt s j) then true
   else vm salt Rtt NN FL HT s rest (wx g ztt)
def findAutPath (shTT salt:Nat) (path:List (List (Nat × Nat × Nat × Nat)))
   (Rtt:Nat->Nat->List (Nat × Nat)) (NN FL HT:Nat->Nat)
   (s:Nat) (zs:List (Nat × Nat)):Bool :=
 vm salt Rtt NN FL HT s path (q72 shTT zs)
def findAutGen (shTT salt:Nat) (gens:List (List (Nat × Nat × Nat × Nat)))
   (aut:Nat->List (Nat × Nat × Nat × Nat))
   (Rtt:Nat->Nat->List (Nat × Nat)) (NN FL HT PT:Nat->Nat)
   (s:Nat) (zs:List (Nat × Nat)):Bool :=
 let zsc:=q186 gens (q72 shTT zs)
 zm (q75 salt zsc) fun h =>
 zm (q85 NN FL HT s h) fun j =>
 if Nat.beq j 999999 then false
 else
   zm (Nat.shiftRight (q192 (PT s) j) 23) fun aidx =>
   jk zsc (wx (aut aidx) (Rtt s j))
def bar (cfg:Cfg) (findFn:Nat->List (Nat × Nat)->Bool) (R:Nat->Nat->List (Nat × Nat)):Nat->Nat->Bool
 | 0,i => match R 0 i with
   | [(w,_)] => !(Nat.beq w cfg.goalv)
   | _ => true
 | s+1,i =>
   let ws:=R (Nat.add s 1) i
   !(scanAll cfg s ws fun zs =>
       !(findFn s zs)&&(Nat.beq s 0||scanInline cfg (Nat.sub s 1) zs))
def span (f:Nat->Bool):Nat->Nat->Bool
 | 0,_ => true
 | n+1,i => f i&&span f n (Nat.add i 1)
def q1 (n r:Nat):Fin n->Bool:=fun i => r.testBit i.val
def q146 {n:Nat} (x:Fin n->Bool):Nat :=
 (List.finRange n).foldr (fun i acc => if x i then acc|||(1 <<< i.val) else acc) 0
lemma qp {m:Nat} (hm:m≠0):(1:Nat).testBit m=false:=by
 cases m with
 | zero => contradiction
 | succ k => simp [Nat.testBit_succ]
lemma z7 {x m:Nat} (h:x.testBit m=true) :
   (x / 2 ^ m) % 2=1:=by
 rw [Nat.testBit_eq_decide_div_mod_eq] at h
 exact of_decide_eq_true h
lemma z5 {x m:Nat} (h:x.testBit m=false) :
   (x / 2 ^ m) % 2=0:=by
 rw [Nat.testBit_eq_decide_div_mod_eq] at h
 have:=of_decide_eq_false h
 omega
lemma zg {x m:Nat} (h:x.testBit m=true) : 2 ^ m<=x:=by
 have h1:=z7 h
 have h2 : 1<=x / 2 ^ m:=by generalize x / 2 ^ m=q at h1 ⊢;omega
 have h3:=Nat.mul_le_mul_right (2 ^ m) h2
 have h4:=Nat.div_mul_le_self x (2 ^ m)
 omega
lemma vz {y m:Nat} (h:y.testBit m=false) :
   y % 2 ^ (m+1) < 2 ^ m:=by
 have h0:(y / 2 ^ m) % 2=0:=z5 h
 have h1:y % 2 ^ (m+1) / 2 ^ m=(y / 2 ^ m) % 2:=by
   rw [Nat.pow_succ,Nat.mod_mul_right_div_self]
 have h2:y % 2 ^ (m+1) / 2 ^ m=0:=by rw [h1,h0]
 exact (Nat.div_eq_zero_iff.1 h2).resolve_left (Nat.ne_of_gt (n2P m))
lemma vk {y m:Nat} (h:y.testBit m=false) (k:Nat) :
   (y+2 ^ m).testBit k=if k=m then true else y.testBit k:=by
 by_cases hkm:k=m
 . subst hkm
   have h0:=z5 h
   rw [Nat.testBit_eq_decide_div_mod_eq,Nat.add_div_right _ (n2P k)]
   simp;omega
 . simp only [hkm,↓reduceIte]
   by_cases hlt:k < m
   . have hdv : 2 ^ m=2 ^ k*2 ^ (m - k):=by
       rw [← Nat.pow_add,Nat.add_sub_cancel' (le_of_lt hlt)]
     have hge : 1<=m - k:=by omega
     have hev : 2 ^ (m - k) % 2=0:=by
       obtain ⟨q,hq⟩:=Nat.exists_eq_add_of_le' hge
       rw [hq,Nat.pow_succ];omega
     rw [Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_eq_decide_div_mod_eq,hdv,
         Nat.mul_comm (2 ^ k),Nat.add_mul_div_right _ _ (n2P k)]
     have:(y / 2 ^ k+2 ^ (m - k)) % 2=(y / 2 ^ k) % 2:=by omega
     rw [this]
   . have hge:m+1<=k:=by omega
     have hrem:y % 2 ^ (m+1)+2 ^ m < 2 ^ (m+1):=by
       have hltm:=vz h
       have hpw : 2 ^ (m+1)=2 ^ m*2:=Nat.pow_succ 2 m
       omega
     have hdiv1:(y+2 ^ m) / 2 ^ (m+1)=y / 2 ^ (m+1):=by
       have hd:y=2 ^ (m+1)*(y / 2 ^ (m+1))+y % 2 ^ (m+1) :=
         (Nat.div_add_mod y (2 ^ (m+1))).symm
       conv_lhs => rw [hd,nAA]
       rw [Nat.mul_add_div (n2P (m+1)),Nat.div_eq_of_lt hrem,nAZ]
     have hpow : 2 ^ k=2 ^ (m+1)*2 ^ (k - (m+1)):=by
       rw [← Nat.pow_add,Nat.add_sub_cancel' hge]
     rw [Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_eq_decide_div_mod_eq,hpow,
         ← Nat.div_div_eq_div_mul,← Nat.div_div_eq_div_mul,hdiv1]
lemma qs {y m:Nat} (h:y.testBit m=false) :
   y+2 ^ m=y^^^2 ^ m:=by
 apply nEQ;intro k
 rw [vk h,nTX,Nat.testBit_two_pow]
 by_cases hkm:k=m
 . subst hkm;simp [h]
 . simp [hkm,Ne.symm hkm]
lemma jl {n:Nat} (x:Fin n->Bool) (k:Nat) :
   (q146 x).testBit k=if h:k < n then x ⟨k,h⟩ else false:=by
 have hgen:∀ (l:List (Fin n)),l.Nodup ->
     (l.foldr (fun i acc => if x i then acc|||(1 <<< i.val) else acc) 0).testBit k =
     if h:k < n then (if ⟨k,h⟩ ∈ l then x ⟨k,h⟩ else false) else false:=by
   intro l hnd
   induction l with
   | nil => simp
   | cons a t ih =>
     obtain ⟨hat,hndt⟩:=List.nodup_cons.1 hnd
     simp only [lFC]
     have iht:=ih hndt
     by_cases hxa:x a=true
     . simp only [hxa,↓reduceIte,nTO,Nat.testBit_shiftLeft,iht]
       by_cases hk:k < n
       . simp only [hk,↓reduceDIte,lMM]
         by_cases heq:(⟨k,hk⟩:Fin n)=a
         . subst heq;simp [hxa]
         . have hne:k≠a.val:=fun e => heq (Fin.ext e)
           have h0:(decide (a.val<=k)&&(1:Nat).testBit (k - a.val))=false:=by
             cases hle:decide (a.val<=k)
             . simp
             . have hle':a.val<=k:=of_decide_eq_true hle
               simp [qp (by omega:k - a.val≠0)]
           simp [heq,h0]
       . have hne:a.val < k:=by omega
         simp [hk,qp (by omega:k - a.val≠0)]
     . simp only [hxa,bFT,↓reduceIte,iht]
       by_cases hk:k < n
       . simp only [hk,↓reduceDIte,lMM]
         by_cases heq:(⟨k,hk⟩:Fin n)=a
         . rw [heq];simp [hat,hxa]
         . simp [heq]
       . simp [hk]
 have h:=hgen (List.finRange n) (List.nodup_finRange n)
 simpa [q146,List.mem_finRange] using h
lemma q178 {n:Nat} (x:Fin n->Bool):q146 x < 2 ^ n:=by
 apply Nat.lt_pow_two_of_testBit
 intro k hk
 rw [jl]
 simp [show ¬ k < n by omega]
lemma q57 {n:Nat} (x:Fin n->Bool):q1 n (q146 x)=x:=by
 funext i
 simp [q1,jl,i.isLt]
def encL {n:Nat} (rows:List Nat) (f:BFn n):Nat :=
 rows.foldr (fun r acc => acc*2+if f (q1 n r) then 1 else 0) 0
def encTT (n:Nat) (f:BFn n):Nat:=encL (List.range (2 ^ n)) f
lemma z8 {n:Nat} (rows:List Nat) (f:BFn n) (i:Nat) :
   (encL rows f).testBit i=match rows[i]? with | some r => f (q1 n r) | none => false:=by
 induction rows generalizing i with
 | nil => simp [encL]
 | cons r rest ih =>
   have hcons:encL (r::rest) f=encL rest f*2+if f (q1 n r) then 1 else 0:=rfl
   rw [hcons]
   cases i with
   | zero =>
     cases h:f (q1 n r) <;> simp [h,Nat.testBit_zero]
   | succ k =>
     rw [Nat.testBit_succ]
     have hd:(encL rest f*2+if f (q1 n r) then 1 else 0) / 2=encL rest f:=by
       cases h:f (q1 n r) <;> simp only [h,↓reduceIte,bFT] <;> omega
     rw [hd]
     exact ih k
lemma q39 {n:Nat} (rows:List Nat):encL (n:=n) rows (fun _ => false)=0:=by
 apply nEQ;intro i
 rw [z8];cases rows[i]? <;> simp
lemma q177 {n:Nat} (rows:List Nat):encL (n:=n) rows (fun _ => true)=2 ^ rows.length - 1:=by
 apply nEQ;intro i
 rw [z8,nTB]
 by_cases hi:i < rows.length
 . rw [List.getElem?_eq_getElem hi];simp [hi]
 . rw [List.getElem?_eq_none (by omega)];simp [hi]
lemma q160 {n:Nat} (rows:List Nat) (f:BFn n) :
   encL rows (invF f)=Nat.xor (encL rows f) (2 ^ rows.length - 1):=by
 apply nEQ;intro i
 rw [nXO,nTX,z8,z8,nTB]
 by_cases hi:i < rows.length
 . rw [List.getElem?_eq_getElem hi];simp [hi,invF]
 . rw [List.getElem?_eq_none (by omega)];simp [hi]
lemma q143 {n:Nat} (rows:List Nat) (f g:BFn n) :
   encL rows (meetF f g)=Nat.land (encL rows f) (encL rows g):=by
 apply nEQ;intro i
 rw [nLA,nTA,z8,z8,z8]
 cases rows[i]? <;> simp [meetF]
lemma q144 {n:Nat} (rows:List Nat) (f g:BFn n) :
   encL rows (joinF f g)=Nat.lor (encL rows f) (encL rows g):=by
 apply nEQ;intro i
 rw [nLO,nTO,z8,z8,z8]
 cases rows[i]? <;> simp [joinF]
lemma vr {n:Nat} (f:BFn n) (r:Nat) :
   (encTT n f).testBit r=if r < 2 ^ n then f (q1 n r) else false:=by
 unfold encTT;rw [z8]
 by_cases hr:r < 2 ^ n
 . rw [List.getElem?_eq_getElem (by simp [hr])];simp [hr]
 . rw [List.getElem?_eq_none (by simp;omega)];simp [hr]
lemma yc {n:Nat}:Function.Injective (encTT n):=by
 intro f g h
 funext x
 have h1:=congrArg (fun m => m.testBit (q146 x)) h
 rw [vr,vr] at h1
 simp only [q178 x,↓reduceIte,q57] at h1
 exact h1
lemma q116 {n:Nat} (pre:List Nat) (f:BFn n) :
   Nat.shiftRight (encL (pre++List.range (2 ^ n)) f) pre.length=encTT n f:=by
 apply nEQ;intro i
 change ((encL (pre++List.range (2 ^ n)) f) >>> pre.length).testBit i=(encTT n f).testBit i
 rw [Nat.shiftRight_eq_div_pow,Nat.testBit_div_two_pow,z8,vr]
 rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel]
 by_cases hi:i < 2 ^ n
 . rw [List.getElem?_eq_getElem (by simp [hi])];simp [hi]
 . rw [List.getElem?_eq_none (by simp;omega)];simp [hi]
lemma q89 {n:Nat} (pre:List Nat) :
   Function.Injective (encL (n:=n) (pre++List.range (2 ^ n))):=by
 intro f g h
 apply yc
 rw [← q116 pre f,← q116 pre g,h]
def yh {n:Nat} (i j:Fin n) (x:Fin n->Bool):Fin n->Bool :=
 fun k => x (if k=i then j else if k=j then i else k)
lemma q104 {n:Nat} (i j:Fin n) (x:Fin n->Bool) :
   yh i j (yh i j x)=x:=by
 funext k;unfold yh
 by_cases h1:k=i
 . rw [h1];by_cases h2:j=i <;> simp [h2]
 . by_cases h2:k=j
   . rw [h2];simp [Ne.symm h1]
   . simp [h1,h2]
def yu (i j r:Nat):Nat :=
 let bi:=r.testBit i
 let bj:=r.testBit j
 if bi==bj then r else Nat.xor r (Nat.lor (1 <<< i) (1 <<< j))
lemma q162 {n i j r:Nat} (hi:i < n) (hj:j < n) (hr:r < 2 ^ n) :
   yu i j r < 2 ^ n:=by
 unfold yu;dsimp only
 split
 . exact hr
 . apply Nat.lt_pow_two_of_testBit
   intro k hk
   rw [nXO,nTX,nLO,nTO,
       Nat.testBit_shiftLeft,Nat.testBit_shiftLeft]
   have hr0:r.testBit k=false:=Nat.testBit_lt_two_pow (lt_of_lt_of_le hr (Nat.pow_le_pow_right (by omega) hk))
   simp [hr0,qp (by omega:k - i≠0),qp (by omega:k - j≠0)]
lemma z9 {n i j r:Nat} (hi:i < n) (hj:j < n) :
   q1 n (yu i j r)=yh ⟨i,hi⟩ ⟨j,hj⟩ (q1 n r):=by
 funext k
 simp only [q1,yh,yu]
 by_cases heq:r.testBit i=r.testBit j
 . simp only [heq,beq_self_eq_true,↓reduceIte]
   by_cases hki:k=⟨i,hi⟩
   . rw [hki];simp [heq]
   . by_cases hkj:k=⟨j,hj⟩
     . rw [hkj];split <;> simp [heq]
     . simp [hki,hkj]
 . have hbeq:(r.testBit i==r.testBit j)=false:=beq_false_of_ne heq
   simp only [hbeq,bFT,↓reduceIte,nXO,nTX,nLO,
     nTO,Nat.testBit_shiftLeft]
   by_cases hki:k=⟨i,hi⟩
   . subst hki
     simp only [↓reduceIte,Nat.le_refl,decide_true,Nat.sub_self,Nat.testBit_one_zero]
     cases h1:r.testBit i <;> cases h2:r.testBit j <;> simp_all
   . by_cases hkj:k=⟨j,hj⟩
     . subst hkj
       simp only [hki,↓reduceIte,Nat.le_refl,decide_true,Nat.sub_self,Nat.testBit_one_zero]
       cases h1:r.testBit i <;> cases h2:r.testBit j <;> simp_all
     . have h1:k.val≠i:=fun e => hki (Fin.ext e)
       have h2:k.val≠j:=fun e => hkj (Fin.ext e)
       have hb:∀ m,k.val≠m->(decide (m<=k.val)&&(1:Nat).testBit (k.val - m))=false:=by
         intro m hne
         cases hle:decide (m<=k.val)
         . simp
         . have hle':m<=k.val:=of_decide_eq_true hle
           simp [qp (by omega:k.val - m≠0)]
       simp [hki,hkj,hb i h1,hb j h2]
def w9 (n i j:Nat):Nat × Nat × Nat × Nat :=
 let d:=2 ^ j - 2 ^ i
 let N:=2 ^ n
 let m01:=(List.range N).foldr (fun x acc => acc*2+if !(x.testBit i)&&x.testBit j then 1 else 0) 0
 let m10:=(List.range N).foldr (fun x acc => acc*2+if x.testBit i&&!(x.testBit j) then 1 else 0) 0
 let mEq:=(List.range N).foldr (fun x acc => acc*2+if x.testBit i==x.testBit j then 1 else 0) 0
 (d,m01,m10,mEq)
lemma jx (N:Nat) (P:Nat->Bool) (r:Nat) :
   ((List.range N).foldr (fun x acc => acc*2+if P x then 1 else 0) 0).testBit r =
   if r < N then P r else false:=by
 have hgen:∀ (l:List Nat) (r:Nat),
     (l.foldr (fun x acc => acc*2+if P x then 1 else 0) 0).testBit r =
     match l[r]? with | some x => P x | none => false:=by
   intro l
   induction l with
   | nil => intro r;simp
   | cons a t ih =>
     intro r;simp only [lFC]
     cases r with
     | zero => cases h:P a <;> simp [h,Nat.testBit_zero]
     | succ k =>
       rw [Nat.testBit_succ]
       have hd:((t.foldr (fun x acc => acc*2+if P x then 1 else 0) 0)*2+if P a then 1 else 0) / 2
           = t.foldr (fun x acc => acc*2+if P x then 1 else 0) 0:=by
         cases P a <;> simp only [↓reduceIte,bFT] <;> omega
       rw [hd];exact ih k
 rw [hgen]
 by_cases hr:r < N
 . rw [List.getElem?_eq_getElem (by simp [hr])];simp [hr]
 . rw [List.getElem?_eq_none (by simp;omega)];simp [hr]
lemma j3 {n i j:Nat} (hij:i < j) (hjn:j < n) (g:BFn n) :
   q76 (w9 n i j) (encTT n g) =
     encTT n (fun x => g (yh ⟨i,by omega⟩ ⟨j,hjn⟩ x)):=by
 have hi:i < n:=by omega
 have hpow : 2 ^ i < 2 ^ j:=Nat.pow_lt_pow_right (by omega) hij
 have hsub_bit:∀ x m,x.testBit m=true->x - 2 ^ m+2 ^ m=x/\(x - 2 ^ m).testBit m=false:=by
   intro x m hm
   have hle : 2 ^ m<=x:=zg hm
   refine ⟨Nat.sub_add_cancel hle,?_⟩
   rw [Nat.testBit_eq_decide_div_mod_eq]
   have hd:(x - 2 ^ m) / 2 ^ m=x / 2 ^ m - 1:=by
     have h1:x=(x - 2 ^ m)+2 ^ m:=(Nat.sub_add_cancel hle).symm
     have h2:((x - 2 ^ m)+2 ^ m) / 2 ^ m=(x - 2 ^ m) / 2 ^ m+1 :=
       Nat.add_div_right (x - 2 ^ m) (n2P m)
     rw [← h1] at h2;rw [h2];simp
   have hm1:=z7 hm
   rw [hd];simp;generalize x / 2 ^ m=q at hm1 ⊢;omega
 have hsw_val:∀ (a b:Nat),a < b->b < n->∀ x < 2 ^ n,
     (x.testBit a=false->x.testBit b=true->x - (2 ^ b - 2 ^ a)=yu a b x) /\
     (x.testBit a=true->x.testBit b=false->x+(2 ^ b - 2 ^ a)=yu a b x):=by
   intro a b hab hbn x _
   have hpa : 2 ^ a < 2 ^ b:=Nat.pow_lt_pow_right (by omega) hab
   have hsh:∀ (m k:Nat),(decide (m<=k)&&(1:Nat).testBit (k - m))=decide (m=k):=by
     intro m k
     by_cases hmk:m=k
     . subst hmk;simp
     . cases hle:decide (m<=k)
       . simp [hmk]
       . have hle':m<=k:=of_decide_eq_true hle
         simp [hmk,qp (by omega:k - m≠0)]
   constructor
   . intro ha0 hb1
     have ⟨hsub_eq,hsub0⟩:=hsub_bit x b hb1
     have hsub_a0:(x - 2 ^ b).testBit a=false:=by
       have h2:=qs hsub0
       rw [hsub_eq] at h2
       have htb:=congrArg (fun z => z.testBit a) h2
       rw [nTX,Nat.testBit_two_pow,ha0] at htb
       have hba:b≠a:=by omega
       simp [hba] at htb;exact htb
     have h2:x - (2 ^ b - 2 ^ a)=(x - 2 ^ b)+2 ^ a:=by
       conv_lhs => rw [← hsub_eq]
       rw [Nat.add_sub_assoc (Nat.sub_le _ _),Nat.sub_sub_self (le_of_lt hpa)]
     rw [h2]
     apply nEQ;intro k
     have h1:x=(x - 2 ^ b)^^^2 ^ b:=by rw [← qs hsub0,hsub_eq]
     have h3:(x - 2 ^ b)+2 ^ a=(x - 2 ^ b)^^^2 ^ a:=qs hsub_a0
     unfold yu;dsimp only
     simp only [ha0,hb1]
     change ((x - 2 ^ b)+2 ^ a).testBit k=(Nat.xor x (Nat.lor (1 <<< a) (1 <<< b))).testBit k
     rw [h3]
     conv_rhs => rw [h1]
     rw [nXO,nLO,nTX,nTX,nTX,
         nTO,Nat.testBit_shiftLeft,Nat.testBit_shiftLeft,Nat.testBit_two_pow,
         Nat.testBit_two_pow,hsh a k,hsh b k]
     by_cases hka:a=k <;> by_cases hkb:b=k <;> try omega
     . subst hka;simp [show b≠a by omega]
     . subst hkb;simp [show a≠b by omega]
     . simp [hka,hkb]
   . intro ha1 hb0
     have ⟨hsub_eq,hsub0⟩:=hsub_bit x a ha1
     have hsub_b0:(x - 2 ^ a).testBit b=false:=by
       have h2:=qs hsub0
       rw [hsub_eq] at h2
       have htb:=congrArg (fun z => z.testBit b) h2
       rw [nTX,Nat.testBit_two_pow,hb0] at htb
       have hab':a≠b:=by omega
       simp [hab'] at htb;exact htb
     have h2:x+(2 ^ b - 2 ^ a)=(x - 2 ^ a)+2 ^ b:=by
       conv_lhs => rw [← hsub_eq]
       rw [nAA,Nat.add_sub_cancel' (le_of_lt hpa)]
     rw [h2]
     apply nEQ;intro k
     have h1:x=(x - 2 ^ a)^^^2 ^ a:=by rw [← qs hsub0,hsub_eq]
     have h3:(x - 2 ^ a)+2 ^ b=(x - 2 ^ a)^^^2 ^ b:=qs hsub_b0
     unfold yu;dsimp only
     simp only [ha1,hb0]
     change ((x - 2 ^ a)+2 ^ b).testBit k=(Nat.xor x (Nat.lor (1 <<< a) (1 <<< b))).testBit k
     rw [h3]
     conv_rhs => rw [h1]
     rw [nXO,nLO,nTX,nTX,nTX,
         nTO,Nat.testBit_shiftLeft,Nat.testBit_shiftLeft,Nat.testBit_two_pow,
         Nat.testBit_two_pow,hsh a k,hsh b k]
     by_cases hka:a=k <;> by_cases hkb:b=k <;> try omega
     . subst hka;simp [show b≠a by omega]
     . subst hkb;simp [show a≠b by omega]
     . simp [hka,hkb]
 have hodd_ji:(2 ^ (j - i) - 1) % 2=1:=by
   have hge : 1<=j - i:=by omega
   have hev : 2 ^ (j - i) % 2=0:=by
     obtain ⟨m,hm⟩:=Nat.exists_eq_add_of_le' hge
     rw [hm,Nat.pow_succ];omega
   have hpos : 2<=2 ^ (j - i):=by
     have:=Nat.pow_le_pow_right (by omega : 0 < 2) hge;simpa using this
   omega
 have hflip_add_i:∀ r,(r+(2 ^ j - 2 ^ i)).testBit i=!(r.testBit i):=by
   intro r
   have hdv : 2 ^ j - 2 ^ i=2 ^ i*(2 ^ (j - i) - 1):=by
     rw [Nat.mul_sub,Nat.mul_one,← Nat.pow_add,Nat.add_sub_cancel' (le_of_lt hij)]
   have h1:(r+(2 ^ j - 2 ^ i)) / 2 ^ i=r / 2 ^ i+(2 ^ (j - i) - 1):=by
     rw [hdv,Nat.mul_comm,Nat.add_mul_div_right _ _ (n2P i)]
   rw [Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_eq_decide_div_mod_eq,h1]
   generalize r / 2 ^ i=q;generalize 2 ^ (j - i) - 1=c at hodd_ji ⊢
   cases hq:decide (q % 2=1)
   . have:q % 2=0:=by have:=of_decide_eq_false hq;omega
     simp;omega
   . have:q % 2=1:=of_decide_eq_true hq
     simp;omega
 have hflip_sub_i:∀ r,2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit i=!(r.testBit i):=by
   intro r hle
   have hdv : 2 ^ j - 2 ^ i=2 ^ i*(2 ^ (j - i) - 1):=by
     rw [Nat.mul_sub,Nat.mul_one,← Nat.pow_add,Nat.add_sub_cancel' (le_of_lt hij)]
   have h1:(r - (2 ^ j - 2 ^ i)) / 2 ^ i=r / 2 ^ i - (2 ^ (j - i) - 1):=by
     have h2:r=(r - (2 ^ j - 2 ^ i))+(2 ^ j - 2 ^ i):=(Nat.sub_add_cancel hle).symm
     have h3:((r - (2 ^ j - 2 ^ i))+2 ^ i*(2 ^ (j - i) - 1)) / 2 ^ i
         = (r - (2 ^ j - 2 ^ i)) / 2 ^ i+(2 ^ (j - i) - 1):=by
       rw [Nat.mul_comm (2 ^ i),Nat.add_mul_div_right _ _ (n2P i)]
     rw [← hdv,← h2] at h3;rw [h3,Nat.add_sub_cancel]
   have hle_div : 2 ^ (j - i) - 1<=r / 2 ^ i:=by
     rw [hdv] at hle
     exact (Nat.le_div_iff_mul_le (n2P i)).2 (by rw [Nat.mul_comm];exact hle)
   rw [Nat.testBit_eq_decide_div_mod_eq,Nat.testBit_eq_decide_div_mod_eq,h1]
   generalize r / 2 ^ i=q at hle_div ⊢;generalize 2 ^ (j - i) - 1=c at hodd_ji hle_div ⊢
   cases hq:decide (q % 2=1)
   . have:q % 2=0:=by have:=of_decide_eq_false hq;omega
     simp;omega
   . have:q % 2=1:=of_decide_eq_true hq
     simp;omega
 have hshl_tb:∀ (x d k:Nat),(Nat.shiftLeft x d).testBit k=(decide (d<=k)&&x.testBit (k - d)):=by
   intro x d k
   change (x <<< d).testBit k=_
   rw [Nat.testBit_shiftLeft]
 apply nEQ
 intro r
 unfold q76 w9
 simp only [nLO,nLA,Nat.shiftRight_eq,Nat.shiftRight_eq_div_pow,
   nTO,nTA,Nat.testBit_div_two_pow,hshl_tb,
   jx,vr]
 by_cases hr:r < 2 ^ n
 . simp only [hr,↓reduceIte]
   have hsw:=hsw_val i j hij hjn r hr
   cases hri:r.testBit i <;> cases hrj:r.testBit j
   ·
     have h00_eq:yh ⟨i,hi⟩ ⟨j,hjn⟩ (q1 n r)=q1 n r:=by
       rw [← z9 hi hjn];unfold yu;simp [hri,hrj]
     rw [h00_eq]
     have hmid:(r+(2 ^ j - 2 ^ i)).testBit i=true:=by rw [hflip_add_i,hri];rfl
     have hsub_i : 2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit i=true:=by
       intro hle;rw [hflip_sub_i r hle,hri];rfl
     have hsub_j : 2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit j=true:=by
       intro hle
       have h1:(r - (2 ^ j - 2 ^ i))+2 ^ j=r+2 ^ i:=by omega
       have hle_div : 1<=r / 2 ^ j:=by
         have hne0:r / 2 ^ j≠0:=by
           intro hz
           have hlt:r < 2 ^ j:=(Nat.div_eq_zero_iff.1 hz).resolve_left (Nat.ne_of_gt (n2P j))
           have hlt2:r - (2 ^ j - 2 ^ i) < 2 ^ i:=by omega
           have hbi:(r - (2 ^ j - 2 ^ i)).testBit i=false:=Nat.testBit_lt_two_pow hlt2
           have:=hsub_i hle;rw [hbi] at this;cases this
         generalize r / 2 ^ j=q at hne0 ⊢;omega
       have hsub_div:(r - (2 ^ j - 2 ^ i)) / 2 ^ j=r / 2 ^ j - 1:=by
         have h2:(r+2 ^ i) / 2 ^ j=r / 2 ^ j:=by
           have hrem:r % 2 ^ j+2 ^ i < 2 ^ j:=by
             have hm0:(r % 2 ^ j).testBit i=false:=by rw [Nat.testBit_mod_two_pow];simp [hij,hri]
             have hlt1:r % 2 ^ j < 2 ^ j:=Nat.mod_lt r (n2P j)
             apply Nat.lt_pow_two_of_testBit;intro k hk
             rw [vk hm0]
             have hne:k≠i:=by omega
             simp only [hne,↓reduceIte]
             exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt1 (Nat.pow_le_pow_right (by omega) hk))
           have hdiv:r=2 ^ j*(r / 2 ^ j)+r % 2 ^ j:=(Nat.div_add_mod r (2 ^ j)).symm
           conv_lhs => rw [hdiv,nAA]
           rw [Nat.mul_add_div (n2P j),Nat.div_eq_of_lt hrem,nAZ]
         have h3:((r - (2 ^ j - 2 ^ i))+2 ^ j) / 2 ^ j=(r - (2 ^ j - 2 ^ i)) / 2 ^ j+1 :=
           Nat.add_div_right _ (n2P j)
         rw [h1,h2] at h3;omega
       have hrj0:=z5 hrj
       rw [Nat.testBit_eq_decide_div_mod_eq,hsub_div];simp
       generalize r / 2 ^ j=q at hle_div hrj0 ⊢;omega
     have hterm1:((if r+(2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r+(2 ^ j - 2 ^ i))) else false) &&
         (if r+(2 ^ j - 2 ^ i) < 2 ^ n then !((r+(2 ^ j - 2 ^ i)).testBit i)&&(r+(2 ^ j - 2 ^ i)).testBit j else false))=false:=by
       split <;> simp [hmid]
     have hterm2:(decide (2 ^ j - 2 ^ i<=r) &&
         ((if r - (2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r - (2 ^ j - 2 ^ i))) else false) &&
          (if r - (2 ^ j - 2 ^ i) < 2 ^ n then (r - (2 ^ j - 2 ^ i)).testBit i&&!((r - (2 ^ j - 2 ^ i)).testBit j) else false)))=false:=by
       by_cases hle : 2 ^ j - 2 ^ i<=r
       . simp [hle,show r - (2 ^ j - 2 ^ i) < 2 ^ n by omega,hsub_j hle]
       . simp [hle]
     rw [hterm1,hterm2];simp
   ·
     have hle_j : 2 ^ j<=r:=zg hrj
     have hle : 2 ^ j - 2 ^ i<=r:=le_trans (Nat.sub_le _ _) hle_j
     have hsw_eq:r - (2 ^ j - 2 ^ i)=yu i j r:=hsw.1 hri hrj
     have hsw_lt:r - (2 ^ j - 2 ^ i) < 2 ^ n:=by omega
     have hsw_i:(r - (2 ^ j - 2 ^ i)).testBit i=true:=by
       rw [hsw_eq];have:=congrFun (z9 hi hjn (r:=r)) ⟨i,hi⟩
       simpa [q1,yh,hrj] using this
     have hsw_j:(r - (2 ^ j - 2 ^ i)).testBit j=false:=by
       rw [hsw_eq];have:=congrFun (z9 hi hjn (r:=r)) ⟨j,hjn⟩
       simpa [q1,yh,show (⟨j,hjn⟩:Fin n)≠⟨i,hi⟩ by intro e;have:=congrArg Fin.val e;simp at this;omega,hri] using this
     have hmid_i:(r+(2 ^ j - 2 ^ i)).testBit i=true:=by rw [hflip_add_i,hri];rfl
     have hterm1:((if r+(2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r+(2 ^ j - 2 ^ i))) else false) &&
         (if r+(2 ^ j - 2 ^ i) < 2 ^ n then !((r+(2 ^ j - 2 ^ i)).testBit i)&&(r+(2 ^ j - 2 ^ i)).testBit j else false))=false:=by
       split <;> simp [hmid_i]
     rw [hterm1]
     simp [hle,hsw_lt,hsw_i,hsw_j]
     rw [hsw_eq,z9 hi hjn]
   ·
     have hsw_eq:r+(2 ^ j - 2 ^ i)=yu i j r:=hsw.2 hri hrj
     have hsw_lt:r+(2 ^ j - 2 ^ i) < 2 ^ n:=by rw [hsw_eq];exact q162 hi hjn hr
     have hsw_i:(r+(2 ^ j - 2 ^ i)).testBit i=false:=by
       rw [hsw_eq];have:=congrFun (z9 hi hjn (r:=r)) ⟨i,hi⟩
       simpa [q1,yh,hrj] using this
     have hsw_j:(r+(2 ^ j - 2 ^ i)).testBit j=true:=by
       rw [hsw_eq];have:=congrFun (z9 hi hjn (r:=r)) ⟨j,hjn⟩
       simpa [q1,yh,show (⟨j,hjn⟩:Fin n)≠⟨i,hi⟩ by intro e;have:=congrArg Fin.val e;simp at this;omega,hri] using this
     have hsub_i : 2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit i=false:=by
       intro hle;rw [hflip_sub_i r hle,hri];rfl
     have hterm2:(decide (2 ^ j - 2 ^ i<=r) &&
         ((if r - (2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r - (2 ^ j - 2 ^ i))) else false) &&
          (if r - (2 ^ j - 2 ^ i) < 2 ^ n then (r - (2 ^ j - 2 ^ i)).testBit i&&!((r - (2 ^ j - 2 ^ i)).testBit j) else false)))=false:=by
       by_cases hle : 2 ^ j - 2 ^ i<=r
       . simp [hle,show r - (2 ^ j - 2 ^ i) < 2 ^ n by omega,hsub_i hle]
       . simp [hle]
     rw [hterm2]
     simp [hsw_lt,hsw_i,hsw_j]
     rw [hsw_eq,z9 hi hjn]
   ·
     have h11_eq:yh ⟨i,hi⟩ ⟨j,hjn⟩ (q1 n r)=q1 n r:=by
       rw [← z9 hi hjn];unfold yu;simp [hri,hrj]
     rw [h11_eq]
     have hmid_j:(r+(2 ^ j - 2 ^ i)).testBit j=false:=by
       have hle_i : 2 ^ i<=r:=zg hri
       have hsub_rem:(r - 2 ^ i) / 2 ^ j=r / 2 ^ j:=by
         have hm1:(r % 2 ^ j).testBit i=true:=by rw [Nat.testBit_mod_two_pow];simp [hij,hri]
         have hmod_i : 2 ^ i<=r % 2 ^ j:=zg hm1
         have hdiv:r=2 ^ j*(r / 2 ^ j)+r % 2 ^ j:=(Nat.div_add_mod r (2 ^ j)).symm
         have hsub:r - 2 ^ i=2 ^ j*(r / 2 ^ j)+(r % 2 ^ j - 2 ^ i):=by omega
         have hlt:r % 2 ^ j - 2 ^ i < 2 ^ j:=lt_of_le_of_lt (Nat.sub_le _ _) (Nat.mod_lt r (n2P j))
         rw [hsub,Nat.mul_add_div (n2P j),Nat.div_eq_of_lt hlt,nAZ]
       have h1:r+(2 ^ j - 2 ^ i)=(r - 2 ^ i)+2 ^ j:=by omega
       rw [Nat.testBit_eq_decide_div_mod_eq,h1,Nat.add_div_right _ (n2P j),hsub_rem]
       have hr1:=z7 hrj
       simp;omega
     have hsub_i : 2 ^ j - 2 ^ i<=r->(r - (2 ^ j - 2 ^ i)).testBit i=false:=by
       intro hle;rw [hflip_sub_i r hle,hri];rfl
     have hterm1:((if r+(2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r+(2 ^ j - 2 ^ i))) else false) &&
         (if r+(2 ^ j - 2 ^ i) < 2 ^ n then !((r+(2 ^ j - 2 ^ i)).testBit i)&&(r+(2 ^ j - 2 ^ i)).testBit j else false))=false:=by
       split <;> simp [hmid_j]
     have hterm2:(decide (2 ^ j - 2 ^ i<=r) &&
         ((if r - (2 ^ j - 2 ^ i) < 2 ^ n then g (q1 n (r - (2 ^ j - 2 ^ i))) else false) &&
          (if r - (2 ^ j - 2 ^ i) < 2 ^ n then (r - (2 ^ j - 2 ^ i)).testBit i&&!((r - (2 ^ j - 2 ^ i)).testBit j) else false)))=false:=by
       by_cases hle : 2 ^ j - 2 ^ i<=r
       . simp [hle,show r - (2 ^ j - 2 ^ i) < 2 ^ n by omega,hsub_i hle]
       . simp [hle]
     rw [hterm1,hterm2];simp
 ·
   have hge1 : ¬ (r+(2 ^ j - 2 ^ i) < 2 ^ n):=by omega
   simp only [hr,hge1,↓reduceIte,Bool.and_false,Bool.false_or]
   by_cases hle : 2 ^ j - 2 ^ i<=r
   . by_cases hlt2:r - (2 ^ j - 2 ^ i) < 2 ^ n
     . have hsub_j:(r - (2 ^ j - 2 ^ i)).testBit j=true:=by
         have hge_q : 2 ^ (n - j) - 1<=(r - (2 ^ j - 2 ^ i)) / 2 ^ j:=by
           have h1 : 2 ^ j*(2 ^ (n - j) - 1)=2 ^ n - 2 ^ j:=by
             rw [Nat.mul_sub,Nat.mul_one,← Nat.pow_add,Nat.add_sub_cancel' (le_of_lt hjn)]
           have h2 : 2 ^ n - 2 ^ j<=r - (2 ^ j - 2 ^ i) :=
             le_trans (Nat.sub_le_sub_left (Nat.sub_le _ _) _) (Nat.sub_le_sub_right (by omega : 2 ^ n<=r) _)
           exact (Nat.le_div_iff_mul_le (n2P j)).2 (by rw [Nat.mul_comm,h1];exact h2)
         have hlt_q:(r - (2 ^ j - 2 ^ i)) / 2 ^ j < 2 ^ (n - j):=by
           have h1 : 2 ^ n=2 ^ j*2 ^ (n - j):=by
             rw [← Nat.pow_add,Nat.add_sub_cancel' (le_of_lt hjn)]
           exact (Nat.div_lt_iff_lt_mul (n2P j)).2 (by rw [Nat.mul_comm,← h1];exact hlt2)
         have heq_q:(r - (2 ^ j - 2 ^ i)) / 2 ^ j=2 ^ (n - j) - 1:=by omega
         rw [Nat.testBit_eq_decide_div_mod_eq,heq_q]
         have hge1' : 1<=n - j:=by omega
         have hev : 2 ^ (n - j) % 2=0:=by
           obtain ⟨m,hm⟩:=Nat.exists_eq_add_of_le' hge1'
           rw [hm,Nat.pow_succ];omega
         have hpos : 2<=2 ^ (n - j):=by
           have:=Nat.pow_le_pow_right (by omega : 0 < 2) hge1';simpa using this
         simp;omega
       simp [hle,hlt2,hsub_j]
     . simp [hle,hlt2]
   . simp [hle]
def q163 (n:Nat) (ps:List (Nat × Nat)):List (Nat × Nat × Nat × Nat) :=
 ps.map fun p => w9 n p.1 p.2
def kq (n:Nat) (ps:List (Nat × Nat)):Bool :=
 ps.all fun p => decide (p.1 < p.2)&&decide (p.2 < n)
def zc {n:Nat}:List (Nat × Nat)->(Fin n->Bool)->(Fin n->Bool)
 | [],x => x
 | (i,j)::rest,x =>
   if h:i < n/\j < n then yh ⟨i,h.1⟩ ⟨j,h.2⟩ (zc rest x)
   else zc rest x
lemma wv {n:Nat} (ps:List (Nat × Nat)) (x:Fin n->Bool) :
   zc ps.reverse (zc ps x)=x:=by
 have hcomp:∀ (a b:List (Nat × Nat)) (y:Fin n->Bool),
     zc (a++b) y=zc a (zc b y):=by
   intro a;induction a with
   | nil => intro b y;rfl
   | cons p t ih =>
     intro b y;rcases p with ⟨i,j⟩
     simp only [lCA,zc];split <;> rw [ih]
 induction ps generalizing x with
 | nil => rfl
 | cons p t ih =>
   rcases p with ⟨i,j⟩
   simp only [lRC,hcomp,zc]
   split
   . rename_i h
     rw [q104,ih]
   . exact ih x
lemma jm {n:Nat} (ps:List (Nat × Nat)) (hv:kq n ps=true) (g:BFn n) :
   ym (q163 n ps) (encTT n g)=encTT n (fun x => g (zc ps x)):=by
 induction ps generalizing g with
 | nil => rfl
 | cons p rest ih =>
   rcases p with ⟨i,j⟩
   simp only [kq,List.all_cons,bAT,decide_eq_true_eq] at hv
   obtain ⟨⟨hij,hjn⟩,hrest⟩:=hv
   change ym (w9 n i j::q163 n rest) (encTT n g)=_
   simp only [ym]
   rw [j3 hij hjn g,ih hrest]
   congr 1;funext x
   have hlt:i < n/\j < n:=by omega
   simp only [zc]
   split
   . rfl
   . contradiction
def vh {n:Nat} (f:BFn n) (sws:List (Nat × Nat × Nat × Nat)):Prop :=
 ∃ π:(Fin n->Bool)->(Fin n->Bool),
   Function.Bijective π/\(∀ x,f (π x)=f x) /\
   ∀ g:BFn n,ym sws (encTT n g)=encTT n (fun x => g (π x))
lemma kw {n:Nat} (f:BFn n) (ps:List (Nat × Nat))
   (hv:kq n ps=true)
   (hfix:ym (q163 n ps) (encTT n f)=encTT n f) :
   vh f (q163 n ps):=by
 refine ⟨zc ps,?_,?_,fun g => jm ps hv g⟩
 . constructor
   . intro x y h
     have:=congrArg (zc ps.reverse) h
     simpa [wv] using this
   . intro y
     refine ⟨zc ps.reverse y,?_⟩
     have:=wv ps.reverse y
     simpa using this
 . intro x
   rw [jm ps hv f] at hfix
   exact congrFun (yc hfix) x
lemma q138 {n:Nat} (f:BFn n):vh f [] :=
 ⟨id,Function.bijective_id,fun _ => rfl,fun _ => rfl⟩
lemma wp {n:Nat} {f:BFn n} {s:Nat} {ws:List (BFn n × Nat)}
   (π:(Fin n->Bool)->(Fin n->Bool)) (hbij:Function.Bijective π) (hfix:∀ x,f (π x)=f x)
   (h:TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s ws) :
   TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s
     (ws.map fun p => ((fun x => p.1 (π x)),p.2)):=by
 let φ:BFn n->BFn n:=fun g x => g (π x)
 have hφ:Function.Injective φ:=by
   intro g1 g2 heq;funext y
   obtain ⟨x,rfl⟩:=hbij.2 y
   exact congrFun heq x
 exact @TagRun.map (BFn n) (BFn n) φ hφ
   invF meetF joinF (fun _ => false) (fun _ => true) f
   invF meetF joinF (fun _ => false) (fun _ => true) f
   rfl rfl (funext hfix) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) s ws h
def z6 (x i:Nat):Nat:=(x / 64 ^ i) % 64
lemma q185 (i:Nat) : 64 ^ i=2 ^ (6*i):=by
 rw [show (64:Nat)=2 ^ 6 by decide,← Nat.pow_mul]
lemma qo (x i k:Nat) :
   (z6 x i).testBit k=if k < 6 then x.testBit (6*i+k) else false:=by
 unfold z6
 rw [q185,show (64:Nat)=2 ^ 6 by decide,Nat.testBit_mod_two_pow,Nat.testBit_div_two_pow]
 by_cases hk:k < 6
 . simp [hk,nAC]
 . simp [hk]
lemma wg {x y:Nat} (h:∀ i,z6 x i=z6 y i):x=y:=by
 apply nEQ;intro k
 have h1:=congrArg (fun z => z.testBit (k % 6)) (h (k / 6))
 have hm:k % 6 < 6:=Nat.mod_lt k (by decide)
 rw [qo,qo] at h1
 simp only [hm,↓reduceIte,Nat.div_add_mod] at h1
 exact h1
lemma z1 (x i:Nat):z6 (x / 64) i=z6 x (i+1):=by
 unfold z6
 rw [Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm (64 ^ i) 64]
lemma q24:∀ {x y:Nat},(∀ i,z6 y i<=z6 x i)->y<=x:=by
 intro x y h
 induction hn:x+y using Nat.strong_induction_on generalizing x y with
 | _ n ih =>
   have h0:y % 64<=x % 64:=by simpa [z6] using h 0
   by_cases hq:x / 64+y / 64 < x+y
   . have hdiv:y / 64<=x / 64 :=
       ih (x / 64+y / 64) (by omega) (fun i => by rw [z1,z1];exact h (i+1)) rfl
     omega
   . omega
lemma q25 {x y:Nat} (h:∀ j,z6 x j+z6 y j < 64) (i:Nat) :
   z6 (x+y) i=z6 x i+z6 y i:=by
 induction i generalizing x y with
 | zero =>
   have h0:x % 64+y % 64 < 64:=by simpa [z6] using h 0
   simp only [z6,Nat.pow_zero,Nat.div_one]
   omega
 | succ i ih =>
   have h0:x % 64+y % 64 < 64:=by simpa [z6] using h 0
   have hdiv:(x+y) / 64=x / 64+y / 64:=by omega
   rw [← z1,hdiv,← z1,← z1]
   exact ih (fun j => by rw [z1,z1];exact h (j+1))
lemma q188 {x y:Nat} (h:∀ j,z6 y j<=z6 x j) (i:Nat) :
   z6 (x - y) i=z6 x i - z6 y i:=by
 induction i generalizing x y with
 | zero =>
   have h0:y % 64<=x % 64:=by simpa [z6] using h 0
   have hle:y<=x:=q24 h
   simp only [z6,Nat.pow_zero,Nat.div_one]
   omega
 | succ i ih =>
   have h0:y % 64<=x % 64:=by simpa [z6] using h 0
   have hle:y<=x:=q24 h
   have hdiv:(x - y) / 64=x / 64 - y / 64:=by omega
   rw [← z1,hdiv,← z1,← z1]
   exact ih (fun j => by rw [z1,z1];exact h (j+1))
lemma v9 (x y i:Nat):z6 (Nat.land x y) i=Nat.land (z6 x i) (z6 y i):=by
 apply nEQ;intro k
 rw [nLA,nLA,nTA,qo,qo,qo]
 by_cases hk:k < 6 <;> simp [hk,nTA]
lemma wb (x y i:Nat):z6 (Nat.lor x y) i=Nat.lor (z6 x i) (z6 y i):=by
 apply nEQ;intro k
 rw [nLO,nLO,nTO,qo,qo,qo]
 by_cases hk:k < 6 <;> simp [hk,nTO]
lemma q110 (x y i:Nat):z6 (Nat.xor x y) i=Nat.xor (z6 x i) (z6 y i):=by
 apply nEQ;intro k
 rw [nXO,nXO,nTX,qo,qo,qo]
 by_cases hk:k < 6 <;> simp [hk,nTX]
def qe (m val:Nat):Nat :=
 match m with
 | 0 => 0
 | m'+1 => val+64*qe m' val
lemma v0 (m val i:Nat) (hv:val < 64) :
   z6 (qe m val) i=if i < m then val else 0:=by
 induction m generalizing i with
 | zero => simp [qe,z6]
 | succ m ih =>
   cases i with
   | zero => simp only [qe,z6,Nat.pow_zero,Nat.div_one,Nat.zero_lt_succ,↓reduceIte];omega
   | succ k =>
     rw [← z1]
     have hd:qe (m+1) val / 64=qe m val:=by simp only [qe];omega
     rw [hd,ih k]
     by_cases h:k < m <;> simp [h,show k+1 < m+1 ↔ k < m by omega]
def v6 (a b c d e f:Bool):Nat :=
 let nd:=!d;let ne:=!e;let nf:=!f
 (if nd&&b then 1 else 0)+(if nd&&c then 1 else 0) +
 (if a&&ne then 1 else 0)+(if a&&nf then 1 else 0) -
 (if (a&&nd)&&((b||c)&&(ne||nf)) then 1 else 0)
def zq (a b c d e f:Bool):Nat :=
 max (v6 a b c d e f) (v6 (!a) (!b) (!c) (!d) (!e) (!f))
lemma q122:v6 true true true false false false=3:=by decide
lemma yr:∀ a b c d e f:Bool,v6 a b c d e f<=3:=by decide
lemma q52:∀ a b c d e f:Bool,zq a b c d e f<=3:=by decide
lemma k7:∀ a b c d e f:Bool,v6 a b c d e f<=zq a b c d e f:=by decide
lemma jp:∀ a b c d e f:Bool,zq (!a) (!b) (!c) (!d) (!e) (!f)=zq a b c d e f:=by decide
lemma w4:∀ a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2:Bool,
   v6 (a1||a2) (b1||b2) (c1||c2) (d1||d2) (e1||e2) (f1||f2) <=
     v6 a1 b1 c1 d1 e1 f1+v6 a2 b2 c2 d2 e2 f2:=by decide
lemma kl:∀ a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2:Bool,
   v6 (a1&&a2) (b1&&b2) (c1&&c2) (d1&&d2) (e1&&e2) (f1&&f2) <=
     v6 a1 b1 c1 d1 e1 f1+v6 a2 b2 c2 d2 e2 f2:=by decide
lemma q14 (a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2:Bool) :
   zq (a1||a2) (b1||b2) (c1||c2) (d1||d2) (e1||e2) (f1||f2) <=
     zq a1 b1 c1 d1 e1 f1+zq a2 b2 c2 d2 e2 f2:=by
 unfold zq
 have h1:=w4 a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2
 have h2:=kl (!a1) (!b1) (!c1) (!d1) (!e1) (!f1) (!a2) (!b2) (!c2) (!d2) (!e2) (!f2)
 simp only [Bool.not_or]
 omega
lemma je (a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2:Bool) :
   zq (a1&&a2) (b1&&b2) (c1&&c2) (d1&&d2) (e1&&e2) (f1&&f2) <=
     zq a1 b1 c1 d1 e1 f1+zq a2 b2 c2 d2 e2 f2:=by
 unfold zq
 have h1:=kl a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2
 have h2:=w4 (!a1) (!b1) (!c1) (!d1) (!e1) (!f1) (!a2) (!b2) (!c2) (!d2) (!e2) (!f2)
 simp only [Bool.not_and]
 omega
lemma wc (w s m i:Nat) :
   z6 (Nat.land (Nat.shiftRight w s) (qe m 1)) i =
     if i < m then (if w.testBit (6*i+s) then 1 else 0) else 0:=by
 rw [v9,v0 m 1 i (by decide)]
 by_cases hi:i < m
 . simp only [hi,↓reduceIte]
   apply nEQ;intro k
   rw [nLA,nTA,qo]
   cases k with
   | zero =>
     simp only [Nat.zero_lt_succ,↓reduceIte,nAZ,Nat.testBit_one_zero,bATR]
     change (w >>> s).testBit (6*i)=_
     rw [nTS,nAC s (6*i)]
     cases h:w.testBit (6*i+s) <;> simp [h]
   | succ k' =>
     rw [qp (by omega),Bool.and_false]
     cases w.testBit (6*i+s) <;> simp [qp (by omega:k'+1≠0)]
 . simp [hi,nLA]
lemma yy (m w0 i:Nat) :
   z6 (qi (qe m 1) w0) i =
     if i < m then
       v6 (w0.testBit (6*i)) (w0.testBit (6*i+1)) (w0.testBit (6*i+2))
               (w0.testBit (6*i+3)) (w0.testBit (6*i+4)) (w0.testBit (6*i+5))
     else 0:=by
 unfold qi
 simp only [v5]
 have hbit:∀ s j,z6 (Nat.land (Nat.shiftRight w0 s) (qe m 1)) j =
     if j < m then (if w0.testBit (6*j+s) then 1 else 0) else 0:=fun s j => wc w0 s m j
 have hbit0:∀ j,z6 (Nat.land w0 (qe m 1)) j =
     if j < m then (if w0.testBit (6*j) then 1 else 0) else 0:=fun j => by
   have:=hbit 0 j;simpa using this
 have hxor:∀ s j,z6 (Nat.xor (qe m 1) (Nat.land (Nat.shiftRight w0 s) (qe m 1))) j =
     if j < m then (if !(w0.testBit (6*j+s)) then 1 else 0) else 0:=by
   intro s j
   rw [q110,v0 m 1 j (by decide),hbit s j]
   by_cases hj:j < m
   . simp only [hj,↓reduceIte];cases w0.testBit (6*j+s) <;> decide
   . simp [hj]
 set a:=Nat.land w0 (qe m 1)
 set b:=Nat.land (Nat.shiftRight w0 1) (qe m 1)
 set c:=Nat.land (Nat.shiftRight w0 2) (qe m 1)
 set nd:=Nat.xor (qe m 1) (Nat.land (Nat.shiftRight w0 3) (qe m 1))
 set ne:=Nat.xor (qe m 1) (Nat.land (Nat.shiftRight w0 4) (qe m 1))
 set nf:=Nat.xor (qe m 1) (Nat.land (Nat.shiftRight w0 5) (qe m 1))
 have h_and_b:∀ bx by_:Bool,
     Nat.land (if bx then 1 else 0) (if by_ then 1 else 0)=if bx&&by_ then 1 else 0:=by
   intro bx by_;cases bx <;> cases by_ <;> decide
 have h_or_b:∀ bx by_:Bool,
     Nat.lor (if bx then 1 else 0) (if by_ then 1 else 0)=if bx||by_ then 1 else 0:=by
   intro bx by_;cases bx <;> cases by_ <;> decide
 have hL:∀ j,z6 (Nat.land nd b) j=if j < m then (if !(w0.testBit (6*j+3))&&w0.testBit (6*j+1) then 1 else 0) else 0:=by
   intro j;rw [v9,hxor 3 j,hbit 1 j];by_cases hj:j < m
   . simp only [hj,↓reduceIte];exact h_and_b _ _
   . simp [hj]
 have hL2:∀ j,z6 (Nat.land nd c) j=if j < m then (if !(w0.testBit (6*j+3))&&w0.testBit (6*j+2) then 1 else 0) else 0:=by
   intro j;rw [v9,hxor 3 j,hbit 2 j];by_cases hj:j < m
   . simp only [hj,↓reduceIte];exact h_and_b _ _
   . simp [hj]
 have hL3:∀ j,z6 (Nat.land a ne) j=if j < m then (if w0.testBit (6*j)&&!(w0.testBit (6*j+4)) then 1 else 0) else 0:=by
   intro j;rw [v9,hbit0 j,hxor 4 j];by_cases hj:j < m
   . simp only [hj,↓reduceIte];exact h_and_b _ _
   . simp [hj]
 have hL4:∀ j,z6 (Nat.land a nf) j=if j < m then (if w0.testBit (6*j)&&!(w0.testBit (6*j+5)) then 1 else 0) else 0:=by
   intro j;rw [v9,hbit0 j,hxor 5 j];by_cases hj:j < m
   . simp only [hj,↓reduceIte];exact h_and_b _ _
   . simp [hj]
 have hSub:∀ j,z6 (Nat.land (Nat.land a nd) (Nat.land (Nat.lor b c) (Nat.lor ne nf))) j =
     if j < m then (if (w0.testBit (6*j)&&!(w0.testBit (6*j+3))) &&
       ((w0.testBit (6*j+1)||w0.testBit (6*j+2)) &&
        (!(w0.testBit (6*j+4))||!(w0.testBit (6*j+5)))) then 1 else 0) else 0:=by
   intro j
   rw [v9 (Nat.land a nd),v9 a nd,v9 (Nat.lor b c),wb b c,wb ne nf,
       hbit0 j,hxor 3 j,hbit 1 j,hbit 2 j,hxor 4 j,hxor 5 j]
   by_cases hj:j < m
   . simp only [hj,↓reduceIte,h_and_b,h_or_b]
   . simp [hj]
 have hSum1:∀ j,z6 (Nat.add (Nat.land nd b) (Nat.land nd c)) j =
     z6 (Nat.land nd b) j+z6 (Nat.land nd c) j:=fun j =>
   q25 (fun l => by rw [hL l,hL2 l];by_cases hl:l < m <;> simp [hl] <;> split <;> split <;> omega) j
 have hSum2:∀ j,z6 (Nat.add (Nat.land a ne) (Nat.land a nf)) j =
     z6 (Nat.land a ne) j+z6 (Nat.land a nf) j:=fun j =>
   q25 (fun l => by rw [hL3 l,hL4 l];by_cases hl:l < m <;> simp [hl] <;> split <;> split <;> omega) j
 have hSumAll:∀ j,z6 (Nat.add (Nat.add (Nat.land nd b) (Nat.land nd c)) (Nat.add (Nat.land a ne) (Nat.land a nf))) j =
     z6 (Nat.land nd b) j+z6 (Nat.land nd c) j+(z6 (Nat.land a ne) j+z6 (Nat.land a nf) j):=by
   intro j
   have hlt:∀ l,z6 (Nat.add (Nat.land nd b) (Nat.land nd c)) l+z6 (Nat.add (Nat.land a ne) (Nat.land a nf)) l < 64:=by
     intro l;rw [hSum1 l,hSum2 l,hL l,hL2 l,hL3 l,hL4 l]
     by_cases hl:l < m <;> simp [hl] <;> split <;> split <;> split <;> split <;> omega
   change z6 (_+_) j=_
   rw [q25 hlt j,hSum1 j,hSum2 j]
 have hSubLe:∀ j,z6 (Nat.land (Nat.land a nd) (Nat.land (Nat.lor b c) (Nat.lor ne nf))) j <=
     z6 (Nat.add (Nat.add (Nat.land nd b) (Nat.land nd c)) (Nat.add (Nat.land a ne) (Nat.land a nf))) j:=by
   intro j;rw [hSumAll j,hSub j,hL j,hL2 j,hL3 j,hL4 j]
   by_cases hj:j < m
   . simp only [hj,↓reduceIte]
     cases w0.testBit (6*j) <;> cases w0.testBit (6*j+1) <;> cases w0.testBit (6*j+2) <;>
       cases w0.testBit (6*j+3) <;> cases w0.testBit (6*j+4) <;> cases w0.testBit (6*j+5) <;> decide
   . simp [hj]
 change z6 (_ - _) i=_
 rw [q188 hSubLe i,hSumAll i,hSub i,hL i,hL2 i,hL3 i,hL4 i]
 by_cases hi:i < m
 . simp only [hi,↓reduceIte,v6]
   omega
 . simp [hi]
lemma q51:∀ v1 v2:Nat,v1<=3->v2<=3 ->
   let u:=Nat.lor v1 v2
   let hi:=Nat.land u 2
   Nat.lor hi (Nat.lor (Nat.lor (Nat.land v1 (Nat.shiftRight v1 1)) (Nat.land v2 (Nat.shiftRight v2 1)))
                       (Nat.land (Nat.land u 1) (Nat.xor 1 (Nat.shiftRight hi 1))))=max v1 v2:=by
 intro v1 v2 h1 h2
 interval_cases v1 <;> interval_cases v2 <;> decide
lemma ya {v:Nat} (hv:∀ j,z6 v j<=3) (i:Nat) :
   z6 (Nat.land v (Nat.shiftRight v 1)) i=Nat.land (z6 v i) (Nat.shiftRight (z6 v i) 1):=by
 apply nEQ;intro k
 rw [nLA,nLA,nTA,qo,qo]
 by_cases hk:k < 6
 . simp only [hk,↓reduceIte,nTA]
   change (v.testBit (6*i+k)&&(v >>> 1).testBit (6*i+k)) =
     (v.testBit (6*i+k)&&((z6 v i) >>> 1).testBit k)
   rw [nTS,nTS,qo]
   by_cases hk5:k < 5
   . have hk1 : 1+k < 6:=by omega
     simp only [hk1,↓reduceIte]
     have : 1+(6*i+k)=6*i+(1+k):=by omega
     rw [this]
   . have hk_eq:k=5:=by omega
     subst hk_eq
     have hvi:z6 v i < 4:=by have:=hv i;omega
     have htb5:(z6 v i).testBit 5=false:=Nat.testBit_lt_two_pow (lt_of_lt_of_le hvi (by decide))
     rw [qo] at htb5
     simp only [show 5 < 6 by decide,↓reduceIte] at htb5
     simp [htb5]
 . simp [hk]
lemma jv {hi:Nat} (hhi:∀ j,z6 hi j=0\/z6 hi j=2) (i:Nat) :
   z6 (Nat.land (Nat.shiftRight hi 1) (qe m 1)) i =
     if i < m then Nat.shiftRight (z6 hi i) 1 else 0:=by
 rw [v9,v0 m 1 i (by decide)]
 by_cases hm:i < m
 . simp only [hm,↓reduceIte]
   apply nEQ;intro k
   rw [nLA,nTA,qo]
   cases k with
   | zero =>
     simp only [Nat.zero_lt_succ,↓reduceIte,nAZ,Nat.testBit_one_zero,bATR]
     change (hi >>> 1).testBit (6*i)=((z6 hi i) >>> 1).testBit 0
     rw [nTS,nTS,qo]
     simp [nAC]
   | succ k' =>
     rw [qp (by omega),Bool.and_false]
     rcases hhi i with h0 | h2
     . rw [h0];simp
     . rw [h2];change false=((2 >>> 1:Nat).testBit (k'+1));simp [qp (by omega:k'+1≠0)]
 . simp [hm,nLA]
lemma kh (sh1 m w i:Nat) :
   z6 (yg sh1 (qe m 1) (qe m 2) w) i =
     if i < m then
       zq (w.testBit (sh1+6*i)) (w.testBit (sh1+6*i+1)) (w.testBit (sh1+6*i+2))
               (w.testBit (sh1+6*i+3)) (w.testBit (sh1+6*i+4)) (w.testBit (sh1+6*i+5))
     else 0:=by
 unfold yg
 simp only [v5]
 set w0:=Nat.shiftRight w sh1
 have hw0:∀ k,w0.testBit k=w.testBit (sh1+k):=fun k => by
   change (w >>> sh1).testBit k=_;rw [nTS,nAC]
 set a:=Nat.land w0 (qe m 1)
 set b:=Nat.land (Nat.shiftRight w0 1) (qe m 1)
 set c:=Nat.land (Nat.shiftRight w0 2) (qe m 1)
 set d:=Nat.land (Nat.shiftRight w0 3) (qe m 1)
 set e:=Nat.land (Nat.shiftRight w0 4) (qe m 1)
 set f:=Nat.land (Nat.shiftRight w0 5) (qe m 1)
 set nd:=Nat.xor (qe m 1) d
 set ne:=Nat.xor (qe m 1) e
 set nf:=Nat.xor (qe m 1) f
 set na:=Nat.xor (qe m 1) a
 set nb:=Nat.xor (qe m 1) b
 set nc:=Nat.xor (qe m 1) c
 set v1:=Nat.sub (Nat.add (Nat.add (Nat.land nd b) (Nat.land nd c)) (Nat.add (Nat.land a ne) (Nat.land a nf)))
                   (Nat.land (Nat.land a nd) (Nat.land (Nat.lor b c) (Nat.lor ne nf)))
 set v2:=Nat.sub (Nat.add (Nat.add (Nat.land d nb) (Nat.land d nc)) (Nat.add (Nat.land na e) (Nat.land na f)))
                   (Nat.land (Nat.land na d) (Nat.land (Nat.lor nb nc) (Nat.lor e f)))
 have hv1_eq:v1=qi (qe m 1) w0:=by
   unfold qi;simp only [v5];rfl
 have hv1:∀ j,z6 v1 j=if j < m then
     v6 (w0.testBit (6*j)) (w0.testBit (6*j+1)) (w0.testBit (6*j+2))
             (w0.testBit (6*j+3)) (w0.testBit (6*j+4)) (w0.testBit (6*j+5)) else 0:=by
   intro j;rw [hv1_eq,yy]
 have hv2_eq:v2=qi (qe m 1) (Nat.xor w0 (2 ^ (6*m) - 1)):=by
   have hbit_inv:∀ s,s < 6->Nat.land (Nat.shiftRight (Nat.xor w0 (2 ^ (6*m) - 1)) s) (qe m 1) =
       Nat.xor (qe m 1) (Nat.land (Nat.shiftRight w0 s) (qe m 1)):=by
     intro s hs
     apply wg;intro j
     rw [wc,q110,v0 m 1 j (by decide),wc]
     by_cases hj:j < m
     . have hlt : 6*j+s < 6*m:=by omega
       simp only [hj,↓reduceIte,nXO,nTX,nTB,hlt,decide_true]
       cases w0.testBit (6*j+s) <;> decide
     . simp [hj]
   have hbit_inv0:Nat.land (Nat.xor w0 (2 ^ (6*m) - 1)) (qe m 1) =
       Nat.xor (qe m 1) (Nat.land w0 (qe m 1)):=by
     have:=hbit_inv 0 (by decide);simpa using this
   have hxor_inv:∀ x,Nat.xor (qe m 1) (Nat.xor (qe m 1) x)=x:=by
     intro x;apply nEQ;intro k
     rw [nXO,nXO,nTX,nTX]
     cases (qe m 1).testBit k <;> cases x.testBit k <;> decide
   unfold qi;simp only [v5]
   rw [hbit_inv0,hbit_inv 1 (by decide),hbit_inv 2 (by decide),
       hbit_inv 3 (by decide),hbit_inv 4 (by decide),hbit_inv 5 (by decide),
       hxor_inv,hxor_inv,hxor_inv]
 have hv2:∀ j,z6 v2 j=if j < m then
     v6 (!(w0.testBit (6*j))) (!(w0.testBit (6*j+1))) (!(w0.testBit (6*j+2)))
             (!(w0.testBit (6*j+3))) (!(w0.testBit (6*j+4))) (!(w0.testBit (6*j+5))) else 0:=by
   intro j;rw [hv2_eq,yy]
   by_cases hj:j < m
   . simp only [hj,↓reduceIte,nXO,nTX,nTB]
     simp only [show 6*j < 6*m by omega,show 6*j+1 < 6*m by omega,
       show 6*j+2 < 6*m by omega,show 6*j+3 < 6*m by omega,
       show 6*j+4 < 6*m by omega,show 6*j+5 < 6*m by omega,
       decide_true,bBT]
   . simp [hj]
 have hv1_le3:∀ j,z6 v1 j<=3:=fun j => by
   rw [hv1 j];split;exact yr _ _ _ _ _ _;omega
 have hv2_le3:∀ j,z6 v2 j<=3:=fun j => by
   rw [hv2 j];split;exact yr _ _ _ _ _ _;omega
 set u:=Nat.lor v1 v2
 set hi:=Nat.land u (qe m 2)
 have hhi_lane:∀ j,z6 hi j=if j < m then Nat.land (Nat.lor (z6 v1 j) (z6 v2 j)) 2 else 0:=by
   intro j;rw [v9,wb,v0 m 2 j (by decide)]
   by_cases hj:j < m <;> simp [hj,nLA]
 have hhi02:∀ j,z6 hi j=0\/z6 hi j=2:=by
   intro j;rw [hhi_lane j]
   split
   . have h1:=hv1_le3 j;have h2:=hv2_le3 j
     generalize z6 v1 j=x at h1;generalize z6 v2 j=y at h2
     interval_cases x <;> interval_cases y <;> decide
   . left;rfl
 have hlast:z6 (Nat.land (Nat.land u (qe m 1)) (Nat.xor (qe m 1) (Nat.shiftRight hi 1))) i =
     if i < m then Nat.land (Nat.land (Nat.lor (z6 v1 i) (z6 v2 i)) 1) (Nat.xor 1 (Nat.shiftRight (z6 hi i) 1)) else 0:=by
   have hrew:Nat.land (Nat.land u (qe m 1)) (Nat.xor (qe m 1) (Nat.shiftRight hi 1)) =
       Nat.land (Nat.land u (qe m 1)) (Nat.xor (qe m 1) (Nat.land (Nat.shiftRight hi 1) (qe m 1))):=by
     apply nEQ;intro k
     simp only [nLA,nXO,nTA,nTX]
     cases (qe m 1).testBit k <;> simp
   rw [hrew,v9,v9,wb,q110,v0 m 1 i (by decide),
       jv (m:=m) hhi02 i]
   by_cases hm:i < m <;> simp [hm,nLA]
 rw [wb,wb,wb,ya hv1_le3 i,
     ya hv2_le3 i,hlast,hhi_lane i]
 by_cases hm:i < m
 . simp only [hm,↓reduceIte]
   have hmain:=q51 (z6 v1 i) (z6 v2 i) (hv1_le3 i) (hv2_le3 i)
   simp only at hmain
   rw [hmain,hv1 i,hv2 i]
   simp only [hm,↓reduceIte,hw0,zq]
   have ha1:sh1+(6*i+1)=sh1+6*i+1:=by omega
   have ha2:sh1+(6*i+2)=sh1+6*i+2:=by omega
   have ha3:sh1+(6*i+3)=sh1+6*i+3:=by omega
   have ha4:sh1+(6*i+4)=sh1+6*i+4:=by omega
   have ha5:sh1+(6*i+5)=sh1+6*i+5:=by omega
   rw [ha1,ha2,ha3,ha4,ha5]
 . simp only [hm,↓reduceIte,hv1 i,hv2 i];decide
lemma q47 {α:Type} (f : α->Nat) (m:Nat)
   (hf:∀ x i,z6 (f x) i<=(if i < m then 3 else 0))
   (xs:List α) (hlen:xs.length<=11) (i:Nat) :
   z6 (xs.foldr (fun x acc => Nat.add (f x) acc) 0) i=(xs.map fun x => z6 (f x) i).sum /\
   (xs.map fun x => z6 (f x) i).sum<=if i < m then 3*xs.length else 0:=by
 induction xs generalizing i with
 | nil => simp [z6]
 | cons a t ih =>
   simp only [lLC] at hlen
   have ih_all:∀ j,z6 (t.foldr (fun x acc => Nat.add (f x) acc) 0) j =
       (t.map fun x => z6 (f x) j).sum /\
       (t.map fun x => z6 (f x) j).sum<=if j < m then 3*t.length else 0 :=
     fun j => ih (by omega) j
   have hlt:∀ j,z6 (f a) j+z6 (t.foldr (fun x acc => Nat.add (f x) acc) 0) j < 64:=by
     intro j
     have h1:=hf a j
     have ⟨h2,h3⟩:=ih_all j
     rw [h2]
     by_cases hj:j < m <;> simp only [hj,↓reduceIte] at h1 h3 <;> omega
   simp only [lFC,lMC,List.sum_cons,lLC]
   have hadd:=q25 hlt i
   have hfa:=hf a i
   have ⟨h2,h3⟩:=ih_all i
   refine ⟨?_,?_⟩
   . change z6 (_+_) i=_;rw [hadd,h2]
   . by_cases hi:i < m <;> simp only [hi,↓reduceIte] at hfa h3 ⊢ <;> omega
lemma ky (S m:Nat)
   (hS_bound:∀ i,z6 S i<=if i < m then 33 else 0)
   (hS_ge3:∀ i < m,3<=z6 S i) :
   Nat.beq (Nat.land (Nat.add S (qe m 29)) (qe m 32)) (qe m 32)=true:=by
 rw [Nat.beq_eq]
 apply wg;intro i
 have hlt:∀ j,z6 S j+z6 (qe m 29) j < 64:=by
   intro j;rw [v0 m 29 j (by decide)]
   have hb:=hS_bound j
   by_cases hj:j < m <;> simp only [hj,↓reduceIte] at hb ⊢ <;> omega
 rw [v9]
 change Nat.land (z6 (S+qe m 29) i) (z6 (qe m 32) i)=z6 (qe m 32) i
 rw [q25 hlt i,v0 m 29 i (by decide),v0 m 32 i (by decide)]
 by_cases hi:i < m
 . simp only [hi,↓reduceIte]
   have hb:=hS_bound i;simp only [hi,↓reduceIte] at hb
   have hge:=hS_ge3 i hi
   have h1 : 32<=z6 S i+29:=by omega
   have h2:z6 S i+29 < 64:=by omega
   generalize z6 S i+29=v at h1 h2
   interval_cases v <;> decide
 . simp [hi,nLA]
def j5 (rp:Nat):Nat->Nat->List Nat
 | 0,_ => []
 | m+1,idx => Nat.land (Nat.shiftRight rp (Nat.mul 7 idx)) 127::j5 rp m (Nat.add idx 1)
lemma q32 (rp m idx:Nat):(j5 rp m idx).length=m:=by
 induction m generalizing idx with
 | zero => rfl
 | succ m ih => simp [j5,ih]
def q106 (rp shTT:Nat):List Nat:=j5 rp shTT 0
def allRows (n rp shTT:Nat):List Nat:=q106 rp shTT++List.range (2 ^ n)
lemma jj (rp shTT:Nat):(q106 rp shTT).length=shTT :=
 q32 rp shTT 0
lemma zl (n rp shTT:Nat):(allRows n rp shTT).length=shTT+2 ^ n:=by
 simp [allRows,jj]
structure CfgOk (n:Nat) (f:BFn n) (rp:Nat) (c:Cfg):Prop where
 sh0_eq:c.sh0=2*c.k
 sh0_le:c.sh0<=c.sh1
 sh1_le:c.sh1<=c.shTT
 p0_dvd:(c.sh1 - c.sh0) % 6=0
 p1_dvd:(c.shTT - c.sh1) % 6=0
 all1v_eq:c.all1v=2 ^ (c.shTT+2 ^ n) - 1
 goalv_eq:c.goalv=encL (allRows n rp c.shTT) f
 lok_eq:c.lok=2 ^ c.k - 1
 m0all_eq:c.m0all=2 ^ (6*((c.sh1 - c.sh0) / 6)) - 1
 m0_eq:c.m0=qe ((c.sh1 - c.sh0) / 6) 1
 a29_0_eq:c.a29_0=qe ((c.sh1 - c.sh0) / 6) 29
 b5_0_eq:c.b5_0=qe ((c.sh1 - c.sh0) / 6) 32
 m1_eq:c.m1=qe ((c.shTT - c.sh1) / 6) 1
 m12_eq:c.m12=qe ((c.shTT - c.sh1) / 6) 2
 a29_1_eq:c.a29_1=qe ((c.shTT - c.sh1) / 6) 29
 b5_1_eq:c.b5_1=qe ((c.shTT - c.sh1) / 6) 32
 cov_ok:∀ i < c.k,
   f (q1 n ((allRows n rp c.shTT).getD i 0))=false /\
   f (q1 n ((allRows n rp c.shTT).getD (c.k+i) 0))=true
 p0_ok:∀ i < (c.sh1 - c.sh0) / 6,
   f (q1 n ((allRows n rp c.shTT).getD (c.sh0+6*i) 0))=true /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh0+6*i+1) 0))=true /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh0+6*i+2) 0))=true /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh0+6*i+3) 0))=false /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh0+6*i+4) 0))=false /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh0+6*i+5) 0))=false
 p1_ok:∀ i < (c.shTT - c.sh1) / 6,
   f (q1 n ((allRows n rp c.shTT).getD (c.sh1+6*i) 0))=true /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh1+6*i+1) 0))=true /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh1+6*i+2) 0))=true /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh1+6*i+3) 0))=false /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh1+6*i+4) 0))=false /\
   f (q1 n ((allRows n rp c.shTT).getD (c.sh1+6*i+5) 0))=false
def w3 (n:Nat) (f:BFn n) (rp:Nat) (c:Cfg):Bool :=
 let np0:=(c.sh1 - c.sh0) / 6
 let np1:=(c.shTT - c.sh1) / 6
 Nat.beq c.sh0 (2*c.k) &&
 Nat.ble c.sh0 c.sh1 &&
 Nat.ble c.sh1 c.shTT &&
 Nat.beq ((c.sh1 - c.sh0) % 6) 0 &&
 Nat.beq ((c.shTT - c.sh1) % 6) 0 &&
 Nat.beq c.all1v (2 ^ (c.shTT+2 ^ n) - 1) &&
 Nat.beq c.goalv (encL (allRows n rp c.shTT) f) &&
 Nat.beq c.lok (2 ^ c.k - 1) &&
 Nat.beq c.m0all (2 ^ (6*np0) - 1) &&
 Nat.beq c.m0 (qe np0 1) &&
 Nat.beq c.a29_0 (qe np0 29) &&
 Nat.beq c.b5_0 (qe np0 32) &&
 Nat.beq c.m1 (qe np1 1) &&
 Nat.beq c.m12 (qe np1 2) &&
 Nat.beq c.a29_1 (qe np1 29) &&
 Nat.beq c.b5_1 (qe np1 32) &&
 Nat.beq (Nat.land c.goalv c.lok) 0 &&
 Nat.beq (Nat.land (Nat.shiftRight c.goalv c.k) c.lok) c.lok &&
 Nat.beq (Nat.land (Nat.shiftRight c.goalv c.sh0) c.m0all) (qe np0 7) &&
 Nat.beq (Nat.land (Nat.shiftRight c.goalv c.sh1) (2 ^ (6*np1) - 1)) (qe np1 7)
lemma qm {n:Nat} (rows:List Nat) (f:BFn n) {idx:Nat} (h:idx < rows.length) :
   (encL rows f).testBit idx=f (q1 n (rows.getD idx 0)):=by
 rw [z8,List.getElem?_eq_getElem h,List.getD_eq_getElem _ _ h]
lemma jn (n:Nat) (f:BFn n) (rp:Nat) (c:Cfg)
   (h:w3 n f rp c=true):CfgOk n f rp c:=by
 unfold w3 at h
 simp only [bAT,Nat.beq_eq,Nat.ble_eq] at h
 rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsh0,h01⟩,h1t⟩,hp0d⟩,hp1d⟩,hall1⟩,hgoal⟩,hlok⟩,hm0all⟩,
   hm0⟩,ha29_0⟩,hb5_0⟩,hm1⟩,hm12⟩,ha29_1⟩,hb5_1⟩,hcov0⟩,hcov1⟩,hp0m⟩,hp1m⟩
 have hlen:(allRows n rp c.shTT).length=c.shTT+2 ^ n:=zl n rp c.shTT
 have hbit_goal:∀ idx < c.shTT,c.goalv.testBit idx=f (q1 n ((allRows n rp c.shTT).getD idx 0)):=by
   intro idx hidx
   rw [hgoal,qm _ _ (by rw [hlen];exact Nat.lt_add_right (2 ^ n) hidx)]
 have hlane7:∀ (sh m:Nat),sh+6*m<=c.shTT ->
     Nat.land (Nat.shiftRight c.goalv sh) (2 ^ (6*m) - 1)=qe m 7 ->
     ∀ i < m,
       f (q1 n ((allRows n rp c.shTT).getD (sh+6*i) 0))=true /\
       f (q1 n ((allRows n rp c.shTT).getD (sh+6*i+1) 0))=true /\
       f (q1 n ((allRows n rp c.shTT).getD (sh+6*i+2) 0))=true /\
       f (q1 n ((allRows n rp c.shTT).getD (sh+6*i+3) 0))=false /\
       f (q1 n ((allRows n rp c.shTT).getD (sh+6*i+4) 0))=false /\
       f (q1 n ((allRows n rp c.shTT).getD (sh+6*i+5) 0))=false:=by
   intro sh m hbound heq i hi
   have htb:∀ off < 6,f (q1 n ((allRows n rp c.shTT).getD (sh+6*i+off) 0))=(7:Nat).testBit off:=by
     intro off hoff
     have h1:=congrArg (fun z => z6 z i) heq
     rw [v0 m 7 i (by decide)] at h1
     simp only [hi,↓reduceIte] at h1
     have h2:=congrArg (fun z => z.testBit off) h1
     rw [qo] at h2
     simp only [hoff,↓reduceIte,nLA,nTA,nTB,
       show 6*i+off < 6*m by omega,decide_true,bATR] at h2
     change (c.goalv >>> sh).testBit (6*i+off)=_ at h2
     rw [nTS,← nAA] at h2
     rw [← hbit_goal (sh+6*i+off) (by omega)]
     exact h2
   exact ⟨by simpa using htb 0 (by decide),htb 1 (by decide),htb 2 (by decide),
          htb 3 (by decide),htb 4 (by decide),htb 5 (by decide)⟩
 refine ⟨hsh0,h01,h1t,hp0d,hp1d,hall1,hgoal,hlok,hm0all,hm0,ha29_0,hb5_0,hm1,hm12,ha29_1,hb5_1,?_,?_,?_⟩
 . intro i hi
   constructor
   . have h1:=congrArg (fun z => z.testBit i) hcov0
     rw [nLA,nTA,hlok,nTB,nZT] at h1
     simp only [hi,decide_true,bATR] at h1
     rw [← hbit_goal i (by omega)];exact h1
   . have h1:=congrArg (fun z => z.testBit i) hcov1
     rw [nLA,nTA,hlok,nTB] at h1
     simp only [hi,decide_true,bATR] at h1
     change (c.goalv >>> c.k).testBit i=true at h1
     rw [nTS] at h1
     rw [← hbit_goal (c.k+i) (by omega)];exact h1
 . apply hlane7 c.sh0 ((c.sh1 - c.sh0) / 6) (by omega)
   rw [← hm0all];exact hp0m
 . apply hlane7 c.sh1 ((c.shTT - c.sh1) / 6) (by omega) hp1m
def AllTagsLe3 {α:Type} (ws:List (α × Nat)):Prop:=∀ p ∈ ws,p.2<=3
lemma AllTagsLe3.perm {α:Type} {xs ys:List (α × Nat)} (hp:xs.Perm ys)
   (h:AllTagsLe3 xs):AllTagsLe3 ys :=
 fun p hm => h p (hp.symm.subset hm)
lemma TagRun.inv_zero {α:Type} {inv : α->α} {meet join : α->α->α} {zero one goal : α}
   {ws:List (α × Nat)} (h:TagRun inv meet join zero one goal 0 ws) :
   ∃ tg,ws=[(goal,tg)]:=by
 generalize hs:(0:Nat)=s at h
 induction h with
 | done tg => exact ⟨tg,rfl⟩
 | perm hp _ ih =>
   obtain ⟨tg,rfl⟩:=ih hs
   exact ⟨tg,List.perm_singleton.1 hp.symm⟩
 | uNot _ _ _ _ _ _ _ _ _ => cases hs
 | bOr _ _ _ _ _ _ _ _ _ _ _ _ => cases hs
 | bAnd _ _ _ _ _ _ _ _ _ _ _ _ => cases hs
lemma TagRun.inv_succ {α:Type} {inv : α->α} {meet join : α->α->α} {zero one goal : α}
   {s:Nat} {ws:List (α × Nat)} (h:TagRun inv meet join zero one goal (s+1) ws) :
   (∃ a ta r save,ws.Perm ((a,ta)::r) /\
     ta≠1/\ta≠2/\(ta=3->save=false) /\
     inv a≠zero/\inv a≠one/\inv a≠a/\(∀ x ∈ r,x.1≠inv a) /\
     TagRun inv meet join zero one goal s ((inv a,if ta=3 then 2 else 0)::qk save (a,0) r)) \/
   (∃ a ta b tb r ka kb,ws.Perm ((a,ta)::(b,tb)::r) /\
     ta≠2/\tb≠2/\(ta=1->ka=false)/\(tb=1->kb=false) /\
     join a b≠zero/\join a b≠one/\join a b≠a/\join a b≠b/\(∀ x ∈ r,x.1≠join a b) /\
     TagRun inv meet join zero one goal s
       ((join a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r))) \/
   (∃ a ta b tb r ka kb,ws.Perm ((a,ta)::(b,tb)::r) /\
     ta≠1/\tb≠1/\(ta≠0->ka=false)/\(tb≠0->kb=false) /\
     meet a b≠zero/\meet a b≠one/\meet a b≠a/\meet a b≠b/\(∀ x ∈ r,x.1≠meet a b) /\
     TagRun inv meet join zero one goal s
       ((meet a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r))):=by
 generalize hs:s+1=s' at h
 induction h with
 | done _ => cases hs
 | perm hp _ ih =>
   rcases ih hs with ⟨a,ta,r,save,hp',rest⟩ | ⟨a,ta,b,tb,r,ka,kb,hp',rest⟩ | ⟨a,ta,b,tb,r,ka,kb,hp',rest⟩
   . exact Or.inl ⟨a,ta,r,save,hp.symm.trans hp',rest⟩
   . exact Or.inr (Or.inl ⟨a,ta,b,tb,r,ka,kb,hp.symm.trans hp',rest⟩)
   . exact Or.inr (Or.inr ⟨a,ta,b,tb,r,ka,kb,hp.symm.trans hp',rest⟩)
 | @uNot s0 a ta r save h1 h2 h3 h4 h5 h6 h7 hsub _ =>
   cases hs
   exact Or.inl ⟨a,ta,r,save,lPR _,h1,h2,h3,h4,h5,h6,h7,hsub⟩
 | @bOr s0 a ta b tb r ka kb h1 h2 h3 h4 h5 h6 h7 h8 h9 hsub _ =>
   cases hs
   exact Or.inr (Or.inl ⟨a,ta,b,tb,r,ka,kb,lPR _,h1,h2,h3,h4,h5,h6,h7,h8,h9,hsub⟩)
 | @bAnd s0 a ta b tb r ka kb h1 h2 h3 h4 h5 h6 h7 h8 h9 hsub _ =>
   cases hs
   exact Or.inr (Or.inr ⟨a,ta,b,tb,r,ka,kb,lPR _,h1,h2,h3,h4,h5,h6,h7,h8,h9,hsub⟩)
lemma q68 {α:Type} {ws:List α} {a : α} {r:List α} (hp:ws.Perm (a::r)) :
   ∃ pre suf,ws=pre++a::suf/\r.Perm (pre++suf):=by
 have hmem:a ∈ ws:=hp.symm.subset (by simp)
 obtain ⟨pre,suf,hws⟩:=List.append_of_mem hmem
 refine ⟨pre,suf,hws,?_⟩
 rw [hws] at hp
 exact (List.perm_cons a).1 (hp.symm.trans lPM)
lemma q67 {α:Type} {ws:List α} {a b : α} {r:List α} (hp:ws.Perm (a::b::r)) :
   (∃ pre mid suf,ws=pre++a::mid++b::suf/\r.Perm (pre++mid++suf)) \/
   (∃ pre mid suf,ws=pre++b::mid++a::suf/\r.Perm (pre++mid++suf)):=by
 obtain ⟨p1,s1,hws,hbr⟩:=q68 hp
 have hmem:b ∈ p1++s1:=hbr.subset (by simp)
 rcases List.mem_append.1 hmem with hbp | hbs
 . obtain ⟨pre,mid,hp1⟩:=List.append_of_mem hbp
   right
   refine ⟨pre,mid,s1,by rw [hws,hp1,lAA,lCA],?_⟩
   rw [hp1,lAA] at hbr
   have hmid:(pre++b::(mid++s1)).Perm (b::(pre++(mid++s1))):=lPM
   have h1:=(List.perm_cons b).1 (hbr.trans hmid)
   simpa [lAA] using h1
 . obtain ⟨mid,suf,hs1⟩:=List.append_of_mem hbs
   left
   refine ⟨p1,mid,suf,by simp [hws,hs1,lAA],?_⟩
   rw [hs1] at hbr
   have hmid:((p1++mid)++b::suf).Perm (b::((p1++mid)++suf)):=lPM
   rw [← lAA] at hbr
   exact (List.perm_cons b).1 (hbr.trans hmid)
lemma z4 {α:Type} (k:Bool) (a : α) (r:List α) (x : α) :
   x ∈ qk k a r ↔ (k=true/\x=a)\/x ∈ r:=by
 cases k <;> simp [qk]
lemma yd {n:Nat} {f:BFn n} {s:Nat} {ws:List (BFn n × Nat)}
   (h:TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s ws)
   (u v:Fin n->Bool) (hu:f u=false) (hv:f v=true) :
   ∃ p ∈ ws,p.1 u≠p.1 v:=by
 induction h with
 | done tg => exact ⟨(f,tg),by simp,by simp [hu,hv]⟩
 | perm hp _ ih =>
   obtain ⟨p,hm,hne⟩:=ih
   exact ⟨p,hp.subset hm,hne⟩
 | @uNot s a ta r save _ _ _ _ _ _ _ _ ih =>
   obtain ⟨p,hm,hne⟩:=ih
   rcases List.mem_cons.1 hm with rfl | hm2
   . exact ⟨(a,ta),by simp,fun e => hne (by dsimp only at e;simp [invF,e])⟩
   . rcases (z4 _ _ _ _).1 hm2 with ⟨_,rfl⟩ | hm3
     . exact ⟨(a,ta),by simp,hne⟩
     . exact ⟨p,by simp [hm3],hne⟩
 | @bOr s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ ih =>
   obtain ⟨p,hm,hne⟩:=ih
   rcases List.mem_cons.1 hm with rfl | hm2
   . by_cases ha:a u=a v
     . exact ⟨(b,tb),by simp,fun hb => hne (by dsimp only at hb;simp [joinF,ha,hb])⟩
     . exact ⟨(a,ta),by simp,ha⟩
   . rcases (z4 _ _ _ _).1 hm2 with ⟨_,rfl⟩ | hm3
     . exact ⟨(a,ta),by simp,hne⟩
     . rcases (z4 _ _ _ _).1 hm3 with ⟨_,rfl⟩ | hm4
       . exact ⟨(b,tb),by simp,hne⟩
       . exact ⟨p,by simp [hm4],hne⟩
 | @bAnd s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ _ ih =>
   obtain ⟨p,hm,hne⟩:=ih
   rcases List.mem_cons.1 hm with rfl | hm2
   . by_cases ha:a u=a v
     . exact ⟨(b,tb),by simp,fun hb => hne (by dsimp only at hb;simp [meetF,ha,hb])⟩
     . exact ⟨(a,ta),by simp,ha⟩
   . rcases (z4 _ _ _ _).1 hm2 with ⟨_,rfl⟩ | hm3
     . exact ⟨(a,ta),by simp,hne⟩
     . rcases (z4 _ _ _ _).1 hm3 with ⟨_,rfl⟩ | hm4
       . exact ⟨(b,tb),by simp,hne⟩
       . exact ⟨p,by simp [hm4],hne⟩
lemma zk {n:Nat} {a b:BFn n} {ta tb t0 t1 t2:Nat} {r:List (BFn n × Nat)}
   {ka kb:Bool} {u v:Fin n->Bool}
   (h:∃ p ∈ (joinF a b,t0)::qk ka (a,t1) (qk kb (b,t2) r),p.1 u=false/\p.1 v=true) :
   ∃ p ∈ (a,ta)::(b,tb)::r,p.1 u=false/\p.1 v=true:=by
 obtain ⟨p,hm,hu,hv⟩:=h
 rcases List.mem_cons.1 hm with rfl | hm2
 . simp only [joinF,Bool.or_eq_false_iff,bOT] at hu hv
   rcases hv with hva | hvb
   . exact ⟨(a,ta),by simp,hu.1,hva⟩
   . exact ⟨(b,tb),by simp,hu.2,hvb⟩
 . rcases (z4 _ _ _ _).1 hm2 with ⟨_,rfl⟩ | hm3
   . exact ⟨(a,ta),by simp,hu,hv⟩
   . rcases (z4 _ _ _ _).1 hm3 with ⟨_,rfl⟩ | hm4
     . exact ⟨(b,tb),by simp,hu,hv⟩
     . exact ⟨p,by simp [hm4],hu,hv⟩
lemma za {n:Nat} {a b:BFn n} {ta tb t0 t1 t2:Nat} {r:List (BFn n × Nat)}
   {ka kb:Bool} {u v:Fin n->Bool}
   (h:∃ p ∈ (meetF a b,t0)::qk ka (a,t1) (qk kb (b,t2) r),p.1 u=false/\p.1 v=true) :
   ∃ p ∈ (a,ta)::(b,tb)::r,p.1 u=false/\p.1 v=true:=by
 obtain ⟨p,hm,hu,hv⟩:=h
 rcases List.mem_cons.1 hm with rfl | hm2
 . simp only [meetF,Bool.and_eq_false_iff,bAT] at hu hv
   rcases hu with hua | hub
   . exact ⟨(a,ta),by simp,hua,hv.1⟩
   . exact ⟨(b,tb),by simp,hub,hv.2⟩
 . rcases (z4 _ _ _ _).1 hm2 with ⟨_,rfl⟩ | hm3
   . exact ⟨(a,ta),by simp,hu,hv⟩
   . rcases (z4 _ _ _ _).1 hm3 with ⟨_,rfl⟩ | hm4
     . exact ⟨(b,tb),by simp,hu,hv⟩
     . exact ⟨p,by simp [hm4],hu,hv⟩
lemma qf {n:Nat} {f:BFn n} {s:Nat} {ws:List (BFn n × Nat)}
   (h:TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s ws)
   (hlen:ws.length=s+1) :
   ∀ u v:Fin n->Bool,f u=false->f v=true->∃ p ∈ ws,p.1 u=false/\p.1 v=true:=by
 induction h with
 | done tg => intro u v hu hv;exact ⟨(f,tg),by simp,hu,hv⟩
 | perm hp _ ih =>
   intro u v hu hv
   obtain ⟨p,hm,h1,h2⟩:=ih (by rw [hp.length_eq];exact hlen) u v hu hv
   exact ⟨p,hp.subset hm,h1,h2⟩
 | @uNot s a ta r save _ _ _ _ _ _ _ hsub _ =>
   have hle:=hsub.len_le
   cases save <;> simp [qk] at hlen hle <;> omega
 | @bOr s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ hsub ih =>
   have hle:=hsub.len_le
   cases ka <;> cases kb <;> simp [qk] at hlen hle <;> try omega
   intro u v hu hv
   exact zk (ka:=false) (kb:=false) (ih (by simp [qk];omega) u v hu hv)
 | @bAnd s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ hsub ih =>
   have hle:=hsub.len_le
   cases ka <;> cases kb <;> simp [qk] at hlen hle <;> try omega
   intro u v hu hv
   exact za (ka:=false) (kb:=false) (ih (by simp [qk];omega) u v hu hv)
lemma kk {n:Nat} {f:BFn n} {s:Nat} {ws:List (BFn n × Nat)}
   (h:TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s ws)
   (hlen:ws.length=s+1)
   (r0 r1 r2 r3 r4 r5:Fin n->Bool)
   (h0:f r0=true) (h1:f r1=true) (h2:f r2=true)
   (h3:f r3=false) (h4:f r4=false) (h5:f r5=false) :
   3<=(ws.map fun p => v6 (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum:=by
 induction h with
 | done tg => simp [h0,h1,h2,h3,h4,h5,q122]
 | perm hp _ ih =>
   rw [← (hp.map _).sum_eq]
   exact ih (by rw [hp.length_eq];exact hlen)
 | @uNot s a ta r save _ _ _ _ _ _ _ hsub _ =>
   have hle:=hsub.len_le
   cases save <;> simp [qk] at hlen hle <;> omega
 | @bOr s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ hsub ih =>
   have hle:=hsub.len_le
   cases ka <;> cases kb <;> simp [qk] at hlen hle <;> try omega
   have hih:=ih (by simp [qk];omega)
   simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,joinF] at hih ⊢
   have hsub6:=w4 (a r0) (a r1) (a r2) (a r3) (a r4) (a r5)
     (b r0) (b r1) (b r2) (b r3) (b r4) (b r5)
   omega
 | @bAnd s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ hsub ih =>
   have hle:=hsub.len_le
   cases ka <;> cases kb <;> simp [qk] at hlen hle <;> try omega
   have hih:=ih (by simp [qk];omega)
   simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,meetF] at hih ⊢
   have hsub6:=kl (a r0) (a r1) (a r2) (a r3) (a r4) (a r5)
     (b r0) (b r1) (b r2) (b r3) (b r4) (b r5)
   omega
lemma qh {n:Nat} {f:BFn n} {s:Nat} {ws:List (BFn n × Nat)}
   (h:TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f s ws)
   (hlen:ws.length=s) :
   (∀ u v:Fin n->Bool,f u=false->f v=true->∃ p ∈ ws,p.1 u=false/\p.1 v=true) \/
   (∀ r0 r1 r2 r3 r4 r5:Fin n->Bool,
     f r0=true->f r1=true->f r2=true->f r3=false->f r4=false->f r5=false ->
     3<=(ws.map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum):=by
 induction h with
 | done tg => simp at hlen
 | perm hp _ ih =>
   rcases ih (by rw [hp.length_eq];exact hlen) with hcov | hsym
   . left;intro u v hu hv
     obtain ⟨p,hm,h1,h2⟩:=hcov u v hu hv
     exact ⟨p,hp.subset hm,h1,h2⟩
   . right;intro r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
     rw [← (hp.map _).sum_eq]
     exact hsym r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
 | @uNot s a ta r save _ _ _ _ _ _ _ hsub _ =>
   have hle:=hsub.len_le
   cases save
   . right
     intro r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
     have hv:=kk hsub (by simp [qk] at hlen ⊢;omega) r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
     have hle_s:∀ l:List (BFn n × Nat),
         (l.map fun p => v6 (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum <=
         (l.map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum:=by
       intro l;induction l with
       | nil => simp
       | cons x t iht =>
         simp only [lMC,List.sum_cons]
         have:=k7 (x.1 r0) (x.1 r1) (x.1 r2) (x.1 r3) (x.1 r4) (x.1 r5)
         omega
     have hs:=le_trans hv (hle_s _)
     simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,invF,jp] at hs ⊢
     exact hs
   . simp [qk] at hlen hle;omega
 | @bOr s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ hsub ih =>
   have hle:=hsub.len_le
   cases ka <;> cases kb
   . rcases ih (by simp [qk] at hlen ⊢;omega) with hcov | hsym
     . left;intro u v hu hv
       exact zk (ka:=false) (kb:=false) (hcov u v hu hv)
     . right;intro r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
       have h1:=hsym r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
       simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,joinF] at h1 ⊢
       have hsub6:=q14 (a r0) (a r1) (a r2) (a r3) (a r4) (a r5)
         (b r0) (b r1) (b r2) (b r3) (b r4) (b r5)
       omega
   . left;intro u v hu hv
     exact zk (ka:=false) (kb:=true) (qf hsub (by simp [qk] at hlen ⊢;omega) u v hu hv)
   . left;intro u v hu hv
     exact zk (ka:=true) (kb:=false) (qf hsub (by simp [qk] at hlen ⊢;omega) u v hu hv)
   . simp [qk] at hlen hle;omega
 | @bAnd s a ta b tb r ka kb _ _ _ _ _ _ _ _ _ hsub ih =>
   have hle:=hsub.len_le
   cases ka <;> cases kb
   . rcases ih (by simp [qk] at hlen ⊢;omega) with hcov | hsym
     . left;intro u v hu hv
       exact za (ka:=false) (kb:=false) (hcov u v hu hv)
     . right;intro r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
       have h1:=hsym r0 r1 r2 r3 r4 r5 h0 h1 h2 h3 h4 h5
       simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,meetF] at h1 ⊢
       have hsub6:=je (a r0) (a r1) (a r2) (a r3) (a r4) (a r5)
         (b r0) (b r1) (b r2) (b r3) (b r4) (b r5)
       omega
   . left;intro u v hu hv
     exact za (ka:=false) (kb:=true) (qf hsub (by simp [qk] at hlen ⊢;omega) u v hu hv)
   . left;intro u v hu hv
     exact za (ka:=true) (kb:=false) (qf hsub (by simp [qk] at hlen ⊢;omega) u v hu hv)
   . simp [qk] at hlen hle;omega
abbrev aR (n rp:Nat) (c:Cfg):=allRows n rp c.shTT
abbrev TR {n:Nat} (f:BFn n):=TagRun (invF (n:=n)) meetF joinF (fun _ => false) (fun _ => true) f
lemma qz {a b:Nat} (h:a=b):Nat.beq a b=true:=Eq.mpr Nat.beq_eq h
lemma q0 (a:Nat):Nat.beq a a=true:=Eq.mpr Nat.beq_eq rfl
lemma q2 {a b:Nat} (h:a≠b):Nat.beq a b=false:=by
 cases hb:Nat.beq a b
 . rfl
 . exact absurd (Eq.mp Nat.beq_eq hb) h
lemma y3 {a b:Nat} (h:Nat.beq a b=false):a≠b :=
 fun e => by subst e;rw [q0] at h;cases h
lemma zh {a b:Nat}:(Nat.beq a b=false) ↔ a≠b :=
 ⟨y3,q2⟩
lemma q4 {b e:Bool} (h:e=true):(if b=true then true else e)=true:=by
 cases b <;> simp [h]
lemma q5 {b e:Bool} (h:b=true):(if b=true then true else e)=true:=by
 rw [h];rfl
lemma v8 (a b:Nat):Nat.add a b=a+b:=rfl
def encWs {n:Nat} (rows:List Nat) (ws:List (BFn n × Nat)):List (Nat × Nat) :=
 ws.map fun p => (encL rows p.1,p.2)
abbrev eW {n:Nat} (rp:Nat) (c:Cfg) (ws:List (BFn n × Nat)):=encWs (aR n rp c) ws
abbrev eL {n:Nat} (rp:Nat) (c:Cfg) (g:BFn n):=encL (aR n rp c) g
lemma q41 {n rp:Nat} {c:Cfg} (a b:BFn n):eL rp c (joinF a b)=Nat.lor (eL rp c a) (eL rp c b):=q144 _ a b
lemma q40 {n rp:Nat} {c:Cfg} (a b:BFn n):eL rp c (meetF a b)=Nat.land (eL rp c a) (eL rp c b):=q143 _ a b
def encTTWs (n:Nat) (ws:List (BFn n × Nat)):List (Nat × Nat) :=
 ws.map fun p => (encTT n p.1,p.2)
lemma qy {n:Nat} (rows:List Nat) (p:BFn n × Nat) (ws:List (BFn n × Nat)) :
   encWs rows (p::ws)=(encL rows p.1,p.2)::encWs rows ws:=rfl
lemma kj {n:Nat} (rows:List Nat) (xs ys:List (BFn n × Nat)) :
   encWs rows (xs++ys)=encWs rows xs++encWs rows ys:=lMA
lemma q49 {n:Nat} (p:BFn n × Nat) (ws:List (BFn n × Nat)) :
   encTTWs n (p::ws)=(encTT n p.1,p.2)::encTTWs n ws:=rfl
lemma q18 (xs ys:List (Nat × Nat)):qx xs ys=xs.reverse++ys:=by
 induction xs generalizing ys with
 | nil => rfl
 | cons a t ih => simp [qx,ih,lAA]
lemma q187 (ws:List (Nat × Nat)):q164 ws=ws.length:=by
 induction ws with
 | nil => rfl
 | cons _ t ih => simp [q164,ih,v8];omega
lemma wh (x:Nat) (ws:List (Nat × Nat)) :
   yz x ws=false ↔ ∀ p ∈ ws,p.1≠x:=by
 induction ws with
 | nil => simp [yz]
 | cons a t ih =>
   rcases a with ⟨w,tg⟩
   simp only [yz,lMM,forall_eq_or_imp]
   by_cases h:x=w
   . subst h;simp [q0]
   . simp [q2 h,ih,Ne.symm h]
lemma jo {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   (ws:List (BFn n × Nat)) (g:BFn n)
   (h0:g≠fun _ => false) (h1:g≠fun _ => true) (hmem:∀ p ∈ ws,p.1≠g) :
   qj c.all1v (eW rp c ws) (eL rp c g)=true:=by
 have hinj:=q89 (n:=n) (q106 rp c.shTT)
 have hlen:(aR n rp c).length=c.shTT+2 ^ n:=zl n rp c.shTT
 have hne0:eL rp c g≠0:=fun e => by
   rw [← q39 (n:=n) (aR n rp c)] at e;exact h0 (hinj e)
 have hne1:eL rp c g≠c.all1v:=fun e => by
   rw [hc.all1v_eq,← hlen,← q177 (n:=n) (aR n rp c)] at e;exact h1 (hinj e)
 have hnc:yz (eL rp c g) (eW rp c ws)=false:=by
   rw [wh]
   intro p hp;rcases List.mem_map.1 hp with ⟨q,hq,rfl⟩
   exact fun e => hmem q hq (hinj e)
 unfold qj
 simp [q2 hne0,q2 hne1,hnc]
lemma qc {n:Nat} (rows:List Nat) (a b:BFn n) :
   encL rows (joinF a b)=Nat.lor (encL rows a) (encL rows b):=q144 rows a b
lemma q9 {n:Nat} (rows:List Nat) (a b:BFn n) :
   encL rows (meetF a b)=Nat.land (encL rows a) (encL rows b):=q143 rows a b
lemma q145 {n:Nat} (rows:List Nat) (a:BFn n) :
   encL rows (invF a)=Nat.xor (encL rows a) (2 ^ rows.length - 1):=q160 rows a
lemma qv {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a:BFn n) :
   eL rp c (invF a)=Nat.xor (eL rp c a) c.all1v:=by
 unfold eL;rw [q160,zl,← hc.all1v_eq]
def wi (c:Cfg) (w:Nat):Nat:=Nat.land w c.lok
def q63 (c:Cfg) (w:Nat):Nat:=Nat.land (Nat.shiftRight w c.k) c.lok
def k1 (c:Cfg) (w:Nat):Nat:=Nat.xor c.lok (q63 c w)
def wC (c:Cfg) (w:Nat):Nat:=Nat.xor (wi c w) (q63 c w)
def wU (c:Cfg) (w:Nat):Nat:=Nat.land (wC c w) (q63 c w)
def wA0 (c:Cfg) (w:Nat):Nat:=Nat.land (Nat.shiftRight w c.sh0) c.m0all
def wV0 (c:Cfg) (w:Nat):Nat:=qi c.m0 (wA0 c w)
def wV1 (c:Cfg) (w:Nat):Nat:=yg c.sh1 c.m1 c.m12 w
def yx (c:Cfg) (ws:List (Nat × Nat)):Nat:=ws.foldr (fun p acc => Nat.lor (wC c p.1) acc) 0
def v4 (c:Cfg) (ws:List (Nat × Nat)):Nat:=ws.foldr (fun p acc => Nat.lor (wU c p.1) acc) 0
def zf (c:Cfg) (ws:List (Nat × Nat)):Nat:=ws.foldr (fun p acc => Nat.add (wV0 c p.1) acc) 0
def va (c:Cfg) (ws:List (Nat × Nat)):Nat:=ws.foldr (fun p acc => Nat.add (wV1 c p.1) acc) 0
lemma qq (a b d:Nat):Nat.lor (Nat.lor a b) d=Nat.lor a (Nat.lor b d):=by
 apply nEQ;intro i;simp [nLO,nTO,Bool.or_assoc]
lemma q7 (a b:Nat):Nat.lor a b=Nat.lor b a:=by
 apply nEQ;intro i;simp [nLO,nTO,Bool.or_comm]
lemma q108 (a b:Nat):Nat.land a b=Nat.land b a:=by
 apply nEQ;intro i;simp [nLA,nTA,Bool.and_comm]
lemma q46 (a:Nat):Nat.lor 0 a=a:=by
 apply nEQ;intro i;simp [nLO,nTO]
lemma qt (a b:Nat):Nat.add a b=Nat.add b a:=nAC a b
lemma y9 (a b d:Nat):Nat.add (Nat.add a b) d=Nat.add a (Nat.add b d):=nAA a b d
lemma yp (c:Cfg) (p:Nat × Nat) (ws:List (Nat × Nat)):yx c (p::ws)=Nat.lor (wC c p.1) (yx c ws):=rfl
lemma vo (c:Cfg) (p:Nat × Nat) (ws:List (Nat × Nat)):v4 c (p::ws)=Nat.lor (wU c p.1) (v4 c ws):=rfl
lemma k0 (c:Cfg) (p:Nat × Nat) (ws:List (Nat × Nat)):zf c (p::ws)=Nat.add (wV0 c p.1) (zf c ws):=rfl
lemma w1 (c:Cfg) (p:Nat × Nat) (ws:List (Nat × Nat)):va c (p::ws)=Nat.add (wV1 c p.1) (va c ws):=rfl
lemma vc (c:Cfg) (xs ys:List (Nat × Nat)):yx c (xs++ys)=Nat.lor (yx c xs) (yx c ys):=by
 induction xs with | nil => simp [yx,q46] | cons a t ih => simp only [lCA,yx,lFC] at ih ⊢;rw [ih,qq]
lemma zu (c:Cfg) (xs ys:List (Nat × Nat)):v4 c (xs++ys)=Nat.lor (v4 c xs) (v4 c ys):=by
 induction xs with | nil => simp [v4,q46] | cons a t ih => simp only [lCA,v4,lFC] at ih ⊢;rw [ih,qq]
lemma zy (c:Cfg) (xs ys:List (Nat × Nat)):zf c (xs++ys)=Nat.add (zf c xs) (zf c ys):=by
 induction xs with | nil => simp [zf,v8] | cons a t ih => simp only [lCA,zf,lFC,v8] at ih ⊢;omega
lemma y6 (c:Cfg) (xs ys:List (Nat × Nat)):va c (xs++ys)=Nat.add (va c xs) (va c ys):=by
 induction xs with | nil => simp [va,v8] | cons a t ih => simp only [lCA,va,lFC,v8] at ih ⊢;omega
lemma yo (c:Cfg) {xs ys:List (Nat × Nat)} (hp:xs.Perm ys):yx c xs=yx c ys:=by
 induction hp with
 | nil => rfl | cons _ _ ih => simp only [yx,lFC] at ih ⊢;rw [ih]
 | swap x y l => simp only [yx,lFC];rw [← qq,q7 (wC c y.1),qq]
 | trans _ _ ih1 ih2 => exact ih1.trans ih2
lemma y0 (c:Cfg) {xs ys:List (Nat × Nat)} (hp:xs.Perm ys):v4 c xs=v4 c ys:=by
 induction hp with
 | nil => rfl | cons _ _ ih => simp only [v4,lFC] at ih ⊢;rw [ih]
 | swap x y l => simp only [v4,lFC];rw [← qq,q7 (wU c y.1),qq]
 | trans _ _ ih1 ih2 => exact ih1.trans ih2
lemma vu (c:Cfg) {xs ys:List (Nat × Nat)} (hp:xs.Perm ys):zf c xs=zf c ys:=by
 induction hp with
 | nil => rfl | cons _ _ ih => simp only [zf,lFC] at ih ⊢;rw [ih]
 | swap _ _ _ => simp only [zf,lFC,v8];omega
 | trans _ _ ih1 ih2 => exact ih1.trans ih2
lemma kz (c:Cfg) {xs ys:List (Nat × Nat)} (hp:xs.Perm ys):va c xs=va c ys:=by
 induction hp with
 | nil => rfl | cons _ _ ih => simp only [va,lFC] at ih ⊢;rw [ih]
 | swap _ _ _ => simp only [va,lFC,v8];omega
 | trans _ _ ih1 ih2 => exact ih1.trans ih2
lemma q149 (c:Cfg) (ws:List (Nat × Nat)) (i:Nat) :
   (yx c ws).testBit i=ws.any (fun p => (wC c p.1).testBit i):=by
 induction ws with
 | nil => simp [yx]
 | cons _ _ ih => simp only [yx,lFC,nLO,nTO,List.any_cons] at ih ⊢;rw [ih]
lemma q148 (c:Cfg) (ws:List (Nat × Nat)) (i:Nat) :
   (v4 c ws).testBit i=ws.any (fun p => (wU c p.1).testBit i):=by
 induction ws with
 | nil => simp [v4]
 | cons _ _ ih => simp only [v4,lFC,nLO,nTO,List.any_cons] at ih ⊢;rw [ih]
lemma zw {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (w i:Nat) :
   (wi c w).testBit i=if i < c.k then w.testBit i else false:=by
 unfold wi;rw [nLA,nTA,hc.lok_eq,nTB]
 by_cases hi:i < c.k <;> simp [hi]
lemma vl {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (w i:Nat) :
   (q63 c w).testBit i=if i < c.k then w.testBit (c.k+i) else false:=by
 unfold q63;rw [nLA,nTA,hc.lok_eq,nTB]
 change ((w >>> c.k).testBit i&&decide (i < c.k))=_
 rw [nTS];by_cases hi:i < c.k <;> simp [hi]
lemma q13 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (w i:Nat) :
   (k1 c w).testBit i=if i < c.k then !(w.testBit (c.k+i)) else false:=by
 unfold k1;rw [nXO,nTX,hc.lok_eq,nTB,vl hc]
 by_cases hi:i < c.k <;> simp [hi]
lemma vp {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (w i:Nat) :
   (wC c w).testBit i=if i < c.k then (w.testBit i ^^ w.testBit (c.k+i)) else false:=by
 unfold wC;rw [nXO,nTX,zw hc,vl hc]
 by_cases hi:i < c.k <;> simp [hi]
lemma vd {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (w i:Nat) :
   (wU c w).testBit i=if i < c.k then (!(w.testBit i)&&w.testBit (c.k+i)) else false:=by
 unfold wU;rw [nLA,nTA,vp hc,vl hc]
 by_cases hi:i < c.k
 . simp only [hi,↓reduceIte];cases w.testBit i <;> cases w.testBit (c.k+i) <;> decide
 . simp [hi]
lemma q197 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a:Nat) :
   wC c (Nat.xor a c.all1v)=wC c a:=by
 have h2n:=n2P n
 have hk_le : 2*c.k<=c.shTT+2 ^ n:=by have:=hc.sh0_eq;have:=hc.sh0_le;have:=hc.sh1_le;omega
 apply nEQ;intro i
 rw [vp hc,vp hc]
 by_cases hi:i < c.k
 . simp only [hi,↓reduceIte,nXO,nTX,hc.all1v_eq,nTB,
     show i < c.shTT+2 ^ n by omega,show c.k+i < c.shTT+2 ^ n by omega,decide_true,bBT]
   cases a.testBit i <;> cases a.testBit (c.k+i) <;> decide
 . simp [hi]
lemma q168 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a:Nat) :
   wU c (Nat.xor a c.all1v)=Nat.land (wC c a) (wi c a):=by
 have h2n:=n2P n
 have hk_le : 2*c.k<=c.shTT+2 ^ n:=by have:=hc.sh0_eq;have:=hc.sh0_le;have:=hc.sh1_le;omega
 apply nEQ;intro i
 rw [vd hc,nLA,nTA,vp hc,zw hc]
 by_cases hi:i < c.k
 . simp only [hi,↓reduceIte,nXO,nTX,hc.all1v_eq,nTB,
     show i < c.shTT+2 ^ n by omega,show c.k+i < c.shTT+2 ^ n by omega,decide_true,bBT]
   cases a.testBit i <;> cases a.testBit (c.k+i) <;> decide
 . simp [hi]
lemma q78 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a:Nat) :
   Nat.lor (wU c (Nat.xor a c.all1v)) (wU c a)=wC c a:=by
 rw [q168 hc];apply nEQ;intro i
 rw [nLO,nLA,nTO,nTA,vp hc,zw hc,vd hc]
 by_cases hi:i < c.k
 . simp only [hi,↓reduceIte];cases a.testBit i <;> cases a.testBit (c.k+i) <;> decide
 . simp [hi]
lemma q169 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a b:Nat) :
   wC c (Nat.lor a b)=Nat.xor (Nat.lor (wi c a) (wi c b)) (Nat.lor (q63 c a) (q63 c b)):=by
 apply nEQ;intro i
 rw [vp hc,nXO,nLO,nLO,nLO,
     nTX,nTO,nTO,nTO,nTO,
     zw hc,zw hc,vl hc,vl hc]
 by_cases hi:i < c.k <;> simp [hi]
lemma q121 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a b:Nat) :
   wC c (Nat.land a b)=Nat.xor (Nat.land (wi c a) (wi c b)) (Nat.land (q63 c a) (q63 c b)):=by
 apply nEQ;intro i
 rw [vp hc,nXO,nLA,nLA,nLA,
     nTX,nTA,nTA,nTA,nTA,
     zw hc,zw hc,vl hc,vl hc]
 by_cases hi:i < c.k <;> simp [hi]
lemma q170 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a:Nat) :
   wA0 c (Nat.xor a c.all1v)=Nat.xor (wA0 c a) c.m0all:=by
 have h2n:=n2P n
 have hbound:c.sh0+6*((c.sh1 - c.sh0) / 6)<=c.shTT+2 ^ n:=by
   have:=hc.sh0_le;have:=hc.sh1_le;have:=hc.p0_dvd;omega
 apply nEQ;intro i;unfold wA0
 simp only [nLA,nXO,nTA,nTX,hc.m0all_eq,nTB]
 change (((a^^^c.all1v) >>> c.sh0).testBit i&&decide (i < 6*((c.sh1 - c.sh0) / 6))) =
   (((a >>> c.sh0).testBit i&&decide (i < 6*((c.sh1 - c.sh0) / 6))) ^^ decide (i < 6*((c.sh1 - c.sh0) / 6)))
 rw [nTS,nTS,nTX,hc.all1v_eq,nTB]
 by_cases hi:i < 6*((c.sh1 - c.sh0) / 6)
 . simp [hi,show c.sh0+i < c.shTT+2 ^ n by omega]
 . simp [hi]
lemma q198 (c:Cfg) (a b:Nat):wA0 c (Nat.lor a b)=Nat.lor (wA0 c a) (wA0 c b):=by
 apply nEQ;intro i;unfold wA0
 simp only [nLA,nLO,nTA,nTO]
 change (((a|||b) >>> c.sh0).testBit i&&c.m0all.testBit i) =
   (((a >>> c.sh0).testBit i&&c.m0all.testBit i)||((b >>> c.sh0).testBit i&&c.m0all.testBit i))
 rw [nTS,nTS,nTS,nTO]
 cases a.testBit (c.sh0+i) <;> cases b.testBit (c.sh0+i) <;> cases c.m0all.testBit i <;> decide
lemma q171 (c:Cfg) (a b:Nat):wA0 c (Nat.land a b)=Nat.land (wA0 c a) (wA0 c b):=by
 apply nEQ;intro i;unfold wA0
 simp only [nLA,nTA]
 change (((a&&&b) >>> c.sh0).testBit i&&c.m0all.testBit i) =
   (((a >>> c.sh0).testBit i&&c.m0all.testBit i)&&((b >>> c.sh0).testBit i&&c.m0all.testBit i))
 rw [nTS,nTS,nTS,nTA]
 cases a.testBit (c.sh0+i) <;> cases b.testBit (c.sh0+i) <;> cases c.m0all.testBit i <;> decide
lemma q200 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (a:Nat) :
   wV1 c (Nat.xor a c.all1v)=wV1 c a:=by
 have h2n:=n2P n
 have hbound:c.sh1+6*((c.shTT - c.sh1) / 6)<=c.shTT+2 ^ n:=by
   have:=hc.sh1_le;have:=hc.p1_dvd;omega
 apply wg;intro i;unfold wV1
 rw [hc.m1_eq,hc.m12_eq,kh,kh]
 by_cases hi:i < (c.shTT - c.sh1) / 6
 . simp only [hi,↓reduceIte,nXO,nTX,hc.all1v_eq,nTB,
     show c.sh1+6*i < c.shTT+2 ^ n by omega,show c.sh1+6*i+1 < c.shTT+2 ^ n by omega,
     show c.sh1+6*i+2 < c.shTT+2 ^ n by omega,show c.sh1+6*i+3 < c.shTT+2 ^ n by omega,
     show c.sh1+6*i+4 < c.shTT+2 ^ n by omega,show c.sh1+6*i+5 < c.shTT+2 ^ n by omega,
     decide_true,bBT,jp]
 . simp [hi]
lemma y4 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   (rU a b:Nat) (hchild:Nat.lor rU (wU c (Nat.lor a b))=c.lok) :
   Nat.land (Nat.xor c.lok rU) (wi c a)=0/\Nat.land (Nat.xor c.lok rU) (wi c b)=0:=by
 constructor <;> (
   apply nEQ;intro i;
   have h1:=congrArg (fun z => z.testBit i) hchild;
   rw [nLA,nXO,nTA,nTX,nZT,
       hc.lok_eq,nTB,zw hc];
   rw [nLO,nTO,vd hc,hc.lok_eq,nTB] at h1;
   by_cases hi:i < c.k
   . simp only [hi,↓reduceIte,decide_true,Bool.true_bne,nLO,nTO] at h1 ⊢
     revert h1;cases rU.testBit i <;> cases a.testBit i <;> cases b.testBit i <;>
       cases a.testBit (c.k+i) <;> cases b.testBit (c.k+i) <;> decide
   . simp [hi])
lemma q10 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   (rU a b:Nat) (hchild:Nat.lor rU (Nat.lor (wU c a) (wU c (Nat.lor a b)))=c.lok) :
   Nat.land (Nat.xor c.lok rU) (wi c a)=0:=by
 apply nEQ;intro i
 have h1:=congrArg (fun z => z.testBit i) hchild
 rw [nLA,nXO,nTA,nTX,nZT,
     hc.lok_eq,nTB,zw hc]
 rw [nLO,nLO,nTO,nTO,vd hc,vd hc,
     hc.lok_eq,nTB] at h1
 by_cases hi:i < c.k
 . simp only [hi,↓reduceIte,decide_true,Bool.true_bne,nLO,nTO] at h1 ⊢
   revert h1;cases rU.testBit i <;> cases a.testBit i <;> cases b.testBit i <;>
     cases a.testBit (c.k+i) <;> cases b.testBit (c.k+i) <;> decide
 . simp [hi]
lemma vw {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   (rU a b:Nat) (hchild:Nat.lor rU (wU c (Nat.land a b))=c.lok) :
   Nat.land (Nat.xor c.lok rU) (k1 c a)=0/\Nat.land (Nat.xor c.lok rU) (k1 c b)=0:=by
 constructor <;> (
   apply nEQ;intro i;
   have h1:=congrArg (fun z => z.testBit i) hchild;
   rw [nLA,nXO,nTA,nTX,nZT,
       hc.lok_eq,nTB,q13 hc];
   rw [nLO,nTO,vd hc,hc.lok_eq,nTB] at h1;
   by_cases hi:i < c.k
   . simp only [hi,↓reduceIte,decide_true,Bool.true_bne,nLA,nTA] at h1 ⊢
     revert h1;cases rU.testBit i <;> cases a.testBit i <;> cases b.testBit i <;>
       cases a.testBit (c.k+i) <;> cases b.testBit (c.k+i) <;> decide
   . simp [hi])
lemma jb {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   (rU a b:Nat) (hchild:Nat.lor rU (Nat.lor (wU c a) (wU c (Nat.land a b)))=c.lok) :
   Nat.land (Nat.xor c.lok rU) (k1 c a)=0:=by
 apply nEQ;intro i
 have h1:=congrArg (fun z => z.testBit i) hchild
 rw [nLA,nXO,nTA,nTX,nZT,
     hc.lok_eq,nTB,q13 hc]
 rw [nLO,nLO,nTO,nTO,vd hc,vd hc,
     hc.lok_eq,nTB] at h1
 by_cases hi:i < c.k
 . simp only [hi,↓reduceIte,decide_true,Bool.true_bne,nLA,nTA] at h1 ⊢
   revert h1;cases rU.testBit i <;> cases a.testBit i <;> cases b.testBit i <;>
     cases a.testBit (c.k+i) <;> cases b.testBit (c.k+i) <;> decide
 . simp [hi]
lemma wk {m x y:Nat} (hx:Nat.land m x=0) (hy:Nat.land m y=0) :
   Nat.land m (Nat.lor x y)=0:=by
 apply nEQ;intro i
 have h1:=congrArg (fun z => z.testBit i) hx
 have h2:=congrArg (fun z => z.testBit i) hy
 simp only [nLA,nLO,nTA,nTO,nZT] at h1 h2 ⊢
 revert h1 h2;cases m.testBit i <;> cases x.testBit i <;> cases y.testBit i <;> decide
lemma zz {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {ws:List (BFn n × Nat)}
   (hcov:∀ u v:Fin n->Bool,f u=false->f v=true->∃ p ∈ ws,p.1 u≠p.1 v) :
   yx c (eW rp c ws)=c.lok:=by
 have h2n:=n2P n
 have hlen:=zl n rp c.shTT
 have hk_le : 2*c.k<=c.shTT:=by have:=hc.sh0_eq;have:=hc.sh0_le;have:=hc.sh1_le;omega
 apply nEQ;intro i
 rw [q149,hc.lok_eq,nTB]
 by_cases hi:i < c.k
 . simp only [hi,decide_true,lAN]
   obtain ⟨hu,hv⟩:=hc.cov_ok i hi
   obtain ⟨p,hp,hne⟩:=hcov _ _ hu hv
   refine ⟨(eL rp c p.1,p.2),List.mem_map.2 ⟨p,hp,rfl⟩,?_⟩
   rw [vp hc,if_pos hi,qm _ _ (by rw [hlen];omega),
       qm _ _ (by rw [hlen];omega)]
   cases h1:p.1 (q1 n ((aR n rp c).getD i 0)) <;>
     cases h2:p.1 (q1 n ((aR n rp c).getD (c.k+i) 0)) <;> simp_all
 . simp only [hi,decide_false]
   rw [Bool.eq_false_iff];intro h;obtain ⟨q,_,htb⟩:=List.any_eq_true.1 h
   rw [vp hc,if_neg hi] at htb;cases htb
lemma q6 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {ws:List (BFn n × Nat)}
   (hcov:∀ u v:Fin n->Bool,f u=false->f v=true->∃ p ∈ ws,p.1 u=false/\p.1 v=true) :
   v4 c (eW rp c ws)=c.lok:=by
 have h2n:=n2P n
 have hlen:=zl n rp c.shTT
 have hk_le : 2*c.k<=c.shTT:=by have:=hc.sh0_eq;have:=hc.sh0_le;have:=hc.sh1_le;omega
 apply nEQ;intro i
 rw [q148,hc.lok_eq,nTB]
 by_cases hi:i < c.k
 . simp only [hi,decide_true,lAN]
   obtain ⟨hu,hv⟩:=hc.cov_ok i hi
   obtain ⟨p,hp,hpu,hpv⟩:=hcov _ _ hu hv
   refine ⟨(eL rp c p.1,p.2),List.mem_map.2 ⟨p,hp,rfl⟩,?_⟩
   rw [vd hc,if_pos hi,qm _ _ (by rw [hlen];omega),
       qm _ _ (by rw [hlen];omega),hpu,hpv];rfl
 . simp only [hi,decide_false]
   rw [Bool.eq_false_iff];intro h;obtain ⟨q,_,htb⟩:=List.any_eq_true.1 h
   rw [vd hc,if_neg hi] at htb;cases htb
lemma q112 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (g:BFn n) (i:Nat) :
   z6 (wV0 c (eL rp c g)) i =
     if i < (c.sh1 - c.sh0) / 6 then
       let rows:=aR n rp c
       v6 (g (q1 n (rows.getD (c.sh0+6*i) 0)))
               (g (q1 n (rows.getD (c.sh0+6*i+1) 0)))
               (g (q1 n (rows.getD (c.sh0+6*i+2) 0)))
               (g (q1 n (rows.getD (c.sh0+6*i+3) 0)))
               (g (q1 n (rows.getD (c.sh0+6*i+4) 0)))
               (g (q1 n (rows.getD (c.sh0+6*i+5) 0)))
     else 0:=by
 have h2n:=n2P n
 have hlen:=zl n rp c.shTT
 have hbound:c.sh0+6*((c.sh1 - c.sh0) / 6)<=c.shTT:=by
   have:=hc.sh0_le;have:=hc.sh1_le;have:=hc.p0_dvd;omega
 unfold wV0;rw [hc.m0_eq,yy]
 by_cases hi:i < (c.sh1 - c.sh0) / 6
 . simp only [hi,↓reduceIte]
   have htb:∀ off < 6,(wA0 c (eL rp c g)).testBit (6*i+off) =
       g (q1 n ((aR n rp c).getD (c.sh0+6*i+off) 0)):=by
     intro off hoff;unfold wA0
     rw [nLA,nTA,hc.m0all_eq,nTB]
     simp only [show 6*i+off < 6*((c.sh1 - c.sh0) / 6) by omega,decide_true,bATR]
     change ((eL rp c g) >>> c.sh0).testBit (6*i+off)=_
     rw [nTS,← nAA,qm _ _ (by rw [hlen];omega)]
   rw [show 6*i=6*i+0 by omega,htb 0 (by decide),htb 1 (by decide),htb 2 (by decide),
       htb 3 (by decide),htb 4 (by decide),htb 5 (by decide)]
   simp only [nAZ]
 . simp [hi]
lemma q111 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c) (g:BFn n) (i:Nat) :
   z6 (wV1 c (eL rp c g)) i =
     if i < (c.shTT - c.sh1) / 6 then
       let rows:=aR n rp c
       zq (g (q1 n (rows.getD (c.sh1+6*i) 0)))
               (g (q1 n (rows.getD (c.sh1+6*i+1) 0)))
               (g (q1 n (rows.getD (c.sh1+6*i+2) 0)))
               (g (q1 n (rows.getD (c.sh1+6*i+3) 0)))
               (g (q1 n (rows.getD (c.sh1+6*i+4) 0)))
               (g (q1 n (rows.getD (c.sh1+6*i+5) 0)))
     else 0:=by
 have h2n:=n2P n
 have hlen:=zl n rp c.shTT
 have hbound:c.sh1+6*((c.shTT - c.sh1) / 6)<=c.shTT:=by
   have:=hc.sh1_le;have:=hc.p1_dvd;omega
 unfold wV1;rw [hc.m1_eq,hc.m12_eq,kh]
 by_cases hi:i < (c.shTT - c.sh1) / 6
 . simp only [hi,↓reduceIte]
   rw [qm _ _ (by rw [hlen];omega),qm _ _ (by rw [hlen];omega),
       qm _ _ (by rw [hlen];omega),qm _ _ (by rw [hlen];omega),
       qm _ _ (by rw [hlen];omega),qm _ _ (by rw [hlen];omega)]
 . simp [hi]
lemma zi {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} {g:BFn n} {tg:Nat} {r:List (BFn n × Nat)}
   (hs:s<=10)
   (htr:TR f s ((g,tg)::r))
   (hlen:((g,tg)::r).length=s+1) :
   qb c (zf c (eW rp c r)) (wV0 c (eL rp c g))=true:=by
 set rows:=aR n rp c
 set m:=(c.sh1 - c.sh0) / 6
 have hsum:Nat.add (zf c (encWs rows r)) (wV0 c (encL rows g))=zf c (encWs rows ((g,tg)::r)):=by
   simp only [encWs,lMC,zf,lFC,v8];omega
 unfold qb;rw [hsum,hc.a29_0_eq,hc.b5_0_eq]
 have hf_le:∀ (p:Nat × Nat) (i:Nat),z6 (wV0 c p.1) i<=if i < m then 3 else 0:=by
   intro p i;unfold wV0;rw [hc.m0_eq,yy];split;exact yr _ _ _ _ _ _;omega
 have hls:=fun i => q47 (fun p:Nat × Nat => wV0 c p.1) m hf_le (encWs rows ((g,tg)::r)) (by rw [encWs,lLM,hlen];omega) i
 apply ky _ m
 . intro i;have ⟨h1,h2⟩:=hls i
   change z6 ((encWs rows ((g,tg)::r)).foldr (fun p acc => Nat.add (wV0 c p.1) acc) 0) i<=_
   have hle_e:(encWs rows ((g,tg)::r)).length=s+1:=by rw [encWs,lLM,hlen]
   rw [h1];rw [hle_e] at h2
   by_cases hi:i < m <;> simp only [hi,↓reduceIte] at h2 ⊢ <;> omega
 . intro i hi;have ⟨h1,_⟩:=hls i
   change 3<=z6 ((encWs rows ((g,tg)::r)).foldr (fun p acc => Nat.add (wV0 c p.1) acc) 0) i
   rw [h1]
   have hmap:((encWs rows ((g,tg)::r)).map fun p => z6 (wV0 c p.1) i) =
       ((g,tg)::r).map fun p =>
         v6 (p.1 (q1 n (rows.getD (c.sh0+6*i) 0)))
                 (p.1 (q1 n (rows.getD (c.sh0+6*i+1) 0)))
                 (p.1 (q1 n (rows.getD (c.sh0+6*i+2) 0)))
                 (p.1 (q1 n (rows.getD (c.sh0+6*i+3) 0)))
                 (p.1 (q1 n (rows.getD (c.sh0+6*i+4) 0)))
                 (p.1 (q1 n (rows.getD (c.sh0+6*i+5) 0))):=by
     simp only [encWs,lMMp];apply List.map_congr_left
     intro p _;dsimp only [Function.comp];rw [q112 hc p.1 i,if_pos hi]
   rw [hmap]
   obtain ⟨h0,h1',h2',h3',h4',h5'⟩:=hc.p0_ok i hi
   exact kk htr hlen _ _ _ _ _ _ h0 h1' h2' h3' h4' h5'
lemma vt {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {ws:List (BFn n × Nat)} (hlen:ws.length<=11)
   (hsym:∀ r0 r1 r2 r3 r4 r5:Fin n->Bool,
     f r0=true->f r1=true->f r2=true->f r3=false->f r4=false->f r5=false ->
     3<=(ws.map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum) :
   z3 c (va c (eW rp c ws))=true:=by
 set rows:=aR n rp c
 set m:=(c.shTT - c.sh1) / 6
 unfold z3;rw [hc.a29_1_eq,hc.b5_1_eq]
 have hf_le:∀ (p:Nat × Nat) (i:Nat),z6 (wV1 c p.1) i<=if i < m then 3 else 0:=by
   intro p i;unfold wV1;rw [hc.m1_eq,hc.m12_eq,kh];split;exact q52 _ _ _ _ _ _;omega
 have hls:=fun i => q47 (fun p:Nat × Nat => wV1 c p.1) m hf_le (encWs rows ws) (by rw [encWs,lLM];omega) i
 apply ky _ m
 . intro i;have ⟨h1,h2⟩:=hls i
   change z6 ((encWs rows ws).foldr (fun p acc => Nat.add (wV1 c p.1) acc) 0) i<=_
   have hle_e:(encWs rows ws).length=ws.length:=lLM _
   rw [h1];rw [hle_e] at h2
   by_cases hi:i < m <;> simp only [hi,↓reduceIte] at h2 ⊢ <;> omega
 . intro i hi;have ⟨h1,_⟩:=hls i
   change 3<=z6 ((encWs rows ws).foldr (fun p acc => Nat.add (wV1 c p.1) acc) 0) i
   rw [h1]
   have hmap:((encWs rows ws).map fun p => z6 (wV1 c p.1) i) =
       ws.map fun p =>
         zq (p.1 (q1 n (rows.getD (c.sh1+6*i) 0)))
                 (p.1 (q1 n (rows.getD (c.sh1+6*i+1) 0)))
                 (p.1 (q1 n (rows.getD (c.sh1+6*i+2) 0)))
                 (p.1 (q1 n (rows.getD (c.sh1+6*i+3) 0)))
                 (p.1 (q1 n (rows.getD (c.sh1+6*i+4) 0)))
                 (p.1 (q1 n (rows.getD (c.sh1+6*i+5) 0))):=by
     simp only [encWs,lMMp];apply List.map_congr_left
     intro p _;dsimp only [Function.comp];rw [q111 hc p.1 i,if_pos hi]
   rw [hmap]
   obtain ⟨h0,h1',h2',h3',h4',h5'⟩:=hc.p1_ok i hi
   exact hsym _ _ _ _ _ _ h0 h1' h2' h3' h4' h5'
abbrev PN (c:Cfg) (w tg:Nat) (l2:List (Nat × Nat)) (pl2:PList):PList :=
 PList.cons w tg (wi c w) (q63 c w) (k1 c w) (wC c w) (wU c w) (wA0 c w) (wV0 c w) (wV1 c w)
   (yx c l2) (v4 c l2) (zf c l2) (va c l2) pl2
inductive PListSpec (c:Cfg):PList->List (Nat × Nat)->Prop where
 | nil:PListSpec c PList.nil []
 | cons (w tg:Nat) (tl:PList) (rest:List (Nat × Nat)) :
     PListSpec c tl rest ->
     PListSpec c
       (PN c w tg rest tl)
       ((w,tg)::rest)
lemma q82 (c:Cfg) (ws:List (Nat × Nat)) :
   ∃ pl,kt c ws=(yx c ws,v4 c ws,zf c ws,va c ws,pl)/\PListSpec c pl ws:=by
 induction ws with
 | nil => exact ⟨PList.nil,rfl,PListSpec.nil⟩
 | cons p rest ih =>
   rcases p with ⟨w,tg⟩;obtain ⟨tl,htl,hsp⟩:=ih
   refine ⟨_,?_,PListSpec.cons w tg tl rest hsp⟩;simp only [kt,htl];rfl
lemma PListSpec.pToList {c:Cfg} {pl:PList} {ws:List (Nat × Nat)} (h:PListSpec c pl ws) :
   pToList pl=ws:=by
 induction h with | nil => rfl | cons _ _ _ _ _ ih => exact congrArg _ ih
lemma q84 (c:Cfg) (ws:List (Nat × Nat)) (a ta alo nahi a0 v0a:Nat)
   (pre mid:List (Nat × Nat)) (pmU pmV0:Nat) (pl:PList) :
   we c ws a ta alo nahi a0 v0a pmU pmV0 pl =
     vx c ws (fun _ => true) a ta alo nahi a0 v0a pre pmU pmV0 mid pl:=by
 induction pl generalizing pmU pmV0 mid with
 | nil => rfl
 | cons b tb blo bhi nbhi cb ub b0 v0b v1b postC postU postV0 postV1 post ih =>
   simp only [we,vx]
   have hor :
     (if (ta.beq 2||tb.beq 2)=true then false
      else
        let okOrA:=((c.lok.xor (pmU.lor postU)).land alo).beq 0
        let okOrB:=((c.lok.xor (pmU.lor postU)).land blo).beq 0
        if okOrA=true then
          let w:=a.lor b;let rV0:=pmV0.add postV0;let v0w:=qi c.m0 (a0.lor b0)
          okOrB&&qj c.all1v ws w||!ta.beq 1&&qb c (rV0.add v0a) v0w&&qj c.all1v ws w ||
            !tb.beq 1&&okOrB&&qb c (rV0.add v0b) v0w&&qj c.all1v ws w
        else if (okOrB&&!tb.beq 1)=true then
          qb c ((pmV0.add postV0).add v0b) (qi c.m0 (a0.lor b0))&&qj c.all1v ws (a.lor b)
        else false) =
     (if (ta.beq 2||tb.beq 2)=true then false
      else
        let okOrA:=((c.lok.xor (pmU.lor postU)).land alo).beq 0
        let okOrB:=((c.lok.xor (pmU.lor postU)).land blo).beq 0
        if okOrA=true then
          let w:=a.lor b;let rV0:=pmV0.add postV0;let v0w:=qi c.m0 (a0.lor b0)
          if (okOrB&&qj c.all1v ws w&&true)=true then true
          else if (!ta.beq 1&&qb c (rV0.add v0a) v0w&&qj c.all1v ws w&&true)=true then true
          else !tb.beq 1&&okOrB&&qb c (rV0.add v0b) v0w&&qj c.all1v ws w&&true
        else if (okOrB&&!tb.beq 1)=true then
          qb c ((pmV0.add postV0).add v0b) (qi c.m0 (a0.lor b0))&&qj c.all1v ws (a.lor b)&&true
        else false):=by
     split
     . rfl
     . dsimp only;split
       . cases ((c.lok.xor (pmU.lor postU)).land blo).beq 0 <;> cases qj c.all1v ws (a.lor b) <;>
         cases ta.beq 1 <;> cases tb.beq 1 <;>
         cases qb c ((pmV0.add postV0).add v0a) (qi c.m0 (a0.lor b0)) <;>
         cases qb c ((pmV0.add postV0).add v0b) (qi c.m0 (a0.lor b0)) <;> rfl
       . split <;> simp
   have hand :
     (if (ta.beq 1||tb.beq 1)=true then false
      else
        let okAndA:=((c.lok.xor (pmU.lor postU)).land nahi).beq 0
        let okAndB:=((c.lok.xor (pmU.lor postU)).land nbhi).beq 0
        if okAndA=true then
          let w:=a.land b;let rV0:=pmV0.add postV0;let v0w:=qi c.m0 (a0.land b0)
          okAndB&&qj c.all1v ws w||ta.beq 0&&qb c (rV0.add v0a) v0w&&qj c.all1v ws w ||
            tb.beq 0&&okAndB&&qb c (rV0.add v0b) v0w&&qj c.all1v ws w
        else if (okAndB&&tb.beq 0)=true then
          qb c ((pmV0.add postV0).add v0b) (qi c.m0 (a0.land b0))&&qj c.all1v ws (a.land b)
        else false) =
     (if (ta.beq 1||tb.beq 1)=true then false
      else
        let okAndA:=((c.lok.xor (pmU.lor postU)).land nahi).beq 0
        let okAndB:=((c.lok.xor (pmU.lor postU)).land nbhi).beq 0
        if okAndA=true then
          let w:=a.land b;let rV0:=pmV0.add postV0;let v0w:=qi c.m0 (a0.land b0)
          if (okAndB&&qj c.all1v ws w&&true)=true then true
          else if (ta.beq 0&&qb c (rV0.add v0a) v0w&&qj c.all1v ws w&&true)=true then true
          else tb.beq 0&&okAndB&&qb c (rV0.add v0b) v0w&&qj c.all1v ws w&&true
        else if (okAndB&&tb.beq 0)=true then
          qb c ((pmV0.add postV0).add v0b) (qi c.m0 (a0.land b0))&&qj c.all1v ws (a.land b)&&true
        else false):=by
     split
     . rfl
     . dsimp only;split
       . cases ((c.lok.xor (pmU.lor postU)).land nbhi).beq 0 <;> cases qj c.all1v ws (a.land b) <;>
         cases ta.beq 0 <;> cases tb.beq 0 <;>
         cases qb c ((pmV0.add postV0).add v0a) (qi c.m0 (a0.land b0)) <;>
         cases qb c ((pmV0.add postV0).add v0b) (qi c.m0 (a0.land b0)) <;> rfl
       . split <;> simp
   rw [hor,hand,ih ((b,tb)::mid) (Nat.lor pmU ub) (Nat.add pmV0 v0b)]
lemma q140 (c:Cfg) (ws:List (Nat × Nat)) (preU preV0:Nat) (pre:List (Nat × Nat)) (pl:PList) :
   q26 c ws preU preV0 pl=js c ws (fun _ => true) preU preV0 pre pl:=by
 induction pl generalizing preU preV0 pre with
 | nil => rfl
 | cons a ta alo ahi nahi ca ua a0 v0a v1a postC postU postV0 postV1 suf ih =>
   simp only [q26,js,q84 c ws a ta alo nahi a0 v0a pre [] preU preV0 suf]
   split;rfl;exact ih _ _ _
lemma wu (c:Cfg) (s:Nat) (ws:List (Nat × Nat)) :
   scanInline c s ws=scanAll c s ws (fun _ => true):=by
 unfold scanInline scanAll
 split
 . rfl
 . cases kt c ws with
   | mk totC r1 => cases r1 with
   | mk totU r2 => cases r2 with
   | mk totV0 r3 => cases r3 with
   | mk totV1 pl =>
     dsimp only
     cases Nat.sub (Nat.add s 2) (q164 ws) with
     | zero => rfl
     | succ d =>
       cases d with
       | zero =>
         cases z3 c totV1
         . simp only [bFT,↓reduceIte];rw [q140 c ws 0 0 []]
         . rfl
       | succ d2 => cases d2 <;> rfl
lemma y8 {α:Type} (x : α) (a b:List α):(x::a++b).Perm (a++x::b) :=
 List.perm_middle.symm
lemma v7 {α:Type} (p:List α) (x : α) (a b:List α) :
   (p++x::a++b).Perm (p++a++x::b):=by
 simpa [lAA] using (lPM (a:=x) (l₁:=a) (l₂:=b)).symm.append_left p
lemma q130 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (l1 l2 pre:List (Nat × Nat)) (a ta preU preV0:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::l2))
   (hU:preU=v4 c pre) (hV0:preV0=zf c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     w7 c ws onSurv (v4 c (pre++l1)) (zf c (pre++l1)) (l1.reverse++pre)
       (PN c a ta l2 pl2)=true) :
   w7 c ws onSurv preU preV0 pre pl=true:=by
 induction l1 generalizing pre preU preV0 pl with
 | nil =>
   cases hsp with | cons _ _ tl _ htl => rw [hU,hV0];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold w7;dsimp only;apply q4
     apply ih ((w,tg)::pre) _ _ tl htl
       (by rw [hU];exact q7 _ _) (by rw [hV0];exact qt _ _)
     intro pl2 hpl2
     have hp:((w,tg)::(pre++t)).Perm (pre++(w,tg)::t):=List.perm_middle.symm
     rw [lCA,y0 c hp,vu c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q128 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (l1 l2 pre:List (Nat × Nat)) (a ta preC preU preV0 preV1:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::l2))
   (hC:preC=yx c pre) (hU:preU=v4 c pre) (hV0:preV0=zf c pre) (hV1:preV1=va c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     w6 c ws onSurv (yx c (pre++l1)) (v4 c (pre++l1)) (zf c (pre++l1)) (va c (pre++l1)) (l1.reverse++pre)
       (PN c a ta l2 pl2)=true) :
   w6 c ws onSurv preC preU preV0 preV1 pre pl=true:=by
 induction l1 generalizing pre preC preU preV0 preV1 pl with
 | nil =>
   cases hsp with | cons _ _ tl _ htl => rw [hC,hU,hV0,hV1];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold w6;dsimp only;apply q4
     apply ih ((w,tg)::pre) _ _ _ _ tl htl
       (by rw [hC];exact q7 _ _) (by rw [hU];exact q7 _ _)
       (by rw [hV0];exact qt _ _) (by rw [hV1];exact qt _ _)
     intro pl2 hpl2
     have hp:((w,tg)::(pre++t)).Perm (pre++(w,tg)::t):=List.perm_middle.symm
     rw [lCA,yo c hp,y0 c hp,vu c hp,kz c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q126 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (l1 l2 pre:List (Nat × Nat)) (a ta preC:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::l2)) (hC:preC=yx c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     w5 c ws onSurv (yx c (pre++l1)) (l1.reverse++pre)
       (PN c a ta l2 pl2)=true) :
   w5 c ws onSurv preC pre pl=true:=by
 induction l1 generalizing pre preC pl with
 | nil => cases hsp with | cons _ _ tl _ htl => rw [hC];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold w5;dsimp only;apply q4
     apply ih ((w,tg)::pre) _ tl htl (by rw [hC];exact q7 _ _)
     intro pl2 hpl2
     have hp:((w,tg)::(pre++t)).Perm (pre++(w,tg)::t):=List.perm_middle.symm
     rw [lCA,yo c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q132 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (a ta:Nat) (pre m1 m2 mid:List (Nat × Nat)) (b tb pmU pmV0:Nat) (pl:PList)
   (hsp:PListSpec c pl (m1++(b,tb)::m2))
   (hU:pmU=v4 c (pre++mid)) (hV0:pmV0=zf c (pre++mid))
   (hstep:∀ pl2,PListSpec c pl2 m2 ->
     ke c ws onSurv a ta (wi c a) (k1 c a) (wA0 c a) pre
       (v4 c (pre++mid++m1)) (zf c (pre++mid++m1)) (m1.reverse++mid)
       (PN c b tb m2 pl2)=true) :
   ke c ws onSurv a ta (wi c a) (k1 c a) (wA0 c a) pre pmU pmV0 mid pl=true:=by
 induction m1 generalizing mid pmU pmV0 pl with
 | nil => cases hsp with | cons _ _ tl _ htl => rw [hU,hV0];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold ke;dsimp only;apply q4;apply q4
     apply ih ((w,tg)::mid) _ _ tl htl
       (by rw [hU,zu,zu,vo,qq,q7 (v4 c mid)])
       (by rw [hV0,zy,zy,k0,y9,qt (zf c mid)])
     intro pl2 hpl2
     have hp:(pre++((w,tg)::mid)++t).Perm (pre++mid++(w,tg)::t):=by
       simpa [lAA] using v7 pre (w,tg) mid t
     rw [y0 c hp,vu c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q97 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (l1 mid l2 pre:List (Nat × Nat)) (a ta b tb preU preV0:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::mid++(b,tb)::l2))
   (hU:preU=v4 c pre) (hV0:preV0=zf c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     ke c ws onSurv a ta (wi c a) (k1 c a) (wA0 c a) (l1.reverse++pre)
       (v4 c (pre++l1++mid)) (zf c (pre++l1++mid)) mid.reverse
       (PN c b tb l2 pl2)=true) :
   q98 c ws onSurv preU preV0 pre pl=true:=by
 induction l1 generalizing pre preU preV0 pl with
 | nil =>
   cases hsp with
   | cons _ _ tl _ htl =>
     unfold q98;apply q5
     apply q132 c ws onSurv a ta pre mid l2 [] b tb preU preV0 tl htl (by simp [hU]) (by simp [hV0])
     intro pl2 hpl2;simpa using hstep pl2 hpl2
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold q98;apply q4
     apply ih ((w,tg)::pre) _ _ tl htl
       (by rw [hU];exact q7 _ _) (by rw [hV0];exact qt _ _)
     intro pl2 hpl2
     have hp:(((w,tg)::pre)++t++mid).Perm (pre++((w,tg)::t)++mid):=by
       simpa [lAA] using y8 (w,tg) pre (t++mid)
     rw [y0 c hp,vu c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q105 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (a ta:Nat) (pre m1 m2 mid:List (Nat × Nat)) (b tb pmU pmV0:Nat) (pl:PList)
   (hsp:PListSpec c pl (m1++(b,tb)::m2))
   (hU:pmU=v4 c (pre++mid)) (hV0:pmV0=zf c (pre++mid))
   (hstep:∀ pl2,PListSpec c pl2 m2 ->
     vx c ws onSurv a ta (wi c a) (k1 c a) (wA0 c a) (wV0 c a) pre
       (v4 c (pre++mid++m1)) (zf c (pre++mid++m1)) (m1.reverse++mid)
       (PN c b tb m2 pl2)=true) :
   vx c ws onSurv a ta (wi c a) (k1 c a) (wA0 c a) (wV0 c a) pre pmU pmV0 mid pl=true:=by
 induction m1 generalizing mid pmU pmV0 pl with
 | nil => cases hsp with | cons _ _ tl _ htl => rw [hU,hV0];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold vx;dsimp only;apply q4;apply q4
     apply ih ((w,tg)::mid) _ _ tl htl
       (by rw [hU,zu,zu,vo,qq,q7 (v4 c mid)])
       (by rw [hV0,zy,zy,k0,y9,qt (zf c mid)])
     intro pl2 hpl2
     have hp:(pre++((w,tg)::mid)++t).Perm (pre++mid++(w,tg)::t):=by
       simpa [lAA] using v7 pre (w,tg) mid t
     rw [y0 c hp,vu c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q65 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (l1 mid l2 pre:List (Nat × Nat)) (a ta b tb preU preV0:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::mid++(b,tb)::l2))
   (hU:preU=v4 c pre) (hV0:preV0=zf c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     vx c ws onSurv a ta (wi c a) (k1 c a) (wA0 c a) (wV0 c a) (l1.reverse++pre)
       (v4 c (pre++l1++mid)) (zf c (pre++l1++mid)) mid.reverse
       (PN c b tb l2 pl2)=true) :
   js c ws onSurv preU preV0 pre pl=true:=by
 induction l1 generalizing pre preU preV0 pl with
 | nil =>
   cases hsp with
   | cons _ _ tl _ htl =>
     unfold js;apply q5
     apply q105 c ws onSurv a ta pre mid l2 [] b tb preU preV0 tl htl (by simp [hU]) (by simp [hV0])
     intro pl2 hpl2;simpa using hstep pl2 hpl2
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold js;apply q4
     apply ih ((w,tg)::pre) _ _ tl htl
       (by rw [hU];exact q7 _ _) (by rw [hV0];exact qt _ _)
     intro pl2 hpl2
     have hp:(((w,tg)::pre)++t++mid).Perm (pre++((w,tg)::t)++mid):=by
       simpa [lAA] using y8 (w,tg) pre (t++mid)
     rw [y0 c hp,vu c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q131 (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (onSurv:List (Nat × Nat)->Bool)
   (a ta:Nat) (pre m1 m2 mid:List (Nat × Nat)) (b tb pmC pmU pmV0 pmV1:Nat) (pl:PList)
   (hsp:PListSpec c pl (m1++(b,tb)::m2))
   (hC:pmC=yx c (pre++mid)) (hU:pmU=v4 c (pre++mid))
   (hV0:pmV0=zf c (pre++mid)) (hV1:pmV1=va c (pre++mid))
   (hstep:∀ pl2,PListSpec c pl2 m2 ->
     kd c ws hasUp onSurv a ta (wi c a) (q63 c a) (k1 c a) (wA0 c a) (wV0 c a) pre
       (yx c (pre++mid++m1)) (v4 c (pre++mid++m1)) (zf c (pre++mid++m1)) (va c (pre++mid++m1)) (m1.reverse++mid)
       (PN c b tb m2 pl2)=true) :
   kd c ws hasUp onSurv a ta (wi c a) (q63 c a) (k1 c a) (wA0 c a) (wV0 c a) pre pmC pmU pmV0 pmV1 mid pl=true:=by
 induction m1 generalizing mid pmC pmU pmV0 pmV1 pl with
 | nil => cases hsp with | cons _ _ tl _ htl => rw [hC,hU,hV0,hV1];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold kd;dsimp only;apply q4;apply q4
     apply ih ((w,tg)::mid) _ _ _ _ tl htl
       (by rw [hC,vc,vc,yp,qq,q7 (yx c mid)])
       (by rw [hU,zu,zu,vo,qq,q7 (v4 c mid)])
       (by rw [hV0,zy,zy,k0,y9,qt (zf c mid)])
       (by rw [hV1,y6,y6,w1,y9,qt (va c mid)])
     intro pl2 hpl2
     have hp:(pre++((w,tg)::mid)++t).Perm (pre++mid++(w,tg)::t):=by
       simpa [lAA] using v7 pre (w,tg) mid t
     rw [yo c hp,y0 c hp,vu c hp,kz c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q95 (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (onSurv:List (Nat × Nat)->Bool)
   (l1 mid l2 pre:List (Nat × Nat)) (a ta b tb preC preU preV0 preV1:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::mid++(b,tb)::l2))
   (hC:preC=yx c pre) (hU:preU=v4 c pre) (hV0:preV0=zf c pre) (hV1:preV1=va c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     kd c ws hasUp onSurv a ta (wi c a) (q63 c a) (k1 c a) (wA0 c a) (wV0 c a) (l1.reverse++pre)
       (yx c (pre++l1++mid)) (v4 c (pre++l1++mid)) (zf c (pre++l1++mid)) (va c (pre++l1++mid)) mid.reverse
       (PN c b tb l2 pl2)=true) :
   q96 c ws hasUp onSurv preC preU preV0 preV1 pre pl=true:=by
 induction l1 generalizing pre preC preU preV0 preV1 pl with
 | nil =>
   cases hsp with
   | cons _ _ tl _ htl =>
     unfold q96;apply q5
     apply q131 c ws hasUp onSurv a ta pre mid l2 [] b tb preC preU preV0 preV1 tl htl
       (by simp [hC]) (by simp [hU]) (by simp [hV0]) (by simp [hV1])
     intro pl2 hpl2;simpa using hstep pl2 hpl2
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold q96;apply q4
     apply ih ((w,tg)::pre) _ _ _ _ tl htl
       (by rw [hC];exact q7 _ _) (by rw [hU];exact q7 _ _)
       (by rw [hV0];exact qt _ _) (by rw [hV1];exact qt _ _)
     intro pl2 hpl2
     have hp:(((w,tg)::pre)++t++mid).Perm (pre++((w,tg)::t)++mid):=by
       simpa [lAA] using y8 (w,tg) pre (t++mid)
     rw [yo c hp,y0 c hp,vu c hp,kz c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q129 (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (totV0:Nat) (onSurv:List (Nat × Nat)->Bool)
   (a ta:Nat) (pre m1 m2 mid:List (Nat × Nat)) (b tb pmC pmU pmV1:Nat) (pl:PList)
   (hsp:PListSpec c pl (m1++(b,tb)::m2))
   (hC:pmC=yx c (pre++mid)) (hU:pmU=v4 c (pre++mid)) (hV1:pmV1=va c (pre++mid))
   (hstep:∀ pl2,PListSpec c pl2 m2 ->
     kc c ws hasUp totV0 onSurv a ta (wi c a) (q63 c a) (k1 c a) (wC c a) (wA0 c a) (wV1 c a) pre
       (yx c (pre++mid++m1)) (v4 c (pre++mid++m1)) (va c (pre++mid++m1)) (m1.reverse++mid)
       (PN c b tb m2 pl2)=true) :
   kc c ws hasUp totV0 onSurv a ta (wi c a) (q63 c a) (k1 c a) (wC c a) (wA0 c a) (wV1 c a) pre pmC pmU pmV1 mid pl=true:=by
 induction m1 generalizing mid pmC pmU pmV1 pl with
 | nil => cases hsp with | cons _ _ tl _ htl => rw [hC,hU,hV1];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold kc;dsimp only;apply q4;apply q4
     apply ih ((w,tg)::mid) _ _ _ tl htl
       (by rw [hC,vc,vc,yp,qq,q7 (yx c mid)])
       (by rw [hU,zu,zu,vo,qq,q7 (v4 c mid)])
       (by rw [hV1,y6,y6,w1,y9,qt (va c mid)])
     intro pl2 hpl2
     have hp:(pre++((w,tg)::mid)++t).Perm (pre++mid++(w,tg)::t):=by
       simpa [lAA] using v7 pre (w,tg) mid t
     rw [yo c hp,y0 c hp,kz c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q93 (c:Cfg) (ws:List (Nat × Nat)) (hasUp:Bool) (totV0:Nat) (onSurv:List (Nat × Nat)->Bool)
   (l1 mid l2 pre:List (Nat × Nat)) (a ta b tb preC preU preV1:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::mid++(b,tb)::l2))
   (hC:preC=yx c pre) (hU:preU=v4 c pre) (hV1:preV1=va c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     kc c ws hasUp totV0 onSurv a ta (wi c a) (q63 c a) (k1 c a) (wC c a) (wA0 c a) (wV1 c a) (l1.reverse++pre)
       (yx c (pre++l1++mid)) (v4 c (pre++l1++mid)) (va c (pre++l1++mid)) mid.reverse
       (PN c b tb l2 pl2)=true) :
   q94 c ws hasUp totV0 onSurv preC preU preV1 pre pl=true:=by
 induction l1 generalizing pre preC preU preV1 pl with
 | nil =>
   cases hsp with
   | cons _ _ tl _ htl =>
     unfold q94;apply q5
     apply q129 c ws hasUp totV0 onSurv a ta pre mid l2 [] b tb preC preU preV1 tl htl
       (by simp [hC]) (by simp [hU]) (by simp [hV1])
     intro pl2 hpl2;simpa using hstep pl2 hpl2
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold q94;apply q4
     apply ih ((w,tg)::pre) _ _ _ tl htl
       (by rw [hC];exact q7 _ _) (by rw [hU];exact q7 _ _)
       (by rw [hV1];exact qt _ _)
     intro pl2 hpl2
     have hp:(((w,tg)::pre)++t++mid).Perm (pre++((w,tg)::t)++mid):=by
       simpa [lAA] using y8 (w,tg) pre (t++mid)
     rw [yo c hp,y0 c hp,kz c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q127 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (a ta:Nat) (pre m1 m2 mid:List (Nat × Nat)) (b tb pmC:Nat) (pl:PList)
   (hsp:PListSpec c pl (m1++(b,tb)::m2)) (hC:pmC=yx c (pre++mid))
   (hstep:∀ pl2,PListSpec c pl2 m2 ->
     k9 c ws onSurv a ta (wi c a) (q63 c a) (wC c a) pre
       (yx c (pre++mid++m1)) (m1.reverse++mid)
       (PN c b tb m2 pl2)=true) :
   k9 c ws onSurv a ta (wi c a) (q63 c a) (wC c a) pre pmC mid pl=true:=by
 induction m1 generalizing mid pmC pl with
 | nil => cases hsp with | cons _ _ tl _ htl => rw [hC];simpa using hstep tl htl
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold k9;dsimp only;apply q4;apply q4
     apply ih ((w,tg)::mid) _ tl htl
       (by rw [hC,vc,vc,yp,qq,q7 (yx c mid)])
     intro pl2 hpl2
     have hp:(pre++((w,tg)::mid)++t).Perm (pre++mid++(w,tg)::t):=by
       simpa [lAA] using v7 pre (w,tg) mid t
     rw [yo c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q91 (c:Cfg) (ws:List (Nat × Nat)) (onSurv:List (Nat × Nat)->Bool)
   (l1 mid l2 pre:List (Nat × Nat)) (a ta b tb preC:Nat) (pl:PList)
   (hsp:PListSpec c pl (l1++(a,ta)::mid++(b,tb)::l2)) (hC:preC=yx c pre)
   (hstep:∀ pl2,PListSpec c pl2 l2 ->
     k9 c ws onSurv a ta (wi c a) (q63 c a) (wC c a) (l1.reverse++pre)
       (yx c (pre++l1++mid)) mid.reverse
       (PN c b tb l2 pl2)=true) :
   q92 c ws onSurv preC pre pl=true:=by
 induction l1 generalizing pre preC pl with
 | nil =>
   cases hsp with
   | cons _ _ tl _ htl =>
     unfold q92;apply q5
     apply q127 c ws onSurv a ta pre mid l2 [] b tb preC tl htl (by simp [hC])
     intro pl2 hpl2;simpa using hstep pl2 hpl2
 | cons x t ih =>
   cases hsp with
   | cons w tg tl _ htl =>
     unfold q92;apply q4
     apply ih ((w,tg)::pre) _ tl htl (by rw [hC];exact q7 _ _)
     intro pl2 hpl2
     have hp:(((w,tg)::pre)++t++mid).Perm (pre++((w,tg)::t)++mid):=by
       simpa [lAA] using y8 (w,tg) pre (t++mid)
     rw [yo c hp]
     simpa [lRC,lAA] using hstep pl2 hpl2
lemma q81 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {ws:List (BFn n × Nat)}
   (htr:TR f 1 ws) :
   j6 c (eW rp c ws)=true:=by
 set rows:=aR n rp c
 have hlen_rows:=zl n rp c.shTT
 rcases htr.inv_succ with
   ⟨a,ta,r,save,hperm,_,_,_,_,_,_,_,hsub⟩ |
   ⟨a,ta,b,tb,r,ka,kb,hperm,_,_,_,_,_,_,_,_,_,hsub⟩ |
   ⟨a,ta,b,tb,r,ka,kb,hperm,_,_,_,_,_,_,_,_,_,hsub⟩
 . obtain ⟨tg,heq⟩:=hsub.inv_zero
   cases save <;> simp only [qk,List.cons.injEq,Prod.mk.injEq,bFT,↓reduceIte] at heq
   . obtain ⟨⟨hinv,_⟩,rfl⟩:=heq
     rw [List.perm_singleton.1 hperm];simp only [encWs,lMC,List.map_nil,j6,Nat.beq_eq]
     rw [← qv hc,hinv,hc.goalv_eq]
   . cases heq.2
 . obtain ⟨tg,heq⟩:=hsub.inv_zero
   cases ka <;> cases kb <;> simp only [qk,List.cons.injEq,Prod.mk.injEq,bFT,↓reduceIte] at heq
   . obtain ⟨⟨hj,_⟩,rfl⟩:=heq
     rcases List.perm_pair.1 hperm with rfl | rfl <;>
       simp only [encWs,lMC,List.map_nil,j6,bOT,Nat.beq_eq]
     . left;rw [← qc,hj,hc.goalv_eq]
     . left;rw [q7,← qc,hj,hc.goalv_eq]
   all_goals cases heq.2
 . obtain ⟨tg,heq⟩:=hsub.inv_zero
   cases ka <;> cases kb <;> simp only [qk,List.cons.injEq,Prod.mk.injEq,bFT,↓reduceIte] at heq
   . obtain ⟨⟨hm,_⟩,rfl⟩:=heq
     rcases List.perm_pair.1 hperm with rfl | rfl <;>
       simp only [encWs,lMC,List.map_nil,j6,bOT,Nat.beq_eq]
     . right;rw [← q9,hm,hc.goalv_eq]
     . right;rw [q108,← q9,hm,hc.goalv_eq]
   all_goals cases heq.2
lemma jc {α:Type} {a w : α} {ta:Nat} {r:List (α × Nat)} {save:Bool}
   (h:AllTagsLe3 ((a,ta)::r)):AllTagsLe3 ((w,if ta=3 then 2 else 0)::qk save (a,0) r):=by
 intro p hp
 rcases List.mem_cons.1 hp with rfl | hp2
 . dsimp only;split <;> omega
 . rcases (z4 _ _ _ _).1 hp2 with ⟨_,rfl⟩ | hp3
   . dsimp only;omega
   . exact h p (List.mem_cons_of_mem _ hp3)
lemma k5 {α:Type} {a b w : α} {ta tb:Nat} {r:List (α × Nat)} {ka kb:Bool}
   (h:AllTagsLe3 ((a,ta)::(b,tb)::r)) :
   AllTagsLe3 ((w,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)):=by
 intro p hp
 rcases List.mem_cons.1 hp with rfl | hp2
 . dsimp only;omega
 . rcases (z4 _ _ _ _).1 hp2 with ⟨_,rfl⟩ | hp3
   . dsimp only;split <;> omega
   . rcases (z4 _ _ _ _).1 hp3 with ⟨_,rfl⟩ | hp4
     . dsimp only;split <;> omega
     . exact h p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp4))
lemma yw {α:Type} {a b w : α} {ta tb:Nat} {r:List (α × Nat)} {ka kb:Bool}
   (h:AllTagsLe3 ((a,ta)::(b,tb)::r)) :
   AllTagsLe3 ((w,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)):=by
 intro p hp
 rcases List.mem_cons.1 hp with rfl | hp2
 . dsimp only;split <;> omega
 . rcases (z4 _ _ _ _).1 hp2 with ⟨_,rfl⟩ | hp3
   . dsimp only;omega
   . rcases (z4 _ _ _ _).1 hp3 with ⟨_,rfl⟩ | hp4
     . dsimp only;omega
     . exact h p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp4))
lemma kv {n:Nat} (a b:BFn n):joinF a b=joinF b a:=by funext x;simp [joinF,Bool.or_comm]
lemma ku {n:Nat} (a b:BFn n):meetF a b=meetF b a:=by funext x;simp [meetF,Bool.and_comm]
lemma q137 {α:Type} (ka kb:Bool) (a b : α) (r:List α) :
   (qk ka a (qk kb b r)).Perm (qk kb b (qk ka a r)):=by
 cases ka <;> cases kb <;> simp only [qk,bFT,↓reduceIte]
 . exact lPR _
 . exact lPR _
 . exact lPR _
 . exact List.Perm.swap _ _ _
lemma ql {α:Type} (l1 mid l2:List α) (a b : α) :
   (l1++a::mid++b::l2).Perm (a::b::(l1++mid++l2)):=by
 have h1:(l1++a::(mid++b::l2)).Perm (a::(l1++mid++b::l2)):=by
   simpa [lAA] using (lPM (a:=a) (l₁:=l1) (l₂:=mid++b::l2))
 have h2:(l1++mid++b::l2).Perm (b::(l1++mid++l2)) :=
   lPM (a:=b) (l₁:=l1++mid) (l₂:=l2)
 simpa [lAA] using h1.trans (lPC a h2)
lemma q135 (a b d:Nat):Nat.lor (Nat.lor d b) a=Nat.lor a (Nat.lor b d):=by
 rw [q7 _ a,q7 d b]
lemma jq {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} {a b:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (h:TR f s ((joinF a b,t)::r)) :
   Nat.lor (yx c (eW rp c r))
     (Nat.xor (Nat.lor (wi c (eL rp c a)) (wi c (eL rp c b)))
              (Nat.lor (q63 c (eL rp c a)) (q63 c (eL rp c b))))=c.lok:=by
 have h0:=zz hc (yd h)
 simp only [qy,yp,qc,q169 hc] at h0
 rw [q7];exact h0
lemma wq {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} {a b:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (h:TR f s ((meetF a b,t)::r)) :
   Nat.lor (yx c (eW rp c r))
     (Nat.xor (Nat.land (wi c (eL rp c a)) (wi c (eL rp c b)))
              (Nat.land (q63 c (eL rp c a)) (q63 c (eL rp c b))))=c.lok:=by
 have h0:=zz hc (yd h)
 simp only [qy,yp,q9,q121 hc] at h0
 rw [q7];exact h0
lemma zx {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} {w x:BFn n} {tw tx:Nat} {r:List (BFn n × Nat)}
   (h:TR f s ((w,tw)::(x,tx)::r)) :
   Nat.lor (Nat.lor (yx c (eW rp c r)) (wC c (eL rp c x)))
     (wC c (eL rp c w))=c.lok:=by
 have h0:=zz hc (yd h)
 simp only [qy,yp] at h0
 rw [q135];exact h0
lemma zp {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {a b:BFn n} {t1 t2:Nat} {r:List (BFn n × Nat)}
   (h:∀ u v,f u=false->f v=true->∃ p ∈ (joinF a b,t1)::(a,t2)::r,p.1 u=false/\p.1 v=true) :
   Nat.land (Nat.xor c.lok (v4 c (eW rp c r))) (wi c (eL rp c a))=0:=by
 apply q10 hc _ _ (eL rp c b)
 have h0:=q6 hc h
 simp only [qy,vo,qc] at h0
 rw [q7 (v4 c _),q7 (wU c (encL _ a)),qq];exact h0
lemma zn {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {a b:BFn n} {t1 t2:Nat} {r:List (BFn n × Nat)}
   (h:∀ u v,f u=false->f v=true->∃ p ∈ (meetF a b,t1)::(a,t2)::r,p.1 u=false/\p.1 v=true) :
   Nat.land (Nat.xor c.lok (v4 c (eW rp c r))) (k1 c (eL rp c a))=0:=by
 apply jb hc _ _ (eL rp c b)
 have h0:=q6 hc h
 simp only [qy,vo,q9] at h0
 rw [q7 (v4 c _),q7 (wU c (encL _ a)),qq];exact h0
lemma yj {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {w x:BFn n} {tw tx:Nat} {r:List (BFn n × Nat)} (hlen:((w,tw)::(x,tx)::r).length<=11)
   (hsym:∀ r0 r1 r2 r3 r4 r5:Fin n->Bool,
     f r0=true->f r1=true->f r2=true->f r3=false->f r4=false->f r5=false ->
     3<=(((w,tw)::(x,tx)::r).map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum) :
   z3 c (Nat.add (Nat.add (va c (eW rp c r)) (wV1 c (eL rp c x)))
     (yg c.sh1 c.m1 c.m12 (eL rp c w)))=true:=by
 have h1:=vt hc hlen hsym
 simp only [qy,w1] at h1
 have heq:Nat.add (Nat.add (va c (eW rp c r)) (wV1 c (eL rp c x)))
     (wV1 c (eL rp c w)) =
     Nat.add (wV1 c (eL rp c w))
       (Nat.add (wV1 c (eL rp c x)) (va c (eW rp c r))):=by
   simp only [v8];omega
 rw [show yg c.sh1 c.m1 c.m12 (eL rp c w)=wV1 c (eL rp c w) from rfl,heq]
 exact h1
lemma k2 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {a b:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (h:∀ u v,f u=false->f v=true->∃ p ∈ (joinF a b,t)::r,p.1 u=false/\p.1 v=true) :
   Nat.lor (v4 c (eW rp c r)) (wU c (Nat.lor (eL rp c a) (eL rp c b)))=c.lok:=by
 have h0:=q6 hc h
 simp only [qy,vo,qc] at h0;rw [q7];exact h0
lemma yt {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {a b:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (h:∀ u v,f u=false->f v=true->∃ p ∈ (meetF a b,t)::r,p.1 u=false/\p.1 v=true) :
   Nat.lor (v4 c (eW rp c r)) (wU c (Nat.land (eL rp c a) (eL rp c b)))=c.lok:=by
 have h0:=q6 hc h
 simp only [qy,vo,q9] at h0;rw [q7];exact h0
lemma kr {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {a b:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (htr:TR f s ((joinF a b,t)::r))
   (hlen:((joinF a b,t)::r).length=s+1) :
   qb c (zf c (eW rp c r)) (qi c.m0 (Nat.lor (wA0 c (eL rp c a)) (wA0 c (eL rp c b))))=true:=by
 have h0:=zi hc hs htr hlen
 unfold wV0 at h0;rw [q41,q198] at h0;exact h0
lemma k8 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {a b:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (htr:TR f s ((meetF a b,t)::r))
   (hlen:((meetF a b,t)::r).length=s+1) :
   qb c (zf c (eW rp c r)) (qi c.m0 (Nat.land (wA0 c (eL rp c a)) (wA0 c (eL rp c b))))=true:=by
 have h0:=zi hc hs htr hlen
 unfold wV0 at h0;rw [q40,q171] at h0;exact h0
lemma vq {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {a b x:BFn n} {t tx:Nat} {r:List (BFn n × Nat)}
   (htr:TR f s ((joinF a b,t)::(x,tx)::r))
   (hlen:((joinF a b,t)::(x,tx)::r).length=s+1) :
   qb c (Nat.add (zf c (eW rp c r)) (wV0 c (eL rp c x)))
     (qi c.m0 (Nat.lor (wA0 c (eL rp c a)) (wA0 c (eL rp c b))))=true:=by
 have h0:=zi hc hs htr hlen
 simp only [qy,k0] at h0
 rw [qt] at h0;unfold wV0 at h0;rw [q41,q198] at h0;exact h0
lemma vf {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {a b x:BFn n} {t tx:Nat} {r:List (BFn n × Nat)}
   (htr:TR f s ((meetF a b,t)::(x,tx)::r))
   (hlen:((meetF a b,t)::(x,tx)::r).length=s+1) :
   qb c (Nat.add (zf c (eW rp c r)) (wV0 c (eL rp c x)))
     (qi c.m0 (Nat.land (wA0 c (eL rp c a)) (wA0 c (eL rp c b))))=true:=by
 have h0:=zi hc hs htr hlen
 simp only [qy,k0] at h0
 rw [qt] at h0;unfold wV0 at h0;rw [q40,q171] at h0;exact h0
lemma q16 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {a:BFn n} {t:Nat} {r:List (BFn n × Nat)}
   (htr:TR f s ((invF a,t)::r))
   (hlen:((invF a,t)::r).length=s+1) :
   qb c (zf c (eW rp c r)) (qi c.m0 (Nat.xor (wA0 c (eL rp c a)) c.m0all))=true:=by
 have h0:=zi hc hs htr hlen
 unfold wV0 at h0;rw [qv hc,q170 hc] at h0;exact h0
lemma q15 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {a:BFn n} {t tx:Nat} {r:List (BFn n × Nat)}
   (htr:TR f s ((invF a,t)::(a,tx)::r))
   (hlen:((invF a,t)::(a,tx)::r).length=s+1) :
   qb c (Nat.add (zf c (eW rp c r)) (wV0 c (eL rp c a)))
     (qi c.m0 (Nat.xor (wA0 c (eL rp c a)) c.m0all))=true:=by
 have h0:=zi hc hs htr hlen
 simp only [qy,k0] at h0
 rw [qt] at h0;unfold wV0 at h0;rw [qv hc,q170 hc] at h0;exact h0
lemma jf {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {w:BFn n} {t:Nat} {r:List (BFn n × Nat)} (hlen:((w,t)::r).length<=11)
   (hsym:∀ r0 r1 r2 r3 r4 r5:Fin n->Bool,f r0=true->f r1=true->f r2=true->f r3=false->f r4=false->f r5=false ->
     3<=(((w,t)::r).map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum) :
   z3 c (Nat.add (va c (eW rp c r)) (yg c.sh1 c.m1 c.m12 (eL rp c w)))=true:=by
 have h0:=vt hc hlen hsym
 simp only [qy,w1] at h0;rw [qt] at h0;exact h0
lemma q17 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {ws_b:List (BFn n × Nat)}
   (htags:AllTagsLe3 ws_b)
   (htr:TR f (s+1) ws_b)
   (onSurv:List (Nat × Nat)->Bool)
   (hon:∀ zs_b,AllTagsLe3 zs_b ->
     TR f s zs_b ->
     onSurv (eW rp c zs_b)=true) :
   scanAll c s (eW rp c ws_b) onSurv=true:=by
 cases s with
 | zero => unfold scanAll;simp only [q0,↓reduceIte];exact q81 hc htr
 | succ s' =>
   have hs_nz:Nat.beq (s'+1) 0=false:=q2 (Nat.succ_ne_zero s')
   unfold scanAll;simp only [hs_nz,bFT,↓reduceIte]
   obtain ⟨pl,hprep,hsp⟩:=q82 c (eW rp c ws_b)
   rw [hprep];dsimp only;rw [q187,show (eW rp c ws_b).length=ws_b.length from lLM _]
   have hws_len_le:ws_b.length<=s'+3:=htr.len_le
   have hun_split:∀ {a ta r save},ws_b.Perm ((a,ta)::r) ->
       ta≠1->ta≠2->(ta=3->save=false) ->
       invF a≠(fun _ => false)->invF a≠(fun _ => true)->invF a≠a->(∀ x ∈ r,x.1≠invF a) ->
       TR f (s'+1) ((invF a,if ta=3 then 2 else 0)::qk save (a,0) r) ->
       ∃ l1 l2,ws_b=l1++(a,ta)::l2/\(save=true->ta=0) /\
         qj c.all1v (eW rp c ws_b) (eL rp c (invF a))=true /\
         AllTagsLe3 ((invF a,if ta=3 then 2 else 0)::qk save (a,0) (l1++l2)) /\
         TR f (s'+1)
           ((invF a,if ta=3 then 2 else 0)::qk save (a,0) (l1++l2)):=by
     intro a ta r save hp h1 h2 h3 h0 h1' hna hnr hsub
     have hvw:=jo hc ws_b (invF a) h0 h1' fun p hpm => by
       rcases List.mem_cons.1 (hp.subset hpm) with rfl | hpm2;exact hna.symm;exact hnr p hpm2
     have htags':=htags.perm hp
     have hta_le:ta<=3:=htags' (a,ta) (by simp)
     have hsave0:save=true->ta=0:=fun hst => by
       have hne3:ta≠3:=fun e => by rw [h3 e] at hst;cases hst
       omega
     obtain ⟨l1,l2,hws,hrp⟩:=q68 hp
     have hkp:((invF a,if ta=3 then 2 else 0)::qk save (a,0) r).Perm
         ((invF a,if ta=3 then 2 else 0)::qk save (a,0) (l1++l2)) :=
       lPC _ (by cases save <;> simp only [qk,bFT,↓reduceIte];exact hrp;exact hrp.cons _)
     exact ⟨l1,l2,hws,hsave0,hvw,(jc htags').perm hkp,TagRun.perm hkp hsub⟩
   have hor_split:∀ {a ta b tb r ka kb},ws_b.Perm ((a,ta)::(b,tb)::r) ->
       ta≠2->tb≠2->(ta=1->ka=false)->(tb=1->kb=false) ->
       joinF a b≠(fun _ => false)->joinF a b≠(fun _ => true)->joinF a b≠a->joinF a b≠b->(∀ x ∈ r,x.1≠joinF a b) ->
       TR f (s'+1)
         ((joinF a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)) ->
       ∃ l1 mid l2 a' ta' b' tb' ka' kb',ws_b=l1++(a',ta')::mid++(b',tb')::l2 /\
         ta'≠2/\tb'≠2/\(ta'=1->ka'=false)/\(tb'=1->kb'=false) /\
         qj c.all1v (eW rp c ws_b) (eL rp c (joinF a' b'))=true /\
         AllTagsLe3 ((joinF a' b',0)::qk ka' (a',if ta'=3 then 1 else 0) (qk kb' (b',if tb'=3 then 1 else 0) (l1++mid++l2))) /\
         TR f (s'+1)
           ((joinF a' b',0)::qk ka' (a',if ta'=3 then 1 else 0) (qk kb' (b',if tb'=3 then 1 else 0) (l1++mid++l2))):=by
     intro a ta b tb r ka kb hp hta htb hka hkb h0 h1 hna hnb hnr hsub
     have hvw:=jo hc ws_b (joinF a b) h0 h1 fun p hpm => by
       rcases List.mem_cons.1 (hp.subset hpm) with rfl | hpm2;exact hna.symm
       rcases List.mem_cons.1 hpm2 with rfl | hpm3;exact hnb.symm;exact hnr p hpm3
     have htags':=htags.perm hp
     rcases q67 hp with ⟨l1,mid,l2,hws,hrp⟩ | ⟨l1,mid,l2,hws,hrp⟩
     . have hkp:((joinF a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).Perm
           ((joinF a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) (l1++mid++l2))) :=
         lPC _ (by cases ka <;> cases kb <;> simp only [qk,bFT,↓reduceIte];exact hrp;exact hrp.cons _;exact hrp.cons _;exact (hrp.cons _).cons _)
       exact ⟨l1,mid,l2,a,ta,b,tb,ka,kb,hws,hta,htb,hka,hkb,hvw,(k5 htags').perm hkp,TagRun.perm hkp hsub⟩
     . have hkp:((joinF a b,0)::qk ka (a,if ta=3 then 1 else 0) (qk kb (b,if tb=3 then 1 else 0) r)).Perm
           ((joinF b a,0)::qk kb (b,if tb=3 then 1 else 0) (qk ka (a,if ta=3 then 1 else 0) (l1++mid++l2))):=by
         rw [kv b a];apply lPC;refine (q137 ka kb _ _ r).trans ?_
         cases kb <;> cases ka <;> simp only [qk,bFT,↓reduceIte];exact hrp;exact hrp.cons _;exact hrp.cons _;exact (hrp.cons _).cons _
       rw [kv a b] at hvw
       exact ⟨l1,mid,l2,b,tb,a,ta,kb,ka,hws,htb,hta,hkb,hka,hvw,(k5 htags').perm hkp,TagRun.perm hkp hsub⟩
   have hand_split:∀ {a ta b tb r ka kb},ws_b.Perm ((a,ta)::(b,tb)::r) ->
       ta≠1->tb≠1->(ta≠0->ka=false)->(tb≠0->kb=false) ->
       meetF a b≠(fun _ => false)->meetF a b≠(fun _ => true)->meetF a b≠a->meetF a b≠b->(∀ x ∈ r,x.1≠meetF a b) ->
       TR f (s'+1)
         ((meetF a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)) ->
       ∃ l1 mid l2 a' ta' b' tb' ka' kb',ws_b=l1++(a',ta')::mid++(b',tb')::l2 /\
         ta'≠1/\tb'≠1/\(ta'≠0->ka'=false)/\(tb'≠0->kb'=false) /\
         qj c.all1v (eW rp c ws_b) (eL rp c (meetF a' b'))=true /\
         AllTagsLe3 ((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::qk ka' (a',0) (qk kb' (b',0) (l1++mid++l2))) /\
         TR f (s'+1)
           ((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::qk ka' (a',0) (qk kb' (b',0) (l1++mid++l2))):=by
     intro a ta b tb r ka kb hp hta htb hka hkb h0 h1 hna hnb hnr hsub
     have hvw:=jo hc ws_b (meetF a b) h0 h1 fun p hpm => by
       rcases List.mem_cons.1 (hp.subset hpm) with rfl | hpm2;exact hna.symm
       rcases List.mem_cons.1 hpm2 with rfl | hpm3;exact hnb.symm;exact hnr p hpm3
     have htags':=htags.perm hp
     rcases q67 hp with ⟨l1,mid,l2,hws,hrp⟩ | ⟨l1,mid,l2,hws,hrp⟩
     . have hkp:((meetF a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)).Perm
           ((meetF a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) (l1++mid++l2))) :=
         lPC _ (by cases ka <;> cases kb <;> simp only [qk,bFT,↓reduceIte];exact hrp;exact hrp.cons _;exact hrp.cons _;exact (hrp.cons _).cons _)
       exact ⟨l1,mid,l2,a,ta,b,tb,ka,kb,hws,hta,htb,hka,hkb,hvw,(yw htags').perm hkp,TagRun.perm hkp hsub⟩
     . have hkp:((meetF a b,if ta=3\/tb=3 then 1 else 0)::qk ka (a,0) (qk kb (b,0) r)).Perm
           ((meetF b a,if tb=3\/ta=3 then 1 else 0)::qk kb (b,0) (qk ka (a,0) (l1++mid++l2))):=by
         have hcond:(if tb=3\/ta=3 then 1 else 0)=(if ta=3\/tb=3 then 1 else 0):=by
           by_cases h1:ta=3 <;> by_cases h2:tb=3 <;> simp [h1,h2]
         rw [ku b a,hcond]
         apply lPC;refine (q137 ka kb _ _ r).trans ?_
         cases kb <;> cases ka <;> simp only [qk,bFT,↓reduceIte];exact hrp;exact hrp.cons _;exact hrp.cons _;exact (hrp.cons _).cons _
       rw [ku a b] at hvw
       exact ⟨l1,mid,l2,b,tb,a,ta,kb,ka,hws,htb,hta,hkb,hka,hvw,(yw htags').perm hkp,TagRun.perm hkp hsub⟩
   have hacc_rest:∀ (l1 mid l2:List (BFn n × Nat)),
       Nat.lor (yx c ([]++eW rp c l1++eW rp c mid)) (yx c (eW rp c l2))=yx c (eW rp c (l1++mid++l2)) /\
       Nat.lor (v4 c ([]++eW rp c l1++eW rp c mid)) (v4 c (eW rp c l2))=v4 c (eW rp c (l1++mid++l2)) /\
       Nat.add (zf c ([]++eW rp c l1++eW rp c mid)) (zf c (eW rp c l2))=zf c (eW rp c (l1++mid++l2)) /\
       Nat.add (va c ([]++eW rp c l1++eW rp c mid)) (va c (eW rp c l2))=va c (eW rp c (l1++mid++l2)) /\
       qx ((eW rp c l1).reverse++[]) (qx (eW rp c mid).reverse (eW rp c l2))=eW rp c (l1++mid++l2):=by
     intro l1 mid l2
     refine ⟨?_,?_,?_,?_,?_⟩
     . rw [← vc];simp [encWs,lAA]
     . rw [← zu];simp [encWs,lAA]
     . rw [← zy];simp [encWs,lAA]
     . rw [← y6];simp [encWs,lAA]
     . simp [q18,encWs,lAA]
   generalize hsl:Nat.sub (Nat.add (s'+1) 2) ws_b.length=slack
   cases slack with
   | zero =>
     have hlen:ws_b.length=s'+3:=by simp at hsl;omega
     have hup:v4 c (eW rp c ws_b)=c.lok:=q6 hc (qf htr hlen)
     simp only [hup,q0,bTA]
     rcases htr.inv_succ with
       ⟨a,ta,r,save,hp,_,_,_,_,_,_,_,hsub⟩ |
       ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩ |
       ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩
     . have hle:=hsub.len_le;have hp_len:=hp.length_eq
       cases save <;> simp [qk] at hlen hle hp_len <;> omega
     . obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',_,_,hvw,htc,hsub'⟩ :=
         hor_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
       have hle:=hsub'.len_le;have hl_eq:l1.length+mid.length+l2.length+2=s'+3:=by have:=congrArg List.length hws;simp at this;omega
       cases ka' <;> cases kb' <;> simp only [qk,bFT,↓reduceIte,lLC,lLA] at hle <;> try omega
       simp only [qk,bFT,↓reduceIte] at htc hsub'
       have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
         simpa [hws,encWs,lAA] using hsp
       apply q97 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 pl hsp' rfl rfl
       intro pl2 hpl2;unfold ke;dsimp only;rw [hpl2.pToList]
       obtain ⟨_,hU,hV0,_,hR⟩:=hacc_rest l1 mid l2;rw [hU,hV0,hR]
       apply q5
       have hch_len:((joinF a' b',0)::(l1++mid++l2)).length=s'+2:=by simp;omega
       have hch_up:=k2 hc (qf hsub' hch_len)
       have ⟨hm1,hm2⟩:=y4 hc _ _ _ hch_up
       have hval0:=kr hc hs hsub' hch_len
       have hsurv:=hon _ htc hsub'
       simp only [q2 hta',q2 htb',bNF,wk hm1 hm2,q0,hval0,← qc,hvw,bTA]
       exact hsurv
     . obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',_,_,hvw,htc,hsub'⟩ :=
         hand_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
       have hle:=hsub'.len_le;have hl_eq:l1.length+mid.length+l2.length+2=s'+3:=by have:=congrArg List.length hws;simp at this;omega
       cases ka' <;> cases kb' <;> simp only [qk,bFT,↓reduceIte,lLC,lLA] at hle <;> try omega
       simp only [qk,bFT,↓reduceIte] at htc hsub'
       have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
         simpa [hws,encWs,lAA] using hsp
       apply q97 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 pl hsp' rfl rfl
       intro pl2 hpl2;unfold ke;dsimp only;rw [hpl2.pToList]
       obtain ⟨_,hU,hV0,_,hR⟩:=hacc_rest l1 mid l2;rw [hU,hV0,hR]
       apply q4;apply q5
       have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+2:=by simp;omega
       have hch_up:=yt hc (qf hsub' hch_len)
       have ⟨hm1,hm2⟩:=vw hc _ _ _ hch_up
       have hval0:=k8 hc hs hsub' hch_len
       have hsurv:=hon _ htc hsub'
       have hwt:(if (ta'.beq 3||tb'.beq 3)=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [bOT,Nat.beq_eq]
       simp only [q2 hta',q2 htb',bNF,wk hm1 hm2,q0,hval0,← q9,hvw,hwt,bTA]
       exact hsurv
   | succ slack' =>
     cases slack' with
     | zero =>
       have hlen:ws_b.length=s'+2:=by simp at hsl;omega
       have hlen11:ws_b.length<=11:=by omega
       cases hsym1:z3 c (va c (eW rp c ws_b))
       . have hno_sym : ¬ (∀ r0 r1 r2 r3 r4 r5:Fin n->Bool,f r0=true->f r1=true->f r2=true->f r3=false->f r4=false->f r5=false ->
             3<=(ws_b.map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum) :=
           fun h => by rw [vt hc hlen11 h] at hsym1;cases hsym1
         have hup:v4 c (eW rp c ws_b)=c.lok:=q6 hc ((qh htr hlen).resolve_right hno_sym)
         simp only [bFT,↓reduceIte,hup,q0,bTA]
         rcases htr.inv_succ with
           ⟨a,ta,r,save,hp,_,_,_,_,_,_,_,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩
         . exfalso;have hle:=hsub.len_le;have hp_len:=hp.length_eq
           cases save
           . apply hno_sym;intro r0 r1 r2 r3 r4 r5 h0' h1' h2' h3' h4' h5'
             have hv:=kk hsub (by simp [qk] at hlen hp_len ⊢;omega) r0 r1 r2 r3 r4 r5 h0' h1' h2' h3' h4' h5'
             have hle_s:∀ l:List (BFn n × Nat),(l.map fun p => v6 (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum <=
                 (l.map fun p => zq (p.1 r0) (p.1 r1) (p.1 r2) (p.1 r3) (p.1 r4) (p.1 r5)).sum:=by
               intro l;induction l with | nil => simp | cons x t iht => simp only [lMC,List.sum_cons];have:=k7 (x.1 r0) (x.1 r1) (x.1 r2) (x.1 r3) (x.1 r4) (x.1 r5);omega
             have hs1:=le_trans hv (hle_s _)
             simp only [qk,bFT,↓reduceIte,lMC,List.sum_cons,invF,jp] at hs1
             rw [(hp.map _).sum_eq];exact hs1
           . simp [qk] at hlen hle hp_len;omega
         . obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hor_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hle:=hsub'.len_le;have hl_eq:l1.length+mid.length+l2.length+2=s'+2:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q65 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 pl hsp' rfl rfl
           intro pl2 hpl2;unfold vx;dsimp only;rw [hpl2.pToList]
           obtain ⟨_,hU,hV0,_,hR⟩:=hacc_rest l1 mid l2;rw [hU,hV0,hR]
           apply q5
           simp only [q2 hta',q2 htb',bOS,bFT,↓reduceIte]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hch_len:((joinF a' b',0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hch_up_p:=(qh hsub' hch_len).resolve_right fun hcs => hno_sym fun r0 r1 r2 r3 r4 r5 h0' h1' h2' h3' h4' h5' => by
               have h1s:=hcs r0 r1 r2 r3 r4 r5 h0' h1' h2' h3' h4' h5'
               rw [hws,((ql l1 mid l2 _ _).map _).sum_eq]
               simp only [lMC,List.sum_cons,joinF] at h1s ⊢
               have:=q14 (a' r0) (a' r1) (a' r2) (a' r3) (a' r4) (a' r5) (b' r0) (b' r1) (b' r2) (b' r3) (b' r4) (b' r5);omega
             have hch_up:=k2 hc hch_up_p
             have ⟨hm1,hm2⟩:=y4 hc _ _ _ hch_up
             have hsurv:=hon _ htc hsub'
             simp only [hm1,hm2,q0,↓reduceIte];apply q5
             simp only [bTA,← qc,hvw];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb1:tb'≠1:=fun e => by have:=hkb' e;cases this
             have hch_len:((joinF a' b',0)::(b',if tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hm2:Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (wi c (eL rp c b'))=0:=by
               have h0:=qf hsub' hch_len;rw [kv] at h0;exact zp hc h0
             have hval0:=vq hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             have htb3:(if tb'.beq 3=true then 1 else 0)=(if tb'=3 then 1 else 0):=by simp [Nat.beq_eq]
             have hokB:Nat.beq (Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (wi c (eL rp c b'))) 0=true:=qz hm2
             split
             . apply q4;apply q4
               simp only [q2 htb1,bNF,hokB,hval0,← qc,hvw,bTA,htb3];exact hsurv
             . simp only [hokB,q2 htb1,bNF,bTA,↓reduceIte,hval0,← qc,hvw,htb3];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta1:ta'≠1:=fun e => by have:=hka' e;cases this
             have hch_len:((joinF a' b',0)::(a',if ta'=3 then 1 else 0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hm1:=zp hc (qf hsub' hch_len)
             have hval0:=vq hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             have hta3:(if ta'.beq 3=true then 1 else 0)=(if ta'=3 then 1 else 0):=by simp [Nat.beq_eq]
             simp only [hm1,q0,↓reduceIte]
             apply q4;apply q5
             simp only [q2 hta1,bNF,hval0,← qc,hvw,bTA,hta3];exact hsurv
           . simp only [qk,↓reduceIte,lLC,lLA] at hle;omega
         . obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hand_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hle:=hsub'.len_le;have hl_eq:l1.length+mid.length+l2.length+2=s'+2:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q65 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 pl hsp' rfl rfl
           intro pl2 hpl2;unfold vx;dsimp only;rw [hpl2.pToList]
           obtain ⟨_,hU,hV0,_,hR⟩:=hacc_rest l1 mid l2;rw [hU,hV0,hR]
           apply q4;apply q5
           have hwt:(if (ta'.beq 3||tb'.beq 3)=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [bOT,Nat.beq_eq]
           simp only [q2 hta',q2 htb',bOS,bFT,↓reduceIte]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hch_up_p:=(qh hsub' hch_len).resolve_right fun hcs => hno_sym fun r0 r1 r2 r3 r4 r5 h0' h1' h2' h3' h4' h5' => by
               have h1s:=hcs r0 r1 r2 r3 r4 r5 h0' h1' h2' h3' h4' h5'
               rw [hws,((ql l1 mid l2 _ _).map _).sum_eq]
               simp only [lMC,List.sum_cons,meetF] at h1s ⊢
               have:=je (a' r0) (a' r1) (a' r2) (a' r3) (a' r4) (a' r5) (b' r0) (b' r1) (b' r2) (b' r3) (b' r4) (b' r5);omega
             have hch_up:=yt hc hch_up_p
             have ⟨hm1,hm2⟩:=vw hc _ _ _ hch_up
             have hsurv:=hon _ htc hsub'
             simp only [hm1,hm2,q0,↓reduceIte];apply q5
             simp only [bTA,← q9,hvw,hwt];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb0:tb'=0:=Classical.byContradiction fun hne => by have:=hkb' hne;cases this
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(b',0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hm2:Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (k1 c (eL rp c b'))=0:=by
               have h0:=qf hsub' hch_len;rw [ku] at h0;exact zn hc h0
             have hval0:=vf hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             have hokB:Nat.beq (Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (k1 c (eL rp c b'))) 0=true:=qz hm2
             have hwt0:(if ta'.beq 3=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by subst htb0;simp [Nat.beq_eq]
             split
             . apply q4;apply q4
               rw [hwt];simp only [qz htb0,hokB,hval0,← q9,hvw,bTA];exact hsurv
             . rw [hwt0];simp only [hokB,qz htb0,bTA,↓reduceIte,hval0,← q9,hvw];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta0:ta'=0:=Classical.byContradiction fun hne => by have:=hka' hne;cases this
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(a',0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hm1:=zn hc (qf hsub' hch_len)
             have hval0:=vf hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             simp only [hm1,q0,↓reduceIte]
             apply q4;apply q5
             rw [hwt];simp only [qz hta0,hval0,← q9,hvw,bTA];exact hsurv
           . simp only [qk,↓reduceIte,lLC,lLA] at hle;omega
       ·
         simp only [↓reduceIte,bOT]
         rcases htr.inv_succ with
           ⟨a,ta,r,save,hp,hta1,hta2,hta3,h0,h1,hna,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩
         . left
           obtain ⟨l1,l2,hws,_,hvw,htc,hsub'⟩:=hun_split hp hta1 hta2 hta3 h0 h1 hna hnr hsub
           have hle:=hsub'.len_le;have hl_eq:l1.length+l2.length+1=s'+2:=by have:=congrArg List.length hws;simp at this;omega
           cases save
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hch_len:((invF a,if ta=3 then 2 else 0)::(l1++l2)).length=s'+2:=by simp;omega
             have hch_up:Nat.lor (v4 c (eW rp c (l1++l2))) (Nat.land (wC c (eL rp c a)) (wi c (eL rp c a)))=c.lok:=by
               have h0u:=q6 hc (qf hsub' hch_len)
               simp only [qy,vo,qv hc,q168 hc] at h0u
               rw [q7];exact h0u
             have hval0:=q16 hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             have hsp':PListSpec c pl (eW rp c l1++(eL rp c a,ta)::eW rp c l2):=by simpa [hws,encWs] using hsp
             apply q130 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c l2) [] (eL rp c a) ta 0 0 pl hsp' rfl rfl
             intro pl2 hpl2;unfold w7;dsimp only;rw [hpl2.pToList,q18];apply q5
             have h1u:Nat.lor (v4 c ([]++eW rp c l1)) (v4 c (eW rp c l2))=v4 c (eW rp c (l1++l2)):=by rw [← zu];simp [encWs]
             have h1v:Nat.add (zf c ([]++eW rp c l1)) (zf c (eW rp c l2))=zf c (eW rp c (l1++l2)):=by rw [← zy];simp [encWs]
             have hta3b:(if ta.beq 3=true then 2 else 0)=(if ta=3 then 2 else 0):=by simp [Nat.beq_eq]
             simp only [h1u,h1v,lANil,lRR,← kj,q2 hta1,q2 hta2,
               bNF,hch_up,q0,hval0,← qv hc,hvw,hta3b,bTA]
             exact hsurv
           . simp only [qk,↓reduceIte,lLC,lLA] at hle;omega
         . right
           obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hor_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hle:=hsub'.len_le;have hl_eq:l1.length+mid.length+l2.length+2=s'+2:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q95 c (eW rp c ws_b) (Nat.beq (v4 c (eW rp c ws_b)) c.lok) onSurv
             (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 0 0 pl hsp' rfl rfl rfl rfl
           intro pl2 hpl2;unfold kd;dsimp only;rw [hpl2.pToList]
           obtain ⟨hC,hU,hV0,hV1,hR⟩:=hacc_rest l1 mid l2;rw [hC,hU,hV0,hV1,hR]
           apply q5
           simp only [q2 hta',q2 htb',bOS,bFT,↓reduceIte]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hch_len:((joinF a' b',0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hcov:=jq hc hsub'
             have hsurv:=hon _ htc hsub'
             rcases qh hsub' hch_len with hcu | hcs
             . have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
                 obtain ⟨p,hpm,h1u,h2v⟩:=zk (t1:=0) (t2:=0) (ka:=false) (kb:=false) (hcu u v hu hv)
                 exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
               have hch_up:=k2 hc hcu
               have ⟨hm1,hm2⟩:=y4 hc _ _ _ hch_up
               simp only [hws_up,q0,↓reduceIte];apply q5
               simp only [hcov,q0,hm1,hm2,bTA,bTOR,← qc,hvw];exact hsurv
             . have hcs':=jf hc (by omega:((joinF a' b',0)::(l1++mid++l2)).length<=11) hcs
               split
               . apply q5;simp only [hcov,q0,← qc,hcs',bOTR,bTA,hvw];exact hsurv
               . simp only [hcov,q0,← qc,hcs',bTA,hvw];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb1:tb'≠1:=fun e => by have:=hkb' e;cases this
             have hch_len:((joinF a' b',0)::(b',if tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hcu:=qf hsub' hch_len
             have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
               obtain ⟨p,hpm,h1u,h2v⟩:=zk (t1:=0) (ka:=false) (kb:=true) (hcu u v hu hv)
               exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
             have hm2:Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (wi c (eL rp c b'))=0:=by
               rw [kv] at hcu;exact zp hc hcu
             have hval0:=vq hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             have htb3:(if tb'.beq 3=true then 1 else 0)=(if tb'=3 then 1 else 0):=by simp [Nat.beq_eq]
             simp only [hws_up,q0,↓reduceIte];apply q4;apply q4
             simp only [q2 htb1,bNF,hm2,q0,hval0,← qc,hvw,bTA,htb3];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta1:ta'≠1:=fun e => by have:=hka' e;cases this
             have hch_len:((joinF a' b',0)::(a',if ta'=3 then 1 else 0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hcu:=qf hsub' hch_len
             have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
               obtain ⟨p,hpm,h1u,h2v⟩:=zk (t2:=0) (ka:=true) (kb:=false) (hcu u v hu hv)
               exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
             have hm1:=zp hc hcu
             have hval0:=vq hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             have hta3:(if ta'.beq 3=true then 1 else 0)=(if ta'=3 then 1 else 0):=by simp [Nat.beq_eq]
             simp only [hws_up,q0,↓reduceIte];apply q4;apply q5
             simp only [q2 hta1,bNF,hm1,q0,hval0,← qc,hvw,bTA,hta3];exact hsurv
           . simp only [qk,↓reduceIte,lLC,lLA] at hle;omega
         . right
           obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hand_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hle:=hsub'.len_le;have hl_eq:l1.length+mid.length+l2.length+2=s'+2:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q95 c (eW rp c ws_b) (Nat.beq (v4 c (eW rp c ws_b)) c.lok) onSurv
             (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 0 0 pl hsp' rfl rfl rfl rfl
           intro pl2 hpl2;unfold kd;dsimp only;rw [hpl2.pToList]
           obtain ⟨hC,hU,hV0,hV1,hR⟩:=hacc_rest l1 mid l2;rw [hC,hU,hV0,hV1,hR]
           apply q4;apply q5
           have hwt:(if (ta'.beq 3||tb'.beq 3)=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [bOT,Nat.beq_eq]
           simp only [q2 hta',q2 htb',bOS,bFT,↓reduceIte]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hcov:=wq hc hsub'
             have hsurv:=hon _ htc hsub'
             rcases qh hsub' hch_len with hcu | hcs
             . have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
                 obtain ⟨p,hpm,h1u,h2v⟩:=za (t1:=0) (t2:=0) (ka:=false) (kb:=false) (hcu u v hu hv)
                 exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
               have hch_up:=yt hc hcu
               have ⟨hm1,hm2⟩:=vw hc _ _ _ hch_up
               simp only [hws_up,q0,↓reduceIte];apply q5
               simp only [hcov,q0,hm1,hm2,bTA,bTOR,← q9,hvw,hwt];exact hsurv
             . have hcs':=jf hc (by omega:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(l1++mid++l2)).length<=11) hcs
               split
               . apply q5;simp only [hcov,q0,← q9,hcs',bOTR,bTA,hvw,hwt];exact hsurv
               . simp only [hcov,q0,← q9,hcs',bTA,hvw,hwt];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb0:tb'=0:=Classical.byContradiction fun hne => by have:=hkb' hne;cases this
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(b',0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hcu:=qf hsub' hch_len
             have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
               obtain ⟨p,hpm,h1u,h2v⟩:=za (t1:=0) (ka:=false) (kb:=true) (hcu u v hu hv)
               exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
             have hm2:Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (k1 c (eL rp c b'))=0:=by
               rw [ku] at hcu;exact zn hc hcu
             have hval0:=vf hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             simp only [hws_up,q0,↓reduceIte];apply q4;apply q4
             rw [hwt];simp only [qz htb0,hm2,q0,hval0,← q9,hvw,bTA];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta0:ta'=0:=Classical.byContradiction fun hne => by have:=hka' hne;cases this
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(a',0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hcu:=qf hsub' hch_len
             have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
               obtain ⟨p,hpm,h1u,h2v⟩:=za (t2:=0) (ka:=true) (kb:=false) (hcu u v hu hv)
               exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
             have hm1:=zn hc hcu
             have hval0:=vf hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             simp only [hws_up,q0,↓reduceIte];apply q4;apply q5
             rw [hwt];simp only [qz hta0,hm1,q0,hval0,← q9,hvw,bTA];exact hsurv
           . simp only [qk,↓reduceIte,lLC,lLA] at hle;omega
     | succ slack'' =>
       cases slack'' with
       | zero =>
         have hlen:ws_b.length=s'+1:=by simp at hsl;omega
         simp only [bOT]
         rcases htr.inv_succ with
           ⟨a,ta,r,save,hp,hta1,hta2,hta3,h0,h1,hna,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩
         . left
           obtain ⟨l1,l2,hws,hsave0,hvw,htc,hsub'⟩:=hun_split hp hta1 hta2 hta3 h0 h1 hna hnr hsub
           have hl_eq:l1.length+l2.length+1=s'+1:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a,ta)::eW rp c l2):=by simpa [hws,encWs] using hsp
           apply q128 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c l2) [] (eL rp c a) ta 0 0 0 0 pl hsp' rfl rfl rfl rfl
           intro pl2 hpl2;unfold w6;dsimp only;rw [hpl2.pToList,q18];apply q5
           have h1c:Nat.lor (yx c ([]++eW rp c l1)) (yx c (eW rp c l2))=yx c (eW rp c (l1++l2)):=by rw [← vc];simp [encWs]
           have h1u:Nat.lor (v4 c ([]++eW rp c l1)) (v4 c (eW rp c l2))=v4 c (eW rp c (l1++l2)):=by rw [← zu];simp [encWs]
           have h1v0:Nat.add (zf c ([]++eW rp c l1)) (zf c (eW rp c l2))=zf c (eW rp c (l1++l2)):=by rw [← zy];simp [encWs]
           have h1v1:Nat.add (va c ([]++eW rp c l1)) (va c (eW rp c l2))=va c (eW rp c (l1++l2)):=by rw [← y6];simp [encWs]
           simp only [h1c,h1u,h1v0,h1v1,lANil,lRR,q2 hta1,q2 hta2,
             bOS,bFT,↓reduceIte,bOT]
           cases save
           . left;simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hch_len:((invF a,if ta=3 then 2 else 0)::(l1++l2)).length=s'+1:=by simp;omega
             have hcov:Nat.lor (yx c (eW rp c (l1++l2))) (wC c (eL rp c a))=c.lok:=by
               have hc0:=zz hc (yd hsub')
               simp only [qy,yp,qv hc,q197 hc] at hc0;rw [q7];exact hc0
             have hor_u:(Nat.beq (Nat.lor (v4 c (eW rp c (l1++l2))) (Nat.land (wC c (eL rp c a)) (wi c (eL rp c a)))) c.lok ||
                 z3 c (Nat.add (va c (eW rp c (l1++l2))) (wV1 c (eL rp c a))))=true:=by
               rcases qh hsub' hch_len with hcu | hcs
               . have h0u:=q6 hc hcu
                 simp only [qy,vo,qv hc,q168 hc] at h0u
                 rw [q7] at h0u;rw [h0u,q0];rfl
               . have h1s:=vt hc (by omega:((invF a,if ta=3 then 2 else 0)::(l1++l2)).length<=11) hcs
                 simp only [qy,w1,qv hc,q200 hc] at h1s
                 have hcomm:Nat.add (va c (eW rp c (l1++l2))) (wV1 c (eL rp c a)) =
                     Nat.add (wV1 c (eL rp c a)) (va c (eW rp c (l1++l2))):=by simp;omega
                 rw [hcomm,h1s];simp
             have hsurv:=hon _ htc hsub'
             have hta3b:(if ta.beq 3=true then 2 else 0)=(if ta=3 then 2 else 0):=by simp [Nat.beq_eq]
             simp only [hcov,q0,hor_u,← qv hc,hvw,hta3b,← kj,bTA];exact hsurv
           . right;have hta0:=hsave0 rfl;simp only [qk,↓reduceIte,hta0] at htc hsub'
             have h03:(if (0:Nat)=3 then 2 else 0)=0:=rfl
             rw [h03] at htc hsub'
             have hch_len:((invF a,0)::(a,0)::(l1++l2)).length=s'+2:=by simp;omega
             have hch_up:Nat.lor (v4 c (eW rp c (l1++l2))) (wC c (eL rp c a))=c.lok:=by
               have h0u:=q6 hc (qf hsub' hch_len)
               simp only [qy,vo,qv hc] at h0u
               rw [← qq,q78 hc,q7] at h0u;exact h0u
             have hval0:=q15 hc hs hsub' hch_len
             have hsurv:=hon _ htc hsub'
             simp only [hta0,q0,hch_up,hval0,← qv hc,hvw,← kj,bTA];exact hsurv
         . right
           obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hor_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hl_eq:l1.length+mid.length+l2.length+2=s'+1:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q93 c (eW rp c ws_b) (Nat.beq (v4 c (eW rp c ws_b)) c.lok) (zf c (eW rp c ws_b)) onSurv
             (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 0 pl hsp' rfl rfl rfl
           intro pl2 hpl2;unfold kc;dsimp only;rw [hpl2.pToList]
           obtain ⟨hC,hU,_,hV1,hR⟩:=hacc_rest l1 mid l2;rw [hC,hU,hV1,hR]
           apply q5
           have hta3b:(if ta'.beq 3=true then 1 else 0)=(if ta'=3 then 1 else 0):=by simp [Nat.beq_eq]
           have htb3b:(if tb'.beq 3=true then 1 else 0)=(if tb'=3 then 1 else 0):=by simp [Nat.beq_eq]
           simp only [q2 hta',q2 htb',bOS,bFT,↓reduceIte]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hcov:=jq hc hsub';have hsurv:=hon _ htc hsub'
             split <;> simp only [hcov,q0,← qc,hvw,bTA,bOT]
             . left;left;left;exact hsurv
             . left;left;exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb1:tb'≠1:=fun e => by have:=hkb' e;cases this
             have hch_len:((joinF a' b',0)::(b',if tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hcov:=zx hc hsub';rw [q41,q169 hc] at hcov
             have hsurv:=hon _ htc hsub'
             rcases qh hsub' hch_len with hcu | hcs
             . have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
                 obtain ⟨p,hpm,h1u,h2v⟩:=zk (t1:=0) (ka:=false) (kb:=true) (hcu u v hu hv)
                 exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
               have hm2:Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (wi c (eL rp c b'))=0:=by
                 rw [kv] at hcu;exact zp hc hcu
               simp only [hws_up,q0,↓reduceIte,bOT];left;right
               simp only [q2 htb1,bNF,hcov,hm2,q0,bTOR,← qc,hvw,htb3b,bTA]
               exact hsurv
             . have h2s:=yj hc (by omega:((joinF a' b',0)::(b',if tb'=3 then 1 else 0)::(l1++mid++l2)).length<=11) hcs
               split <;> simp only [bOT]
               . left;right;simp only [q2 htb1,bNF,hcov,q0,← qc,h2s,bOTR,hvw,htb3b,bTA];exact hsurv
               . right;simp only [q2 htb1,bNF,hcov,q0,← qc,h2s,hvw,htb3b,bTA];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta1:ta'≠1:=fun e => by have:=hka' e;cases this
             have hch_len:((joinF a' b',0)::(a',if ta'=3 then 1 else 0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hcov:=zx hc hsub';rw [q41,q169 hc] at hcov
             have hsurv:=hon _ htc hsub'
             rcases qh hsub' hch_len with hcu | hcs
             . have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
                 obtain ⟨p,hpm,h1u,h2v⟩:=zk (t2:=0) (ka:=true) (kb:=false) (hcu u v hu hv)
                 exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
               have hm1:=zp hc hcu
               simp only [hws_up,q0,↓reduceIte,bOT];left;left;right
               simp only [q2 hta1,bNF,hcov,hm1,q0,bTOR,← qc,hvw,hta3b,bTA]
               exact hsurv
             . have h2s:=yj hc (by omega:((joinF a' b',0)::(a',if ta'=3 then 1 else 0)::(l1++mid++l2)).length<=11) hcs
               split <;> simp only [bOT]
               . left;left;right;simp only [q2 hta1,bNF,hcov,q0,← qc,h2s,bOTR,hvw,hta3b,bTA];exact hsurv
               . left;right;simp only [q2 hta1,bNF,hcov,q0,← qc,h2s,hvw,hta3b,bTA];exact hsurv
           . simp only [qk,↓reduceIte] at htc hsub'
             have hta1:ta'≠1:=fun e => by have:=hka' e;cases this
             have htb1:tb'≠1:=fun e => by have:=hkb' e;cases this
             have hch_len:((joinF a' b',0)::(a',if ta'=3 then 1 else 0)::(b',if tb'=3 then 1 else 0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
               obtain ⟨p,hpm,h1u,h2v⟩:=zk (ka:=true) (kb:=true) (qf hsub' hch_len u v hu hv)
               exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
             have htot_eq:zf c (eW rp c ((a',if ta'=3 then 1 else 0)::(b',if tb'=3 then 1 else 0)::(l1++mid++l2)))=zf c (eW rp c ws_b):=by
               have h1:zf c (eW rp c ws_b)=zf c (eW rp c ((a',ta')::(b',tb')::(l1++mid++l2))):=by
                 rw [hws];exact vu c ((ql l1 mid l2 _ _).map _)
               rw [h1];rfl
             have hval0:=kr hc hs hsub' hch_len;rw [htot_eq] at hval0
             have hsurv:=hon _ htc hsub'
             simp only [hws_up,q0,↓reduceIte,bOT];right
             simp only [q2 hta1,q2 htb1,bNF,hval0,← qc,hvw,hta3b,htb3b,bTA]
             exact hsurv
         . right
           obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hand_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hl_eq:l1.length+mid.length+l2.length+2=s'+1:=by have:=congrArg List.length hws;simp at this;omega
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q93 c (eW rp c ws_b) (Nat.beq (v4 c (eW rp c ws_b)) c.lok) (zf c (eW rp c ws_b)) onSurv
             (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 0 0 pl hsp' rfl rfl rfl
           intro pl2 hpl2;unfold kc;dsimp only;rw [hpl2.pToList]
           obtain ⟨hC,hU,_,hV1,hR⟩:=hacc_rest l1 mid l2;rw [hC,hU,hV1,hR]
           apply q4;apply q5
           have hwt:(if (ta'.beq 3||tb'.beq 3)=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [bOT,Nat.beq_eq]
           have hwt_or:(if ta'.beq 3=true\/tb'.beq 3=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [Nat.beq_eq]
           simp only [q2 hta',q2 htb',bOS,bFT,↓reduceIte]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hcov:=wq hc hsub';have hsurv:=hon _ htc hsub'
             split <;> simp only [hcov,q0,← q9,hvw,bTA,bOT,hwt_or]
             . left;left;left;exact hsurv
             . left;left;exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb0:tb'=0:=Classical.byContradiction fun hne => by have:=hkb' hne;cases this
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(b',0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hcov:=zx hc hsub';rw [q40,q121 hc] at hcov
             have hsurv:=hon _ htc hsub'
             rcases qh hsub' hch_len with hcu | hcs
             . have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
                 obtain ⟨p,hpm,h1u,h2v⟩:=za (t1:=0) (ka:=false) (kb:=true) (hcu u v hu hv)
                 exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
               have hm2:Nat.land (Nat.xor c.lok (v4 c (eW rp c (l1++mid++l2)))) (k1 c (eL rp c b'))=0:=by
                 rw [ku] at hcu;exact zn hc hcu
               simp only [hws_up,q0,↓reduceIte,bOT];left;right
               rw [hwt_or];simp only [qz htb0,hcov,hm2,q0,bTOR,← q9,hvw,bTA];exact hsurv
             . have h2s:=yj hc (by omega:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(b',0)::(l1++mid++l2)).length<=11) hcs
               split <;> simp only [bOT]
               . left;right;simp only [hwt_or,qz htb0,hcov,q0,← q9,h2s,bOTR,hvw,bTA];exact hsurv
               . right;simp only [hwt_or,qz htb0,hcov,q0,← q9,h2s,hvw,bTA];exact hsurv
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta0:ta'=0:=Classical.byContradiction fun hne => by have:=hka' hne;cases this
             have hch_len:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(a',0)::(l1++mid++l2)).length=s'+1:=by simp;omega
             have hcov:=zx hc hsub';rw [q40,q121 hc] at hcov
             have hsurv:=hon _ htc hsub'
             rcases qh hsub' hch_len with hcu | hcs
             . have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
                 obtain ⟨p,hpm,h1u,h2v⟩:=za (t2:=0) (ka:=true) (kb:=false) (hcu u v hu hv)
                 exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
               have hm1:=zn hc hcu
               simp only [hws_up,q0,↓reduceIte,bOT];left;left;right
               rw [hwt_or];simp only [qz hta0,hcov,hm1,q0,bTOR,← q9,hvw,bTA];exact hsurv
             . have h2s:=yj hc (by omega:((meetF a' b',if ta'=3\/tb'=3 then 1 else 0)::(a',0)::(l1++mid++l2)).length<=11) hcs
               split <;> simp only [bOT]
               . left;left;right;simp only [hwt_or,qz hta0,hcov,q0,← q9,h2s,bOTR,hvw,bTA];exact hsurv
               . left;right;simp only [hwt_or,qz hta0,hcov,q0,← q9,h2s,hvw,bTA];exact hsurv
           . have hta0:ta'=0:=Classical.byContradiction fun hne => by have:=hka' hne;cases this
             have htb0:tb'=0:=Classical.byContradiction fun hne => by have:=hkb' hne;cases this
             simp only [qk,↓reduceIte,hta0,htb0] at htc hsub'
             have h03:(if (0:Nat)=3\/(0:Nat)=3 then 1 else 0)=0:=by decide
             rw [h03] at htc hsub'
             have hch_len:((meetF a' b',0)::(a',0)::(b',0)::(l1++mid++l2)).length=s'+2:=by simp;omega
             have hws_up:v4 c (eW rp c ws_b)=c.lok:=q6 hc fun u v hu hv => by
               obtain ⟨p,hpm,h1u,h2v⟩:=za (ka:=true) (kb:=true) (qf hsub' hch_len u v hu hv)
               exact ⟨p,by rw [hws];exact (ql l1 mid l2 _ _).symm.subset hpm,h1u,h2v⟩
             have hch_perm:((meetF a' b',0)::(a',0)::(b',0)::(l1++mid++l2)).Perm ((meetF a' b',0)::ws_b):=by
               apply lPC;rw [hws,hta0,htb0];exact (ql l1 mid l2 _ _).symm
             have hval0:=k8 hc hs (TagRun.perm hch_perm hsub') (by rw [← hch_perm.length_eq];exact hch_len)
             have hsurv:=hon _ (htc.perm hch_perm) (TagRun.perm hch_perm hsub')
             simp only [hws_up,q0,↓reduceIte,bOT];right
             simp only [hta0,htb0,q0,hval0,← q9,hvw,bTA];exact hsurv
       | succ _ =>
         simp only [bOT]
         rcases htr.inv_succ with
           ⟨a,ta,r,save,hp,hta1,hta2,hta3,h0,h1,hna,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩ |
           ⟨a,ta,b,tb,r,ka,kb,hp,hta,htb,hka,hkb,h0,h1,hna,hnb,hnr,hsub⟩
         . left
           obtain ⟨l1,l2,hws,hsave0,hvw,htc,hsub'⟩:=hun_split hp hta1 hta2 hta3 h0 h1 hna hnr hsub
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a,ta)::eW rp c l2):=by simpa [hws,encWs] using hsp
           apply q126 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c l2) [] (eL rp c a) ta 0 pl hsp' rfl
           intro pl2 hpl2;unfold w5;dsimp only;rw [hpl2.pToList,q18];apply q5
           have h1c:Nat.lor (yx c ([]++eW rp c l1)) (yx c (eW rp c l2))=yx c (eW rp c (l1++l2)):=by rw [← vc];simp [encWs]
           simp only [h1c,lANil,lRR,q2 hta1,q2 hta2,
             bNF,bTA,← qv hc,hvw,bOT]
           cases save
           . left;simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hcov:Nat.lor (yx c (eW rp c (l1++l2))) (wC c (eL rp c a))=c.lok:=by
               have hc0:=zz hc (yd hsub')
               simp only [qy,yp,qv hc,q197 hc] at hc0;rw [q7];exact hc0
             have hsurv:=hon _ htc hsub'
             have hta3b:(if ta.beq 3=true then 2 else 0)=(if ta=3 then 2 else 0):=by simp [Nat.beq_eq]
             simp only [hcov,q0,bTA,hta3b,← kj];exact hsurv
           . right;have hta0:=hsave0 rfl;simp only [qk,↓reduceIte,hta0] at htc hsub'
             have h03:(if (0:Nat)=3 then 2 else 0)=0:=rfl;rw [h03] at htc hsub'
             have hch_perm:((invF a,0)::(a,0)::(l1++l2)).Perm ((invF a,0)::ws_b) :=
               lPC _ (by rw [hws,hta0];exact List.perm_middle.symm)
             have hsurv:=hon _ (htc.perm hch_perm) (TagRun.perm hch_perm hsub')
             simp only [hta0,q0,bTA];exact hsurv
         . right
           obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hor_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q91 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 pl hsp' rfl
           intro pl2 hpl2;unfold k9;dsimp only;rw [hpl2.pToList]
           obtain ⟨hC,_,_,_,hR⟩:=hacc_rest l1 mid l2;rw [hC,hR]
           apply q5
           have hta3b:(if ta'.beq 3=true then 1 else 0)=(if ta'=3 then 1 else 0):=by simp [Nat.beq_eq]
           have htb3b:(if tb'.beq 3=true then 1 else 0)=(if tb'=3 then 1 else 0):=by simp [Nat.beq_eq]
           simp only [q2 hta',q2 htb',bNF,bTA,← qc,hvw,bOT]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             left;left;left;simp only [jq hc hsub',q0,bTA];exact hon _ htc hsub'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb1:tb'≠1:=fun e => by have:=hkb' e;cases this
             have hcov:=zx hc hsub';rw [q41,q169 hc] at hcov
             left;right;simp only [q2 htb1,bNF,hcov,q0,htb3b,bTA];exact hon _ htc hsub'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta1:ta'≠1:=fun e => by have:=hka' e;cases this
             have hcov:=zx hc hsub';rw [q41,q169 hc] at hcov
             left;left;right;simp only [q2 hta1,bNF,hcov,q0,hta3b,bTA];exact hon _ htc hsub'
           . simp only [qk,↓reduceIte] at htc hsub'
             have hta1:ta'≠1:=fun e => by have:=hka' e;cases this
             have htb1:tb'≠1:=fun e => by have:=hkb' e;cases this
             right;simp only [q2 hta1,q2 htb1,bNF,hta3b,htb3b,bTA];exact hon _ htc hsub'
         . right
           obtain ⟨l1,mid,l2,a',ta',b',tb',ka',kb',hws,hta',htb',hka',hkb',hvw,htc,hsub'⟩ :=
             hand_split hp hta htb hka hkb h0 h1 hna hnb hnr hsub
           have hsp':PListSpec c pl (eW rp c l1++(eL rp c a',ta')::eW rp c mid++(eL rp c b',tb')::eW rp c l2):=by
             simpa [hws,encWs,lAA] using hsp
           apply q91 c (eW rp c ws_b) onSurv (eW rp c l1) (eW rp c mid) (eW rp c l2) [] (eL rp c a') ta' (eL rp c b') tb' 0 pl hsp' rfl
           intro pl2 hpl2;unfold k9;dsimp only;rw [hpl2.pToList]
           obtain ⟨hC,_,_,_,hR⟩:=hacc_rest l1 mid l2;rw [hC,hR]
           apply q4;apply q5
           have hwt_or:(if ta'.beq 3=true\/tb'.beq 3=true then 1 else 0)=(if ta'=3\/tb'=3 then 1 else 0):=by simp [Nat.beq_eq]
           simp only [q2 hta',q2 htb',bNF,bTA,← q9,hvw,bOT,hwt_or]
           cases ka' <;> cases kb'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             left;left;left;simp only [wq hc hsub',q0,bTA];exact hon _ htc hsub'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have htb0:tb'=0:=Classical.byContradiction fun hne => by have:=hkb' hne;cases this
             have hcov:=zx hc hsub';rw [q40,q121 hc] at hcov
             left;right;simp only [qz htb0,q0,hcov,bTA];exact hon _ htc hsub'
           . simp only [qk,bFT,↓reduceIte] at htc hsub'
             have hta0:ta'=0:=Classical.byContradiction fun hne => by have:=hka' hne;cases this
             have hcov:=zx hc hsub';rw [q40,q121 hc] at hcov
             left;left;right;simp only [qz hta0,q0,hcov,bTA];exact hon _ htc hsub'
           . have hta0:ta'=0:=Classical.byContradiction fun hne => by have:=hka' hne;cases this
             have htb0:tb'=0:=Classical.byContradiction fun hne => by have:=hkb' hne;cases this
             simp only [qk,↓reduceIte,hta0,htb0] at htc hsub'
             have h03:(if (0:Nat)=3\/(0:Nat)=3 then 1 else 0)=0:=by decide
             rw [h03] at htc hsub'
             have hch_perm:((meetF a' b',0)::(a',0)::(b',0)::(l1++mid++l2)).Perm ((meetF a' b',0)::ws_b):=by
               apply lPC;rw [hws,hta0,htb0];exact (ql l1 mid l2 _ _).symm
             right;simp only [hta0,htb0,q0,bTA]
             exact hon _ (htc.perm hch_perm) (TagRun.perm hch_perm hsub')
lemma wj {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   {s:Nat} (hs:s<=10) {ws_b:List (BFn n × Nat)}
   (htags:AllTagsLe3 ws_b)
   (htr:TR f (s+1) ws_b) :
   scanInline c s (eW rp c ws_b)=true:=by
 rw [wu]
 exact q17 hc hs htags htr (fun _ => true) (fun _ _ _ => rfl)
def ki {n:Nat}:Nat->List (BFn n × Nat)->BFn n × Nat
 | _,[] => ((fun _ => false),0)
 | 0,a::_ => a
 | k+1,_::rest => ki k rest
def yl {n:Nat}:Nat->List (BFn n × Nat)->List (BFn n × Nat)
 | _,[] => []
 | 0,_::rest => rest
 | k+1,a::rest => a::yl k rest
def q136 {n:Nat} (code:Nat) (ws:List (BFn n × Nat)):List (BFn n × Nat) :=
 if Nat.ble code 32 then
   let c:=Nat.sub code 1;let i:=Nat.shiftRight c 1;let save:=Nat.beq (Nat.land c 1) 1
   let (a,ta):=ki i ws;let wt:=if Nat.beq ta 3 then 2 else 0
   let w:=invF a;let r:=yl i ws
   if save then (w,wt)::(a,0)::r else (w,wt)::r
 else
   let rem:=Nat.sub code 33
   let kb:=Nat.beq (Nat.land rem 1) 1
   let ka:=Nat.beq (Nat.land (Nat.shiftRight rem 1) 1) 1
   let conj:=Nat.beq (Nat.land (Nat.shiftRight rem 2) 1) 1
   let (i,j):=q42 (Nat.shiftRight rem 3) 16 1
   let (a,ta):=ki i ws;let (b,tb):=ki j ws
   let r:=yl i (yl j ws)
   if conj then
     let wt:=if Nat.beq ta 3||Nat.beq tb 3 then 1 else 0
     let r1:=if kb then (b,0)::r else r
     let r2:=if ka then (a,0)::r1 else r1
     (meetF a b,wt)::r2
   else
     let r1:=if kb then (b,if Nat.beq tb 3 then 1 else 0)::r else r
     let r2:=if ka then (a,if Nat.beq ta 3 then 1 else 0)::r1 else r1
     (joinF a b,0)::r2
def q31 {n:Nat} (xs_b:List (BFn n × Nat)) (PT:Nat->Nat):Nat->Nat->Nat->List (BFn n × Nat)
 | 0,_,_ => xs_b
 | d+1,s,j =>
   let e:=q192 (PT s) j;let code:=Nat.land e 1023
   if Nat.beq code 0 then xs_b
   else q136 code (q31 xs_b PT d (Nat.add s 1) (Nat.land (Nat.shiftRight e 10) 8191))
def RgenB {n:Nat} (cap:Nat) (xs_b:List (BFn n × Nat)) (PT:Nat->Nat) (s j:Nat):List (BFn n × Nat) :=
 q31 xs_b PT (Nat.sub cap s) s j
lemma q27 {n:Nat} (rows:List Nat) (i:Nat) (ws:List (BFn n × Nat)) :
   jw i (encWs rows ws)=(encL rows (ki i ws).1,(ki i ws).2):=by
 induction i generalizing ws with
 | zero => cases ws with | nil => simp [jw,ki,encWs,q39] | cons _ _ => rfl
 | succ k ih => cases ws with | nil => simp [jw,ki,encWs,q39] | cons _ t => exact ih t
lemma q28 {n:Nat} (rows:List Nat) (i:Nat) (ws:List (BFn n × Nat)) :
   q38 i (encWs rows ws)=encWs rows (yl i ws):=by
 induction i generalizing ws with
 | zero => cases ws <;> rfl
 | succ k ih => cases ws with | nil => rfl | cons p t => simp only [qy,q38,yl,ih]
lemma q153 {n:Nat} (rows:List Nat) (code:Nat) (ws:List (BFn n × Nat)) :
   q203 (2 ^ rows.length - 1) code (encWs rows ws)=encWs rows (q136 code ws):=by
 unfold q203 q136;simp only [v5]
 split
 . simp only [q27,q28];split <;> simp [encWs,q145]
 . simp only [q27,q28]
   split
   . cases Nat.beq (Nat.land (Nat.sub code 33) 1) 1 <;> cases Nat.beq (Nat.land (Nat.shiftRight (Nat.sub code 33) 1) 1) 1 <;> simp [encWs,q9]
   . cases Nat.beq (Nat.land (Nat.sub code 33) 1) 1 <;> cases Nat.beq (Nat.land (Nat.shiftRight (Nat.sub code 33) 1) 1) 1 <;> simp [encWs,qc]
lemma q119 {n:Nat} (rows:List Nat) (xs_b:List (BFn n × Nat)) (PT:Nat->Nat) (d s j:Nat) :
   q120 (2 ^ rows.length - 1) (encWs rows xs_b) PT d s j=encWs rows (q31 xs_b PT d s j):=by
 induction d generalizing s j with
 | zero => rfl
 | succ d ih => simp only [q120,q31,v5];split;rfl;rw [ih,q153]
lemma q102 {n:Nat} (rows:List Nat) (cap:Nat) (xs_b:List (BFn n × Nat)) (PT:Nat->Nat) (s j:Nat) :
   Rgen (2 ^ rows.length - 1) cap (encWs rows xs_b) PT s j=encWs rows (RgenB cap xs_b PT s j) :=
 q119 rows xs_b PT (Nat.sub cap s) s j
lemma q150 {n:Nat} (cap:Nat) (xs_b:List (BFn n × Nat)) (PT:Nat->Nat) (s j:Nat) :
   Rgen (2 ^ (2 ^ n) - 1) cap (encTTWs n xs_b) PT s j=encTTWs n (RgenB cap xs_b PT s j):=by
 have hlen:(List.range (2 ^ n)).length=2 ^ n:=List.length_range
 simpa [encTTWs,encWs,encTT,hlen] using q102 (List.range (2 ^ n)) cap xs_b PT s j
lemma wm {n:Nat} (i:Nat) (ws:List (BFn n × Nat)):(yl i ws).Sublist ws:=by
 induction i generalizing ws with
 | zero => cases ws with | nil => exact List.Sublist.slnil | cons a t => exact List.Sublist.cons a (List.Sublist.refl t)
 | succ k ih => cases ws with | nil => exact List.Sublist.slnil | cons a t => exact List.Sublist.cons_cons a (ih t)
lemma vj {α:Type} (b:Bool) (x : α × Nat) (l:List (α × Nat))
   (hx:x.2<=3) (hl:AllTagsLe3 l):AllTagsLe3 (if b then x::l else l):=by
 intro p hp;cases b
 . exact hl p hp
 . rcases List.mem_cons.1 hp with rfl | h'
   . exact hx
   . exact hl p h'
lemma vn {α:Type} (x : α × Nat) (l:List (α × Nat))
   (hx:x.2<=3) (hl:AllTagsLe3 l):AllTagsLe3 (x::l):=by
 intro p hp;rcases List.mem_cons.1 hp with rfl | h';exact hx;exact hl p h'
lemma q43 {n:Nat} (code:Nat) {ws:List (BFn n × Nat)} (h:AllTagsLe3 ws) :
   AllTagsLe3 (q136 code ws):=by
 unfold q136
 have her:∀ i,AllTagsLe3 (yl i ws):=fun i p hp => h p ((wm i ws).subset hp)
 have her2:∀ i j,AllTagsLe3 (yl i (yl j ws)):=fun i j p hp => her j p ((wm i _).subset hp)
 split
 . dsimp only;split
   . exact vn _ _ (by split <;> omega) (vn _ _ (by omega) (her _))
   . exact vn _ _ (by split <;> omega) (her _)
 . dsimp only;split
   . exact vn _ _ (by split <;> omega)
       (vj _ _ _ (by omega) (vj _ _ _ (by omega) (her2 _ _)))
   . exact vn _ _ (by omega)
       (vj _ _ _ (by split <;> omega) (vj _ _ _ (by split <;> omega) (her2 _ _)))
lemma q59 {n:Nat} (cap:Nat) {xs_b:List (BFn n × Nat)} (h:AllTagsLe3 xs_b)
   (PT:Nat->Nat) (s j:Nat):AllTagsLe3 (RgenB cap xs_b PT s j):=by
 unfold RgenB;generalize Nat.sub cap s=d
 induction d generalizing s j with
 | zero => exact h
 | succ d ih => simp only [q31];split;exact h;exact q43 _ (ih _ _)
lemma q195 (T h fuel lo hi:Nat) (hlo:lo < hi):q167 T h fuel lo hi < hi:=by
 induction fuel generalizing lo hi with
 | zero => exact hlo
 | succ fuel ih =>
   simp only [q167,v5];split
   . rename_i hle;have hle':lo+2<=hi:=Eq.mp Nat.ble_eq hle
     have hdiv:Nat.div (Nat.add lo hi) 2=(lo+hi) / 2:=rfl
     have hmid_lt:Nat.div (Nat.add lo hi) 2 < hi:=by rw [hdiv];omega
     have hlo_lt_mid:lo < Nat.div (Nat.add lo hi) 2:=by rw [hdiv];omega
     split;exact ih _ hi hmid_lt;exact lt_trans (ih lo _ hlo_lt_mid) hmid_lt
   . exact hlo
lemma j8 (NN FL HT:Nat->Nat) (s h:Nat) (hne:q85 NN FL HT s h≠999999) :
   q85 NN FL HT s h < NN s:=by
 unfold q85 at hne ⊢;simp only [v5] at hne ⊢
 cases hz:Nat.beq (NN s) 0
 . rw [hz] at hne;simp only [bFT,↓reduceIte] at hne ⊢
   have hpos : 0 < NN s:=by have:=y3 hz;omega
   cases hm:Nat.beq (q205 (HT s) (q167 (HT s) h (FL s) 0 (NN s))) h
   . rw [hm] at hne;simp only [bFT,↓reduceIte] at hne;exact absurd rfl hne
   . simp only [↓reduceIte];exact q195 (HT s) h (FL s) 0 (NN s) hpos
 . rw [hz] at hne;exact absurd rfl hne
lemma q181 (a b:Nat × Nat):twEq a b=true ↔ a=b:=by
 rcases a with ⟨a1,a2⟩;rcases b with ⟨b1,b2⟩;simp [twEq,Nat.beq_eq]
lemma q142 (x:Nat × Nat) (bs bs':List (Nat × Nat)) (h:jy x bs=some bs'):bs.Perm (x::bs'):=by
 induction bs generalizing bs' with
 | nil => simp [jy] at h
 | cons a t ih =>
   simp only [jy] at h;split at h
   . rename_i heq;cases h;rw [(q181 x a).1 heq]
   . cases he:jy x t with
     | none => rw [he] at h;cases h
     | some r => rw [he] at h;cases h;exact (lPC a (ih r he)).trans (List.Perm.swap x a r)
lemma y5 (xs ys:List (Nat × Nat)) (h:jk xs ys=true):xs.Perm ys:=by
 induction xs generalizing ys with
 | nil => cases ys with | nil => exact List.Perm.nil | cons _ _ => simp [jk] at h
 | cons a t ih =>
   simp only [jk] at h
   cases he:jy a ys with
   | none => rw [he] at h;cases h
   | some ys' => rw [he] at h;exact (lPC a (ih ys' h)).trans (q142 a ys ys' he).symm
lemma q113 (x:Nat × Nat) (xs:List (Nat × Nat)):(q62 x xs).Perm (x::xs):=by
 induction xs with | nil => exact lPR _ | cons a t ih => simp only [q62];split;exact lPR _;exact (lPC a ih).trans (List.Perm.swap x a t)
lemma q64 (xs:List (Nat × Nat)):(q125 xs).Perm xs:=by
 induction xs with | nil => exact List.Perm.nil | cons a t ih => exact (q113 a (q125 t)).trans (lPC a ih)
lemma kg {n:Nat} (rp shTT:Nat) (ws:List (BFn n × Nat)) :
   q72 shTT (encWs (allRows n rp shTT) ws)=encTTWs n ws:=by
 induction ws with
 | nil => rfl
 | cons p t ih =>
   rcases p with ⟨g,tg⟩;simp only [qy,q49,q72,v5,ih]
   have hsh:=q116 (n:=n) (q106 rp shTT) g
   rw [jj rp shTT] at hsh;rw [allRows,hsh]
lemma yk {n:Nat} {f:BFn n} {g:List (Nat × Nat × Nat × Nat)} (hg:vh f g) (ws:List (BFn n × Nat)) :
   ∃ π:(Fin n->Bool)->(Fin n->Bool),Function.Bijective π/\(∀ x,f (π x)=f x) /\
     wx g (encTTWs n ws)=encTTWs n (ws.map fun p => ((fun x => p.1 (π x)),p.2)):=by
 obtain ⟨π,hbij,hfix,happ⟩:=hg;refine ⟨π,hbij,hfix,?_⟩
 induction ws with | nil => rfl | cons p t ih => rcases p with ⟨h,tg⟩;simp only [q49,lMC,wx,v5,happ,ih]
lemma yv {α β:Type} {f : α->β} (hf:Function.Injective f) :
   ∀ {xs ys:List α},(xs.map f).Perm (ys.map f)->xs.Perm ys
 | [],ys,hp => by cases ys with | nil => exact List.Perm.nil | cons _ _ => exact absurd hp.length_eq (by simp)
 | x::xs,ys,hp => by
   have hmem:f x ∈ ys.map f:=hp.subset (by simp)
   obtain ⟨y,hy,heq⟩:=List.mem_map.1 hmem
   have hxy:y=x:=hf heq;subst hxy
   obtain ⟨l1,l2,rfl⟩:=List.append_of_mem hy
   have hp2:(f y::xs.map f).Perm (f y::(l1++l2).map f) :=
     hp.trans (by simpa [lMA] using (lPM (a:=f y) (l₁:=l1.map f) (l₂:=l2.map f)))
   exact (lPC y (yv hf (List.Perm.cons_inv hp2))).trans List.perm_middle.symm
lemma zv {n:Nat} (xs ys:List (BFn n × Nat)):(encTTWs n xs).Perm (encTTWs n ys) ↔ xs.Perm ys:=by
 constructor
 . intro hp
   have hinj:Function.Injective (fun p:BFn n × Nat => (encTT n p.1,p.2)):=fun ⟨_,_⟩ ⟨_,_⟩ e => by
     simp only [Prod.mk.injEq] at e;exact Prod.ext (yc e.1) e.2
   exact yv hinj hp
 . exact fun hp => hp.map _
lemma q19 {n:Nat} {f:BFn n} {g:List (Nat × Nat × Nat × Nat)} (hg:vh f g)
   (ws:List (Nat × Nat)) (ws_b:List (BFn n × Nat)) (hp:ws.Perm (encTTWs n ws_b)) :
   ∃ π:(Fin n->Bool)->(Fin n->Bool),Function.Bijective π/\(∀ x,f (π x)=f x) /\
     (q69 g ws).Perm (encTTWs n (ws_b.map fun p => ((fun x => p.1 (π x)),p.2))):=by
 unfold q69;dsimp only;split
 . obtain ⟨π,hbij,hfix,hmg⟩:=yk hg ws_b;refine ⟨π,hbij,hfix,?_⟩
   have hmap_eq:∀ l,wx g l=l.map (fun p => (ym g p.1,p.2)):=fun l => by
     induction l with | nil => rfl | cons p t ih => simp [wx,v5,ih]
   have hmgp:(wx g ws).Perm (wx g (encTTWs n ws_b)):=by rw [hmap_eq,hmap_eq];exact hp.map _
   exact (q64 _).trans (hmgp.trans (by rw [hmg]))
 . exact ⟨id,Function.bijective_id,fun _ => rfl,by simpa using hp⟩
lemma q20 {n:Nat} {f:BFn n} (gens:List (List (Nat × Nat × Nat × Nat)))
   (hgens:∀ g ∈ gens,vh f g) (ws:List (Nat × Nat)) (ws_b:List (BFn n × Nat)) (hp:ws.Perm (encTTWs n ws_b)) :
   ∃ π:(Fin n->Bool)->(Fin n->Bool),Function.Bijective π/\(∀ x,f (π x)=f x) /\
     (q35 gens ws).Perm (encTTWs n (ws_b.map fun p => ((fun x => p.1 (π x)),p.2))):=by
 induction gens generalizing ws ws_b with
 | nil => exact ⟨id,Function.bijective_id,fun _ => rfl,by simpa [q35] using hp⟩
 | cons g rest ih =>
   obtain ⟨π1,hb1,hf1,hp1⟩:=q19 (hgens g (by simp)) ws ws_b hp
   obtain ⟨π2,hb2,hf2,hp2⟩:=ih (fun g' hm => hgens g' (List.mem_cons_of_mem g hm)) (q69 g ws) _ hp1
   exact ⟨π1 ∘ π2,hb1.comp hb2,fun x => by simp [hf1,hf2],by simpa [q35,lMMp,fCD] using hp2⟩
lemma q152 {n:Nat} {f:BFn n} (gens:List (List (Nat × Nat × Nat × Nat)))
   (hgens:∀ g ∈ gens,vh f g) (ws_b:List (BFn n × Nat)) :
   ∃ π:(Fin n->Bool)->(Fin n->Bool),Function.Bijective π/\(∀ x,f (π x)=f x) /\
     (q186 gens (encTTWs n ws_b)).Perm (encTTWs n (ws_b.map fun p => ((fun x => p.1 (π x)),p.2))):=by
 unfold q186;have hs0:=q64 (encTTWs n ws_b)
 cases gens with
 | nil => exact ⟨id,Function.bijective_id,fun _ => rfl,by simpa using hs0⟩
 | cons g rest =>
   cases rest with
   | nil => exact q19 (hgens g (by simp)) _ ws_b hs0
   | cons g2 rest2 =>
     obtain ⟨π1,hb1,hf1,hp1⟩:=q20 (g::g2::rest2) hgens _ ws_b hs0
     obtain ⟨π2,hb2,hf2,hp2⟩:=q20 (g::g2::rest2) hgens _ _ hp1
     exact ⟨π1 ∘ π2,hb1.comp hb2,fun x => by simp [hf1,hf2],by simpa [lMMp,fCD] using hp2⟩
def w2 {n:Nat} (f:BFn n) (rows:List Nat) (NN:Nat->Nat)
   (R_bfn:Nat->Nat->List (BFn n × Nat)) (findFn:Nat->List (Nat × Nat)->Bool):Prop :=
 ∀ s zs_b,findFn s (encWs rows zs_b)=true ->
   ∃ j < NN s,∃ π:(Fin n->Bool)->(Fin n->Bool),
     Function.Bijective π/\(∀ x,f (π x)=f x) /\
     (zs_b.map fun p => ((fun x => p.1 (π x)),p.2)).Perm (R_bfn s j)
lemma q87 {n:Nat} (f:BFn n) (rp shTT salt:Nat) (NN FL HT:Nat->Nat)
   (R_bfn:Nat->Nat->List (BFn n × Nat)) (Rtt:Nat->Nat->List (Nat × Nat))
   (hRtt:∀ s j,Rtt s j=encTTWs n (R_bfn s j)) :
   w2 f (allRows n rp shTT) NN R_bfn (findAut1 shTT salt Rtt NN FL HT):=by
 intro s zs_b h;unfold findAut1 at h
 simp only [v5,kg,bAT,bNT,zh] at h
 obtain ⟨hne,hpeq⟩:=h;rw [hRtt] at hpeq
 exact ⟨_,j8 NN FL HT s _ hne,id,Function.bijective_id,fun _ => rfl,
   by simpa using (zv zs_b (R_bfn s _)).1 (y5 _ _ hpeq)⟩
lemma q86 {n:Nat} (f:BFn n) (rp shTT salt:Nat)
   (g0:List (Nat × Nat × Nat × Nat)) (hg0:vh f g0) (NN FL HT:Nat->Nat)
   (R_bfn:Nat->Nat->List (BFn n × Nat)) (Rtt:Nat->Nat->List (Nat × Nat))
   (hRtt:∀ s j,Rtt s j=encTTWs n (R_bfn s j)) :
   w2 f (allRows n rp shTT) NN R_bfn (findAut2 shTT salt g0 Rtt NN FL HT):=by
 intro s zs_b h;unfold findAut2 at h;simp only [v5,kg] at h
 split at h
 . rename_i h0;simp only [bAT,bNT,zh] at h0
   obtain ⟨hne,hpeq⟩:=h0;rw [hRtt] at hpeq
   exact ⟨_,j8 NN FL HT s _ hne,id,Function.bijective_id,fun _ => rfl,
     by simpa using (zv zs_b (R_bfn s _)).1 (y5 _ _ hpeq)⟩
 . simp only [bAT,bNT,zh] at h
   obtain ⟨hne,hpeq⟩:=h;obtain ⟨π,hbij,hfix,hmg⟩:=yk hg0 zs_b
   rw [hmg] at hne hpeq;rw [hRtt] at hpeq
   exact ⟨_,j8 NN FL HT s _ hne,π,hbij,hfix,(zv _ _).1 (y5 _ _ hpeq)⟩
lemma q37 {n:Nat} (f:BFn n) (rp shTT salt:Nat)
   (path:List (List (Nat × Nat × Nat × Nat))) (hpath:∀ g ∈ path,vh f g)
   (NN FL HT:Nat->Nat) (R_bfn:Nat->Nat->List (BFn n × Nat)) (Rtt:Nat->Nat->List (Nat × Nat))
   (hRtt:∀ s j,Rtt s j=encTTWs n (R_bfn s j)) :
   w2 f (allRows n rp shTT) NN R_bfn (findAutPath shTT salt path Rtt NN FL HT):=by
 have hloop:∀ p:List (List (Nat × Nat × Nat × Nat)),(∀ g ∈ p,vh f g)->∀ s (zs_b:List (BFn n × Nat)),
     vm salt Rtt NN FL HT s p (encTTWs n zs_b)=true ->
     ∃ j < NN s,∃ π:(Fin n->Bool)->(Fin n->Bool),Function.Bijective π/\(∀ x,f (π x)=f x) /\
       (zs_b.map fun q => ((fun x => q.1 (π x)),q.2)).Perm (R_bfn s j):=by
   intro p;induction p with
   | nil =>
     intro _ s zs_b h
     simp only [vm,v5,bAT,bNT,zh] at h
     obtain ⟨hne,hpeq⟩:=h;rw [hRtt] at hpeq
     exact ⟨_,j8 NN FL HT s _ hne,id,Function.bijective_id,fun _ => rfl,
       by simpa using (zv zs_b (R_bfn s _)).1 (y5 _ _ hpeq)⟩
   | cons g rest ih =>
     intro hp s zs_b h;simp only [vm,v5] at h
     split at h
     . rename_i h0;simp only [bAT,bNT,zh] at h0
       obtain ⟨hne,hpeq⟩:=h0;rw [hRtt] at hpeq
       exact ⟨_,j8 NN FL HT s _ hne,id,Function.bijective_id,fun _ => rfl,
         by simpa using (zv zs_b (R_bfn s _)).1 (y5 _ _ hpeq)⟩
     . obtain ⟨π1,hb1,hf1,hmg⟩:=yk (hp g (by simp)) zs_b;rw [hmg] at h
       obtain ⟨j,hj,π2,hb2,hf2,hperm⟩:=ih (fun g' hm => hp g' (List.mem_cons_of_mem g hm)) s _ h
       exact ⟨j,hj,π1 ∘ π2,hb1.comp hb2,fun x => by simp [hf1,hf2],by simpa [lMMp,fCD] using hperm⟩
 intro s zs_b h;unfold findAutPath at h;rw [kg] at h;exact hloop path hpath s zs_b h
lemma q55 {n:Nat} (f:BFn n) (rp shTT salt:Nat)
   (gens:List (List (Nat × Nat × Nat × Nat))) (hgens:∀ g ∈ gens,vh f g)
   (aut:Nat->List (Nat × Nat × Nat × Nat)) (haut:∀ k,vh f (aut k))
   (NN FL HT PT:Nat->Nat) (R_bfn:Nat->Nat->List (BFn n × Nat)) (Rtt:Nat->Nat->List (Nat × Nat))
   (hRtt:∀ s j,Rtt s j=encTTWs n (R_bfn s j)) :
   w2 f (allRows n rp shTT) NN R_bfn (findAutGen shTT salt gens aut Rtt NN FL HT PT):=by
 intro s zs_b h;unfold findAutGen at h;simp only [v5,kg] at h
 split at h;· cases h
 . rename_i hne_b
   have hne:=y3 (Bool.eq_false_iff.2 hne_b)
   set j:=q85 NN FL HT s (q75 salt (q186 gens (encTTWs n zs_b)))
   have hj:j < NN s:=j8 NN FL HT s _ hne
   set aidx:=Nat.shiftRight (q192 (PT s) j) 23
   obtain ⟨π1,hb1,hf1,hori⟩:=q152 gens hgens zs_b
   obtain ⟨π2,hb2,hf2,hmg⟩:=yk (haut aidx) (R_bfn s j)
   rw [hRtt,hmg] at h
   have hperm_b:=(zv _ _).1 (hori.symm.trans (y5 _ _ h))
   obtain ⟨π2_inv,hleft,hright⟩:=Function.bijective_iff_has_inverse.1 hb2
   have hinv_bij:Function.Bijective π2_inv:=Function.bijective_iff_has_inverse.2 ⟨π2,hright,hleft⟩
   have hinv_fix:∀ x,f (π2_inv x)=f x:=fun x => by have:=hf2 (π2_inv x);rw [hright x] at this;exact this.symm
   refine ⟨j,hj,π1 ∘ π2_inv,hb1.comp hinv_bij,fun x => by simp [hf1,hinv_fix],?_⟩
   have hmap_inv:=hperm_b.map (fun p:BFn n × Nat => ((fun x => p.1 (π2_inv x)),p.2))
   have hrhs:(((R_bfn s j).map fun p => ((fun x => p.1 (π2 x)),p.2)).map fun p => ((fun x => p.1 (π2_inv x)),p.2))=R_bfn s j:=by
     rw [lMMp]
     have hfg:((fun p:BFn n × Nat => ((fun x => p.1 (π2_inv x)),p.2)) ∘ fun p:BFn n × Nat => ((fun x => p.1 (π2 x)),p.2))=id:=by
       funext ⟨g,tg⟩;simp only [fCD,id];congr 1;funext x;exact congrArg g (hright x)
     rw [hfg,List.map_id]
   rw [hrhs] at hmap_inv
   simpa [lMMp,fCD] using hmap_inv
lemma span_sound (P:Nat->Bool) (len start:Nat) (h:span P len start=true) :
   ∀ i,start<=i->i < start+len->P i=true:=by
 induction len generalizing start with
 | zero => intro i h1 h2;omega
 | succ m ih =>
   simp only [span,bAT] at h;intro i h1 h2
   by_cases heq:i=start
   . subst heq;exact h.1
   . exact ih (start+1) h.2 i (by omega) (by omega)
lemma q179 {n:Nat} {f:BFn n} {rp:Nat} {c:Cfg} (hc:CfgOk n f rp c)
   (cap:Nat) (hcap:cap<=11) (NN:Nat->Nat)
   (R_bfn:Nat->Nat->List (BFn n × Nat)) (R:Nat->Nat->List (Nat × Nat))
   (hR:∀ s j,R s j=eW rp c (R_bfn s j))
   (hTags:∀ s j,AllTagsLe3 (R_bfn s j))
   (findFn:Nat->List (Nat × Nat)->Bool)
   (hFind:w2 f (aR n rp c) NN R_bfn findFn)
   (hBar:∀ s ≤ cap,∀ i < NN s,bar c findFn R s i=true) :
   ∀ s ≤ cap,∀ i < NN s,
     ¬ TR f s (R_bfn s i):=by
 intro s;induction s with
 | zero =>
   intro _ i hi htr;have hb:=hBar 0 (nZL cap) i hi;obtain ⟨tg,heq⟩:=htr.inv_zero
   simp only [bar,hR,heq,encWs,lMC,List.map_nil,hc.goalv_eq,q0] at hb;cases hb
 | succ s ih =>
   intro hs i hi htr
   have hih:=ih (by omega)
   have hb:=hBar (s+1) hs i hi
   simp only [bar,v8] at hb
   have hscan_false:scanAll c s (R (s+1) i)
       (fun zs => !(findFn s zs)&&(Nat.beq s 0||scanInline c (Nat.sub s 1) zs))=false:=by simpa using hb
   have hscan_true:scanAll c s (eW rp c (R_bfn (s+1) i))
       (fun zs => !(findFn s zs)&&(Nat.beq s 0||scanInline c (Nat.sub s 1) zs))=true:=by
     apply q17 hc (by omega:s<=10) (hTags (s+1) i) htr
     intro zs_b hzt htr_z
     have hnf:findFn s (eW rp c zs_b)=false:=by
       cases hf:findFn s (eW rp c zs_b)
       . rfl
       . exfalso;obtain ⟨j,hj,π,hbij,hfix,hperm⟩:=hFind s zs_b hf
         exact hih j hj (TagRun.perm hperm (wp π hbij hfix htr_z))
     simp only [hnf,bNF,bTA]
     cases s with
     | zero => rfl
     | succ s' =>
       simp only [q2 (Nat.succ_ne_zero s'),Bool.false_or]
       exact wj hc (by omega:s'<=10) hzt htr_z
   rw [hR,hscan_true] at hscan_false;cases hscan_false
def checkGenList (n:Nat) (f:BFn n):List (List (Nat × Nat × Nat × Nat))->List (List (Nat × Nat))->Bool
 | [],[] => true
 | sw::sws,ps::pss =>
   kq n ps&&(q163 n ps==sw)&&(ym sw (encTT n f)==encTT n f)&&checkGenList n f sws pss
 | _,_ => false
lemma ye (n:Nat) (f:BFn n) (gsw:List (List (Nat × Nat × Nat × Nat)))
   (gsp:List (List (Nat × Nat))) (h:checkGenList n f gsw gsp=true) :
   ∀ sw ∈ gsw,vh f sw:=by
 induction gsw generalizing gsp with
 | nil => intro _ hm;cases hm
 | cons sw sws ih =>
   cases gsp with
   | nil => simp [checkGenList] at h
   | cons ps pss =>
     simp only [checkGenList,bAT,beq_iff_eq] at h
     obtain ⟨⟨⟨hv,hmk⟩,hfix⟩,hrest⟩:=h
     intro g hg;rcases List.mem_cons.1 hg with rfl | hg2
     . rw [← hmk] at hfix ⊢;exact kw f ps hv hfix
     . exact ih pss hrest g hg2
def checkAutFn (n:Nat) (f:BFn n) (aut:Nat->List (Nat × Nat × Nat × Nat)) (autp:List (List (Nat × Nat))):Bool :=
 (List.range autp.length).all fun i =>
   let ps:=autp.getD i []
   kq n ps&&(q163 n ps==aut i)&&(ym (aut i) (encTT n f)==encTT n f)
lemma q58 (n:Nat) (f:BFn n) (aut:Nat->List (Nat × Nat × Nat × Nat))
   (autp:List (List (Nat × Nat))) (h:checkAutFn n f aut autp=true) (hdef:∀ i ≥ autp.length,aut i=[]) :
   ∀ i,vh f (aut i):=by
 intro i;by_cases hi:i < autp.length
 . have h1:=List.all_eq_true.1 h i (List.mem_range.2 hi)
   simp only [bAT,beq_iff_eq] at h1
   obtain ⟨⟨hv,hmk⟩,hfix⟩:=h1;rw [← hmk] at hfix ⊢;exact kw f (autp.getD i []) hv hfix
 . rw [hdef i (by omega)];exact q138 f
def w8 (n:Nat) (f:BFn n):Bool :=
 let t:=encTT n f;!(Nat.beq t 0)&&!(Nat.beq t (2 ^ (2 ^ n) - 1))
lemma ju (n:Nat) (f:BFn n) (h:w8 n f=true) :
   ∃ y y':Fin n->Bool,f y≠f y':=by
 unfold w8 at h;simp only [bAT,bNT,zh] at h
 obtain ⟨hne0,hne1⟩:=h
 have hex1:∃ r < 2 ^ n,f (q1 n r)=true:=by
   by_contra hall;push Not at hall;apply hne0;apply nEQ;intro r
   rw [vr,nZT];split;exact Bool.eq_false_iff.2 (hall r ‹_›);rfl
 have hex0:∃ r < 2 ^ n,f (q1 n r)=false:=by
   by_contra hall;push Not at hall;apply hne1;apply nEQ;intro r
   rw [vr,nTB];split
   . rename_i hr;have:f (q1 n r)=true:=by cases hf:f (q1 n r);exact absurd hf (hall r hr);rfl
     simp [hr,this]
   . rename_i hr;simp [hr]
 obtain ⟨r1,_,h1⟩:=hex1;obtain ⟨r0,_,h0⟩:=hex0
 exact ⟨q1 n r1,q1 n r0,by rw [h1,h0];decide⟩
def q77 (n:Nat) (f:BFn n):Bool :=
 (List.finRange n).all fun v =>
   (List.range (2 ^ n)).any fun r => let x:=q1 n r;f (Function.update x v (!x v))!=f x
lemma q44 (n:Nat) (f:BFn n) (h:q77 n f=true) :
   ∀ v:Fin n,∃ x:Fin n->Bool,f (Function.update x v (!x v))≠f x:=by
 intro v;have h1:=List.all_eq_true.1 h v (List.mem_finRange v)
 obtain ⟨r,_,hr⟩:=List.any_eq_true.1 h1;exact ⟨q1 n r,bne_iff_ne.1 hr⟩
def q147 (c:Cfg) (findFn:Nat->List (Nat × Nat)->Bool) (xs:List (Nat × Nat)) (s0:Nat):Bool :=
 findFn s0 xs||!(Nat.beq s0 0||scanInline c (Nat.sub s0 1) xs)
def verifyBase (n cap:Nat) (f:BFn n) (rp:Nat) (c:Cfg) (initTags:Fin n->Nat)
   (xs xstt:List (Nat × Nat)) (findFn:Nat->List (Nat × Nat)->Bool):Bool :=
 let rows:=aR n rp c
 let xs_b:=List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)
 Nat.ble cap 11&&w3 n f rp c&&w8 n f&&q77 n f &&
 ((List.finRange n).all fun i => Nat.ble (initTags i) 3) &&
 (xs==encWs rows xs_b)&&(xstt==encTTWs n xs_b) &&
 ((List.range (cap+1)).all fun s0 => Nat.blt (Nat.add s0 1) n||q147 c findFn xs s0)
lemma prove_base {n cap:Nat} (f:BFn n) (rp:Nat) (c:Cfg) (initTags:Fin n->Nat)
   (xs xstt:List (Nat × Nat)) (NN PT:Nat->Nat) (findFn:Nat->List (Nat × Nat)->Bool)
   (hBase:verifyBase n cap f rp c initTags xs xstt findFn=true)
   (hFind:w2 f (aR n rp c) NN
     (RgenB cap (List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)) PT) findFn)
   (hBar:∀ s ≤ cap,∀ i < NN s,bar c findFn (Rgen c.all1v cap xs PT) s i=true)
   (htag:∀ v:Fin n,initTags v=0 \/
     (initTags v=1/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 1<=s') \/
     (initTags v=3/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 2<=s')) :
   ∀ t:Nat,HasCircuitSize n f t->cap+1<=t:=by
 unfold verifyBase at hBase
 simp only [bAT,Nat.ble_eq,beq_iff_eq] at hBase
 rcases hBase with ⟨⟨⟨⟨⟨⟨⟨hcap,hcfg_b⟩,hnc_b⟩,hdep_b⟩,htags_b⟩,hxs⟩,hxstt⟩,hroots⟩
 have hc:=jn n f rp c hcfg_b
 have hnc:=ju n f hnc_b
 have hdep:=q44 n f hdep_b
 set xs_b:List (BFn n × Nat):=List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)
 have hTags_xs:AllTagsLe3 xs_b:=fun p hp => by
   rw [List.mem_ofFn] at hp;obtain ⟨i,rfl⟩:=hp
   exact Eq.mp Nat.ble_eq (List.all_eq_true.1 htags_b i (List.mem_finRange i))
 have hlen_rows:=zl n rp c.shTT
 have hR:∀ s j,Rgen c.all1v cap xs PT s j=eW rp c (RgenB cap xs_b PT s j):=fun s j => by
   rw [hxs,hc.all1v_eq,← hlen_rows,q102]
 have hNoRun:=q179 hc cap hcap NN (RgenB cap xs_b PT) (Rgen c.all1v cap xs PT) hR
   (fun s j => q59 cap hTags_xs PT s j) findFn hFind hBar
 intro t hcirc;by_contra hlt;have hle:t<=cap:=by omega
 obtain ⟨s0,hs0,htr⟩:=q88 f cap initTags hnc hdep htag t hle hcirc
 have hroot:=List.all_eq_true.1 hroots s0 (List.mem_range.2 (by omega))
 simp only [bOT] at hroot
 rcases hroot with hlen_small | hchk
 . have hlt_n:s0+1 < n:=by simpa [Nat.blt_eq,v8] using hlen_small
   have htr_len:n<=s0+1:=by simpa using htr.len_le
   omega
 . unfold q147 at hchk;simp only [bOT] at hchk
   rcases hchk with hfound | hkill
   . rw [hxs] at hfound;obtain ⟨j,hj,π,hbij,hfix,hperm⟩:=hFind s0 xs_b hfound
     exact hNoRun s0 hs0 j hj (TagRun.perm hperm (wp π hbij hfix htr))
   . simp only [bNT,Bool.or_eq_false_iff,zh] at hkill
     obtain ⟨hs0_nz,hinl_f⟩:=hkill
     cases s0 with
     | zero => exact hs0_nz rfl
     | succ s' =>
       rw [hxs] at hinl_f;have hinl_t:=wj hc (by omega:s'<=10) hTags_xs htr
       change scanInline c s' (eW rp c xs_b)=false at hinl_f
       rw [hinl_t] at hinl_f;cases hinl_f
lemma Rgen_encTTWs_eq {n all1tt cap:Nat} (hall:all1tt=2 ^ 2 ^ n - 1)
   (xs_b:List (BFn n × Nat)) (xstt:List (Nat × Nat)) (hxs:xstt=encTTWs n xs_b)
   (PT:Nat->Nat) (s j:Nat) :
   Rgen all1tt cap xstt PT s j=encTTWs n (RgenB cap xs_b PT s j):=by
 rw [hall,hxs];exact q150 cap xs_b PT s j
lemma q196 {c:Cfg} {findFn:Nat->List (Nat × Nat)->Bool} {R:Nat->Nat->List (Nat × Nat)}
   {cap:Nat} {NN:Nat->Nat}
   (h:∀ s ≤ cap,∀ i < NN s,bar c findFn R s i=true) :
   ∀ s ≤ cap,∀ i < NN s,bar c findFn R s i=true:=h
lemma span_all_sound {P:Nat->Nat->Bool} {cap:Nat} {NN:Nat->Nat}
   (h:(List.range (cap+1)).all (fun s => span (P s) (NN s) 0)=true) :
   ∀ s ≤ cap,∀ i < NN s,P s i=true:=fun s hs i hi =>
 span_sound (P s) (NN s) 0 (List.all_eq_true.1 h s (List.mem_range.2 (by omega))) i (nZL _) (by omega)
lemma span_chunk_join {P:Nat->Bool} {a b:Nat}
   (h1:span P a 0=true) (h2:span P (b - a) a=true) :
   ∀ i < b,P i=true:=fun i hi => by
 by_cases h:i < a
 . exact span_sound P a 0 h1 i (nZL _) (by omega)
 . exact span_sound P (b - a) a h2 i (by omega) (by omega)
lemma span_chunk3 {P:Nat->Bool} {a b d:Nat}
   (h1:span P a 0=true) (h2:span P b a=true) (h3:span P (d - (a+b)) (a+b)=true) :
   ∀ i < d,P i=true:=fun i hi => by
 by_cases h1i:i < a
 . exact span_sound P a 0 h1 i (nZL _) (by omega)
 . by_cases h2i:i < a+b
   . exact span_sound P b a h2 i (by omega) (by omega)
   . exact span_sound P (d - (a+b)) (a+b) h3 i (by omega) (by omega)
lemma span_chunk4 {P:Nat->Bool} {a b d e:Nat}
   (h1:span P a 0=true) (h2:span P b a=true) (h3:span P d (a+b)=true)
   (h4:span P (e - (a+b+d)) (a+b+d)=true) :
   ∀ i < e,P i=true:=fun i hi => by
 by_cases h1i:i < a
 . exact span_sound P a 0 h1 i (nZL _) (by omega)
 . by_cases h2i:i < a+b
   . exact span_sound P b a h2 i (by omega) (by omega)
   . by_cases h3i:i < a+b+d
     . exact span_sound P d (a+b) h3 i (by omega) (by omega)
     . exact span_sound P (e - (a+b+d)) (a+b+d) h4 i (by omega) (by omega)
lemma fun_eq_of_encTT {n:Nat} (f g:BFn n) (h:Nat.beq (encTT n f) (encTT n g)=true):f=g :=
 yc (Eq.mp Nat.beq_eq h)
lemma prove_base1 {n cap all1tt:Nat} (f:BFn n) (rp salt:Nat) (c:Cfg) (initTags:Fin n->Nat)
   (xs xstt:List (Nat × Nat)) (NN FL HT PT:Nat->Nat)
   (hall:all1tt=2 ^ 2 ^ n - 1)
   (hxstt:xstt=encTTWs n (List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)))
   (hBase:verifyBase n cap f rp c initTags xs xstt
     (findAut1 c.shTT salt (Rgen all1tt cap xstt PT) NN FL HT)=true)
   (hBar:∀ s ≤ cap,∀ i < NN s,bar c (findAut1 c.shTT salt (Rgen all1tt cap xstt PT) NN FL HT) (Rgen c.all1v cap xs PT) s i=true)
   (htag:∀ v:Fin n,initTags v=0 \/
     (initTags v=1/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 1<=s') \/
     (initTags v=3/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 2<=s')) :
   ∀ t:Nat,HasCircuitSize n f t->cap+1<=t :=
 prove_base f rp c initTags xs xstt NN PT _ hBase
   (q87 f rp c.shTT salt NN FL HT _ _ (Rgen_encTTWs_eq hall _ xstt hxstt PT)) hBar htag
lemma prove_base2 {n cap all1tt:Nat} (f:BFn n) (rp salt:Nat) (c:Cfg) (initTags:Fin n->Nat)
   (xs xstt:List (Nat × Nat)) (g0:List (Nat × Nat × Nat × Nat)) (g0p:List (Nat × Nat))
   (NN FL HT PT:Nat->Nat)
   (hall:all1tt=2 ^ 2 ^ n - 1)
   (hxstt:xstt=encTTWs n (List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)))
   (hg0:checkGenList n f [g0] [g0p]=true)
   (hBase:verifyBase n cap f rp c initTags xs xstt
     (findAut2 c.shTT salt g0 (Rgen all1tt cap xstt PT) NN FL HT)=true)
   (hBar:∀ s ≤ cap,∀ i < NN s,bar c (findAut2 c.shTT salt g0 (Rgen all1tt cap xstt PT) NN FL HT) (Rgen c.all1v cap xs PT) s i=true)
   (htag:∀ v:Fin n,initTags v=0 \/
     (initTags v=1/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 1<=s') \/
     (initTags v=3/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 2<=s')) :
   ∀ t:Nat,HasCircuitSize n f t->cap+1<=t :=
 prove_base f rp c initTags xs xstt NN PT _ hBase
   (q86 f rp c.shTT salt g0 (ye n f [g0] [g0p] hg0 g0 (by simp))
     NN FL HT _ _ (Rgen_encTTWs_eq hall _ xstt hxstt PT)) hBar htag
lemma prove_basePath {n cap all1tt:Nat} (f:BFn n) (rp salt:Nat) (c:Cfg) (initTags:Fin n->Nat)
   (xs xstt:List (Nat × Nat)) (gsw path:List (List (Nat × Nat × Nat × Nat))) (gsp:List (List (Nat × Nat)))
   (NN FL HT PT:Nat->Nat)
   (hall:all1tt=2 ^ 2 ^ n - 1)
   (hxstt:xstt=encTTWs n (List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)))
   (hgen:checkGenList n f gsw gsp=true)
   (hsub:path.all (fun g => gsw.contains g)=true)
   (hBase:verifyBase n cap f rp c initTags xs xstt
     (findAutPath c.shTT salt path (Rgen all1tt cap xstt PT) NN FL HT)=true)
   (hBar:∀ s ≤ cap,∀ i < NN s,bar c (findAutPath c.shTT salt path (Rgen all1tt cap xstt PT) NN FL HT) (Rgen c.all1v cap xs PT) s i=true)
   (htag:∀ v:Fin n,initTags v=0 \/
     (initTags v=1/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 1<=s') \/
     (initTags v=3/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 2<=s')) :
   ∀ t:Nat,HasCircuitSize n f t->cap+1<=t:=by
 have hg:=ye n f gsw gsp hgen
 have hp:∀ g ∈ path,vh f g:=fun g hgp =>
   hg g (List.contains_iff_mem.1 (List.all_eq_true.1 hsub g hgp))
 exact prove_base f rp c initTags xs xstt NN PT _ hBase
   (q37 f rp c.shTT salt path hp NN FL HT _ _ (Rgen_encTTWs_eq hall _ xstt hxstt PT)) hBar htag
lemma prove_baseGen {n cap all1tt:Nat} (f:BFn n) (rp salt:Nat) (c:Cfg) (initTags:Fin n->Nat)
   (xs xstt:List (Nat × Nat)) (gsw:List (List (Nat × Nat × Nat × Nat))) (gsp:List (List (Nat × Nat)))
   (aut:Nat->List (Nat × Nat × Nat × Nat)) (autp:List (List (Nat × Nat)))
   (NN FL HT PT:Nat->Nat)
   (hall:all1tt=2 ^ 2 ^ n - 1)
   (hxstt:xstt=encTTWs n (List.ofFn fun i:Fin n => ((fun x:Fin n->Bool => x i),initTags i)))
   (hgen:checkGenList n f gsw gsp=true)
   (haut:checkAutFn n f aut autp=true)
   (hdef:∀ i ≥ autp.length,aut i=[])
   (hBase:verifyBase n cap f rp c initTags xs xstt
     (findAutGen c.shTT salt gsw aut (Rgen all1tt cap xstt PT) NN FL HT PT)=true)
   (hBar:∀ s ≤ cap,∀ i < NN s,bar c (findAutGen c.shTT salt gsw aut (Rgen all1tt cap xstt PT) NN FL HT PT) (Rgen c.all1v cap xs PT) s i=true)
   (htag:∀ v:Fin n,initTags v=0 \/
     (initTags v=1/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 1<=s') \/
     (initTags v=3/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize n (fun x => f (Function.update x v false)) s'->cap - 2<=s')) :
   ∀ t:Nat,HasCircuitSize n f t->cap+1<=t :=
 prove_base f rp c initTags xs xstt NN PT _ hBase
   (q55 f rp c.shTT salt gsw (ye n f gsw gsp hgen)
     aut (q58 n f aut autp haut hdef) NN FL HT PT _ _ (Rgen_encTTWs_eq hall _ xstt hxstt PT)) hBar htag
structure BaseEntry where
 k:Nat
 E:List (Fin k × Fin k)
 lb:Nat
def BaseTableOk (bs:List BaseEntry):Prop :=
 ∀ b ∈ bs,∀ s:Nat,HasCircuitSize b.k (gfn [] b.E) s->b.lb<=s
def q61 {n:Nat}:List (Fin n)->Bool
 | [] => true
 | a::t => !t.contains a&&q61 t
lemma q83 {n:Nat} (l:List (Fin n)) (h:q61 l=true):l.Nodup:=by
 induction l with
 | nil => exact List.nodup_nil
 | cons a t ih =>
   simp only [q61,bAT,bNT] at h
   exact List.nodup_cons.2 ⟨by simpa [List.contains_eq_mem] using h.1,ih h.2⟩
inductive GTree (n:Nat) where
 | emp
 | base (idx:Nat) (π:List Nat)
 | f0 (p:Fin n) (t:GTree n)
 | f1 (p:Fin n) (t:GTree n)
 | b2 (p:Fin n) (t0 t1:GTree n)
def checkGTree (bs:List BaseEntry) (n:Nat)
   (A:List (Fin (n+1))) (E:List (Fin (n+1) × Fin (n+1))) (req:Nat):GTree (n+1)->Bool
 | GTree.emp => E.isEmpty&&q61 A&&Nat.ble req (A.length - 1)
 | GTree.base idx π =>
   match bs[idx]? with
   | none => false
   | some b =>
     if h : 0 < b.k then
       A.isEmpty&&Nat.ble req b.lb &&
       isoCheck E b.E (fun i => ⟨π.getD i.1 0 % b.k,Nat.mod_lt _ h⟩)
     else false
 | GTree.f0 p t =>
   let A':=fix0A A p;let E':=fix0E E p
   depCheck A E p&&(!A'.isEmpty||!E'.isEmpty)&&checkGTree bs n A' E' (req - 1) t
 | GTree.f1 p t =>
   let A':=fix1A A E p;let E':=fix1E A E p
   depCheck A E p&&!A.contains p&&E.all (fun e => e.1!=e.2) &&
     (!A'.isEmpty||!E'.isEmpty)&&checkGTree bs n A' E' (req - 1) t
 | GTree.b2 p t0 t1 =>
   let A0:=fix0A A p;let E0:=fix0E E p
   let A1:=fix1A A E p;let E1:=fix1E A E p
   depCheck A E p&&!A.contains p&&E.all (fun e => e.1!=e.2) &&
     (!A0.isEmpty||!E0.isEmpty)&&(!A1.isEmpty||!E1.isEmpty) &&
     checkGTree bs n A0 E0 (req - 2) t0&&checkGTree bs n A1 E1 (req - 2) t1
lemma checkGTree_sound (bs:List BaseEntry) (hbs:BaseTableOk bs) {n:Nat}
   (t:GTree (n+1)) (A:List (Fin (n+1))) (E:List (Fin (n+1) × Fin (n+1))) (req:Nat)
   (h:checkGTree bs n A E req t=true) :
   ∀ s:Nat,HasCircuitSize (n+1) (gfn A E) s->req<=s:=by
 induction t generalizing A E req with
 | emp =>
   simp only [checkGTree,bAT,List.isEmpty_iff] at h
   rcases h with ⟨⟨rfl,hnd⟩,hle⟩
   intro s hs;have h1:=q176 A (q83 A hnd) s hs
   have h2:req<=A.length - 1:=Eq.mp Nat.ble_eq hle;omega
 | base idx π =>
   unfold checkGTree at h
   cases hb:bs[idx]? with
   | none => rw [hb] at h;cases h
   | some b =>
     rw [hb] at h;dsimp only at h
     split at h
     . rename_i hk
       simp only [bAT,List.isEmpty_iff] at h
       rcases h with ⟨⟨rfl,hle⟩,hiso⟩
       have hbmem:b ∈ bs:=List.mem_of_getElem? hb
       intro s hs
       have h1:=q191 E b.E (fun i => ⟨π.getD i.1 0 % b.k,Nat.mod_lt _ hk⟩) hiso (hbs b hbmem) s hs
       have h2:req<=b.lb:=Eq.mp Nat.ble_eq hle;omega
     . cases h
 | f0 p t ih =>
   simp only [checkGTree,bAT] at h
   rcases h with ⟨⟨hdep,hnc⟩,hsub⟩
   intro s hs;have h1:=q190 A E p (fix0A A p) (fix0E E p) (req - 1) hdep rfl rfl hnc (ih _ _ _ hsub) s hs;omega
 | f1 p t ih =>
   simp only [checkGTree,bAT] at h
   rcases h with ⟨⟨⟨⟨hdep,hpA⟩,hloop⟩,hnc⟩,hsub⟩
   intro s hs;have h1:=q189 A E p (fix1A A E p) (fix1E A E p) (req - 1) hdep hpA hloop rfl rfl hnc (ih _ _ _ hsub) s hs;omega
 | b2 p t0 t1 ih0 ih1 =>
   simp only [checkGTree,bAT] at h
   rcases h with ⟨⟨⟨⟨⟨⟨hdep,hpA⟩,hloop⟩,hnc0⟩,hnc1⟩,hsub0⟩,hsub1⟩
   intro s hs
   have h1:=q155 A E p (fix0A A p) (fix0E E p) (fix1A A E p) (fix1E A E p) (req - 2)
     hdep hpA hloop rfl rfl rfl rfl hnc0 hnc1 (ih0 _ _ _ hsub0) (ih1 _ _ _ hsub1) s hs;omega
def checkTags (bs:List BaseEntry) (n cap:Nat) (E:List (Fin (n+1) × Fin (n+1)))
   (initTags:Fin (n+1)->Nat) (trees:List (GTree (n+1))):Bool :=
 (List.finRange (n+1)).all fun v =>
   let tg:=initTags v
   let E0:=fix0E E v
   let tr:=trees.getD v.1 GTree.emp
   Nat.beq tg 0 ||
   (Nat.beq tg 1&&!E0.isEmpty&&checkGTree bs n [] E0 (cap - 1) tr) ||
   (Nat.beq tg 3&&!E0.isEmpty&&checkGTree bs n [] E0 (cap - 2) tr)
lemma checkTags_sound (bs:List BaseEntry) (hbs:BaseTableOk bs) {n cap:Nat}
   (f:BFn (n+1)) (E:List (Fin (n+1) × Fin (n+1))) (initTags:Fin (n+1)->Nat)
   (trees:List (GTree (n+1)))
   (hf:Nat.beq (encTT (n+1) f) (encTT (n+1) (gfn [] E))=true)
   (h:checkTags bs n cap E initTags trees=true) :
   ∀ v:Fin (n+1),initTags v=0 \/
     (initTags v=1/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize (n+1) (fun x => f (Function.update x v false)) s'->cap - 1<=s') \/
     (initTags v=3/\(∃ x y,f (Function.update x v false)≠f (Function.update y v false)) /\
       ∀ s',HasCircuitSize (n+1) (fun x => f (Function.update x v false)) s'->cap - 2<=s'):=by
 have hfeq:f=gfn [] E:=fun_eq_of_encTT _ _ hf
 intro v
 have hv:=List.all_eq_true.1 h v (List.mem_finRange v)
 simp only [bOT,bAT] at hv
 rcases hv with (h0 | ⟨⟨h1,hnc⟩,htr⟩) | ⟨⟨h3,hnc⟩,htr⟩
 . exact Or.inl (Eq.mp Nat.beq_eq h0)
 . refine Or.inr (Or.inl ⟨Eq.mp Nat.beq_eq h1,?_,?_⟩)
   . have hres:(fun x => f (Function.update x v false))=gfn [] (fix0E E v):=by
       rw [hfeq];exact zo [] E v
     obtain ⟨x,y,hxy⟩:=q99 [] (fix0E E v) (by simp [hnc])
     exact ⟨x,y,by simpa [congrFun hres] using hxy⟩
   . intro s' hs'
     have hres:(fun x => f (Function.update x v false))=gfn [] (fix0E E v):=by
       rw [hfeq];exact zo [] E v
     rw [hres] at hs';exact checkGTree_sound bs hbs _ [] (fix0E E v) (cap - 1) htr s' hs'
 . refine Or.inr (Or.inr ⟨Eq.mp Nat.beq_eq h3,?_,?_⟩)
   . have hres:(fun x => f (Function.update x v false))=gfn [] (fix0E E v):=by
       rw [hfeq];exact zo [] E v
     obtain ⟨x,y,hxy⟩:=q99 [] (fix0E E v) (by simp [hnc])
     exact ⟨x,y,by simpa [congrFun hres] using hxy⟩
   . intro s' hs'
     have hres:(fun x => f (Function.update x v false))=gfn [] (fix0E E v):=by
       rw [hfeq];exact zo [] E v
     rw [hres] at hs';exact checkGTree_sound bs hbs _ [] (fix0E E v) (cap - 2) htr s' hs'
lemma conj_of_gtree (bs:List BaseEntry) (hbs:BaseTableOk bs) {n req:Nat}
   (f:BFn (n+1)) (E:List (Fin (n+1) × Fin (n+1))) (t:GTree (n+1))
   (hf:Nat.beq (encTT (n+1) f) (encTT (n+1) (gfn [] E))=true)
   (h:checkGTree bs n [] E req t=true) :
   ∀ s:Nat,HasCircuitSize (n+1) f s->req<=s:=by
 rw [fun_eq_of_encTT _ _ hf]
 exact checkGTree_sound bs hbs t [] E req h
lemma baseTable_cons (b:BaseEntry) (bs:List BaseEntry)
   (hb:∀ s:Nat,HasCircuitSize b.k (gfn [] b.E) s->b.lb<=s)
   (hbs:BaseTableOk bs):BaseTableOk (b::bs):=fun x hx => by
 rcases List.mem_cons.1 hx with rfl | hx2;exact hb;exact hbs x hx2
lemma baseEntry_of_f {k lb:Nat} (f:BFn k) (E:List (Fin k × Fin k))
   (hf:Nat.beq (encTT k f) (encTT k (gfn [] E))=true)
   (h:∀ s:Nat,HasCircuitSize k f s->lb<=s) :
   ∀ s:Nat,HasCircuitSize k (gfn [] E) s->lb<=s:=by
 rw [← fun_eq_of_encTT _ _ hf];exact h
def a1t3:=0xff
def a1t5:=0xffffffff
def a1t6:=0xffffffffffffffff
def a1t7:=0xffffffffffffffffffffffffffffffff
def tv0:=0xaaaaaaaaaaaaaaaa
def tv1:=0xcccccccccccccccc
def tv2:=0xf0f0f0f0f0f0f0f0
def tv3:=0xff00ff00ff00ff00
def tv4:=0xffff0000ffff0000
def tv5:=0xffffffff00000000
def tv6:=0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def tv7:=0xcccccccccccccccccccccccccccccccc
def tv8:=0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def tv9:=0xff00ff00ff00ff00ff00ff00ff00ff00
def tv10:=0xffff0000ffff0000ffff0000ffff0000
def tv11:=0xffffffff00000000ffffffff00000000
def tv12:=0xffffffffffffffff0000000000000000
def sw0:Nat×Nat×Nat×Nat:=(2,0x30,0xc,0xc3)
def sw1:Nat×Nat×Nat×Nat:=(1,0x44,0x22,0x99)
def sw2:Nat×Nat×Nat×Nat:=(4,0xf000f00,0xf000f0,0xf00ff00f)
def sw3:Nat×Nat×Nat×Nat:=(14,0x33330000,0xcccc,0xcccc3333)
def sw4:Nat×Nat×Nat×Nat:=(12,0xf0f0000,0xf0f0,0xf0f00f0f)
def sw5:Nat×Nat×Nat×Nat:=(1,0x44444444,0x22222222,0x99999999)
def sw6:Nat×Nat×Nat×Nat:=(8,0xff0000,0xff00,0xff0000ff)
def sw7:Nat×Nat×Nat×Nat:=(2,0x30303030,0xc0c0c0c,0xc3c3c3c3)
def sw8:Nat×Nat×Nat×Nat:=(6,0x33003300,0xcc00cc,0xcc33cc33)
def sw9:Nat×Nat×Nat×Nat:=(16,0xffff00000000,0xffff0000,0xffff00000000ffff)
def sw10:Nat×Nat×Nat×Nat:=(2,0x3030303030303030,0xc0c0c0c0c0c0c0c,0xc3c3c3c3c3c3c3c3)
def sw11:Nat×Nat×Nat×Nat:=(8,0xff000000ff0000,0xff000000ff00,0xff0000ffff0000ff)
def sw12:Nat×Nat×Nat×Nat:=(1,0x4444444444444444,0x2222222222222222,0x9999999999999999)
def sw13:Nat×Nat×Nat×Nat:=(28,0xf0f0f0f00000000,0xf0f0f0f0,0xf0f0f0f00f0f0f0f)
def sw14:Nat×Nat×Nat×Nat:=(7,0x5500550055005500,0xaa00aa00aa00aa,0xaa55aa55aa55aa55)
def sw15:Nat×Nat×Nat×Nat:=(4,0xf000f000f000f00,0xf000f000f000f0,0xf00ff00ff00ff00f)
def sw16:Nat×Nat×Nat×Nat:=(14,0x3333000033330000,0xcccc0000cccc,0xcccc3333cccc3333)
def sw17:Nat×Nat×Nat×Nat:=(12,0xf0f00000f0f0000,0xf0f00000f0f0,0xf0f00f0ff0f00f0f)
def sw18:Nat×Nat×Nat×Nat:=(6,0x3300330033003300,0xcc00cc00cc00cc,0xcc33cc33cc33cc33)
def sw19:Nat×Nat×Nat×Nat:=(31,0x5555555500000000,0xaaaaaaaa,0xaaaaaaaa55555555)
def sw20:Nat×Nat×Nat×Nat:=(3,0x5050505050505050,0xa0a0a0a0a0a0a0a,0xa5a5a5a5a5a5a5a5)
def sw21:Nat×Nat×Nat×Nat:=(30,0x3333333300000000,0xcccccccc,0xcccccccc33333333)
def sw22:Nat×Nat×Nat×Nat:=(15,0x5555000055550000,0xaaaa0000aaaa,0xaaaa5555aaaa5555)
def sw23:Nat×Nat×Nat×Nat:=(32,0xffffffff0000000000000000,0xffffffff00000000,0xffffffff0000000000000000ffffffff)
def sw24:Nat×Nat×Nat×Nat:=(8,0xff000000ff000000ff000000ff0000,0xff000000ff000000ff000000ff00,0xff0000ffff0000ffff0000ffff0000ff)
def sw25:Nat×Nat×Nat×Nat:=(2,0x30303030303030303030303030303030,0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c,0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3)
def sw26:Nat×Nat×Nat×Nat:=(16,0xffff000000000000ffff00000000,0xffff000000000000ffff0000,0xffff00000000ffffffff00000000ffff)
def sw27:Nat×Nat×Nat×Nat:=(4,0xf000f000f000f000f000f000f000f00,0xf000f000f000f000f000f000f000f0,0xf00ff00ff00ff00ff00ff00ff00ff00f)
def sw28:Nat×Nat×Nat×Nat:=(1,0x44444444444444444444444444444444,0x22222222222222222222222222222222,0x99999999999999999999999999999999)
def sw29:Nat×Nat×Nat×Nat:=(56,0xff00ff00ff00ff0000000000000000,0xff00ff00ff00ff00,0xff00ff00ff00ff0000ff00ff00ff00ff)
def sw30:Nat×Nat×Nat×Nat:=(14,0x33330000333300003333000033330000,0xcccc0000cccc0000cccc0000cccc,0xcccc3333cccc3333cccc3333cccc3333)
def sw31:Nat×Nat×Nat×Nat:=(3,0x50505050505050505050505050505050,0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a,0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5)
def sw32:Nat×Nat×Nat×Nat:=(48,0xffff0000ffff0000000000000000,0xffff0000ffff0000,0xffff0000ffff00000000ffff0000ffff)
def sw33:Nat×Nat×Nat×Nat:=(28,0xf0f0f0f000000000f0f0f0f00000000,0xf0f0f0f000000000f0f0f0f0,0xf0f0f0f00f0f0f0ff0f0f0f00f0f0f0f)
def sw34:Nat×Nat×Nat×Nat:=(7,0x55005500550055005500550055005500,0xaa00aa00aa00aa00aa00aa00aa00aa,0xaa55aa55aa55aa55aa55aa55aa55aa55)
def sw35:Nat×Nat×Nat×Nat:=(60,0xf0f0f0f0f0f0f0f0000000000000000,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f)
def sw36:Nat×Nat×Nat×Nat:=(30,0x33333333000000003333333300000000,0xcccccccc00000000cccccccc,0xcccccccc33333333cccccccc33333333)
def sw37:Nat×Nat×Nat×Nat:=(15,0x55550000555500005555000055550000,0xaaaa0000aaaa0000aaaa0000aaaa,0xaaaa5555aaaa5555aaaa5555aaaa5555)
def sw38:Nat×Nat×Nat×Nat:=(62,0x33333333333333330000000000000000,0xcccccccccccccccc,0xcccccccccccccccc3333333333333333)
def sw39:Nat×Nat×Nat×Nat:=(24,0xff00ff0000000000ff00ff00000000,0xff00ff0000000000ff00ff00,0xff00ff0000ff00ffff00ff0000ff00ff)
def sw40:Nat×Nat×Nat×Nat:=(12,0xf0f00000f0f00000f0f00000f0f0000,0xf0f00000f0f00000f0f00000f0f0,0xf0f00f0ff0f00f0ff0f00f0ff0f00f0f)
def sw41:Nat×Nat×Nat×Nat:=(6,0x33003300330033003300330033003300,0xcc00cc00cc00cc00cc00cc00cc00cc,0xcc33cc33cc33cc33cc33cc33cc33cc33)
def mk0:=0x9e3779b97f4a7c15f39cc0605cedc835
def mk1:=0x3fffffffff
def mk2:=0x1ff
def mk3:=0x3f
def mk4:=0x1
def mk5:=0x1d
def mk6:=0x20
def mk7:=0x2
def mk8:=0xffffffffffffffffffffffffffffffffffffffffff
def mk9:=0x3ffffffffffff
def mk10:=0x3fffffff
def mk11:=0x1041041
def mk12:=0x1d75d75d
def mk13:=0x20820820
def mk14:=0x1715609f7c746c6dc20fc1e1d0a4e909
def mk15:=0xfffffffffffffffffffffffffffffffffffffffffffff
def mk16:=0xfffffffff
def mk17:=0x41041041
def mk18:=0x75d75d75d
def mk19:=0x820820820
def mk20:=0x41
def mk21:=0x82
def mk22:=0x75d
def mk23:=0x820
def mk24:=0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def mk25:=0xffffffffffffffffff
def mk26:=0x3fffffffffffff
def mk27:=0x1041041041041
def mk28:=0x1d75d75d75d75d
def mk29:=0x20820820820820
def mk30:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def mk31:=0x3fffffffffffffffffff
def mk32:=0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def mk33:=0x3fffffffffffffffffffffffff
def mk34:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def mk35:=0xffffffffffffffffffffff
def mk36:=0x1041
def mk37:=0x2082
def mk38:=0x1d75d
def mk39:=0x20820
def mk40:=0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def mk41:=0x41041041041041041
def mk42:=0x75d75d75d75d75d75d
def mk43:=0x820820820820820820
def mk44:=0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def mk45:=0xfffffffffffffffffffffffffffffffffff
def mk46:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def mk47:=0xffffffffffffffffffffffffffffffffffff
def mk48:=0x1041041041041041041041041
def mk49:=0x1d75d75d75d75d75d75d75d75d
def mk50:=0x20820820820820820820820820
def mk51:=0x1041041041
def mk52:=0x2082082082
def mk53:=0x1d75d75d75d
def mk54:=0x20820820820
def mk55:=0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def mk56:=0x7fffffffffffffffffffffffffffffffffffff
def mk57:=0x2082082
def mk58:=0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def mk59:=0x7fffffffffffffffffffffffffffffffffff
def mk60:=0xfffffffffffffffffffffffffff
def mk61:=0x41041041041041041041041041
def mk62:=0x75d75d75d75d75d75d75d75d75d
def mk63:=0x820820820820820820820820820
def mk64:=0x41041041041
def mk65:=0x82082082082
def mk66:=0x75d75d75d75d
def mk67:=0x820820820820
def mk68:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def mk69:=0x41041041041041
def mk70:=0x82082082082082
def mk71:=0x75d75d75d75d75d
def mk72:=0x820820820820820
def mk73:=0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def mk74:=0x3fffffffffffffffffffffffffffffffffff
def mk75:=0x3ffffffffffffffffffffff
def mk76:=0x1041041041041041041041
def mk77:=0x1d75d75d75d75d75d75d75d
def mk78:=0x20820820820820820820820
def mk79:=0x82082082
def mk80:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def mk81:=0x1fffffffffffffffffffffffffffffffffffffff
def mk82:=0x41041
def mk83:=0x82082
def mk84:=0x75d75d
def mk85:=0x820820
def mk86:=0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def mk87:=0x1041041041041041041
def mk88:=0x1d75d75d75d75d75d75d
def mk89:=0x20820820820820820820
def mk90:=0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def mk91:=0x1ffffffffffffffffffffffffffffffffffffffff
def mk92:=0x82082082082082082
def mk93:=0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def mk94:=0x3ffffffffffffffffffffffffffffffffffffff
def mk95:=0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def mk96:=0x1ffffffffffffffffffffffffffffffffffff
def mk97:=0x3fffffffffffffffffffffffffffffffffffff
def mk98:=0x1041041041041041041041041041041041041
def mk99:=0x1d75d75d75d75d75d75d75d75d75d75d75d75d
def mk100:=0x20820820820820820820820820820820820820
def mk101:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def mk102:=0x3ffffffffffffffffffffffffffffffffff
def mk103:=0x1041041041041041041041041041041041
def mk104:=0x1d75d75d75d75d75d75d75d75d75d75d75d
def mk105:=0x20820820820820820820820820820820820
def mk106:=0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def mk107:=0x1ffffffffffffffffffffffffffffffffffffff
def mk108:=0x2082082082082
def E0:List (Fin 3×Fin 3):=[(0,1),(0,2),(1,2)]
abbrev f0:=gfn [] E0
def r0:=0x101081828304042060a0c1850c18286061418404041010804202
def x0:=[(0x2a934f2e54,0),(0x332596daa1,0),(0x3c0e39f50a,0)]
def xt0:=[(0xaa,0),(0xcc,0),(0xf0,0)]
def c0:Cfg:=⟨9,18,24,30,mk1,0x3a071ffe00,mk2,mk3,mk4,mk5,mk6,mk4,mk7,mk5,mk6⟩
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
def g0_0:=[sw0]
def g0_1:=[sw1]
def gs0:=[g0_0,g0_1]
def pa0:=[g0_0,g0_1,g0_0,g0_1,g0_0]
lemma b0_ok:(List.range 4).all (fun s=>span ((bar c0 (findAutPath c0.shTT mk0 pa0 (Rgen a1t3 3 xt0 P0) N0 L0 H0) (Rgen c0.all1v 3 x0 P0)) s) (N0 s) 0)=true:=by decide +kernel
lemma lb0:∀ t,HasCircuitSize 3 f0 t->4<=t:=prove_basePath f0 r0 mk0 c0 (fun _=>0) x0 xt0 gs0 pa0 [[(1,2)],[(0,1)]] N0 L0 H0 P0 rfl (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (span_all_sound b0_ok) (fun _=>Or.inl rfl)
def E1:List (Fin 5×Fin 5):=[(0,1),(0,4),(1,2),(2,3),(3,4)]
abbrev f1:=gfn [] E1
def r1:=0x404a162a0c8080a446180404a110c0c404246030c20045180644282123018622606060644c0c0c0c8981818191303030322606060668c982a44e1a30346161c346062c2c3860654991160ca142850a122448912142850a142448912242850a1428a1220281284880508485091008a090a100942440502
def x1:=[(0xaaaaaaaa4cc5404ea8c6318ac446fc0007feb111a0,0),(0xcccccccc9408ca29318c631c119fac1ff80104640b,0),(0xf0f0f0f038a293025318c630a7fb43e0003e2982d0,0),(0xff00ff0001302530c6318c673ee40800ffc1c03902,0),(0xffff00003a530c940c6318c7f90873ff00000e421c,0)]
def xt1:=[(0xaaaaaaaa,0),(0xcccccccc,0),(0xf0f0f0f0,0),(0xff00ff00,0),(0xffff0000,0)]
def c1:Cfg:=⟨50,100,130,136,mk8,0xffeaf8c81c71c71c7ffffffffffffc000000000000,mk9,mk10,mk11,mk12,mk13,mk4,mk7,mk5,mk6⟩
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
def au1:Nat->List (Nat×Nat×Nat×Nat)
 | 0=>[]
 | _=>[]
def ap1:List (List (Nat×Nat)):=[[]]
lemma b1_ok:(List.range 7).all (fun s=>span ((bar c1 (findAutGen c1.shTT mk0 gs1 au1 (Rgen a1t5 6 xt1 P1) N1 L1 H1 P1) (Rgen c1.all1v 6 x1 P1)) s) (N1 s) 0)=true:=by decide +kernel
lemma lb1:∀ t,HasCircuitSize 5 f1 t->7<=t:=prove_baseGen f1 r1 mk0 c1 (fun _=>0) x1 xt1 gs1 [[(2,3),(1,4)],[(2,4),(0,1)]] au1 ap1 N1 L1 H1 P1 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 1<=i from hi) with ⟨k,rfl⟩;rw [nAC];rfl) (by decide +kernel) (span_all_sound b1_ok) (fun _=>Or.inl rfl)
def E2:List (Fin 5×Fin 5):=[(0,1),(0,2),(0,3),(0,4),(1,2),(3,4)]
abbrev f2:=gfn [] E2
def r2:=0x8041060614808024449818045060614201244430520200911260202021418624045180644501246088930188890a0cc06222428330188890a0cc0622242833018e1a3044e1a3024b0e0c14b0e0c0ca9322345890a0ca142850a142448912244860c183060c142850a14280811828401284880124281012830201284880c1420202
def x2:=[(0xaaaaaaaa4ce4d538e4d33cf3cf04447fc000003111100,0),(0xcccccccc38038a013aa8451451513bd240fc0fc44e049,0),(0xf0f0f0f0940963025000492492623fa4bf03f00880e92,0),(0xff00ff00013a004c0325924924bbd1070003ffce0441c,0),(0xffff000002500c94094ea28a28bfa2383ffc0000e88e0,0)]
def xt2:=[(0xaaaaaaaa,0),(0xcccccccc,0),(0xf0f0f0f0,0),(0xff00ff00,0),(0xffff0000,0)]
def c2:Cfg:=⟨50,100,136,148,mk15,0xffeaeae81c71c71c71c7ffffffffffffc000000000000,mk9,mk16,mk17,mk18,mk19,mk20,mk21,mk22,mk23⟩
def N2:Nat->Nat
 | 5=>3
 | 6=>10
 | 7=>1
 | _=>0
def L2:Nat->Nat
 | 5=>2
 | 6=>4
 | 7=>0
 | _=>0
def H2:Nat->Nat
 | 5=>0xbb49cd5b9db55b9db4
 | 6=>0xfb774bef6629cd7f96cb72d6ad30b16e3b0069d9355b9db43cfc9803e857
 | 7=>0x5b9db4
 | _=>0
def P2:Nat->Nat
 | 5=>0x43900000c3500000000
 | 6=>0x48008000040000000100000024008000030000002800000034000000000000003800000044
 | 7=>0x0
 | _=>0
def gs2:=[[sw6],[sw7],[sw4,sw8]]
def au2:Nat->List (Nat×Nat×Nat×Nat)
 | 0=>[]
 | 1=>[sw2,sw3]
 | _=>[]
def ap2:List (List (Nat×Nat)):=[[],[(2,3),(1,4)]]
lemma b2_ok:(List.range 8).all (fun s=>span ((bar c2 (findAutGen c2.shTT mk14 gs2 au2 (Rgen a1t5 7 xt2 P2) N2 L2 H2 P2) (Rgen c2.all1v 7 x2 P2)) s) (N2 s) 0)=true:=by decide +kernel
lemma lb2:∀ t,HasCircuitSize 5 f2 t->8<=t:=prove_baseGen f2 r2 mk14 c2 (fun _=>0) x2 xt2 gs2 [[(3,4)],[(1,2)],[(2,4),(1,3)]] au2 ap2 N2 L2 H2 P2 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 2<=i from hi) with ⟨k,rfl⟩;rw [nAC];rfl) (by decide +kernel) (span_all_sound b2_ok) (fun _=>Or.inl rfl)
def E3:List (Fin 6×Fin 6):=[(0,1),(0,2),(0,3),(1,2),(1,4),(2,5)]
abbrev f3:=gfn [] E3
def r3:=0xa0170f148504042060a0c88470904854209c12120c60270909064405c12120c50470909060804106061410108182832805c241214202021418648483090a0d2120c2428348483090a0d2120c2428378d162474c8d1272a4c8978d5a2e58992a42a3830574cd9233c68b13243830372ad4a33a64a8d162428370e1c3870e18b162c58b154a952a54a8e1c3870e1c38506045488502628488170c582a50890a0222810170c58213860a11203020170a94223860a0c1420202
def x3:=[(0x2aaaaaaaaaaaaaaa934e38c04c04d34ce1c71c700f429511fff03f00000f429511000,0),(0x3333333333333333009405539633a50136596590f0146fff509000fc00f0146000509,0),(0x3c3c3c3c3c3c3c3c2539502501594e965aaaaaaf00fff0a60b200003ff000000a60b2,0),(0x3fc03fc03fc03fc00e00a2a82a8000280104104aaf9848c4edcfc0fffaa09848c4edc,0),(0x3fffc0003fffc0002c02830a30a000a00410410cfae08ef88e0fff03fc0ae08ef88e0,0),(0x3fffffffc00000000e00ca0ca0c000300820820fccff0f00f00ffffc00ccff0f00f00,0)]
def xt3:=[(tv0,0),(tv1,0),(tv2,0),(tv3,0),(tv4,0),(tv5,0)]
def c3:Cfg:=⟨72,144,198,210,mk24,0x3fbf3ebe3bbb3aba071c71c71c71c71c7ffffffffffffffffff000000000000000000,mk25,mk26,mk27,mk28,mk29,mk20,mk21,mk22,mk23⟩
def N3:Nat->Nat
 | 6=>3
 | 7=>1
 | _=>0
def L3:Nat->Nat
 | 6=>2
 | 7=>0
 | _=>0
def H3:Nat->Nat
 | 6=>0xa6b96175b1643a0f39
 | 7=>0x3a0f39
 | _=>0
def P3:Nat->Nat
 | 6=>0x530000003f00000000
 | 7=>0x0
 | _=>0
def g3_0:=[sw9,sw10]
def g3_1:=[sw11,sw12]
def gs3:=[g3_0,g3_1]
def pa3:=[g3_0,g3_1,g3_0,g3_1,g3_0]
lemma b3_ok:(List.range 8).all (fun s=>span ((bar c3 (findAutPath c3.shTT mk0 pa3 (Rgen a1t6 7 xt3 P3) N3 L3 H3) (Rgen c3.all1v 7 x3 P3)) s) (N3 s) 0)=true:=by decide +kernel
lemma lb3:∀ t,HasCircuitSize 6 f3 t->8<=t:=prove_basePath f3 r3 mk0 c3 (fun _=>0) x3 xt3 gs3 pa3 [[(4,5),(1,2)],[(3,4),(0,1)]] N3 L3 H3 P3 rfl (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (span_all_sound b3_ok) (fun _=>Or.inl rfl)
def E4:List (Fin 6×Fin 6):=[(0,1),(0,2),(1,3),(2,4),(3,5),(4,5)]
abbrev f4:=gfn [] E4
def r4:=0x40460e1a0d00824c0528040460a0a0c80442c029410090a80628301245018560a0a0a0a0d828282828360a0a0a0a0d828282828360a0a0a0a0dcb864c582c52a1b3464c581c2c5172c54a541a1c2929d3858a941a1519b344c70b140d3a5464c6870a0d3264c9932642850a14284c993264c992448912244860c183060c326091120304884c9112140303044c9112140483024264c1222404814264c1118244014c911121818202
def x4:=[(0xaaaaaaaaaaaaaaaa4c04ca2930c30c30e4840432f57fc0fff000921010cbd500,0),(0xcccccccccccccccc94a9404ea14514514828a9c43fed7f000fc020a2a71000b5,0),(0xf0f0f0f0f0f0f0f038029302528a28a28131f0bfc233bf00003f04c7c20008ce,0),(0xff00ff00ff00ff00393300940514514531c13fd89b820003f03fc70400626e08,0),(0xffff0000ffff000000c02500ca28a28a3e3fc11f1c040003ffc0f800047c7010,0),(0xffffffff0000000002500c300c30c30c3ffe3e2020383ffc000000f8f88080e0,0)]
def xt4:=[(tv0,0),(tv1,0),(tv2,0),(tv3,0),(tv4,0),(tv5,0)]
def c4:Cfg:=⟨78,156,186,192,mk30,0xffffffa8fcf8eca81c71c71c7fffffffffffffffffffc0000000000000000000,mk31,mk10,mk11,mk12,mk13,mk4,mk7,mk5,mk6⟩
def N4:Nat->Nat
 | 6=>1
 | 7=>1
 | _=>0
def L4:Nat->Nat
 | 6=>0
 | 7=>0
 | _=>0
def H4:Nat->Nat
 | 6=>0x3a0f39
 | 7=>0x3a0f39
 | _=>0
def P4:Nat->Nat
 | 6=>0x0
 | 7=>0x0
 | _=>0
def gs4:=[[sw11,sw10],[sw13,sw14],[sw9,sw15,sw12]]
def au4:Nat->List (Nat×Nat×Nat×Nat)
 | 0=>[]
 | _=>[]
def ap4:List (List (Nat×Nat)):=[[]]
lemma b4_ok:(List.range 8).all (fun s=>span ((bar c4 (findAutGen c4.shTT mk0 gs4 au4 (Rgen a1t6 7 xt4 P4) N4 L4 H4 P4) (Rgen c4.all1v 7 x4 P4)) s) (N4 s) 0)=true:=by decide +kernel
lemma lb4:∀ t,HasCircuitSize 6 f4 t->8<=t:=prove_baseGen f4 r4 mk0 c4 (fun _=>0) x4 xt4 gs4 [[(3,4),(1,2)],[(2,5),(0,3)],[(4,5),(2,3),(0,1)]] au4 ap4 N4 L4 H4 P4 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 1<=i from hi) with ⟨k,rfl⟩;rw [nAC];rfl) (by decide +kernel) (span_all_sound b4_ok) (fun _=>Or.inl rfl)
def E5:List (Fin 6×Fin 6):=[(0,1),(0,2),(1,2),(3,4),(3,5),(4,5)]
abbrev f5:=gfn [] E5
def r5:=0x20202141862021030506091108182832208a060a0c901281828314246060a0c80840c141860a0c060a0d828301828360a0c060a0d828301828360a0c060a0d828301828360a0c060a0d828301828360a0c060a0da3262c162a52a1a3262c0e1a326162a52a0e1a32613252c5470d0c153232c4c70b0c0d2a32a4c68b0a0d2244891224448912244890a142850a12850a14285091224489122244891224460c183060c142850a142848912244892848890182848848890a0182848848890a02848890448491114241014884a1118242014888a121828202
def x5:=[(0x2aaaaaaaaaaaaaaa8e0138d34c00c30c30c30c30c8888895557fc003f000fc003f222222555500,0),(0x33333333333333331302556594014514514514515111112abfd540fc003f000fc0444444aa0055,0),(0x3c3c3c3c3c3c3c3c2500e38e3801861861861861a222223feaaabf000fc003f00088888800aaaa,0),(0x3fc03fc03fc03fc0004c0000e13618618618618603c3ffc303030000000003ffff0f0f000c0c0c,0),(0x3fffc0003fffc00000970a28025a28a28a28a28a3c3fc3cc0c0c00000ffffc0000f0000f303030,0),(0x3fffffffc00000000038000000ec30c30c30c30c3ffc3c3030303ffff00000000000f0f0c0c0c0,0)]
def xt5:=[(tv0,0),(tv1,0),(tv2,0),(tv3,0),(tv4,0),(tv5,0)]
def c5:Cfg:=⟨102,204,234,246,mk32,0x3ffffffa3ffa3a3a071c71c71c7fffffffffffffffffffffffffc0000000000000000000000000,mk33,mk10,mk11,mk12,mk13,mk20,mk21,mk22,mk23⟩
def N5:Nat->Nat
 | 5=>2
 | 6=>4
 | 7=>7
 | 8=>1
 | _=>0
def L5:Nat->Nat
 | 5=>1
 | 6=>2
 | 7=>3
 | 8=>0
 | _=>0
def H5:Nat->Nat
 | 5=>0xeefac1bbad2d
 | 6=>0xffda6bb031537320fc3a0f39
 | 7=>0xfa694af585053a85243a0f391b223b18f97c001f92
 | 8=>0x3a0f39
 | _=>0
def P5:Nat->Nat
 | 5=>0x200082900000435
 | 6=>0x1801439000000350100003d00000000
 | 7=>0x40000000280080000100000000008000020000003c00000024
 | 8=>0x0
 | _=>0
def gs5:=[[sw9],[sw11],[sw10],[sw12],[sw13,sw16,sw14]]
def au5:Nat->List (Nat×Nat×Nat×Nat)
 | 0=>[]
 | 1=>[sw17,sw18,sw19]
 | 2=>[sw20]
 | 3=>[sw13,sw16,sw14]
 | 4=>[sw15,sw21,sw22]
 | _=>[]
def ap5:List (List (Nat×Nat)):=[[],[(2,4),(1,3),(0,5)],[(0,2)],[(2,5),(1,4),(0,3)],[(2,3),(1,5),(0,4)]]
lemma b5_ok:(List.range 9).all (fun s=>span ((bar c5 (findAutGen c5.shTT mk0 gs5 au5 (Rgen a1t6 8 xt5 P5) N5 L5 H5 P5) (Rgen c5.all1v 8 x5 P5)) s) (N5 s) 0)=true:=by decide +kernel
lemma lb5:∀ t,HasCircuitSize 6 f5 t->9<=t:=prove_baseGen f5 r5 mk0 c5 (fun _=>0) x5 xt5 gs5 [[(4,5)],[(3,4)],[(1,2)],[(0,1)],[(2,5),(1,4),(0,3)]] au5 ap5 N5 L5 H5 P5 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 5<=i from hi) with ⟨k,rfl⟩;rw [nAC];rfl) (by decide +kernel) (span_all_sound b5_ok) (fun _=>Or.inl rfl)
def E6:List (Fin 6×Fin 6):=[(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,5)]
abbrev f6:=gfn [] E6
def r6:=0x804106061500822c4ca820090b1464820202141861804506061501014a093040208b012a1121481828360a090612141b050483090a0d828241848506c14120c2428360a090612141b050483090a0de3868c582c54a1a3262c0d1258a94a832253252a383054c8cf1a2c4c90e0c0d2a33a64a8d162428348912244891222448912244890a142850a14270e1c3870e1c2244891224488a142850a1428e18284480c1421222428050248890a0220512122281014884e18284480c08052223860a0c1420202
def x6:=[(0xaaaaaaaaaaaaaaaa4ce38e4c02930e1c3870e1c4082d9447ff0003f80fe004082d944400,0),(0xcccccccccccccccc3804d338a0253264c993264093426ffd0901fc00001fc09342600109,0),(0xf0f0f0f0f0f0f0f094002594000e142850a142a92083fa9ab2fe0007f0002920800a9ab2,0),(0xff00ff00ff00ff00013000a0c4c0489122448931c2fc4310dc000007f01ff1c2004310dc,0),(0xffff0000ffff000000e940013300a142850a143e3f0883e0e0000007ffe03e000883e0e0,0),(0xffffffff00000000025380025978c183060c183ffcf30c0300fffff80000003cf30c0300,0)]
def xt6:=[(tv0,0),(tv1,0),(tv2,0),(tv3,0),(tv4,0),(tv5,0)]
def c6:Cfg:=⟨88,176,206,224,mk34,0xffffffe8eeeceae81c71c71c71c7ffffffffffffffffffffff0000000000000000000000,mk35,mk10,mk11,mk12,mk13,mk36,mk37,mk38,mk39⟩
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
def g6:=[sw11,sw12]
lemma b6_ok:(List.range 9).all (fun s=>span ((bar c6 (findAut2 c6.shTT mk0 g6 (Rgen a1t6 8 xt6 P6) N6 L6 H6) (Rgen c6.all1v 8 x6 P6)) s) (N6 s) 0)=true:=by decide +kernel
lemma lb6:∀ t,HasCircuitSize 6 f6 t->9<=t:=prove_base2 f6 r6 mk0 c6 (fun _=>0) x6 xt6 g6 [(3,4),(0,1)] N6 L6 H6 P6 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (span_all_sound b6_ok) (fun _=>Or.inl rfl)
def bsT1:List BaseEntry:=[⟨3,E0,4⟩,⟨5,E1,7⟩,⟨5,E2,8⟩,⟨6,E3,8⟩,⟨6,E4,8⟩,⟨6,E5,9⟩,⟨6,E6,9⟩]
lemma hT1:BaseTableOk bsT1:=(baseTable_cons _ _ lb0 (baseTable_cons _ _ lb1 (baseTable_cons _ _ lb2 (baseTable_cons _ _ lb3 (baseTable_cons _ _ lb4 (baseTable_cons _ _ lb5 (baseTable_cons _ _ lb6 (fun _ h=>by cases h))))))))
def E7:List (Fin 6×Fin 6):=[(0,1),(0,2),(0,3),(1,2),(3,4),(3,5),(4,5)]
def f7:BFn 6:=fun x => (x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 2)||(x 3&&x 4)||(x 3&&x 5)||(x 4&&x 5)
def r7:=0x10108182830808085061890a44c951a2208a060a0d201441818514046060a0c60114181852228918062490128182832421130506100820c0c280808085061908a44a01892804906061501010a0c3060a0c0612141b050603090a0d828301848506c14180c2428360a0c0612141b050603090a0d828301848506c14180c2428368c98b058a943464c581c346162a52a0e1a32604a64a58a8e0c153232c4c706069519526345890a0d22448912244889122448912242850a142850942850a142850912244891224448912244891183060c183060a142850a1428a12224060a1091121403050848890a02848890028909222281014884a1118100a4445090c1420202
def x7:=[(0x2aaaaaaaaaaaaaaa933808d34d38d30003a34c00e1c3870e1c38720408aa54ffc000fe0007f000081022a95200,0),(0x3333333333333333254ff54e94e6a5a004da380122448912244894489115bfaa407f0003f8001fd122445600a9,3),(0x3c3c3c3c3c3c3c3c0e9403a53a500e000940940142850a142850a891221feb54bf8001fc000fe022448800ad52,3),(0x3fc03fc03fc03fc000013000a285404d301500e68d1a3468d1a340e1ffe1020700000000000fffc3870004081c,0),(0x3fffc0003fffc00000025a00000b2894e000a13a142850a142850f1fc3c60c18000001fffff0003c000f183060,3),(0x3fffffffc00000000000e0280000003a502c025c183060c183060ffe3c1830603ffffe000000000078f060c180,3)]
def xt7:=[(tv0,0),(tv1,3),(tv2,3),(tv3,0),(tv4,3),(tv5,3)]
def c7:Cfg:=⟨102,204,276,294,mk40,0x3ffffffa3ffa3aba071c71c71c71c71c71c71c7fffffffffffffffffffffffffc0000000000000000000000000,mk33,mk25,mk41,mk42,mk43,mk36,mk37,mk38,mk39⟩
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
def tg7:Fin 6->Nat | 0=>0 | 1=>3 | 2=>3 | 3=>0 | 4=>3 | 5=>3
def gs7:=[[sw9],[sw10],[sw13,sw16,sw14]]
def au7:Nat->List (Nat×Nat×Nat×Nat)
 | 0=>[]
 | 1=>[sw13,sw16,sw14]
 | 2=>[sw17,sw21,sw14]
 | 3=>[sw10]
 | 4=>[sw9]
 | _=>[]
def ap7:List (List (Nat×Nat)):=[[],[(2,5),(1,4),(0,3)],[(2,4),(1,5),(0,3)],[(1,2)],[(4,5)]]
lemma b7_ok:(List.range 10).all (fun s=>span ((bar c7 (findAutGen c7.shTT mk0 gs7 au7 (Rgen a1t6 9 xt7 P7) N7 L7 H7 P7) (Rgen c7.all1v 9 x7 P7)) s) (N7 s) 0)=true:=by decide +kernel
lemma lb7:∀ t,HasCircuitSize 6 f7 t->10<=t:=prove_baseGen f7 r7 mk0 c7 tg7 x7 xt7 gs7 [[(4,5)],[(1,2)],[(2,5),(1,4),(0,3)]] au7 ap7 N7 L7 H7 P7 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 5<=i from hi) with ⟨k,rfl⟩;rw [nAC];rfl) (by decide +kernel) (span_all_sound b7_ok) (checkTags_sound bsT1 hT1 f7 E7 tg7 [.emp,.b2 2 (.f0 0 (.base 0 [0,0,0,0,1,2])) (.f0 0 (.base 0 [0,0,0,0,1,2])),.b2 1 (.f0 0 (.base 0 [0,0,0,0,1,2])) (.f0 0 (.base 0 [0,0,0,0,1,2])),.emp,.b2 5 (.f0 3 (.base 0 [0,1,2])) (.f0 3 (.base 0 [0,1,2])),.b2 4 (.f0 3 (.base 0 [0,1,2])) (.f0 3 (.base 0 [0,1,2]))] (by decide +kernel) (by decide))
def E8:List (Fin 7×Fin 7):=[(0,1),(0,2),(1,3),(2,4),(3,5),(4,6),(5,6)]
def f8:BFn 7:=fun x => (x 0&&x 1)||(x 0&&x 2)||(x 1&&x 3)||(x 2&&x 4)||(x 3&&x 5)||(x 4&&x 6)||(x 5&&x 6)
def r8:=0x101183868320120d18a5040242a018a8080c505180301182828320120d00a503012450185c14141414141e0a0a0a0a0a0f050505050507828282828283c14141414141e0a0a0a0a0a0f050505050507cb8f0cd93161c166c52a343669d19b262c381cb858a545cb362b54a5468366870b149d29d3970b962a52a0d0e15362b66ad129d3858a941a1674b950d9a3366898e16281cd8f161b34e951931a1c283993264c993264993264c993263468d1a3468cc993264c993262c58b162c58a64c993264c98c993264c9932c98b04c911214064c122242649911a2428300c98182444c9322344850602648303048d099316099222428090605260b262c10993048890120664991058a1326088c12200cc8d121324c911121818202
def x8:=[(0x2aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa9338a013293060c183060c1a1490a48401086b2d7abfff01fc000fe03fa1490a48401086b2d7aa000,3),(0x333333333333333333333333333333332501302502a0a142850a142ca10500292e539043ffebb50003fff01fc04a10500292e539040000bb5,3),(0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c0e4c002a4e5142850a142850c0260931f8617ffe011ccefe03f8001fc00c0260931f8610002011cce,3),(0x3fc03fc03fc03fc03fc03fc03fc03fc00e02528c0002850a142850a006383fc04fffc18b8dd008fffc0000003f806383fc04000418b8dd008,3),(0x3fffc0003fffc0003fffc0003fffc0000094030094c50a142850a14707c031fff3821df02e0110000007ffe03ff07c0300003821df02e0110,3),(0x3fffffffc00000003fffffffc00000000000c4c0000a142850a14287f83ffe0183fc1e003001e0000007ffffc07f800000183fc1e003001e0,3),(0x3fffffffffffffffc00000000000000000380940300c183060c18307ffffc1fe0c006003c01e00fffff80000000003fc1fe0c006003c01e00,3)]
def xt8:=[(tv6,3),(tv7,3),(tv8,3),(tv9,3),(tv10,3),(tv11,3),(tv12,3)]
def c8:Cfg:=⟨140,280,310,322,mk44,0x3ffffffffffffb2a3ffe3fea3f3e3b2a071c71c71c7fffffffffffffffffffffffffffffffffff00000000000000000000000000000000000,mk45,mk10,mk11,mk12,mk13,mk20,mk21,mk22,mk23⟩
def N8:Nat->Nat
 | 7=>1
 | 8=>6
 | 9=>1
 | _=>0
def L8:Nat->Nat
 | 7=>0
 | 8=>3
 | 9=>0
 | _=>0
def H8:Nat->Nat
 | 7=>0x4bbd1
 | 8=>0xd0086eb9560893ea786ae3574c46e804bbd1
 | 9=>0x4bbd1
 | _=>0
def P8:Nat->Nat
 | 7=>0x0
 | 8=>0x10000b400800007000000240000003c0000007400000000
 | 9=>0x0
 | _=>0
def tg8:Fin 7->Nat | 0=>3 | 1=>3 | 2=>3 | 3=>3 | 4=>3 | 5=>3 | 6=>3
def gs8:=[[sw23,sw24,sw25],[sw26,sw27,sw28]]
def au8:Nat->List (Nat×Nat×Nat×Nat)
 | 0=>[]
 | 1=>[sw29,sw30,sw31]
 | 2=>[sw32,sw33,sw34]
 | _=>[]
def ap8:List (List (Nat×Nat)):=[[],[(3,6),(1,4),(0,2)],[(4,6),(2,5),(0,3)]]
lemma b8_ok:(List.range 10).all (fun s=>span ((bar c8 (findAutGen c8.shTT mk0 gs8 au8 (Rgen a1t7 9 xt8 P8) N8 L8 H8 P8) (Rgen c8.all1v 9 x8 P8)) s) (N8 s) 0)=true:=by decide +kernel
lemma lb8:∀ t,HasCircuitSize 7 f8 t->10<=t:=prove_baseGen f8 r8 mk0 c8 tg8 x8 xt8 gs8 [[(5,6),(3,4),(1,2)],[(4,5),(2,3),(0,1)]] au8 ap8 N8 L8 H8 P8 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 3<=i from hi) with ⟨k,rfl⟩;rw [nAC];rfl) (by decide +kernel) (span_all_sound b8_ok) (checkTags_sound bsT1 hT1 f8 E8 tg8 [.b2 1 (.f0 2 (.b2 3 (.f1 6 (.emp)) (.f1 4 (.emp)))) (.b2 2 (.f1 6 (.emp)) (.f1 5 (.emp))),.b2 0 (.f0 2 (.b2 3 (.f1 6 (.emp)) (.f1 4 (.emp)))) (.b2 3 (.f1 6 (.emp)) (.f1 4 (.emp))),.b2 0 (.f0 1 (.b2 3 (.f1 6 (.emp)) (.f1 4 (.emp)))) (.b2 3 (.f1 6 (.emp)) (.f1 4 (.emp))),.b2 1 (.f0 0 (.b2 2 (.f1 6 (.emp)) (.f1 5 (.emp)))) (.b2 2 (.f1 6 (.emp)) (.f1 5 (.emp))),.b2 2 (.f0 0 (.b2 1 (.f1 5 (.emp)) (.f1 5 (.emp)))) (.b2 1 (.f1 5 (.emp)) (.f1 5 (.emp))),.b2 3 (.f0 1 (.b2 0 (.f1 4 (.emp)) (.f1 4 (.emp)))) (.b2 0 (.f1 4 (.emp)) (.f1 4 (.emp))),.b2 4 (.f0 2 (.b2 0 (.f1 3 (.emp)) (.f1 3 (.emp)))) (.b2 0 (.f1 3 (.emp)) (.f1 3 (.emp)))] (by decide +kernel) (by decide))
def bsT2:List BaseEntry:=[⟨6,E7,10⟩,⟨7,E8,10⟩]++bsT1
lemma hT2:BaseTableOk bsT2:=(baseTable_cons _ _ (baseEntry_of_f f7 E7 (by decide +kernel) lb7) (baseTable_cons _ _ (baseEntry_of_f f8 E8 (by decide +kernel) lb8) hT1))
def E9:List (Fin 7×Fin 7):=[(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(2,6),(3,4)]
def f9:BFn 7:=fun x => (x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 0&&x 4)||(x 1&&x 2)||(x 1&&x 5)||(x 2&&x 6)||(x 3&&x 4)
def r9:=0x4213469981440120608895005838222410150a9483080644c921460ad1b350e20200911262801906049104042060a0d801506049108041060616101d088483824b822220d601d11048514049180624a011860291284b844441908cd1104855005818222490114601916807844221608ad088483182b4444418808024449831111062224283311110622242833111106222428331111062224283311110622242833111106222428331111062224283e9b3254991396ac4c9522f1c6d58a2f1c313868c11f1a6d5892f1c293868c09e9b32e4ad5274c8d162252c38305e5ab1e286d992e54991a22c38303e3a69d197261b562b54a52a4c88d1624283e1c3870e1c3870d1a3468d1a3468c3870e1c3870e1a54a952a54a952952a54a952a54a68d1a3468d1a3458b162c58b162c68b1214181294a8448502d18654882b14211828401e18695082d18212848801e1a30e0a54254885060212428101e1a30e082d182c50910a02830201e1a2950952213460b1424284880c1420202
def x9:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa9534d34c03934d34d38d34d30234d34e300e0f0f0f0f0f0f0f00049149120512821fffff0000ff000000000004914912051282100000,0),(0xcccccccccccccccccccccccccccccccc0000250130009403a5540a804c002a0154c03131313131313103f2042040a8effff2a049000000ffff000003f2042040a8e00002a049,0),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f04c000096500038094002502a95500094094052525252525252fc0048048ffff054e015920000000000fffffc00480480000054e01592,0),(0xff00ff00ff00ff00ff00ff00ff00ff003a594e3bf4ce00e00a02a94c01a94c01ae1384848484848484492b6efff430441844c61c00ff0000ff00ff492b6e000430441844c61c,3),(0xffff0000ffff0000ffff0000ffff000000e380000965025000680325e003a5a8002588888888888888924fffb6e8c088608b18e0ff0000ff00ff00924000b6e8c088608b18e0,3),(0xffffffff00000000ffffffff00000000b00b0e00e00002800c3280002a8a00a0c28020202020202020e3fc70c70f010f7f0c1f00ffffff0000ffffe00c70c70f010f7f0c1f00,1),(0xffffffffffffffff000000000000000038000038e028000028a0c00030c00032830040404040404040ff8f80f80ffe0f800fe000ffffffffff0000038f80f80ffe0f800fe000,1)]
def xt9:=[(tv6,0),(tv7,0),(tv8,0),(tv9,3),(tv10,3),(tv11,1),(tv12,1)]
def c9:Cfg:=⟨144,288,390,432,mk46,0xfffefefcfffafaf8ffeeeeecffeaeae81c71c71c71c71c71c71c71c71c71c71c71c7ffffffffffffffffffffffffffffffffffff000000000000000000000000000000000000,mk47,mk33,mk48,mk49,mk50,mk51,mk52,mk53,mk54⟩
def N9:Nat->Nat
 | 5=>6
 | 6=>37
 | 7=>83
 | 8=>110
 | 9=>15
 | 10=>1
 | _=>0
def L9:Nat->Nat
 | 5=>3
 | 6=>6
 | 7=>7
 | 8=>7
 | 9=>4
 | 10=>0
 | _=>0
def H9:Nat->Nat
 | 5=>0xba9c1793d43a8f50ef52114437b3f91aae26
 | 6=>0xfdf6a1eeb668ed9dccead113e8b77bdb63bfcd8fa5c6b7cfb7691ab08eaa8b38ad8a5fe689da1e892c658401e6804d5d7a2511758521721551697a5763309061f7d9608f494c51df4b1e5e44d08b42c1f33ff6b72e33ae1c37d91aae261a347d1084590ec6750d6d6d032ecc008b05
 | 7=>0xff09f4fdac1bf8abc6f67292efff1deecb9cec6009ead113e8f91ae69741e671b9dc9449d5a584d251f1cf198ec1adf6c0d2b8bda347bd90f7b8648bb35f38af5b7aac15b3a8612aa468f1a32363a30061a272da9fc9019e78f29e60719c97b192342c919aad8d1ec58c8d5c8b445d841499811b44804d5d7f19dc7dd0dd7719b07465ac718b936d05d36b9d4368455662c732608f495c399e5ad10e55efd752f5715037674e56b24deea64a723e4a6cb049c4ae444ba642c1f33ec80b33fdfc320bef31817c3081a12ccd242b6ef425352c2515cc2180a31dd4d71b92531934e717018015968e144e1810b46e1094cd0d6d6d08986008447b
 | 8=>0xfbd136f9b7d5f8b775f76bdcf6034cf2ab5ff014fcf01492ef417ced4f00ec6009ea613de84cefe671b9e5947be3acffe0fe68db2bb9d93375d6b940d44aaed1b507cdc511cd6c70cb72ffc7f7dbc5abe2c44352c143bfc07045be5502ba81f5b9be8fb7d436b5883db41fadb3d03fb390cab23c04ae315da8612aa5bae6a35378a333d7a312bfa300619ec8af9e6a4e9e60719d22dd987bfe9839dd96788695c05791080c8efe208ca8e08aaa14888c1c8593ed8273ed7f4b8f78db44779e4f771b5973e67e718b9370d7c26e33a66d05d36c384b6bf7656b9d4364c97c614fbf60c6325fa3725c11c95b1f0c5ad10e505b004bf184490dcb4206853f17c83b44bb36092e3493053210fb2f19112ef4232a873f2a329f29f7ea27a8c2255cc923f43922faa02180a31fe8ea1e05e91b9a461b8e4a193ec417e726141f4711d46a0be61a0972a108ae7a
 | 9=>0xf6034cec6009c7320fc44352c07045b9be8fb41fad9e6a4e7de2ff72ae37718b936b9d4323f43920960511d46a
 | 10=>0x718b93
 | _=>0
def P9:Nat->Nat
 | 5=>0x682a00000025000018260000503900007c3d00005479
 | 6=>0x842b00008473000084230000942d00006ca10000847b0000f873000134410000b4990000742d00000825000138a90000e82d000134a90000ac830000ec390000283d0000543e0000843b000110a90000b8390000f4a10000e03d00013859000134590000c8a10000eca100009c7900002051000138a10000ac7900012c3a0000e4a900009ca900007ca900008841000068a9
 | 7=>0x78250000d4c900017851000080d90001143b0001142b0000ac730000a02d000114460000409900018cab000040a1000060d10000c03d0001143a00002c260000f43a00012c2d0001802f000080710000f4390001003e000114ab00018c2e000100b300017c55000128c9000114a30000f4a30001383d0000943e0000c4c90001004a0001103e0000302d00004c2d00004c3d0000782f000030410001143900002c2500002c2d0000f42b0001145300000000000094b30000aca30000a4ab000100420001003d000078ab000140d100010ca100017cd9000170730000603d000078260001a855000074a30000f49b0001149b000114a10000782d000080510000742600002c2f0000508b0000e0730000f43b00004cd10000a02f000128a1000100a300002cab00018056000178c90000f4530000b04100002c4a0000d451000078a90000d4390000ccc9
 | 8=>0x1c75000038d300003464000038b3000010280000389b000038db000034a30000280100001c6c000010730000005100000c2c000034ab000020cb00000c400000205c000038390000283e0000186200000c020000043e000004560000343c0000203500002ca300002c8300001003000030db00001034000008d1000028d300001001000020d3000020b300001024000024a30000385300002835000020db0000342e000038c90000204a0000003a00002c73000020c9000008ab0000103c00000c3e0000082a00001ce3000008520000183e000000390000180100000c0100003450000000530000203e0000380100000c30000018bb00001c4a000000990000383e0000204200000000000038a30000389900000cb30000340100000001000010a30000187a00002052000020620000383b000034300000083a000028d100000899000018560000302e000030a300002c7b0000344c0000003b000030a10000200100003851000020a30000082e000038cb0000383a000008db000008b30000100400001c7a000020a100003402000008d300001c0100001c8200001ca30000009b0000083e00001038000000d300001c3e00003454
 | 9=>0x280000007300000002000000030000003400000001000000240000003c000000440000000700000000000000a3000000040000006c00000038
 | 10=>0x0
 | _=>0
def tg9:Fin 7->Nat | 0=>0 | 1=>0 | 2=>0 | 3=>3 | 4=>3 | 5=>1 | 6=>1
def g9_0:=[sw24]
def g9_1:=[sw23,sw25]
def gs9:=[g9_0,g9_1]
def pa9:=[g9_0,g9_1,g9_0]
lemma b9_ok:(List.range 11).all (fun s=>span ((bar c9 (findAutPath c9.shTT mk0 pa9 (Rgen a1t7 10 xt9 P9) N9 L9 H9) (Rgen c9.all1v 10 x9 P9)) s) (N9 s) 0)=true:=by decide +kernel
lemma lb9:∀ t,HasCircuitSize 7 f9 t->11<=t:=prove_basePath f9 r9 mk0 c9 tg9 x9 xt9 gs9 pa9 [[(3,4)],[(5,6),(1,2)]] N9 L9 H9 P9 rfl (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (span_all_sound b9_ok) (checkTags_sound bsT2 hT2 f9 E9 tg9 [.emp,.emp,.emp,.base 5 [0,1,2,0,3,4,5],.base 5 [0,1,2,3,0,4,5],.f0 6 (.base 4 [0,1,2,3,4]),.f0 5 (.base 4 [0,1,2,3,4])] (by decide +kernel) (by decide))
def E10:List (Fin 7×Fin 7):=[(0,1),(0,2),(0,3),(0,4),(1,2),(3,5),(4,6),(5,6)]
def f10:BFn 7:=fun x => (x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 0&&x 4)||(x 1&&x 2)||(x 3&&x 5)||(x 4&&x 6)||(x 5&&x 6)
def r10:=0x4042060a0c201041818540220e192a0202021418680410e16341092681828340220e012a1101481828388061060614a01894029114051280624202021418680410e0234210188182833406550064602031414604805106061705050188890a0f05050188890a0f05050188890a0f05050188890a0f05050188890a0f05050188890a0f05050188890a0f05050188890a0fa72e193161c172d58a94a86cd5a3262c381e3a70b1528b96ac54a5468312325e3a70b152950267468ad93253c587060b3a3436c9919e2c383039b2e4c586d59b14a8ce9b32549911a2c485073264c993264c992a54a952a54a95060c183060c182d1a3468d1a3468c993264c993264850a142850a14270e1c3870e1c3868d1a3468d1a34d193048890a03868c14244264a91121418070d18182844c9522242830108182d193048890a0032a141648909a242810199120b44884e1418100cc952224268c98244470d18284880c1420202
def x10:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa4d338e3a32934d34ce2934c04c3c3c3c3c3c3c3c3c10008005c1490921fffff80007f80007f800002001000b8292124200000,0),(0xcccccccccccccccccccccccccccccccc94e013015025380a93025a80384444444444444445224912481236f7ff4a524807f80007f80007fa44922490246de00094a49,3),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f03a502500e00e96a02500e00094484848484848484a44922490243ffede94a497f80007f80007f8048924492048000dbd29492,3),(0xff00ff00ff00ff00ff00ff00ff00ff000004c00004c0000940000a0a009090909090909090071c3fe07fe0a414e038e7fff800000007fff80e387fc000414829c071c,3),(0xffff0000ffff0000ffff0000ffff00000000004d80000250004c094c01212121212121212387e038ffb804c098073f00000007fff807ffff0fc07000700981300e7e0,3),(0xffffffff00000000ffffffff000000000009403a8968000300300013a28282828282828283f81fff013f8700e007c000000007fffff80007f00000027f0e01c00f800,3),(0xffffffffffffffff0000000000000000000380940300a0c000968325030303030303030303ffffc0fe40380700f80007fffff80000000000003f81fc80700e01f0000,3)]
def xt10:=[(tv6,0),(tv7,3),(tv8,3),(tv9,3),(tv10,3),(tv11,3),(tv12,3)]
def c10:Cfg:=⟨151,302,374,404,mk55,0xffffffffffffeae8ffeaffe8eaeaeae81c71c71c71c71c71c71c71c71ffffffffffffffffffffffffffffffffffffff80000000000000000000000000000000000000,mk56,mk25,mk41,mk42,mk43,mk11,mk57,mk12,mk13⟩
def N10:Nat->Nat
 | 6=>1
 | 7=>5
 | 8=>48
 | 9=>16
 | 10=>1
 | _=>0
def L10:Nat->Nat
 | 6=>0
 | 7=>3
 | 8=>6
 | 9=>4
 | 10=>0
 | _=>0
def H10:Nat->Nat
 | 6=>0xc11ff7
 | 7=>0xf273e39720a189002e466fe40df704
 | 8=>0xf74a15ed067dec1d2bdf539ddd82b6d6a5abd267d1cf95afcf766ccf5f56cbbbeac4ce28c17d32ba541ab8529fb752c9b6c9cfb615b6b5a379b1c214a61557a562eda3ed219a368f9720a19259fb869ae57248746af7cb5afe805a2b5b58846f516a22502eca4eefed4a4ae249b068435a554123583bef5837b86035769b3157ee2b07cd253b2f1de2e91c3959102ed9
 | 9=>0xed067decc71de705cfdf539dcf766cc3ff5cb8529fb6c9cfa562eda30e739843459720a15761cb462b1338a6f20f5485
 | 10=>0x9720a1
 | _=>0
def P10:Nat->Nat
 | 6=>0x109d
 | 7=>0xac8200000000000088cd0000b4410000b42d
 | 8=>0x83e0000102400003c420000100100001c750000209a00001cca00000c0b0000107c0000203e00002401000028a200003c6200001caa000010b40000183e000010440000089a0000389a0000284a000020da00001074000020a200003c5200000000000018d2000028ca000018ca00003c0100002c3e00001cd200000c070000043e00002cd20000206200001c4a000024da00003c4a0000288200003c9a0000243e000008d2000024cd000020ca00001c0100001c8200003c3d00002c62
 | 9=>0x2400000002000000c4000000010000007c0000003c000000b400000044000000740000008c0000000700000000000000030000006c000000340000000b
 | 10=>0x0
 | _=>0
def tg10:Fin 7->Nat | 0=>0 | 1=>3 | 2=>3 | 3=>3 | 4=>3 | 5=>3 | 6=>3
def g10_0:=[sw25]
def g10_1:=[sw23,sw24]
def gs10:=[g10_0,g10_1]
def pa10:=[g10_0,g10_1,g10_0]
lemma b10_ok:(List.range 11).all (fun s=>span ((bar c10 (findAutPath c10.shTT mk0 pa10 (Rgen a1t7 10 xt10 P10) N10 L10 H10) (Rgen c10.all1v 10 x10 P10)) s) (N10 s) 0)=true:=by decide +kernel
lemma lb10:∀ t,HasCircuitSize 7 f10 t->11<=t:=prove_basePath f10 r10 mk0 c10 tg10 x10 xt10 gs10 pa10 [[(1,2)],[(5,6),(3,4)]] N10 L10 H10 P10 rfl (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (span_all_sound b10_ok) (checkTags_sound bsT2 hT2 f10 E10 tg10 [.emp,.f0 2 (.base 3 [0,0,0,1,4,2,3]),.f0 1 (.base 3 [0,0,0,1,4,2,3]),.f0 5 (.b2 6 (.f0 4 (.base 2 [0,1,2])) (.f0 4 (.base 2 [0,1,2]))),.f0 6 (.b2 5 (.f0 3 (.base 2 [0,1,2])) (.f0 3 (.base 2 [0,1,2]))),.f0 3 (.b2 6 (.f0 4 (.base 2 [0,1,2])) (.f0 4 (.base 2 [0,1,2]))),.f0 4 (.b2 5 (.f0 3 (.base 2 [0,1,2])) (.f0 3 (.base 2 [0,1,2])))] (by decide +kernel) (by decide))
def E11:List (Fin 7×Fin 7):=[(0,1),(0,2),(0,3),(1,2),(1,4),(2,5),(3,6),(4,6)]
def f11:BFn 7:=fun x => (x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 2)||(x 1&&x 4)||(x 2&&x 5)||(x 3&&x 6)||(x 4&&x 6)
def r11:=0x2241851a18585062468a0d802c3c6192500716a8624201851a18504062468a0c60a70f1d0e80208d13322082881828304042060a0ca02894031284062060a0c88470904852228c12120d08270484831809c2424186018920289140614a06262418418185220a0d0064850470909062805c241215101704848380208d0132224282141868040548254284848483090a0e84848483090a0e84848483090a0e84848483090a0e84848483090a0e84848483090a0e84848483090a0fc71e1ab45cb1528d0992a46478d1624e5c7854a54683a646896ad3a264a9321ca93227365c91a2bc6ad172c4c952151c182e38d0dd33648cf1a2c4c90e0c0f1c586e55a94674c951a2c485078b162c58b162c5870e1c3870e1c312244891224488e1c3870e1c3870c58b162c58b162a952a54a952a5470e1c3870e1c38e18b054a0e18284480c142221c2830262c3822428301522140b161c11214180c5091038b0e08505c3160a9422428088a04070c482e18b04270c142240604038a24270a94223860a0c1420202
def x11:=[(0x2aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa934ce4d34c03a34c04e38e30134d3a804d328e001c1c1c1c1c1c1d02004408bd28535447fff807f80007f80002040088117a50a6a888000,0),(0x333333333333333333333333333333330e95338e9530159539405554c0b8e4e30250132864646464646464404089f102428dfffea84ff800000007f800808113e20485180005509,0),(0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c253800253a500e3aa39500096a02501594002500a8a8a8a8a8a8a8149f100203fffe829905900007f8000007f8293e200400000105320b2,0),(0x3fc03fc03fc03fc03fc03fc03fc03fc00000094003f4c000000a68aa2594002828a4c0311111111111111278ea015ffc1308231076e0000007f807fffcf1d402800026104620edc,3),(0x3fffc0003fffc0003fffc0003fffc0000002500000e380025028b0c28000094aa0c3004e424242424242439f0cffe0281c103be04700000007fff807ff3e18000050382077c08e0,3),(0x3fffffffc00000003fffffffc00000000002cb0000e00000000c02830000000c3280000080808080808083e01fe19c339fe13c027807fff807fffff807c001c338673fc27804f00,1),(0x3fffffffffffffffc0000000000000003ef8e38e38096800ca0000000c3383000009789703030303030303fff0fe1fc3e001c0038007fffff8000000000021fc3f87c0038007000,3)]
def xt11:=[(tv6,0),(tv7,0),(tv8,0),(tv9,3),(tv10,3),(tv11,1),(tv12,3)]
def c11:Cfg:=⟨143,286,394,442,mk58,0x3ffffffe3ffffffa3fbf3ebe3bbb3aba071c71c71c71c71c71c71c71c71c71c71c71c71ffffffffffffffffffffffffffffffffffff800000000000000000000000000000000000,mk59,mk60,mk61,mk62,mk63,mk64,mk65,mk66,mk67⟩
def N11:Nat->Nat
 | 6=>7
 | 7=>43
 | 8=>119
 | 9=>19
 | 10=>1
 | _=>0
def L11:Nat->Nat
 | 6=>3
 | 7=>6
 | 8=>7
 | 9=>5
 | 10=>0
 | _=>0
def H11:Nat->Nat
 | 6=>0xe9b48ccf9f03c665569ef2f99689577b43a759a674
 | 7=>0xff4747fea3e0fe3f0cfc4e2bf56ea8f07485eb845ae6b3aae35a2ed8d702d7499dd38693ce2b5dc66556bd21f2bc64bfbc14fcbbcc8ab855ecaae26ca16c73a101919ef2f97d677779138274cad97456e068dfd05e930b5bfc5e53733252a3984740cf3e3bc139e7cc38f2d438da531df13a18b2831531871377e20e536b08a239
 | 8=>0xff4747fe3f0cfdd095fd8b3bfc4e2bfae71ff8ebc4f56ea8f172aaf087edefdd98ee5ef7ee3b3fee0338ed986bec56ebe5fef0e57bbbe507f0e06174dfe635d8c182d8083bd7499dd5c144d41736d39852ceb9fecb91decb795dcb7496c56378c50447c1467ec07afabecdebbdc5b0bbcc8abba79cba8caab97c13b4f54cb4ce5eaffecaad497eac9c63ac5bb7a5bae6a113aa9ed6cb9c95069732bf96d04196261a94c8ad8afb3a89cdd383f408835abe82b6c57f5ed87a83cf7913826b2a7a6991d067df32655dd15e8b0f5e68805d0f905c27dd59c90558fa6a583a7d58267856e4b1516aa84f5be34b19d94740cf467208464dd3450b4c4345dd40d3264044433ee2453b4f7039e7cc38da53389a2636fa84369aa531ac973162a5307ef32ec0502d93982a329f281df424471123259321d9112049f81d43ed1c5e49191e98153f951247660ea72a0769e306c773062b3a061fbf058ebd03d03903ced20330db0099f7
 | 9=>0xff61b0fe3f0ce15367cb795dc07afabdc5b0b2d943ad497e9042de88fbc382b6c57913826b2a7a53e58846720840d3262b1dc71f710a1c5e49
 | 10=>0xfe3f0c
 | _=>0
def P11:Nat->Nat
 | 6=>0x743b0000747300009c3d00002039000074230000907500001825
 | 7=>0x148710000783a0000000000008899000148c9000158990001b84a000130a100006c9900009c8b000148390000c42d0000782b0001c83d0000787a00017c730001c8420000ec510000943d0000742d0001b42600000041000078390001a0710001d473000074620000a45500006ca10000742f00007873000130510001a05100014851000078530000e03e0000744a000164a100000c3d0001c43e0001c83e0000783b00002c990000789b
 | 8=>0x34710000000000003856000020a300000c990000209900001c01000034c9000038750000189900000c94000028ca00000cca00000c5200001c400000203b000018ab000014ab00003862000014ca000008d200003cca0000107b000034390000142e0000247200003c01000014a300003c4a0000442c0000349900000c7a0000182a000014a10000449c00003473000044300000205100000ca30000384a00002c76000034cb0000283e00001c2c0000446c00001c0200002456000020c900003c720000043e00002cd20000007b0000343b0000083e000008560000349b000008720000086200001472000044280000209b00003c94000044730000440600003c3e0000203900002ccd000018ca00002c3e00003cb300001cb400001c9c000040010000383e00000c350000403e0000243e000034b300001c8c000034510000440100003ca3000028d200002862000044240000205300000c9b00001ca400001c3e00003ca1000034a30000343a000024ca00001cac0000182e0000240100003c3500003401000020cb00001c9400002c0100003882000028b300002882000024d2000044050000285600000c3e000020010000007300003c620000345300003801000024820000084a00001c6c0000203e0000045600000c42
 | 9=>0x700000000000000ac0000002c0000009c000000300000000d0000006c000000540000004c0000002800000073000000060000000200000001000000240000003c000000b400000005
 | 10=>0x0
 | _=>0
def tg11:Fin 7->Nat | 0=>0 | 1=>0 | 2=>0 | 3=>3 | 4=>3 | 5=>1 | 6=>3
def g11:=[sw24,sw28]
lemma b11_ok:(List.range 11).all (fun s=>span ((bar c11 (findAut2 c11.shTT mk0 g11 (Rgen a1t7 10 xt11 P11) N11 L11 H11) (Rgen c11.all1v 10 x11 P11)) s) (N11 s) 0)=true:=by decide +kernel
lemma lb11:∀ t,HasCircuitSize 7 f11 t->11<=t:=prove_base2 f11 r11 mk0 c11 tg11 x11 xt11 g11 [(3,4),(0,1)] N11 L11 H11 P11 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (span_all_sound b11_ok) (checkTags_sound bsT2 hT2 f11 E11 tg11 [.emp,.emp,.emp,.f0 5 (.b2 6 (.f0 4 (.base 2 [0,1,2])) (.f0 4 (.base 2 [0,1,2]))),.f0 5 (.b2 6 (.f0 3 (.base 2 [0,1,2])) (.f0 3 (.base 2 [0,1,2]))),.base 8 [0,1,2,3,4,0,5],.base 5 [0,1,2,3,4,5]] (by decide +kernel) (by decide))
def E12:List (Fin 7×Fin 7):=[(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(3,6),(4,5)]
def f12:BFn 7:=fun x => (x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 2)||(x 1&&x 4)||(x 3&&x 5)||(x 3&&x 6)||(x 4&&x 5)
def r12:=0x88061460614101489928344852264a0c1013068c83404052a34c0202021418640208b132a02010418185100522c4a2480248d131240208b012a1084441818544052060a0d20144181852228c12120c20202141861406148062488ca9202891804506061501014a093022090b0064a121c81828348090850619208a9218283046a480a26201841818528092300c4984850483090a0d84850483090a0d84850483090a0d84850483090a0d84850483090a0d84850483090a0d84850483090a0ee58992a474e3c1e3868c582c54a3a72e3c293464c581a25b3569d172cd8992a4c858a94a83227365ab1a2a64a547060b9b1d6a74a3434c8cf1a2c4c90e0c0f2e3ab161a54674c951a2c4850793264c993264c98b162c58b162c5870e1c3870e1c352a54a952a54a9468d1a3468d1a270e1c3870e1c382850a142850a1470c0c1422a51a070c14224060a1193161c1092224280502c98b0e0a94684485060244485011038b0d185051212228101c986a51a1120a44270c142240604039315489092223860a0c1420202
def x12:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa4d34d300e3934c02a34d38ce4e34c0a933804d3001c1c1c1c1c1c1c0840841222daca9447fff80007f807f800001081082445b5952888000,0),(0xcccccccccccccccccccccccccccccccc3a596539300e01300e94e553a8038a4e54c000e4c64646464646464400929a0442537fffd284807f800000007f880125340884a600002509,0),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f094e38002502538e0153a502501a94000e9682a5a82828282828282a92921044883ffd2a9ad597f80007f807f8052524208910000a5535ab2,3),(0xff00ff00ff00ff00ff00ff00ff00ff0000000e3804c09404c0000680955a0c0000159400191919191919193e31c017fffc020031006e00000000007ffffc638020000004006200dc,0),(0xffff0000ffff0000ffff0000ffff000000000e4c0380025300000b0002801394000ae0096424242424242431fe3ff87008841c3e08700000007fffff8063fc0000e01108387c10e0,3),(0xffffffff00000000ffffffff0000000000ef8094094038e968a28000000025318a2300032828282828282801fffde780f31860c031807fffff8000000000007bcf01e630c1806300,3),(0xffffffffffffffff0000000000000000b0000000000000000000000030c00002800c3280101010101010103fc03e07ff03e07f003e007fffffffff800003807c0ffe07c0fe007c00,1)]
def xt12:=[(tv6,0),(tv7,0),(tv8,3),(tv9,0),(tv10,3),(tv11,3),(tv12,1)]
def c12:Cfg:=⟨143,286,388,448,mk68,0xffffffe8ffecffe8ffffffe8eeeceae81c71c71c71c71c71c71c71c71c71c71c71c71c71ffffffffffffffffffffffffffffffffffff800000000000000000000000000000000000,mk59,mk33,mk48,mk49,mk50,mk69,mk70,mk71,mk72⟩
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
def tg12:Fin 7->Nat | 0=>0 | 1=>0 | 2=>3 | 3=>0 | 4=>3 | 5=>3 | 6=>1
lemma b12_ok:(List.range 11).all (fun s=>span ((bar c12 (findAut1 c12.shTT mk0 (Rgen a1t7 10 xt12 P12) N12 L12 H12) (Rgen c12.all1v 10 x12 P12)) s) (N12 s) 0)=true:=by decide +kernel
lemma lb12:∀ t,HasCircuitSize 7 f12 t->11<=t:=prove_base1 f12 r12 mk0 c12 tg12 x12 xt12 N12 L12 H12 P12 rfl (by decide +kernel) (by decide +kernel) (span_all_sound b12_ok) (checkTags_sound bsT2 hT2 f12 E12 tg12 [.emp,.emp,.f0 6 (.base 3 [0,1,0,4,2,3]),.emp,.f0 5 (.b2 6 (.f0 3 (.base 2 [0,1,2])) (.f0 3 (.base 2 [0,1,2]))),.f0 4 (.b2 6 (.f0 3 (.base 2 [0,1,2])) (.f0 3 (.base 2 [0,1,2]))),.base 8 [0,1,2,3,4,5]] (by decide +kernel) (by decide))
def E13:List (Fin 7×Fin 7):=[(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,6),(5,6)]
def f13:BFn 7:=fun x => (x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 2)||(x 1&&x 4)||(x 3&&x 5)||(x 4&&x 6)||(x 5&&x 6)
def r13:=0x1121489928304052264a0c40148b12890808085061900883864a8302a65c9c6a08414181854805106061410108182834411085061850144a01894445a060a0e010458095040220e012a22018418185220a0d0064a08a981828318052280a2520242141868080c505180a028940312c1414120c24283c1414120c24283c1414120c24283c1414120c24283c1414120c24283c1414120c24283c1414120c24283e9c7864c58705cb1528d0d9ab464c58703c70b1528b96ac54a546832344a4bc72e162a52a0c899d1a2b54c94a8e0c1674686d99b24c8cf1a2c4c90e0c0e6cb93161b54a8ce992a345890a0e64c993264c993254a952a54a952a0c183060c18305a3468d1a3468d18b162c58b162c512244891224488e1c3870e1c3871a3160911214070c14224264a91121418070c0c142264a9112141808850282d18b048890a0220654282c5121222810199120b462c12213860a112030201992a44484d12223860a0c1420202
def x13:=[(0x2aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa934d338e0234d33934c0293aa34ce000070707070707074420400428b364a447fffc0003fc03fc000110810010a2cd929110000,0),(0x33333333333333333333333333333333259404c04ce3a58ea94a00e4d50130131919191919191908048249c10c9bfffd242403fc000003fc00201209270432600004909,0),(0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c0e38e94039594e54038002500eaa502a0a0a0a0a0a0a0a91491490120fff4a9a5acbfc0003fc0003fe4524524048000d2a696b2,3),(0x3fc03fc03fc03fc03fc03fc03fc03fc000025013fc80000250004c001894028024242424242424018e1fe0bff81203138373fffc00000003fc06387f820020480c4e0dc,3),(0x3fffc0003fffc0003fffc0003fffc0000000000094000000061300094000032550505050505050e1f018ffdc212073e01380000003fffc03ff87c06000708481cf804e0,3),(0x3fffffffc00000003fffffffc00000003e38e025000a00a0ca0c9400003284c0a0a0a0a0a0a0a0fe0fff011fc1c07c001c00000003fffffc03f80000047f0701f000700,3),(0x3fffffffffffffffc0000000000000000000000e3a000000002532832800094cc0c0c0c0c0c0c0ffffe0fe200e038003e003fffffc00000000003f83f880380e000f800,3)]
def xt13:=[(tv6,0),(tv7,0),(tv8,3),(tv9,3),(tv10,3),(tv11,3),(tv12,3)]
def c13:Cfg:=⟨142,284,374,410,mk73,0x3ffffffffffffaba3ffb3ffa3bbb3aba071c71c71c71c71c71c71c71c71c71c7fffffffffffffffffffffffffffffffffffc00000000000000000000000000000000000,mk74,mk75,mk76,mk77,mk78,mk17,mk79,mk18,mk19⟩
def N13:Nat->Nat
 | 6=>1
 | 7=>7
 | 8=>67
 | 9=>19
 | 10=>1
 | _=>0
def L13:Nat->Nat
 | 6=>0
 | 7=>3
 | 8=>7
 | 9=>5
 | 10=>0
 | _=>0
def H13:Nat->Nat
 | 6=>0xfc41e9
 | 7=>0xd3826cd24293c422208fd01167d39b2d95d5297c53
 | 8=>0xfff01af85b54f7291af5760cf44d7ff37491f274bbf137a8eda210e64aede084dfde827ed99244d73462d24293cd7bedcccbefc206bfc1bcd7bfaf1bb4670eb464fbb1a43cadf40cad6a66acd8369f17119c86009966ff97476c954d4d92c7fb91c53e8b9aaf88d1e584d25a7ce53474744b72da52721b1271003170988d6c79e06a29a164be0c63bf88605d215dd15a59201f5904db56ba4c5699414d308449ee09326c072c3e042c29ff213d4c1a758f190ed318a4a814d6ad1447ca13ed5b0d89c30d4d8506dddc
 | 9=>0xff214ef37491e084dfdeccc1de3065d36537d24293a668d69c4f27947e81814d0564466556ba4c4ad4c44a767727e90f2227c11a758f14d6ad
 | 10=>0xd24293
 | _=>0
def P13:Nat->Nat
 | 6=>0x49d
 | 7=>0x5851000000000000fccd000040510000a43d0000188200004099
 | 8=>0x48a20000246200002482000040aa00001c82000030b40000383e0000209a00001caa000018010000307400002c3e0000484a0000445600000000000038d200002cd200000052000048ca0000285600003c7200000cca0000287a0000189b000038ca00003c6200001c9a0000403e0000007a00004862000040d2000000010000183b000028da00001c3e000044da00003c3e000028a20000443e0000404a00003c4a000020d2000044cd0000483e0000283e0000009a000040010000487200002c56000040820000302800001c6200003c9a000028ca0000203e0000243e00000035000040620000300100001cd200004075000030240000185300000042000040ca0000183900004401
 | 9=>0x3c000000b4000000740000002c0000008c0000000700000000000000840000004c0000009c0000006c0000005400000028000000050000000b00000002000000c40000000100000024
 | 10=>0x0
 | _=>0
def tg13:Fin 7->Nat | 0=>0 | 1=>0 | 2=>3 | 3=>3 | 4=>3 | 5=>3 | 6=>3
def g13:=[sw23,sw24,sw28]
lemma b13_ok:(List.range 11).all (fun s=>span ((bar c13 (findAut2 c13.shTT mk0 g13 (Rgen a1t7 10 xt13 P13) N13 L13 H13) (Rgen c13.all1v 10 x13 P13)) s) (N13 s) 0)=true:=by decide +kernel
lemma lb13:∀ t,HasCircuitSize 7 f13 t->11<=t:=prove_base2 f13 r13 mk0 c13 tg13 x13 xt13 g13 [(5,6),(3,4),(0,1)] N13 L13 H13 P13 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (span_all_sound b13_ok) (checkTags_sound bsT2 hT2 f13 E13 tg13 [.emp,.emp,.base 6 [0,1,0,2,3,4,5],.f0 5 (.b2 6 (.f0 4 (.base 2 [0,1,2])) (.f0 4 (.base 2 [0,1,2]))),.f0 6 (.b2 5 (.f0 3 (.base 2 [0,1,2])) (.f0 3 (.base 2 [0,1,2]))),.f0 3 (.b2 6 (.f0 4 (.base 2 [0,1,2])) (.f0 4 (.base 2 [0,1,2]))),.f0 4 (.b2 5 (.f0 3 (.base 2 [0,1,2])) (.f0 3 (.base 2 [0,1,2])))] (by decide +kernel) (by decide))
def E14:List (Fin 7×Fin 7):=[(0,1),(0,2),(0,3),(1,2),(3,4),(4,5),(4,6),(5,6)]
def f14:BFn 7:=fun x => (x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 2)||(x 3&&x 4)||(x 4&&x 5)||(x 4&&x 6)||(x 5&&x 6)
def r14:=0x80410606141012858a830808895261880842c549844052060a0d20144181851804a180a2490128182832804906061509083828300808085061880842c0498140491a062705060603090a0f05060603090a0f05060603090a0f05060603090a0f05060603090a0f05060603090a0f05060603090a0f05060603090a0f05060603090a0f66ad193161c152951a1b3568c98b0e068c98b0b96ac54a54683c74e1a3262c0e1a312549c3464c099d1a2ae4c94b151c182ce8d0d726465898e0c0e6cb93161ad56a52a32a4c68b12141cc993264c993264a952a54a952a54183060c183060ac58b162c58b162a54a952a54a952142850a142850942850a142850a1224489122448911224489122448ac54a12224280a12224264a911214180509112132548890a0c058a9424448500c14220a12848890032a1415489092222810199120ac4884a1118100cc952224258a9424445090c1420202
def x14:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa4d338e4d34d34e838a4c1c1c1c1c1c1c1c1c1c110220408652524a7fffe0001fe0001fe0001fe088110204329292520000,0),(0xcccccccccccccccccccccccccccccccc3a54c094e0253804c0b824242424242424242522244489108dadffd295201fe0001fe0001fe00911222448846d600094a9,3),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f094e9403a5a8e9409400028282828282828282a44488912210fffb5a52a5fe0001fe0001fe000122244489108000dad2952,3),(0xff00ff00ff00ff00ff00ff00ff00ff000000130009400000139450505050505050505380700e1c3ff9092139c39fffe01fffe00000001c038070e1c0484909ce1c,1),(0xffff0000ffff0000ffff0000ffff000000e3a5000328a1302531c1c1c1c1c1c1c1c1c00780fffff9e03006000c0000000000001fffffe03c0780000f0180300060,0),(0xffffffff00000000ffffffff0000000000000ea2800002500c02828282828282828283f87ff01fc201c03801f00000001fffffe000001fc00000fe100e01c00f80,3),(0xffffffffffffffff000000000000000000000000000000e00003030303030303030303ffff0fe0040e01c03e001fffffe000000000000003f87f0020700e01f000,3)]
def xt14:=[(tv6,0),(tv7,3),(tv8,3),(tv9,1),(tv10,0),(tv11,3),(tv12,3)]
def c14:Cfg:=⟨157,314,368,392,mk80,0xffffffffffffeae8ffffeae8ffe8eae81c71c71c71c71c71c71fffffffffffffffffffffffffffffffffffffffe000000000000000000000000000000000000000,mk81,mk26,mk27,mk28,mk29,mk82,mk83,mk84,mk85⟩
def N14:Nat->Nat
 | 7=>3
 | 8=>21
 | 9=>10
 | 10=>1
 | _=>0
def L14:Nat->Nat
 | 7=>2
 | 8=>5
 | 9=>4
 | 10=>0
 | _=>0
def H14:Nat->Nat
 | 7=>0xac40209f96b27be80a
 | 8=>0xe741eee585acdd89acd1cde6c955f0c7820eb43dd5ae502dabafb48868757be80a6694506246b54b876a3fc5e93e757436318b3082412df76a20b91420b6c1
 | 9=>0xd1cde6c9e349c955f0b43dd57be80a6246b53082411f97a01d6e5b01709c
 | 10=>0x7be80a
 | _=>0
def P14:Nat->Nat
 | 7=>0x8034410080342d00000000
 | 8=>0x8000a20000083a000000010000142400801474010024010000147c00802442010018d200801c9e0000000000801cd20080140102001c4a0000183e0000049a0000043e010014030180244a000024720000249a
 | 9=>0x2400800002008000740000007c000000000080000101000003000000580000003400000054
 | 10=>0x0
 | _=>0
def tg14:Fin 7->Nat | 0=>0 | 1=>3 | 2=>3 | 3=>1 | 4=>0 | 5=>3 | 6=>3
def gs14:=[[sw23],[sw25],[sw35,sw36,sw37]]
def au14:Nat->List (Nat×Nat×Nat×Nat)
 | 0=>[]
 | 1=>[sw35,sw36,sw37]
 | 2=>[sw33,sw38,sw37]
 | 3=>[sw25]
 | 4=>[sw23]
 | _=>[]
def ap14:List (List (Nat×Nat)):=[[],[(2,6),(1,5),(0,4)],[(2,5),(1,6),(0,4)],[(1,2)],[(5,6)]]
lemma b14_ok:(List.range 11).all (fun s=>span ((bar c14 (findAutGen c14.shTT mk0 gs14 au14 (Rgen a1t7 10 xt14 P14) N14 L14 H14 P14) (Rgen c14.all1v 10 x14 P14)) s) (N14 s) 0)=true:=by decide +kernel
lemma lb14:∀ t,HasCircuitSize 7 f14 t->11<=t:=prove_baseGen f14 r14 mk0 c14 tg14 x14 xt14 gs14 [[(5,6)],[(1,2)],[(2,6),(1,5),(0,4)]] au14 ap14 N14 L14 H14 P14 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 5<=i from hi) with ⟨k,rfl⟩;rw [nAC];rfl) (by decide +kernel) (span_all_sound b14_ok) (checkTags_sound bsT2 hT2 f14 E14 tg14 [.emp,.f0 2 (.b2 0 (.f0 3 (.base 2 [0,0,0,0,0,1,2])) (.f0 3 (.base 2 [0,0,0,0,0,1,2]))),.f0 1 (.b2 0 (.f0 3 (.base 2 [0,0,0,0,0,1,2])) (.f0 3 (.base 2 [0,0,0,0,0,1,2]))),.base 7 [0,1,2,0,3,4,5],.emp,.f0 6 (.b2 4 (.f0 3 (.base 2 [0,1,2])) (.f0 3 (.base 2 [0,1,2]))),.f0 5 (.b2 4 (.f0 3 (.base 2 [0,1,2])) (.f0 3 (.base 2 [0,1,2])))] (by decide +kernel) (by decide))
def E15:List (Fin 7×Fin 7):=[(0,1),(0,2),(0,3),(1,4),(2,5),(3,6),(4,5),(4,6)]
def f15:BFn 7:=fun x => (x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 4)||(x 2&&x 5)||(x 3&&x 6)||(x 4&&x 5)||(x 4&&x 6)
def r15:=0x28190b1465900422c4aa4508716ac6a50100c98b302208a120a0d00422c0aa40c04a160a0c2015090485890712406145013048483404225048c088242c019280208d013214181c9093040108b10a91421c5201898850748254283090909090a0e83090909090a0e83090909090a0e83090909090a0e83090909090a0e83090909090a0e83090909090a0f568b962a51a13a64a919b23c70d18b05cb1324e5c7856a94a8d074e19316078d1625ab4e89d3254990a4c89cd972455cb132548542e3868cf1a2c4c903c71e2c356a519d325478d1624385078b162c58b162c5870e1c3870e1c31a3468d1a3468ca952a54a952a5470e1c3870e1c38448912244891223870e1c3870e1ca941c30508901c305088d10e18284480e1818262c382344850602a50890a01c28302c587046890a0c042440e2c3820aa50890a022070c14270c1422400e28d1212a5088e18283860a1018202
def x15:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa38e4c08ca4d34d302a280393001c1c1c1c1c1c1c100204210217517c5ffff807f8000007f80020040842042ea2f8a0000,0),(0xcccccccccccccccccccccccccccccccc4c038e5409402a501300a00a28242424242424260540a94a7ca08a1ffda2aff807fff80007fc0a815294f94114001b455,3),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0c5300e293ba594028000c4c0e048484848484848a674f18050c0ffe28617300007f807f807f94ce9e300a18000050c2e6,3),(0xff00ff00ff00ff00ff00ff00ff00ff0000094000000a02a0004f80253090909090909093c798c00c67ff0c0300dbc0000007fff807ff8f318018c000180601b78,3),(0xffff0000ffff0000ffff0000ffff000094e013b0e30000c5653133004f23232323232320f81f0ffff8020043e01c0000000007fff801f03e000000040087c0380,0),(0xffffffff00000000ffffffff000000003a5fe502500c3008cc0259780141414141414143007ffe0f8704ef9408e007fff807f800000600001c1f0e09df2811c00,3),(0xffffffffffffffff0000000000000000000380000000e0030094000c9682828282828283ffe00ff007f8f0180f0007fffff80000000000c01fe00ff1e0301e000,3)]
def xt15:=[(tv6,0),(tv7,3),(tv8,3),(tv9,3),(tv10,0),(tv11,3),(tv12,3)]
def c15:Cfg:=⟨143,286,364,388,mk86,0xfffffff8ffffffa8fffffaf8eeecaaa81c71c71c71c71c71c71c71c71ffffffffffffffffffffffffffffffffffff800000000000000000000000000000000000,mk59,mk31,mk87,mk88,mk89,mk82,mk83,mk84,mk85⟩
def N15:Nat->Nat
 | 7=>3
 | 8=>46
 | 9=>14
 | 10=>1
 | _=>0
def L15:Nat->Nat
 | 7=>2
 | 8=>6
 | 9=>4
 | 10=>0
 | _=>0
def H15:Nat->Nat
 | 7=>0xf8b05d3512280340e8
 | 8=>0xf8b05df4b9e9e9200ad34600ce5998c6ab4bc36a01bfdf73b661f1b2f9deb00648afb019abda9eaabfbda981dba4ea119d7f149a36ae955a9490a5df8b2bd6875a0086caeb7f72a57f07bb7e38ef739e4e7150cf71428e5a51ff5341cd48458347ab1645ec3743380540e35933f78d3183b81e9da51aef0c1282b009d00806f2a9060957053a8b04f048
 | 9=>0xf8b05dccd6a0c2bcf1b8f1879c5ff39a36ae7e38ef71428e4e96394e56d940e3591b149506f2a9053a8b
 | 10=>0xf8b05d
 | _=>0
def P15:Nat->Nat
 | 7=>0x645100003855
 | 8=>0x2c7600002cd200000062000000720000147a000004da000020760000089a0000203e0000049e000010760000044a0000004a000004c40000144a0000149a00003434000014760000083e00002c3e000020a2000004010000048200001ca2000034540000009a000010720000340500001c010000205200001c9400000462000024520000045500003401000004ca0000280500002c9a000020d2000000ca0000143a00003474000000a20000342c0000303e
 | 9=>0x840000004c0000000300000058000000340000005400000005000000240000000200000001000000ac000000740000002c
 | 10=>0x0
 | _=>0
def tg15:Fin 7->Nat | 0=>0 | 1=>3 | 2=>3 | 3=>3 | 4=>0 | 5=>3 | 6=>3
def g15_0:=[sw23,sw27]
def g15_1:=[sw29,sw33,sw37]
def gs15:=[g15_0,g15_1]
def pa15:=[g15_0,g15_1,g15_0]
lemma b15_ok:(List.range 11).all (fun s=>span ((bar c15 (findAutPath c15.shTT mk0 pa15 (Rgen a1t7 10 xt15 P15) N15 L15 H15) (Rgen c15.all1v 10 x15 P15)) s) (N15 s) 0)=true:=by decide +kernel
lemma lb15:∀ t,HasCircuitSize 7 f15 t->11<=t:=prove_basePath f15 r15 mk0 c15 tg15 x15 xt15 gs15 pa15 [[(5,6),(2,3)],[(3,6),(2,5),(0,4)]] N15 L15 H15 P15 rfl (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (span_all_sound b15_ok) (checkTags_sound bsT2 hT2 f15 E15 tg15 [.emp,.base 6 [0,0,1,2,5,3,4],.f0 5 (.base 3 [0,1,0,4,2,0,3]),.f0 6 (.base 3 [0,1,4,0,2,3]),.emp,.f0 2 (.base 3 [0,1,0,4,2,0,3]),.f0 3 (.base 3 [0,1,4,0,2,3])] (by decide +kernel) (by decide))
def E16:List (Fin 7×Fin 7):=[(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(3,4),(5,6)]
def f16:BFn 7:=fun x => (x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 0&&x 4)||(x 0&&x 5)||(x 0&&x 6)||(x 1&&x 2)||(x 3&&x 4)||(x 5&&x 6)
def r16:=0x80491606148011870491040460e1a0c201449918544892050a0c50a18142830806146861408124448832020091126020202141862004418124602003050e020054213044a01241818588061410c14401206088928046180a446019504305a406518064590154601918806106061520164443055406560068650155801c1202009112609019504c1180800c143830180d0509112141e0301a0a12224283c06034142444850780c0682848890a0f0180d0509112141e0301a0a12224283c06034142444850780c0682848890a0f0180dd3970d9ab464c5820f4e5c366ad1931604372d5878e9c1c34608dcb561e3a7070d18135a7466cb93161c182d69d19b2e4c5870607569d19b2e4c58705ab362b55a94a8d095264468b12141d4a952a54a952a54a54a952a54a952a53264c993264c993254a952a54a952a53468d1a3468d1a3464c993264c993264b162c58b162c58b152a54a952a54a95010205a3260b15284889001a94a84c9522242800664a90b15281828401a94a83464c0a12200694a84c95222428101a9322345890a0c0806a52a132548890a03464c162a5091120284880c1420202
def x16:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa4d34d31c74f738e4ce5535534d54d34d54d3395387e3f1f8fc7e3f1f8fc002008020080200ffffffe000000000000000001c010040100401004000000,0),(0xcccccccccccccccccccccccccccccccc38094ec7138901300000e28000aaaa38aaaa02800824120904824120904a4892248927fdffa49249200ff803fe00ff803fe12449124493fe001249249,3),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f094c3a538e9400250000258c0aa300096300000000844221108844221108c9124491247ffff4924925ff007fc01ff007fc002489224892000ffa492492,3),(0xff00ff00ff00ff00ff00ff00ff00ff0000e3800380004c038028002532830c000a284ca010884422110884422110e0387fdffa48920e0703800007fffe00007fffe0701c3fe0012449070381c,3),(0xffff0000ffff0000ffff0000ffff000032500000000e9409408e800e94096500c00096301108844221108844221701c07ffff4912470381c1ffff80001ffff80000380e0000ffa4892381c0e0,3),(0xffffffff00000000ffffffff0000000000000ee0000000001330000000002802894c0004e2110884422110884427fdff8e0380e038003fe00000000001ffffffffe3fe000701c0701c001ff00,3),(0xffffffffffffffff0000000000000000000000000380000025000b0000ca00a0032500c964120904824120904827ffff701c0701c07fc0001ffffffffe000000000000ffb80e0380e03fe0000,3)]
def xt16:=[(tv6,0),(tv7,3),(tv8,3),(tv9,3),(tv10,3),(tv11,3),(tv12,3)]
def c16:Cfg:=⟨161,322,412,484,mk90,0xffffffffffeaeaeaffeaeaeaffeaeae81c71c71c71c71c71c71c71c71c71c71c71c71c71ffffffffffffffffffffffffffffffffffffffffe0000000000000000000000000000000000000000,mk91,mk75,mk76,mk77,mk78,mk41,mk92,mk42,mk43⟩
def N16:Nat->Nat
 | 6=>4
 | 7=>30
 | 8=>83
 | 9=>57
 | 10=>7
 | 11=>1
 | _=>0
def L16:Nat->Nat
 | 6=>2
 | 7=>5
 | 8=>7
 | 9=>6
 | 10=>3
 | 11=>0
 | _=>0
def H16:Nat->Nat
 | 6=>0xe23a82d1ab86771c5933b439
 | 7=>0xf69f5fddde26dc0279db59c9d45c9fcb8f8fc1e6a4b47324acff8e9c2dff97fcd29720a18c2efc85e2ac74efe56dfba76d30806823c35a1dc5581b4e5453ca51ee3d50624037340127be8326aaf22542da2266070df704065fbe
 | 8=>0xfb1ce8f64a97f59c1bf1b211ed067dec1d2be835eee57d55e23343df539ddc481cd7715acf5f56ca579bc6e84bbe5666bce41bba28a0b94f44b6c9cfb2b7a6b16818aa5391a4a40ea491f9a0dda49f0ccf9a368f97fcd29720a193edd49160ed8fbb738e52d48c2efc8b528e89f6ca828dbb8171de7db07a7cf7927b7ca9778de26e5ad96ce52966c001658ece65892961f3315b49775aafd55a1a5c581b4e547fb153709951ee3d516a22508b1e4d25374bbad84930013f43903df07d39b218388c3537578931ee98309df730769f2eea1c2ebc562e63092de4422a50b328544726aaf2247b181b6a841871d80df70409b52709ace70926d7
 | 9=>0xfefccbf990abf8f44ff1b211ef35e5edfc36ed4129ed067decc71dec1d2be7b164df9d46df539ddccaa9dc481cd6a5abd229c6cf5f56c82003c818d1c6e84bc3eebcb842bbb71311b6c9cfa9826da8404ca1a0b4a16154a04ed49f0ccf9c10ef9a368f9720a193edd48e4d6e8af01289f6ca8410a380d9ee7a0a526b640666c00159fd24587f15516a224bbad84930014611d74494c442acf938a6f235397923564e19e5380c704b06aefd
 | 10=>0xed067decc71ddf539db6c9cf9720a14bbad838a6f2
 | 11=>0x9720a1
 | _=>0
def P16:Nat->Nat
 | 6=>0x600582a088068610100582600006839
 | 7=>0x8078260100604100000c42088000750100f4590300103d0100144901000c3102011451038104590581185100000000080118990600783a0300f43d058114710900c043008064490201149901013441018010250200942d00809025040088510580f03e0680685103009c5a040060590001342d04000061
 | 8=>0x983d0000643d0000a4560000145200005c240000c4420300a88c0300242d0480ac9d00005c010300c43d0400385a0000803e0580383e0200807a0400605a0580383d0000bc5a0200387200005c440300242e0300907a0300a84a03007c5a068040390200382e0080c4010000c45205809c51000000000080b0030000d83d0000609a06802c5308009c990300a86c0000c02a0500245201809c010300605700804c3201002c0103007c6a0200902d0080343d0200c4620100dc61030094290300243e0780402901007801060020520100bc410300243d0000cc510200382d0000143e0300bc2f03002c2b00805c030300c44a0700d09a0000d49a05809c53030060550000843d030018550000785203808c0700004c2e0280389a0080cc5d08009c9b0000d4560080cc2906802c510300103d0000dc3d018008610000bc2d05809c2b018060010300a844
 | 9=>0x104400001844000018bc0000005201800c01008018020200046c000008240000080200001842000000940000142c00000801000018540300183d00000c9a0000102400000c3e00000c940100000202000c7a01000405018004070000186c000008440300183f0000183a02000444008014050000004000801801000018940000185200000000008010030000144c00000cbc0000142a0200044c0000103401800c020280048c020018620080043400000c400000003e008008030300184a01000001000000bc00001434000008340000143200000c3c0000185c0000146400000cfc
 | 10=>0x24000000020000000100000044000000000080000300000034
 | 11=>0x0
 | _=>0
def tg16:Fin 7->Nat | 0=>0 | 1=>3 | 2=>3 | 3=>3 | 4=>3 | 5=>3 | 6=>3
def gs16:=[[sw23],[sw24],[sw25],[sw32,sw39],[sw40,sw41]]
def au16:Nat->List (Nat×Nat×Nat×Nat)
 | 0=>[]
 | 1=>[sw33,sw38]
 | 2=>[sw35,sw36]
 | 3=>[sw24,sw33,sw38]
 | 4=>[sw26,sw29,sw33,sw38]
 | 5=>[sw23,sw33,sw38]
 | 6=>[sw25]
 | 7=>[sw24,sw35,sw36]
 | 8=>[sw26,sw29,sw25]
 | 9=>[sw24,sw40,sw41]
 | 10=>[sw24,sw27,sw30]
 | 11=>[sw40,sw41]
 | 12=>[sw32,sw39,sw35,sw36]
 | 13=>[sw26,sw29]
 | 14=>[sw26,sw29,sw27,sw30]
 | 15=>[sw32,sw39,sw33,sw38]
 | 16=>[sw23]
 | 17=>[sw24,sw25]
 | 18=>[sw23,sw32,sw39]
 | _=>[]
def ap16:List (List (Nat×Nat)):=[[],[(2,5),(1,6)],[(2,6),(1,5)],[(3,4),(2,5),(1,6)],[(4,5),(3,6),(2,5),(1,6)],[(5,6),(2,5),(1,6)],[(1,2)],[(3,4),(2,6),(1,5)],[(4,5),(3,6),(1,2)],[(3,4),(2,4),(1,3)],[(3,4),(2,3),(1,4)],[(2,4),(1,3)],[(4,6),(3,5),(2,6),(1,5)],[(4,5),(3,6)],[(4,5),(3,6),(2,3),(1,4)],[(4,6),(3,5),(2,5),(1,6)],[(5,6)],[(3,4),(1,2)],[(5,6),(4,6),(3,5)]]
lemma b16_ok:(List.range 12).all (fun s=>span ((bar c16 (findAutGen c16.shTT mk0 gs16 au16 (Rgen a1t7 11 xt16 P16) N16 L16 H16 P16) (Rgen c16.all1v 11 x16 P16)) s) (N16 s) 0)=true:=by decide +kernel
lemma lb16:∀ t,HasCircuitSize 7 f16 t->12<=t:=prove_baseGen f16 r16 mk0 c16 tg16 x16 xt16 gs16 [[(5,6)],[(3,4)],[(1,2)],[(4,6),(3,5)],[(2,4),(1,3)]] au16 ap16 N16 L16 H16 P16 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 19<=i from hi) with ⟨k,rfl⟩;rw [nAC];rfl) (by decide +kernel) (span_all_sound b16_ok) (checkTags_sound bsT2 hT2 f16 E16 tg16 [.emp,.f0 2 (.base 4 [0,0,0,1,2,3,4]),.f0 1 (.base 4 [0,0,0,1,2,3,4]),.f0 4 (.base 4 [0,1,2,0,0,3,4]),.f0 3 (.base 4 [0,1,2,0,0,3,4]),.f0 6 (.base 4 [0,1,2,3,4]),.f0 5 (.base 4 [0,1,2,3,4])] (by decide +kernel) (by decide))
def E17:List (Fin 7×Fin 7):=[(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(1,6),(3,4),(5,6)]
def f17:BFn 7:=fun x => (x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 0&&x 4)||(x 1&&x 2)||(x 1&&x 5)||(x 1&&x 6)||(x 3&&x 4)||(x 5&&x 6)
def r17:=0x4012060889608543852c420114385850808085061a020050916060a10b152e0a012444305420a0e006892024214186240451812464025181142500a4608489801506049182090e007088080244498880a08506194216060889808014245806011424305c0621220c444850780c4244188890a0f018848831112141e031091062224283c0621220c444850780c4244188890a0f018848831112141e031091062224283e9c3668c987052950ba70d9a3261c0c9522b9628bc70c4e1a3046e5892f1c293868c098a94b0e0c16b529d2a34384d992e54991a22c38303ab466c98ad58ad5294a9322345890a0ea54a952a54a952a4c993264c993264c83060c183060c182d1a3468d1a3468d162c58b162c58b162142850a142850a124489122448912242850a142850a1429a3058a12214048502a9426488906012140a64882b14211828401a9420b46084a1220060a12428101a942648890603460b14244280a0c0806a50992223460b1424284880c1420202
def x17:=[(0x2aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa934d3380395a8e4c0013a8e3930150783c1e0f0783c1e0f0401024491c41021ffffc0000ff80001ff0000010040912471040840000,0),(0x333333333333333333333333333333330000e4ce00a4d3a134c04c04c038a389c4e271389c4e27101c07010043bffff001240000000000000ffffc0701c04010e000000049,0),(0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c00025940023025000000000940023090482412090482412a82a092248fea54ead64bffff007fffe0000002a0a82489200a953ab592,1),(0x3fc03fc03fc03fc03fc03fc03fc03fc02538e0004c00003a8a0e01302502c422110884422110884308c2dbbff10c1843187001ff00003fe00007fcc230b6e000430610c61c,3),(0x3fffc0003fffc0003fffc0003fffc0000e94000096c00094002502500e000442211088442211088c1304fff6e230608c6383fe00007fc0000ff80304c1000db88c182318e0,3),(0x3fffffffc00000003fffffffc000000000fc0013fc096800e9683000384c0904824120904824120fe3ff1c0704007f007c000000007ffffff00003f8000701c1001fc01f00,3),(0x3fffffffffffffffc00000000000000000000025000300025380940a00940a05028140a05028140ffff8e038083f800f8003ffffff80000000000000fe380e020fe003e000,3)]
def xt17:=[(tv6,0),(tv7,0),(tv8,1),(tv9,3),(tv10,3),(tv11,3),(tv12,3)]
def c17:Cfg:=⟨154,308,386,422,mk93,0x3ffffffffffbbbbb3ffbbbbb3ffababa071c71c71c71c71c71c71c71c71c7ffffffffffffffffffffffffffffffffffffffc00000000000000000000000000000000000000,mk94,mk31,mk87,mk88,mk89,mk17,mk79,mk18,mk19⟩
def N17:Nat->Nat
 | 6=>1
 | 7=>22
 | 8=>150
 | 9=>118
 | 10=>10
 | 11=>1
 | _=>0
def L17:Nat->Nat
 | 6=>0
 | 7=>5
 | 8=>8
 | 9=>7
 | 10=>4
 | 11=>0
 | _=>0
def H17:Nat->Nat
 | 6=>0xfe6ca4
 | 7=>0xf34f09ede643e13e8fdf7df8c6c8f4b90e4aa7c723a3af8a95cbd78ede908d6e9a78d09c4c000449c339460eb043fea32825b0212d581b1b5c1192700e70ff009426
 | 8=>0xff1cdffe5ad8fdda50f8f832f76961f6db80efdc38ed8c62ed1f81e9adc8e5ed05e4bc5ee485b3de75c9dd8aa1dd3b9cd3fa0ad217d8d06dabd01d73ceee53cde00ecd16a4cb3bb7cad2a5ca8e1cc94d9fc62ca7c5eb99c468b2c425e5c21e8dbfb62bbdc0bbb90e4aaeec42ae0d81a73515a66d49a60e0aa5db2da464a1a1a59da13d3ca0d225a0618f9d8cab9ad392960f4f960a2995dc63951bd695044f94bfc393333091c53e8f7ea78e2c048d6e9a88728e863af9856c498101928062ef8033177f62c97f4aa07ed93d7ea8117bf56a7b40c977d0d376e33574f56771bbe4710f1b70d5346ec5b56d50d16b76f0671fe066f3c1645cf4644a2f635bdc6117626005445d6aa45cbc285c337d5acc585990815822c557820156368355b25a5426405338374fe19f4c31494965c1477739460eb0419255418c553e712b3d86033d29ba3c88d83a99223a806b3a2c403941183840ba383829367f633678f735a826343deb3417eb339d5c31c4983177a82f14662eac422e62642bf052259aca24042822f0a42155df1de9dc1d804219dc481941d6189e4d16ec9215110c11927010a41d10810c0cc5150bc6090bb2060834e804d059044ecd019bdb01569c00cd0f
 | 9=>0xf47c21f30b62f0d9d1ef9260ed8c62eb30b0eaa960e8ff1fe8c1e8e6d02ed89e43d68772d23d62d217d8d074fdd05282cfe8e8cde954cde00eca8e1cc6e577c648dfc62ca7c3fb16c2e8e4c21e8dc09ce2c083a6bf9f22b9f0abb90e4ab69706b42f5dac7d2baafdaaaa1283a6de49a26195a1f7fb9d2137962caf960a2991c53e9128ea9113698fe1798f7ea78e56598c90e98af8798a765b894e3888728e85088f8105457ed93d7dceb77cf6c278ed5c76ad4e730588728c7b71bbe470a19b7038016dcf0a69a7b4686e05648140644a2f637534607df660145c5fe91054268a4cb3774aa4604872cf45149b43eab6428aa03e712b3e608b3d86033d29ba3840ba367f633678f7339d5c32d8f032b48a32199c31c4983087852c2c282c0ccc281c76259aca1de9dc1d80421d45db19a192197e9e18e46614abf213e0441354a111927010a41d1082100e5fa30d4d85068f3004d0590330fc02467001569c00cd0f
 | 10=>0xc62ca7c3fb16c09ce2960a29644a2f54268a3e712b1de9dc1d8042119270
 | 11=>0x119270
 | _=>0
def P17:Nat->Nat
 | 6=>0x801826
 | 7=>0x2808871020080cd010234250001c43d00804041010190510101bc2d0080a04900006c5100008c3e0081744100816c3a01016c260080bc420081742d0080bc3101006c71010170590300d061000000000100244900817c59
 | 8=>0x807cc901015c2401015c0101807c01018080320000049a0080dc010100900100819c6103018c7202815c840300743e0080002d03015c5c020088a30000dc73000084320000ac0100001801000070990300742e0100904a0101487900014875008168560081782e0180dc9b010028070081909a0380007a0081983d0080903e0080a0510301346a010130510000dc510300fc610000543d010078d200813801008104ca0080e43d008114a50101b89d00807ccb0001003d0101c03d00807c5101007029000028280281046a0301749d02807c730080887b00811c5a0001303b0080907a008010a200811c410000909a00807c2b0100380b0080849a0080e8560100f82d0000dc530101c43e010048d2010110cd0301049d0000345103018c7a0200cc3e0000182800016c3e0000203d00015c2800005c3d0080d03d0100a0710081889a0280f4a2020104a200802801010128cd010150070081b43900000c3d008104560300048a00005057008000ca00006056010070a5010104010001902e0300f47a0300fc9d0001ac5100013c3d0300742d0200785a00811c2d00818836010108750000283c010130530081782a00807c5300019c3d00009c3d0000184401012c5b0081789a0300244a00804c3e01804c820300248c0001389a01000401030090820000483e00018c3e0100c8290000505203009429010080cd0001300100018c3d0001b03d00014859008028740000288c0300dc2b0001702e018080010180789a0281d429000000000300907501011c2f0000dc710101b451010190320300f8d200804cd20101b4990000008a0000ac520080aca2
 | 9=>0x200040202802484008020ac0080202c01000c010100245c0080209c0080205c0080203600000cc4000010380080143c008020640000100100000c7c008020a4008020bc0000205201000c4a0080202e00800874008008f401000007008000020000185c00800c3e0000006c00801c010080084000801404010018510000043c0080146c0000140300000c3c0000180200802032008018a4000018bc00000c7203000c77000000280000183b0080147c00001c400080142400800c7a00000cfc00800c40008014740080083c0080205a00000c9a00000c8c0000105c010004d2000018520080203000001037008008ca008020fc0080144400001c3e008020a20080148c008008c40200040101800802008008d40080000100000cb4008010a4000010bc000004400000002400000ca40100243800802038000018940000105400801c020000003c00802409010018530080202a0080209a0080083e0180088203000c8201000c020200240b00000c9c0000043e00001c9a0000088c00801c56000004fc00001801008000740000008c008014280000200601800801010014070000100200802094008014c40000000003000c7500001cfc0180140b0000183900802034008008d2000010940000185400001052008010a2
 | 10=>0x1000007008000020000006c0000002800800001000000240000003c008000740000008c00000000
 | 11=>0x0
 | _=>0
def tg17:Fin 7->Nat | 0=>0 | 1=>0 | 2=>1 | 3=>3 | 4=>3 | 5=>3 | 6=>3
def gs17:=[[sw23],[sw24],[sw32,sw39,sw28]]
def au17:Nat->List (Nat×Nat×Nat×Nat)
 | 0=>[]
 | 1=>[sw32,sw39,sw28]
 | 2=>[sw26,sw29,sw28]
 | 3=>[sw23]
 | 4=>[sw23,sw24]
 | 5=>[sw23,sw26,sw29,sw28]
 | 6=>[sw24]
 | 7=>[sw23,sw32,sw39,sw28]
 | _=>[]
def ap17:List (List (Nat×Nat)):=[[],[(4,6),(3,5),(0,1)],[(4,5),(3,6),(0,1)],[(5,6)],[(5,6),(3,4)],[(5,6),(4,5),(3,6),(0,1)],[(3,4)],[(5,6),(4,6),(3,5),(0,1)]]
lemma b17_ok:(List.range 12).all (fun s=>span ((bar c17 (findAutGen c17.shTT mk0 gs17 au17 (Rgen a1t7 11 xt17 P17) N17 L17 H17 P17) (Rgen c17.all1v 11 x17 P17)) s) (N17 s) 0)=true:=by decide +kernel
lemma lb17:∀ t,HasCircuitSize 7 f17 t->12<=t:=prove_baseGen f17 r17 mk0 c17 tg17 x17 xt17 gs17 [[(5,6)],[(3,4)],[(4,6),(3,5),(0,1)]] au17 ap17 N17 L17 H17 P17 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun i hi=>by rcases Nat.exists_eq_add_of_le (show 8<=i from hi) with ⟨k,rfl⟩;rw [nAC];rfl) (by decide +kernel) (span_all_sound b17_ok) (checkTags_sound bsT2 hT2 f17 E17 tg17 [.emp,.emp,.base 0 [0,3,0,1,2,4,5],.f0 4 (.base 4 [1,0,2,0,0,3,4]),.f0 3 (.base 4 [1,0,2,0,0,3,4]),.f0 6 (.base 4 [0,1,2,3,4]),.f0 5 (.base 4 [0,1,2,3,4])] (by decide +kernel) (by decide))
def E18:List (Fin 7×Fin 7):=[(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(3,6),(5,6)]
def f18:BFn 7:=fun x => (x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 0&&x 4)||(x 1&&x 2)||(x 1&&x 5)||(x 3&&x 4)||(x 3&&x 6)||(x 5&&x 6)
def r18:=0x8080850619812a9d233204062468a0c10150a9483608543852c542160e18a9400a2648c882012458985808054a558182842c54b814046060a0d08c686028942105180614a01244430585062060a0c1011824303480a2600c886011424305202009112618215060491a0218603120501246018982210e013206012860289824aa060a0e2428214186420a0e00688901146819150858182225a0158602918080548458224184181858821a603121802a98032260a10911263048308831112141e090611062224283c120c220c44485078241844188890a0f048308831112141e090611062224283c120c220c4448507d386cd1930e0992a474e5c3262c38192a4545e386270d182372d58992a4c878e149c34604d68d152961c182d68d0db325ca9323445870607569d18b0dab15aa5295264468b12141d4a952a54a952a54a54a952a54a952a5060c183060c18305a3468d1a3468d1a2c58b162c58b162c42850a142850a1422850a142850a1429a3058a12214030508a94a8448506012140a0ac508460a1006a52a11214180d18212848801a50a0a12428101a9120b460b14244280a0c0806a52a11213460b1424284880c1420202
def x18:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa3804d34d301300e4e38d54d5015393013a938cea934d3013000381e0f0783c1e0f078200848822262410ffffe00007fc0000ff80010042441113120840000,0),(0xcccccccccccccccccccccccccccccccc4d39650004ce38094028a9634ca00002a0005534ee00028e013006231188c4623118804938224099dfffa409200ff8000000007fc0249c11204ce00012049,0),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f094e3800003a500039a46338aaa300000002a3a500002a025a0a0024120904824120954920244891ffaa74ab25ff00003ffff00002a49012244800d53a5592,3),(0xff00ff00ff00ff00ff00ff00ff00ff0000000e3a5000393a1530000c02c4ce4e54e500000c94c3004c04d88c46231188c46218e01377ffe080c200c38000000001ff007fcc7009b8000040610061c,0),(0xffff0000ffff0000ffff0000ffff000003d00094e00e02500c12c000000965a8c00c6000253a50002a894904824120904824601c27ff0dd11304731c1ffff803fe000000300e100386e88982398e0,3),(0xffffffff00000000ffffffff0000000002500efff9404ff028800000940038300300000940e284c0325e24120904824120907f1ffb800e0203f803e000000003ffffff803f8001c0070101fc01f00,3),(0xffffffffffffffff000000000000000000e380000380940000000e00300000940940a3830000097894c030180c06030180c07fffc407f01c1c007c001ffffffc00000000000fe203f80e0e003e000,3)]
def xt18:=[(tv6,0),(tv7,0),(tv8,3),(tv9,0),(tv10,3),(tv11,3),(tv12,3)]
def c18:Cfg:=⟨145,290,440,500,mk95,0xffffffffffeaffe8ffeeeeecffeaeae81c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71ffffffffffffffffffffffffffffffffffffe000000000000000000000000000000000000,mk96,mk97,mk98,mk99,mk100,mk69,mk70,mk71,mk72⟩
def N18:Nat->Nat
 | 6=>6
 | 7=>90
 | 8=>712
 | 9=>446
 | 10=>21
 | 11=>1
 | _=>0
def L18:Nat->Nat
 | 6=>3
 | 7=>7
 | 8=>10
 | 9=>9
 | 10=>5
 | 11=>0
 | _=>0
def H18:Nat->Nat
 | 6=>0xe6c2cfd42454ba0d10920f62604f1b0c412e
 | 7=>0xf946ddea3efee734c5e66fcbe45111dc40dacdcf0acd6985c9d185be4ec5be3bebbc5386b93accb7b954b291d6ad6f72ad3da1aa3a93a0ccff9fe7299cc7139bd3e49a956796d72f9643ff93b362911c2f91082b905f308fd0118ed12a89c31583f2a883dd647f999f7daebc7daad67bda197a025b779c00742965706b5c7057466d8ca16ce44f6caae56a448a69286665b7c56444b660fe8360968c5ec0915ea7075e40895815e554971b54805951691b512b0750990c4e57bd4a2da84765f046a8bf4578f14562b441a8613ba60a3a1c683951493710d72bd68329dac6271ea62628832251b11ea8841d4cf81d4cea1d24861c400216a1561575ab14b98a0f93db0e4ec50d450702db4900a1a2
 | 8=>0xffe6b3ffde37fdc7cffd7b18fd7350fd0772fc75cefc7456fb11fcfa56d7fa4cedfa244cfa0760f8ed98f8d8c2f7262bf710a2f6e720f6b94af69551f5414df51659f50c3ff4b0bdf3c26af394cbf31498f2d91df2d24df2bd9df2b82bf26c97f1b452f19901f0eb1ef08849f06c2bef5d67eec4cfee8799ee6deaee3bd0ee35d0ed97b3ed2648ec7f4eec58a7eb7c0aeac730ea7ddbea5d04ea538dea2f7ee9da91e89bf6e8854ee84c09e7e0b4e7b682e792e0e771f9e760bde74c00e6f6aee6cd30e586f6e5768de52378e40a51e3d00ce3b10de38236e375a3e33ff4e32a28e304d4e2b842e28cf9e287d0e2354ce21575e20bfce16f64e0c166e0b895e01b2edfa8b8df739fde122bde0f53de08c6dd9e7bdd1152dcd481dcbec3dca033dc84d6dc5b38dc4830dc4093dc04dadbe1f8dbc5fcdbbde1db404fdab1d3da095ed9b5d5d9a9efd94342d93b3cd81e40d8030dd80183d7a6f6d74ce7d6a4f8d69659d65de8d57d04d4f856d4cdc9d361d3d34f5ed2642bd24445d21feed09546cfdf17cfbfd5cf9c87cf4b4fcee9cacea561ce936fce8258ce0ec0cdd66fcdc5c8cd5b74cd0840cc7e37cbb40acb5d4ccb4d34cafb45cac619cac00fca7bd6ca45f2c9cc6fc9c494c96443c94590c8c683c7f472c7ef2ac7e964c7de51c7dd75c7cff1c7908fc78ba9c770efc749c1c732a6c6b9edc6a065c58f4ec581b6c4fb08c3ee26c3e5d4c3c223c2f5a9c2e9cfc26dd8c20f61c1c6bac1c686c15224c12fd2c0f004c0380dc01fb4bec142be7405be3bebbdf75ebdb928bdb33bbd30a8bd126cbd051abc6703bc2042bbd2b5bbc3a4bba2d6bb6b21bae28eba84f5ba80cdba2f1aba0541b99447b8f70bb8c547b8b906b86f84b85b81b7bd47b79dd2b7658cb70f01b6fc98b6adf5b62bd1b56ba9b55e11b53cabb47a9ab44c68b3e705b3b254b3316ab329d5b2d6f7b254bbb1e0b9b1dff2b1ce88b1aacbb17b65b0f848affccbaf7eb0af06eaae381eadeac1add0e1ace3d6acd445accfb6acc824ac8961abaf83ab5a8fab2043ab0453aaac54aa83cbaa7360aa17b4a9d5a0a9c09da8b329a880c7a84bdfa8083fa7eff3a7b743a67385a54a83a5005ba48943a4734fa3d86ba3d40ea2dfd6a21c5ca20726a1f6aba1cc24a18967a18817a1427da0d4a3a0af63a0acf8a043d8a02e64a00d0ba004f59ff38a9f87d89f6a149f03b09efdad9dd49f9d45519c8f609c85b39c05d39becf59b848e9b82819b7e119b61159a35dd99f1c799ed64993bb498b79598378397cff497b65b97389c961e06948b7393b39b92ffd492d1ab92ccfb921a239168849091ae90714d90658f8f47dd8f0a418e2efa8e1d438de8c58dc8188db53b8d298b8d13508c99038b79308ad4808a341c887f58887e39883cf188332f87492c87368886dc7286696b862df685dc1085a54b85276b850e5e84e51384ab0f8417d483fda4838eea837749834bdf834a5a83024f82baa0827a6f8264c182246182038181fd028146a580c7c380a3857fce4d7ee1167ec1537eae337e3be17e33a17dc7a77dbe967d980e7d8eb77d01277ce08f7b58557b1a497a3cc079c01f7952b1791d7a78f86778ddcd7863e77835dd77b80a779c00777c2077058876d52e76d50076bc1876b3e075bcb975a31775399574837e73b54f7365c773322673001672e0717248e371cd38713b3b71122d6f53a36ec8086e884f6e4a766dcf266dc4bd6d642d6d21c76bdd186bb6346bac7e6b818a6b628b6ad93d6ac6a86a6bf16a448a69f92f69e04969d12169406069300a68de8c688a826874756849396838bc682d6a67d79a678211677db0673a21673786667e02664125662ad1659c3e6533aa65271f64e0cf6499a16454a663f65463f239637338634301631b7d61b28861891c6135b061236560eebf60b99160b5546059896019b45ff1315f380a5e7c085e4a8e5e30315e146a5da8a75da69a5cf9895c617d5c36735c24f85b41c35b3bd25ab6fc5a83d05a6e8c5a69105a2cdd59a350597d785828b2581e105809c557e15857aa4f57a808579339576f3257408c567c0b56794356316d55fe9c55e98d55a859541063531ba852b78552864a525be9521da151fc1e51d4e551811c50b84e508b9b4fb8e04f52bc4eed594e894f4e7ef14c707a4c66af4bfe9c4b2c334af0954aba7b4a5b7a49f259486926485f1c48506347c1624794f2477fd24769ef45fa124527d445197744a772449a5543ac59439a23437104430d914308ac42b8ca42b3a442573e42506c42000741f9f34179d941693e409c003fdcbc3fce4f3f72a33f42063efa7a3e4ff53e452d3e3e3b3d58ce3ce05f3c28223c25893bdaf73b0a583a747a39f202394d763929dc3906ae37a4a93722ab3647b735ede9353f0334c13c3399bd3375d133303932693c3266cc32355b31f30931d65731ca4531a1a13197c731855731213530d7023051543022792f93652f8cb52f53ad2e722b2e56912e42272dca622d741f2d4b832cdf6e2c3e082c35cd2bfff42bf41b2b0da92acd1a2ac86a2a3edd297e05297c0329558b290bec28e30928439d28049b272a3426bdd426a00226820125c17d25589d253a7024f8b124959e23f86123d46a22e20622858c2211b621c08c21282721061d20cc61209eed209503204d4e2046a31fff141ff5ca1fbe531f28c61ef3cf1dc3341bb6741b9a4a1a3f0619dded19db0319d6b8192a7318f9e9188636182dbd1801a016e9fc16d99e16bb19168ffe1599e1153bc814da9514cf761479001447ca14263614076a12c245122a1d1214f1119faa11898910f3aa0f30030ed8010dce940d4f370d36a40d1f580d1f2b0cb9800ac92c0a39770a294f090370089b5f08549b0832c907c10207af3a0778d1076a64066ee706054c05af6b052aaf04eb5604d34f042b7c0420ab03e63e031a2f02dffe02ad5f0249cf023d5e02062f01f20801c061019ed10165ca0152a400d00500cbe7
 | 9=>0xfff4bfffe6b3ff8b25fed920fe01f8fb4cb9fa2740f9c450f9831bf95ab6f946ddf850fcf7b659f7580cf7262bf710a2f698def59119f5405af51c4af4cf7df49628f384acf366cef31498f0cc38f06c2bf05745f04b6befca22ef6731ef341bef08e4eee26feddc28ed97b3ecda7bebb082eb9e56eb6853eb649feb12a7eb0a06ea6acbea2f7ee9d335e910f0e808aae7b682e71f41e5f34ee5d1bae56de7e519ede3a076e3862be33ff4e2b842e16f64e0ca9fe0adf5e0a023e0752ae01b2ee016dddf826bddf11fddd46bdcbec3dc4093dac91cdab1d3da952ad90865d8f992d8b647d80e3ed71a6bd59039d57d04d5624dd5269fd4f648d4b776d3853dd32f98d2e50ed2c98dd24445d1dbe7d0e833cf921fcc7e37cc7b7ccbd363cb69c9cac619ca7bd6ca2663c9ef56c98cbfc96443c80efac7ef2ac64b0dc5f941c58de1c44af3c3e5d4c30bf3c2e9cfc277e8c1c686c1b842c1556dc089bfbfeddbbfb257bf8f8ebf8441bf1378bf07fcbe49d1be3bebbd6c64bc09d4bb45d5bae788ba9ab8b9691ab952adb94360b8d78db8c547b77cfab77978b73bf5b5f81fb46a47b4185cb3e829b338abb25ee3b0f2a3af0200aeedfbae381ead6d57ab9772ab3925aa7713a96a07a92f08a8ce26a7b743a74085a67bb8a355ffa2f77ca2cda0a216f6a0acf8a06066a043d8a01f5fa000599f28399eca8d9eca569dc0529d02269cfe629c77569c55a89c3bdb9bd9099b7e119b363f9a35dd9a136999ed6499a9cf985a209740d896529795be2395a89a956b6394a3769308c99307de92d3d79298d292622e924cfa8fd0118f8ea68f0b448f04948eba258e2efa8df30e8dc8188dabaa8d89748d02078ae6a089efc489888b89862a8985db894b0889278e88ff2688abbd887f5888332f882b3486915485bd008547be85174c835f2e8330ed82ea6f8243ec81fac5819cf68146a5813a4580c7c37f5e307f01187ee6dd7ec1537ea2cb7dbe967d7b8d7d2ebf7be4d47b41b17b40c57b383d7962367903e978433f77d43e77379776d50075995b736e9573251c7296fb71748370c8a170a4916ec8086e86696d77936d5c846d2d216c5fb36ad93d6a788869bfe268de8c68c06a67d79a67b7ad6737866721ba669a26662ad165b7c56594fb6533aa6517dc6514c163c79562dc6c61b28860d8d85ff1315e40895e146a5cf9895cc9eb5c36735ab2c65a80b75a79cb5926a658b1de58472657c891578b0e570cae56bbfe56768156541556316d559df655697954b87d5409d853e5d85387c4537c3e50f5f050b5334fb8e04f717c4f3dd24e51d44d4fd84d064b4c707a4c56794ba8364afb43490301485f1c47a4ec476769475baa4519774503a544cad4445b7542b3a441478d404f723f8f6f3cc66f3c8af43c2ff73c28223a6fd839d700393a64392c173929dc38e67037b6fe36ce1c366fcf36469f3618dd35f7b3356a5c3357e233054132e07f32653f31a9e2319416318cce30792e3002e12f53ad2f45402ee5372e42272ca2ca2bb83e2bb5e82b72f02ac86a2a3edd29d75829a03d293da628d31f2896b527378725d40e2596d725389b24f1bf24959e23f86123343d2249de2224b3218d21206c952046a31f774d1f35f61f34031d7dd81b8fde1b88391b81ed1ac9921aab471a4b9f1a2b3c1903941848f517c51b16d9e7165cb71599e11575ab14b1331447ca141b2e13e26713531e13159b12f915122639115d7d11019010f3aa0fea5e0fcf120f12510eb0d10e9ee20e21190dc9f60d5a330d36a40b6c390832c9072b84066ee706642d062c9f05a42c053f7c05098f04ef9204d34f04c08f039be103697f02a863019ed101765c00e63600e5af00d005000718
 | 10=>0xe33ff4e0a023cf921fcc7e37cac619be3beb92622e76d50070a4914c707a475baa42b3a436ce1c366fcf33054113e26710f3aa0e2119066ee704d34f00d005
 | 11=>0xbe3beb
 | _=>0
def P18:Nat->Nat
 | 6=>0x689d0001142f00012c390001144200012c710000b49d
 | 7=>0x2ac390006505500057899000854cd000780590003502d0001dccd00010455000a6cc90008ec2d0000000000080099000108cd00082827000a309e0003a055000540590005143a0004b861000a6455000514390003409b0002745500042049000ad8cd0004bc710007e48a0004a45900026c550002ac51000610990005143b0004bcc90001f4750003a471000514230004fc51000800c90005149b0001643d00056c5a0002ec2d000308590007c02d0005145a000370d10002d051000800710002acc90003402b0004a07a000308d100051453000564710002ac710007dccd0003a4990003e05a000370790001b8710004bc99000610c9000578510003405a000514730004fc71000340730001c0d1000610710003f055000370a100096c750003403b000a105900020c6a0001b899000910550002282d0002d48a0001888a000558cd00021c2e000828a20002ac990004945100005c3d0001c0a1000a44cd000b103d00034053
 | 8=>0x4420002d0530000ecc900004ca200042c760004b8a20003743d0006307a0002d04300020c3d0004aca20002fca200028858000250750003987100002862000574560000147a0002849a0002d09a0005cc3d0004ac570004889a0002d0010004d43d0006d45a000600760002290500036c3d0000503d0001b42d000334560000a4540001e00100015c4800052c5d000028da0002949a0006043d000398520002b0bc00031836000564cd0002f8560005d8760001cc51000468a2000668530001c451000504610006bc76000544510001d0cb00046c9a00015cac000014b2000284520005f10100000482000434aa000594cf0002b0580000b03d000288940006f08a0001b87100041c710003647a0001502e0005c476000510cd00054453000594720005087c0002c0010006c83d0001d0730000f83d0004085100014c2d0005050500028472000584aa0004ac01000410ca0005748200023c3d0002b4010004f105000500720000a83e0003642d0005ac3d0003f43d0000949a0003045e000000290004d0d20004e8ca000028ca0003943b0006942b000054720006182900059cca000314620006345a0002c82e00015c440005c4560005583b0002d0710003bc51000034d10004ac8a0001083e0004885a0001582d0000a46000031476000344a30005349a00029432000634d2000384710001d0010005c45a0000a83d00068ca2000694c9000280720006bca20003982b000034710005e08a0003709a0000a4ac0004443d0001082e000364d200060cd2000508740005f8d20001a06a0004d07a0005e0cd0005082c0001a05a0003f03e0000549a0004e8320003d49e000204ca0002b4530001f83d00046c5a000600560001ec3d0006a8c90002d0c90002880100027876000678290005d82e00038c7a000590510000e03d0003e87400059071000590990002a89b000694010000283e0003989b0002509d000314aa0003b43d000160320002d0d2000584820006342d00050052000640560002a43d0002c0da0005e0560006b82e000000000004909e0002d09900069c75000294720004e82e0006b8010006cc01000668510003445e00009cd30004887a00068c9e00037056000410360005442b0006cc480001a0760006743d0002a8510003f0d200015c8c000408c900050c320006383d00014ca20002b42b00053071000284d200008c3d0003006100053099000530c900053c7a00015c3800009c7b00041c990002d06a0004b8760002303d0005d8d20003c90d0001083f0006ccac0001a0560002b4990000483d000408710006bcca000544e20004acda000004ca0003bcc90004accf00029477000434bc0002a873000035010001b8990006a851000630520002c8730002b02c000514d20002b00100064052000490760001607600035c9b00035c01000398760003850100037d050002c07a000588a20003bc7100028c530003d42d000358710004d056000250790004e02d0005d8ca0002a8cb00025055000158720000142e000560e2000398530006b43d0003849900013801000028760001e4d20006cc40000544710001b47a0002283d00014cb20000545a00015076000560010006302e0003982e0003045a0003cc010003046a0002a801000134a200038ca2000314cd0002d04100031401000370ca0001d09b000544730006d1050002403d00015456000398cb000514b20004483d0002d051000590390004708a0006d03d000280520006f0420004e8a20003185200021c5a0004b87a000534cf0002105a000028aa0004d0a200053c9e00006056000150ca0006703d0002d02b0005e83d0000ec3b0005e09e000610d30005843e000594570001b4d20003f0760000a85a000560560001483d0005e4010002c056000544cb0002788a0000a4300004ac760001c89900005c39000464290001a08a000278010003d4a20004e89a00050c2e0001347200022c3d0005d89a00055c390005d82d0002d02e0006cc8c000584d20001d05600045032000668420001082d00000401000514560004682f0002d08a0003988a0001d03b0002fc7a000250cd0006d4560001b48a0003645a000500ca0000ec0100025109000630320002c0cd0003903d000560cd0004d83d0001f43d0001e0520001083d0002e43e0006bc9a0005589b000508a40002c8010005f83e0002803e0005783d0006bc2d0005b10500069105000304aa0000803d00010ccd0002e89d000250a10002bc7600050001000634a2000218560006143e0000d0550006f09a000218760002743d0003cc3b0002b4510001e02b00004c2d000034c900009ca300006c550000045600057905000498760001e05100053c2e0000b0750002ec560005f83d0003cccb0005743e0003987300005c290002803d0002107600040899000584760003ccc9000338e200052c510001e49a0002fc760006803d0005883e0005e0e20002043e000158520000a4580006cc300006f02e0003e88c0002f03d0006b89b000210a20002fc5a0002f8520006689b0002d056000534cd0006cc28000364a20000a8720002603e0000a4010001e43e0000142d0005a43e0001a0010001042d0005844a0003bc9900014c8a0005744a0002fcd2000004720004cc750005f82d00028c010003f8610001e0c900048c76000370b20001385a0001345a0003048a0002703500059452000384c90002510500021cca0003e8010005e432000288280001e05300016829000150320006003e00066c3d000294cf000154d20003989900027c610001200100059477000144350001a055000694cb000630560000843d000488360004a8510000049a0003445b00041c510002785a0001a0b2000508340002b030000408390001e03b000668360006f05a000104d20002189e0003e8ac0003143e000534d20003d4ca000334520001e0cb0005949a00011c3d0002a8710003f0560006088a0001547a00038c560002107a0002d0730001385700038cd20005f029000508280000145a0004b8d20002bc3e0006bc7a0003bc39000424d300028c9b000058610001c4710000cd0d0001e0710001d43d0002b4aa00015c7c0002a82b0002a8b200060c2d000614d20000d03d00038451000218e20002a8c9000610a3000104a20005749a000420cd00031856000544990002002200055c29000294ca0006503d000054d20005345a0002d0cb0006f0410002888c000590c90006305a00039851000594ca000468d20005943f0003e8280004accd000264d20005449b0000146a0003980100004c9e0000044a0001a07a0004e0560001e47a000488d20000903d00003499000608e20001e07300021c010005cc5500042c3e0000148a0005e4cd0000045200000462000250d1000338560006f06a0002d09b0003b10500003509000398c90001e0990005a4760002b0600003942b0001607a000450ca000344d30002343d000204aa000614620003283d0005c48a0002789a000531010006f02d0004509a00052029000034a10002a85300014c7a0001389a00058856000304d20006e1050005589900028860000640320003447b000558010002383d00053cca0001087a00014cd20005943a0001582e00056c29000488a200069d0d0004f4750003803d000288ac00046c56000014a2000574620006f07a00050c760004b85a000370720001d0530001e09b0000eccb0002543d0001602e0004ac5a0000143f000468e2000508030001fc3d0001c8510002b49b00025059000584620005949f00034c5600035c53000210d2000468cf000278ca00060c5a0001003d00028830000314da0001b8c90005f85a000158a2000154a2000508010004d09a00014cca0004cccd0006ec3d0005085c0005f10d0004687a0006342e000544010005e0010000a43c0001dc0100037c3d000514ca0001a0ca0006cc74000004a20001cc7100049822000508240004d05a
 | 9=>0x28d400000042000034f40000304400000440000024dc000048010000305c000044ca000030bc00002439000044c40000204800001c6000000462000040560000409400001840000024740000303800002cc4000050bc0000343c0000142c00004c76000000cc000004da0000289c00001801000040b4000020ac00000c0200001cac000044ec000050fc00003056000044540000183a000018d40000200d00001430000024c400001c0d00002cec000024cb0000302a00002840000014b4000000820000303a00000824000048580000306000001084000028020000040200003c7c00002473000044aa000034cf000024ec00003cac000020440000408200001c5c0000340200000828000044bc0000149a000004ca000004780000346200000884000040a4000004bc00000c3e000040ca000044fc00002c5c00003476000040f400002cbc000000b40000247c00003801000010a4000040010000249c00002401000010480000244c00003c6400003c74000014dc00002464000024bc00003c2c0000383e00002c0200001028000030d200002cca00004c0200004c560000140600004c400000100d000040580000043e000000d4000034aa00003878000044820000006000000002000030fc0000204c0000480200001c640000208c00002c72000008a4000030ca00000000000004d40000003a0000203800001c3800001044000000dc000010940000143a00000804000038d2000024680000306c0000307c0000243a0000103c00002c400000283c0000303400005076000024ca0000200b000010b4000000ca000000580000205000001c680000005c00000401000000c4000038ca000048a20000245200001008000020090000105c000004f40000144c0000047600004072000028d200004002000030580000304200000074000000ec0000142a00001464000038fc0000309400002cfc0000302c000050d4000034cd00003874000034010000305a0000249b0000108c00001438000028fc0000043c0000142e000030a40000303600000834000030e400002c7c0000007c000024fc00003c840000009c0000245100000844000010070000004c000044d4000004aa0000287c00000c5600003440000004c4000040d400001436000000640000246c000000bc00001005000024840000100b00004cfc000014680000443e00003876000034bc0000189a0000305e00000038000044e4000040e400001074000018fc00002c520000308c00001054000044d2000050f4000024560000385800000805000030ac000000010000080b0000243b000010090000304c0000049a00002c01000030f4000008480000203400001c3400002c94000000360000302e00003ca4000000680000383c000040c40000003f00002ca40000247200003c040000503e0000249400002c9a0000005400000c01000028a400000056000044f4000028ec0000403e000040ec00004476000024ac0000289a00005001000014050000483e000024c90000447400002c3e000024e400001802000014fc00004c7800003052000010c40000283e000024710000444a0000404a0000407c000000720000446c0000280100001484000008030000289400004c010000104c0000307a00002cf40000240200001434000008c400004c3e0000448c000018ec000004fc0000248c0000406c00003032000040bc000024a4000000fc0000009a0000489a000024440000249a000024f40000085c00003c340000440100000494000034ec000014320000343e0000006c0000008400003c440000385600002835000030b40000189400003c280000449000001040000040700000106c0000102400004440000050d20000243c0000102c0000504000004c540000409a000014ac00004c5800003c0500003c0b000014e400004040000030a2000024cc000010ac00003c48000030dc0000149c0000507400005002000030680000309a0000003d0000004a00001852000030720000287a0000009400002454000048400000087c0000005200000062000004a400003030000030d4000008ac000050ca000004ec000000ac000000370000148c0000087400002caa00005062000000e400001064000014a40000349c0000144400004856000048fc0000107c000034fc00001034000010bc00004478000028bc00003478000040fc000030640000503c000030c400002ccc00000864000024b4000004cc0000406200002499000014a2000024530000305400003c0200004494000044b4000014420000008c0000408c0000109c00003c030000405400000c58000000a400003454000030ec00003cc4000038020000004400004462000000f4000034da000018bc00003c010000409c0000300a000050ec0000245800002cd4000024d400003c5c00003840000024600000443c00003084000000a20000082c0000347400002c5600003c2400004402
 | 10=>0x7c000000ac00000064000000740000002c0000000000000084000000a400000004000000340000004400000028000000050000000b000000480000000200000003000000c4000000010000005c00000024
 | 11=>0x0
 | _=>0
def tg18:Fin 7->Nat | 0=>0 | 1=>0 | 2=>3 | 3=>0 | 4=>3 | 5=>3 | 6=>3
def g18:=[sw23,sw40,sw41]
abbrev bf18:=bar c18 (findAut2 c18.shTT mk0 g18 (Rgen a1t7 11 xt18 P18) N18 L18 H18) (Rgen c18.all1v 11 x18 P18)
lemma b18_sm:([6,7,10,11]).all (fun s=>span (bf18 s) (N18 s) 0)=true:=by decide +kernel
lemma b18_8_0:span (bf18 8) 190 0=true:=by decide +kernel
lemma b18_8_1:span (bf18 8) 190 190=true:=by decide +kernel
lemma b18_8_2:span (bf18 8) 190 (190+190)=true:=by decide +kernel
lemma b18_8_3:span (bf18 8) (712-(190+190+190)) (190+190+190)=true:=by decide +kernel
lemma b18_9_0:span (bf18 9) 200 0=true:=by decide +kernel
lemma b18_9_1:span (bf18 9) 200 200=true:=by decide +kernel
lemma b18_9_2:span (bf18 9) (446-(200+200)) (200+200)=true:=by decide +kernel
lemma lb18:∀ t,HasCircuitSize 7 f18 t->12<=t:=prove_base2 f18 r18 mk0 c18 tg18 x18 xt18 g18 [(5,6),(2,4),(1,3)] N18 L18 H18 P18 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun s hs=>match s,hs with | 0,_=>fun i hi=>by simp [N18] at hi | 1,_=>fun i hi=>by simp [N18] at hi | 2,_=>fun i hi=>by simp [N18] at hi | 3,_=>fun i hi=>by simp [N18] at hi | 4,_=>fun i hi=>by simp [N18] at hi | 5,_=>fun i hi=>by simp [N18] at hi | 6,_=>fun i hi=>span_sound (bf18 6) (N18 6) 0 (lAL.1 b18_sm 6 (by decide)) i (nZL _) (by omega) | 7,_=>fun i hi=>span_sound (bf18 7) (N18 7) 0 (lAL.1 b18_sm 7 (by decide)) i (nZL _) (by omega) | 8,_=>span_chunk4 b18_8_0 b18_8_1 b18_8_2 b18_8_3 | 9,_=>span_chunk3 b18_9_0 b18_9_1 b18_9_2 | 10,_=>fun i hi=>span_sound (bf18 10) (N18 10) 0 (lAL.1 b18_sm 10 (by decide)) i (nZL _) (by omega) | 11,_=>fun i hi=>span_sound (bf18 11) (N18 11) 0 (lAL.1 b18_sm 11 (by decide)) i (nZL _) (by omega) | _+12,hs=>by omega) (checkTags_sound bsT2 hT2 f18 E18 tg18 [.emp,.emp,.base 8 [0,3,0,1,2,5,4],.emp,.base 8 [0,1,2,3,0,4,5],.f0 6 (.base 4 [0,1,2,3,4]),.f0 5 (.base 4 [0,1,2,3,4])] (by decide +kernel) (by decide))
def E19:List (Fin 7×Fin 7):=[(0,1),(0,2),(0,3),(1,2),(1,4),(2,5),(3,6),(4,6),(5,6)]
def f19:BFn 7:=fun x => (x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 2)||(x 1&&x 4)||(x 2&&x 5)||(x 3&&x 6)||(x 4&&x 6)||(x 5&&x 6)
def r19:=0x4042060a0ca1170f1c851829c3a68382010418185804054a354010170e9c83890a0c58718802895231280208d1332100483862a42228c12120e01015209504251c24121450118182834405c12120c802834219242120e00a91104858032480411602540504709090618062488a262418418185890a085061850185281894229c12120d00483822a4280a2500c4888283401922845c241216020294126085062060a0e00823404c81809c24241b050909090612141e0a1212120c24283c1424242418485078284848483090a0f050909090612141e0a1212120c24283c142424241848507e38f0d5a3161c172c54a34264a9193161c0f1a2c4952951a0e991a253254990e5499131a2bc6ad172c4c952151c182c686e99b24678d16264870607161b956a519d325468b12141c489122448912244850a142850a14285060c183060c18305c3870e1c3870e1c3162c58b162c58b154a952a54a952a5470e1c3870e1c3871c3160a94224280e18284480c14222428300e1418122428301522140a24283018a1220614170c582a50890a022281018905c316084e18284480c080624270a94223860a0c1420202
def x19:=[(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa4d301301338038e8c08d34caa800004d33938ca02a4c04ca000e070381c0e0703a108101017a852a88fffe00007fc01ff0000108408080bd4295444000,0),(0xcccccccccccccccccccccccccccccccc94054e3a54d300054a02595302a2a300e4ee5404d30009404c32190c86432190c8a012027a0428dfffaa1200ff8000000ff8005009013d021460001509,0),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f03a58e500094e01300054e0004d3015aa5940013a8094a38094542a150a8542a15005247c0407fff0534165ff000000000007fc02923e0200000829a0b2,0),(0xff00ff00ff00ff00ff00ff00ff00ff0000ef4038e0004c068c2a8280000028940025680000280013a08844221108844224c6385057f93084621db80000003fe00ffffe631c2828009842310edc,3),(0xffff0000ffff0000ffff0000ffff000003e3804ce025380b136003250004ca000000300965e0c00c29209048241209048707c067f851c1077c11c00000003ffff007ff83e0300028e083be08e0,3),(0xffffffff00000000ffffffff0000000000e38000e000025000b00a0096530c000000a25000313000324120904824120907f807f86061fe07801e000000003ffffff803fc00003030ff03c00f00,3),(0xffffffffffffffff0000000000000000000000940fce94e02500000e30c9403b8e0c00e30c025e250381c0e070381c0e07ffff8787860018006001ffffffc0000000000003c3c3c3000c003000,0)]
def xt19:=[(tv6,0),(tv7,0),(tv8,0),(tv9,3),(tv10,3),(tv11,3),(tv12,0)]
def c19:Cfg:=⟨145,290,428,488,mk101,0xffffffffffffffe8fefcfaf8eeeceae81c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71c71ffffffffffffffffffffffffffffffffffffe000000000000000000000000000000000000,mk96,mk102,mk103,mk104,mk105,mk69,mk70,mk71,mk72⟩
def N19:Nat->Nat
 | 7=>33
 | 8=>410
 | 9=>263
 | 10=>14
 | 11=>1
 | _=>0
def L19:Nat->Nat
 | 7=>6
 | 8=>9
 | 9=>9
 | 10=>4
 | 11=>0
 | _=>0
def H19:Nat->Nat
 | 7=>0xfc1d3ff265c7e812fce5a76ed89461d88eaad26c97d0643ecdf6dfc028f7bdfdd8bbb70ab3eecca3f960a29d8a9dd247927c39870c65865d21814b60736c4e66c418668aa64b29394b14ee474db34553e938afad2e577e245196087b2c0663d60112d4
 | 8=>0xfeab26fe8728fdeffafdb1c7fcfb8cfc7a24fb63bffa836ef9a99df90eb0f8c7eaf8b9a7f86134f84291f8410df7059ff657edf2c31df29d7ff0d59df0a424eff21cefceddeefaf5eebf41edbd32ed74cfed68c2ed53bced46d0ec298deb3bd1eb1cfce86aade83289e7455ce66679e6142fe48b4fe470f4e46c98e3d83ae3977ce373c4e2a68ce1ecdce1a545e17e78e0eb83dfecbfdfe214da8f09d9ee0cd876edd7ef58d5f404d599f9d51ebad4bdfad3a7d6d376fad20e10d20632d204b8d186e2d16a24d10d01d0643ecfa0f2cee3fecd8cf6cd5a19ccc3d5cb4e66ca7a31ca4aebc9f76ec94d84c893e6c84d47c6ed8cc606dcc52ec9c525d3c4b357c49a6dc45634c39f7cc38d9ec35e85c264a4c25838c226c5c1ce28c1b943c16760c16589c0ab84bfd89bbe0b0abdef9ebd2579bbf83ebbf655bba0e6bb50d8baf10dbad6ceba2ae8b97e92b83688b807deb7442fb623d6b5b37fb5a785b4c95fb45961b40ecdb3dfe6b3d577b36fd4b29c4cb05ee7affe00af8fb0af5e85aef714aeddd5add1bfad5a84ad546dad07bbac15b7abcae9aae402a95832a8c94fa8972da73822a72bfba6af15a5d3f1a555dea510a5a50f89a3f3f7a3d74ca369d0a31ff7a262f9a1f965a162f1a03ef89f36c99ec0449dfc9b9c98179aeaf49a2b959a18a09880ac9873ee9870139611dc94196a940f5093a2d3938464935c3591cd8b8ff53f8feae28fb2138f0a328df1bc8ddefa8d6a668d2e708ce5f58c1b808ae79589e7df898450897371896f9388cf04860ea085e42785b92d852bcd84ab378402ef83ddea830f0882552382239582204581a3a480e2817f66387ecd807e61de7e39027dc4a17d847c7b4ad67acc7279f812784baf7791c876e92a76137e75147d739e967340fd7301b0726b5a72527f71ae7771abcb719c4b71061270c1097078f46fa9a76f7d606f59fd6f0df06e737e6e13c96dbc4c6cf3276ca3236c84926c53de6c1cad6bcd556b5f3d6b22e86b1d656a645f699e2469684f691f0368041667cb2a6705eb66c418664d90660c506603d7653aa464c190635adb633ffa630d226171ea6103465ffafd5f31935ee0eb5ee0445de7c95b6ad15b20f55a94435a444a58bcfc578d9654dbf754b35254039853af7052f43c50b8ff508450503c2550245b50223850069f4f98a24f85634eff604efbb24edafa4db2a24d73024d24384c0d284bc3874b29204aecfb4a567848d9f448cded489d314826bd46908e4649a2462f9845b7e24275914180d040c4d4404de5402c124004d23f76253e9cd23dfc053da0393d51b13d15003c92c63b5d663a43d139f9943941183900f7387a6e3866853859f0341d9533cec632c5fc3217d330f3ed30c2852fd8002ede2b2de8842dc5ac2cd4712c93792bf7bd2bd6a02af9f52a4baa2a3f1429e15c292bb227ccbe27c1e027be93279dfe26dab226a4e12616e4260aba244f452391f8224a002239e422011f20fd3c2087fd206d5f1f53a51e13411daef31d536a1d336b1cfd4c1c44011b7ee219f08518973a17e5441771e516eeee1651c415fd0c15f43b14b5bc14a98f14a56513f84812697512102711df3c114d7811334c1124690f98910f06950eefeb0db4650d265b0ceedf0ced3f0cb0db0c77a30b488d0affec0ad4da0ac46f0aafdd0a464d09cd9509869d08b6b708a1e10630d4056827050b7f04ce0500a92200369d00030f
 | 9=>0xff93a7ff442bfefeaefeab26fde67bfddbc6fcc126fb63bffb1c74fb000dfa836ef97e1df8c7eaf86960f84799f8410df729a3f6da01f604bbf58e78f51d2af443a2f26731f252dff18b2ef0cb97ec5e75ebdfcaeb3bd1e9494fe7b0d1e7891de6ab2fe66679e64511e62e49e564bbe3977ce373c4e2f1d5e2923ae16e9ddbd5cfda3a37d8ef61d71205d636edd599f9d56091d51ebad4e0fad46e9fd3fb1dd3005fd1bb5fd0758dd0643ed05af0cfa0f2ce1f04c99e85c8c200c893e6c87930c7d478c6ed8cc4c5d3c42f46c3ffa3c38e6ac2d1b1c0ab84c058bbbf7e49bebd1abdfdd8bc6a94bbef9cbba0e6bb4e80ba79d9b8a6dcb79a7eb6d623b6cb6eb61aeab5b37fb54604b40ecdb019b8aef714ae4a44add1bfad334aac23a2abf93cabcae9aac275aa7ad6a95832a8c94fa85234a6ad61a510b2a3a828a2dbfc9ebac59c98179c62699beefb9a46439921489570eb944bf0940f5093eccc93a2d391cd8b8f21488e7b7b8d9e508ccc1d88cf0486794c85f0d985b92d824ba782239581a3a4816b898012377dc4a17d3fa37b51ba7acc727a25cf786a4b76928375f8886ed33a6e13c96de7ee6c53de6b75066b4df86ade326aa6026a500b69dd9a69594f69200e691f0368ded6688fbe67e6bc66c4186547f464c99764bdf16398f6615fba5ffafd5e12825e01865dd6c15cdc8b5cdc315cb36b5b03a55a698c5862a4577818575617573da95688445630c254dbf753ba4152c0a44f3feb4e6e664d73024d032c4b29394aecfb4a89d24a532647b75146487f4646c1446834444364432f504275914158a440fae640e24d3e46503e2e983e14783c0cf53c01d63b5c043ad5273a43d13a2b38388686359a963555e03414e93412c6339896336ecd3286e332632b3249783075fb2f51002e99752de8842dcfeb2d74202b40752af28028fa932812da2749802607de25a6a52542242451962362d6231afc224ba822011f1f306f1dccf51dcbf31d536a1b7ef7192006181a8c15ce8a152adf14a98f136f5b13453410d2cb0e2c7c0b59fb0b4f46082f93077567072c36070a3605e342051f5604b5bc03783b0301f801b72201aed300b8fc
 | 10=>0xf8c7eaeb3bd1e66679bc6a94b5b37faef714add1bfa9583293a2d3816b8967e6bc66c41815ce8a14a98f
 | 11=>0x66c418
 | _=>0
def P19:Nat->Nat
 | 7=>0x2683d000560a20002f4530004f8530005b4590005083d000560270005e83900014c9900014c710005e8990001289d0002b8510003ac750003f8cd00048c710004f82b0004eca200048c510004cc7a0005982d00000000000058aa0005e8c90004ecb2000304c90004cc8a0004d4590002f4230005e8510004f89b00014cc900030471
 | 8=>0x2483e0000583d0001388a0002e0290001183e0003ac9a0002c0010002142e0003dc5a00038c7a0001ac540002309a0003b4c90003d45a00028c9a0000e1010000806c0000ac3d000218ce0003acca00006c520002009a000380560002347600020c31000060ce000090ce00034456000274990000e88a000080010001ac280002b87300020c9b0002cc3d000134510001ac0d000310560000e85a0001a03d00041459000080480003e8ca00028cca000060a20002b8010002307a00026c2b0000ac5a000415050000dc6a0000ac8a0001e0ce00006cce0000643d000278350002e8ca000248d20003dc010002b85300015c3d00038c56000414d1000224010003b05100020c99000160560003a8390003a8cb000224d20002f839000268a50003bc6a00021cd200035c9f0000e8b2000090ca0000443d0002c082000170ca0000503e000080280000cc5a00030c3900020ccb00008050000288790000e8e20003b4d10003149b00014c390003dc550003407100029035000060c900011ca20001e00100028c350002b8cb0000943e0000ac7a0000fc3d000060510001dc3d000248ce00026c9900038c5a00026c530000e89f0001e0530003805a0003dc620000aca20001783d0001ac9c0002009f000158d10000d43d0003a8ce0002003f00026ccb00026c010001703d0000c0cd000200570003546a0001605a0001ac010001f03d0001aca00000608a00022456000344a2000158a30003e8620000782e0001ac240003a8530002c83500025c3d00015039000060b20002fc290003bc7a0002fc9b0001bc5a0001d4710000689d000350220000609b000114d100020c2b0003d83d0000787a0003105a00020cd20000183d000050ce00040cce0003f09b00013c240002d43d0001d0350001a43d0002e06a000080b40000483e0001ac3c000338010000c8c9000050d200013c0100006c360002603d000398c4000158590003845a0003bcca000288d30003dcca00002c51000130990003b50100035c320003103e0003bc9a0003e8820001fc990003389c0000509a00038871000118320003c49d000200520002003a0002f4760003e8aa000388510003e8560001183a0003545a000078ca0001903d0002fc3b00028c3e0002ec48000130a50003a801000108710000ac3f00011c560000ac2d000080b00000ccda000384b2000080a40001907500020c530000ccce0002ec24000224cd000288d6000084ca0003dc7a00014cc90000702b000200cf0003d47a0003143b00040c2e0002484a0003d4ce000384e2000340510000c8510003a83e0002a029000060cb000080a80000e49d00020cce0002eca0000080ac00040c0100028c42000380aa00006071000200ca000000000000d875000060530003840100006ca20003a0560000c0a50002305a0001043600026c9b000380770002c04a00041509000179050003ac32000080a000020c5100006c5a000128ca0003383c0000e82f000314010003a83b0003fc3e00037c010001e8d20003c03d0003b5090002103d0002fc010003447a00020c010001d451000060010002f4a2000344d20000c871000094560002bc3d0002c03e0000e8a20001609a0000cc560003bc8a0003e8ce0000143d0002f4d20002887b000134710003202d00026cca0001003d0001803d000320a20003a89b00027471000310320000983500006cd20003d4d20001d43900009035000234720001d4c90003bc560000ccca00040c9b00026c290003e8d20001043e000158d300008030000218730003b471000414790003f0360003bcda0002182e00021cce0001f055000384560003bc760004087500028c7a0002ecb40003083d0003bcce0003984c0003445a0000803c0002fc2b0001483d0003b4790001283200014c5100038cd200008040000158a1000114d300014c71000414cd0001085100041455000344ce0000e0990003f03e000050760000602b0002180100041475000338a400007832000158d60003e83e000220510000590500006cca000174290001e4360000c8390002fc73000338a80003ac2e0003102e00038001000104ca00026c510001acb40003d4560002ec280001585b0003183d000060730002ec40000244560003dc56000230ce0000e87a0002d82900026cc90002383d0002f4560002eca4000224ce0000bc51000114d60001e0cb0000e0710000605200013c4800020c9a000138290001bc41000288d10002ec010000c899000160ca0002eca8000230d200013c3c0000f055000288a3
 | 9=>0x1c5000003002000028340000143e000028d200002034000024380000240100001c400000244c0000102e000030a40000085400000056000018d40000189a000030bc0000309a000028d60000205c000004ca000020a4000004fc00001472000028320000304000000c3800002872000008280000285c00001c3a00000c0d000024750000080d00000440000030ca000014e8000034ca000018ca000014ca000014d4000028ac0000285a0000148c000014e4000028100000185c000028ca000034fc000014d20000340100000c090000207c00003052000034f0000034d00000303900001034000030cb000018370000200e000028640000248200001038000030fc0000043e00001072000030e80000104c000028d000002c24000018350000184000001c9a000000400000309900000802000004d0000014ce0000204400001402000014b4000018a400000ca400000c4c000020a00000089c000018bc000030ce000020070000080100001084000008a000000cac00000402000000ac000034620000304800000c34000008240000305300001440000034f40000049c0000303c0000344000000054000004ce000024400000282c00003094000030ec00002c940000107a0000003e000028300000083c000004d20000345400002024000034bc000004010000348200002028000018fc0000049a000018e8000034aa000034560000080e000030b40000183e0000307c0000309c0000300100002c2800002c7c000018440000306c000028060000144a000028ce0000303e000028940000203c00002c38000030cc000028ec0000180200001c02000034cc0000184200001848000034ec0000080700000000000014d0000028c4000024c400002484000020040000244a000024fc0000206c0000102c000020b400001cc400002850000030e400003402000018940000305400002094000018ec0000185200001cfc0000303b000028f400000002000020380000287c0000243e000024ac000030c9000034ce000034e800002402000034d40000282a000020bc00002c5400001c720000102a0000309b000004780000287a000028380000282e000018b4000034e40000280f000014c40000187c0000189c000034d2000030d4000030d000002477000010320000186c000020540000349a000028360000249c0000243c000030d8000010c40000107c0000200d0000187a0000183800001036000028cc000014f400002c340000000100001801000018cc0000147c0000183a00003051000018ce0000285200001c01000004760000303a0000209c000034b40000343e00002009000018e40000305c0000086c00001030000008b4000010ac00002c5c00001401000028e0000028d40000284c00000c500000245000003458000034a4000010500000348c000034c4000028d800002884000028dc00002003000020a8
 | 10=>0x54000000280000000d000000020000009c00000001000000a0000000240000003c0000000e00000007000000000000006c000000b4
 | 11=>0x0
 | _=>0
def tg19:Fin 7->Nat | 0=>0 | 1=>0 | 2=>0 | 3=>3 | 4=>3 | 5=>3 | 6=>0
def g19_0:=[sw26,sw25]
def g19_1:=[sw24,sw28]
def gs19:=[g19_0,g19_1]
def pa19:=[g19_0,g19_1,g19_0,g19_1,g19_0]
abbrev bf19:=bar c19 (findAutPath c19.shTT mk0 pa19 (Rgen a1t7 11 xt19 P19) N19 L19 H19) (Rgen c19.all1v 11 x19 P19)
lemma b19_sm:([7,10,11]).all (fun s=>span (bf19 s) (N19 s) 0)=true:=by decide +kernel
lemma b19_8_0:span (bf19 8) 200 0=true:=by decide +kernel
lemma b19_8_1:span (bf19 8) 200 200=true:=by decide +kernel
lemma b19_8_2:span (bf19 8) (410-(200+200)) (200+200)=true:=by decide +kernel
lemma b19_9_0:span (bf19 9) 131 0=true:=by decide +kernel
lemma b19_9_1:span (bf19 9) (263-131) 131=true:=by decide +kernel
lemma lb19:∀ t,HasCircuitSize 7 f19 t->12<=t:=prove_basePath f19 r19 mk0 c19 tg19 x19 xt19 gs19 pa19 [[(4,5),(1,2)],[(3,4),(0,1)]] N19 L19 H19 P19 rfl (by decide +kernel) (by decide +kernel) (by decide) (by decide +kernel) (fun s hs=>match s,hs with | 0,_=>fun i hi=>by simp [N19] at hi | 1,_=>fun i hi=>by simp [N19] at hi | 2,_=>fun i hi=>by simp [N19] at hi | 3,_=>fun i hi=>by simp [N19] at hi | 4,_=>fun i hi=>by simp [N19] at hi | 5,_=>fun i hi=>by simp [N19] at hi | 6,_=>fun i hi=>by simp [N19] at hi | 7,_=>fun i hi=>span_sound (bf19 7) (N19 7) 0 (lAL.1 b19_sm 7 (by decide)) i (nZL _) (by omega) | 8,_=>span_chunk3 b19_8_0 b19_8_1 b19_8_2 | 9,_=>span_chunk_join b19_9_0 b19_9_1 | 10,_=>fun i hi=>span_sound (bf19 10) (N19 10) 0 (lAL.1 b19_sm 10 (by decide)) i (nZL _) (by omega) | 11,_=>fun i hi=>span_sound (bf19 11) (N19 11) 0 (lAL.1 b19_sm 11 (by decide)) i (nZL _) (by omega) | _+12,hs=>by omega) (checkTags_sound bsT2 hT2 f19 E19 tg19 [.emp,.emp,.emp,.base 8 [2,0,1,0,3,4,5],.base 8 [0,2,1,3,0,4,5],.base 8 [0,1,2,3,4,0,5],.emp] (by decide +kernel) (by decide))
def E20:List (Fin 7×Fin 7):=[(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(3,6),(4,5),(5,6)]
def f20:BFn 7:=fun x => (x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 2)||(x 1&&x 4)||(x 3&&x 5)||(x 3&&x 6)||(x 4&&x 5)||(x 5&&x 6)
def r20:=0x202225418648890a546982020214186100522c4a2480242c519220092344c4a008418144848851264695010858a93088061060615121481828342212280a26008418144808088920a18202021418685062060a0e08843804c82222a480a26242821418618045090c16208498144822090b006492214418185404052824c110a858a52a28092300c4b03090a090612141e061214120c24283c0c24282418485078184850483090a0f03090a090612141e061214120c24283c0c24282418485078184850483090a0f262c382e58992a474e3c3262c381e3868c582c54a293464c581a2572cd8992a4c858a94a83226ac68a992951c182d6a74a3434c8cf1a2c4c90e0c0eac5869519d325468b12141d4a952a54a952a54a3468d1a3468d1a30a142850a1428509224489122448912224489122448912242850a142850a14270e1c3870e1c387050a142850a1428524448501c3030508a946844850601c3050890182844248890a0140aa51a112141809112140440d185051212228101a946844829109c305089018100d489092223860a0c1420202
def x20:=[(0x2aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa8e38e4ce0004c04d38c028e4ea8ce540a93000000e070381c0e070381c8088404222eb29447ffe00ff8000000ff8000040442021117594a22000,0),(0x33333333333333333333333333333333134d30134c038e3a50005539400132804ce2bf4c32190c86432190c86504100a984414dfffca1200007fc01ff00003fe8208054c220a60000509,0),(0x3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c2596538038094094e2808e53802a58e8025000a8140a05028140a0502a29229104883ff2a9b565ff00003fe00007fc011491488244000954dab2,3),(0x3fc03fc03fc03fc03fc03fc03fc03fc000000940013000000553000013540b1300031300c86432190c864321903e031c17ffc0803101b800000000000007fffe1f018e080000401880dc,0),(0x3fffc0003fffc0003fffc0003fffc0000c000025940013000000300000a000009404c09520904824120904824031c3e3ff00a11c3e21c1ffff8000000007fc0018e1f00380508e1f10e0,1),(0x3fffffffc00000003fffffffc000000000fc038e38efe5038b0e00000c00000e3389653341a0d068341a0d0683c1fffde00f0600c006000000003ffffff80001e00000f0078300600300,0),(0x3fffffffffffffffc0000000000000000000000002500ea00025000e2533802500000e028140a05028140a0503fffc0207f0381f003801ffffffc0000000000000fe0103f81c0f801c00,3)]
def xt20:=[(tv6,0),(tv7,0),(tv8,3),(tv9,0),(tv10,1),(tv11,0),(tv12,3)]
def c20:Cfg:=⟨153,306,408,462,mk106,0x3ffffffffffb3ffa3ffffffa3bbb3aba071c71c71c71c71c71c71c71c71c71c71c71c71ffffffffffffffffffffffffffffffffffffffe00000000000000000000000000000000000000,mk107,mk33,mk48,mk49,mk50,mk27,mk108,mk28,mk29⟩
def N20:Nat->Nat
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
def tg20:Fin 7->Nat | 0=>0 | 1=>0 | 2=>3 | 3=>0 | 4=>1 | 5=>0 | 6=>3
def g20:=[sw35,sw36,sw34]
abbrev bf20:=bar c20 (findAut2 c20.shTT mk0 g20 (Rgen a1t7 11 xt20 P20) N20 L20 H20) (Rgen c20.all1v 11 x20 P20)
lemma b20_sm:([6,7,10,11]).all (fun s=>span (bf20 s) (N20 s) 0)=true:=by decide +kernel
lemma b20_8_0:span (bf20 8) 200 0=true:=by decide +kernel
lemma b20_8_1:span (bf20 8) 200 200=true:=by decide +kernel
lemma b20_8_2:span (bf20 8) (557-(200+200)) (200+200)=true:=by decide +kernel
lemma b20_9_0:span (bf20 9) 200 0=true:=by decide +kernel
lemma b20_9_1:span (bf20 9) 200 200=true:=by decide +kernel
lemma b20_9_2:span (bf20 9) (410-(200+200)) (200+200)=true:=by decide +kernel
lemma lb20:∀ t,HasCircuitSize 7 f20 t->12<=t:=prove_base2 f20 r20 mk0 c20 tg20 x20 xt20 g20 [(2,6),(1,5),(0,3)] N20 L20 H20 P20 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun s hs=>match s,hs with | 0,_=>fun i hi=>by simp [N20] at hi | 1,_=>fun i hi=>by simp [N20] at hi | 2,_=>fun i hi=>by simp [N20] at hi | 3,_=>fun i hi=>by simp [N20] at hi | 4,_=>fun i hi=>by simp [N20] at hi | 5,_=>fun i hi=>by simp [N20] at hi | 6,_=>fun i hi=>span_sound (bf20 6) (N20 6) 0 (lAL.1 b20_sm 6 (by decide)) i (nZL _) (by omega) | 7,_=>fun i hi=>span_sound (bf20 7) (N20 7) 0 (lAL.1 b20_sm 7 (by decide)) i (nZL _) (by omega) | 8,_=>span_chunk3 b20_8_0 b20_8_1 b20_8_2 | 9,_=>span_chunk3 b20_9_0 b20_9_1 b20_9_2 | 10,_=>fun i hi=>span_sound (bf20 10) (N20 10) 0 (lAL.1 b20_sm 10 (by decide)) i (nZL _) (by omega) | 11,_=>fun i hi=>span_sound (bf20 11) (N20 11) 0 (lAL.1 b20_sm 11 (by decide)) i (nZL _) (by omega) | _+12,hs=>by omega) (checkTags_sound bsT2 hT2 f20 E20 tg20 [.emp,.emp,.base 8 [3,5,0,0,4,1,2],.emp,.base 0 [0,1,2,3,0,4,5],.emp,.base 8 [0,1,2,3,4,5]] (by decide +kernel) (by decide))
def bsT3:List BaseEntry:=[⟨7,E9,11⟩,⟨7,E10,11⟩,⟨7,E11,11⟩,⟨7,E12,11⟩,⟨7,E13,11⟩,⟨7,E14,11⟩,⟨7,E15,11⟩,⟨7,E16,12⟩,⟨7,E17,12⟩,⟨7,E18,12⟩,⟨7,E19,12⟩,⟨7,E20,12⟩]++bsT2
lemma hT3:BaseTableOk bsT3:=(baseTable_cons _ _ (baseEntry_of_f f9 E9 (by decide +kernel) lb9) (baseTable_cons _ _ (baseEntry_of_f f10 E10 (by decide +kernel) lb10) (baseTable_cons _ _ (baseEntry_of_f f11 E11 (by decide +kernel) lb11) (baseTable_cons _ _ (baseEntry_of_f f12 E12 (by decide +kernel) lb12) (baseTable_cons _ _ (baseEntry_of_f f13 E13 (by decide +kernel) lb13) (baseTable_cons _ _ (baseEntry_of_f f14 E14 (by decide +kernel) lb14) (baseTable_cons _ _ (baseEntry_of_f f15 E15 (by decide +kernel) lb15) (baseTable_cons _ _ (baseEntry_of_f f16 E16 (by decide +kernel) lb16) (baseTable_cons _ _ (baseEntry_of_f f17 E17 (by decide +kernel) lb17) (baseTable_cons _ _ (baseEntry_of_f f18 E18 (by decide +kernel) lb18) (baseTable_cons _ _ (baseEntry_of_f f19 E19 (by decide +kernel) lb19) (baseTable_cons _ _ (baseEntry_of_f f20 E20 (by decide +kernel) lb20) hT2))))))))))))
abbrev cg {n req:Nat}:=conj_of_gtree (n:=n) (req:=req) bsT3 hT3
def cj1:=cg (req:=10) (fun x:Fin 7->Bool=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 0&&x 4)||(x 1&&x 2)||(x 3&&x 4)||(x 5&&x 6)) [(0,1),(0,2),(0,3),(0,4),(1,2),(3,4),(5,6)] (.f1 5 (.f0 6 (.base 16 [0,1,2,3,4]))) (by decide +kernel) (by decide)
def cj2:=cg (req:=10) (fun x:Fin 7->Bool=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 0&&x 4)||(x 1&&x 2)||(x 3&&x 5)||(x 4&&x 6)) [(0,1),(0,2),(0,3),(0,4),(1,2),(3,5),(4,6)] (.b2 5 (.f0 3 (.b2 6 (.f0 4 (.base 14 [0,1,2])) (.f0 4 (.base 14 [0,1,2])))) (.f0 3 (.b2 6 (.f0 4 (.base 14 [0,1,2])) (.f0 4 (.base 14 [0,1,2]))))) (by decide +kernel) (by decide)
def cj3:=cg (req:=10) (fun x:Fin 7->Bool=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 2)||(x 1&&x 4)||(x 3&&x 5)||(x 4&&x 6)) [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,6)] (.b2 5 (.f0 3 (.b2 6 (.f0 4 (.base 14 [0,1,2])) (.f0 4 (.base 14 [0,1,2])))) (.f0 3 (.b2 6 (.f0 4 (.base 14 [0,1,2])) (.f0 4 (.base 14 [0,1,2]))))) (by decide +kernel) (by decide)
def cj4:=cg (req:=10) (fun x:Fin 7->Bool=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 2)||(x 3&&x 4)||(x 3&&x 5)||(x 4&&x 6)) [(0,1),(0,2),(0,3),(1,2),(3,4),(3,5),(4,6)] (.b2 6 (.f0 4 (.b2 5 (.f0 3 (.base 14 [0,1,2])) (.f0 3 (.base 14 [0,1,2])))) (.f0 4 (.b2 5 (.f0 3 (.base 14 [0,1,2])) (.f0 3 (.base 14 [0,1,2]))))) (by decide +kernel) (by decide)
def cj5:=cg (req:=10) (fun x:Fin 7->Bool=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 2)||(x 3&&x 4)||(x 4&&x 5)||(x 5&&x 6)) [(0,1),(0,2),(0,3),(1,2),(3,4),(4,5),(5,6)] (.b2 6 (.f0 5 (.b2 4 (.f0 3 (.base 14 [0,1,2])) (.f0 3 (.base 14 [0,1,2])))) (.f0 5 (.b2 4 (.f0 3 (.base 14 [0,1,2])) (.f0 3 (.base 14 [0,1,2]))))) (by decide +kernel) (by decide)
def cj6:=cg (req:=10) (fun x:Fin 7->Bool=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 2)||(x 4&&x 5)||(x 4&&x 6)||(x 5&&x 6)) [(0,1),(0,2),(0,3),(1,2),(4,5),(4,6),(5,6)] (.f0 3 (.base 19 [0,1,2,0,3,4,5])) (by decide +kernel) (by decide)
def cj7:=cg (req:=10) (fun x:Fin 7->Bool=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 4)||(x 2&&x 5)||(x 3&&x 6)||(x 4&&x 5)) [(0,1),(0,2),(0,3),(1,4),(2,5),(3,6),(4,5)] (.b2 6 (.f0 3 (.base 15 [0,1,4,0,2,3])) (.f0 3 (.base 15 [0,1,4,0,2,3]))) (by decide +kernel) (by decide)
def cj9:=cg (req:=10) (fun x:Fin 7->Bool=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 0&&x 4)||(x 0&&x 5)||(x 0&&x 6)||(x 1&&x 2)||(x 3&&x 4)) [(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,2),(3,4)] (.f0 5 (.f0 6 (.base 16 [0,1,2,3,4]))) (by decide +kernel) (by decide)
def cj10:=cg (req:=10) (fun x:Fin 7->Bool=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 0&&x 4)||(x 0&&x 5)||(x 1&&x 2)||(x 1&&x 6)||(x 3&&x 4)) [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,6),(3,4)] (.f0 5 (.f0 6 (.base 16 [0,1,2,3,4]))) (by decide +kernel) (by decide)
def cj11:=cg (req:=11) (fun x:Fin 7->Bool=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 0&&x 4)||(x 0&&x 5)||(x 1&&x 2)||(x 3&&x 4)||(x 5&&x 6)) [(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(3,4),(5,6)] (.b2 6 (.f0 5 (.base 16 [0,1,2,3,4])) (.f0 5 (.base 16 [0,1,2,3,4]))) (by decide +kernel) (by decide)
def cj12:=cg (req:=10) (fun x:Fin 7->Bool=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 0&&x 4)||(x 1&&x 2)||(x 1&&x 5)||(x 1&&x 6)||(x 3&&x 4)) [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(1,6),(3,4)] (.f0 5 (.f0 6 (.base 16 [0,1,2,3,4]))) (by decide +kernel) (by decide)
def cj14:=cg (req:=10) (fun x:Fin 7->Bool=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 0&&x 4)||(x 1&&x 2)||(x 1&&x 5)||(x 3&&x 4)||(x 3&&x 6)) [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(3,6)] (.f0 5 (.f0 6 (.base 16 [0,1,2,3,4]))) (by decide +kernel) (by decide)
def cj15:=cg (req:=11) (fun x:Fin 7->Bool=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 0&&x 4)||(x 1&&x 2)||(x 1&&x 5)||(x 3&&x 4)||(x 5&&x 6)) [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,4),(5,6)] (.b2 6 (.f0 5 (.base 16 [0,1,2,3,4])) (.f0 5 (.base 16 [0,1,2,3,4]))) (by decide +kernel) (by decide)
def cj16:=cg (req:=10) (fun x:Fin 7->Bool=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 0&&x 4)||(x 1&&x 2)||(x 1&&x 5)||(x 3&&x 6)||(x 5&&x 6)) [(0,1),(0,2),(0,3),(0,4),(1,2),(1,5),(3,6),(5,6)] (.f0 4 (.base 20 [0,1,2,3,0,4,5])) (by decide +kernel) (by decide)
def cj17:=cg (req:=11) (fun x:Fin 7->Bool=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 0&&x 4)||(x 1&&x 2)||(x 3&&x 5)||(x 3&&x 6)||(x 5&&x 6)) [(0,1),(0,2),(0,3),(0,4),(1,2),(3,5),(3,6),(5,6)] (.f0 4 (.base 12 [0,1,2,3,0,4,5])) (by decide +kernel) (by decide)
def cj21:=cg (req:=11) (fun x:Fin 7->Bool=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 2)||(x 1&&x 4)||(x 3&&x 5)||(x 3&&x 6)||(x 5&&x 6)) [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(3,6),(5,6)] (.f0 4 (.base 12 [0,1,2,3,0,4,5])) (by decide +kernel) (by decide)
def cj22:=cg (req:=10) (fun x:Fin 7->Bool=>(x 0&&x 1)||(x 0&&x 2)||(x 0&&x 3)||(x 1&&x 2)||(x 1&&x 4)||(x 3&&x 5)||(x 4&&x 5)||(x 5&&x 6)) [(0,1),(0,2),(0,3),(1,2),(1,4),(3,5),(4,5),(5,6)] (.f0 6 (.base 20 [0,1,2,3,4,5])) (by decide +kernel) (by decide)
end PEqualNP.Outside.L_meta_982_aux
open PEqualNP.Outside.L_meta_982_aux in
theorem PEqualNP.Outside.L_meta_982 : (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 5)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 3 && x 5) || (x 4 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 1 && x 6) || (x 3 && x 4)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 4)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 5 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 6) || (x 5 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 5 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 5) || (x 5 && x 6)) t → 10 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 3 && x 4) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 4 && x 6)) t → 11 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 2) || (x 3 && x 4) || (x 5 && x 6)) t → 12 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 1 && x 6) || (x 3 && x 4) || (x 5 && x 6)) t → 12 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 5) || (x 3 && x 4) || (x 3 && x 6) || (x 5 && x 6)) t → 12 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 2 && x 5) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)) t → 12 ≤ t) ∧ (∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 7 (fun x : Fin 7 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 4) || (x 3 && x 5) || (x 3 && x 6) || (x 4 && x 5) || (x 5 && x 6)) t → 12 ≤ t) :=
 ⟨lb7,cj1,cj2,cj3,cj4,cj5,cj6,cj7,lb8,cj9,cj10,cj11,cj12,lb9,cj14,cj15,cj16,cj17,lb10,lb11,lb12,cj21,cj22,lb13,lb14,lb15,lb16,lb17,lb18,lb19,lb20⟩
