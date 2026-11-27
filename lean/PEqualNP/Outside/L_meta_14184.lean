import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14184

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity



lemma lLC {α:Type _} {a : α} {l:List α}:(a::l).length=l.length+1:=List.length_cons
lemma lLA {α:Type _} {l1 l2:List α}:(l1++l2).length=l1.length+l2.length:=List.length_append
lemma fUN {α:Type _} [DecidableEq α] {β : α->Sort _} {f:∀ a,β a} {a b : α} {v : β a} (h:b≠a):Function.update f a v b=f b:=Function.update_of_ne h v f
lemma fUS {α:Type _} [DecidableEq α] {β : α->Sort _} {f:∀ a,β a} {a : α} {v : β a}:Function.update f a v a=v:=Function.update_self a v f
lemma nAA (a b d:Nat):a+b+d=a+(b+d):=Nat.add_assoc a b d
lemma lMMp {α β γ:Type _} {g : β->γ} {f : α->β} {l:List α}:(l.map f).map g=l.map (g ∘ f):=List.map_map
lemma lGD {α:Type _} (l:List α) (d : α) {i:Nat} (h:l.length<=i):l.getD i d=d:=List.getD_eq_default l d h
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool
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
   refine ⟨⟨Or.inr (Or.inr rfl),?_⟩,fun _ => ?_⟩ <;> simp [vg]
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
lemma q151 (op:GateOp) (m : ℕ) (ins:List Stat) :
   ∀ g ∈ (qg op m ins).1,Ok g:=by
 intro g hg
 cases op <;> simp only [qg] at hg
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp_all [ko, Ok]
   subst g
   simp
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp_all [ji, Ok]
   subst g
   simp
 . rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;>
     simp_all [wr, Ok]
   subst g
   simp
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
   . cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
       simp_all [qg,ko,qn,ze,GateOp.eval,q3]
   . simp at hlen
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
   . simp [qg,ji,qn,ze,GateOp.eval]
   . cases a <;> simp_all [qg,ji,qn,ze,GateOp.eval,q3]
   . cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
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



def fix {n : ℕ} (f : BFn n) (p : Fin n) (b : Bool) : BFn n :=
  fun x => f (Function.update x p b)

def depends {n : ℕ} (f : BFn n) (p : Fin n) : Prop :=
  ∃ x : Fin n → Bool, fix f p (!x p) x ≠ f x

def nonconstant {n : ℕ} (f : BFn n) : Prop :=
  ∃ x y : Fin n → Bool, f x ≠ f y



lemma arm_lower {n k s : ℕ} {f g : BFn (n+1)} {leaf inner : Fin (n+1)}
    (usesLeaf : depends f leaf)
    (usesInner : ∀ b : Bool, depends (fix f leaf b) inner)
    (vary : nonconstant g)
    (reduce : ∀ b : Bool, fix (fix f leaf b) inner false = g)
    (lower : ∀ t, HasCircuitSize (n+1) g t → k ≤ t)
    (small : HasCircuitSize (n+1) f s) : k + 3 ≤ s := by
  have varySlice (b : Bool) : nonconstant (fix f leaf b) := by
    obtain ⟨x, y, hxy⟩ := vary
    exact ⟨Function.update x inner false, Function.update y inner false, by
      simpa only [← reduce b, fix] using hxy⟩
  obtain ⟨b, t, ht, first⟩ := q141 n f leaf s usesLeaf varySlice small
  have varyTwice : nonconstant (fix (fix f leaf b) inner false) := (reduce b).symm ▸ vary
  obtain ⟨u, hu, second⟩ :=
    q70 n (fix f leaf b) inner false t (usesInner b) varyTwice first
  have hk := lower u (reduce b ▸ second)
  omega


namespace Core0

namespace Aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Sig := Nat × Nat

def top : Nat := 0x7ffffffffffffff
def zero : Sig := (0, 0)
def one : Sig := (top, top)
def target : Sig := (top, 0)
def neg (a : Sig) : Sig := (top ^^^ a.1, top ^^^ a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1, a.2 ||| b.2) else (a.1 &&& b.1, a.2 &&& b.2)
def sep (allowNot : Bool) (a : Sig) : Nat :=
  if allowNot then a.1 ^^^ a.2 else a.1 &&& (top ^^^ a.2)
def cuts (allowNot : Bool) (ws : List Sig) : Nat :=
  ws.foldr (fun w v => sep allowNot w ||| v) 0

def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def bounded (n : Nat) : Prop := ∀ i, 59 ≤ i → n.testBit i = false
def valid (a : Sig) : Prop := bounded a.1 ∧ bounded a.2

def rawInputs : List Sig :=
  [(0x403fc88992851fb, 0x4444400100810ba),
   (0x03c3d116651a6c3, 0x088880044112441),
   (0x3c00266789e38c4, 0x5dddc44781c38c0),
   (0x3ffc38780e03f0c, 0x222238380e00304),
   (0x40003f800ffc010, 0x22223b800e2c000),
   (0x00003ffff000020, 0x33333ffab000000)]

theorem testBit_top (i : Nat) : top.testBit i = decide (i < 59) := by
  have h : top = 2 ^ 59 - 1 := by decide
  rw [h, Nat.testBit_two_pow_sub_one]

theorem bounded_of_lt {n : Nat} (h : n < 2 ^ 59) : bounded n := fun i hi =>
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) hi))

theorem bounded_zero : bounded 0 := fun i _ => by simp
theorem bounded_top : bounded top := fun i hi => by rw [testBit_top]; simp [Nat.not_lt.mpr hi]
theorem bounded_and {x y : Nat} (hx : bounded x) : bounded (x &&& y) := fun i hi => by
  simp [Nat.testBit_and, hx i hi]
theorem bounded_or {x y : Nat} (hx : bounded x) (hy : bounded y) : bounded (x ||| y) := fun i hi => by
  simp [Nat.testBit_or, hx i hi, hy i hi]
theorem bounded_xor {x y : Nat} (hx : bounded x) (hy : bounded y) : bounded (x ^^^ y) := fun i hi => by
  simp [Nat.testBit_xor, hx i hi, hy i hi]

theorem nat_eq_of_testBit {x y : Nat} (hx : bounded x) (hy : bounded y)
    (h : ∀ i < 59, x.testBit i = y.testBit i) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 59
  · exact h i hi
  · rw [hx i (by omega), hy i (by omega)]

theorem valid_zero : valid zero := ⟨bounded_zero, bounded_zero⟩
theorem valid_one : valid one := ⟨bounded_top, bounded_top⟩
theorem valid_target : valid target := ⟨bounded_top, bounded_zero⟩
theorem valid_neg {a : Sig} (ha : valid a) : valid (neg a) :=
  ⟨bounded_xor bounded_top ha.1, bounded_xor bounded_top ha.2⟩
theorem valid_bin {d : Bool} {a b : Sig} (ha : valid a) (hb : valid b) : valid (bin d a b) := by
  cases d
  · exact ⟨bounded_and ha.1, bounded_and ha.2⟩
  · exact ⟨bounded_or ha.1 hb.1, bounded_or ha.2 hb.2⟩

theorem valid_sep {allowNot : Bool} {a : Sig} (ha : valid a) : bounded (sep allowNot a) := by
  cases allowNot
  · exact bounded_and ha.1
  · exact bounded_xor ha.1 ha.2

theorem bounded_cuts {allowNot : Bool} {ws : List Sig} (hw : ∀ w ∈ ws, valid w) :
    bounded (cuts allowNot ws) := by
  induction ws with
  | nil => exact bounded_zero
  | cons a rest ih =>
    exact bounded_or (valid_sep (hw a (by simp))) (ih fun w h => hw w (by simp [h]))

theorem neg_neg {a : Sig} (ha : valid a) : neg (neg a) = a := by
  apply Prod.ext
  · apply nat_eq_of_testBit (bounded_xor bounded_top (bounded_xor bounded_top ha.1)) ha.1
    intro i _; simp
  · apply nat_eq_of_testBit (bounded_xor bounded_top (bounded_xor bounded_top ha.2)) ha.2
    intro i _; simp

theorem neg_zero : neg zero = one := by decide
theorem neg_one : neg one = zero := by decide

theorem proper_neg {a : Sig} (ha : valid a) (hp : proper a) : proper (neg a) := by
  constructor
  · intro h
    have := congrArg neg h
    rw [neg_neg ha, neg_zero] at this
    exact hp.2 this
  · intro h
    have := congrArg neg h
    rw [neg_neg ha, neg_one] at this
    exact hp.1 this

theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin, Nat.and_comm, Nat.or_comm]

theorem bin_zero_left (d : Bool) (a : Sig) : bin d zero a = if d then a else zero := by
  cases d <;> simp [bin, zero]

theorem bin_zero_right (d : Bool) (a : Sig) : bin d a zero = if d then a else zero := by
  rw [bin_comm, bin_zero_left]

theorem bin_one_left (d : Bool) {a : Sig} (ha : valid a) : bin d one a = if d then one else a := by
  cases d
  · apply Prod.ext
    · apply nat_eq_of_testBit (bounded_and bounded_top) ha.1
      intro i hi; simp [Nat.testBit_and, testBit_top, hi]
    · apply nat_eq_of_testBit (bounded_and bounded_top) ha.2
      intro i hi; simp [Nat.testBit_and, testBit_top, hi]
  · apply Prod.ext
    · apply nat_eq_of_testBit (bounded_or bounded_top ha.1) bounded_top
      intro i hi; simp [Nat.testBit_or, testBit_top, hi]
    · apply nat_eq_of_testBit (bounded_or bounded_top ha.2) bounded_top
      intro i hi; simp [Nat.testBit_or, testBit_top, hi]

theorem bin_one_right (d : Bool) {a : Sig} (ha : valid a) : bin d a one = if d then one else a := by
  rw [bin_comm, bin_one_left d ha]

theorem bin_self (d : Bool) (a : Sig) : bin d a a = a := by
  cases d <;> simp [bin, Nat.and_self, Nat.or_self]

def build : ℕ → Finset Sig → Prop
  | 0, av => target ∈ av
  | k+1, av =>
      build k av ∨
      (∃ a ∈ av, proper a ∧ build k (insert (neg a) av)) ∨
      (∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ proper a ∧ proper b ∧
        ∃ d : Bool, proper (bin d a b) ∧ build k (insert (bin d a b) av))

def live : ℕ → ℕ → Finset Sig → Prop
  | 0, t, s => t = 0 ∧ s = {target}
  | k+1, t, s =>
      live k t s ∨
      (t > 0 ∧ ∃ a ∈ s, proper a ∧ neg a ∉ s ∧
        ∃ rest : Finset Sig, s = insert a rest ∧ live k (t - 1) (insert (neg a) rest)) ∨
      (∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ proper a ∧ proper b ∧
        ∃ d : Bool, proper (bin d a b) ∧ bin d a b ∉ s ∧
          ∃ rest : Finset Sig, s = insert a (insert b rest) ∧ live k t (insert (bin d a b) rest))

theorem compress {k : ℕ} {av : Finset Sig} (h : build k av) :
    ∃ t, ∃ s ⊆ av, live k t s := by
  induction k generalizing av with
  | zero =>
    exact ⟨0, {target}, Finset.singleton_subset_iff.mpr h, rfl, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, hpa, tail⟩ | ⟨a, ha, b, hb, hab, hpa, hpb, d, hpz, tail⟩
    · obtain ⟨t, s, hs, hrun⟩ := ih skip
      exact ⟨t, s, hs, Or.inl hrun⟩
    · obtain ⟨t, s', hs', hrun⟩ := ih tail
      by_cases sub : s' ⊆ av
      · exact ⟨t, s', sub, Or.inl hrun⟩
      · have hzmem : neg a ∈ s' := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (hs' hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : neg a ∉ av := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ hs')
        let rest := s'.erase (neg a)
        have hrest : rest ⊆ av := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (hs' hu'.2)).resolve_left hu'.1
        let s := insert a rest
        have hs : s ⊆ av := Finset.insert_subset ha hrest
        refine ⟨t + 1, s, hs, Or.inr (Or.inl ⟨by omega, a, by simp [s], hpa,
          fun hm => hzout (hs hm), rest, rfl, ?_⟩)⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun
    · obtain ⟨t, s', hs', hrun⟩ := ih tail
      by_cases sub : s' ⊆ av
      · exact ⟨t, s', sub, Or.inl hrun⟩
      · have hzmem : bin d a b ∈ s' := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (hs' hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : bin d a b ∉ av := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ hs')
        let rest := s'.erase (bin d a b)
        have hrest : rest ⊆ av := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (hs' hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ av := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨t, s, hs, Or.inr (Or.inr ⟨a, by simp [s], b, by simp [s], hab, hpa, hpb, d, hpz,
          fun hm => hzout (hs hm), rest, rfl, ?_⟩)⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {k t : ℕ} {s : Finset Sig} (h : live k t s) : s.card + t ≤ k + 1 := by
  induction k generalizing t s with
  | zero =>
    obtain ⟨rfl, rfl⟩ := h
    simp
  | succ k ih =>
    rcases h with skip | ⟨ht, a, _, _, hout, rest, rfl, tail⟩ |
        ⟨a, _, b, _, _, _, _, d, _, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : neg a ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a rest
      omega
    · have hzrest : bin d a b ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

def differs (allowNot : Bool) (i : Fin 59) (w : Sig) : Prop :=
  if allowNot then w.1.testBit i.val ≠ w.2.testBit i.val
  else w.1.testBit i.val = true ∧ w.2.testBit i.val = false

theorem differs_mono {b : Bool} {i : Fin 59} {w : Sig} (h : differs b i w) :
    differs true i w := by
  cases b
  · simp only [differs, ite_true] at h ⊢
    rw [h.1, h.2]; decide
  · exact h

theorem differs_target (allowNot : Bool) (i : Fin 59) : differs allowNot i target := by
  cases allowNot <;> simp [differs, target, testBit_top, i.isLt]

theorem differs_neg {b : Bool} {i : Fin 59} {a : Sig} (h : differs b i (neg a)) :
    differs true i a := by
  have h' := differs_mono h
  simp only [differs, ite_true, neg, Nat.testBit_xor, testBit_top, i.isLt, decide_true] at h' ⊢
  cases ha1 : a.1.testBit i.val <;> cases ha2 : a.2.testBit i.val <;> simp_all

theorem differs_bin {b d : Bool} {i : Fin 59} {a c : Sig} (h : differs b i (bin d a c)) :
    differs b i a ∨ differs b i c := by
  cases b <;> cases d <;>
    simp only [differs, bin, Bool.false_eq_true, ite_true, ite_false] at h ⊢ <;>
    (try simp only [Nat.testBit_and] at h) <;>
    (try simp only [Nat.testBit_or] at h) <;>
    cases ha1 : a.1.testBit i.val <;> cases ha2 : a.2.testBit i.val <;>
    cases hc1 : c.1.testBit i.val <;> cases hc2 : c.2.testBit i.val <;> simp_all

theorem live_separates (i : Fin 59) {k t : ℕ} {s : Finset Sig} (h : live k t s) :
    ∃ w ∈ s, differs (decide (0 < t)) i w := by
  induction k generalizing t s with
  | zero =>
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨target, by simp, differs_target false i⟩
  | succ k ih =>
    rcases h with skip | ⟨ht, a, ha, _, _, rest, rfl, tail⟩ |
        ⟨a, ha, b, hb, _, _, _, d, _, _, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      have hdt : decide (0 < t) = true := by simp [ht]
      rw [hdt]
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact ⟨a, ha, differs_neg hD⟩
      · exact ⟨w, by simp [hw], differs_mono hD⟩
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases differs_bin hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {k t : ℕ} {s : Finset Sig} (h : live (k+1) t s) :
    (t = 0 ∧ s = {target}) ∨
    (t > 0 ∧ ∃ a ∈ s, proper a ∧ neg a ∉ s ∧
      ∃ rest : Finset Sig, s = insert a rest ∧ live k (t - 1) (insert (neg a) rest)) ∨
    (∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ proper a ∧ proper b ∧
      ∃ d : Bool, proper (bin d a b) ∧ bin d a b ∉ s ∧
        ∃ rest : Finset Sig, s = insert a (insert b rest) ∧ live k t (insert (bin d a b) rest)) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step1 | step2
    · rcases ih skip with done | ⟨ht, a, ha, hpa, hn, r, hs, tail⟩ |
          ⟨a, ha, b, hb, hab, hpa, hpb, d, hpz, hn, r, hs, tail⟩
      · exact Or.inl done
      · exact Or.inr (Or.inl ⟨ht, a, ha, hpa, hn, r, hs, Or.inl tail⟩)
      · exact Or.inr (Or.inr ⟨a, ha, b, hb, hab, hpa, hpb, d, hpz, hn, r, hs, Or.inl tail⟩)
    · exact Or.inr (Or.inl step1)
    · exact Or.inr (Or.inr step2)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with rfl | ha'
    · obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with rfl | hb'
      · obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) ha'
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha' hb'
        refine ⟨x :: r, ?_, (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

theorem testBit_sep (allowNot : Bool) (w : Sig) (i : Fin 59) :
    (sep allowNot w).testBit i.val = true ↔ differs allowNot i w := by
  cases allowNot
  · simp only [sep, differs, Bool.false_eq_true, ite_false, Nat.testBit_and, Nat.testBit_xor,
      testBit_top, i.isLt, decide_true]
    cases w.1.testBit i.val <;> cases w.2.testBit i.val <;> simp
  · simp only [sep, differs, ite_true, Nat.testBit_xor]
    cases w.1.testBit i.val <;> cases w.2.testBit i.val <;> simp

theorem cuts_spec (allowNot : Bool) (ws : List Sig) (i : Fin 59) :
    (cuts allowNot ws).testBit i.val = true ↔ ∃ w ∈ ws, differs allowNot i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep allowNot a ||| cuts allowNot rest).testBit i.val = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih, testBit_sep]
    simp

theorem cuts_full {k t : ℕ} {ws : List Sig} (hv : ∀ w ∈ ws, valid w)
    (h : live k t ws.toFinset) : cuts (decide (0 < t)) ws = top := by
  apply nat_eq_of_testBit (bounded_cuts hv) bounded_top
  intro j hj
  have hw := live_separates ⟨j, hj⟩ h
  have hbit := (cuts_spec (decide (0 < t)) ws ⟨j, hj⟩).mpr (by simpa using hw)
  rw [hbit, testBit_top]
  simp [hj]

theorem recover_kept1 {ws r : List Sig} {a : Sig} {needed : Finset Sig}
    (hp : ws.Perm (a :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a needed) :
    ∃ kept ∈ [r, a :: r], kept.Nodup ∧ kept.toFinset = needed := by
  have har := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a r.toFinset := by
    ext v; simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a := by
    intro v
    have he : v ∈ insert a r.toFinset ↔ v ∈ insert a needed := by rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons] at har
    grind
  by_cases ha : a ∈ needed
  · refine ⟨a :: r, by simp, har, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp, (List.nodup_cons.mp har).2, ?_⟩
    ext v; simp [henne]; grind

def keepChoices (a b : Sig) (r : List Sig) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept2 {ws r : List Sig} {a b : Sig} {needed : Finset Sig}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v; simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : v ∈ insert a (insert b r.toFinset) ↔ v ∈ insert a (insert b needed) := by rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List Sig} (hn : ws.Nodup) (hs : ws.toFinset = {target}) :
    ws = [target] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatchUnary (extra : ℕ) (tNext : ℕ) (ws : List Sig) (next : List Sig → Bool)
    (a : Sig) (rest : List Sig) : Bool :=
  let na := neg a
  if na == zero || na == one || ws.contains na then false
  else
    let allowNext := tNext != 0
    let base := cuts allowNext rest
    let v := sep allowNext na ||| base
    ((v == top) && next (na :: rest)) ||
    ((extra != 0) && (v ||| sep allowNext a == top) && next (na :: a :: rest))

def dispatchBin (extra : ℕ) (allowNot : Bool) (ws : List Sig) (next : List Sig → Bool)
    (a b : Sig) (rest : List Sig) : Bool :=
  let base := cuts allowNot rest
  let sa := sep allowNot a
  let sb := sep allowNot b
  let tryZ (z : Sig) : Bool :=
    if z == zero || z == one || ws.contains z then false
    else
      let v := sep allowNot z ||| base
      ((v == top) && next (z :: rest)) ||
      ((extra != 0) && (((v ||| sa == top) && next (z :: a :: rest)) ||
                        ((v ||| sb == top) && next (z :: b :: rest)))) ||
      ((extra ≥ 2) && (v ||| sa ||| sb == top) && next (z :: a :: b :: rest))
  tryZ (bin false a b) || tryZ (bin true a b)

def search : ℕ → ℕ → List Sig → Bool
  | 0, t, ws => (t == 0) && (ws == [target])
  | k+1, t, ws =>
      ((t == 0) && (ws == [target])) ||
      (if t == 0 then false
       else
         let extra := k + 2 - ws.length - t
         (singles ws).any (fun (a, rest) => dispatchUnary extra (t - 1) ws (search k (t - 1)) a rest)) ||
      (let extra := k + 2 - ws.length - t
       let allowNot := t != 0
       (pairs ws).any (fun (a, b, rest) => dispatchBin extra allowNot ws (search k t) a b rest))

theorem dispatchUnary_complete {k tNext : ℕ} {ws r kept : List Sig} {a : Sig}
    (next : List Sig → Bool)
    (hp : proper (neg a)) (hout : neg a ∉ ws)
    (hk : kept ∈ [r, a :: r])
    (he : k + 2 - ws.length - (tNext + 1) = k + 1 - r.length - (tNext + 1))
    (hlen : kept.length + tNext ≤ k)
    (hc : cuts (decide (0 < tNext)) (neg a :: kept) = top)
    (ht : next (neg a :: kept) = true) :
    dispatchUnary (k + 2 - ws.length - (tNext + 1)) tNext ws next a r = true := by
  have hcond : (neg a == zero || neg a == one || ws.contains (neg a)) = false := by
    simp [hp.1, hp.2, hout]
  dsimp only [dispatchUnary]
  rw [hcond]
  simp only [Bool.false_eq_true, ite_false]
  have hallow : (tNext != 0) = decide (0 < tNext) := by cases tNext <;> rfl
  rw [hallow]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · simp only [cuts, List.foldr_cons] at hc
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
    exact Or.inl ⟨hc, ht⟩
  · simp only [cuts, List.foldr_cons] at hc
    simp only [List.length_cons] at hlen
    have hex : (k + 2 - ws.length - (tNext + 1) != 0) = true := by
      simp only [bne_iff_ne, ne_eq]; omega
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
    refine Or.inr ⟨⟨hex, ?_⟩, ht⟩
    calc (sep (decide (0 < tNext)) (neg a) ||| cuts (decide (0 < tNext)) r) ||| sep (decide (0 < tNext)) a
        = sep (decide (0 < tNext)) (neg a) ||| (sep (decide (0 < tNext)) a ||| cuts (decide (0 < tNext)) r) := by
          ac_rfl
      _ = top := hc

theorem dispatchBin_complete {k t : ℕ} {ws r kept : List Sig} {a b : Sig} {d : Bool}
    (next : List Sig → Bool)
    (hpz : proper (bin d a b)) (hout : bin d a b ∉ ws)
    (hk : kept ∈ keepChoices a b r)
    (he : k + 2 - ws.length - t = k - r.length - t)
    (hlen : kept.length + t ≤ k)
    (hc : cuts (decide (0 < t)) (bin d a b :: kept) = top)
    (ht : next (bin d a b :: kept) = true) :
    dispatchBin (k + 2 - ws.length - t) (t != 0) ws next a b r = true := by
  have hallow : (t != 0) = decide (0 < t) := by cases t <;> rfl
  dsimp only [dispatchBin]
  rw [hallow]
  have hcond : (bin d a b == zero || bin d a b == one || ws.contains (bin d a b)) = false := by
    simp [hpz.1, hpz.2, hout]
  have htry : (if (bin d a b == zero || bin d a b == one || ws.contains (bin d a b)) = true then false else
      let v := sep (decide (0 < t)) (bin d a b) ||| cuts (decide (0 < t)) r
      ((v == top) && next (bin d a b :: r)) ||
      ((k + 2 - ws.length - t != 0) &&
        (((v ||| sep (decide (0 < t)) a == top) && next (bin d a b :: a :: r)) ||
         ((v ||| sep (decide (0 < t)) b == top) && next (bin d a b :: b :: r)))) ||
      ((k + 2 - ws.length - t ≥ 2) &&
        (v ||| sep (decide (0 < t)) a ||| sep (decide (0 < t)) b == top) &&
        next (bin d a b :: a :: b :: r))) = true := by
    rw [hcond]
    simp only [Bool.false_eq_true, ite_false]
    simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;>
      simp only [cuts, List.foldr_cons] at hc <;>
      (try simp only [List.length_cons] at hlen) <;>
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, decide_eq_true_eq]
    · exact Or.inl (Or.inl ⟨hc, ht⟩)
    · refine Or.inl (Or.inr ⟨by omega, Or.inl ⟨?_, ht⟩⟩)
      calc (sep (decide (0 < t)) (bin d a b) ||| cuts (decide (0 < t)) r) ||| sep (decide (0 < t)) a
          = sep (decide (0 < t)) (bin d a b) ||| (sep (decide (0 < t)) a ||| cuts (decide (0 < t)) r) := by ac_rfl
        _ = top := hc
    · refine Or.inl (Or.inr ⟨by omega, Or.inr ⟨?_, ht⟩⟩)
      calc (sep (decide (0 < t)) (bin d a b) ||| cuts (decide (0 < t)) r) ||| sep (decide (0 < t)) b
          = sep (decide (0 < t)) (bin d a b) ||| (sep (decide (0 < t)) b ||| cuts (decide (0 < t)) r) := by ac_rfl
        _ = top := hc
    · refine Or.inr ⟨⟨by omega, ?_⟩, ht⟩
      calc ((sep (decide (0 < t)) (bin d a b) ||| cuts (decide (0 < t)) r) ||| sep (decide (0 < t)) a) ||| sep (decide (0 < t)) b
          = sep (decide (0 < t)) (bin d a b) ||| (sep (decide (0 < t)) a ||| (sep (decide (0 < t)) b ||| cuts (decide (0 < t)) r)) := by ac_rfl
        _ = top := hc
  cases d
  · exact Bool.or_eq_true _ _ |>.mpr (Or.inl htry)
  · exact Bool.or_eq_true _ _ |>.mpr (Or.inr htry)

theorem search_complete (k t : ℕ) (ws : List Sig) (hn : ws.Nodup) (hv : ∀ w ∈ ws, valid w)
    (h : live k t ws.toFinset) : search k t ws = true := by
  induction k generalizing t ws with
  | zero =>
    obtain ⟨rfl, hs⟩ := h
    simp [search, singleton_list hn hs]
  | succ k ih =>
    rcases first_live h with ⟨rfl, hs⟩ |
        ⟨ht, a, ha, hpa, hout, needed, hs, tail⟩ |
        ⟨a, ha, b, hb, hab, hpa, hpb, d, hpz, hout, needed, hs, tail⟩
    · simp [search, singleton_list hn hs]
    · obtain ⟨r, hm, hp⟩ := pick_one (List.mem_toFinset.mp ha)
      obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept1 hp hn hs
      have hznew : neg a ∉ kept := by
        intro hu
        apply hout
        rw [hs]
        exact Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu)
      have hnd : (neg a :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hl : live k (t - 1) (neg a :: kept).toFinset := by
        simpa [hfin] using tail
      have hv_kept : ∀ w ∈ neg a :: kept, valid w := by
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact valid_neg (hv a (List.mem_toFinset.mp ha))
        · apply hv w
          apply List.mem_toFinset.mp
          rw [hs]
          exact Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hw)
      have hcard := live_card hl
      rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hcard
      have hlen_ws : ws.length = r.length + 1 := by
        have := hp.length_eq; simp at this; exact this
      cases t with
      | zero => omega
      | succ t' =>
        simp only [Nat.add_sub_cancel] at hl hcard
        have hrec := ih t' (neg a :: kept) hnd hv_kept hl
        have hcut := cuts_full hv_kept hl
        have hdisp := dispatchUnary_complete (k := k) (tNext := t') (ws := ws) (r := r) (kept := kept)
          (a := a) (search k t') (proper_neg (hv a (List.mem_toFinset.mp ha)) hpa)
          (fun hmem => hout (List.mem_toFinset.mpr hmem)) hk (by omega) (by omega) hcut hrec
        simp only [search, Bool.or_eq_true, Nat.add_eq_zero_iff, one_ne_zero, and_false,
          beq_iff_eq, ite_false, Nat.add_sub_cancel]
        exact Or.inl (Or.inr (List.any_eq_true.mpr ⟨(a, r), hm, hdisp⟩))
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : Sig} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed))
          (ha' : a ∈ ws) (hb' : b ∈ ws)
          (hpz' : proper (bin d a b)) (hout' : bin d a b ∉ ws.toFinset)
          (htail : live k t (insert (bin d a b) needed)) :
          dispatchBin (k + 2 - ws.length - t) (t != 0) ws (search k t) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept2 perm hn hset
        have hznew : bin d a b ∉ kept := by
          intro hu
          apply hout'
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu))
        have hnd : (bin d a b :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live k t (bin d a b :: kept).toFinset := by
          simpa [hfin] using htail
        have hv_kept : ∀ w ∈ bin d a b :: kept, valid w := by
          intro w hw
          rcases List.mem_cons.mp hw with rfl | hw
          · exact valid_bin (hv a ha') (hv b hb')
          · apply hv w
            apply List.mem_toFinset.mp
            rw [hset]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hw))
        have hcard := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hcard
        have hlen_ws : ws.length = r.length + 2 := by
          have := perm.length_eq; simp at this; exact this
        exact dispatchBin_complete (k := k) (t := t) (ws := ws) (r := r) (kept := kept)
          (a := a) (b := b) (d := d) (search k t) hpz'
          (fun hmem => hout' (List.mem_toFinset.mpr hmem)) hk (by omega) (by omega)
          (cuts_full hv_kept hl) (ih t (bin d a b :: kept) hnd hv_kept hl)
      simp only [search, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hpz hout tail⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm])
          (List.mem_toFinset.mp hb) (List.mem_toFinset.mp ha)
          (bin_comm d a b ▸ hpz) (bin_comm d a b ▸ hout) (bin_comm d a b ▸ tail)⟩

private def possible (w : List Sig) (z : Sig) : Bool :=
  z == zero || z == one || w.any (fun u => z == u || z == neg u ||
    w.any (fun v => z == bin false u v || z == bin true u v))

private def bit (k : Fin 118) (z : Sig) : Bool :=
  if k.val < 59 then z.2.testBit k.val else z.1.testBit (k.val - 59)

private theorem read_bit (w : List Sig) (i : ℕ) (k : Fin 118) :
    (w.map (bit k)).getD i false = bit k (w.getD i zero) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit, zero]

private theorem read_wire (w : List Sig) (i : ℕ) : w.getD i zero = zero ∨ w.getD i zero ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem bit_zero (k : Fin 118) : bit k zero = false := by
  unfold bit zero; split <;> simp

private theorem bit_one (k : Fin 118) : bit k one = true := by
  unfold bit one
  by_cases h : k.val < 59
  · simp [h, testBit_top]
  · simp [h, testBit_top, show k.val - 59 < 59 by omega]

private theorem bit_neg (k : Fin 118) (z : Sig) : bit k (neg z) = !(bit k z) := by
  unfold bit neg
  by_cases h : k.val < 59
  · simp [h, Nat.testBit_xor, testBit_top]
  · simp [h, Nat.testBit_xor, testBit_top, show k.val - 59 < 59 by omega]

private theorem bit_and (k : Fin 118) (x y : Sig) : bit k (bin false x y) = (bit k x && bit k y) := by
  unfold bit bin
  split <;> simp [Nat.testBit_and]

private theorem bit_or (k : Fin 118) (x y : Sig) : bit k (bin true x y) = (bit k x || bit k y) := by
  unfold bit bin
  split <;> simp [Nat.testBit_or]

private theorem atom {ws : List Sig} {x : Sig} (hx : x = zero ∨ x ∈ ws) :
    possible ws x ∧ possible ws (neg x) := by
  rcases hx with rfl | hx
  · simp [possible, neg_zero]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

private theorem pair_possible {ws : List Sig} {x y : Sig} (hx : x = zero ∨ x ∈ ws) (hy : y = zero ∨ y ∈ ws) :
    possible ws (bin false x y) ∧ possible ws (bin true x y) := by
  rcases hx with rfl | hx
  · simpa [bin_zero_left] using (show possible ws zero ∧ possible ws y from ⟨by simp [possible], (atom hy).1⟩)
  rcases hy with rfl | hy
  · simpa [bin_zero_right] using (show possible ws zero ∧ possible ws x from ⟨by simp [possible], (atom (.inr hx)).1⟩)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w : List Sig) (hwv : ∀ u ∈ w, valid u) (g : Gate) (hg : legal g) :
    ∃ z, valid z ∧ possible w z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i zero = zero ∨ w.getD i zero ∈ w := read_wire w i
  have vmem (i : ℕ) : valid (w.getD i zero) := by
    rcases mem i with h | h
    · rw [h]; exact valid_zero
    · exact hwv _ h
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨one, valid_one, by simp [possible], by intro k; simp [step, GateOp.eval, bit_one]⟩
    · exact ⟨zero, valid_zero, by simp [possible], by intro k; simp [step, GateOp.eval, bit_zero]⟩
    · exact ⟨one, valid_one, by simp [possible], by intro k; simp [step, GateOp.eval, bit_one]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact ⟨_, vmem i, (atom (mem i)).1, by intro k; simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, vmem i, (atom (mem i)).1, by intro k; simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, valid_neg (vmem i), (atom (mem i)).2, by intro k; simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit_neg]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · exact ⟨_, valid_bin (vmem i) (vmem j), (pair_possible (mem i) (mem j)).1,
            by intro k; simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit_and]⟩
        · exact ⟨_, valid_bin (vmem i) (vmem j), (pair_possible (mem i) (mem j)).2,
            by intro k; simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit_or]⟩
        · exact ⟨_, valid_neg (vmem i), (atom (mem i)).2,
            by intro k; simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit_neg]⟩

def represents (av : Finset Sig) (w : List Sig) : Prop :=
  ∀ u ∈ w, u = zero ∨ u = one ∨ u ∈ av

theorem classify {av : Finset Sig} {ws : List Sig}
    (hav : ∀ u ∈ av, proper u ∧ valid u)
    (hw : represents av ws) {z : Sig} (hz : possible ws z) :
    z = zero ∨ z = one ∨ z ∈ av ∨
      (∃ a ∈ av, proper a ∧ z = neg a) ∨
      (∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ proper a ∧ proper b ∧ ∃ d : Bool, proper z ∧ z = bin d a b) := by
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((rfl | rfl) | ⟨x, hx, (rfl | rfl) | ⟨y, hy, hh⟩⟩)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · rcases hw z hx with rfl | rfl | hxm
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl hxm))
  · rcases hw x hx with rfl | rfl | hxm
    · exact Or.inr (Or.inl neg_zero)
    · exact Or.inl neg_one
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨x, hxm, (hav x hxm).1, rfl⟩)))
  · have binCase (d : Bool) :
        bin d x y = zero ∨ bin d x y = one ∨ bin d x y ∈ av ∨
        (∃ a ∈ av, proper a ∧ bin d x y = neg a) ∨
        (∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ proper a ∧ proper b ∧ ∃ d' : Bool, proper (bin d x y) ∧ bin d x y = bin d' a b) := by
      have hvx : valid x := by
        rcases hw x hx with rfl | rfl | hxm
        · exact valid_zero
        · exact valid_one
        · exact (hav x hxm).2
      have hvy : valid y := by
        rcases hw y hy with rfl | rfl | hym
        · exact valid_zero
        · exact valid_one
        · exact (hav y hym).2
      rcases hw x hx with rfl | rfl | hxm
      · rw [bin_zero_left]; cases d
        · exact Or.inl rfl
        · rcases hw y hy with rfl | rfl | hym
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl hym))
      · rw [bin_one_left d hvy]; cases d
        · rcases hw y hy with rfl | rfl | hym
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl hym))
        · exact Or.inr (Or.inl rfl)
      rcases hw y hy with rfl | rfl | hym
      · rw [bin_zero_right]; cases d
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl hxm))
      · rw [bin_one_right d hvx]; cases d
        · exact Or.inr (Or.inr (Or.inl hxm))
        · exact Or.inr (Or.inl rfl)
      by_cases hxy : x = y
      · subst hxy; rw [bin_self]; exact Or.inr (Or.inr (Or.inl hxm))
      · by_cases hz0 : bin d x y = zero
        · exact Or.inl hz0
        · by_cases hz1 : bin d x y = one
          · exact Or.inr (Or.inl hz1)
          · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨x, hxm, y, hym, hxy, (hav x hxm).1, (hav y hym).1, d, ⟨hz0, hz1⟩, rfl⟩)))
    rcases hh with rfl | rfl
    · exact binCase false
    · exact binCase true

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List Sig) (av : Finset Sig)
    (hwv : ∀ u ∈ w, valid u) (hav : ∀ u ∈ av, proper u ∧ valid u) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k target) :
    build gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hvout : valid (w.getD out zero) := by
      rcases read_wire w out with h | h
      · rw [h]; exact valid_zero
      · exact hwv _ h
    have hval : w.getD out zero = target := by
      apply Prod.ext
      · apply nat_eq_of_testBit hvout.1 valid_target.1
        intro i hi
        have hk := he ⟨59 + i, by omega⟩
        simp only [List.foldl_nil, read_bit, bit, show ¬(59 + i < 59) by omega, ite_false,
          Nat.add_sub_cancel_left] at hk
        exact hk
      · apply nat_eq_of_testBit hvout.2 valid_target.2
        intro i hi
        have hk := he ⟨i, by omega⟩
        simp only [List.foldl_nil, read_bit, bit, hi, ite_true] at hk
        exact hk
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim ((by decide : target ≠ zero) hz)
    · rcases hw target hm with hz | ho | hmem
      · exact False.elim ((by decide : target ≠ zero) hz)
      · exact False.elim ((by decide : target ≠ one) ho)
      · exact hmem
  | cons g gs ih =>
    obtain ⟨z, hvz, hz, hstep⟩ := gate_table w hwv g (hg g (by simp))
    have hwv' : ∀ u ∈ w ++ [z], valid u := by
      intro u hu
      rcases List.mem_append.mp hu with h | h
      · exact hwv u h
      · rw [List.mem_singleton.mp h]; exact hvz
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k target := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = zero ∨ z = one ∨ z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw u old
      · rw [List.mem_singleton.mp fresh]; exact h
    rcases classify hav hw hz with h0 | h1 | hmem | ⟨a, ha, hpa, rfl⟩ |
        ⟨a, ha, b, hb, hab, hpa, hpb, d, hpz, rfl⟩
    · exact Or.inl (fn av hwv' hav (appendOK (.inl h0)) he')
    · exact Or.inl (fn av hwv' hav (appendOK (.inr (.inl h1))) he')
    · exact Or.inl (fn av hwv' hav (appendOK (.inr (.inr hmem))) he')
    · refine Or.inr (Or.inl ⟨a, ha, hpa, fn (insert (neg a) av) hwv' ?_ ?_ he'⟩)
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact ⟨proper_neg (hav a ha).2 hpa, valid_neg (hav a ha).2⟩
        · exact hav u hu
      · intro u hu
        rcases List.mem_append.mp hu with old | fresh
        · rcases hw u old with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Finset.mem_insert_of_mem h))
        · rw [List.mem_singleton.mp fresh]; exact Or.inr (Or.inr (Finset.mem_insert_self _ _))
    · refine Or.inr (Or.inr ⟨a, ha, b, hb, hab, hpa, hpb, d, hpz, fn (insert (bin d a b) av) hwv' ?_ ?_ he'⟩)
      · intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact ⟨hpz, valid_bin (hav a ha).2 (hav b hb).2⟩
        · exact hav u hu
      · intro u hu
        rcases List.mem_append.mp hu with old | fresh
        · rcases hw u old with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Finset.mem_insert_of_mem h))
        · rw [List.mem_singleton.mp fresh]; exact Or.inr (Or.inr (Finset.mem_insert_self _ _))

def graph (x : Fin 6 → Bool) : Bool :=
  (x 0 && x 1) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 3) || (x 2 && x 4)

def assignment (k : Fin 118) (i : Fin 6) : Bool := bit k (rawInputs.getD i.val zero)

theorem rawInputs_valid : ∀ u ∈ rawInputs, valid u := by
  have h : rawInputs.all (fun u => decide (u.1 < 2 ^ 59) && decide (u.2 < 2 ^ 59)) = true := by decide
  intro u hu
  have h' := List.all_eq_true.mp h u hu
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
  exact ⟨bounded_of_lt h'.1, bounded_of_lt h'.2⟩

theorem rawInputs_proper : ∀ u ∈ rawInputs, proper u := by
  have h : rawInputs.all (fun u => (u != zero) && (u != one)) = true := by decide
  intro u hu
  have h' := List.all_eq_true.mp h u hu
  simp only [Bool.and_eq_true, bne_iff_ne] at h'
  exact h'

theorem full_inputs {s : Finset Sig} {k t : ℕ} (hs : s ⊆ rawInputs.toFinset)
    (hr : live k t s) : s = rawInputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  let sites : List (Fin 59) := [0, 1, 2, 3, 4, 5]
  have necessary : rawInputs.all (fun a => sites.any (fun i => rawInputs.all (fun b =>
      (b.1.testBit i.val == b.2.testBit i.val) || b == a))) = true := by decide
  obtain ⟨i, _, hAll⟩ := List.any_eq_true.mp (List.all_eq_true.mp necessary a (List.mem_toFinset.mp ha))
  have hi (b : Sig) (hb : b ∈ rawInputs) (hd : differs (decide (0 < t)) i b) : b = a := by
    have hd' := differs_mono hd
    simp only [differs, ite_true] at hd'
    have hrow := List.all_eq_true.mp hAll b hb
    simp only [Bool.or_eq_true, beq_iff_eq] at hrow
    exact hrow.resolve_left hd'
  obtain ⟨b, hb, hd⟩ := live_separates i hr
  exact hi b (List.mem_toFinset.mp (hs hb)) hd ▸ hb

theorem input_rows (k : Fin 118) : List.ofFn (assignment k) = rawInputs.map (bit k) := by
  rfl

theorem graph_rows (k : Fin 118) : graph (assignment k) = bit k target := by
  let x := fun (i : Nat) => rawInputs.getD i zero
  have hp : (x 0).1 &&& (x 1).1 ||| (x 0).1 &&& (x 3).1 ||| (x 0).1 &&& (x 4).1 ||| (x 0).1 &&& (x 5).1 ||| (x 1).1 &&& (x 3).1 ||| (x 1).1 &&& (x 4).1 ||| (x 1).1 &&& (x 5).1 ||| (x 2).1 &&& (x 3).1 ||| (x 2).1 &&& (x 4).1 = top := by decide
  have hn : (x 0).2 &&& (x 1).2 ||| (x 0).2 &&& (x 3).2 ||| (x 0).2 &&& (x 4).2 ||| (x 0).2 &&& (x 5).2 ||| (x 1).2 &&& (x 3).2 ||| (x 1).2 &&& (x 4).2 ||| (x 1).2 &&& (x 5).2 ||| (x 2).2 &&& (x 3).2 ||| (x 2).2 &&& (x 4).2 = 0 := by decide
  unfold graph assignment bit target
  by_cases hk : k.val < 59
  · simp only [hk, ite_true]
    change _ = (0 : Nat).testBit k.val
    rw [← hn]
    simp only [Nat.testBit_or, Nat.testBit_and]
    rfl
  · simp only [hk, ite_false]
    change _ = top.testBit (k.val - 59)
    rw [← hp]
    simp only [Nat.testBit_or, Nat.testBit_and]
    rfl

theorem rows_eval (C : Circuit) (he : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = graph x) (k : Fin 118) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false = bit k target := by
  rw [← input_rows, ← graph_rows]
  exact he (assignment k)

theorem initial_rep : represents rawInputs.toFinset rawInputs := by
  intro u hu
  exact Or.inr (Or.inr (List.mem_toFinset.mpr hu))

theorem get_build (C : Circuit) (hg : FanInTwo C)
    (he : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = graph x) :
    build C.gates.length rawInputs.toFinset :=
  compile C.gates C.output hg rawInputs rawInputs.toFinset rawInputs_valid
    (fun u hu => ⟨rawInputs_proper u (List.mem_toFinset.mp hu), rawInputs_valid u (List.mem_toFinset.mp hu)⟩)
    initial_rep (rows_eval C he)

theorem extend_live {m n t : ℕ} (le : m ≤ n) (h : live m t rawInputs.toFinset) :
    live n t rawInputs.toFinset := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem check_t0 : search 7 0 rawInputs = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem check_t1 : search 7 1 rawInputs = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem check_t2 : search 7 2 rawInputs = false := by decide +kernel

theorem main_proof (t : ℕ) (h : HasCircuitSize 6 graph t) : 8 ≤ t := by
  by_contra! hs
  obtain ⟨C, hg, hsize, he⟩ := h
  have hl : C.gates.length ≤ 7 := by change C.gates.length ≤ t at hsize; omega
  obtain ⟨kNot, s, hsub, hLive⟩ := compress (get_build C hg he)
  have hsEq := full_inputs hsub hLive
  subst hsEq
  have hLive7 := extend_live hl hLive
  have hcard := live_card hLive7
  have hrawCard : rawInputs.toFinset.card = 6 := by decide
  rw [hrawCard] at hcard
  have hnodup : rawInputs.Nodup := by decide
  have hsearched := search_complete 7 kNot rawInputs hnodup rawInputs_valid hLive7
  have hkLe : kNot ≤ 2 := by omega
  interval_cases kNot
  · exact Bool.noConfusion (check_t0.symm.trans hsearched)
  · exact Bool.noConfusion (check_t1.symm.trans hsearched)
  · exact Bool.noConfusion (check_t2.symm.trans hsearched)

end Aux

theorem checkedCore :
    ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => (x 0 && x 1) || (x 0 && x 3) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 3) || (x 1 && x 4) || (x 1 && x 5) || (x 2 && x 3) || (x 2 && x 4)) t → 8 ≤ t :=
  Aux.main_proof

end Core0

def assignment (a : ℕ) (i : Fin 8) : Bool := a.testBit i.val

def graph0 (x : Fin 8 → Bool) : Bool := (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 6 && x 7)

def graph1 (x : Fin 8 → Bool) : Bool := (x 1 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 6 && x 7)

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma lower0 (t : ℕ) (h : HasCircuitSize 8 graph1 t) : 8 ≤ t := by
  let r : Fin 8 → Fin 6 := ![0, 3, 4, 5, 0, 2, 0, 1]
  have reduced := yn r graph1 t h
  apply Core0.checkedCore t
  convert reduced using 1
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma lower1 (t : ℕ) (h : HasCircuitSize 8 graph0 t) : 11 ≤ t := by
  apply arm_lower (n := 7) (leaf := 4) (inner := 0) (g := graph1)
    (k := 8) _ _ _ _ lower0 h
  · exact ⟨assignment 1, by decide⟩
  · intro b
    cases b
    · exact ⟨assignment 32, by decide⟩
    · exact ⟨assignment 0, by decide⟩
  · exact ⟨assignment 0, assignment 34, by decide⟩
  · intro b
    cases b <;> funext x <;> revert x <;> decide +kernel

def witness : List Gate := [⟨.or, [4, 5]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [5, 10]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [7, 12]⟩, ⟨.and, [6, 13]⟩, ⟨.and, [7, 12]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [15, 17]⟩]

theorem witnessBasis : ∀ g ∈ witness,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨witness, 18⟩ (List.ofFn x) = graph0 x := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem graph_correct : ∀ x : Fin 8 → Bool, graph0 x = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_14184

open PEqualNP.Outside.L_meta_14184 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_14184 :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _oneNot computes
  have h : HasCircuitSize 8 graph0 gates.length :=
    ⟨⟨gates, o⟩, legal, le_rfl, fun x => (computes x).trans (graph_correct x).symm⟩
  have large := lower1 gates.length h
  have hw : witness.length = 11 := rfl
  exact ⟨witness, 18, witnessBasis, by omega, fun x => (witnessCorrect x).trans (graph_correct x)⟩
