import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_14630

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Circuit restrictions adapted from L-meta-9349 and L-meta-9129.

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

-- Adapted from L_meta_5445.
namespace Leaf5445
open PEqualNP.CircuitLowerBounds




def mem (t : ℕ) : List ℕ → Bool
  | [] => false
  | a :: r => Nat.beq t a || mem t r

def pairsWith (a : ℕ) (acc : List ℕ) : List ℕ → List ℕ
  | [] => acc
  | b :: r => (a &&& b) :: (a ||| b) :: pairsWith a acc r


def prs (M : ℕ) : List ℕ → List ℕ
  | [] => [M]
  | a :: r => (M ^^^ a) :: pairsWith a (prs M r) r

def c0 (F : ℕ) (L : List ℕ) : Bool := Nat.beq F 0 || mem F L

def nw (Z acc : List ℕ) : List ℕ → List ℕ
  | [] => acc
  | t :: r => if (Nat.beq t 0 || mem t Z || mem t acc) = true then nw Z acc r else nw Z (t :: acc) r

def orHit (F t : ℕ) : List ℕ → Bool
  | [] => false
  | c :: r => Nat.beq (t ||| c) F || orHit F t r

def andHit (F t : ℕ) : List ℕ → Bool
  | [] => false
  | c :: r => Nat.beq (t &&& c) F || andHit F t r


def newOK (M F t : ℕ) (L : List ℕ) : Bool :=
  Nat.beq F (M ^^^ t) || (Nat.beq (t ||| F) F && orHit F t L) ||
    (Nat.beq (t &&& F) F && andHit F t L)

def can (M F : ℕ) : ℕ → List ℕ → Bool
  | 0, L => c0 F L
  | 1, L => c0 F L || mem F (prs M L)
  | 2, L => c0 F L || mem F (prs M L) || (prs M L).any (fun t => newOK M F t L)
  | k + 3, L => c0 F L || (nw L [] (prs M L)).any (fun t => can M F (k + 2) (t :: L))

theorem mem_iff (t : ℕ) (L : List ℕ) : mem t L = true ↔ t ∈ L := by
  induction L with
  | nil => simp [mem]
  | cons a r ih => simp [mem, ih]

theorem pairsWith_mem (a x : ℕ) (acc r : List ℕ) :
    x ∈ pairsWith a acc r ↔ x ∈ acc ∨ ∃ c ∈ r, x = a &&& c ∨ x = a ||| c := by
  induction r with
  | nil => simp [pairsWith]
  | cons b r ih =>
    simp only [pairsWith, List.mem_cons, ih, or_and_right, exists_or, exists_eq_left]
    constructor
    · rintro (h | h | h | h)
      · exact Or.inr (Or.inl (Or.inl h))
      · exact Or.inr (Or.inl (Or.inr h))
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | (h | h) | h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))

theorem prs_cons (M t x : ℕ) (L : List ℕ) :
    x ∈ prs M (t :: L) ↔ x = M ^^^ t ∨ x ∈ prs M L ∨ ∃ c ∈ L, x = t &&& c ∨ x = t ||| c := by
  simp only [prs, List.mem_cons, pairsWith_mem]

theorem M_mem (M : ℕ) (L : List ℕ) : M ∈ prs M L := by
  induction L with
  | nil => simp [prs]
  | cons a r ih => exact (prs_cons M a M r).2 (Or.inr (Or.inl ih))

theorem not_mem (M a : ℕ) (L : List ℕ) (h : a ∈ L) : M ^^^ a ∈ prs M L := by
  induction L with
  | nil => simp at h
  | cons b r ih =>
    rw [prs_cons]
    rcases List.mem_cons.1 h with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (Or.inl (ih h))

theorem pair_mem (M a b : ℕ) (L : List ℕ) (ha : a ∈ L) (hb : b ∈ L) :
    (a &&& b ∈ L ∨ a &&& b ∈ prs M L) ∧ (a ||| b ∈ L ∨ a ||| b ∈ prs M L) := by
  induction L with
  | nil => simp at ha
  | cons x r ih =>
    rcases List.mem_cons.1 ha with ha1 | ha1 <;> rcases List.mem_cons.1 hb with hb1 | hb1
    · rw [ha1, hb1]
      simp
    · rw [ha1]
      refine ⟨Or.inr ((prs_cons M x _ r).2 (Or.inr (Or.inr ⟨b, hb1, Or.inl rfl⟩))),
        Or.inr ((prs_cons M x _ r).2 (Or.inr (Or.inr ⟨b, hb1, Or.inr rfl⟩)))⟩
    · rw [hb1]
      refine ⟨Or.inr ((prs_cons M x _ r).2 (Or.inr (Or.inr ⟨a, ha1, Or.inl (Nat.land_comm _ _)⟩))),
        Or.inr ((prs_cons M x _ r).2 (Or.inr (Or.inr ⟨a, ha1, Or.inr (Nat.lor_comm _ _)⟩)))⟩
    · obtain ⟨h1, h2⟩ := ih ha1 hb1
      refine ⟨?_, ?_⟩
      · rcases h1 with h1 | h1
        · exact Or.inl (List.mem_cons_of_mem _ h1)
        · exact Or.inr ((prs_cons M x _ r).2 (Or.inr (Or.inl h1)))
      · rcases h2 with h2 | h2
        · exact Or.inl (List.mem_cons_of_mem _ h2)
        · exact Or.inr ((prs_cons M x _ r).2 (Or.inr (Or.inl h2)))

theorem and_in (M a b : ℕ) (L : List ℕ) (ha : a = 0 ∨ a ∈ L) (hb : b = 0 ∨ b ∈ L) :
    a &&& b = 0 ∨ a &&& b ∈ L ∨ a &&& b ∈ prs M L := by
  rcases ha with ha | ha
  · subst ha; simp
  rcases hb with hb | hb
  · subst hb; simp
  exact Or.inr (pair_mem M a b L ha hb).1

theorem or_in (M a b : ℕ) (L : List ℕ) (ha : a = 0 ∨ a ∈ L) (hb : b = 0 ∨ b ∈ L) :
    a ||| b = 0 ∨ a ||| b ∈ L ∨ a ||| b ∈ prs M L := by
  rcases ha with ha | ha
  · subst ha; rw [Nat.zero_or]; tauto
  rcases hb with hb | hb
  · subst hb; rw [Nat.or_zero]; tauto
  exact Or.inr (pair_mem M a b L ha hb).2

theorem not_in (M a : ℕ) (L : List ℕ) (ha : a = 0 ∨ a ∈ L) : M ^^^ a ∈ prs M L := by
  rcases ha with ha | ha
  · subst ha; simpa using M_mem M L
  exact not_mem M a L ha

theorem nw_acc (Z acc ts : List ℕ) (t : ℕ) (h : t ∈ acc) : t ∈ nw Z acc ts := by
  induction ts generalizing acc with
  | nil => simpa [nw] using h
  | cons s r ih =>
    simp only [nw]
    split
    · exact ih acc h
    · exact ih (s :: acc) (List.mem_cons_of_mem _ h)

theorem nw_mem (Z acc ts : List ℕ) (t : ℕ) (h : t ∈ ts) (h0 : t ≠ 0) (hZ : t ∉ Z) :
    t ∈ nw Z acc ts := by
  induction ts generalizing acc with
  | nil => simp at h
  | cons s r ih =>
    simp only [nw]
    rcases List.mem_cons.1 h with h | h
    · subst h
      split
      · rename_i hc
        simp only [Bool.or_eq_true, Nat.beq_eq, mem_iff] at hc
        rcases hc with (hc | hc) | hc
        · exact absurd hc h0
        · exact absurd hc hZ
        · exact nw_acc Z acc r t hc
      · exact nw_acc Z (t :: acc) r t (List.mem_cons_self)
    · split
      · exact ih acc h
      · exact ih (s :: acc) h

theorem orHit_iff (F t : ℕ) (L : List ℕ) : orHit F t L = true ↔ ∃ c ∈ L, t ||| c = F := by
  induction L with
  | nil => simp [orHit]
  | cons c r ih => simp [orHit, ih]

theorem andHit_iff (F t : ℕ) (L : List ℕ) : andHit F t L = true ↔ ∃ c ∈ L, t &&& c = F := by
  induction L with
  | nil => simp [andHit]
  | cons c r ih => simp [andHit, ih]

theorem newOK_complete (M F t : ℕ) (L : List ℕ)
    (h : F = M ^^^ t ∨ ∃ c ∈ L, F = t &&& c ∨ F = t ||| c) : newOK M F t L = true := by
  unfold newOK
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, orHit_iff, andHit_iff]
  rcases h with h | ⟨c, hc, h | h⟩
  · exact Or.inl (Or.inl h)
  · right
    refine ⟨?_, c, hc, h.symm⟩
    subst h
    apply Nat.eq_of_testBit_eq
    intro i
    simp [Nat.testBit_land]
  · left; right
    refine ⟨?_, c, hc, h.symm⟩
    subst h
    apply Nat.eq_of_testBit_eq
    intro i
    simp [Nat.testBit_lor]

theorem newOK_sound (M F t : ℕ) (L : List ℕ) (h : newOK M F t L = true) :
    F ∈ prs M (t :: L) := by
  unfold newOK at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, orHit_iff, andHit_iff] at h
  rw [prs_cons]
  rcases h with (h | ⟨_, c, hc, h⟩) | ⟨_, c, hc, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inr ⟨c, hc, Or.inr h.symm⟩)
  · exact Or.inr (Or.inr ⟨c, hc, Or.inl h.symm⟩)


theorem absorb (M t x : ℕ) (L : List ℕ) (ht : t = 0 ∨ t ∈ L) (hx : x ∈ prs M (t :: L)) :
    x = 0 ∨ x ∈ L ∨ x ∈ prs M L := by
  rcases (prs_cons M t x L).1 hx with h | h | ⟨c, hc, h | h⟩
  · subst h; exact Or.inr (Or.inr (not_in M t L ht))
  · exact Or.inr (Or.inr h)
  · subst h; exact and_in M t c L ht (Or.inr hc)
  · subst h; exact or_in M t c L ht (Or.inr hc)

theorem can_of_c0 (M F k : ℕ) (L : List ℕ) (h : c0 F L = true) : can M F k L = true := by
  rcases k with _ | _ | _ | k <;> simp [can, h]

theorem c0_iff (F : ℕ) (L : List ℕ) : c0 F L = true ↔ F = 0 ∨ F ∈ L := by
  simp [c0, mem_iff]


theorem can_of_prs (M F k : ℕ) (L : List ℕ) (h : F ∈ prs M L) : can M F (k + 1) L = true := by
  rcases k with _ | _ | k
  · simp [can, mem_iff, h]
  · simp [can, mem_iff, h]
  · by_cases hc : c0 F L = true
    · exact can_of_c0 M F _ L hc
    · rw [c0_iff] at hc
      push_neg at hc
      show (c0 F L || (nw L [] (prs M L)).any (fun t => can M F (k + 2) (t :: L))) = true
      simp only [Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨F, nw_mem L [] _ F h hc.1 hc.2, can_of_c0 M F _ _ (by simp [c0, mem_iff])⟩

theorem mono (M F : ℕ) : ∀ (k : ℕ) (L : List ℕ), can M F k L = true → can M F (k + 1) L = true := by
  intro k
  induction k with
  | zero =>
    intro L h
    exact can_of_c0 M F 1 L h
  | succ k ih =>
    intro L h
    rcases k with _ | _ | k
    · 
      simp only [can, Bool.or_eq_true, mem_iff] at h
      rcases h with h | h
      · exact can_of_c0 M F 2 L h
      · exact can_of_prs M F 1 L h
    · 
      simp only [can, Bool.or_eq_true, mem_iff, List.any_eq_true] at h
      rcases h with (h | h) | ⟨t, ht, h⟩
      · exact can_of_c0 M F 3 L h
      · exact can_of_prs M F 2 L h
      · have hF := newOK_sound M F t L h
        have ht' : t ∈ prs M L := ht
        by_cases h0 : t = 0 ∨ t ∈ L
        · rcases absorb M t F L h0 hF with h1 | h1 | h1
          · exact can_of_c0 M F 3 L (by simp [c0, h1])
          · exact can_of_c0 M F 3 L (by simp [c0, mem_iff, h1])
          · exact can_of_prs M F 2 L h1
        · push_neg at h0
          show (c0 F L || (nw L [] (prs M L)).any (fun t => can M F 2 (t :: L))) = true
          simp only [Bool.or_eq_true, List.any_eq_true]
          refine Or.inr ⟨t, nw_mem L [] _ t ht' h0.1 h0.2, ?_⟩
          exact can_of_prs M F 1 (t :: L) hF
    · show (c0 F L || (nw L [] (prs M L)).any (fun t => can M F (k + 1 + 2) (t :: L))) = true
      have h' : (c0 F L || (nw L [] (prs M L)).any (fun t => can M F (k + 2) (t :: L))) = true := h
      simp only [Bool.or_eq_true, List.any_eq_true] at h' ⊢
      rcases h' with h' | ⟨t, ht, h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨t, ht, ih (t :: L) h'⟩


theorem can_step (M F k t : ℕ) (L : List ℕ) (ht : t ∈ prs M L) (h0 : t ≠ 0) (hL : t ∉ L)
    (h : can M F k (t :: L) = true) : can M F (k + 1) L = true := by
  rcases k with _ | _ | k
  · simp only [can, c0_iff, List.mem_cons] at h
    rcases h with h | h | h
    · exact can_of_c0 M F 1 L (by simp [c0, h])
    · subst h; exact can_of_prs M F 0 L ht
    · exact can_of_c0 M F 1 L (by simp [c0, mem_iff, h])
  · simp only [can, Bool.or_eq_true, c0_iff, List.mem_cons, mem_iff] at h
    rcases h with (h | h | h) | h
    · exact can_of_c0 M F 2 L (by simp [c0, h])
    · subst h; exact can_of_prs M F 1 L ht
    · exact can_of_c0 M F 2 L (by simp [c0, mem_iff, h])
    · rcases (prs_cons M t F L).1 h with h1 | h1 | h1
      · show (c0 F L || mem F (prs M L) || (prs M L).any (fun t => newOK M F t L)) = true
        simp only [Bool.or_eq_true, List.any_eq_true]
        exact Or.inr ⟨t, ht, newOK_complete M F t L (Or.inl h1)⟩
      · exact can_of_prs M F 1 L h1
      · show (c0 F L || mem F (prs M L) || (prs M L).any (fun t => newOK M F t L)) = true
        simp only [Bool.or_eq_true, List.any_eq_true]
        exact Or.inr ⟨t, ht, newOK_complete M F t L (Or.inr h1)⟩
  · show (c0 F L || (nw L [] (prs M L)).any (fun t => can M F (k + 2) (t :: L))) = true
    simp only [Bool.or_eq_true, List.any_eq_true]
    exact Or.inr ⟨t, nw_mem L [] _ t ht h0 hL, h⟩


def Inv (N : ℕ) (L : List ℕ) (w : ℕ → List Bool) : Prop :=
  ∀ i, ∃ a, (a = 0 ∨ a ∈ L) ∧ ∀ j < N, a.testBit j = (w j).getD i false

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem eq_of_bits (N a b : ℕ) (ha : a < 2 ^ N) (hb : b < 2 ^ N)
    (h : ∀ j < N, a.testBit j = b.testBit j) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < N
  · exact h i hi
  · have hp : 2 ^ N ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem gate_tab (N M : ℕ) (hM : ∀ j < N, M.testBit j = true) (hMb : M < 2 ^ N)
    (L : List ℕ) (hb : ∀ a ∈ L, a < 2 ^ N) (w : ℕ → List Bool) (hI : Inv N L w) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) :
    ∃ t, (t = 0 ∨ t ∈ L ∨ t ∈ prs M L) ∧ t < 2 ^ N ∧
      ∀ j < N, t.testBit j = g.op.eval (g.inputs.map fun i => (w j).getD i false) := by
  have hz : (0 : ℕ) < 2 ^ N := Nat.two_pow_pos N
  have hbd : ∀ a, (a = 0 ∨ a ∈ L) → a < 2 ^ N := by
    intro a ha
    rcases ha with ha | ha
    · rw [ha]; exact hz
    · exact hb a ha
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with hop | hop | hop <;> subst hop
    · exact ⟨M, Or.inr (Or.inr (M_mem M L)), hMb, fun j hj => by simp [GateOp.eval, hM j hj]⟩
    · exact ⟨0, Or.inl rfl, hz, fun j _ => by simp [GateOp.eval]⟩
    · exact ⟨M, Or.inr (Or.inr (M_mem M L)), hMb, fun j hj => by simp [GateOp.eval, hM j hj]⟩
  | [i], _ =>
    obtain ⟨a, ha, haw⟩ := hI i
    rcases hop with hop | hop | hop <;> subst hop
    · exact ⟨a, by tauto, hbd a ha, fun j hj => by simp [GateOp.eval, haw j hj]⟩
    · exact ⟨a, by tauto, hbd a ha, fun j hj => by simp [GateOp.eval, haw j hj]⟩
    · refine ⟨M ^^^ a, Or.inr (Or.inr (not_in M a L ha)), Nat.xor_lt_two_pow hMb (hbd a ha),
        fun j hj => ?_⟩
      simp [GateOp.eval, Nat.testBit_xor, haw j hj, hM j hj]
  | [i1, i2], _ =>
    obtain ⟨a, ha, haw⟩ := hI i1
    obtain ⟨b, hb', hbw⟩ := hI i2
    rcases hop with hop | hop | hop <;> subst hop
    · refine ⟨a &&& b, and_in M a b L ha hb', Nat.and_lt_two_pow _ (hbd b hb'), fun j hj => ?_⟩
      simp [GateOp.eval, Nat.testBit_land, haw j hj, hbw j hj]
    · refine ⟨a ||| b, or_in M a b L ha hb', Nat.or_lt_two_pow (hbd a ha) (hbd b hb'),
        fun j hj => ?_⟩
      simp [GateOp.eval, Nat.testBit_lor, haw j hj, hbw j hj]
    · refine ⟨M ^^^ a, Or.inr (Or.inr (not_in M a L ha)), Nat.xor_lt_two_pow hMb (hbd a ha),
        fun j hj => ?_⟩
      simp [GateOp.eval, Nat.testBit_xor, haw j hj, hM j hj]
  | _ :: _ :: _ :: _, h => simp at h

theorem getD_snoc (l : List Bool) (v : Bool) (i : ℕ) :
    (l ++ [v]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then v else false := by
  simp only [List.getD_eq_getElem?_getD]
  rcases lt_trichotomy i l.length with h | h | h
  · rw [if_pos h, List.getElem?_append_left h]
  · subst h
    simp
  · rw [if_neg (by omega), if_neg (by omega), List.getElem?_eq_none (by simp; omega)]
    rfl

theorem inv_snoc (N m : ℕ) (L L' : List ℕ) (w : ℕ → List Bool) (v : ℕ → Bool) (t : ℕ)
    (hw : ∀ j, (w j).length = m) (hI : Inv N L w) (hLL : ∀ a ∈ L, a ∈ L')
    (ht : t = 0 ∨ t ∈ L') (htv : ∀ j < N, t.testBit j = v j) :
    Inv N L' (fun j => w j ++ [v j]) := by
  intro i
  by_cases h1 : i < m
  · obtain ⟨a, ha, haw⟩ := hI i
    refine ⟨a, ?_, fun j hj => ?_⟩
    · rcases ha with ha | ha
      · exact Or.inl ha
      · exact Or.inr (hLL a ha)
    · simp only [getD_snoc, hw j, if_pos h1]
      exact haw j hj
  · by_cases h2 : i = m
    · refine ⟨t, ht, fun j hj => ?_⟩
      simp only [getD_snoc, hw j, if_neg h1, if_pos h2]
      exact htv j hj
    · refine ⟨0, Or.inl rfl, fun j hj => ?_⟩
      simp only [getD_snoc, hw j, if_neg h1, if_neg h2, Nat.zero_testBit]

theorem sound (N M F : ℕ) (hM : ∀ j < N, M.testBit j = true) (hMb : M < 2 ^ N)
    (hF : F < 2 ^ N) :
    ∀ (gs : List Gate) (k m : ℕ) (L : List ℕ) (w : ℕ → List Bool),
      (∀ a ∈ L, a < 2 ^ N) → (∀ j, (w j).length = m) → Inv N L w →
      (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g.inputs.length ≤ 2) →
      gs.length ≤ k → ∀ o : ℕ,
      (∀ j < N, (gs.foldl stp (w j)).getD o false = F.testBit j) → can M F k L = true := by
  intro gs
  induction gs with
  | nil =>
    intro k m L w hb _ hI _ _ o ho
    obtain ⟨a, ha, haw⟩ := hI o
    have hab : a < 2 ^ N := by
      rcases ha with ha | ha
      · rw [ha]; exact Nat.two_pow_pos N
      · exact hb a ha
    have hEq : a = F := eq_of_bits N a F hab hF (fun j hj => by
      rw [haw j hj]; exact ho j hj)
    exact can_of_c0 M F k L (by rw [c0_iff, ← hEq]; tauto)
  | cons g gs ih =>
    intro k m L w hb hw hI hg hk o ho
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have hk' : gs.length ≤ k := by simp at hk; omega
    obtain ⟨t, htm, htb, htv⟩ :=
      gate_tab N M hM hMb L hb w hI g (hg g List.mem_cons_self).1 (hg g List.mem_cons_self).2
    have hw' : ∀ j, (stp (w j) g).length = m + 1 := by
      intro j; simp [stp, hw j]
    have hg' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
        g'.inputs.length ≤ 2 := fun g' h' => hg g' (List.mem_cons_of_mem _ h')
    have ho' : ∀ j < N, (gs.foldl stp (stp (w j) g)).getD o false = F.testBit j := ho
    by_cases hold : t = 0 ∨ t ∈ L
    · have hI' : Inv N L (fun j => stp (w j) g) :=
        inv_snoc N m L L w _ t hw hI (fun a h => h) hold htv
      exact mono M F k L (ih k (m + 1) L _ hb hw' hI' hg' hk' o ho')
    · push_neg at hold
      have htp : t ∈ prs M L := by
        rcases htm with h | h | h
        · exact absurd h hold.1
        · exact absurd h hold.2
        · exact h
      have hI' : Inv N (t :: L) (fun j => stp (w j) g) :=
        inv_snoc N m L (t :: L) w _ t hw hI (fun a h => List.mem_cons_of_mem _ h)
          (Or.inr List.mem_cons_self) htv
      have hb' : ∀ a ∈ t :: L, a < 2 ^ N := by
        intro a h
        rcases List.mem_cons.1 h with h | h
        · rw [h]; exact htb
        · exact hb a h
      exact can_step M F k t L htp hold.1 hold.2 (ih k (m + 1) (t :: L) _ hb' hw' hI' hg' hk' o ho')

theorem ofFn_getD (n : ℕ) (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]



theorem main_gen (n N M F K : ℕ) (L0 : List ℕ) (f : (Fin n → Bool) → Bool)
    (hM : ∀ j < N, M.testBit j = true) (hMb : M < 2 ^ N) (hF : F < 2 ^ N)
    (hL0 : ∀ a ∈ L0, a < 2 ^ N)
    (hin : ∀ i < n, ∃ a ∈ L0, ∀ j < N, a.testBit j = j.testBit i)
    (hf : ∀ j < N, f (fun i => j.testBit i) = F.testBit j)
    (hs : can M F K L0 = false) :
    ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize n f t → K + 1 ≤ t := by
  intro t ⟨C, hfan, hsize, heval⟩
  by_contra hlt
  have hk : C.gates.length ≤ K := by
    have : C.size = C.gates.length := rfl
    omega
  have hI : Inv N L0 (fun j => List.ofFn (fun i : Fin n => j.testBit i)) := by
    intro i
    by_cases hi : i < n
    · obtain ⟨a, ha, haj⟩ := hin i hi
      refine ⟨a, Or.inr ha, fun j hj => ?_⟩
      rw [ofFn_getD, dif_pos hi]
      exact haj j hj
    · refine ⟨0, Or.inl rfl, fun j _ => ?_⟩
      rw [ofFn_getD, dif_neg hi, Nat.zero_testBit]
  have ho : ∀ j < N, (C.gates.foldl stp (List.ofFn (fun i : Fin n => j.testBit i))).getD
      C.output false = F.testBit j := by
    intro j hj
    rw [← hf j hj, ← heval]
    rfl
  have := sound N M F hM hMb hF C.gates K n L0 _ hL0 (fun j => by simp) hI hfan hk C.output ho
  rw [hs] at this
  exact absurd this (by decide)

theorem search : can 0xFFFF 0xEEE8 4 [0xFF00, 0xF0F0, 0xCCCC, 0xAAAA] = false := by
  decide +kernel

theorem final : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 3)) t → 5 ≤ t :=
  main_gen 4 16 0xFFFF 0xEEE8 4 [0xFF00, 0xF0F0, 0xCCCC, 0xAAAA] _ (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) search

theorem checkedLeaf : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) || (x 1 && x 2) || (x 1 && x 3)) t → 5 ≤ t := by
  intro t h
  exact final t h
end Leaf5445


def assignment (a : ℕ) (i : Fin 8) : Bool := a.testBit i.val

def graph0 (x : Fin 8 → Bool) : Bool := (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 4 && x 7) || (x 5 && x 7)

def graph1 (x : Fin 8 → Bool) : Bool := (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 5 && x 7)

def graph2 (x : Fin 8 → Bool) : Bool := (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 7) || (x 1 && x 7) || (x 5 && x 7)

def graph3 (x : Fin 8 → Bool) : Bool := (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 7) || (x 1 && x 7) || (x 5 && x 7)

lemma lower0 (t : ℕ) (h : HasCircuitSize 8 graph3 t) : 5 ≤ t := by
  let r : Fin 8 → Fin 4 := ![2, 3, 0, 0, 0, 0, 0, 1]
  have reduced := yn r graph3 t h
  apply Leaf5445.checkedLeaf t
  convert reduced using 1
  decide +kernel

lemma lower1 (t : ℕ) (h : HasCircuitSize 8 graph2 t) : 6 ≤ t := by
  have eq : fix graph2 2 false = graph3 := by
    funext x
    simp [fix, Function.update, graph2, graph3] <;> simp only [Bool.eq_iff_iff, Bool.and_eq_true, Bool.or_eq_true] <;> tauto
  have nc : nonconstant (fix graph2 2 false) := eq.symm ▸ ⟨assignment 0, assignment 33, by decide⟩
  obtain ⟨s, hs, reduced⟩ := q70 7 graph2 2 false t ⟨assignment 32, by decide⟩ nc h
  have bound := lower0 s (eq ▸ reduced)
  omega

lemma lower2 (t : ℕ) (h : HasCircuitSize 8 graph1 t) : 9 ≤ t := by
  apply arm_lower (n := 7) (leaf := 3) (inner := 6) (g := graph2)
    (k := 6) _ _ _ _ lower1 h
  · exact ⟨assignment 64, by decide⟩
  · intro b
    cases b
    · exact ⟨assignment 1, by decide⟩
    · exact ⟨assignment 0, by decide⟩
  · exact ⟨assignment 0, assignment 33, by decide⟩
  · intro b
    cases b <;> funext x <;> simp [fix, Function.update, graph1, graph2]
      <;> simp only [Bool.eq_iff_iff, Bool.and_eq_true, Bool.or_eq_true] <;> tauto

lemma lower3 (t : ℕ) (h : HasCircuitSize 8 graph0 t) : 10 ≤ t := by
  have eq : fix graph0 4 false = graph1 := by
    funext x
    simp [fix, Function.update, graph0, graph1] <;> simp only [Bool.eq_iff_iff, Bool.and_eq_true, Bool.or_eq_true] <;> tauto
  have nc : nonconstant (fix graph0 4 false) := eq.symm ▸ ⟨assignment 0, assignment 33, by decide⟩
  obtain ⟨s, hs, reduced⟩ := q70 7 graph0 4 false t ⟨assignment 128, by decide⟩ nc h
  have bound := lower2 s (eq ▸ reduced)
  omega

def witness : List Gate := [⟨.or, [0, 1]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [5, 10]⟩, ⟨.or, [3, 9]⟩, ⟨.and, [6, 12]⟩, ⟨.or, [4, 8]⟩, ⟨.and, [7, 14]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [15, 16]⟩]

theorem witnessBasis : ∀ g ∈ witness,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool,
    Circuit.eval ⟨witness, 17⟩ (List.ofFn x) = graph0 x := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem graph_correct : ∀ x : Fin 8 → Bool, graph0 x = decide (∃ i < ([0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_14630

open PEqualNP.Outside.L_meta_14630 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_14630 :
∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 0, 7, 1, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _oneNot computes
  have h : HasCircuitSize 8 graph0 gates.length :=
    ⟨⟨gates, o⟩, legal, le_rfl, fun x => (computes x).trans (graph_correct x).symm⟩
  have large := lower3 gates.length h
  have hw : witness.length = 10 := rfl
  exact ⟨witness, 17, witnessBasis, by omega, fun x => (witnessCorrect x).trans (graph_correct x)⟩
