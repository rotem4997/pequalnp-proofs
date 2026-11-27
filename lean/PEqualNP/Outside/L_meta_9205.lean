import PEqualNP.Defs

-- Circuit restriction proofs adapted from the L-meta-9129 contributors.
namespace PEqualNP.Outside.L_meta_9205

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

-- The five-cycle certificate is adapted from L-meta-6571 and L-meta-527.
-- Each bit records the value of a wire on one of the 32 inputs of the five-cycle.

def Next527 (w : Finset (BitVec 32)) (z : BitVec 32) : Prop :=
  (∃ a ∈ w, z = ~~~a) ∨
    (∃ a ∈ w, ∃ b ∈ w, a ≠ b ∧ (z = a &&& b ∨ z = a ||| b))

def Reach527 : Finset (BitVec 32) → ℕ → BitVec 32 → Prop
  | w, 0, t => t ∈ w
  | w, j + 1, t => t ∈ w ∨ ∃ z, z ∉ w ∧ z ≠ 0 ∧
      z ≠ ~~~(0 : BitVec 32) ∧ Next527 w z ∧ Reach527 (insert z w) j t

def cand527 (ws : List (BitVec 32)) : List (BitVec 32) :=
  let raw := ws.map (fun a => ~~~a) ++
    ws.flatMap (fun a => ws.flatMap fun b => [a &&& b, a ||| b])
  raw.eraseDups.filter fun z => !(ws.contains z) && z != 0 && z != ~~~(0 : BitVec 32)

theorem cand_complete527 {ws : List (BitVec 32)} {z : BitVec 32}
    (h : Next527 ws.toFinset z) (hn : z ∉ ws)
    (h0 : z ≠ 0) (h1 : z ≠ ~~~(0 : BitVec 32)) : z ∈ cand527 ws := by
  simp only [cand527, List.mem_filter, List.mem_eraseDups, List.mem_append,
    List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  refine ⟨?_, by simp [hn]; exact ⟨h0, h1⟩⟩
  rcases h with ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, _, hab | hab⟩
  · exact Or.inl ⟨a, List.mem_toFinset.mp ha, rfl⟩
  · exact Or.inr ⟨a, List.mem_toFinset.mp ha, b, List.mem_toFinset.mp hb, Or.inl hab⟩
  · exact Or.inr ⟨a, List.mem_toFinset.mp ha, b, List.mem_toFinset.mp hb, Or.inr hab⟩

theorem next_mono527 {w v : Finset (BitVec 32)} {z : BitVec 32}
    (hw : w ⊆ v) (h : Next527 w z) : Next527 v z := by
  rcases h with ⟨a, ha, hz⟩ | ⟨a, ha, b, hb, hab, hz⟩
  · exact Or.inl ⟨a, hw ha, hz⟩
  · exact Or.inr ⟨a, hw ha, b, hw hb, hab, hz⟩

theorem reach_succ527 {w : Finset (BitVec 32)} {j : ℕ} {t : BitVec 32}
    (h : Reach527 w j t) : Reach527 w (j+1) t := by
  induction j generalizing w with
  | zero => exact Or.inl h
  | succ j ih =>
    rcases h with ht | ⟨z, hzw, hz0, hz1, hnext, hr⟩
    · exact Or.inl ht
    · exact Or.inr ⟨z, hzw, hz0, hz1, hnext, ih hr⟩

theorem reach_mono527 {w v : Finset (BitVec 32)} {j : ℕ} {t : BitVec 32}
    (hw : w ⊆ v) (h : Reach527 w j t) : Reach527 v j t := by
  induction j generalizing w v with
  | zero => exact hw h
  | succ j ih =>
    rcases h with ht | ⟨z, hzw, hz0, hz1, hnext, hr⟩
    · exact Or.inl (hw ht)
    · by_cases hzv : z ∈ v
      · exact reach_succ527 (ih (Finset.insert_subset hzv hw) hr)
      · exact Or.inr ⟨z, hzv, hz0, hz1, next_mono527 hw hnext,
          ih (Finset.insert_subset_insert _ hw) hr⟩

private theorem next_small527 {w : Finset (BitVec 32)} {z : BitVec 32}
    (h : Next527 w z) : ∃ p ⊆ w, p.card ≤ 2 ∧ Next527 p z := by
  rcases h with ⟨a, ha, hz⟩ | ⟨a, ha, b, hb, hab, hz⟩
  · exact ⟨{a}, by simpa, by simp, Or.inl ⟨a, by simp, hz⟩⟩
  · refine ⟨{a,b}, ?_, ?_, Or.inr ⟨a, by simp, b, by simp, hab, hz⟩⟩
    · exact Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb)
    · simp [hab]

theorem reach_support527 {w : Finset (BitVec 32)} {k : ℕ} {t : BitVec 32}
    (h : Reach527 w k t) : ∃ u ⊆ w, u.card ≤ k+1 ∧ Reach527 u k t := by
  induction k generalizing w with
  | zero => exact ⟨{t}, Finset.singleton_subset_iff.mpr h, by simp, Finset.mem_singleton_self _⟩
  | succ j ih =>
    rcases h with ht | ⟨z, hzw, hz0, hz1, hn, hr⟩
    · exact ⟨{t}, Finset.singleton_subset_iff.mpr ht, by simp, Or.inl (Finset.mem_singleton_self _)⟩
    · obtain ⟨u, hus, hcard, hu⟩ := ih hr
      by_cases hzu : z ∈ u
      · obtain ⟨p, hpw, hpcard, hpnext⟩ := next_small527 hn
        let v := u.erase z ∪ p
        have hvw : v ⊆ w := by
          intro x hx
          rcases Finset.mem_union.mp hx with he | hp
          · obtain ⟨hne,hxu⟩ := Finset.mem_erase.mp he
            exact (Finset.mem_insert.mp (hus hxu)).resolve_left hne
          · exact hpw hp
        have huv : u ⊆ insert z v := by
          intro x hx
          by_cases he : x = z
          · exact Finset.mem_insert.mpr (Or.inl he)
          · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he,hx⟩)))
        have hvsize := Finset.card_union_le (u.erase z) p
        have herase := Finset.card_erase_of_mem hzu
        have hpositive : 0 < u.card := Finset.card_pos.mpr ⟨z,hzu⟩
        refine ⟨v, hvw, ?_, Or.inr ⟨z, fun hz => hzw (hvw hz), hz0, hz1,
            next_mono527 (Finset.subset_union_right : p ⊆ v) hpnext, reach_mono527 huv hu⟩⟩
        dsimp [v]
        omega
      · refine ⟨u, ?_, by omega, reach_succ527 hu⟩
        intro x hx
        rcases Finset.mem_insert.mp (hus hx) with he | hw
        · exact False.elim (hzu (he ▸ hx))
        · exact hw

theorem reach_row527 {w : Finset (BitVec 32)} {k : ℕ} {t : BitVec 32}
    (h : Reach527 w k t) (i j : Fin 32)
    (eqw : ∀ a ∈ w, a.getLsbD i.val = a.getLsbD j.val) :
    t.getLsbD i.val = t.getLsbD j.val := by
  induction k generalizing w with
  | zero => exact eqw t h
  | succ k ih =>
    rcases h with ht | ⟨z, _, _, _, hn, hr⟩
    · exact eqw t ht
    · apply ih hr
      intro wire hwire
      rcases Finset.mem_insert.mp hwire with rfl | hw
      · rcases hn with ⟨a, ha, hz⟩ | ⟨a, ha, b, hb, _, hz | hz⟩
        · simp only [hz, BitVec.getLsbD_not, i.isLt, j.isLt, eqw a ha]
        · simp only [hz, BitVec.getLsbD_and, eqw a ha, eqw b hb]
        · simp only [hz, BitVec.getLsbD_or, eqw a ha, eqw b hb]
      · exact eqw wire hw

theorem reach_advance527 {ws : List (BitVec 32)} {k : ℕ} {t : BitVec 32}
    (h : Reach527 ws.toFinset (k+1) t) (hw : ws.Nodup) (ht : t ∉ ws) :
    ∃ z ∈ cand527 ws, ∃ us ∈ List.sublistsLen (min (k+1) (z::ws).length) (z::ws),
      us.Nodup ∧ Reach527 us.toFinset k t := by
  rcases h with hnow | ⟨z, hzw, hz0, hz1, hn, hr⟩
  · exact False.elim (ht (List.mem_toFinset.mp hnow))
  · have hz : z ∉ ws := by simpa using hzw
    have hw' : (z :: ws).Nodup := List.nodup_cons.mpr ⟨hz,hw⟩
    have hr' : Reach527 (z :: ws).toFinset k t := by simpa using hr
    obtain ⟨u, hsub, hsmall, hur⟩ := reach_support527 hr'
    let size := min (k+1) (z::ws).length
    have hle : u.card ≤ size :=
      le_min hsmall ((Finset.card_le_card hsub).trans_eq (List.toFinset_card_of_nodup hw'))
    have hlen : size ≤ (z::ws).toFinset.card := by
      rw [List.toFinset_card_of_nodup hw']
      exact min_le_right _ _
    obtain ⟨v, huv, hvw, hvcard⟩ := Finset.exists_subsuperset_card_eq hsub hle hlen
    let us := (z::ws).filter (fun a => a ∈ v)
    have hsubl : List.Sublist us (z::ws) := List.filter_sublist
    have hus : us.toFinset = v := by
      ext a
      simp only [us, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      exact ⟨And.right, fun ha => ⟨List.mem_toFinset.mp (hvw ha),ha⟩⟩
    have hd : us.Nodup := hsubl.nodup hw'
    have huslen : us.length = size := by
      rw [← List.toFinset_card_of_nodup hd, hus]
      exact hvcard
    have husreach : Reach527 us.toFinset k t := by
      rw [hus]
      exact reach_mono527 huv hur
    exact ⟨z, cand_complete527 hn hz hz0 hz1, us,
      List.mem_sublistsLen.mpr ⟨hsubl,huslen⟩, hd, husreach⟩

-- A circuit with k gates can depend on at most k + 1 wires already present.
-- Each layer lists wire sets covering the possibilities that still distinguish
-- inputs with different outputs. The last layer has no successor.

def root527 : List (BitVec 32) := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]
def goal527 : BitVec 32 := 0xffeaf8c8

def layer1527 : List (List (BitVec 32)) :=
  [[0x0000ffff, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0x00ff00ff, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0x0f0f0f0f, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0x33333333, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0x55555555, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0x88888888, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xa0a0a0a0, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaa00aa00, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaa0000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xc0c0c0c0, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcc00cc00, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccc0000, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xeeeeeeee, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf000f000, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f00000, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xfafafafa, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xfcfcfcfc, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff000000, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffaaffaa, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffccffcc, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xfff0fff0, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000, 0xffffaaaa],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000, 0xffffcccc],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000, 0xfffff0f0],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000, 0xffffff00]]

def layer2527 : List (List (BitVec 32)) :=
  [[0x0000ffff, 0x00ff00ff, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0],
   [0x0000ffff, 0x0f0f0f0f, 0xaaaaaaaa, 0xcccccccc, 0xff00ff00],
   [0x0000ffff, 0x33333333, 0xaaaaaaaa, 0xf0f0f0f0, 0xff00ff00],
   [0x0000ffff, 0x55555555, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00],
   [0x0000ffff, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00],
   [0x00ff00ff, 0x0f0f0f0f, 0xaaaaaaaa, 0xcccccccc, 0xffff0000],
   [0x00ff00ff, 0x33333333, 0xaaaaaaaa, 0xf0f0f0f0, 0xffff0000],
   [0x00ff00ff, 0x55555555, 0xcccccccc, 0xf0f0f0f0, 0xffff0000],
   [0x00ff00ff, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xffff0000],
   [0x0f0f0f0f, 0x33333333, 0xaaaaaaaa, 0xff00ff00, 0xffff0000],
   [0x0f0f0f0f, 0x55555555, 0xcccccccc, 0xff00ff00, 0xffff0000],
   [0x0f0f0f0f, 0xaaaaaaaa, 0xcccccccc, 0xff00ff00, 0xffff0000],
   [0x33333333, 0x55555555, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0x33333333, 0xaaaaaaaa, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0x55555555, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaa8888, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xc8c8c8c8, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0c0f0c0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00f000, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffaa0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff8888],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffffc0c0],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xfffff000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff88ff88, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xffaaff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xffc0ffc0, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xf8f8f8f8, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xfafaf0f0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xcccccccc, 0xff00ff00, 0xfff0f0f0, 0xffff0000],
   [0xaaaaaaaa, 0xeeeecccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xf0f0f0f0, 0xfcccfccc, 0xff00ff00, 0xffff0000],
   [0xaaaaaaaa, 0xf0f0f0f0, 0xff00ff00, 0xffcccccc, 0xffff0000],
   [0xcccccccc, 0xeaeaeaea, 0xf0f0f0f0, 0xff00ff00, 0xffff0000],
   [0xcccccccc, 0xf0f0f0f0, 0xfaaafaaa, 0xff00ff00, 0xffff0000],
   [0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffaaaaaa, 0xffff0000]]

def separatingRows : List (Fin 32 × Fin 32) :=
  [(11,9),(13,5),(21,20),(22,18),(26,10),(11,10),(21,5),(22,20),(13,9),(26,18),
   (3,5),(3,18),(6,10),(12,20),(6,4),(12,8),(3,2),(3,9),(3,10),(6,5),
   (6,18),(6,20),(12,4),(12,9),(17,1),(3,1),(6,2),(7,5),(14,10),(17,16),
   (19,18),(24,8),(24,16),(25,9),(28,20)]

def separates527 (ws : List (BitVec 32)) : Bool :=
  separatingRows.all fun p => ws.any fun a => a.getLsbD p.1.val != a.getLsbD p.2.val

theorem reach_separates527 {ws : List (BitVec 32)} {k : Nat}
    (h : Reach527 ws.toFinset k goal527) : separates527 ws = true := by
  have different : separatingRows.all
      (fun (i,j) => goal527.getLsbD i.val != goal527.getLsbD j.val) = true := by decide
  apply List.all_eq_true.mpr
  intro ⟨i,j⟩ hp
  by_contra hn
  have eq : goal527.getLsbD i.val = goal527.getLsbD j.val := by
    apply reach_row527 h i j
    intro a ha
    by_contra hne
    apply hn
    exact List.any_eq_true.mpr
      ⟨a, List.mem_toFinset.mp ha, by simpa only [bne_iff_ne] using hne⟩
  have diff := List.all_eq_true.mp different (i,j) hp
  change (goal527.getLsbD i.val != goal527.getLsbD j.val) = true at diff
  rw [eq] at diff
  exact (bne_iff_ne.mp diff) rfl

def checkLayer527 (w : List (BitVec 32)) (k : ℕ) (layers : List (List (BitVec 32))) : Bool :=
  !w.contains goal527 && (cand527 w).all fun z =>
    ((z :: w).sublistsLen (min (k+1) (z :: w).length)).all fun u =>
      !separates527 u || layers.any (fun v => u.all (fun a => v.contains a))

private def matchesRows (p : Fin 32 × Fin 32) (a : BitVec 32) : Bool :=
  a.getLsbD p.1.val == a.getLsbD p.2.val

private def coveredByLayer (layers : List (List (BitVec 32))) (u : List (BitVec 32)) : Bool :=
  layers.any (fun v => u.all (fun a => v.contains a))

-- For a fixed subset of old wires, each matching row pair rules out all
-- candidates that also match on that pair.
private def checkCandidates (layers : List (List (BitVec 32))) (u : List (BitVec 32)) :
    List (Fin 32 × Fin 32) → List (BitVec 32) → Bool
  | [], zs => zs.all fun z => coveredByLayer layers (z :: u)
  | _, [] => true
  | p :: ps, z :: zs =>
    if u.all (matchesRows p) then
      checkCandidates layers u ps ((z :: zs).filter fun a => !(matchesRows p a))
    else
      checkCandidates layers u ps (z :: zs)

private theorem checkCandidates_sound {layers : List (List (BitVec 32))}
    {u : List (BitVec 32)} {z : BitVec 32} {rows : List (Fin 32 × Fin 32)}
    (hrows : ∀ p ∈ rows, p ∈ separatingRows) {zs : List (BitVec 32)} (hz : z ∈ zs)
    (h : checkCandidates layers u rows zs = true) (hs : separates527 (z :: u) = true) :
    coveredByLayer layers (z :: u) = true := by
  induction rows generalizing zs with
  | nil => exact List.all_eq_true.mp h z hz
  | cons p ps ih =>
    have htail : ∀ q ∈ ps, q ∈ separatingRows :=
      fun q hq => hrows q (List.mem_cons_of_mem p hq)
    cases zs with
    | nil => simp at hz
    | cons a tail =>
      by_cases hp : u.all (matchesRows p) = true
      · simp only [checkCandidates, hp, ite_true] at h
        apply ih htail _ h
        refine List.mem_filter.mpr ⟨hz, ?_⟩
        have hnot : matchesRows p z ≠ true := by
          intro hm
          have hd := List.all_eq_true.mp hs p (hrows p List.mem_cons_self)
          obtain ⟨b, hb, hne⟩ := List.any_eq_true.mp hd
          have he : matchesRows p b = true := by
            rcases List.mem_cons.mp hb with rfl | hb
            · exact hm
            · exact List.all_eq_true.mp hp b hb
          exact (bne_iff_ne.mp hne) (beq_iff_eq.mp he)
        rw [Bool.eq_false_iff.mpr hnot]
        rfl
      · simp only [checkCandidates, hp] at h
        exact ih htail hz h

private def fastCheck (w : List (BitVec 32)) (k : ℕ)
    (layers : List (List (BitVec 32))) : Bool :=
  let n := min k w.length
  !w.contains goal527 &&
    ((w.sublistsLen (n+1)).all (fun u => !separates527 u || coveredByLayer layers u) &&
      (w.sublistsLen n).all (fun u => checkCandidates layers u separatingRows (cand527 w)))

private theorem fastCheck_sound {w : List (BitVec 32)} {k : ℕ}
    {layers : List (List (BitVec 32))} (h : fastCheck w k layers = true) :
    checkLayer527 w k layers = true := by
  obtain ⟨hn, hold, hnew⟩ :=
    (Bool.and_eq_true_iff.mp h).imp_right Bool.and_eq_true_iff.mp
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hn, List.all_eq_true.mpr ?_⟩
  intro z hz
  have hk : min (k+1) (z :: w).length = min k w.length + 1 := by
    simp only [List.length_cons]
    omega
  rw [hk, List.sublistsLen_succ_cons]
  apply List.all_eq_true.mpr
  intro u hu
  rcases List.mem_append.mp hu with hu | hu
  · exact List.all_eq_true.mp hold u hu
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    by_cases hs : separates527 (z :: v) = true
    · have hc := checkCandidates_sound (fun _ hp => hp) hz (List.all_eq_true.mp hnew v hv) hs
      simpa only [hs, Bool.not_true, Bool.false_or, coveredByLayer] using hc
    · simp [Bool.eq_false_iff.mpr hs]

theorem close527 {w : List (BitVec 32)} {k : ℕ} {layer : List (List (BitVec 32))}
    (hn : w.Nodup) (hc : fastCheck w k layer = true)
    (hL : ∀ v ∈ layer, ¬ Reach527 v.toFinset k goal527) :
    ¬ Reach527 w.toFinset (k+1) goal527 := by
  intro h
  obtain ⟨hnow, hall⟩ := Bool.and_eq_true_iff.mp (fastCheck_sound hc)
  have ht : goal527 ∉ w := by simpa using hnow
  obtain ⟨z,hz,u,hu,_,hr⟩ := reach_advance527 h hn ht
  have ha := List.all_eq_true.mp (List.all_eq_true.mp hall z hz) u hu
  rw [reach_separates527 hr] at ha
  have hb : layer.any (fun v => u.all (fun a => v.contains a)) = true := ha
  obtain ⟨v,hv,hinc⟩ := List.any_eq_true.mp hb
  apply hL v hv
  apply reach_mono527 _ hr
  intro a ha
  exact List.mem_toFinset.mpr (by simpa using List.all_eq_true.mp hinc a (List.mem_toFinset.mp ha))

-- Check each remaining wire set separately to bound peak kernel memory.
private def lastCase (w : List (BitVec 32)) : Bool :=
  decide w.Nodup && fastCheck w 3 []

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow1 : lastCase [0x0000ffff, 0x00ff00ff, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow2 : lastCase [0x0000ffff, 0x0f0f0f0f, 0xaaaaaaaa, 0xcccccccc, 0xff00ff00] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow3 : lastCase [0x0000ffff, 0x33333333, 0xaaaaaaaa, 0xf0f0f0f0, 0xff00ff00] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow4 : lastCase [0x0000ffff, 0x55555555, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow5 : lastCase [0x0000ffff, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow6 : lastCase [0x00ff00ff, 0x0f0f0f0f, 0xaaaaaaaa, 0xcccccccc, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow7 : lastCase [0x00ff00ff, 0x33333333, 0xaaaaaaaa, 0xf0f0f0f0, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow8 : lastCase [0x00ff00ff, 0x55555555, 0xcccccccc, 0xf0f0f0f0, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow9 : lastCase [0x00ff00ff, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow10 : lastCase [0x0f0f0f0f, 0x33333333, 0xaaaaaaaa, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow11 : lastCase [0x0f0f0f0f, 0x55555555, 0xcccccccc, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow12 : lastCase [0x0f0f0f0f, 0xaaaaaaaa, 0xcccccccc, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow13 : lastCase [0x33333333, 0x55555555, 0xf0f0f0f0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow14 : lastCase [0x33333333, 0xaaaaaaaa, 0xf0f0f0f0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow15 : lastCase [0x55555555, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow16 : lastCase [0xaaaa8888, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow17 : lastCase [0xaaaaaaaa, 0xc8c8c8c8, 0xf0f0f0f0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow18 : lastCase [0xaaaaaaaa, 0xcccccccc, 0xf0c0f0c0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow19 : lastCase [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00f000, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow20 : lastCase [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffaa0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow21 : lastCase [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow22 : lastCase [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff8888] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow23 : lastCase [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffffc0c0] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow24 : lastCase [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xfffff000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow25 : lastCase [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff88ff88, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow26 : lastCase [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xffaaff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow27 : lastCase [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xffc0ffc0, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow28 : lastCase [0xaaaaaaaa, 0xcccccccc, 0xf8f8f8f8, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow29 : lastCase [0xaaaaaaaa, 0xcccccccc, 0xfafaf0f0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow30 : lastCase [0xaaaaaaaa, 0xcccccccc, 0xff00ff00, 0xfff0f0f0, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow31 : lastCase [0xaaaaaaaa, 0xeeeecccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow32 : lastCase [0xaaaaaaaa, 0xf0f0f0f0, 0xfcccfccc, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow33 : lastCase [0xaaaaaaaa, 0xf0f0f0f0, 0xff00ff00, 0xffcccccc, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow34 : lastCase [0xcccccccc, 0xeaeaeaea, 0xf0f0f0f0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow35 : lastCase [0xcccccccc, 0xf0f0f0f0, 0xfaaafaaa, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem lastRow36 : lastCase [0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffaaaaaa, 0xffff0000] = true := by decide +kernel

private theorem lastChecks527 :
    layer2527.all (fun w => decide w.Nodup && fastCheck w 3 []) = true := by
  change layer2527.all lastCase = true
  simp only [layer2527, List.all_cons, List.all_nil, Bool.true_and,
    lastRow1, lastRow2, lastRow3, lastRow4, lastRow5,
    lastRow6, lastRow7, lastRow8, lastRow9, lastRow10,
    lastRow11, lastRow12, lastRow13, lastRow14, lastRow15,
    lastRow16, lastRow17, lastRow18, lastRow19, lastRow20,
    lastRow21, lastRow22, lastRow23, lastRow24, lastRow25,
    lastRow26, lastRow27, lastRow28, lastRow29, lastRow30,
    lastRow31, lastRow32, lastRow33, lastRow34, lastRow35,
    lastRow36]

private def middleCase (w : List (BitVec 32)) : Bool :=
  decide w.Nodup && fastCheck w 4 layer2527

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow1 : middleCase [0x0000ffff, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow2 : middleCase [0x00ff00ff, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow3 : middleCase [0x0f0f0f0f, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow4 : middleCase [0x33333333, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow5 : middleCase [0x55555555, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow6 : middleCase [0x88888888, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow7 : middleCase [0xa0a0a0a0, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow8 : middleCase [0xaa00aa00, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow9 : middleCase [0xaaaa0000, 0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow10 : middleCase [0xaaaaaaaa, 0xc0c0c0c0, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow11 : middleCase [0xaaaaaaaa, 0xcc00cc00, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow12 : middleCase [0xaaaaaaaa, 0xcccc0000, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow13 : middleCase [0xaaaaaaaa, 0xcccccccc, 0xeeeeeeee, 0xf0f0f0f0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow14 : middleCase [0xaaaaaaaa, 0xcccccccc, 0xf000f000, 0xf0f0f0f0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow15 : middleCase [0xaaaaaaaa, 0xcccccccc, 0xf0f00000, 0xf0f0f0f0, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow16 : middleCase [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xfafafafa, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow17 : middleCase [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xfcfcfcfc, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow18 : middleCase [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff000000, 0xff00ff00, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow19 : middleCase [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffaaffaa, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow20 : middleCase [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffccffcc, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow21 : middleCase [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xfff0fff0, 0xffff0000] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow22 : middleCase [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000, 0xffffaaaa] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow23 : middleCase [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000, 0xffffcccc] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow24 : middleCase [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000, 0xfffff0f0] = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem middleRow25 : middleCase [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000, 0xffffff00] = true := by decide +kernel

private theorem middleChecks527 :
    layer1527.all (fun w => decide w.Nodup && fastCheck w 4 layer2527) = true := by
  change layer1527.all middleCase = true
  simp only [layer1527, List.all_cons, List.all_nil, Bool.true_and,
    middleRow1, middleRow2, middleRow3, middleRow4, middleRow5,
    middleRow6, middleRow7, middleRow8, middleRow9, middleRow10,
    middleRow11, middleRow12, middleRow13, middleRow14, middleRow15,
    middleRow16, middleRow17, middleRow18, middleRow19, middleRow20,
    middleRow21, middleRow22, middleRow23, middleRow24, middleRow25]

set_option maxRecDepth 32768 in
private theorem firstCheck527 : fastCheck root527 5 layer1527 = true := by decide +kernel

theorem cycleExcluded527 : ¬ Reach527 root527.toFinset 6 goal527 := by
  apply close527 (by decide) firstCheck527
  intro v hv
  obtain ⟨hn,hc⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp middleChecks527 v hv)
  apply close527 (of_decide_eq_true hn) hc
  intro u hu
  obtain ⟨hn',hc'⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp lastChecks527 u hu)
  apply close527 (of_decide_eq_true hn') hc'
  simp

private abbrev Word527 := BitVec 32

private def Known527 (w : Finset Word527) (a : Word527) : Prop :=
  a = 0 ∨ a = BitVec.allOnes 32 ∨ a ∈ w

private def inputCols527 : List Word527 :=
  [0xaaaaaaaa, 0, 0xf0f0f0f0, 0, 0xffff0000, 0, 0xcccccccc, 0, 0xff00ff00]

def inputSet527 : Finset Word527 :=
  {0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000}

private def wordOp527 (op : GateOp) (as : List Word527) : Word527 :=
  match op, as with
  | .and, [] => BitVec.allOnes 32
  | .and, [a] => a
  | .and, a :: b :: _ => a &&& b
  | .or, [] => 0
  | .or, [a] => a
  | .or, a :: b :: _ => a ||| b
  | .not, [] => BitVec.allOnes 32
  | .not, a :: _ => ~~~a
  | _, _ => 0

private def wordStep527 (w : List Word527) (g : Gate) : Word527 :=
  wordOp527 g.op (g.inputs.map fun i => w.getD i 0)

private def wordRun527 (w : List Word527) (gs : List Gate) : List Word527 :=
  gs.foldl (fun ws g => ws ++ [wordStep527 ws g]) w

private def bits527 (w : List Word527) (j : ℕ) : List Bool :=
  w.map (fun a => a.getLsbD j)

private lemma bits_get527 (w : List Word527) (j i : ℕ) :
    (bits527 w j).getD i false = (w.getD i 0).getLsbD j := by
  simpa [bits527] using (List.getD_map (l := w) (d := 0) (n := i)
    (fun a : Word527 => a.getLsbD j))

private def Allowed527 (op : GateOp) : Prop := op = .and ∨ op = .or ∨ op = .not

private theorem wordOp_bits527 (op : GateOp) (as : List Word527) (j : ℕ) (hj : j < 32)
    (h : Allowed527 op) (hlen : as.length ≤ 2) :
    (wordOp527 op as).getLsbD j = op.eval (bits527 as j) := by
  rcases h with rfl | rfl | rfl <;>
    cases as with
    | nil =>
      first
      | exact BitVec.getLsbD_zero
      | simp only [wordOp527, GateOp.eval, bits527, List.map_nil, List.all_nil,
          List.headD_nil, BitVec.getLsbD_allOnes,
          hj, decide_true, Bool.not_false]
    | cons a rest =>
      cases rest with
      | nil => simp only [wordOp527, GateOp.eval, bits527, List.map_cons, List.map_nil,
          List.all_cons, List.any_cons, List.headD_cons, id_eq, List.all_nil, List.any_nil,
          Bool.and_true, Bool.or_false, BitVec.getLsbD_not, hj, decide_true, Bool.true_and]
      | cons b tail =>
        have ht : tail = [] := by simpa using hlen
        subst tail
        simp only [wordOp527, GateOp.eval, bits527, List.map_cons, List.map_nil, List.all_cons,
          List.any_cons, List.headD_cons, id_eq, List.all_nil, List.any_nil, Bool.and_true,
          Bool.or_false, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hj,
          decide_true, Bool.true_and]

private theorem wordStep_bits527 (g : Gate) (w : List Word527) (j : ℕ) (hj : j < 32)
    (h : Allowed527 g.op) (hlen : g.inputs.length ≤ 2) :
    (wordStep527 w g).getLsbD j = g.op.eval (g.inputs.map fun i => (bits527 w j).getD i false) := by
  rw [wordStep527, wordOp_bits527 _ _ _ hj h (by simpa)]
  simp only [bits527, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (bits_get527 w j i).symm

private theorem wordRun_bits527 (gs : List Gate) (ws : List Word527) (j : ℕ) (hj : j < 32)
    (hok : ∀ g ∈ gs, Allowed527 g.op ∧ g.inputs.length ≤ 2) :
    bits527 (wordRun527 ws gs) j =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (bits527 ws j) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    change bits527 (wordRun527 (ws ++ [wordStep527 ws g]) gs) j = _
    rw [ih _ (fun g hg => hok g (List.mem_cons_of_mem _ hg))]
    simp only [List.foldl_cons]
    congr 1
    have hg := hok g List.mem_cons_self
    unfold bits527
    rw [List.map_append]
    exact congrArg (fun a => (ws.map (fun b => b.getLsbD j)) ++ [a])
      (wordStep_bits527 g ws j hj hg.1 hg.2)

private theorem known_get527 {ws : List Word527} {w : Finset Word527}
    (hknown : ∀ a ∈ ws, Known527 w a) (i : ℕ) : Known527 w (ws.getD i 0) := by
  by_cases h : i < ws.length
  · rw [List.getD_eq_getElem _ _ h]
    exact hknown _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Or.inl rfl

private theorem andGate527 {w : Finset Word527} {a b : Word527}
    (ha : Known527 w a) (hb : Known527 w b) : Known527 w (a &&& b) ∨ Next527 w (a &&& b) := by
  rcases ha with rfl | rfl | ha
  · exact Or.inl (Or.inl BitVec.zero_and)
  · simpa only [BitVec.allOnes_and] using Or.inl (b := Next527 w b) hb
  rcases hb with rfl | rfl | hb
  · exact Or.inl (Or.inl BitVec.and_zero)
  · exact Or.inl (Or.inr (Or.inr (by simpa only [BitVec.and_allOnes] using ha)))
  by_cases he : a = b
  · subst b
    exact Or.inl (Or.inr (Or.inr (by simpa only [BitVec.and_self] using ha)))
  · exact Or.inr (Or.inr ⟨a, ha, b, hb, he, Or.inl rfl⟩)

private theorem orGate527 {w : Finset Word527} {a b : Word527}
    (ha : Known527 w a) (hb : Known527 w b) : Known527 w (a ||| b) ∨ Next527 w (a ||| b) := by
  rcases ha with rfl | rfl | ha
  · rw [show (0 : Word527) ||| b = b from BitVec.zero_or]
    exact Or.inl hb
  · exact Or.inl (Or.inr (Or.inl BitVec.allOnes_or))
  rcases hb with rfl | rfl | hb
  · rw [show a ||| (0 : Word527) = a from BitVec.or_zero]
    exact Or.inl (Or.inr (Or.inr ha))
  · exact Or.inl (Or.inr (Or.inl BitVec.or_allOnes))
  by_cases he : a = b
  · subst b
    exact Or.inl (Or.inr (Or.inr (by simpa only [BitVec.or_self] using ha)))
  · exact Or.inr (Or.inr ⟨a, ha, b, hb, he, Or.inr rfl⟩)

private theorem notGate527 {w : Finset Word527} {a : Word527} (ha : Known527 w a) :
    Known527 w (~~~a) ∨ Next527 w (~~~a) := by
  rcases ha with rfl | rfl | ha
  · exact Or.inl (Or.inr (Or.inl rfl))
  · exact Or.inl (Or.inl rfl)
  · exact Or.inr (Or.inl ⟨a, ha, rfl⟩)

private theorem wordOp_next527 (w : Finset Word527) (op : GateOp) (as : List Word527)
    (hknown : ∀ a ∈ as, Known527 w a) (hop : Allowed527 op) :
    Known527 w (wordOp527 op as) ∨ Next527 w (wordOp527 op as) := by
  rcases hop with rfl | rfl | rfl <;>
    cases as with
    | nil => first | exact Or.inl (Or.inl rfl) | exact Or.inl (Or.inr (Or.inl rfl))
    | cons a rest =>
      have ha := hknown a List.mem_cons_self
      cases rest with
      | nil => first | exact Or.inl ha | exact notGate527 ha
      | cons b tail =>
        have hb := hknown b (List.mem_cons_of_mem a List.mem_cons_self)
        first | exact andGate527 ha hb | exact orGate527 ha hb | exact notGate527 ha

private theorem reachable527 (w : Finset Word527) (ws : List Word527) (gs : List Gate)
    (k : ℕ) (o : ℕ) (t : Word527) (hk : gs.length ≤ k)
    (hknown : ∀ a ∈ ws, Known527 w a)
    (hok : ∀ g ∈ gs, Allowed527 g.op) (hzero : t ≠ 0) (hone : t ≠ BitVec.allOnes 32)
    (ht : (wordRun527 ws gs).getD o 0 = t) : Reach527 w k t := by
  induction gs generalizing ws w k with
  | nil =>
    change ws.getD o 0 = t at ht
    have h := known_get527 hknown o
    rw [ht] at h
    have hmem := (h.resolve_left hzero).resolve_left hone
    cases k with
    | zero => exact hmem
    | succ k => exact Or.inl hmem
  | cons g gs ih =>
    let z := wordStep527 ws g
    change (wordRun527 (ws ++ [z]) gs).getD o 0 = t at ht
    have hrest := fun g' (hg' : g' ∈ gs) => hok g' (List.mem_cons_of_mem g hg')
    cases k with
    | zero => simp at hk
    | succ k =>
      have hlen : gs.length ≤ k := by simpa using hk
      by_cases h : Known527 w z
      · apply ih w (ws ++ [z]) (k+1) (by omega) _ hrest ht
        intro a ha
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · exact hknown a ha
        · exact h
      · have hz : Known527 w z ∨ Next527 w z :=
          wordOp_next527 w g.op _ (by
            intro a ha
            obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
            exact known_get527 hknown i) (hok g List.mem_cons_self)
        refine Or.inr ⟨z, fun hm => h (Or.inr (Or.inr hm)), fun h0 => h (Or.inl h0),
          fun h1 => h (Or.inr (Or.inl h1)), hz.resolve_left h, ?_⟩
        apply ih (insert z w) (ws ++ [z]) k hlen _ hrest ht
        intro a ha
        simp only [List.mem_append, List.mem_singleton] at ha
        rcases ha with ha | rfl
        · rcases hknown a ha with h0 | h1 | hm
          · exact Or.inl h0
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr (Finset.mem_insert_of_mem hm))
        · exact Or.inr (Or.inr (Finset.mem_insert_self _ _))

private def row527 (j : ℕ) (i : Fin 9) : Bool := (inputCols527.getD i.val 0).getLsbD j

private theorem table_reach527 {f : (Fin 9 → Bool) → Bool} {k : ℕ} {t : Word527}
    (hf : HasCircuitSize 9 f k) (h0 : t ≠ 0) (h1 : t ≠ BitVec.allOnes 32)
    (hb : ∀ j : Fin 32, f (row527 j.val) = t.getLsbD j.val) : Reach527 inputSet527 k t := by
  obtain ⟨C, hok, hs, hev⟩ := hf
  have hok' : ∀ g ∈ C.gates, Allowed527 g.op ∧ g.inputs.length ≤ 2 := hok
  refine reachable527 inputSet527 inputCols527 C.gates k C.output t hs ?_ (fun g hg => (hok' g hg).1) h0 h1 ?_
  · intro a ha
    simp only [inputCols527, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> unfold Known527 <;> decide
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [← bits_get527, wordRun_bits527 _ _ _ hj hok']
    have hinput : bits527 inputCols527 j = List.ofFn (row527 j) := by rfl
    rw [hinput]
    exact (hev (row527 j)).trans (hb ⟨j, hj⟩)

def fix {n : ℕ} (f : BFn n) (p : Fin n) (b : Bool) : BFn n :=
  fun x => f (Function.update x p b)

def depends {n : ℕ} (f : BFn n) (p : Fin n) : Prop :=
  ∃ x : Fin n → Bool, fix f p (!x p) x ≠ f x

def nonconstant {n : ℕ} (f : BFn n) : Prop :=
  ∃ x y : Fin n → Bool, f x ≠ f y

-- Fix the end of a two-edge arm, then fix its intermediate vertex to false.
-- The first restriction can save two gates in one of the two branches.
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

def cycle (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4) || (x 0 && x 6) || (x 2 && x 6) || (x 2 && x 8) || (x 4 && x 8)

theorem cycle_lower (t : Nat) (h : HasCircuitSize 9 cycle t) : 7 ≤ t := by
  by_contra! small
  obtain ⟨C, legal, size, computes⟩ := h
  have smaller : HasCircuitSize 9 cycle 6 := ⟨C, legal, size.trans (by omega), computes⟩
  have reached : Reach527 inputSet527 6 goal527 :=
    table_reach527 smaller (by decide) (by decide) (by decide)
  have same : root527.toFinset = inputSet527 := by decide
  exact cycleExcluded527 (same.symm ▸ reached)

def mask (m : ℕ) (i : Fin 9) : Bool := m.testBit i.val

def withArm (inner leaf attach : Fin 9) (f : BFn 9) (x : Fin 9 → Bool) : Bool :=
  f x || (x inner && (x leaf || x attach))

def firstArm : BFn 9 := withArm 7 3 2 cycle

def secondArm : BFn 9 := withArm 1 5 8 firstArm

lemma firstArm_lower (t : ℕ) (h : HasCircuitSize 9 firstArm t) : 10 ≤ t := by
  apply arm_lower (leaf := 3) (inner := 7) (g := cycle) (k := 7) (s := t) _ _ _ _
    cycle_lower h
  · exact ⟨mask 128, by decide⟩
  · intro b
    cases b
    · exact ⟨mask 4, by decide⟩
    · exact ⟨mask 0, by decide⟩
  · exact ⟨mask 0, mask 17, by decide⟩
  · intro b
    funext x
    simp [fix, firstArm, withArm, cycle, Function.update]

lemma secondArm_lower (t : ℕ) (h : HasCircuitSize 9 secondArm t) : 13 ≤ t := by
  apply arm_lower (leaf := 5) (inner := 1) (g := firstArm) (k := 10) (s := t) _ _ _ _
    firstArm_lower h
  · exact ⟨mask 2, by decide⟩
  · intro b
    cases b
    · exact ⟨mask 256, by decide⟩
    · exact ⟨mask 0, by decide⟩
  · exact ⟨mask 0, mask 17, by decide⟩
  · intro b
    funext x
    simp [fix, secondArm, firstArm, withArm, cycle, Function.update]

lemma fn_eq_all :
    ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Bool,
      let y : Fin 9 → Bool := ![a0, a1, a2, a3, a4, a5, a6, a7, a8]
      secondArm y = ((y 0 && y 4) || (y 1 && y 5) || (y 0 && y 6) || (y 2 && y 6) || (y 2 && y 7) || (y 3 && y 7) || (y 1 && y 8) || (y 2 && y 8) || (y 4 && y 8)) := by
  decide

lemma fn_eq : secondArm = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 2 && x 7) || (x 3 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 4 && x 8)) := by
  funext x
  have hx : x = ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8] := by
    funext i; fin_cases i <;> rfl
  rw [hx]
  exact fn_eq_all (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)

end PEqualNP.Outside.L_meta_9205

open PEqualNP.Outside.L_meta_9205 in
theorem PEqualNP.Outside.L_meta_9205 :
∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 2 && x 7) || (x 3 && x 7) || (x 1 && x 8) || (x 2 && x 8) || (x 4 && x 8)) t → 13 ≤ t := by
  intro t h
  exact secondArm_lower t (fn_eq ▸ h)
