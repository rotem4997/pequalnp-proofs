import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_5126
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.SplitCount Finset
variable {n:ℕ} {G:SimpleGraph (Fin n)} [DecidableRel G.Adj] {C:Circuit}
def aB {n:ℕ} (G:SimpleGraph (Fin n)) (U:Finset (Sym2 (Fin n))) (W:Finset (Fin n)):Prop:=∃z:Fin n,∀w∈W,G.Adj z w/\s(z,w)∉U
def aE {n:ℕ} (U:Finset (Sym2 (Fin n))) (a:Fin n):Finset (Fin n):=univ.filter λw=>s(a,w)∈U
def dB {ν α:Type} [DecidableEq α] (J:ν ->Prop) (l r:ν ->ν) (rk:ν ->ℕ) (f:ν ->Finset α):Prop:=∀w,J w ->rk (l w)<rk w/\rk (r w)<rk w/\f w=f (l w)∪f (r w)
def aM {ν:Type} (J:ν ->Prop) (l r:ν ->ν):ν ->ν ->Prop:=Relation.ReflTransGen λw w'=>J w/\(w'=l w\/w'=r w)
lemma nM {α β:Type} {st:List α ->β ->List α} {F:List α ->β ->α} (hst:∀a g,st a g=a++[F a g]) (d:α) (gs:List β) (init:List α):(gs.foldl st init).length=init.length+gs.length/\(∀i< init.length,(gs.foldl st init).getD i d=init.getD i d)/\∀j (hj:j<gs.length),∃p:List α,p.length=init.length+j/\(∀i<p.length,p.getD i d=(gs.foldl st init).getD i d)/\(gs.foldl st init).getD (init.length+j) d=F p gs[j]:=by
 obtain rfl:st=λa g=>a++[F a g]:=by funext a g;exact hst a g
 induction gs using List.reverseRecOn with
 |nil=>simp
 |append_singleton gs g ih=>
  obtain⟨h1,h2,h3⟩:=ih;simp only[List.foldl_append,List.foldl_cons,List.foldl_nil,List.length_append,List.length_singleton];have key:∀i< init.length+gs.length,(gs.foldl (λa g=>a++[F a g]) init++[F (gs.foldl (λa g=>a++[F a g]) init) g]).getD i d=(gs.foldl (λa g=>a++[F a g]) init).getD i d:=λi hi=>by
   simp[List.getD_eq_getElem?_getD,List.getElem?_append_left (h1▸hi)]
  refine⟨by omega,λi hi=>by rw[key i (by omega),h2 i hi],λj hj=>?_⟩;rcases Nat.lt_or_ge j gs.length with h|h
  ·obtain⟨p,hp1,hp2,hp3⟩:=h3 j h;refine⟨p,hp1,λi hi=>by rw[key i (by omega),hp2 i hi],?_⟩;rw[key _ (by omega),hp3,List.getElem_append_left h]
  ·obtain rfl:j=gs.length:=by omega
   refine⟨_,h1,λi hi=>(key i (h1▸hi)).symm,?_⟩;simp[List.getD_eq_getElem?_getD,←h1]
lemma e6 {C:Circuit} {j:ℕ} (hj:j<C.gates.length):gateAt C j=C.gates[j]:=by
 simp[gateAt,hj]
lemma a5 (C:Circuit) (x:Fin n ->Bool):(∀v:Fin n,wireVal n C v x=x v)/\(∀w,n+C.gates.length≤w ->wireVal n C w x=false)/\∀j<C.gates.length,wireVal n C (n+j) x=(gateAt C j).op.eval ((gateAt C j).inputs.map λi=>if i<n+j then wireVal n C i x else false):=by
 have hf:=nM (st:=λ(w:List Bool) (g:Gate)=>w++[g.op.eval (g.inputs.map λi=>w.getD i false)]) (λ_ _=>rfl) false C.gates (List.ofFn x);simp only[List.length_ofFn]at hf;unfold wireVal Circuit.wires;refine⟨λv=>by simpa using hf.2.1 v v.2,λw hw=>?_,λj hj=>?_⟩
 ·rw[List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega)];rfl
 ·obtain⟨p,hp1,hp2,hp3⟩:=hf.2.2 j hj;rw[hp3,e6 hj]
  congr 1
  apply List.map_congr_left;intro i _;split_ifs with h
  ·exact hp2 i (by omega)
  ·simp[List.getD_eq_getElem?_getD,List.getElem?_eq_none (show p.length≤ i by omega)]
lemma aZ {i j:ℕ}:InCone n C i j↔j<C.gates.length/\∃k<j,n+k∈(gateAt C j).inputs/\(i=k\/InCone n C i k):=by
 have hf:=nM (st:=coneStep n) (λ_ _=>rfl) [] C.gates [];unfold InCone cones;by_cases hj:j<C.gates.length
 ·obtain⟨p,hp1,hp2,hp3⟩:=hf.2.2 j hj;simp only[List.length_nil,Nat.zero_add]at hp1 hp3;rw[hp3,e6 hj];simp only[List.mem_flatMap,List.mem_filter,decide_eq_true_eq,List.mem_cons,hp1];constructor
  ·rintro⟨w,⟨hw,h1,h2⟩,h3⟩;refine⟨hj,w-n,by omega,by rwa[show n+(w-n)=w by omega],?_⟩;rwa[hp2 _ (by omega)]at h3
  ·rintro⟨_,k,hk,hw,h3⟩;refine⟨n+k,⟨hw,by omega,by omega⟩,?_⟩;rw[show n+k-n=k by omega,hp2 _ (by omega)];exact h3
 ·have h0:(C.gates.foldl (coneStep n) []).getD j []=[]:=by
   rw[List.getD_eq_getElem?_getD,List.getElem?_eq_none (by have:=hf.1;simp at this;omega)];rfl
  rw[h0];simp[hj]
lemma bD {k g:ℕ}:OrReaches n C (n+k) g↔k<C.gates.length/\(g=k\/((gateAt C k).op=GateOp.or/\∃i∈(gateAt C k).inputs,i<n+k/\OrReaches n C i g)):=by
 have hf:=nM (st:=orStep n) (λ_ _=>rfl) [] C.gates [];unfold OrReaches orSets;rw[show n+k-n=k by omega];by_cases hk:k<C.gates.length
 ·obtain⟨p,hp1,hp2,hp3⟩:=hf.2.2 k hk;simp only[List.length_nil,Nat.zero_add]at hp1 hp3;rw[hp3,e6 hk];simp only[List.mem_cons,hp1,Nat.le_add_right,true_and,hk];refine or_congr Iff.rfl ?_;split_ifs with hop
  ·simp only[List.mem_flatMap,List.mem_filter,decide_eq_true_eq,hop,true_and];constructor
   ·rintro⟨w,⟨hw,h1,h2⟩,h3⟩;exact⟨w,hw,h2,h1,by rwa[hp2 _ (by omega)]at h3⟩
   ·rintro⟨w,hw,h2,h1,h3⟩;exact⟨w,⟨hw,h1,h2⟩,by rwa[hp2 _ (by omega)]⟩
  ·simp[hop]
 ·have h0:(C.gates.foldl (orStep n) []).getD k []=[]:=by
   rw[List.getD_eq_getElem?_getD,List.getElem?_eq_none (by have:=hf.1;simp at this;omega)];rfl
  rw[h0];simp[hk]
lemma bA (C:Circuit) (x:Fin n ->Bool) (v:Fin n):wireVal n C v x=x v:=(a5 C x).1 v
def jW (C:Circuit):Prop:=∀k<C.gates.length,((gateAt C k).op=GateOp.and\/(gateAt C k).op=GateOp.or)/\(gateAt C k).inputs.length=2
lemma bZ:IsAO2 n C↔jW C/\ReadsBack n C:=by
 have hm:∀g∈C.gates,∃k<C.gates.length,gateAt C k=g:=λg hg=>by
  obtain⟨k,hk,rfl⟩:=List.mem_iff_getElem.mp hg;exact⟨k,hk,e6 hk⟩
 constructor
 ·rintro⟨h1,h2,h3⟩;exact⟨λk hk=>⟨h1 _ (e6 hk▸List.getElem_mem hk),h3 _ (e6 hk▸List.getElem_mem hk)⟩,h2⟩
 ·rintro⟨h1,h2⟩;refine⟨λg hg=>?_,h2,λg hg=>?_⟩<;>obtain⟨k,hk,rfl⟩:=hm g hg
  ·exact(h1 k hk).1
  ·exact(h1 k hk).2
lemma bO {C:Circuit} (h:jW C) {k:ℕ} (hk:k<C.gates.length):(gateAt C k).inputs=[opnd C k 0,opnd C k 1]:=by
 obtain⟨a,b,hab⟩:=List.length_eq_two.mp (h k hk).2;simp[opnd,hab]
lemma aH (h:IsAO2 n C) {k:ℕ} (hk:k<C.gates.length) (b:Fin 2):opnd C k b<n+k:=by
 have:=bO (bZ.mp h).1 hk;refine(bZ.mp h).2 k hk _ ?_;rw[this];fin_cases b<;>simp
lemma kX (h:IsAO2 n C) {k:ℕ} (hk:k<C.gates.length) (x:Fin n ->Bool):((gateAt C k).op=GateOp.and ->wireVal n C (n+k) x=(wireVal n C (opnd C k 0) x&&wireVal n C (opnd C k 1) x))/\((gateAt C k).op=GateOp.or ->wireVal n C (n+k) x=(wireVal n C (opnd C k 0) x||wireVal n C (opnd C k 1) x)):=by
 rw[(a5 C x).2.2 k hk,bO (bZ.mp h).1 hk];have h0:=aH h hk 0;have h1:=aH h hk 1;constructor<;>intro hop<;>simp[hop,h0,h1,GateOp.eval]
lemma eS (h:IsAO2 n C) {k:ℕ} (hk:k<C.gates.length):(gateAt C k).op=GateOp.and\/(gateAt C k).op=GateOp.or:=((bZ.mp h).1 k hk).1
lemma nH (h:jW C) {x y:Fin n ->Bool} (hxy:∀v,x v=true ->y v=true) (w:ℕ):wireVal n C w x=true ->wireVal n C w y=true:=by
 induction w using Nat.strong_induction_on with
 |_ w ih=>
  rcases Nat.lt_or_ge w n with hw|hw
  ·have:=bA C x ⟨w,hw⟩;have:=bA C y ⟨w,hw⟩;simp_all
  ·obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by omega⟩;rcases Nat.lt_or_ge k C.gates.length with hk|hk
   ·rw[(a5 C x).2.2 k hk,(a5 C y).2.2 k hk];rcases (h k hk).1 with hop|hop<;>simp only[hop,GateOp.eval,List.all_map,List.any_map,List.all_eq_true,List.any_eq_true,Function.comp,id]
    ·intro h1 i hi;have:=h1 i hi;split_ifs at this⊢with hlt;simp_all
    ·rintro⟨i,hi,h1⟩;refine⟨i,hi,?_⟩;split_ifs at h1⊢with hlt;simp_all
   ·simp[(a5 C x).2.1 (n+k) (by omega)]
lemma dN (h:IsAO2 n C) {k g:ℕ}:OrReaches n C (n+k) g↔k<C.gates.length/\(g=k\/((gateAt C k).op=GateOp.or/\(OrReaches n C (opnd C k 0) g\/OrReaches n C (opnd C k 1) g))):=by
 rw[bD];refine and_congr_right λhk=>or_congr_right (and_congr_right λ_=>?_);have h0:=aH h hk 0;have h1:=aH h hk 1;simp[bO (bZ.mp h).1 hk,h0,h1]
lemma aX {w g:ℕ} (h:OrReaches n C w g):n+g≤w/\g<C.gates.length:=by
 induction w using Nat.strong_induction_on with
 |_ w ih=>
  obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by have:=h.1;omega⟩;obtain⟨hk,rfl|⟨_,i,_,hi,hr⟩⟩:=bD.mp h
  ·exact⟨le_rfl,hk⟩
  ·have:=ih i hi hr;exact⟨by omega,this.2⟩
lemma dV {w:ℕ} {v:Fin n}:v∈orIn n C w↔(v:ℕ)=w\/∃k<C.gates.length,OrReaches n C w k/\(gateAt C k).op=GateOp.or/\(v:ℕ)∈(gateAt C k).inputs:=by simp[orIn]
lemma fA {w:ℕ} (hw:w<n):orIn n C w={⟨w,hw⟩}:=by
 ext v;simp only[dV,mem_singleton,Fin.ext_iff];exact⟨λh=>h.elim id λ⟨k,_,hr,_⟩=>absurd hr.1 (by omega),Or.inl⟩
lemma dO (h:IsAO2 n C) {k:ℕ} (hk:k<C.gates.length) (hop:(gateAt C k).op=GateOp.or):orIn n C (n+k)=orIn n C (opnd C k 0)∪orIn n C (opnd C k 1):=by
 ext v;simp only[dV,mem_union,dN h,hk,true_and];have hin:=bO (bZ.mp h).1 hk;constructor
 ·rintro(h1|⟨g,hg,(rfl|⟨_,h2|h2⟩),hgo,hv⟩)
  ·exact absurd h1 (by have:=v.2;omega)
  ·rw[hin]at hv;simp at hv;tauto
  ·exact Or.inl (Or.inr ⟨g,hg,h2,hgo,hv⟩)
  ·exact Or.inr (Or.inr ⟨g,hg,h2,hgo,hv⟩)
 ·rintro((h1|⟨g,hg,h2,hgo,hv⟩)|(h1|⟨g,hg,h2,hgo,hv⟩))
  ·exact Or.inr ⟨k,hk,Or.inl rfl,hop,by rw[hin,h1];simp⟩
  ·exact Or.inr ⟨g,hg,Or.inr ⟨hop,Or.inl h2⟩,hgo,hv⟩
  ·exact Or.inr ⟨k,hk,Or.inl rfl,hop,by rw[hin,h1];simp⟩
  ·exact Or.inr ⟨g,hg,Or.inr ⟨hop,Or.inr h2⟩,hgo,hv⟩
lemma b6 {k:ℕ} (hop:k<C.gates.length ->(gateAt C k).op≠GateOp.or):orIn n C (n+k)=∅:=by
 ext v;simp only[dV,notMem_empty,iff_false,not_or];refine⟨by have:=v.2;omega,?_⟩;rintro⟨g,hg,hr,hgo,_⟩;obtain⟨hk,rfl|⟨h2,_⟩⟩:=bD.mp hr
 ·exact hop hk hgo
 ·exact hop hk h2
lemma kU (h:IsAO2 n C) (x:Fin n ->Bool) (w:ℕ):wireVal n C w x=true↔(∃v∈orIn n C w,x v=true)\/∃k,(gateAt C k).op=GateOp.and/\OrReaches n C w k/\gateVal n C k x=true:=by
 induction w using Nat.strong_induction_on with
 |_ w ih=>
  rcases Nat.lt_or_ge w n with hw|hw
  ·rw[fA hw];have:=bA C x ⟨w,hw⟩;simp only[mem_singleton,exists_eq_left]at this⊢;rw[this];exact⟨Or.inl,λh1=>h1.elim id λ⟨k,_,hr,_⟩=>absurd hr.1 (by omega)⟩
  ·obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by omega⟩;by_cases hk:k<C.gates.length
   ·rcases eS h hk with hop|hop
    ·rw[b6 (λ_=>by simp[hop])];simp only[notMem_empty,false_and,exists_false,false_or];constructor
     ·exact λhv=>⟨k,hop,bD.mpr ⟨hk,Or.inl rfl⟩,hv⟩
     ·rintro⟨g,hg,hr,hv⟩;obtain⟨_,rfl|⟨h2,_⟩⟩:=bD.mp hr
      ·exact hv
      ·rw[hop]at h2;cases h2
    ·rw[(kX h hk x).2 hop,Bool.or_eq_true,ih _ (aH h hk 0),ih _ (aH h hk 1),dO h hk hop];simp only[mem_union,dN h,hk,true_and];constructor
     ·rintro((⟨v,hv,hx⟩|⟨g,hg,hr,hx⟩)|(⟨v,hv,hx⟩|⟨g,hg,hr,hx⟩))
      ·exact Or.inl ⟨v,Or.inl hv,hx⟩
      ·exact Or.inr ⟨g,hg,Or.inr ⟨hop,Or.inl hr⟩,hx⟩
      ·exact Or.inl ⟨v,Or.inr hv,hx⟩
      ·exact Or.inr ⟨g,hg,Or.inr ⟨hop,Or.inr hr⟩,hx⟩
     ·rintro(⟨v,hv|hv,hx⟩|⟨g,hg,(rfl|⟨_,hr|hr⟩),hx⟩)
      ·exact Or.inl (Or.inl ⟨v,hv,hx⟩)
      ·exact Or.inr (Or.inl ⟨v,hv,hx⟩)
      ·rw[hop]at hg;cases hg
      ·exact Or.inl (Or.inr ⟨g,hg,hr,hx⟩)
      ·exact Or.inr (Or.inr ⟨g,hg,hr,hx⟩)
   ·rw[(a5 C x).2.1 _ (by omega),b6 (λh1=>absurd h1 hk)];simp only[Bool.false_eq_true,notMem_empty,false_and,exists_false,false_or,false_iff,not_exists,not_and];exact λg _ hr=>absurd (bD.mp hr).1 hk
lemma dJ (x:Fin n ->Bool):graphFun G ∅ x=true↔∃u v,G.Adj u v/\x u=true/\x v=true:=by simp[graphFun]
lemma aT (u v:Fin n):graphFun G ∅ (pairInput u v)=true↔G.Adj u v:=by
 simp only[dJ,pairInput,decide_eq_true_eq];constructor
 ·rintro⟨a,b,hab,rfl|rfl,rfl|rfl⟩;exacts[(G.irrefl hab).elim,hab,hab.symm,(G.irrefl hab).elim]
 ·exact λh=>⟨u,v,h,Or.inl rfl,Or.inr rfl⟩
lemma e8 (v:Fin n):graphFun G ∅ (unitInput v)=false:=by
 rw[←Bool.not_eq_true,dJ];rintro⟨a,b,hab,ha,hb⟩;simp only[unitInput,decide_eq_true_eq]at ha hb;exact G.irrefl (ha▸hb▸hab)
def dY (m:ℕ) (g:ℕ ->Gate) (o:ℕ):Circuit:=⟨(List.range m).map g,o⟩
@[simp] lemma l1_mk_len (m:ℕ) (g:ℕ ->Gate) (o:ℕ):(dY m g o).gates.length=m:=by
 simp[dY]
lemma bR {m:ℕ} {g:ℕ ->Gate} {o k:ℕ} (hk:k<m):gateAt (dY m g o) k=g k:=by
 simp[dY,gateAt,hk]
lemma kO {n m:ℕ} {g:ℕ ->Gate} {o:ℕ}:IsAO2 n (dY m g o)↔∀k<m,((g k).op=GateOp.and\/(g k).op=GateOp.or)/\(g k).inputs.length=2/\∀i∈(g k).inputs,i<n+k:=by
 simp only[bZ,jW,ReadsBack,l1_mk_len];constructor
 ·rintro⟨h1,h2⟩ k hk;have:=h1 k hk;have:=h2 k hk;rw[bR hk]at*;tauto
 ·intro h;refine⟨λk hk=>?_,λk hk=>?_⟩<;>rw[bR hk]
  ·exact⟨(h k hk).1,(h k hk).2.1⟩
  ·exact(h k hk).2.2
lemma gM {n:ℕ} {C D:Circuit} (x:Fin n ->Bool) {m:ℕ} (hC:m≤C.gates.length) (hD:m≤D.gates.length) (h:∀k<m,gateAt C k=gateAt D k):∀w<n+m,wireVal n C w x=wireVal n D w x:=by
 intro w
 induction w using Nat.strong_induction_on with
 |_ w ih=>
  intro hw;rcases Nat.lt_or_ge w n with hn|hn
  ·exact(bA C x ⟨w,hn⟩).trans (bA D x ⟨w,hn⟩).symm
  ·obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by omega⟩;rw[(a5 C x).2.2 k (by omega),(a5 D x).2.2 k (by omega),h k (by omega)]
   congr 1
   apply List.map_congr_left;intro i _;split_ifs with hi
   ·exact ih i hi (by omega)
   ·rfl
lemma mH {n:ℕ} {C D:Circuit} {m:ℕ} (hD:m≤D.gates.length) (h:∀k<m,gateAt C k=gateAt D k) (i:ℕ):∀j<m,InCone n C i j ->InCone n D i j:=by
 intro j
 induction j using Nat.strong_induction_on with
 |_ j ih=>
  intro hj hc;obtain⟨_,k,hk,hin,h3⟩:=aZ.mp hc;exact aZ.mpr ⟨by omega,k,hk,h j hj▸hin,h3.imp id (ih k hk (by omega))⟩
lemma aP {i:ℕ}:∀{j:ℕ},InCone n C i j ->i<j:=by
 intro j
 induction j using Nat.strong_induction_on with
 |_ j ih=>
  intro hc;obtain⟨_,k,hk,_,rfl|h3⟩:=aZ.mp hc
  ·exact hk
  ·exact(ih k hk h3).trans hk
lemma dI {a k:ℕ} (hak:InCone n C a k):∀{j:ℕ},InCone n C k j ->InCone n C a j:=by
 intro j
 induction j using Nat.strong_induction_on with
 |_ j ih=>
  intro hc;obtain⟨hj,k2,hk2,hin,rfl|h3⟩:=aZ.mp hc
  ·exact aZ.mpr ⟨hj,k,hk2,hin,Or.inr hak⟩
  ·exact aZ.mpr ⟨hj,k2,hk2,hin,Or.inr (ih k2 hk2 h3)⟩
lemma qT {n:ℕ} {D:Circuit} (h:jW D) {w:ℕ} (hw:wireVal n D w (λ_=>true)=false) (x:Fin n ->Bool):wireVal n D w x=false:=Bool.eq_false_iff.mpr λhx=>by
  have:=nH h (y:=λ_=>true) (λ_ _=>rfl) w hx;simp_all
def eJ (n:ℕ) (D:Circuit) (k:ℕ):Prop:=∀i∈(gateAt D k).inputs,i<n+k/\wireVal n D i (λ_=>true)=true
lemma rV {n:ℕ} {D:Circuit} (hD:jW D):∀j≤D.gates.length,∃(g':ℕ ->Gate) (m':ℕ) (κ:ℕ ->ℕ),IsAO2 n (dY m' g' 0)/\(∀w<n+j,wireVal n D w (λ_=>true)=true ->∃w'<n+m',(∀x,wireVal n (dY m' g' 0) w' x=wireVal n D w x)/\(n≤w' ->n≤w/\(w=n+κ (w'-n)\/InCone n D (κ (w'-n)) (w-n))))/\(∀k'<m',κ k'<j/\eJ n D (κ k')/\(g' k').op=(gateAt D (κ k')).op/\(∀x,wireVal n (dY m' g' 0) (n+k') x=wireVal n D (n+κ k') x)/\∀k''<k',κ k''<κ k')/\(∀k<j,eJ n D k ->∃k'<m',κ k'=k)/\(∀a' b',b'<m' ->InCone n (dY m' g' 0) a' b' ->InCone n D (κ a') (κ b')):=by
 intro j
 induction j with
 |zero=>
  intro _;refine⟨λ_=>⟨GateOp.or,[]⟩,0,id,kO.mpr (by simp),λw hw _=>⟨w,hw,λx=>?_,by omega⟩,by simp,by simp,by simp⟩;exact(bA _ x ⟨w,by omega⟩).trans (bA D x ⟨w,by omega⟩).symm
 |succ j ih=>
  intro hj;obtain⟨g',m',κ,ha,hb,hc,hd,he⟩:=ih (by omega);have hjl:j<D.gates.length:=by omega
  have hin:=bO hD hjl;by_cases hK:eJ n D j
  ·have hla:=hK (opnd D j 0) (by rw[hin];simp);have hlb:=hK (opnd D j 1) (by rw[hin];simp);obtain⟨a',ha',hav,haa⟩:=hb _ hla.1 hla.2;obtain⟨b',hb',hbv,hba⟩:=hb _ hlb.1 hlb.2;have hg:∀k<m',gateAt (dY m' g' 0) k=gateAt (dY (m'+1) (Function.update g' m' ⟨(gateAt D j).op,[a',b']⟩) 0) k:=λk hk=>by
    rw[bR hk,bR (by omega),Function.update_of_ne (Nat.ne_of_lt hk)]
   have hW:=λx=>gM (n:=n) x (by simp) (by simp) hg;have hnew:∀x,wireVal n (dY (m'+1) (Function.update g' m' ⟨(gateAt D j).op,[a',b']⟩) 0) (n+m') x=wireVal n D (n+j) x:=λx=>by
    rw[(a5 _ x).2.2 m' (by simp),(a5 D x).2.2 j hjl,bR (by omega),hin];simp[ha',hb',hla.1,hlb.1,←hW x a' ha',←hW x b' hb',hav x,hbv x]
   refine⟨Function.update g' m' ⟨(gateAt D j).op,[a',b']⟩,m'+1,Function.update κ m' j,?_,?_,?_,?_,?_⟩
   ·rw[kO]at ha⊢;intro k hk;rcases Nat.lt_or_ge k m' with h|h
    ·simpa[Function.update_of_ne (Nat.ne_of_lt h)]using ha k h
    ·obtain rfl:k=m':=by omega
     simp[(hD j hjl).1,ha',hb']
   ·intro w hw hv;rcases Nat.lt_or_ge w (n+j)with h|h
    ·obtain⟨w',hw',h1,h2⟩:=hb w h hv;refine⟨w',by omega,λx=>by rw[←hW x w' hw',h1],λh3=>?_⟩;rw[Function.update_of_ne (by omega)];exact h2 h3
    ·obtain rfl:w=n+j:=by omega
     exact⟨n+m',by omega,hnew,λ_=>⟨by omega,Or.inl (by simp)⟩⟩
   ·intro k' hk';rcases Nat.lt_or_ge k' m' with h|h
    ·obtain⟨h1,h2,h3,h4,h5⟩:=hc k' h;rw[Function.update_of_ne (Nat.ne_of_lt h),Function.update_of_ne (Nat.ne_of_lt h)];refine⟨by omega,h2,h3,λx=>by rw[←hW x _ (by omega),h4],λk'' hk''=>?_⟩;rw[Function.update_of_ne (by omega)];exact h5 k'' hk''
    ·obtain rfl:k'=m':=by omega
     simp only[Function.update_self];refine⟨by omega,hK,trivial,hnew,λk'' hk''=>?_⟩;rw[Function.update_of_ne (by omega)];exact(hc k'' hk'').1
   ·intro k hk hKk;rcases Nat.lt_or_ge k j with h|h
    ·obtain⟨k',hk',rfl⟩:=hd k h hKk;exact⟨k',by omega,Function.update_of_ne (by omega) _ _⟩
    ·exact⟨m',by omega,by simp;omega⟩
   ·intro c' d' hd'lt hcone;have hcl:=aP hcone;rw[Function.update_of_ne (show c'≠m' by omega)];have hcg:=λc k hk=>mH (n:=n) (m:=m') (D:=dY m' g' 0) (by simp) (λk hk=>(hg k hk).symm) c k hk;rcases Nat.lt_or_ge d' m' with h|h
    ·rw[Function.update_of_ne (by omega)];exact he c' d' h (hcg c' d' h hcone)
    ·obtain rfl:d'=m':=by omega
     simp only[Function.update_self];obtain⟨_,k'',hk'',hmem,h3⟩:=aZ.mp hcone;rw[bR (by omega)]at hmem;have h3':c'=k''\/InCone n D (κ c') (κ k''):=h3.imp id λh=>he c' k'' hk'' (hcg c' k'' hk'' h);have key:∀u u',u∈(gateAt D j).inputs ->u<n+j ->(n≤u' ->n≤u/\(u=n+κ (u'-n)\/InCone n D (κ (u'-n)) (u-n))) ->n+k''=u' ->InCone n D (κ c') j:=by
      intro u u' hu hul hal heq;obtain⟨hnu,hal⟩:=hal (by omega);rw[←heq,show n+k''-n=k'' by omega]at hal;refine aZ.mpr ⟨hjl,u-n,by omega,by rwa[show n+(u-n)=u by omega],?_⟩;rcases h3' with rfl|h3'<;>rcases hal with hal|hal
      ·left;omega
      ·right;exact hal
      ·right;rwa[show u-n=κ k'' by omega]
      ·right;exact dI h3' hal
     simp only[Function.update_self,List.mem_cons,List.not_mem_nil,or_false]at hmem;rcases hmem with h|h
     ·exact key _ a' (by rw[hin];simp) hla.1 haa h
     ·exact key _ b' (by rw[hin];simp) hlb.1 hba h
  ·refine⟨g',m',κ,ha,?_,λk' hk'=>?_,?_,he⟩
   ·intro w hw hv;rcases Nat.lt_or_ge w (n+j)with h|h
    ·exact hb w h hv
    ·obtain rfl:w=n+j:=by omega
     have key:∀u,u∈(gateAt D j).inputs ->(∀x,wireVal n D (n+j) x=wireVal n D u x) ->u<n+j ->wireVal n D u (λ_=>true)=true ->∃w'<n+m',(∀x,wireVal n (dY m' g' 0) w' x=wireVal n D (n+j) x)/\(n≤w' ->n≤n+j/\(n+j=n+κ (w'-n)\/InCone n D (κ (w'-n)) (n+j-n))):=by
      intro u hu hval hul hut;obtain⟨w',hw',h1,h2⟩:=hb u hul hut;refine⟨w',hw',λx=>by rw[h1,hval],λh3=>⟨by omega,Or.inr ?_⟩⟩;obtain⟨hnu,h2⟩:=h2 h3;rw[show n+j-n=j by omega];refine aZ.mpr ⟨hjl,u-n,by omega,by rwa[show n+(u-n)=u by omega],?_⟩;rcases h2 with h2|h2
      ·left;omega
      ·right;exact h2
     have hval:=λx:Fin n ->Bool=>(a5 D x).2.2 j hjl;simp only[hin]at hval;have hK':¬((opnd D j 0<n+j/\wireVal n D (opnd D j 0) (λ_=>true)=true)/\(opnd D j 1<n+j/\wireVal n D (opnd D j 1) (λ_=>true)=true)):=by
      intro h;apply hK;intro i hi;rw[hin]at hi;simp at hi;rcases hi with rfl|rfl;exacts[h.1,h.2]
     have hd0:∀u,¬(u<n+j/\wireVal n D u (λ_=>true)=true) ->∀x,u<n+j ->wireVal n D u x=false:=λu hu x h=>qT hD (by simpa[h]using hu) x;rw[hval]at hv;rcases (hD j hjl).1 with hop|hop
     ·simp[hop,GateOp.eval]at hv;exact absurd ⟨⟨by tauto,by tauto⟩,⟨by tauto,by tauto⟩⟩ hK'
     ·by_cases h0:opnd D j 0<n+j/\wireVal n D (opnd D j 0) (λ_=>true)=true
      ·have h1:=hd0 _ (λh=>hK' ⟨h0,h⟩)
       exact key _ (by rw[hin];simp) (λx=>by
        rw[hval];simp[hop,GateOp.eval,h0.1]
        exact λhlt hv=>absurd hv (by simp[h1 x hlt])) h0.1 h0.2
      ·have h1:=hd0 _ h0;have h2:opnd D j 1<n+j/\wireVal n D (opnd D j 1) (λ_=>true)=true:=by
        simp[hop,GateOp.eval]at hv;tauto
       exact key _ (by rw[hin];simp) (λx=>by
        rw[hval];simp[hop,GateOp.eval,h2.1]
        exact λhlt hv=>absurd hv (by simp[h1 x hlt])) h2.1 h2.2
   ·obtain⟨h1,h2⟩:=hc k' hk';exact⟨by omega,h2⟩
   ·intro k hk hKk;rcases Nat.lt_or_ge k j with h|h
    ·exact hd k h hKk
    ·exact absurd ((show k=j by omega)▸hKk) hK
theorem lU {n:ℕ} (D:Circuit) (hD:jW D):∃(D':Circuit) (κ:ℕ ->ℕ),IsAO2 n D'/\(wireVal n D D.output (λ_=>true)=true ->circuitFun n D'=circuitFun n D)/\(∀w,wireVal n D w (λ_=>true)=true ->∃w'<n+D'.gates.length,∀x,wireVal n D' w' x=wireVal n D w x)/\(∀k'<D'.gates.length,κ k'<D.gates.length/\eJ n D (κ k')/\(gateAt D' k').op=(gateAt D (κ k')).op/\(∀x,gateVal n D' k' x=gateVal n D (κ k') x)/\∀k''<k',κ k''<κ k')/\(∀k<D.gates.length,eJ n D k ->∃k'<D'.gates.length,κ k'=k)/\(∀a' b',InCone n D' a' b' ->InCone n D (κ a') (κ b')):=by
 obtain⟨g',m',κ,ha,hb,hc,hd,he⟩:=rV (n:=n) hD _ le_rfl;have hlive:∀w,wireVal n D w (λ_=>true)=true ->w<n+D.gates.length:=λw hw=>by
   by_contra h;rw[(a5 D _).2.1 w (by omega)]at hw;cases hw
 obtain⟨o',ho'⟩:∃o',wireVal n D D.output (λ_=>true)=true ->∀x,wireVal n (dY m' g' 0) o' x=wireVal n D D.output x:=by
  by_cases h:wireVal n D D.output (λ_=>true)=true
  ·obtain⟨w',_,h1,_⟩:=hb _ (hlive _ h) h;exact⟨w',λ_=>h1⟩
  ·exact⟨0,λh'=>absurd h' h⟩
 refine⟨dY m' g' o',κ,ha,λh=>funext (ho' h),λw hw=>?_,λk' hk'=>?_,λk hk hK=>?_,λa' b' hc'=>?_⟩
 ·obtain⟨w',h1,h2,_⟩:=hb w (hlive w hw) hw;exact⟨w',by simpa using h1,h2⟩
 ·rw[l1_mk_len]at hk';obtain⟨h1,h2,h3,h4,h5⟩:=hc k' hk';exact⟨h1,h2,by rw[bR hk'];exact h3,h4,h5⟩
 ·simpa using hd k hk hK
 ·exact he a' b' (by simpa using(aZ.mp hc').1) hc'
lemma pJ {m m':ℕ} {κ:ℕ ->ℕ} {K:ℕ ->Prop} (hc:∀k'<m',κ k'<m/\K (κ k')/\∀k''<k',κ k''<κ k') (hd:∀k<m,K k ->∃k'<m',κ k'=k) (S:Finset ℕ):((∀k∈S,k<m/\¬K k) ->m'+S.card≤m)/\((∀k<m,k∉S ->K k) ->m≤m'+S.card):=by
 have hinj:Set.InjOn κ (range m'):=by
  intro a ha b hb hab;simp only[coe_range,Set.mem_Iio]at ha hb;rcases Nat.lt_trichotomy a b with h|h|h
  ·have:=(hc b hb).2.2 a h;omega
  ·exact h
  ·have:=(hc a ha).2.2 b h;omega
 have hcard:=card_image_of_injOn hinj;rw[card_range]at hcard;constructor
 ·intro hS;have hsub:(range m').image κ∪S⊆range m:=by
   intro k hk;simp only[mem_union,mem_image,mem_range]at hk⊢;rcases hk with⟨k',hk',rfl⟩|hk
   ·exact(hc k' hk').1
   ·exact(hS k hk).1
  have hdis:Disjoint ((range m').image κ) S:=by
   rw[disjoint_left];intro k hk hkS;simp only[mem_image,mem_range]at hk;obtain⟨k',hk',rfl⟩:=hk;exact(hS _ hkS).2 (hc k' hk').2.1
  have:=card_le_card hsub;rwa[card_union_of_disjoint hdis,hcard,card_range]at this
 ·intro hS;have hsub:range m⊆(range m').image κ∪S:=by
   intro k hk;simp only[mem_union,mem_image,mem_range]at hk⊢;by_cases hkS:k∈S
   ·exact Or.inr hkS
   ·obtain⟨k',hk',rfl⟩:=hd k hk (hS k hk hkS);exact Or.inl ⟨k',hk',rfl⟩
  have:=(card_le_card hsub).trans (card_union_le _ _);rwa[hcard,card_range]at this
lemma pE {ι:Type} {op:GateOp} (hop:op=GateOp.and\/op=GateOp.or) (l:List ι) (f g:ι ->Bool) (h:∀i∈l,f i=true ->g i=true):op.eval (l.map f)=true ->op.eval (l.map g)=true:=by
 rcases hop with rfl|rfl<;>simp only[GateOp.eval,List.all_map,List.any_map,List.all_eq_true,List.any_eq_true,Function.comp,id]
 ·exact λh1 i hi=>h i hi (h1 i hi)
 ·exact λ⟨i,hi,h1⟩=>⟨i,hi,h i hi h1⟩
lemma dW (h:IsAO2 n C):∀w<n+C.gates.length,wireVal n C w (λ_=>true)=true:=by
 intro w
 induction w using Nat.strong_induction_on with
 |_ w ih=>
  intro hw;rcases Nat.lt_or_ge w n with hn|hn
  ·exact bA C _ ⟨w,hn⟩
  ·obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by omega⟩;have hk:k<C.gates.length:=by omega
   have h0:=ih _ (aH h hk 0) (by have:=aH h hk 0;omega);have h1:=ih _ (aH h hk 1) (by have:=aH h hk 1;omega);rcases eS h hk with hop|hop
   ·rw[(kX h hk _).1 hop,h0,h1];rfl
   ·rw[(kX h hk _).2 hop,h0,h1];rfl
lemma lK {i:ℕ}:∀{j:ℕ},InCone n C i j ->∃r≤j,r<C.gates.length/\n+i∈(gateAt C r).inputs:=by
 intro j
 induction j using Nat.strong_induction_on with
 |_ j ih=>
  intro hc;obtain⟨hj,k,hk,hin,rfl|h3⟩:=aZ.mp hc
  ·exact⟨j,le_rfl,hj,hin⟩
  ·obtain⟨r,hr,h1,h2⟩:=ih k hk h3;exact⟨r,by omega,h1,h2⟩
def gF (n:ℕ) (C:Circuit) (Y Z:Finset ℕ) (k:ℕ):Gate:=⟨(gateAt C k).op,(gateAt C k).inputs.map λw=>if k∈Z\/(n≤w/\w-n∈Y)then n+C.gates.length+1 else w⟩
def bQ (n:ℕ) (C:Circuit) (Y Z:Finset ℕ) (a b:ℕ):Circuit:=dY (C.gates.length+1) (λk=>if k<C.gates.length then gF n C Y Z k else⟨GateOp.or,[a,b]⟩) (n+C.gates.length)
lemma fH (h:IsAO2 n C) (Y Z:Finset ℕ) (a b:ℕ):jW (bQ n C Y Z a b):=by
 intro k hk;simp only[bQ,l1_mk_len]at hk;rw[bQ,bR hk];split_ifs with h1
 ·exact⟨eS h h1,by simp[gF,bO (bZ.mp h).1 h1]⟩
 ·exact⟨Or.inr rfl,rfl⟩
lemma eX (h:IsAO2 n C) (Y Z:Finset ℕ) (a b:ℕ) (x:Fin n ->Bool):∀w<n+C.gates.length,(wireVal n (bQ n C Y Z a b) w x=true ->wireVal n C w x=true)/\((∀y∈Y,gateVal n C y x=false\/¬InCone n C y (w-n)) ->(∀z∈Z,gateVal n C z x=false\/¬(w=n+z\/InCone n C z (w-n))) ->wireVal n (bQ n C Y Z a b) w x=wireVal n C w x):=by
 intro w
 induction w using Nat.strong_induction_on with
 |_ w ih=>
  intro hw;rcases Nat.lt_or_ge w n with hn|hn
  ·have:=(bA (bQ n C Y Z a b) x ⟨w,hn⟩).trans (bA C x ⟨w,hn⟩).symm;exact⟨λh1=>this▸h1,λ_ _=>this⟩
  ·obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by omega⟩;have hk:k<C.gates.length:=by omega
   have hRB:=(bZ.mp h).2 k hk;have hD:=(a5 (bQ n C Y Z a b) x).2.2 k (by simp[bQ];omega);have hg:gateAt (bQ n C Y Z a b) k=gF n C Y Z k:=by
    rw[bQ,bR (by omega)];simp[hk]
   rw[hg]at hD;simp only[gF,List.map_map]at hD;constructor
   ·rw[hD,(a5 C x).2.2 k hk];refine pE (eS h hk) _ _ _ λi hi=>?_;have hik:=hRB i hi;have:=(ih i hik (by omega)).1;simp only[Function.comp,hik,↓reduceIte];split_ifs<;>first|assumption|omega|simp
   ·intro hY hZ;by_cases hkZ:k∈Z
    ·rw[hD,show wireVal n C (n+k) x=false from(hZ k hkZ).resolve_right λh1=>h1 (Or.inl rfl),bO (bZ.mp h).1 hk];rcases eS h hk with hop|hop<;>simp[hop,GateOp.eval,hkZ,show ¬n+C.gates.length+1<n+k by omega]
    ·rw[hD,(a5 C x).2.2 k hk]
     congr 1
     apply List.map_congr_left;intro i hi;have hik:=hRB i hi;have hmem:∀c,n+c=i ->n+c∈(gateAt C k).inputs:=λc hc=>hc▸hi;simp only[Function.comp,hik,↓reduceIte,hkZ,false_or];split_ifs with h1 h2
     ·omega
     ·rcases hY _ h1.2 with h3|h3
      ·rw[show i=n+(i-n) by omega];exact h3.symm
      ·exact absurd (aZ.mpr ⟨hk,i-n,by omega,hmem _ (by omega),Or.inl rfl⟩) (by rwa[show n+k-n=k by omega]at h3)
     ·refine(ih i hik (by omega)).2 (λy hy=>(hY y hy).imp id λh3 h4=>h3 ?_) λz hz=>(hZ z hz).imp id λh3 h4=>h3 (Or.inr ?_)
      ·rw[show n+k-n=k by omega];have:=aP h4;exact aZ.mpr ⟨hk,i-n,by omega,hmem _ (by omega),Or.inr h4⟩
      ·rw[show n+k-n=k by omega];rcases h4 with h4|h4
       ·exact aZ.mpr ⟨hk,z,by omega,hmem _ h4.symm,Or.inl rfl⟩
       ·have:=aP h4;exact aZ.mpr ⟨hk,i-n,by omega,hmem _ (by omega),Or.inr h4⟩
lemma eO (C:Circuit) (Y Z:Finset ℕ) (a b:ℕ):(bQ n C Y Z a b).gates.length=C.gates.length+1/\(bQ n C Y Z a b).output=n+C.gates.length/\(∀k<C.gates.length,gateAt (bQ n C Y Z a b) k=gF n C Y Z k)/\gateAt (bQ n C Y Z a b) C.gates.length=⟨GateOp.or,[a,b]⟩:=by
 refine⟨by simp[bQ],by simp[bQ,dY],λk hk=>?_,?_⟩<;>
  rw[bQ,bR (by omega)]<;>simp[*]
lemma mL (hA:IsAO2 n C) (hF:circuitFun n C=graphFun G ∅) {i:ℕ} (hi:i<C.gates.length) (hb:BelowF G C i) (x:Fin n ->Bool):wireVal n (bQ n C {i} ∅ C.output (n+i)) (n+C.gates.length) x=graphFun G ∅ x:=by
 have hF':wireVal n C C.output x=graphFun G ∅ x:=congrFun hF x;have hval:=eX hA {i} ∅ C.output (n+i) x;obtain⟨hDlen,-,-,hgm⟩:=eO (n:=n) C {i} ∅ C.output (n+i)
 have hvi:=(hval (n+i) (by omega)).2 (λz hz=>Or.inr λh=>by
  have:=aP h;simp at hz;omega) (by simp)
 rw[(a5 _ x).2.2 _ (by omega),hgm];simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id,Bool.or_false,show n+i<n+C.gates.length by omega,↓reduceIte,hvi];cases hv:wireVal n C (n+i) x with
 |true=>rw[hb x hv];simp
 |false=>
  rw[Bool.or_false,←hF'];split_ifs with hlt
  ·exact(hval _ hlt).2 (λz hz=>Or.inl (by
    simp only[mem_singleton]at hz;subst hz;exact hv)) (by simp)
  ·exact((a5 C x).2.1 _ (by omega)).symm
lemma aI {a:ℕ}:a∈tops G C↔a<C.gates.length/\(gateAt C a).op=GateOp.and/\BelowF G C a:=by
 simp[tops,gatesWhere]
lemma aA {k:ℕ}:k∈junk G C↔k<C.gates.length/\(gateAt C k).op=GateOp.and/\¬BelowF G C k:=by
 unfold junk gatesWhere;rw[mem_filter,mem_range];unfold IsDirtyAnd IsDirty BelowF;constructor
 ·rintro⟨h1,h2,_,x,hx,hF⟩;exact⟨h1,h2,λh=>by simp[h x hx]at hF⟩
 ·rintro⟨h1,h2,h3⟩;obtain⟨x,hx⟩:=not_forall.mp h3;exact⟨h1,h2,h1,x,(Classical.not_imp.mp hx).1,by simpa using(Classical.not_imp.mp hx).2⟩
lemma pF (hC:IsLeastAO G C) {i j:ℕ} (hi:i<C.gates.length) (hbi:BelowF G C i) (hopi:(gateAt C i).op=GateOp.and) (hopj:(gateAt C j).op=GateOp.and) (hij:InCone n C i j):∃C':Circuit,IsLeastAO G C'/\C'.size=C.size/\andPairs n C'<andPairs n C/\(junk G C').card=(junk G C).card/\∀k'∈junk G C',∃k∈junk G C,∀x,graphFun G ∅ x=false ->gateVal n C' k' x=gateVal n C k x:=by
 obtain⟨hA,hF,hmin⟩:=hC;have hbi':∀x,wireVal n C (n+i) x=true ->graphFun G ∅ x=true:=hbi;have hDA:=fH hA {i} ∅ C.output (n+i);have hval:=λx=>eX hA {i} ∅ C.output (n+i) x;have hDF:=mL hA hF hi hbi;obtain⟨hDlen,hDout,hgD,hgm⟩:=eO (n:=n) C {i} ∅ C.output (n+i)
 generalize bQ n C {i} ∅ C.output (n+i)=D at*
 have hoff:∀x,graphFun G ∅ x=false ->wireVal n C (n+i) x=false:=λx hx=>by
  by_contra h;have:=hbi' x (by simpa using h);simp_all
 have heq:∀x,wireVal n C (n+i) x=false ->∀w<n+C.gates.length,wireVal n D w x=wireVal n C w x:=λx hx w hw=>(hval x w hw).2 (λz hz=>Or.inl (by
   simp only[mem_singleton]at hz;subst hz;exact hx)) (by simp)
 have hlive:wireVal n D D.output (λ_=>true)=true:=by
  rw[hDout,hDF];exact hbi' _ (dW hA _ (by omega))
 obtain⟨D',κ,hA',hfun,-,hc,hd,he⟩:=lU (n:=n) D hDA
 have hfun':circuitFun n D'=graphFun G ∅:=(hfun hlive).trans (funext λx=>by
  rw[←hDF x,←hDout];rfl)
 obtain⟨r,-,hr,hrin⟩:=lK hij;have hNK:¬eJ n D r:=λhK=>by
  have:=(hK (n+C.gates.length+1) (by
   rw[hgD r hr];simp only[gF,List.mem_map];exact⟨n+i,hrin,by simp⟩)).1
  omega
 have hkc:=pJ (K:=eJ n D) (m:=C.gates.length+1) (λk' hk'=>⟨hDlen▸(hc k' hk').1,(hc k' hk').2.1,(hc k' hk').2.2.2.2⟩) (λk hk=>hd k (hDlen▸hk));have h1:=(hkc {r}).1 (by simp;exact⟨by omega,hNK⟩);have h2:C.gates.length≤D'.gates.length:=hmin D' hA' hfun';have hsz:D'.gates.length=C.gates.length:=by simp at h1;omega
 have hK1:∀k<C.gates.length+1,k≠r ->eJ n D k:=by
  intro k hk hkr;by_contra hnk
  have:=(hkc {r,k}).1 (by
   intro z hz;simp at hz;rcases hz with rfl|rfl
   exacts[⟨by omega,hNK⟩,⟨hk,hnk⟩])
  rw[card_pair (Ne.symm hkr)]at this;omega
 have hκ:∀k'<D'.gates.length,(gateAt D' k').op=GateOp.and ->κ k'<C.gates.length/\(gateAt C (κ k')).op=GateOp.and:=by
  intro k' hk' hop;have h3:=(hc k' hk').1;have h4:=(hc k' hk').2.2.1;rcases Nat.lt_or_ge (κ k') C.gates.length with h|h
  ·exact⟨h,by rw[←hop,h4,hgD _ h];rfl⟩
  ·rw[show κ k'=C.gates.length by omega,hgm]at h4;rw[h4]at hop;cases hop
 have hκinj:∀a<D'.gates.length,∀b<D'.gates.length,κ a=κ b ->a=b:=by
  intro a ha b hb hab;rcases Nat.lt_trichotomy a b with h|h|h
  ·have:=(hc b hb).2.2.2.2 a h;omega
  ·exact h
  ·have:=(hc a ha).2.2.2.2 b h;omega
 have hrb:(gateAt C r).op=GateOp.and ->BelowF G C r:=λhop x hx=>hbi' x (by
  have hin:=bO (bZ.mp hA).1 hr;rw[hin]at hrin;rw[show gateVal n C r x=wireVal n C (n+r) x from rfl,(kX hA hr x).1 hop,Bool.and_eq_true]at hx;simp at hrin;rcases hrin with h|h
  ·exact h▸hx.1
  ·exact h▸hx.2)
 have hmem:∀k'∈junk G D',κ k'∈junk G C/\∀x,graphFun G ∅ x=false ->gateVal n D' k' x=gateVal n C (κ k') x:=by
  intro k' hk';obtain⟨hk',hop,hnb⟩:=aA.mp hk';obtain⟨h3,h4⟩:=hκ k' hk' hop;refine⟨aA.mpr ⟨h3,h4,λhb=>hnb λx hx=>hb x ?_⟩,λx hx=>?_⟩
  ·rw[(hc k' hk').2.2.2.1]at hx;exact(hval x _ (by omega)).1 hx
  ·rw[(hc k' hk').2.2.2.1];exact heq x (hoff x hx) _ (by omega)
 have hcut:∀a b,b<C.gates.length ->InCone n D a b ->InCone n C a b/\a≠i:=by
  intro a b
  induction b using Nat.strong_induction_on with
  |_ b ih=>
   intro hb hcn;obtain⟨-,k,hk,hin,h3⟩:=aZ.mp hcn;rw[hgD b hb]at hin;simp only[gF,List.mem_map]at hin;obtain⟨w0,hw0,hw0e⟩:=hin;split_ifs at hw0e with hz
   ·omega
   ·subst hw0e;have hki:k≠i:=λh=>hz (Or.inr ⟨by omega,by simp[h]⟩);rcases h3 with rfl|h3
    ·exact⟨aZ.mpr ⟨hb,a,hk,hw0,Or.inl rfl⟩,hki⟩
    ·have:=ih k hk (by omega) h3;exact⟨aZ.mpr ⟨hb,k,hk,hw0,Or.inr this.1⟩,this.2⟩
 refine⟨D',⟨hA',hfun',λE hE hEf=>Nat.le_trans (Nat.le_of_eq hsz) (hmin E hE hEf)⟩,hsz,?_,?_,λk' hk'=>⟨_,hmem k' hk'⟩⟩
 ·unfold andPairs;refine lt_of_le_of_lt (card_le_card_of_injOn (λp:ℕ×ℕ=>(κ p.1,κ p.2)) (t:=erase _ (i,j)) ?_ ?_) (card_erase_lt_of_mem ?_)
  ·rintro⟨a',b'⟩ hp;simp only[mem_coe,mem_filter,mem_product,mem_range]at hp;obtain⟨⟨ha',hb'⟩,hopa,hopb,hcone⟩:=hp;obtain⟨h3,h4⟩:=hκ a' ha' hopa;obtain⟨h5,h6⟩:=hκ b' hb' hopb;have hcC:=hcut _ _ h5 (he a' b' hcone);simp only[mem_coe,mem_erase,mem_filter,mem_product,mem_range];exact⟨λh=>hcC.2 (congrArg Prod.fst h),⟨h3,h5⟩,h4,h6,hcC.1⟩
  ·rintro⟨a1,b1⟩ h3 ⟨a2,b2⟩ h4 h5;simp only[mem_coe,mem_filter,mem_product,mem_range]at h3 h4;rw[Prod.mk.injEq]at h5;rw[hκinj a1 h3.1.1 a2 h4.1.1 h5.1,hκinj b1 h3.1.2 b2 h4.1.2 h5.2]
  ·simp only[mem_filter,mem_product,mem_range];exact⟨⟨hi,(aZ.mp hij).1⟩,hopi,hopj,hij⟩
 ·refine card_bij (λk' _=>κ k') (λk' hk'=>(hmem k' hk').1) (λa ha b hb hab=>hκinj a (aA.mp ha).1 b (aA.mp hb).1 hab) λk hk=>?_;obtain⟨hk,hop,hnb⟩:=aA.mp hk;have hkr:k≠r:=λh=>hnb (h▸hrb (h▸hop));obtain⟨k',hk',hkk⟩:=hd k (by omega) (hK1 k (by omega) hkr);subst hkk;refine⟨k',aA.mpr ⟨hk',by rw[(hc k' hk').2.2.1,hgD _ hk];exact hop,λhb=>hnb λx hx=>?_⟩,rfl⟩;by_contra hFx;rw[Bool.not_eq_true]at hFx;have:=hb x (by rw[(hc k' hk').2.2.2.1];exact(heq x (hoff x hFx) _ (by omega)).trans hx)
  simp_all
theorem qG {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]:∀(N:ℕ) (C:Circuit),andPairs n C=N ->IsLeastAO G C ->∃C':Circuit,IsLeastAO G C'/\TopForm G C'/\C'.size=C.size/\(junk G C').card=(junk G C).card/\∀k'∈junk G C',∃k∈junk G C,∀x,graphFun G ∅ x=false ->gateVal n C' k' x=gateVal n C k x:=by
 intro N
 induction N using Nat.strong_induction_on with
 |_ N ih=>
  intro C hN hC;by_cases hT:TopForm G C
  ·exact⟨C,hC,hT,rfl,rfl,λk hk=>⟨k,hk,λ_ _=>rfl⟩⟩
  ·simp only[TopForm,not_forall]at hT;obtain⟨i,hi,j,-,hopi,hbi,hopj,hij⟩:=hT;obtain⟨C₁,hC₁,hs,hlt,hj1,hj2⟩:=pF hC hi hbi hopi hopj (not_not.mp hij);obtain⟨C',h1,h2,h3,h4,h5⟩:=ih _ (hN▸hlt) C₁ rfl hC₁;refine⟨C',h1,h2,h3.trans hs,h4.trans hj1,λk' hk'=>?_⟩;obtain⟨k₁,hk₁,e1⟩:=h5 k' hk';obtain⟨k,hk,e2⟩:=hj2 k₁ hk₁;exact⟨k,hk,λx hx=>(e1 x hx).trans (e2 x hx)⟩
theorem l1_normalize {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (hC:IsLeastAO G C) (hoff:∀k∈junk G C,∀v:Fin n,gateVal n C k (unitInput v)=false):∃C':Circuit,IsLeastAO G C'/\TopForm G C'/\C'.size=C.size/\(junk G C').card=(junk G C).card/\∀k∈junk G C',∀v:Fin n,gateVal n C' k (unitInput v)=false:=by
 obtain⟨C',h1,h2,h3,h4,h5⟩:=qG G _ C rfl hC;refine⟨C',h1,h2,h3,h4,λk hk v=>?_⟩;obtain⟨k₀,hk₀,e⟩:=h5 k hk;rw[e _ (e8 v)];exact hoff k₀ hk₀ v
section
open Finset
lemma aQ (h4:NoFourCycle G) {a b w w':Fin n} (hab:a≠b) (h1:G.Adj a w) (h2:G.Adj b w) (h3:G.Adj a w') (h5:G.Adj b w'):w=w':=card_le_one.mp (h4 a b hab) w (by simp[h1,h2]) w' (by simp[h3,h5])
lemma bT {n:ℕ} {G:SimpleGraph (Fin n)} {U U':Finset (Sym2 (Fin n))} {W W':Finset (Fin n)} (hU:U'⊆U) (hW:W'⊆W) (h:aB G U W):aB G U' W':=h.elim λz hz=>⟨z,λw hw=>⟨(hz w (hW hw)).1,λh'=>(hz w (hW hw)).2 (hU h')⟩⟩
lemma aU {n:ℕ} {G:SimpleGraph (Fin n)} {U:Finset (Sym2 (Fin n))} {W:Finset (Fin n)} (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (h:aB G U W):∃c:Bool,∀w∈W,col w=c:=h.elim λz hz=>⟨!col z,λw hw=>Bool.eq_not_of_ne (hcol z w (hz w hw).1).symm⟩
lemma a4 (h4:NoFourCycle G) {U:Finset (Sym2 (Fin n))} (hU:U⊆G.edgeFinset) {W:Finset (Fin n)} (h:aB G U W) (a z':Fin n) (hz:G.Adj a z'):(W∩insert z' (aE U a)).card≤1:=by
 obtain⟨z,hzW⟩:=h;refine card_le_one.mpr λw hw w' hw'=>?_;simp[aE]at hw hw';have ha:∀v,v=z'\/s(a,v)∈U ->G.Adj a v:=by
  rintro v (rfl|h);exacts[hz,by simpa using hU h]
 by_cases e:z=a
 ·subst e;rw[hw.2.resolve_right (hzW w hw.1).2,hw'.2.resolve_right (hzW w' hw'.1).2]
 ·exact aQ h4 e (hzW w hw.1).1 (ha w hw.2) (hzW w' hw'.1).1 (ha w' hw'.2)
lemma aF (h4:NoFourCycle G) {U:Finset (Sym2 (Fin n))} (hU:U⊆G.edgeFinset) {W:Finset (Fin n)} (h:aB G U W) (a:Fin n):(W∩aE U a).card≤1:=by
 rcases (W∩aE U a).eq_empty_or_nonempty with e|⟨w,hw⟩
 ·simp[e]
 ·exact(card_le_card (inter_subset_inter_left (subset_insert _ _))).trans (a4 h4 hU h a w (by simpa using hU (mem_filter.mp (mem_inter.mp hw).2).2))
lemma pA {n:ℕ} {G:SimpleGraph (Fin n)} (U:Finset (Sym2 (Fin n))) (p:Fin n) {B W:Finset (Fin n)} (hB:∀b∈B,G.Adj p b) (hW:W⊆B):aB G (U\B.image λb=>s(p,b)) W:=⟨p,λw hw=>⟨hB w (hW hw),λh=>(mem_sdiff.mp h).2 (mem_image.mpr ⟨w,hW hw,rfl⟩)⟩⟩
lemma aK {ν α:Type} [DecidableEq α] {J:ν ->Prop} {l r:ν ->ν} {rk:ν ->ℕ} {f:ν ->Finset α} (hD:dB J l r rk f) {w h:ν} (hr:aM J l r w h):f h⊆f w:=by
 induction hr with
 |refl=>exact subset_rfl
 |tail _ hs ih=>
  obtain⟨hJ,rfl|rfl⟩:=hs<;>rw[(hD _ hJ).2.2]at ih;exacts[union_subset_left ih,union_subset_right ih]
lemma rR {ν α:Type} [DecidableEq α] {J:ν ->Prop} {l r:ν ->ν} {rk:ν ->ℕ} {f:ν ->Finset α} (hD:dB J l r rk f) {w h:ν} (hr:aM J l r w h):rk h≤rk w/\(rk w≤rk h ->h=w):=by
 induction hr with
 |refl=>exact⟨le_rfl,λ_=>rfl⟩
 |tail _ hs ih=>
  have:=hD _ hs.1;rcases hs.2 with rfl|rfl<;>exact⟨by omega,λ_=>by omega⟩
theorem cU {ν α:Type} [DecidableEq ν] [DecidableEq α] {J:ν ->Prop} {l r:ν ->ν} {rk:ν ->ℕ} {f:ν ->Finset α} (hD:dB J l r rk f) (S:Finset α) (R:Finset ν) (hleaf:∀w∈R,∀u,aM J l r w u ->¬J u ->(f u∩S).card≤1):∃P:Finset ν,(∀h∈P,J h/\(∃w∈R,aM J l r w h)/\¬(f (l h)∩S⊆f (r h))/\¬(f (r h)∩S⊆f (l h)))/\(R.biUnion f∩S).card≤R.card+P.card:=by
 induction hm:∑w∈R,3^rk w using Nat.strong_induction_on generalizing R with|_ m ih
 rcases R.eq_empty_or_nonempty with rfl|hne
 ·exact⟨∅,by simp,by simp⟩
 obtain⟨w,hw,hmax⟩:=exists_max_image R rk hne;have hsum:=add_sum_erase R (λu=>3^rk u) hw;have hcard:=card_erase_add_one hw;have hbU:R.biUnion f=f w∪(R.erase w).biUnion f:=by
  rw[←biUnion_insert,insert_erase hw]
 have hins:∀(a:ν) (T:Finset ν),∑u∈insert a T,3^rk u≤3^rk a+∑u∈T,3^rk u/\(insert a T).card≤T.card+1:=λa T=>⟨by by_cases ha:a∈T<;>simp[ha],card_insert_le a T⟩;have step:∀(R':Finset ν) (e:ℕ),∑u∈R',3^rk u<m ->(∀u∈R',∃v∈R,aM J l r v u) ->(R.biUnion f∩S).card+R'.card≤(R'.biUnion f∩S).card+R.card+e ->∃P':Finset ν,(∀h∈P',J h/\(∃v∈R,aM J l r v h)/\_)/\(∀h∈P',∃u∈R',aM J l r u h)/\(R.biUnion f∩S).card≤R.card+P'.card+e:=λR' e h1 h2 h3=>by
  obtain⟨P',hP',hc⟩:=ih _ h1 R' (λu hu x hx=>(h2 u hu).elim λv hv=>hleaf v hv.1 x (hv.2.trans hx)) rfl;exact⟨P',λh hh=>⟨(hP' h hh).1,(hP' h hh).2.1.elim λu hu=>(h2 u hu.1).elim λv hv=>⟨v,hv.1,hv.2.trans hu.2⟩,(hP' h hh).2.2⟩,λh hh=>(hP' h hh).2.1,by omega⟩
 have hpos:0<3^rk w:=by positivity
 by_cases hJ:J w
 swap
 ·obtain⟨P',hP',-,hc⟩:=step (R.erase w) 0 (by omega) (λu hu=>⟨u,mem_of_mem_erase hu, .refl⟩) (by
    rw[hbU,union_inter_distrib_right];have:=card_union_le (f w∩S) ((R.erase w).biUnion f∩S);have:=hleaf w hw w .refl hJ
    omega)
  exact⟨P',hP',hc⟩
 obtain⟨hl,hr,hf⟩:=hD w hJ;have hpow:∀c,c=l w\/c=r w ->3^rk c*3≤3^rk w:=λc hc=>by
  rw[←pow_succ];exact Nat.pow_le_pow_right (by norm_num) (by rcases hc with rfl|rfl<;>omega)
 have hR':∀c,c=l w\/c=r w ->∀u∈insert c (R.erase w),∃v∈R,aM J l r v u:=λc hc u hu=>(mem_insert.mp hu).elim (λe=>⟨w,hw, .single ⟨hJ,e▸hc⟩⟩) λh=>⟨u,mem_of_mem_erase h, .refl⟩;by_cases hreal:¬(f (l w)∩S⊆f (r w))/\¬(f (r w)∩S⊆f (l w))
 ·have i1:=hins (l w) (insert (r w) (R.erase w));have i2:=hins (r w) (R.erase w);obtain⟨P',hP',hP2,hc⟩:=step (insert (l w) (insert (r w) (R.erase w))) 1 (by have:=hpow _ (.inl rfl);have:=hpow _ (.inr rfl);omega) (λu hu=>(mem_insert.mp hu).elim (λe=>hR' _ (.inl rfl) u (e▸mem_insert_self _ _)) (hR' _ (.inr rfl) u)) (by rw[hbU,biUnion_insert,biUnion_insert,hf,union_assoc];omega);have hn:w∉P':=λhwP=>by
   obtain⟨u,hu,huw⟩:=hP2 w hwP;have h1:=rR hD huw;simp only[mem_insert,mem_erase]at hu;rcases hu with rfl|rfl|⟨hne,hu⟩;exacts[by omega,by omega,hne (h1.2 (hmax u hu)).symm]
  exact⟨insert w P',λh hh=>(mem_insert.mp hh).elim (λe=>e▸⟨hJ,⟨w,hw, .refl⟩,hreal⟩) (hP' h),by rw[card_insert_of_notMem hn];omega⟩
 ·obtain⟨c,hc,hsub⟩:∃c,(c=l w\/c=r w)/\f w∩S⊆f c:=by
   rw[hf,union_inter_distrib_right];by_cases h1:f (l w)∩S⊆f (r w)
   ·exact⟨_, .inr rfl,union_subset h1 inter_subset_left⟩
   ·exact⟨_, .inl rfl,union_subset inter_subset_left (not_not.mp λh2=>hreal ⟨h1,h2⟩)⟩
  have i1:=hins c (R.erase w)
  obtain⟨P',hP',-,hc'⟩:=step (insert c (R.erase w)) 0 (by have:=hpow c hc;omega) (hR' c hc) (by
    rw[hbU,biUnion_insert,union_inter_distrib_right,union_inter_distrib_right];have:=card_le_card (union_subset_union_left (t:=(R.erase w).biUnion f∩S) (subset_inter hsub inter_subset_right))
    omega)
  exact⟨P',hP',hc'⟩
theorem d8 {ν α:Type} [DecidableEq ν] [DecidableEq α] {J:ν ->Prop} {l r:ν ->ν} {rk:ν ->ℕ} {f:ν ->Finset α} (hD:dB J l r rk f) (Fr:Finset α ->Prop) (S:Finset α) (w:ν) (hS:S⊆f w) (hsp:∀W,Fr W ->(W∩S).card≤1) (hleaf:∀u,aM J l r w u ->¬J u ->Fr (f u)\/(f u).card≤1):∃P:Finset ν,(∀h∈P,J h/\aM J l r w h/\¬Fr (f h)/\1<(f h∩S).card)/\S.card≤P.card+1:=by
 obtain⟨P,hP,hc⟩:=cU hD S {w} λv hv u hu hJ=>by
  rw[mem_singleton.mp hv]at hu;exact(hleaf u hu hJ).elim (hsp _) (card_le_card inter_subset_left).trans
 refine⟨P,λh hh=>?_,by simpa[inter_eq_right.mpr hS,add_comm]using hc⟩;obtain⟨hJ,⟨v,hv,hvh⟩,h1,h2⟩:=hP h hh;rw[mem_singleton.mp hv]at hvh;have h3:1<(f h∩S).card:=by
  obtain⟨a,ha,ha'⟩:=not_subset.mp h1;obtain⟨b,hb,hb'⟩:=not_subset.mp h2;rw[one_lt_card,(hD h hJ).2.2];exact⟨a,by grind,b,by grind,by grind⟩
 exact⟨hJ,hvh,λhF=>not_lt.mpr (hsp _ hF) h3,h3⟩
theorem eU {ν α:Type} [DecidableEq ν] [DecidableEq α] {J:ν ->Prop} {l r:ν ->ν} {rk:ν ->ℕ} {f:ν ->Finset α} (hD:dB J l r rk f) (Fr:Finset α ->Prop) (w:ν) (a b:α) (hab:a≠b) (ha:a∈f w) (hb:b∈f w) (hsp:∀W,Fr W ->¬(a∈W/\b∈W)) (hleaf:∀u,aM J l r w u ->¬J u ->Fr (f u)\/(f u).card≤1):∃h,J h/\aM J l r w h/\¬Fr (f h)/\a∈f h/\b∈f h:=by
 have key:∀W:Finset α,1<(W∩{a,b}).card ->a∈W/\b∈W:=λW hW=>by
  rw[one_lt_card]at hW
  grind
 obtain⟨P,hP,hc⟩:=d8 hD Fr {a,b} w (insert_subset ha (singleton_subset_iff.mpr hb)) (λW hW=>not_lt.mp λh=>hsp W hW (key W h)) hleaf;rw[card_pair hab]at hc;obtain⟨h,hh⟩:=card_pos.mp (by omega:0<P.card);exact⟨h,(hP h hh).1,(hP h hh).2.1,(hP h hh).2.2.1,key _ (hP h hh).2.2.2⟩
def kA (a0 a1 a2 l0 l1 l2 r0 r1 r2:Bool):Bool:=(a0&&l0|| !a0&&r0)||(a1&&l1|| !a1&&r1)||(a2&&l2|| !a2&&r2)
lemma u7:∀a b c d e f g h i:Bool,a=true ->e=true ->i=true ->(a&&d&&b&&e)=false ->(a&&d&&c&&f)=false ->(b&&e&&c&&f)=false ->(a&&g&&b&&h)=false ->(a&&g&&c&&i)=false ->(b&&h&&c&&i)=false ->(d&&g&&e&&h)=false ->(d&&g&&f&&i)=false ->(e&&h&&f&&i)=false ->∀t u v x y z:Bool,∃l m n p q r:Bool,(l&&(p&&a||q&&b||r&&c)||m&&(p&&d||q&&e||r&&f)||n&&(p&&g||q&&h||r&&i))=false/\(l||m||n)=true/\(p||q||r)=true/\kA t u v l m n p q r=true/\kA x y z l m n p q r=true:=by
 decide
def kY {n:ℕ} (G:SimpleGraph (Fin n)) (col:Fin n ->Bool) (S:Fin 4 ->Finset (Fin n)) (a b:Fin n):Prop:=G.Adj a b/\col a=false/\col b=true/\∀k,a∈S k\/b∈S k
lemma rK {n:ℕ} {G:SimpleGraph (Fin n)} {col:Fin n ->Bool} (hcol:∀u v,G.Adj u v ->col u≠col v) {S:Fin 4 ->Finset (Fin n)} {u v:Fin n} (hA:G.Adj u v) (hk:∀k,u∈S k\/v∈S k):kY G col S u v\/kY G col S v u:=by
 have h:=hcol u v hA;cases hc:col u
 ·exact .inl ⟨hA,hc,by simpa[hc]using h.symm,hk⟩
 ·exact .inr ⟨hA.symm,by simpa[hc]using h.symm,hc,λk=>(hk k).symm⟩
lemma s5 {col:Fin n ->Bool} (hcol:∀u v,G.Adj u v ->col u≠col v) (h4:NoFourCycle G) {S:Fin 4 ->Finset (Fin n)} (hH:∀x:Fin n ->Bool,(∀k,∃v∈S k,x v=true) ->graphFun G ∅ x=true) {L0 R0 L1 R1 L2 R2:Fin n} (o0:kY G col S L0 R0) (o1:kY G col S L1 R1) (o2:kY G col S L2 R2) (hd:L0≠L1/\L0≠L2/\L1≠L2/\R0≠R1/\R0≠R2/\R1≠R2):False:=by
 obtain⟨a,b,c,d,e,g⟩:=hd;have miss:∀x:Fin n ->Bool,(∀u v,G.Adj u v ->x u=true ->x v=true ->False) ->∃k,∀v∈S k,x v=false:=λx hx=>by
  by_contra! hc;have h:=hH x λk=>(hc k).imp λv h=>⟨h.1,by simpa using h.2⟩;simp[graphFun]at h;obtain⟨u,v,h⟩:=h;exact hx u v h.1 h.2.1 h.2.2
 obtain⟨kR,hkR⟩:=miss (λv=> !col v) λu v h hu hv=>hcol u v h (by simp_all);obtain⟨kL,hkL⟩:=miss col λu v h hu hv=>hcol u v h (hu.trans hv.symm);have hLk:∀{a b},kY G col S a b ->a∈S kL/\a∉S kR:=λo=>⟨(o.2.2.2 kL).resolve_right λh=>absurd o.2.2.1 (by simp[hkL _ h]),λh=>by simpa[o.2.1]using hkR _ h⟩;have hm:∀{a b w w':Fin n},a≠b ->w≠w' ->(decide (G.Adj a w)&&decide (G.Adj b w)&&decide (G.Adj a w')&&decide (G.Adj b w'))=false:=λhab hww=>by
  simpa using λh1 h2 h3 h5=>hww (aQ h4 hab h1 h2 h3 h5)
 obtain⟨ka,kb,hk⟩:=(by decide:∀a b:Fin 4,a≠b ->∃c d:Fin 4,∀k,k=a\/k=b\/k=c\/k=d) kL kR λe=>(hLk o0).2 (e▸(hLk o0).1);obtain⟨l0,l1,l2,r0,r1,r2,hi,h1,h2,h3,h5⟩:=u7 _ _ _ _ _ _ _ _ _ (decide_eq_true o0.1) (decide_eq_true o1.1) (decide_eq_true o2.1) (hm a d) (hm a e) (hm a g) (hm b d) (hm b e) (hm b g) (hm c d) (hm c e) (hm c g) (decide (L0∈S ka)) (decide (L1∈S ka)) (decide (L2∈S ka)) (decide (L0∈S kb)) (decide (L1∈S kb)) (decide (L2∈S kb))
 let x:Fin n ->Bool:=λv=>if col v then
  r0&&decide (v=R0)||r1&&decide (v=R1)||r2&&decide (v=R2)else
  l0&&decide (v=L0)||l1&&decide (v=L1)||l2&&decide (v=L2)
 have key:∀u v,G.Adj u v ->x u=true ->x v=true ->col u=false ->col v=true ->False:=λu v huv hu hv cu cv=>by
  simp[x,cu,cv]at hu hv;rcases hu with(⟨hl,rfl⟩|⟨hl,rfl⟩)|⟨hl,rfl⟩<;>
  rcases hv with(⟨hr,rfl⟩|⟨hr,rfl⟩)|⟨hr,rfl⟩<;>simp[hl,hr,huv]at hi
 obtain⟨k,hk'⟩:=miss x λu v huv hu hv=>by
  cases hc:col u<;>cases hc':col v;exacts[hcol u v huv (hc.trans hc'.symm),key u v huv hu hv hc hc',key v u huv.symm hv hu hc' hc,hcol u v huv (hc.trans hc'.symm)]
 have hit:kA (decide (L0∈S k)) (decide (L1∈S k)) (decide (L2∈S k)) l0 l1 l2 r0 r1 r2=true:=by
  rcases hk k with rfl|rfl|rfl|rfl;exacts[by simpa[kA,hLk o0,hLk o1,hLk o2]using h1,by simpa[kA,hLk o0,hLk o1,hLk o2]using h2,h3,h5]
 simp[kA]at hit;have cs:=And.intro o0.2.1 (And.intro o1.2.1 (And.intro o2.2.1 (And.intro o0.2.2.1 (And.intro o1.2.2.1 o2.2.2.1))));rcases hit with((⟨m,e⟩|⟨m,e⟩)|(⟨m,e⟩|⟨m,e⟩))|(⟨m,e⟩|⟨m,e⟩)<;>first
  |simpa[x,e,cs]using hk' _ m
  |simpa[x,e,cs]using hk' _ ((o0.2.2.2 k).resolve_left m)
  |simpa[x,e,cs]using hk' _ ((o1.2.2.2 k).resolve_left m)
  |simpa[x,e,cs]using hk' _ ((o2.2.2.2 k).resolve_left m)
theorem p4 (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (h4:NoFourCycle G) (S:Fin 4 ->Finset (Fin n)) (hH:∀x:Fin n ->Bool,(∀k,∃v∈S k,x v=true) ->graphFun G ∅ x=true) (x y:Fin 3 ->Fin n) (hadj:∀i,G.Adj (x i) (y i)) (hacc:∀i k,x i∈S k\/y i∈S k) (hdis:∀i j,i≠j ->x i≠x j/\x i≠y j/\y i≠y j):False:=by
 rcases rK hcol (hadj 0) (hacc 0)with o0|o0<;>
 rcases rK hcol (hadj 1) (hacc 1)with o1|o1<;>
 rcases rK hcol (hadj 2) (hacc 2)with o2|o2<;>
 exact s5 hcol h4 hH o0 o1 o2 (by grind)
theorem gY (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (h4:NoFourCycle G) (S:Fin 4 ->Finset (Fin n)) (hH:∀x:Fin n ->Bool,(∀k,∃v∈S k,x v=true) ->graphFun G ∅ x=true) (U:Finset (Sym2 (Fin n))) (hU:U⊆G.edgeFinset) (hacc:∀e∈U,∀k,∃v∈S k,v∈e):∃Q:Finset (Fin n),Q.card≤2/\∀e∈U,∃v∈Q,v∈e:=by
 have ho:∀e∈U,∃a b,e=s(a,b)/\kY G col S a b:=λe he=>by
  induction e using Sym2.ind with|_ u v=>?_
  exact(rK hcol (by simpa using hU he) λk=>by
   simpa[and_or_left,exists_or]using hacc _ he k).elim
   (λo=>⟨u,v,rfl,o⟩) λo=>⟨v,u,Sym2.eq_swap,o⟩
 by_contra hcon;have hN:∀p q:Fin n,∃a b,kY G col S a b/\a≠p/\b≠p/\a≠q/\b≠q:=λp q=>by
  by_contra h;refine hcon ⟨{p,q},card_le_two,λe he=>?_⟩;obtain⟨a,b,rfl,o⟩:=ho e he;by_contra h';exact h ⟨a,b,o,by simp at h';grind⟩
 obtain⟨e,he⟩:U.Nonempty:=nonempty_of_ne_empty λh=>hcon ⟨∅,by simp,by simp[h]⟩;obtain⟨a1,b1,-,e1⟩:=ho e he;obtain⟨a2,b2,e2,n1,-,-,n2⟩:=hN a1 b1;obtain⟨x1,y1,f1,m1,-,m2,-⟩:=hN a1 a2;obtain⟨x4,y4,f4,-,m3,-,m4⟩:=hN b1 b2;obtain⟨x2,y2,f2,m5,-,-,m6⟩:=hN a1 b2;obtain⟨x3,y3,f3,-,m7,m8,-⟩:=hN b1 a2;have N:= @s5 n G _ col hcol h4 S hH;have:=N e1 e2 f1;have:=N e1 e2 f4;have:=N e1 e2 f2;have:=N e1 e2 f3;have:=N f1 f4 e2;have:=N f3 f4 e1;have:=N f1 f3 e2;have:=N f1 f4 f3;have:=N f2 f4 e2;have:=N f1 f2 e1;have:=N f1 f4 f2;have:=N f1 f4 e1
 grind (splits:=40)
end
lemma jB {k:ℕ}:k∈orT G C↔k<C.gates.length/\(gateAt C k).op=GateOp.or/\BelowF G C k:=by
 simp[orT,gatesWhere]
lemma dS {k:ℕ}:k∈orN G C↔k<C.gates.length/\(gateAt C k).op=GateOp.or/\¬BelowF G C k:=by
 simp[orN,gatesWhere]
lemma tJ (h:IsAO2 n C):C.size=(tops G C).card+(junk G C).card+(orT G C).card+(orN G C).card:=by
 have hU:range C.gates.length=((tops G C∪junk G C)∪orT G C)∪orN G C:=by
  ext k;simp only[mem_range,mem_union,aI,aA,jB,dS];constructor
  ·intro hk;rcases eS h hk with hop|hop<;>by_cases hb:BelowF G C k<;>simp[hk,hop,hb]
  ·tauto
 rw[Circuit.size,←card_range C.gates.length,hU,card_union_of_disjoint,card_union_of_disjoint,card_union_of_disjoint]<;>
 ·simp only[disjoint_left,mem_union,aI,aA,jB,dS]
  grind
lemma aO (h:IsAO2 n C) (x:Fin n ->Bool) {g:ℕ}:∀{w:ℕ},OrReaches n C w g ->gateVal n C g x=true ->wireVal n C w x=true:=by
 intro w
 induction w using Nat.strong_induction_on with
 |_ w ih=>
  intro hr hg;obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by have:=hr.1;omega⟩;obtain⟨hk,rfl|⟨hop,h1|h1⟩⟩:=(dN h).mp hr
  ·exact hg
  ·rw[(kX h hk x).2 hop,ih _ (aH h hk 0) h1 hg];rfl
  ·rw[(kX h hk x).2 hop,ih _ (aH h hk 1) h1 hg];simp
def bX (n:ℕ) (C:Circuit) (w:ℕ):Prop:=n≤w/\w-n<C.gates.length/\(gateAt C (w-n)).op=GateOp.or
def bF (n:ℕ) (C:Circuit) (w:ℕ):ℕ:=opnd C (w-n) 0
def bI (n:ℕ) (C:Circuit) (w:ℕ):ℕ:=opnd C (w-n) 1
lemma a7 {k:ℕ}:bX n C (n+k)↔k<C.gates.length/\(gateAt C k).op=GateOp.or:=by
 simp[bX]
lemma aJ (h:IsAO2 n C):dB (bX n C) (bF n C) (bI n C) id (orIn n C):=by
 intro w hw;obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by have:=hw.1;omega⟩;obtain⟨hk,hop⟩:=a7.mp hw;simp only[show n+k-n=k by omega,bF,bI,id];exact⟨aH h hk 0,aH h hk 1,dO h hk hop⟩
lemma cK (h:IsAO2 n C) {w g:ℕ}:OrReaches n C w g↔g<C.gates.length/\aM (bX n C) (bF n C) (bI n C) w (n+g):=by
 constructor
 ·induction w using Nat.strong_induction_on with
  |_ w ih=>
   intro hr;obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by have:=hr.1;omega⟩;obtain⟨hk,rfl|⟨hop,h1⟩⟩:=(dN h).mp hr
   ·exact⟨hk,Relation.ReflTransGen.refl⟩
   ·have hJ:bX n C (n+k):=a7.mpr ⟨hk,hop⟩;rcases h1 with h1|h1
    ·exact⟨(aX h1).2,Relation.ReflTransGen.head ⟨hJ,Or.inl (by simp[bF])⟩ (ih _ (aH h hk 0) h1).2⟩
    ·exact⟨(aX h1).2,Relation.ReflTransGen.head ⟨hJ,Or.inr (by simp[bI])⟩ (ih _ (aH h hk 1) h1).2⟩
 ·rintro⟨hg,hr⟩;unfold aM at hr
  induction hr using Relation.ReflTransGen.head_induction_on with
  |refl=>exact bD.mpr ⟨hg,Or.inl rfl⟩
  | @head a c hstep _ ih=>
   obtain⟨hJ,hc⟩:=hstep;obtain⟨k,rfl⟩:∃k,a=n+k:=⟨a-n,by have:=hJ.1;omega⟩;obtain⟨hk,hop⟩:=a7.mp hJ;simp only[show n+k-n=k by omega,bF,bI]at hc;exact(dN h).mpr ⟨hk,Or.inr ⟨hop,by rcases hc with rfl|rfl;exacts[Or.inl ih,Or.inr ih]⟩⟩
lemma a6 (h:IsAO2 n C) {w g:ℕ} (hr:OrReaches n C w g):orIn n C (n+g)⊆orIn n C w:=aK (aJ h) ((cK h).mp hr).2
lemma bY (h:IsAO2 n C) {w:ℕ} {v:Fin n} (hv:v∈orIn n C w) {x:Fin n ->Bool} (hx:x v=true):wireVal n C w x=true:=(kU h x w).mpr (Or.inl ⟨v,hv,hx⟩)
lemma cE (h:IsAO2 n C) {a:ℕ} (ha:a∈tops G C) {u v:Fin n} (hu:u∈side C a 0) (hv:v∈side C a 1):G.Adj u v:=by
 obtain⟨hk,hop,hb⟩:=aI.mp ha;refine(aT u v).mp (hb _ ?_);rw[show gateVal n C a _=wireVal n C (n+a) _ from rfl,(kX h hk _).1 hop,bY h hu (by simp[pairInput]),bY h hv (by simp[pairInput])];rfl
lemma qI (h:IsAO2 n C) (h4:NoFourCycle G) {a:ℕ} (ha:a∈tops G C):(side (n:=n) C a 0).card≤1\/(side (n:=n) C a 1).card≤1:=by
 by_contra hcon;simp only[not_or,not_le]at hcon;obtain⟨u,hu,u',hu',huu⟩:=one_lt_card.mp hcon.1;obtain⟨v,hv,v',hv',hvv⟩:=one_lt_card.mp hcon.2;exact hvv (aQ h4 huu (cE h ha hu hv) (cE h ha hu' hv) (cE h ha hu hv') (cE h ha hu' hv'))
lemma qA (h:IsAO2 n C) {a:ℕ}:∀{k:ℕ},InCone n C a k ->OrReaches n C (n+k) a\/∃k₂,(gateAt C k₂).op=GateOp.and/\InCone n C a k₂:=by
 intro k
 induction k using Nat.strong_induction_on with
 |_ k ih=>
  intro hc;obtain⟨hk,k1,hk1,hin,h3⟩:=aZ.mp hc;rcases eS h hk with hop|hop
  ·exact Or.inr ⟨k,hop,hc⟩
  ·have hup:OrReaches n C (n+k1) a ->OrReaches n C (n+k) a:=λh1=>bD.mpr ⟨hk,Or.inr ⟨hop,_,hin,by omega,h1⟩⟩;rcases h3 with rfl|h3
   ·exact Or.inl (hup (bD.mpr ⟨by omega,Or.inl rfl⟩))
   ·exact(ih k1 hk1 h3).imp hup id
lemma eD {n:ℕ} (D:Circuit) (hD:jW D) (hl:wireVal n D D.output (λ_=>true)=true) (S:Finset ℕ) (hS:∀k∈S,k<D.gates.length/\¬eJ n D k):∃C':Circuit,IsAO2 n C'/\circuitFun n C'=circuitFun n D/\C'.size+S.card≤D.size:=by
 obtain⟨D',κ,hA',hfun,-,hc,hd,-⟩:=lU (n:=n) D hD;exact⟨D',hA',hfun hl,(pJ (K:=eJ n D) (λk' hk'=>⟨(hc k' hk').1,(hc k' hk').2.1,(hc k' hk').2.2.2.2⟩) hd S).1 hS⟩
lemma kT (hC:IsLeastAO G C) (hT:TopForm G C) {a:ℕ} (ha:a∈tops G C):OrReaches n C C.output a:=by
 by_contra hno;obtain⟨hA,hF,hmin⟩:=hC;obtain⟨hk,hop,hb⟩:=aI.mp ha;have hne:¬(C.output=n+a\/InCone n C a (C.output-n)):=by
  rintro(h|h)
  ·exact hno (h▸bD.mpr ⟨hk,Or.inl rfl⟩)
  ·have hlt:=aP h;rcases qA hA h with h1|⟨k₂,hop₂,hc₂⟩
   ·rw[show n+(C.output-n)=C.output by omega]at h1;exact hno h1
   ·exact hT a hk k₂ (aZ.mp hc₂).1 hop hb hop₂ hc₂
 have hDA:=fH hA ∅ {a} C.output (n+C.gates.length+1);have hval:=λx=>eX hA ∅ {a} C.output (n+C.gates.length+1) x;obtain⟨hDlen,hDout,hgD,hgm⟩:=eO (n:=n) C ∅ {a} C.output (n+C.gates.length+1)
 generalize bQ n C ∅ {a} C.output (n+C.gates.length+1)=D at*
 have hDF:∀x,wireVal n D D.output x=wireVal n C C.output x:=λx=>by
  rw[hDout,(a5 D x).2.2 _ (by omega),hgm];simp only[GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id,Bool.or_false,show ¬n+C.gates.length+1<n+C.gates.length by omega,↓reduceIte];split_ifs with hlt
  ·exact(hval x _ hlt).2 (by simp) λz hz=>Or.inr (by simp at hz;subst hz;exact hne)
  ·exact((a5 C x).2.1 _ (by omega)).symm
 have hl:wireVal n D D.output (λ_=>true)=true:=by
  have:=hb _ (dW hA (n+a) (by omega));rw[←hF]at this;rw[hDF];exact this
 obtain⟨C',hA',hfun,hsz⟩:=eD (n:=n) D hDA hl {a,C.gates.length} (by
  intro k hk';simp only[mem_insert,mem_singleton]at hk';rcases hk' with rfl|rfl
  ·refine⟨by omega,λhK=>?_⟩
   have:=(hK (n+C.gates.length+1) (by
    rw[hgD _ hk,gF,bO (bZ.mp hA).1 hk];simp)).1
   omega
  ·refine⟨by omega,λhK=>?_⟩;have:=(hK (n+C.gates.length+1) (by rw[hgm];simp)).1
   omega)
 have:=hmin C' hA' (hfun.trans (funext λx=>(hDF x).trans (congrFun hF x)));rw[card_pair (by omega)]at hsz;simp only[Circuit.size]at this hsz;omega
open Classical in
noncomputable def fX (n:ℕ) (C:Circuit) (w:ℕ):Finset ℕ:=(range C.gates.length).filter λk=>(gateAt C k).op=GateOp.and/\OrReaches n C w k
lemma fQ {w k:ℕ}:k∈fX n C w↔(gateAt C k).op=GateOp.and/\OrReaches n C w k:=by
 simp only[fX,mem_filter,mem_range,and_iff_right_iff_imp];exact λh=>(aX h.2).2
lemma r3 (h:IsAO2 n C):dB (bX n C) (bF n C) (bI n C) id (fX n C):=by
 intro w hw;obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by have:=hw.1;omega⟩;obtain⟨hk,hop⟩:=a7.mp hw;simp only[show n+k-n=k by omega,bF,bI,id];refine⟨aH h hk 0,aH h hk 1,?_⟩;ext g;simp only[fQ,mem_union,dN h,hk,true_and,hop];constructor
 ·rintro⟨hg,rfl|h1⟩
  ·rw[hop]at hg;cases hg
  ·tauto
 ·tauto
lemma p7 (hC:IsLeastAO G C) (hT:TopForm G C):(tops G C).card≤(orT G C).card+1:=by
 have hA:=hC.1
 obtain⟨P,hP,hcard⟩:=cU (r3 hA) (tops G C) {C.output} (by
  intro w _ u _ hu;refine(card_le_card inter_subset_left).trans (card_le_one.mpr ?_);have:∀g∈fX n C u,g=u-n:=λg hg=>by
   obtain⟨_,hr⟩:=fQ.mp hg;obtain⟨k,rfl⟩:∃k,u=n+k:=⟨u-n,by have:=hr.1;omega⟩;obtain⟨hk,rfl|⟨hop,_⟩⟩:=bD.mp hr
   ·omega
   ·exact absurd (a7.mpr ⟨hk,hop⟩) hu
  exact λg hg g' hg'=>(this g hg).trans (this g' hg').symm)
 have h1:tops G C⊆({C.output}:Finset ℕ).biUnion (fX n C)∩tops G C:=λa ha=>by
  simp only[singleton_biUnion,mem_inter];exact⟨fQ.mpr ⟨(aI.mp ha).2.1,kT hC hT ha⟩,ha⟩
 have h2:P.card≤(orT G C).card:=by
  refine card_le_card_of_injOn (λw=>w-n) (λw hw=>?_) λw hw w' hw' he=>?_
  ·obtain⟨hJ,⟨w0,hw0,hr⟩,-⟩:=hP w hw;obtain rfl:=mem_singleton.mp hw0;obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by have:=hJ.1;omega⟩;obtain⟨hk,hop⟩:=a7.mp hJ;simp only[show n+k-n=k by omega,mem_coe]
   exact jB.mpr ⟨hk,hop,λx hx=>by
    rw[←hC.2.1];exact aO hA x ((cK hA).mpr ⟨hk,hr⟩) hx⟩
  ·have:=(hP w hw).1.1;have:=(hP w' hw').1.1;simp only at he;omega
 have:=card_le_card h1;simp only[card_singleton]at hcard;omega
lemma bL {w:ℕ} (hw:¬bX n C w):(orIn n C w).card≤1:=by
 rcases Nat.lt_or_ge w n with hn|hn
 ·rw[fA hn];simp
 ·obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by omega⟩;rw[b6 λhk hop=>hw (a7.mpr ⟨hk,hop⟩)];simp
lemma aV (h:IsAO2 n C) {a:ℕ} (ha:a∈tops G C) (b:Fin 2) {c u:Fin n} (hc:c∈side C a (1-b)) (hu:u∈side C a b):G.Adj c u/\s(c,u)∈starEdges G C:=by
 have key:∀x y:Fin n,x∈side C a 0 ->y∈side C a 1 ->s(x,y)∈starEdges G C:=λx y hx hy=>by
   simp only[starEdges,mem_biUnion,mem_image,mem_product];exact⟨a,ha,(x,y),⟨hx,hy⟩,rfl⟩
 fin_cases b
 ·exact⟨(cE h ha hu hc).symm,Sym2.eq_swap▸key u c hu hc⟩
 ·exact⟨cE h ha hc hu,key c u hc hu⟩
lemma pX (h:IsAO2 n C):starEdges G C⊆G.edgeFinset:=by
 intro e he;simp only[starEdges,mem_biUnion,mem_image,mem_product]at he;obtain⟨a,ha,⟨u,v⟩,⟨hu,hv⟩,rfl⟩:=he;exact SimpleGraph.mem_edgeFinset.mpr (cE h ha hu hv)
lemma fU (h:IsAO2 n C) (h4:NoFourCycle G) {a:ℕ} (ha:a∈tops G C\centreless G C):a∈tops G C/\(side (n:=n) C a 0).Nonempty/\(side (n:=n) C a 1).Nonempty/\∃b:Fin 2,∃c:Fin n,side C a (1-b)={c}:=by
 obtain⟨ha1,ha2⟩:=mem_sdiff.mp ha;simp only[centreless,mem_filter,ha1,true_and,not_or,←nonempty_iff_ne_empty]at ha2;refine⟨ha1,ha2.1,ha2.2,?_⟩;rcases qI h h4 ha1 with h1|h1
 ·obtain⟨c,hc⟩:=card_eq_one.mp (le_antisymm h1 ha2.1.card_pos);exact⟨1,c,hc⟩
 ·obtain⟨c,hc⟩:=card_eq_one.mp (le_antisymm h1 ha2.2.card_pos);exact⟨0,c,hc⟩
lemma jA {h:ℕ}:h∈lam G C↔h∈orN G C/\(orIn n C (opnd C h 0)).Nonempty/\(orIn n C (opnd C h 1)).Nonempty/\∃a∈tops G C,∃b:Fin 2,(side (n:=n) C a (1-b)).card=1/\OrReaches n C (opnd C a b) h:=by
 simp[lam]
lemma qO (hC:IsLeastAO G C) (h4:NoFourCycle G):(starEdges G C).card≤(tops G C\centreless G C).card+(lam G C).card:=by
 have hA:=hC.1;rcases Nat.eq_zero_or_pos n with rfl|hn
 ·simp[eq_empty_of_isEmpty (starEdges G C)]
 have:Nonempty (Fin n):=⟨⟨0,hn⟩⟩;have hsel:=λa ha=>(fU hA h4 (a:=a) ha).2.2.2
 choose! bs cen hcen using hsel
 have hD:dB (λp:ℕ×Fin n=>bX n C p.1) (λp=>(bF n C p.1,p.2)) (λp=>(bI n C p.1,p.2)) (λp=>p.1) (λp=>(orIn n C p.1).image λv=>s(p.2,v)):=λp hp=>⟨(aJ hA p.1 hp).1,(aJ hA p.1 hp).2.1,by
   simp only[(aJ hA p.1 hp).2.2,image_union]⟩
 obtain⟨P,hP,hcard⟩:=cU hD univ ((tops G C\centreless G C).image λa=>(opnd C a (bs a),cen a)) (λw _ u _ hu=>(card_le_card inter_subset_left).trans (card_image_le.trans (bL hu)));have hproj:∀q p:ℕ×Fin n,aM (λp:ℕ×Fin n=>bX n C p.1) (λp=>(bF n C p.1,p.2)) (λp=>(bI n C p.1,p.2)) q p ->p.2=q.2/\aM (bX n C) (bF n C) (bI n C) q.1 p.1:=by
  intro q p hqp;unfold aM at hqp⊢
  induction hqp using Relation.ReflTransGen.head_induction_on with
  |refl=>exact⟨rfl,Relation.ReflTransGen.refl⟩
  | @head a c hstep _ ih=>
   obtain⟨hJ,hc⟩:=hstep;have:c.2=a.2/\(c.1=bF n C a.1\/c.1=bI n C a.1):=by
    rcases hc with rfl|rfl<;>simp
   exact⟨ih.1.trans this.1,Relation.ReflTransGen.head ⟨hJ,this.2⟩ ih.2⟩
 have hfacts:∀p∈P,∃h,p.1=n+h/\h∈lam G C/\(∀u∈orIn n C (n+h),G.Adj p.2 u)/\∃v v',v≠v'/\v∈orIn n C (n+h)/\v'∈orIn n C (n+h):=by
  intro p hp;obtain⟨hJ,⟨q,hq,hr⟩,hl,hr'⟩:=hP p hp;obtain⟨a,ha,rfl⟩:=mem_image.mp hq;obtain⟨h,hh⟩:∃h,p.1=n+h:=⟨p.1-n,by have:=hJ.1;omega⟩;obtain⟨hpc,hrc⟩:=hproj _ _ hr;simp only at hpc hrc;rw[hh]at hJ hrc;obtain⟨hk,hop⟩:=a7.mp hJ;have hreach:=(cK hA).mpr ⟨hk,hrc⟩;have hat:=(fU hA h4 ha).1;obtain⟨e,he,hne⟩:=not_subset.mp hl;obtain⟨e',he',hne'⟩:=not_subset.mp hr';simp only[inter_univ,mem_image,hh,show n+h-n=h by omega,bF,bI]at he hne he' hne';obtain⟨v,hv,rfl⟩:=he;obtain⟨v',hv',rfl⟩:=he';have hvn:v∉orIn n C (opnd C h 1):=λhx=>hne ⟨v,hx,rfl⟩;have hsub:=dO hA hk hop;have hin:v∈orIn n C (n+h):=hsub▸mem_union_left _ hv;have hin':v'∈orIn n C (n+h):=hsub▸mem_union_right _ hv';refine⟨h,hh,jA.mpr ⟨dS.mpr ⟨hk,hop,λhb=>?_⟩,⟨v,hv⟩,⟨v',hv'⟩,a,hat,bs a,by rw[hcen a ha];rfl,hreach⟩,λu hu=>?_,v,v',λhvv=>hvn (hvv▸hv'),hin,hin'⟩
  ·have:=hb (unitInput v) (bY hA hin (by simp[unitInput]));rw[e8]at this;cases this
  ·rw[hpc];exact(aV hA hat (bs a) (by rw[hcen a ha];simp) (a6 hA hreach hu)).1
 have h1:starEdges G C⊆((tops G C\centreless G C).image λa=>(opnd C a (bs a),cen a)).biUnion (λp=>(orIn n C p.1).image λv=>s(p.2,v))∩univ:=by
  intro e he;simp only[starEdges,mem_biUnion,mem_image,mem_product]at he;obtain⟨a,ha,⟨u,v⟩,⟨hu,hv⟩,rfl⟩:=he
  have hnc:a∈tops G C\centreless G C:=mem_sdiff.mpr ⟨ha,λhc=>by
   simp only[centreless,mem_filter]at hc;rcases hc.2 with h|h
   ·exact absurd hu (h▸notMem_empty u)
   ·exact absurd hv (h▸notMem_empty v)⟩
  have hc:=hcen a hnc;simp only[inter_univ,mem_biUnion,mem_image];refine⟨_,⟨a,hnc,rfl⟩,?_⟩
  generalize bs a=b at hc⊢
  fin_cases b
  ·have hc':side C a 1={cen a}:=hc;exact⟨u,hu,mem_singleton.mp (hc'▸hv)▸Sym2.eq_swap⟩
  ·have hc':side C a 0={cen a}:=hc;exact⟨v,hv,mem_singleton.mp (hc'▸hu)▸rfl⟩
 have h2:P.card≤(lam G C).card:=by
  refine card_le_card_of_injOn (λp=>p.1-n) (λp hp=>?_) λp hp p' hp' he=>?_
  ·obtain⟨h,hh,hl,-⟩:=hfacts p hp;simp only[hh,show n+h-n=h by omega,mem_coe];exact hl
  ·obtain⟨h,hh,-,hadj,v,v',hvv,hv,hv'⟩:=hfacts p hp;obtain⟨h',hh',-,hadj',-⟩:=hfacts p' hp';simp only[hh,hh']at he;obtain rfl:h=h':=by omega
   refine Prod.ext (hh.trans hh'.symm) ?_;by_contra hne;exact hvv (aQ h4 hne (hadj v hv) (hadj' v hv) (hadj v' hv') (hadj' v' hv'))
 have:=(card_le_card h1).trans hcard;have:=card_image_le (s:=tops G C\centreless G C) (f:=λa=>(opnd C a (bs a),cen a));omega
theorem uS (h4:NoFourCycle G) (hC:IsLeastAO G C) (hT:TopForm G C):G.edgeFinset.card+(tops G C\centreless G C).card+2*(centreless G C).card+(junk G C).card+(orN G C\lam G C).card≤C.size+(Ustar G C).card+1:=by
 have h1:=p7 hC hT;have h2:=qO hC h4;have h3:=tJ (G:=G) hC.1;have h5:=card_sdiff_add_card_eq_card (show centreless G C⊆tops G C from filter_subset _ _);have h6:=card_sdiff_add_card_eq_card (show lam G C⊆orN G C from filter_subset _ _);have h7:=card_sdiff_add_card_eq_card (pX (G:=G) hC.1);rw[show G.edgeFinset\starEdges G C=Ustar G C from rfl]at h7;omega
def fM (n:ℕ) (f:(Fin n ->Bool) ->Bool) (s:ℕ):Prop:=∀gs:List Gate,IsAO2 n ⟨gs,0⟩ ->∃(gs':List Gate) (w:ℕ),IsAO2 n ⟨gs++gs',0⟩/\gs'.length≤s/\w<n+(gs++gs').length/\∀x,wireVal n ⟨gs++gs',0⟩ w x=f x
lemma kE {n:ℕ} (L L':List Gate) (o o':ℕ) (x:Fin n ->Bool) {w:ℕ} (hw:w<n+L.length):wireVal n ⟨L++L',o⟩ w x=wireVal n ⟨L,o'⟩ w x:=gM x (m:=L.length) (by simp) le_rfl (λk hk=>by simp[gateAt,List.getElem?_append_left hk]) w hw
lemma t5 {n:ℕ} {L:List Gate} (h:IsAO2 n ⟨L,0⟩) {op:GateOp} (hop:op=GateOp.and\/op=GateOp.or) {a b:ℕ} (ha:a<n+L.length) (hb:b<n+L.length):IsAO2 n ⟨L++[⟨op,[a,b]⟩],0⟩/\∀x,wireVal n ⟨L++[⟨op,[a,b]⟩],0⟩ (n+L.length) x=op.eval [wireVal n ⟨L,0⟩ a x,wireVal n ⟨L,0⟩ b x]:=by
 have hg:gateAt ⟨L++[⟨op,[a,b]⟩],0⟩ L.length=⟨op,[a,b]⟩:=by simp[gateAt]
 have hlt:∀k<L.length,gateAt ⟨L++[⟨op,[a,b]⟩],0⟩ k=gateAt ⟨L,0⟩ k:=λk hk=>by simp[gateAt,List.getElem?_append_left hk]
 refine⟨?_,λx=>?_⟩
 ·rw[bZ]at h⊢;refine⟨λk hk=>?_,λk hk=>?_⟩<;>simp only[List.length_append,List.length_singleton]at hk<;>rcases Nat.lt_or_ge k L.length with h1|h1
  ·rw[hlt k h1];exact h.1 k h1
  ·obtain rfl:k=L.length:=by omega
   rw[hg];exact⟨hop,rfl⟩
  ·rw[hlt k h1];exact h.2 k h1
  ·obtain rfl:k=L.length:=by omega
   rw[hg];simp[ha,hb]
 ·rw[(a5 _ x).2.2 L.length (by simp),hg];simp[ha,hb,kE L _ 0 0 x ha,kE L _ 0 0 x hb]
lemma lP {n:ℕ} (v:Fin n):fM n (λx=>x v) 0:=λgs h=>⟨[],v,by simpa using h,le_rfl,by simp;omega,λx=>bA _ x v⟩
lemma pB {n:ℕ} {f f':(Fin n ->Bool) ->Bool} {s t:ℕ} (h:fM n f s) (hst:s≤t) (hf:∀x,f x=f' x):fM n f' t:=λgs hg=>by
 obtain⟨gs',w,h1,h2,h3,h4⟩:=h gs hg;exact⟨gs',w,h1,h2.trans hst,h3,λx=>(h4 x).trans (hf x)⟩
lemma mX {n:ℕ} {f g:(Fin n ->Bool) ->Bool} {s t:ℕ} (hf:fM n f s) (hg:fM n g t) {op:GateOp} (hop:op=GateOp.and\/op=GateOp.or):fM n (λx=>op.eval [f x,g x]) (s+t+1):=λgs h=>by
 obtain⟨g1,w1,hA1,hl1,hw1,hv1⟩:=hf gs h;obtain⟨g2,w2,hA2,hl2,hw2,hv2⟩:=hg (gs++g1) hA1;have hw1':w1<n+(gs++g1++g2).length:=by simp at hw1⊢;omega
 obtain⟨hA3,hv3⟩:=t5 hA2 hop hw1' hw2;refine⟨g1++g2++[⟨op,[w1,w2]⟩],n+(gs++g1++g2).length,by simpa[List.append_assoc]using hA3,by simp;omega,by simp,λx=>?_⟩;have:=hv3 x;rw[kE (gs++g1) g2 0 0 x hw1,hv1,hv2]at this;simpa[List.append_assoc]using this
lemma jM {n:ℕ} {ι:Type} (I:Finset ι) (g:ι ->(Fin n ->Bool) ->Bool) (c:ι ->ℕ) (hg:∀i∈I,fM n (g i) (c i)) (hI:I.Nonempty):∃s f,fM n f s/\(∀x,f x=true↔∃i∈I,g i x=true)/\s+1≤∑i∈I,(c i+1):=by
 induction hI using Finset.Nonempty.cons_induction with
 |singleton a=>exact⟨c a,g a,hg a (by simp),λx=>by simp,by simp⟩
 |cons a s ha hs ih=>
  obtain⟨t,f,ht,hspec,hle⟩:=ih λi hi=>hg i (mem_cons.mpr (Or.inr hi));refine⟨c a+t+1,_,mX (hg a (mem_cons_self a s)) ht (Or.inr rfl),λx=>?_,by rw[sum_cons];omega⟩;simp[GateOp.eval,hspec]
lemma pT {n:ℕ} {f:(Fin n ->Bool) ->Bool} {s:ℕ} (h:fM n f s):∃C:Circuit,IsAO2 n C/\circuitFun n C=f/\C.size≤s:=by
 obtain⟨gs',w,h1,h2,-,h4⟩:=h [] (by simp[IsAO2,AndOrOnly,ReadsBack]);exact⟨⟨gs',w⟩,h1,funext h4,h2⟩
theorem lC (hC:IsLeastAO G C) (hne:G.edgeFinset.Nonempty) (Z:Finset (Fin n)) (hZ:∀u v,G.Adj u v ->u∈Z\/v∈Z):C.size+1≤G.edgeFinset.card+Z.card:=by
 classical
 let L:Fin n ->Finset (Fin n):=λv=>
  univ.filter λl=>G.Adj v l/\¬(l∈Z/\l<v)
 have hL:∀v l,l∈L v↔G.Adj v l/\¬(l∈Z/\l<v):=λv l=>by simp[L]
 have hrep:∀u w,G.Adj u w ->∃v∈Z,∃l∈L v,s(v,l)=s(u,w):=by
  intro u w huw;by_cases h1:u∈Z/\¬(w∈Z/\w<u)
  ·exact⟨u,h1.1,w,(hL _ _).mpr ⟨huw,h1.2⟩,rfl⟩
  ·have hw:w∈Z:=by rcases hZ u w huw with h|h<;>tauto
   exact⟨w,hw,u,(hL _ _).mpr ⟨huw.symm,λh2=>h1 ⟨h2.1,λh3=>absurd h2.2 (not_lt_of_gt h3.2)⟩⟩,Sym2.eq_swap⟩
 have hZ'ne:(Z.filter λv=>(L v).Nonempty).Nonempty:=by
  obtain⟨e,he⟩:=hne
  induction e using Sym2.ind with
  |_ u w=>
   obtain⟨v,hv,l,hl,-⟩:=hrep u w (SimpleGraph.mem_edgeFinset.mp he);exact⟨v,mem_filter.mpr ⟨hv,l,hl⟩⟩
 have hcv:∀v∈Z.filter λv=>(L v).Nonempty,∃f,fM n f (L v).card/\∀x,f x=true↔x v=true/\∃l∈L v,x l=true:=by
  intro v hv;obtain⟨s,f,hf,hspec,hs⟩:=jM (L v) (λl x=>x l) (λ_=>0) (λl _=>lP l) (mem_filter.mp hv).2;simp only[zero_add,sum_const,smul_eq_mul,mul_one]at hs;exact⟨λx=>x v&&f x,pB (mX (lP v) hf (Or.inl rfl)) (by omega) (λx=>by simp[GateOp.eval]),λx=>by simp[hspec]⟩
 choose! fv hfv hfs using hcv
 obtain⟨s,f,hf,hspec,hs⟩:=jM _ fv (λv=>(L v).card) hfv hZ'ne;obtain⟨C',hA',hfun,hsz⟩:=pT hf;have hF:circuitFun n C'=graphFun G ∅:=by
  rw[hfun];funext x;rw[Bool.eq_iff_iff,hspec,dJ];constructor
  ·rintro⟨v,hv,h1⟩;obtain⟨hxv,l,hl,hxl⟩:=(hfs v hv x).mp h1;exact⟨v,l,((hL _ _).mp hl).1,hxv,hxl⟩
  ·rintro⟨u,w,huw,hu,hw⟩;obtain⟨v,hv,l,hl,he⟩:=hrep u w huw;have hv':v∈Z.filter λv=>(L v).Nonempty:=mem_filter.mpr ⟨hv,l,hl⟩;refine⟨v,hv',(hfs v hv' x).mpr ?_⟩;rcases Sym2.eq_iff.mp he with⟨rfl,rfl⟩|⟨rfl,rfl⟩
   ·exact⟨hu,_,hl,hw⟩
   ·exact⟨hw,_,hl,hu⟩
 have hmin:=hC.2.2 C' hA' hF;have hsum:∑v∈Z.filter λv=>(L v).Nonempty,(L v).card≤G.edgeFinset.card:=by
  rw[←card_sigma];refine card_le_card_of_injOn (λp=>s(p.1,p.2)) (λp hp=>?_) λp hp q hq he=>?_
  ·exact mem_coe.mpr (SimpleGraph.mem_edgeFinset.mpr ((hL _ _).mp (mem_sigma.mp (mem_coe.mp hp)).2).1)
  ·obtain⟨hp1,hp2⟩:=mem_sigma.mp (mem_coe.mp hp);obtain⟨hq1,hq2⟩:=mem_sigma.mp (mem_coe.mp hq);obtain⟨v,l⟩:=p;obtain⟨v',l'⟩:=q;rcases Sym2.eq_iff.mp he with⟨h1,h2⟩|⟨h1,h2⟩
   ·simp only at h1 h2;subst h1 h2;rfl
   ·simp only at h1 h2 hp1 hp2 hq1 hq2;subst h1 h2;have h3:=((hL _ _).mp hp2).2;have h4:=((hL _ _).mp hq2).2;have h5:=(mem_filter.mp hp1).1;have h6:=(mem_filter.mp hq1).1;rcases lt_trichotomy v l with h|h|h
    ·exact absurd ⟨h5,h⟩ h4
    ·exact absurd ((hL _ _).mp hp2).1 (h▸G.irrefl)
    ·exact absurd ⟨h6,h⟩ h3
 have h1:∑v∈Z.filter λv=>(L v).Nonempty,((L v).card+1)=∑v∈Z.filter λv=>(L v).Nonempty,(L v).card+(Z.filter λv=>(L v).Nonempty).card:=by
  rw[sum_add_distrib];simp
 have h2:=card_le_card (filter_subset (λv=>(L v).Nonempty) Z);simp only[Circuit.size]at*;omega
theorem mI (hC:IsLeastAO G C) (hne:G.edgeFinset.Nonempty) (K X:Finset (Fin n)) (hK:∀e∈starEdges G C,∃v∈K,v∈e) (hX:∀e∈Ustar G C,∃v∈X,v∈e):C.size+1≤G.edgeFinset.card+K.card+(X\K).card:=by
 have:=lC hC hne (K∪X) λu v huv=>by
  by_cases hs:s(u,v)∈starEdges G C
  ·obtain⟨w,hw,hwe⟩:=hK _ hs;rcases Sym2.mem_iff.mp hwe with rfl|rfl<;>simp[hw]
  ·obtain⟨w,hw,hwe⟩:=hX _ (show s(u,v)∈G.edgeFinset\starEdges G C from mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr huv,hs⟩);rcases Sym2.mem_iff.mp hwe with rfl|rfl<;>simp[hw]
 rw[←union_sdiff_self_eq_union,card_union_of_disjoint disjoint_sdiff]at this;omega
theorem e4 (h4:NoFourCycle G) (hC:IsLeastAO G C) (hT:TopForm G C) (hj:(junk G C).card=2) (K X:Finset (Fin n)) (hK:∀e∈starEdges G C,∃v∈K,v∈e) (hX:∀e∈Ustar G C,∃v∈X,v∈e):2+2*(centreless G C).card+(orN G C\lam G C).card+(tops G C\centreless G C).card≤(Ustar G C).card+K.card+(X\K).card:=by
 have hA:=uS h4 hC hT;by_cases hne:G.edgeFinset.Nonempty
 ·have:=mI hC hne K X hK hX;omega
 ·have h0:C.size≤0:=hC.2.2 ⟨[],n⟩ (by simp[IsAO2,AndOrOnly,ReadsBack]) (by
   funext x
   rw[show circuitFun n ⟨[],n⟩ x=wireVal n ⟨[],n⟩ n x from rfl,(a5 _ x).2.1 n (by simp),eq_comm,←Bool.not_eq_true,dJ];rintro⟨u,v,huv,-⟩
   exact hne ⟨s(u,v),SimpleGraph.mem_edgeFinset.mpr huv⟩)
  have:=card_le_card (show junk G C⊆range C.gates.length from filter_subset _ _);simp only[Circuit.size,card_range]at h0 this;omega
lemma bW {a:ℕ} (ha:a∈tops G C) {u v:Fin n} (hu:u∈side C a 0) (hv:v∈side C a 1):a∈tops G C\centreless G C:=mem_sdiff.mpr ⟨ha,λhc=>by
 simp only[centreless,mem_filter]at hc;rcases hc.2 with h|h
 ·exact absurd hu (h▸notMem_empty u)
 ·exact absurd hv (h▸notMem_empty v)⟩
theorem k3 (hA:IsAO2 n C) (h4:NoFourCycle G) (pref:Fin n ->Prop):∃K:Finset (Fin n),K.card≤(tops G C\centreless G C).card/\(∀e∈starEdges G C,∃v∈K,v∈e)/\∀a∈tops G C\centreless G C,∃b:Fin 2,∃p∈K,side C a (1-b)={p}/\((∃b':Fin 2,∃p',side C a (1-b')={p'}/\pref p') ->pref p):=by
 classical
 have hsel:∀a:{a//a∈tops G C\centreless G C},∃b:Fin 2,∃p:Fin n,side C a.1 (1-b)={p}/\((∃b':Fin 2,∃p',side C a.1 (1-b')={p'}/\pref p') ->pref p):=by
  intro a;by_cases hp:∃b':Fin 2,∃p',side C a.1 (1-b')={p'}/\pref p'
  ·obtain⟨b',p',h1,h2⟩:=hp;exact⟨b',p',h1,λ_=>h2⟩
  ·obtain⟨b,c,hc⟩:=(fU hA h4 a.2).2.2.2;exact⟨b,c,hc,λh=>absurd h hp⟩
 choose bs cen hcen using hsel;refine⟨univ.image cen,card_image_le.trans (by simp),λe he=>?_,λa ha=>⟨bs ⟨a,ha⟩,cen ⟨a,ha⟩,mem_image_of_mem _ (mem_univ _),hcen ⟨a,ha⟩⟩⟩;simp only[starEdges,mem_biUnion,mem_image,mem_product]at he;obtain⟨a,ha,⟨u,v⟩,⟨hu,hv⟩,rfl⟩:=he;have hc:=(hcen ⟨a,bW ha hu hv⟩).1;refine⟨_,mem_image_of_mem _ (mem_univ ⟨a,bW ha hu hv⟩),?_⟩
 generalize bs ⟨a,bW ha hu hv⟩=b at hc
 fin_cases b
 ·have hc':side C a 1={cen ⟨a,bW ha hu hv⟩}:=hc;simp[←mem_singleton.mp (hc'▸hv)]
 ·have hc':side C a 0={cen ⟨a,bW ha hu hv⟩}:=hc;simp[←mem_singleton.mp (hc'▸hu)]
def fJ {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (col:Fin n ->Bool) (U:Finset (Sym2 (Fin n))) (S:Fin 4 ->Finset (Fin n)):Prop:=(∀u v,G.Adj u v ->col u≠col v)/\NoFourCycle G/\U⊆G.edgeFinset/\(∀x:Fin n ->Bool,(∀k,∃v∈S k,x v=true) ->graphFun G ∅ x=true)/\∀e∈U,∀k,∃v∈S k,v∈e
lemma sC:∀i j d v:Fin 4,i≠j ->d≠i ->d≠j ->v≠i ->v≠j ->d≠v ->∀m,m=i\/m=j\/m=d\/m=v:=by decide
lemma jE {S:Fin 4 ->Finset (Fin n)} (hH:∀x:Fin n ->Bool,(∀k,∃v∈S k,x v=true) ->graphFun G ∅ x=true) (I:Fin n ->Bool) (hI:∀u v,G.Adj u v ->I u=true ->I v=true ->False):∃k,∀v∈S k,I v=false:=by
 by_contra hc;push Not at hc;obtain⟨u,v,huv,hu,hv⟩:∃u v,G.Adj u v/\I u=true/\I v=true:=by
  simpa[graphFun]using hH I (by simpa using hc)
 exact hI u v huv hu hv
theorem mT (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (S:Fin 4 ->Finset (Fin n)) (hH:∀x:Fin n ->Bool,(∀k,∃v∈S k,x v=true) ->graphFun G ∅ x=true) (U:Finset (Sym2 (Fin n))) (hacc:∀e∈U,∀k,∃v∈S k,v∈e) (hne:U.Nonempty):∃i j:Fin 4,i≠j/\(∀v∈S i,col v=false)/\(∀v∈S j,col v=true):=by
 obtain⟨j,hj⟩:=jE hH (λv=> !col v) (by grind);obtain⟨i,hi⟩:=jE hH col (by grind);refine⟨i,j,?_,hi,by simpa using hj⟩;rintro rfl;obtain⟨e,he⟩:=hne;obtain⟨v,hv,-⟩:=hacc e he i
 grind
section
open Finset
variable {n:ℕ} {G:SimpleGraph (Fin n)} {col:Fin n ->Bool} {U:Finset (Sym2 (Fin n))} {ν:Type} [DecidableEq ν] {J:ν ->Prop} {l r:ν ->ν} {rk:ν ->ℕ} {f:ν ->Finset (Fin n)} {rt:Fin 4 ->ν}
lemma aD {p b:Fin n}:b∈aE U p↔s(p,b)∈U:=by simp[aE]
lemma lQ {p q:Fin n} (hc:∀e∈U,p∈e\/q∈e) (hno:∃e∈U,q∉e):∃b∈aE U p,b≠q:=by
 obtain⟨e,he,hqe⟩:=hno;obtain⟨b,rfl⟩:=Sym2.mem_iff_exists.mp ((hc e he).resolve_right hqe);exact⟨b,aD.mpr he,λhbq=>hqe (by simp[hbq])⟩
lemma l9 (U:Finset (Sym2 (Fin n))) {p q:Fin n} (hpq:p≠q) (hc:∀e∈U,p∈e\/q∈e):U.card=(aE U p).card+((aE U q).erase p).card:=by
 have hU:U=(aE U p).image (λb=>s(p,b))∪((aE U q).erase p).image (λb=>s(q,b)):=by
  ext e
  induction e with|h x y=>?_
  have:=hc s(x,y);simp only[mem_union,mem_image,mem_erase,aD,Sym2.eq_iff,Sym2.mem_iff]at this⊢
  grind [Sym2.eq_swap]
 conv_lhs=>rw[hU]
 rw[card_union_of_disjoint,card_image_of_injective _ λa b hab=>Sym2.congr_right.mp hab,card_image_of_injective _ λa b hab=>Sym2.congr_right.mp hab];simp only[disjoint_left,mem_image,mem_erase]
 grind
lemma pG {W:Finset (Fin n)} {x y:Fin n} (h:¬(x∈W/\y∈W)):(W∩{x,y}).card≤1:=by
 refine card_le_one.mpr λu hu v hv=>?_;simp only[mem_inter,mem_insert,mem_singleton]at hu hv
 grind
lemma j9 (hD:dB J l r rk f) (hleaf:∀k u,aM J l r (rt k) u ->¬J u ->aB G U (f u)\/(f u).card≤1) (k₁ k₂:Fin 4) {S₁ S₂:Finset (Fin n)} (h1:S₁⊆f (rt k₁)) (h2:S₂⊆f (rt k₂)) (p1:∀W,aB G U W ->(W∩S₁).card≤1) (p2:∀W,aB G U W ->(W∩S₂).card≤1) (hsep:(f (rt k₂)∩S₁).card≤1) (m:ℕ) (hm:m+2≤S₁.card+S₂.card):∃P:Finset ν,(∀h∈P,J h/\¬aB G U (f h)/\(aM J l r (rt k₁) h\/aM J l r (rt k₂) h))/\m≤P.card:=by
 obtain⟨P₁,hP₁,c1⟩:=d8 hD _ _ _ h1 p1 (hleaf k₁);obtain⟨P₂,hP₂,c2⟩:=d8 hD _ _ _ h2 p2 (hleaf k₂);have hd:Disjoint P₁ P₂:=disjoint_left.mpr λh a b=>by
  have:=card_le_card (inter_subset_inter_right (u:=S₁) (aK hD (hP₂ h b).2.1));have:=(hP₁ h a).2.2.2;omega
 refine⟨P₁∪P₂,λh hh=>?_,by rw[card_union_of_disjoint hd];omega⟩;have:=hP₁ h;have:=hP₂ h
 grind
variable [DecidableRel G.Adj] {S:Fin 4 ->Finset (Fin n)}
lemma lD (h:fJ G col U S) {a b:Fin n} (hn:¬G.Adj a b):∃k,a∉S k/\b∉S k:=by
 obtain⟨k,hk⟩:=jE h.2.2.2.1 (λv=>decide (v=a\/v=b)) (by grind [SimpleGraph.irrefl,SimpleGraph.adj_comm]);exact⟨k,by grind,by grind⟩
lemma j8 (h:fJ G col U S) {a b:Fin n} (hab:∀k,a∈S k\/b∈S k):G.Adj a b:=not_not.mp λhn=>(lD h hn).elim λk hk=>(hab k).elim hk.1 hk.2
lemma cO (h:fJ G col U S) {p b:Fin n} (hb:b∈aE U p):G.Adj p b:=by
 simpa using h.2.2.1 (aD.mp hb)
lemma cR (h:fJ G col U S) {p b:Fin n} (hb:b∈aE U p) (k:Fin 4):p∈S k\/b∈S k:=by
 obtain⟨v,hv,hve⟩:=h.2.2.2.2 _ (aD.mp hb) k;rcases Sym2.mem_iff.mp hve with rfl|rfl<;>simp[hv]
lemma gL (h:fJ G col U S) {i j:Fin 4} {c:Bool} (hA:∀v∈S i,col v=c) (hB:∀v∈S j,col v= !c) {p b:Fin n} (hb:b∈aE U p) (cp:col p=c):p∈S i/\b∈S j/\col b= !c:=by
 have:=h.1 p b (cO h hb);have:=cR h hb i;have:=cR h hb j
 grind
lemma mU (h:fJ G col U S) {W T₁ T₂:Finset (Fin n)} (hW:aB G U W) (c:Bool) (h1:∀v∈T₁,col v=c) (h2:∀v∈T₂,col v= !c) (s1:(W∩T₁).card≤1) (s2:(W∩T₂).card≤1):(W∩(T₁∪T₂)).card≤1:=by
 obtain⟨c',hc'⟩:=aU col h.1 hW;rw[card_le_one]at s1 s2⊢;simp only[mem_inter,mem_union]at s1 s2⊢
 grind
end
open Finset in
theorem mP (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (h4:NoFourCycle G) {ν:Type} [DecidableEq ν] {J:ν ->Prop} {l r:ν ->ν} {rk:ν ->ℕ} {f:ν ->Finset (Fin n)} (hD:dB J l r rk f) (rt:Fin 4 ->ν) (hH:∀x:Fin n ->Bool,(∀k,∃v∈f (rt k),x v=true) ->graphFun G ∅ x=true) (U:Finset (Sym2 (Fin n))) (hU:U⊆G.edgeFinset) (hacc:∀e∈U,∀k,∃v∈f (rt k),v∈e) (hleaf:∀k u,aM J l r (rt k) u ->¬J u ->aB G U (f u)\/(f u).card≤1) (p:Fin n) (hp:∀e∈U,p∈e) (hne:U.Nonempty):∃k:Fin 4,∃P:Finset ν,(∀h∈P,J h/\aM J l r (rt k) h/\¬aB G U (f h))/\U.card≤P.card+1:=by
 have h:fJ G col U λk=>f (rt k):=⟨hcol,h4,hU,hH,hacc⟩;obtain⟨i,j,-,hA,hB⟩:=mT col hcol _ hH U hacc hne;obtain⟨k,hk⟩:∃k,aE U p⊆f (rt k):=by
  cases hp':col p;exacts[⟨j,λb hb=>(gL h hA hB hb hp').2.1⟩,⟨i,λb hb=>(gL h hB hA hb hp').2.1⟩]
 obtain⟨P,hP,hc⟩:=d8 hD _ _ _ hk (λW hW=>aF h4 hU hW p) (hleaf k);refine⟨k,P,λx hx=>by have:=hP x hx;tauto,?_⟩;have hs:U⊆(aE U p).image λb=>s(p,b):=λe he=>by
  obtain⟨b,rfl⟩:=Sym2.mem_iff_exists.mp (hp e he);exact mem_image.mpr ⟨b,aD.mpr he,rfl⟩
 have:=(card_le_card hs).trans card_image_le;omega
open Finset in
theorem kM (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (h4:NoFourCycle G) {ν:Type} [DecidableEq ν] {J:ν ->Prop} {l r:ν ->ν} {rk:ν ->ℕ} {f:ν ->Finset (Fin n)} (hD:dB J l r rk f) (rt:Fin 4 ->ν) (hH:∀x:Fin n ->Bool,(∀k,∃v∈f (rt k),x v=true) ->graphFun G ∅ x=true) (U:Finset (Sym2 (Fin n))) (hU:U⊆G.edgeFinset) (hacc:∀e∈U,∀k,∃v∈f (rt k),v∈e) (hleaf:∀k u,aM J l r (rt k) u ->¬J u ->aB G U (f u)\/(f u).card≤1) (hno:∀p:Fin n,∃e∈U,p∉e):(∃k₁ k₂:Fin 4,∃P:Finset ν,(∀h∈P,J h/\¬aB G U (f h)/\(aM J l r (rt k₁) h\/aM J l r (rt k₂) h))/\U.card≤P.card)\/(∃i j k:Fin 4,∃p q:Fin n,i≠j/\k≠i/\k≠j/\(∀v∈f (rt i),col v=false)/\(∀v∈f (rt j),col v=true)/\p∈f (rt i)/\q∈f (rt j)/\s(p,q)∈U/\((aE U p).erase q).Nonempty/\((aE U q).erase p).Nonempty/\U.card=((aE U p).erase q).card+((aE U q).erase p).card+1/\(∃P:Finset ν,(∀h∈P,J h/\¬aB G U (f h)/\(aM J l r (rt i) h\/aM J l r (rt j) h))/\U.card≤P.card+1)/\∃h₀,J h₀/\¬aB G U (f h₀)/\aM J l r (rt k) h₀/\¬aM J l r (rt i) h₀/\¬aM J l r (rt j) h₀/\p∈f h₀/\q∈f h₀):=by
 have h:fJ G col U λk=>f (rt k):=⟨hcol,h4,hU,hH,hacc⟩;rcases U.eq_empty_or_nonempty with rfl|hne
 ·exact Or.inl ⟨0,0,∅,by simp⟩
 obtain⟨i,j,hij,hA,hB⟩:=mT col hcol _ hH U hacc hne;by_cases hop:∃p q,col p=false/\col q=true/\∀e∈U,p∈e\/q∈e
 swap
 ·have hop':∀x y:Fin n,(∀e∈U,x∈e\/y∈e) ->col x=col y:=by grind
  obtain⟨Q,hQ2,hQ⟩:=gY col hcol h4 _ hH U hU hacc;obtain⟨p,hp,-⟩:=hQ _ hne.choose_spec;obtain⟨e,he,hpe⟩:=hno p;obtain⟨q,hq,hqe⟩:=hQ e he;have hpq:p≠q:=λx=>hpe (x▸hqe);have hc:∀e∈U,p∈e\/q∈e:=λe' he'=>by
   by_contra hcon;push Not at hcon;obtain⟨w,hw,hwe⟩:=hQ e' he';have:=two_lt_card.mpr ⟨p,hp,q,hq,w,hw,hpq,by grind,by grind⟩;omega
  have deg:∀x y:Fin n,(∀e∈U,x∈e\/y∈e) ->1<(aE U x).card:=λx y hc'=>by
    by_contra hx1;obtain⟨b,hb,-⟩:=lQ hc' (hno y);refine hcol x b (cO h hb) ((hop' x y hc').trans (hop' b y λe he=>?_).symm);rcases hc' e he with hx|hy
    ·obtain⟨b',rfl⟩:=Sym2.mem_iff_exists.mp hx;rw[card_le_one.mp (by omega) b' (aD.mpr he) b hb];exact Or.inl (Sym2.mem_mk_right x b)
    ·exact Or.inr hy
  have h1:=deg p q hc;have h2:=deg q p λe he=>(hc e he).symm;obtain⟨i,j,hij,hA,hB⟩:∃i j:Fin 4,i≠j/\(∀v∈f (rt i),col v=col p)/\∀v∈f (rt j),col v= !col p:=by
   cases col p;exacts[⟨i,j,hij,hA,hB⟩,⟨j,i,hij.symm,hB,hA⟩]
  have cq:=(hop' p q hc).symm;have L:=λ{x b:Fin n} (cx:col x=col p) (hb:b∈aE U x)=>gL h hA hB hb cx;have K:∀x y:Fin n,x≠y ->1<(aE U x).card ->∃m,x∈f (rt m)/\y∉f (rt m):=λx y hxy hx=>by
   by_contra hK;push Not at hK;obtain⟨b1,hb1,b2,hb2,hne⟩:=one_lt_card.mp hx;have ad:∀b∈aE U x,G.Adj y b:=λb hb=>j8 h λm=>(cR h hb m).imp_left (hK m);exact hne (aQ h4 hxy (cO h hb1) (ad b1 hb1) (cO h hb2) (ad b2 hb2))
  obtain⟨d,hpd,hqd⟩:=K p q hpq h1;obtain⟨v,hqv,hpv⟩:=K q p hpq.symm h2;obtain⟨b,hb,-⟩:=one_lt_card.mp h1;obtain⟨a,ha,-⟩:=one_lt_card.mp h2;have hpA:=(L rfl hb).1;have hqA:=(L cq ha).1;have hall:=sC i j d v hij (by grind) (by grind) (by grind) (by grind) (by grind);have sp:∀x y:Fin n,col x=col p ->col y=col p ->∀W,aB G U W ->(W∩insert x (aE U y)).card≤1:=λx y cx cy W hW=>by
   rw[insert_eq];exact mU h hW _ (λz hz=>mem_singleton.mp hz▸cx) (λz hz=>(L cy hz).2.2) (card_le_card inter_subset_right) (aF h4 hU hW y)
  have key:∀z∈f (rt v)∩insert p (aE U q),G.Adj p z/\G.Adj q z:=λz hz=>by
   rw[mem_inter,mem_insert]at hz;have hzq:=hz.2.resolve_left λe=>hpv (e▸hz.1);have:=(L cq hzq).2.1;exact⟨j8 h λm=>by have:=hall m;grind,cO h hzq⟩
  have np:p∉aE U q:=λhp'=>hcol q p (cO h hp') cq;have nq:q∉aE U p:=λhq'=>hcol p q (cO h hq') cq.symm;have hcard:=l9 U hpq hc;rw[erase_eq_of_notMem np]at hcard;exact Or.inl ⟨d,v,j9 hD hleaf d v (insert_subset hpd λx hx=>(cR h hx d).resolve_left hqd) (insert_subset hqv λx hx=>(cR h hx v).resolve_left hpv) (sp p q rfl cq) (sp q p cq rfl) (card_le_one.mpr λz1 h1 z2 h2=>aQ h4 hpq (key z1 h1).1 (key z1 h1).2 (key z2 h2).1 (key z2 h2).2) U.card (by rw[card_insert_of_notMem np,card_insert_of_notMem nq];omega)⟩
 obtain⟨p,q,cp,cq,hc⟩:=hop;have hpq:p≠q:=by grind
 have hd:∀x,x∈f (rt i) ->x∈f (rt j) ->False:=by grind
 have L:=λ{b:Fin n} (hb:b∈aE U p)=>gL h hA hB hb cp;have R:=λ{a:Fin n} (ha:a∈aE U q)=>gL h hB hA ha cq;obtain⟨b,hb,hbq⟩:=lQ hc (hno q);obtain⟨a,ha,hap⟩:=lQ (λe he=>(hc e he).symm) (hno p);have hpA:=(L hb).1;have hqB:=(R ha).1;have hcard:=l9 U hpq hc;have hfc:∀W,aB G U W ->¬(p∈W/\q∈W):=λW hW hh=>by
  obtain⟨c,hc'⟩:=aU col hcol hW
  grind
 by_cases hadj:G.Adj p q
 ·have s1:insert p (aE U q)⊆f (rt i):=insert_subset hpA λx hx=>(R hx).2.1;have T:=j9 hD hleaf i j s1 (insert_subset hqB λx hx=>(L hx).2.1) (λW hW=>a4 h4 hU hW q p hadj.symm) (λW hW=>a4 h4 hU hW p q hadj) (card_le_one.mpr λx hx=>(hd x (s1 (mem_inter.mp hx).2) (mem_inter.mp hx).1).elim);by_cases hU':s(p,q)∈U
  ·have hq':q∈aE U p:=aD.mpr hU';have hp':p∈aE U q:=aD.mpr (Sym2.eq_swap▸hU');have c3:=card_erase_add_one hq';have c4:=card_erase_add_one hp';obtain⟨P,hP,hm⟩:=T (U.card-1) (by rw[insert_eq_of_mem hp',insert_eq_of_mem hq'];omega);have nab:¬G.Adj a b:=λhab=>hbq (aQ h4 (hap.symm) (cO h hb) hab hadj (cO h ha).symm);obtain⟨k,hka,hkb⟩:=lD h nab;obtain⟨h₀,hJ,hR,hF,hp0,hq0⟩:=eU hD _ _ p q hpq ((cR h hb k).resolve_right hkb) ((cR h ha k).resolve_right hka) hfc (hleaf k);refine Or.inr ⟨i,j,k,p,q,hij,λe=>hka (e▸(R ha).2.1),λe=>hkb (e▸(L hb).2.1),hA,hB,hpA,hqB,hU',⟨b,mem_erase.mpr ⟨hbq,hb⟩⟩,⟨a,mem_erase.mpr ⟨hap,ha⟩⟩,by omega,⟨P,hP,by omega⟩,h₀,hJ,hF,hR,λhr=>hd q (aK hD hr hq0) hqB,λhr=>hd p hpA (aK hD hr hp0),hp0,hq0⟩
  ·have hq':q∉aE U p:=λx=>hU' (aD.mp x);have hp':p∉aE U q:=λx=>hU' (Sym2.eq_swap▸aD.mp x);rw[erase_eq_of_notMem hp']at hcard;exact Or.inl ⟨i,j,T U.card (by rw[card_insert_of_notMem hp',card_insert_of_notMem hq'];omega)⟩
 ·obtain⟨E,hpE,hqE⟩:=lD h hadj;rw[erase_eq_of_notMem λhp'=>hadj (cO h hp').symm]at hcard;obtain⟨k₁,y,hxy,hx,hy,hfr⟩:∃(k₁:Fin 4) (y:Fin n),p≠y/\p∈f (rt k₁)/\y∈f (rt k₁)/\∀W,aB G U W ->¬(p∈W/\y∈W):=by
   by_cases hT:∃m,p∈f (rt m)/\q∈f (rt m)
   ·obtain⟨m,hpm,hqm⟩:=hT;exact⟨m,q,hpq,hpm,hqm,hfc⟩
   ·push Not at hT;have hab:G.Adj a b:=j8 h λm=>by
     have:=cR h hb m;have:=cR h ha m
     grind
    refine⟨i,a,hap.symm,hpA,(R ha).2.1,λW ⟨z,hz⟩ hh=>?_⟩;obtain rfl:=aQ h4 (hap.symm) (hz p hh.1).1.symm (hz a hh.2).1.symm (cO h hb) hab;exact(hz p hh.1).2 (Sym2.eq_swap▸aD.mp hb)
  exact Or.inl ⟨k₁,E,j9 hD hleaf k₁ E (insert_subset hx (singleton_subset_iff.mpr hy)) (union_subset (λx hx=>(cR h hx E).resolve_left hpE) λx hx=>(cR h hx E).resolve_left hqE) (λW hW=>pG (hfr W hW)) (λW hW=>mU h hW true (λv hv=>(L hv).2.2) (λv hv=>(R hv).2.2) (aF h4 hU hW p) (aF h4 hU hW q)) (pG λhh=>hpE hh.1) U.card (by
    rw[card_pair hxy,card_union_of_disjoint (disjoint_left.mpr λv h1 h2=>hd v (R h2).2.1 (L h1).2.1)]
    omega)⟩
lemma uO (h:IsAO2 n C) (hle:∀x,circuitFun n C x=true ->graphFun G ∅ x=true) (hacc:∀u v,G.Adj u v ->circuitFun n C (pairInput u v)=true):circuitFun n C=graphFun G ∅:=by
 funext x
 rw[Bool.eq_iff_iff];refine⟨hle x,λhx=>?_⟩;obtain⟨u,v,huv,hu,hv⟩:=(dJ x).mp hx
 exact nH (bZ.mp h).1 (x:=pairInput u v) (λw hw=>by
  simp only[pairInput,decide_eq_true_eq]at hw;rcases hw with rfl|rfl<;>assumption)
  C.output (hacc u v huv)
def aL (C:Circuit) (j:ℕ) (g:Gate):Circuit:=dY C.gates.length (Function.update (gateAt C) j g) C.output
lemma b7 (h:IsAO2 n C) {j:ℕ} (hj:j<C.gates.length) {op:GateOp} (hop:op=GateOp.and\/op=GateOp.or) {a b:ℕ} (ha:a<n+j) (hb:b<n+j) (x:Fin n ->Bool):IsAO2 n (aL C j ⟨op,[a,b]⟩)/\(aL C j ⟨op,[a,b]⟩).size=C.size/\(aL C j ⟨op,[a,b]⟩).output=C.output/\(∀k<C.gates.length,k≠j ->gateAt (aL C j ⟨op,[a,b]⟩) k=gateAt C k)/\(∀w<n+j,wireVal n (aL C j ⟨op,[a,b]⟩) w x=wireVal n C w x)/\wireVal n (aL C j ⟨op,[a,b]⟩) (n+j) x=op.eval [wireVal n C a x,wireVal n C b x]:=by
 have hg:∀k<C.gates.length,gateAt (aL C j ⟨op,[a,b]⟩) k=Function.update (gateAt C) j ⟨op,[a,b]⟩ k:=λk hk=>bR hk;have hl:(aL C j ⟨op,[a,b]⟩).gates.length=C.gates.length:=by simp[aL]
 have hW:=gM x (m:=j) (hl▸hj.le) hj.le λk hk=>by
  rw[hg k (by omega),Function.update_of_ne (by omega)]
 refine⟨kO.mpr λk hk=>?_,hl,rfl,λk hk hkj=>by rw[hg k hk,Function.update_of_ne hkj],hW,?_⟩
 ·rcases eq_or_ne k j with rfl|hkj
  ·rw[Function.update_self];exact⟨hop,rfl,by simp[ha,hb]⟩
  ·rw[Function.update_of_ne hkj];exact⟨((bZ.mp h).1 k hk).1,((bZ.mp h).1 k hk).2,(bZ.mp h).2 k hk⟩
 ·rw[(a5 _ x).2.2 j (by omega),hg j hj,Function.update_self];simp[ha,hb,hW a ha,hW b hb]
theorem lH (hA:IsAO2 n C) (hF:circuitFun n C=graphFun G ∅) {i:ℕ} (hi:i<C.gates.length) (hb:BelowF G C i):∃C':Circuit,IsAO2 n C'/\circuitFun n C'=graphFun G ∅/\C'.size+(readers n C i).card≤C.size+1:=by
 have hDF:=mL hA hF hi hb;obtain⟨hDlen,hDout,hgD,-⟩:=eO (n:=n) C {i} ∅ C.output (n+i);obtain⟨C',hA',hfun,hsz⟩:=eD _ (fH hA {i} ∅ C.output (n+i)) (by rw[hDout,hDF];exact hb _ (dW hA _ (by omega))) (readers n C i) λr hr=>by
   obtain⟨hr,hin⟩:=mem_filter.mp hr;rw[mem_range]at hr;refine⟨by omega,λhK=>?_⟩
   have:=(hK (n+C.gates.length+1) (by
    rw[hgD r hr];simp only[gF,List.mem_map];exact⟨n+i,hin,by simp⟩)).1
   omega
 refine⟨C',hA',hfun.trans (funext λx=>by rw[←hDF x,←hDout];rfl),?_⟩;simp only[Circuit.size,hDlen]at hsz⊢;omega
theorem eC (hC:IsLeastAO G C) {i:ℕ} (hi:i<C.gates.length) (hb:BelowF G C i):(readers n C i).card≤1:=by
 obtain⟨C',hA',hF',hsz⟩:=lH hC.1 hC.2.1 hi hb;have:=hC.2.2 C' hA' hF';omega
lemma lW {j:ℕ} {g:Gate} (hj:j<C.gates.length) (x:Fin n ->Bool) (he:g.op.eval (g.inputs.map λi=>if i<n+j then wireVal n C i x else false)=wireVal n C (n+j) x) (w:ℕ):wireVal n (aL C j g) w x=wireVal n C w x:=by
 induction w using Nat.strong_induction_on with
 |_ w ih=>
  rcases Nat.lt_or_ge w n with hn|hn
  ·exact(bA _ x ⟨w,hn⟩).trans (bA C x ⟨w,hn⟩).symm
  obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by omega⟩;have hm:∀l:List ℕ,(l.map λi=>if i<n+k then wireVal n (aL C j g) i x else false)=l.map λi=>if i<n+k then wireVal n C i x else false:=λl=>List.map_congr_left λi _=>by split_ifs with h;exacts[ih i h,rfl]
  rcases Nat.lt_or_ge k C.gates.length with hk|hk
  ·rw[(a5 _ x).2.2 k (by simpa[aL]using hk),
    show gateAt (aL C j g) k=_ from bR hk,hm]
   rcases eq_or_ne k j with rfl|hkj
   ·rw[Function.update_self];exact he
   ·rw[Function.update_of_ne hkj];exact((a5 C x).2.2 k hk).symm
  ·rw[(a5 _ x).2.1 _ (by simp[aL];omega),(a5 C x).2.1 _ (by omega)]
theorem uJ (hA:IsAO2 n C) {j w:ℕ} (hj:j<C.gates.length) (hw:w<n+j) (he:∀x,wireVal n C (n+j) x=wireVal n C w x):∃C':Circuit,IsAO2 n C'/\circuitFun n C'=circuitFun n C/\C'.size+1≤C.size:=by
 have hv:=λx:Fin n ->Bool=>lW (g:=⟨GateOp.or,[w,n+C.gates.length]⟩) hj x (by simp[GateOp.eval,hw,he,not_lt.mpr hj.le]);have hl:(aL C j ⟨GateOp.or,[w,n+C.gates.length]⟩).gates.length=C.gates.length:=by
  simp[aL]
 have hg:∀k<C.gates.length,gateAt (aL C j ⟨GateOp.or,[w,n+C.gates.length]⟩) k=Function.update (gateAt C) j ⟨GateOp.or,[w,n+C.gates.length]⟩ k:=λk hk=>bR hk;by_cases hlive:wireVal n C C.output (λ_=>true)=true
 ·obtain⟨C',hA',hfun,hsz⟩:=eD _ (λk hk=>by
    rw[hl]at hk;rw[hg k hk];rcases eq_or_ne k j with rfl|hkj
    ·simp
    ·rw[Function.update_of_ne hkj];exact(bZ.mp hA).1 k hk)
   (by rw[hv];exact hlive) {j} λk hk=>by
    rw[mem_singleton.mp hk,hl];refine⟨hj,λhK=>?_⟩;have:=(hK (n+C.gates.length) (by rw[hg j hj,Function.update_self];simp)).1;omega
  exact⟨C',hA',hfun.trans (funext λx=>hv x C.output),by
   simp only[Circuit.size,hl,card_singleton]at hsz⊢;omega⟩
 ·refine⟨⟨[],n⟩,by simp[IsAO2,AndOrOnly,ReadsBack],funext λx=>?_,
   show 0+1≤C.gates.length by omega⟩
  show wireVal n ⟨[],n⟩ n x=wireVal n C C.output x;rw[(a5 _ x).2.1 n (by simp),qT (bZ.mp hA).1 (by simpa using hlive) x]
theorem d3 (hC:IsLeastAO G C) {j w:ℕ} (hj:j<C.gates.length) (hw:w<n+j):¬∀x,wireVal n C (n+j) x=wireVal n C w x:=λhe=>by
 obtain⟨C',hA',hf,hsz⟩:=uJ hC.1 hj hw he;have:=hC.2.2 C' hA' (hf.trans hC.2.1);omega
lemma jY (h:IsAO2 n C) (z:Fin n) {W:Finset (Fin n)} (hW:∀w∈W,∃a∈tops G C,∃b:Fin 2,z∈side C a (1-b)/\w∈side C a b):aB G (Ustar G C) W:=⟨z,λw hw=>by
 obtain⟨a,ha,b,hz,hw⟩:=hW w hw;have:=aV h ha b hz hw
 exact⟨this.1,λhU=>(mem_sdiff.mp (show s(z,w)∈G.edgeFinset\starEdges G C from hU)).2 this.2⟩⟩
lemma k5 (h:IsAO2 n C) {g:ℕ} (hg:g∈lam G C):aB G (Ustar G C) (orIn n C (n+g)):=by
 obtain⟨-,-,-,a,ha,b,hc,hr⟩:=jA.mp hg;obtain⟨c,hc⟩:=card_eq_one.mp hc;exact jY h c λw hw=>⟨a,ha,b,by rw[hc];exact mem_singleton_self c,a6 h hr hw⟩
lemma gO (h:IsAO2 n C) {m:ℕ} {r:Fin n} (hr:r∈orIn n C (n+m)) {W:Finset (Fin n)} (hW:∀w∈W,∃a∈tops G C,∃b:Fin 2,OrReaches n C (opnd C a b) m/\w∈side C a (1-b)):aB G (Ustar G C) W:=jY h r λw hw=>by
  obtain⟨a,ha,b,hm,hw⟩:=hW w hw;exact⟨a,ha,1-b,by rw[sub_sub_cancel];exact a6 h hm hr,hw⟩
theorem gJ (h4:NoFourCycle G) (hC:IsLeastAO G C) (hT:TopForm G C) (hj:(junk G C).card=2) (pref:Fin n ->Prop) (X:Finset (Fin n)) (hX:∀e∈Ustar G C,∃v∈X,v∈e):∃K:Finset (Fin n),K.card≤(tops G C\centreless G C).card/\(∀e∈starEdges G C,∃v∈K,v∈e)/\(∀a∈tops G C\centreless G C,∃b:Fin 2,∃p∈K,side C a (1-b)={p}/\((∃b':Fin 2,∃p',side C a (1-b')={p'}/\pref p') ->pref p))/\2+2*(centreless G C).card+(orN G C\lam G C).card+((tops G C\centreless G C).card-K.card)≤(Ustar G C).card+(X\K).card:=by
 obtain⟨K,h1,h2,h3⟩:=k3 hC.1 h4 pref;exact⟨K,h1,h2,h3,by have:=e4 h4 hC hT hj K X h2 hX;omega⟩
def cM:Prop:=∀(n':ℕ) (G':SimpleGraph (Fin n')) [DecidableRel G'.Adj] (C':Circuit) (s':Fin n' ->Bool),(∀u v,G'.Adj u v ->s' u≠s' v) ->NoFourCycle G' ->IsLeastAO G' C' ->(junk G' C').card≠1
lemma pO {w k:ℕ} (hr:OrReaches n C w k):w=n+k\/InCone n C k (w-n):=by
 induction w using Nat.strong_induction_on with
 |_ w ih=>
  obtain⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,by have:=hr.1;omega⟩;obtain⟨hj,rfl|⟨-,i,hi,hlt,hr'⟩⟩:=bD.mp hr
  ·exact Or.inl rfl
  ·right;rw[show n+j-n=j by omega];have hni:n≤ i:=hr'.1;rcases ih i hlt hr' with rfl|h
   ·exact aZ.mpr ⟨hj,k,by omega,hi,Or.inl rfl⟩
   ·exact aZ.mpr ⟨hj,i-n,by omega,by rwa[show n+(i-n)=i by omega],Or.inr h⟩
lemma dA (h:IsAO2 n C) {j:ℕ} (hj:j<C.gates.length) (b:Fin 2):opnd C j b∈(gateAt C j).inputs:=by
 rw[bO (bZ.mp h).1 hj];fin_cases b<;>simp
lemma bU (h:IsAO2 n C) {j k:ℕ} (hj:j<C.gates.length) (b:Fin 2) (hr:OrReaches n C (opnd C j b) k):InCone n C k j:=by
 have hlt:=aH h hj b;have hm:=dA h hj b;have hn:n≤opnd C j b:=hr.1;rcases pO hr with he|hc
 ·exact aZ.mpr ⟨hj,k,by omega,he▸hm,Or.inl rfl⟩
 ·exact aZ.mpr ⟨hj,opnd C j b-n,by omega,by rwa[show n+(opnd C j b-n)=opnd C j b by omega],Or.inr hc⟩
lemma cG (h:IsAO2 n C) {w g k:ℕ} (h1:OrReaches n C w g) (h2:OrReaches n C (n+g) k):OrReaches n C w k:=by
 obtain⟨-,r1⟩:=(cK h).mp h1;obtain⟨hk,r2⟩:=(cK h).mp h2;exact(cK h).mpr ⟨hk,Relation.ReflTransGen.trans r1 r2⟩
lemma d9 (h:IsAO2 n C) {g k:ℕ} (hg:g<C.gates.length) (hop:(gateAt C g).op=GateOp.or) (b:Fin 2) (hr:OrReaches n C (opnd C g b) k):OrReaches n C (n+g) k:=(dN h).mpr ⟨hg,Or.inr ⟨hop,by fin_cases b<;>simp_all⟩⟩
lemma d4 (hT:TopForm G C) {k j:ℕ} (hj:j<C.gates.length) (hkop:(gateAt C k).op=GateOp.and) (hjop:(gateAt C j).op=GateOp.and) (hc:InCone n C k j):k∈junk G C:=by
 have hk:k<C.gates.length:=(aP hc).trans hj;exact aA.mpr ⟨hk,hkop,λhb=>hT k hk j hj hkop hb hjop hc⟩
lemma a8 (h:IsAO2 n C) (hT:TopForm G C) {j:ℕ} (hj:j<C.gates.length) (hop:(gateAt C j).op=GateOp.and) (b:Fin 2) (x:Fin n ->Bool):wireVal n C (opnd C j b) x=true↔(∃v∈orIn n C (opnd C j b),x v=true)\/∃k∈junk G C,InCone n C k j/\OrReaches n C (opnd C j b) k/\gateVal n C k x=true:=by
 rw[kU h];refine or_congr Iff.rfl ⟨λ⟨k,hk,hr,hx⟩=>?_,λ⟨k,hk,_,hr,hx⟩=>?_⟩
 ·have hc:=bU h hj b hr;exact⟨k,d4 hT hj hk hop hc,hc,hr,hx⟩
 ·exact⟨k,(aA.mp hk).2.1,hr,hx⟩
lemma eA (h:IsAO2 n C) {j:ℕ} (hj:j<C.gates.length) (hop:(gateAt C j).op=GateOp.and) (x:Fin n ->Bool):gateVal n C j x=true↔wireVal n C (opnd C j 0) x=true/\wireVal n C (opnd C j 1) x=true:=by
 show wireVal n C (n+j) x=true↔_;rw[(kX h hj x).1 hop,Bool.and_eq_true]
lemma tK (hj:(junk G C).card=2):∃q r,q<r/\junk G C={q,r}:=by
 obtain⟨x,y,hxy,he⟩:=card_eq_two.mp hj;rcases lt_or_gt_of_ne hxy with h1|h1
 ·exact⟨x,y,h1,he⟩
 ·exact⟨y,x,h1,by rw[he,pair_comm]⟩
lemma eI (h:IsAO2 n C) (hT:TopForm G C) {j:ℕ} (hj:j∈junk G C) (hno:∀k∈junk G C,¬InCone n C k j) (b:Fin 2) (x:Fin n ->Bool):wireVal n C (opnd C j b) x=true↔∃v∈orIn n C (opnd C j b),x v=true:=by
 obtain⟨hjl,hop,-⟩:=aA.mp hj;rw[a8 h hT hjl hop b x];exact⟨λh1=>h1.resolve_right λ⟨k,hk,hc,_⟩=>hno k hk hc,Or.inl⟩
lemma rN (h:IsAO2 n C) (hT:TopForm G C) {j:ℕ} (hj:j∈junk G C) (hno:∀k∈junk G C,¬InCone n C k j) (x:Fin n ->Bool):gateVal n C j x=true↔(∃a∈orIn n C (opnd C j 0),x a=true)/\∃b∈orIn n C (opnd C j 1),x b=true:=by
 obtain⟨hjl,hop,-⟩:=aA.mp hj;rw[eA h hjl hop,eI h hT hj hno,eI h hT hj hno]
lemma gU {S:Finset (Fin n)} (v:Fin n):(∃a∈S,unitInput v a=true)↔v∈S:=by
 simp[unitInput]
lemma p8 {S:Finset (Fin n)}:(∃a∈S,(λ_=>true:Fin n ->Bool) a=true)↔S.Nonempty:=by simp[Finset.Nonempty]
lemma dF {q r:ℕ} (hqr:q<r) (hJ:junk G C={q,r}):∀k∈junk G C,¬InCone n C k q:=by
 intro k hk hc;have:=aP hc;rw[hJ,mem_insert,mem_singleton]at hk;omega
theorem cH (h:IsAO2 n C) (hT:TopForm G C) {j:ℕ} (hj:j∈junk G C) (hno:∀k∈junk G C,¬InCone n C k j) (hoff:∀v:Fin n,gateVal n C j (unitInput v)=false):(∀x,gateVal n C j x=true↔(∃a∈orIn n C (opnd C j 0),x a=true)/\∃b∈orIn n C (opnd C j 1),x b=true)/\(orIn n C (opnd C j 0)).Nonempty/\(orIn n C (opnd C j 1)).Nonempty/\Disjoint (orIn n C (opnd C j 0)) (orIn n C (opnd C j 1)):=by
 have hr:=rN h hT hj hno;have hall:=(hr _).mp (dW h _ (by have:=(aA.mp hj).1;omega));refine⟨hr,p8.mp hall.1,p8.mp hall.2,disjoint_left.mpr λv h1 h2=>?_⟩;have:=(hr (unitInput v)).mpr ⟨(gU v).mpr h1,(gU v).mpr h2⟩;rw[hoff v]at this;cases this
lemma eZ (hC:IsLeastAO G C) {k:ℕ} (hr:OrReaches n C C.output k):BelowF G C k:=λx hx=>by
 rw[←hC.2.1];exact aO hC.1 x hr hx
lemma jK (hC:IsLeastAO G C):orIn n C C.output=∅:=by
 refine eq_empty_of_forall_notMem λv hv=>?_;have h1:=bY hC.1 hv (x:=unitInput v) (by simp[unitInput]);have h2:wireVal n C C.output (unitInput v)=graphFun G ∅ (unitInput v):=congrFun hC.2.1 _;rw[h1,e8]at h2;cases h2
theorem fD (hC:IsLeastAO G C) (hT:TopForm G C) {u v:Fin n} (he:s(u,v)∈Ustar G C):∃a∈tops G C,gateVal n C a (pairInput u v)=true/\∃b:Fin 2,∃k∈junk G C,InCone n C k a/\OrReaches n C (opnd C a b) k/\gateVal n C k (pairInput u v)=true:=by
 have hA:=hC.1;obtain⟨heG,hst⟩:=mem_sdiff.mp (show s(u,v)∈G.edgeFinset\starEdges G C from he);have hadj:G.Adj u v:=SimpleGraph.mem_edgeFinset.mp heG;have hout:wireVal n C C.output (pairInput u v)=true:=by
  rw[show wireVal n C C.output (pairInput u v)=graphFun G ∅ (pairInput u v)from congrFun hC.2.1 _,aT];exact hadj
 obtain⟨w,hw,-⟩|⟨a,hop,hr,hx⟩:=(kU hA _ _).mp hout
 ·rw[jK hC]at hw;simp at hw
 have hal:=(aX hr).2;have ha:a∈tops G C:=aI.mpr ⟨hal,hop,eZ hC hr⟩;refine⟨a,ha,hx,?_⟩;obtain⟨h0,h1⟩:=(eA hA hal hop _).mp hx;have hpi:∀w:Fin n,pairInput u v w=true ->w=u\/w=v:=λw hw=>by
  simpa[pairInput]using hw
 rcases (a8 hA hT hal hop 0 _).mp h0 with⟨u0,hu0,hx0⟩|⟨k,hk,hc,hr,hx⟩
 ·rcases (a8 hA hT hal hop 1 _).mp h1 with⟨v0,hv0,hx1⟩|⟨k,hk,hc,hr,hx⟩
  ·exfalso;have hadj0:=cE hA ha hu0 hv0;have hs:s(u0,v0)∈starEdges G C:=(aV hA ha 1 hu0 hv0).2;have:s(u0,v0)=s(u,v):=by
    rcases hpi u0 hx0 with rfl|rfl<;>rcases hpi v0 hx1 with rfl|rfl
    ·exact(G.irrefl hadj0).elim
    ·rfl
    ·exact Sym2.eq_swap
    ·exact(G.irrefl hadj0).elim
   exact hst (this▸hs)
  ·exact⟨1,k,hk,hc,hr,hx⟩
 ·exact⟨0,k,hk,hc,hr,hx⟩
lemma rX (h:IsAO2 n C) {g k:ℕ} (hg:g<C.gates.length) (hop:(gateAt C g).op=GateOp.or) (hk:k∈junk G C) (hr:OrReaches n C (n+g) k):g∈orN G C:=by
 refine dS.mpr ⟨hg,hop,λhb=>(aA.mp hk).2.2 λx hx=>hb x ?_⟩;exact aO h x hr hx
lemma qD {g:ℕ} {b:Fin 2} (he:orIn n C (opnd C g b)=∅):g∉lam G C:=by
 intro hg;obtain⟨-,h0,h1,-⟩:=jA.mp hg;fin_cases b
 ·exact h0.ne_empty he
 ·exact h1.ne_empty he
lemma f0 (h:IsAO2 n C) {g k:ℕ} (hg:g<C.gates.length) (hop:(gateAt C g).op=GateOp.or) (hk:k∈junk G C) (hr:OrReaches n C (n+g) k) {b:Fin 2} (he:orIn n C (opnd C g b)=∅):g∈orN G C\lam G C:=mem_sdiff.mpr ⟨rX h hg hop hk hr,qD he⟩
theorem fE (h:IsAO2 n C) {k:ℕ} (hk:(gateAt C k).op=GateOp.and):∀{w:ℕ},OrReaches n C w k ->(orIn n C w).Nonempty ->∃m,∃b:Fin 2,m<C.gates.length/\(gateAt C m).op=GateOp.or/\OrReaches n C w m/\(orIn n C (n+m)).Nonempty/\orIn n C (opnd C m b)=∅/\OrReaches n C (opnd C m b) k:=by
 intro w
 induction w using Nat.strong_induction_on with
 |_ w ih=>
  intro hr hne;obtain⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,by have:=hr.1;omega⟩;obtain⟨hj,rfl|⟨hop,hb⟩⟩:=(dN h).mp hr
  ·rw[b6 (λ_=>by rw[hk];simp)]at hne;simp at hne
  ·have key:∀b:Fin 2,OrReaches n C (opnd C j b) k ->∃m,∃b:Fin 2,m<C.gates.length/\(gateAt C m).op=GateOp.or/\OrReaches n C (n+j) m/\(orIn n C (n+m)).Nonempty/\orIn n C (opnd C m b)=∅/\OrReaches n C (opnd C m b) k:=λb hb=>by
    by_cases he:orIn n C (opnd C j b)=∅
    ·exact⟨j,b,hj,hop,bD.mpr ⟨hj,Or.inl rfl⟩,hne,he,hb⟩
    ·obtain⟨m,b',h1,h2,h3,h4⟩:=ih _ (aH h hj b) hb (nonempty_iff_ne_empty.mpr he);exact⟨m,b',h1,h2,d9 h hj hop b h3,h4⟩
   rcases hb with hb|hb
   ·exact key 0 hb
   ·exact key 1 hb
lemma fR (h:IsAO2 n C) (hT:TopForm G C) {q r:ℕ} (hqr:q<r) (hJ:junk G C={q,r}) (b:Fin 2) (x:Fin n ->Bool):wireVal n C (opnd C r b) x=true↔(∃v∈orIn n C (opnd C r b),x v=true)\/OrReaches n C (opnd C r b) q/\gateVal n C q x=true:=by
 have hr:r∈junk G C:=by rw[hJ];simp
 obtain⟨hrl,hop,-⟩:=aA.mp hr;rw[a8 h hT hrl hop b x];refine or_congr Iff.rfl ⟨λ⟨k,hk,hc,hr',hx⟩=>?_,λ⟨h1,h2⟩=>?_⟩
 ·rw[hJ,mem_insert,mem_singleton]at hk;rcases hk with rfl|rfl
  ·exact⟨hr',hx⟩
  ·exact absurd (aP hc) (lt_irrefl _)
 ·exact⟨q,by rw[hJ];simp,bU h hrl b h1,h1,h2⟩
lemma nS (h:IsAO2 n C) {a:ℕ}:∀{k:ℕ},InCone n C a k ->OrReaches n C (n+k) a\/∃k₂,(gateAt C k₂).op=GateOp.and/\InCone n C a k₂/\(k₂=k\/InCone n C k₂ k):=by
 intro k
 induction k using Nat.strong_induction_on with
 |_ k ih=>
  intro hc;obtain⟨hk,k1,hk1,hin,h3⟩:=aZ.mp hc;rcases eS h hk with hop|hop
  ·exact Or.inr ⟨k,hop,hc,Or.inl rfl⟩
  ·have hup:OrReaches n C (n+k1) a ->OrReaches n C (n+k) a:=λh1=>bD.mpr ⟨hk,Or.inr ⟨hop,_,hin,by omega,h1⟩⟩;have hk1c:InCone n C k1 k:=aZ.mpr ⟨hk,k1,hk1,hin,Or.inl rfl⟩;rcases h3 with rfl|h3
   ·exact Or.inl (hup (bD.mpr ⟨by omega,Or.inl rfl⟩))
   ·rcases ih k1 hk1 h3 with h4|⟨k₂,h5,h6,h7⟩
    ·exact Or.inl (hup h4)
    ·exact Or.inr ⟨k₂,h5,h6,Or.inr (h7.elim (·▸hk1c) λh8=>dI h8 hk1c)⟩
theorem g8 (h:IsAO2 n C) (hT:TopForm G C) {q r:ℕ} (hqr:q<r) (hJ:junk G C={q,r}) (hc:InCone n C q r):∃b:Fin 2,OrReaches n C (opnd C r b) q:=by
 have hr:r∈junk G C:=by rw[hJ];simp
 obtain⟨hrl,hop,-⟩:=aA.mp hr;obtain⟨-,k0,hk0,hin,h3⟩:=aZ.mp hc;have hb:∃b:Fin 2,opnd C r b=n+k0:=by
  rw[bO (bZ.mp h).1 hrl]at hin;simp only[List.mem_cons,List.not_mem_nil,or_false]at hin;rcases hin with h1|h1
  ·exact⟨0,h1.symm⟩
  ·exact⟨1,h1.symm⟩
 obtain⟨b,hb⟩:=hb;refine⟨b,hb▸?_⟩;have hk0c:InCone n C k0 r:=aZ.mpr ⟨hrl,k0,hk0,by rw[←hb];exact dA h hrl b,Or.inl rfl⟩;rcases h3 with rfl|h3
 ·exact bD.mpr ⟨by omega,Or.inl rfl⟩
 rcases nS h h3 with h4|⟨k₂,hop₂,h5,h6⟩
 ·exact h4
 ·exfalso;have hk2r:InCone n C k₂ r:=h6.elim (·▸hk0c) λh7=>dI h7 hk0c;have:=d4 hT hrl hop₂ hop hk2r;rw[hJ,mem_insert,mem_singleton]at this;rcases this with rfl|rfl
  ·exact lt_irrefl _ (aP h5)
  ·exact lt_irrefl _ (aP hk2r)
lemma bG (b:Fin 2):b=0/\1-b=1\/b=1/\1-b=0:=by fin_cases b<;>simp
lemma aN (h:IsAO2 n C) {j:ℕ} (hj:j<C.gates.length) (hop:(gateAt C j).op=GateOp.and) (b:Fin 2) (x:Fin n ->Bool):gateVal n C j x=true↔wireVal n C (opnd C j b) x=true/\wireVal n C (opnd C j (1-b)) x=true:=by
 rw[eA h hj hop];rcases bG b with⟨rfl,h1⟩|⟨rfl,h1⟩<;>rw[h1];exact and_comm
theorem cN (h:IsAO2 n C) (hT:TopForm G C) {q r:ℕ} (hqr:q<r) (hJ:junk G C={q,r}) (hoff:∀k∈junk G C,∀v:Fin n,gateVal n C k (unitInput v)=false) {b:Fin 2} (hb:OrReaches n C (opnd C r b) q) (hnb:¬OrReaches n C (opnd C r (1-b)) q):(∀x,gateVal n C r x=true↔(gateVal n C q x=true\/∃c∈orIn n C (opnd C r b),x c=true)/\∃d∈orIn n C (opnd C r (1-b)),x d=true)/\(orIn n C (opnd C r (1-b))).Nonempty/\Disjoint (orIn n C (opnd C r b)) (orIn n C (opnd C r (1-b))):=by
 have hr:r∈junk G C:=by rw[hJ];simp
 have hq:q∈junk G C:=by rw[hJ];simp
 obtain⟨hrl,hop,-⟩:=aA.mp hr;have hval:∀x,gateVal n C r x=true↔(gateVal n C q x=true\/∃c∈orIn n C (opnd C r b),x c=true)/\∃d∈orIn n C (opnd C r (1-b)),x d=true:=λx=>by
   rw[aN h hrl hop b,fR h hT hqr hJ,fR h hT hqr hJ];constructor
   ·rintro⟨h1|h1,h2|h2⟩
    ·exact⟨Or.inr h1,h2⟩
    ·exact absurd h2.1 hnb
    ·exact⟨Or.inl h1.2,h2⟩
    ·exact absurd h2.1 hnb
   ·rintro⟨h1|h1,h2⟩
    ·exact⟨Or.inr ⟨hb,h1⟩,Or.inl h2⟩
    ·exact⟨Or.inl h1,Or.inl h2⟩
 have hall:=(hval _).mp (dW h _ (by omega));refine⟨hval,p8.mp hall.2,disjoint_left.mpr λv h1 h2=>?_⟩;have:=(hval (unitInput v)).mpr ⟨Or.inr ((gU v).mpr h1),(gU v).mpr h2⟩;rw[hoff r hr v]at this;cases this
theorem gE (h:IsAO2 n C) (hT:TopForm G C) {q r:ℕ} (hqr:q<r) (hJ:junk G C={q,r}) (hoff:∀k∈junk G C,∀v:Fin n,gateVal n C k (unitInput v)=false) (h0:OrReaches n C (opnd C r 0) q) (h1:OrReaches n C (opnd C r 1) q):(∀x,gateVal n C r x=true↔(gateVal n C q x=true\/∃c∈orIn n C (opnd C r 0),x c=true)/\(gateVal n C q x=true\/∃d∈orIn n C (opnd C r 1),x d=true))/\Disjoint (orIn n C (opnd C r 0)) (orIn n C (opnd C r 1)):=by
 have hr:r∈junk G C:=by rw[hJ];simp
 have hq:q∈junk G C:=by rw[hJ];simp
 obtain⟨hrl,hop,-⟩:=aA.mp hr;have hval:∀x,gateVal n C r x=true↔(gateVal n C q x=true\/∃c∈orIn n C (opnd C r 0),x c=true)/\(gateVal n C q x=true\/∃d∈orIn n C (opnd C r 1),x d=true):=λx=>by
  rw[eA h hrl hop,fR h hT hqr hJ,fR h hT hqr hJ];simp only[h0,h1,true_and];exact and_congr or_comm or_comm
 refine⟨hval,disjoint_left.mpr λv h2 h3=>?_⟩;have:=(hval (unitInput v)).mpr ⟨Or.inr ((gU v).mpr h2),Or.inr ((gU v).mpr h3)⟩;rw[hoff r hr v]at this;cases this
def mM (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit):Prop:=∀q r,q<r ->junk G C={q,r} ->2≤(orIn n C (opnd C q 0)).card/\2≤(orIn n C (opnd C q 1)).card
def sE (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit):Prop:=∀q r,q<r ->junk G C={q,r} ->¬InCone n C q r ->False
def tQ (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit):Prop:=∀q r,q<r ->junk G C={q,r} ->OrReaches n C (opnd C r 0) q ->OrReaches n C (opnd C r 1) q ->False
def tZ (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit):Prop:=∀q r (b:Fin 2),q<r ->junk G C={q,r} ->OrReaches n C (opnd C r b) q ->¬OrReaches n C (opnd C r (1-b)) q ->orIn n C (opnd C r b)=∅ ->False
theorem jH (hC:IsLeastAO G C) (hT:TopForm G C) (hj:(junk G C).card=2) (hoff:∀k∈junk G C,∀v:Fin n,gateVal n C k (unitInput v)=false) (hW:mM G C) (hP:sE G C) (hII:tQ G C) (hB1:tZ G C):∃q r,q<r/\junk G C={q,r}/\InCone n C q r/\(∀x,gateVal n C q x=true↔(∃a∈orIn n C (opnd C q 0),x a=true)/\∃b∈orIn n C (opnd C q 1),x b=true)/\Disjoint (orIn n C (opnd C q 0)) (orIn n C (opnd C q 1))/\2≤(orIn n C (opnd C q 0)).card/\2≤(orIn n C (opnd C q 1)).card/\∃b:Fin 2,OrReaches n C (opnd C r b) q/\¬OrReaches n C (opnd C r (1-b)) q/\(orIn n C (opnd C r b)).Nonempty/\(orIn n C (opnd C r (1-b))).Nonempty/\Disjoint (orIn n C (opnd C r b)) (orIn n C (opnd C r (1-b)))/\∀x,gateVal n C r x=true↔(gateVal n C q x=true\/∃c∈orIn n C (opnd C r b),x c=true)/\∃d∈orIn n C (opnd C r (1-b)),x d=true:=by
 have h:=hC.1;obtain⟨q,r,hqr,hJ⟩:=tK hj;have hq:q∈junk G C:=by rw[hJ];simp
 obtain⟨hqv,-,-,hqd⟩:=cH h hT hq (dF hqr hJ) (hoff q hq);obtain⟨hA2,hB2⟩:=hW q r hqr hJ;have hc:InCone n C q r:=by_contra λhc=>hP q r hqr hJ hc;obtain⟨b,hb⟩:=g8 h hT hqr hJ hc;have hnb:¬OrReaches n C (opnd C r (1-b)) q:=λhnb=>by
  rcases bG b with⟨rfl,h1⟩|⟨rfl,h1⟩<;>rw[h1]at hnb
  ·exact hII q r hqr hJ hb hnb
  ·exact hII q r hqr hJ hnb hb
 have hCne:(orIn n C (opnd C r b)).Nonempty:=nonempty_iff_ne_empty.mpr λhe=>hB1 q r b hqr hJ hb hnb he;obtain⟨hrv,hDne,hCD⟩:=cN h hT hqr hJ hoff hb hnb;exact⟨q,r,hqr,hJ,hc,hqv,hqd,hA2,hB2,b,hb,hnb,hCne,hDne,hCD,hrv⟩
def fY (C D:Circuit) (j:ℕ):Prop:=D.gates.length=C.gates.length/\∀k<C.gates.length,k≠j ->gateAt D k=gateAt C k
def aG (n:ℕ) (C:Circuit) (j:ℕ):Circuit:=aL C j ⟨GateOp.and,[n+j,n+j]⟩
lemma cV (j:ℕ) (g:Gate):fY C (aL C j g) j:=⟨by simp[aL],λk hk hkj=>by
  rw[show gateAt (aL C j g) k=_ from bR hk,Function.update_of_ne hkj]⟩
lemma bJ (j:ℕ):fY C (aG n C j) j:=cV j _
lemma mJ {j:ℕ} (hj:j<C.gates.length) (x:Fin n ->Bool):wireVal n (aG n C j) (n+j) x=false:=by
 rw[aG,(a5 _ x).2.2 j (by simpa[aL]using hj),
  show gateAt (aL C j _) j=_ from bR hj,Function.update_self]
 simp[GateOp.eval]
lemma kQ {C₁ C₂:Circuit} {m j:ℕ} (h1:m≤C₁.gates.length) (h2:m≤C₂.gates.length) (hg:∀k<m,k≠j ->gateAt C₁ k=gateAt C₂ k) (hop:∀k<m,k≠j ->(gateAt C₁ k).op=GateOp.and\/(gateAt C₁ k).op=GateOp.or) (x:Fin n ->Bool) (hj:wireVal n C₁ (n+j) x=true ->wireVal n C₂ (n+j) x=true):∀w<n+m,wireVal n C₁ w x=true ->wireVal n C₂ w x=true:=by
 intro w
 induction w using Nat.strong_induction_on with
 |_ w ih=>
  intro hw hx;rcases Nat.lt_or_ge w n with hn|hn
  ·rwa[bA C₂ x ⟨w,hn⟩,←bA C₁ x ⟨w,hn⟩]
  obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by omega⟩;by_cases hkj:k=j
  ·subst hkj;exact hj hx
  rw[(a5 C₁ x).2.2 k (by omega)]at hx;rw[(a5 C₂ x).2.2 k (by omega),←hg k (by omega) hkj];refine pE (hop k (by omega) hkj) _ _ _ (λi _ hi=>?_) hx;split_ifs at hi⊢with hik;exact ih i (by omega) (by omega) hi
lemma eB {D:Circuit} {j:ℕ} (hD:fY C D j) (x:Fin n ->Bool):∀w,w≠n+j ->(n≤w ->¬InCone n C j (w-n)) ->wireVal n D w x=wireVal n C w x:=by
 intro w
 induction w using Nat.strong_induction_on with
 |_ w ih=>
  intro hwj hc;rcases Nat.lt_or_ge w n with hn|hn
  ·exact(bA D x ⟨w,hn⟩).trans (bA C x ⟨w,hn⟩).symm
  obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by omega⟩;have hkj:k≠j:=λh=>hwj (by rw[h]);have hc':¬InCone n C j k:=by simpa using hc hn
  rcases Nat.lt_or_ge k C.gates.length with hk|hk
  ·rw[(a5 D x).2.2 k (by rw[hD.1];exact hk),(a5 C x).2.2 k hk,hD.2 k hk hkj]
   congr 1
   refine List.map_congr_left λi hi=>?_;split_ifs with hik
   ·refine ih i hik (λhe=>hc' (aZ.mpr ⟨hk,j,by omega,he▸hi,Or.inl rfl⟩)) λhni hcj=>hc' (aZ.mpr ⟨hk,i-n,by omega,by rwa[show n+(i-n)=i by omega],Or.inr hcj⟩)
   ·rfl
  ·rw[(a5 D x).2.1 _ (by rw[hD.1];omega),(a5 C x).2.1 _ (by omega)]
lemma fB (h:IsAO2 n C) {D:Circuit} {j:ℕ} (hD:fY C D j) (hjop:(gateAt C j).op=GateOp.and) (x:Fin n ->Bool) {a:ℕ}:∀{w:ℕ},OrReaches n C w a ->wireVal n D (n+a) x=true ->wireVal n D w x=true:=by
 intro w
 induction w using Nat.strong_induction_on with
 |_ w ih=>
  intro hr ha;obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by have:=hr.1;omega⟩;obtain⟨hk,rfl|⟨hop,hb⟩⟩:=(dN h).mp hr
  ·exact ha
  have hkj:k≠j:=λhe=>by rw[he,hjop]at hop;cases hop
  rw[(a5 D x).2.2 k (by rw[hD.1];exact hk),hD.2 k hk hkj,hop,bO (bZ.mp h).1 hk];have h0:=aH h hk 0;have h1:=aH h hk 1;rcases hb with hb|hb
  ·simp[GateOp.eval,h0,ih _ h0 hb ha]
  ·simp[GateOp.eval,h1,ih _ h1 hb ha]
lemma b9 (h:IsAO2 n C) {D:Circuit} {j:ℕ} (hD:fY C D j) (hjop:(gateAt C j).op=GateOp.and) {x:Fin n ->Bool} {w:ℕ} {v:Fin n} (hv:v∈orIn n C w) (hx:x v=true):wireVal n D w x=true:=by
 rcases dV.mp hv with he|⟨k,hk,hr,hop,hin⟩
 ·rw[←he,bA D x v];exact hx
 refine fB h hD hjop x hr ?_;have hkj:k≠j:=λhe=>by rw[he,hjop]at hop;cases hop
 rw[(a5 D x).2.2 k (by rw[hD.1];exact hk),hD.2 k hk hkj,hop];simp only[GateOp.eval,List.any_map,List.any_eq_true,Function.comp,id];exact⟨v,hin,by simp[show(v:ℕ)<n+k by omega,bA D x v,hx]⟩
lemma fV (h:IsAO2 n C) {D:Circuit} {j:ℕ} (hD:fY C D j) {a:ℕ} (ha:a<C.gates.length) (haj:a≠j) (hop:(gateAt C a).op=GateOp.and) (x:Fin n ->Bool):wireVal n D (n+a) x=(wireVal n D (opnd C a 0) x&&wireVal n D (opnd C a 1) x):=by
 rw[(a5 D x).2.2 a (by rw[hD.1];exact ha),hD.2 a ha haj,hop,bO (bZ.mp h).1 ha];simp[GateOp.eval,aH h ha 0,aH h ha 1]
lemma kS (hC:IsLeastAO G C) (hT:TopForm G C) {D:Circuit} {j:ℕ} (hD:fY C D j) (hjop:(gateAt C j).op=GateOp.and) {a:ℕ} (ha:a∈tops G C) (haj:a≠j) {x:Fin n ->Bool} (h0:wireVal n D (opnd C a 0) x=true) (h1:wireVal n D (opnd C a 1) x=true):wireVal n D C.output x=true:=by
 obtain⟨hal,hop,-⟩:=aI.mp ha;refine fB hC.1 hD hjop x (kT hC hT ha) ?_;rw[fV hC.1 hD hal haj hop,h0,h1];rfl
theorem cT (hC:IsLeastAO G C) {j:ℕ} (hj:j<C.gates.length) {op:GateOp} (hop:op=GateOp.and\/op=GateOp.or) {a b:ℕ} (ha:a<n+j) (hb:b<n+j) (hle:∀x,op.eval [wireVal n C a x,wireVal n C b x]=true ->gateVal n C j x=true) (hacc:∀u v,G.Adj u v ->wireVal n (aG n C j) C.output (pairInput u v)=true\/op.eval [wireVal n C a (pairInput u v),wireVal n C b (pairInput u v)]=true):IsLeastAO G (aL C j ⟨op,[a,b]⟩)/\(∀k∈junk G (aL C j ⟨op,[a,b]⟩),k=j\/k∈junk G C)/\∀k∈junk G C,k≠j ->¬InCone n C j k ->k∈junk G (aL C j ⟨op,[a,b]⟩):=by
 have hA:=hC.1;obtain⟨hA',hsz,hout,-,-,hval⟩:=b7 hA hj hop ha hb (λ_=>true);have hD:=cV (C:=C) j ⟨op,[a,b]⟩;set D:=aL C j ⟨op,[a,b]⟩;have hopC:∀k<C.gates.length,k≠j ->(gateAt C k).op=GateOp.and\/(gateAt C k).op=GateOp.or:=λk hk _=>eS hA hk;have hlen:=hD.1
 have hDC:∀x,∀w<n+C.gates.length,wireVal n D w x=true ->wireVal n C w x=true:=λx=>kQ (C₁:=D) (C₂:=C) (m:=C.gates.length) hlen.ge le_rfl (λk hk hkj=>hD.2 k hk hkj) (λk hk hkj=>by rw[hD.2 k hk hkj];exact eS hA hk) x (λh1=>by
    rw[(b7 hA hj hop ha hb x).2.2.2.2.2]at h1;exact hle x h1)
 have hlow:∀x,wireVal n D C.output x=true ->graphFun G ∅ x=true:=λx h1=>by
  rw[←show wireVal n C C.output x=graphFun G ∅ x from congrFun hC.2.1 x];by_cases ho:C.output<n+C.gates.length
  ·exact hDC x _ ho h1
  ·rw[(a5 D x).2.1 _ (by rw[hlen];omega)]at h1;cases h1
 have hacc':∀u v,G.Adj u v ->wireVal n D C.output (pairInput u v)=true:=by
  intro u v huv;have hF:wireVal n C C.output (pairInput u v)=true:=by
   rw[show wireVal n C C.output _=graphFun G ∅ _ from congrFun hC.2.1 _,aT];exact huv
  rcases hacc u v huv with h1|h1
  ·by_cases ho:C.output<n+C.gates.length
   ·have hK:fY C (aG n C j) j:=bJ j;refine kQ (C₁:=aG n C j) (C₂:=D) (m:=C.gates.length) hK.1.ge hlen.ge (λk hk hkj=>(hK.2 k hk hkj).trans (hD.2 k hk hkj).symm) (λk hk hkj=>by rw[hK.2 k hk hkj];exact eS hA hk) _ (λh2=>by rw[mJ hj]at h2;cases h2) _ ho h1
   ·rw[(a5 (aG n C j) _).2.1 _ (by simp[aG,aL];omega)]at h1;cases h1
  ·rw[lW hj _ (by simpa[ha,hb]using(show op.eval [wireVal n C a _,wireVal n C b _]=wireVal n C (n+j) _ from by rw[h1];exact(hle _ h1).symm))];exact hF
 have hF:circuitFun n D=graphFun G ∅:=by
  have:=uO (G:=G) hA' (λx h1=>hlow x (by rw[←hout];exact h1)) (λu v huv=>by show wireVal n D D.output _=true;rw[hout];exact hacc' u v huv);exact this
 refine⟨⟨hA',hF,λC' h1 h2=>hsz▸hC.2.2 C' h1 h2⟩,λk hk=>?_,λk hk hkj hc=>?_⟩
 ·obtain⟨hkl,hkop,hkb⟩:=aA.mp hk;rcases eq_or_ne k j with rfl|hkj
  ·exact Or.inl rfl
  right;rw[hlen]at hkl;rw[hD.2 k hkl hkj]at hkop;exact aA.mpr ⟨hkl,hkop,λhb'=>hkb λx hx=>hb' x (hDC x _ (by omega) hx)⟩
 ·obtain⟨hkl,hkop,hkb⟩:=aA.mp hk;have he:∀x,gateVal n D k x=gateVal n C k x:=λx=>eB hD x (n+k) (by omega) λ_=>by simpa using hc
  refine aA.mpr ⟨by rw[hlen];exact hkl,by rw[hD.2 k hkl hkj];exact hkop,λhb'=>hkb λx hx=>hb' x (by rw[he];exact hx)⟩
theorem jJ (hC:IsLeastAO G C) {j:ℕ} (hj:j<C.gates.length) (hacc:∀u v,G.Adj u v ->wireVal n (aG n C j) C.output (pairInput u v)=true):False:=by
 have hA:=hC.1;by_cases hE:∃u v,G.Adj u v
 swap
 ·have hz:circuitFun n ⟨[],n⟩=graphFun G ∅:=funext λx=>by
   rw[show circuitFun n ⟨[],n⟩ x=wireVal n ⟨[],n⟩ n x from rfl,(a5 _ x).2.1 n (by simp)]
   exact(Bool.eq_false_iff.mpr λh1=>by
    obtain⟨u,v,huv,-⟩:=(dJ x).mp h1;exact hE ⟨u,v,huv⟩).symm
  have h0:C.gates.length≤0:=hC.2.2 _ (by simp[IsAO2,AndOrOnly,ReadsBack]) hz;omega
 obtain⟨u0,v0,huv0⟩:=hE;have ho:C.output<n+C.gates.length:=by
  by_contra ho;have:=hacc u0 v0 huv0;rw[(a5 (aG n C j) _).2.1 _ (by simp[aG,aL];omega)]at this;cases this
 obtain⟨hDlen,hDout,hgD,hgm⟩:=eO (n:=n) C ∅ {j} C.output (n+C.gates.length+1);have hDA:=fH hA ∅ {j} C.output (n+C.gates.length+1);have hval:=λx=>eX hA ∅ {j} C.output (n+C.gates.length+1) x
 generalize hDdef:bQ n C ∅ {j} C.output (n+C.gates.length+1)=D at*
 have hgk:∀k<C.gates.length,k≠j ->gateAt D k=gateAt C k:=λk hk hkj=>by
  rw[hgD k hk,gF];simp[hkj]
 have hDj:∀x,wireVal n D (n+j) x=false:=λx=>by
  rw[(a5 D x).2.2 j (by omega),hgD j hj,gF,bO (bZ.mp hA).1 hj];have hd:¬(n+C.gates.length+1<n+j):=by omega
  rcases eS hA hj with hop|hop<;>simp[hop,GateOp.eval,hd]
 have hout:∀x,wireVal n D D.output x=wireVal n D C.output x:=λx=>by
  rw[hDout,(a5 D x).2.2 _ (by omega),hgm];simp[GateOp.eval,ho]
 have hK:fY C (aG n C j) j:=bJ j;have hKD:∀x,wireVal n (aG n C j) C.output x=true ->wireVal n D C.output x=true:=λx=>kQ (C₁:=aG n C j) (C₂:=D) (m:=C.gates.length) hK.1.ge (by omega) (λk hk hkj=>(hK.2 k hk hkj).trans (hgk k hk hkj).symm) (λk hk hkj=>by rw[hK.2 k hk hkj];exact eS hA hk) x (λh2=>by rw[mJ hj]at h2;cases h2) _ ho;have hFD:∀x,wireVal n D D.output x=graphFun G ∅ x:=λx=>by
  rw[hout,Bool.eq_iff_iff];constructor
  ·intro h1;rw[←show wireVal n C C.output x=graphFun G ∅ x from congrFun hC.2.1 x];exact(hval x _ ho).1 h1
  ·intro h1;obtain⟨u,v,huv,hu,hv⟩:=(dJ x).mp h1
   exact nH hDA (x:=pairInput u v) (λw hw=>by
    simp only[pairInput,decide_eq_true_eq]at hw;rcases hw with rfl|rfl<;>assumption)
    _ (hKD _ (hacc u v huv))
 have hl:wireVal n D D.output (λ_=>true)=true:=by
  rw[hFD,dJ];exact⟨u0,v0,huv0,rfl,rfl⟩
 obtain⟨C',hA',hfun,hsz⟩:=eD (n:=n) D hDA hl {j,C.gates.length} (by
  intro k hk';simp only[mem_insert,mem_singleton]at hk';rcases hk' with rfl|rfl
  ·refine⟨by omega,λhK'=>?_⟩
   have:=(hK' (n+C.gates.length+1) (by
    rw[hgD _ hj,gF,bO (bZ.mp hA).1 hj];simp)).1
   omega
  ·refine⟨by omega,λhK'=>?_⟩;have:=(hK' (n+C.gates.length+1) (by rw[hgm];simp)).1
   omega)
 have:=hC.2.2 C' hA' (hfun.trans (funext hFD));rw[card_pair (by omega)]at hsz;simp only[Circuit.size]at this hsz;omega
def kV {ν α:Type} [DecidableEq α] (f:ν ->Finset α) (R:List ν) (i:ℕ):Finset α:=((R.drop i).map f).foldr (·∪·) ∅
lemma rQ {ν α:Type} [DecidableEq α] {f:ν ->Finset α} {x:α} (R:List ν) (i:ℕ):x∈kV f R i↔∃v∈R.drop i,x∈f v:=by
 unfold kV
 generalize R.drop i=L
 induction L with
 |nil=>simp
 |cons v L ih=>simp[ih]
def eR {ν:Type} (J:ν ->Prop) (R:List ν):ν⊕ℕ ->Prop:=Sum.elim J λi=>i+1<R.length
def gG {ν:Type} (l:ν ->ν) (R:List ν) (d:ν):ν⊕ℕ ->ν⊕ℕ:=Sum.elim (λv=>Sum.inl (l v)) λi=>Sum.inl (R.getD i d)
def f5 {ν:Type} (r:ν ->ν) (R:List ν) (d:ν):ν⊕ℕ ->ν⊕ℕ:=Sum.elim (λv=>Sum.inl (r v)) λi=>if i+2<R.length then Sum.inr (i+1)else Sum.inl (R.getD (i+1) d)
def sL {ν:Type} (rk:ν ->ℕ) (R:List ν):ν⊕ℕ ->ℕ:=Sum.elim rk λi=>(R.map rk).sum+1+R.length-i
def jS {ν α:Type} [DecidableEq α] (f:ν ->Finset α) (R:List ν):ν⊕ℕ ->Finset α:=Sum.elim f (kV f R)
def dM {ν:Type} (R:List ν) (d:ν):ν⊕ℕ:=if 1<R.length then Sum.inr 0 else Sum.inl (R.getD 0 d)
theorem nL {ν α:Type} [DecidableEq α] {J:ν ->Prop} {l r:ν ->ν} {rk:ν ->ℕ} {f:ν ->Finset α} (hD:dB J l r rk f) (R:List ν) (d:ν):dB (eR J R) (gG l R d) (f5 r R d) (sL rk R) (jS f R):=by
 rintro(v|i) hw
 ·exact hD v hw
 simp only[eR,Sum.elim_inr]at hw;have hi:i<R.length:=by omega
 have hmem:∀t (ht:t<R.length),rk (R.getD t d)≤(R.map rk).sum:=λt ht=>by
  rw[List.getD_eq_getElem _ _ ht];exact List.le_sum_of_mem (List.mem_map.mpr ⟨_,List.getElem_mem ht,rfl⟩)
 have hU:∀t (ht:t<R.length),kV f R t=f (R.getD t d)∪kV f R (t+1):=λt ht=>by
   simp only[kV,List.drop_eq_getElem_cons ht,List.map_cons,List.foldr_cons,List.getD_eq_getElem _ _ ht]
 simp only[gG,f5,sL,jS,Sum.elim_inr];refine⟨by have:=hmem i hi;simp only[Sum.elim_inl];omega,?_,?_⟩
 ·split_ifs with h2
  ·simp only[Sum.elim_inr];omega
  ·have:=hmem (i+1) (by omega);simp only[Sum.elim_inl];omega
 ·rw[hU i hi];split_ifs with h2
  ·simp only[Sum.elim_inl,Sum.elim_inr]
  ·have he:kV f R (i+1)=f (R.getD (i+1) d):=by
    rw[hU (i+1) hw];simp[kV,List.drop_eq_nil_of_le (show R.length≤ i+1+1 by omega)]
   simp only[Sum.elim_inl,he]
lemma eL {ν:Type} {J:ν ->Prop} {l r:ν ->ν} {R:List ν} {d:ν} {v:ν} {u:ν⊕ℕ} (h:aM (eR J R) (gG l R d) (f5 r R d) (Sum.inl v) u):∃w,u=Sum.inl w/\aM J l r v w:=by
 induction h with
 |refl=>exact⟨v,rfl, .refl⟩
 |tail _ hs ih=>
  obtain⟨w,rfl,hw⟩:=ih;obtain⟨hJ,he|he⟩:=hs
  ·exact⟨l w,he,hw.tail ⟨hJ,Or.inl rfl⟩⟩
  ·exact⟨r w,he,hw.tail ⟨hJ,Or.inr rfl⟩⟩
lemma pC {ν:Type} {J:ν ->Prop} {l r:ν ->ν} {R:List ν} {d:ν} {i:ℕ} (hi:i+1<R.length) {u:ν⊕ℕ} (h:aM (eR J R) (gG l R d) (f5 r R d) (Sum.inr i) u):(∃i',u=Sum.inr i'/\i'+1<R.length)\/∃t<R.length,∃w,u=Sum.inl w/\aM J l r (R.getD t d) w:=by
 induction h with
 |refl=>exact Or.inl ⟨i,rfl,hi⟩
 |tail _ hs ih=>
  rcases ih with⟨i',rfl,hi'⟩|⟨t,ht,w,rfl,hw⟩
  ·obtain⟨-,he|he⟩:=hs
   ·exact Or.inr ⟨i',by omega,_,he, .refl⟩
   ·simp only[f5,Sum.elim_inr]at he;split_ifs at he with h2
    ·exact Or.inl ⟨_,he,h2⟩
    ·exact Or.inr ⟨i'+1,by omega,_,he, .refl⟩
  ·obtain⟨hJ,he|he⟩:=hs
   ·exact Or.inr ⟨t,ht,l w,he,hw.tail ⟨hJ,Or.inl rfl⟩⟩
   ·exact Or.inr ⟨t,ht,r w,he,hw.tail ⟨hJ,Or.inr rfl⟩⟩
theorem nO {ν:Type} {J:ν ->Prop} {l r:ν ->ν} {R:List ν} {d:ν} (hR:R≠[]) {u:ν⊕ℕ} (h:aM (eR J R) (gG l R d) (f5 r R d) (dM R d) u):(∃i,u=Sum.inr i/\i+1<R.length)\/∃v∈R,∃w,u=Sum.inl w/\aM J l r v w:=by
 have hpos:0<R.length:=List.length_pos_iff.mpr hR;unfold dM at h;split_ifs at h with h1
 ·rcases pC (by omega) h with h2|⟨t,ht,w,rfl,hw⟩
  ·exact Or.inl h2
  ·exact Or.inr ⟨_,by rw[List.getD_eq_getElem _ _ ht];exact List.getElem_mem ht,w,rfl,hw⟩
 ·obtain⟨w,rfl,hw⟩:=eL h;exact Or.inr ⟨_,by rw[List.getD_eq_getElem _ _ hpos];exact List.getElem_mem hpos,w,rfl,hw⟩
theorem jI {ν α:Type} [DecidableEq α] (f:ν ->Finset α) {R:List ν} (d:ν) (hR:R≠[]) {x:α}:x∈jS f R (dM R d)↔∃v∈R,x∈f v:=by
 have hpos:0<R.length:=List.length_pos_iff.mpr hR;unfold dM;split_ifs with h1
 ·simp[jS,rQ]
 ·obtain⟨v,rfl⟩:∃v,R=[v]:=List.length_eq_one_iff.mp (by omega);simp[jS]
theorem f7 (hC:IsLeastAO G C) (hT:TopForm G C) {j k:ℕ} (hJ:junk G C={j,k}) (hkj:k≠j) (hjk:¬InCone n C j k) {u v:Fin n} (huv:G.Adj u v) (hl:wireVal n (aG n C j) C.output (pairInput u v)=false):∃a∈tops G C,∃b:Fin 2,OrReaches n C (opnd C a b) j/\gateVal n C j (pairInput u v)=true/\((∃w∈orIn n C (opnd C a (1-b)),w=u\/w=v)\/OrReaches n C (opnd C a (1-b)) k/\gateVal n C k (pairInput u v)=true):=by
 have hA:=hC.1;have hjJ:j∈junk G C:=by rw[hJ];simp
 obtain⟨-,hjop,hjb⟩:=aA.mp hjJ;have hF:wireVal n C C.output (pairInput u v)=true:=by
  rw[show wireVal n C C.output _=graphFun G ∅ _ from congrFun hC.2.1 _,aT];exact huv
 obtain⟨w,hw,-⟩|⟨a,hop,hr,hx⟩:=(kU hA _ _).mp hF
 ·rw[jK hC]at hw;simp at hw
 have hal:=(aX hr).2;have ha:a∈tops G C:=aI.mpr ⟨hal,hop,eZ hC hr⟩;have haj:a≠j:=λhe=>hjb (he▸eZ hC hr);have hK:fY C (aG n C j) j:=bJ j;have hpx:∀w:Fin n,pairInput u v w=true ->w=u\/w=v:=λw hw=>by
  simpa[pairInput]using hw
 obtain⟨b,hb⟩:∃b:Fin 2,wireVal n (aG n C j) (opnd C a b) (pairInput u v)=false:=by
  by_contra hne;simp only[not_exists,Bool.not_eq_false]at hne;have:=kS hC hT hK hjop ha haj (hne 0) (hne 1);rw[hl]at this;cases this
 have hab:=(aN hA hal hop b _).mp hx;rcases (a8 hA hT hal hop b _).mp hab.1 with⟨w,hw,hxw⟩|⟨k',hk',-,hrk,hxk⟩
 ·rw[b9 hA hK hjop hw hxw]at hb;cases hb
 rw[hJ,mem_insert,mem_singleton]at hk';rcases hk' with he|he
 swap
 ·rw[he]at hrk hxk;have hkk:wireVal n (aG n C j) (n+k) (pairInput u v)=true:=by
   rw[eB hK _ (n+k) (by omega) (λ_=>by simpa using hjk)];exact hxk
  rw[fB hA hK hjop _ hrk hkk]at hb;cases hb
 rw[he]at hrk hxk;refine⟨a,ha,b,hrk,hxk,?_⟩;rcases (a8 hA hT hal hop (1-b) _).mp hab.2 with⟨w,hw,hxw⟩|⟨k'',hk'',-,hrk',hxk'⟩
 ·exact Or.inl ⟨w,hw,hpx w hxw⟩
 rw[hJ,mem_insert,mem_singleton]at hk'';rcases hk'' with he'|he'
 ·rw[he']at hrk';exfalso;exact hjb λy hy=>(aI.mp ha).2.2 y ((aN hA hal hop b y).mpr ⟨aO hA y hrk hy,aO hA y hrk' hy⟩)
 ·rw[he']at hrk' hxk';exact Or.inr ⟨hrk',hxk'⟩
lemma n0 (hC:IsLeastAO G C) {j a:ℕ} (ha:a∈tops G C) {b:Fin 2} (hr:OrReaches n C (opnd C a b) j) {S T:Finset (Fin n)} (hval:∀x,gateVal n C j x=true↔(∃v∈S,x v=true)/\∃v∈T,x v=true) {p:Fin n} (hp:p∈orIn n C (opnd C a (1-b))) (hpS:p∈S):∀z∈T,G.Adj p z:=by
 intro z hz;have hA:=hC.1;obtain⟨hal,hop,hb⟩:=aI.mp ha;exact(aT p z).mp (hb _ ((aN hA hal hop b _).mpr ⟨aO hA _ hr ((hval _).mpr ⟨⟨p,hpS,by simp[pairInput]⟩,⟨z,hz,by simp[pairInput]⟩⟩),bY hA hp (by simp[pairInput])⟩))
lemma bC (h4:NoFourCycle G) {T:Finset (Fin n)} (hT2:2≤T.card) {p p':Fin n} (hp:∀z∈T,G.Adj p z) (hp':∀z∈T,G.Adj p' z):p=p':=by
 by_contra hne;obtain⟨z,hz,z',hz',hzz⟩:=one_lt_card.mp (by omega:1<T.card);exact hzz (aQ h4 hne (hp z hz) (hp' z hz) (hp z' hz') (hp' z' hz'))
theorem fK (hR1:cM) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (h4:NoFourCycle G) (hC:IsLeastAO G C) {j k:ℕ} (hJ:junk G C={j,k}) (hkj:k≠j) (hjk:¬InCone n C j k) {S T:Finset (Fin n)} {b:Fin 2} (hpure:∀x,wireVal n C (opnd C j b) x=true↔∃t∈T,x t=true) (hval:∀x,gateVal n C j x=true↔(∃v∈S,x v=true)/\∃v∈T,x v=true) {c:Fin n} (hcS:c∈S) (hcT:∀t∈T,G.Adj c t) (hlost:∀u v,G.Adj u v ->wireVal n (aG n C j) C.output (pairInput u v)=false ->(u=c/\v∈T)\/(v=c/\u∈T)):False:=by
 have hA:=hC.1;have hjJ:j∈junk G C:=by rw[hJ];simp
 have hkJ:k∈junk G C:=by rw[hJ];simp
 have hjl:=(aA.mp hjJ).1;have hc:(c:ℕ)<n+j:=by have:=c.2;omega
 have hob:=aH hA hjl b;have hev:∀x,GateOp.and.eval [wireVal n C c x,wireVal n C (opnd C j b) x]=true↔x c=true/\∃t∈T,x t=true:=λx=>by
  simp only[GateOp.eval,List.all_cons,List.all_nil,id,Bool.and_true,Bool.and_eq_true,bA C x c,hpure]
 obtain⟨hD,hsub,hkeep⟩:=cT hC hjl (Or.inl rfl) hc hob (λx h1=>(hval x).mpr ⟨⟨c,hcS,((hev x).mp h1).1⟩,((hev x).mp h1).2⟩) (λu v huv=>by
   cases hk:wireVal n (aG n C j) C.output (pairInput u v)
   ·right;rw[hev];rcases hlost u v huv hk with⟨rfl,hv⟩|⟨rfl,hu⟩
    ·exact⟨by simp[pairInput],v,hv,by simp[pairInput]⟩
    ·exact⟨by simp[pairInput],u,hu,by simp[pairInput]⟩
   ·exact Or.inl rfl)
 have hjD:j∉junk G (aL C j ⟨GateOp.and,[c,opnd C j b]⟩):=λhj'=>by
  refine(aA.mp hj').2.2 λy hy=>?_;have h1:=(b7 hA hjl (Or.inl rfl) hc hob y).2.2.2.2.2;rw[show gateVal n _ j y=wireVal n _ (n+j) y from rfl,h1]at hy;obtain⟨hyc,t,ht,hyt⟩:=(hev y).mp hy;exact(dJ y).mpr ⟨c,t,hcT t ht,hyc,hyt⟩
 have hone:junk G (aL C j ⟨GateOp.and,[c,opnd C j b]⟩)={k}:=by
  ext k';simp only[mem_singleton];refine⟨λhk'=>?_,λhe=>he▸hkeep k hkJ hkj hjk⟩;rcases hsub k' hk' with he|hk''
  ·exact absurd (he▸hk') hjD
  ·rw[hJ,mem_insert,mem_singleton]at hk'';exact hk''.resolve_left λhe=>hjD (he▸hk')
 exact hR1 n G _ col hcol h4 hD (by rw[hone,card_singleton])
lemma nQ (hC:IsLeastAO G C) (hT:TopForm G C) {j k:ℕ} (hJ:junk G C={j,k}) (hkj:k≠j) (hjk:¬InCone n C j k) {S T:Finset (Fin n)} (hval:∀x,gateVal n C j x=true↔(∃v∈S,x v=true)/\∃v∈T,x v=true) (hd:Disjoint S T) (hnc:∀a∈tops G C,∀b:Fin 2,OrReaches n C (opnd C a b) j ->¬OrReaches n C (opnd C a (1-b)) k) {u v:Fin n} (huv:G.Adj u v) (hl:wireVal n (aG n C j) C.output (pairInput u v)=false):∃a∈tops G C,∃b:Fin 2,OrReaches n C (opnd C a b) j/\∃w∈orIn n C (opnd C a (1-b)),∃t,((w=u/\t=v)\/(w=v/\t=u))/\((w∈S/\t∈T)\/(w∈T/\t∈S)):=by
 obtain⟨a,ha,b,hr,hjx,hw|hw⟩:=f7 hC hT hJ hkj hjk huv hl
 swap
 ·exact absurd hw.1 (hnc a ha b hr)
 obtain⟨w,hw,hwuv⟩:=hw;obtain⟨⟨s,hs,hsx⟩,⟨t,ht,htx⟩⟩:=(hval _).mp hjx;have hs':s=u\/s=v:=by simpa[pairInput]using hsx
 have ht':t=u\/t=v:=by simpa[pairInput]using htx
 have hst:s≠t:=λhe=>disjoint_left.mp hd hs (he▸ht);refine⟨a,ha,b,hr,w,hw,?_⟩;rcases hwuv with h1|h1<;>rcases hs' with h2|h2<;>rcases ht' with h3|h3<;>first
  |exact absurd (h2.trans h3.symm) hst
  |exact⟨t,Or.inl ⟨h1,h3⟩,Or.inl ⟨by rw[h1,←h2];exact hs,ht⟩⟩
  |exact⟨s,Or.inl ⟨h1,h2⟩,Or.inr ⟨by rw[h1,←h3];exact ht,hs⟩⟩
  |exact⟨t,Or.inr ⟨h1,h3⟩,Or.inl ⟨by rw[h1,←h2];exact hs,ht⟩⟩
  |exact⟨s,Or.inr ⟨h1,h2⟩,Or.inr ⟨by rw[h1,←h3];exact ht,hs⟩⟩
lemma lY (hR1:cM) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (h4:NoFourCycle G) (hC:IsLeastAO G C) (hT:TopForm G C) {j k:ℕ} (hJ:junk G C={j,k}) (hkj:k≠j) (hjk:¬InCone n C j k) {bS:Fin 2} {S T:Finset (Fin n)} (hpure:∀x,wireVal n C (opnd C j bS) x=true↔∃t∈S,x t=true) (hval:∀x,gateVal n C j x=true↔(∃v∈S,x v=true)/\∃v∈T,x v=true) (hd:Disjoint S T) (hS2:2≤S.card) (hnc:∀a∈tops G C,∀b:Fin 2,OrReaches n C (opnd C a b) j ->¬OrReaches n C (opnd C a (1-b)) k):∃a∈tops G C,∃b:Fin 2,OrReaches n C (opnd C a b) j/\∃p∈orIn n C (opnd C a (1-b)),p∈S:=by
 have hval':∀x,gateVal n C j x=true↔(∃v∈T,x v=true)/\∃v∈S,x v=true:=λx=>(hval x).trans and_comm;have hjl:=(aA.mp (show j∈junk G C by rw[hJ];simp)).1;by_contra hR;have hlost:∀u v,G.Adj u v ->wireVal n (aG n C j) C.output (pairInput u v)=false ->∃a∈tops G C,∃b:Fin 2,OrReaches n C (opnd C a b) j/\∃w∈orIn n C (opnd C a (1-b)),w∈T/\((w=u/\v∈S)\/(w=v/\u∈S)):=by
  intro u v huv hl;obtain⟨a,ha,b,hr,w,hw,t,hwt,⟨hwS,-⟩|⟨hwT,htS⟩⟩:=nQ hC hT hJ hkj hjk hval hd hnc huv hl
  ·exact absurd ⟨a,ha,b,hr,w,hw,hwS⟩ hR
  ·refine⟨a,ha,b,hr,w,hw,hwT,?_⟩;rcases hwt with⟨h1,h2⟩|⟨h1,h2⟩
   ·exact Or.inl ⟨h1,h2▸htS⟩
   ·exact Or.inr ⟨h1,h2▸htS⟩
 by_cases hTu:∃a∈tops G C,∃b:Fin 2,OrReaches n C (opnd C a b) j/\∃z∈orIn n C (opnd C a (1-b)),z∈T
 ·obtain⟨a0,ha0,b0,hr0,z,hz,hzT⟩:=hTu;have hzS:∀t∈S,G.Adj z t:=n0 hC ha0 hr0 hval' hz hzT;refine fK hR1 col hcol h4 hC hJ hkj hjk hpure hval' hzT hzS λu v huv hl=>?_;obtain⟨a,ha,b,hr,w,hw,hwT,hc⟩:=hlost u v huv hl;have hwz:w=z:=bC h4 hS2 (n0 hC ha hr hval' hw hwT) hzS;rcases hc with⟨h1,h2⟩|⟨h1,h2⟩
  ·exact Or.inl ⟨h1.symm.trans hwz,h2⟩
  ·exact Or.inr ⟨h1.symm.trans hwz,h2⟩
 ·exact jJ hC hjl λu v huv=>by
   by_contra hl;obtain⟨a,ha,b,hr,w,hw,hwT,-⟩:=hlost u v huv (by simpa using hl);exact hTu ⟨a,ha,b,hr,w,hw,hwT⟩
theorem nP (hR1:cM) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (h4:NoFourCycle G) (hC:IsLeastAO G C) (hT:TopForm G C) {j k:ℕ} (hJ:junk G C={j,k}) (hkj:k≠j) (hjk:¬InCone n C j k) (hkjc:¬InCone n C k j) (hoff:∀v:Fin n,gateVal n C j (unitInput v)=false) (hA2:2≤(orIn n C (opnd C j 0)).card) (hB2:2≤(orIn n C (opnd C j 1)).card) (hnc:∀a∈tops G C,∀b:Fin 2,OrReaches n C (opnd C a b) j ->¬OrReaches n C (opnd C a (1-b)) k):(∃a∈tops G C,∃b:Fin 2,OrReaches n C (opnd C a b) j/\∃p∈orIn n C (opnd C a (1-b)),p∈orIn n C (opnd C j 0))/\(∃a∈tops G C,∃b:Fin 2,OrReaches n C (opnd C a b) j/\∃z∈orIn n C (opnd C a (1-b)),z∈orIn n C (opnd C j 1)):=by
 have hA:=hC.1;have hjJ:j∈junk G C:=by rw[hJ];simp
 have hno:∀k'∈junk G C,¬InCone n C k' j:=λk' hk' hc=>by
  rw[hJ,mem_insert,mem_singleton]at hk';rcases hk' with he|he
  ·rw[he]at hc;exact lt_irrefl _ (aP hc)
  ·rw[he]at hc;exact hkjc hc
 obtain⟨hval,-,-,hd⟩:=cH hA hT hjJ hno hoff;exact⟨lY hR1 col hcol h4 hC hT hJ hkj hjk (bS:=0) (eI hA hT hjJ hno 0) hval hd hA2 hnc,lY hR1 col hcol h4 hC hT hJ hkj hjk (bS:=1) (eI hA hT hjJ hno 1) (λx=>(hval x).trans and_comm) hd.symm hB2 hnc⟩
omit [DecidableRel G.Adj]in
def bM (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit):Prop:=IsLeastAO G C/\TopForm G C/\NoFourCycle G/\(junk G C).card=2/\(∀j∈junk G C,∀k∈junk G C,¬InCone n C j k)/\(∀j∈junk G C,∀v,gateVal n C j (unitInput v)=false)/\∀j∈junk G C,∀β:Fin 2,2≤(orIn n C (opnd C j β)).card
def jD (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (j:ℕ) (v:Fin n):Prop:=∃a∈tops G C,∃b:Fin 2,OrReaches n C (opnd C a b) j/\v∈orIn n C (opnd C a (1-b))
lemma dC:∀β β':Fin 2,β'=β\/β'=1-β:=by decide
lemma gK:∀a b c:Bool,a≠c ->b≠c ->a=b:=by decide
lemma dD (β:Fin 2):1-(1-β)=β:=sub_sub_cancel 1 β
lemma gC (h2:(junk G C).card=2) {j:ℕ} (hj:j∈junk G C):∃k,k≠j/\junk G C={j,k}:=by
 obtain⟨x,y,hxy,he⟩:=card_eq_two.mp h2;rw[he,mem_insert,mem_singleton]at hj;rcases hj with rfl|rfl
 ·exact⟨y,hxy.symm,he⟩
 ·exact⟨x,hxy,by rw[he,pair_comm]⟩
lemma kK {u v u' v':Fin n} (h:s(u,v)=s(u',v')):pairInput u v=pairInput u' v':=by
 rcases Sym2.eq_iff.mp h with⟨rfl,rfl⟩|⟨rfl,rfl⟩
 ·rfl
 ·funext w;simp[pairInput,or_comm]
lemma cS (X:bM G C) {j:ℕ} (hj:j∈junk G C):(∀β:Fin 2,∀x,gateVal n C j x=true↔(∃a∈orIn n C (opnd C j β),x a=true)/\∃b∈orIn n C (opnd C j (1-β)),x b=true)/\Disjoint (orIn n C (opnd C j 0)) (orIn n C (opnd C j 1))/\∀β:Fin 2,∀x,wireVal n C (opnd C j β) x=true↔∃t∈orIn n C (opnd C j β),x t=true:=by
 have hno:∀k∈junk G C,¬InCone n C k j:=λk hk=>X.2.2.2.2.1 k hk j hj;obtain⟨hv,-,-,hd⟩:=cH X.1.1 X.2.1 hj hno (X.2.2.2.2.2.1 j hj);refine⟨λβ x=>?_,hd,eI X.1.1 X.2.1 hj hno⟩;rcases bG β with⟨rfl,h⟩|⟨rfl,h⟩<;>rw[h]
 ·exact hv x
 ·exact(hv x).trans and_comm
lemma cY (X:bM G C) {j:ℕ} (hj:j∈junk G C) {β:Fin 2} {v:Fin n} (hv:v∈orIn n C (opnd C j β)) (hu:jD n G C j v):∀t∈orIn n C (opnd C j (1-β)),G.Adj v t:=by
 obtain⟨a,ha,b,hr,hva⟩:=hu;exact n0 X.1 ha hr ((cS X hj).1 β) hva hv
lemma sK (X:bM G C) {j:ℕ} (hj:j∈junk G C) {β:Fin 2} {v w:Fin n} (hv:∀t∈orIn n C (opnd C j (1-β)),G.Adj v t) (hw:∀t∈orIn n C (opnd C j (1-β)),G.Adj w t):v=w:=bC X.2.2.1 (X.2.2.2.2.2.2 j hj _) hv hw
def dP (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (L:ℕ ->Fin 2 ->Fin n):Prop:=∀j∈junk G C,∀β:Fin 2,L j β∈orIn n C (opnd C j β)/\jD n G C j (L j β)
lemma e9 (X:bM G C) {L:ℕ ->Fin 2 ->Fin n} (hL:dP G C L) {j:ℕ} (hj:j∈junk G C) (β:Fin 2):∀t∈orIn n C (opnd C j (1-β)),G.Adj (L j β) t:=cY X hj (hL j hj β).1 (hL j hj β).2
lemma eW (X:bM G C) {L:ℕ ->Fin 2 ->Fin n} (hL:dP G C L) {j:ℕ} (hj:j∈junk G C) (β:Fin 2):∀t∈orIn n C (opnd C j β),G.Adj (L j (1-β)) t:=by
 have:=e9 X hL hj (1-β);rwa[dD]at this
lemma m9 (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (X:bM G C) {L:ℕ ->Fin 2 ->Fin n} (hL:dP G C L) {j:ℕ} (hj:j∈junk G C) (β:Fin 2):(∀t∈orIn n C (opnd C j β),col t=col (L j β))/\col (L j (1-β))≠col (L j β):=⟨λt ht=>gK _ _ _ (hcol _ _ (eW X hL hj β t ht)).symm (hcol _ _ (eW X hL hj β _ (hL j hj β).1)).symm,hcol _ _ (eW X hL hj β _ (hL j hj β).1)⟩
lemma nT (X:bM G C) {L:ℕ ->Fin 2 ->Fin n} (hL:dP G C L) {j:ℕ} (hj:j∈junk G C) {u v:Fin n} (huv:G.Adj u v) (hx:gateVal n C j (pairInput u v)=true):∃β:Fin 2,∃w∈orIn n C (opnd C j (1-β)),s(u,v)=s(L j β,w):=by
 obtain⟨⟨s,hs,hsx⟩,⟨t,ht,htx⟩⟩:=((cS X hj).1 0 _).mp hx;have hst:s≠t:=λe=>disjoint_left.mp (cS X hj).2.1 hs (e▸ht);have hs':s=u\/s=v:=by simpa[pairInput]using hsx
 have ht':t=u\/t=v:=by simpa[pairInput]using htx
 have he:s(u,v)=s(s,t)/\G.Adj s t:=by
  rcases hs' with rfl|rfl<;>rcases ht' with rfl|rfl;exacts[absurd rfl hst,⟨rfl,huv⟩,⟨Sym2.eq_swap,huv.symm⟩,absurd rfl hst]
 by_cases h0:s=L j 0
 ·exact⟨0,t,ht,h0▸he.1⟩
 by_cases h1:t=L j 1
 ·exact⟨1,s,hs,he.1.trans (h1▸Sym2.eq_swap)⟩
 exact absurd (aQ X.2.2.1 h0 he.2 (e9 X hL hj 0 t ht) (by simpa using(eW X hL hj 0 s hs).symm) (e9 X hL hj 0 _ (hL j hj 1).1)) h1
lemma pK (X:bM G C) {L:ℕ ->Fin 2 ->Fin n} (hL:dP G C L) {e:Sym2 (Fin n)} (he:e∈Ustar G C):∃j∈junk G C,∃β:Fin 2,∃w∈orIn n C (opnd C j (1-β)),e=s(L j β,w):=by
 induction e using Sym2.ind with
 |_ u v=>
 obtain⟨-,-,-,-,k,hk,-,-,hkx⟩:=fD X.1 X.2.1 he;have huv:G.Adj u v:=SimpleGraph.mem_edgeFinset.mp (mem_sdiff.mp he).1;exact⟨k,hk,nT X hL hk huv hkx⟩
lemma jV (X:bM G C) {j k:ℕ} (hj:j∈junk G C) {w:ℕ} {x:Fin n ->Bool} (h:(∃v∈orIn n C w,x v=true)\/(k∈junk G C/\k≠j/\OrReaches n C w k/\gateVal n C k x=true)):wireVal n (aG n C j) w x=true:=by
 have hop:=(aA.mp hj).2.1;rcases h with⟨v,hv,hx⟩|⟨hk,hkj,hr,hkx⟩
 ·exact b9 X.1.1 (bJ j) hop hv hx
 ·refine fB X.1.1 (bJ j) hop x hr ?_;rw[eB (bJ j) x (n+k) (by omega) (λ_=>by simpa using X.2.2.2.2.1 j hj k hk)];exact hkx
lemma lS (X:bM G C) {j:ℕ} (hj:j∈junk G C) {a:ℕ} (ha:a∈tops G C) {x:Fin n ->Bool} (h:∀b:Fin 2,wireVal n (aG n C j) (opnd C a b) x=true):wireVal n (aG n C j) C.output x=true:=kS X.1 X.2.1 (bJ j) (aA.mp hj).2.1 ha (λe=>(aA.mp hj).2.2 (e▸(aI.mp ha).2.2)) (h 0) (h 1)
lemma sV (X:bM G C) {j:ℕ} (hj:j∈junk G C) {a:ℕ} (ha:a∈tops G C) {x:Fin n ->Bool} (h:∀b:Fin 2,∃v∈orIn n C (opnd C a b),x v=true):wireVal n (aG n C j) C.output x=true:=lS X hj ha λb=>jV X hj (k:=j) (Or.inl (h b))
lemma qU (X:bM G C) {j:ℕ} (hj:j∈junk G C) {u v:Fin n} (hs:s(u,v)∈starEdges G C):wireVal n (aG n C j) C.output (pairInput u v)=true:=by
 simp only[starEdges,mem_biUnion,mem_image,mem_product]at hs;obtain⟨a,ha,⟨u',v'⟩,⟨hu,hv⟩,e⟩:=hs;rw[←kK e];exact sV X hj ha λb=>by
  fin_cases b
  ·exact⟨u',hu,by simp[pairInput]⟩
  ·exact⟨v',hv,by simp[pairInput]⟩
lemma uV (X:bM G C) {L:ℕ ->Fin 2 ->Fin n} (hL:dP G C L) {j k:ℕ} (hj:j∈junk G C) (hk:k∈junk G C) (hkj:k≠j) {u v:Fin n} (huv:G.Adj u v) (hx:gateVal n C k (pairInput u v)=true):wireVal n (aG n C j) C.output (pairInput u v)=true:=by
 obtain⟨γ,w,-,e⟩:=nT X hL hk huv hx;obtain⟨a,ha,b,hr,hv⟩:=(hL k hk γ).2;have hin:pairInput u v (L k γ)=true:=by
  rcases Sym2.eq_iff.mp e with⟨h1,-⟩|⟨-,h1⟩<;>simp[pairInput,h1]
 refine lS X hj ha λb'=>?_;rcases dC b b' with rfl|rfl
 ·exact jV X hj (Or.inr ⟨hk,hkj,hr,hx⟩)
 ·exact jV X hj (k:=k) (Or.inl ⟨_,hv,hin⟩)
theorem sU (hR1:cM) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (X:bM G C) {L:ℕ ->Fin 2 ->Fin n} (hL:dP G C L) {j:ℕ} (hj:j∈junk G C) {β:Fin 2} {t:Fin n} (hT:orIn n C (opnd C j (1-β))={L j (1-β),t}):wireVal n (aG n C j) C.output (pairInput (L j β) t)=false:=by
 obtain⟨k,hkj,hJ⟩:=gC X.2.2.2.1 hj;have hk:k∈junk G C:=by rw[hJ];simp
 have hjk:=X.2.2.2.2.1 j hj k hk;by_contra hacc;have hv:=(cS X hj).1 (1-β);rw[dD]at hv;refine fK hR1 col hcol X.2.2.1 X.1 hJ hkj hjk ((cS X hj).2.2 β) hv (hL j hj (1-β)).1 (eW X hL hj β) λu v huv hl=>?_;obtain⟨a,ha,b,hr,hjx,-⟩:=f7 X.1 X.2.1 hJ hkj hjk huv hl;obtain⟨γ,w,hw,e⟩:=nT X hL hj huv hjx;rcases dC β γ with rfl|rfl
 ·rw[hT,mem_insert,mem_singleton]at hw;rcases hw with rfl|rfl
  ·rcases Sym2.eq_iff.mp e with⟨rfl,rfl⟩|⟨rfl,rfl⟩
   ·exact Or.inr ⟨rfl,(hL j hj _).1⟩
   ·exact Or.inl ⟨rfl,(hL j hj _).1⟩
  ·exact absurd (by rw[kK e]at hl;exact hl) hacc
 ·rw[dD]at hw;rcases Sym2.eq_iff.mp e with⟨rfl,rfl⟩|⟨rfl,rfl⟩
  ·exact Or.inl ⟨rfl,hw⟩
  ·exact Or.inr ⟨rfl,hw⟩
lemma pZ (hR1:cM) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (X:bM G C) {L:ℕ ->Fin 2 ->Fin n} (hL:dP G C L) {j:ℕ} (hj:j∈junk G C) {β:Fin 2} {t:Fin n} (hT:orIn n C (opnd C j (1-β))={L j (1-β),t}):s(L j β,t)∉starEdges G C/\∀k∈junk G C,k≠j ->gateVal n C k (pairInput (L j β) t)=false:=by
 have hp:=sU hR1 col hcol X hL hj hT;refine⟨λhs=>(by rw[qU X hj hs]at hp;cases hp),λk hk hkj=>?_⟩;by_contra hx;have hadj:G.Adj (L j β) t:=e9 X hL hj β t (by rw[hT];simp);rw[uV X hL hj hk hkj hadj (by simpa using hx)]at hp;cases hp
lemma eH (hA:IsAO2 n C) {a J:ℕ} (ha:a∈tops G C) {b:Fin 2} (hr:OrReaches n C (opnd C a b) J) {w:Fin n} (hw:w∈orIn n C (opnd C a (1-b))):∀χ,gateVal n C J χ=true ->χ w=true ->graphFun G ∅ χ=true:=λχ h1 h2=>by
 obtain⟨hal,hop,hb⟩:=aI.mp ha;exact hb χ ((aN hA hal hop b χ).mpr ⟨aO hA χ hr h1,bY hA hw h2⟩)
lemma sT (X:bM G C) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) {L:ℕ ->Fin 2 ->Fin n} (hL:dP G C L) {J:ℕ} (hJ:J∈junk G C) {β:Fin 2} {y:Fin n} (hy:∀χ,gateVal n C J χ=true ->χ y=true ->graphFun G ∅ χ=true) (hc:col y=col (L J β)) (hne:y≠L J β):∃t,t≠L J (1-β)/\orIn n C (opnd C J (1-β))={L J (1-β),t}/\G.Adj y t:=by
 have h4:=X.2.2.1;have hx':=(hL J hJ (1-β)).1;have h2:∀γ,1<(orIn n C (opnd C J γ)).card:=λγ=>X.2.2.2.2.2.2 J hJ γ;obtain⟨s,hs,hsx⟩:=exists_mem_ne (h2 β) (L J β);have key:∀t∈orIn n C (opnd C J (1-β)),t≠L J (1-β) ->G.Adj y t:=by
  intro t ht htx;have hst:¬G.Adj s t:=λh=>htx (aQ h4 hsx.symm (e9 X hL hJ β t ht) h (e9 X hL hJ β _ hx') (eW X hL hJ β s hs).symm);have hsy:¬G.Adj s y:=λh=>hcol s y h (((m9 col hcol X hL hJ β).1 s hs).trans hc.symm);obtain⟨u,v,huv,hu,hv⟩:=(dJ _).mp (hy (λw=>decide (w=s\/w=t\/w=y)) (((cS X hJ).1 β _).mpr ⟨⟨s,hs,by simp⟩,t,ht,by simp⟩) (by simp));simp only[decide_eq_true_eq]at hu hv;rcases hu with rfl|rfl|rfl<;>rcases hv with rfl|rfl|rfl<;>
  first
  |exact(G.irrefl huv).elim
  |exact absurd huv hst
  |exact absurd huv.symm hst
  |exact absurd huv hsy
  |exact absurd huv.symm hsy
  |exact huv
  |exact huv.symm
 obtain⟨t0,ht0,ht0x⟩:=exists_mem_ne (h2 (1-β)) (L J (1-β));refine⟨t0,ht0x,?_,key t0 ht0 ht0x⟩;ext t;simp only[mem_insert,mem_singleton];exact⟨λht=>or_iff_not_imp_left.mpr λhtx=>aQ h4 (Ne.symm hne) (e9 X hL hJ β t ht) (key t ht htx) (e9 X hL hJ β t0 ht0) (key t0 ht0 ht0x),λh=>h.elim (·▸hx') (·▸ht0)⟩
lemma vA (hR1:cM) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (X:bM G C) {L:ℕ ->Fin 2 ->Fin n} (hL:dP G C L) {J:ℕ} (hJ:J∈junk G C) {β:Fin 2} {a:ℕ} (ha:a∈tops G C) {b:Fin 2} (hr:OrReaches n C (opnd C a b) J) (hv:L J β∈orIn n C (opnd C a (1-b))) (hne:(orIn n C (opnd C a b)).Nonempty):orIn n C (opnd C a (1-b))={L J β}:=by
 refine eq_singleton_iff_unique_mem.mpr ⟨hv,λw hw=>by_contra λhwv=>?_⟩;obtain⟨y0,hy0⟩:=hne;have h1:=aV X.1.1 ha b hv hy0;have h2:=(aV X.1.1 ha b hw hy0).1;obtain⟨t0,-,hT,hwt⟩:=sT X col hcol hL hJ (eH X.1.1 ha hr hw) (gK _ _ _ (hcol _ _ h2) (hcol _ _ h1.1)) hwv;have e:=aQ X.2.2.1 (Ne.symm hwv) h1.1 h2 (e9 X hL hJ β t0 (by rw[hT];simp)) hwt;exact(pZ hR1 col hcol X hL hJ hT).1 (e▸h1.2)
lemma q3 (hR1:cM) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (X:bM G C) {L:ℕ ->Fin 2 ->Fin n} (hL:dP G C L) {i:ℕ} (hi:i∈junk G C) {δ:Fin 2} {W:Finset (Fin n)} (hW:∀y∈W,∀χ,gateVal n C i χ=true ->χ y=true ->graphFun G ∅ χ=true) (hx:L i δ∈W) {y:Fin n} (hy:y∈W) (hc:col y=col (L i δ)) (hne:y≠L i δ):¬aB G (Ustar G C) W/\¬∃J∈junk G C,∃β:Fin 2,W⊆orIn n C (opnd C J β):=by
 obtain⟨t0,ht0,hT,hyt⟩:=sT X col hcol hL hi (hW y hy) hc hne;have hxt:=e9 X hL hi δ t0 (by rw[hT];simp);have hpr:=pZ hR1 col hcol X hL hi hT;have huq:∀z,G.Adj z (L i δ) ->G.Adj z y ->z=t0:=λz h1 h2=>aQ X.2.2.1 (Ne.symm hne) h1.symm h2.symm hxt hyt;refine⟨λ⟨z,hz⟩=>?_,λ⟨J,hJ,β,hWs⟩=>?_⟩
 ·obtain rfl:=huq z (hz _ hx).1 (hz _ hy).1;exact(hz _ hx).2 (mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr (hz _ hx).1,λhs=>hpr.1 (by rwa[Sym2.eq_swap]at hs)⟩)
 have he:=huq _ (eW X hL hJ β _ (hWs hx)) (eW X hL hJ β _ (hWs hy));by_cases hJi:J=i
 ·subst hJi;rcases dC δ β with rfl|rfl
  ·exact ht0 he.symm
  ·rw[dD]at he;exact hxt.ne he
 ·have:=hpr.2 J hJ hJi;rw[((cS X hJ).1 β _).mpr ⟨⟨_,hWs hx,by simp[pairInput]⟩,t0,he▸(hL J hJ (1-β)).1,by simp[pairInput]⟩]at this;cases this
lemma u9 (hR1:cM) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (X:bM G C) {L:ℕ ->Fin 2 ->Fin n} (hL:dP G C L) {i:ℕ} (hi:i∈junk G C) {W:Finset (Fin n)} (hW:∀y∈W,∀χ,gateVal n C i χ=true ->χ y=true ->graphFun G ∅ χ=true) {J₁ J₂:ℕ} (hJ₁:J₁∈junk G C) (hJ₂:J₂∈junk G C) {β₁ β₂:Fin 2} (h₁:L J₁ β₁∈W) (h₂:L J₂ β₂∈W) (hne:L J₁ β₁≠L J₂ β₂):¬aB G (Ustar G C) W/\¬∃J∈junk G C,∃β:Fin 2,W⊆orIn n C (opnd C J β):=by
 by_cases hc:col (L J₁ β₁)=col (L J₂ β₂)
 ·by_cases e₁:J₁=i
  ·subst e₁;exact q3 hR1 col hcol X hL hJ₁ hW h₁ h₂ hc.symm (Ne.symm hne)
  by_cases e₂:J₂=i
  ·subst e₂;exact q3 hR1 col hcol X hL hJ₂ hW h₂ h₁ hc hne
  obtain⟨k,-,hk⟩:=gC X.2.2.2.1 hi;have f:∀J∈junk G C,J≠i ->J=k:=λJ hJ hJi=>by
   rw[hk,mem_insert,mem_singleton]at hJ;exact hJ.resolve_left hJi
  obtain rfl:=(f _ hJ₁ e₁).trans (f _ hJ₂ e₂).symm;rcases dC β₁ β₂ with rfl|rfl
  ·exact absurd rfl hne
  ·exact absurd hc.symm (m9 col hcol X hL hJ₁ β₁).2
 ·refine⟨λhf=>?_,λ⟨J,hJ,β,hs⟩=>?_⟩
  ·obtain⟨c,h⟩:=aU col hcol hf;exact hc ((h _ h₁).trans (h _ h₂).symm)
  ·have h:=(m9 col hcol X hL hJ β).1;exact hc ((h _ (hs h₁)).trans (h _ (hs h₂)).symm)
lemma g4 (hA:IsAO2 n C) {h:ℕ} (hJ:bX n C h) (hne:(orIn n C h).Nonempty) (hf:¬aB G (Ustar G C) (orIn n C h)):h∈(orN G C\lam G C).image (n+·):=by
 obtain⟨k,rfl⟩:∃k,h=n+k:=⟨h-n,by have:=hJ.1;omega⟩;obtain⟨hk,hop⟩:=a7.mp hJ;obtain⟨v,hv⟩:=hne;refine mem_image.mpr ⟨k,mem_sdiff.mpr ⟨dS.mpr ⟨hk,hop,λhb=>?_⟩,λhl=>hf (k5 hA hl)⟩,rfl⟩;have:=hb _ (bY hA hv (x:=unitInput v) (by simp[unitInput]));rw[e8]at this;cases this
lemma sP (X:bM G C) {L:ℕ ->Fin 2 ->Fin n} (hL:dP G C L) {J:ℕ} (hJ:J∈junk G C) {V:Finset (Sym2 (Fin n))} (hVU:V⊆Ustar G C) (hVE:∀e∈V,∃β:Fin 2,∃w∈orIn n C (opnd C J (1-β)),e=s(L J β,w)):∃P:Finset ℕ,(∀h∈P,h∈(orN G C\lam G C).image (n+·)/\¬aB G V (orIn n C h)/\∃β,aM (bX n C) (bF n C) (bI n C) (opnd C J β) h)/\V.card≤P.card+1:=by
 have hA:=X.1.1;have ch:∀β β':Fin 2,β'=1-β ->∃P:Finset ℕ,(∀h∈P,bX n C h/\aM (bX n C) (bF n C) (bI n C) (opnd C J β') h/\¬aB G V (orIn n C h)/\1<(orIn n C h∩(orIn n C (opnd C J β')∩insert (L J β') (aE V (L J β)))).card)/\(orIn n C (opnd C J β')∩insert (L J β') (aE V (L J β))).card≤P.card+1:=by
  rintro β _ rfl;exact d8 (aJ hA) _ _ _ inter_subset_left (λW hW=>(card_le_card (inter_subset_inter_left inter_subset_right)).trans (a4 X.2.2.1 (hVU.trans sdiff_subset) hW _ _ (e9 X hL hJ β _ (hL J hJ (1-β)).1))) λu _ hu=>Or.inr (bL hu)
 obtain⟨P0,hP0,c0⟩:=ch 0 1 rfl;obtain⟨P1,hP1,c1⟩:=ch 1 0 rfl;set S0:=orIn n C (opnd C J 1)∩insert (L J 1) (aE V (L J 0));set S1:=orIn n C (opnd C J 0)∩insert (L J 0) (aE V (L J 1))
 have hP:∀h∈P0∪P1,bX n C h/\¬aB G V (orIn n C h)/\(orIn n C h).Nonempty/\∃β,aM (bX n C) (bF n C) (bI n C) (opnd C J β) h:=λh hh=>(mem_union.mp hh).elim (λhh=>let ⟨a,b,c,d⟩:=hP0 h hh
    ⟨a,c,(card_pos.mp (zero_lt_one.trans d)).mono inter_subset_left,1,b⟩)
   (λhh=>let ⟨a,b,c,d⟩:=hP1 h hh
    ⟨a,c,(card_pos.mp (zero_lt_one.trans d)).mono inter_subset_left,0,b⟩)
 have hdis:Disjoint P0 P1:=disjoint_left.mpr λh h0 h1=>by
  obtain⟨v,hv⟩:=(hP h (mem_union_left _ h0)).2.2.1;exact disjoint_left.mp (cS X hJ).2.1 (aK (aJ hA) (hP1 h h1).2.1 hv) (aK (aJ hA) (hP0 h h0).2.1 hv)
 have hcov:V⊆S0.image (s(L J 0,·))∪(S1.erase (L J 0)).image (s(L J 1,·)):=by
  intro e he;obtain⟨β,w,hw,rfl⟩:=hVE e he;rcases bG β with⟨rfl,h⟩|⟨rfl,h⟩<;>rw[h]at hw
  ·exact mem_union_left _ (mem_image_of_mem _ (mem_inter.mpr ⟨hw,mem_insert_of_mem (aD.mpr he)⟩))
  ·by_cases hw0:w=L J 0
   ·subst hw0;exact mem_union_left _ (mem_image.mpr ⟨L J 1,mem_inter.mpr ⟨(hL J hJ 1).1,mem_insert_self _ _⟩,Sym2.eq_swap⟩)
   ·exact mem_union_right _ (mem_image_of_mem _ (mem_erase.mpr ⟨hw0,mem_inter.mpr ⟨hw,mem_insert_of_mem (aD.mpr he)⟩⟩))
 have hm:L J 0∈S1:=mem_inter.mpr ⟨(hL J hJ 0).1,mem_insert_self _ _⟩;have:=(card_le_card hcov).trans ((card_union_le _ _).trans (add_le_add card_image_le card_image_le));rw[card_erase_of_mem hm]at this;have:=card_pos.mpr ⟨_,hm⟩;refine⟨P0∪P1,λh hh=>?_,by rw[card_union_of_disjoint hdis];omega⟩;obtain⟨a,b,c,d⟩:=hP h hh;exact⟨g4 hA a c λhu=>b (bT hVU subset_rfl hu),b,d⟩
lemma tA (X:bM G C) {L:ℕ ->Fin 2 ->Fin n} (hL:dP G C L):∃P:Finset ℕ,(∀h∈P,h∈(orN G C\lam G C).image (n+·)/\∃J∈junk G C,∃β,aM (bX n C) (bF n C) (bI n C) (opnd C J β) h)/\(Ustar G C).card≤P.card+2:=by
 classical
 obtain⟨j,hj⟩:(junk G C).Nonempty:=card_pos.mp (by rw[X.2.2.2.1];omega);obtain⟨k,-,hJ⟩:=gC X.2.2.2.1 hj;have hk:k∈junk G C:=by rw[hJ];simp
 let E:Sym2 (Fin n) ->Prop:=λe=>
  ∃β:Fin 2,∃w∈orIn n C (opnd C j (1-β)),e=s(L j β,w)
 obtain⟨P1,hP1,c1⟩:=sP X hL hj (V:=(Ustar G C).filter E) (filter_subset _ _) λe he=>(mem_filter.mp he).2;obtain⟨P2,hP2,c2⟩:=sP X hL hk (V:=(Ustar G C).filter λe=>¬E e) (filter_subset _ _) λe he=>by
   obtain⟨hU,hn⟩:=mem_filter.mp he;obtain⟨J,hJ',β,w,hw,rfl⟩:=pK X hL hU;rw[hJ,mem_insert,mem_singleton]at hJ';rcases hJ' with rfl|rfl
   ·exact absurd ⟨β,w,hw,rfl⟩ hn
   ·exact⟨β,w,hw,rfl⟩
 have hdis:Disjoint P1 P2:=disjoint_left.mpr λh h1 h2=>by
  obtain⟨-,-,β,hr⟩:=hP1 h h1;refine(hP2 h h2).2.1 ⟨L j (1-β),λw hw=>?_⟩;have hw':=aK (aJ X.1.1) hr hw;exact⟨eW X hL hj β w hw',λhm=>(mem_filter.mp hm).2 ⟨1-β,w,by rwa[dD],rfl⟩⟩
 refine⟨P1∪P2,λh hh=>(mem_union.mp hh).elim (λh1=>⟨(hP1 h h1).1,j,hj,(hP1 h h1).2.2⟩) (λh1=>⟨(hP2 h h1).1,k,hk,(hP2 h h1).2.2⟩),?_⟩;rw[card_union_of_disjoint hdis,←card_filter_add_card_filter_not (s:=Ustar G C) E];omega
theorem uE (hA:IsAO2 n C) (h4:NoFourCycle G) (Q:ℕ ->Fin 2 ->Fin n ->Prop):∃K:Finset (Fin n),K.card≤(tops G C\centreless G C).card/\(∀e∈starEdges G C,∃v∈K,v∈e)/\∀a∈tops G C\centreless G C,∃b:Fin 2,∃p∈K,side C a (1-b)={p}/\((∃b':Fin 2,∃p',side C a (1-b')={p'}/\Q a b' p') ->Q a b p):=by
 classical
 have hsel:∀a:{a//a∈tops G C\centreless G C},∃b:Fin 2,∃p:Fin n,side C a.1 (1-b)={p}/\((∃b':Fin 2,∃p',side C a.1 (1-b')={p'}/\Q a.1 b' p') ->Q a.1 b p):=by
  intro a;by_cases hp:∃b':Fin 2,∃p',side C a.1 (1-b')={p'}/\Q a.1 b' p'
  ·obtain⟨b',p',h1,h2⟩:=hp;exact⟨b',p',h1,λ_=>h2⟩
  ·obtain⟨b,c,hc⟩:=(fU hA h4 a.2).2.2.2;exact⟨b,c,hc,λh=>absurd h hp⟩
 choose bs cen hcen using hsel;refine⟨univ.image cen,card_image_le.trans (by simp),λe he=>?_,λa ha=>⟨bs ⟨a,ha⟩,cen ⟨a,ha⟩,mem_image_of_mem _ (mem_univ _),hcen ⟨a,ha⟩⟩⟩;simp only[starEdges,mem_biUnion,mem_image,mem_product]at he;obtain⟨a,ha,⟨u,v⟩,⟨hu,hv⟩,rfl⟩:=he;have hc:=(hcen ⟨a,bW ha hu hv⟩).1;refine⟨_,mem_image_of_mem _ (mem_univ ⟨a,bW ha hu hv⟩),?_⟩
 generalize bs ⟨a,bW ha hu hv⟩=b at hc
 fin_cases b
 ·have hc':side C a 1={cen ⟨a,bW ha hu hv⟩}:=hc;simp[←mem_singleton.mp (hc'▸hv)]
 ·have hc':side C a 0={cen ⟨a,bW ha hu hv⟩}:=hc;simp[←mem_singleton.mp (hc'▸hu)]
def jT (n:ℕ) (C:Circuit) (a:ℕ):ℕ:=if orIn n C (opnd C a 0)=∅ then opnd C a 1 else opnd C a 0
lemma mF {a:ℕ} (ha:a∈tops G C) {b:Fin 2} (he:orIn n C (opnd C a b)=∅):a∈centreless G C:=mem_filter.mpr ⟨ha,by rcases bG b with⟨rfl,-⟩|⟨rfl,-⟩;exacts[Or.inl he,Or.inr he]⟩
lemma q4 {a:ℕ} (ha:a∈tops G C) {b:Fin 2} (h1:(orIn n C (opnd C a b)).Nonempty) (h2:(orIn n C (opnd C a (1-b))).Nonempty):a∈tops G C\centreless G C:=by
 obtain⟨u,hu⟩:=h1;obtain⟨v,hv⟩:=h2;rcases bG b with⟨rfl,h⟩|⟨rfl,h⟩<;>rw[h]at hv;exacts[bW ha hu hv,bW ha hv hu]
lemma sY {a:ℕ} (ha:a∈centreless G C):∃b:Fin 2,jT n C a=opnd C a (1-b)/\orIn n C (opnd C a b)=∅:=by
 have h2:=(mem_filter.mp ha).2;unfold jT;split_ifs with h
 ·exact⟨0,rfl,h⟩
 ·exact⟨1,rfl,h2.resolve_left h⟩
lemma tV {a:ℕ} (ha:a∈tops G C) {b:Fin 2} (he:orIn n C (opnd C a b)=∅) {v:Fin n} (hv:v∈orIn n C (opnd C a (1-b))):v∈((centreless G C).image (jT n C)).biUnion (orIn n C):=by
 obtain⟨b',hb',he'⟩:=sY (mF ha he);refine mem_biUnion.mpr ⟨_,mem_image_of_mem _ (mF ha he),?_⟩;rw[hb'];rcases dC b b' with rfl|rfl
 ·exact hv
 ·rw[he']at hv;simp at hv
lemma uQ (hA:IsAO2 n C) (hT:TopForm G C) {a:ℕ} (ha:a∈tops G C) {b:Fin 2} (he:orIn n C (opnd C a b)=∅):∃i∈junk G C,OrReaches n C (opnd C a b) i:=by
 obtain⟨hal,hop,-⟩:=aI.mp ha;rcases (a8 hA hT hal hop b _).mp ((aN hA hal hop b _).mp (dW hA (n+a) (by omega))).1 with⟨v,hv,-⟩|⟨i,hi,-,hr,-⟩
 ·rw[he]at hv;simp at hv
 ·exact⟨i,hi,hr⟩
def mD (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (h:ℕ):Prop:=bX n C h/\(∃J∈junk G C,OrReaches n C h J)/\(orIn n C (bF n C h)=∅\/orIn n C (bI n C h)=∅)
lemma u3 (hA:IsAO2 n C) {w J:ℕ} (hJ:J∈junk G C) (hr:OrReaches n C w J) (hne:(orIn n C w).Nonempty):∃h,mD n G C h/\orIn n C h⊆orIn n C w/\(orIn n C h).Nonempty:=by
 obtain⟨m,b,hm,hop,hwm,hne',he,hrJ⟩:=fE hA (aA.mp hJ).2.1 hr hne;refine⟨n+m,⟨a7.mpr ⟨hm,hop⟩,⟨J,hJ,d9 hA hm hop b hrJ⟩,?_⟩,a6 hA hwm,hne'⟩;simp only[bF,bI,Nat.add_sub_cancel_left];rcases bG b with⟨rfl,-⟩|⟨rfl,-⟩;exacts[Or.inl he,Or.inr he]
lemma q0 (hA:IsAO2 n C) {h:ℕ} (hM:mD n G C h):h∈(orN G C\lam G C).image (n+·):=by
 obtain⟨hJ,⟨J,hJJ,hr⟩,he⟩:=hM;obtain⟨k,rfl⟩:∃k,h=n+k:=⟨h-n,by have:=hJ.1;omega⟩;obtain⟨hk,hop⟩:=a7.mp hJ;simp only[bF,bI,Nat.add_sub_cancel_left]at he;exact mem_image.mpr ⟨k,he.elim (f0 hA hk hop hJJ hr) (f0 hA hk hop hJJ hr),rfl⟩
theorem eT (hR1:cM) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (X:bM G C) {L:ℕ ->Fin 2 ->Fin n} (hL:dP G C L):False:=by
 classical
 have hA:=X.1.1;set Xs:=((junk G C)×ˢ (univ:Finset (Fin 2))).image λq=>L q.1 q.2;have hXs:∀v,v∈Xs↔∃J∈junk G C,∃β,L J β=v:=λv=>by simp[Xs]
 obtain⟨P,hP,hu⟩:=tA X hL;obtain⟨K,hKc,hKs,hKa⟩:=uE hA X.2.2.1 λa b p=>∃J∈junk G C,∃γ,L J γ=p/\OrReaches n C (opnd C a b) J;have hM:=e4 X.2.2.1 X.1 X.2.1 X.2.2.2.1 K Xs hKs λe he=>by
  obtain⟨J,hJ,β,w,-,rfl⟩:=pK X hL he;exact⟨L J β,(hXs _).mpr ⟨J,hJ,β,rfl⟩,Sym2.mem_mk_left _ _⟩
 set R:=(centreless G C).image (jT n C);obtain⟨Pf,hPf,hcf⟩:=cU (aJ hA) Xs R λ_ _ u _ hu=>(card_le_card inter_subset_left).trans (bL hu);have hPf':∀h∈Pf,h∈(orN G C\lam G C).image (n+·)/\(¬∃J∈junk G C,∃β:Fin 2,orIn n C h⊆orIn n C (opnd C J β))/\(orIn n C (bF n C h)).Nonempty/\(orIn n C (bI n C h)).Nonempty:=by
  intro h hh;obtain⟨hJh,⟨w,hw,hrw⟩,h1,h2⟩:=hPf h hh;obtain⟨x1,hx1,hx1'⟩:=not_subset.mp h1;obtain⟨x2,hx2,hx2'⟩:=not_subset.mp h2;obtain⟨a,ha,rfl⟩:=mem_image.mp hw;obtain⟨b,hb,he⟩:=sY ha;have hat:=(mem_filter.mp ha).1;obtain⟨i,hi,hri⟩:=uQ hA X.2.1 hat he;have hf:=(aJ hA h hJh).2.2;have hsub:=aK (aJ hA) hrw;rw[hb]at hsub;obtain⟨J₁,hJ₁,β₁,rfl⟩:=(hXs _).mp (mem_inter.mp hx1).2;obtain⟨J₂,hJ₂,β₂,rfl⟩:=(hXs _).mp (mem_inter.mp hx2).2;have hm:=u9 hR1 col hcol X hL hi (W:=orIn n C h) (λy hy=>eH hA hat hri (hsub hy)) hJ₁ hJ₂ (hf▸mem_union_left _ (mem_inter.mp hx1).1) (hf▸mem_union_right _ (mem_inter.mp hx2).1) λe=>hx2' (e▸(mem_inter.mp hx1).1);exact⟨g4 hA hJh ⟨_,hf▸mem_union_left _ (mem_inter.mp hx1).1⟩ hm.1,hm.2,⟨_,(mem_inter.mp hx1).1⟩,⟨_,(mem_inter.mp hx2).1⟩⟩
 set Mix:=(range (n+C.gates.length)).filter (mD n G C);have hr:P.card+Pf.card+Mix.card≤(orN G C\lam G C).card:=by
  have d1:Disjoint P Pf:=disjoint_left.mpr λh h1 h2=>by
   obtain⟨-,J,hJ,β,hr⟩:=hP h h1;exact(hPf' h h2).2.1 ⟨J,hJ,β,aK (aJ hA) hr⟩
  have d2:Disjoint (P∪Pf) Mix:=disjoint_left.mpr λh h1 h2=>by
   obtain⟨hJh,⟨J',hJ',hr'⟩,he⟩:=(mem_filter.mp h2).2;rcases mem_union.mp h1 with h1|h1
   ·obtain⟨-,J,hJ,β,hr⟩:=hP h h1;obtain⟨g,rfl⟩:∃g,h=n+g:=⟨h-n,by have:=hJh.1;omega⟩;exact X.2.2.2.2.1 J' hJ' J hJ (bU hA (aA.mp hJ).1 β (cG hA ((cK hA).mpr ⟨(a7.mp hJh).1,hr⟩) hr'))
   ·obtain⟨-,-,⟨v,hv⟩,⟨w,hw⟩⟩:=hPf' h h1;rcases he with he|he
    ·rw[he]at hv;simp at hv
    ·rw[he]at hw;simp at hw
  have:=card_le_card (show P∪Pf∪Mix⊆(orN G C\lam G C).image (n+·)from λh hh=>by
    rcases mem_union.mp hh with hh|hh
    ·rcases mem_union.mp hh with hh|hh;exacts[(hP h hh).1,(hPf' h hh).1]
    ·exact q0 hA (mem_filter.mp hh).2)
  rwa[card_union_of_disjoint d2,card_union_of_disjoint d1,card_image_of_injective _ (add_right_injective n)]at this
 set D:=(Xs\K)\R.biUnion (orIn n C)with hDd;have hx:(Xs\K).card≤D.card+(R.biUnion (orIn n C)∩Xs).card:=by
  have:=card_sdiff_add_card_inter (Xs\K) (R.biUnion (orIn n C));rw[←hDd]at this;have:=card_le_card (show(Xs\K)∩R.biUnion (orIn n C)⊆R.biUnion (orIn n C)∩Xs from λv hv=>mem_inter.mpr ⟨(mem_inter.mp hv).2,(mem_sdiff.mp (mem_inter.mp hv).1).1⟩);omega
 have hRc:R.card≤(centreless G C).card:=card_image_le;have key:(centreless G C).card+Mix.card≤D.card:=by omega
 have hmix:∀{w J:ℕ},J∈junk G C ->OrReaches n C w J ->(orIn n C w).Nonempty ->∃h∈Mix,orIn n C h⊆orIn n C w/\(orIn n C h).Nonempty:=λhJ hr hne=>by
  obtain⟨h,hM,h1,h2⟩:=u3 hA hJ hr hne;exact⟨h,mem_filter.mpr ⟨mem_range.mpr (by have:=hM.1.1;have:=hM.1.2.1;omega),hM⟩,h1,h2⟩
 rcases D.eq_empty_or_nonempty with hD|⟨v0,hv0⟩
 ·rw[hD,card_empty]at key;obtain⟨j,hj⟩:(junk G C).Nonempty:=card_pos.mp (by rw[X.2.2.2.1];omega);obtain⟨a,ha,b,hr,-⟩:=(hL j hj 0).2;have hne:(orIn n C (opnd C a b)).Nonempty:=nonempty_iff_ne_empty.mpr λhe=>by
   have:=card_pos.mpr ⟨a,mF ha he⟩;omega
  obtain⟨h,hh,-⟩:=hmix hj hr hne;have:=card_pos.mpr ⟨h,hh⟩;omega
 have claim:∀v∈D,∃p∈K,∃h∈Mix,∃h'∈Mix,orIn n C h={v}/\orIn n C h'={p}:=by
  intro v hv;obtain⟨hvXK,hvR⟩:=mem_sdiff.mp hv;obtain⟨hvX,hvK⟩:=mem_sdiff.mp hvXK;obtain⟨J,hJ,β,rfl⟩:=(hXs _).mp hvX;obtain⟨a,ha,b,hr,hva⟩:=(hL J hJ β).2;have hne:(orIn n C (opnd C a b)).Nonempty:=nonempty_iff_ne_empty.mpr λhe=>hvR (tV ha he hva);have hsg:=vA hR1 col hcol X hL hJ ha hr hva hne;obtain⟨b',p,hpK,hside,hQ⟩:=hKa a (q4 ha hne ⟨_,hva⟩);obtain⟨J',hJ',γ,rfl,hr'⟩:=hQ ⟨b,L J β,hsg,J,hJ,β,rfl,hr⟩;have hside:orIn n C (opnd C a (1-b'))={L J' γ}:=hside;rcases dC b b' with rfl|rfl
  ·rw[hsg,singleton_inj]at hside;exact absurd (hside▸hpK) hvK
  rw[dD]at hside;obtain⟨h1,hh1,s1,n1⟩:=hmix hJ' hr' ⟨_,hva⟩;obtain⟨h2,hh2,s2,n2⟩:=hmix hJ hr hne;rw[hsg]at s1;rw[hside]at s2;exact⟨_,hpK,h1,hh1,h2,hh2,n1.subset_singleton_iff.mp s1,n2.subset_singleton_iff.mp s2⟩
 obtain⟨p0,hp0,-,-,h',hh',-,hh'p⟩:=claim v0 hv0;have hsub:insert p0 D⊆(Mix.filter λh=>(orIn n C h).card=1).biUnion (orIn n C):=by
  intro v hv;obtain⟨h,hh,e⟩:∃h∈Mix,orIn n C h={v}:=by
   rcases mem_insert.mp hv with rfl|hv
   ·exact⟨h',hh',hh'p⟩
   ·obtain⟨-,-,h,hh,-,-,e,-⟩:=claim v hv;exact⟨h,hh,e⟩
  exact mem_biUnion.mpr ⟨h,mem_filter.mpr ⟨hh,by rw[e,card_singleton]⟩,by rw[e];exact mem_singleton_self _⟩
 have h1:=(card_le_card hsub).trans card_biUnion_le;rw[sum_congr rfl λh hh=>(mem_filter.mp hh).2,sum_const,smul_eq_mul,mul_one,card_insert_of_notMem (s:=D) λh=>(mem_sdiff.mp (mem_sdiff.mp h).1).2 hp0]at h1;have:=card_filter_le Mix λh=>(orIn n C h).card=1;omega
theorem jR (hR1:cM) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (X:bM G C) (hnc:∀a∈tops G C,∀j∈junk G C,∀k∈junk G C,k≠j ->∀b:Fin 2,OrReaches n C (opnd C a b) j ->¬OrReaches n C (opnd C a (1-b)) k):False:=by
 obtain⟨j0,hj0⟩:(junk G C).Nonempty:=card_pos.mp (by rw[X.2.2.2.1];omega)
 obtain⟨v0,-⟩:=card_pos.mp (show 0<(orIn n C (opnd C j0 0)).card by
  have:=X.2.2.2.2.2.2 j0 hj0 0;omega)
 have hex:∀(J:ℕ) (β:Fin 2),∃v:Fin n,J∈junk G C ->v∈orIn n C (opnd C J β)/\jD n G C J v:=by
  intro J β;by_cases hJ:J∈junk G C
  ·obtain⟨k,hkj,hJk⟩:=gC X.2.2.2.1 hJ;have hk:k∈junk G C:=by rw[hJk];simp
   obtain⟨hp,hz⟩:=nP hR1 col hcol X.2.2.1 X.1 X.2.1 hJk hkj (X.2.2.2.2.1 J hJ k hk) (X.2.2.2.2.1 k hk J hJ) (X.2.2.2.2.2.1 J hJ) (X.2.2.2.2.2.2 J hJ 0) (X.2.2.2.2.2.2 J hJ 1) λa ha b hr=>hnc a ha J hJ k hk hkj b hr;rcases bG β with⟨rfl,-⟩|⟨rfl,-⟩
   ·obtain⟨a,ha,b,hr,p,hp,hpS⟩:=hp;exact⟨p,λ_=>⟨hpS,a,ha,b,hr,hp⟩⟩
   ·obtain⟨a,ha,b,hr,p,hp,hpS⟩:=hz;exact⟨p,λ_=>⟨hpS,a,ha,b,hr,hp⟩⟩
  ·exact⟨v0,λh=>absurd h hJ⟩
 choose L hL using hex;exact eT hR1 col hcol X λJ hJ β=>hL J β hJ
def bN (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (J:ℕ) (β:Fin 2) (v:Fin n):Prop:=v∈side C J β/\jD n G C J v
open Classical in
noncomputable def dL (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit):Finset ℕ:=(range (n+C.gates.length)).filter (mD n G C)
lemma f6 {h:ℕ}:h∈dL n G C↔h<n+C.gates.length/\mD n G C h:=by
 simp[dL]
def fG (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (a:ℕ):Prop:=a∈tops G C/\∃b:Fin 2,∃J∈junk G C,∃K∈junk G C,K≠J/\OrReaches n C (opnd C a b) J/\OrReaches n C (opnd C a (1-b)) K
def gN (n:ℕ) (C:Circuit):ℕ ->ℕ ->Prop:=aM (bX n C) (bF n C) (bI n C)
def l6 (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit):Finset ℕ:=(orN G C\lam G C).image (n+·)
def nZ (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (K Lns:Finset (Fin n)):Prop:=K.card≤(tops G C\centreless G C).card/\(∀e∈starEdges G C,∃v∈K,v∈e)/\∀a∈tops G C\centreless G C,∃b:Fin 2,∃p∈K,side C a (1-b)={p}/\((∃b':Fin 2,∃p',side C a (1-b')={p'}/\p'∈Lns) ->p∈Lns)
lemma n5 (X:bM G C) (Lns:Finset (Fin n)):∃K,nZ G C K Lns:=let ⟨K,h⟩:=uE X.1.1 X.2.2.1 λ_ _ v=>v∈Lns;⟨K,h⟩
lemma pI (hA:IsAO2 n C) {a J:ℕ} (ha:a∈tops G C) (hJ:J∈junk G C) {b:Fin 2} (h0:OrReaches n C (opnd C a b) J) (h1:OrReaches n C (opnd C a (1-b)) J):False:=by
 obtain⟨hal,hop,hb⟩:=aI.mp ha;exact(aA.mp hJ).2.2 λx hx=>hb x ((aN hA hal hop b x).mpr ⟨aO hA x h0 hx,aO hA x h1 hx⟩)
lemma nB (hA:IsAO2 n C) {a:ℕ} (hx:fG G C a) (χ:Fin n ->Bool) (h:∀i∈junk G C,gateVal n C i χ=true):graphFun G ∅ χ=true:=by
 obtain⟨ha,b,J,hJ,K,hK,-,h0,h1⟩:=hx;obtain⟨hal,hop,hb⟩:=aI.mp ha;exact hb χ ((aN hA hal hop b χ).mpr ⟨aO hA χ h0 (h J hJ),aO hA χ h1 (h K hK)⟩)
lemma tU {a:ℕ} (hx:fG G C a) (b:Fin 2):∃i∈junk G C,OrReaches n C (opnd C a b) i:=by
 obtain⟨-,b',J,hJ,K,hK,-,h0,h1⟩:=hx;rcases dC b' b with rfl|rfl;exacts[⟨J,hJ,h0⟩,⟨K,hK,h1⟩]
lemma n3 (hA:IsAO2 n C) {w J:ℕ} (hJ:J∈junk G C) (hr:OrReaches n C w J) (hne:(orIn n C w).Nonempty):∃m,n+m∈dL n G C/\OrReaches n C w m/\OrReaches n C (n+m) J:=by
 obtain⟨m,b,hm,hop,hwm,-,he,hrJ⟩:=fE hA (aA.mp hJ).2.1 hr hne;refine⟨m,f6.mpr ⟨by omega,a7.mpr ⟨hm,hop⟩,⟨J,hJ,d9 hA hm hop b hrJ⟩,?_⟩,hwm,d9 hA hm hop b hrJ⟩;simp only[bF,bI,Nat.add_sub_cancel_left];rcases bG b with⟨rfl,-⟩|⟨rfl,-⟩;exacts[Or.inl he,Or.inr he]
lemma qX (hA:IsAO2 n C) {a:ℕ} (hx:fG G C a):a∈centreless G C\/2≤(dL n G C).card:=by
 refine or_iff_not_imp_left.mpr λhc=>?_;obtain⟨ha,b,J,hJ,K,hK,hKJ,h0,h1⟩:=hx;have hne:∀b',(orIn n C (opnd C a b')).Nonempty:=λb'=>nonempty_iff_ne_empty.mpr λhe=>hc (mF ha he);obtain⟨m1,hm1,r1,-⟩:=n3 hA hJ h0 (hne b);obtain⟨m2,hm2,-,s2⟩:=n3 hA hK h1 (hne (1-b));have:n+m1≠n+m2:=λe=>by
  obtain rfl:m1=m2:=by omega
  exact pI hA ha hK (cG hA r1 s2) h1
 exact(card_le_card (insert_subset_iff.mpr ⟨hm1,singleton_subset_iff.mpr hm2⟩)).trans' (by rw[card_insert_of_notMem (by simpa using this),card_singleton])
lemma nN (hA:IsAO2 n C) {a:ℕ} (hxa:fG G C a):2≤2*(centreless G C).card+(dL n G C).card:=by
 rcases qX hA hxa with h|h
 ·have:=card_pos.mpr ⟨_,h⟩;omega
 ·omega
lemma jU {J K:ℕ} (h:junk G C={J,K}):J∈junk G C/\K∈junk G C:=by
 rw[h];simp
lemma eF {J K i:ℕ} (h:junk G C={J,K}) (hi:i∈junk G C):i=J\/i=K:=by
 rwa[h,mem_insert,mem_singleton]at hi
lemma jX (X:bM G C) {J:ℕ} (hJ:J∈junk G C) (δ:Fin 2):Disjoint (side (n:=n) C J δ) (side C J (1-δ)):=by
 have d:=(cS X hJ).2.1;rcases bG δ with⟨rfl,h⟩|⟨rfl,h⟩<;>rw[h];exacts[d,d.symm]
lemma q8 (X:bM G C) {J:ℕ} (hJ:J∈junk G C) {δ δ':Fin 2} {x:Fin n} (h1:x∈side C J δ) (h2:x∈side C J δ'):δ'=δ:=(dC δ δ').resolve_right λe=>disjoint_left.mp (jX X hJ δ) h1 (e▸h2)
lemma eE (X:bM G C) {J:ℕ} (hJ:J∈junk G C) {u v:Fin n} (hx:gateVal n C J (pairInput u v)=true):∃γ:Fin 2,u∈side C J γ/\v∈side C J (1-γ):=by
 obtain⟨⟨s,hs,hsx⟩,⟨t,ht,htx⟩⟩:=((cS X hJ).1 0 _).mp hx;have hst:s≠t:=λe=>disjoint_left.mp (cS X hJ).2.1 hs (e▸ht);have hs':s=u\/s=v:=by simpa[pairInput]using hsx
 have ht':t=u\/t=v:=by simpa[pairInput]using htx
 rcases hs' with rfl|rfl<;>rcases ht' with rfl|rfl;exacts[absurd rfl hst,⟨0,hs,ht⟩,⟨1,ht,hs⟩,absurd rfl hst]
lemma kF (X:bM G C) {e:Sym2 (Fin n)} (he:e∈Ustar G C):(∃J∈junk G C,∃γ:Fin 2,∃v,bN n G C J γ v/\∃w∈side C J (1-γ),e=s(v,w))\/∃u v,e=s(u,v)/\G.Adj u v/\∀i∈junk G C,gateVal n C i (pairInput u v)=true:=by
 induction e using Sym2.ind with
 |_ u v=>
 have huv:G.Adj u v:=SimpleGraph.mem_edgeFinset.mp (mem_sdiff.mp he).1;obtain⟨a,ha,hax,b,k,hk,-,hr,hkx⟩:=fD X.1 X.2.1 he;obtain⟨hal,hop,-⟩:=aI.mp ha;rcases (a8 X.1.1 X.2.1 hal hop (1-b) _).mp ((aN X.1.1 hal hop b _).mp hax).2 with⟨w,hw,hwx⟩|⟨k',hk',-,hr',hk'x⟩
 ·obtain⟨γ,hu,hv⟩:=eE X hk hkx;have hwuv:w=u\/w=v:=by simpa[pairInput]using hwx
  rcases hwuv with rfl|rfl
  ·exact Or.inl ⟨k,hk,γ,w,⟨hu,a,ha,b,hr,hw⟩,v,hv,rfl⟩
  ·exact Or.inl ⟨k,hk,1-γ,w,⟨hv,a,ha,b,hr,hw⟩,u,by rwa[dD],Sym2.eq_swap⟩
 obtain⟨k2,-,hJ2⟩:=gC X.2.2.2.1 hk;refine Or.inr ⟨u,v,rfl,huv,λi hi=>?_⟩;rcases eF hJ2 hi with rfl|rfl
 ·exact hkx
 ·exact(eF hJ2 hk').resolve_left (λe=>pI X.1.1 ha hk hr (e▸hr'))▸hk'x
lemma nW (X:bM G C) {J:ℕ} {β:Fin 2} {p z:Fin n} (hpf:∀t∈side C J (1-β),G.Adj p t) {V:Finset (Sym2 (Fin n))} (hVU:V⊆Ustar G C) (hVE:∀e∈V,∃w∈side C J (1-β),e=s(p,w)) (hz:z∈side C J (1-β)):∃P:Finset ℕ,(∀h∈P,h∈l6 n G C/\¬aB G V (orIn n C h)/\(orIn n C h).Nonempty/\gN n C (opnd C J (1-β)) h)/\V.card≤P.card+1/\(s(p,z)∉V ->V.card≤P.card):=by
 have hS:insert z (aE V p)⊆orIn n C (opnd C J (1-β)):=insert_subset_iff.mpr ⟨hz,λw hw=>by obtain⟨w',hw',e⟩:=hVE _ (aD.mp hw);rwa[Sym2.congr_right.mp e]⟩;obtain⟨P,hP,hc⟩:=d8 (aJ X.1.1) (aB G V) _ _ hS (λW hW=>a4 X.2.2.1 (hVU.trans sdiff_subset) hW p z (hpf z hz)) λu _ hu=>Or.inr (bL hu)
 have hV:V.card≤(aE V p).card:=(card_le_card λe he=>by
  obtain⟨w,-,rfl⟩:=hVE e he
  exact mem_image_of_mem _ (aD.mpr he)).trans card_image_le
 refine⟨P,λh hh=>?_,?_,λhn=>?_⟩
 ·obtain⟨a,b,c,d⟩:=hP h hh;have hne:=(card_pos.mp (zero_lt_one.trans d)).mono inter_subset_left;exact⟨g4 X.1.1 a hne λhu=>c (bT hVU subset_rfl hu),c,hne,b⟩
 ·have:=card_le_card (subset_insert z (aE V p));omega
 ·rw[card_insert_of_notMem (λh=>hn (aD.mp h))]at hc;omega
lemma qW (X:bM G C) {J:ℕ} {β:Fin 2} {p x y:Fin n} (hpf:∀t∈side C J (1-β),G.Adj p t) (hp:p∈side C J β) (hx:x∈side C J β) (hxp:x≠p) (hy:y∈side C J (1-β)) (hxy:G.Adj x y) (hU:s(x,y)∈Ustar G C):∃h,h∈l6 n G C/\gN n C (opnd C J β) h/\x∈orIn n C h/\p∈orIn n C h:=by
 obtain⟨h,hJh,hr,hf,hxh,hph⟩:=eU (aJ X.1.1) (aB G {s(x,y)}) (opnd C J β) x p hxp hx hp (λW ⟨z,hz⟩ ⟨hxW,hpW⟩=>by
   refine(hz x hxW).2 (mem_singleton.mpr ?_)
   rw[aQ X.2.2.1 hxp (hz x hxW).1.symm (hz p hpW).1.symm hxy (hpf y hy),Sym2.eq_swap])
  λu _ hu=>Or.inr (bL hu)
 exact⟨h,g4 X.1.1 hJh ⟨x,hxh⟩ λhu=>hf (bT (singleton_subset_iff.mpr hU) subset_rfl hu),hr,hxh,hph⟩
theorem lL (X:bM G C) {K Lns:Finset (Fin n)} (hKC:nZ G C K Lns) {Xc:Finset (Fin n)} (hX:∀e∈Ustar G C,∃v∈Xc,v∈e) {P:Finset ℕ} (hP:∀h∈P,h∈l6 n G C/\∃J∈junk G C,∃β:Fin 2,gN n C (opnd C J β) h) (hlt:(Ustar G C).card+(Xc\K).card<2+2*(centreless G C).card+P.card+(dL n G C).card):False:=by
 have hA:=X.1.1;have hM:=e4 X.2.2.1 X.1 X.2.1 X.2.2.2.1 K Xc hKC.2.1 hX;have d2:Disjoint P (dL n G C):=disjoint_left.mpr λh h1 h2=>by
  obtain⟨hJh,⟨J',hJ',hr'⟩,-⟩:=(f6.mp h2).2;obtain⟨-,J,hJ,β,hr⟩:=hP h h1;obtain⟨g,rfl⟩:∃g,h=n+g:=⟨h-n,by have:=hJh.1;omega⟩;exact X.2.2.2.2.1 J' hJ' J hJ (bU hA (aA.mp hJ).1 β (cG hA ((cK hA).mpr ⟨(a7.mp hJh).1,hr⟩) hr'))
 have:=card_le_card (show P∪dL n G C⊆(orN G C\lam G C).image (n+·)from λh hh=>(mem_union.mp hh).elim (λhh=>(hP h hh).1) λhh=>q0 hA (f6.mp hh).2);rw[card_union_of_disjoint d2,card_image_of_injective _ (add_right_injective n)]at this;have:=hKC.1;omega
lemma pY {a b c:Fin n} (h:graphFun G ∅ (λz=>decide (z=a\/z=b\/z=c))=true):G.Adj a b\/G.Adj a c\/G.Adj b c:=by
 obtain⟨u,v,huv,hu,hv⟩:=(dJ _).mp h;simp only[decide_eq_true_eq]at hu hv;rcases hu with rfl|rfl|rfl<;>rcases hv with rfl|rfl|rfl<;>
 first
 |exact(G.irrefl huv).elim
 |exact Or.inl huv
 |exact Or.inl huv.symm
 |exact Or.inr (Or.inl huv)
 |exact Or.inr (Or.inl huv.symm)
 |exact Or.inr (Or.inr huv)
 |exact Or.inr (Or.inr huv.symm)
section
variable (hR1:cM) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (X:bM G C)
include col hcol X
lemma rD {a:ℕ} (hxa:fG G C a) {j k:ℕ} (hJK:junk G C={j,k}) {V:Finset (Sym2 (Fin n))} (hVU:V⊆Ustar G C) (hVE:∀e∈V,∃u v,e=s(u,v)/\∀i∈junk G C,gateVal n C i (pairInput u v)=true):∃Q:Finset (Fin n),∃P:Finset ℕ,(∀e∈V,∃v∈Q,v∈e)/\(∀h∈P,h∈l6 n G C/\¬aB G V (orIn n C h)/\∃J∈junk G C,∃β:Fin 2,gN n C (opnd C J β) h)/\V.card+Q.card≤P.card+2/\Q.card≤2*V.card:=by
 have hA:=X.1.1;obtain⟨hj,hk⟩:=jU hJK;rcases V.eq_empty_or_nonempty with rfl|hne
 ·exact⟨∅,∅,by simp,by simp,by simp⟩
 have hV1:=card_pos.mpr hne;obtain⟨e0,he0⟩:=id hne;obtain⟨z,-,-,-⟩:=hVE e0 he0
 let rt:Fin 4 ->ℕ:= ![opnd C j 0,opnd C j 1,opnd C k 0,opnd C k 1]
 have hrt:∀i,∃J∈junk G C,∃β:Fin 2,rt i=opnd C J β:=λi=>by
  fin_cases i;exacts[⟨j,hj,0,rfl⟩,⟨j,hj,1,rfl⟩,⟨k,hk,0,rfl⟩,⟨k,hk,1,rfl⟩]
 have hH:∀χ:Fin n ->Bool,(∀i,∃v∈orIn n C (rt i),χ v=true) ->graphFun G ∅ χ=true:=λχ h=>nB hA hxa χ λi hi=>by
   rcases eF hJK hi with rfl|rfl
   ·exact((cS X hj).1 0 χ).mpr ⟨h 0,h 1⟩
   ·exact((cS X hk).1 0 χ).mpr ⟨h 2,h 3⟩
 have hacc:∀e∈V,∀i,∃v∈orIn n C (rt i),v∈e:=λe he i=>by
  obtain⟨u,v,rfl,hall⟩:=hVE e he;obtain⟨J,hJ,β,hi⟩:=hrt i;rw[hi];obtain⟨γ,hu,hv⟩:=eE X hJ (hall J hJ);rcases dC γ β with rfl|rfl;exacts[⟨u,hu,Sym2.mem_mk_left _ _⟩,⟨v,hv,Sym2.mem_mk_right _ _⟩]
 have hleaf:∀i u,gN n C (rt i) u ->¬bX n C u ->aB G V (orIn n C u)\/(orIn n C u).card≤1:=λ_ u _ hu=>Or.inr (bL hu);have hV:V⊆G.edgeFinset:=hVU.trans sdiff_subset;have cv:∀h,bX n C h ->¬aB G V (orIn n C h) ->∀i,gN n C (rt i) h ->h∈l6 n G C/\¬aB G V (orIn n C h)/\∃J∈junk G C,∃β:Fin 2,gN n C (opnd C J β) h:=λh hJh hf i hr=>by
   obtain⟨J,hJ,β,e⟩:=hrt i;exact⟨g4 hA hJh (nonempty_iff_ne_empty.mpr λe=>hf ⟨z,by simp[e]⟩) λhu=>hf (bT hVU subset_rfl hu),hf,J,hJ,β,e▸hr⟩
 by_cases hcom:∃p,∀e∈V,p∈e
 ·obtain⟨p,hp⟩:=hcom;obtain⟨i,P,hP,hc⟩:=mP col hcol X.2.2.1 (aJ hA) rt hH V hV hacc hleaf p hp hne;exact⟨{p},P,λe he=>⟨p,mem_singleton_self _,hp e he⟩,λh hh=>cv h (hP h hh).1 (hP h hh).2.2 i (hP h hh).2.1,by rw[card_singleton];omega,by rw[card_singleton];omega⟩
 push Not at hcom;obtain⟨Q,hQ2,hQ⟩:=gY col hcol X.2.2.1 (λi=>orIn n C (rt i)) hH V hV hacc;rcases kM col hcol X.2.2.1 (aJ hA) rt hH V hV hacc hleaf hcom with⟨i1,i2,P,hP,hc⟩|⟨i,i',i'',-,-,-,-,-,-,-,-,-,-,-,-,-,⟨P,hP,hc⟩,h0,hJ0,hF0,hR0,hn1,hn2,-,-⟩
 ·refine⟨Q,P,hQ,λh hh=>?_,by omega,by omega⟩;obtain⟨hJh,hf,hr⟩:=hP h hh;rcases hr with hr|hr;exacts[cv h hJh hf i1 hr,cv h hJh hf i2 hr]
 ·have h0P:h0∉P:=λh=>(hP h0 h).2.2.elim hn1 hn2;refine⟨Q,insert h0 P,hQ,λh hh=>?_,by rw[card_insert_of_notMem h0P];omega,by omega⟩;rcases mem_insert.mp hh with rfl|hh
  ·exact cv h hJ0 hF0 i'' hR0
  ·obtain⟨hJh,hf,hr⟩:=hP h hh;rcases hr with hr|hr;exacts[cv h hJh hf i hr,cv h hJh hf i' hr]
lemma rF {ax:ℕ} (hxa:fG G C ax) {J:ℕ} (hJ:J∈junk G C) {β:Fin 2} {p:Fin n} (hp:bN n G C J β p) {x y:Fin n} (hx:x∈side C J β) (hxp:x≠p) (hy:y∈side C J (1-β)) (hxy:G.Adj x y) {K Lns:Finset (Fin n)} (hpL:p∈Lns) (hKC:nZ G C K Lns):∃t∈side C J (1-β),s(p,t)∉Ustar G C\/3≤2*(centreless G C).card+(dL n G C).card+(Lns∩K).card:=by
 have hA:=X.1.1;have h4:=X.2.2.1;obtain⟨a,ha,b,hr,hpa⟩:=hp.2;have hrx:=qX hA hxa;by_cases he:orIn n C (opnd C a b)=∅
 ·refine⟨y,hy,Or.inr ?_⟩;have hac:=mF ha he;have c1:=card_pos.mpr ⟨_,hac⟩;rcases hrx with hxc|hm2
  ·by_cases hax:a=ax
   ·subst hax;obtain⟨i,hi,hri⟩:=tU hxa (1-b);obtain⟨m,hm,-⟩:=n3 hA hi hri ⟨p,hpa⟩;have:=card_pos.mpr ⟨_,hm⟩;omega
   ·have:=card_le_card (insert_subset_iff.mpr ⟨hac,singleton_subset_iff.mpr hxc⟩);rw[card_insert_of_notMem (by simpa using hax),card_singleton]at this;omega
  ·omega
 have hne:(side (n:=n) C a b).Nonempty:=nonempty_iff_ne_empty.mpr he;by_cases hs:side C a (1-b)={p}
 ·refine⟨y,hy,Or.inr ?_⟩;obtain⟨b',p',hp'K,-,hQ⟩:=hKC.2.2 a (q4 ha hne ⟨p,hpa⟩);have:=card_pos.mpr ⟨p',mem_inter.mpr ⟨hQ ⟨b,p,hs,hpL⟩,hp'K⟩⟩;rcases hrx with hxc|hm2
  ·have:=card_pos.mpr ⟨_,hxc⟩;omega
  ·omega
 obtain⟨w,hw,hwp⟩:∃w∈side C a (1-b),w≠p:=by
  by_contra h;push Not at h;exact hs (eq_singleton_iff_unique_mem.mpr ⟨hpa,h⟩)
 obtain⟨s0,hs0⟩:=hne;have h1:=aV hA ha b hpa hs0;have h2:=(aV hA ha b hw hs0).1;have hpf:=cY X hJ hp.1 hp.2;have cw:col w=col x:=(gK _ _ _ (hcol _ _ h2) (hcol _ _ h1.1)).trans (gK _ _ _ (hcol _ _ hxy) (hcol _ _ (hpf y hy))).symm;obtain⟨t0,ht0,ht0y⟩:=exists_mem_ne (X.2.2.2.2.2.2 J hJ (1-β)) y;have hxt:¬G.Adj x t0:=λh=>ht0y (aQ h4 hxp hxy (hpf y hy) h (hpf t0 ht0)).symm;have hwt:G.Adj w t0:=by
  rcases pY (eH hA ha hr hw (λz=>decide (z=x\/z=t0\/z=w)) (((cS X hJ).1 β _).mpr ⟨⟨x,hx,by simp⟩,t0,ht0,by simp⟩) (by simp))with h|h|h;exacts[absurd h hxt,absurd cw.symm (hcol _ _ h),h.symm]
 exact⟨t0,ht0,Or.inl λhm=>(mem_sdiff.mp hm).2 (aQ h4 hwp h2 h1.1 hwt (hpf t0 ht0)▸h1.2)⟩
theorem tO {ax:ℕ} (hxa:fG G C ax) {j k:ℕ} (hJK:junk G C={j,k}) (hno:∀i∈junk G C,∀δ v,¬bN n G C i δ v):False:=by
 obtain⟨Kc,hKC⟩:=n5 X ∅;obtain⟨Q,P,hQ,hP,hc,-⟩:=rD col hcol X hxa hJK subset_rfl λe he=>by
  rcases kF X he with⟨i,hi,δ,v,hv,-⟩|⟨u,v,rfl,-,hall⟩;exacts[absurd hv (hno i hi δ v),⟨u,v,rfl,hall⟩]
 refine lL X hKC hQ (λh hh=>⟨(hP h hh).1,(hP h hh).2.2⟩) ?_;have:=card_le_card (sdiff_subset (s:=Q) (t:=Kc));have:=nN X.1.1 hxa;omega
theorem tX {ax:ℕ} (hxa:fG G C ax) {j k:ℕ} (hJK:junk G C={j,k}) {J:ℕ} (hJ:J∈junk G C) {β:Fin 2} {p:Fin n} (hp:bN n G C J β p) (hLs:∀i∈junk G C,∀δ v,bN n G C i δ v ->i=J/\δ=β/\v=p):False:=by
 classical
 have hA:=X.1.1;obtain⟨Kc,hKC⟩:=n5 X {p};have hpf:=cY X hJ hp.1 hp.2
 let st:Sym2 (Fin n) ->Prop:=λe=>∃w∈side C J (1-β),e=s(p,w)
 set Vp:=(Ustar G C).filter st;set U':=(Ustar G C).filter λe=>¬st e;have hsplit:Vp.card+U'.card=(Ustar G C).card:=card_filter_add_card_filter_not st;have hU':∀e∈U',∃u v,e=s(u,v)/\G.Adj u v/\∀i∈junk G C,gateVal n C i (pairInput u v)=true:=λe he=>by
  obtain⟨heU,hn⟩:=mem_filter.mp he;rcases kF X heU with⟨i,hi,δ,v,hv,w,hw,rfl⟩|h
  ·obtain⟨rfl,rfl,rfl⟩:=hLs i hi δ v hv;exact absurd ⟨w,hw,rfl⟩ hn
  ·exact h
 obtain⟨Q,P',hQ,hP',hc',hQ2⟩:=rD col hcol X hxa hJK (V:=U') (filter_subset _ _) λe he=>by obtain⟨u,v,h1,-,h2⟩:=hU' e he;exact⟨u,v,h1,h2⟩
 obtain⟨z,hz,hres⟩:∃z∈side C J (1-β),s(p,z)∉Vp\/3≤2*(centreless G C).card+(dL n G C).card+({p}∩Kc).card\/U'=∅:=by
  rcases U'.eq_empty_or_nonempty with h0|⟨e0,he0⟩
  ·obtain⟨z,hz⟩:=card_pos.mp (zero_lt_two.trans_le (X.2.2.2.2.2.2 J hJ (1-β)));exact⟨z,hz,Or.inr (Or.inr h0)⟩
  obtain⟨u,v,rfl,huv,hall⟩:=hU' e0 he0;obtain⟨x,y,hx,hy,hxy,hU⟩:∃x y,x∈side C J β/\y∈side C J (1-β)/\G.Adj x y/\s(x,y)∈U':=by
   obtain⟨δ,hu,hv⟩:=eE X hJ (hall J hJ);rcases dC β δ with rfl|rfl
   ·exact⟨u,v,hu,hv,huv,he0⟩
   ·rw[dD]at hv;exact⟨v,u,hv,hu,huv.symm,by rwa[Sym2.eq_swap]⟩
  obtain⟨t,ht,h⟩:=rF col hcol X hxa hJ hp hx (λe=>(mem_filter.mp hU).2 ⟨y,hy,by rw[e]⟩) hy hxy (mem_singleton_self p) hKC;exact⟨t,ht,h.imp (λh hm=>h (mem_filter.mp hm).1) Or.inl⟩
 obtain⟨Pp,hPp,c1,c2⟩:=nW X hpf (V:=Vp) (filter_subset _ _) (λe he=>(mem_filter.mp he).2) hz;have hd:Disjoint Pp P':=disjoint_left.mpr λh h1 h2=>(hP' h h2).2.1 ⟨p,λw hw=>⟨hpf w (aK (aJ hA) (hPp h h1).2.2.2 hw),λhm=>(mem_filter.mp hm).2 ⟨w,aK (aJ hA) (hPp h h1).2.2.2 hw,rfl⟩⟩⟩;have hX:∀e∈Ustar G C,∃v∈insert p Q,v∈e:=λe he=>by
  by_cases hs:st e
  ·obtain⟨w,-,rfl⟩:=hs;exact⟨p,mem_insert_self _ _,Sym2.mem_mk_left _ _⟩
  ·obtain⟨v,hv,hve⟩:=hQ e (mem_filter.mpr ⟨he,hs⟩);exact⟨v,mem_insert_of_mem hv,hve⟩
 refine lL X hKC hX (P:=Pp∪P') (λh hh=>(mem_union.mp hh).elim (λhh=>⟨(hPp h hh).1,J,hJ,_,(hPp h hh).2.2.2⟩) λhh=>⟨(hP' h hh).1,(hP' h hh).2.2⟩) ?_;have:=card_sdiff_add_card_inter (insert p Q) Kc;have:=card_le_card (inter_subset_inter_right (u:=Kc) (singleton_subset_iff.mpr (mem_insert_self p Q)));have:=card_insert_le p Q;have:=nN hA hxa;rw[card_union_of_disjoint hd];rcases hres with h|h|h
 ·have:=c2 h;omega
 ·omega
 ·rw[h,card_empty]at hQ2 hsplit;omega
lemma rC {ax:ℕ} (hxa:fG G C ax) {J K:ℕ} (hJK:junk G C={J,K}) {β γ:Fin 2} {p q x y:Fin n} (hpf:∀t∈side C J (1-β),G.Adj p t) (hqf:∀t∈side C K (1-γ),G.Adj q t) (hx:x∈side C J β) (hy:y∈side C J (1-β)) (hxK:x∈side C K γ) (hyK:y∈side C K (1-γ)) (hxp:x≠p) (hxq:x≠q) (hxy:G.Adj x y):False:=by
 obtain⟨hJ,hK⟩:=jU hJK;have h4:=X.2.2.1;obtain⟨t,ht,hty⟩:=exists_mem_ne (X.2.2.2.2.2.2 J hJ (1-β)) y;obtain⟨t',ht',ht'y⟩:=exists_mem_ne (X.2.2.2.2.2.2 K hK (1-γ)) y;have h1:¬G.Adj x t:=λh=>hty (aQ h4 hxp hxy (hpf y hy) h (hpf t ht)).symm;have h2:¬G.Adj x t':=λh=>ht'y (aQ h4 hxq hxy (hqf y hyK) h (hqf t' ht')).symm;have h3:col t=col t':=(gK _ _ _ (hcol _ _ (hpf t ht)).symm (hcol _ _ (hpf y hy)).symm).trans (gK _ _ _ (hcol _ _ (hqf t' ht')).symm (hcol _ _ (hqf y hyK)).symm).symm
 rcases pY (nB X.1.1 hxa (λz=>decide (z=x\/z=t\/z=t')) λi hi=>by
   rcases eF hJK hi with rfl|rfl
   ·exact((cS X hJ).1 β _).mpr ⟨⟨x,hx,by simp⟩,t,ht,by simp⟩
   ·exact((cS X hK).1 γ _).mpr ⟨⟨x,hxK,by simp⟩,t',ht',by simp⟩)with h|h|h
 exacts[h1 h,h2 h,hcol _ _ h h3]
include hR1
theorem rG {J K:ℕ} (hJK:junk G C={J,K}) (hKJ:K≠J) {β:Fin 2} (hβ:∀v,¬bN n G C J β v):∃x y:Fin n,G.Adj x y/\s(x,y)∈Ustar G C/\(∀i∈junk G C,gateVal n C i (pairInput x y)=true)/\∀i∈junk G C,∀w,jD n G C i w ->w≠x/\w≠y:=by
 obtain⟨hJ,hK⟩:=jU hJK;have hjk:=X.2.2.2.2.1 J hJ K hK;by_contra hno;have key:∀u v,G.Adj u v ->wireVal n (aG n C J) C.output (pairInput u v)=false ->∃γ w,(w=u\/w=v)/\bN n G C J γ w/\gateVal n C J (pairInput u v)=true:=by
  intro u v huv hl;obtain⟨a,ha,b,hr,hjx,h⟩:=f7 X.1 X.2.1 hJK hKJ hjk huv hl;have hl':∀w,jD n G C J w ->(w=u\/w=v) ->∃γ w,(w=u\/w=v)/\bN n G C J γ w/\gateVal n C J (pairInput u v)=true:=λw hw hwuv=>by
   obtain⟨γ,hu,hv⟩:=eE X hJ hjx;rcases hwuv with rfl|rfl;exacts[⟨γ,w,Or.inl rfl,⟨hu,hw⟩,hjx⟩,⟨1-γ,w,Or.inr rfl,⟨hv,hw⟩,hjx⟩]
  rcases h with⟨w,hw,hwuv⟩|⟨-,hkx⟩
  ·exact hl' w ⟨a,ha,b,hr,hw⟩ hwuv
  by_contra hc
  refine hno ⟨u,v,huv,mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr huv,λhs=>by
   rw[qU X hJ hs]at hl;cases hl⟩,λi hi=>?_,λi hi w hw=>?_⟩
  ·rcases eF hJK hi with rfl|rfl;exacts[hjx,hkx]
  by_contra hw';have hwuv:w=u\/w=v:=by tauto
  rcases eF hJK hi with rfl|rfl
  ·exact hc (hl' w hw hwuv)
  obtain⟨a',ha',b',hr',hv'⟩:=hw
  rw[lS X hJ ha' λb''=>by
   rcases dC b' b'' with rfl|rfl
   exacts[jV X hJ (Or.inr ⟨hi,hKJ,hr',hkx⟩),jV X hJ (k:=i) (Or.inl ⟨_,hv',by rcases hwuv with rfl|rfl<;>simp[pairInput]⟩)]]at hl
  cases hl
 have hside:∀γ w,bN n G C J γ w ->γ=1-β:=λγ w h=>(dC β γ).resolve_left λe=>hβ w (e▸h);by_cases hc:∃c,bN n G C J (1-β) c
 ·obtain⟨c,hc⟩:=hc;have hv:=(cS X hJ).1 (1-β);have hcT:=cY X hJ hc.1 hc.2;rw[dD]at hv hcT;refine fK hR1 col hcol X.2.2.1 X.1 hJK hKJ hjk ((cS X hJ).2.2 β) hv hc.1 hcT λu v huv hl=>?_;obtain⟨γ,w,hwuv,hw,hjx⟩:=key u v huv hl;obtain rfl:=hside γ w hw;obtain rfl:w=c:=sK X hJ (cY X hJ hw.1 hw.2) (cY X hJ hc.1 hc.2);obtain⟨δ,hu,hv'⟩:=eE X hJ hjx;rcases hwuv with rfl|rfl
  ·obtain rfl:=q8 X hJ hw.1 hu;rw[dD]at hv';exact Or.inl ⟨rfl,hv'⟩
  ·obtain rfl:δ=β:=by rw[←dD δ,q8 X hJ hw.1 hv',dD]
   exact Or.inr ⟨rfl,hu⟩
 ·refine jJ X.1 (aA.mp hJ).1 λu v huv=>by_contra λhl=>?_;obtain⟨γ,w,-,hw,-⟩:=key u v huv (Bool.eq_false_iff.mpr hl);exact hc ⟨w,hside γ w hw▸hw⟩
theorem tN {ax:ℕ} (hxa:fG G C ax) {J K:ℕ} (hJK:junk G C={J,K}) (hKJ:K≠J) {β γ:Fin 2} {p q:Fin n} (hp:bN n G C J β p) (hq:bN n G C K γ q) (hLs:∀i∈junk G C,∀δ v,bN n G C i δ v ->(i=J/\δ=β/\v=p)\/(i=K/\δ=γ/\v=q)):False:=by
 classical
 have hA:=X.1.1;have h4:=X.2.2.1;obtain⟨hJ,hK⟩:=jU hJK;obtain⟨Kc,hKC⟩:=n5 X {p,q};have pf:=cY X hJ hp.1 hp.2;have qf:=cY X hK hq.1 hq.2;obtain⟨x,y,hx,hy,hxy,hU,hk,hnu⟩:∃x y,x∈side C J β/\y∈side C J (1-β)/\G.Adj x y/\s(x,y)∈Ustar G C/\gateVal n C K (pairInput x y)=true/\∀i∈junk G C,∀w,jD n G C i w ->w≠x/\w≠y:=by
  obtain⟨x,y,hxy,hU,hall,hnu⟩:=rG hR1 col hcol X hJK hKJ (β:=1-β) λv hv=>by
   rcases hLs J hJ _ v hv with⟨-,h,-⟩|⟨h,-⟩
   ·exact absurd h (by rcases bG β with⟨rfl,-⟩|⟨rfl,-⟩<;>decide)
   ·exact hKJ h.symm
  obtain⟨δ,hx,hy⟩:=eE X hJ (hall J hJ);rcases dC β δ with rfl|rfl
  ·exact⟨x,y,hx,hy,hxy,hU,hall K hK,hnu⟩
  rw[dD]at hy;exact⟨y,x,hy,hx,hxy.symm,by rwa[Sym2.eq_swap],by rw[kK Sym2.eq_swap,hall K hK],λi hi w hw=>(hnu i hi w hw).symm⟩
 have hxp:x≠p:=λe=>(hnu J hJ p hp.2).1 e.symm;have hq':=hnu K hK q hq.2;obtain⟨ε,hxK,hyK⟩:=eE X hK hk;rcases dC γ ε with rfl|rfl
 ·exact rC col hcol X hxa hJK pf qf hx hy hxK hyK hxp (λe=>hq'.1 e.symm) hxy
 rw[dD]at hyK;have hyq:y≠q:=λe=>hq'.2 e.symm;have hpq:¬G.Adj p q:=λh=>hxp (aQ h4 hyq (pf y hy).symm h.symm hxy.symm (qf x hxK)).symm;have hTT:∀t∈side C J (1-β),t∉side C K (1-γ):=λt h1 h2=>hcol _ _ hxy (gK _ _ (col p) ((gK _ _ _ (hcol _ _ (pf t h1)) (hcol _ _ (qf t h2))).symm▸(hcol _ _ (qf x hxK)).symm) (hcol _ _ (pf y hy)).symm)
 have xt:∀u v,gateVal n C J (pairInput u v)=true ->gateVal n C K (pairInput u v)=true ->G.Adj u v:=λu v h1 h2=>(aT u v).mp (nB hA hxa _ λi hi=>by
  rcases eF hJK hi with rfl|rfl;exacts[h1,h2])
 have tv:∀{i:ℕ} (hi:i∈junk G C) (δ:Fin 2) {u v:Fin n},u∈side C i δ ->v∈side C i (1-δ) ->gateVal n C i (pairInput u v)=true:=λhi δ u v hu hv=>((cS X hi).1 δ _).mpr ⟨⟨u,hu,by simp[pairInput]⟩,v,hv,by simp[pairInput]⟩
 let stp:Sym2 (Fin n) ->Prop:=λe=>∃w∈side C J (1-β),e=s(p,w)
 let stq:Sym2 (Fin n) ->Prop:=λe=>∃w∈side C K (1-γ),e=s(q,w)
 set Vp:=(Ustar G C).filter stp;set Vq:=(Ustar G C).filter stq;have cl:∀u v,u∈side C J β ->v∈side C J (1-β) ->G.Adj u v ->gateVal n C K (pairInput u v)=true ->stp s(u,v)\/stq s(u,v)\/s(u,v)=s(x,y):=by
  intro u v hu hv huv hk;by_cases hup:u=p
  ·exact Or.inl ⟨v,hv,by rw[hup]⟩
  obtain⟨ε,huK,hvK⟩:=eE X hK hk;rcases dC γ ε with rfl|rfl
  ·by_cases huq:u=q
   ·exact Or.inr (Or.inl ⟨v,hvK,by rw[huq]⟩)
   exact(rC col hcol X hxa hJK pf qf hu hv huK hvK hup huq huv).elim
  rw[dD]at hvK;by_cases hvq:v=q
  ·exact Or.inr (Or.inl ⟨u,huK,by rw[hvq,Sym2.eq_swap]⟩)
  obtain rfl:y=v:=aQ h4 hxp hxy (pf y hy) (xt x v (tv hJ β hx hv) (by rw[kK Sym2.eq_swap];exact tv hK γ hvK hxK)) (pf v hv);obtain rfl:x=u:=aQ h4 hyq hxy.symm (qf x hxK) (xt u y (tv hJ β hu hy) (by rw[kK Sym2.eq_swap];exact tv hK γ hyK huK)).symm (qf u huK);exact Or.inr (Or.inr rfl)
 have hcov:Ustar G C⊆Vp∪Vq∪{s(x,y)}:=λe he=>by
  have h3:stp e\/stq e\/e=s(x,y):=by
   rcases kF X he with⟨i,hi,δ,v,hv,w,hw,rfl⟩|⟨u,v,rfl,huv,hall⟩
   ·rcases hLs i hi δ v hv with⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩;exacts[Or.inl ⟨w,hw,rfl⟩,Or.inr (Or.inl ⟨w,hw,rfl⟩)]
   obtain⟨δ,hu,hv⟩:=eE X hJ (hall J hJ);rcases dC β δ with rfl|rfl
   ·exact cl u v hu hv huv (hall K hK)
   rw[dD]at hv;rw[show s(u,v)=s(v,u)from Sym2.eq_swap];exact cl v u hv hu huv.symm (by rw[kK Sym2.eq_swap];exact hall K hK)
  rcases h3 with h|h|rfl
  ·exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨he,h⟩))
  ·exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨he,h⟩))
  ·exact mem_union_right _ (mem_singleton_self _)
 obtain⟨z,hz,hres⟩:=rF col hcol X hxa hJ hp hx hxp hy hxy (by simp) hKC;obtain⟨Pp,hPp,cp1,cp2⟩:=nW X pf (V:=Vp) (filter_subset _ _) (λe he=>(mem_filter.mp he).2) hz;obtain⟨Pq,hPq,cq1,-⟩:=nW X qf (V:=Vq) (filter_subset _ _) (λe he=>(mem_filter.mp he).2) hxK;obtain⟨g1,hg1,hr1,hx1,hp1⟩:=qW X pf hp.1 hx hxp hy hxy hU;obtain⟨g2,hg2,hr2,hy2,hq2⟩:=qW X qf hq.1 hyK hyq hxK hxy.symm (by rwa[Sym2.eq_swap]);have out:∀{w h:ℕ} {v:Fin n},gN n C w h ->v∈orIn n C h ->v∈orIn n C w:=λhr hv=>aK (aJ hA) hr hv;have d1:Disjoint Pp Pq:=disjoint_left.mpr λh h1 h2=>by
  obtain⟨v,hv⟩:=(hPp h h1).2.2.1;exact hTT v (out (hPp h h1).2.2.2 hv) (out (hPq h h2).2.2.2 hv)
 have g1n:g1∉insert g2 (Pp∪Pq):=by
  simp only[mem_insert,mem_union,not_or];exact⟨λe=>disjoint_left.mp (jX X hK γ) (out hr2 (e▸hx1)) hxK,λh=>disjoint_left.mp (jX X hJ β) hx (out (hPp g1 h).2.2.2 hx1),λh=>hpq (qf p (out (hPq g1 h).2.2.2 hp1)).symm⟩
 have g2n:g2∉Pp∪Pq:=by
  simp only[mem_union,not_or];exact⟨λh=>hpq (pf q (out (hPp g2 h).2.2.2 hq2)),λh=>disjoint_left.mp (jX X hK γ) hyK (out (hPq g2 h).2.2.2 hy2)⟩
 have hX:∀e∈Ustar G C,∃v∈({p,q,x}:Finset (Fin n)),v∈e:=λe he=>by
  rcases mem_union.mp (hcov he)with h|h
  ·rcases mem_union.mp h with h|h
   ·obtain⟨w,-,rfl⟩:=(mem_filter.mp h).2;exact⟨p,by simp,Sym2.mem_mk_left _ _⟩
   ·obtain⟨w,-,rfl⟩:=(mem_filter.mp h).2;exact⟨q,by simp,Sym2.mem_mk_left _ _⟩
  ·rw[mem_singleton.mp h];exact⟨x,by simp,Sym2.mem_mk_left _ _⟩
 refine lL X hKC hX (P:=insert g1 (insert g2 (Pp∪Pq))) (λh hh=>?_) ?_
 ·simp only[mem_insert,mem_union]at hh;rcases hh with rfl|rfl|hh|hh;exacts[⟨hg1,J,hJ,β,hr1⟩,⟨hg2,K,hK,γ,hr2⟩,⟨(hPp h hh).1,J,hJ,_,(hPp h hh).2.2.2⟩,⟨(hPq h hh).1,K,hK,_,(hPq h hh).2.2.2⟩]
 have:=card_sdiff_add_card_inter ({p,q,x}:Finset (Fin n)) Kc;have:=card_le_card (inter_subset_inter_right (u:=Kc) (insert_subset_insert p (singleton_subset_iff.mpr (mem_insert_self q {x}))));have:({p,q,x}:Finset (Fin n)).card≤3:=card_le_three;have:=card_le_card hcov;have:=card_union_le (Vp∪Vq) {s(x,y)};have:=card_union_le Vp Vq;rw[card_singleton]at*;have:=nN hA hxa;rw[card_insert_of_notMem g1n,card_insert_of_notMem g2n,card_union_of_disjoint d1];rcases hres with h|h
 ·have:=cp2 λhm=>h (mem_filter.mp hm).1;omega
 ·omega
end
theorem fL (hR1:cM) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (X:bM G C):False:=by
 classical
 by_cases hHL:∀J∈junk G C,∀β:Fin 2,∃v,bN n G C J β v
 ·obtain⟨j0,hj0⟩:(junk G C).Nonempty:=card_pos.mp (by rw[X.2.2.2.1];omega);obtain⟨v0,-⟩:=hHL j0 hj0 0;have hex:∀(J:ℕ) (β:Fin 2),∃v:Fin n,J∈junk G C ->bN n G C J β v:=λJ β=>if h:J∈junk G C then(hHL J h β).imp λ_ h' _=>h' else⟨v0,λh'=>absurd h' h⟩;choose L hL using hex;exact eT hR1 col hcol X (L:=L) λJ hJ β=>hL J β hJ
 by_cases hnc:∀a∈tops G C,∀j∈junk G C,∀k∈junk G C,k≠j ->∀b:Fin 2,OrReaches n C (opnd C a b) j ->¬OrReaches n C (opnd C a (1-b)) k
 ·exact jR hR1 col hcol X hnc
 push Not at hHL hnc;obtain⟨ax,hax,j,hj,k,hk,hkj,bx,h0,h1⟩:=hnc;have hxa:fG G C ax:=⟨hax,bx,j,hj,k,hk,hkj,h0,h1⟩;obtain⟨J,hJ,β,hβ⟩:=hHL;obtain⟨K,hKJ,hJK⟩:=gC X.2.2.2.1 hJ;have hK:=(jU hJK).2;obtain⟨γ,hγ⟩:∃γ,∀v,¬bN n G C K γ v:=by
  by_contra hL;push Not at hL;obtain⟨x,y,hxy,-,hall,hnu⟩:=rG hR1 col hcol X hJK hKJ hβ;obtain⟨γ,hx,hy⟩:=eE X hK (hall K hK);obtain⟨p,hp⟩:=hL γ;obtain⟨q,hq⟩:=hL (1-γ);have hpf:=cY X hK hp.1 hp.2;have hqf:=cY X hK hq.1 hq.2;rw[dD]at hqf;exact(hnu K hK q hq.2).2 (aQ X.2.2.1 (λe=>(hnu K hK p hp.2).1 e.symm) hxy (hpf y hy) (hqf x hx).symm (hpf q hq.1)).symm
 have sd:∀{i β'},(∀v,¬bN n G C i β' v) ->∀δ v,bN n G C i δ v ->δ=1-β':=λhb δ v hv=>(dC _ δ).resolve_left λe=>hb v (e▸hv);have uq:∀{i δ v w},i∈junk G C ->bN n G C i δ v ->bN n G C i δ w ->v=w:=λhi hv hw=>sK X hi (cY X hi hv.1 hv.2) (cY X hi hw.1 hw.2);have one:∀{J' K' β' γ'},junk G C={J',K'} ->J'∈junk G C ->(∀v,¬bN n G C J' β' v) ->(∀v,¬bN n G C K' γ' v) ->(∀v,¬bN n G C K' (1-γ') v) ->∀p,bN n G C J' (1-β') p ->False:=by
  intro J' K' β' γ' hJK' hJ' hb hc hc' p hp;exact tX col hcol X hxa hJK hJ' hp λi hi δ v hv=>by
   rcases eF hJK' hi with rfl|rfl
   ·obtain rfl:=sd hb δ v hv;exact⟨rfl,rfl,uq hi hv hp⟩
   ·obtain rfl:=sd hc δ v hv;exact absurd hv (hc' v)
 by_cases hp:∃p,bN n G C J (1-β) p<;>by_cases hq:∃q,bN n G C K (1-γ) q
 ·obtain⟨p,hp⟩:=hp;obtain⟨q,hq⟩:=hq;exact tN hR1 col hcol X hxa hJK hKJ hp hq λi hi δ v hv=>by
   rcases eF hJK hi with rfl|rfl
   ·obtain rfl:=sd hβ δ v hv;exact Or.inl ⟨rfl,rfl,uq hi hv hp⟩
   ·obtain rfl:=sd hγ δ v hv;exact Or.inr ⟨rfl,rfl,uq hi hv hq⟩
 ·exact one hJK hJ hβ hγ (λv hv=>hq ⟨v,hv⟩) _ hp.choose_spec
 ·exact one (by rw[hJK,pair_comm]) hK hγ hβ (λv hv=>hp ⟨v,hv⟩) _ hq.choose_spec
 ·exact tO col hcol X hxa hJK λi hi δ v hv=>by
   rcases eF hJK hi with rfl|rfl
   ·exact hp ⟨v,sd hβ δ v hv▸hv⟩
   ·exact hq ⟨v,sd hγ δ v hv▸hv⟩
def gP (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (q r:ℕ):Prop:=IsLeastAO G C/\TopForm G C/\NoFourCycle G/\q<r/\junk G C={q,r}/\(∀k∈junk G C,∀v:Fin n,gateVal n C k (unitInput v)=false)/\∀β:Fin 2,2≤(orIn n C (opnd C q β)).card
def aC (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (k:ℕ) (v:Fin n):Prop:=∃a∈tops G C,∃b:Fin 2,OrReaches n C (opnd C a b) k/\v∈orIn n C (opnd C a (1-b))
def k4 (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (k:ℕ) (w:Fin n):Prop:=∀χ,gateVal n C k χ=true ->χ w=true ->graphFun G ∅ χ=true
def eM (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (w:Fin n):Prop:=∃k∈junk G C,aC n G C k w
lemma bV (β:Fin 2):1-(1-β)=β:=sub_sub_cancel 1 β
lemma aS:∀β β':Fin 2,β'=β\/β'=1-β:=by decide
lemma bB:∀a b c:Bool,a≠c ->b≠c ->a=b:=by decide
lemma dT {u v u' v':Fin n} (h:s(u,v)=s(u',v')):pairInput u v=pairInput u' v':=by
 rcases Sym2.eq_iff.mp h with⟨rfl,rfl⟩|⟨rfl,rfl⟩
 ·rfl
 ·funext w;simp[pairInput,or_comm]
lemma aW {u v w:Fin n} (h:pairInput u v w=true):w=u\/w=v:=by
 simpa[pairInput]using h
lemma j4 (hA:IsAO2 n C) {a k:ℕ} (ha:a∈tops G C) {b:Fin 2} (hr:OrReaches n C (opnd C a b) k) {w:Fin n} (hw:w∈orIn n C (opnd C a (1-b))):k4 n G C k w:=λχ h1 h2=>by
 obtain⟨hal,hop,hb⟩:=aI.mp ha;exact hb χ ((aN hA hal hop b χ).mpr ⟨aO hA χ hr h1,bY hA hw h2⟩)
lemma bH (hA:IsAO2 n C) {k:ℕ} {w:Fin n} (h:aC n G C k w):k4 n G C k w:=let ⟨_,ha,_,hr,hw⟩:=h;j4 hA ha hr hw
lemma g6 (hA:IsAO2 n C) {m:ℕ} (hm:m∈junk G C) (hmin:∀k∈junk G C,∀x,gateVal n C m x=true ->gateVal n C k x=true) {a:ℕ} (ha:a∈tops G C) {b:Fin 2} {k k':ℕ} (hk:k∈junk G C) (hk':k'∈junk G C) (h1:OrReaches n C (opnd C a b) k) (h2:OrReaches n C (opnd C a (1-b)) k'):False:=by
 obtain⟨hal,hop,hb⟩:=aI.mp ha;exact(aA.mp hm).2.2 λx hx=>hb x ((aN hA hal hop b x).mpr ⟨aO hA x h1 (hmin k hk x hx),aO hA x h2 (hmin k' hk' x hx)⟩)
lemma qH (hA:IsAO2 n C) (hT:TopForm G C) {m:ℕ} (hm:m∈junk G C) (hmin:∀k∈junk G C,∀x,gateVal n C m x=true ->gateVal n C k x=true) {a:ℕ} (ha:a∈tops G C) {b:Fin 2} {k:ℕ} (hk:k∈junk G C) (h1:OrReaches n C (opnd C a b) k) {x:Fin n ->Bool} (hx:wireVal n C (opnd C a (1-b)) x=true):∃v∈orIn n C (opnd C a (1-b)),x v=true:=by
 obtain⟨hal,hop,-⟩:=aI.mp ha;rcases (a8 hA hT hal hop (1-b) x).mp hx with h|⟨k',hk',-,h2,-⟩
 ·exact h
 ·exact(g6 hA hm hmin ha hk hk' h1 h2).elim
lemma fI (hA:IsAO2 n C) {j k:ℕ} (hj:j∈junk G C) {w:ℕ} {x:Fin n ->Bool} (h:(∃v∈orIn n C w,x v=true)\/(k≠j/\¬InCone n C j k/\OrReaches n C w k/\gateVal n C k x=true)):wireVal n (aG n C j) w x=true:=by
 have hop:=(aA.mp hj).2.1;rcases h with⟨v,hv,hx⟩|⟨hkj,hjk,hr,hkx⟩
 ·exact b9 hA (bJ j) hop hv hx
 ·refine fB hA (bJ j) hop x hr ?_;rw[eB (bJ j) x (n+k) (by omega) (λ_=>by simpa using hjk)];exact hkx
lemma fW (hC:IsLeastAO G C) (hT:TopForm G C) {j:ℕ} (hj:j∈junk G C) {a:ℕ} (ha:a∈tops G C) {x:Fin n ->Bool} (h:∀b:Fin 2,wireVal n (aG n C j) (opnd C a b) x=true):wireVal n (aG n C j) C.output x=true:=kS hC hT (bJ j) (aA.mp hj).2.1 ha (λe=>(aA.mp hj).2.2 (e▸(aI.mp ha).2.2)) (h 0) (h 1)
lemma lA (hC:IsLeastAO G C) (hT:TopForm G C) {j:ℕ} (hj:j∈junk G C) {u v:Fin n} (hs:s(u,v)∈starEdges G C):wireVal n (aG n C j) C.output (pairInput u v)=true:=by
 simp only[starEdges,mem_biUnion,mem_image,mem_product]at hs;obtain⟨a,ha,⟨u',v'⟩,⟨hu,hv⟩,e⟩:=hs;rw[←dT e]
 exact fW hC hT hj ha λb=>fI hC.1 (k:=j) hj (Or.inl (by
  fin_cases b
  ·exact⟨u',hu,by simp[pairInput]⟩
  ·exact⟨v',hv,by simp[pairInput]⟩))
theorem lR (hC:IsLeastAO G C) (hT:TopForm G C) {m:ℕ} (hm:m∈junk G C) (hmin:∀k∈junk G C,∀x,gateVal n C m x=true ->gateVal n C k x=true) {j:ℕ} (hj:j∈junk G C) {u v:Fin n} (huv:G.Adj u v) (hl:wireVal n (aG n C j) C.output (pairInput u v)=false):∃k∈junk G C,gateVal n C k (pairInput u v)=true/\wireVal n (aG n C j) (n+k) (pairInput u v)=false/\∃w,aC n G C k w/\(w=u\/w=v):=by
 have hA:=hC.1;obtain⟨-,hjop,hjb⟩:=aA.mp hj;have hF:wireVal n C C.output (pairInput u v)=true:=by
  rw[show wireVal n C C.output _=graphFun G ∅ _ from congrFun hC.2.1 _,aT];exact huv
 obtain⟨w,hw,-⟩|⟨a,hop,hr,hx⟩:=(kU hA _ _).mp hF
 ·rw[jK hC]at hw;simp at hw
 have hal:=(aX hr).2;have ha:a∈tops G C:=aI.mpr ⟨hal,hop,eZ hC hr⟩;have hK:fY C (aG n C j) j:=bJ j;obtain⟨b,hb⟩:∃b:Fin 2,wireVal n (aG n C j) (opnd C a b) (pairInput u v)=false:=by
  by_contra hne;simp only[not_exists,Bool.not_eq_false]at hne;rw[fW hC hT hj ha hne]at hl;cases hl
 have hab:=(aN hA hal hop b _).mp hx;rcases (a8 hA hT hal hop b _).mp hab.1 with⟨w,hw,hxw⟩|⟨k,hk,-,hrk,hxk⟩
 ·rw[b9 hA hK hjop hw hxw]at hb;cases hb
 refine⟨k,hk,hxk,?_,?_⟩
 ·by_contra h';rw[fB hA hK hjop _ hrk (by simpa using h')]at hb;cases hb
 ·obtain⟨w,hw,hxw⟩:=qH hA hT hm hmin ha hk hrk hab.2;exact⟨w,⟨a,ha,b,hrk,hw⟩,aW hxw⟩
section X
variable {q r:ℕ}
lemma bK (X:gP G C q r):q∈junk G C/\r∈junk G C:=by
 rw[X.2.2.2.2.1];simp
lemma bP (X:gP G C q r) (β:Fin 2) (x:Fin n ->Bool):gateVal n C q x=true↔(∃a∈orIn n C (opnd C q β),x a=true)/\∃b∈orIn n C (opnd C q (1-β)),x b=true:=by
 obtain⟨hv,-,-,-⟩:=cH X.1.1 X.2.1 (bK X).1 (dF X.2.2.2.1 X.2.2.2.2.1) (X.2.2.2.2.2.1 q (bK X).1);rcases bG β with⟨rfl,h⟩|⟨rfl,h⟩<;>rw[h];exacts[hv x,(hv x).trans and_comm]
lemma cJ (X:gP G C q r) (β:Fin 2):Disjoint (orIn n C (opnd C q β)) (orIn n C (opnd C q (1-β))):=by
 obtain⟨-,-,-,hd⟩:=cH X.1.1 X.2.1 (bK X).1 (dF X.2.2.2.1 X.2.2.2.2.1) (X.2.2.2.2.2.1 q (bK X).1);rcases bG β with⟨rfl,h⟩|⟨rfl,h⟩<;>rw[h];exacts[hd,hd.symm]
lemma f8 (X:gP G C q r) {β:Fin 2} {v:Fin n} (hv:v∈orIn n C (opnd C q β)) (hW:k4 n G C q v):∀t∈orIn n C (opnd C q (1-β)),G.Adj v t:=λt ht=>(aT v t).mp (hW _ ((bP X β _).mpr ⟨⟨v,hv,by simp[pairInput]⟩,t,ht,by simp[pairInput]⟩) (by simp[pairInput]))
lemma u5 (X:gP G C q r) {u v:Fin n} (huv:G.Adj u v) (hx:gateVal n C q (pairInput u v)=true):∃s∈orIn n C (opnd C q 0),∃t∈orIn n C (opnd C q 1),s(u,v)=s(s,t)/\G.Adj s t:=by
 obtain⟨⟨s,hs,hsx⟩,⟨t,ht,htx⟩⟩:=(bP X 0 _).mp hx;have hst:s≠t:=λe=>disjoint_left.mp (cJ X 0) hs (e▸ht);refine⟨s,hs,t,ht,?_⟩;rcases aW hsx with rfl|rfl<;>rcases aW htx with rfl|rfl;exacts[absurd rfl hst,⟨rfl,huv⟩,⟨Sym2.eq_swap,huv.symm⟩,absurd rfl hst]
lemma k7 (X:gP G C q r) {L:Fin 2 ->Fin n} (hL:∀β,L β∈orIn n C (opnd C q β)/\∀t∈orIn n C (opnd C q (1-β)),G.Adj (L β) t) {u v:Fin n} (huv:G.Adj u v) (hx:gateVal n C q (pairInput u v)=true):∃β:Fin 2,∃w∈orIn n C (opnd C q (1-β)),s(u,v)=s(L β,w):=by
 obtain⟨s,hs,t,ht,he,hst⟩:=u5 X huv hx;by_cases h0:s=L 0
 ·exact⟨0,t,ht,h0▸he⟩
 by_cases h1:t=L 1
 ·exact⟨1,s,hs,he.trans (h1▸Sym2.eq_swap)⟩
 exact absurd (aQ X.2.2.1 h0 hst ((hL 0).2 t ht) ((hL 1).2 s hs).symm ((hL 0).2 _ (hL 1).1)) h1
end X
lemma j3 (hA:IsAO2 n C) {h:ℕ} (hJ:bX n C h) (hne:(orIn n C h).Nonempty) (hf:¬aB G (Ustar G C) (orIn n C h)):h∈(orN G C\lam G C).image (n+·):=by
 obtain⟨k,rfl⟩:∃k,h=n+k:=⟨h-n,by have:=hJ.1;omega⟩;obtain⟨hk,hop⟩:=a7.mp hJ;obtain⟨v,hv⟩:=hne;refine mem_image.mpr ⟨k,mem_sdiff.mpr ⟨dS.mpr ⟨hk,hop,λhb=>?_⟩,λhl=>hf (k5 hA hl)⟩,rfl⟩;have:=hb _ (bY hA hv (x:=unitInput v) (by simp[unitInput]));rw[e8]at this;cases this
lemma r6 {ν:Type} {J J':ν ->Prop} {l r:ν ->ν} (hJ:∀x,J x ->J' x) {w h:ν} (hr:aM J l r w h):aM J' l r w h:=by
 induction hr with
 |refl=>exact .refl
 |tail _ hs ih=>exact ih.tail ⟨hJ _ hs.1,hs.2⟩
def b5 (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (V:Finset (Sym2 (Fin n))) (w h:ℕ):Prop:=h∈(orN G C\lam G C).image (n+·)/\¬aB G V (orIn n C h)/\(orIn n C (bF n C h)).Nonempty/\(orIn n C (bI n C h)).Nonempty/\aM (bX n C) (bF n C) (bI n C) w h
lemma fC (hA:IsAO2 n C) {V:Finset (Sym2 (Fin n))} (hV:V⊆Ustar G C) (w:ℕ) (S:Finset (Fin n)) (hsp:∀W,aB G V W ->(W∩S).card≤1):∃P:Finset ℕ,(∀h∈P,b5 n G C V w h)/\(orIn n C w∩S).card≤P.card+1:=by
 classical
 have hD:dB (λh=>bX n C h/\¬aB G V (orIn n C h)) (bF n C) (bI n C) id (orIn n C):=λh hh=>aJ hA h hh.1;obtain⟨P,hP,hc⟩:=cU hD S {w} λ_ _ u _ hu=>by
  by_cases hj:bX n C u
  ·exact hsp _ (by by_contra h;exact hu ⟨hj,h⟩)
  ·exact(card_le_card inter_subset_left).trans (bL hj)
 refine⟨P,λh hh=>?_,by simpa[add_comm]using hc⟩;obtain⟨⟨hj,hf⟩,⟨w',hw',hr⟩,h1,h2⟩:=hP h hh;rw[mem_singleton]at hw';subst hw';obtain⟨x1,hx1,-⟩:=not_subset.mp h1;obtain⟨x2,hx2,-⟩:=not_subset.mp h2
 have hne:(orIn n C h).Nonempty:=⟨x1,by
  rw[(aJ hA h hj).2.2];exact mem_union_left _ (mem_inter.mp hx1).1⟩
 exact⟨j3 hA hj hne λhu=>hf (bT hV subset_rfl hu),hf,⟨x1,(mem_inter.mp hx1).1⟩,⟨x2,(mem_inter.mp hx2).1⟩,r6 (λ_ h=>h.1) hr⟩
lemma mR {V:Finset (Sym2 (Fin n))} {w h:ℕ} (hh:b5 n G C V w h):bX n C h:=by
 obtain⟨k,hk,rfl⟩:=mem_image.mp hh.1;obtain⟨hkl,hop,-⟩:=dS.mp (mem_sdiff.mp hk).1;exact a7.mpr ⟨hkl,hop⟩
lemma gW (hA:IsAO2 n C) {V:Finset (Sym2 (Fin n))} {w h:ℕ} (hh:b5 n G C V w h):(orIn n C h).Nonempty:=by
 obtain⟨v,hv⟩:=hh.2.2.1;exact⟨v,by rw[(aJ hA h (mR hh)).2.2];exact mem_union_left _ hv⟩
lemma kJ (hA:IsAO2 n C) (h4:NoFourCycle G) {w:Fin 2 ->ℕ} {y:Fin 2 ->Fin n} (hd:Disjoint (orIn n C (w 0)) (orIn n C (w 1))) (hy:∀β,y β∈orIn n C (w β)) (hyy:G.Adj (y 0) (y 1)) {V:Finset (Sym2 (Fin n))} (hVU:V⊆Ustar G C) (hVE:∀e∈V,∃β:Fin 2,∃t∈orIn n C (w (1-β)),e=s(y β,t)):∃P:Finset ℕ,(∀h∈P,∃β,b5 n G C V (w β) h)/\V.card≤P.card+1:=by
 classical
 have hE:V⊆G.edgeFinset:=hVU.trans sdiff_subset;obtain⟨P0,hP0,c0⟩:=fC hA hVU (w 1) (insert (y 1) (aE V (y 0))) λW hW=>a4 h4 hE hW _ _ hyy;obtain⟨P1,hP1,c1⟩:=fC hA hVU (w 0) (insert (y 0) (aE V (y 1))) λW hW=>a4 h4 hE hW _ _ hyy.symm;have hdis:Disjoint P0 P1:=disjoint_left.mpr λh h0 h1=>by
  obtain⟨v,hv⟩:=gW hA (hP0 h h0);exact disjoint_left.mp hd (aK (aJ hA) (hP1 h h1).2.2.2.2 hv) (aK (aJ hA) (hP0 h h0).2.2.2.2 hv)
 set S0:=orIn n C (w 1)∩insert (y 1) (aE V (y 0));set S1:=orIn n C (w 0)∩insert (y 0) (aE V (y 1));have hcov:V⊆S0.image (s(y 0,·))∪(S1.erase (y 0)).image (s(y 1,·)):=by
  intro e he;obtain⟨β,t,ht,rfl⟩:=hVE e he;rcases bG β with⟨rfl,h⟩|⟨rfl,h⟩<;>rw[h]at ht
  ·exact mem_union_left _ (mem_image_of_mem _ (mem_inter.mpr ⟨ht,mem_insert_of_mem (aD.mpr he)⟩))
  ·by_cases ht0:t=y 0
   ·subst ht0;exact mem_union_left _ (mem_image.mpr ⟨y 1,mem_inter.mpr ⟨hy 1,mem_insert_self _ _⟩,Sym2.eq_swap⟩)
   ·exact mem_union_right _ (mem_image_of_mem _ (mem_erase.mpr ⟨ht0,mem_inter.mpr ⟨ht,mem_insert_of_mem (aD.mpr he)⟩⟩))
 have hm:y 0∈S1:=mem_inter.mpr ⟨hy 0,mem_insert_self _ _⟩;have:=(card_le_card hcov).trans ((card_union_le _ _).trans (add_le_add card_image_le card_image_le));rw[card_erase_of_mem hm]at this;have:=card_pos.mpr ⟨_,hm⟩;refine⟨P0∪P1,λh hh=>(mem_union.mp hh).elim (λh0=>⟨1,hP0 h h0⟩) (λh1=>⟨0,hP1 h h1⟩),?_⟩;rw[card_union_of_disjoint hdis];omega
lemma dH (hA:IsAO2 n C) {k i:ℕ} (hk:k<C.gates.length) (hi:i∈(gateAt C k).inputs):i<n+k:=by
 rw[bO (bZ.mp hA).1 hk]at hi;simp only[List.mem_cons,List.not_mem_nil,or_false]at hi;rcases hi with rfl|rfl;exacts[aH hA hk 0,aH hA hk 1]
lemma gQ {k:ℕ}:∀{w:ℕ},OrReaches n C w k ->w≠n+k ->∃h<C.gates.length,(gateAt C h).op=GateOp.or/\n+k∈(gateAt C h).inputs/\OrReaches n C w h:=by
 intro w
 induction w using Nat.strong_induction_on with
 |_ w ih=>
  intro hr hne;obtain⟨j,rfl⟩:∃j,w=n+j:=⟨w-n,by have:=hr.1;omega⟩;obtain⟨hj,rfl|⟨hop,i,hi,hlt,hri⟩⟩:=bD.mp hr
  ·exact absurd rfl hne
  by_cases hik:i=n+k
  ·exact⟨j,hj,hop,hik▸hi,bD.mpr ⟨hj,Or.inl rfl⟩⟩
  obtain⟨h,hh,h1,h2,h3⟩:=ih i hlt hri hik;exact⟨h,hh,h1,h2,bD.mpr ⟨hj,Or.inr ⟨hop,i,hi,hlt,h3⟩⟩⟩
def c6 (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (q r:ℕ):Prop:=gP G C q r/\∀β:Fin 2,OrReaches n C (opnd C r β) q
section F2
variable {q r:ℕ}
lemma lJ (Y:c6 G C q r) (β:Fin 2) (x:Fin n ->Bool):gateVal n C r x=true↔(gateVal n C q x=true\/∃c∈orIn n C (opnd C r β),x c=true)/\(gateVal n C q x=true\/∃d∈orIn n C (opnd C r (1-β)),x d=true):=by
 have h:=(gE Y.1.1.1 Y.1.2.1 Y.1.2.2.2.1 Y.1.2.2.2.2.1 Y.1.2.2.2.2.2.1 (Y.2 0) (Y.2 1)).1 x;rcases bG β with⟨rfl,e⟩|⟨rfl,e⟩<;>rw[e];exacts[h,h.trans and_comm]
lemma jZ (Y:c6 G C q r) (β:Fin 2):Disjoint (orIn n C (opnd C r β)) (orIn n C (opnd C r (1-β))):=by
 have h:=(gE Y.1.1.1 Y.1.2.1 Y.1.2.2.2.1 Y.1.2.2.2.2.1 Y.1.2.2.2.2.2.1 (Y.2 0) (Y.2 1)).2;rcases bG β with⟨rfl,e⟩|⟨rfl,e⟩<;>rw[e];exacts[h,h.symm]
lemma eK (Y:c6 G C q r):∀k∈junk G C,∀x,gateVal n C q x=true ->gateVal n C k x=true:=λk hk x hx=>by
 rw[Y.1.2.2.2.2.1,mem_insert,mem_singleton]at hk;rcases hk with rfl|rfl;exacts[hx,(lJ Y 0 x).mpr ⟨Or.inl hx,Or.inl hx⟩]
lemma k6 (Y:c6 G C q r) (β:Fin 2):(orIn n C (opnd C r β)).Nonempty:=by
 by_contra he;rw[not_nonempty_iff_eq_empty]at he;have hr:=(bK Y.1).2;refine d3 Y.1.1 (aA.mp hr).1 (w:=n+q) (by have:=Y.1.2.2.2.1;omega) λx=>?_;rw[Bool.eq_iff_iff];show gateVal n C r x=true↔gateVal n C q x=true;rw[lJ Y β,he];simp only[notMem_empty,false_and,exists_false,or_false];exact⟨λh=>h.1,λh=>⟨h,Or.inl h⟩⟩
lemma tL (Y:c6 G C q r):2≤(readers n C q).card:=by
 obtain⟨hC,hT,-,hqr,hJ,-,-⟩:=Y.1;have hA:=hC.1;have hr:=(bK Y.1).2;have hrl:=(aA.mp hr).1;have hql:q<C.gates.length:=by omega
 have hqop:=(aA.mp (bK Y.1).1).2.1;have hne:∀β,opnd C r β≠n+q:=λβ he=>by
  have:=k6 Y β;rw[he,b6 (λ_=>by rw[hqop];simp)]at this;simp at this
 choose h hh hop hin hrh using λβ=>gQ (Y.2 β) (hne β);have hmem:∀β,h β∈readers n C q:=λβ=>by simp[readers,hh β,hin β]
 by_cases e:h 0=h 1
 ·exfalso
  have hz:orIn n C (n+h 0)=∅:=eq_empty_of_forall_notMem λv hv=>disjoint_left.mp (jZ Y 0) (a6 hA (hrh 0) hv) (by
    rw[e]at hv;exact a6 hA (hrh 1) hv)
  refine d3 hC (hh 0) (w:=n+q) (by have:=dH hA (hh 0) (hin 0);omega) λx=>?_;rw[Bool.eq_iff_iff];constructor
  ·intro h1;rcases (kU hA x _).mp h1 with⟨v,hv,-⟩|⟨k,hk,hrk,hkx⟩
   ·rw[hz]at hv;simp at hv
   ·have hc:=bU hA hrl 0 (cG hA (hrh 0) hrk);have:=d4 hT hrl hk (aA.mp hr).2.1 hc;rw[hJ,mem_insert,mem_singleton]at this;rcases this with rfl|rfl
    ·exact hkx
    ·exact absurd (aP hc) (lt_irrefl _)
  ·exact λh1=>aO hA x (bD.mpr ⟨hh 0,Or.inr ⟨hop 0,n+q,hin 0,dH hA (hh 0) (hin 0),bD.mpr ⟨hql,Or.inl rfl⟩⟩⟩) h1
 ·rw[←card_pair e];exact card_le_card λx hx=>by
   rcases mem_insert.mp hx with rfl|hx
   ·exact hmem 0
   ·rw[mem_singleton.mp hx];exact hmem 1
theorem rP (Y:c6 G C q r) (β:Fin 2) {p:Fin n} (hp:p∈orIn n C (opnd C q (1-β))) (hpf:∀t∈orIn n C (opnd C q β),G.Adj p t) (hacc:∀u v,G.Adj u v ->wireVal n (aG n C q) C.output (pairInput u v)=true\/p∈s(u,v)/\∃t∈orIn n C (opnd C q β),t∈s(u,v)):False:=by
 have hC:=Y.1.1;have hql:=(aA.mp (bK Y.1).1).1;have hv:∀x,GateOp.and.eval [wireVal n C (opnd C q β) x,wireVal n C p x]=true↔(∃t∈orIn n C (opnd C q β),x t=true)/\x p=true:=λx=>by
  simp only[GateOp.eval,List.all_cons,List.all_nil,id,Bool.and_true,Bool.and_eq_true,bA,eI hC.1 Y.1.2.1 (bK Y.1).1 (dF Y.1.2.2.2.1 Y.1.2.2.2.2.1)]
 have ha:=aH hC.1 hql β;have hb:p.1<n+q:=by have:=p.2;omega
 have hcl:∀x,GateOp.and.eval [wireVal n C (opnd C q β) x,wireVal n C p x]=true ->graphFun G ∅ x=true:=λx hx=>by
  obtain⟨⟨t,ht,hxt⟩,hxp⟩:=(hv x).mp hx;exact(dJ x).mpr ⟨p,t,hpf t ht,hxp,hxt⟩
 obtain⟨hD,-,-⟩:=cT hC hql (Or.inl rfl) ha hb (λx hx=>by
  obtain⟨⟨t,ht,hxt⟩,hxp⟩:=(hv x).mp hx
  exact(bP Y.1 β x).mpr ⟨⟨t,ht,hxt⟩,p,hp,hxp⟩) λu v huv=>
  (hacc u v huv).imp id λ⟨h1,t,ht,h2⟩=>(hv _).mpr ⟨⟨t,ht,by
   rcases Sym2.mem_iff.mp h2 with rfl|rfl<;>simp[pairInput]⟩,by
   rcases Sym2.mem_iff.mp h1 with rfl|rfl<;>simp[pairInput]⟩
 have hsp:=b7 hC.1 hql (Or.inl rfl) ha hb;have hlen:=(cV (C:=C) q ⟨GateOp.and,[opnd C q β,p.1]⟩).1
 have h1:=eC hD (i:=q) (by rw[hlen];exact hql) λx hx=>hcl x (by
  rw[show gateVal n _ q x=wireVal n _ (n+q) x from rfl,(hsp x).2.2.2.2.2]at hx;exact hx)
 have he:readers n (aL C q ⟨GateOp.and,[opnd C q β,p.1]⟩) q=readers n C q:=by
  ext k;simp only[readers,mem_filter,mem_range,hlen];refine and_congr_right λhk=>?_;by_cases hkq:k=q
  ·subst hkq;rw[show gateAt (aL C k _) k=_ from bR hk,Function.update_self];simp only[List.mem_cons,List.not_mem_nil,or_false];refine⟨by omega,λh=>?_⟩;have:=dH hC.1 hk h;omega
  ·rw[(cV q _).2 k hk hkq]
 have:=tL Y;rw[he]at h1;omega
lemma qE (Y:c6 G C q r) {u v:Fin n} (huv:G.Adj u v) (hl:wireVal n (aG n C q) C.output (pairInput u v)=false):gateVal n C q (pairInput u v)=true/\∃w,(aC n G C q w\/aC n G C r w)/\(w=u\/w=v):=by
 obtain⟨hC,hT,-,hqr,hJ,-,-⟩:=Y.1;obtain⟨hq,hr⟩:=bK Y.1;obtain⟨k,hk,hkx,hkk,w,hw,hwe⟩:=lR hC hT hq (eK Y) hq huv hl;rw[hJ,mem_insert,mem_singleton]at hk;rcases hk with rfl|rfl
 ·exact⟨hkx,w,Or.inl hw,hwe⟩
 refine⟨by_contra λhq'=>?_,w,Or.inr hw,hwe⟩;obtain⟨h0|⟨c,hc,hcx⟩,h1|⟨d,hd,hdx⟩⟩:=(lJ Y 0 _).mp hkx
 ·exact hq' h0
 ·exact hq' h0
 ·exact hq' h1
 obtain⟨hrl,hrop,-⟩:=aA.mp hr;rw[fV hC.1 (bJ q) hrl (by omega) hrop,fI hC.1 (k:=q) hq (Or.inl ⟨c,hc,hcx⟩),fI hC.1 (w:=opnd C k 1) (k:=q) hq (Or.inl ⟨d,hd,hdx⟩)]at hkk;cases hkk
lemma uP (Y:c6 G C q r) {w:Fin n} (h:aC n G C q w\/aC n G C r w):k4 n G C q w:=by
 rcases h with h|h
 ·exact bH Y.1.1.1 h
 ·exact λχ h1 h2=>bH Y.1.1.1 h χ ((eK Y) r (bK Y.1).2 χ h1) h2
lemma g0 (Y:c6 G C q r) {β:Fin 2} {v:Fin n} (hv:v∈orIn n C (opnd C q β)) (hu:aC n G C q v\/aC n G C r v):∀t∈orIn n C (opnd C q (1-β)),G.Adj v t:=f8 Y.1 hv (uP Y hu)
lemma qC (Y:c6 G C q r) {β:Fin 2} {v w:Fin n} (hv:v∈orIn n C (opnd C q β)) (hw:w∈orIn n C (opnd C q β)) (hu:aC n G C q v\/aC n G C r v) (hu':aC n G C q w\/aC n G C r w):v=w:=bC Y.1.2.2.1 (Y.1.2.2.2.2.2.2 _) (g0 Y hv hu) (g0 Y hw hu')
lemma l8 (X:gP G C q r) (β:Fin 2) {u v w:Fin n} (hx:gateVal n C q (pairInput u v)=true) (hw:w=u\/w=v):w∈orIn n C (opnd C q β)\/w∈orIn n C (opnd C q (1-β)):=by
 obtain⟨⟨a,ha,hax⟩,⟨b,hb,hbx⟩⟩:=(bP X β _).mp hx;have hab:a≠b:=λe=>disjoint_left.mp (cJ X β) ha (e▸hb);rcases aW hax with rfl|rfl<;>rcases aW hbx with rfl|rfl<;>rcases hw with rfl|rfl
 all_goals first|exact absurd rfl hab|exact Or.inl ha|exact Or.inr hb
lemma fP {u v w b:Fin n} (hw:w=u\/w=v) (hb:b=u\/b=v) (hwb:w≠b):s(u,v)=s(w,b):=by
 rcases hw with rfl|rfl<;>rcases hb with rfl|rfl;exacts[absurd rfl hwb,rfl,Sym2.eq_swap,absurd rfl hwb]
lemma sW (Y:c6 G C q r) (β:Fin 2):∃v∈orIn n C (opnd C q β),aC n G C q v\/aC n G C r v:=by
 have hC:=Y.1.1;have hql:=(aA.mp (bK Y.1).1).1;by_contra hno;have hno':∀w,(aC n G C q w\/aC n G C r w) ->∀u v,G.Adj u v ->gateVal n C q (pairInput u v)=true ->(w=u\/w=v) ->w∈orIn n C (opnd C q (1-β)):=λw hw u v _ hx hwe=>(l8 Y.1 β hx hwe).resolve_left λh=>hno ⟨w,h,hw⟩;by_cases h':∃p∈orIn n C (opnd C q (1-β)),aC n G C q p\/aC n G C r p
 ·obtain⟨p,hp,hpu⟩:=h';have hpf:=g0 Y hp hpu;rw[bV]at hpf;refine rP Y β hp hpf λu v huv=>?_;cases hk:wireVal n (aG n C q) C.output (pairInput u v)
  ·obtain⟨hx,w,hw,hwe⟩:=qE Y huv hk;obtain rfl:=qC Y (hno' w hw u v huv hx hwe) hp hw hpu;obtain⟨⟨t,ht,htx⟩,-⟩:=(bP Y.1 β _).mp hx
   exact Or.inr ⟨by rcases hwe with rfl|rfl<;>simp,t,ht,by
    rcases aW htx with rfl|rfl<;>simp⟩
  ·exact Or.inl rfl
 ·exact jJ hC hql λu v huv=>by
   by_contra hk;obtain⟨hx,w,hw,hwe⟩:=qE Y huv (by simpa using hk);exact h' ⟨w,hno' w hw u v huv hx hwe,hw⟩
lemma tC (Y:c6 G C q r) {L:Fin 2 ->Fin n} (hL:∀β,L β∈orIn n C (opnd C q β)/\(aC n G C q (L β)\/aC n G C r (L β))) {β:Fin 2} {t:Fin n} (hT:orIn n C (opnd C q (1-β))={L (1-β),t}):wireVal n (aG n C q) C.output (pairInput (L β) t)=false:=by
 have hC:=Y.1.1;have hql:=(aA.mp (bK Y.1).1).1;have hpf:=g0 Y (hL (1-β)).1 (hL (1-β)).2;rw[bV]at hpf;by_contra hacc;refine rP Y β (hL (1-β)).1 hpf λu v huv=>?_;cases hk:wireVal n (aG n C q) C.output (pairInput u v)
 swap
 ·exact Or.inl rfl
 right;obtain⟨hx,w,hw,hwe⟩:=qE Y huv hk;obtain⟨⟨s,hs,hsx⟩,⟨b,hb,hbx⟩⟩:=(bP Y.1 β _).mp hx;refine⟨by_contra λhp=>?_,s,hs,by rcases aW hsx with rfl|rfl<;>simp⟩
 replace hp:pairInput u v (L (1-β))≠true:=λh=>hp (by
  rcases aW h with h|h<;>simp[h])
 have hbt:b=t:=by
  rw[hT,mem_insert,mem_singleton]at hb;exact hb.resolve_left λe=>hp (by rw[←e];simpa using hbx)
 rcases l8 Y.1 β hx hwe with hw1|hw1
 ·obtain rfl:=qC Y hw1 (hL β).1 hw (hL β).2;have:=fP hwe (aW hbx) λe=>disjoint_left.mp (cJ Y.1 β) hw1 (e▸hb);rw[dT this,hbt]at hk;exact hacc (by simpa using hk)
 ·obtain rfl:=qC Y hw1 (hL (1-β)).1 hw (hL (1-β)).2;exact hp (by rcases hwe with rfl|rfl<;>simp[pairInput])
lemma uT (Y:c6 G C q r) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) {L:Fin 2 ->Fin n} (hL:∀β,L β∈orIn n C (opnd C q β)/\(aC n G C q (L β)\/aC n G C r (L β))) {β:Fin 2} {a:ℕ} (ha:a∈tops G C) {b:Fin 2} {k:ℕ} (hk:k∈junk G C) (hr:OrReaches n C (opnd C a b) k) (hv:L β∈orIn n C (opnd C a (1-b))) (hne:(orIn n C (opnd C a b)).Nonempty):orIn n C (opnd C a (1-b))={L β}:=by
 obtain⟨hC,hT,h4,-,-,-,hW⟩:=Y.1;refine eq_singleton_iff_unique_mem.mpr ⟨hv,λw hw=>by_contra λhwv=>?_⟩;obtain⟨y0,hy0⟩:=hne;have h1:=aV hC.1 ha b hv hy0;have h2:=(aV hC.1 ha b hw hy0).1;have hF:∀β',∀t∈orIn n C (opnd C q (1-β')),G.Adj (L β') t:=λβ'=>g0 Y (hL β').1 (hL β').2;have hF':∀t∈orIn n C (opnd C q β),G.Adj (L (1-β)) t:=by
  have:=hF (1-β);rwa[bV]at this
 have hwW:k4 n G C q w:=λχ h3 h5=>j4 hC.1 ha hr hw χ (eK Y k hk χ h3) h5;have hcw:col w=col (L β):=bB _ _ _ (hcol _ _ h2) (hcol _ _ h1.1);obtain⟨s,hs,hsL⟩:=exists_mem_ne (hW β) (L β);have hcs:col s=col (L β):=bB _ _ _ (hcol _ _ (hF' s hs)).symm (hcol _ _ (hF' _ (hL β).1)).symm;have key:∀t∈orIn n C (opnd C q (1-β)),t≠L (1-β) ->G.Adj w t:=by
  intro t ht htx;have hst:¬G.Adj s t:=λh=>htx (aQ h4 hsL h (hF β t ht) (hF' s hs).symm (hF β _ (hL _).1));have hsw:¬G.Adj s w:=λh=>hcol s w h (hcs.trans hcw.symm);obtain⟨u,v,huv,hu,hv⟩:=(dJ _).mp (hwW (λz=>decide (z=s\/z=t\/z=w)) ((bP Y.1 β _).mpr ⟨⟨s,hs,by simp⟩,t,ht,by simp⟩) (by simp));simp only[decide_eq_true_eq]at hu hv;rcases hu with rfl|rfl|rfl<;>rcases hv with rfl|rfl|rfl<;>
  first
  |exact(G.irrefl huv).elim
  |exact absurd huv hst
  |exact absurd huv.symm hst
  |exact absurd huv hsw
  |exact absurd huv.symm hsw
  |exact huv
  |exact huv.symm
 obtain⟨t0,ht0,ht0x⟩:=exists_mem_ne (hW (1-β)) (L (1-β));have hy:y0=t0:=aQ h4 hwv h2 h1.1 (key t0 ht0 ht0x) (hF β t0 ht0);have hT2:orIn n C (opnd C q (1-β))={L (1-β),t0}:=by
  ext t;simp only[mem_insert,mem_singleton];exact⟨λht=>or_iff_not_imp_left.mpr λhtx=>aQ h4 hwv (key t ht htx) (hF β t ht) (key t0 ht0 ht0x) (hF β t0 ht0),λh=>h.elim (·▸(hL _).1) (·▸ht0)⟩
 have:=tC Y hL hT2;rw[←hy,lA hC hT (bK Y.1).1 h1.2]at this;cases this
lemma sN (Y:c6 G C q r) {u v:Fin n} (he:s(u,v)∈Ustar G C):gateVal n C q (pairInput u v)=true\/∃β:Fin 2,∃c∈orIn n C (opnd C r β),∃d∈orIn n C (opnd C r (1-β)),s(u,v)=s(c,d)/\aC n G C r c:=by
 obtain⟨hC,hT,-,-,hJ,-,-⟩:=Y.1;obtain⟨a,ha,hax,b,k,hk,-,hr,hkx⟩:=fD hC hT he;obtain⟨hal,hop,-⟩:=aI.mp ha;obtain⟨w,hw,hwx⟩:=qH hC.1 hT (bK Y.1).1 (eK Y) ha hk hr ((aN hC.1 hal hop b _).mp hax).2;by_cases hq:gateVal n C q (pairInput u v)=true
 ·exact Or.inl hq
 right;rw[hJ,mem_insert,mem_singleton]at hk;rcases hk with rfl|rfl
 ·exact absurd hkx hq
 obtain⟨h0|⟨c,hc,hcx⟩,h1|⟨d,hd,hdx⟩⟩:=(lJ Y 0 _).mp hkx
 ·exact absurd h0 hq
 ·exact absurd h0 hq
 ·exact absurd h1 hq
 have hcd:c≠d:=λe=>disjoint_left.mp (jZ Y 0) hc (e▸hd);have hU:aC n G C k w:=⟨a,ha,b,hr,hw⟩;rcases aW hwx with rfl|rfl<;>rcases aW hcx with h3|h3<;>rcases aW hdx with h5|h5<;>subst h3 h5
 all_goals first
  |exact absurd rfl hcd
  |exact⟨0,_,hc,_,hd,rfl,hU⟩
  |exact⟨0,_,hc,_,hd,Sym2.eq_swap,hU⟩
  |exact⟨1,_,hd,_,hc,rfl,hU⟩
  |exact⟨1,_,hd,_,hc,Sym2.eq_swap,hU⟩
lemma r9 (Y:c6 G C q r):∃a∈tops G C,∃b:Fin 2,OrReaches n C (opnd C a b) r:=by
 obtain⟨hC,hT,-,hqr,hJ,-,-⟩:=Y.1;obtain⟨hq,hr⟩:=bK Y.1;by_contra hno;refine jJ hC (aA.mp hr).1 λu v huv=>by_contra λhk=>?_;obtain⟨k,hk',hkx,hkk,w,⟨a,ha,b,hra,-⟩,-⟩:=lR hC hT hq (eK Y) hr huv (by simpa using hk);rw[hJ,mem_insert,mem_singleton]at hk';rcases hk' with rfl|rfl
 ·rw[eB (bJ r) _ (n+k) (by omega) (λ_=>by simpa using λhc=>absurd (aP hc) (by omega))]at hkk;rw[show gateVal n C k _=wireVal n C (n+k) _ from rfl,hkk]at hkx;cases hkx
 ·exact hno ⟨a,ha,b,hra⟩
lemma t6 (Y:c6 G C q r) {V:Finset (Sym2 (Fin n))} (hV:∀e∈V,∃β:Fin 2,∃c∈orIn n C (opnd C r β),∃d∈orIn n C (opnd C r (1-β)),e=s(c,d)/\aC n G C r c) (hne:V.Nonempty):∃y:Fin 2 ->Fin n,(∀β,y β∈orIn n C (opnd C r β))/\G.Adj (y 0) (y 1)/\(∀e∈V,∃β:Fin 2,∃t∈orIn n C (opnd C r (1-β)),e=s(y β,t))/\((∃v,∀e∈V,v∈e)\/∀β,∀t∈orIn n C (opnd C r β),G.Adj (y (1-β)) t):=by
 have h4:=Y.1.2.2.1;have gl:∀β,∀c∈orIn n C (opnd C r β),aC n G C r c ->∀d∈orIn n C (opnd C r (1-β)),G.Adj c d:=λβ c hc hu d hd=>(aT c d).mp (bH Y.1.1.1 hu _ ((lJ Y β _).mpr ⟨Or.inr ⟨c,hc,by simp[pairInput]⟩,Or.inr ⟨d,hd,by simp[pairInput]⟩⟩) (by simp[pairInput]));have uq:∀β,2≤(orIn n C (opnd C r (1-β))).card ->∀c∈orIn n C (opnd C r β),∀c'∈orIn n C (opnd C r β),aC n G C r c ->aC n G C r c' ->c=c':=λβ h2 c hc c' hc' hu hu'=>bC h4 h2 (gl β c hc hu) (gl β c' hc' hu');have hy:∀β:Fin 2,∃y∈orIn n C (opnd C r β),(∃c∈orIn n C (opnd C r β),aC n G C r c) ->aC n G C r y:=λβ=>by
  by_cases h:∃c∈orIn n C (opnd C r β),aC n G C r c
  ·obtain⟨c,hc,hu⟩:=h;exact⟨c,hc,λ_=>hu⟩
  ·obtain⟨y,hy⟩:=k6 Y β;exact⟨y,hy,λh'=>absurd h' h⟩
 choose y hy hyu using hy;have one:∀β,(orIn n C (opnd C r β)).card<2 ->∀c∈orIn n C (opnd C r β),c=y β:=λβ h c hc=>card_le_one.mp (by omega) c hc _ (hy β);have form:∀e∈V,∃β:Fin 2,∃t∈orIn n C (opnd C r (1-β)),e=s(y β,t):=by
  intro e he;obtain⟨β,c,hc,d,hd,rfl,hu⟩:=hV e he;by_cases h2:2≤(orIn n C (opnd C r (1-β))).card
  ·exact⟨β,d,hd,by rw[uq β h2 c hc _ (hy β) hu (hyu β ⟨c,hc,hu⟩)]⟩
  ·refine⟨1-β,c,by rwa[bV],?_⟩;rw[one _ (by omega) d hd,Sym2.eq_swap]
 obtain⟨e0,he0⟩:=hne;obtain⟨β0,c0,hc0,-,-,-,hu0⟩:=hV e0 he0;have hadj:=gl β0 _ (hy β0) (hyu β0 ⟨c0,hc0,hu0⟩) _ (hy (1-β0));have hyy:G.Adj (y 0) (y 1):=by
  rcases bG β0 with⟨rfl,h⟩|⟨rfl,h⟩<;>rw[h]at hadj;exacts[hadj,hadj.symm]
 refine⟨y,hy,hyy,form,?_⟩;by_cases hall:∀β,aC n G C r (y β)/\2≤(orIn n C (opnd C r β)).card
 ·right;intro β t ht;have:=gl (1-β) _ (hy _) (hall _).1 t;rw[bV]at this;exact this ht
 left;simp only[not_forall,not_and,not_le]at hall;obtain⟨β,hβ⟩:=hall;by_cases h2:2≤(orIn n C (opnd C r β)).card
 ·refine⟨y (1-β),λe he=>?_⟩;obtain⟨β',c,hc,d,hd,rfl,hu⟩:=hV e he;rcases aS β β' with rfl|rfl
  ·have:=hβ (hyu _ ⟨c,hc,hu⟩);omega
  ·rw[uq _ (by rwa[bV]) c hc _ (hy _) hu (hyu _ ⟨c,hc,hu⟩)];exact Sym2.mem_mk_left _ _
 ·refine⟨y β,λe he=>?_⟩;obtain⟨β',c,hc,d,hd,rfl,-⟩:=hV e he;rcases aS β β' with rfl|rfl
  ·rw[one _ (by omega) c hc];exact Sym2.mem_mk_left _ _
  ·rw[bV]at hd;rw[one _ (by omega) d hd];exact Sym2.mem_mk_right _ _
end F2
def aR (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (h:ℕ):Prop:=bX n C h/\(∃J∈junk G C,OrReaches n C h J)/\(orIn n C (bF n C h)=∅\/orIn n C (bI n C h)=∅)
lemma dR (hA:IsAO2 n C) {w J:ℕ} (hJ:J∈junk G C) (hr:OrReaches n C w J) (hne:(orIn n C w).Nonempty):∃m,aR n G C (n+m)/\m<C.gates.length/\OrReaches n C w m/\OrReaches n C (n+m) J/\(orIn n C (n+m)).Nonempty:=by
 obtain⟨m,b,hm,hop,hwm,hne',he,hrJ⟩:=fE hA (aA.mp hJ).2.1 hr hne;have:=d9 hA hm hop b hrJ;refine⟨m,⟨a7.mpr ⟨hm,hop⟩,⟨J,hJ,this⟩,?_⟩,hm,hwm,this,hne'⟩;simp only[bF,bI,Nat.add_sub_cancel_left];fin_cases b;exacts[Or.inl he,Or.inr he]
lemma g7 (hA:IsAO2 n C) {h:ℕ} (hM:aR n G C h):h∈(orN G C\lam G C).image (n+·):=by
 obtain⟨hJ,⟨J,hJJ,hr⟩,he⟩:=hM;obtain⟨k,rfl⟩:∃k,h=n+k:=⟨h-n,by have:=hJ.1;omega⟩;obtain⟨hk,hop⟩:=a7.mp hJ;simp only[bF,bI,Nat.add_sub_cancel_left]at he;exact mem_image.mpr ⟨k,he.elim (f0 hA hk hop hJJ hr) (f0 hA hk hop hJJ hr),rfl⟩
lemma gZ {V:Finset (Sym2 (Fin n))} {w h:ℕ} (hM:aR n G C h) (hc:b5 n G C V w h):False:=by
 rcases hM.2.2 with e|e
 ·exact hc.2.2.1.ne_empty e
 ·exact hc.2.2.2.1.ne_empty e
theorem qZ (hA:IsAO2 n C) (h4:NoFourCycle G) (Q:ℕ ->Fin 2 ->Fin n ->Prop):∃K:Finset (Fin n),K.card≤(tops G C\centreless G C).card/\(∀e∈starEdges G C,∃v∈K,v∈e)/\∀a∈tops G C\centreless G C,∃b:Fin 2,∃p∈K,side C a (1-b)={p}/\((∃b':Fin 2,∃p',side C a (1-b')={p'}/\Q a b' p') ->Q a b p):=by
 classical
 have hsel:∀a:{a//a∈tops G C\centreless G C},∃b:Fin 2,∃p:Fin n,side C a.1 (1-b)={p}/\((∃b':Fin 2,∃p',side C a.1 (1-b')={p'}/\Q a.1 b' p') ->Q a.1 b p):=by
  intro a;by_cases hp:∃b':Fin 2,∃p',side C a.1 (1-b')={p'}/\Q a.1 b' p'
  ·obtain⟨b',p',h1,h2⟩:=hp;exact⟨b',p',h1,λ_=>h2⟩
  ·obtain⟨b,c,hc⟩:=(fU hA h4 a.2).2.2.2;exact⟨b,c,hc,λh=>absurd h hp⟩
 choose bs cen hcen using hsel;refine⟨univ.image cen,card_image_le.trans (by simp),λe he=>?_,λa ha=>⟨bs ⟨a,ha⟩,cen ⟨a,ha⟩,mem_image_of_mem _ (mem_univ _),hcen ⟨a,ha⟩⟩⟩;simp only[starEdges,mem_biUnion,mem_image,mem_product]at he;obtain⟨a,ha,⟨u,v⟩,⟨hu,hv⟩,rfl⟩:=he;have hc:=(hcen ⟨a,bW ha hu hv⟩).1;refine⟨_,mem_image_of_mem _ (mem_univ ⟨a,bW ha hu hv⟩),?_⟩
 generalize bs ⟨a,bW ha hu hv⟩=b at hc
 fin_cases b
 ·have hc':side C a 1={cen ⟨a,bW ha hu hv⟩}:=hc;simp[←mem_singleton.mp (hc'▸hv)]
 ·have hc':side C a 0={cen ⟨a,bW ha hu hv⟩}:=hc;simp[←mem_singleton.mp (hc'▸hu)]
lemma c7 {a:ℕ} (ha:a∈tops G C) {b:Fin 2} (he:orIn n C (opnd C a b)=∅):a∈centreless G C:=mem_filter.mpr ⟨ha,by fin_cases b;exacts[Or.inl he,Or.inr he]⟩
lemma jO {a:ℕ} (ha:a∈tops G C) {b:Fin 2} (h1:(orIn n C (opnd C a b)).Nonempty) (h2:(orIn n C (opnd C a (1-b))).Nonempty):a∈tops G C\centreless G C:=by
 obtain⟨u,hu⟩:=h1;obtain⟨v,hv⟩:=h2;rcases bG b with⟨rfl,h⟩|⟨rfl,h⟩<;>rw[h]at hv;exacts[bW ha hu hv,bW ha hv hu]
lemma tP {q r:ℕ} (Y:c6 G C q r) {V:Finset (Sym2 (Fin n))} (hVU:V⊆Ustar G C) (hV:∀e∈V,∃β:Fin 2,∃c∈orIn n C (opnd C r β),∃d∈orIn n C (opnd C r (1-β)),e=s(c,d)/\aC n G C r c):∃P:Finset ℕ,∃Xg:Finset (Fin n),(∀h∈P,∃β,b5 n G C V (opnd C r β) h)/\V.card≤P.card+1/\(∀e∈V,∃v∈Xg,v∈e)/\Xg.card≤2/\(2≤Xg.card ->∀β,∃y,∀t∈orIn n C (opnd C r β),G.Adj y t):=by
 classical
 rcases V.eq_empty_or_nonempty with rfl|hne
 ·exact⟨∅,∅,by simp,by simp,by simp,by simp,by simp⟩
 obtain⟨y,hy,hyy,form,hc⟩:=t6 Y hV hne;obtain⟨P,hP,cP⟩:=kJ Y.1.1.1 Y.1.2.2.1 (w:=λβ=>opnd C r β) (y:=y) (jZ Y 0) hy hyy hVU form;rcases hc with⟨v,hv⟩|hall
 ·exact⟨P,{v},hP,cP,λe he=>⟨v,mem_singleton_self _,hv e he⟩,by simp,by simp⟩
 refine⟨P,{y 0,y 1},hP,cP,λe he=>?_,card_le_two,λ_ β=>⟨_,hall β⟩⟩;obtain⟨β,t,-,rfl⟩:=form e he;exact⟨y β,by fin_cases β<;>simp,Sym2.mem_mk_left _ _⟩
theorem gI (hR1:cM) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (h4:NoFourCycle G) (hC:IsLeastAO G C) (hT:TopForm G C) (q r:ℕ) (hqr:q<r) (hJ:junk G C={q,r}) (hoff:∀k∈junk G C,∀v:Fin n,gateVal n C k (unitInput v)=false) (hW:2≤(orIn n C (opnd C q 0)).card/\2≤(orIn n C (opnd C q 1)).card) (h0:OrReaches n C (opnd C r 0) q) (h1:OrReaches n C (opnd C r 1) q):False:=by
 classical
 have _h:=hR1;have Y:c6 G C q r:=⟨⟨hC,hT,h4,hqr,hJ,hoff,Fin.forall_fin_two.mpr hW⟩,Fin.forall_fin_two.mpr ⟨h0,h1⟩⟩;have hA:=hC.1;obtain⟨hq,hr⟩:=bK Y.1;have hj2:(junk G C).card=2:=by rw[hJ,card_pair (by omega)]
 choose L hL using sW Y;have hF:∀β,∀t∈orIn n C (opnd C q (1-β)),G.Adj (L β) t:=λβ=>g0 Y (hL β).1 (hL β).2;have hL01:G.Adj (L 0) (L 1):=hF 0 _ (hL 1).1;have hcL:col (L 0)≠col (L 1):=hcol _ _ hL01;set E:Sym2 (Fin n) ->Prop:=λe=>∃β:Fin 2,∃w∈orIn n C (opnd C q (1-β)),e=s(L β,w)with hE;obtain⟨Pq,hPq,cq⟩:=kJ hA h4 (w:=λβ=>opnd C q β) (y:=L) (cJ Y.1 0) (λβ=>(hL β).1) hL01 (V:=(Ustar G C).filter E) (filter_subset _ _) λe he=>(mem_filter.mp he).2;have hUg:∀e∈(Ustar G C).filter λe=>¬E e,∃β:Fin 2,∃c∈orIn n C (opnd C r β),∃d∈orIn n C (opnd C r (1-β)),e=s(c,d)/\aC n G C r c:=by
  intro e he
  induction e using Sym2.ind with
  |_ u v=>
  obtain⟨heU,hnE⟩:=mem_filter.mp he;rcases sN Y heU with hx|h
  ·exact absurd (k7 Y.1 (λβ=>⟨(hL β).1,hF β⟩) (SimpleGraph.mem_edgeFinset.mp (mem_sdiff.mp heU).1) hx) hnE
  ·exact h
 obtain⟨Pg,Xg,hPg,cg,hXg,hXg2,hmono⟩:=tP Y (filter_subset _ _) hUg;have hdis:Disjoint Pq Pg:=disjoint_left.mpr λh hq' hg'=>by
  obtain⟨β,hch⟩:=hPq h hq';obtain⟨_,hcg⟩:=hPg h hg';refine hcg.2.1 ⟨L (1-β),λw hw=>?_⟩;have hw':w∈orIn n C (opnd C q β):=aK (aJ hA) hch.2.2.2.2 hw;have hw'':w∈orIn n C (opnd C q (1-(1-β))):=by rwa[bV]
  exact⟨hF (1-β) w hw'',λhm=>(mem_filter.mp hm).2 ⟨1-β,w,hw'',rfl⟩⟩
 set Mix:=(range (n+C.gates.length)).filter (aR n G C);have hmix:∀{w J:ℕ},J∈junk G C ->OrReaches n C w J ->(orIn n C w).Nonempty ->∃m,n+m∈Mix/\OrReaches n C w m/\OrReaches n C (n+m) J/\(orIn n C (n+m)).Nonempty:=λhJ' hr' hne'=>by
  obtain⟨m,hM,hm,h1,h2,h3⟩:=dR hA hJ' hr' hne';exact⟨m,mem_filter.mpr ⟨mem_range.mpr (by omega),hM⟩,h1,h2,h3⟩
 obtain⟨m0,hm0,hr0,-,hn0⟩:=hmix hq (Y.2 0) (k6 Y 0);obtain⟨m1,hm1,hr1,-,-⟩:=hmix hq (Y.2 1) (k6 Y 1);have hm01:n+m0≠n+m1:=λe=>by
  obtain⟨v,hv⟩:=hn0;exact disjoint_left.mp (jZ Y 0) (a6 hA hr0 hv) (by rw[e]at hv;exact a6 hA hr1 hv)
 have hrl:=(aA.mp hr).1;have hlt:∀β m,OrReaches n C (opnd C r β) m ->m<r:=λβ m h=>by
  have:=(aX h).1;have:=aH hA hrl β;omega
 have hM2:2≤Mix.card:=(card_pair hm01).symm.le.trans (card_le_card (by simp[insert_subset_iff,hm0,hm1]));have hM3:(centreless G C).card=0 ->3≤Mix.card:=λhc0=>by
  obtain⟨a,ha,b,hra⟩:=r9 Y;have hne:(orIn n C (opnd C a b)).Nonempty:=nonempty_iff_ne_empty.mpr λhe=>by
   have:=card_pos.mpr ⟨a,c7 ha he⟩;omega
  obtain⟨m3,hm3,-,hr3,-⟩:=hmix hr hra hne;have h3:r<m3:=by
   have:=(aX hr3).1;rcases (show r≤m3 by omega).lt_or_eq with h|h
   ·exact h
   ·have:=(a7.mp (mem_filter.mp hm3).2.1).2;rw[←h,(aA.mp hr).2.1]at this;cases this
  have:=hlt 0 m0 hr0;have:=hlt 1 m1 hr1
  have:=card_le_card (show({n+m3,n+m0,n+m1}:Finset ℕ)⊆Mix by
   simp[insert_subset_iff,hm3,hm0,hm1])
  rw[card_insert_of_notMem (by simp;omega),card_pair hm01]at this;exact this
 obtain⟨K,hKc,hKs,hKa⟩:=qZ hA h4 λa b p=>(∃k∈junk G C,OrReaches n C (opnd C a b) k)/\(p=L 0\/p=L 1);have hLK:∀β,L β∈K\/∃a∈centreless G C,∃b:Fin 2,∃k∈junk G C,OrReaches n C (opnd C a b) k/\L β∈orIn n C (opnd C a (1-b)):=by
  intro β;obtain⟨k,hk,hU⟩:∃k∈junk G C,aC n G C k (L β):=(hL β).2.elim (λh=>⟨q,hq,h⟩) λh=>⟨r,hr,h⟩;obtain⟨a,ha,b,hra,hv⟩:=hU;by_cases hne:(orIn n C (opnd C a b)).Nonempty
  ·left;have hsg:=uT Y col hcol hL ha hk hra hv hne;obtain⟨b',p,hpK,hside,hQ⟩:=hKa a (jO ha hne ⟨_,hv⟩);obtain⟨⟨k',hk',hr'⟩,-⟩:=hQ ⟨b,L β,hsg,⟨k,hk,hra⟩,by fin_cases β;exacts[Or.inl rfl,Or.inr rfl]⟩;rcases aS b b' with e|e
   ·rw[e]at hside;have h':orIn n C (opnd C a (1-b))={p}:=hside;rw[hsg,singleton_inj]at h';exact h'▸hpK
   ·rw[e]at hr';exact(g6 hA hq (eK Y) ha hk hk' hra hr').elim
  ·exact Or.inr ⟨a,c7 ha (not_nonempty_iff_eq_empty.mp hne),b,k,hk,hra,hv⟩
 obtain⟨X,hXd⟩:∃X:Finset (Fin n),X=({L 0,L 1}:Finset (Fin n))∪Xg:=⟨_,rfl⟩;have hX:∀e∈Ustar G C,∃v∈X,v∈e:=λe he=>by
  rw[hXd];by_cases hEe:E e
  ·obtain⟨β,w,-,rfl⟩:=hEe;exact⟨L β,mem_union_left _ (by fin_cases β<;>simp),Sym2.mem_mk_left _ _⟩
  ·obtain⟨v,hv,hve⟩:=hXg e (mem_filter.mpr ⟨he,hEe⟩);exact⟨v,mem_union_right _ hv,hve⟩
 have hM:=e4 h4 hC hT hj2 K X hKs hX;have hu:=card_filter_add_card_filter_not (s:=Ustar G C) E;have hPM:Disjoint (Pq∪Pg) Mix:=disjoint_left.mpr λh h1 h2=>by
  rcases mem_union.mp h1 with h1|h1
  ·obtain⟨_,hc⟩:=hPq h h1;exact gZ (mem_filter.mp h2).2 hc
  ·obtain⟨_,hc⟩:=hPg h h1;exact gZ (mem_filter.mp h2).2 hc
 have hsub:Pq∪Pg∪Mix⊆(orN G C\lam G C).image (n+·):=λh hh=>by
  rcases mem_union.mp hh with hh|hh
  ·rcases mem_union.mp hh with hh|hh
   ·obtain⟨_,hc⟩:=hPq h hh;exact hc.1
   ·obtain⟨_,hc⟩:=hPg h hh;exact hc.1
  ·exact g7 hA (mem_filter.mp hh).2
 have hρ:∀H:Finset ℕ,H⊆(orN G C\lam G C).image (n+·) ->Disjoint (Pq∪Pg∪Mix) H ->Pq.card+Pg.card+Mix.card+H.card≤(orN G C\lam G C).card:=λH hH hd=>by
  have:=card_le_card (union_subset hsub hH);rwa[card_union_of_disjoint hd,card_union_of_disjoint hPM,card_union_of_disjoint hdis,card_image_of_injective _ (add_right_injective n)]at this
 have h0ρ:=hρ ∅ (empty_subset _) (disjoint_empty_right _)
 have hXc:X.card≤2+Xg.card:=hXd▸(card_union_le _ _).trans (by
  have:=card_le_two (a:=L 0) (b:=L 1);omega)
 by_cases hK2:L 0∈K/\L 1∈K
 ·have:(X\K).card≤Xg.card:=card_le_card λv hv=>by
   obtain⟨hvX,hvK⟩:=mem_sdiff.mp hv;rcases mem_union.mp (hXd▸hvX)with h|h
   ·simp only[mem_insert,mem_singleton]at h;rcases h with rfl|rfl;exacts[absurd hK2.1 hvK,absurd hK2.2 hvK]
   ·exact h
  by_cases hc0:(centreless G C).card=0
  ·have:=hM3 hc0;omega
  ·omega
 have hc1:1≤(centreless G C).card:=by
  rcases not_and_or.mp hK2 with h|h<;>[rcases hLK 0 with h'|⟨a,ha,-⟩;rcases hLK 1 with h'|⟨a,ha,-⟩]<;>first|exact absurd h' h|exact card_pos.mpr ⟨a,ha⟩
 have hXK:(X\K).card≤X.card:=card_le_card sdiff_subset;by_cases hcx:(centreless G C).card=1/\4≤(X\K).card
 swap
 ·have:(X\K).card≤4:=by omega
  omega
 obtain⟨hc1',hx4⟩:=hcx;have hout:∀β,L β∉K:=λβ hβ=>by
  have:(X\K).card≤(X.erase (L β)).card:=card_le_card λv hv=>by
   obtain⟨hvX,hvK⟩:=mem_sdiff.mp hv;exact mem_erase.mpr ⟨λe=>hvK (e▸hβ),hvX⟩
  rw[card_erase_of_mem (hXd▸mem_union_left _ (by fin_cases β<;>
   simp))]at this
  omega
 have hg2:2≤Xg.card:=by omega
 obtain⟨a0,ha0,b0,k0,hk0,hr00,hv0⟩:=(hLK 0).resolve_left (hout 0);obtain⟨a1,ha1,b1,k1,hk1,hr11,hv1⟩:=(hLK 1).resolve_left (hout 1);have ha:a1=a0:=card_le_one.mp (by omega) _ ha1 _ ha0;rw[ha]at hr11 hv1;have hat:=(mem_filter.mp ha0).1;have hb:b1=b0:=by
  rcases aS b0 b1 with h|h
  ·exact h
  ·rw[h]at hr11;exact(g6 hA hq (eK Y) hat hk0 hk1 hr00 hr11).elim
 rw[hb]at hv1
 obtain⟨h,hJh,hRh,hFh,hh0,hh1⟩:=eU (aJ hA) (aB G (Ustar G C)) (opnd C a0 (1-b0)) (L 0) (L 1) (λe=>hL01.ne e) hv0 hv1 (λW hW ⟨h1',h2'⟩=>by
   obtain⟨c,hc⟩:=aU col hcol hW
   exact hcL ((hc _ h1').trans (hc _ h2').symm))
  λu _ hu=>Or.inr (bL hu)
 have hhI:=j3 hA hJh ⟨_,hh0⟩ hFh;have hnot:h∉Pq∪Pg∪Mix:=λhh=>by
  rcases mem_union.mp hh with hh|hh
  ·rcases mem_union.mp hh with hh|hh
   ·obtain⟨β,hc⟩:=hPq h hh;have hs:=aK (aJ hA) hc.2.2.2.2;fin_cases β
    ·exact disjoint_left.mp (cJ Y.1 0) (hs hh1) (hL 1).1
    ·exact disjoint_left.mp (cJ Y.1 1) (hs hh0) (hL 0).1
   ·obtain⟨β,hc⟩:=hPg h hh;have hs:=aK (aJ hA) hc.2.2.2.2;obtain⟨y,hy⟩:=hmono hg2 β;exact hcL (bB _ _ _ (hcol _ _ (hy _ (hs hh0))).symm (hcol _ _ (hy _ (hs hh1))).symm)
  ·obtain⟨-,⟨J,hJ',hrJ⟩,-⟩:=(mem_filter.mp hh).2;obtain⟨hJl,hrJ'⟩:=(cK hA).mp hrJ;exact g6 hA hq (eK Y) hat hk0 hJ' hr00 ((cK hA).mpr ⟨hJl,hRh.trans hrJ'⟩)
 have:=hρ {h} (singleton_subset_iff.mpr hhI) (disjoint_singleton_right.mpr hnot);rw[card_singleton]at this;omega
def d6 (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (q r:ℕ) (b:Fin 2):Prop:=gP G C q r/\OrReaches n C (opnd C r b) q/\¬OrReaches n C (opnd C r (1-b)) q/\orIn n C (opnd C r b)=∅
section B1
variable {q r:ℕ} {b:Fin 2}
lemma lF (Z:d6 G C q r b) (x:Fin n ->Bool):gateVal n C r x=true↔gateVal n C q x=true/\∃d∈orIn n C (opnd C r (1-b)),x d=true:=by
 rw[(cN Z.1.1.1 Z.1.2.1 Z.1.2.2.2.1 Z.1.2.2.2.2.1 Z.1.2.2.2.2.2.1 Z.2.1 Z.2.2.1).1 x,Z.2.2.2];simp
lemma fT (Z:d6 G C q r b):∀k∈junk G C,∀x,gateVal n C r x=true ->gateVal n C k x=true:=λk hk x hx=>by
 rw[Z.1.2.2.2.2.1,mem_insert,mem_singleton]at hk;rcases hk with rfl|rfl;exacts[((lF Z x).mp hx).1,hx]
lemma u8 (Z:d6 G C q r b) (x:Fin n ->Bool):wireVal n (aG n C r) (n+q) x=gateVal n C q x:=eB (bJ r) _ _ (by have:=Z.1.2.2.2.1;omega) λ_=>by simpa using λhc=>absurd (aP hc) (by have:=Z.1.2.2.2.1;omega)
lemma tS (Z:d6 G C q r b) {w:Fin n} (hw:aC n G C q w) {u v:Fin n} (hx:gateVal n C q (pairInput u v)=true) (hwe:w=u\/w=v):wireVal n (aG n C r) C.output (pairInput u v)=true:=by
 obtain⟨a,ha,b',hra,hva⟩:=hw;have hr:=(bK Z.1).2;have hqr:=Z.1.2.2.2.1;refine fW Z.1.1 Z.1.2.1 hr ha λb''=>?_;rcases aS b' b'' with rfl|rfl
 ·exact fI Z.1.1.1 hr (Or.inr ⟨by omega,λhc=>absurd (aP hc) (by omega),hra,hx⟩)
 ·exact fI Z.1.1.1 (k:=r) hr (Or.inl ⟨_,hva,by rcases hwe with rfl|rfl<;>
   simp[pairInput]⟩)
lemma vB (Z:d6 G C q r b) {u v:Fin n} (huv:G.Adj u v) (hl:wireVal n (aG n C r) C.output (pairInput u v)=false):gateVal n C r (pairInput u v)=true:=by
 obtain⟨hC,hT,-,-,hJ,-,-⟩:=Z.1;have hr:=(bK Z.1).2;obtain⟨k,hk,hkx,hkk,-⟩:=lR hC hT hr (fT Z) hr huv hl;rw[hJ,mem_insert,mem_singleton]at hk;rcases hk with rfl|rfl
 ·rw[u8 Z,hkx]at hkk;cases hkk
 ·exact hkx
lemma s4 (Z:d6 G C q r b) {L:Fin 2 ->Fin n} (hL:∀β,L β∈orIn n C (opnd C q β)/\aC n G C q (L β)):False:=by
 have hC:=Z.1.1;have hF:∀β,∀t∈orIn n C (opnd C q (1-β)),G.Adj (L β) t:=λβ=>f8 Z.1 (hL β).1 (bH hC.1 (hL β).2);refine jJ hC (aA.mp (bK Z.1).2).1 λu v huv=>by_contra λhk=>?_;have hqx:=((lF Z _).mp (vB Z huv (by simpa using hk))).1;obtain⟨β,w,-,e⟩:=k7 Z.1 (λβ=>⟨(hL β).1,hF β⟩) huv hqx;rw[dT e]at hk hqx;exact hk (tS Z (hL β).2 hqx (Or.inl rfl))
lemma mC (Z:d6 G C q r b) (β:Fin 2) {e:Sym2 (Fin n)} (he:e∈Ustar G C):∃s∈orIn n C (opnd C q β),∃t∈orIn n C (opnd C q (1-β)),e=s(s,t)/\G.Adj s t/\∃w∈e,aC n G C q w\/aC n G C r w/\∃d∈orIn n C (opnd C r (1-b)),d∈e:=by
 induction e using Sym2.ind with|_ u v=>
 obtain⟨hC,hT,-,-,hJ,-,-⟩:=Z.1;obtain⟨a,ha,hax,b',k,hk,-,hrk,hkx⟩:=fD hC hT he;obtain⟨hal,hop,-⟩:=aI.mp ha;obtain⟨w,hw,hwx⟩:=qH hC.1 hT (bK Z.1).2 (fT Z) ha hk hrk ((aN hC.1 hal hop b' _).mp hax).2;have hU:aC n G C k w:=⟨a,ha,b',hrk,hw⟩;rw[hJ,mem_insert,mem_singleton]at hk;obtain⟨hq,hD⟩:gateVal n C q (pairInput u v)=true/\(aC n G C q w\/aC n G C r w/\∃d∈orIn n C (opnd C r (1-b)),d∈s(u,v)):=by
  rcases hk with rfl|rfl
  ·exact⟨hkx,Or.inl hU⟩
  ·obtain⟨hq,d,hd,hdx⟩:=(lF Z _).mp hkx;exact⟨hq,Or.inr ⟨hU,d,hd,by rcases aW hdx with rfl|rfl<;>simp⟩⟩
 obtain⟨⟨s,hs,hsx⟩,t,ht,htx⟩:=(bP Z.1 β _).mp hq;have e:=fP (aW hsx) (aW htx) λe=>disjoint_left.mp (cJ Z.1 β) hs (e▸ht);have hE:s(s,t)∈G.edgeFinset:=e▸(mem_sdiff.mp he).1;exact⟨s,hs,t,ht,e,by simpa using hE,w,by rcases aW hwx with rfl|rfl<;>simp,hD⟩
end B1
def nA (n:ℕ) (C:Circuit):ℕ⊕Finset (Fin n) ->Prop:=Sum.elim (bX n C) λ_=>False
def nU (n:ℕ) (C:Circuit):ℕ⊕Finset (Fin n) ->ℕ⊕Finset (Fin n):=Sum.elim (λw=>Sum.inl (bF n C w)) Sum.inr
def nI (n:ℕ) (C:Circuit):ℕ⊕Finset (Fin n) ->ℕ⊕Finset (Fin n):=Sum.elim (λw=>Sum.inl (bI n C w)) Sum.inr
def lI (n:ℕ) (C:Circuit):ℕ⊕Finset (Fin n) ->Finset (Fin n):=Sum.elim (orIn n C) id
lemma rY (hA:IsAO2 n C):dB (nA n C) (nU n C) (nI n C) (Sum.elim id λ_=>0) (lI n C):=by
 rintro(w|W) hw
 ·exact aJ hA w hw
 ·exact hw.elim
def fN (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (w:ℕ):Prop:=∀k∈junk G C,¬OrReaches n C w k
def qK (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (U:Finset (Sym2 (Fin n))):ℕ⊕Finset (Fin n) ->Prop:=Sum.elim (λw=>fN n G C w/\(¬bX n C w ->(orIn n C w).card≤1)) (aB G U)
lemma rO (hA:IsAO2 n C) {U:Finset (Sym2 (Fin n))} {v:ℕ⊕Finset (Fin n)} (hv:Sum.elim (fN n G C) (aB G U) v) {u:ℕ⊕Finset (Fin n)} (hu:aM (nA n C) (nU n C) (nI n C) v u):qK n G C U u:=by
 induction hu with
 |refl=>
  rcases v with w|W
  ·exact⟨hv,λh=>bL h⟩
  ·exact hv
 | @tail u' u'' _ hs ih=>
  obtain⟨hJ,he|he⟩:=hs<;>rcases u' with w|W
  all_goals try exact hJ.elim
  all_goals subst he
  all_goals refine⟨λk hk hr=>ih.1 k hk ?_,λh=>bL h⟩
  ·exact(cK hA).mpr ⟨((cK hA).mp hr).1,Relation.ReflTransGen.single ⟨hJ,Or.inl rfl⟩
    |>.trans ((cK hA).mp hr).2⟩
  ·exact(cK hA).mpr ⟨((cK hA).mp hr).1,Relation.ReflTransGen.single ⟨hJ,Or.inr rfl⟩
    |>.trans ((cK hA).mp hr).2⟩
lemma e7 {ν:Type} {J:ν ->Prop} {l r:ν ->ν} {R:List ν} {d:ν} (Θ:ν ->Prop) {x:ν⊕ℕ} (hx:(x=dM R d/\R≠[]/\∀v∈R,∀w,aM J l r v w ->Θ w)\/∃v,x=Sum.inl v/\∀w,aM J l r v w ->Θ w) {u:ν⊕ℕ} (hu:aM (eR J R) (gG l R d) (f5 r R d) x u):Sum.elim Θ (λi=>i+1<R.length) u:=by
 rcases hx with⟨rfl,hR,h⟩|⟨v,rfl,h⟩
 ·rcases nO hR hu with⟨i,rfl,hi⟩|⟨v,hv,w,rfl,hw⟩
  ·exact hi
  ·exact h v hv w hw
 ·obtain⟨w,rfl,hw⟩:=eL hu;exact h w hw
lemma q5 {ν:Type} [DecidableEq ν] {J:ν ->Prop} {R:List ν} (P:Finset (ν⊕ℕ)) (hP:∀h∈P,eR J R h):P.card≤P.toLeft.card+(R.length-1)/\∀v∈P.toLeft,J v:=by
 refine⟨?_,λv hv=>hP _ (mem_toLeft.mp hv)⟩;have:=card_toLeft_add_card_toRight (u:=P);have:P.toRight⊆range (R.length-1):=λi hi=>by
  have:=hP _ (mem_toRight.mp hi);simp only[eR,Sum.elim_inr]at this;exact mem_range.mpr (by omega)
 have:=card_le_card this;simp at this;omega
lemma rH {q r:ℕ} {b:Fin 2} (Z:d6 G C q r b):∃Rc Ms:Finset ℕ,∃Wg:ℕ ->Finset (Fin n),Rc.card≤(centreless G C).card/\(∀w∈Rc,fN n G C w)/\(∀m∈Ms,aR n G C (n+m)/\aB G (Ustar G C) (Wg m))/\∀x,eM n G C x↔(∃w∈Rc,x∈orIn n C w)\/∃m∈Ms,x∈Wg m:=by
 classical
 have hA:=Z.1.1.1;have hr:=(bK Z.1).2;set DT:=(tops G C).filter λa=>∃β:Fin 2,∃k∈junk G C,OrReaches n C (opnd C a β) k;have hβ:∀a,∃β:Fin 2,a∈DT ->∃k∈junk G C,OrReaches n C (opnd C a β) k:=λa=>by
  by_cases ha:a∈DT
  ·obtain⟨β,h⟩:=(mem_filter.mp ha).2;exact⟨β,λ_=>h⟩
  ·exact⟨0,λh=>absurd h ha⟩
 choose βf hβf using hβ;have huq:∀a∈tops G C,∀β,∀k∈junk G C,OrReaches n C (opnd C a β) k ->a∈DT/\βf a=β:=λa ha β k hk hrk=>by
  have hD:a∈DT:=mem_filter.mpr ⟨ha,β,k,hk,hrk⟩;obtain⟨k',hk',hr'⟩:=hβf a hD;refine⟨hD,(aS β (βf a)).resolve_right λe=>?_⟩;rw[e]at hr';exact g6 hA hr (fT Z) ha hk hk' hrk hr'
 have hpf:∀a∈DT,fN n G C (opnd C a (1-βf a)):=λa ha k hk hrk=>by
  obtain⟨k',hk',hr'⟩:=hβf a ha;exact g6 hA hr (fT Z) (mem_filter.mp ha).1 hk' hk hr' hrk
 set Dn:=DT.filter λa=>a∉centreless G C;set Dc:=DT.filter λa=>a∈centreless G C;have hm:∀a,∃m,a∈Dn ->aR n G C (n+m)/\m<C.gates.length/\OrReaches n C (opnd C a (βf a)) m/\(orIn n C (n+m)).Nonempty:=λa=>by
  by_cases ha:a∈Dn
  ·obtain⟨haD,hac⟩:=mem_filter.mp ha;obtain⟨k,hk,hrk⟩:=hβf a haD;obtain⟨m,h1,h2,h3,-,h5⟩:=dR hA hk hrk (nonempty_iff_ne_empty.mpr λhe=>hac (c7 (mem_filter.mp haD).1 he));exact⟨m,λ_=>⟨h1,h2,h3,h5⟩⟩
  ·exact⟨0,λh=>absurd h ha⟩
 choose mf hmf using hm;set Ms:=Dn.image mf;set Wg:ℕ ->Finset (Fin n):=λm0=>(Dn.filter λa=>mf a=m0).biUnion λa=>orIn n C (opnd C a (1-βf a));have hWf:∀m0∈Ms,aB G (Ustar G C) (Wg m0):=λm0 hm0=>by
  obtain⟨a0,ha0,rfl⟩:=mem_image.mp hm0;obtain⟨y,hy⟩:=(hmf a0 ha0).2.2.2;refine⟨y,λw hw=>?_⟩;obtain⟨a,ha,hwa⟩:=mem_biUnion.mp hw;obtain⟨haDn,hma⟩:=mem_filter.mp ha;have hat:=(mem_filter.mp (mem_filter.mp haDn).1).1;have hy':=a6 hA (hmf a haDn).2.2.1 (hma▸hy);obtain⟨h1,h2⟩:=aV hA hat (βf a) hwa hy';exact⟨h1.symm,λhu=>(mem_sdiff.mp hu).2 (by rwa[Sym2.eq_swap])⟩
 refine⟨Dc.image λa=>opnd C a (1-βf a),Ms,Wg,card_image_le.trans (card_le_card λa ha=>(mem_filter.mp ha).2),λw hw=>?_,λm hm=>⟨?_,hWf m hm⟩,λx=>⟨?_,?_⟩⟩
 ·obtain⟨a,ha,rfl⟩:=mem_image.mp hw;exact hpf a (mem_filter.mp ha).1
 ·obtain⟨a,ha,rfl⟩:=mem_image.mp hm;exact(hmf a ha).1
 ·rintro⟨k,hk,a,ha,β,hrk,hw⟩;obtain⟨haD,rfl⟩:=huq a ha β k hk hrk;by_cases hac:a∈centreless G C
  ·exact Or.inl ⟨_,mem_image_of_mem _ (mem_filter.mpr ⟨haD,hac⟩),hw⟩
  ·have haN:a∈Dn:=mem_filter.mpr ⟨haD,hac⟩;exact Or.inr ⟨mf a,mem_image_of_mem _ haN,mem_biUnion.mpr ⟨a,mem_filter.mpr ⟨haN,rfl⟩,hw⟩⟩
 ·rintro(⟨w,hw,hx⟩|⟨m,-,hx⟩)
  ·obtain⟨a,ha,rfl⟩:=mem_image.mp hw;have haD:=(mem_filter.mp ha).1;obtain⟨k,hk,hrk⟩:=hβf a haD;exact⟨k,hk,a,(mem_filter.mp haD).1,βf a,hrk,hx⟩
  ·obtain⟨a',ha',hw'⟩:=mem_biUnion.mp hx;have haD:=(mem_filter.mp (mem_filter.mp ha').1).1;obtain⟨k,hk,hrk⟩:=hβf a' haD;exact⟨k,hk,a',(mem_filter.mp haD).1,βf a',hrk,hw'⟩
theorem tE {q r:ℕ} {b:Fin 2} (Z:d6 G C q r b) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (ex:List ℕ) (hpx:∀w∈ex,fN n G C w) (hxW:∀w∈ex,∀v∈orIn n C w,k4 n G C q v) (hxD:∀γ,∀w∈orIn n C (opnd C q γ),aC n G C q w ->∃y∈ex,w∈orIn n C y) (hU:(Ustar G C).Nonempty):∃Q:Finset (Fin n),Q.card≤2/\(∀e∈Ustar G C,∃v∈Q,v∈e)/\((∀y,∃e∈Ustar G C,y∉e) ->(Ustar G C).card+1≤(orN G C\lam G C).card+(centreless G C).card+ex.length):=by
 classical
 obtain⟨hC,hT,h4,hqr,hJ,-,-⟩:=Z.1;have hA:=hC.1;obtain⟨hq,hr⟩:=bK Z.1;have hE:Ustar G C⊆G.edgeFinset:=sdiff_subset;obtain⟨e0,he0⟩:=hU;obtain⟨z0,-,-,-,-,-,w0,-,hw0⟩:=mC Z 0 he0;obtain⟨Rc,Ms,Wg,hRc,hpRc,hMs,hU'⟩:=rH Z;set RV:List (ℕ⊕Finset (Fin n)):=Rc.toList.map Sum.inl++Ms.toList.map λm0=>Sum.inr (Wg m0);have hRVm:∀v∈RV,Sum.elim (fN n G C) (aB G (Ustar G C)) v:=λv hv=>by
  rcases List.mem_append.mp hv with hv|hv<;>obtain⟨a,ha,rfl⟩:=List.mem_map.mp hv;exacts[hpRc a (mem_toList.mp ha),(hMs a (mem_toList.mp ha)).2]
 have hused:∀w,eM n G C w↔∃v∈RV,w∈lI n C v:=λw=>by
  rw[hU' w];constructor
  ·rintro(⟨w',hw',hw⟩|⟨m,hm,hw⟩)
   ·exact⟨_,List.mem_append_left _ (List.mem_map.mpr ⟨w',mem_toList.mpr hw',rfl⟩),hw⟩
   ·exact⟨_,List.mem_append_right _ (List.mem_map.mpr ⟨m,mem_toList.mpr hm,rfl⟩),hw⟩
  ·rintro⟨v,hv,hw⟩;rcases List.mem_append.mp hv with hv|hv<;>obtain⟨a,ha,rfl⟩:=List.mem_map.mp hv;exacts[Or.inl ⟨a,mem_toList.mp ha,hw⟩,Or.inr ⟨a,mem_toList.mp ha,hw⟩]
 have hRV:RV≠[]:=λh=>by
  obtain⟨v,hv,-⟩:=(hused w0).mp (hw0.elim (⟨q,hq,·⟩) λh=>⟨r,hr,h.1⟩);rw[h]at hv;simp at hv
 set RD:List ((ℕ⊕Finset (Fin n))⊕ℕ):=(opnd C r (1-b)::ex).map λw=>Sum.inl (Sum.inl w);have hRD:RD≠[]:=by simp[RD]
 have D3:=nL (nL (rY hA) RV (Sum.inl 0)) RD (Sum.inl (Sum.inl 0));set J3:=eR (eR (nA n C) RV) RD;set L3:=gG (gG (nU n C) RV (Sum.inl 0)) RD (Sum.inl (Sum.inl 0));set R3:=f5 (f5 (nI n C) RV (Sum.inl 0)) RD (Sum.inl (Sum.inl 0));set F3:=jS (jS (lI n C) RV) RD;set rt:Fin 4 ->((ℕ⊕Finset (Fin n))⊕ℕ)⊕ℕ:= ![Sum.inl (Sum.inl (Sum.inl (opnd C q 0))),Sum.inl (Sum.inl (Sum.inl (opnd C q 1))),dM RD (Sum.inl (Sum.inl 0)),Sum.inl (dM RV (Sum.inl 0))];have f2:∀x,x∈F3 (rt 2)↔∃w∈opnd C r (1-b)::ex,x∈orIn n C w:=λx=>by
  rw[show rt 2=dM RD _ from rfl,jI _ _ hRD];simp[RD,jS,lI]
 have f3:∀x,x∈F3 (rt 3)↔∃v∈RV,x∈lI n C v:=λx=>jI _ _ hRV;have hH:∀x:Fin n ->Bool,(∀k,∃v∈F3 (rt k),x v=true) ->graphFun G ∅ x=true:=λx h=>by
   obtain⟨v,hv,hx⟩:=h 2;obtain⟨w,hw,hvw⟩:=(f2 v).mp hv;obtain⟨u,hu,hxu⟩:=h 3;obtain⟨k,hk,hk'⟩:=(hused u).mpr ((f3 u).mp hu);have hq:=(bP Z.1 0 x).mpr ⟨h 0,h 1⟩;rcases List.mem_cons.mp hw with rfl|hw
   ·exact bH hA hk' x (fT Z k hk x ((lF Z x).mpr ⟨hq,v,hvw,hx⟩)) hxu
   ·exact hxW w hw v hvw x hq hx
 have hacc:∀e∈Ustar G C,∀k,∃v∈F3 (rt k),v∈e:=λe he k=>by
  obtain⟨s,hs,t,ht,rfl,-,w,hw,h⟩:=mC Z 0 he;have hwU:eM n G C w:=h.elim (⟨q,hq,·⟩) λh=>⟨r,hr,h.1⟩;fin_cases k
  ·exact⟨s,hs,Sym2.mem_mk_left _ _⟩
  ·exact⟨t,ht,Sym2.mem_mk_right _ _⟩
  ·rcases h with h|⟨-,d,hd,hde⟩
   ·obtain⟨y,hy,hwy⟩:∃y∈ex,w∈orIn n C y:=by
     rcases Sym2.mem_iff.mp hw with rfl|rfl;exacts[hxD 0 _ hs h,hxD 1 _ ht h]
    exact⟨w,(f2 w).mpr ⟨y,List.mem_cons.mpr (Or.inr hy),hwy⟩,hw⟩
   ·exact⟨d,(f2 d).mpr ⟨_,List.mem_cons.mpr (Or.inl rfl),hd⟩,hde⟩
  ·exact⟨w,(f3 w).mpr ((hused w).mp hwU),hw⟩
 have pq:∀β,fN n G C (opnd C q β):=λβ k hk hrk=>dF hqr hJ k hk (bU hA (aA.mp hq).1 β hrk);have pD:∀w∈opnd C r (1-b)::ex,fN n G C w:=λw hw k hk hrk=>by
  rcases List.mem_cons.mp hw with rfl|hw
  ·rw[hJ,mem_insert,mem_singleton]at hk;rcases hk with rfl|rfl
   ·exact Z.2.2.1 hrk
   ·have:=(aX hrk).1;have:=aH hA (aA.mp hr).1 (1-b);omega
  ·exact hpx w hw k hk hrk
 have phys:∀w,fN n G C w ->∀u,aM (eR (nA n C) RV) (gG (nU n C) RV (Sum.inl 0)) (f5 (nI n C) RV (Sum.inl 0)) (Sum.inl (Sum.inl w)) u ->Sum.elim (qK n G C (Ustar G C)) (λi=>i+1<RV.length) u:=λw hw u hu=>e7 _ (Or.inr ⟨Sum.inl w,rfl,λ_ hw'=>rO hA (v:=Sum.inl w) hw hw'⟩) hu;have reach:∀k u,aM J3 L3 R3 (rt k) u ->Sum.elim (Sum.elim (qK n G C (Ustar G C)) (λi=>i+1<RV.length)) (λi=>i+1<RD.length) u:=λk u hu=>by
  fin_cases k
  ·exact e7 _ (Or.inr ⟨_,rfl,phys _ (pq 0)⟩) hu
  ·exact e7 _ (Or.inr ⟨_,rfl,phys _ (pq 1)⟩) hu
  ·refine e7 _ (Or.inl ⟨rfl,hRD,λv hv=>?_⟩) hu;obtain⟨w,hw,rfl⟩:=List.mem_map.mp hv;exact phys w (pD w hw)
  ·exact e7 _ (Or.inr ⟨_,rfl,λw hw=>e7 _ (Or.inl ⟨rfl,hRV,λv hv _ hw'=>rO hA (hRVm v hv) hw'⟩) hw⟩) hu
 have hleaf:∀k u,aM J3 L3 R3 (rt k) u ->¬J3 u ->aB G (Ustar G C) (F3 u)\/(F3 u).card≤1:=λk u hu hnj=>by
  have h:=reach k u hu;rcases u with((w|W)|i)|i;exacts[Or.inr (h.2 hnj),Or.inl h,absurd h hnj,absurd h hnj]
 have count:∀P:Finset (((ℕ⊕Finset (Fin n))⊕ℕ)⊕ℕ),(∀h∈P,J3 h/\¬aB G (Ustar G C) (F3 h)/\∃k,aM J3 L3 R3 (rt k) h) ->P.card+1≤(orN G C\lam G C).card+(centreless G C).card+ex.length:=by
  intro P hP;obtain⟨c3,hJ2⟩:=q5 P λh hh=>(hP h hh).1;obtain⟨c2,hJ1⟩:=q5 P.toLeft hJ2;have c1:=card_toLeft_add_card_toRight (u:=P.toLeft.toLeft);rw[eq_empty_of_forall_notMem λW hW=>hJ1 _ (mem_toRight.mp hW),card_empty]at c1;have hP0:∀w∈P.toLeft.toLeft.toLeft,bX n C w/\¬aB G (Ustar G C) (orIn n C w)/\fN n G C w:=λw hw=>by
   obtain⟨hJw,hF,k,hk⟩:=hP (Sum.inl (Sum.inl (Sum.inl w))) (by simpa using hw);exact⟨hJw,hF,(reach k _ hk).1⟩
  have hsub:P.toLeft.toLeft.toLeft∪Ms.image (n+·)⊆(orN G C\lam G C).image (n+·):=λw hw=>by
    rcases mem_union.mp hw with hw|hw
    ·obtain⟨hJw,hF,-⟩:=hP0 w hw;exact j3 hA hJw (nonempty_iff_ne_empty.mpr λe=>hF ⟨z0,by simp[e]⟩) hF
    ·obtain⟨m0,hm0,rfl⟩:=mem_image.mp hw;exact g7 hA (hMs m0 hm0).1
  have hdisj:Disjoint P.toLeft.toLeft.toLeft (Ms.image (n+·)):=disjoint_left.mpr λw hw hw'=>by
    obtain⟨m0,hm0,rfl⟩:=mem_image.mp hw';obtain⟨-,⟨J,hJ',hrJ⟩,-⟩:=(hMs m0 hm0).1;exact(hP0 _ hw).2.2 J hJ' hrJ
  have:=card_le_card hsub;rw[card_union_of_disjoint hdisj,card_image_of_injective _ (add_right_injective n),card_image_of_injective _ (add_right_injective n)]at this;have hRDl:RD.length=ex.length+1:=by simp[RD]
  have:=List.length_pos_iff.mpr hRV;have:RV.length≤(centreless G C).card+Ms.card:=by
   simp only[RV,List.length_append,List.length_map,length_toList];omega
  omega
 obtain⟨Q,hQ2,hQ⟩:=gY col hcol h4 _ hH _ hE hacc;refine⟨Q,hQ2,hQ,λhno=>?_⟩;rcases kM col hcol h4 D3 rt hH _ hE hacc hleaf hno with⟨k1,k2,P,hP,hc⟩|⟨i,j,k,-,-,-,-,-,-,-,-,-,-,-,-,-,⟨P,hP,hc⟩,h0,hJ0,hF0,hR0,hn1,hn2,-,-⟩
 ·have:=count P λh hh=>⟨(hP h hh).1,(hP h hh).2.1,(hP h hh).2.2.elim (λx=>⟨k1,x⟩) λx=>⟨k2,x⟩⟩;omega
 ·have h0P:h0∉P:=λh=>(hP h0 h).2.2.elim hn1 hn2;have:=count (insert h0 P) λh hh=>by
   rcases mem_insert.mp hh with rfl|hh
   ·exact⟨hJ0,hF0,k,hR0⟩
   ·exact⟨(hP h hh).1,(hP h hh).2.1,(hP h hh).2.2.elim (λx=>⟨i,x⟩) λx=>⟨j,x⟩⟩
  rw[card_insert_of_notMem h0P]at this;omega
lemma lG {q r:ℕ} (X:gP G C q r) (Y:Finset (Fin n)) (hY:∀e∈Ustar G C,∃v∈Y,v∈e):2+2*(centreless G C).card+(orN G C\lam G C).card≤(Ustar G C).card+Y.card:=by
 obtain⟨K,-,-,-,h⟩:=gJ X.2.2.1 X.1 X.2.1 (by rw[X.2.2.2.2.1,card_pair X.2.2.2.1.ne]) (λ_=>True) Y hY;have:=card_le_card (sdiff_subset (s:=Y) (t:=K));omega
lemma qY (h4:NoFourCycle G) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) {U:Finset (Sym2 (Fin n))} {W:Finset (Fin n)} (hW:aB G U W) {x y:Fin n} (h:G.Adj x y\/∃z,x≠y/\G.Adj x z/\G.Adj y z/\(s(z,x)∈U\/s(z,y)∈U)):(W∩{x,y}).card≤1:=by
 have nf:x∈W ->y∈W ->False:=λhx hy=>by
  obtain⟨v,hv⟩:=id hW;rcases h with h|⟨z,hxy,h1,h2,h3⟩
  ·obtain⟨c,hc⟩:=aU col hcol hW;exact hcol x y h ((hc x hx).trans (hc y hy).symm)
  ·rw[←aQ h4 hxy (hv x hx).1.symm (hv y hy).1.symm h1 h2]at h3;exact h3.elim (hv x hx).2 (hv y hy).2
 refine card_le_one.mpr λa ha c hc=>?_;simp only[mem_inter,mem_insert,mem_singleton]at ha hc;rcases ha with⟨ha,rfl|rfl⟩<;>rcases hc with⟨hc,rfl|rfl⟩;exacts[rfl,(nf ha hc).elim,(nf hc ha).elim,rfl]
section B1c
variable {q r:ℕ} {b:Fin 2}
lemma k8 (Z:d6 G C q r b) {P:Finset ℕ} (hP:∀h∈P,∃V w,b5 n G C V w h) {S:Finset (Fin n)} (hS:∀x∈S,eM n G C x) (hsp:∀W,aB G (Ustar G C) W ->(W∩S).card≤1) (hc:(centreless G C).card=0\/S=∅):P.card+S.card≤(orN G C\lam G C).card:=by
 classical
 obtain⟨Rc,Ms,Wg,hRc,-,hMs,hU⟩:=rH Z;have h1:S.card≤Ms.card:=by
  rcases hc with hc|rfl
  ·refine(card_le_card (t:=Ms.biUnion λm=>Wg m∩S) λx hx=>?_).trans (card_biUnion_le.trans ((sum_le_card_nsmul Ms _ 1 λm hm=>hsp _ (hMs m hm).2).trans (by simp)));obtain⟨w,hw,-⟩|⟨m,hm,hx'⟩:=(hU x).mp (hS x hx)
   ·exact absurd (card_pos.mpr ⟨w,hw⟩) (by omega)
   ·exact mem_biUnion.mpr ⟨m,hm,mem_inter.mpr ⟨hx',hx⟩⟩
  ·simp
 have hsub:P∪Ms.image (n+·)⊆(orN G C\lam G C).image (n+·):=λh hh=>by
  rcases mem_union.mp hh with hh|hh
  ·obtain⟨V,w,hc⟩:=hP h hh;exact hc.1
  ·obtain⟨m,hm,rfl⟩:=mem_image.mp hh;exact g7 Z.1.1.1 (hMs m hm).1
 have hd:Disjoint P (Ms.image (n+·)):=disjoint_left.mpr λh hh hi=>by
  obtain⟨m,hm,rfl⟩:=mem_image.mp hi;obtain⟨V,w,hc⟩:=hP _ hh;exact gZ (hMs m hm).1 hc
 have:=card_le_card hsub;rw[card_union_of_disjoint hd,card_image_of_injective _ (add_right_injective n),card_image_of_injective _ (add_right_injective n)]at this;omega
lemma uZ (Z:d6 G C q r b) {y:Fin n} (hy:∀e∈Ustar G C,y∈e):(Ustar G C).card≤(orN G C\lam G C).card+2*(centreless G C).card:=by
 classical
 rcases (Ustar G C).eq_empty_or_nonempty with h0|⟨e0,he0⟩
 ·simp[h0]
 obtain⟨s,hs,t,ht,rfl,-,w0,-,hu0⟩:=mC Z 0 he0;obtain⟨γ,hyγ⟩:∃γ:Fin 2,y∈orIn n C (opnd C q γ):=by
  rcases Sym2.mem_iff.mp (hy _ he0)with rfl|rfl;exacts[⟨0,hs⟩,⟨1,ht⟩]
 have hsub:aE (Ustar G C) y⊆orIn n C (opnd C q (1-γ)):=λx hx=>by
  obtain⟨s',hs',t',ht',e,-⟩:=mC Z γ (aD.mp hx);rcases Sym2.eq_iff.mp e with⟨-,h⟩|⟨h,-⟩
  ·rw[h];exact ht'
  ·exact absurd (h▸ht') (disjoint_left.mp (cJ Z.1 γ) hyγ)
 obtain⟨P,hP,hc⟩:=fC Z.1.1.1 subset_rfl (opnd C q (1-γ)) (aE (Ustar G C) y) λW hW=>aF Z.1.2.2.1 sdiff_subset hW y;rw[inter_eq_right.mpr hsub]at hc
 have:=(card_le_card (s:=Ustar G C) (t:=(aE (Ustar G C) y).image (s(y,·))) λe he=>by
   obtain⟨x,rfl⟩:=Sym2.mem_iff_exists.mp (hy e he)
   exact mem_image_of_mem _ (aD.mpr he)).trans card_image_le
 have hP':∀h∈P,∃V w,b5 n G C V w h:=λh hh=>⟨_,_,hP h hh⟩;by_cases hc0:(centreless G C).card=0
 ·have:=k8 Z hP' (S:={w0}) (by
   simpa[eM]using hu0.elim (⟨q,(bK Z.1).1,·⟩) λh=>⟨r,(bK Z.1).2,h.1⟩)
   (λW _=>(card_le_card inter_subset_right).trans (card_singleton _).le) (Or.inl hc0)
  rw[card_singleton]at this;omega
 ·have:=k8 Z hP' (S:=∅) (by simp) (by simp) (Or.inr rfl);simp at this;omega
lemma tT (Z:d6 G C q r b) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (hc0:(centreless G C).card=0) {β:Fin 2} {p:Fin n} (hp:p∈orIn n C (opnd C q β)) (hpu:aC n G C q p) (hdir:∀γ,∀w∈orIn n C (opnd C q γ),aC n G C q w ->w=p) {Q:Finset (Fin n)} (hQ2:Q.card≤2) (hQ:∀e∈Ustar G C,∃v∈Q,v∈e) (hno:∀y,∃e∈Ustar G C,y∉e):(Ustar G C).card+1≤(orN G C\lam G C).card:=by
 classical
 have hA:=Z.1.1.1;have h4:=Z.1.2.2.1;obtain⟨hq,hr⟩:=bK Z.1;have hd:=cJ Z.1 β;set A:=orIn n C (opnd C q β);set B:=orIn n C (opnd C q (1-β));set D:=orIn n C (opnd C r (1-b));set U:=Ustar G C;have hne:∀a∈A,∀t∈B,a≠t:=λa ha t ht e=>disjoint_left.mp hd ha (e▸ht);have hF:∀t∈B,G.Adj p t:=f8 Z.1 hp (bH hA hpu);have c4:∀a∈A,a≠p ->∀t∈B,∀t'∈B,G.Adj a t ->G.Adj a t' ->t=t':=λa _ hap t ht t' ht' h1 h2=>aQ h4 hap h1 (hF t ht) h2 (hF t' ht');have hpU:eM n G C p:=⟨q,hq,hpu⟩;have E:∀e∈U,∃s∈A,∃t∈B,e=s(s,t)/\G.Adj s t/\(∃w∈e,eM n G C w)/\∃w∈e,w=p\/w∈D:=λe he=>by
  obtain⟨s,hs,t,ht,rfl,hst,w,hw,h⟩:=mC Z β he;refine⟨s,hs,t,ht,rfl,hst,⟨w,hw,h.elim (⟨q,hq,·⟩) λh=>⟨r,hr,h.1⟩⟩,?_⟩;rcases h with h|⟨-,d,hd,hde⟩
  ·rcases Sym2.mem_iff.mp hw with rfl|rfl;exacts[⟨_,hw,Or.inl (hdir _ _ hs h)⟩,⟨_,hw,Or.inl (hdir _ _ ht h)⟩]
  ·exact⟨d,hde,Or.inr hd⟩
 have hadj:∀s∈A,∀t∈B,(s∈D\/t∈D) ->(eM n G C s\/eM n G C t) ->G.Adj s t:=λs hs t ht h1 h2=>by
  have hr:gateVal n C r (pairInput s t)=true:=(lF Z _).mpr ⟨(bP Z.1 β _).mpr ⟨⟨s,hs,by simp[pairInput]⟩,t,ht,by simp[pairInput]⟩,h1.elim (⟨s,·,by simp[pairInput]⟩) (⟨t,·,by simp[pairInput]⟩)⟩;refine(aT s t).mp ?_;rcases h2 with⟨k,hk,h⟩|⟨k,hk,h⟩<;>exact bH hA h _ (fT Z k hk _ hr) (by simp[pairInput])
 obtain⟨e1,he1,hpe1⟩:=hno p;obtain⟨a1,ha1,z1,hz1,rfl,h11,⟨x1,hx1,hu1⟩,hD1⟩:=E _ he1;have hap1:a1≠p:=λh=>hpe1 (h▸Sym2.mem_mk_left _ _);by_cases hX:∀e∈U,p∈e\/z1∈e
 ·obtain⟨P,hP,hc⟩:=kJ hA h4 (w:= ![opnd C q β,opnd C q (1-β)]) (y:= ![p,z1]) (V:=U)
   (by simpa using hd) (λγ=>by fin_cases γ;exacts[hp,hz1]) (by simpa using hF z1 hz1)
   subset_rfl λe he=>by
    obtain⟨s,hs,t,ht,rfl,-⟩:=E e he;rcases hX _ he with h|h<;>rcases Sym2.mem_iff.mp h with h|h
    ·exact⟨0,t,by simpa using ht,by simp[h]⟩
    ·exact absurd (h▸ht) (disjoint_left.mp hd hp)
    ·exact absurd (h▸hs) (disjoint_right.mp hd hz1)
    ·exact⟨1,s,by simpa using hs,by simp[h,Sym2.eq_swap]⟩
  have hx1p:x1≠p:=λh=>hpe1 (h▸hx1);have:=k8 Z (λh hh=>let ⟨_,hc⟩:=hP h hh;⟨_,_,hc⟩) (S:={x1,p})
   (by simpa using⟨hu1,hpU⟩) (λW hW=>qY h4 col hcol hW (by
    rcases Sym2.mem_iff.mp hx1 with rfl|rfl
    ·exact Or.inr ⟨z1,hap1,h11,hF z1 hz1,Or.inl (by rw[Sym2.eq_swap];exact he1)⟩
    ·exact Or.inl (hF _ hz1).symm)) (Or.inl hc0)
  rw[card_pair hx1p]at this;omega
 simp only[not_forall,not_or]at hX;obtain⟨e2,he2,hpe2,hze2⟩:=hX;obtain⟨a2,ha2,z2,hz2,rfl,h22,⟨x2,hx2,hu2⟩,hD2⟩:=E _ he2;have hap2:a2≠p:=λh=>hpe2 (h▸Sym2.mem_mk_left _ _);have hz12:z1≠z2:=λh=>hze2 (h▸Sym2.mem_mk_right _ _);have n12:¬G.Adj a1 z2:=λh=>hz12 (c4 _ ha1 hap1 _ hz1 _ hz2 h11 h);have n21:¬G.Adj a2 z1:=λh=>hz12 (c4 _ ha2 hap2 _ hz1 _ hz2 h h22);have hst:∀a∈A,a≠p ->∀z∈B,G.Adj a z ->∀e∈U,a∈e ->z∈e:=λa ha hap z hz haz e he hae=>by
   obtain⟨s,hs,t,ht,rfl,hst,-⟩:=E e he;rcases Sym2.mem_iff.mp hae with rfl|rfl
   ·rw[c4 _ ha hap _ hz _ ht haz hst];exact Sym2.mem_mk_right _ _
   ·exact absurd rfl (hne _ ha _ ht)
 obtain⟨v1,hv1,hv1e⟩:=hQ _ he1;obtain⟨v2,hv2,hv2e⟩:=hQ _ he2;have hv12:v1≠v2:=by
  rcases Sym2.mem_iff.mp hv1e with rfl|rfl<;>rcases Sym2.mem_iff.mp hv2e with rfl|rfl;exacts[λh=>n12 (h▸h22),hne _ ha1 _ hz2,(hne _ ha2 _ hz1).symm,hz12]
 have hcov:∀e∈U,z1∈e\/z2∈e:=λe he=>by
  obtain⟨v,hv,hve⟩:=hQ e he;have:v=v1\/v=v2:=by
   by_contra! h
   have:=card_le_card (show {v,v1,v2}⊆Q by
    simp only[insert_subset_iff,singleton_subset_iff];exact⟨hv,hv1,hv2⟩)
   rw[card_insert_of_notMem (by simp[h.1,h.2]),card_pair hv12]at this;omega
  rcases this with rfl|rfl
  ·rcases Sym2.mem_iff.mp hv1e with rfl|rfl;exacts[Or.inl (hst _ ha1 hap1 _ hz1 h11 e he hve),Or.inl hve]
  ·rcases Sym2.mem_iff.mp hv2e with rfl|rfl;exacts[Or.inr (hst _ ha2 hap2 _ hz2 h22 e he hve),Or.inr hve]
 have x2:∀z∈B,∀z'∈B,z≠z' ->eM n G C z ->¬eM n G C z' ->(∀e∈U,z∈e\/z'∈e) ->U.card+1≤(orN G C\lam G C).card:=by
  intro z hz z' hz' hzz hzu hz'u hcv;have hL:∀y∈B,aE U y⊆A:=λy hy x hx=>by
   obtain⟨s,hs,t,ht,e,-⟩:=E _ (aD.mp hx);rcases Sym2.eq_iff.mp e with⟨h,-⟩|⟨-,h⟩;exacts[absurd (h▸hy) (disjoint_left.mp hd hs),h▸hs]
  have hu:=(card_le_card (s:=U) (t:=(aE U z).image (s(z,·))∪(aE U z').image (s(z',·))) λe he=>by
    rcases hcv e he with h|h<;>obtain⟨x,rfl⟩:=Sym2.mem_iff_exists.mp h
    exacts[mem_union_left _ (mem_image_of_mem _ (aD.mpr he)),mem_union_right _ (mem_image_of_mem _ (aD.mpr he))]).trans
   ((card_union_le _ _).trans (add_le_add card_image_le card_image_le))
  obtain⟨PA,hPA,cA⟩:=fC hA subset_rfl (opnd C q β) (insert p (aE U z)) λW hW=>a4 h4 sdiff_subset hW z p (hF z hz).symm;rw[inter_eq_right.mpr (insert_subset hp (hL z hz))]at cA;obtain⟨PB,hPB,cB⟩:∃PB:Finset ℕ,(∀h∈PB,b5 n G C U (opnd C q (1-β)) h)/\(p∈(aE U z)\/p∈(aE U z') ->1≤PB.card):=by
   by_cases hpL:p∈(aE U z)\/p∈(aE U z')
   ·obtain⟨PB,hPB,c⟩:=fC hA subset_rfl (opnd C q (1-β)) {z,z'} λW hW=>qY h4 col hcol hW (Or.inr ⟨p,hzz,(hF z hz).symm,(hF z' hz').symm,by
      rcases hpL with h|h<;>[left;right]<;>rw[Sym2.eq_swap]<;>exact aD.mp h⟩)
    rw[inter_eq_right.mpr (insert_subset hz (singleton_subset_iff.mpr hz')),card_pair hzz]at c;exact⟨PB,hPB,λ_=>by omega⟩
   ·exact⟨∅,by simp,λh=>absurd h hpL⟩
  have hcz:∀x∈insert p (aE U z'),col x≠col z:=λx hx=>by
   rcases mem_insert.mp hx with rfl|hx
   ·exact hcol _ _ (hF z hz)
   ·rw[bB _ _ _ (hcol z p (hF z hz).symm) (hcol z' p (hF z' hz').symm)];exact(hcol _ _ (by simpa using(mem_sdiff.mp (aD.mp hx)).1)).symm
  have hdis:Disjoint PA PB:=disjoint_left.mpr λh ha hb=>by
   obtain⟨v,hv⟩:=gW hA (hPA h ha);exact disjoint_left.mp hd (aK (aJ hA) (hPA h ha).2.2.2.2 hv) (aK (aJ hA) (hPB h hb).2.2.2.2 hv)
  have hρ:=k8 Z (P:=PA∪PB) (λh hh=>(mem_union.mp hh).elim (λh'=>⟨_,_,hPA h h'⟩) λh'=>⟨_,_,hPB h h'⟩) (S:=insert z (insert p (aE U z'))) (λx hx=>by
    rcases mem_insert.mp hx with rfl|hx
    ·exact hzu
    rcases mem_insert.mp hx with rfl|hx
    ·exact hpU
    obtain⟨-,-,-,-,-,-,⟨w,hw,hwu⟩,-⟩:=E _ (aD.mp hx);rcases Sym2.mem_iff.mp hw with rfl|rfl;exacts[(hz'u hwu).elim,hwu]) (λW hW=>by
    obtain⟨c,hc⟩:=aU col hcol hW;have s1:=a4 h4 sdiff_subset hW z' p (hF z' hz').symm;refine card_le_one.mpr λa ha a' ha'=>?_;rw[mem_inter,mem_insert]at ha ha';rcases ha with⟨ha,rfl|ha2⟩<;>rcases ha' with⟨ha',rfl|ha2'⟩
    ·rfl
    ·exact absurd ((hc _ ha).trans (hc _ ha').symm) (hcz _ ha2').symm
    ·exact absurd ((hc _ ha).trans (hc _ ha').symm) (hcz _ ha2)
    ·exact card_le_one.mp s1 a (mem_inter.mpr ⟨ha,ha2⟩) a' (mem_inter.mpr ⟨ha',ha2'⟩))
   (Or.inl hc0)
  rw[card_union_of_disjoint hdis,card_insert_of_notMem λh=>(mem_insert.mp h).elim (hne _ hp _ hz ·.symm) λh=>hne _ (hL z' hz' h) _ hz rfl]at hρ;have:=card_le_card (subset_insert p (aE U z));have:=card_le_card (subset_insert p (aE U z'));by_cases h:p∈(aE U z)\/p∈(aE U z')
  ·have:=cB h;omega
  ·rw[card_insert_of_notMem λh'=>h (Or.inl h')]at cA;rw[card_insert_of_notMem λh'=>h (Or.inr h')]at hρ;omega
 have D1:a1∈D\/z1∈D:=by
  obtain⟨w,hw,h⟩:=hD1;rcases Sym2.mem_iff.mp hw with rfl|rfl<;>rcases h with h|h;exacts[(hap1 h).elim,Or.inl h,(hne _ hp _ hz1 h.symm).elim,Or.inr h]
 have U1:eM n G C a1\/eM n G C z1:=by
  rcases Sym2.mem_iff.mp hx1 with rfl|rfl;exacts[Or.inl hu1,Or.inr hu1]
 have U2:eM n G C a2\/eM n G C z2:=by
  rcases Sym2.mem_iff.mp hx2 with rfl|rfl;exacts[Or.inl hu2,Or.inr hu2]
 by_cases hz1u:eM n G C z1<;>by_cases hz2u:eM n G C z2
 ·rcases D1 with h|h;exacts[(n12 (hadj _ ha1 _ hz2 (Or.inl h) (Or.inr hz2u))).elim,(n21 (hadj _ ha2 _ hz1 (Or.inr h) (Or.inr hz1u))).elim]
 ·exact x2 _ hz1 _ hz2 hz12 hz1u hz2u hcov
 ·exact x2 _ hz2 _ hz1 hz12.symm hz2u hz1u λe he=>(hcov e he).symm
 ·rcases D1 with h|h;exacts[(n12 (hadj _ ha1 _ hz2 (Or.inl h) (Or.inl (U1.resolve_right hz1u)))).elim,(n21 (hadj _ ha2 _ hz1 (Or.inr h) (Or.inl (U2.resolve_right hz2u)))).elim]
end B1c
theorem dZ (hR1:cM) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (h4:NoFourCycle G) (hC:IsLeastAO G C) (hT:TopForm G C) (q r:ℕ) (hqr:q<r) (hJ:junk G C={q,r}) (hoff:∀k∈junk G C,∀v:Fin n,gateVal n C k (unitInput v)=false) (hW:2≤(orIn n C (opnd C q 0)).card/\2≤(orIn n C (opnd C q 1)).card) (b:Fin 2) (hb:OrReaches n C (opnd C r b) q) (hnb:¬OrReaches n C (opnd C r (1-b)) q) (hCempty:orIn n C (opnd C r b)=∅):False:=by
 classical
 have _h:=hR1;have Z:d6 G C q r b:=⟨⟨hC,hT,h4,hqr,hJ,hoff,Fin.forall_fin_two.mpr hW⟩,hb,hnb,hCempty⟩;rcases (Ustar G C).eq_empty_or_nonempty with h0|hU
 ·have:=lG Z.1 ∅ (by simp[h0]);simp[h0]at this
 by_cases hcv:∃y,∀e∈Ustar G C,y∈e
 ·obtain⟨y,hy⟩:=hcv;have:=lG Z.1 {y} λe he=>⟨y,mem_singleton_self _,hy e he⟩;have:=uZ Z hy;rw[card_singleton]at*;omega
 simp only[not_exists,not_forall]at hcv;replace hcv:∀y,∃e∈Ustar G C,y∉e:=λy=>let ⟨e,he,h⟩:=hcv y;⟨e,he,h⟩
 by_cases hd:∃β,∃p∈orIn n C (opnd C q β),aC n G C q p
 ·obtain⟨β,p,hp,hpu⟩:=hd;have hb2:∀w∈orIn n C (opnd C q (1-β)),¬aC n G C q w:=λw hw hwu=>by
   rcases bG β with⟨rfl,e⟩|⟨rfl,e⟩<;>rw[e]at hw
   ·exact s4 Z (L:= ![p,w]) λδ=>by fin_cases δ<;>simp[hp,hpu,hw,hwu]
   ·exact s4 Z (L:= ![w,p]) λδ=>by fin_cases δ<;>simp[hp,hpu,hw,hwu]
  have hdir:∀γ,∀w∈orIn n C (opnd C q γ),aC n G C q w ->w=p:=λγ w hw hu=>by
   rcases aS β γ with rfl|rfl
   ·exact bC h4 (Z.1.2.2.2.2.2.2 _) (f8 Z.1 hw (bH hC.1 hu)) (f8 Z.1 hp (bH hC.1 hpu))
   ·exact(hb2 w hw hu).elim
  have hpo:orIn n C p.1={p}:=by rw[fA p.2]
  obtain⟨Q,hQ2,hQ,hgc⟩:=tE Z col hcol [p.1] (λw hw k _ hr=>by rw[List.mem_singleton]at hw;have:=hr.1;have:=p.2;omega) (λw hw v hv=>by
    rw[List.mem_singleton]at hw;rw[hw,hpo,mem_singleton]at hv
    exact hv▸bH hC.1 hpu)
   (λγ w hw hu=>⟨p.1,List.mem_singleton_self _,by
    rw[hpo,hdir γ w hw hu];exact mem_singleton_self _⟩) hU
  have:=lG Z.1 Q hQ;have:=hgc hcv;rw[List.length_singleton]at this;by_cases hc0:(centreless G C).card=0
  ·have:=tT Z col hcol hc0 hp hpu hdir hQ2 hQ hcv;omega
  ·omega
 ·simp only[not_exists,not_and]at hd;obtain⟨Q,hQ2,hQ,hgc⟩:=tE Z col hcol [] (by simp) (by simp) (λγ w hw hu=>(hd γ w hw hu).elim) hU;have:=lG Z.1 Q hQ;have:=hgc hcv;rw[List.length_nil]at this;omega
section
variable (hR1 : cM) (col : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → col u ≠ col v)
def vK (n:ℕ) (C:Circuit) (w h:ℕ):Prop:=aM (bX n C) (bF n C) (bI n C) w h
def c8 (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (h:ℕ):Prop:=
 bX n C h∧¬aB G (Ustar G C) (orIn n C h) ∧
  (orIn n C (bF n C h)).Nonempty∧(orIn n C (bI n C h)).Nonempty
lemma t7 (hA:IsAO2 n C) {h:ℕ} (hP:c8 n G C h):(orIn n C h).Nonempty:=
 let ⟨v,hv⟩:=hP.2.2.1;⟨v,(aJ hA h hP.1).2.2▸mem_union_left _ hv⟩
lemma sG (hA:IsAO2 n C) {h:ℕ} (hP:c8 n G C h) :
 h∈(orN G C \ lam G C).image (n+·):=g4 hA hP.1 (t7 hA hP) hP.2.1
lemma sQ (hA:IsAO2 n C) {P M:Finset ℕ} (hP:∀ h∈P,c8 n G C h)
 (hM:∀ h∈M,aR n G C h):#P+#M≤#(orN G C \ lam G C):=by
 have:=card_le_card (show P∪M⊆(orN G C \ lam G C).image (n+·) from fun h hh=>
  (mem_union.mp hh).elim (sG hA<|hP h ·) (g7 hA<|hM h ·))
 rwa [card_union_of_disjoint (disjoint_left.mpr fun h hp hm=>(hM h hm).2.2.elim
  (hP h hp).2.2.1.ne_empty (hP h hp).2.2.2.ne_empty),
  card_image_of_injective _ (add_right_injective n)] at this
lemma kB (hA:IsAO2 n C) (R:Finset ℕ) (S:Finset (Fin n))
 (hsp:∀ W,aB G (Ustar G C) W→ #(W∩S)≤1) :
 ∃ P:Finset ℕ,(∀ h∈P,c8 n G C h∧(∃ w∈R,vK n C w h) ∧
  1<#(orIn n C h∩S))∧#(R.biUnion (orIn n C)∩S)≤#R+#P:=by
 obtain ⟨P,hP,hc⟩:=cU (aJ hA) S R fun _ _ u _ hu=>
  (card_le_card inter_subset_left).trans (bL hu)
 refine ⟨P,fun h hh=>?_,hc⟩
 obtain ⟨hj,hr,h1,h2⟩:=hP h hh
 obtain ⟨x1,hx1,-⟩:=not_subset.mp h1
 obtain ⟨x2,hx2,hx2'⟩:=not_subset.mp h2
 rw [mem_inter] at hx1 hx2
 have he:=(aJ hA h hj).2.2
 have:1<#(orIn n C h∩S):=one_lt_card.mpr ⟨x1,mem_inter.mpr
  ⟨he▸mem_union_left _ hx1.1,hx1.2⟩,x2,mem_inter.mpr ⟨he▸mem_union_right _ hx2.1,
   hx2.2⟩,fun e=>hx2' (e▸hx1.1)⟩
 exact ⟨⟨hj,fun hf=>by have:=hsp _ hf;omega,⟨x1,hx1.1⟩,⟨x2,hx2.1⟩⟩,hr,this⟩
lemma jC (hA:IsAO2 n C) (w:ℕ) (S:Finset (Fin n))
 (hsp:∀ W,aB G (Ustar G C) W→ #(W∩S)≤1) :
 ∃ P:Finset ℕ,(∀ h∈P,c8 n G C h∧orIn n C h⊆orIn n C w ∧
  1<#(orIn n C h∩S))∧#(orIn n C w∩S)≤1+#P:=by
 obtain ⟨P,hP,hc⟩:=kB hA {w} S hsp
 simp only [singleton_biUnion,card_singleton] at hc
 refine ⟨P,fun h hh=>⟨(hP h hh).1,?_,(hP h hh).2.2⟩,hc⟩
 obtain ⟨w',hw',hr⟩:=(hP h hh).2.1
 exact mem_singleton.mp hw'▸aK (aJ hA) hr
lemma nK (hA:IsAO2 n C) (w:ℕ) {x y:Fin n} (hxy:x≠y) (hx:x∈orIn n C w)
 (hy:y∈orIn n C w) (hsp:∀ W,aB G (Ustar G C) W→ x∈W→ y∈W→ False) :
 ∃ h,c8 n G C h∧x∈orIn n C h∧y∈orIn n C h:=by
 obtain ⟨P,hP,hc⟩:=jC hA w {x,y} fun W hW=>card_le_one.mpr fun a ha b hb=>by
  simp only [mem_inter,mem_insert,mem_singleton] at ha hb
  rcases ha with ⟨ha,rfl|rfl⟩<;>rcases hb with ⟨hb,rfl|rfl⟩<;>
   first|rfl|exact (hsp W hW ha hb).elim|exact (hsp W hW hb ha).elim
 rw [inter_eq_right.mpr (insert_subset hx (singleton_subset_iff.mpr hy)),card_pair hxy] at hc
 obtain ⟨h,hh⟩:=card_pos.mp (by omega:0<#P)
 have e:=eq_of_subset_of_card_le (inter_subset_right (s₁:=orIn n C h))
  (by rw [card_pair hxy];exact (hP h hh).2.2)
 exact ⟨h,(hP h hh).1,(mem_inter.mp (by rw [e];simp:x∈orIn n C h∩{x,y})).1,
  (mem_inter.mp (by rw [e];simp:y∈orIn n C h∩{x,y})).1⟩
lemma mZ (hA:IsAO2 n C) {V:Finset (Sym2 (Fin n))} (hV:V⊆Ustar G C) {w h:ℕ}
 (hh:b5 n G C V w h):c8 n G C h∧orIn n C h⊆orIn n C w:=
 ⟨⟨mR hh,fun hf=>hh.2.1 (bT hV subset_rfl hf),hh.2.2.1,hh.2.2.2.1⟩,
  aK (aJ hA) hh.2.2.2.2⟩
lemma dE {u v:Fin n} (h:s(u,v)∈Ustar G C):G.Adj u v:=
 SimpleGraph.mem_edgeFinset.mp (mem_sdiff.mp h).1
lemma dQ {p x:Fin n} (h:x∈aE (Ustar G C) p):G.Adj p x:=dE (aD.mp h)
lemma jQ (hA:IsAO2 n C) {a i:ℕ} (ha:a∈tops G C) (hi:i∈junk G C) {b:Fin 2}
 (h1:OrReaches n C (opnd C a b) i) (h2:OrReaches n C (opnd C a (1-b)) i):False:=
 let ⟨hal,hop,hb⟩:=aI.mp ha
 (aA.mp hi).2.2 fun x hx=>hb x ((aN hA hal hop b x).mpr
  ⟨aO hA x h1 hx,aO hA x h2 hx⟩)
lemma d7 {g:ℕ} {β β':Fin 2} (h:orIn n C (opnd C g β)=∅) {v:Fin n}
 (hv:v∈orIn n C (opnd C g (1-β'))):β'=β:=by
 rcases aS β β' with rfl|rfl
 ·rfl
 ·rw [sub_sub_cancel,h] at hv;simp at hv
lemma g5 (hC:IsLeastAO G C) (hT:TopForm G C) {i:ℕ} (hi:i∈junk G C) {u v:Fin n}
 (huv:G.Adj u v) (hl:wireVal n (aG n C i) C.output (pairInput u v)=false) :
 s(u,v)∈Ustar G C:=
 mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr huv,fun hs=>by
  rw [lA hC hT hi hs] at hl;cases hl⟩
lemma vD {P1 P2 P3 P4:Finset ℕ} (h12:Disjoint (P1∩P2) (P3∪P4)) (h34:Disjoint (P3∩P4) (P1∪P2)) :
 #P1+#P2+#P3+#P4≤2*#(P1∪P2∪P3∪P4):=by
 have e1:=card_union_add_card_inter P1 P2
 have e2:=card_union_add_card_inter P3 P4
 have e3:=card_union_add_card_inter (P1∪P2) (P3∪P4)
 have d1:Disjoint ((P1∪P2)∩(P3∪P4)) (P1∩P2):=
  disjoint_left.mpr fun x hx hx'=>disjoint_left.mp h12 hx' (mem_inter.mp hx).2
 have d2:Disjoint ((P1∪P2)∩(P3∪P4)∪P1∩P2) (P3∩P4):=disjoint_left.mpr
  fun x hx hx'=>disjoint_left.mp h34 hx' ((mem_union.mp hx).elim (fun h=>(mem_inter.mp h).1)
   fun h=>mem_union_left _ (mem_inter.mp h).1)
 have:=card_le_card (show (P1∪P2)∩(P3∪P4)∪P1∩P2∪P3∩P4⊆P1∪P2∪P3∪P4 by
  intro x hx;simp only [mem_union,mem_inter] at hx ⊢;tauto)
 rw [card_union_of_disjoint d2,card_union_of_disjoint d1,union_assoc (P1∪P2)] at this
 rw [union_assoc (P1∪P2)]
 omega
def dG (n:ℕ) (C:Circuit) (i m:ℕ):Prop:=
 m<C.gates.length∧(gateAt C m).op=GateOp.or∧(orIn n C (n+m)).Nonempty ∧
  ∃ b:Fin 2,orIn n C (opnd C m b)=∅∧OrReaches n C (opnd C m b) i
lemma lX (hA:IsAO2 n C) {i m:ℕ} (hF:dG n C i m):OrReaches n C (n+m) i:=
 let ⟨hm,hop,_,b,_,hr⟩:=hF;d9 hA hm hop b hr
lemma c5 (hA:IsAO2 n C) {i m:ℕ} (hi:i∈junk G C) (hF:dG n C i m) : aR n G C (n+m):=by
 obtain ⟨hm,hop,-,b,he,-⟩:=id hF
 refine ⟨a7.mpr ⟨hm,hop⟩,⟨i,hi,lX hA hF⟩,?_⟩
 simp only [bF,bI,Nat.add_sub_cancel_left]
 fin_cases b
 exacts [Or.inl he,Or.inr he]
theorem nD (hA:IsAO2 n C) {i:ℕ} (hi:i∈junk G C) (L:Finset (Fin n))
 (hsp:∀ W,aB G (Ustar G C) W→ #(W∩L)≤1)
 (hL:∀ ℓ∈L,aC n G C i ℓ) :
 ∃ Mx Rc P:Finset ℕ,(∀ m∈Mx,dG n C i m)∧Rc⊆centreless G C ∧
  (∀ a∈Rc,∃ b:Fin 2,OrReaches n C (opnd C a b) i ∧ (orIn n C (opnd C a (1-b))).Nonempty) ∧
  (∀ h∈P,c8 n G C h∧1<#(orIn n C h∩L)∧∃ a∈Rc,∃ b:Fin 2,
   OrReaches n C (opnd C a b) i∧orIn n C h⊆orIn n C (opnd C a (1-b))) ∧
  (Rc=∅→ ∀ ℓ∈L,∃ m∈Mx,∃ a∈tops G C,∃ b:Fin 2,
   OrReaches n C (opnd C a b) m∧ℓ∈orIn n C (opnd C a (1-b))) ∧
  #L≤#Mx+#Rc+#P:=by
 classical
 choose! a ha b hr hm using hL
 have hb:∀ ℓ∈L,b ℓ=if OrReaches n C (opnd C (a ℓ) 0) i then 0 else 1:=fun ℓ hℓ=>by
  split_ifs with hc<;>rcases bG (b ℓ) with ⟨h0,h2⟩|⟨h1,h2⟩
  exacts [h0,(jQ hA (ha ℓ hℓ) hi (hr ℓ hℓ) (by rw [h2];exact hc)).elim,
   absurd (h0▸hr ℓ hℓ) hc,h1]
 set L1:=L.filter fun ℓ=>a ℓ∉centreless G C
 set L2:=L.filter fun ℓ=>a ℓ∈centreless G C
 have hmx:∀ ℓ∈L1,∃ m,dG n C i m∧OrReaches n C (opnd C (a ℓ) (b ℓ)) m:= fun ℓ hℓ=>by
  obtain ⟨hℓ,hc⟩:=mem_filter.mp hℓ
  obtain ⟨m,b',hm,hop,hwm,hne',he,hrJ⟩:=fE hA (aA.mp hi).2.1 (hr ℓ hℓ)
   (nonempty_iff_ne_empty.mpr fun e=>hc (c7 (ha ℓ hℓ) e))
  exact ⟨m,⟨hm,hop,hne',b',he,hrJ⟩,hwm⟩
 choose! m hm1 hm2 using hmx
 have hinj:Set.InjOn m L1:=fun ℓ hℓ ℓ' hℓ' he=>by
  obtain ⟨r0,hr0⟩:=(hm1 ℓ hℓ).2.2.1
  have hW:=gO hA hr0 (W:={ℓ,ℓ'}) fun w hw=>by
   rcases mem_insert.mp hw with rfl|hw
   ·exact ⟨a w,ha w (mem_filter.mp hℓ).1,b w,hm2 w hℓ,hm w (mem_filter.mp hℓ).1⟩
   ·rw [mem_singleton.mp hw]
    exact ⟨a ℓ',ha ℓ' (mem_filter.mp hℓ').1,b ℓ',he▸hm2 ℓ' hℓ', hm ℓ' (mem_filter.mp hℓ').1⟩
  have:=hsp _ hW
  rw [inter_eq_left.mpr (insert_subset (mem_filter.mp hℓ).1
   (singleton_subset_iff.mpr (mem_filter.mp hℓ').1))] at this
  by_contra hne
  rw [card_pair hne] at this;omega
 set root:ℕ→ ℕ:=fun a'=>opnd C a' (1-if OrReaches n C (opnd C a' 0) i then 0 else 1)
 obtain ⟨P,hP,hc⟩:=kB hA ((L2.image a).image root) L2 fun W hW=>
  (card_le_card (inter_subset_inter_left (filter_subset _ _))).trans (hsp W hW)
 have hL2:L2⊆((L2.image a).image root).biUnion (orIn n C):=fun ℓ hℓ=>by
  have hℓL:=(mem_filter.mp hℓ).1
  refine mem_biUnion.mpr ⟨root (a ℓ),mem_image_of_mem _ (mem_image_of_mem _ hℓ),?_⟩
  simp only [root,← hb ℓ hℓL];exact hm ℓ hℓL
 rw [inter_eq_right.mpr hL2] at hc
 refine ⟨L1.image m,L2.image a,P,fun m' hm'=>?_,fun a' ha'=>?_,fun a' ha'=>?_,
  fun h hh=>?_,fun he ℓ hℓ=>?_,?_⟩
 ·obtain ⟨ℓ,hℓ,rfl⟩:=mem_image.mp hm'
  exact hm1 ℓ hℓ
 ·obtain ⟨ℓ,hℓ,rfl⟩:=mem_image.mp ha'
  exact (mem_filter.mp hℓ).2
 ·obtain ⟨ℓ,hℓ,rfl⟩:=mem_image.mp ha'
  exact ⟨b ℓ,hr ℓ (mem_filter.mp hℓ).1,ℓ,hm ℓ (mem_filter.mp hℓ).1⟩
 ·obtain ⟨hP1,⟨w,hw,hr'⟩,hlt⟩:=hP h hh
  obtain ⟨a',ha',rfl⟩:=mem_image.mp hw
  obtain ⟨ℓ,hℓ,rfl⟩:=mem_image.mp ha'
  have hℓL:=(mem_filter.mp hℓ).1
  refine ⟨hP1,lt_of_lt_of_le hlt (card_le_card (inter_subset_inter_left (filter_subset _ _))),
   a ℓ,ha',b ℓ,hr ℓ hℓL,?_⟩
  simpa only [root,← hb ℓ hℓL] using aK (aJ hA) hr'
 ·by_cases hc':a ℓ∈centreless G C
  ·exact absurd he (ne_empty_of_mem (mem_image_of_mem a (mem_filter.mpr ⟨hℓ,hc'⟩)))
  ·have h1:ℓ∈L1:=mem_filter.mpr ⟨hℓ,hc'⟩
   exact ⟨m ℓ,mem_image_of_mem _ h1,a ℓ,ha ℓ hℓ,b ℓ,hm2 ℓ h1,hm ℓ hℓ⟩
 ·have h12:#L2+#L1=#L:=card_filter_add_card_filter_not _
  rw [card_image_of_injOn hinj]
  have:=card_image_le (s:=L2.image a) (f:=root)
  omega
lemma k9 (hA:IsAO2 n C) {i i':ℕ} (hi:i∈junk G C) (hii:i≠i') {w:ℕ}
 (he:orIn n C w=∅) (h1:OrReaches n C w i) (h2:OrReaches n C w i') :
 aR n G C w:=by
 obtain ⟨g,rfl⟩:∃ g,w=n+g:=⟨w-n,by have:=h1.1;omega⟩
 have hg:=((dN hA).mp h1).1
 have hop:(gateAt C g).op=GateOp.or:=by
  rcases ((dN hA).mp h1).2 with rfl|⟨h,-⟩
  ·rcases ((dN hA).mp h2).2 with rfl|⟨h,-⟩
   exacts [absurd rfl hii,h]
  ·exact h
 refine ⟨a7.mpr ⟨hg,hop⟩,⟨i,hi,h1⟩,Or.inl ?_⟩
 have:=dO hA hg hop
 rw [he] at this
 simpa only [bF,Nat.add_sub_cancel_left] using (union_eq_empty.mp this.symm).1
lemma jN (hA:IsAO2 n C) {i i' m:ℕ} (hi:i∈junk G C) (hii:i≠i')
 (h1:dG n C i m) (h2:dG n C i' m):∃ g,aR n G C g∧orIn n C g=∅:=by
 obtain ⟨hm,hop,⟨v,hv⟩,b,he,hr⟩:=h1
 obtain ⟨-,-,-,b',he',hr'⟩:=h2
 rw [dO hA hm hop] at hv
 obtain rfl:b'=b:=by
  by_contra hb
  fin_cases b<;>fin_cases b'<;>simp_all
 exact ⟨_,k9 hA hi hii he hr hr',he⟩
lemma r4 (hA:IsAO2 n C) {i i' a:ℕ} (hi:i∈junk G C) (hii:i≠i')
 (ha:a∈centreless G C) {b b':Fin 2} (h1:OrReaches n C (opnd C a b) i)
 (n1:(orIn n C (opnd C a (1-b))).Nonempty) (h2:OrReaches n C (opnd C a b') i')
 (n2:(orIn n C (opnd C a (1-b'))).Nonempty):∃ g,aR n G C g∧orIn n C g=∅:=by
 obtain ⟨β',he⟩:∃ β',orIn n C (opnd C a β')=∅:= (mem_filter.mp ha).2.elim (⟨0,·⟩) (⟨1,·⟩)
 obtain ⟨v,hv⟩:=n1
 obtain ⟨v',hv'⟩:=n2
 rw [← d7 he hv] at he
 rw [d7 he hv'] at h2
 exact ⟨_,k9 hA hi hii he h1 h2,he⟩
lemma jP (h4:NoFourCycle G) {p p':Fin n} (hpp:p≠p') {S:Finset (Fin n)}
 (hS:∀ v∈S,G.Adj p v∧G.Adj p' v) (h:1<#S):False:=
 let ⟨x,hx,y,hy,hxy⟩:=one_lt_card.mp h
 hxy (aQ h4 hpp (hS x hx).1 (hS x hx).2 (hS y hy).1 (hS y hy).2)
def j6 (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (col:Fin n→ Bool)
 (x f:Fin n):Prop:=
 ∀ a∈tops G C,∀ β:Fin 2,f∈side C a β → ∃ w∈side C a β,w≠f∧¬G.Adj x w∧col w=col f
include hcol in
lemma mE (c:Fin n) {R:Finset (Fin n)} (hR:∀ v∈R,col v≠col c∧¬G.Adj c v) :
 graphFun G ∅ (fun v=>decide (v=c∨v∈R))=false:=by
 rw [← Bool.not_eq_true,dJ]
 rintro ⟨u,v,huv,hu,hv⟩
 simp only [decide_eq_true_eq] at hu hv
 rcases hu with hu|hu<;>rcases hv with hv|hv
 ·exact huv.ne (hu.trans hv.symm)
 ·exact (hR v hv).2 (hu▸huv)
 ·exact (hR u hu).2 (hv▸huv.symm)
 ·exact hcol u v huv (bB _ _ _ (hR u hu).1 (hR v hv).1)
lemma mO {e:Sym2 (Fin n)} (he:e∈starEdges G C) :
 ∃ a∈tops G C,∃ u∈side C a 0,∃ v∈side C a 1,e=s(u,v):=by
 simp only [starEdges,mem_biUnion,mem_image,mem_product] at he
 obtain ⟨a,ha,⟨u,v⟩,⟨hu,hv⟩,rfl⟩:=he
 exact ⟨a,ha,u,hu,v,hv,rfl⟩
lemma mN (hA:IsAO2 n C) {a:ℕ} (ha:a∈tops G C) {β:Fin 2} {u v:Fin n}
 (hu:u∈side C a β) (hv:v∈side C a (1-β)):G.Adj u v:=by
 rcases bG β with ⟨rfl,h⟩|⟨rfl,h⟩<;>rw [h] at hv
 exacts [cE hA ha hu hv,(cE hA ha hv hu).symm]
include hcol in
lemma mK (h4:NoFourCycle G) {p a:Fin n} (hca:col a=col p) {W:Finset (Fin n)}
 (hW:aB G (Ustar G C) W):#(W∩insert a (aE (Ustar G C) p))≤1:=by
 obtain ⟨c,hc⟩:=aU col hcol hW
 have s:=card_le_one.mp (aF h4 sdiff_subset hW p)
 have hn:∀ v∈aE (Ustar G C) p,col v≠col a:=fun v hv=>hca▸(hcol p v (dQ hv)).symm
 refine card_le_one.mpr fun u hu v hv=>?_
 simp only [mem_inter,mem_insert] at hu hv
 obtain ⟨huW,hu|hu⟩:=hu<;>obtain ⟨hvW,hv|hv⟩:=hv
 ·exact hu.trans hv.symm
 ·exact absurd ((hc _ hvW).trans (hu▸hc _ huW).symm) (hn v hv)
 ·exact absurd ((hc _ huW).trans (hv▸hc _ hvW).symm) (hn u hu)
 ·exact s u (mem_inter.mpr ⟨huW,hu⟩) v (mem_inter.mpr ⟨hvW,hv⟩)
def j1 (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (j k:ℕ) (α:Fin 2)
 (p:Fin n):Prop:=
 IsLeastAO G C∧TopForm G C∧NoFourCycle G∧junk G C={j,k}∧k≠j ∧
  (∀ i∈junk G C,∀ v:Fin n,gateVal n C i (unitInput v)=false) ∧
  (∀ i∈junk G C,¬InCone n C i j)∧orIn n C (opnd C j α)={p}
def gD (n:ℕ) (C:Circuit) (k:ℕ) (Γ:Finset (Fin 2)) (z:Fin 2→ Fin n) (e:Sym2 (Fin n)):Prop:=
 ∃ γ∈Γ,∃ t∈orIn n C (opnd C k (1-γ)),e=s(z γ,t)
def gB (n:ℕ) (G:SimpleGraph (Fin n)) (C:Circuit) (k:ℕ) (Γ:Finset (Fin 2))
 (z:Fin 2→ Fin n):Prop:=
 ∀ γ∈Γ,z γ∈orIn n C (opnd C k γ)∧∀ t∈orIn n C (opnd C k (1-γ)),G.Adj (z γ) t
def j5 (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (j k:ℕ)
 (α:Fin 2) (p:Fin n) (Γ:Finset (Fin 2)) (z:Fin 2→ Fin n):Prop:=
 ∀ e∈Ustar G C,(∃ b∈orIn n C (opnd C j (1-α)),e=s(p,b))∨gD n C k Γ z e
theorem lB (hA:IsAO2 n C) (h4:NoFourCycle G) {i:ℕ} (hi:i∈junk G C) {x:Fin n}
 {w:ℕ} (L:Finset (Fin n))
 (hL:∀ ℓ∈L,ℓ∈aE (Ustar G C) x∧ℓ∈orIn n C w∧aC n G C i ℓ)
 (hx:∀ v∈orIn n C w,aC n G C i v→ G.Adj x v) :
 ∃ P Q Mx Rc:Finset ℕ,(∀ h∈P∪Q,c8 n G C h∧1<#(orIn n C h∩L)) ∧
  (∀ h∈P,orIn n C h⊆orIn n C w∧(h∈Q→ ∀ v∈orIn n C h,G.Adj x v)) ∧
  (∀ m∈Mx,dG n C i m)∧Rc⊆centreless G C ∧
  (∀ a∈Rc,∃ b:Fin 2,OrReaches n C (opnd C a b) i ∧ (orIn n C (opnd C a (1-b))).Nonempty) ∧
  (Rc=∅→ #L≤#Mx∧∀ ℓ∈L,∃ m∈Mx,∃ a∈tops G C,∃ b:Fin 2,
   OrReaches n C (opnd C a b) m∧ℓ∈orIn n C (opnd C a (1-b))) ∧
  #L≤1+#P∧#L≤#Mx+#Rc+#Q:=by
 have hsp:∀ W,aB G (Ustar G C) W→ #(W∩L)≤1:=fun W hW=>
  (card_le_card (inter_subset_inter_left fun ℓ h=>(hL ℓ h).1)).trans
   (aF h4 sdiff_subset hW x)
 obtain ⟨Mx,Rc,Q,hM,hR,hRc,hQ,hpl,cQ⟩:=nD hA hi L hsp fun ℓ h=>(hL ℓ h).2.2
 obtain ⟨P,hP,cP⟩:=jC hA w L hsp
 rw [inter_eq_right.mpr fun ℓ h=>(hL ℓ h).2.1] at cP
 refine ⟨P,Q,Mx,Rc,fun h hh=>(mem_union.mp hh).elim (fun h1=>⟨(hP h h1).1,(hP h h1).2.2⟩)
  fun h1=>⟨(hQ h h1).1,(hQ h h1).2.1⟩,fun h hh=>⟨(hP h hh).2.1,fun hq v hv=>?_⟩,hM,hR,
  hRc,fun he=>⟨?_,hpl he⟩,cP,cQ⟩
 ·obtain ⟨-,-,a,ha,b,hr,hs⟩:=hQ h hq
  exact hx v ((hP h hh).2.1 hv) ⟨a,(mem_filter.mp (hR ha)).1,b,hr,hs hv⟩
 ·have:#Q=0:=card_eq_zero.mpr (eq_empty_of_forall_notMem fun h hh=>by
   obtain ⟨-,-,a,ha,-⟩:=hQ h hh;rw [he] at ha;exact notMem_empty _ ha)
  rw [he,card_empty] at cQ;omega
lemma q6 (h4:NoFourCycle G) {x1 x2:Fin n} (hx:x1≠x2) {L1 L2:Finset (Fin n)}
 (h1:∀ ℓ∈L1,ℓ∈aE (Ustar G C) x1) (h2:∀ ℓ∈L2,ℓ∈aE (Ustar G C) x2)
 {P1 Q1 P2 Q2:Finset ℕ} {w1 w2:ℕ}
 (hPQ1:∀ h∈P1∪Q1,c8 n G C h∧1<#(orIn n C h∩L1))
 (hPQ2:∀ h∈P2∪Q2,c8 n G C h∧1<#(orIn n C h∩L2))
 (ha1:∀ h∈P1,orIn n C h⊆orIn n C w1∧(h∈Q1→ ∀ v∈orIn n C h,G.Adj x1 v))
 (ha2:∀ h∈P2,orIn n C h⊆orIn n C w2∧(h∈Q2→ ∀ v∈orIn n C h,G.Adj x2 v)) :
 (∀ h∈P1∪Q1∪P2∪Q2,c8 n G C h) ∧ #P1+#Q1+#P2+#Q2≤2*#(P1∪Q1∪P2∪Q2):=by
 refine ⟨fun h hh=>?_,vD (disjoint_left.mpr fun h hh hh'=>jP h4 hx
  (S:=orIn n C h∩L2) (fun v hv=>⟨(ha1 h (mem_inter.mp hh).1).2 (mem_inter.mp hh).2 v
   (mem_inter.mp hv).1,dQ (h2 _ (mem_inter.mp hv).2)⟩) (hPQ2 h hh').2)
  (disjoint_left.mpr fun h hh hh'=>jP h4 hx (S:=orIn n C h∩L1) (fun v hv=>
   ⟨dQ (h1 _ (mem_inter.mp hv).2),(ha2 h (mem_inter.mp hh).1).2 (mem_inter.mp hh).2 v
    (mem_inter.mp hv).1⟩) (hPQ1 h hh').2)⟩
 rcases mem_union.mp hh with hh|hh
 ·rcases mem_union.mp hh with hh|hh
  exacts [(hPQ1 h hh).1,(hPQ2 h (mem_union_left _ hh)).1]
 ·exact (hPQ2 h (mem_union_right _ hh)).1
section Z
variable {j k : ℕ} {α : Fin 2} {p : Fin n}
variable (Z : j1 G C j k α p)
include Z
lemma aY:j∈junk G C∧k∈junk G C:=by
 rw [Z.2.2.2.1];simp
theorem cF {X:Finset (Fin n)}
 (hX:∀ e∈Ustar G C,∃ v∈X,v∈e) {P M:Finset ℕ} (hP:∀ h∈P,c8 n G C h)
 (hM:∀ h∈M,aR n G C h)
 (hlt:#(Ustar G C)+#X<2+2*#(centreless G C)+#P+#M) :
 False:=by
 obtain ⟨K,-,-,-,h⟩:=gJ Z.2.2.1 Z.1 Z.2.1
  (by rw [Z.2.2.2.1,card_pair Z.2.2.2.2.1.symm]) (fun _=>True) X hX
 have:=card_le_card (sdiff_subset (s:=X) (t:=K))
 have:=sQ Z.1.1 hP hM
 omega
lemma jL (x:Fin n→ Bool):gateVal n C j x=true ↔
 x p=true∧∃ b∈orIn n C (opnd C j (1-α)),x b=true:=by
 have hv:=(cH Z.1.1 Z.2.1 (aY Z).1 Z.2.2.2.2.2.2.1
  (Z.2.2.2.2.2.1 j (aY Z).1)).1 x
 rcases bG α with ⟨rfl,h⟩|⟨rfl,h⟩<;>rw [h,hv,Z.2.2.2.2.2.2.2]
 ·simp
 ·simp [and_comm]
lemma sO:p∉orIn n C (opnd C j (1-α)):=fun hb=>by
 have:=(jL Z (unitInput p)).mpr ⟨by simp [unitInput],p,hb,by simp [unitInput]⟩
 rw [Z.2.2.2.2.2.1 j (aY Z).1 p] at this;cases this
lemma kD {v:Fin n} (hv:v∈orIn n C (opnd C j (1-α))) : gateVal n C j (pairInput p v)=true:=
 (jL Z _).mpr ⟨by simp [pairInput],v,hv,by simp [pairInput]⟩
lemma cZ {u v:Fin n} (h:gateVal n C j (pairInput u v)=true) :
 ∃ b∈orIn n C (opnd C j (1-α)),s(u,v)=s(p,b):=
 let ⟨hp,b,hb,hbx⟩:=(jL Z _).mp h
 ⟨b,hb,fP (aW hp) (aW hbx) fun e=>sO Z (e▸hb)⟩
lemma sR (b:Fin 2) {x:Fin n→ Bool} (hx:gateVal n C j x=false) :
 wireVal n C (opnd C k b) x=true↔ ∃ c∈orIn n C (opnd C k b),x c=true:=by
 obtain ⟨hkl,hop,-⟩:=aA.mp (aY Z).2
 rw [a8 Z.1.1 Z.2.1 hkl hop b x]
 refine ⟨fun h=>h.resolve_right fun ⟨i,hi,hc,_,hix⟩=>?_,Or.inl⟩
 rw [Z.2.2.2.1,mem_insert,mem_singleton] at hi
 rcases hi with rfl|rfl
 exacts [Bool.false_ne_true (hx▸hix),lt_irrefl _ (aP hc)]
lemma nC {x:Fin n→ Bool}
 (h0:∃ c∈orIn n C (opnd C k 0),x c=true) (h1:∃ d∈orIn n C (opnd C k 1),x d=true) :
 gateVal n C k x=true:=
 let ⟨hkl,hop,_⟩:=aA.mp (aY Z).2
 let ⟨_,hc,hcx⟩:=h0;let ⟨_,hd,hdx⟩:=h1
 (eA Z.1.1 hkl hop x).mpr ⟨bY Z.1.1 hc hcx,bY Z.1.1 hd hdx⟩
lemma lZ :
 Disjoint (orIn n C (opnd C k 0)) (orIn n C (opnd C k 1)):=disjoint_left.mpr fun v h0 h1=>by
 have:=nC Z (x:=unitInput v) ⟨v,h0,by simp [unitInput]⟩ ⟨v,h1,by simp [unitInput]⟩
 rw [Z.2.2.2.2.2.1 k (aY Z).2 v] at this;cases this
lemma gS {γ:Fin 2} {v:Fin n} (h:v∈orIn n C (opnd C k γ)):v∉orIn n C (opnd C k (1-γ)):=by
 rcases bG γ with ⟨rfl,e⟩|⟨rfl,e⟩<;>rw [e]
 exacts [disjoint_left.mp (lZ Z) h,disjoint_right.mp (lZ Z) h]
lemma fO {γ:Fin 2} {z:Fin n} (hz:z∈orIn n C (opnd C k γ))
 (hu:aC n G C k z):∀ d∈orIn n C (opnd C k (1-γ)),G.Adj z d:=fun d hd=>by
 obtain ⟨a,ha,b,hr,hw⟩:=hu
 refine (aT z d).mp (eH Z.1.1 ha hr hw _ ?_ (by simp [pairInput]))
 rcases bG γ with ⟨rfl,h⟩|⟨rfl,h⟩<;>rw [h] at hd
 ·exact nC Z ⟨z,hz,by simp [pairInput]⟩ ⟨d,hd,by simp [pairInput]⟩
 ·exact nC Z ⟨d,hd,by simp [pairInput]⟩ ⟨z,hz,by simp [pairInput]⟩
lemma gV {e:Sym2 (Fin n)} (he:e∈Ustar G C) :
 (∃ b∈orIn n C (opnd C j (1-α)),e=s(p,b))∨∃ γ:Fin 2,∃ c∈orIn n C (opnd C k γ),
  ∃ d∈orIn n C (opnd C k (1-γ)),e=s(c,d)∧aC n G C k c:=by
 induction e using Sym2.ind with|_ u v=>?_
 have hA:=Z.1.1
 have hJ:=Z.2.2.2.1
 cases hjx:gateVal n C j (pairInput u v)
 swap
 ·exact Or.inl (cZ Z hjx)
 right
 obtain ⟨a,ha,hax,b,i,hi,-,hr,hix⟩:=fD Z.1 Z.2.1 he
 obtain ⟨hal,hop,-⟩:=aI.mp ha
 obtain rfl:i=k:=by
  rw [hJ,mem_insert,mem_singleton] at hi
  exact hi.resolve_left fun e=>by rw [e,hjx] at hix;cases hix
 obtain ⟨w,hw,hwx⟩:∃ w∈orIn n C (opnd C a (1-b)),pairInput u v w=true:=by
  rcases (a8 hA Z.2.1 hal hop (1-b) _).mp ((aN hA hal hop b _).mp hax).2 with
   h|⟨i',hi',-,hr',hix'⟩
  ·exact h
  rw [hJ,mem_insert,mem_singleton] at hi'
  rcases hi' with rfl|rfl
  exacts [(Bool.false_ne_true (hjx▸hix')).elim,(jQ hA ha hi hr hr').elim]
 have hk:=(eA hA (aA.mp hi).1 (aA.mp hi).2.1 _).mp hix
 obtain ⟨c,hc,hcx⟩:=(sR Z 0 hjx).mp hk.1
 obtain ⟨d,hd,hdx⟩:=(sR Z 1 hjx).mp hk.2
 have hus:=fP (aW hcx) (aW hdx) fun e=>disjoint_left.mp (lZ Z) hc (e▸hd)
 rcases Sym2.mem_iff.mp (hus▸Sym2.mem_iff.mpr (aW hwx):w∈s(c,d)) with h|h
 ·exact ⟨0,c,hc,d,hd,hus,a,ha,b,hr,h▸hw⟩
 ·exact ⟨1,d,hd,c,hc,hus.trans Sym2.eq_swap,a,ha,b,hr,h▸hw⟩
lemma tH (Γ:Finset (Fin 2)) (z:Fin 2→ Fin n) (hz:gB n G C k Γ z)
 {V:Finset (Sym2 (Fin n))} (hV:V⊆Ustar G C) (hVE:∀ e∈V,gD n C k Γ z e) :
 ∃ P:Finset ℕ,(∀ h∈P,c8 n G C h∧∃ γ∈Γ,orIn n C h⊆orIn n C (opnd C k (1-γ))) ∧ #V≤#P+1:=by
 classical
 have hA:=Z.1.1
 have one:∀ γ∈Γ,(∀ γ'∈Γ,γ'=γ)→ ∃ P:Finset ℕ,(∀ h∈P,c8 n G C h ∧
  ∃ γ∈Γ,orIn n C h⊆orIn n C (opnd C k (1-γ)))∧#V≤#P+1:=by
  intro γ hγ hu
  obtain ⟨P,hP,hc⟩:=fC hA hV (opnd C k (1-γ)) (aE V (z γ))
   fun W hW=>aF Z.2.2.1 (hV.trans sdiff_subset) hW _
  refine ⟨P,fun h hh=>⟨(mZ hA hV (hP h hh)).1,γ,hγ,(mZ hA hV (hP h hh)).2⟩,
   (card_le_card (t:=(orIn n C (opnd C k (1-γ))∩aE V (z γ)).image (s(z γ,·)))
    fun e he=>?_).trans (card_image_le.trans hc)⟩
  obtain ⟨γ',hγ',t,ht,rfl⟩:=hVE e he
  obtain rfl:=hu γ' hγ'
  exact mem_image_of_mem _ (mem_inter.mpr ⟨ht,aD.mpr he⟩)
 by_cases h0:(0:Fin 2)∈Γ<;>by_cases h1:(1:Fin 2)∈Γ
 ·obtain ⟨P,hP,hc⟩:=kJ hA Z.2.2.1 (w:=(opnd C k ·)) (lZ Z)
   (fun β=>(hz β (by fin_cases β<;>assumption)).1) ((hz 0 h0).2 _ (hz 1 h1).1) hV
   fun e he=>let ⟨γ,_,t,ht,e⟩:=hVE e he;⟨γ,t,ht,e⟩
  refine ⟨P,fun h hh=>?_,hc⟩
  obtain ⟨β,hb⟩:=hP h hh
  exact ⟨(mZ hA hV hb).1,1-β,by fin_cases β<;>assumption,
   by rw [sub_sub_cancel];exact (mZ hA hV hb).2⟩
 ·exact one 0 h0 fun γ' _=>by fin_cases γ'<;>simp_all
 ·exact one 1 h1 fun γ' _=>by fin_cases γ'<;>simp_all
 ·have:V=∅:=eq_empty_of_forall_notMem fun e he=>by
   obtain ⟨γ,hγ,-⟩:=hVE e he;fin_cases γ<;>simp_all
  exact ⟨∅,by simp,by simp [this]⟩
theorem kI (Γ:Finset (Fin 2)) (z:Fin 2→ Fin n) (hz:gB n G C k Γ z)
 (A:Finset (Fin n)) (hA1:#A≤1) (hAB:A⊆orIn n C (opnd C j (1-α)))
 (hAsp:∀ W,aB G (Ustar G C) W→ #(W∩(A∪aE (Ustar G C) p))≤1)
 (hAL:∀ a∈A,s(p,a)∈Ustar G C→ gD n C k Γ z s(p,a))
 (hAT:∀ γ∈Γ,∀ a∈A,a∈orIn n C (opnd C k (1-γ))→ ∀ ℓ∈aE (Ustar G C) p,
  ℓ∈orIn n C (opnd C k (1-γ))→ False)
 (hU:j5 n G C j k α p Γ z) :
 ∃ P:Finset ℕ,(∀ h∈P,c8 n G C h∧(orIn n C h⊆orIn n C (opnd C j (1-α)) ∨
  ∃ γ∈Γ,orIn n C h⊆orIn n C (opnd C k (1-γ)))) ∧
  #(Ustar G C)+#A≤#P+2:=by
 classical
 obtain ⟨L,hL⟩:∃ L:Finset (Fin n),∀ b,b∈L↔ b∈orIn n C (opnd C j (1-α)) ∧
  s(p,b)∈Ustar G C∧¬gD n C k Γ z s(p,b):=⟨_,fun b=>mem_filter⟩
 have hLN:L⊆aE (Ustar G C) p:=fun b hb=>aD.mpr ((hL b).mp hb).2.1
 obtain ⟨PL,hPL,cL⟩:=tH Z Γ z hz (filter_subset (gD n C k Γ z) (Ustar G C))
  fun e he=>(mem_filter.mp he).2
 obtain ⟨PB,hPB,cB⟩:=jC Z.1.1 (opnd C j (1-α)) (A∪L) fun W hW=>
  (card_le_card (inter_subset_inter_left (union_subset_union subset_rfl hLN))).trans (hAsp W hW)
 rw [inter_eq_right.mpr (union_subset hAB fun b hb=>((hL b).mp hb).1),
  card_union_of_disjoint (disjoint_left.mpr fun a ha hl=>
   ((hL a).mp hl).2.2 (hAL a ha ((hL a).mp hl).2.1))] at cB
 have hdis:Disjoint PL PB:=disjoint_left.mpr fun h h1 h2=>by
  obtain ⟨-,γ,hγ,hsub⟩:=hPL h h1
  obtain ⟨x,hx,y,hy,hxy⟩:=one_lt_card.mp (hPB h h2).2.2
  have key:∀ x y,x∈L→ y∈A∪L→ x∈orIn n C (opnd C k (1-γ)) →
   y∈orIn n C (opnd C k (1-γ))→ x≠y→ False:=fun x y hx hy hxT hyT hxy=>by
   rcases mem_union.mp hy with hy|hy
   ·exact hAT γ hγ y hy hyT x (hLN hx) hxT
   by_cases hzp:z γ=p
   ·exact ((hL x).mp hx).2.2 ⟨γ,hγ,x,hxT,by rw [hzp]⟩
   exact hxy (aQ Z.2.2.1 (Ne.symm hzp) (dQ (hLN hx)) ((hz γ hγ).2 x hxT)
    (dQ (hLN hy)) ((hz γ hγ).2 y hyT))
  rw [mem_inter] at hx hy
  rcases mem_union.mp hx.2 with hxA|hxL
  ·rcases mem_union.mp hy.2 with hyA|hyL
   ·exact hxy (card_le_one.mp hA1 x hxA y hyA)
   ·exact key y x hyL hx.2 (hsub hy.1) (hsub hx.1) (Ne.symm hxy)
  ·exact key x y hxL hy.2 (hsub hx.1) (hsub hy.1) hxy
 refine ⟨PL∪PB,fun h hh=>(mem_union.mp hh).elim
  (fun h1=>⟨(hPL h h1).1,Or.inr (hPL h h1).2⟩) fun h1=>⟨(hPB h h1).1,Or.inl (hPB h h1).2.1⟩,
  ?_⟩
 have:=card_filter_add_card_filter_not (s:=Ustar G C) (gD n C k Γ z)
 have:#((Ustar G C).filter fun e=>¬gD n C k Γ z e)≤#L:=
  (card_le_card (t:=L.image (s(p,·))) fun e he=>by
   obtain ⟨he,hne⟩:=mem_filter.mp he
   rcases hU e he with ⟨b,hb,rfl⟩|h
   exacts [mem_image_of_mem _ ((hL b).mpr ⟨hb,he,hne⟩),absurd h hne]).trans card_image_le
 rw [card_union_of_disjoint hdis];omega
theorem mQ (Γ:Finset (Fin 2)) (zf:Fin 2→ Fin n) (hz:gB n G C k Γ zf)
 (A:Finset (Fin n)) (hA1:#A≤1) (hAB:A⊆orIn n C (opnd C j (1-α)))
 (hAsp:∀ W,aB G (Ustar G C) W→ #(W∩(A∪aE (Ustar G C) p))≤1)
 (hAL:∀ a∈A,s(p,a)∈Ustar G C→ gD n C k Γ zf s(p,a))
 (hAT:∀ γ∈Γ,∀ a∈A,a∈orIn n C (opnd C k (1-γ))→ ∀ ℓ∈aE (Ustar G C) p,
  ℓ∈orIn n C (opnd C k (1-γ))→ False)
 (hU:j5 n G C j k α p Γ zf)
 {Q M:Finset ℕ} {X:Finset (Fin n)} (hQ:∀ h∈Q,c8 n G C h ∧
  ¬orIn n C h⊆orIn n C (opnd C j (1-α))∧∀ γ∈Γ,¬orIn n C h⊆orIn n C (opnd C k (1-γ)))
 (hM:∀ h∈M,aR n G C h) (hpX:p∈X) (hzX:∀ γ∈Γ,zf γ∈X)
 (hlt:#X<2*#(centreless G C)+#Q+#M+#A):False:=by
 obtain ⟨P,hP,hu⟩:=kI Z Γ zf hz A hA1 hAB hAsp hAL hAT hU
 have hd:Disjoint P Q:=disjoint_left.mpr fun h hp hq=>by
  rcases (hP h hp).2 with hs|⟨γ,hγ,hs⟩
  exacts [(hQ h hq).2.1 hs,(hQ h hq).2.2 γ hγ hs]
 refine cF Z (X:=X) (fun e he=>?_) (P:=P∪Q) (M:=M)
  (fun h hh=>(mem_union.mp hh).elim (fun h1=>(hP h h1).1) fun h1=>(hQ h h1).1) hM ?_
 ·rcases hU e he with ⟨b,-,rfl⟩|⟨γ,hγ,t,-,rfl⟩
  exacts [⟨p,hpX,Sym2.mem_mk_left _ _⟩,⟨zf γ,hzX γ hγ,Sym2.mem_mk_left _ _⟩]
 ·rw [card_union_of_disjoint hd];omega
theorem f9 (Γ:Finset (Fin 2)) (zf:Fin 2→ Fin n) (hz:gB n G C k Γ zf)
 (hU:j5 n G C j k α p Γ zf)
 {Q M:Finset ℕ} {X:Finset (Fin n)} (hQ:∀ h∈Q,c8 n G C h ∧
  ¬orIn n C h⊆orIn n C (opnd C j (1-α))∧∀ γ∈Γ,¬orIn n C h⊆orIn n C (opnd C k (1-γ)))
 (hM:∀ h∈M,aR n G C h) (hpX:p∈X) (hzX:∀ γ∈Γ,zf γ∈X)
 (hlt:#X<2*#(centreless G C)+#Q+#M):False:=
 mQ Z Γ zf hz ∅ (by simp) (empty_subset _)
  (fun W hW=>by rw [empty_union];exact aF Z.2.2.1 sdiff_subset hW p)
  (by simp) (by simp) hU hQ hM hpX hzX (by rw [card_empty];omega)
lemma uX (hc:#(centreless G C)=0) {u v:Fin n} (he:s(u,v)∈Ustar G C):∃ m,aR n G C m:=by
 obtain ⟨a,ha,-,b,i,hi,-,hr,-⟩:=fD Z.1 Z.2.1 he
 obtain ⟨m,hm,-⟩:=dR Z.1.1 hi hr (nonempty_iff_ne_empty.mpr fun e=>
  (card_pos.mpr ⟨a,c7 ha e⟩).ne' hc)
 exact ⟨_,hm⟩
theorem n4 (hU:∀ e∈Ustar G C,∃ b∈orIn n C (opnd C j (1-α)),e=s(p,b)):False:=by
 classical
 obtain ⟨P,hP,hc⟩:=jC Z.1.1 (opnd C j (1-α)) (aE (Ustar G C) p)
  fun W hW=>aF Z.2.2.1 sdiff_subset hW p
 have hu:#(Ustar G C)≤(orIn n C (opnd C j (1-α))∩aE (Ustar G C) p).card:=
  (card_le_card (t:=(orIn n C (opnd C j (1-α))∩aE (Ustar G C) p).image (s(p,·))) fun e he=>by
   obtain ⟨b,hb,rfl⟩:=hU e he
   exact mem_image_of_mem _ (mem_inter.mpr ⟨hb,aD.mpr he⟩)).trans card_image_le
 have hX:∀ e∈Ustar G C,∃ v∈({p}:Finset (Fin n)),v∈e:=fun e he=>by
  obtain ⟨b,-,rfl⟩:=hU e he;exact ⟨p,mem_singleton_self _,Sym2.mem_mk_left _ _⟩
 have hP':=fun h hh=>(hP h hh).1
 by_cases h:#(Ustar G C)=0∨0<#(centreless G C)
 ·exact cF Z hX hP' (M:=∅) (by simp) (by simp only [card_singleton,card_empty];omega)
 obtain ⟨e,he⟩:=card_pos.mp (by omega:0<#(Ustar G C))
 obtain ⟨b,-,rfl⟩:=hU e he
 obtain ⟨m,hm⟩:=uX Z (by omega) he
 exact cF Z hX hP' (M:={m}) (by simpa using hm) (by simp only [card_singleton];omega)
include hR1 hcol in
theorem kP (hjk:¬InCone n C j k) : ∃ b₁ b₂:Fin n,b₁≠b₂ ∧
 (b₁∈orIn n C (opnd C j (1-α))∧G.Adj p b₁ ∧
  wireVal n (aG n C j) C.output (pairInput p b₁)=false) ∧
 (b₂∈orIn n C (opnd C j (1-α))∧G.Adj p b₂ ∧
  wireVal n (aG n C j) C.output (pairInput p b₂)=false):=by
 obtain ⟨hC,hT,h4,hJ,hkj,-,-,-⟩:=id Z
 have hA:=hC.1
 have hjl:=(aA.mp (aY Z).1).1
 have hL:∀ u v,G.Adj u v→ wireVal n (aG n C j) C.output (pairInput u v)=false →
  ∃ b∈orIn n C (opnd C j (1-α)),G.Adj p b∧s(u,v)=s(p,b) ∧
   wireVal n (aG n C j) C.output (pairInput p b)=false:=fun u v huv hl=>by
  obtain ⟨-,-,-,-,hjx,-⟩:=f7 hC hT hJ hkj hjk huv hl
  obtain ⟨b,hb,e⟩:=cZ Z hjx
  refine ⟨b,hb,?_,e,by rw [← dT e];exact hl⟩
  rcases Sym2.eq_iff.mp e with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  exacts [huv,huv.symm]
 by_contra hno
 by_cases h1:∃ b0∈orIn n C (opnd C j (1-α)),G.Adj p b0 ∧
  wireVal n (aG n C j) C.output (pairInput p b0)=false
 swap
 ·refine jJ hC hjl fun u v huv=>?_
  by_contra hl
  obtain ⟨b,hb,hpb,-,hl'⟩:=hL u v huv (by simpa using hl)
  exact h1 ⟨b,hb,hpb,hl'⟩
 obtain ⟨b0,hb0,hpb,hl0⟩:=h1
 have hall:∀ u v,G.Adj u v→ wireVal n (aG n C j) C.output (pairInput u v)=false →
  s(u,v)=s(p,b0):=fun u v huv hl=>by
  obtain ⟨b,hb,hpb',e,hl'⟩:=hL u v huv hl
  by_cases hbb:b=b0
  ·rw [e,hbb]
  ·exact (hno ⟨b,b0,hbb,⟨hb,hpb',hl'⟩,hb0,hpb,hl0⟩).elim
 have hpn:(p:ℕ)<n+j:=by have:=p.2;omega
 have hbn:(b0:ℕ)<n+j:=by have:=b0.2;omega
 have hev:∀ x,GateOp.and.eval [wireVal n C p x,wireVal n C b0 x]=true ↔
  x p=true∧x b0=true:=fun x=>by
  simp only [GateOp.eval,List.all_cons,List.all_nil,id,Bool.and_true,Bool.and_eq_true,
   bA C x]
 obtain ⟨hD,hsub,hkeep⟩:=cT hC hjl (Or.inl rfl) hpn hbn
  (fun x h=>(jL Z x).mpr ⟨((hev x).mp h).1,b0,hb0,((hev x).mp h).2⟩)
  (fun u v huv=>by
   cases hk:wireVal n (aG n C j) C.output (pairInput u v)
   ·right;rw [hev,dT (hall u v huv hk)];simp [pairInput]
   ·exact Or.inl rfl)
 have hjD:j∉junk G (aL C j ⟨GateOp.and,[(p:ℕ),(b0:ℕ)]⟩):=fun hj'=>by
  refine (aA.mp hj').2.2 fun y hy=>?_
  have h1:=(b7 hA hjl (Or.inl rfl) hpn hbn y).2.2.2.2.2
  rw [show gateVal n _ j y=wireVal n _ (n+j) y from rfl,h1,hev] at hy
  exact (dJ y).mpr ⟨p,b0,hpb,hy.1,hy.2⟩
 have hone:junk G (aL C j ⟨GateOp.and,[(p:ℕ),(b0:ℕ)]⟩)={k}:=by
  ext k'
  simp only [mem_singleton]
  refine ⟨fun hk'=>?_,fun he=>he▸hkeep k (aY Z).2 hkj hjk⟩
  rcases hsub k' hk' with he|hk''
  ·exact absurd (he▸hk') hjD
  ·rw [hJ,mem_insert,mem_singleton] at hk''
   exact hk''.resolve_left fun he=>hjD (he▸hk')
 exact hR1 n G _ col hcol h4 hD (by rw [hone,card_singleton])
theorem rL (H:(∀ γ,(orIn n C (opnd C k γ)).Nonempty)→ ∀ (Γ:Finset (Fin 2)) (z:Fin 2→ Fin n),
 (gB n G C k Γ z) →
 (∀ γ∈Γ,aC n G C k (z γ))→ (∀ e∈Ustar G C,
  (∃ b∈orIn n C (opnd C j (1-α)),e=s(p,b))∨gD n C k Γ z e)→ False)
 (N:(∀ γ,(orIn n C (opnd C k γ)).Nonempty)→ ∀ γ z,orIn n C (opnd C k γ)={z} →
  ¬aC n G C k z→ False):False:=by
 classical
 by_cases hne:∀ γ:Fin 2,(orIn n C (opnd C k γ)).Nonempty
 swap
 ·refine n4 Z fun e he=>(gV Z he).resolve_right fun ⟨γ,c,hc,d,hd,_⟩=> hne fun γ'=>?_
  rcases aS γ γ' with rfl|rfl
  exacts [⟨c,hc⟩,⟨d,hd⟩]
 by_cases hw:∀ γ:Fin 2,2≤#(orIn n C (opnd C k γ))
 ·set zf:Fin 2→ Fin n:=fun γ=>
   if h:∃ z∈orIn n C (opnd C k γ),aC n G C k z then h.choose else p
  have hzf:∀ γ,(∃ z∈orIn n C (opnd C k γ),aC n G C k z) →
   zf γ∈orIn n C (opnd C k γ)∧aC n G C k (zf γ):=fun γ h=>by
   simp only [zf,h,↓reduceDIte];exact h.choose_spec
  refine H hne (univ.filter fun γ=>∃ z∈orIn n C (opnd C k γ),aC n G C k z) zf
   (fun γ hγ=>?_) (fun γ hγ=>(hzf γ (mem_filter.mp hγ).2).2) fun e he=>?_
  ·have:=hzf γ (mem_filter.mp hγ).2;exact ⟨this.1,fO Z this.1 this.2⟩
  rcases gV Z he with h|⟨γ,c,hc,d,hd,he',hu⟩
  ·exact Or.inl h
  have hγ:∃ z∈orIn n C (opnd C k γ),aC n G C k z:=⟨c,hc,hu⟩
  have hcz:c=zf γ:=bC Z.2.2.1 (hw (1-γ)) (fO Z hc hu)
   (fO Z (hzf γ hγ).1 (hzf γ hγ).2)
  exact Or.inr ⟨γ,mem_filter.mpr ⟨mem_univ _,hγ⟩,d,hd,hcz▸he'⟩
 simp only [not_forall,not_le] at hw
 obtain ⟨γ,hγ⟩:=hw
 obtain ⟨z,hz⟩:=card_eq_one.mp (show #(orIn n C (opnd C k γ))=1 by
  have:=card_pos.mpr (hne γ);omega)
 by_cases hu:aC n G C k z
 ·have hzm:z∈orIn n C (opnd C k γ):=hz▸mem_singleton_self z
  refine H hne {γ} (fun _=>z) (fun γ' h=>by
   rw [mem_singleton.mp h];exact ⟨hzm,fO Z hzm hu⟩) (fun _ _=>hu) fun e he=>?_
  rcases gV Z he with h|⟨γ',c,hc,d,hd,e,-⟩
  ·exact Or.inl h
  right
  rcases aS γ γ' with rfl|rfl
  ·rw [hz,mem_singleton] at hc;exact ⟨_,mem_singleton_self _,d,hd,by rw [e,hc]⟩
  ·rw [sub_sub_cancel,hz,mem_singleton] at hd
   exact ⟨_,mem_singleton_self _,c,hc,by rw [e,hd,Sym2.eq_swap]⟩
 ·exact N hne γ z hz hu
lemma nF {γ:Fin 2} {z:Fin n} (hγ:orIn n C (opnd C k γ)={z}) (hz:¬aC n G C k z) :
 ∀ e∈Ustar G C,(∃ b∈orIn n C (opnd C j (1-α)),e=s(p,b)) ∨
  ∃ t∈orIn n C (opnd C k (1-γ)),aC n G C k t∧e=s(z,t):=fun e he=>by
 rcases gV Z he with h|⟨γ',c,hc,d,hd,e,hu⟩
 ·exact Or.inl h
 right
 rcases aS γ γ' with rfl|rfl
 ·rw [hγ,mem_singleton] at hc;exact absurd (hc▸hu) hz
 ·rw [sub_sub_cancel,hγ,mem_singleton] at hd
  exact ⟨c,hc,hu,by rw [e,hd,Sym2.eq_swap]⟩
include hcol in
lemma sZ (Γ:Finset (Fin 2)) (z:Fin 2→ Fin n) (hz:gB n G C k Γ z)
 (hUs:∀ γ∈Γ,aC n G C k (z γ)) :
 ∃ M:Finset ℕ,(∀ h∈M,aR n G C h∧n+k≤h) ∧ Γ.card≤#M+2*#(centreless G C):=by
 classical
 have hA:=Z.1.1
 rcases Nat.eq_zero_or_pos #(centreless G C) with hc|hc
 swap
 ·exact ⟨∅,by simp,by have:=card_le_univ Γ;simp only [Fintype.card_fin] at this;simp;omega⟩
 choose! md hmd hmk hmr using fun γ (hγ:γ∈Γ)=>(by
  obtain ⟨a,ha,β,hr,hw⟩:=hUs γ hγ
  obtain ⟨m,hm,-,hwm,hmk,r,hr'⟩:=dR hA (aY Z).2 hr
   (nonempty_iff_ne_empty.mpr fun e=>(card_pos.mpr ⟨a,c7 ha e⟩).ne' hc)
  exact ⟨m,hm,(aX hmk).1,r,hr',a,ha,β,hwm,hw⟩:∃ m,aR n G C (n+m) ∧
   n+k≤n+m∧∃ r,r∈orIn n C (n+m)∧∃ a∈tops G C,∃ β:Fin 2,
    OrReaches n C (opnd C a β) m∧z γ∈orIn n C (opnd C a (1-β)))
 refine ⟨Γ.image (n+md ·),fun h hh=>?_,?_⟩
 ·obtain ⟨γ,hγ,rfl⟩:=mem_image.mp hh;exact ⟨hmd γ hγ,hmk γ hγ⟩
 rw [card_image_of_injOn fun γ hγ γ' hγ' he=>?_]
 ·omega
 by_contra hne
 obtain ⟨r,hr,-⟩:=hmr γ hγ
 have hW:=gO hA hr (W:={z γ,z γ'}) fun w hw=>by
  rcases mem_insert.mp hw with rfl|hw
  ·obtain ⟨-,-,h⟩:=hmr γ hγ;exact h
  ·obtain ⟨-,-,a,ha,b,h1,h2⟩:=hmr γ' hγ'
   rw [mem_singleton.mp hw]
   exact ⟨a,ha,b,by rw [show md γ=md γ' by simpa using he];exact h1,h2⟩
 obtain ⟨c,hcw⟩:=aU col hcol hW
 exact hcol _ _ ((hz γ hγ).2 _ ((aS γ γ').resolve_left (Ne.symm hne)▸(hz γ' hγ').1))
  ((hcw _ (mem_insert_self _ _)).trans (hcw _ (mem_insert_of_mem (mem_singleton_self _))).symm)
lemma n9 (h0:OrReaches n C (opnd C k 0) j)
 (h1:OrReaches n C (opnd C k 1) j) (hne:∀ γ,(orIn n C (opnd C k γ)).Nonempty) :
 ∃ M:Finset ℕ,(∀ h∈M,aR n G C h∧h<n+k)∧#M=2:=by
 have hA:=Z.1.1
 obtain ⟨m0,hm0,-,hr0,-,v,hv⟩:=dR hA (aY Z).1 h0 (hne 0)
 obtain ⟨m1,hm1,-,hr1,-⟩:=dR hA (aY Z).1 h1 (hne 1)
 have:=(aX hr0).1;have:=(aX hr1).1
 have:=aH hA (aA.mp (aY Z).2).1 0
 have:=aH hA (aA.mp (aY Z).2).1 1
 refine ⟨{n+m0,n+m1},?_,card_pair fun he=>disjoint_left.mp (lZ Z)
  (a6 hA hr0 hv) (a6 hA hr1 (he▸hv))⟩
 simp only [mem_insert,mem_singleton]
 rintro h (rfl|rfl)<;>constructor<;>first|assumption|omega
lemma e5 {v:Fin n} (hv:v∈orIn n C (opnd C j (1-α))) (hu:aC n G C j v):G.Adj p v:=
 let ⟨_,ha,_,hr,hw⟩:=hu
 (aT p v).mp (eH Z.1.1 ha hr hw _ (kD Z hv) (by simp [pairInput]))
lemma l4 {u v:Fin n} (he:s(u,v)∈Ustar G C) :
 gateVal n C j (pairInput u v)=true∨gateVal n C k (pairInput u v)=true:=by
 obtain ⟨-,-,-,-,i,hi,-,-,hix⟩:=fD Z.1 Z.2.1 he
 rw [Z.2.2.2.1,mem_insert,mem_singleton] at hi
 rcases hi with rfl|rfl
 exacts [Or.inl hix,Or.inr hix]
lemma pP:¬aC n G C j p:=fun ⟨_,ha,_,hr,hw⟩=>
 (aA.mp (aY Z).1).2.2 fun x hx=>eH Z.1.1 ha hr hw x hx ((jL Z x).mp hx).1
lemma l5 {u v:Fin n} (he:s(u,v)∈Ustar G C)
 (hj:gateVal n C j (pairInput u v)=true) (hk:gateVal n C k (pairInput u v)=false) :
 ∃ ℓ∈orIn n C (opnd C j (1-α)),aC n G C j ℓ∧s(u,v)=s(p,ℓ):=by
 have hA:=Z.1.1
 have hJ:=Z.2.2.2.1
 obtain ⟨a,ha,hax,b,i,hi,-,hr,hix⟩:=fD Z.1 Z.2.1 he
 obtain ⟨hal,hop,-⟩:=aI.mp ha
 obtain rfl:i=j:=by
  rw [hJ,mem_insert,mem_singleton] at hi
  exact hi.resolve_right fun e=>by rw [e,hk] at hix;cases hix
 obtain ⟨w,hw,hwx⟩:∃ w∈orIn n C (opnd C a (1-b)),pairInput u v w=true:=by
  rcases (a8 hA Z.2.1 hal hop (1-b) _).mp ((aN hA hal hop b _).mp hax).2 with
   h|⟨i',hi',-,hr',hix'⟩
  ·exact h
  rw [hJ,mem_insert,mem_singleton] at hi'
  rcases hi' with rfl|rfl
  exacts [(jQ hA ha hi hr hr').elim,(Bool.false_ne_true (hk▸hix')).elim]
 obtain ⟨c,hc,e⟩:=cZ Z hj
 refine ⟨c,hc,?_,e⟩
 rw [dT e] at hwx
 rcases aW hwx with rfl|rfl
 exacts [(pP Z ⟨a,ha,b,hr,hw⟩).elim,⟨a,ha,b,hr,hw⟩]
lemma s8 {γ:Fin 2} (hγ:orIn n C (opnd C k γ)={p})
 (hz:¬aC n G C k p) {Mi:Finset ℕ} (hMi:∀ h∈Mi,aR n G C h∧h<n+k)
 (h1:Mi.Nonempty):False:=by
 classical
 have hA:=Z.1.1
 have hU:=nF Z hγ hz
 obtain ⟨P,hP,hc⟩:=kB hA {opnd C j (1-α),opnd C k (1-γ)} (aE (Ustar G C) p)
  fun W hW=>aF Z.2.2.1 sdiff_subset hW p
 rw [inter_eq_right.mpr fun ℓ hℓ=>by
  rcases hU _ (aD.mp hℓ) with ⟨b,hb,e⟩|⟨t,ht,-,e⟩<;>
   rcases Sym2.eq_iff.mp e with ⟨-,rfl⟩|⟨rfl,rfl⟩<;>simp_all] at hc
 have:=card_le_two (a:=opnd C j (1-α)) (b:=opnd C k (1-γ))
 have hu:#(Ustar G C)≤#(aE (Ustar G C) p):=
  (card_le_card (t:=(aE (Ustar G C) p).image (s(p,·))) fun e he=>by
   rcases hU e he with ⟨b,-,rfl⟩|⟨t,-,-,rfl⟩<;>
    exact mem_image_of_mem _ (aD.mpr he)).trans card_image_le
 have hX:∀ e∈Ustar G C,∃ v∈({p}:Finset (Fin n)),v∈e:=fun e he=>by
  rcases hU e he with ⟨b,-,rfl⟩|⟨t,-,-,rfl⟩<;>exact ⟨p,mem_singleton_self _,by simp⟩
 have hP':=fun h hh=>(hP h hh).1
 have hM':=fun h hh=>(hMi h hh).1
 have:=card_pos.mpr h1
 by_cases h2:1<2*#(centreless G C)+#Mi
 ·exact cF Z hX hP' hM' (by rw [card_singleton];omega)
 by_cases hall:∀ e∈Ustar G C,∃ b∈orIn n C (opnd C j (1-α)),e=s(p,b)
 ·exact n4 Z hall
 simp only [not_forall,not_exists,not_and] at hall
 obtain ⟨e,he,hne⟩:=hall
 rcases hU e he with ⟨b,hb,rfl⟩|⟨t,-,⟨a,ha,β,hr,-⟩,-⟩
 ·exact hne b hb rfl
 obtain ⟨m,hm,-,-,hmk,-⟩:=dR hA (aY Z).2 hr (nonempty_iff_ne_empty.mpr fun e'=>
  (card_pos.mpr ⟨a,c7 ha e'⟩).ne' (by omega))
 have:=(aX hmk).1
 refine cF Z hX hP' (M:=insert (n+m) Mi) (fun h hh=>(mem_insert.mp hh).elim (·▸hm) (hM' h)) ?_
 rw [card_insert_of_notMem fun h=>by have:=(hMi _ h).2;omega,card_singleton];omega
lemma rA {γ:Fin 2} {z:Fin n} (hγ:orIn n C (opnd C k γ)={z}) (hz:¬aC n G C k z) :
 (∀ e∈Ustar G C,∃ v∈({p,z}:Finset (Fin n)),v∈e)∧∃ Lz:Finset (Fin n),
  (∀ t∈Lz,t∈orIn n C (opnd C k (1-γ))∧t∈aE (Ustar G C) z∧aC n G C k t) ∧
  #(Ustar G C)≤(orIn n C (opnd C j (1-α))∩aE (Ustar G C) p).card+#Lz:=by
 classical
 have hU:=nF Z hγ hz
 refine ⟨fun e he=>?_,(orIn n C (opnd C k (1-γ))).filter fun t=>
  t∈aE (Ustar G C) z∧aC n G C k t,fun t ht=>by simpa using ht,?_⟩
 ·rcases hU e he with ⟨b,-,rfl⟩|⟨t,-,-,rfl⟩
  ·exact ⟨p,by simp,by simp⟩
  ·exact ⟨z,by simp,by simp⟩
 refine (card_le_card (t:=(orIn n C (opnd C j (1-α))∩aE (Ustar G C) p).image
  (s(p,·))∪((orIn n C (opnd C k (1-γ))).filter fun t=>
   t∈aE (Ustar G C) z∧aC n G C k t).image (s(z,·))) fun e he=>?_).trans
  ((card_union_le _ _).trans (add_le_add card_image_le card_image_le))
 rcases hU e he with ⟨b,hb,rfl⟩|⟨t,ht,htU,rfl⟩
 ·exact mem_union_left _ (mem_image_of_mem _ (mem_inter.mpr ⟨hb,aD.mpr he⟩))
 ·exact mem_union_right _ (mem_image_of_mem _ (mem_filter.mpr ⟨ht,aD.mpr he,htU⟩))
lemma tG (h0:OrReaches n C (opnd C k 0) j)
 (h1:OrReaches n C (opnd C k 1) j) (hne:∀ γ,(orIn n C (opnd C k γ)).Nonempty)
 {γ:Fin 2} {z:Fin n} (hγ:orIn n C (opnd C k γ)={z}) (hz:¬aC n G C k z) :
 False:=by
 classical
 have hA:=Z.1.1
 have h4:=Z.2.2.1
 obtain ⟨Mi,hMi,cMi⟩:=n9 Z h0 h1 hne
 by_cases hzp:z=p
 ·subst hzp;exact s8 Z hγ hz hMi (card_pos.mp (by omega))
 obtain ⟨hX,Lz,hLz,hu⟩:=rA Z hγ hz
 obtain ⟨PB,hPB,cB⟩:=jC hA (opnd C j (1-α)) (aE (Ustar G C) p) fun W hW=>
  aF h4 sdiff_subset hW p
 obtain ⟨Mx,Rc,Pf,hMx,hRc,-,hPf,-,cf⟩:=nD hA (aY Z).2 Lz
  (fun W hW=>(card_le_card (inter_subset_inter_left fun t ht=>(hLz t ht).2.1)).trans
   (aF h4 sdiff_subset hW z)) fun t ht=>(hLz t ht).2.2
 have hdis:Disjoint PB Pf:=disjoint_left.mpr fun h hp1 hp2=>by
  refine jP h4 hzp (S:=orIn n C h∩Lz) (fun v hv=>⟨dQ (hLz v (mem_inter.mp hv).2).2.1,
   ?_⟩) (hPf h hp2).2.1
  obtain ⟨a,ha,b,hr,hw⟩:=(hLz v (mem_inter.mp hv).2).2.2
  have hj:=kD Z ((hPB h hp1).2.1 (mem_inter.mp hv).1)
  exact (aT p v).mp (eH hA ha hr hw _ ((eA hA (aA.mp
   (aY Z).2).1 (aA.mp (aY Z).2).2.1 _).mpr ⟨aO hA _ h0 hj,
    aO hA _ h1 hj⟩) (by simp [pairInput]))
 have hMd:Disjoint Mi (Mx.image (n+·)):=disjoint_left.mpr fun h hh hh'=>by
  obtain ⟨m,hm,rfl⟩:=mem_image.mp hh'
  have:=(aX (lX hA (hMx m hm))).1;have:=(hMi _ hh).2;omega
 have:=card_le_card hRc
 refine cF Z hX (P:=PB∪Pf) (M:=Mi∪Mx.image (n+·))
  (fun h hh=>(mem_union.mp hh).elim (fun h1=>(hPB h h1).1) fun h2=>(hPf h h2).1)
  (fun h hh=>(mem_union.mp hh).elim (fun h1=>(hMi h h1).1) fun hh'=>by
   obtain ⟨m,hm,rfl⟩:=mem_image.mp hh';exact c5 hA (aY Z).2 (hMx m hm)) ?_
 rw [card_union_of_disjoint hdis,card_union_of_disjoint hMd,cMi,
  card_image_of_injective _ (add_right_injective n),card_pair (Ne.symm hzp)]
 omega
include hcol in
lemma tB (h0:OrReaches n C (opnd C k 0) j)
 (h1:OrReaches n C (opnd C k 1) j) (hne:∀ γ,(orIn n C (opnd C k γ)).Nonempty)
 (Γ:Finset (Fin 2)) (z:Fin 2→ Fin n)
 (hz:gB n G C k Γ z)
 (hUs:∀ γ∈Γ,aC n G C k (z γ))
 (hU:j5 n G C j k α p Γ z):False:=by
 obtain ⟨Mi,hMi,cMi⟩:=n9 Z h0 h1 hne
 obtain ⟨Md,hMd,cMd⟩:=sZ col hcol Z Γ z hz hUs
 refine f9 Z Γ z hz hU (Q:=∅) (M:=Mi∪Md) (X:=insert p (Γ.image z)) (by simp)
  (fun h hh=>(mem_union.mp hh).elim (fun h1=>(hMi h h1).1) fun h1=>(hMd h h1).1)
  (mem_insert_self _ _) (fun γ hγ=>mem_insert_of_mem (mem_image_of_mem _ hγ)) ?_
 rw [card_union_of_disjoint (disjoint_left.mpr fun h h1 h2=>by
  have:=(hMi h h1).2;have:=(hMd h h2).2;omega)]
 have:=card_insert_le p (Γ.image z);have:=card_image_le (s:=Γ) (f:=z)
 simp only [card_empty];omega
include hcol in
theorem mS (hc0:#(centreless G C)=0) {X:Finset (Fin n)}
 (hX:∀ e∈Ustar G C,∃ v∈X,v∈e) {P M:Finset ℕ}
 (hP:∀ h∈P,c8 n G C h) (hM:∀ h∈M,aR n G C h)
 (hR:#(Ustar G C)+#X≤2+#P+#M)
 {x1 x2:Fin n} (h1:x1∈X) (h2:x2∈X) (h12:x1≠x2) :
 ∃ f1 f2:Fin n,f1≠f2∧s(x1,f1)∈Ustar G C∧s(x2,f2)∈Ustar G C∧f1∉X ∧
  f2∉X∧j6 G C col x1 f1∧j6 G C col x2 f2∧j6 G C col f2 x2:=by
 classical
 have:Nonempty (Fin n):=⟨x1⟩
 have hA:=Z.1.1
 have h4:=Z.2.2.1
 have ht:tops G C \ centreless G C=tops G C:=by rw [card_eq_zero.mp hc0,sdiff_empty]
 have hcov:∀ Y:Finset (Fin n),(∀ e∈G.edgeFinset,∃ v∈Y,v∈e) → #(tops G C)+#X≤#Y:=fun Y hY=>by
  have hsE:∀ e∈starEdges G C,e∈G.edgeFinset:=fun e he=>by
   obtain ⟨a,ha,u,hu,v,hv,rfl⟩:=mO he
   exact SimpleGraph.mem_edgeFinset.mpr (cE hA ha hu hv)
  have h1:=e4 h4 Z.1 Z.2.1 (by rw [Z.2.2.2.1,card_pair Z.2.2.2.2.1.symm]) Y Y
   (fun e he=>hY e (hsE e he)) (fun e he=>hY e (mem_sdiff.mp he).1)
  rw [sdiff_self,bot_eq_empty,card_empty,ht] at h1
  have:=sQ hA hP hM
  omega
 obtain ⟨K0,-,-,hKa⟩:=k3 hA h4 (fun _=>True)
 rw [ht] at hKa
 choose! βf yf hyf using fun a (ha:a∈tops G C)=>
  let ⟨β,y,_,hs,_⟩:=hKa a ha;(⟨β,y,hs⟩:∃ β:Fin 2,∃ y,side C a (1-β)={y})
 set K:=(tops G C).image yf
 have hKm:∀ a∈tops G C,yf a∈K:=fun a ha=>mem_image_of_mem _ ha
 have hst:∀ e∈starEdges G C,∃ a∈tops G C,∃ u∈side C a 0,∃ v∈side C a 1,
  e=s(u,v)∧yf a∈e:=fun e he=>by
  obtain ⟨a,ha,u,hu,v,hv,rfl⟩:=mO he
  have hs:=hyf a ha
  refine ⟨a,ha,u,hu,v,hv,rfl,?_⟩
  rcases bG (βf a) with ⟨-,h⟩|⟨-,h⟩<;>rw [h] at hs
  ·rw [hs,mem_singleton] at hv;rw [← hv];exact Sym2.mem_mk_right _ _
  ·rw [hs,mem_singleton] at hu;rw [← hu];exact Sym2.mem_mk_left _ _
 set T:=K∪X
 have hTc:∀ e∈G.edgeFinset,∃ v∈T,v∈e:=fun e he=>by
  by_cases hs:e∈starEdges G C
  ·obtain ⟨a,ha,-,-,-,-,-,h⟩:=hst e hs;exact ⟨_,mem_union_left _ (hKm a ha),h⟩
  ·obtain ⟨v,hv,hve⟩:=hX e (mem_sdiff.mpr ⟨he,hs⟩);exact ⟨v,mem_union_right _ hv,hve⟩
 have e1:=hcov T hTc
 have e2:#T+#(K∩X)=#K+#X:=card_union_add_card_inter K X
 have e3:#K≤#(tops G C):=card_image_le
 have hdKX:Disjoint K X:=disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp (by omega))
 have hinj:=card_image_iff.mp (by omega:#K=#(tops G C))
 have hKX:∀ a∈tops G C,yf a∉X:=fun a ha h=>disjoint_left.mp hdKX (hKm a ha) h
 set N:Fin n→ Finset (Fin n):=fun y=>univ.filter (G.Adj y) \ T
 have hmono:∀ A⊆T,∀ c:Bool,(∀ u∈A,col u=c)→ #A≤#(A.biUnion N):= fun A hAT c hc=>by
  have key:∀ u v,G.Adj u v→ u∈T→ ∃ y∈(T \ A)∪A.biUnion N,y=u∨y=v:= fun u v huv hu=>by
   by_cases huA:u∈A
   ·by_cases hvT:v∈T
    ·exact ⟨v,mem_union_left _ (mem_sdiff.mpr ⟨hvT,fun hvA=>
      hcol u v huv ((hc u huA).trans (hc v hvA).symm)⟩),Or.inr rfl⟩
    ·exact ⟨v,mem_union_right _ (mem_biUnion.mpr ⟨u,huA,mem_sdiff.mpr
      ⟨mem_filter.mpr ⟨mem_univ _,huv⟩,hvT⟩⟩),Or.inr rfl⟩
   ·exact ⟨u,mem_union_left _ (mem_sdiff.mpr ⟨hu,huA⟩),Or.inl rfl⟩
  have:=hcov ((T \ A)∪A.biUnion N) fun e he=>by
   induction e using Sym2.ind with|_ u v=>?_
   have huv:=SimpleGraph.mem_edgeFinset.mp he
   obtain ⟨w,hw,hwe⟩:=hTc _ he
   rcases Sym2.mem_iff.mp hwe with rfl|rfl
   ·obtain ⟨y,hy,h'⟩:=key _ _ huv hw
    exact ⟨y,hy,by rcases h' with rfl|rfl<;>simp⟩
   ·obtain ⟨y,hy,h'⟩:=key _ _ huv.symm hw
    exact ⟨y,hy,by rcases h' with rfl|rfl<;>simp⟩
  have:=card_union_le (T \ A) (A.biUnion N)
  have:=card_sdiff_add_card_eq_card hAT
  omega
 have hall:∀ A⊆T,#A≤#(A.biUnion N):=fun A hAT=>by
  have e0:=card_filter_add_card_filter_not (s:=A) (fun u=>col u=true)
  have d:Disjoint ((A.filter fun u=>col u=true).biUnion N)
   ((A.filter fun u=>¬col u=true).biUnion N):=by
   rw [disjoint_biUnion_left];intro u hu;rw [disjoint_biUnion_right];intro v hv
   refine disjoint_left.mpr fun x hx hx'=>(mem_filter.mp hv).2 ?_
   rw [← bB _ _ _ (hcol u x (mem_filter.mp (mem_sdiff.mp hx).1).2)
    (hcol v x (mem_filter.mp (mem_sdiff.mp hx').1).2)]
   exact (mem_filter.mp hu).2
  have s1:=hmono (A.filter fun u=>col u=true) ((filter_subset _ _).trans hAT) true
   fun u hu=>(mem_filter.mp hu).2
  have s2:=hmono (A.filter fun u=>¬col u=true) ((filter_subset _ _).trans hAT) false
   fun u hu=>by simpa using (mem_filter.mp hu).2
  have s3:=card_le_card (union_subset (biUnion_subset_biUnion_of_subset_left N
   (filter_subset (fun u=>col u=true) A))
   (biUnion_subset_biUnion_of_subset_left N (filter_subset (fun u=>¬col u=true) A)))
  rw [card_union_of_disjoint d] at s3
  omega
 have hNK:∀ a∈tops G C,∀ u∈N (yf a),u∈side C a (βf a):=fun a ha u hu=>by
  simp only [N,mem_sdiff,mem_filter,mem_univ,true_and] at hu
  have hs:s(yf a,u)∈starEdges G C:=by
   by_contra hn
   obtain ⟨v,hv,hve⟩:=hX _ (mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hu.1,hn⟩)
   rcases Sym2.mem_iff.mp hve with rfl|rfl
   exacts [hKX a ha hv,hu.2 (mem_union_right _ hv)]
  obtain ⟨a',ha',u',hu',v',hv',e,h⟩:=hst _ hs
  have haa:a'=a:=(Sym2.mem_iff.mp h).elim (hinj ha' ha) fun h'=>
   (hu.2 (h'▸mem_union_left _ (hKm a' ha'))).elim
  rw [haa] at hu' hv'
  obtain ⟨γ,hγ⟩:∃ γ:Fin 2,u∈side C a γ:=by
   rcases Sym2.eq_iff.mp e with ⟨-,h⟩|⟨-,h⟩
   exacts [⟨1,h▸hv'⟩,⟨0,h▸hu'⟩]
  rcases aS (βf a) γ with rfl|rfl
  ·exact hγ
  ·rw [hyf a ha,mem_singleton] at hγ;exact absurd hγ hu.1.ne'
 set tF:=(tops G C).filter fun a=>∃ f∉T,side C a (βf a)={f}
 set F:=tF.biUnion fun a=>side C a (βf a)
 have hFc:#F≤#tF*1:=card_biUnion_le_card_mul _ _ _ fun a ha=>by
  obtain ⟨f,-,hf⟩:=(mem_filter.mp ha).2;rw [hf,card_singleton]
 have hFT:∀ f∈F,f∉T:=fun f hf=>by
  obtain ⟨a,ha,hf⟩:=mem_biUnion.mp hf
  obtain ⟨f',hf',e⟩:=(mem_filter.mp ha).2
  rw [e,mem_singleton] at hf;exact hf▸hf'
 have hS:∀ S⊆X,#S≤#(S.biUnion N \ F):=fun S hSX=>by
  have hd:Disjoint S (tF.image yf):=disjoint_left.mpr fun x hx hx'=>by
   obtain ⟨a,ha,rfl⟩:=mem_image.mp hx'
   exact hKX a (mem_filter.mp ha).1 (hSX hx)
  have:=hall (S∪tF.image yf) (union_subset (hSX.trans subset_union_right)
   fun y hy=>by obtain ⟨a,ha,rfl⟩:=mem_image.mp hy;exact mem_union_left _ (hKm a (mem_filter.mp ha).1))
  have hci:#(tF.image yf)=#tF:= card_image_of_injOn (hinj.mono fun a ha=>(mem_filter.mp ha).1)
  rw [card_union_of_disjoint hd,hci] at this
  have hsub:(S∪tF.image yf).biUnion N⊆(S.biUnion N \ F)∪F:=by
   intro u hu
   rcases mem_biUnion.mp hu with ⟨y,hy,hu⟩
   rcases mem_union.mp hy with hy|hy
   ·by_cases hF:u∈F
    ·exact mem_union_right _ hF
    ·exact mem_union_left _ (mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨y,hy,hu⟩,hF⟩)
   ·obtain ⟨a,ha,rfl⟩:=mem_image.mp hy
    exact mem_union_right _ (mem_biUnion.mpr ⟨a,ha,hNK a (mem_filter.mp ha).1 u hu⟩)
  have:=(card_le_card hsub).trans (card_union_le _ _)
  omega
 have g1:=hS {x1} (singleton_subset_iff.mpr h1)
 have g2:=hS {x2} (singleton_subset_iff.mpr h2)
 have g12:=hS {x1,x2} (insert_subset h1 (singleton_subset_iff.mpr h2))
 rw [singleton_biUnion,card_singleton] at g1 g2
 rw [biUnion_insert,singleton_biUnion,union_sdiff_distrib,card_pair h12] at g12
 obtain ⟨f1,hf1,f2,hf2,hne⟩:∃ f1∈N x1 \ F,∃ f2∈N x2 \ F,f1≠f2:=by
  by_contra hno
  simp only [not_exists,not_and,not_not] at hno
  obtain ⟨g,hg⟩:=card_pos.mp (show 0<#(N x2 \ F) by omega)
  obtain ⟨f,hf⟩:=card_pos.mp (show 0<#(N x1 \ F) by omega)
  have:#(N x1 \ F∪N x2 \ F)≤1:=card_le_one.mpr fun u hu v hv=>by
   have e:∀ w∈N x1 \ F∪N x2 \ F,w=g:=fun w hw=>
    (mem_union.mp hw).elim (hno w · g hg) fun hw=>(hno f hf w hw).symm.trans (hno f hf g hg)
   rw [e u hu,e v hv]
  omega
 have hNX:∀ x∈X,∀ f∈N x \ F,s(x,f)∈Ustar G C∧f∉X∧G.Adj x f∧f∉T ∧ f∉F:=fun x hx f hf=>by
  simp only [N,mem_sdiff,mem_filter,mem_univ,true_and] at hf
  refine ⟨mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hf.1.1,fun hs=>?_⟩,
   fun h=>hf.1.2 (mem_union_right _ h),hf.1.1,hf.1.2,hf.2⟩
  obtain ⟨a,ha,-,-,-,-,-,h⟩:=hst _ hs
  rcases Sym2.mem_iff.mp h with h'|h'
  ·exact hKX a ha (h'▸hx)
  ·exact hf.1.2 (h'▸mem_union_left _ (hKm a ha))
 have h3:∀ f x',f∉K→ f∉F→ x'∉K→ G.Adj x' f→ j6 G C col x' f:=
  fun f x' hfK hfF hxK hxf a ha β hf=>by
  have hs:=hyf a ha
  have hβ:βf a=β:=by
   rcases aS β (1-βf a) with h|h
   ·rw [← h,hs,mem_singleton] at hf;exact absurd (hf▸hKm a ha) hfK
   ·rw [sub_right_inj] at h;exact h
  subst hβ
  obtain ⟨w,hw,hwf⟩:∃ w∈side C a (βf a),w≠f:=by
   by_contra hno
   simp only [not_exists,not_and,not_not] at hno
   have hsf:side C a (βf a)={f}:=eq_singleton_iff_unique_mem.mpr ⟨hf,hno⟩
   by_cases hfT:f∈T
   ·have:=hall {yf a} (singleton_subset_iff.mpr (mem_union_left _ (hKm a ha)))
    rw [singleton_biUnion,card_singleton] at this
    obtain ⟨u,hu⟩:=card_pos.mp this
    have:=hNK a ha u hu
    rw [hsf,mem_singleton] at this
    exact (mem_sdiff.mp hu).2 (this▸hfT)
   ·exact hfF (mem_biUnion.mpr ⟨a,mem_filter.mpr ⟨ha,f,hfT,hsf⟩,hf⟩)
  have hy:yf a∈side C a (1-βf a):=by rw [hs];exact mem_singleton_self _
  have hyf':=mN hA ha hf hy
  have hyw:=mN hA ha hw hy
  exact ⟨w,hw,hwf,fun hxw=>hwf (aQ h4 (fun e=>hxK (by rw [e];exact hKm a ha)) hxw hyw.symm hxf
   hyf'.symm),bB _ _ _ (hcol _ _ hyw.symm).symm (hcol _ _ hyf'.symm).symm⟩
 obtain ⟨u1,x1X,hx1f,hf1T,hf1F⟩:=hNX x1 h1 f1 hf1
 obtain ⟨u2,x2X,hx2f,hf2T,hf2F⟩:=hNX x2 h2 f2 hf2
 have hxK:∀ x∈X,x∉K:=fun x hx h=>disjoint_left.mp hdKX h hx
 exact ⟨f1,f2,hne,u1,u2,x1X,x2X,h3 _ _ (fun h=>hf1T (mem_union_left _ h)) hf1F (hxK x1 h1)
  hx1f,h3 _ _ (fun h=>hf2T (mem_union_left _ h)) hf2F (hxK x2 h2) hx2f,h3 _ _ (hxK x2 h2)
  (fun h=>hFT x2 h (mem_union_right _ h2)) (fun h=>hf2T (mem_union_left _ h)) hx2f.symm⟩
variable {b : Fin 2}
lemma kH (hb:OrReaches n C (opnd C k b) j) (hnb:¬OrReaches n C (opnd C k (1-b)) j) :
 (∀ x,gateVal n C k x=true↔ (gateVal n C j x=true ∨
  ∃ c∈orIn n C (opnd C k b),x c=true)∧∃ d∈orIn n C (opnd C k (1-b)),x d=true) ∧
 (orIn n C (opnd C k (1-b))).Nonempty ∧
 Disjoint (orIn n C (opnd C k b)) (orIn n C (opnd C k (1-b))):=
 cN Z.1.1 Z.2.1 (aP (bU Z.1.1
  (aA.mp (aY Z).2).1 b hb)) Z.2.2.2.1 Z.2.2.2.2.2.1 hb hnb
lemma rW : ∃ bs∈orIn n C (opnd C j (1-α)),¬G.Adj p bs:=by
 by_contra h
 simp only [not_exists,not_and,not_not] at h
 exact (aA.mp (aY Z).1).2.2 fun x hx=>by
  obtain ⟨hp,b',hb',hx'⟩:=(jL Z x).mp hx
  exact (dJ x).mpr ⟨p,b',h b' hb',hp,hx'⟩
include hcol in
lemma pV (hb:OrReaches n C (opnd C k b) j)
 (hnb:¬OrReaches n C (opnd C k (1-b)) j) {b':Fin n} (hU:s(p,b')∈Ustar G C)
 (hBr:∀ a∈orIn n C (opnd C j (1-α)),col a≠col p) (h3:j6 G C col p b') :
 b'∈orIn n C (opnd C k (1-b)) ∧ ∀ d∈orIn n C (opnd C k (1-b)),col d≠col p→ G.Adj p d:=by
 classical
 obtain ⟨bs,hbs,hba⟩:=rW Z
 have hA:=Z.1.1
 have hkv:=(kH Z hb hnb).1
 have hcb:col b'≠col p:=(hcol p b' (dE hU)).symm
 have jt:∀ R:Finset (Fin n),bs∈R → gateVal n C j (fun v=>decide (v=p∨v∈R))=true:=
  fun R h=>(jL Z _).mpr ⟨by simp,bs,hbs,by simp [h]⟩
 have ind:∀ R:Finset (Fin n),(∀ v∈R,col v≠col p∧¬G.Adj p v) →
  graphFun G ∅ (fun v=>decide (v=p∨v∈R))=true→ False:=
  fun R hR h=>Bool.false_ne_true ((mE col hcol p hR).symm.trans h)
 have hjk:∀ i∈junk G C,i=j∨i=k:=fun i hi=>by
  rw [Z.2.2.2.1,mem_insert,mem_singleton] at hi;exact hi
 obtain ⟨hk,S,hS,hSR⟩:gateVal n C k (pairInput p b')=true∧∃ S:Finset (Fin n),
  (∀ v∈S,col v≠col p∧¬G.Adj p v)∧∀ R:Finset (Fin n),bs∈R→ S⊆R →
   gateVal n C k (fun v=>decide (v=p∨v∈R))=true →
   graphFun G ∅ (fun v=>decide (v=p∨v∈R))=true:=by
  obtain ⟨a,ha,hax,β,i,hi,-,hr,hix⟩:=fD Z.1 Z.2.1 hU
  obtain ⟨hal,hop,htop⟩:=aI.mp ha
  have top:∀ x,gateVal n C i x=true→ wireVal n C (opnd C a (1-β)) x=true →
   graphFun G ∅ x=true:=fun x h1 h2=>
   htop x ((aN hA hal hop β x).mpr ⟨aO hA x hr h1,h2⟩)
  rcases (a8 hA Z.2.1 hal hop (1-β) _).mp ((aN hA hal hop β _).mp hax).2 with
   ⟨w0,hw0,hw0x⟩|⟨i',hi',-,hr',hix'⟩
  ·obtain ⟨S,hS,w1,hw1,hw1S⟩:∃ S:Finset (Fin n),
    (∀ v∈S,col v≠col p∧¬G.Adj p v)∧∃ w1∈side C a (1-β),w1=p∨w1∈S:=by
    rcases aW hw0x with h|h<;>rw [h] at hw0
    ·exact ⟨∅,by simp,p,hw0,Or.inl rfl⟩
    ·obtain ⟨w,hw,-,hpw,hcw⟩:=h3 a ha _ hw0
     exact ⟨{w},by simp [hcw,hcb,hpw],w,hw,Or.inr (mem_singleton_self w)⟩
   have tw:∀ R:Finset (Fin n),S⊆R → wireVal n C (opnd C a (1-β)) (fun v=>decide (v=p∨v∈R))=true:=
    fun R hR=>bY hA hw1 (by rcases hw1S with h|h;exacts [by simp [h],by simp [hR h]])
   rcases hjk i hi with h|h<;>rw [h] at top hix
   ·exact (ind (insert bs S) ((forall_mem_insert _ _ _).mpr ⟨⟨hBr bs hbs,hba⟩,hS⟩)
     (top _ (jt _ (mem_insert_self _ _)) (tw _ (subset_insert _ _)))).elim
   ·exact ⟨hix,S,hS,fun R _ hSR hk=>top _ hk (tw R hSR)⟩
  ·have hii:i≠i':=fun e=>jQ hA ha hi hr (e▸hr')
   have hup:=fun x=>aO hA x hr'
   rcases hjk i hi with h|h<;>rcases hjk i' hi' with h'|h'<;>rw [h] at top hix<;>
    rw [h'] at hup hix'<;>first|exact absurd (h.trans h'.symm) hii |
     exact ⟨hix',∅,by simp,fun R hR _ hk=>top _ (jt R hR) (hup _ hk)⟩ |
     exact ⟨hix,∅,by simp,fun R hR _ hk=>top _ hk (hup _ (jt R hR))⟩
 have hR0:=(forall_mem_insert _ _ _).mpr ⟨⟨hBr bs hbs,hba⟩,hS⟩
 obtain ⟨d0,hd0,hd0x⟩:=((hkv _).mp hk).2
 have hpD:p∉orIn n C (opnd C k (1-b)):=fun hp=>ind _ hR0 (hSR _ (mem_insert_self _ _)
  (subset_insert _ _) ((hkv _).mpr ⟨Or.inl (jt _ (mem_insert_self _ _)),p,hp,by simp⟩))
 refine ⟨(aW hd0x).elim (fun h=>absurd (h▸hd0) hpD) (·▸hd0),fun d hd hcd=>?_⟩
 by_contra hpd
 exact ind _ ((forall_mem_insert _ _ _).mpr ⟨⟨hcd,hpd⟩,hR0⟩) (hSR _ (mem_insert_of_mem
  (mem_insert_self _ _)) ((subset_insert _ _).trans (subset_insert _ _))
  ((hkv _).mpr ⟨Or.inl (jt _ (mem_insert_of_mem (mem_insert_self _ _))),d,hd,by simp⟩))
include hcol in
lemma sB (hb:OrReaches n C (opnd C k b) j)
 (hnb:¬OrReaches n C (opnd C k (1-b)) j) {a' d b':Fin n}
 (ha:a'∈orIn n C (opnd C k b)) (had:G.Adj a' d) (hdU:aC n G C k d)
 (hd:d∈orIn n C (opnd C k (1-b))) (hb':b'∈orIn n C (opnd C k (1-b)))
 (hpD:∀ x∈orIn n C (opnd C k (1-b)),col x≠col p→ G.Adj p x)
 (hpb:G.Adj p b') (hpa:p≠a') (hbd:b'≠d) (h3:j6 G C col a' d)
 {X:Finset (Fin n)} (hX:∀ e∈Ustar G C,∃ v∈X,v∈e) {P M:Finset ℕ}
 (hP:∀ h∈P,c8 n G C h)
 (hm:∀ h∈P,∀ x∈orIn n C h,∀ y∈orIn n C h,col x=col y)
 (hM:∀ h∈M,aR n G C h)
 (hR:#(Ustar G C)+#X≤2+2*#(centreless G C)+#P+#M) :
 False:=by
 have hc:col d≠col b':=fun hc=>by
  obtain ⟨t,ht,β,hr,hv⟩:=hdU
  obtain ⟨w,hw,-,haw,hcw⟩:=h3 t ht _ hv
  have hca:col d≠col a':=(hcol a' d had).symm
  have hab:G.Adj a' b':=by
   by_contra hab
   exact Bool.false_ne_true ((mE col hcol a' (R:={b',w})
    (by simp [hab,haw,← hc,hcw,hca])).symm.trans (eH Z.1.1 ht hr hw _
     ((kH Z hb hnb).1 _|>.mpr ⟨Or.inr ⟨a',ha,by simp⟩,b',hb',by simp⟩)
     (by simp)))
  exact hbd (aQ Z.2.2.1 hpa hpb hab (hpD d hd (hc▸(hcol p b' hpb).symm)) had)
 obtain ⟨h,hh,hbh,hdh⟩:=nK Z.1.1 _ hbd hb' hd fun W hW h1 h2=>
  let ⟨_,hc'⟩:=aU col hcol hW;hc ((hc' d h2).trans (hc' b' h1).symm)
 exact cF Z hX (P:=insert h P) (fun h' hh'=>(mem_insert.mp hh').elim (·▸hh) (hP h'))
  hM (by rw [card_insert_of_notMem fun hm'=>hc (hm h hm' d hdh b' hbh)];omega)
include hcol in
lemma rU (hb:OrReaches n C (opnd C k b) j)
 (hnb:¬OrReaches n C (opnd C k (1-b)) j) (hCn:(orIn n C (opnd C k b)).Nonempty)
 (Γ:Finset (Fin 2)) (z:Fin 2→ Fin n)
 (hz:gB n G C k Γ z)
 (hUs:∀ γ∈Γ,aC n G C k (z γ))
 (hU:j5 n G C j k α p Γ z):False:=by
 classical
 have hA:=Z.1.1
 have h4:=Z.2.2.1
 rcases Γ.eq_empty_or_nonempty with hΓ|⟨γ1,hγ1⟩
 ·exact n4 Z fun e he=>(hU e he).resolve_right fun ⟨γ,hγ,_⟩=>by simp [hΓ] at hγ
 obtain ⟨m0,hm0,-,hr0,-⟩:=dR hA (aY Z).1 hb hCn
 obtain ⟨Md,hMd,cMd⟩:=sZ col hcol Z Γ z hz hUs
 have hm0k:n+m0<n+k:= (aX hr0).1.trans_lt (aH hA (aA.mp (aY Z).2).1 b)
 set X:=insert p (Γ.image z)
 set M:=insert (n+m0) Md
 have hX:∀ e∈Ustar G C,∃ v∈X,v∈e:=fun e he=>by
  rcases hU e he with ⟨b',-,rfl⟩|⟨γ,hγ,t,-,rfl⟩
  ·exact ⟨p,mem_insert_self _ _,Sym2.mem_mk_left _ _⟩
  ·exact ⟨z γ,mem_insert_of_mem (mem_image_of_mem _ hγ),Sym2.mem_mk_left _ _⟩
 have hXc:#X≤Γ.card+1:= (card_insert_le p _).trans (by have:=card_image_le (s:=Γ) (f:=z);omega)
 have hΓ2:Γ.card≤2:=(card_le_univ Γ).trans (by simp)
 have hMw:∀ h∈M,aR n G C h:=fun h hh=>(mem_insert.mp hh).elim (·▸hm0) fun h'=>(hMd h h').1
 have hMc:#M=#Md+1:=card_insert_of_notMem fun h=>by
  have:=(hMd _ h).2;omega
 by_cases hl:∃ a∈orIn n C (opnd C j (1-α)),col a=col p
 ·obtain ⟨a,ha,hca⟩:=hl
  obtain ⟨P,hP,hu⟩:=kI Z Γ z hz {a} (card_singleton a).le
   (singleton_subset_iff.mpr ha) (fun W hW=>by
    rw [← insert_eq];exact mK col hcol h4 hca hW)
   (fun a' ha' h=>by
    rw [mem_singleton.mp ha'] at h;exact absurd hca (hcol p a (dE h)).symm)
   (fun γ hγ a' ha' haT ℓ hℓ hℓT=>by
    rw [mem_singleton.mp ha'] at haT
    exact hcol p ℓ (dQ hℓ) (hca.symm.trans (bB _ _ _
     (hcol _ _ ((hz γ hγ).2 _ haT)).symm (hcol _ _ ((hz γ hγ).2 _ hℓT)).symm))) hU
  rw [card_singleton] at hu
  exact cF Z hX (fun h hh=>(hP h hh).1) hMw (by omega)
 simp only [not_exists,not_and] at hl
 obtain ⟨P,hP,hu⟩:=kI Z Γ z hz ∅ (by simp) (empty_subset _)
  (fun W hW=>by rw [empty_union];exact aF h4 sdiff_subset hW p) (by simp)
  (by simp) hU
 rw [card_empty] at hu
 have hPw:∀ h∈P,c8 n G C h:=fun h hh=>(hP h hh).1
 by_cases hg:p∈Γ.image z∨Γ.card<#Md+2*#(centreless G C)
 ·refine cF Z hX hPw hMw ?_
  rcases hg with hg|hg
  ·have:#X≤Γ.card:=(card_insert_of_mem hg).trans_le card_image_le;omega
  ·omega
 simp only [not_or,not_lt] at hg
 obtain ⟨hpz,hΓM⟩:=hg
 have hPm:∀ h∈P,∀ x∈orIn n C h,∀ y∈orIn n C h,col x=col y:=fun h hh x hx y hy=>by
  rcases (hP h hh).2 with hs|⟨γ,hγ,hs⟩
  ·exact bB _ _ _ (hl x (hs hx)) (hl y (hs hy))
  ·exact bB _ _ _ (hcol _ _ ((hz γ hγ).2 x (hs hx))).symm
    (hcol _ _ ((hz γ hγ).2 y (hs hy))).symm
 rcases Nat.eq_zero_or_pos #(centreless G C) with hc|hc
 ·obtain ⟨γ0,hγ0,hγ0b⟩:∃ γ0∈Γ,b∈Γ→ γ0=b:=
   if h:b∈Γ then ⟨b,h,fun _=>rfl⟩ else ⟨γ1,hγ1,fun h'=>absurd h' h⟩
  have hγp:p≠z γ0:=fun e=>hpz (e▸mem_image_of_mem z hγ0)
  have hzX:z γ0∈X:=mem_insert_of_mem (mem_image_of_mem z hγ0)
  obtain ⟨b',v,hbv,hpb,hzv,hbX,hvX,h3p,-,h3⟩:=mS col hcol Z hc hX hPw hMw
   (by omega) (mem_insert_self p _) hzX hγp
  obtain ⟨hb'D,hpD⟩:=pV col hcol Z hb hnb hpb hl h3p
  have hv:v∈orIn n C (opnd C k (1-γ0)):=by
   rcases hU _ hzv with ⟨b'',-,e⟩|⟨γ,hγ,t,ht,e⟩
   ·rcases Sym2.eq_iff.mp e with ⟨h,-⟩|⟨-,h⟩
    exacts [absurd h.symm hγp,(hvX (h▸mem_insert_self p _)).elim]
   ·rcases Sym2.eq_iff.mp e with ⟨h1,h2⟩|⟨-,h2⟩
    ·obtain rfl:γ=γ0:=(aS γ0 γ).resolve_right fun h=>gS Z (hz γ0 hγ0).1
      (by rw [h1,← h];exact (hz γ hγ).1)
     exact h2▸ht
    ·exact (hvX (h2▸mem_insert_of_mem (mem_image_of_mem z hγ))).elim
  by_cases hbΓ:b∈Γ
  ·obtain rfl:=hγ0b hbΓ
   have h1:=(hz γ0 hγ0).2 b' hb'D
   have h2:=(hz γ0 hγ0).2 v hv
   exact hbv (aQ h4 hγp (dE hpb) h1 (hpD v hv
    (bB _ _ _ (hcol _ _ h2).symm (hcol _ _ h1).symm▸(hcol p b' (dE hpb)).symm)) h2)
  have e:γ0=1-b:=(aS b γ0).resolve_left fun h=>hbΓ (h▸hγ0)
  exact sB col hcol Z hb hnb (by rw [e,sub_sub_cancel] at hv;exact hv)
   (dE hzv).symm (hUs γ0 hγ0) (e▸(hz γ0 hγ0).1) hb'D hpD (dE hpb)
   (fun h=>hvX (h▸mem_insert_self p _)) (fun h=>hbX (h▸hzX)) h3 hX hPw hPm hMw
   (by omega)
 have hΓu:∀ γ,γ∈Γ:=fun γ=>by
  rw [eq_univ_of_card Γ (by simp;omega)];exact mem_univ γ
 by_cases hnc:∃ γ:Fin 2,∃ a∈tops G C \ centreless G C,∃ β:Fin 2,
  OrReaches n C (opnd C a β) k∧z γ∈orIn n C (opnd C a (1-β))
 ·obtain ⟨γ,a,ha,β,hr,-⟩:=hnc
  obtain ⟨m,hm,-,-,hmk,-⟩:=dR hA (aY Z).2 hr (nonempty_iff_ne_empty.mpr fun e=>
   (mem_sdiff.mp ha).2 (c7 (mem_sdiff.mp ha).1 e))
  have:=(aX hmk).1
  exact cF Z hX hPw (M:={n+m0,n+m}) (by simp [hm0,hm]) (by rw [card_pair (by omega)];omega)
 simp only [not_exists,not_and] at hnc
 obtain ⟨t0,ht0⟩:=card_eq_one.mp (show #(centreless G C)=1 by omega)
 have hct:∀ γ,∃ β:Fin 2,z γ∈orIn n C (opnd C t0 (1-β)) ∧ orIn n C (opnd C t0 β)=∅:=fun γ=>by
  obtain ⟨a,ha,β,hr,hw⟩:=hUs γ (hΓu γ)
  have hc:a∈centreless G C:=by_contra fun h=>hnc γ a (mem_sdiff.mpr ⟨ha,h⟩) β hr hw
  have hat:a∈({t0}:Finset ℕ):=ht0▸hc
  obtain ⟨β',he⟩:∃ β',orIn n C (opnd C a β')=∅:=(mem_filter.mp hc).2.elim (⟨0,·⟩) (⟨1,·⟩)
  rw [mem_singleton.mp hat] at hw he
  exact ⟨β,hw,d7 he hw▸he⟩
 obtain ⟨β0,hw0,he0⟩:=hct 0
 obtain ⟨β1,hw1,he1⟩:=hct 1
 obtain rfl:β1=β0:=by
  rcases aS β0 β1 with h|h
  ·exact h
  rw [h,sub_sub_cancel,he0] at hw1;simp at hw1
 have h01:G.Adj (z 0) (z 1):=(hz 0 (hΓu 0)).2 _ (by simpa using (hz 1 (hΓu 1)).1)
 obtain ⟨h,hh,h0h,h1h⟩:=nK hA _ (G.ne_of_adj h01) hw0 hw1 fun W hW h1 h2=>
  let ⟨_,hc'⟩:=aU col hcol hW;hcol _ _ h01 ((hc' _ h1).trans (hc' _ h2).symm)
 exact cF Z hX (P:=insert h P) (fun h' hh'=>(mem_insert.mp hh').elim (·▸hh) (hPw h'))
  hMw (by rw [card_insert_of_notMem fun hm'=>hcol _ _ h01 (hPm h hm' _ h0h _ h1h)];omega)
include hcol in
lemma rT (hb:OrReaches n C (opnd C k b) j)
 (hnb:¬OrReaches n C (opnd C k (1-b)) j) (hne:∀ γ,(orIn n C (opnd C k γ)).Nonempty)
 {γ:Fin 2} {z:Fin n} (hγ:orIn n C (opnd C k γ)={z}) (hz:¬aC n G C k z) :
 False:=by
 classical
 have hA:=Z.1.1
 have h4:=Z.2.2.1
 obtain ⟨hjJ,hkJ⟩:=aY Z
 have hkv:=(kH Z hb hnb).1
 obtain ⟨m0,hm0,-,hr0,-⟩:=dR hA hjJ hb (hne b)
 have hm0k:n+m0<n+k:= (aX hr0).1.trans_lt (aH hA (aA.mp hkJ).1 b)
 by_cases hzp:z=p
 ·subst hzp;exact s8 Z hγ hz (Mi:={n+m0}) (by simp [hm0,hm0k]) (singleton_nonempty _)
 obtain ⟨hX,Lz,hLz,hu⟩:=rA Z hγ hz
 set Lp:=orIn n C (opnd C j (1-α))∩aE (Ustar G C) p
 have hXc:#({p,z}:Finset (Fin n))=2:=card_pair (Ne.symm hzp)
 have hspz:∀ W,aB G (Ustar G C) W→ #(W∩Lz)≤1:=fun W hW=>
  (card_le_card (inter_subset_inter_left fun t ht=>(hLz t ht).2.1)).trans
   (aF h4 sdiff_subset hW z)
 have hspp:∀ W,aB G (Ustar G C) W→ #(W∩Lp)≤1:=fun W hW=>
  (card_le_card (inter_subset_inter_left inter_subset_right)).trans
   (aF h4 sdiff_subset hW p)
 by_cases hD1:0<#(centreless G C)∧γ=1-b
 ·obtain ⟨hc1,rfl⟩:=hD1
  have hLzC:Lz⊆orIn n C (opnd C k b):=fun t ht=>by
   simpa only [sub_sub_cancel] using (hLz t ht).1
  have hzD:z∈orIn n C (opnd C k (1-b)):=hγ▸mem_singleton_self z
  by_cases hpz:col p=col z
  swap
  ·have mix:∀ x y,col x=col y→ x∈Lp→ y∈Lz→ False:=fun x y hxy hx hy=>
    hpz (bB _ _ _ (hcol p x (dQ (mem_inter.mp hx).2))
     (hxy▸hcol z y (dQ (hLz y hy).2.1)))
   obtain ⟨P,hP,hc⟩:=kB hA {opnd C j (1-α),opnd C k b} (Lp∪Lz) fun W hW=>
    card_le_one.mpr fun u hu v hv=>by
    obtain ⟨c,hc⟩:=aU col hcol hW
    simp only [mem_inter,mem_union] at hu hv
    obtain ⟨huW,hu|hu⟩:=hu<;>obtain ⟨hvW,hv|hv⟩:=hv
    ·exact card_le_one.mp (hspp W hW) u (mem_inter.mpr ⟨huW,hu⟩) v (mem_inter.mpr ⟨hvW,hv⟩)
    ·exact (mix u v ((hc u huW).trans (hc v hvW).symm) hu hv).elim
    ·exact (mix v u ((hc v hvW).trans (hc u huW).symm) hv hu).elim
    ·exact card_le_one.mp (hspz W hW) u (mem_inter.mpr ⟨huW,hu⟩) v (mem_inter.mpr ⟨hvW,hv⟩)
   rw [biUnion_insert,singleton_biUnion,inter_eq_right.mpr (union_subset_union
    inter_subset_left hLzC),card_union_of_disjoint (disjoint_left.mpr fun x hx hx'=>
     mix x x rfl hx hx')] at hc
   have:=card_le_two (a:=opnd C j (1-α)) (b:=opnd C k b)
   exact cF Z hX (fun h hh=>(hP h hh).1) (M:={n+m0}) (by simpa using hm0)
    (by rw [card_singleton];omega)
  have hLpq:∀ x∈Lp,aC n G C j x:=fun x hx=>by
   obtain ⟨hxB,hxN⟩:=mem_inter.mp hx
   have hk:gateVal n C k (pairInput p x)=false:=by
    cases hk:gateVal n C k (pairInput p x)
    ·rfl
    obtain ⟨d,hd,hdx⟩:=((hkv _).mp hk).2
    rw [hγ,mem_singleton] at hd
    rcases aW (hd▸hdx) with h|h
    exacts [absurd h hzp,(hcol p x (dQ hxN) (hpz.trans (congrArg col h))).elim]
   obtain ⟨ℓ,-,hℓ,e⟩:=l5 Z (aD.mp hxN) (kD Z hxB) hk
   exact Sym2.congr_right.mp e▸hℓ
  obtain ⟨P1,Q1,M1,T1,hPQ1,hP1,hM1,hT1,-,-,cP1,cQ1⟩:=lB hA h4 hjJ Lp
   (fun ℓ h=>⟨(mem_inter.mp h).2,(mem_inter.mp h).1,hLpq ℓ h⟩) fun v hv hu=>e5 Z hv hu
  obtain ⟨P2,Q2,M2,T2,hPQ2,hP2,hM2,hT2,-,-,cP2,cQ2⟩:=lB hA h4 hkJ (w:=opnd C k b)
   Lz (fun ℓ h=>⟨(hLz ℓ h).2.1,hLzC h,(hLz ℓ h).2.2⟩) fun v hv ⟨a,ha,β,hr,hw⟩=>
    (aT z v).mp (eH hA ha hr hw _ ((hkv _).mpr ⟨Or.inr ⟨v,hv,by simp [pairInput]⟩,
     z,hzD,by simp [pairInput]⟩) (by simp [pairInput]))
  obtain ⟨hPA,hm2⟩:=q6 h4 (Ne.symm hzp) (fun ℓ h=>(mem_inter.mp h).2)
   (fun ℓ h=>(hLz ℓ h).2.1) hPQ1 hPQ2 hP1 hP2
  have h0:m0∉M2:=fun h=>by have:=(aX (lX hA (hM2 m0 h))).1;omega
  have hN1:=card_le_card (show M1⊆insert m0 (M1∪M2) from
   subset_union_left.trans (subset_insert _ _))
  have hN2:=card_le_card (show insert m0 M2⊆insert m0 (M1∪M2) from
   insert_subset_insert _ subset_union_right)
  rw [card_insert_of_notMem h0] at hN2
  have:=card_le_card hT1
  have:=card_le_card hT2
  refine cF Z hX hPA (M:=(insert m0 (M1∪M2)).image (n+·)) (fun h hh=>?_) ?_
  ·obtain ⟨m,hm,rfl⟩:=mem_image.mp hh
   rcases mem_insert.mp hm with rfl|hm
   ·exact hm0
   ·exact (mem_union.mp hm).elim (c5 hA hjJ<|hM1 _ ·) (c5 hA hkJ<|hM2 _ ·)
  ·rw [card_image_of_injective _ (add_right_injective n)];omega
 obtain ⟨Mx,Rc,Pf,hMx,hRc,-,hPf,-,cf⟩:=nD hA hkJ Lz hspz fun t ht=>(hLz t ht).2.2
 have hRcc:=card_le_card hRc
 have hPfB:∀ h∈Pf,orIn n C h⊆orIn n C (opnd C j (1-α))→ False:=fun h h2 hs=>by
  obtain ⟨-,-,a,ha,-⟩:=hPf h h2
  have hγb:γ=b:=(aS b γ).resolve_right fun e=>hD1 ⟨card_pos.mpr ⟨a,hRc ha⟩,e⟩
  refine jP h4 (Ne.symm hzp) (S:=orIn n C h∩Lz) (fun v hv=>?_) (hPf h h2).2.1
  obtain ⟨hvD,hvU,a',ha',β,hr,hw⟩:=hLz v (mem_inter.mp hv).2
  rw [hγb] at hvD
  exact ⟨(aT p v).mp (eH hA ha' hr hw _ ((hkv _).mpr ⟨Or.inl
   (kD Z (hs (mem_inter.mp hv).1)),v,hvD,by simp [pairInput]⟩) (by simp [pairInput])),
    dQ hvU⟩
 have hm0n:n+m0∉Mx.image (n+·):=fun h=>by
  obtain ⟨m,hm,e⟩:=mem_image.mp h;have:=(aX (lX hA (hMx m hm))).1;omega
 set M:=insert (n+m0) (Mx.image (n+·))
 have hMw:∀ h∈M,aR n G C h:=fun h hh=>(mem_insert.mp hh).elim (·▸hm0) fun hh'=>by
  obtain ⟨m,hm,rfl⟩:=mem_image.mp hh';exact c5 hA hkJ (hMx m hm)
 have hMc:#M=#Mx+1:=by
  rw [card_insert_of_notMem hm0n,card_image_of_injective _ (add_right_injective n)]
 have fin:∀ PB:Finset ℕ,(∀ h∈PB,c8 n G C h ∧ orIn n C h⊆orIn n C (opnd C j (1-α))) →
  #Lp≤#(centreless G C)+#PB→ False:=fun PB hPB hc=>by
  refine cF Z hX (P:=PB∪Pf) (fun h hh=>(mem_union.mp hh).elim (fun h1=>(hPB h h1).1)
   fun h2=>(hPf h h2).1) hMw ?_
  rw [card_union_of_disjoint (disjoint_left.mpr fun h h1 h2=>hPfB h h2 (hPB h h1).2),hXc,hMc]
  omega
 by_cases hl:∃ a∈orIn n C (opnd C j (1-α)),col a=col p
 ·obtain ⟨a,ha,hca⟩:=hl
  obtain ⟨P,hP,hc⟩:=jC hA (opnd C j (1-α)) (insert a Lp) fun W hW=>
   (card_le_card (inter_subset_inter_left (insert_subset_insert a inter_subset_right))).trans
    (mK col hcol h4 hca hW)
  have:=card_le_card (show insert a Lp⊆orIn n C (opnd C j (1-α))∩insert a Lp from
   subset_inter (insert_subset ha inter_subset_left) subset_rfl)
  rw [card_insert_of_notMem (s:=Lp) fun h=>hcol p a (dQ (mem_inter.mp h).2) hca.symm] at this
  exact fin P (fun h hh=>⟨(hP h hh).1,(hP h hh).2.1⟩) (by omega)
 simp only [not_exists,not_and] at hl
 obtain ⟨PB,hPB,cB⟩:=jC hA (opnd C j (1-α)) Lp hspp
 replace cB:#Lp≤1+#PB:= (card_le_card (subset_inter inter_subset_left subset_rfl)).trans cB
 rcases Nat.eq_zero_or_pos #(centreless G C) with hc0|hc0
 swap
 ·exact fin PB (fun h hh=>⟨(hPB h hh).1,(hPB h hh).2.1⟩) (by omega)
 have hPf0:#Pf=0:=card_eq_zero.mpr (eq_empty_of_forall_notMem fun h hh=>by
  obtain ⟨-,-,a,ha,-⟩:=hPf h hh;have:=card_pos.mpr ⟨a,ha⟩;omega)
 obtain ⟨b',v,hbv,hpb,hzv,hbX,hvX,h3p,h3,-⟩:=mS col hcol Z hc0 hX
  (fun h hh=>(hPB h hh).1) hMw (by rw [hXc,hMc];omega) (mem_insert_self p {z}) (by simp)
  (Ne.symm hzp)
 obtain ⟨hb'D,hpD⟩:=pV col hcol Z hb hnb hpb hl h3p
 rcases aS b γ with h|h<;>rw [h] at hγ hLz
 ·obtain ⟨hvD,hvU⟩:v∈orIn n C (opnd C k (1-b))∧aC n G C k v:=by
   rcases nF Z hγ hz _ hzv with ⟨b'',-,e⟩|⟨t,ht,htU,e⟩
   ·rcases Sym2.eq_iff.mp e with ⟨h,-⟩|⟨-,h⟩
    exacts [absurd h hzp,(hvX (h▸by simp)).elim]
   ·rw [Sym2.congr_right.mp e];exact ⟨ht,htU⟩
  exact sB col hcol Z hb hnb (hγ▸mem_singleton_self z) (dE hzv) hvU hvD hb'D hpD
   (dE hpb) (Ne.symm hzp) hbv h3 hX (fun h hh=>(hPB h hh).1) (fun h hh x hx y hy=>
    bB _ _ _ (hl x ((hPB h hh).2.1 hx)) (hl y ((hPB h hh).2.1 hy))) hMw
   (by rw [hXc,hMc];omega)
 ·rw [hγ,mem_singleton] at hb'D
  exact hbX (by simp [hb'D])
lemma qM (hjk:¬InCone n C j k) : ∀ i∈junk G C,¬InCone n C i k:=fun i hi hc=>by
 rw [Z.2.2.2.1,mem_insert,mem_singleton] at hi
 rcases hi with rfl|rfl
 exacts [hjk hc,lt_irrefl _ (aP hc)]
lemma p3 (hjk:¬InCone n C j k) (γ:Fin 2) (x:Fin n→ Bool) :
 gateVal n C k x=true↔ (∃ a∈orIn n C (opnd C k γ),x a=true) ∧
  ∃ b∈orIn n C (opnd C k (1-γ)),x b=true:=by
 have hv:=rN Z.1.1 Z.2.1 (aY Z).2 (qM Z hjk) x
 rcases bG γ with ⟨rfl,h⟩|⟨rfl,h⟩<;>rw [h]
 exacts [hv,hv.trans and_comm]
lemma l7 (hjk:¬InCone n C j k) {x y:Fin n} (h:gateVal n C k (pairInput x y)=true) :
 ∃ γ:Fin 2,x∈orIn n C (opnd C k γ)∧y∈orIn n C (opnd C k (1-γ)):=by
 obtain ⟨⟨c,hc,hcx⟩,d,hd,hdx⟩:=(p3 Z hjk 0 _).mp h
 rcases aW hcx with rfl|rfl<;>rcases aW hdx with rfl|rfl
 exacts [absurd hd (gS Z hc),⟨0,hc,hd⟩,⟨1-0,hd,by rwa [sub_sub_cancel]⟩,
  absurd hd (gS Z hc)]
lemma pR (hjk:¬InCone n C j k) {y:Fin n}
 (hy:aC n G C k y) {x:Fin n→ Bool} (hx:gateVal n C k x=true) (hyx:x y=true) :
 wireVal n (aG n C j) C.output x=true:=by
 obtain ⟨t,ht,b,hr,hyt⟩:=hy
 refine fW Z.1 Z.2.1 (aY Z).1 ht fun b'=>fI Z.1.1 (k:=k) (aY Z).1 ?_
 rcases aS b b' with rfl|rfl
 exacts [Or.inr ⟨Z.2.2.2.2.1,hjk,hr,hx⟩,Or.inl ⟨y,hyt,hyx⟩]
lemma r8 (hjk:¬InCone n C j k) {zf:Fin 2→ Fin n}
 (hzf:∀ γ,zf γ∈orIn n C (opnd C k γ)∧aC n G C k (zf γ)) {u v:Fin n}
 (huv:G.Adj u v) (hx:gateVal n C k (pairInput u v)=true) :
 wireVal n (aG n C j) C.output (pairInput u v)=true:=by
 obtain ⟨γ,hu,hv⟩:=l7 Z hjk hx
 have hfl:=fun γ=>fO Z (hzf γ).1 (hzf γ).2
 by_cases h1:u=zf γ
 ·exact pR Z hjk (hzf γ).2 hx (by simp [pairInput,h1])
 by_cases h2:v=zf (1-γ)
 ·exact pR Z hjk (hzf (1-γ)).2 hx (by simp [pairInput,h2])
 exact absurd (aQ Z.2.2.1 h1 huv (hfl γ v hv)
  (hfl (1-γ) u (by rwa [sub_sub_cancel])).symm (hfl γ _ (hzf (1-γ)).1)) h2
lemma pW (hjk:¬InCone n C j k) {zf:Fin 2→ Fin n}
 (hzf:∀ γ,zf γ∈orIn n C (opnd C k γ)∧aC n G C k (zf γ)) {b:Fin n}
 (hpb:G.Adj p b) (hl:wireVal n (aG n C j) C.output (pairInput p b)=false) :
 aC n G C j b:=by
 obtain ⟨t,ht,β,hr,-,⟨w,hw,hwpb⟩|⟨-,hkx⟩⟩:= f7 Z.1 Z.2.1 Z.2.2.2.1 Z.2.2.2.2.1 hjk hpb hl
 ·rcases hwpb with rfl|rfl
  exacts [(pP Z ⟨t,ht,β,hr,hw⟩).elim,⟨t,ht,β,hr,hw⟩]
 ·rw [r8 Z hjk hzf hpb hkx] at hl;cases hl
lemma s7 {t:ℕ} (ht:t∈tops G C) {b:Fin 2}
 (h1:OrReaches n C (opnd C t b) k) (h2:OrReaches n C (opnd C t (1-b)) j) :
 ∃ M:Finset ℕ,(∀ h∈M,aR n G C h)∧2≤2*#(centreless G C)+#M:=by
 have hA:=Z.1.1
 by_cases hc:t∈centreless G C
 ·exact ⟨∅,by simp,by have:=card_pos.mpr ⟨t,hc⟩;omega⟩
 have hne:∀ β,(orIn n C (opnd C t β)).Nonempty:=fun β=>
  nonempty_iff_ne_empty.mpr fun e=>hc (c7 ht e)
 obtain ⟨m1,hm1,-,hw1,-⟩:=dR hA (aY Z).2 h1 (hne b)
 obtain ⟨m2,hm2,-,-,hr2,-⟩:=dR hA (aY Z).1 h2 (hne _)
 refine ⟨{n+m1,n+m2},by simp [hm1,hm2],?_⟩
 rw [card_pair fun e=>jQ hA ht (aY Z).1
  (cG hA hw1 (by rwa [show m1=m2 by omega])) h2];omega
lemma q7 {Γ:Finset (Fin 2)} {zf:Fin 2→ Fin n}
 (hq:∀ γ y,y∈orIn n C (opnd C k γ)→ aC n G C k y→ γ∈Γ∧y=zf γ) :
 j5 n G C j k α p Γ zf:=
 fun e he=>(gV Z he).imp_right fun ⟨γ,c,hc,d,hd,e,hus⟩=>by
  obtain ⟨hγ,rfl⟩:=hq γ c hc hus;exact ⟨γ,hγ,d,hd,e⟩
lemma p6 {i:ℕ} (hi:i∈junk G C) {v:Fin n}
 (hv:aC n G C i v):(∃ m,dG n C i m∧aC n G C m v) ∨
  ∃ t∈centreless G C,∃ β:Fin 2,OrReaches n C (opnd C t β) i ∧
   orIn n C (opnd C t β)=∅∧v∈orIn n C (opnd C t (1-β)):=by
 obtain ⟨t,ht,β,hr,hvt⟩:=hv
 by_cases hc:t∈centreless G C
 ·obtain ⟨β',he⟩:∃ β',orIn n C (opnd C t β')=∅:= (mem_filter.mp hc).2.elim (⟨0,·⟩) (⟨1,·⟩)
  exact Or.inr ⟨t,hc,β,hr,d7 he hvt▸he,hvt⟩
 obtain ⟨m,b,hm,hop,hwm,hne',he,hrJ⟩:=fE Z.1.1 (aA.mp hi).2.1 hr
  (nonempty_iff_ne_empty.mpr fun e=>hc (c7 ht e))
 exact Or.inl ⟨m,⟨hm,hop,hne',b,he,hrJ⟩,t,ht,β,hwm,hvt⟩
lemma pQ {i i' m:ℕ} {v v':Fin n}
 (h:dG n C i m∧aC n G C m v) (h':dG n C i' m∧aC n G C m v') :
 aB G (Ustar G C) {v,v'}:=
 let ⟨_,hr⟩:=h.1.2.2.1
 gO Z.1.1 hr fun w hw=>by
  rcases mem_insert.mp hw with rfl|hw
  ·exact h.2
  ·rw [mem_singleton.mp hw];exact h'.2
include hcol in
lemma lE {i i' m:ℕ} {v v':Fin n} (h:dG n C i m∧aC n G C m v)
 (h':dG n C i' m∧aC n G C m v'):col v=col v':=
 let ⟨_,hc⟩:=aU col hcol (pQ Z h h')
 (hc v (by simp)).trans (hc v' (by simp)).symm
include hR1 hcol in
theorem pU (hjk:¬InCone n C j k) (hw:∀ γ,2≤#(orIn n C (opnd C k γ))) : False:=by
 classical
 have hA:=Z.1.1
 have h4:=Z.2.2.1
 obtain ⟨hjJ,hkJ⟩:=aY Z
 have huq:∀ γ y y',y∈orIn n C (opnd C k γ)→ aC n G C k y →
  y'∈orIn n C (opnd C k γ)→ aC n G C k y'→ y=y':=fun γ y y' hy hu hy' hu'=>
  bC h4 (hw (1-γ)) (fO Z hy hu) (fO Z hy' hu')
 by_cases hb:(∃ y∈orIn n C (opnd C k 0),aC n G C k y) ∧
  ∃ y∈orIn n C (opnd C k 1),aC n G C k y
 ·obtain ⟨⟨a,ha,hau⟩,z,hz,hzu⟩:=hb
  have hzf:∀ γ,![a,z] γ∈orIn n C (opnd C k γ)∧aC n G C k (![a,z] γ):=fun γ=>by
   fin_cases γ<;>simp [ha,hau,hz,hzu]
  have hU:=q7 Z (Γ:=univ) (zf:=![a,z]) fun γ y hy hyu=>
   ⟨mem_univ _,huq γ y _ hy hyu (hzf γ).1 (hzf γ).2⟩
  have fin:∀ {Q M:Finset ℕ},(∀ h∈Q,c8 n G C h ∧ ¬orIn n C h⊆orIn n C (opnd C j (1-α)) ∧
   ∀ γ∈(univ:Finset (Fin 2)),¬orIn n C h⊆orIn n C (opnd C k (1-γ))) →
   (∀ h∈M,aR n G C h)→ 3<2*#(centreless G C)+#Q+#M→ False:=
   fun hQ hM hlt=>f9 Z univ ![a,z] (fun γ _=>⟨(hzf γ).1,
    fO Z (hzf γ).1 (hzf γ).2⟩) hU hQ hM (X:={p,a,z}) (by simp)
    (fun γ _=>by fin_cases γ<;>simp) (card_le_three.trans_lt hlt)
  have haz:G.Adj a z:=fO Z ha hau z (by simpa using hz)
  obtain ⟨b1,b2,hb12,⟨-,hpb1,hl1⟩,-,hpb2,hl2⟩:=kP hR1 col hcol Z hjk
  have hu1:=g5 Z.1 Z.2.1 hjJ hpb1 hl1
  have hu2:=g5 Z.1 Z.2.1 hjJ hpb2 hl2
  have hm1:=pW Z hjk hzf hpb1 hl1
  have hm2:=pW Z hjk hzf hpb2 hl2
  have hxx:∀ {x x'},dG n C j x∧aC n G C x b1→ dG n C j x'∧aC n G C x' b2 →
   x≠x':=fun hx hx' e=>hb12 (card_le_one.mp (aF h4 sdiff_subset
    (pQ Z hx (e▸hx')) p) _ (mem_inter.mpr ⟨by simp,aD.mpr hu1⟩) _
    (mem_inter.mpr ⟨by simp,aD.mpr hu2⟩))
  have hyy:∀ {y y'},dG n C k y∧aC n G C y a→ dG n C k y'∧aC n G C y' z →
   y≠y':=fun hy hy' e=>hcol a z haz (lE col hcol Z hy (e▸hy'))
  have two:∀ {w w'},aR n G C w→ aR n G C w'→ w≠w'→ 0<#(centreless G C) →
   False:=fun {w w'} hw hw' hne hc=>fin (Q:=∅) (M:={w,w'}) (by simp)
    (by simp [hw,hw']) (by rw [card_pair hne];simp only [card_empty];omega)
  rcases Nat.lt_or_ge #(centreless G C) 2 with hc|hc
  swap
  ·exact fin (Q:=∅) (M:=∅) (by simp) (by simp) (by simp only [card_empty];omega)
  rcases Nat.eq_zero_or_pos #(centreless G C) with hc0|hc1
  ·have mx:∀ {i v},i∈junk G C→ aC n G C i v→ ∃ m,dG n C i m∧aC n G C m v:=
    fun hi hv=>(p6 Z hi hv).resolve_right fun ⟨t,ht,_⟩=>by
     simp [card_eq_zero.mp hc0] at ht
   obtain ⟨x1,hx1⟩:=mx hjJ hm1
   obtain ⟨x2,hx2⟩:=mx hjJ hm2
   obtain ⟨ya,hya⟩:=mx hkJ hau
   obtain ⟨yz,hyz⟩:=mx hkJ hzu
   have h12:=hxx hx1 hx2
   have hcb:col b1=col b2:=
    bB _ _ _ (hcol p b1 (dE hu1)).symm (hcol p b2 (dE hu2)).symm
   have key:∀ {v v' y y'},dG n C k y∧aC n G C y v →
    dG n C k y'∧aC n G C y' v'→ y≠y'→ col v≠col b1→ False:=
    fun {v v' y y'} hy hy' hyy' hc=>by
    have hy1:y≠x1:=fun e=>hc (lE col hcol Z hy (e▸hx1))
    have hy2:y≠x2:=fun e=>hc ((lE col hcol Z hy (e▸hx2)).trans hcb.symm)
    obtain ⟨w,hw,hwy⟩:∃ w,aR n G C w∧w∉({n+y,n+x1,n+x2}:Finset ℕ):=by
     by_cases ho:y'=x1∨y'=x2
     ·obtain ⟨w,hw,hwe⟩:∃ w,aR n G C w∧orIn n C w=∅:=by
       rcases ho with rfl|rfl
       exacts [jN hA hjJ Z.2.2.2.2.1.symm hx1.1 hy'.1,
        jN hA hjJ Z.2.2.2.2.1.symm hx2.1 hy'.1]
      refine ⟨w,hw,?_⟩
      simp only [mem_insert,mem_singleton]
      rintro (rfl|rfl|rfl)
      exacts [hy.1.2.2.1.ne_empty hwe,hx1.1.2.2.1.ne_empty hwe,hx2.1.2.2.1.ne_empty hwe]
     ·exact ⟨_,c5 hA hkJ hy'.1,by simp only [not_or] at ho;simp;omega⟩
    refine fin (Q:=∅) (M:=insert w {n+y,n+x1,n+x2}) (by simp) (fun h hh=>?_) ?_
    ·simp only [mem_insert,mem_singleton] at hh
     rcases hh with rfl|rfl|rfl|rfl
     exacts [hw,c5 hA hkJ hy.1,c5 hA hjJ hx1.1,c5 hA hjJ hx2.1]
    ·rw [card_insert_of_notMem hwy,card_insert_of_notMem (by simp;omega),
      card_pair (by omega)];simp only [card_empty];omega
   by_cases hca:col a=col b1
   ·exact key hyz hya (hyy hya hyz).symm fun e=>hcol a z haz (hca.trans e.symm)
   ·exact key hya hyz (hyy hya hyz) hca
  obtain ⟨t0,ht0⟩:=card_eq_one.mp (show #(centreless G C)=1 by omega)
  have dc:∀ {i v},i∈junk G C→ aC n G C i v→ (∃ m,dG n C i m ∧
   aC n G C m v)∨∃ β:Fin 2,OrReaches n C (opnd C t0 β) i ∧
    orIn n C (opnd C t0 β)=∅∧v∈orIn n C (opnd C t0 (1-β)):=fun hi hv=>
   (p6 Z hi hv).imp_right fun ⟨t,ht,h⟩=>by rw [ht0,mem_singleton] at ht;exact ht▸h
  by_cases hjs:∃ β:Fin 2,OrReaches n C (opnd C t0 β) j∧orIn n C (opnd C t0 β)=∅
  swap
  ·rcases dc hjJ hm1 with ⟨x1,hx1⟩|⟨β,hr,he,-⟩
   ·rcases dc hjJ hm2 with ⟨x2,hx2⟩|⟨β,hr,he,-⟩
    ·exact two (c5 hA hjJ hx1.1) (c5 hA hjJ hx2.1) (by have:=hxx hx1 hx2;omega) hc1
    ·exact hjs ⟨β,hr,he⟩
   ·exact hjs ⟨β,hr,he⟩
  obtain ⟨βj,hrj,hej⟩:=hjs
  have jn:∀ {β:Fin 2} {v:Fin n},OrReaches n C (opnd C t0 β) k →
   v∈orIn n C (opnd C t0 (1-β))→ aR n G C (opnd C t0 βj):=fun hr hv=>by
   obtain rfl:=d7 hej hv
   exact k9 hA hjJ Z.2.2.2.2.1.symm hej hrj hr
  have one:∀ {x v},dG n C k x∧aC n G C x v→ aR n G C (opnd C t0 βj)→ False:=
   fun hx hw=>two (c5 hA hkJ hx.1) hw (fun e=>hx.1.2.2.1.ne_empty (e▸hej)) hc1
  rcases dc hkJ hau with ⟨ya,hya⟩|⟨βa,hra,-,hat⟩<;> rcases dc hkJ hzu with ⟨yz,hyz⟩|⟨βz,hrz,-,hzt⟩
  ·exact two (c5 hA hkJ hya.1) (c5 hA hkJ hyz.1) (by have:=hyy hya hyz;omega) hc1
  ·exact one hya (jn hrz hzt)
  ·exact one hyz (jn hra hat)
  rw [d7 hej hat] at hra hat
  rw [d7 hej hzt] at hzt
  obtain ⟨h,hP,hah,hzh⟩:=nK hA (opnd C t0 (1-βj)) (G.ne_of_adj haz) hat hzt
   fun W hW haW hzW=>let ⟨_,hc⟩:=aU col hcol hW
    hcol a z haz ((hc a haW).trans (hc z hzW).symm)
  have ht0':t0∈tops G C:=(mem_filter.mp (ht0▸mem_singleton_self t0)).1
  refine fin (Q:={h}) (M:={opnd C t0 βj}) ?_
   (by simpa using k9 hA hjJ Z.2.2.2.2.1.symm hej hrj hra)
   (by simp only [card_singleton];omega)
  simp only [mem_singleton,forall_eq]
  refine ⟨hP,fun hs=>hcol a z haz (bB _ _ _
   (hcol p a (e5 Z (hs hah) ⟨t0,ht0',βj,hrj,hat⟩)).symm
   (hcol p z (e5 Z (hs hzh) ⟨t0,ht0',βj,hrj,hzt⟩)).symm),fun γ _ hs=>?_⟩
  fin_cases γ
  exacts [gS Z ha (hs hah),gS Z hz (hs hzh)]
 by_cases hn:∃ γ,∃ z∈orIn n C (opnd C k γ),aC n G C k z
 swap
 ·exact n4 Z fun e he=>(gV Z he).resolve_right fun ⟨γ,c,hc,_,_,_,hu⟩=> hn ⟨γ,c,hc,hu⟩
 obtain ⟨γ,z,hzγ,hzU⟩:=hn
 have hq:∀ γ' y,y∈orIn n C (opnd C k γ')→ aC n G C k y →
  γ'∈({γ}:Finset (Fin 2))∧y=z:=fun γ' y hy hyu=>by
  rcases aS γ γ' with rfl|rfl
  ·exact ⟨mem_singleton_self _,huq _ y z hy hyu hzγ hzU⟩
  ·exact (hb (by fin_cases γ;exacts [⟨⟨z,hzγ,hzU⟩,y,hy,hyu⟩, ⟨⟨y,hy,hyu⟩,z,hzγ,hzU⟩])).elim
 have hfl:=fO Z hzγ hzU
 have hU:=q7 Z (zf:=fun _=>z) hq
 have hJ':junk G C={k,j}:=by rw [Z.2.2.2.1,pair_comm]
 by_cases hall:∀ u v,G.Adj u v→ wireVal n (aG n C k) C.output (pairInput u v)=false →
  (u=z∧v∈orIn n C (opnd C k (1-γ)))∨(v=z∧u∈orIn n C (opnd C k (1-γ)))
 ·exact fK hR1 col hcol h4 Z.1 hJ' Z.2.2.2.2.1.symm (Z.2.2.2.2.2.2.1 k hkJ)
   (b:=1-γ) (fun x=>eI hA Z.2.1 hkJ (qM Z hjk) _ x) (p3 Z hjk γ) hzγ hfl
   hall
 simp only [not_forall] at hall
 obtain ⟨u,v,huv,hl,hoff⟩:=hall
 obtain ⟨t,ht,β,hr,hkx,hw|⟨hr',hjx⟩⟩:=
  f7 Z.1 Z.2.1 hJ' Z.2.2.2.2.1.symm (Z.2.2.2.2.2.2.1 k hkJ) huv hl
 ·obtain ⟨w,hw,hwuv⟩:=hw
  obtain ⟨γ',hu,hv⟩:=l7 Z hjk hkx
  exfalso;apply hoff
  rcases hwuv with rfl|rfl
  ·obtain ⟨h1,h2⟩:=hq γ' w hu ⟨t,ht,β,hr,hw⟩
   rw [mem_singleton.mp h1] at hv;exact Or.inl ⟨h2,hv⟩
  ·obtain ⟨h1,h2⟩:=hq _ w hv ⟨t,ht,β,hr,hw⟩
   rw [← mem_singleton.mp h1,sub_sub_cancel] at*;exact Or.inr ⟨h2,hu⟩
 obtain ⟨b',hb',e⟩:=cZ Z hjx
 have hpb:s(p,b')∈Ustar G C:=e▸g5 Z.1 Z.2.1 hkJ huv hl
 rw [dT e] at hkx
 have hoff':¬(b'=z∧p∈orIn n C (opnd C k (1-γ))):=by
  rcases Sym2.eq_iff.mp e with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  exacts [fun h=>hoff (Or.inr h),fun h=>hoff (Or.inl h)]
 obtain ⟨M,hM,hM2⟩:=s7 Z ht hr hr'
 obtain ⟨γ1,hp1,hb1⟩:=l7 Z hjk hkx
 have hz:gB n G C k {γ} fun _=>z:=fun γ' h=>by
  rw [mem_singleton.mp h];exact ⟨hzγ,hfl⟩
 by_cases hzp:z=p
 ·exact f9 Z {γ} _ hz hU (Q:=∅) (by simp) hM (mem_singleton_self p)
   (fun _ _=>by simp [hzp]) (by rw [card_singleton,card_empty];omega)
 have hX:∀ γ'∈({γ}:Finset (Fin 2)),(fun _=>z) γ'∈({p,z}:Finset (Fin n)):=by simp
 have hXc:#({p,z}:Finset (Fin n))=2:=card_pair (Ne.symm hzp)
 have one:∀ {w:ℕ} {x y:Fin n},x≠y→ x∈orIn n C w→ y∈orIn n C w →
  (∀ W,aB G (Ustar G C) W→ x∈W→ y∈W→ False) →
  (∀ h,x∈orIn n C h→ y∈orIn n C h→ ¬orIn n C h⊆orIn n C (opnd C j (1-α)) ∧
   ¬orIn n C h⊆orIn n C (opnd C k (1-γ)))→ False:=fun hxy hx hy hsp hq'=>by
  obtain ⟨h,hP,hxh,hyh⟩:=nK hA _ hxy hx hy hsp
  obtain ⟨n1,n2⟩:=hq' h hxh hyh
  exact f9 Z {γ} _ hz hU (Q:={h}) (by simpa using ⟨hP,n1,n2⟩) hM (by simp) hX
   (by rw [hXc,card_singleton];omega)
 have sp:∀ {a x y:Fin n},G.Adj a y→ s(a,x)∈Ustar G C→ x≠y →
  ∀ W,aB G (Ustar G C) W→ x∈W→ y∈W→ False:=
  fun hay hax hxy W hW hx hy=>hxy (card_le_one.mp (a4 h4 sdiff_subset hW _ _ hay)
   _ (mem_inter.mpr ⟨hx,mem_insert_of_mem (aD.mpr hax)⟩) _
   (mem_inter.mpr ⟨hy,mem_insert_self _ _⟩))
 rcases aS γ γ1 with h|h<;>rw [h] at hp1 hb1
 ·exact one (Ne.symm hzp) hp1 hzγ (sp (hfl b' hb1).symm (Sym2.eq_swap▸hpb) (Ne.symm hzp))
   fun h' hph _=>⟨fun hs=>sO Z (hs hph),fun hs=>gS Z hp1 (hs hph)⟩
 rw [sub_sub_cancel] at hb1
 have hbz:b'≠z:=fun h'=>hoff' ⟨h',hp1⟩
 by_cases hzB:z∈orIn n C (opnd C j (1-α))
 ·exact mQ Z {γ} _ hz {z} (card_singleton z).le (singleton_subset_iff.mpr hzB)
   (fun W hW=>by
    rw [← insert_eq];exact a4 h4 sdiff_subset hW p z (hfl p hp1).symm)
   (fun a ha _=>by rw [mem_singleton.mp ha];exact ⟨γ,mem_singleton_self _,p,hp1, Sym2.eq_swap⟩)
   (fun γ' hγ' a ha haT=>by
    rw [mem_singleton.mp hγ',mem_singleton.mp ha] at haT;exact absurd haT (gS Z hzγ))
   hU (Q:=∅) (by simp) hM (by simp) hX (by rw [hXc,card_empty,card_singleton];omega)
 ·exact one hbz hb1 hzγ (sp (hfl p hp1).symm hpb hbz)
   fun h' _ hzh=>⟨fun hs=>hzB (hs hzh),fun hs=>gS Z hzγ (hs hzh)⟩
variable {α' : Fin 2} {p' : Fin n}
lemma mW (Z':j1 G C k j α' p') :
 ∀ e∈Ustar G C,∃ v∈({p,p'}:Finset (Fin n)),v∈e:=fun e he=>by
 induction e using Sym2.ind with|h u v=>?_
 rcases l4 Z he with h|h
 ·obtain ⟨b,-,e⟩:=cZ Z h
  exact ⟨p,mem_insert_self _ _,by rw [e];exact Sym2.mem_mk_left _ _⟩
 ·obtain ⟨b,-,e⟩:=cZ Z' h
  exact ⟨p',mem_insert_of_mem (mem_singleton_self _),by rw [e];exact Sym2.mem_mk_left _ _⟩
include hR1 hcol in
lemma q9 (hjk:¬InCone n C j k)
 (hno:∀ u v,s(u,v)∈Ustar G C→ gateVal n C j (pairInput u v)=true →
  gateVal n C k (pairInput u v)=false) :
 ∃ L:Finset (Fin n),(∀ ℓ∈L,ℓ∈aE (Ustar G C) p ∧
  ℓ∈orIn n C (opnd C j (1-α))∧aC n G C j ℓ)∧(∀ u v,s(u,v)∈Ustar G C →
  gateVal n C j (pairInput u v)=true→ s(u,v)∈L.image (s(p,·)))∧1<#L:=by
 classical
 refine ⟨(aE (Ustar G C) p).filter fun ℓ=>ℓ∈orIn n C (opnd C j (1-α)) ∧
  aC n G C j ℓ,fun ℓ h=>by simpa using h,fun u v he hj=>?_,?_⟩
 ·obtain ⟨ℓ,hℓ,hU,e⟩:=l5 Z he hj (hno u v he hj)
  exact mem_image.mpr ⟨ℓ,mem_filter.mpr ⟨aD.mpr (e▸he),hℓ,hU⟩,e.symm⟩
 obtain ⟨b1,b2,hb,⟨h1,a1,l1⟩,h2,a2,l2⟩:=kP hR1 col hcol Z hjk
 have hm:∀ b∈orIn n C (opnd C j (1-α)),G.Adj p b →
  wireVal n (aG n C j) C.output (pairInput p b)=false→ b∈(aE (Ustar G C) p).filter
   fun ℓ=>ℓ∈orIn n C (opnd C j (1-α))∧aC n G C j ℓ:=fun b hb ha hl=>by
  have hU:=g5 Z.1 Z.2.1 (aY Z).1 ha hl
  obtain ⟨ℓ,hℓ,hU',e⟩:=l5 Z hU (kD Z hb) (hno p b hU (kD Z hb))
  exact mem_filter.mpr ⟨aD.mpr hU,hb,Sym2.congr_right.mp e▸hU'⟩
 exact one_lt_card.mpr ⟨b1,hm b1 h1 a1 l1,b2,hm b2 h2 a2 l2,hb⟩
include hR1 hcol in
lemma rS (Z':j1 G C k j α' p') :
 ∃ M:Finset ℕ,(∀ h∈M,aR n G C h)∧2≤2*#(centreless G C)+#M:=by
 have hA:=Z.1.1
 obtain ⟨hj,hk⟩:=aY Z
 rcases Nat.eq_zero_or_pos #(centreless G C) with hc|hc
 swap
 ·exact ⟨∅,by simp,by omega⟩
 have mj:∀ {j k α p},j1 G C j k α p→ ¬InCone n C j k→ ∃ m,dG n C j m:=
  fun {j k α p} Z hjk=>by
  obtain ⟨b,-,-,⟨-,hpb,hl⟩,-⟩:=kP hR1 col hcol Z hjk
  obtain ⟨a,ha,b',hr,-⟩:=f7 Z.1 Z.2.1 Z.2.2.2.1 Z.2.2.2.2.1 hjk hpb hl
  obtain ⟨m,b'',hm,hop,hwm,hne',he,hrJ⟩:=fE hA (aA.mp (aY Z).1).2.1
   hr (nonempty_iff_ne_empty.mpr fun e=>(card_pos.mpr ⟨a,c7 ha e⟩).ne' hc)
  exact ⟨m,hm,hop,hne',b'',he,hrJ⟩
 obtain ⟨m,hm⟩:=mj Z (Z'.2.2.2.2.2.2.1 j hj)
 obtain ⟨m',hm'⟩:=mj Z' (Z.2.2.2.2.2.2.1 k hk)
 by_cases e:m=m'
 ·subst e
  obtain ⟨g,hg,hg0⟩:=jN hA hj Z.2.2.2.2.1.symm hm hm'
  exact ⟨{n+m,g},by simp [c5 hA hj hm,hg],by
   rw [card_pair fun e=>hm.2.2.1.ne_empty (by rw [e];exact hg0)];omega⟩
 ·exact ⟨{n+m,n+m'},by simp [c5 hA hj hm,c5 hA hk hm'],by
   rw [card_pair (by omega)];omega⟩
include hR1 hcol in
lemma pS (Z':j1 G C k j α' p') (S:Finset (Fin n))
 (hS:S⊆orIn n C (opnd C j (1-α))∪orIn n C (opnd C k (1-α')))
 (hsp:∀ W,aB G (Ustar G C) W→ #(W∩S)≤1)
 (hu:#(Ustar G C)+#({p,p'}:Finset (Fin n))≤#S+1):False:=by
 obtain ⟨P,hP,hc⟩:=kB Z.1.1 {opnd C j (1-α),opnd C k (1-α')} S hsp
 rw [biUnion_insert,singleton_biUnion,inter_eq_right.mpr hS] at hc
 have:=card_le_two (a:=opnd C j (1-α)) (b:=opnd C k (1-α'))
 obtain ⟨M,hM,hM2⟩:=rS hR1 col hcol Z Z'
 exact cF Z (mW Z Z') (fun h hh=>(hP h hh).1) hM (by omega)
lemma lV (Z':j1 G C k j α' p') (hb:p'∈orIn n C (opnd C j (1-α))∨p=p') :
 aE (Ustar G C) p⊆orIn n C (opnd C j (1-α))∪orIn n C (opnd C k (1-α')):=
 fun ℓ hℓ=>by
 have he:=aD.mp hℓ
 rcases l4 Z he with h|h
 ·obtain ⟨b,hb',e⟩:=cZ Z h
  rw [Sym2.congr_right.mp e];exact mem_union_left _ hb'
 ·obtain ⟨b,hb',e⟩:=cZ Z' h
  rcases Sym2.eq_iff.mp e with ⟨-,h2⟩|⟨-,h2⟩
  ·rw [h2];exact mem_union_right _ hb'
  ·rcases hb with hb|hb
   ·rw [h2];exact mem_union_left _ hb
   ·exact ((dE he).ne (hb.trans h2.symm)).elim
include hR1 hcol in
theorem pN (Z':j1 G C k j α' p'):False:=by
 classical
 have hA:=Z.1.1
 have h4:=Z.2.2.1
 obtain ⟨hjJ,hkJ⟩:=aY Z
 have hkj:=Z.2.2.2.2.1
 have hcov:=mW Z Z'
 by_cases hpp:p=p'
 ·subst hpp
  refine pS hR1 col hcol Z Z' _ (lV Z Z' (Or.inr rfl))
   (fun W hW=>aF h4 sdiff_subset hW p) ?_
  have:=(card_le_card (t:=(aE (Ustar G C) p).image (s(p,·))) fun e he=>by
   obtain ⟨v,hv,hve⟩:=hcov e he
   obtain rfl:v=p:=by simpa using hv
   obtain ⟨w,rfl⟩:=Sym2.mem_iff_exists.mp hve
   exact mem_image_of_mem _ (aD.mpr he)).trans card_image_le
  rw [insert_eq_of_mem (mem_singleton_self p),card_singleton];omega
 by_cases hx:∃ u v,s(u,v)∈Ustar G C∧gateVal n C j (pairInput u v)=true ∧
  gateVal n C k (pairInput u v)=true
 ·obtain ⟨u,v,he,hju,hku⟩:=hx
  obtain ⟨b1,hb1,e1⟩:=cZ Z hju
  obtain ⟨b2,hb2,e2⟩:=cZ Z' hku
  obtain ⟨h1,h2⟩:b1=p'∧b2=p:=by
   rcases Sym2.eq_iff.mp (e1.symm.trans e2) with ⟨h,-⟩|⟨h1,h2⟩
   exacts [absurd h hpp,⟨h2,h1.symm⟩]
  rw [h1] at hb1 e1
  rw [h2] at hb2
  have hpp':=e1▸he
  have hc:∀ x∈aE (Ustar G C) p,∀ y∈aE (Ustar G C) p',col x≠col y:= fun x hx y hy e=>by
   have h1:=hcol _ _ (dQ hx)
   have h2:=hcol _ _ (dQ hy)
   have h3:=hcol _ _ (dE hpp')
   rw [e] at h1
   revert h1 h2 h3
   cases col p<;>cases col p'<;>cases col y<;>decide
  have hp:p∈aE (Ustar G C) p':=aD.mpr (Sym2.eq_swap▸hpp')
  have:=card_le_card (s:=Ustar G C) (t:=(aE (Ustar G C) p).image (s(p,·)) ∪
   ((aE (Ustar G C) p').erase p).image (s(p',·))) fun e he=>by
   by_cases hpe:p∈e
   ·obtain ⟨w,rfl⟩:=Sym2.mem_iff_exists.mp hpe
    exact mem_union_left _ (mem_image_of_mem _ (aD.mpr he))
   obtain ⟨v,hv,hve⟩:=hcov e he
   rcases mem_insert.mp hv with rfl|hv
   ·exact absurd hve hpe
   rw [mem_singleton.mp hv] at hve
   obtain ⟨w,rfl⟩:=Sym2.mem_iff_exists.mp hve
   exact mem_union_right _ (mem_image_of_mem _ (mem_erase.mpr
    ⟨fun h=>hpe (h▸Sym2.mem_mk_right _ _),aD.mpr he⟩))
  have:=this.trans ((card_union_le _ _).trans (add_le_add card_image_le card_image_le))
  rw [card_erase_of_mem hp] at this
  have:=card_pos.mpr ⟨p,hp⟩
  refine pS hR1 col hcol Z Z' _ (union_subset (lV Z Z' (Or.inl hb1)) fun ℓ hℓ=>by
   rcases mem_union.mp (lV Z' Z (Or.inl hb2) hℓ) with h|h
   exacts [mem_union_right _ h,mem_union_left _ h])
   (fun W hW=>card_le_one.mpr fun x hx y hy=>?_) ?_
  ·obtain ⟨c0,hc0⟩:=aU col hcol hW
   have s1:=card_le_one.mp (aF h4 sdiff_subset hW p)
   have s2:=card_le_one.mp (aF h4 sdiff_subset hW p')
   simp only [mem_inter,mem_union] at hx hy
   obtain ⟨hxW,hx|hx⟩:=hx<;>obtain ⟨hyW,hy|hy⟩:=hy
   ·exact s1 x (mem_inter.mpr ⟨hxW,hx⟩) y (mem_inter.mpr ⟨hyW,hy⟩)
   ·exact (hc x hx y hy ((hc0 x hxW).trans (hc0 y hyW).symm)).elim
   ·exact (hc y hy x hx ((hc0 y hyW).trans (hc0 x hxW).symm)).elim
   ·exact s2 x (mem_inter.mpr ⟨hxW,hx⟩) y (mem_inter.mpr ⟨hyW,hy⟩)
  ·rw [card_union_of_disjoint (disjoint_left.mpr fun x hx hx'=>hc x hx x hx' rfl),
    card_pair hpp];omega
 simp only [not_exists,not_and] at hx
 have hno:∀ {j k α p},j1 G C j k α p→ (∀ u v,s(u,v)∈Ustar G C →
  gateVal n C j (pairInput u v)=true→ gateVal n C k (pairInput u v)=true→ False) →
  ∀ u v,s(u,v)∈Ustar G C→ gateVal n C j (pairInput u v)=true →
   gateVal n C k (pairInput u v)=false:=fun _ h u v he hj=>by
  cases hk:gateVal _ _ _ (pairInput u v)
  exacts [rfl,(h u v he hj hk).elim]
 obtain ⟨L1,hL1,cv1,two1⟩:=q9 hR1 col hcol Z (Z'.2.2.2.2.2.2.1 j hjJ) (hno Z hx)
 obtain ⟨L2,hL2,cv2,two2⟩:=q9 hR1 col hcol Z' (Z.2.2.2.2.2.2.1 k hkJ)
  (hno Z' fun u v he h1 h2=>hx u v he h2 h1)
 have hu:#(Ustar G C)≤#L1+#L2:=by
  refine (card_le_card (t:=L1.image (s(p,·))∪L2.image (s(p',·))) fun e he=>?_).trans
   ((card_union_le _ _).trans (add_le_add card_image_le card_image_le))
  induction e using Sym2.ind with|_ u v=>?_
  rcases l4 Z he with h|h
  exacts [mem_union_left _ (cv1 u v he h),mem_union_right _ (cv2 u v he h)]
 obtain ⟨P1,Q1,M1,T1,hPQ1,hP1,hM1,hT1,hTn1,hT01,cP1,cQ1⟩:=
  lB hA h4 hjJ L1 hL1 fun v hv hu=>e5 Z hv hu
 obtain ⟨P2,Q2,M2,T2,hPQ2,hP2,hM2,hT2,hTn2,hT02,cP2,cQ2⟩:=
  lB hA h4 hkJ L2 hL2 fun v hv hu=>e5 Z' hv hu
 obtain ⟨hPA,hm2⟩:=q6 h4 hpp (fun ℓ h=>(hL1 ℓ h).1) (fun ℓ h=>(hL2 ℓ h).1) hPQ1 hPQ2 hP1 hP2
 have hMM:∀ h∈(M1∪M2).image (n+·),aR n G C h:=fun h hh=>by
  obtain ⟨m,hm,rfl⟩:=mem_image.mp hh
  exact (mem_union.mp hm).elim (c5 hA hjJ<|hM1 m ·) (c5 hA hkJ<|hM2 m ·)
 have hMc:((M1∪M2).image (n+·)).card=#(M1∪M2):= card_image_of_injective _ (add_right_injective n)
 have m1:=card_le_card (subset_union_left (s₁:=M1) (s₂:=M2))
 have m2:=card_le_card (subset_union_right (s₁:=M1) (s₂:=M2))
 have hXc:#({p,p'}:Finset (Fin n))=2:=card_pair hpp
 have hc1:=card_le_card hT1
 have hc2:=card_le_card hT2
 have hP1A:=card_le_card (show P1⊆P1∪Q1∪P2∪Q2 from fun h hh=>
  mem_union_left _ (mem_union_left _ (mem_union_left _ hh)))
 have fin1:∀ (P:Finset ℕ) g,(∀ h∈P,c8 n G C h)→ aR n G C g→ orIn n C g=∅ →
  #(Ustar G C)+2<2+2*#(centreless G C)+#P+#(M1∪M2)+1→ False:=
  fun P g hP hg hg0 hlt=>by
  refine cF Z hcov hP (M:=insert g ((M1∪M2).image (n+·))) (fun h hh=>
   (mem_insert.mp hh).elim (·▸hg) (hMM h)) ?_
  rw [card_insert_of_notMem (s:=(M1∪M2).image (n+·)) fun h=>by
   obtain ⟨m,hm,rfl⟩:=mem_image.mp h
   exact ((mem_union.mp hm).elim (fun h=>(hM1 m h).2.2.1) fun h=>
    (hM2 m h).2.2.1).ne_empty hg0,hMc];omega
 rcases Nat.lt_or_ge #(centreless G C) 1 with hc0|hc
 ·have hz:∀ {T:Finset ℕ},T⊆centreless G C→ T=∅:=fun hT'=>
   eq_empty_of_forall_notMem fun a ha=>by have:=card_pos.mpr ⟨a,hT' ha⟩;omega
  obtain ⟨cM1,hl1⟩:=hT01 (hz hT1)
  obtain ⟨cM2,-⟩:=hT02 (hz hT2)
  by_cases hd:Disjoint M1 M2
  ·rw [card_union_of_disjoint hd] at hMc
   exact cF Z hcov hPA hMM (by omega)
  obtain ⟨m,hm1,hm2⟩:=not_disjoint_iff.mp hd
  obtain ⟨g,hg,hg0⟩:=jN hA hjJ hkj.symm (hM1 m hm1) (hM2 m hm2)
  by_cases he:M1=M2
  ·have hd12:Disjoint P1 P2:=disjoint_left.mpr fun h h1 h2=>
    jP h4 hpp (S:=orIn n C h∩L1) (fun v hv=>⟨dQ (hL1 v (mem_inter.mp hv).2).1,
     e5 Z' ((hP2 h h2).1 (mem_inter.mp hv).1) (by
      obtain ⟨m',hm',a,ha,β,hr,hℓa⟩:=hl1 v (mem_inter.mp hv).2
      rw [he] at hm'
      exact ⟨a,ha,β,cG hA hr (lX hA (hM2 m' hm')),hℓa⟩)⟩)
     (hPQ1 h (mem_union_left _ h1)).2
   exact fin1 _ g (fun h hh=>(mem_union.mp hh).elim (fun h1=>(hPQ1 h (mem_union_left _ h1)).1)
    fun h2=>(hPQ2 h (mem_union_left _ h2)).1) hg hg0 (by rw [card_union_of_disjoint hd12];omega)
  ·have:=card_union_add_card_inter M1 M2
   have:=card_lt_card ⟨inter_subset_union (s:=M1) (t:=M2),fun h=>he (subset_antisymm
    ((subset_union_left.trans h).trans inter_subset_right)
    ((subset_union_right.trans h).trans inter_subset_left))⟩
   exact fin1 _ g hPA hg hg0 (by omega)
 ·by_cases hc2:2≤#(centreless G C)∨#T1+#T2≤1
  ·exact cF Z hcov hPA hMM (by omega)
  simp only [not_or,not_le] at hc2
  obtain ⟨t0,ht0⟩:=card_eq_one.mp (show #(centreless G C)=1 by omega)
  have hTe:∀ {T:Finset ℕ},T⊆centreless G C→ 0<#T→ t0∈T:=fun hT hp=>by
   obtain ⟨a,ha⟩:=card_pos.mp hp
   have:=hT ha;rw [ht0,mem_singleton] at this;exact this▸ha
  obtain ⟨β1,hr1,hn1⟩:=hTn1 t0 (hTe hT1 (by omega))
  obtain ⟨β2,hr2,hn2⟩:=hTn2 t0 (hTe hT2 (by omega))
  obtain ⟨g,hg,hg0⟩:=r4 hA hjJ hkj.symm (by rw [ht0];exact mem_singleton_self _)
   hr1 hn1 hr2 hn2
  exact fin1 _ g hPA hg hg0 (by omega)
end Z
theorem eQ (hR1:cM) (col:Fin n→ Bool)
 (hcol:∀ u v,G.Adj u v→ col u≠col v) (h4:NoFourCycle G)
 (hC:IsLeastAO G C) (hT:TopForm G C) (hj:(junk G C).card=2)
 (hoff:∀ k∈junk G C,∀ v:Fin n,gateVal n C k (unitInput v)=false)
 {j:ℕ} (hj_mem:j∈junk G C) (hbot:∀ k∈junk G C,¬InCone n C k j) :
 2≤(orIn n C (opnd C j 0)).card∧2≤(orIn n C (opnd C j 1)).card:=by
 have hA:=hC.1
 obtain ⟨k,hkj,hJ⟩:=gC hj hj_mem
 have sng:∀ {i i':ℕ},junk G C={i,i'}→ i'≠i→ (∀ m∈junk G C,¬InCone n C m i) →
  ¬(2≤(orIn n C (opnd C i 0)).card∧2≤(orIn n C (opnd C i 1)).card) →
  ∃ α p,j1 G C i i' α p:=fun {i i'} hJ' hne hb hn=>by
  have hi:i∈junk G C:=by rw [hJ'];simp
  obtain ⟨-,h0,h1,-⟩:=cH hA hT hi hb (hoff i hi)
  obtain ⟨α,hα⟩:∃ α:Fin 2,(orIn n C (opnd C i α)).card<2:=by
   by_contra h';simp only [not_exists,not_lt] at h';exact hn ⟨h' 0,h' 1⟩
  have:=card_pos.mpr (show (orIn n C (opnd C i α)).Nonempty by fin_cases α;exacts [h0,h1])
  obtain ⟨p,hp⟩:=card_eq_one.mp (show (orIn n C (opnd C i α)).card=1 by omega)
  exact ⟨α,p,hC,hT,h4,hJ',hne,hoff,hb,hp⟩
 by_contra hcon
 obtain ⟨α,p,Z⟩:=sng hJ hkj hbot hcon
 by_cases hc:InCone n C j k
 ·obtain ⟨b,hb⟩:=g8 hA hT (aP hc) hJ hc
  by_cases hnb:OrReaches n C (opnd C k (1-b)) j
  ·have h01:∀ γ,OrReaches n C (opnd C k γ) j:=fun γ=>by
    rcases aS b γ with rfl|rfl;exacts [hb,hnb]
   exact rL Z (fun hne=>tB col hcol Z (h01 0) (h01 1) hne)
    fun hne _ _=>tG Z (h01 0) (h01 1) hne
  ·exact rL Z (fun hne=>rU col hcol Z hb hnb (hne b))
    fun hne _ _=>rT col hcol Z hb hnb hne
 ·by_cases hw:2≤(orIn n C (opnd C k 0)).card∧2≤(orIn n C (opnd C k 1)).card
  ·exact pU hR1 col hcol Z hc fun γ=>by fin_cases γ;exacts [hw.1,hw.2]
  ·obtain ⟨α',p',Z'⟩:=sng (by rw [hJ,pair_comm]) hkj.symm (qM Z hc) hw
   exact pN hR1 col hcol Z Z'
theorem p9 (hR1:cM) (col:Fin n→ Bool)
 (hcol:∀ u v,G.Adj u v→ col u≠col v) (h4:NoFourCycle G)
 (hC:IsLeastAO G C) (hT:TopForm G C) (hj:(junk G C).card=2)
 (hoff:∀ k∈junk G C,∀ v:Fin n,gateVal n C k (unitInput v)=false) :
 mM G C:=fun _ _ hqr hJ=>
 eQ hR1 col hcol h4 hC hT hj hoff (by rw [hJ];simp) (dF hqr hJ)
end
def cI (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (q r:ℕ) (b:Fin 2):Prop:=gP G C q r/\OrReaches n C (opnd C r b) q/\¬OrReaches n C (opnd C r (1-b)) q/\(orIn n C (opnd C r b)).Nonempty
def b8 (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (q r:ℕ) (b:Fin 2):Prop:=∀x,gateVal n C q x=true ->(∃d∈orIn n C (opnd C r (1-b)),x d=true) ->graphFun G ∅ x=true
lemma j7 {D:Circuit} {m:ℕ} (hC:m≤C.gates.length) (hD:m≤D.gates.length) (h:∀k<m,gateAt C k=gateAt D k) {g:ℕ}:∀w<n+m,(OrReaches n C w g↔OrReaches n D w g):=by
 intro w
 induction w using Nat.strong_induction_on with
 |_ w ih=>
  intro hw;rcases Nat.lt_or_ge w n with hn|hn
  ·exact⟨λh1=>absurd h1.1 (by omega),λh1=>absurd h1.1 (by omega)⟩
  obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by omega⟩;simp only[bD,h k (by omega)];exact and_congr ⟨λ_=>by omega,λ_=>by omega⟩ (or_congr Iff.rfl (and_congr Iff.rfl (exists_congr λi=>and_congr_right λ_=>and_congr_right λhlt=>ih i hlt (by omega))))
lemma qP {D:Circuit} {m:ℕ} (hC:m≤C.gates.length) (hD:m≤D.gates.length) (h:∀k<m,gateAt C k=gateAt D k) {w:ℕ} (hw:w<n+m):orIn n C w=orIn n D w:=by
 ext v;simp only[dV];refine or_congr Iff.rfl ⟨λ⟨k,_,h1,h2,h3⟩=>?_,λ⟨k,_,h1,h2,h3⟩=>?_⟩
 ·have:=(aX h1).1;exact⟨k,by omega,(j7 hC hD h w hw).mp h1,h k (by omega)▸h2,h k (by omega)▸h3⟩
 ·have:=(aX h1).1;exact⟨k,by omega,(j7 hC hD h w hw).mpr h1,(h k (by omega)).symm▸h2,(h k (by omega)).symm▸h3⟩
lemma g9 {j:ℕ} {g:Gate} (hj:j<C.gates.length) (hin:∀i∈g.inputs,n≤ i ->InCone n C (i-n) j) (a:ℕ):∀k,InCone n (aL C j g) a k ->InCone n C a k:=by
 intro k
 induction k using Nat.strong_induction_on with
 |_ k ih=>
  intro hc;obtain⟨hk,i,hik,hin',h3⟩:=aZ.mp hc;have hk':k<C.gates.length:=by simpa[aL]using hk
  have h3':a=i\/InCone n C a i:=h3.imp_right (ih i hik);by_cases hkj:k=j
  ·subst hkj;rw[aL,bR hk',Function.update_self]at hin';have:=hin _ hin' (by omega);rw[show n+i-n=i by omega]at this;rcases h3' with rfl|h3'
   ·exact this
   ·exact dI h3' this
  ·rw[(cV j g).2 k hk' hkj]at hin';exact aZ.mpr ⟨hk',i,hik,hin',h3'⟩
lemma qV (hC:IsLeastAO G C) {j:ℕ} {u v:Fin n} (huv:G.Adj u v) (hl:wireVal n (aG n C j) C.output (pairInput u v)=false):gateVal n C j (pairInput u v)=true:=by
 have hA:=hC.1;have hF:wireVal n C C.output (pairInput u v)=true:=by
  rw[show wireVal n C C.output _=graphFun G ∅ _ from congrFun hC.2.1 _,aT];exact huv
 by_contra h;rw[Bool.not_eq_true]at h;have hK:=bJ (n:=n) (C:=C) j;by_cases ho:C.output<n+C.gates.length
 ·have:=kQ (C₁:=C) (C₂:=aG n C j) (m:=C.gates.length) le_rfl hK.1.ge (λk hk hkj=>(hK.2 k hk hkj).symm) (λk hk _=>eS hA hk) _ (λh1=>by rw[show wireVal n C (n+j) _=gateVal n C j _ from rfl,h]at h1;cases h1) _ ho hF;rw[hl]at this;cases this
 ·rw[(a5 C _).2.1 _ (by omega)]at hF;cases hF
section F
variable {q r:ℕ} {b:Fin 2}
lemma b4 (Z:cI G C q r b):q∈junk G C/\r∈junk G C:=bK Z.1
lemma dU (Z:cI G C q r b) (x:Fin n ->Bool):gateVal n C r x=true↔(gateVal n C q x=true\/∃c∈orIn n C (opnd C r b),x c=true)/\∃d∈orIn n C (opnd C r (1-b)),x d=true:=(cN Z.1.1.1 Z.1.2.1 Z.1.2.2.2.1 Z.1.2.2.2.2.1 Z.1.2.2.2.2.2.1 Z.2.1 Z.2.2.1).1 x
lemma kZ (Z:cI G C q r b):Disjoint (orIn n C (opnd C r b)) (orIn n C (opnd C r (1-b))):=(cN Z.1.1.1 Z.1.2.1 Z.1.2.2.2.1 Z.1.2.2.2.2.1 Z.1.2.2.2.2.2.1 Z.2.1 Z.2.2.1).2.2
lemma qR (Z:cI G C q r b):(orIn n C (opnd C r (1-b))).Nonempty:=(cN Z.1.1.1 Z.1.2.1 Z.1.2.2.2.1 Z.1.2.2.2.2.1 Z.1.2.2.2.2.2.1 Z.2.1 Z.2.2.1).2.1
lemma vG (Z:cI G C q r b) (x:Fin n ->Bool):wireVal n C (opnd C r (1-b)) x=true↔∃d∈orIn n C (opnd C r (1-b)),x d=true:=by
 rw[fR Z.1.1.1 Z.1.2.1 Z.1.2.2.2.1 Z.1.2.2.2.2.1];simp[Z.2.2.1]
theorem sH (hR1:cM) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (Z:cI G C q r b) (β:Fin 2) {p:Fin n} (hp:p∈orIn n C (opnd C q (1-β))) (hpf:∀t∈orIn n C (opnd C q β),G.Adj p t) (hacc:∀u v,G.Adj u v ->wireVal n (aG n C q) C.output (pairInput u v)=true\/p∈s(u,v)/\∃t∈orIn n C (opnd C q β),t∈s(u,v)) (hx:2≤(readers n C q).card\/∃x,(∃c∈orIn n C (opnd C r b),x c=true)/\(∃d∈orIn n C (opnd C r (1-b)),x d=true)/\graphFun G ∅ x=false):False:=by
 have hC:=Z.1.1;have hA:=hC.1;obtain⟨hq,hr⟩:=b4 Z;obtain⟨hql,hqop,-⟩:=aA.mp hq;have hv:∀x,GateOp.and.eval [wireVal n C (opnd C q β) x,wireVal n C p x]=true↔(∃t∈orIn n C (opnd C q β),x t=true)/\x p=true:=λx=>by
  simp only[GateOp.eval,List.all_cons,List.all_nil,id,Bool.and_true,Bool.and_eq_true,bA,eI hA Z.1.2.1 hq (dF Z.1.2.2.2.1 Z.1.2.2.2.2.1)]
 have ha:=aH hA hql β;have hb:p.1<n+q:=by have:=p.2;omega
 have hcl:∀x,GateOp.and.eval [wireVal n C (opnd C q β) x,wireVal n C p x]=true ->graphFun G ∅ x=true:=λx hx=>by
  obtain⟨⟨t,ht,hxt⟩,hxp⟩:=(hv x).mp hx;exact(dJ x).mpr ⟨p,t,hpf t ht,hxp,hxt⟩
 obtain⟨hD,hj1,-⟩:=cT hC hql (Or.inl rfl) ha hb (λx hx=>by
  obtain⟨⟨t,ht,hxt⟩,hxp⟩:=(hv x).mp hx
  exact(bP Z.1 β x).mpr ⟨⟨t,ht,hxt⟩,p,hp,hxp⟩) λu v huv=>
  (hacc u v huv).imp id λ⟨h1,t,ht,h2⟩=>(hv _).mpr ⟨⟨t,ht,by
   rcases Sym2.mem_iff.mp h2 with rfl|rfl<;>simp[pairInput]⟩,by
   rcases Sym2.mem_iff.mp h1 with rfl|rfl<;>simp[pairInput]⟩
 have hsp:=b7 hA hql (Or.inl rfl) ha hb;have hag:=cV (C:=C) q ⟨GateOp.and,[opnd C q β,p.1]⟩
 have hbf:BelowF G (aL C q ⟨GateOp.and,[opnd C q β,p.1]⟩) q:=λx hx=>hcl x (by
  rw[show gateVal n _ q x=wireVal n _ (n+q) x from rfl,(hsp x).2.2.2.2.2]at hx;exact hx)
 rcases hx with hx|⟨x,⟨c,hc,hxc⟩,⟨d,hd,hxd⟩,hFx⟩
 ·have h1:=eC hD (i:=q) (by rw[hag.1];exact hql) hbf;have he:readers n (aL C q ⟨GateOp.and,[opnd C q β,p.1]⟩) q=readers n C q:=by
   ext k;simp only[readers,mem_filter,mem_range,hag.1];refine and_congr_right λhk=>?_;by_cases hkq:k=q
   ·subst hkq;rw[aL,bR hk,Function.update_self];simp only[List.mem_cons,List.not_mem_nil,or_false];refine⟨by omega,λh=>?_⟩;have:=dH hA hk h;omega
   ·rw[hag.2 k hk hkq]
  rw[he]at h1;omega
 ·obtain⟨hrl,hrop,-⟩:=aA.mp hr;have hrq:r≠q:=by have:=Z.1.2.2.2.1;omega
  apply hR1 n G _ col hcol Z.1.2.2.1 hD;rw[card_eq_one];refine⟨r,ext λk=>⟨λhk=>?_,λhk=>?_⟩⟩
  ·rcases hj1 k hk with h|h
   ·exact absurd (h▸hbf) (aA.mp hk).2.2
   ·rw[Z.1.2.2.2.2.1,mem_insert,mem_singleton]at h;rcases h with h|h
    ·exact absurd (h▸hbf) (aA.mp hk).2.2
    ·exact mem_singleton.mpr h
  ·rw[mem_singleton.mp hk];have hw:∀β',wireVal n (aL C q ⟨GateOp.and,[opnd C q β,p.1]⟩) (opnd C r β') x=true:=λβ'=>by
    rcases aS b β' with rfl|rfl;exacts[b9 hA hag hqop hc hxc,b9 hA hag hqop hd hxd]
   refine aA.mpr ⟨by rw[hag.1];exact hrl,by rw[hag.2 r hrl hrq];exact hrop,λhB=>?_⟩
   have:=hB x (by
    show wireVal n _ (n+r) x=true
    rw[fV hA hag hrl hrq hrop x,hw 0,hw 1];rfl)
   rw[hFx]at this;cases this
theorem uH (hR1:cM) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (Z:cI G C q r b) (hacc:∀u v,G.Adj u v ->wireVal n (aG n C r) C.output (pairInput u v)=true\/gateVal n C q (pairInput u v)=true/\∃d∈orIn n C (opnd C r (1-b)),pairInput u v d=true):False:=by
 classical
 have hC:=Z.1.1;have hA:=hC.1;obtain⟨hq,hr⟩:=b4 Z;have hqr:=Z.1.2.2.2.1;obtain⟨hrl,hrop,-⟩:=aA.mp hr;obtain⟨hql,hqop,-⟩:=aA.mp hq;have hw1:=aH hA hrl (1-b);have hv:∀x,GateOp.and.eval [wireVal n C (n+q) x,wireVal n C (opnd C r (1-b)) x]=true↔gateVal n C q x=true/\∃d∈orIn n C (opnd C r (1-b)),x d=true:=λx=>by
  rw[←vG Z x];simp only[GateOp.eval,List.all_cons,List.all_nil,id,Bool.and_true,Bool.and_eq_true];exact Iff.rfl
 obtain⟨hD,hj1,hj2⟩:=cT hC hrl (Or.inl rfl) (by omega:n+q<n+r) hw1 (λx hx=>(dU Z x).mpr ⟨Or.inl ((hv x).mp hx).1,((hv x).mp hx).2⟩) λu v huv=>(hacc u v huv).imp id λh=>(hv _).mpr h;have hsp:=b7 hA hrl (Or.inl rfl) (by omega:n+q<n+r) hw1;have hag:=cV (C:=C) r ⟨GateOp.and,[n+q,opnd C r (1-b)]⟩;set D:=aL C r ⟨GateOp.and,[n+q,opnd C r (1-b)]⟩with hDdef;have hqD:q∈junk G D:=hj2 q hq (by omega) λhc=>absurd (aP hc) (by omega);have hrv:∀x,gateVal n D r x=true↔gateVal n C q x=true/\∃d∈orIn n C (opnd C r (1-b)),x d=true:=λx=>by
  rw[show gateVal n D r x=wireVal n D (n+r) x from rfl,(hsp x).2.2.2.2.2];exact hv x
 by_cases hg:b8 G C q r b
 ·have hbf:BelowF G D r:=λx hx=>hg x ((hrv x).mp hx).1 ((hrv x).mp hx).2;apply hR1 n G D col hcol Z.1.2.2.1 hD;rw[card_eq_one];refine⟨q,ext λk=>⟨λhk=>?_,λhk=>mem_singleton.mp hk▸hqD⟩⟩;rcases hj1 k hk with h|h
  ·exact absurd (h▸hbf) (aA.mp hk).2.2
  ·rw[Z.1.2.2.2.2.1,mem_insert,mem_singleton]at h;rcases h with h|h
   ·exact mem_singleton.mpr h
   ·exact absurd (h▸hbf) (aA.mp hk).2.2
 simp only[b8,not_forall]at hg;obtain⟨x0,h1,⟨d0,hd0,hxd0⟩,h3⟩:=hg;have hDr:gateAt D r=⟨GateOp.and,[n+q,opnd C r (1-b)]⟩:=by
  rw[hDdef,aL,bR hrl,Function.update_self]
 have hrD:r∈junk G D:=aA.mpr ⟨by rw[hag.1];exact hrl,by rw[hDr],λhB=>h3 (hB x0 ((hrv x0).mpr ⟨h1,d0,hd0,hxd0⟩))⟩;have hJD:junk G D={q,r}:=by
  ext k;simp only[mem_insert,mem_singleton];refine⟨λhk=>?_,λh=>h.elim (·▸hqD) (·▸hrD)⟩;rcases hj1 k hk with h|h
  ·exact Or.inr h
  ·rwa[Z.1.2.2.2.2.1,mem_insert,mem_singleton]at h
 have hg':∀k<r,gateAt C k=gateAt D k:=λk hk=>(hag.2 k (by omega) (by omega)).symm;have hor:∀w<n+r,∀g,OrReaches n C w g↔OrReaches n D w g:=λw hw g=>j7 hrl.le (by rw[hag.1];exact hrl.le) hg' w hw;have hoi:∀w<n+r,orIn n C w=orIn n D w:=λw hw=>qP hrl.le (by rw[hag.1];exact hrl.le) hg' hw;have hqo:∀β,opnd D q β=opnd C q β:=λβ=>by
  simp only[opnd,hag.2 q hql (by omega)]
 have hD0:opnd D r 0=n+q:=by simp[opnd,hDr]
 have hD1:opnd D r 1=opnd C r (1-b):=by simp[opnd,hDr]
 have hqopD:(gateAt D q).op=GateOp.and:=by rw[hag.2 q hql (by omega)];exact hqop
 refine dZ hR1 col hcol Z.1.2.2.1 hD ?_ q r hqr hJD ?_ ⟨?_,?_⟩ 0 ?_ ?_ ?_
 ·intro i hi j hj hiop hib hjop hc;have hi':i<C.gates.length:=by rwa[hag.1]at hi
  have hj':j<C.gates.length:=by rwa[hag.1]at hj
  have hni:i∉junk G D:=λh=>(aA.mp h).2.2 hib;rw[hJD,mem_insert,mem_singleton,not_or]at hni;have hgi:=hag.2 i hi' hni.2;have hjop':(gateAt C j).op=GateOp.and:=by
   by_cases hjr:j=r
   ·rw[hjr];exact hrop
   ·rwa[hag.2 j hj' hjr]at hjop
  refine Z.1.2.1 i hi' j hj' (by rwa[hgi]at hiop) (by_contra λhb'=>?_) hjop' (g9 hrl (λi' hi'' hn=>?_) i j hc)
  ·have:i∈junk G C:=aA.mpr ⟨hi',by rwa[hgi]at hiop,hb'⟩;rw[Z.1.2.2.2.2.1,mem_insert,mem_singleton]at this;exact this.elim hni.1 hni.2
  ·simp only[List.mem_cons,List.not_mem_nil,or_false]at hi'';rcases hi'' with rfl|rfl
   ·rw[show n+q-n=q by omega];exact bU hA hrl b Z.2.1
   ·exact aZ.mpr ⟨hrl,opnd C r (1-b)-n,by omega,by rw[show n+(opnd C r (1-b)-n)=opnd C r (1-b) by omega];exact dA hA hrl (1-b),Or.inl rfl⟩
 ·intro k hk v;rw[hJD,mem_insert,mem_singleton]at hk;rcases hk with rfl|rfl
  ·rw[show gateVal n D k _=wireVal n D (n+k) _ from rfl,(hsp _).2.2.2.2.1 _ (by omega)];exact Z.1.2.2.2.2.2.1 k hq v
  ·exact Bool.eq_false_iff.mpr λh=>by
    have:=((hrv _).mp h).1;rw[Z.1.2.2.2.2.2.1 q hq v]at this;cases this
 ·rw[hqo,←hoi _ (by have:=aH hA hql 0;omega)];exact Z.1.2.2.2.2.2.2 0
 ·rw[hqo,←hoi _ (by have:=aH hA hql 1;omega)];exact Z.1.2.2.2.2.2.2 1
 ·rw[hD0];exact bD.mpr ⟨by rw[hag.1];exact hql,Or.inl rfl⟩
 ·rw[show(1:Fin 2)-0=1 from rfl,hD1];exact λh=>Z.2.2.1 ((hor _ hw1 q).mpr h)
 ·rw[hD0];exact b6 λ_=>by rw[hqopD];simp
end F
def dX (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (q:ℕ) (v:Fin n):Prop:=∃a∈tops G C,∃s:Fin 2,OrReaches n C (opnd C a s) q/\v∈orIn n C (opnd C a (1-s))
def a9 (n:ℕ) (C:Circuit) (q:ℕ) (L:Fin 2 ->Fin n) (e:Sym2 (Fin n)):Prop:=∃β:Fin 2,∃w∈orIn n C (opnd C q (1-β)),e=s(L β,w)
def c9 (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (q r:ℕ) (b:Fin 2) (L:Fin 2 ->Fin n) (col:Fin n ->Bool):Prop:=cM/\(∀u v,G.Adj u v ->col u≠col v)/\cI G C q r b/\(∀β,L β∈orIn n C (opnd C q β)/\∀t∈orIn n C (opnd C q (1-β)),G.Adj (L β) t)/\(2≤(readers n C q).card\/∃x,(∃c∈orIn n C (opnd C r b),x c=true)/\(∃d∈orIn n C (opnd C r (1-b)),x d=true)/\graphFun G ∅ x=false)/\((∀β,aC n G C q (L β))\/b8 G C q r b/\∀β,aC n G C q (L β)\/L β∈orIn n C (opnd C r (1-b)))
def pL (n:ℕ) (C:Circuit) (q:ℕ) (L:Fin 2 ->Fin n) (s:Fin n) (a:ℕ) (b':Fin 2) (v:Fin n):Prop:=(OrReaches n C (opnd C a b') q/\(v=L 0\/v=L 1))\/(v=s/\¬∃b'':Fin 2,∃p,orIn n C (opnd C a (1-b''))={p}/\OrReaches n C (opnd C a b'') q/\(p=L 0\/p=L 1))
def n7 (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (q:ℕ) (L:Fin 2 ->Fin n) (s:Fin n) (K:Finset (Fin n)):Prop:=∀a∈tops G C\centreless G C,∃b':Fin 2,∃p∈K,side (n:=n) C a (1-b')={p}/\((∃b'':Fin 2,∃p',side (n:=n) C a (1-b'')={p'}/\pL n C q L s a b'' p') ->pL n C q L s a b' p)
lemma eP (L:Fin 2 ->Fin n) (β:Fin 2):L β=L 0\/L β=L 1:=by
 fin_cases β<;>simp
lemma eG (K S:Finset (Fin n)) (x:Fin n):(insert x S\K).card≤(if x∈K then 0 else 1)+(S\K).card:=by
 split_ifs with h
 ·rw[insert_sdiff_of_mem _ h];omega
 ·rw[insert_sdiff_of_notMem _ h];exact(card_insert_le _ _).trans (by omega)
lemma gX (K:Finset (Fin n)) (x:Fin n):({x}\K).card≤ if x∈K then 0 else 1:=by
 split_ifs with h
 ·simp[h]
 ·exact(card_le_card sdiff_subset).trans (card_singleton x).le
lemma eY {x y z:Fin n} (h:graphFun G ∅ (λw=>decide (w=x\/w=y\/w=z))=true):G.Adj x y\/G.Adj y z\/G.Adj x z:=by
 obtain⟨u,v,huv,hu,hv⟩:=(dJ _).mp h;simp only[decide_eq_true_eq]at hu hv;rcases hu with rfl|rfl|rfl<;>rcases hv with rfl|rfl|rfl<;>
 first
 |exact(G.irrefl huv).elim
 |exact Or.inl huv
 |exact Or.inl huv.symm
 |exact Or.inr (Or.inl huv)
 |exact Or.inr (Or.inl huv.symm)
 |exact Or.inr (Or.inr huv)
 |exact Or.inr (Or.inr huv.symm)
lemma nV (hA:IsAO2 n C) {a k:ℕ} (ha:a∈tops G C) (hk:k∈junk G C) {β:Fin 2} (h1:OrReaches n C (opnd C a β) k) (h2:OrReaches n C (opnd C a (1-β)) k):False:=by
 obtain⟨hal,hop,hb⟩:=aI.mp ha;exact(aA.mp hk).2.2 λx hx=>hb x ((aN hA hal hop β x).mpr ⟨aO hA x h1 hx,aO hA x h2 hx⟩)
lemma rI {A:Finset (Fin n)} {x y:Fin n} (h:1<(A∩{x,y}).card):x∈A/\y∈A:=by
 by_contra hn;refine absurd h (not_lt.mpr (card_le_one.mpr λa ha c hc=>?_));simp only[mem_inter,mem_insert,mem_singleton]at ha hc;rcases ha with⟨ha,rfl|rfl⟩<;>rcases hc with⟨hc,rfl|rfl⟩;exacts[rfl,absurd ⟨ha,hc⟩ hn,absurd ⟨hc,ha⟩ hn,rfl]
lemma sD (hA:IsAO2 n C) {V:Finset (Sym2 (Fin n))} (hV:V⊆Ustar G C) (w:ℕ) (S:Finset (Fin n)) (hsp:∀W,aB G V W ->(W∩S).card≤1):∃P:Finset ℕ,(∀h∈P,b5 n G C V w h/\1<(orIn n C h∩S).card)/\(orIn n C w∩S).card≤P.card+1:=by
 classical
 have hD:dB (λh=>bX n C h/\¬aB G V (orIn n C h)) (bF n C) (bI n C) id (orIn n C):=λh hh=>aJ hA h hh.1;obtain⟨P,hP,hc⟩:=cU hD S {w} λ_ _ u _ hu=>by
  by_cases hj:bX n C u
  ·exact hsp _ (by by_contra h;exact hu ⟨hj,h⟩)
  ·exact(card_le_card inter_subset_left).trans (bL hj)
 refine⟨P,λh hh=>?_,by simpa[add_comm]using hc⟩;obtain⟨⟨hj,hf⟩,⟨w',hw',hr⟩,h1,h2⟩:=hP h hh;rw[mem_singleton]at hw';subst hw';obtain⟨x1,hx1,hx1'⟩:=not_subset.mp h1;obtain⟨x2,hx2,hx2'⟩:=not_subset.mp h2;have he:=(aJ hA h hj).2.2;have m1:x1∈orIn n C h:=by rw[he];exact mem_union_left _ (mem_inter.mp hx1).1
 have m2:x2∈orIn n C h:=by rw[he];exact mem_union_right _ (mem_inter.mp hx2).1
 refine⟨⟨j3 hA hj ⟨x1,m1⟩ λhu=>hf (bT hV subset_rfl hu),hf,⟨x1,(mem_inter.mp hx1).1⟩,⟨x2,(mem_inter.mp hx2).1⟩,r6 (λ_ h=>h.1) hr⟩,one_lt_card.mpr ⟨x1,mem_inter.mpr ⟨m1,(mem_inter.mp hx1).2⟩,x2,mem_inter.mpr ⟨m2,(mem_inter.mp hx2).2⟩,λe=>hx1' (e▸(mem_inter.mp hx2).1)⟩⟩
lemma kN (hA:IsAO2 n C) {w:ℕ} {x y:Fin n} (hxy:x≠y) (hx:x∈orIn n C w) (hy:y∈orIn n C w) (hsp:∀W,aB G (Ustar G C) W ->¬(x∈W/\y∈W)):∃h,b5 n G C (Ustar G C) w h/\x∈orIn n C h/\y∈orIn n C h:=by
 obtain⟨P,hP,hc⟩:=sD hA subset_rfl w {x,y} λW hW=>by
  by_contra h';exact hsp W hW (rI (not_le.mp h'))
 rw[inter_eq_right.mpr (insert_subset hx (singleton_subset_iff.mpr hy)),card_pair hxy]at hc;obtain⟨h,hh⟩:=card_pos.mp (by omega:0<P.card);exact⟨h,(hP h hh).1,rI (hP h hh).2⟩
section F
variable {q r:ℕ} {b:Fin 2} {L:Fin 2 ->Fin n} {col:Fin n ->Bool}
lemma s9 (Z:cI G C q r b) {u v:Fin n} (he:s(u,v)∈Ustar G C):(gateVal n C q (pairInput u v)=true/\∃w,(w=u\/w=v)/\aC n G C q w)\/(gateVal n C r (pairInput u v)=true/\∃w,(w=u\/w=v)/\aC n G C r w)\/(gateVal n C q (pairInput u v)=true/\gateVal n C r (pairInput u v)=true):=by
 obtain⟨hC,hT,-,-,hJ,-,-⟩:=Z.1;have hA:=hC.1;obtain⟨a,ha,hax,β,k,hk,-,hrk,hkx⟩:=fD hC hT he;obtain⟨hal,hop,-⟩:=aI.mp ha;rcases (a8 hA hT hal hop (1-β) _).mp ((aN hA hal hop β _).mp hax).2 with⟨w,hw,hwx⟩|⟨k',hk',-,hr',hk'x⟩
 ·have hU:aC n G C k w:=⟨a,ha,β,hrk,hw⟩;rw[hJ,mem_insert,mem_singleton]at hk;rcases hk with h|h<;>rw[h]at hU hkx
  ·exact Or.inl ⟨hkx,w,aW hwx,hU⟩
  ·exact Or.inr (Or.inl ⟨hkx,w,aW hwx,hU⟩)
 ·right;right;have hkk:k≠k':=λe=>nV hA ha hk hrk (e▸hr');rw[hJ,mem_insert,mem_singleton]at hk hk';rcases hk with h|h<;>rcases hk' with h'|h'<;>rw[h]at hkx hkk<;>rw[h']at hk'x hkk;exacts[absurd rfl hkk,⟨hkx,hk'x⟩,⟨hk'x,hkx⟩,absurd rfl hkk]
lemma jF (Z:cI G C q r b) {j:ℕ} (hj:j∈junk G C) {u v:Fin n} (huv:G.Adj u v) (hl:wireVal n (aG n C j) C.output (pairInput u v)=false):gateVal n C j (pairInput u v)=true/\s(u,v)∈Ustar G C:=by
 refine⟨qV Z.1.1 huv hl,show s(u,v)∈G.edgeFinset\starEdges G C from mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr huv,λhs=>?_⟩⟩;rw[lA Z.1.1 Z.1.2.1 hj hs]at hl;cases hl
lemma tM (Z:cI G C q r b) {γ:Fin 2} {c d:Fin n} (hc:c∈orIn n C (opnd C r γ)) (hd:d∈orIn n C (opnd C r (1-γ))):gateVal n C r (pairInput c d)=true:=by
 rcases aS b γ with h|h<;>rw[h]at hc hd
 ·exact(dU Z _).mpr ⟨Or.inr ⟨c,hc,by simp[pairInput]⟩,d,hd,by simp[pairInput]⟩
 ·rw[bV]at hd;exact(dU Z _).mpr ⟨Or.inr ⟨d,hd,by simp[pairInput]⟩,c,hc,by simp[pairInput]⟩
lemma fF (Z:cI G C q r b) {γ:Fin 2} {c d:Fin n} (hc:c∈orIn n C (opnd C r γ)) (hu:aC n G C r c) (hd:d∈orIn n C (opnd C r (1-γ))):G.Adj c d:=(aT c d).mp (bH Z.1.1.1 hu _ (tM Z hc hd) (by simp[pairInput]))
lemma nY (Z:cI G C q r b) {u v:Fin n} (he:s(u,v)∈Ustar G C) (hq:gateVal n C q (pairInput u v)=false):∃γ:Fin 2,∃c∈orIn n C (opnd C r γ),∃d∈orIn n C (opnd C r (1-γ)),s(u,v)=s(c,d)/\aC n G C r c:=by
 rcases s9 Z he with⟨h,-⟩|⟨hr,w,hw,hu⟩|⟨h,-⟩
 ·rw[hq]at h;cases h
 ·obtain⟨h1|⟨c,hc,hcx⟩,d,hd,hdx⟩:=(dU Z _).mp hr
  ·rw[hq]at h1;cases h1
  have hcd:c≠d:=λe=>disjoint_left.mp (kZ Z) hc (e▸hd);have e:=fP (aW hcx) (aW hdx) hcd;have hw':w=c\/w=d:=by
   have:w∈s(c,d):=e▸(by rcases hw with h|h<;>rw[h]<;>simp);simpa using this
  rcases hw' with h|h<;>rw[h]at hu
  ·exact⟨b,c,hc,d,hd,e,hu⟩
  ·exact⟨1-b,d,hd,c,by rwa[bV],e.trans Sym2.eq_swap,hu⟩
 ·rw[hq]at h;cases h
lemma tD (Z:cI G C q r b) {c d w:Fin n} (hc:c∈orIn n C (opnd C r b)) (hd:d∈orIn n C (opnd C r (1-b))) (hw:w=c\/w=d) (hu:aC n G C r w):wireVal n (aG n C q) C.output (pairInput c d)=true:=by
 obtain⟨hC,hT,-,hqr,-,-,-⟩:=Z.1;have hA:=hC.1;obtain⟨hq,hr⟩:=b4 Z;obtain⟨hrl,hrop,-⟩:=aA.mp hr;have hqop:=(aA.mp hq).2.1;have hK:=bJ (n:=n) (C:=C) q;obtain⟨a,ha,β,hra,hwa⟩:=hu;have hw':∀β',wireVal n (aG n C q) (opnd C r β') (pairInput c d)=true:=λβ'=>by
  rcases aS b β' with h|h<;>rw[h]
  ·exact b9 hA hK hqop hc (by simp[pairInput])
  ·exact b9 hA hK hqop hd (by simp[pairInput])
 have hrv:wireVal n (aG n C q) (n+r) (pairInput c d)=true:=by
  rw[fV hA hK hrl (by omega) hrop,hw' 0,hw' 1];rfl
 refine fW hC hT hq ha λβ'=>?_;rcases aS β β' with h|h<;>rw[h]
 ·exact fB hA hK hqop _ hra hrv
 ·exact b9 hA hK hqop hwa (by rcases hw with h|h<;>rw[h]<;>simp[pairInput])
lemma mY (Z:cI G C q r b):∃m,aR n G C (n+m)/\m<r/\(orIn n C (n+m)).Nonempty:=by
 obtain⟨m,hM,-,hrm,-,hne⟩:=dR Z.1.1.1 (b4 Z).1 Z.2.1 Z.2.2.2;have:=(aX hrm).1;have:=aH Z.1.1.1 (aA.mp (b4 Z).2).1 b;exact⟨m,hM,by omega,hne⟩
lemma qF (Z:cI G C q r b) {w:Fin n} {a:ℕ} (ha:a∈tops G C) {β:Fin 2} (hr:OrReaches n C (opnd C a β) r) (hw:w∈orIn n C (opnd C a (1-β))) (hne:(orIn n C (opnd C a β)).Nonempty):∃m,aR n G C (n+m)/\r<m/\(orIn n C (n+m)).Nonempty/\∀y∈orIn n C (n+m),G.Adj w y:=by
 have hA:=Z.1.1.1;obtain⟨m,hM,-,hwm,hmr,hne'⟩:=dR hA (b4 Z).2 hr hne;refine⟨m,hM,?_,hne',λy hy=>(aV hA ha β hw (a6 hA hwm hy)).1⟩;have:=(aX hmr).1;rcases (show r≤m by omega).lt_or_eq with h|h
 ·exact h
 ·have:=(a7.mp hM.1).2;rw[←h,(aA.mp (b4 Z).2).2.1]at this;cases this
lemma uK (Z:cI G C q r b) {a:ℕ} {β1 β2:Fin 2} (h1:OrReaches n C (opnd C a β1) q) (e1:orIn n C (opnd C a β1)=∅) (h2:OrReaches n C (opnd C a β2) r) (v2:(orIn n C (opnd C a (1-β2))).Nonempty):∃m,aR n G C (n+m)/\orIn n C (n+m)=∅:=by
 have hA:=Z.1.1.1;rcases aS β1 β2 with h|h<;>rw[h]at h2 v2
 swap
 ·rw[bV,e1]at v2;exact absurd v2 (by simp)
 obtain⟨k,hk⟩:∃k,opnd C a β1=n+k:=⟨opnd C a β1-n,by have:=h1.1;omega⟩;rw[hk]at h1 h2 e1;obtain⟨hkl,h|⟨hop,-⟩⟩:=bD.mp h1
 ·rw[←h]at h2;obtain⟨-,h3|⟨h3,-⟩⟩:=bD.mp h2
  ·have:=Z.1.2.2.2.1;omega
  ·rw[(aA.mp (b4 Z).1).2.1]at h3;cases h3
 have hJ:bX n C (n+k):=a7.mpr ⟨hkl,hop⟩;have h3:=(aJ hA _ hJ).2.2;rw[e1]at h3;refine⟨k,⟨hJ,⟨q,(b4 Z).1,h1⟩,Or.inl (eq_empty_of_forall_notMem λv hv=>?_)⟩,e1⟩;have:=mem_union_left (orIn n C (bI n C (n+k))) hv;rw[←h3]at this;exact notMem_empty v this
lemma tI (Z:cI G C q r b) {V:Finset (Sym2 (Fin n))} (hV:∀e∈V,∃γ:Fin 2,∃c∈orIn n C (opnd C r γ),∃d∈orIn n C (opnd C r (1-γ)),e=s(c,d)/\aC n G C r c):(∃v,∀e∈V,v∈e)\/∃y:Fin 2 ->Fin n,(∀γ,y γ∈orIn n C (opnd C r γ)/\aC n G C r (y γ)/\2≤(orIn n C (opnd C r γ)).card)/\∀e∈V,∃γ:Fin 2,∃t∈orIn n C (opnd C r (1-γ)),e=s(y γ,t):=by
 have h4:=Z.1.2.2.1;have rne:∀γ,(orIn n C (opnd C r γ)).Nonempty:=λγ=>by
  rcases aS b γ with h|h<;>rw[h];exacts[Z.2.2.2,qR Z]
 have uq:∀γ,2≤(orIn n C (opnd C r (1-γ))).card ->∀c∈orIn n C (opnd C r γ),∀c'∈orIn n C (opnd C r γ),aC n G C r c ->aC n G C r c' ->c=c':=λγ h2 c hc c' hc' hu hu'=>bC h4 h2 (λd hd=>fF Z hc hu hd) (λd hd=>fF Z hc' hu' hd);have hy:∀γ:Fin 2,∃y∈orIn n C (opnd C r γ),(∃c∈orIn n C (opnd C r γ),aC n G C r c) ->aC n G C r y:=λγ=>by
  by_cases h:∃c∈orIn n C (opnd C r γ),aC n G C r c
  ·obtain⟨c,hc,hu⟩:=h;exact⟨c,hc,λ_=>hu⟩
  ·obtain⟨y,hy⟩:=rne γ;exact⟨y,hy,λh'=>absurd h' h⟩
 choose y hy hyu using hy;have one:∀γ,(orIn n C (opnd C r γ)).card<2 ->∀c∈orIn n C (opnd C r γ),c=y γ:=λγ h c hc=>card_le_one.mp (by omega) c hc _ (hy γ);have form:∀e∈V,∃γ:Fin 2,∃t∈orIn n C (opnd C r (1-γ)),e=s(y γ,t):=by
  intro e he;obtain⟨γ,c,hc,d,hd,rfl,hu⟩:=hV e he;by_cases h2:2≤(orIn n C (opnd C r (1-γ))).card
  ·exact⟨γ,d,hd,by rw[uq γ h2 c hc _ (hy γ) hu (hyu γ ⟨c,hc,hu⟩)]⟩
  ·refine⟨1-γ,c,by rwa[bV],?_⟩;rw[one _ (by omega) d hd,Sym2.eq_swap]
 by_cases hall:∀γ,aC n G C r (y γ)/\2≤(orIn n C (opnd C r γ)).card
 ·exact Or.inr ⟨y,λγ=>⟨hy γ,hall γ⟩,form⟩
 left;simp only[not_forall,not_and,not_le]at hall;obtain⟨γ,hγ⟩:=hall;by_cases h2:2≤(orIn n C (opnd C r γ)).card
 ·refine⟨y (1-γ),λe he=>?_⟩;obtain⟨γ',c,hc,d,hd,rfl,hu⟩:=hV e he;rcases aS γ γ' with h|h<;>rw[h]at hc hd
  ·have:=hγ (hyu _ ⟨c,hc,hu⟩);omega
  ·rw[uq _ (by rwa[bV]) c hc _ (hy _) hu (hyu _ ⟨c,hc,hu⟩)];exact Sym2.mem_mk_left _ _
 ·refine⟨y γ,λe he=>?_⟩;obtain⟨γ',c,hc,d,hd,rfl,-⟩:=hV e he;rcases aS γ γ' with h|h<;>rw[h]at hc hd
  ·rw[one _ (by omega) c hc];exact Sym2.mem_mk_left _ _
  ·rw[bV]at hd;rw[one _ (by omega) d hd];exact Sym2.mem_mk_right _ _
lemma t4 (Z:cI G C q r b) (hcol:∀u v,G.Adj u v ->col u≠col v) {p z:Fin n} (hpz:G.Adj p z) (hp:aC n G C q p) (hz:aC n G C q z):2≤(readers n C q).card:=by
 obtain⟨hC,hT,-,-,hJ,-,-⟩:=Z.1;have hA:=hC.1;obtain⟨hq,hr⟩:=b4 Z;obtain⟨hrl,hrop,-⟩:=aA.mp hr;obtain⟨hql,hqop,-⟩:=aA.mp hq;have hne:opnd C r b≠n+q:=λhe=>by
  have:=Z.2.2.2;rw[he,b6 (λ_=>by rw[hqop];simp)]at this;simp at this
 obtain⟨m,hm,hop,hin,hrm⟩:=gQ Z.2.1 hne;have hmR:m∈readers n C q:=mem_filter.mpr ⟨mem_range.mpr hm,hin⟩;by_contra hlt;have huq:∀k∈readers n C q,k=m:=λk hk=>card_le_one.mp (by omega) k hk m hmR;have hreach:∀w,aC n G C q w ->∃a∈tops G C,∃β:Fin 2,OrReaches n C (opnd C a β) m/\w∈orIn n C (opnd C a (1-β)):=by
  rintro w ⟨a,ha,β,hra,hw⟩;obtain⟨hal,haop,-⟩:=aI.mp ha;by_cases he:opnd C a β=n+q
  ·have:=huq a (mem_filter.mpr ⟨mem_range.mpr hal,he▸dA hA hal β⟩);rw[this,hop]at haop;cases haop
  ·obtain⟨m',hm',-,hin',hrm'⟩:=gQ hra he;exact⟨a,ha,β,huq m' (mem_filter.mpr ⟨mem_range.mpr hm',hin'⟩)▸hrm',hw⟩
 obtain⟨a1,ha1,β1,hr1,hp1⟩:=hreach p hp;obtain⟨a2,ha2,β2,hr2,hz2⟩:=hreach z hz;have hmE:orIn n C (n+m)=∅:=eq_empty_of_forall_notMem λy hy=>by
  have h1:=(aV hA ha1 β1 hp1 (a6 hA hr1 hy)).1;have h2:=(aV hA ha2 β2 hz2 (a6 hA hr2 hy)).1;exact hcol p z hpz (bB _ _ _ (hcol _ _ h1) (hcol _ _ h2))
 refine d3 hC hm (w:=n+q) (dH hA hm hin) λx=>?_;rw[Bool.eq_iff_iff];constructor
 ·intro h1;rcases (kU hA x _).mp h1 with⟨v,hv,-⟩|⟨k,hk,hrk,hkx⟩
  ·rw[hmE]at hv;simp at hv
  ·have hc:=bU hA hrl b (cG hA hrm hrk);have:=d4 hT hrl hk hrop hc;rw[hJ,mem_insert,mem_singleton]at this;rcases this with h|h<;>rw[h]at hkx hc
   ·exact hkx
   ·exact absurd (aP hc) (lt_irrefl _)
 ·exact λh1=>aO hA x (bD.mpr ⟨hm,Or.inr ⟨hop,n+q,hin,dH hA hm hin,bD.mpr ⟨hql,Or.inl rfl⟩⟩⟩) h1
end F
section W
variable {q r:ℕ} {b:Fin 2} {L:Fin 2 ->Fin n} {col:Fin n ->Bool}
lemma fS (W:c9 G C q r b L col) (γ:Fin 2):∀w∈orIn n C (opnd C q γ),G.Adj (L (1-γ)) w:=by
 have:=(W.2.2.2.1 (1-γ)).2;rwa[bV]at this
lemma fZ (W:c9 G C q r b L col) {γ:Fin 2} {w:Fin n} (hw:w∈orIn n C (opnd C q γ)):col w=col (L γ):=bB _ _ _ (W.2.1 _ _ (fS W γ w hw)).symm (W.2.1 _ _ (fS W γ _ (W.2.2.2.1 γ).1)).symm
lemma j2 (W:c9 G C q r b L col) {β:Fin 2} {t:Fin n} (hT:∀t'∈orIn n C (opnd C q (1-β)),t'=L (1-β)\/t'=t):wireVal n (aG n C q) C.output (pairInput (L β) t)=false:=by
 obtain⟨hR1,hcol,Z,hL,hrd,-⟩:=W;by_contra hacc;rw[Bool.not_eq_false]at hacc;have hpf:=(hL (1-β)).2;rw[bV]at hpf;refine sH hR1 col hcol Z β (hL (1-β)).1 hpf (λu v huv=>?_) hrd;cases hk:wireVal n (aG n C q) C.output (pairInput u v)
 swap
 ·exact Or.inl rfl
 right;obtain⟨hq,-⟩:=jF Z (b4 Z).1 huv hk;obtain⟨γ,w,hw,e⟩:=k7 Z.1 hL huv hq;rcases aS β γ with h|h<;>rw[h]at e hw
 ·rcases hT w hw with h'|h'<;>rw[h']at e
  ·exact⟨by rw[e];exact Sym2.mem_mk_right _ _,L β,(hL β).1,by rw[e];exact Sym2.mem_mk_left _ _⟩
  ·rw[←dT e,hk]at hacc;cases hacc
 ·rw[bV]at hw;exact⟨by rw[e];exact Sym2.mem_mk_left _ _,w,hw,by rw[e];exact Sym2.mem_mk_right _ _⟩
lemma uM (W:c9 G C q r b L col) {β:Fin 2} {a:ℕ} (ha:a∈tops G C) {b':Fin 2} (hr:OrReaches n C (opnd C a b') q) (hv:L β∈orIn n C (opnd C a (1-b'))) (hne:(orIn n C (opnd C a b')).Nonempty):orIn n C (opnd C a (1-b'))={L β}:=by
 have hcol:=W.2.1;have Z:=W.2.2.1;have hL:=W.2.2.2.1;obtain⟨hC,hT,h4,-,-,-,hW⟩:=Z.1;refine eq_singleton_iff_unique_mem.mpr ⟨hv,λw hw=>by_contra λhwv=>?_⟩;obtain⟨y0,hy0⟩:=hne;have h1:=aV hC.1 ha b' hv hy0;have h2:=(aV hC.1 ha b' hw hy0).1;have hF:∀β',∀t∈orIn n C (opnd C q (1-β')),G.Adj (L β') t:=λβ'=>(hL β').2;have hF':=fS W β;have hwW:k4 n G C q w:=j4 hC.1 ha hr hw;have hcw:col w=col (L β):=bB _ _ _ (hcol _ _ h2) (hcol _ _ h1.1);obtain⟨s,hs,hsL⟩:=exists_mem_ne (hW β) (L β);have hcs:col s=col (L β):=fZ W hs;have key:∀t∈orIn n C (opnd C q (1-β)),t≠L (1-β) ->G.Adj w t:=by
  intro t ht htx;have hst:¬G.Adj s t:=λh=>htx (aQ h4 hsL h (hF β t ht) (hF' s hs).symm (hF β _ (hL _).1));have hsw:¬G.Adj s w:=λh=>hcol s w h (hcs.trans hcw.symm);rcases eY (hwW (λz=>decide (z=s\/z=t\/z=w)) ((bP Z.1 β _).mpr ⟨⟨s,hs,by simp⟩,t,ht,by simp⟩) (by simp))with h|h|h;exacts[(hst h).elim,h.symm,(hsw h).elim]
 obtain⟨t0,ht0,ht0x⟩:=exists_mem_ne (hW (1-β)) (L (1-β));have hy:y0=t0:=aQ h4 hwv h2 h1.1 (key t0 ht0 ht0x) (hF β t0 ht0);have:=j2 W (β:=β) (t:=t0) λt ht=>or_iff_not_imp_left.mpr λhtx=>aQ h4 hwv (key t ht htx) (hF β t ht) (key t0 ht0 ht0x) (hF β t0 ht0);rw[←hy,lA hC hT (b4 Z).1 h1.2]at this;cases this
lemma uL (W:c9 G C q r b L col) {s:Fin n} {K:Finset (Fin n)} (hK:n7 G C q L s K) {β:Fin 2} {a:ℕ} (ha:a∈tops G C) {b':Fin 2} (hr:OrReaches n C (opnd C a b') q) (hv:L β∈orIn n C (opnd C a (1-b'))) (hne:(orIn n C (opnd C a b')).Nonempty):L β∈K:=by
 have hsg:=uM W ha hr hv hne;obtain⟨b'',p,hpK,hside,hQ⟩:=hK a (jO ha hne ⟨_,hv⟩);rcases hQ ⟨b',L β,hsg,Or.inl ⟨hr,eP L β⟩⟩with⟨hr',-⟩|⟨-,hno⟩
 ·rcases aS b' b'' with e|e<;>rw[e]at hside hr'
  ·have h':orIn n C (opnd C a (1-b'))={p}:=hside;rw[hsg,singleton_inj]at h';exact h'▸hpK
  ·exact(nV W.2.2.1.1.1.1 ha (b4 W.2.2.1).1 hr hr').elim
 ·exact(hno ⟨b',L β,hsg,hr,eP L β⟩).elim
lemma uU {s:Fin n} {K:Finset (Fin n)} (hK:n7 G C q L s K) {a:ℕ} (ha:a∈tops G C\centreless G C) {b':Fin 2} (hs:orIn n C (opnd C a (1-b'))={s}):s∈K\/L 0∈K\/L 1∈K:=by
 obtain⟨b'',p,hpK,hside,hQ⟩:=hK a ha;by_cases hex:∃b₁:Fin 2,∃p₁,orIn n C (opnd C a (1-b₁))={p₁}/\OrReaches n C (opnd C a b₁) q/\(p₁=L 0\/p₁=L 1)
 ·obtain⟨b₁,p₁,h1,h2,h3⟩:=hex;rcases hQ ⟨b₁,p₁,h1,Or.inl ⟨h2,h3⟩⟩with⟨-,h⟩|⟨-,hno⟩
  ·rcases h with h|h<;>rw[h]at hpK;exacts[Or.inr (Or.inl hpK),Or.inr (Or.inr hpK)]
  ·exact(hno ⟨b₁,p₁,h1,h2,h3⟩).elim
 ·rcases hQ ⟨b',s,hs,Or.inr ⟨rfl,hex⟩⟩with⟨h2,h⟩|⟨h,-⟩
  ·exact(hex ⟨b'',p,hside,h2,h⟩).elim
  ·rw[h]at hpK;exact Or.inl hpK
lemma gT (W:c9 G C q r b L col) {s:Fin n} {K:Finset (Fin n)} (hK:n7 G C q L s K) {β:Fin 2} (hu:aC n G C q (L β)) (hnk:L β∉K):∃a∈centreless G C,∃b':Fin 2,OrReaches n C (opnd C a b') q/\orIn n C (opnd C a b')=∅/\L β∈orIn n C (opnd C a (1-b')):=by
 obtain⟨a,ha,b',hr,hv⟩:=hu;by_cases hne:(orIn n C (opnd C a b')).Nonempty
 ·exact(hnk (uL W hK ha hr hv hne)).elim
 ·rw[not_nonempty_iff_eq_empty]at hne;exact⟨a,c7 ha hne,b',hr,hne,hv⟩
lemma nE (W:c9 G C q r b L col):∃u v,s(u,v)∈Ustar G C/\gateVal n C q (pairInput u v)=false:=by
 obtain⟨hR1,hcol,Z,-,-,-⟩:=W;by_contra hno;refine uH hR1 col hcol Z λu v huv=>?_;cases hk:wireVal n (aG n C r) C.output (pairInput u v)
 swap
 ·exact Or.inl rfl
 right;obtain⟨hr,hU⟩:=jF Z (b4 Z).2 huv hk;have hq:gateVal n C q (pairInput u v)=true:=by
  by_contra h;exact hno ⟨u,v,hU,by simpa using h⟩
 exact⟨hq,((dU Z _).mp hr).2⟩
lemma uW (W:c9 G C q r b L col) {u v:Fin n} (he:s(u,v)∈Ustar G C) (hE:¬a9 n C q L s(u,v)):gateVal n C q (pairInput u v)=false:=by
 by_contra h;rw[Bool.not_eq_false]at h;exact hE (k7 W.2.2.1.1 W.2.2.2.1 (SimpleGraph.mem_edgeFinset.mp (mem_sdiff.mp he).1) h)
open Classical in
lemma lO (W:c9 G C q r b L col) {e:Sym2 (Fin n)} (he:e∈(Ustar G C).filter λe=>¬a9 n C q L e):∃γ:Fin 2,∃c∈orIn n C (opnd C r γ),∃d∈orIn n C (opnd C r (1-γ)),e=s(c,d)/\aC n G C r c:=by
 obtain⟨heU,hE⟩:=mem_filter.mp he
 induction e using Sym2.ind with|_ u v=>exact nY W.2.2.1 heU (uW W heU hE)
open Classical in
lemma g3 (W:c9 G C q r b L col) {K X:Finset (Fin n)} {Pg M H:Finset ℕ} {a:ℕ} (hKc:K.card≤(tops G C\centreless G C).card) (hKs:∀e∈starEdges G C,∃v∈K,v∈e) (hX:∀e∈Ustar G C,∃v∈X,v∈e) (hPg:∀h∈Pg,∃w,b5 n G C ((Ustar G C).filter λe=>¬a9 n C q L e) w h) (hcg:((Ustar G C).filter λe=>¬a9 n C q L e).card+a≤Pg.card+1) (hM:∀h∈M,aR n G C h) (hH:∀h∈H,(∃V w,b5 n G C V w h)/\(∀γ,¬orIn n C h⊆orIn n C (opnd C q γ))/\h∉Pg) (hfin:(X\K).card+1≤2*(centreless G C).card+M.card+H.card+a):False:=by
 obtain⟨-,-,Z,hL,-,-⟩:=W;obtain⟨hC,hT,h4,hqr,hJ,-,-⟩:=Z.1;have hA:=hC.1;have hL01:G.Adj (L 0) (L 1):=(hL 0).2 _ (hL 1).1;obtain⟨Pq,hPq,cq⟩:=kJ hA h4 (w:=λγ=>opnd C q γ) (y:=L) (cJ Z.1 0) (λγ=>(hL γ).1) hL01 (V:=(Ustar G C).filter (a9 n C q L)) (filter_subset _ _) λe he=>(mem_filter.mp he).2;have hdis:Disjoint Pq Pg:=disjoint_left.mpr λh h1 h2=>by
  obtain⟨γ,hc⟩:=hPq h h1;obtain⟨_,hc'⟩:=hPg h h2;refine hc'.2.1 ⟨L (1-γ),λw hw=>?_⟩;have hw':w∈orIn n C (opnd C q γ):=aK (aJ hA) hc.2.2.2.2 hw;have hw'':w∈orIn n C (opnd C q (1-(1-γ))):=by rwa[bV]
  exact⟨(hL (1-γ)).2 w hw'',λhm=>(mem_filter.mp hm).2 ⟨1-γ,w,hw'',rfl⟩⟩
 have hPM:Disjoint (Pq∪Pg) M:=disjoint_left.mpr λh h1 h2=>by
  rcases mem_union.mp h1 with h1|h1
  ·obtain⟨_,hc⟩:=hPq h h1;exact gZ (hM h h2) hc
  ·obtain⟨_,hc⟩:=hPg h h1;exact gZ (hM h h2) hc
 have hPH:Disjoint (Pq∪Pg∪M) H:=disjoint_right.mpr λh hh h1=>by
  obtain⟨⟨V,w,hc⟩,hq',hg'⟩:=hH h hh;rcases mem_union.mp h1 with h1|h1
  ·rcases mem_union.mp h1 with h1|h1
   ·obtain⟨γ,hc'⟩:=hPq h h1;exact hq' γ (aK (aJ hA) hc'.2.2.2.2)
   ·exact hg' h1
  ·exact gZ (hM h h1) hc
 have hsub:Pq∪Pg∪M∪H⊆(orN G C\lam G C).image (n+·):=λh hh=>by
  rcases mem_union.mp hh with hh|hh
  ·rcases mem_union.mp hh with hh|hh
   ·rcases mem_union.mp hh with hh|hh
    ·obtain⟨_,hc⟩:=hPq h hh;exact hc.1
    ·obtain⟨_,hc⟩:=hPg h hh;exact hc.1
   ·exact g7 hA (hM h hh)
  ·obtain⟨⟨_,_,hc⟩,-⟩:=hH h hh;exact hc.1
 have hρ:=card_le_card hsub;rw[card_union_of_disjoint hPH,card_union_of_disjoint hPM,card_union_of_disjoint hdis,card_image_of_injective _ (add_right_injective n)]at hρ;have hu:=card_filter_add_card_filter_not (s:=Ustar G C) (a9 n C q L);have hm:=e4 h4 hC hT (by rw[hJ,card_pair hqr.ne]) K X hKs hX;omega
lemma r5 (W:c9 G C q r b L col) {u v:Fin n} (h:a9 n C q L s(u,v)):gateVal n C q (pairInput u v)=true:=by
 obtain⟨β,w,hw,e⟩:=h;rw[dT e];exact(bP W.2.2.1.1 β _).mpr ⟨⟨L β,(W.2.2.2.1 β).1,by simp[pairInput]⟩,w,hw,by simp[pairInput]⟩
lemma sA (Z:cI G C q r b) (hg:b8 G C q r b):∃x,(∃c∈orIn n C (opnd C r b),x c=true)/\(∃d∈orIn n C (opnd C r (1-b)),x d=true)/\graphFun G ∅ x=false:=by
 have hr:=(aA.mp (b4 Z).2).2.2;simp only[BelowF,not_forall,Bool.not_eq_true]at hr;obtain⟨x,hx,hF⟩:=hr;obtain⟨h1|h1,h2⟩:=(dU Z x).mp hx
 ·rw[hg x h1 h2]at hF;cases hF
 ·exact⟨x,h1,h2,hF⟩
lemma lT (Z:cI G C q r b) (γ:Fin 2):Disjoint (orIn n C (opnd C r γ)) (orIn n C (opnd C r (1-γ))):=by
 rcases aS b γ with h|h<;>rw[h]
 ·exact kZ Z
 ·rw[bV];exact(kZ Z).symm
lemma eV {P:ℕ ->Prop} {a c:ℕ} (ha:P a) (hc:P c):∀h∈({a,c}:Finset ℕ),P h:=by
 intro h hh;simp only[mem_insert,mem_singleton]at hh;rcases hh with h'|h'<;>rw[h']<;>assumption
lemma q1 {P:ℕ ->Prop} {a c d:ℕ} (ha:P a) (hc:P c) (hd:P d):∀h∈({a,c,d}:Finset ℕ),P h:=by
 intro h hh;simp only[mem_insert,mem_singleton]at hh;rcases hh with h'|h'|h'<;>rw[h']<;>assumption
lemma q2 (h4:NoFourCycle G) (hcol:∀u v,G.Adj u v ->col u≠col v) {V:Finset (Sym2 (Fin n))} (hV:V⊆G.edgeFinset) {W':Finset (Fin n)} (hW:aB G V W') {s w:Fin n} (hw:col w=col s):(W'∩(aE V s∪{w})).card≤1:=by
 obtain⟨c,hc⟩:=aU col hcol hW;have hs1:=aF h4 hV hW s;have hcl:∀x∈aE V s,col x≠col s:=λx hx=>(hcol _ _ (SimpleGraph.mem_edgeFinset.mp (hV (aD.mp hx)))).symm;refine card_le_one.mpr λx hx x' hx'=>?_;simp only[mem_inter,mem_union,mem_singleton]at hx hx';rcases hx with⟨hxW,hx|hx⟩<;>rcases hx' with⟨hx'W,hx'|hx'⟩
 ·exact card_le_one.mp hs1 x (mem_inter.mpr ⟨hxW,hx⟩) x' (mem_inter.mpr ⟨hx'W,hx'⟩)
 ·rw[hx']at hx'W;exact absurd ((hc _ hxW).trans ((hc _ hx'W).symm.trans hw)) (hcl x hx)
 ·rw[hx]at hxW;exact absurd ((hc _ hx'W).trans ((hc _ hxW).symm.trans hw)) (hcl x' hx')
 ·rw[hx,hx']
open Classical in
lemma kC:(Ustar G C).filter (λe=>¬a9 n C q L e)⊆G.edgeFinset:=(filter_subset _ _).trans sdiff_subset
open Classical in
lemma gR (W:c9 G C q r b L col) {s ℓ:Fin n} {σ:Fin 2} (hs:s∈orIn n C (opnd C r σ)) (he:s(s,ℓ)∈(Ustar G C).filter λe=>¬a9 n C q L e):ℓ∈orIn n C (opnd C r (1-σ)):=by
 have Z:=W.2.2.1;obtain⟨γ,c,hc,d,hd,e,-⟩:=lO W he;rcases Sym2.eq_iff.mp e with⟨h1,h2⟩|⟨h1,h2⟩
 ·rw[←h1]at hc;rw[←h2]at hd;rcases aS σ γ with h|h<;>rw[h]at hc hd
  ·exact hd
  ·exact absurd hc (disjoint_left.mp (lT Z σ) hs)
 ·rw[←h1]at hd;rw[←h2]at hc;rcases aS σ γ with h|h<;>rw[h]at hc hd
  ·exact absurd hd (disjoint_left.mp (lT Z σ) hs)
  ·exact hc
open Classical in
lemma lM (W:c9 G C q r b L col) {s:Fin n} {σ:Fin 2} (hs:s∈orIn n C (opnd C r σ)) (hcv:∀e∈(Ustar G C).filter (λe=>¬a9 n C q L e),s∈e) {Anc:Finset (Fin n)} (hAnc:Anc⊆orIn n C (opnd C r (1-σ))) (hdj:Disjoint Anc (aE ((Ustar G C).filter λe=>¬a9 n C q L e) s)) (hsp:∀W',aB G ((Ustar G C).filter λe=>¬a9 n C q L e) W' ->(W'∩(aE ((Ustar G C).filter λe=>¬a9 n C q L e) s∪Anc)).card≤1):∃Pg:Finset ℕ,(∀h∈Pg,b5 n G C ((Ustar G C).filter λe=>¬a9 n C q L e) (opnd C r (1-σ)) h/\orIn n C h⊆orIn n C (opnd C r (1-σ)))/\((Ustar G C).filter λe=>¬a9 n C q L e).card+Anc.card≤Pg.card+1:=by
 have hA:=W.2.2.1.1.1.1;obtain⟨P,hP,hc⟩:=sD hA (filter_subset _ _) (opnd C r (1-σ)) _ hsp;have hnb:aE ((Ustar G C).filter λe=>¬a9 n C q L e) s⊆orIn n C (opnd C r (1-σ)):=λx hx=>gR W hs (aD.mp hx);rw[inter_eq_right.mpr (union_subset hnb hAnc),card_union_of_disjoint hdj.symm]at hc;refine⟨P,λh hh=>⟨(hP h hh).1,aK (aJ hA) (hP h hh).1.2.2.2.2⟩,?_⟩
 have:=(card_le_card (s:=(Ustar G C).filter λe=>¬a9 n C q L e) (t:=(aE ((Ustar G C).filter λe=>¬a9 n C q L e) s).image (s(s,·))) λe he=>by
   obtain⟨x,rfl⟩:=Sym2.mem_iff_exists.mp (hcv e he)
   exact mem_image_of_mem _ (aD.mpr he)).trans card_image_le
 omega
lemma nX (W:c9 G C q r b L col) (hg:b8 G C q r b) {β:Fin 2} (hmono:∀d∈orIn n C (opnd C r (1-b)),col d=col (L β)) (hD2:2≤(orIn n C (opnd C r (1-b))).card):∃t∈orIn n C (opnd C q (1-β)),t≠L (1-β)/\(∀t'∈orIn n C (opnd C q (1-β)),t'=L (1-β)\/t'=t)/\∀d∈orIn n C (opnd C r (1-b)),G.Adj t d:=by
 have hcol:=W.2.1;have Z:=W.2.2.1;have hL:=W.2.2.2.1;obtain⟨-,-,h4,-,-,-,hW⟩:=Z.1;obtain⟨a,ha,hap⟩:=exists_mem_ne (hW β) (L β);have hca:=fZ W ha;have key:∀t∈orIn n C (opnd C q (1-β)),t≠L (1-β) ->∀d∈orIn n C (opnd C r (1-b)),G.Adj t d:=by
  intro t ht htx d hd;have hat:¬G.Adj a t:=λh=>htx (aQ h4 hap h ((hL β).2 t ht) (fS W β a ha).symm ((hL β).2 _ (hL _).1));have had:¬G.Adj a d:=λh=>hcol a d h (hca.trans (hmono d hd).symm);rcases eY (hg (λz=>decide (z=a\/z=t\/z=d)) ((bP Z.1 β _).mpr ⟨⟨a,ha,by simp⟩,t,ht,by simp⟩) ⟨d,hd,by simp⟩)with h|h|h;exacts[(hat h).elim,h,(had h).elim]
 obtain⟨t0,ht0,ht0x⟩:=exists_mem_ne (hW (1-β)) (L (1-β));obtain⟨d1,hd1,d2,hd2,hd12⟩:=one_lt_card.mp (by omega:1<(orIn n C (opnd C r (1-b))).card);refine⟨t0,ht0,ht0x,λt' ht'=>or_iff_not_imp_left.mpr λh=>?_,key t0 ht0 ht0x⟩;exact aQ h4 hd12 (key t' ht' h d1 hd1).symm (key t' ht' h d2 hd2).symm (key t0 ht0 ht0x d1 hd1).symm (key t0 ht0 ht0x d2 hd2).symm
lemma nJ (W:c9 G C q r b L col) (hc0:(centreless G C).card=0):∃m,aR n G C (n+m)/\r<m:=by
 obtain⟨u,v,he,hq⟩:=nE W;obtain⟨-,c,-,-,-,-,a,ha,β,hr,hw⟩:=nY W.2.2.1 he hq
 obtain⟨m,hM,hm,-⟩:=qF W.2.2.1 ha hr hw (nonempty_iff_ne_empty.mpr λh=>by
  have:=card_pos.mpr ⟨a,c7 ha h⟩;omega)
 exact⟨m,hM,hm⟩
lemma sX (W:c9 G C q r b L col) (hc1:(centreless G C).card≤1) {a1:ℕ} (ha1:a1∈centreless G C) {b1:Fin 2} (hr1:OrReaches n C (opnd C a1 b1) q) (he1:orIn n C (opnd C a1 b1)=∅) {w:Fin n} (hw:aC n G C r w):∃m,aR n G C (n+m)/\(r<m\/orIn n C (n+m)=∅):=by
 obtain⟨a,ha,β,hr,hwa⟩:=hw;by_cases hne:(orIn n C (opnd C a β)).Nonempty
 ·obtain⟨m,hM,hm,-⟩:=qF W.2.2.1 ha hr hwa hne;exact⟨m,hM,Or.inl hm⟩
 ·rw[not_nonempty_iff_eq_empty]at hne;rw[card_le_one.mp hc1 a (c7 ha hne) a1 ha1]at hr hwa;obtain⟨m,hM,hme⟩:=uK W.2.2.1 hr1 he1 hr ⟨w,hwa⟩;exact⟨m,hM,Or.inr hme⟩
open Classical in
lemma u4 (W:c9 G C q r b L col) {y:Fin 2 ->Fin n} (hy:∀γ,y γ∈orIn n C (opnd C r γ)/\aC n G C r (y γ)/\2≤(orIn n C (opnd C r γ)).card) (form:∀e∈(Ustar G C).filter (λe=>¬a9 n C q L e),∃γ:Fin 2,∃t∈orIn n C (opnd C r (1-γ)),e=s(y γ,t)):False:=by
 have hcol:=W.2.1;have Z:=W.2.2.1;have hL:=W.2.2.2.1;obtain⟨hC,-,h4,-,-,-,-⟩:=Z.1;have hA:=hC.1;have hyy:G.Adj (y 0) (y 1):=fF Z (hy 0).1 (hy 0).2.1 (hy 1).1;have hL01:G.Adj (L 0) (L 1):=(hL 0).2 _ (hL 1).1;have hLu:∀β,aC n G C q (L β):=by
  rcases W.2.2.2.2.2 with h|⟨hg,hD⟩
  ·exact h
  intro β;refine(hD β).resolve_right λhp=>?_;have hyD:∀d∈orIn n C (opnd C r (1-b)),G.Adj (y b) d:=λd hd=>fF Z (hy b).1 (hy b).2.1 hd;obtain⟨t,-,-,hT',htD⟩:=nX W hg (λd hd=>bB _ _ _ (hcol _ _ (hyD d hd)).symm (hcol _ _ (hyD _ hp)).symm) (hy (1-b)).2.2;have h1:=j2 W hT';rw[←bC h4 (hy (1-b)).2.2 hyD htD,dT Sym2.eq_swap,tD Z (hy b).1 hp (Or.inl rfl) (hy b).2.1]at h1;cases h1
 obtain⟨K,hKc,hKs,hKa⟩:=qZ hA h4 (pL n C q L (L 0));have hX:∀e∈Ustar G C,∃v∈({L 0,L 1,y 0,y 1}:Finset (Fin n)),v∈e:=by
  intro e he;by_cases hE:a9 n C q L e
  ·obtain⟨β,w,-,rfl⟩:=hE;exact⟨L β,by rcases eP L β with h|h<;>rw[h]<;>simp,Sym2.mem_mk_left _ _⟩
  ·obtain⟨γ,t,-,rfl⟩:=form e (mem_filter.mpr ⟨he,hE⟩);exact⟨y γ,by rcases eP y γ with h|h<;>rw[h]<;>simp,Sym2.mem_mk_left _ _⟩
 obtain⟨Pg,hPg,cg⟩:=kJ hA h4 (w:=λγ=>opnd C r γ) (y:=y) (lT Z 0) (λγ=>(hy γ).1) hyy (V:=(Ustar G C).filter λe=>¬a9 n C q L e) (filter_subset _ _) form;obtain⟨m0,hM0,hm0r,hm0n⟩:=mY Z;have hN:=(eG K _ (L 0)).trans (Nat.add_le_add_left ((eG K _ (L 1)).trans (Nat.add_le_add_left ((eG K _ (y 0)).trans (Nat.add_le_add_left (gX K (y 1)) _)) _)) _);have F0:∀M H:Finset ℕ,(∀h∈M,aR n G C h) ->(∀h∈H,(∃V w,b5 n G C V w h)/\(∀γ,¬orIn n C h⊆orIn n C (opnd C q γ))/\h∉Pg) ->(({L 0,L 1,y 0,y 1}:Finset (Fin n))\K).card+1≤2*(centreless G C).card+M.card+H.card ->False:=λM H hM hH hc=>g3 W (a:=0) hKc hKs hX (λh hh=>let ⟨_,hc⟩:=hPg h hh;⟨_,hc⟩) (by omega) hM hH
   (by omega)
 have hM0':∀h∈({n+m0}:Finset ℕ),aR n G C h:=λh hh=>by
  rw[mem_singleton.mp hh];exact hM0
 by_cases hc2:2≤(centreless G C).card
 ·refine F0 {n+m0} ∅ hM0' (by simp) ?_;rw[card_singleton,card_empty];split_ifs at hN<;>omega
 by_cases hc0:(centreless G C).card=0
 ·have hLK:∀β,L β∈K:=λβ=>by_contra λh=>by
   obtain⟨a,ha,-⟩:=gT W hKa (hLu β) h;have:=card_pos.mpr ⟨a,ha⟩;omega
  have hmd:∀γ,∃m,aR n G C (n+m)/\r<m/\(orIn n C (n+m)).Nonempty/\∀y'∈orIn n C (n+m),G.Adj (y γ) y':=λγ=>by
   obtain⟨a,ha,β',hr',hw⟩:=(hy γ).2.1;refine qF Z ha hr' hw (nonempty_iff_ne_empty.mpr λhe=>?_);have:=card_pos.mpr ⟨a,c7 ha he⟩;omega
  obtain⟨m1,hM1,hr1,⟨y1,hy1⟩,ha1⟩:=hmd 0;obtain⟨m2,hM2,hr2,-,ha2⟩:=hmd 1;have h12:m1≠m2:=λe=>hcol _ _ hyy (bB _ _ _ (hcol _ _ (ha1 y1 hy1)) (hcol _ _ (ha2 y1 (e▸hy1))));refine F0 {n+m0,n+m1,n+m2} ∅ (q1 hM0 hM1 hM2) (by simp) ?_;rw[ite_eq_left (hLK 0),ite_eq_left (hLK 1)]at hN;rw[card_insert_of_notMem (by simp;omega),card_pair (by omega),card_empty];split_ifs at hN<;>omega
 have hc1:(centreless G C).card=1:=by omega
 by_cases hLK:L 0∈K/\L 1∈K
 ·refine F0 {n+m0} ∅ hM0' (by simp) ?_;rw[ite_eq_left hLK.1,ite_eq_left hLK.2]at hN;rw[card_singleton,card_empty];split_ifs at hN<;>omega
 obtain⟨β0,hβ0⟩:∃β,L β∉K:=by
  by_contra h;simp only[not_exists,not_not]at h;exact hLK ⟨h 0,h 1⟩
 obtain⟨a1,ha1,b1,hr1,he1,-⟩:=gT W hKa (hLu β0) hβ0;have hmx:∀γ,∃m,aR n G C (n+m)/\m≠m0:=λγ=>by
  obtain⟨m,hM,h⟩:=sX W (by omega) ha1 hr1 he1 (hy γ).2.1;refine⟨m,hM,λe=>?_⟩;rw[e]at h;rcases h with h|h
  ·omega
  ·rw[h]at hm0n;simp at hm0n
 obtain⟨mA,hMA,hA0⟩:=hmx 0;obtain⟨mB,hMB,hB0⟩:=hmx 1;have c2:({n+m0,n+mA}:Finset ℕ).card=2:=card_pair (by omega);by_cases hall:L 0∉K/\L 1∉K/\y 0∉K/\y 1∉K
 swap
 ·refine F0 {n+m0,n+mA} ∅ (eV hM0 hMA) (by simp) ?_;rw[c2,card_empty];simp only[not_and_or,not_not]at hall;rcases hall with h|h|h|h<;>rw[ite_eq_left h]at hN<;>split_ifs at hN<;>omega
 by_cases hAB:mA=mB
 swap
 ·refine F0 {n+m0,n+mA,n+mB} ∅ (q1 hM0 hMA hMB) (by simp) ?_;rw[card_insert_of_notMem (by simp;omega),card_pair (by omega),card_empty];split_ifs at hN<;>omega
 obtain⟨a2,ha2,b2,hr2,he2,hv2⟩:=gT W hKa (hLu 0) hall.1;obtain⟨a3,ha3,b3,hr3,he3,hv3⟩:=gT W hKa (hLu 1) hall.2.1;rw[card_le_one.mp (by omega) a2 ha2 a3 ha3]at hr2 he2 hv2;have hb:b3=b2:=by
  rcases aS b2 b3 with h|h
  ·exact h
  ·rw[h,bV,he2]at hv3;simp at hv3
 rw[hb]at hv3;obtain⟨h,hCh,h0,h1⟩:=kN hA (G.ne_of_adj hL01) hv2 hv3 λW' hW' ⟨i0,i1⟩=>by
  obtain⟨c,hc⟩:=aU col hcol hW';exact hcol _ _ hL01 ((hc _ i0).trans (hc _ i1).symm)
 have hLh:∀β,L β∈orIn n C h:=λβ=>by
  rcases eP L β with e|e<;>rw[e];exacts[h0,h1]
 refine F0 {n+m0,n+mA} {h} (eV hM0 hMA) (λh' hh=>?_) ?_
 ·rw[mem_singleton.mp hh];refine⟨⟨_,_,hCh⟩,λγ hs=>disjoint_left.mp (cJ Z.1 γ) (hs (hLh (1-γ))) (hL (1-γ)).1,λhp=>?_⟩;obtain⟨γ',hc'⟩:=hPg h hp;have hsub:=aK (aJ hA) hc'.2.2.2.2;have hy':∀β,G.Adj (y (1-γ')) (L β):=λβ=>fF Z (hy (1-γ')).1 (hy _).2.1 (by rw[bV];exact hsub (hLh β));exact hcol _ _ hL01 (bB _ _ _ (hcol _ _ (hy' 0)).symm (hcol _ _ (hy' 1)).symm)
 ·rw[c2,card_singleton];split_ifs at hN<;>omega
open Classical in
lemma tY (W:c9 G C q r b L col) {β0:Fin 2} (hcv:∀e∈(Ustar G C).filter (λe=>¬a9 n C q L e),L β0∈e):False:=by
 have hcol:=W.2.1;have Z:=W.2.2.1;have hL:=W.2.2.2.1;obtain⟨hC,-,h4,-,-,-,-⟩:=Z.1;have hA:=hC.1;have hL01:G.Adj (L 0) (L 1):=(hL 0).2 _ (hL 1).1;obtain⟨u0,v0,he0,hq0⟩:=nE W;obtain⟨γ,c,hc,d,hd,e,-⟩:=nY Z he0 hq0;obtain⟨σ,hσ⟩:∃σ,L β0∈orIn n C (opnd C r σ):=by
  have h:=hcv _ (mem_filter.mpr ⟨he0,λhE=>by rw[r5 W hE]at hq0;cases hq0⟩);rw[e]at h;rcases Sym2.mem_iff.mp h with h|h<;>rw[h];exacts[⟨γ,hc⟩,⟨1-γ,hd⟩]
 obtain⟨K,hKc,hKs,hKa⟩:=qZ hA h4 (pL n C q L (L 0));have hX:∀e∈Ustar G C,∃v∈({L 0,L 1}:Finset (Fin n)),v∈e:=by
  intro e he;by_cases hE:a9 n C q L e
  ·obtain⟨β,w,-,rfl⟩:=hE;exact⟨L β,by rcases eP L β with h|h<;>rw[h]<;>simp,Sym2.mem_mk_left _ _⟩
  ·exact⟨L β0,by rcases eP L β0 with h|h<;>rw[h]<;>simp,hcv e (mem_filter.mpr ⟨he,hE⟩)⟩
 obtain⟨Pg,hPg,cg⟩:=lM W hσ hcv (Anc:=∅) (empty_subset _) (disjoint_empty_left _) λW' hW'=>by
   simpa using aF h4 kC hW' (L β0)
 obtain⟨m0,hM0,hm0r,-⟩:=mY Z;have hN:=(eG K _ (L 0)).trans (Nat.add_le_add_left (gX K (L 1)) _);have F0:∀M H:Finset ℕ,(∀h∈M,aR n G C h) ->(∀h∈H,(∃V w,b5 n G C V w h)/\(∀γ,¬orIn n C h⊆orIn n C (opnd C q γ))/\h∉Pg) ->(({L 0,L 1}:Finset (Fin n))\K).card+1≤2*(centreless G C).card+M.card+H.card ->False:=λM H hM hH hc=>g3 W (a:=0) hKc hKs hX (λh hh=>⟨_,(hPg h hh).1⟩) (by simpa using cg) hM hH (by omega);by_cases hc0:(centreless G C).card=0
 swap
 ·refine F0 {n+m0} ∅ (λh hh=>by rw[mem_singleton.mp hh];exact hM0) (by simp) ?_;rw[card_singleton,card_empty];split_ifs at hN<;>omega
 obtain⟨m1,hM1,hm1⟩:=nJ W hc0;have c2:({n+m0,n+m1}:Finset ℕ).card=2:=card_pair (by omega);by_cases hLK:L 0∈K\/L 1∈K
 ·refine F0 {n+m0,n+m1} ∅ (eV hM0 hM1) (by simp) ?_;rw[c2,card_empty];rcases hLK with h|h<;>rw[ite_eq_left h]at hN<;>split_ifs at hN<;>omega
 simp only[not_or]at hLK;have hDL:∀β,L β∈orIn n C (opnd C r (1-b)):=λβ=>by
  have hnu:¬aC n G C q (L β):=λhu=>by
   obtain⟨a,ha,-⟩:=gT W hKa hu (by
    rcases eP L β with h|h<;>rw[h]
    exacts[hLK.1,hLK.2])
   have:=card_pos.mpr ⟨a,ha⟩;omega
  rcases W.2.2.2.2.2 with h|⟨-,hD⟩
  ·exact(hnu (h β)).elim
  ·exact(hD β).resolve_left hnu
 obtain⟨h,hCh,h0,h1⟩:=kN hA (G.ne_of_adj hL01) (hDL 0) (hDL 1) λW' hW' ⟨i0,i1⟩=>by
  obtain⟨c,hc⟩:=aU col hcol hW';exact hcol _ _ hL01 ((hc _ i0).trans (hc _ i1).symm)
 have hLh:∀β,L β∈orIn n C h:=λβ=>by
  rcases eP L β with e|e<;>rw[e];exacts[h0,h1]
 refine F0 {n+m0,n+m1} {h} (eV hM0 hM1) (λh' hh=>?_) ?_
 ·rw[mem_singleton.mp hh];exact⟨⟨_,_,hCh⟩,λγ hs=>disjoint_left.mp (cJ Z.1 γ) (hs (hLh (1-γ))) (hL (1-γ)).1,λhp=>disjoint_left.mp (lT Z σ) hσ ((hPg h hp).2 (hLh β0))⟩
 ·rw[c2,card_singleton];rw[ite_eq_right hLK.1,ite_eq_right hLK.2]at hN;omega
open Classical in
lemma u6 (W:c9 G C q r b L col) (hg:b8 G C q r b) {s:Fin n} {σ:Fin 2} (hs:s∈orIn n C (opnd C r σ)) (hcv:∀e∈(Ustar G C).filter (λe=>¬a9 n C q L e),s∈e) (hnc:∀β,∃e∈(Ustar G C).filter (λe=>¬a9 n C q L e),L β∉e) (hnorm:aC n G C r s\/(orIn n C (opnd C r σ)={s}/\2≤(aE ((Ustar G C).filter λe=>¬a9 n C q L e) s).card)) {β:Fin 2} (hp:L β∈orIn n C (opnd C r (1-b))):(σ=1-b/\∃h,b5 n G C (Ustar G C) (opnd C r (1-b)) h/\∀γ,¬orIn n C h⊆orIn n C (opnd C q γ))\/(σ=b/\∃w∈orIn n C (opnd C r (1-b)),col w=col s):=by
 have hcol:=W.2.1;have Z:=W.2.2.1;have hL:=W.2.2.2.1;obtain⟨hC,-,h4,-,-,-,-⟩:=Z.1;have hA:=hC.1;have hsL:∀β',s≠L β':=λβ' e=>by
  obtain⟨e',he',hne⟩:=hnc β';exact hne (e▸hcv e' he')
 rcases aS b σ with hσ|hσ<;>rw[hσ]at hs hnorm
 ·rcases hnorm with hu|⟨hsing,h2⟩
  ·exfalso;have hsD:∀d∈orIn n C (opnd C r (1-b)),G.Adj s d:=λd hd=>fF Z hs hu hd;by_cases hD2:2≤(orIn n C (opnd C r (1-b))).card
   ·obtain⟨t,-,-,hT',htD⟩:=nX W hg (λd hd=>bB _ _ _ (hcol _ _ (hsD d hd)).symm (hcol _ _ (hsD _ hp)).symm) hD2;have h1:=j2 W hT';rw[←bC h4 hD2 hsD htD,dT Sym2.eq_swap,tD Z hs hp (Or.inl rfl) hu]at h1;cases h1
   ·obtain⟨e',he',hne⟩:=hnc β;obtain⟨γ',c',hc',d',hd',rfl,-⟩:=lO W he';rcases aS b γ' with h|h<;>rw[h]at hc' hd'
    ·exact hne (by rw[card_le_one.mp (by omega) d' hd' _ hp];exact Sym2.mem_mk_right _ _)
    ·exact hne (by rw[card_le_one.mp (by omega) c' hc' _ hp];exact Sym2.mem_mk_left _ _)
  ·by_cases hw:∃w∈orIn n C (opnd C r (1-b)),col w=col s
   ·exact Or.inr ⟨hσ,hw⟩
   exfalso;simp only[not_exists,not_and]at hw;obtain⟨ℓ1,hℓ1,ℓ2,hℓ2,hℓ12⟩:=one_lt_card.mp (by omega:1<(aE ((Ustar G C).filter λe=>¬a9 n C q L e) s).card);have hE1:=aD.mp hℓ1;have hE2:=aD.mp hℓ2;have hd1:=gR W hs hE1;have hd2:=gR W hs hE2;have hadj:∀ℓ,s(s,ℓ)∈(Ustar G C).filter (λe=>¬a9 n C q L e) ->G.Adj s ℓ:=λℓ h=>SimpleGraph.mem_edgeFinset.mp (mem_sdiff.mp (mem_filter.mp h).1).1;obtain⟨t,-,-,-,htD⟩:=nX W hg (λd hd=>bB _ _ _ (hw d hd) (hw _ hp)) (one_lt_card.mpr ⟨ℓ1,hd1,ℓ2,hd2,hℓ12⟩);have hst:s=t:=aQ h4 hℓ12 (hadj _ hE1).symm (hadj _ hE2).symm (htD _ hd1).symm (htD _ hd2).symm;obtain⟨x,⟨c,hc,hxc⟩,⟨d,hd,hxd⟩,hF⟩:=sA Z hg;rw[hsing,mem_singleton]at hc;rw[hc]at hxc;rw[(dJ x).mpr ⟨s,d,by rw[hst];exact htD d hd,hxc,hxd⟩]at hF;cases hF
 ·rcases hnorm with hu|⟨hsing,-⟩
  swap
  ·rw[hsing,mem_singleton]at hp;exact(hsL β hp.symm).elim
  left;refine⟨hσ,?_⟩;by_cases hmix:∃d∈orIn n C (opnd C r (1-b)),col d≠col (L β)
  ·obtain⟨d,hd,hcd⟩:=hmix;obtain⟨h,hCh,h0,h1⟩:=kN hA (λe=>hcd (by rw[e])) hp hd λW' hW' ⟨i0,i1⟩=>by
    obtain⟨c,hc⟩:=aU col hcol hW';exact hcd ((hc _ i1).trans (hc _ i0).symm)
   exact⟨h,hCh,λγ hsub=>hcd ((fZ W (hsub h1)).trans (fZ W (hsub h0)).symm)⟩
  ·simp only[not_exists,not_and,not_not]at hmix;have hD2:2≤(orIn n C (opnd C r (1-b))).card:=one_lt_card.mpr ⟨_,hs,_,hp,hsL β⟩;obtain⟨t,ht,htz,hT',htD⟩:=nX W hg hmix hD2;have hpt:=(hL β).2 t ht;obtain⟨-,hU⟩:=jF Z (b4 Z).1 hpt (j2 W hT');obtain⟨h,hCh,h0,h1⟩:=kN hA (hsL β).symm hp hs λW' hW' ⟨i0,i1⟩=>by
    obtain⟨z,hz⟩:=hW';have:=aQ h4 (hsL β).symm (hz _ i0).1.symm (hz _ i1).1.symm hpt (htD s hs).symm;rw[this]at hz;exact(hz _ i0).2 (by rw[Sym2.eq_swap];exact hU)
   refine⟨h,hCh,λγ hsub=>?_⟩;rcases aS β γ with e|e<;>rw[e]at hsub
   ·exact htz (aQ h4 (hsL β) (fS W β s (hsub h1)).symm ((hL β).2 _ (hL (1-β)).1) (htD s hs).symm hpt).symm
   ·exact disjoint_left.mp (cJ Z.1 β) (hL β).1 (hsub h0)
open Classical in
lemma vC (W:c9 G C q r b L col) (hg:b8 G C q r b) {s:Fin n} {σ:Fin 2} (hs:s∈orIn n C (opnd C r σ)) (hcv:∀e∈(Ustar G C).filter (λe=>¬a9 n C q L e),s∈e) (hnc:∀β,∃e∈(Ustar G C).filter (λe=>¬a9 n C q L e),L β∉e) (hnorm:aC n G C r s\/(orIn n C (opnd C r σ)={s}/\2≤(aE ((Ustar G C).filter λe=>¬a9 n C q L e) s).card)) (hc0:(centreless G C).card=0) (hDL:∀β,L β∈orIn n C (opnd C r (1-b))) {K:Finset (Fin n)} (hKc:K.card≤(tops G C\centreless G C).card) (hKs:∀e∈starEdges G C,∃v∈K,v∈e) (hKa:n7 G C q L s K) (hnK:L 0∉K/\L 1∉K/\s∉K):False:=by
 have hcol:=W.2.1;have Z:=W.2.2.1;have hL:=W.2.2.2.1;obtain⟨hC,-,h4,-,-,-,hW⟩:=Z.1;have hA:=hC.1;have hfull:=fS W;have hsL:∀β',s≠L β':=λβ' e=>by
  obtain⟨e',he',hne⟩:=hnc β';exact hne (e▸hcv e' he')
 have hL01:G.Adj (L 0) (L 1):=(hL 0).2 _ (hL 1).1;obtain⟨m0,hM0,hm0r,-⟩:=mY Z;obtain⟨m1,hM1,hm1⟩:=nJ W hc0;have c2:({n+m0,n+m1}:Finset ℕ).card=2:=card_pair (by omega);obtain⟨β',hcs⟩:∃β',col (L β')=col s:=by
  by_cases h:col (L 0)=col s
  ·exact⟨0,h⟩
  ·exact⟨1,bB _ _ _ (hcol _ _ hL01).symm (Ne.symm h)⟩
 have hc1:col (L (1-β'))≠col (L β'):=hcol _ _ ((hL β').2 _ (hL (1-β')).1)|>.symm;rcases aS b σ with hσ|hσ<;>rw[hσ]at hs hnorm
 ·rcases hnorm with hu|⟨hsing,h2⟩
  ·exact hcol _ _ hL01 (bB _ _ _ (hcol _ _ (fF Z hs hu (hDL 0))).symm (hcol _ _ (fF Z hs hu (hDL 1))).symm)
  obtain⟨ℓ1,hℓ1,ℓ2,hℓ2,hℓ12⟩:=one_lt_card.mp (by omega:1<(aE ((Ustar G C).filter λe=>¬a9 n C q L e) s).card);have hadj:∀ℓ∈aE ((Ustar G C).filter λe=>¬a9 n C q L e) s,G.Adj s ℓ:=λℓ h=>SimpleGraph.mem_edgeFinset.mp (mem_sdiff.mp (mem_filter.mp (aD.mp h)).1).1;have hcl:∀ℓ∈aE ((Ustar G C).filter λe=>¬a9 n C q L e) s,col ℓ≠col s:=λℓ h=>(hcol _ _ (hadj ℓ h)).symm;obtain⟨t1,ht1,ht1z⟩:=exists_mem_ne (hW (1-β')) (L (1-β'));have key:∀d∈orIn n C (opnd C r (1-b)),col d≠col s ->∀a∈orIn n C (opnd C q β'),a≠L β' ->G.Adj a d:=by
   intro d hd hcd a ha hap;have hat:¬G.Adj a t1:=λh=>ht1z (aQ h4 hap h ((hL β').2 t1 ht1) (hfull β' a ha).symm ((hL β').2 _ (hL _).1));have htd:¬G.Adj t1 d:=λh=>hcol _ _ h ((fZ W ht1).trans (bB _ _ _ hc1 (by rw[hcs];exact hcd)));rcases eY (hg (λz=>decide (z=a\/z=t1\/z=d)) ((bP Z.1 β' _).mpr ⟨⟨a,ha,by simp⟩,t1,ht1,by simp⟩) ⟨d,hd,by simp⟩)with h|h|h;exacts[(hat h).elim,(htd h).elim,h]
  have hlD:=λℓ (h:ℓ∈aE ((Ustar G C).filter λe=>¬a9 n C q L e) s)=>gR W hs (aD.mp h);have hAβ:∀a∈orIn n C (opnd C q β'),a=L β'\/a=s:=λa ha=>or_iff_not_imp_left.mpr λhap=>aQ h4 hℓ12 (key _ (hlD _ hℓ1) (hcl _ hℓ1) a ha hap).symm (key _ (hlD _ hℓ2) (hcl _ hℓ2) a ha hap).symm (hadj _ hℓ1).symm (hadj _ hℓ2).symm;have hX:∀e∈Ustar G C,∃v∈({L β',s}:Finset (Fin n)),v∈e:=by
   intro e he;by_cases hE:a9 n C q L e
   ·obtain⟨γ,w,hw,rfl⟩:=hE;rcases aS β' γ with h|h<;>rw[h]at hw⊢
    ·exact⟨L β',by simp,Sym2.mem_mk_left _ _⟩
    ·rw[bV]at hw;rcases hAβ w hw with h'|h'<;>rw[h']
     ·exact⟨L β',by simp,Sym2.mem_mk_right _ _⟩
     ·exact⟨s,by simp,Sym2.mem_mk_right _ _⟩
   ·exact⟨s,by simp,hcv e (mem_filter.mpr ⟨he,hE⟩)⟩
  obtain⟨Pg,hPg,cg⟩:=lM W hs hcv (Anc:={L β'}) (singleton_subset_iff.mpr (hDL β')) (disjoint_singleton_left.mpr λh=>hcl _ h hcs) (λW' hW'=>q2 h4 hcol kC hW' hcs);refine g3 W (a:=1) hKc hKs hX (λh hh=>⟨_,(hPg h hh).1⟩) (by simpa using cg) (eV hM0 hM1) (H:=∅) (by simp) ?_;rw[c2,card_empty];have:=(eG K _ (L β')).trans (Nat.add_le_add_left (gX K s) _);split_ifs at this<;>omega
 ·rcases hnorm with hu|⟨hsing,-⟩
  swap
  ·have:=hDL 0;rw[hsing,mem_singleton]at this;exact(hsL 0 this.symm).elim
  have hsC:∀c∈orIn n C (opnd C r b),G.Adj s c:=λc hc=>fF Z hs hu (by rwa[bV]);obtain⟨a0,ha0,ha0p⟩:=exists_mem_ne (hW β') (L β');have key:∀t∈orIn n C (opnd C q (1-β')),t≠L (1-β') ->G.Adj s t:=by
   intro t ht htz;have hat:¬G.Adj a0 t:=λh=>htz (aQ h4 ha0p h ((hL β').2 t ht) (hfull β' a0 ha0).symm ((hL β').2 _ (hL _).1));have has:¬G.Adj a0 s:=λh=>hcol _ _ h ((fZ W ha0).trans hcs);rcases eY (hg (λz=>decide (z=a0\/z=t\/z=s)) ((bP Z.1 β' _).mpr ⟨⟨a0,ha0,by simp⟩,t,ht,by simp⟩) ⟨s,hs,by simp⟩)with h|h|h;exacts[(hat h).elim,h.symm,(has h).elim]
  obtain⟨t0,ht0,ht0z⟩:=exists_mem_ne (hW (1-β')) (L (1-β'));have hT0:∀t∈orIn n C (opnd C q (1-β')),t=L (1-β')\/t=t0:=λt ht=>or_iff_not_imp_left.mpr λhtz=>aQ h4 (hsL β') (key t ht htz) ((hL β').2 t ht) (key t0 ht0 ht0z) ((hL β').2 t0 ht0);obtain⟨as,has,βs,hrs,hss⟩:=hu;obtain⟨y0,hy0⟩:(orIn n C (opnd C as βs)).Nonempty:=nonempty_iff_ne_empty.mpr λhe=>by
   have:=card_pos.mpr ⟨as,c7 has he⟩;omega
  obtain⟨w,hw,hws⟩:∃w∈orIn n C (opnd C as (1-βs)),w≠s:=by
   by_contra h;simp only[not_exists,not_and,not_not]at h;rcases uU hKa (jO has ⟨_,hy0⟩ ⟨_,hss⟩) (eq_singleton_iff_unique_mem.mpr ⟨hss,h⟩)with h'|h'|h';exacts[hnK.2.2 h',hnK.1 h',hnK.2.1 h']
  have hsy:=(aV hA has βs hss hy0).1;have hwy:=(aV hA has βs hw hy0).1;have hcw:col w=col s:=bB _ _ _ (hcol _ _ hwy) (hcol _ _ hsy);have hpc:∀c∈orIn n C (opnd C r b),c≠t0 ->¬G.Adj (L β') c:=λc hc hct h=>hct (aQ h4 (hsL β').symm h (hsC c hc) ((hL β').2 t0 ht0) (key t0 ht0 ht0z));have hwW:k4 n G C r w:=j4 hA has hrs hw;have hwc:∀c∈orIn n C (opnd C r b),c≠t0 ->G.Adj w c:=by
   intro c hc hct;rcases eY (hwW (λz=>decide (z=c\/z=L β'\/z=w)) ((dU Z _).mpr ⟨Or.inr ⟨c,hc,by simp⟩,L β',hDL β',by simp⟩) (by simp))with h|h|h
   ·exact(hpc c hc hct h.symm).elim
   ·exact(hcol _ _ h (hcs.trans hcw.symm)).elim
   ·exact h.symm
  have hVg:∀e∈(Ustar G C).filter (λe=>¬a9 n C q L e),t0∈e:=by
   intro e he;obtain⟨ℓ,rfl⟩:=Sym2.mem_iff_exists.mp (hcv e he);have hℓ:=gR W hs he;rw[bV]at hℓ;by_cases hℓt:ℓ=t0
   ·rw[hℓt];exact Sym2.mem_mk_right _ _
   exfalso;have hsl:G.Adj s ℓ:=SimpleGraph.mem_edgeFinset.mp (mem_sdiff.mp (mem_filter.mp he).1).1;have:=aQ h4 (Ne.symm hws) hsl (hwc ℓ hℓ hℓt) hsy hwy;rw[this]at he;exact(mem_sdiff.mp (mem_filter.mp he).1).2 (aV hA has βs hss hy0).2
  have hX:∀e∈Ustar G C,∃v∈({L (1-β'),t0}:Finset (Fin n)),v∈e:=by
   intro e he;by_cases hE:a9 n C q L e
   ·obtain⟨γ,x,hx,rfl⟩:=hE;rcases aS β' γ with h|h<;>rw[h]at hx⊢
    ·rcases hT0 x hx with h'|h'<;>rw[h']
     ·exact⟨L (1-β'),by simp,Sym2.mem_mk_right _ _⟩
     ·exact⟨t0,by simp,Sym2.mem_mk_right _ _⟩
    ·exact⟨L (1-β'),by simp,Sym2.mem_mk_left _ _⟩
   ·exact⟨t0,by simp,hVg e (mem_filter.mpr ⟨he,hE⟩)⟩
  obtain⟨Pg,hPg,cg⟩:=lM W hs hcv (Anc:=∅) (empty_subset _) (disjoint_empty_left _) λW' hW'=>by
    simpa using aF h4 kC hW' s
  obtain⟨h,hCh,h0,h1⟩:=kN hA (G.ne_of_adj hL01) (hDL 0) (hDL 1) λW' hW' ⟨i0,i1⟩=>by
   obtain⟨c,hc⟩:=aU col hcol hW';exact hcol _ _ hL01 ((hc _ i0).trans (hc _ i1).symm)
  have hLh:∀β,L β∈orIn n C h:=λβ=>by
   rcases eP L β with e|e<;>rw[e];exacts[h0,h1]
  refine g3 W (a:=0) hKc hKs hX (λh hh=>⟨_,(hPg h hh).1⟩) (by simpa using cg) (eV hM0 hM1) (H:={h}) (λh' hh=>?_) ?_
  ·rw[mem_singleton.mp hh];refine⟨⟨_,_,hCh⟩,λγ hsub=>disjoint_left.mp (cJ Z.1 γ) (hsub (hLh (1-γ))) (hL (1-γ)).1,λhp=>?_⟩;have:=(hPg h hp).2 (hLh 0);rw[bV]at this;exact disjoint_left.mp (kZ Z) this (hDL 0)
  ·rw[c2,card_singleton];have:=(eG K _ (L (1-β'))).trans (Nat.add_le_add_left (gX K t0) _);split_ifs at this<;>omega
open Classical in
lemma t3 (W:c9 G C q r b L col) {s:Fin n} {σ:Fin 2} (hs:s∈orIn n C (opnd C r σ)) (hcv:∀e∈(Ustar G C).filter (λe=>¬a9 n C q L e),s∈e) (hnc:∀β,∃e∈(Ustar G C).filter (λe=>¬a9 n C q L e),L β∉e) (hnorm:aC n G C r s\/(orIn n C (opnd C r σ)={s}/\2≤(aE ((Ustar G C).filter λe=>¬a9 n C q L e) s).card)):False:=by
 have hcol:=W.2.1;have Z:=W.2.2.1;obtain⟨hC,-,h4,-,-,-,-⟩:=Z.1;have hA:=hC.1;obtain⟨K,hKc,hKs,hKa⟩:=qZ hA h4 (pL n C q L s);have hX:∀e∈Ustar G C,∃v∈({L 0,L 1,s}:Finset (Fin n)),v∈e:=by
  intro e he;by_cases hE:a9 n C q L e
  ·obtain⟨β,w,-,rfl⟩:=hE;exact⟨L β,by rcases eP L β with h|h<;>rw[h]<;>simp,Sym2.mem_mk_left _ _⟩
  ·exact⟨s,by simp,hcv e (mem_filter.mpr ⟨he,hE⟩)⟩
 obtain⟨Pg,hPg,cg⟩:=lM W hs hcv (Anc:=∅) (empty_subset _) (disjoint_empty_left _) λW' hW'=>by simpa using aF h4 kC hW' s
 obtain⟨m0,hM0,hm0r,hm0n⟩:=mY Z;have hN:=(eG K _ (L 0)).trans (Nat.add_le_add_left ((eG K _ (L 1)).trans (Nat.add_le_add_left (gX K s) _)) _);have F0:∀M H:Finset ℕ,(∀h∈M,aR n G C h) ->(∀h∈H,(∃V w,b5 n G C V w h)/\(∀γ,¬orIn n C h⊆orIn n C (opnd C q γ))/\h∉Pg) ->(({L 0,L 1,s}:Finset (Fin n))\K).card+1≤2*(centreless G C).card+M.card+H.card ->False:=λM H hM hH hc=>g3 W (a:=0) hKc hKs hX (λh hh=>⟨_,(hPg h hh).1⟩) (by simpa using cg) hM hH (by omega);have hM0':∀h∈({n+m0}:Finset ℕ),aR n G C h:=λh hh=>by
  rw[mem_singleton.mp hh];exact hM0
 have hN3:(({L 0,L 1,s}:Finset (Fin n))\K).card≤3:=by split_ifs at hN<;>omega
 by_cases hc2:2≤(centreless G C).card
 ·exact F0 {n+m0} ∅ hM0' (by simp) (by rw[card_singleton,card_empty];omega)
 by_cases hDβ:∃β,L β∉K/\¬aC n G C q (L β)
 ·obtain⟨β,-,hβu⟩:=hDβ;obtain⟨hg,hpD⟩:b8 G C q r b/\L β∈orIn n C (opnd C r (1-b)):=by
   rcases W.2.2.2.2.2 with h|⟨hg,hD⟩
   ·exact(hβu (h β)).elim
   ·exact⟨hg,(hD β).resolve_left hβu⟩
  have FD:∀M:Finset ℕ,(∀h∈M,aR n G C h) ->(({L 0,L 1,s}:Finset (Fin n))\K).card+1≤2*(centreless G C).card+M.card+1 ->False:=by
   intro M hM hc;rcases u6 W hg hs hcv hnc hnorm hpD with⟨hσ,h,hCh,hHq⟩|⟨hσ,w,hwD,hcw⟩
   ·refine F0 M {h} hM (λh' hh=>?_) (by rw[card_singleton];omega);rw[mem_singleton.mp hh];refine⟨⟨_,_,hCh⟩,hHq,λhp=>?_⟩;obtain⟨v,hv⟩:=gW hA hCh;have h1:=(hPg h hp).2 hv;rw[hσ,bV]at h1;exact disjoint_left.mp (kZ Z) h1 (aK (aJ hA) hCh.2.2.2.2 hv)
   ·rw[hσ]at hs;obtain⟨Pg1,hPg1,cg1⟩:=lM W hs hcv (Anc:={w}) (singleton_subset_iff.mpr hwD) (disjoint_singleton_left.mpr λh=>hcol _ _ (SimpleGraph.mem_edgeFinset.mp (kC (aD.mp h))) hcw.symm) (λW' hW'=>q2 h4 hcol kC hW' hcw);exact g3 W (a:=1) hKc hKs hX (λh hh=>⟨_,(hPg1 h hh).1⟩) (by simpa using cg1) hM (H:=∅) (by simp) (by rw[card_empty];omega)
  by_cases hc0:(centreless G C).card=0
  ·obtain⟨m1,hM1,hm1⟩:=nJ W hc0;have c2:({n+m0,n+m1}:Finset ℕ).card=2:=card_pair (by omega);by_cases hall:L 0∉K/\L 1∉K/\s∉K
   ·have hDL:∀β',L β'∈orIn n C (opnd C r (1-b)):=λβ'=>by
     have hnu:¬aC n G C q (L β'):=λhu=>by
      obtain⟨a,ha,-⟩:=gT W hKa hu (by
       rcases eP L β' with h|h<;>rw[h]
       exacts[hall.1,hall.2.1])
      have:=card_pos.mpr ⟨a,ha⟩;omega
     rcases W.2.2.2.2.2 with h|⟨-,hD⟩
     ·exact(hnu (h β')).elim
     ·exact(hD β').resolve_left hnu
    exact vC W hg hs hcv hnc hnorm hc0 hDL hKc hKs hKa hall
   ·refine FD {n+m0,n+m1} (eV hM0 hM1) ?_;rw[c2];simp only[not_and_or,not_not]at hall;rcases hall with h|h|h<;>rw[ite_eq_left h]at hN<;>split_ifs at hN<;>omega
  ·exact FD {n+m0} hM0' (by rw[card_singleton];omega)
 simp only[not_exists,not_and,not_not]at hDβ;by_cases hc0:(centreless G C).card=0
 ·obtain⟨m1,hM1,hm1⟩:=nJ W hc0;have hLK:∀β,L β∈K:=λβ=>by_contra λh=>by
   obtain⟨a,ha,-⟩:=gT W hKa (hDβ β h) h;have:=card_pos.mpr ⟨a,ha⟩;omega
  refine F0 {n+m0,n+m1} ∅ (eV hM0 hM1) (by simp) ?_;rw[ite_eq_left (hLK 0),ite_eq_left (hLK 1)]at hN;rw[card_pair (by omega),card_empty];split_ifs at hN<;>omega
 by_cases hLK:L 0∈K\/L 1∈K\/s∈K
 ·refine F0 {n+m0} ∅ hM0' (by simp) ?_;rw[card_singleton,card_empty];rcases hLK with h|h|h<;>rw[ite_eq_left h]at hN<;>split_ifs at hN<;>omega
 simp only[not_or]at hLK;obtain⟨a1,ha1,b1,hr1,he1,-⟩:=gT W hKa (hDβ 0 hLK.1) hLK.1;obtain⟨u,v,he,hq⟩:=nE W;obtain⟨-,c,-,-,-,-,hu⟩:=nY Z he hq;obtain⟨m1,hM1,hm1⟩:=sX W (by omega) ha1 hr1 he1 hu;have hm10:m1≠m0:=λe=>by
  rw[e]at hm1;rcases hm1 with h|h
  ·omega
  ·rw[h]at hm0n;simp at hm0n
 refine F0 {n+m0,n+m1} ∅ (eV hM0 hM1) (by simp) ?_;rw[card_pair (by omega),card_empty];omega
open Classical in
lemma sF (W:c9 G C q r b L col) {s0:Fin n} (hcv:∀e∈(Ustar G C).filter (λe=>¬a9 n C q L e),s0∈e) {e0:Sym2 (Fin n)} (he0:e0∈(Ustar G C).filter (λe=>¬a9 n C q L e)):∃s:Fin n,∃σ:Fin 2,s∈orIn n C (opnd C r σ)/\(∀e∈(Ustar G C).filter (λe=>¬a9 n C q L e),s∈e)/\(aC n G C r s\/(orIn n C (opnd C r σ)={s}/\2≤(aE ((Ustar G C).filter λe=>¬a9 n C q L e) s).card)):=by
 have Z:=W.2.2.1;have h4:=Z.1.2.2.1;obtain⟨γ,c,hc,d,hd,he,hu⟩:=lO W he0;have hs0:=hcv _ he0;rw[he]at hs0;by_cases hus:aC n G C r s0
 ·rcases Sym2.mem_iff.mp hs0 with h|h
  ·exact⟨c,γ,hc,λe he=>h▸hcv e he,Or.inl (h▸hus)⟩
  ·exact⟨d,1-γ,hd,λe he=>h▸hcv e he,Or.inl (h▸hus)⟩
 have hsd:s0=d:=(Sym2.mem_iff.mp hs0).resolve_left λh=>hus (h▸hu);by_cases hone:∀e∈(Ustar G C).filter (λe=>¬a9 n C q L e),c∈e
 ·exact⟨c,γ,hc,hone,Or.inl hu⟩
 obtain⟨e1,he1,hce1⟩:∃e∈(Ustar G C).filter (λe=>¬a9 n C q L e),c∉e:=by
  by_contra h;simp only[not_exists,not_and,not_not]at h;exact hone h
 obtain⟨γ1,c1,hc1,d1,hd1,he1',hu1⟩:=lO W he1;have hs1:=hcv _ he1;rw[he1']at hs1 hce1;have hsd1:s0=d1:=(Sym2.mem_iff.mp hs1).resolve_left λh=>hus (h▸hu1);rw[←hsd]at hd;rw[←hsd1]at hd1;have hγ:γ1=γ:=by
  rcases aS γ γ1 with h|h
  ·exact h
  ·rw[h,bV]at hd1;exact absurd hd (disjoint_left.mp (lT Z γ) hd1)
 rw[hγ]at hc1;have hcc:c≠c1:=λh=>hce1 (by rw[h];exact Sym2.mem_mk_left _ _);have hR1:(orIn n C (opnd C r (1-γ))).card≤1:=by
  by_contra h2;exact hcc (bC h4 (by omega) (λt ht=>fF Z hc hu ht) (λt ht=>fF Z hc1 hu1 ht))
 refine⟨s0,1-γ,hd,hcv,Or.inr ⟨eq_singleton_iff_unique_mem.mpr ⟨hd,λx hx=>card_le_one.mp hR1 x hx s0 hd⟩,?_⟩⟩;have h2:=card_le_card (s:=({c,c1}:Finset (Fin n))) (t:=aE ((Ustar G C).filter λe=>¬a9 n C q L e) s0) λx hx=>by
   simp only[mem_insert,mem_singleton]at hx;rcases hx with h|h<;>rw[h]<;>refine aD.mpr ?_
   ·rw[hsd,Sym2.eq_swap,←he];exact he0
   ·rw[hsd1,Sym2.eq_swap,←he1'];exact he1
 rwa[card_pair hcc]at h2
open Classical in
theorem p5 (W:c9 G C q r b L col):False:=by
 obtain⟨u0,v0,he0,hq0⟩:=nE W;have he0g:s(u0,v0)∈(Ustar G C).filter (λe=>¬a9 n C q L e):=mem_filter.mpr ⟨he0,λhE=>by rw[r5 W hE]at hq0;cases hq0⟩;rcases tI W.2.2.1 (λe he=>lO W he)with⟨s0,hs0⟩|⟨y,hy,form⟩
 ·by_cases hnc:∀β,∃e∈(Ustar G C).filter (λe=>¬a9 n C q L e),L β∉e
  ·obtain⟨s,σ,hs,hcv,hnorm⟩:=sF W hs0 he0g;exact t3 W hs hcv hnc hnorm
  ·simp only[not_forall,not_exists,not_and,not_not]at hnc;obtain⟨β,hβ⟩:=hnc;exact tY W hβ
 ·exact u4 W hy form
end W
section T
variable {q r:ℕ} {b:Fin 2}
theorem jG (hR1:cM) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (Z:cI G C q r b) (hg:b8 G C q r b):False:=by
 have hA:=Z.1.1.1;have h4:=Z.1.2.2.1;obtain⟨hq,-⟩:=b4 Z;have hql:=(aA.mp hq).1;have hrd:=sA Z hg;have hcf:∀γ,∀v∈orIn n C (opnd C q γ),(aC n G C q v\/v∈orIn n C (opnd C r (1-b))) ->∀t∈orIn n C (opnd C q (1-γ)),G.Adj v t:=by
  intro γ v hv hc t ht;rcases hc with hu|hD
  ·exact f8 Z.1 hv (bH hA hu) t ht
  ·exact(aT v t).mp (hg _ ((bP Z.1 γ _).mpr ⟨⟨v,hv,by simp[pairInput]⟩,t,ht,by simp[pairInput]⟩) ⟨v,hD,by simp[pairInput]⟩)
 have hex:∀γ,∃v∈orIn n C (opnd C q γ),aC n G C q v\/v∈orIn n C (opnd C r (1-b)):=by
  by_contra hno;simp only[not_forall,not_exists,not_and,not_or]at hno;obtain⟨γ,hγ⟩:=hno;have key:∀u v,G.Adj u v ->wireVal n (aG n C q) C.output (pairInput u v)=false ->∃w∈orIn n C (opnd C q (1-γ)),(w=u\/w=v)/\(aC n G C q w\/w∈orIn n C (opnd C r (1-b)))/\∃t∈orIn n C (opnd C q γ),t=u\/t=v:=by
   intro u v huv hk;obtain⟨hqx,hU⟩:=jF Z hq huv hk;obtain⟨w,hwe,hwc⟩:∃w,(w=u\/w=v)/\(aC n G C q w\/w∈orIn n C (opnd C r (1-b))):=by
    rcases s9 Z hU with⟨-,w,hw,hu⟩|⟨hr,-⟩|⟨-,hr⟩
    ·exact⟨w,hw,Or.inl hu⟩
    ·obtain⟨d,hd,hdx⟩:=((dU Z _).mp hr).2;exact⟨d,aW hdx,Or.inr hd⟩
    ·obtain⟨d,hd,hdx⟩:=((dU Z _).mp hr).2;exact⟨d,aW hdx,Or.inr hd⟩
   obtain⟨⟨a,ha,hax⟩,⟨t,ht,htx⟩⟩:=(bP Z.1 γ _).mp hqx;have hat:a≠t:=λe=>disjoint_left.mp (cJ Z.1 γ) ha (e▸ht);have e:=fP (aW hax) (aW htx) hat;have:w∈s(a,t):=e▸(by rcases hwe with h|h<;>rw[h]<;>simp);rcases Sym2.mem_iff.mp this with h|h
   ·rw[h]at hwc;rcases hwc with h'|h';exacts[((hγ a ha).1 h').elim,((hγ a ha).2 h').elim]
   ·exact⟨w,by rw[h];exact ht,hwe,hwc,a,ha,aW hax⟩
  by_cases hp:∃p∈orIn n C (opnd C q (1-γ)),aC n G C q p\/p∈orIn n C (opnd C r (1-b))
  ·obtain⟨p,hp,hpc⟩:=hp;have hpf:=hcf _ p hp hpc;rw[bV]at hpf;refine sH hR1 col hcol Z γ hp hpf (λu v huv=>?_) (Or.inr hrd);cases hk:wireVal n (aG n C q) C.output (pairInput u v)
   ·right;obtain⟨w,hw,hwe,hwc,t,ht,hte⟩:=key u v huv hk;have hwf:=hcf _ w hw hwc;rw[bV]at hwf;rw[bC h4 (Z.1.2.2.2.2.2.2 γ) hwf hpf]at hwe;exact⟨by rcases hwe with h|h<;>rw[h]<;>simp,t,ht,by rcases hte with h|h<;>rw[h]<;>simp⟩
   ·exact Or.inl rfl
  ·exact jJ Z.1.1 hql λu v huv=>by
    by_contra hk;obtain⟨w,hw,-,hwc,-⟩:=key u v huv (by simpa using hk);exact hp ⟨w,hw,hwc⟩
 choose L hL hLc using hex;exact p5 (L:=L) (col:=col) ⟨hR1,hcol,Z,λβ=>⟨hL β,hcf β _ (hL β) (hLc β)⟩,Or.inr hrd,Or.inr ⟨hg,hLc⟩⟩
theorem eN (hR1:cM) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (Z:cI G C q r b) (h0:∃p∈orIn n C (opnd C q 0),dX G C q p/\∀t∈orIn n C (opnd C q 1),G.Adj p t) (h1:∃z∈orIn n C (opnd C q 1),dX G C q z/\∀s∈orIn n C (opnd C q 0),G.Adj s z):False:=by
 obtain⟨p,hp,hpu,hpf⟩:=h0;obtain⟨z,hz,hzu,hzf⟩:=h1;refine p5 (L:= ![p,z]) (col:=col) ⟨hR1,hcol,Z,λβ=>?_,Or.inl (t4 Z hcol (hpf z hz) hpu hzu),Or.inl λβ=>?_⟩
 ·fin_cases β
  ·exact⟨hp,hpf⟩
  ·exact⟨hz,λs hs=>(hzf s hs).symm⟩
 ·fin_cases β;exacts[hpu,hzu]
end T
open Classical in
noncomputable def gH (n:ℕ) (C:Circuit) (w:ℕ):ℕ:=if _h:bX n C w/\bF n C w<w/\bI n C w<w/\(orIn n C (bF n C w)=∅\/orIn n C (bI n C w)=∅)then if orIn n C (bF n C w)=∅ then gH n C (bI n C w)else gH n C (bF n C w)else w
termination_by w
decreasing_by exacts[_h.2.2.1,_h.2.1]
def vL (n:ℕ) (C:Circuit) (w:ℕ):Prop:=¬(bX n C w/\(orIn n C (bF n C w)=∅\/orIn n C (bI n C w)=∅))
lemma gA (hA:IsAO2 n C) (w:ℕ):gH n C w<=w/\orIn n C (gH n C w)=orIn n C w/\vL n C (gH n C w):=by
 induction w using Nat.strong_induction_on with
 |_ w ih=>
  rw[gH];split_ifs with h1 h2
  ·obtain⟨a,e,c⟩:=ih _ h1.2.2.1;refine⟨by omega,?_,c⟩;rw[e,(aJ hA w h1.1).2.2,h2,empty_union]
  ·obtain⟨a,e,c⟩:=ih _ h1.2.1;refine⟨by omega,?_,c⟩;rw[e,(aJ hA w h1.1).2.2,h1.2.2.2.resolve_left h2,union_empty]
  ·exact⟨le_rfl,rfl,λh=>h1 ⟨h.1,(aJ hA w h.1).1,(aJ hA w h.1).2.1,h.2⟩⟩
def qQ (n:ℕ) (C:Circuit):(ℕ⊕Finset (Fin n)⊕Fin 2) ->Prop:=Sum.elim (λw=>bX n C w/\(orIn n C (bF n C w)).Nonempty/\(orIn n C (bI n C w)).Nonempty) (Sum.elim (λ_=>False) λ_=>True)
noncomputable def qL (n:ℕ) (C:Circuit) (q:ℕ):(ℕ⊕Finset (Fin n)⊕Fin 2) ->(ℕ⊕Finset (Fin n)⊕Fin 2):=Sum.elim (λw=>Sum.inl (gH n C (bF n C w))) (Sum.elim (λW=>Sum.inr (Sum.inl W)) λB=>Sum.inl (gH n C (opnd C q B)))
noncomputable def qN (n:ℕ) (C:Circuit) (c:ℕ):(ℕ⊕Finset (Fin n)⊕Fin 2) ->(ℕ⊕Finset (Fin n)⊕Fin 2):=Sum.elim (λw=>Sum.inl (gH n C (bI n C w))) (Sum.elim (λW=>Sum.inr (Sum.inl W)) λ_=>Sum.inl (gH n C c))
def rZ (n:ℕ) (C:Circuit):(ℕ⊕Finset (Fin n)⊕Fin 2) ->ℕ:=Sum.elim id (Sum.elim (λ_=>0) λ_=>n+C.gates.length)
def pM (n:ℕ) (C:Circuit) (q c:ℕ):(ℕ⊕Finset (Fin n)⊕Fin 2) ->Finset (Fin n):=Sum.elim (orIn n C) (Sum.elim id λB=>orIn n C (opnd C q B)∪orIn n C c)
lemma uR (hA:IsAO2 n C) {q c:ℕ} (hq:q<C.gates.length) (hc:c<n+C.gates.length):dB (qQ n C) (qL n C q) (qN n C c) (rZ n C) (pM n C q c):=by
 rintro(w|W|B) hw
 ·have h:=aJ hA w hw.1;have h1:=gA hA (bF n C w);have h2:=gA hA (bI n C w);simp only[qL,qN,rZ,pM,Sum.elim_inl,id]at h⊢;exact⟨by omega,by omega,by rw[h1.2.1,h2.2.1];exact h.2.2⟩
 ·exact hw.elim
 ·have h1:=gA hA (opnd C q B);have h2:=gA hA c;have h3:=aH hA hq B;simp only[qL,qN,rZ,pM,Sum.elim_inl,Sum.elim_inr,id];exact⟨by omega,by omega,by rw[h1.2.1,h2.2.1]⟩
def kW (n:ℕ) (G:SimpleGraph (Fin n)) (C:Circuit) (U:Finset (Sym2 (Fin n))) (s:Fin 2 ->Prop):(ℕ⊕Finset (Fin n)⊕Fin 2) ->Prop:=Sum.elim (vL n C) (Sum.elim (aB G U) s)
omit [DecidableRel G.Adj]in
lemma rB (hA:IsAO2 n C) {q c:ℕ} {U:Finset (Sym2 (Fin n))} {s:Fin 2 ->Prop} {v u:(ℕ⊕Finset (Fin n)⊕Fin 2)} (hv:kW n G C U s v) (hu:aM (qQ n C) (qL n C q) (qN n C c) v u):kW n G C U s u:=by
 induction hu with
 |refl=>exact hv
 | @tail u' u'' _ hs ih=>
  obtain⟨hJ,he|he⟩:=hs<;>rcases u' with w|W|B
  all_goals try exact hJ.elim
  all_goals subst he
  all_goals exact(gA hA _).2.2
omit [DecidableRel G.Adj]in
lemma vJ {U:Finset (Sym2 (Fin n))} {s:Fin 2 ->Prop} {u:(ℕ⊕Finset (Fin n)⊕Fin 2)} (hu:kW n G C U s u) (hJ:¬qQ n C u) {q c:ℕ}:aB G U (pM n C q c u)\/(pM n C q c u).card<=1:=by
 rcases u with w|W|B
 ·refine Or.inr (bL λhp=>hJ ⟨hp,?_,?_⟩)<;>
  exact nonempty_iff_ne_empty.mpr λe=>hu ⟨hp,by tauto⟩
 ·exact Or.inl hu
 ·exact(hJ trivial).elim
noncomputable def sM (n:ℕ) (C:Circuit) (dw:ℕ) (RV:List ((ℕ⊕Finset (Fin n)⊕Fin 2))):Fin 4 ->(ℕ⊕Finset (Fin n)⊕Fin 2)⊕ℕ:= ![Sum.inl (Sum.inr (Sum.inr 0)),Sum.inl (Sum.inr (Sum.inr 1)),Sum.inl (Sum.inl (gH n C dw)),dM RV (Sum.inl 0)]
omit [DecidableRel G.Adj]in
lemma mG (hA:IsAO2 n C) {q c dw:ℕ} {U:Finset (Sym2 (Fin n))} {RV:List ((ℕ⊕Finset (Fin n)⊕Fin 2))} (hR:RV≠[]) (hRV:∀v∈RV,kW n G C U (λ_=>False) v) (k:Fin 4) {u:(ℕ⊕Finset (Fin n)⊕Fin 2)⊕ℕ} (hu:aM (eR (qQ n C) RV) (gG (qL n C q) RV (Sum.inl 0)) (f5 (qN n C c) RV (Sum.inl 0)) (sM n C dw RV k) u):Sum.elim (kW n G C U λB=>(k:ℕ)=B) (λi=>k=3/\i+1<RV.length) u:=by
 fin_cases k
 ·obtain⟨w,rfl,hw⟩:=eL hu;exact rB hA (v:=Sum.inr (Sum.inr 0)) rfl hw
 ·obtain⟨w,rfl,hw⟩:=eL hu;exact rB hA (v:=Sum.inr (Sum.inr 1)) rfl hw
 ·obtain⟨w,rfl,hw⟩:=eL hu;exact rB hA (v:=Sum.inl _) (gA hA dw).2.2 hw
 ·have:=e7 (kW n G C U λB=>((3:Fin 4):ℕ)=B) (x:=dM RV (Sum.inl 0)) (Or.inl ⟨rfl,hR,λv hv w hw=>rB hA (by
    rcases v with w'|W|B
    exacts[hRV _ hv,hRV _ hv,(hRV _ hv).elim]) hw⟩) hu
  rcases u with v|i
  ·exact this
  ·exact⟨rfl,this⟩
omit [DecidableRel G.Adj]in
lemma uN (hA:IsAO2 n C) {q c dw:ℕ} {U:Finset (Sym2 (Fin n))} {RV:List ((ℕ⊕Finset (Fin n)⊕Fin 2))} (hR:RV≠[]) (hRV:∀v∈RV,kW n G C U (λ_=>False) v) (S:Finset ((ℕ⊕Finset (Fin n)⊕Fin 2)⊕ℕ)) (K:Fin 4 ->Prop) [DecidablePred K] (hS:∀h∈S,eR (qQ n C) RV h/\∃k,K k/\aM (eR (qQ n C) RV) (gG (qL n C q) RV (Sum.inl 0)) (f5 (qN n C c) RV (Sum.inl 0)) (sM n C dw RV k) h):S.card<=S.toLeft.toLeft.card+((if K 0 then 1 else 0)+(if K 1 then 1 else 0))+(if K 3 then RV.length-1 else 0):=by
 have c1:=card_toLeft_add_card_toRight (u:=S);have c2:=card_toLeft_add_card_toRight (u:=S.toLeft);have c3:=card_toLeft_add_card_toRight (u:=S.toLeft.toRight);have e3:S.toLeft.toRight.toLeft=∅:=eq_empty_of_forall_notMem λW hW=>(hS _ (mem_toLeft.mp (mem_toRight.mp (mem_toLeft.mp hW)))).1;have b1:S.toRight.card<=if K 3 then RV.length-1 else 0:=by
  split_ifs with h3
  ·have:S.toRight⊆range (RV.length-1):=λi hi=>by
    have:=(hS _ (mem_toRight.mp hi)).1;simp only[eR,Sum.elim_inr]at this;exact mem_range.mpr (by omega)
   simpa using card_le_card this
  ·rw[card_eq_zero.mpr (eq_empty_of_forall_notMem λi hi=>by
    obtain⟨-,k,hk,hr⟩:=hS _ (mem_toRight.mp hi)
    exact h3 ((mG hA hR hRV k hr).1▸hk))]
 have b2:S.toLeft.toRight.toRight.card<=(if K 0 then 1 else 0)+(if K 1 then 1 else 0):=by
  have:S.toLeft.toRight.toRight⊆(if K 0 then {0}else ∅)∪(if K 1 then {1}else ∅):=λB hB=>by
    obtain⟨-,k,hk,hr⟩:=hS _ (mem_toLeft.mp (mem_toRight.mp (mem_toRight.mp hB)));have e:(k:ℕ)=B:=mG hA hR hRV k hr;fin_cases B
    ·obtain rfl:k=0:=Fin.ext (by simpa using e);simp[hk]
    ·obtain rfl:k=1:=Fin.ext (by simpa using e);simp[hk]
  refine(card_le_card this).trans ((card_union_le _ _).trans ?_);split_ifs<;>simp
 rw[e3,card_empty]at c3;omega
lemma rM {T:Finset (Fin n)} {x y:Fin n}:(∃v∈T,pairInput x y v=true)↔x∈T\/y∈T:=by
 constructor
 ·rintro⟨v,hv,h⟩;rcases aW h with rfl|rfl;exacts[Or.inl hv,Or.inr hv]
 ·rintro(h|h);exacts[⟨x,h,by simp[pairInput]⟩,⟨y,h,by simp[pairInput]⟩]
section F
variable {q r:ℕ} {b:Fin 2}
lemma dK (Z:cI G C q r b) (x y:Fin n):gateVal n C r (pairInput x y)=true↔(gateVal n C q (pairInput x y)=true\/x∈orIn n C (opnd C r b)\/y∈orIn n C (opnd C r b))/\(x∈orIn n C (opnd C r (1-b))\/y∈orIn n C (opnd C r (1-b))):=by
 rw[dU Z,rM,rM]
lemma rJ (Z:cI G C q r b) (B:Fin 2) (x y:Fin n):gateVal n C q (pairInput x y)=true↔(x∈orIn n C (opnd C q B)\/y∈orIn n C (opnd C q B))/\(x∈orIn n C (opnd C q (1-B))\/y∈orIn n C (opnd C q (1-B))):=by
 rw[bP Z.1 B,rM,rM]
lemma n8 (Z:cI G C q r b) {x y:Fin n} (h:gateVal n C r (pairInput x y)=true) (B:Fin 2):(x∈orIn n C (opnd C q B)∪orIn n C (opnd C r b)\/y∈orIn n C (opnd C q B)∪orIn n C (opnd C r b))/\(x∈orIn n C (opnd C r (1-b))\/y∈orIn n C (opnd C r (1-b))):=by
 obtain⟨h1,h2⟩:=(dK Z x y).mp h;refine⟨?_,h2⟩;simp only[mem_union];rcases h1 with h|h|h
 ·rcases ((rJ Z B x y).mp h).1 with h'|h'<;>tauto
 ·tauto
 ·tauto
lemma uI (Z:cI G C q r b) {W:Finset (Fin n)} (hWs:∀w∈W,aC n G C r w) (x:Fin n ->Bool) (h0:∃v∈orIn n C (opnd C q 0)∪orIn n C (opnd C r b),x v=true) (h1:∃v∈orIn n C (opnd C q 1)∪orIn n C (opnd C r b),x v=true) (h2:∃v∈orIn n C (opnd C r (1-b)),x v=true) (h3:∃v∈W,x v=true):graphFun G ∅ x=true:=by
 obtain⟨v0,hv0,hx0⟩:=h0;obtain⟨v1,hv1,hx1⟩:=h1;obtain⟨w,hw,hxw⟩:=h3;refine bH Z.1.1.1 (hWs w hw) x ((dU Z x).mpr ⟨?_,h2⟩) hxw;rcases mem_union.mp hv0 with h|h
 ·rcases mem_union.mp hv1 with h'|h'
  ·exact Or.inl ((bP Z.1 0 x).mpr ⟨⟨v0,h,hx0⟩,v1,h',hx1⟩)
  ·exact Or.inr ⟨v1,h',hx1⟩
 ·exact Or.inr ⟨v0,h,hx0⟩
lemma vF (Z:cI G C q r b) {a:ℕ} (ha:a∈tops G C) {B:Fin 2} (h1:OrReaches n C (opnd C a B) r) (h2:OrReaches n C (opnd C a (1-B)) r):False:=by
 obtain⟨hal,hop,hb⟩:=aI.mp ha;exact(aA.mp (b4 Z).2).2.2 λx hx=>hb x ((aN Z.1.1.1 hal hop B x).mpr ⟨aO Z.1.1.1 x h1 hx,aO Z.1.1.1 x h2 hx⟩)
lemma r7 (Z:cI G C q r b):k∈junk G C↔k=q\/k=r:=by
 rw[Z.1.2.2.2.2.1,mem_insert,mem_singleton]
lemma qS (Z:cI G C q r b) (hu:aC n G C r w) (h:gateVal n C r (pairInput x y)=true) (hw:w=x\/w=y):G.Adj x y:=(aT x y).mp (bH Z.1.1.1 hu _ h (by rcases hw with rfl|rfl<;>simp[pairInput]))
lemma rE (Z:cI G C q r b) (hx:x∈orIn n C (opnd C q B)) (hy:y∈orIn n C (opnd C q (1-B))):gateVal n C q (pairInput x y)=true:=(bP Z.1 B _).mpr ⟨⟨x,hx,by simp[pairInput]⟩,y,hy,by simp[pairInput]⟩
lemma uF {U:Finset (Sym2 (Fin n))} (hy:∀e∈U,y∈e):U.card<=(aE U y).card:=(card_le_card (t:=(aE U y).image (s(y,·))) λe he=>by
  obtain⟨l,rfl⟩:=Sym2.mem_iff_exists.mp (hy e he)
  exact mem_image_of_mem _ (aD.mpr he)).trans card_image_le
lemma uD (Z:cI G C q r b) (hng:¬b8 G C q r b) {u v:Fin n} (he:s(u,v)∈Ustar G C):(gateVal n C q (pairInput u v)=true/\∃w,(w=u\/w=v)/\aC n G C q w)\/(gateVal n C r (pairInput u v)=true/\∃w,(w=u\/w=v)/\aC n G C r w):=by
 obtain⟨hC,hT,-,-,hJ,-,-⟩:=Z.1;have hA:=hC.1;obtain⟨a,ha,hax,B,k,hk,-,hrk,hkx⟩:=fD hC hT he;obtain⟨hal,hop,hab⟩:=aI.mp ha;rcases (a8 hA hT hal hop (1-B) _).mp ((aN hA hal hop B _).mp hax).2 with⟨w,hw,hwx⟩|⟨k',hk',-,hr',-⟩
 ·rw[hJ,mem_insert,mem_singleton]at hk;rcases hk with rfl|rfl;exacts[Or.inl ⟨hkx,w,aW hwx,a,ha,B,hrk,hw⟩,Or.inr ⟨hkx,w,aW hwx,a,ha,B,hrk,hw⟩]
 refine(hng λx hq ⟨d,hd,hxd⟩=>hab x ((aN hA hal hop B x).mpr ?_)).elim;have:∀k∈junk G C,gateVal n C k x=true:=λk hk=>by
  rw[hJ,mem_insert,mem_singleton]at hk;rcases hk with rfl|rfl;exacts[hq,(dU Z x).mpr ⟨Or.inl hq,d,hd,hxd⟩]
 exact⟨aO hA x hrk (this k hk),aO hA x hr' (this k' hk')⟩
lemma s6 (Z:cI G C q r b) (hrd:∀k∈readers n C q,∀k'∈readers n C q,(gateAt C k).op=GateOp.or ->(gateAt C k').op=GateOp.or ->k=k'):∃m,m<C.gates.length/\(gateAt C m).op=GateOp.or/\n+q∈(gateAt C m).inputs/\OrReaches n C (opnd C r b) m/\(orIn n C (n+m)).Nonempty/\∀w,OrReaches n C w q ->w≠n+q ->OrReaches n C w m:=by
 obtain⟨hC,hT,-,-,hJ,-,-⟩:=Z.1;have hA:=hC.1;obtain⟨hq,hr⟩:=b4 Z;obtain⟨hrl,hrop,-⟩:=aA.mp hr;obtain⟨hql,hqop,-⟩:=aA.mp hq;obtain⟨m,hm,hop,hin,hrm⟩:=gQ Z.2.1 λhe=>by
  have:=Z.2.2.2;rw[he,b6 (λ_=>by rw[hqop];simp)]at this;simp at this
 refine⟨m,hm,hop,hin,hrm,nonempty_iff_ne_empty.mpr λhmE=>?_,λw hrw hw=>?_⟩
 ·refine d3 hC hm (w:=n+q) (dH hA hm hin) λx=>Bool.eq_iff_iff.mpr ⟨λh1=>?_,aO hA x (bD.mpr ⟨hm,Or.inr ⟨hop,n+q,hin,dH hA hm hin,bD.mpr ⟨hql,Or.inl rfl⟩⟩⟩)⟩;rcases (kU hA x _).mp h1 with⟨v,hv,-⟩|⟨k,hk,hrk,hkx⟩
  ·simp[hmE]at hv
  have hc:=bU hA hrl b (cG hA hrm hrk);have:=d4 hT hrl hk hrop hc;rw[hJ,mem_insert,mem_singleton]at this;rcases this with rfl|rfl;exacts[hkx,absurd (aP hc) (lt_irrefl _)]
 ·obtain⟨m',hm',hop',hin',hrm'⟩:=gQ hrw hw;exact hrd m' (mem_filter.mpr ⟨mem_range.mpr hm',hin'⟩) m (mem_filter.mpr ⟨mem_range.mpr hm,hin⟩) hop' hop▸hrm'
lemma uB (Z:cI G C q r b) (hrd:(readers n C q).card<=1):∃m,OrReaches n C (opnd C r b) m/\(orIn n C (n+m)).Nonempty/\∀a∈tops G C,∀B:Fin 2,OrReaches n C (opnd C a B) q ->OrReaches n C (opnd C a B) m:=by
 obtain⟨m,hm,hop,hin,hrm,hne,hw⟩:=s6 Z λk hk k' hk' _ _=>card_le_one.mp hrd k hk k' hk';refine⟨m,hrm,hne,λa ha B hra=>hw _ hra λhe=>?_⟩;obtain⟨hal,haop,-⟩:=aI.mp ha;have:=card_le_one.mp hrd a (mem_filter.mpr ⟨mem_range.mpr hal,he▸dA Z.1.1.1 hal B⟩) m (mem_filter.mpr ⟨mem_range.mpr hm,hin⟩);rw[this,hop]at haop;cases haop
def n6 (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (q r:ℕ) (b o:Fin 2) (p:Fin n) (col:Fin n ->Bool):Prop:=cM/\(∀u v,G.Adj u v ->col u≠col v)/\cI G C q r b/\¬b8 G C q r b/\p∈orIn n C (opnd C q o)/\aC n G C q p/\(∀t∈orIn n C (opnd C q (1-o)),G.Adj p t)/\∀z∈orIn n C (opnd C q (1-o)),¬aC n G C q z
def bE (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (q:ℕ) (o:Fin 2) (p:Fin n):Finset (Sym2 (Fin n)):=Ustar G C\(orIn n C (opnd C q (1-o))).image λt=>s(p,t)
def sJ (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (C:Circuit) (r:ℕ) (Rc Ms:Finset ℕ) (Wg:ℕ ->Finset (Fin n)) (m0:ℕ):Prop:=aR n G C (n+m0)/\(orIn n C (n+m0)).Nonempty/\Rc.card<=(centreless G C).card/\(∀w∈Rc,∃a∈centreless G C,∃B:Fin 2,OrReaches n C (opnd C a B) r/\w=opnd C a (1-B))/\(∀m∈Ms,aR n G C (n+m)/\m0<m/\aB G (Ustar G C) (Wg m)/\(orIn n C (n+m)).Nonempty/\∃B:Fin 2,orIn n C (opnd C m B)=∅/\OrReaches n C (opnd C m B) r)/\∀x,aC n G C r x↔(∃w∈Rc,x∈orIn n C w)\/∃m∈Ms,x∈Wg m
lemma kG (hA:IsAO2 n C) {U1:Finset (Sym2 (Fin n))} {Pp Pr Xs Rc Ms:Finset ℕ} {Wg:ℕ ->Finset (Fin n)} {m0:ℕ} (H:sJ G C r Rc Ms Wg m0) (hp:∀h∈Pp,∃w,b5 n G C U1 w h) (hb:∀h∈Pr,(∃w,b5 n G C (Ustar G C) w h)/\aB G U1 (orIn n C h)) (hx:∀h∈Xs,h∈(orN G C\lam G C).image (n+·)/\(orIn n C (bF n C h)=∅\/orIn n C (bI n C h)=∅)/\h∉(insert m0 Ms).image (n+·)):Pp.card+Pr.card+Xs.card+Ms.card+1<=(orN G C\lam G C).card:=by
 obtain⟨hM0,-,-,-,hMs,-⟩:=H;have hMi:∀h∈(insert m0 Ms).image (n+·),aR n G C h:=λh hh=>by
  obtain⟨m,hm,rfl⟩:=mem_image.mp hh;rcases mem_insert.mp hm with rfl|hm;exacts[hM0,(hMs m hm).1]
 have hP:∀h∈Pp∪Pr,h∈(orN G C\lam G C).image (n+·)/\(orIn n C (bF n C h)).Nonempty/\(orIn n C (bI n C h)).Nonempty:=λh hh=>by
  rcases mem_union.mp hh with hh|hh
  ·obtain⟨w,h1,-,h3,h4,-⟩:=hp h hh;exact⟨h1,h3,h4⟩
  ·obtain⟨⟨w,h1,-,h3,h4,-⟩,-⟩:=hb h hh;exact⟨h1,h3,h4⟩
 have hsub:Pp∪Pr∪(Xs∪(insert m0 Ms).image (n+·))⊆(orN G C\lam G C).image (n+·):=λh hh=>by
   rcases mem_union.mp hh with hh|hh
   ·exact(hP h hh).1
   rcases mem_union.mp hh with hh|hh;exacts[(hx h hh).1,g7 hA (hMi h hh)]
 have:=card_le_card hsub
 rw[card_union_of_disjoint (disjoint_left.mpr λh h1 h2=>by
   have:=hP h h1;rcases mem_union.mp h2 with h2|h2
   exacts[(hx h h2).2.1.elim this.2.1.ne_empty this.2.2.ne_empty,(hMi h h2).2.2.elim this.2.1.ne_empty this.2.2.ne_empty]),
  card_union_of_disjoint (disjoint_left.mpr λh h1 h2=>let ⟨_,c⟩:=hp h h1;c.2.1 (hb h h2).2),
  card_union_of_disjoint (disjoint_left.mpr λh h1=>(hx h h1).2.2),
  card_image_of_injective _ (add_right_injective n),
  card_image_of_injective _ (add_right_injective n),
  card_insert_of_notMem λh=>by have:=(hMs m0 h).2.1;omega]at this
 omega
lemma uY {U:Finset (Sym2 (Fin n))} {x y:Fin n} (hxy:s(x,y)∈U) (hne:x≠y) (hu:U.card=((aE U x).erase y).card+((aE U y).erase x).card+1):∀e∈U,x∈e\/y∈e:=by
 have hT:(aE U x).image (s(x,·))∪((aE U y).erase x).image (s(y,·))⊆U:=by
  intro e he;rcases mem_union.mp he with he|he<;>obtain⟨l,hl,rfl⟩:=mem_image.mp he;exacts[aD.mp hl,aD.mp (mem_of_mem_erase hl)]
 have hc:=card_union_of_disjoint (s:=(aE U x).image (s(x,·))) (t:=((aE U y).erase x).image (s(y,·))) (disjoint_left.mpr λe h1 h2=>by
   obtain⟨a,-,rfl⟩:=mem_image.mp h1;obtain⟨c,hc,e⟩:=mem_image.mp h2;rcases Sym2.eq_iff.mp e with⟨h,-⟩|⟨-,h⟩
   exacts[hne h.symm,(mem_erase.mp hc).1 h])
 rw[card_image_of_injective _ (λa c h=>Sym2.congr_right.mp h),card_image_of_injective _ (λa c h=>Sym2.congr_right.mp h),←card_erase_add_one (aD.mpr hxy)]at hc;intro e he;rw[←eq_of_subset_of_card_le hT (by omega)]at he;rcases mem_union.mp he with he|he<;>obtain⟨l,-,rfl⟩:=mem_image.mp he<;>simp
lemma tW:∀i j k:Fin 4,i≠j ->k≠i ->k≠j ->(0=i\/0=j\/0=k) ->(1=i\/1=j\/1=k) ->(3=i\/3=j\/3=k) ->(i=0/\j=1/\k=3)\/(i=1/\j=0/\k=3)\/(i=0/\j=3/\k=1)\/(i=3/\j=0/\k=1)\/(i=1/\j=3/\k=0)\/(i=3/\j=1/\k=0):=by
 intro i j k;fin_cases i<;>fin_cases j<;>fin_cases k<;>decide
lemma uG {K:Finset (Fin n)} {Q:ℕ ->Fin 2 ->Fin n ->Prop} (hK:∀a∈tops G C\centreless G C,∃b':Fin 2,∃p'∈K,side C a (1-b')={p'}/\Q a b' p') {a:ℕ} (ha:a∈tops G C) {s:Fin 2} {Zs:Finset (Fin n)} (hZ:Zs⊆orIn n C (opnd C a s)) (hZne:Zs.Nonempty) {p:Fin n} (hp:p∈orIn n C (opnd C a (1-s))):p∈K\/∃p'∈K,∀z∈Zs,z=p':=by
 obtain⟨z0,hz0⟩:=hZne;obtain⟨b',p',hp'K,hside,-⟩:=hK a (jO ha ⟨z0,hZ hz0⟩ ⟨p,hp⟩);simp only[side]at hside;rcases aS s b' with e|e<;>rw[e]at hside
 ·rw[hside,mem_singleton]at hp;exact Or.inl (hp▸hp'K)
 ·rw[bV]at hside;exact Or.inr ⟨p',hp'K,λz hz=>mem_singleton.mp (hside▸hZ hz)⟩
lemma sS (Z:cI G C q r b):∃Rc Ms Wg m0,sJ G C r Rc Ms Wg m0:=by
 have hA:=Z.1.1.1;obtain⟨hq,hr⟩:=b4 Z;obtain⟨m0,hM0,-,hr0,-,hne0⟩:=dR hA hq Z.2.1 Z.2.2.2;have hm0:m0<r:=by
  have:=(aX hr0).1;have:=aH hA (aA.mp hr).1 b;omega
 set DT:=(tops G C).filter λa=>∃B:Fin 2,OrReaches n C (opnd C a B) r;have hB:∀a,∃B:Fin 2,a∈DT ->OrReaches n C (opnd C a B) r:=λa=>if ha:a∈DT then(mem_filter.mp ha).2.imp λ_ h _=>h else⟨0,λh=>absurd h ha⟩;choose Bf hBf using hB;have huq:∀a∈tops G C,∀B,OrReaches n C (opnd C a B) r ->a∈DT/\Bf a=B:=λa ha B hrk=>have hD:a∈DT:=mem_filter.mpr ⟨ha,B,hrk⟩;⟨hD,(aS B (Bf a)).resolve_right λe=>vF Z ha hrk (e▸hBf a hD)⟩;set Dn:=DT.filter λa=>a∉centreless G C;have hm:∀a,∃m,a∈Dn ->aR n G C (n+m)/\m0<m/\OrReaches n C (opnd C a (Bf a)) m/\(orIn n C (n+m)).Nonempty/\∃B:Fin 2,orIn n C (opnd C m B)=∅/\OrReaches n C (opnd C m B) r:=λa=>by
  by_cases ha:a∈Dn
  ·obtain⟨haD,hac⟩:=mem_filter.mp ha;obtain⟨m,B,hm,hop,hwm,hne',he,hrJ⟩:=fE hA (aA.mp hr).2.1 (hBf a haD) (nonempty_iff_ne_empty.mpr λhe=>hac (c7 (mem_filter.mp haD).1 he));have:=d9 hA hm hop B hrJ;refine⟨m,λ_=>⟨⟨a7.mpr ⟨hm,hop⟩,⟨r,hr,this⟩,?_⟩,by have:=(aX this).1;omega,hwm,hne',B,he,hrJ⟩⟩;simp only[bF,bI,Nat.add_sub_cancel_left];fin_cases B;exacts[Or.inl he,Or.inr he]
  ·exact⟨0,λh=>absurd h ha⟩
 choose mf hmf using hm;refine⟨(DT.filter λa=>a∈centreless G C).image λa=>opnd C a (1-Bf a),Dn.image mf,λk=>(Dn.filter λa=>mf a=k).biUnion λa=>orIn n C (opnd C a (1-Bf a)),m0,hM0,hne0,card_image_le.trans (card_le_card λa ha=>(mem_filter.mp ha).2),λw hw=>?_,λm hm=>?_,λx=>⟨?_,?_⟩⟩
 ·obtain⟨a,ha,rfl⟩:=mem_image.mp hw;exact⟨a,(mem_filter.mp ha).2,Bf a,hBf a (mem_filter.mp ha).1,rfl⟩
 ·obtain⟨a0,ha0,rfl⟩:=mem_image.mp hm;obtain⟨h1,h2,-,⟨y,hy⟩,h6⟩:=hmf a0 ha0;refine⟨h1,h2,⟨y,λw hw=>?_⟩,⟨y,hy⟩,h6⟩;obtain⟨a,ha,hwa⟩:=mem_biUnion.mp hw;obtain⟨haDn,hma⟩:=mem_filter.mp ha;obtain⟨h1,h2⟩:=aV hA (mem_filter.mp (mem_filter.mp haDn).1).1 (Bf a) hwa (a6 hA (hmf a haDn).2.2.1 (hma▸hy));exact⟨h1.symm,λhu=>(mem_sdiff.mp hu).2 (by rwa[Sym2.eq_swap])⟩
 ·rintro⟨a,ha,B,hrk,hw⟩;obtain⟨haD,rfl⟩:=huq a ha B hrk;by_cases hac:a∈centreless G C
  ·exact Or.inl ⟨_,mem_image_of_mem _ (mem_filter.mpr ⟨haD,hac⟩),hw⟩
  ·exact Or.inr ⟨mf a,mem_image_of_mem _ (mem_filter.mpr ⟨haD,hac⟩),mem_biUnion.mpr ⟨a,mem_filter.mpr ⟨mem_filter.mpr ⟨haD,hac⟩,rfl⟩,hw⟩⟩
 ·rintro(⟨w,hw,hx⟩|⟨m,-,hx⟩)
  ·obtain⟨a,ha,rfl⟩:=mem_image.mp hw;have haD:=(mem_filter.mp ha).1;exact⟨a,(mem_filter.mp haD).1,Bf a,hBf a haD,hx⟩
  ·obtain⟨a',ha',hw'⟩:=mem_biUnion.mp hx;have haD:=(mem_filter.mp (mem_filter.mp ha').1).1;exact⟨a',(mem_filter.mp haD).1,Bf a',hBf a' haD,hw'⟩
theorem qB (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (Z:cI G C q r b) {U1:Finset (Sym2 (Fin n))} (hU1:U1⊆Ustar G C) (hU:∀u v,s(u,v)∈U1 ->gateVal n C r (pairInput u v)=true/\∃w,(w=u\/w=v)/\aC n G C r w) {u0 v0:Fin n} (he0:s(u0,v0)∈U1) (hq0:gateVal n C q (pairInput u0 v0)=false) {Rc Ms:Finset ℕ} {Wg:ℕ ->Finset (Fin n)} {m0:ℕ} (H:sJ G C r Rc Ms Wg m0) {Pr Xs:Finset ℕ} (hPr:∀h∈Pr,(∃w,b5 n G C (Ustar G C) w h)/\aB G U1 (orIn n C h)) (hXs:∀h∈Xs,h∈(orN G C\lam G C).image (n+·)/\(orIn n C (bF n C h)=∅\/orIn n C (bI n C h)=∅)/\h∉(insert m0 Ms).image (n+·)) (L:ℕ) (hM:∀Q:Finset (Fin n),(∀e∈U1,∃v∈Q,v∈e) ->2+2*(centreless G C).card+(orN G C\lam G C).card<=U1.card+Q.card+Pr.card+Xs.card+L) (hL:L=0\/L=1/\1<=(centreless G C).card/\(1<=Ms.card\/2<=(centreless G C).card)/\∀(B:Fin 2) (x y:Fin n) (cX:Bool),(∀v∈orIn n C (opnd C q B)∪orIn n C (opnd C r b),col v=cX) ->(∀v,aC n G C r v ->col v≠cX) ->x∈orIn n C (opnd C q B)∪orIn n C (opnd C r b) ->aC n G C r y ->s(x,y)∈U1 ->((aE U1 y).erase x).Nonempty ->(∀e∈U1,x∈e\/y∈e) ->False):False:=by
 obtain⟨hC,hT,h4,-,-,-,-⟩:=Z.1;have hA:=hC.1;obtain⟨hq,hr⟩:=b4 Z;obtain⟨hM0,-,hRc,-,hMs,hV⟩:=id H;have hrl:=(aA.mp hr).1;have hql:q<C.gates.length:=by have:=Z.1.2.2.2.1;omega
 have hE:U1⊆G.edgeFinset:=hU1.trans sdiff_subset;have hUr:∀u v,s(u,v)∈U1 ->gateVal n C r (pairInput u v)=true:=λu v h=>(hU u v h).1;have hUs:∀e∈U1,∃w∈e,aC n G C r w:=λe he=>by
  induction e using Sym2.ind with|_ u v=>
  obtain⟨-,w,hw,hu⟩:=hU u v he;exact⟨w,by rcases hw with rfl|rfl<;>simp,hu⟩
 set RV:List (ℕ⊕Finset (Fin n)⊕Fin 2):=Rc.toList.map (λw=>Sum.inl (gH n C w))++Ms.toList.map λm=>Sum.inr (Sum.inl (Wg m));have hRVl:RV.length=Rc.card+Ms.card:=by simp[RV]
 have hRVm:∀v∈RV,kW n G C U1 (λ_=>False) v:=λv hv=>by
  rcases List.mem_append.mp hv with hv|hv<;>obtain⟨a,ha,rfl⟩:=List.mem_map.mp hv;exacts[(gA hA a).2.2,bT hU1 subset_rfl (hMs a (mem_toList.mp ha)).2.2.1]
 have hRVf:∀x,(∃v∈RV,x∈pM n C q (opnd C r b) v)↔aC n G C r x:=λx=>by simp[RV,hV,pM,λa=>(gA hA a).2.1]
 have hRV0:RV≠[]:=λh=>by
  obtain⟨w,-,hw⟩:=hUs _ he0;obtain⟨v,hv,-⟩:=(hRVf w).mpr hw;simp[h]at hv
 have hlen:=List.length_pos_iff.mpr hRV0;have D1:=nL (uR hA hql (c:=opnd C r b) (by have:=aH hA hrl b;omega)) RV (Sum.inl 0);set J1:=eR (qQ n C) RV;set L1:=gG (qL n C q) RV (Sum.inl 0);set R1:=f5 (qN n C (opnd C r b)) RV (Sum.inl 0);set F1:=jS (pM n C q (opnd C r b)) RV;set rt:=sM n C (opnd C r (1-b)) RV;have e2:F1 (rt 2)=orIn n C (opnd C r (1-b)):=(gA hA _).2.1;have e3:∀x,x∈F1 (rt 3)↔aC n G C r x:=λx=>(jI _ _ hRV0).trans (hRVf x);have hH:∀x:Fin n ->Bool,(∀k,∃v∈F1 (rt k),x v=true) ->graphFun G ∅ x=true:=λx h=>uI Z (W:=F1 (rt 3)) (λw hw=>(e3 w).mp hw) x (h 0) (h 1) (by rw[←e2];exact h 2) (h 3);have hacc:∀e∈U1,∀k,∃v∈F1 (rt k),v∈e:=λe he k=>by
  induction e using Sym2.ind with|_ u v=>
  have hit:=n8 Z (hUr u v he);have pk:∀T:Finset (Fin n),(u∈T\/v∈T) ->∃w∈T,w∈s(u,v):=λT h=>h.elim (⟨u,·,by simp⟩) (⟨v,·,by simp⟩);obtain⟨w,hw,hwU⟩:=hUs _ he;fin_cases k
  ·exact pk _ (hit 0).1
  ·exact pk _ (hit 1).1
  ·exact pk _ (by show u∈F1 (rt 2)\/v∈F1 (rt 2);rw[e2];exact(hit 0).2)
  ·exact⟨w,(e3 w).mpr hwU,hw⟩
 have hleaf:∀k u,aM J1 L1 R1 (rt k) u ->¬J1 u ->aB G U1 (F1 u)\/(F1 u).card<=1:=λk u hu hnj=>by
  have h:=mG hA hRV0 hRVm k hu;rcases u with v|i
  ·exact vJ h hnj
  ·exact absurd h.2 hnj
 have cnt:∀(S:Finset ((ℕ⊕Finset (Fin n)⊕Fin 2)⊕ℕ)) (K:Fin 4 ->Prop) [DecidablePred K],(∀h∈S,J1 h/\∃k,K k/\aM J1 L1 R1 (rt k) h) ->S.card<=S.toLeft.toLeft.card+((if K 0 then 1 else 0)+(if K 1 then 1 else 0))+(if K 3 then RV.length-1 else 0):=λS K _ hS=>uN hA hRV0 hRVm S K hS
 have rho:∀S:Finset ((ℕ⊕Finset (Fin n)⊕Fin 2)⊕ℕ),(∀h∈S,J1 h/\¬aB G U1 (F1 h)) ->S.toLeft.toLeft.card+Pr.card+Xs.card+Ms.card+1<=(orN G C\lam G C).card:=λS hS=>kG hA H (λw hw=>by
   obtain⟨⟨hpJ,h1,h2⟩,hF⟩:=hS _ (mem_toLeft.mp (mem_toLeft.mp hw))
   exact⟨w,j3 hA hpJ (by rw[(aJ hA w hpJ).2.2];exact h1.mono subset_union_left) (λhf=>hF (bT hU1 subset_rfl hf)),hF,h1,h2, .refl⟩) hPr hXs
 by_cases hcv:∃y,∀e∈U1,y∈e
 ·obtain⟨y,hy⟩:=hcv;have hM':=hM {y} λe he=>⟨y,by simp,hy e he⟩;obtain⟨k,P,hP,hc⟩:=mP col hcol h4 D1 rt hH _ hE hacc hleaf y hy ⟨_,he0⟩;have h1:=cnt P (λk'=>k'=k) λh hh=>⟨(hP h hh).1,k,rfl,(hP h hh).2.1⟩;have h2:=rho P λh hh=>⟨(hP h hh).1,(hP h hh).2.2⟩;rw[card_singleton]at hM';fin_cases k<;>simp at h1<;>omega
 push Not at hcv;obtain⟨Q,hQ2,hQ⟩:=gY col hcol h4 _ hH _ hE hacc;have hM':=hM Q hQ;by_cases hg:(centreless G C).card=0/\Ms.card=1
 ·obtain⟨m,hm⟩:=card_eq_one.mp hg.2;have hmM:m∈Ms:=hm▸mem_singleton_self m;have hRc0:Rc=∅:=card_eq_zero.mp (by omega);have hWf:=bT hU1 subset_rfl (hMs m hmM).2.2.1;have hWs:∀w∈Wg m,aC n G C r w:=λw hw=>(hV w).mpr (Or.inr ⟨m,hmM,hw⟩);have hWc:∀e∈U1,∃w∈Wg m,w∈e:=λe he=>by
   obtain⟨w,hw,hwU⟩:=hUs e he;obtain⟨w',hw',-⟩|⟨m',hm',hwm⟩:=(hV w).mp hwU
   ·simp[hRc0]at hw'
   ·rw[hm,mem_singleton]at hm';exact⟨w,hm'▸hwm,hw⟩
  have hk0:L=0:=by rcases hL with h|⟨h,h',-⟩<;>omega
  generalize Wg m=W at hWf hWs hWc
  have hCD:=kZ Z;obtain⟨z,hz⟩:=id hWf;obtain⟨cW,hcW⟩:=aU col hcol hWf;have adj:∀{x y:Fin n},s(x,y)∈U1 ->G.Adj x y:=λh=>by simpa using hE h
  have ind:∀v∈W,∀w∈W,¬G.Adj v w:=λv hv w hw h=>hcol v w h ((hcW v hv).trans (hcW w hw).symm);have rad:∀v∈W,∀w,gateVal n C r (pairInput v w)=true ->G.Adj v w:=λv hv w h=>(aT v w).mp (bH hA (hWs v hv) _ h (by simp[pairInput]));have c4:∀v∈W,∀v'∈W,v≠v' ->∀l,s(v,l)∈U1 ->G.Adj v' l ->False:=λv hv v' hv' hvv l hl hl'=>by
    have:=aQ h4 hvv (hz v hv).1.symm (hz v' hv').1.symm (adj hl) hl';subst this;exact(hz v hv).2 (by rwa[Sym2.eq_swap])
  have dec:∀e∈U1,∃v∈W,∃l,e=s(v,l):=λe he=>let ⟨w,hw,hwe⟩:=hWc e he;⟨w,hw,Sym2.mem_iff_exists.mp hwe⟩;obtain⟨p,hpW,l1,he1⟩:=dec _ he0;have hp1:s(p,l1)∈U1:=he1▸he0;obtain⟨e2,he2,hpe2⟩:=hcv p;obtain⟨q',hqW,l2,rfl⟩:=dec _ he2;have hpq:p≠q':=λh=>hpe2 (h▸Sym2.mem_mk_left _ _);have hcov:∀e∈U1,p∈e\/q'∈e:=λe he=>by
   by_contra! hc;obtain⟨v3,hv3,l3,rfl⟩:=dec e he;have hp3:p≠v3:=λh=>hc.1 (h▸Sym2.mem_mk_left _ _);have hq3:q'≠v3:=λh=>hc.2 (h▸Sym2.mem_mk_left _ _);have hx:∀i:Fin 3,![p,q',v3] i∈W:=λi=>by fin_cases i;exacts[hpW,hqW,hv3]
   have hm':∀i:Fin 3,s(![p,q',v3] i,![l1,l2,l3] i)∈U1:=λi=>by
    fin_cases i;exacts[hp1,he2,he]
   refine p4 col hcol h4 ![orIn n C (opnd C q 0)∪orIn n C (opnd C r b),orIn n C (opnd C q 1)∪orIn n C (opnd C r b),orIn n C (opnd C r (1-b)),W] (λx h=>uI Z hWs x (h 0) (h 1) (h 2) (h 3)) ![p,q',v3] ![l1,l2,l3] (λi=>adj (hm' i)) (λi k=>?_) λi j hij=>?_
   ·have hh:=n8 Z (hUr _ _ (hm' i));obtain⟨w,hw,hwe⟩:=hWc _ (hm' i);fin_cases k;exacts[(hh 0).1,(hh 1).1,(hh 0).2,by rcases Sym2.mem_iff.mp hwe with rfl|rfl;exacts[Or.inl hw,Or.inr hw]]
   ·have hxx: ![p,q',v3] i≠![p,q',v3] j:=by
     fin_cases i<;>fin_cases j<;>first|exact absurd rfl hij|simp[hpq,hp3,hq3,hpq.symm,hp3.symm,hq3.symm]
    refine⟨hxx,λe=>ind _ (hx j) _ (hx i) (by rw[e];exact adj (hm' j)),λe=>hxx ?_⟩;by_contra hne;exact c4 _ (hx i) _ (hx j) hne _ (hm' i) (by rw[e];exact adj (hm' j))
  have hM:=hM {p,q'} λe he=>(hcov e he).elim (⟨p,by simp,·⟩) (⟨q',by simp,·⟩);rw[card_pair hpq]at hM
  have hu:U1.card<=(aE U1 p).card+(aE U1 q').card:=(card_le_card (t:=(aE U1 p).image (s(p,·))∪(aE U1 q').image (s(q',·))) λe he=>by
     rcases hcov e he with h|h<;>obtain⟨x,rfl⟩:=Sym2.mem_iff_exists.mp h
     exacts[mem_union_left _ (mem_image_of_mem _ (aD.mpr he)),mem_union_right _ (mem_image_of_mem _ (aD.mpr he))]).trans
    ((card_union_le _ _).trans (add_le_add card_image_le card_image_le))
  have hr1:=(dK Z p l1).mp (hUr _ _ hp1);rw[dT he1]at hq0;have hc1:=hr1.1.resolve_left (by simp[hq0]);have hxW:gateVal n C r (λv=>decide (v∈W))≠true:=λh=>by
   obtain⟨a,a',haa,ha,ha'⟩:=(dJ _).mp (bH hA (hWs p hpW) _ h (by simpa using hpW));exact ind a (by simpa using ha) a' (by simpa using ha') haa
  obtain⟨d0,hd0,hd0W⟩:∃d∈orIn n C (opnd C r (1-b)),d∈W:=by
   by_contra! hDW;have hpC:=hc1.resolve_right λh=>disjoint_left.mp hCD h (hr1.2.resolve_left λh=>hDW p h hpW);exact c4 q' hqW p hpW hpq.symm l2 he2 (rad p hpW l2 ((dK Z p l2).mpr ⟨Or.inr (Or.inl hpC),Or.inr (((dK Z q' l2).mp (hUr _ _ he2)).2.resolve_left λh=>hDW q' h hqW)⟩))
  have hCW:∀c∈orIn n C (opnd C r b),c∉W:=λc hc hcW'=>hxW ((dU Z _).mpr ⟨Or.inr ⟨c,hc,by simpa using hcW'⟩,d0,hd0,by simpa using hd0W⟩);obtain⟨B,hB⟩:∃B:Fin 2,∀a∈orIn n C (opnd C q B),a∉W:=by
   by_contra! hall;obtain⟨a0,ha0,ha0W⟩:=hall 0;obtain⟨a1,ha1,ha1W⟩:=hall 1;exact hxW ((dU Z _).mpr ⟨Or.inl ((bP Z.1 0 _).mpr ⟨⟨a0,ha0,by simpa using ha0W⟩,a1,ha1,by simpa using ha1W⟩),d0,hd0,by simpa using hd0W⟩)
  have hpC:p∉orIn n C (opnd C r b):=λh=>hCW p h hpW;have hl1C:=hc1.resolve_left hpC;have hpD:=hr1.2.resolve_right λh=>disjoint_left.mp hCD hl1C h;have hqD:q'∉orIn n C (opnd C r (1-b)):=λh=>c4 p hpW q' hqW hpq l1 hp1 (rad q' hqW l1 ((dK Z q' l1).mpr ⟨Or.inr (Or.inr hl1C),Or.inl h⟩));have hLq:∀l∈aE U1 q',l∈orIn n C (opnd C q B)/\l∈orIn n C (opnd C r (1-b)):=λl hl=>by
   obtain⟨h1,h2⟩:=(dK Z q' l).mp (hUr _ _ (aD.mp hl));have hlD:=h2.resolve_left hqD;exact⟨((rJ Z B q' l).mp (h1.resolve_right (not_or.mpr ⟨λh=>hCW q' h hqW,λh=>disjoint_left.mp hCD h hlD⟩))).1.resolve_left λh=>hB q' h hqW,hlD⟩
  have hpA:p∉orIn n C (opnd C q (1-B)):=λh=>by
   obtain⟨hA2,hD2⟩:=hLq l2 (aD.mpr he2);exact c4 q' hqW p hpW hpq.symm l2 he2 (rad p hpW l2 ((dK Z p l2).mpr ⟨Or.inl ((rJ Z B p l2).mpr ⟨Or.inr hA2,Or.inl h⟩),Or.inr hD2⟩))
  have hLp:∀l∈aE U1 p,l∈orIn n C (opnd C r b):=λl hl=>by
   rcases ((dK Z p l).mp (hUr _ _ (aD.mp hl))).1 with h|h|h
   ·obtain⟨h3,h5⟩:=(rJ Z B p l).mp h;exact absurd (h5.resolve_left hpA) (disjoint_left.mp (cJ Z.1 B) (h3.resolve_left λh=>hB p h hpW))
   ·exact absurd h hpC
   ·exact h
  have hqcol:∀l∈aE U1 q',col l≠cW:=λl hl h=>hcol q' l (adj (aD.mp hl)) ((hcW q' hqW).trans h.symm);obtain⟨PD,hPD,cD⟩:=fC hA hU1 (opnd C r (1-b)) (insert p (aE U1 q')) λW' hW'=>by
   obtain⟨c',hc'⟩:=aU col hcol hW';have s1:=aF h4 hE hW' q';refine card_le_one.mpr λa ha a' ha'=>?_;rw[mem_inter,mem_insert]at ha ha';rcases ha with⟨ha,rfl|ha2⟩<;>rcases ha' with⟨ha',rfl|ha2'⟩
   ·rfl
   ·exact absurd (((hc' _ ha').trans (hc' _ ha).symm).trans (hcW _ hpW)) (hqcol _ ha2')
   ·exact absurd (((hc' _ ha).trans (hc' _ ha').symm).trans (hcW _ hpW)) (hqcol _ ha2)
   ·exact card_le_one.mp s1 a (mem_inter.mpr ⟨ha,ha2⟩) a' (mem_inter.mpr ⟨ha',ha2'⟩)
  rw[inter_eq_right.mpr (insert_subset hpD λl hl=>(hLq l hl).2),card_insert_of_notMem λh=>ind q' hqW p hpW (adj (aD.mp h))]at cD;obtain⟨PC,hPC,cC⟩:=fC hA hU1 (opnd C r b) (aE U1 p) λW' hW'=>aF h4 hE hW' p;rw[inter_eq_right.mpr hLp]at cC;have hρ:=kG hA H (Pp:=PD∪PC) (λh hh=>(mem_union.mp hh).elim (⟨_,hPD h ·⟩) (⟨_,hPC h ·⟩)) hPr hXs
  rw[card_union_of_disjoint (disjoint_left.mpr λh h1 h2=>by
   obtain⟨v,hv⟩:=gW hA (hPD h h1)
   exact disjoint_left.mp hCD (aK (aJ hA) (hPC h h2).2.2.2.2 hv) (aK (aJ hA) (hPD h h1).2.2.2.2 hv))]at hρ
  omega
 have hg2:1<=(centreless G C).card\/2<=Ms.card:=by omega
 obtain⟨c0,hc0'⟩:=Z.2.2.2;have hc00:c0∈F1 (rt 0):=mem_union_right _ hc0';have hc01:c0∈F1 (rt 1):=mem_union_right _ hc0';have X:∀I κ':Fin 4,(I=0/\κ'=1\/I=1/\κ'=0) ->∀x y:Fin n,∀cX:Bool,(∀v∈F1 (rt I),col v=cX) ->(∀v∈F1 (rt 3),col v≠cX) ->x∈F1 (rt I) ->x∈F1 (rt κ') ->y∈F1 (rt 3) ->s(x,y)∈U1 ->((aE U1 x).erase y).Nonempty ->((aE U1 y).erase x).Nonempty ->U1.card=((aE U1 x).erase y).card+((aE U1 y).erase x).card+1 ->(centreless G C).card=0\/L=1 ->False:=by
  intro I κ' hIL x y cX hcX hcV hxI hxL hy hxy hLx hLy hu hX;rcases hX with hX|hX
  swap
  ·rcases hL with h|⟨-,-,-,HX⟩
   ·omega
   have hxy':x≠y:=λh=>by have:=hE hxy;simp[h]at this
   rcases hIL with⟨rfl,rfl⟩|⟨rfl,rfl⟩<;>exact HX _ x y cX hcX (λv hv=>hcV v ((e3 v).mpr hv)) hxI ((e3 y).mp hy) hxy hLy (uY hxy hxy' hu)
  have hRc0:Rc=∅:=card_eq_zero.mp (by omega);have hxC:x∈orIn n C (opnd C r b):=by
   have d:=disjoint_left.mp (cJ Z.1 0);rcases hIL with⟨rfl,rfl⟩|⟨rfl,rfl⟩<;>rcases mem_union.mp hxI with h|h<;>rcases mem_union.mp hxL with h'|h'<;>first|assumption|exact(d h h').elim|exact(d h' h).elim
  have hD:∀w,s(x,w)∈U1 ->w∈F1 (rt 2):=λw hw=>by
   rw[e2];exact(n8 Z (hUr x w hw) 0).2.resolve_left (disjoint_left.mp (kZ Z) hxC)
  obtain⟨l,hl⟩:=hLx;obtain⟨hly,hlx⟩:=mem_erase.mp hl;have hyx:y∈aE U1 x:=aD.mpr hxy;have hxy':x∈aE U1 y:=aD.mpr (by rwa[Sym2.eq_swap]);obtain⟨E,hJE,hRE,hFE,hyE,-⟩:=eU D1 (aB G U1) (rt 2) y l (Ne.symm hly) (hD y hxy) (hD l (aD.mp hlx)) (λW hW h=>hly (card_le_one.mp (aF h4 hE hW x) l (mem_inter.mpr ⟨h.2,hlx⟩) y (mem_inter.mpr ⟨h.1,hyx⟩))) (hleaf 2)
  obtain⟨P',hP',hc'⟩:=d8 D1 (aB G U1) (insert x (aE U1 y)) (rt I) (insert_subset hxI λw hw=>by
    obtain⟨v,hv,hve⟩:=hacc _ (aD.mp hw) I;rcases Sym2.mem_iff.mp hve with rfl|rfl
    exacts[absurd (hcX v hv) (hcV v hy),hv])
   (λW hW=>a4 h4 hE hW y x (by simpa using hE (aD.mp hxy')))
   (hleaf I)
  rw[insert_eq_of_mem hxy']at hc';have hEP:E∉P':=λh=>hcV y hy (hcX y (aK D1 (hP' E h).2.1 hyE));have h1:=cnt (insert E P') (λk=>k=I\/k=2) λh hh=>by
   rcases mem_insert.mp hh with rfl|hh;exacts[⟨hJE,2,Or.inr rfl,hRE⟩,⟨(hP' h hh).1,I,Or.inl rfl,(hP' h hh).2.1⟩]
  have h2:=rho (insert E P') λh hh=>by
   rcases mem_insert.mp hh with rfl|hh;exacts[⟨hJE,hFE⟩,⟨(hP' h hh).1,(hP' h hh).2.2.1⟩]
  rw[card_insert_of_notMem hEP]at h1;have hg:(aE U1 x).card<=Ms.card:=by
   refine(card_le_card (t:=Ms.biUnion λm=>Wg m∩aE U1 x) λw hw=>?_).trans (card_biUnion_le.trans ((sum_le_card_nsmul Ms _ 1 λm hm=>aF h4 hE (bT hU1 subset_rfl (hMs m hm).2.2.1) x).trans (by simp)));obtain⟨v,hv,hve⟩:=hacc _ (aD.mp hw) 3;rcases Sym2.mem_iff.mp hve with rfl|rfl
   ·exact absurd (hcX v hxI) (hcV v hv)
   obtain⟨w',hw',-⟩|⟨m,hm,hwm⟩:=(hV v).mp ((e3 v).mp hv)
   ·simp[hRc0]at hw'
   ·exact mem_biUnion.mpr ⟨m,hm,mem_inter.mpr ⟨hwm,hw⟩⟩
  have c1:=card_erase_add_one hyx;have c2:=card_erase_add_one hxy';rcases hL with h|⟨h,h',-⟩<;>rcases hIL with⟨rfl,rfl⟩|⟨rfl,rfl⟩<;>simp at h1<;>omega
 rcases kM col hcol h4 D1 rt hH _ hE hacc hleaf hcv with⟨k1,k2,P,hP,hc⟩|⟨i,j,k,x,y,hij,hki,hkj,hci,hcj,hxi,hyj,hxy,hLx,hLy,hu,⟨P,hP,hc⟩,h0,hJ0,hF0,hR0,hn1,hn2,hx0,hy0⟩
 ·have h1:=cnt P (λk'=>k'=k1\/k'=k2) λh hh=>⟨(hP h hh).1,(hP h hh).2.2.elim (⟨k1,Or.inl rfl,·⟩) (⟨k2,Or.inr rfl,·⟩)⟩;have h2:=rho P λh hh=>⟨(hP h hh).1,(hP h hh).2.1⟩;rcases hL with h|⟨h,h',h'',-⟩<;>fin_cases k1<;>fin_cases k2<;>simp at h1<;>omega
 have h0P:h0∉P:=λh=>(hP h0 h).2.2.elim hn1 hn2;have h1:=cnt (insert h0 P) (λk'=>k'=i\/k'=j\/k'=k) λh hh=>by
  rcases mem_insert.mp hh with rfl|hh
  ·exact⟨hJ0,k,Or.inr (Or.inr rfl),hR0⟩
  ·exact⟨(hP h hh).1,(hP h hh).2.2.elim (⟨i,Or.inl rfl,·⟩) (⟨j,Or.inr (Or.inl rfl),·⟩)⟩
 have h2:=rho (insert h0 P) λh hh=>by
  rcases mem_insert.mp hh with rfl|hh;exacts[⟨hJ0,hF0⟩,⟨(hP h hh).1,(hP h hh).2.1⟩]
 rw[card_insert_of_notMem h0P]at h1;by_cases hK:(0=i\/0=j\/0=k)/\(1=i\/1=j\/1=k)/\(3=i\/3=j\/3=k)
 ·have hX:(centreless G C).card=0\/L=1:=by
   by_contra! hX;rcases hL with h|h
   ·split_ifs at h1<;>omega
   ·exact hX.2 h.1
  have hx0':=aK D1 hR0 hx0;have hy0':=aK D1 hR0 hy0;rcases tW i j k hij hki hkj hK.1 hK.2.1 hK.2.2 with⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
  ·exact absurd (hci c0 hc00) (by rw[hcj c0 hc01];decide)
  ·exact absurd (hci c0 hc01) (by rw[hcj c0 hc00];decide)
  ·exact X 0 1 (Or.inl ⟨rfl,rfl⟩) x y false hci (λv hv=>by rw[hcj v hv];decide) hxi hx0' hyj hxy hLx hLy hu hX
  ·exact X 0 1 (Or.inl ⟨rfl,rfl⟩) y x true hcj (λv hv=>by rw[hci v hv];decide) hyj hy0' hxi (by rwa[Sym2.eq_swap]) hLy hLx (by omega) hX
  ·exact X 1 0 (Or.inr ⟨rfl,rfl⟩) x y false hci (λv hv=>by rw[hcj v hv];decide) hxi hx0' hyj hxy hLx hLy hu hX
  ·exact X 1 0 (Or.inr ⟨rfl,rfl⟩) y x true hcj (λv hv=>by rw[hci v hv];decide) hyj hy0' hxi (by rwa[Sym2.eq_swap]) hLy hLx (by omega) hX
 ·simp only[not_and_or]at hK;rcases hL with h|⟨h,h',h'',-⟩<;>rcases hK with hK|hK|hK<;>simp only[hK,↓reduceIte]at h1<;>split_ifs at h1<;>omega
lemma uC (hR1:cM) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (Z:cI G C q r b) {U1:Finset (Sym2 (Fin n))} (hx:∀u v,s(u,v)∈Ustar G C ->s(u,v)∉U1 ->wireVal n (aG n C r) C.output (pairInput u v)=true):∃u0 v0,s(u0,v0)∈U1/\gateVal n C q (pairInput u0 v0)=false:=by
 by_contra hno;simp only[not_exists,not_and,Bool.not_eq_false]at hno;refine uH hR1 col hcol Z λu v huv=>?_;cases hk:wireVal n (aG n C r) C.output (pairInput u v)
 ·obtain⟨hrx,hs⟩:=jF Z (b4 Z).2 huv hk;by_cases hi:s(u,v)∈U1
  ·exact Or.inr ⟨hno u v hi,((dU Z _).mp hrx).2⟩
  ·rw[hx u v hs hi]at hk;cases hk
 ·exact Or.inl rfl
theorem nG (hR1:cM) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (Z:cI G C q r b) (hU:∀u v,s(u,v)∈Ustar G C ->gateVal n C r (pairInput u v)=true/\∃w,(w=u\/w=v)/\aC n G C r w):False:=by
 obtain⟨u0,v0,he0,hq0⟩:=uC hR1 col hcol Z (U1:=Ustar G C) λ_ _ h h'=>(h' h).elim;obtain⟨Rc,Ms,Wg,m0,H⟩:=sS Z;exact qB col hcol Z subset_rfl hU he0 hq0 H (Pr:=∅) (by simp) (Xs:=∅) (by simp) 0 (λQ hQ=>by have:=lG Z.1 Q hQ;rw[card_empty];omega) (Or.inl rfl)
end F
section W
variable {q r:ℕ} {b o:Fin 2} {p:Fin n} {col:Fin n ->Bool}
lemma sI (W:n6 G C q r b o p col) (hv:v∈orIn n C (opnd C q o)) (hu:aC n G C q v):v=p:=by
 obtain⟨-,-,Z,-,hpA,hpU,-,-⟩:=W;exact bC Z.1.2.2.1 (Z.1.2.2.2.2.2.2 _) (f8 Z.1 hv (bH Z.1.1.1 hu)) (f8 Z.1 hpA (bH Z.1.1.1 hpU))
lemma vE (W:n6 G C q r b o p col) (he:s(u,v)∈Ustar G C):(∃t∈orIn n C (opnd C q (1-o)),s(u,v)=s(p,t))\/(gateVal n C r (pairInput u v)=true/\∃w,(w=u\/w=v)/\aC n G C r w):=by
 have Z:=W.2.2.1;refine(uD Z W.2.2.2.1 he).imp_left λ⟨hx,w,hw,hu⟩=>?_;rcases l8 Z.1 o hx hw with h|h
 ·obtain rfl:=sI W h hu;obtain⟨-,⟨t,ht,hxt⟩⟩:=(bP Z.1 o _).mp hx;exact⟨t,ht,fP hw (aW hxt) λe=>disjoint_left.mp (cJ Z.1 o) h (e▸ht)⟩
 ·exact(W.2.2.2.2.2.2.2 w h hu).elim
lemma d5 (W:n6 G C q r b o p col) (he:s(u,v)∈bE G C q o p):gateVal n C r (pairInput u v)=true/\∃w,(w=u\/w=v)/\aC n G C r w:=(vE W (mem_sdiff.mp he).1).resolve_left λ⟨t,ht,e⟩=>(mem_sdiff.mp he).2 (mem_image.mpr ⟨t,ht,e.symm⟩)
lemma pH (W:n6 G C q r b o p col) (pref:Fin n ->Prop) (Y:Finset (Fin n)) (hY:∀e∈bE G C q o p,∃v∈Y,v∈e):∃K:Finset (Fin n),(∀a∈tops G C\centreless G C,∃b':Fin 2,∃p'∈K,side C a (1-b')={p'}/\((∃b'':Fin 2,∃p'',side C a (1-b'')={p''}/\pref p'') ->pref p'))/\2+2*(centreless G C).card+(orN G C\lam G C).card<=((orIn n C (opnd C q (1-o))).filter λt=>s(p,t)∈Ustar G C).card+(bE G C q o p).card+(insert p Y\K).card:=by
 obtain⟨hC,hT,h4,hqr,hJ,-,-⟩:=W.2.2.1.1;have hs:∀e∈Ustar G C,e∈((orIn n C (opnd C q (1-o))).filter λt=>s(p,t)∈Ustar G C).image (s(p,·))∪bE G C q o p:=λe he=>by
  by_cases hi:e∈(orIn n C (opnd C q (1-o))).image λt=>s(p,t)
  ·obtain⟨t,ht,rfl⟩:=mem_image.mp hi;exact mem_union_left _ (mem_image_of_mem _ (mem_filter.mpr ⟨ht,he⟩))
  ·exact mem_union_right _ (mem_sdiff.mpr ⟨he,hi⟩)
 obtain⟨K,-,-,hK,h⟩:=gJ h4 hC hT (by rw[hJ,card_pair hqr.ne]) pref (insert p Y) λe he=>by
   rcases mem_union.mp (hs e he)with hi|hi
   ·obtain⟨t,-,rfl⟩:=mem_image.mp hi;exact⟨p,by simp,by simp⟩
   ·obtain⟨v,hv,hve⟩:=hY e hi;exact⟨v,mem_insert_of_mem hv,hve⟩
 have:=(card_le_card hs).trans ((card_union_le _ _).trans (Nat.add_le_add_right card_image_le _));exact⟨K,hK,by omega⟩
lemma tR (W:n6 G C q r b o p col):∃P:Finset ℕ,(∀h∈P,(∃w,b5 n G C (Ustar G C) w h)/\aB G (bE G C q o p) (orIn n C h))/\((orIn n C (opnd C q (1-o))).filter λt=>s(p,t)∈Ustar G C).card<=P.card+1/\((∃t∈orIn n C (opnd C q (1-o)),s(p,t)∉Ustar G C) ->((orIn n C (opnd C q (1-o))).filter λt=>s(p,t)∈Ustar G C).card<=P.card):=by
 obtain⟨-,-,Z,-,-,-,hpB,-⟩:=W;have hA:=Z.1.1.1;set B0:=(orIn n C (opnd C q (1-o))).filter λt=>s(p,t)∈Ustar G C;have key:∀S⊆orIn n C (opnd C q (1-o)),(∀t∈S,t∉B0 ->∀t'∈S,t'∉B0 ->t=t') ->∃P:Finset ℕ,(∀h∈P,(∃w,b5 n G C (Ustar G C) w h)/\aB G (bE G C q o p) (orIn n C h))/\S.card<=P.card+1:=λS hSB hS1=>by
  obtain⟨P,hP,hc⟩:=fC (G:=G) hA subset_rfl (opnd C q (1-o)) S λW' ⟨z,hz⟩=>card_le_one.mpr λt1 h1 t2 h2=>by
    obtain⟨h1W,h1S⟩:=mem_inter.mp h1;obtain⟨h2W,h2S⟩:=mem_inter.mp h2;by_cases hzp:z=p
    ·subst hzp;exact hS1 t1 h1S (λh=>(hz t1 h1W).2 (mem_filter.mp h).2) t2 h2S λh=>(hz t2 h2W).2 (mem_filter.mp h).2
    ·exact aQ Z.1.2.2.1 hzp (hz t1 h1W).1 (hpB t1 (hSB h1S)) (hz t2 h2W).1 (hpB t2 (hSB h2S))
  rw[inter_eq_right.mpr hSB]at hc;exact⟨P,λh hh=>⟨⟨_,hP h hh⟩,pA (Ustar G C) p hpB (aK (aJ hA) (hP h hh).2.2.2.2)⟩,hc⟩
 by_cases hex:∃t∈orIn n C (opnd C q (1-o)),s(p,t)∉Ustar G C
 ·obtain⟨t',ht',hn'⟩:=hex;obtain⟨P,hP,hc⟩:=key (insert t' B0) (insert_subset ht' (filter_subset _ _)) λt ht hn t2 ht2 hn2=>by
    rcases mem_insert.mp ht with rfl|h
    ·rcases mem_insert.mp ht2 with rfl|h2;exacts[rfl,(hn2 h2).elim]
    ·exact(hn h).elim
  rw[card_insert_of_notMem (show t'∉B0 from λh=>hn' (mem_filter.mp h).2)]at hc;exact⟨P,hP,by omega,λ_=>by omega⟩
 ·obtain⟨P,hP,hc⟩:=key B0 (filter_subset _ _) λt ht hn=>(hn ht).elim;exact⟨P,hP,hc,λh=>(hex h).elim⟩
lemma mV {D:Circuit} {t:ℕ} (hD:fY C D t) (h1:(gateAt C t).op=GateOp.and) (h2:(gateAt D t).op=GateOp.and) (g:ℕ):∀w,OrReaches n D w g↔OrReaches n C w g:=by
 intro w
 induction w using Nat.strong_induction_on with
 |_ w ih=>
  rcases Nat.lt_or_ge w n with hn|hn
  ·exact⟨λh=>absurd h.1 (by omega),λh=>absurd h.1 (by omega)⟩
  obtain⟨k,rfl⟩:∃k,w=n+k:=⟨w-n,by omega⟩;rw[bD,bD,hD.1];refine and_congr_right λhk=>or_congr_right ?_;by_cases hkt:k=t
  ·subst hkt;rw[h1,h2];simp
  ·rw[hD.2 k hk hkt];exact and_congr_right λ_=>exists_congr λi=>and_congr_right λ_=>and_congr_right λhi=>ih i (by omega)
lemma qJ {D:Circuit} {t:ℕ} (hD:fY C D t) (h1:(gateAt C t).op=GateOp.and) (h2:(gateAt D t).op=GateOp.and) (w:ℕ):orIn n D w=orIn n C w:=by
 ext v;simp only[dV,hD.1,mV hD h1 h2];refine or_congr Iff.rfl (exists_congr λk=>and_congr_right λhk=>and_congr_right λ_=>?_);by_cases hkt:k=t
 ·subst hkt;rw[h1,h2];simp
 ·rw[hD.2 k hk hkt]
lemma vI (W:n6 G C q r b o p col):∃u0 v0,s(u0,v0)∈bE G C q o p/\gateVal n C q (pairInput u0 v0)=false:=by
 obtain⟨hR1,hcol,Z,-,hpA,⟨a,ha,s,hras,hpa⟩,-,-⟩:=W;obtain⟨hC,hT,-,hqr,-,-,-⟩:=Z.1;have hr:=(b4 Z).2;refine uC hR1 col hcol Z λu v hU hi=>?_;obtain⟨t,ht,he⟩:=mem_image.mp (not_not.mp λh=>hi (mem_sdiff.mpr ⟨hU,h⟩));rw[←dT he];exact fW hC hT hr ha λB=>by
  rcases aS s B with rfl|rfl
  ·exact fI hC.1 hr (Or.inr ⟨hqr.ne,λhc=>absurd (aP hc) (by omega),hras,rE Z hpA ht⟩)
  ·exact fI hC.1 (k:=q) hr (Or.inl ⟨p,hpa,by simp[pairInput]⟩)
lemma vH (W:n6 G C q r b o p col):∃t∈orIn n C (opnd C q (1-o)),s(p,t)∈Ustar G C/\¬(gateVal n C r (pairInput p t)=true/\(aC n G C r p\/aC n G C r t)):=by
 by_contra hno;refine nG W.1 col W.2.1 W.2.2.1 λu v he=>?_;rcases vE W he with⟨t,ht,e⟩|h
 ·obtain⟨hrx,hu⟩:=not_not.mp λh=>hno ⟨t,ht,e▸he,h⟩;rw[dT e];exact⟨hrx,hu.elim (⟨p,Sym2.mem_iff.mp (e▸Sym2.mem_mk_left p t),·⟩) (⟨t,Sym2.mem_iff.mp (e▸Sym2.mem_mk_right p t),·⟩)⟩
 ·exact h
lemma nR (W:n6 G C q r b o p col) {y x:Fin n} {w:ℕ} (hy:∀e∈bE G C q o p,y∈e) (hl:∀l,s(y,l)∈bE G C q o p ->l∈orIn n C w) (hx:x∈orIn n C w) (hyx:G.Adj y x):∃Pm:Finset ℕ,(∀h∈Pm,∃w,b5 n G C (bE G C q o p) w h)/\(bE G C q o p).card+(if s(y,x)∈bE G C q o p then 0 else 1)<=Pm.card+1:=by
 obtain⟨P,hP,hc⟩:=fC W.2.2.1.1.1.1 (sdiff_subset:bE G C q o p⊆Ustar G C) w (insert x (aE (bE G C q o p) y)) λW' hW'=>a4 W.2.2.1.1.2.2.1 (sdiff_subset.trans sdiff_subset) hW' y x hyx;rw[inter_eq_right.mpr (insert_subset hx λl h=>hl l (aD.mp h))]at hc;refine⟨P,λh hh=>⟨_,hP h hh⟩,?_⟩;have hu:=uF hy;split_ifs with h
 ·exact hu.trans ((card_le_card (subset_insert _ _)).trans hc)
 ·rw[card_insert_of_notMem λh'=>h (aD.mp h')]at hc;omega
end W
section F
variable {q r:ℕ} {b:Fin 2}
lemma lN (K:Finset (Fin n)) (x y:Fin n):(insert x {y}\K).card<=2/\(x∈K\/y∈K ->(insert x {y}\K).card<=1):=by
 have h1:=eG K {y} x;have h2:=gX K y;refine⟨by split_ifs at h1 h2<;>omega,λh=>?_⟩;rcases h with h|h<;>simp only[h,↓reduceIte]at h1 h2<;>split_ifs at h1 h2<;>omega
lemma t9 (H:sJ G C r Rc Ms Wg m0) (hw:aC n G C r w):1<=(centreless G C).card+Ms.card:=by
 rcases (H.2.2.2.2.2 w).mp hw with⟨w',hw',-⟩|⟨m',hm',-⟩
 ·have:=H.2.2.1;have:=card_pos.mpr ⟨w',hw'⟩;omega
 ·have:=card_pos.mpr ⟨m',hm'⟩;omega
lemma t8 (Z:cI G C q r b) (H:sJ G C r Rc Ms Wg m0) (hk:k<C.gates.length) (hop:(gateAt C k).op=GateOp.or) (hrk:OrReaches n C (n+k) q) (he:∃B:Fin 2,orIn n C (opnd C k B)=∅) (hm0:k≠m0) (hkq:orIn n C (n+k)=∅\/n+q∈(gateAt C k).inputs):n+k∈(orN G C\lam G C).image (n+·)/\(orIn n C (bF n C (n+k))=∅\/orIn n C (bI n C (n+k))=∅)/\n+k∉(insert m0 Ms).image (n+·):=by
 have hA:=Z.1.1.1;obtain⟨hq,hr⟩:=b4 Z;obtain⟨B,hB⟩:=he;refine⟨mem_image_of_mem _ (f0 hA hk hop hq hrk hB),?_,λhh=>?_⟩
 ·simp only[bF,bI,Nat.add_sub_cancel_left];fin_cases B;exacts[Or.inl hB,Or.inr hB]
 obtain⟨m,hm,e⟩:=mem_image.mp hh;obtain rfl:m=k:=by omega
 rcases mem_insert.mp hm with h|h
 ·exact hm0 h
 obtain⟨-,-,-,hne,O,hO,hOr⟩:=H.2.2.2.2.1 m h;rcases hkq with h1|h1
 ·rw[h1]at hne;simp at hne
 rw[bO (bZ.mp hA).1 hk]at h1;simp only[List.mem_cons,List.not_mem_nil,or_false]at h1;have hqop:=(aA.mp hq).2.1;have hq0:orIn n C (n+q)=∅:=b6 λ_=>by rw[hqop];simp
 have hqr:¬OrReaches n C (n+q) r:=λh=>by
  obtain⟨-,h|⟨h,-⟩⟩:=bD.mp h
  ·exact Z.1.2.2.2.1.ne h.symm
  ·rw[hqop]at h;cases h
 rw[dO hA hk hop]at hne;rcases bG O with⟨rfl,-⟩|⟨rfl,-⟩<;>rcases h1 with h1|h1<;>first|exact hqr (h1▸hOr)|(rw[hO,←h1,hq0]at hne;simp at hne)
theorem uA (hR1:cM) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (Z:cI G C q r b) (hng:¬b8 G C q r b) (o:Fin 2) (p:Fin n) (hpA:p∈orIn n C (opnd C q o)) (hpU:dX G C q p) (hpB:∀t∈orIn n C (opnd C q (1-o)),G.Adj p t) (hno:∀z∈orIn n C (opnd C q (1-o)),¬dX G C q z):False:=by
 have W:n6 G C q r b o p col:=⟨hR1,hcol,Z,hng,hpA,hpU,hpB,hno⟩;obtain⟨hC,hT,h4,hqr,hJ,hoff,hW2⟩:=Z.1;have hA:=hC.1;obtain⟨hq,hr⟩:=b4 Z;have hCD:=kZ Z;obtain⟨hql,hqop,-⟩:=aA.mp hq;obtain⟨hrl,hrop,hrb⟩:=aA.mp hr;have hE:Ustar G C⊆G.edgeFinset:=sdiff_subset;have hU1U:bE G C q o p⊆Ustar G C:=sdiff_subset;have hU1E:bE G C q o p⊆G.edgeFinset:=hU1U.trans hE;obtain⟨Rc,Ms,Wg,m0,H⟩:=sS Z;obtain⟨hM0,hm0ne,hRc,hRcd,hMs,hV⟩:=id H;obtain⟨Pb,hPb,hb1,hb2⟩:=tR W;obtain⟨u0,v0,he0,hq0⟩:=vI W;by_cases hE1:∃u v,s(u,v)∈bE G C q o p/\gateVal n C q (pairInput u v)=true
 swap
 ·have hE0:∀u v,s(u,v)∈bE G C q o p ->gateVal n C q (pairInput u v)=false:=λu v h=>Bool.eq_false_iff.mpr λh'=>hE1 ⟨u,v,h,h'⟩;have hne:(bE G C q o p).Nonempty:=⟨_,he0⟩;obtain⟨a,ha,s,hras,hpa⟩:=hpU;by_cases hx:2<=(readers n C q).card\/∃x,(∃c∈orIn n C (opnd C r b),x c=true)/\(∃d∈orIn n C (opnd C r (1-b)),x d=true)/\graphFun G ∅ x=false
  ·refine sH hR1 col hcol Z (1-o) (by rw[bV];exact hpA) hpB (λu v huv=>?_) hx;cases hk:wireVal n (aG n C q) C.output (pairInput u v)
   ·obtain⟨hqx,hU⟩:=jF Z hq huv hk;by_cases hi:s(u,v)∈bE G C q o p
    ·simp[hE0 u v hi]at hqx
    obtain⟨t,ht,he⟩:=mem_image.mp (not_not.mp λh=>hi (mem_sdiff.mpr ⟨hU,h⟩));rw[←he];exact Or.inr ⟨by simp,t,ht,by simp⟩
   ·exact Or.inl rfl
  simp only[not_or,not_le,not_exists,not_and,Bool.not_eq_false]at hx;obtain⟨hrd,hS⟩:=hx;obtain⟨m,hrm,hZne,hreach⟩:=uB Z (by omega);have hZC:orIn n C (n+m)⊆orIn n C (opnd C r b):=a6 hA hrm;have hSa:∀c∈orIn n C (opnd C r b),∀d∈orIn n C (opnd C r (1-b)),G.Adj c d:=λc hc d hd=>(aT c d).mp (hS _ ⟨c,hc,by simp[pairInput]⟩ ⟨d,hd,by simp[pairInput]⟩);have hcd:∀e∈bE G C q o p,∃c∈orIn n C (opnd C r b),∃d∈orIn n C (opnd C r (1-b)),e=s(c,d):=λe he=>by
   induction e using Sym2.ind with|_ u v=>
   obtain⟨h1,h2⟩:=(dK Z u v).mp (d5 W he).1;rw[hE0 u v he]at h1;rcases h1 with h1|h1|h1<;>rcases h2 with h2|h2<;>first|cases h1|exact(disjoint_left.mp hCD h1 h2).elim|exact⟨u,h1,v,h2,rfl⟩|exact⟨v,h1,u,h2,Sym2.eq_swap⟩
  have hZa:orIn n C (n+m)⊆orIn n C (opnd C a s):=a6 hA (hreach a ha s hras);obtain⟨e0,he0⟩:=id hne;have hg1:1<=(centreless G C).card+Ms.card:=by
   induction e0 using Sym2.ind with|_ u v=>
   obtain⟨-,w,-,hw⟩:=d5 W he0;exact t9 H hw
  have rho:∀Pm:Finset ℕ,(∀h∈Pm,∃w,b5 n G C (bE G C q o p) w h) ->Pb.card+Pm.card+Ms.card+1<=(orN G C\lam G C).card:=λPm hPm=>by
   have:=kG hA H hPm hPb (Xs:=∅) (by simp);rw[card_empty]at this;omega
  by_cases hcs:∀c∈orIn n C (opnd C r b),∀c'∈orIn n C (opnd C r b),c=c'
  ·obtain⟨c,hc⟩:=Z.2.2.2;have hy:∀e∈bE G C q o p,c∈e:=λe he=>by
    obtain⟨c',hc',d,-,rfl⟩:=hcd e he;rw[hcs c hc c' hc'];exact by simp
   obtain⟨c',hc',d,hd,rfl⟩:=hcd e0 he0
   obtain⟨Pm,hPm,hcm⟩:=nR W hy (λl hl=>by
    obtain⟨c',hc',d,hd,e⟩:=hcd _ hl;rcases Sym2.eq_iff.mp e with⟨-,rfl⟩|⟨rfl,-⟩
    exacts[hd,(disjoint_left.mp hCD hc hd).elim]) hd (hSa c hc d hd)
   obtain⟨K,hK,hM⟩:=pH W (λ_=>True) {c} λe he=>⟨c,by simp,hy e he⟩
   have h2:=(lN K p c).2 (by
    rcases uG hK ha hZa hZne hpa with h|⟨p',hp',hz⟩
    ·exact Or.inl h
    ·obtain⟨z,hz'⟩:=hZne
     exact Or.inr (hcs _ (hZC hz') _ hc▸hz z hz'▸hp'))
   have:=rho Pm hPm;split_ifs at hcm<;>omega
  push Not at hcs;obtain⟨c,hc,c',hc',hcc⟩:=hcs;have hDs:∀d∈orIn n C (opnd C r (1-b)),∀d'∈orIn n C (opnd C r (1-b)),d=d':=λd hd d' hd'=>aQ h4 hcc (hSa c hc d hd) (hSa c' hc' d hd) (hSa c hc d' hd') (hSa c' hc' d' hd');obtain⟨d,hd⟩:=qR Z;have hy:∀e∈bE G C q o p,d∈e:=λe he=>by
   obtain⟨c'',-,d',hd',rfl⟩:=hcd e he;rw[hDs d' hd' d hd];exact by simp
  have hl:∀l,s(d,l)∈bE G C q o p ->l∈orIn n C (opnd C r b):=λl hl=>by
   obtain⟨c'',hc'',d',hd',e⟩:=hcd _ hl;rcases Sym2.eq_iff.mp e with⟨rfl,-⟩|⟨-,rfl⟩;exacts[(disjoint_left.mp hCD hc'' hd).elim,hc'']
  obtain⟨c0,hc0,d0,hd0,rfl⟩:=hcd e0 he0;have he0':s(d,c0)∈bE G C q o p:=by rw[Sym2.eq_swap,←hDs d0 hd0 d hd];exact he0
  by_cases hcg:(centreless G C).card=0/\Ms.card=1
  ·obtain⟨m1,hm1⟩:=card_eq_one.mp hcg.2;have hRc0:Rc=∅:=card_eq_zero.mp (by omega);have hLW:∀l,s(d,l)∈bE G C q o p ->l∈Wg m1∩aE (Ustar G C) d:=λl hl'=>by
    obtain⟨-,w,hw,hwu⟩:=d5 W hl';rcases hw with rfl|rfl
    ·exact(hng λx hqx ⟨d',hd',hxd'⟩=>bH hA hwu x ((dU Z x).mpr ⟨Or.inl hqx,d',hd',hxd'⟩) (hDs d' hd' w hd▸hxd')).elim
    rcases (hV w).mp hwu with⟨w',hw',-⟩|⟨m',hm',hwm⟩
    ·simp[hRc0]at hw'
    ·rw[hm1,mem_singleton]at hm';exact mem_inter.mpr ⟨hm'▸hwm,aD.mpr (mem_sdiff.mp hl').1⟩
   have hL1:=aF h4 hE (hMs m1 (by rw[hm1];exact by simp)).2.2.1 d;have huq:∀e∈bE G C q o p,e=s(d,c0):=λe he=>by
    obtain⟨l,rfl⟩:=Sym2.mem_iff_exists.mp (hy e he);rw[card_le_one.mp hL1 l (hLW l he) c0 (hLW c0 he0')]
   obtain⟨K,hK,hM⟩:=pH W (λ_=>True) {c0} λe he=>⟨c0,by simp,huq e he▸Sym2.mem_mk_right _ _⟩;obtain⟨x,hx,h2⟩:∃x∈orIn n C (opnd C r b),(insert p {c0}\K).card<=1+if s(d,x)∈bE G C q o p then 0 else 1:=by
    rcases uG hK ha hZa hZne hpa with h|⟨p',hp',hz⟩
    ·exact⟨c0,hc0,by simp[he0',(lN K p c0).2 (Or.inl h)]⟩
    obtain⟨z,hz'⟩:=hZne;by_cases hpc:p'=c0
    ·exact⟨c0,hc0,by simp[he0',(lN K p c0).2 (Or.inr (hpc▸hp'))]⟩
    refine⟨p',hz z hz'▸hZC hz',?_⟩;have hnot:s(d,p')∉bE G C q o p:=λh=>by
     rcases Sym2.eq_iff.mp (huq _ h)with⟨-,h'⟩|⟨h',-⟩;exacts[hpc h',disjoint_left.mp hCD hc0 (h'▸hd)]
    simp[hnot,(lN K p c0).1]
   obtain⟨Pm,hPm,hcm⟩:=nR W hy hl hx (hSa x hx d hd).symm;have:=rho Pm hPm;split_ifs at hcm h2<;>omega
  ·obtain⟨Pm,hPm,hcm⟩:=nR W hy hl hc0 (hSa c0 hc0 d hd).symm;obtain⟨K,hK,hM⟩:=pH W (λ_=>True) {d} λe he=>⟨d,by simp,hy e he⟩;have h2:=(lN K p d).1;have:=rho Pm hPm;simp only[he0',↓reduceIte]at hcm;omega
 obtain⟨u,v,hE0,hqx⟩:=hE1;obtain⟨⟨a0,ha0,hxa⟩,⟨b0,hb0,hxb⟩⟩:=(bP Z.1 o _).mp hqx;rw[fP (aW hxa) (aW hxb) λe=>disjoint_left.mp (cJ Z.1 o) ha0 (e▸hb0)]at hE0;have hab:G.Adj a0 b0:=by
  simpa using hU1E hE0
 have ha0p:a0≠p:=λh=>(mem_sdiff.mp hE0).2 (mem_image.mpr ⟨b0,hb0,by rw[h]⟩);by_cases hIp:∃a∈tops G C,∃s:Fin 2,OrReaches n C (opnd C a s) q/\p∈orIn n C (opnd C a (1-s))/\(orIn n C (opnd C a s)).Nonempty
 swap
 ·obtain⟨t,ht,s,hts,hpt⟩:=hpU;have hte:orIn n C (opnd C t s)=∅:=not_nonempty_iff_eq_empty.mp λh=>hIp ⟨t,ht,s,hts,hpt,h⟩;obtain⟨htl,htop,htb⟩:=aI.mp ht;have hpure:∀k∈junk G C,¬OrReaches n C (opnd C t (1-s)) k:=λk hk hk'=>by
   rcases (r7 Z).1 hk with rfl|rfl
   ·exact nV hA ht hq hts hk'
   ·exact hng λx hqx ⟨d,hd,hxd⟩=>htb x ((aN hA htl htop s x).mpr ⟨aO hA x hts hqx,aO hA x hk' ((dU Z x).mpr ⟨Or.inl hqx,d,hd,hxd⟩)⟩)
  by_cases htr:OrReaches n C (opnd C t s) r
  ·obtain⟨k,hk⟩:∃k,opnd C t s=n+k:=⟨opnd C t s-n,by have:=hts.1;omega⟩;have hts':=hts;have hte':=hte;rw[hk]at hts hte htr;obtain⟨hkl,hk1⟩:=bD.mp hts;have hkop:(gateAt C k).op=GateOp.or:=by
    rcases hk1 with h|⟨h,-⟩
    ·obtain⟨-,h'|⟨h',-⟩⟩:=bD.mp htr;exacts[absurd (h.trans h'.symm) hqr.ne,h']
    ·exact h
   have hx:=t8 Z H hkl hkop hts ⟨0,by rw[dO hA hkl hkop]at hte;exact(union_eq_empty.mp hte).1⟩ (λe=>by rw[←e,hte]at hm0ne;simp at hm0ne) (Or.inl hte);have hpV:aC n G C r p:=⟨t,ht,s,by rw[hk];exact htr,hpt⟩;have htc:t∈centreless G C:=c7 ht hte'
   refine qB col hcol Z hU1U (λu v h=>d5 W h) he0 hq0 H hPb (Xs:={n+k}) (λh hh=>mem_singleton.mp hh▸hx) (if ∃t∈orIn n C (opnd C q (1-o)),s(p,t)∉Ustar G C then 0 else 1) (λQ hQ=>by
      obtain⟨K,-,hM⟩:=pH W (λ_=>True) Q hQ;have h1:=eG K Q p;have h2:=card_le_card (sdiff_subset (s:=Q) (t:=K));rw[card_singleton]
      split_ifs at h1⊢<;>first|omega|(have:=hb2 ‹_›;omega)) ?_
   split_ifs with hε
   ·exact Or.inl rfl
   refine Or.inr ⟨rfl,card_pos.mpr ⟨t,htc⟩,?_,λB x y cX hcX hcV hx hy hxy hLy hcov=>?_⟩
   ·by_contra! hg
    have hc1:centreless G C={t}:=(card_eq_one.mp (show(centreless G C).card=1 by
     have:=card_pos.mpr ⟨t,htc⟩;omega)).elim λt' ht'=>by
      rw[ht']at htc⊢;rw[mem_singleton.mp htc]
    obtain⟨-,w,hw,hwu⟩:=d5 W hE0;rcases (hV w).mp hwu with⟨w',hw',hww⟩|⟨m',hm',-⟩
    ·obtain⟨a',ha',β',hra',rfl⟩:=hRcd w' hw';rw[hc1,mem_singleton]at ha';subst ha';obtain rfl:β'=s:=(aS s β').resolve_right λh=>hpure r hr (h▸hra');rcases hw with rfl|rfl;exacts[ha0p (sI W ha0 ⟨a',ht,β',hts',hww⟩),hno w hb0 ⟨a',ht,β',hts',hww⟩]
    ·exact absurd (card_pos.mpr ⟨m',hm'⟩) (by omega)
   rcases aS o B with hB|hB
   ·exact hcV p hpV (hcX p (mem_union_left _ (hB▸hpA)))
   subst hB;have hcb0:col b0=cX:=hcX b0 (mem_union_left _ hb0);obtain⟨-,w0,hw0,hwu0⟩:=d5 W hE0;have ha0V:aC n G C r a0:=by
    rcases hw0 with rfl|rfl;exacts[hwu0,(hcV _ hwu0 hcb0).elim]
   have ha0D:a0∉orIn n C (opnd C r (1-b)):=λh=>ha0p (bC h4 (hW2 (1-o)) (λt' ht'=>qS Z ha0V ((dK Z a0 t').mpr ⟨Or.inl (rE Z ha0 ht'),Or.inl h⟩) (Or.inl rfl)) hpB);have adj:∀{x' y':Fin n},s(x',y')∈bE G C q o p ->G.Adj x' y':=λh=>by
    simpa using hU1E h
   have hx0:x=b0:=by
    rcases hcov _ hE0 with h|h<;>rcases Sym2.mem_iff.mp h with h'|h'
    ·exact(hcV _ ha0V (h'▸hcX _ hx)).elim
    ·exact h'
    ·by_contra hxb;subst h';rcases mem_union.mp hx with hxB|hxC
     ·exact hxb (aQ h4 ha0p (adj hxy).symm (hpB x hxB) hab (hpB b0 hb0))
     ·rcases ((dK Z x y).mp (d5 W hxy).1).2 with h2|h2;exacts[disjoint_left.mp hCD hxC h2,ha0D h2]
    ·exact(hcV _ (h'▸hy) hcb0).elim
   subst hx0
   have hyp:y≠p:=λh=>(mem_sdiff.mp hxy).2 (mem_image.mpr ⟨x,hb0,by
    rw[h,Sym2.eq_swap]⟩)
   obtain⟨l,hl⟩:=hLy;obtain⟨hlx,hly⟩:=mem_erase.mp hl;have hyl:=aD.mp hly;have hyD:y∈orIn n C (opnd C r (1-b)):=by
    rcases mem_union.mp (((n8 Z (d5 W hyl).1 (1-o)).1).resolve_left λh=>hcV y hy (hcX y h))with hlB|hlC
    ·exact(hlx (aQ h4 hyp (adj hyl) (hpB l hlB) (adj hxy).symm (hpB x hb0))).elim
    ·exact((dK Z y l).mp (d5 W hyl).1).2.resolve_right λh=>disjoint_left.mp hCD hlC h
   obtain⟨b',hb'B,hb'b⟩:=exists_mem_ne (hW2 (1-o)) x;rcases eY (x:=a0) (y:=y) (z:=b') (bH hA hy _ ((dU Z _).mpr ⟨Or.inl ((bP Z.1 o _).mpr ⟨⟨a0,ha0,by simp⟩,b',hb'B,by simp⟩),y,hyD,by simp⟩) (by simp))with h|h|h
   ·exact hcol _ _ h (bB _ _ _ (hcV _ ha0V) (hcV _ hy))
   ·exact hb'b (aQ h4 hyp h (hpB b' hb'B) (adj hxy).symm (hpB x hb0))
   ·exact hb'b (aQ h4 ha0p h (hpB b' hb'B) hab (hpB x hb0))
  have hw1:∀x,wireVal n C (opnd C t (1-s)) x=true↔∃v∈orIn n C (opnd C t (1-s)),x v=true:=λx=>by
   rw[a8 hA hT htl htop (1-s) x];exact or_iff_left λ⟨k,hk,_,hk',_⟩=>hpure k hk hk'
  have hw0:∀x,wireVal n C (opnd C t s) x=true↔gateVal n C q x=true:=λx=>by
   rw[a8 hA hT htl htop s x,hte];simp only[notMem_empty,false_and,exists_false,false_or]
   exact⟨λ⟨k,hk,_,hk',hkx⟩=>by
    rcases (r7 Z).1 hk with rfl|rfl
    exacts[hkx,(htr hk').elim],λh=>⟨q,hq,bU hA htl s hts,hts,h⟩⟩
  have hqt:q<t:=by have:=(aX hts).1;have:=aH hA htl s;omega
  have hrt:r≠t:=λe=>hrb (e▸htb);have hpl:(p:ℕ)<n+t:=by have:=p.2;omega
  have hbl:opnd C q (1-o)<n+t:=by have:=aH hA hql (1-o);omega
  have hv:∀x,GateOp.and.eval [wireVal n C p x,wireVal n C (opnd C q (1-o)) x]=true↔x p=true/\∃v∈orIn n C (opnd C q (1-o)),x v=true:=λx=>by
   simp only[GateOp.eval,List.all_cons,List.all_nil,id,Bool.and_true,Bool.and_eq_true,bA,eI hA hT hq (dF hqr hJ)]
  have hle:∀x,GateOp.and.eval [wireVal n C p x,wireVal n C (opnd C q (1-o)) x]=true ->gateVal n C t x=true:=λx hx=>by
   obtain⟨hxp,v,hv',hxv⟩:=(hv x).mp hx;exact(aN hA htl htop s x).mpr ⟨(hw0 x).mpr ((bP Z.1 o x).mpr ⟨⟨p,hpA,hxp⟩,v,hv',hxv⟩),(hw1 x).mpr ⟨p,hpt,hxp⟩⟩
  obtain⟨hD,hj1,hj2⟩:=cT hC htl (Or.inl rfl) hpl hbl hle λu v huv=>by
   cases hk:wireVal n (aG n C t) C.output (pairInput u v)
   ·right;obtain⟨h0,h1⟩:=(aN hA htl htop s _).mp (qV hC huv hk);obtain⟨w,hw,hxw⟩:=(hw1 _).mp h1;have hqx:=(hw0 _).mp h0;rcases l8 Z.1 o hqx (aW hxw)with hwA|hwB
    ·obtain rfl:=sI W hwA ⟨t,ht,s,hts,hw⟩;obtain⟨-,⟨t',ht',hxt⟩⟩:=(bP Z.1 o _).mp hqx;exact(hv _).mpr ⟨hxw,t',ht',hxt⟩
    ·exact(hno w hwB ⟨t,ht,s,hts,hw⟩).elim
   ·exact Or.inl rfl
  have hsp:=b7 hA htl (Or.inl rfl) hpl hbl;have hag:=cV (C:=C) t ⟨GateOp.and,[(p:ℕ),opnd C q (1-o)]⟩;set D:=aL C t ⟨GateOp.and,[(p:ℕ),opnd C q (1-o)]⟩with hDd;have hDt:gateAt D t=⟨GateOp.and,[(p:ℕ),opnd C q (1-o)]⟩:=by
   rw[hDd,aL,bR htl,Function.update_self]
  have hDl:D.gates.length=C.gates.length:=hag.1;have hor:∀g w,OrReaches n D w g↔OrReaches n C w g:=λg=>mV hag htop (by rw[hDt]) g;have hoi:∀w,orIn n D w=orIn n C w:=qJ hag htop (by rw[hDt]);have hop:∀k<C.gates.length,k≠t ->∀B,opnd D k B=opnd C k B:=λk hk hkt B=>by simp only[opnd,hag.2 k hk hkt]
  have hnc:∀k∈junk G C,¬InCone n C t k:=λk hk hc=>by
   rcases (r7 Z).1 hk with rfl|rfl
   ·have:=aP hc;omega
   ·exact hT t htl k hrl htop htb hrop hc
  have hval:∀k∈junk G C,∀x,gateVal n D k x=gateVal n C k x:=λk hk x=>eB hag x (n+k) (by
    have:k≠t:=λe=>(aA.mp hk).2.2 (e▸htb)
    omega) λ_=>by simpa using hnc k hk
  have htD:BelowF G D t:=λx hx=>by
   rw[show gateVal n D t x=wireVal n D (n+t) x from rfl,(hsp x).2.2.2.2.2]at hx;obtain⟨hxp,v,hv',hxv⟩:=(hv x).mp hx;exact(dJ x).mpr ⟨p,v,hpB v hv',hxp,hxv⟩
  have hJD:∀k,k∈junk G D↔k∈junk G C:=λk=>by
   refine⟨λhk=>(hj1 k hk).resolve_left λh=>(aA.mp hk).2.2 (h▸htD),λhkJ=>hj2 k hkJ (λe=>(aA.mp hkJ).2.2 (e▸htb)) (hnc k hkJ)⟩
  have hTD:TopForm G D:=by
   intro i hi j hj hiop hib hjop hc;rw[hDl]at hi hj
   have hc':=g9 htl (λi hi hn=>by
    simp only[List.mem_cons,List.not_mem_nil,or_false]at hi;rcases hi with rfl|rfl
    ·have:=p.2;omega
    ·exact dI (aZ.mpr ⟨hql,opnd C q (1-o)-n,by
      have:=aH hA hql (1-o);omega,by
      rw[show n+(opnd C q (1-o)-n)=opnd C q (1-o) by omega]
      exact dA hA hql (1-o),Or.inl rfl⟩) (bU hA htl s hts)) i j hc
   have hjop':(gateAt C j).op=GateOp.and:=by
    by_cases hjt:j=t
    ·rw[hjt];exact htop
    ·rwa[hag.2 j hj hjt]at hjop
   by_cases hit:i=t
   ·rw[hit]at hc';exact hT t htl j hj htop htb hjop' hc'
   have hgi:=hag.2 i hi hit;refine hT i hi j hj (by rwa[hgi]at hiop) (by_contra λhb'=>?_) hjop' hc';exact(aA.mp ((hJD i).2 (aA.mpr ⟨hi,by rwa[hgi]at hiop,hb'⟩))).2.2 hib
  have Z':cI G D q r b:=⟨⟨hD,hTD,h4,hqr,by ext k;rw[hJD,hJ],λk hk v=>by
   rw[hval k ((hJD k).1 hk)];exact hoff k ((hJD k).1 hk) v,λB=>by
   rw[hop q hql hqt.ne B,hoi];exact hW2 B⟩,by rw[hop r hrl hrt b,hor];exact Z.2.1,
   by rw[hop r hrl hrt (1-b),hor];exact Z.2.2.1,by rw[hop r hrl hrt b,hoi];exact Z.2.2.2⟩
  have htopD:∀a∈tops G C,a≠t ->a∈tops G D:=λa ha hat=>by
   obtain⟨hal,haop,hab⟩:=aI.mp ha;exact aI.mpr ⟨by rw[hDl];exact hal,by rw[hag.2 a hal hat];exact haop,λx hx=>hab x (kQ (C₁:=D) (C₂:=C) (m:=C.gates.length) (j:=t) hag.1.ge le_rfl (λk hk hkt=>hag.2 k hk hkt) (λk hk hkt=>by rw[hag.2 k hk hkt];exact eS hA hk) x (λh'=>by rw[(hsp x).2.2.2.2.2]at h';exact hle x h') (n+a) (by omega) hx)⟩
  refine nG hR1 col hcol Z' λu v he=>?_;obtain⟨heE,hnS⟩:=mem_sdiff.mp he;have hU1:s(u,v)∈bE G C q o p:=by
   refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨heE,λhs=>hnS ?_⟩,λhi=>hnS ?_⟩
   ·simp only[starEdges,mem_biUnion,mem_image,mem_product]at hs⊢;obtain⟨a,ha,⟨x,y⟩,⟨hx,hy⟩,e⟩:=hs;have hat:a≠t:=by
     rintro rfl;simp only[side]at hx hy;rcases bG s with⟨rfl,-⟩|⟨rfl,-⟩<;>simp[hte]at hx hy
    refine⟨a,htopD a ha hat,(x,y),⟨?_,?_⟩,e⟩<;>simp only[side,hop a (aI.mp ha).1 hat,hoi]<;>assumption
   ·obtain⟨t',ht',e⟩:=mem_image.mp hi;simp only[starEdges,mem_biUnion,mem_image,mem_product];refine⟨t,aI.mpr ⟨by rw[hDl];exact htl,by rw[hDt],htD⟩,(p,t'),⟨?_,?_⟩,e⟩
    ·show p∈orIn n D (opnd D t 0);rw[show opnd D t 0=p by simp only[opnd,hDt];rfl,hoi,fA p.2];simp
    ·show t'∈orIn n D (opnd D t 1);rw[show opnd D t 1=opnd C q (1-o) by simp only[opnd,hDt];rfl,hoi];exact ht'
  obtain⟨hrx,w,hw,a,ha,s',hra,hwa⟩:=d5 W hU1;have hal:=(aI.mp ha).1;have hat:a≠t:=by
   rintro rfl;rcases aS s s' with rfl|rfl;exacts[htr hra,hpure r hr hra]
  exact⟨by rw[hval r hr];exact hrx,w,hw,a,htopD a ha hat,s',by rw[hop a hal hat,hor];exact hra,by rw[hop a hal hat,hoi];exact hwa⟩
 obtain⟨a,ha,s,hras,hpa,hne⟩:=hIp;by_cases hIw:∃w∈orIn n C (opnd C a (1-s)),w≠p
 ·obtain⟨w,hwa,hwp⟩:=hIw;obtain⟨r0,hr0⟩:=hne;have hst:∀c∈orIn n C (opnd C a (1-s)),∀z∈orIn n C (opnd C a s),G.Adj c z/\s(c,z)∈starEdges G C:=λc hc z hz=>aV hA ha s hc hz;have hcw:col w=col p:=bB _ _ _ (hcol _ _ (hst w hwa r0 hr0).1) (hcol _ _ (hst p hpa r0 hr0).1);have hwW:=j4 hA ha hras hwa;have tri:∀s'∈orIn n C (opnd C q o),∀t'∈orIn n C (opnd C q (1-o)),G.Adj s' t'\/G.Adj t' w\/G.Adj s' w:=λs' hs' t' ht'=>eY (hwW _ ((bP Z.1 o _).mpr ⟨⟨s',hs',by simp⟩,t',ht',by simp⟩) (by simp));have hB2:∀t∈orIn n C (opnd C q (1-o)),t≠b0 ->t=r0:=λt ht htb=>by
   rcases tri a0 ha0 t ht with h|h|h
   ·exact(htb (aQ h4 ha0p hab (hpB b0 hb0) h (hpB t ht)).symm).elim
   ·exact aQ h4 hwp h.symm (hpB t ht) (hst w hwa r0 hr0).1 (hst p hpa r0 hr0).1
   ·exact(hcol _ _ h ((bB _ _ _ (hcol _ _ hab) (hcol _ _ (hpB b0 hb0))).trans hcw.symm)).elim
  obtain⟨t1,ht1,t2,ht2,h12⟩:=one_lt_card.mp (hW2 (1-o));have hr0B:r0∈orIn n C (opnd C q (1-o))/\r0≠b0:=by
   by_cases h1:t1=b0
   ·have:=hB2 t2 ht2 (λh=>h12 (h1.trans h.symm));exact⟨this▸ht2,λh=>h12 (by rw[h1,←h,this])⟩
   ·exact⟨hB2 t1 ht1 h1▸ht1,λh=>h1 (by rw[hB2 t1 ht1 h1,h])⟩
  have hacc:∀u v,G.Adj u v ->wireVal n (aG n C q) C.output (pairInput u v)=true\/(∃a∈orIn n C (opnd C q o),a∈s(u,v))/\b0∈s(u,v):=λu v huv=>by
   cases hk:wireVal n (aG n C q) C.output (pairInput u v)
   ·right;obtain⟨hqx,hU⟩:=jF Z (b4 Z).1 huv hk;obtain⟨⟨s',hs',hxs⟩,⟨t',ht',hxt⟩⟩:=(bP Z.1 o _).mp hqx;have e:=fP (aW hxs) (aW hxt) λe=>disjoint_left.mp (cJ Z.1 o) hs' (e▸ht');by_cases htb:t'=b0
    ·rw[e,←htb];exact⟨⟨s',hs',by simp⟩,by simp⟩
    exfalso;have htr:=hB2 t' ht' htb;have hadj:G.Adj s' r0:=by
     rw[←htr];have:=huv;rw[←aT,dT e,aT]at this;exact this
    by_cases hsp:s'=p
    ·rw[e,htr,hsp]at hU;exact(mem_sdiff.mp hU).2 (hst p hpa r0 hr0).2
    rcases tri s' hs' b0 hb0 with h|h|h
    ·exact hr0B.2 (aQ h4 hsp hadj (hst p hpa r0 hr0).1 h (hpB b0 hb0))
    ·exact hr0B.2 (aQ h4 hwp h.symm (hpB b0 hb0) (hst w hwa r0 hr0).1 (hst p hpa r0 hr0).1).symm
    ·exact hcol _ _ h ((bB _ _ _ (hcol _ _ hadj) (hcol _ _ (hst p hpa r0 hr0).1)).trans hcw.symm)
   ·exact Or.inl rfl
  obtain⟨hrd,hS⟩:(readers n C q).card<=1/\∀x,(∃c∈orIn n C (opnd C r b),x c=true) ->(∃d∈orIn n C (opnd C r (1-b)),x d=true) ->graphFun G ∅ x=true:=by
   have ha:=aH hA hql o;have hb:b0.1<n+q:=by have:=b0.2;omega
   have hv:∀x,GateOp.and.eval [wireVal n C (opnd C q o) x,wireVal n C b0 x]=true↔(∃a∈orIn n C (opnd C q o),x a=true)/\x b0=true:=λx=>by
    simp only[GateOp.eval,List.all_cons,List.all_nil,id,Bool.and_true,Bool.and_eq_true,bA,eI hA hT hq (dF hqr hJ)]
   have hle:∀x,GateOp.and.eval [wireVal n C (opnd C q o) x,wireVal n C b0 x]=true ->gateVal n C q x=true:=λx hx=>let ⟨h1,h2⟩:=(hv x).mp hx;(bP Z.1 o x).mpr ⟨h1,b0,hb0,h2⟩
   obtain⟨hD,hj1,-⟩:=cT hC hql (Or.inl rfl) ha hb hle λu v huv=>(hacc u v huv).imp id λ⟨⟨a,haA,h1⟩,h2⟩=>(hv _).mpr ⟨⟨a,haA,by
     rcases Sym2.mem_iff.mp h1 with rfl|rfl<;>simp[pairInput]⟩,by
     rcases Sym2.mem_iff.mp h2 with rfl|rfl<;>simp[pairInput]⟩
   have hsp:=b7 hA hql (Or.inl rfl) ha hb;have hag:=cV (C:=C) q ⟨GateOp.and,[opnd C q o,b0.1]⟩;set D:=aL C q ⟨GateOp.and,[opnd C q o,b0.1]⟩with hDd;have hDq:gateAt D q=⟨GateOp.and,[opnd C q o,b0.1]⟩:=by
    rw[hDd,aL,bR hql,Function.update_self]
   have hDl:D.gates.length=C.gates.length:=hag.1;have hsub:∀k∈junk G D,k=q\/k=r:=λk hk=>(hj1 k hk).elim Or.inl λh=>by rwa[hJ,mem_insert,mem_singleton]at h
   have h1:∀k∈junk G D,(∀k'∈junk G D,k'=k) ->False:=λk hk h=>hR1 n G D col hcol h4 hD (card_eq_one.mpr ⟨k,eq_singleton_iff_unique_mem.mpr ⟨hk,h⟩⟩);have hrq:r≠q:=hqr.ne';by_cases hq1:q∈junk G D
   ·by_cases hr1:r∈junk G D
    swap
    ·exact(h1 q hq1 λk hk=>(hsub k hk).resolve_right λh=>hr1 (h▸hk)).elim
    exfalso;have hJD:junk G D={q,r}:=by
     ext k;simp only[mem_insert,mem_singleton];exact⟨hsub k,λh=>h.elim (·▸hq1) (·▸hr1)⟩
    have hin:∀i∈(⟨GateOp.and,[opnd C q o,b0.1]⟩:Gate).inputs,n<=i ->InCone n C (i-n) q:=λi hi hn=>by
     simp only[List.mem_cons,List.not_mem_nil,or_false]at hi;rcases hi with rfl|rfl
     ·exact aZ.mpr ⟨hql,opnd C q o-n,by omega,by
       rw[show n+(opnd C q o-n)=opnd C q o by omega];exact dA hA hql o,
       Or.inl rfl⟩
     ·have:=b0.2;omega
    have hTD:TopForm G D:=by
     intro i hi j hj hiop hib hjop hc;rw[hDl]at hi hj;by_cases hiq:i=q
     ·exact(aA.mp (hiq▸hq1)).2.2 (hiq▸hib)
     have hgi:=hag.2 i hi hiq
     refine Z.1.2.1 i hi j hj (by rwa[hgi]at hiop) (by_contra λhb'=>?_) (by
      by_cases hjq:j=q
      ·rw[hjq];exact hqop
      ·rwa[hag.2 j hj hjq]at hjop) (g9 hql hin i j hc)
     have:i∈junk G C:=aA.mpr ⟨hi,by rwa[hgi]at hiop,hb'⟩;rw[hJ,mem_insert,mem_singleton]at this;rcases this with h|h;exacts[hiq h,(aA.mp (h▸hr1)).2.2 (h▸hib)]
    have hw:=(eQ hR1 col hcol h4 hD hTD (by rw[hJD,card_pair hrq.symm]) (λk hk v=>Bool.eq_false_iff.mpr λh=>by
      have hkC:k∈junk G C:=by rcases hsub k hk with rfl|rfl<;>assumption
      have:gateVal n C k _=true:=kQ (C₁:=D) (C₂:=C) (m:=C.gates.length) (j:=q) hag.1.ge le_rfl (λk hk hkq=>hag.2 k hk hkq) (λk hk hkq=>by rw[hag.2 k hk hkq];exact eS hA hk) _ (λh'=>by rw[(hsp _).2.2.2.2.2]at h';exact hle _ h') (n+k) (by have:=(aA.mp hkC).1;omega) h
      rw[hoff k hkC v]at this;cases this) hq1 λk hk hc=>by
     have:=aP hc
     rcases hsub k hk with rfl|rfl<;>omega).2
    rw[show opnd D q 1=b0.1 by simp[opnd,hDq],fA b0.2]at hw;simp at hw
   have hbf:BelowF G D q:=by
    by_contra h;exact hq1 (aA.mpr ⟨by rw[hDl];exact hql,by rw[hDq],h⟩)
   refine⟨?_,λx ⟨c,hc,hxc⟩ ⟨d,hd,hxd⟩=>?_⟩
   ·have:=eC hD (i:=q) (by rw[hDl];exact hql) hbf
    rwa[show readers n D q=readers n C q by
     ext k;simp only[readers,mem_filter,mem_range,hDl];refine and_congr_right λhk=>?_;by_cases hkq:k=q
     ·subst hkq;rw[hDq];simp only[List.mem_cons,List.not_mem_nil,or_false];refine⟨λh=>?_,λh=>?_⟩
      ·rcases h with h|h
       ·omega
       ·have:=b0.2;omega
      ·have:=dH hA hk h;omega
     ·rw[hag.2 k hk hkq]]at this
   by_cases hr1:r∈junk G D
   ·exact(h1 r hr1 λk hk=>(hsub k hk).resolve_left λh=>hq1 (h▸hk)).elim
   refine(show BelowF G D r by
    by_contra h
    exact hr1 (aA.mpr ⟨by rw[hDl];exact hrl,by rw[hag.2 r hrl hrq];exact hrop,h⟩))
    x ?_
   show wireVal n D (n+r) x=true;have hw:∀β',wireVal n D (opnd C r β') x=true:=λβ'=>by
    rcases aS b β' with rfl|rfl;exacts[b9 hA hag hqop hc hxc,b9 hA hag hqop hd hxd]
   rw[fV hA hag hrl hrq hrop x,hw 0,hw 1];rfl
  obtain⟨m,hrm,⟨z,hz⟩,hreach⟩:=uB Z hrd;have hzA:=a6 hA (hreach a ha s hras) hz;have hr0C:r0∈orIn n C (opnd C r b):=aQ h4 hwp (hst w hwa z hzA).1 (hst p hpa z hzA).1 (hst w hwa r0 hr0).1 (hst p hpa r0 hr0).1▸a6 hA hrm hz;have hadjD:∀d∈orIn n C (opnd C r (1-b)),G.Adj r0 d:=λd hd=>(aT r0 d).mp (hS _ ⟨r0,hr0C,by simp[pairInput]⟩ ⟨d,hd,by simp[pairInput]⟩);rcases ((dK Z a0 b0).mp (d5 W hE0).1).2 with h|h
  ·exact hr0B.2 (aQ h4 ha0p (hadjD a0 h).symm (hst p hpa r0 hr0).1 hab (hpB b0 hb0))
  ·exact hcol _ _ (hadjD b0 h) (bB _ _ _ (hcol _ _ (hpB r0 hr0B.1)).symm (hcol _ _ (hpB b0 hb0)).symm)
 have h1s:orIn n C (opnd C a (1-s))={p}:=eq_singleton_iff_unique_mem.mpr ⟨hpa,λw hw=>by_contra λh=>hIw ⟨w,hw,h⟩⟩;have hms:∀Y:Finset (Fin n),(∀e∈bE G C q o p,∃v∈Y,v∈e) ->2+2*(centreless G C).card+(orN G C\lam G C).card<=((orIn n C (opnd C q (1-o))).filter λt=>s(p,t)∈Ustar G C).card+(bE G C q o p).card+Y.card:=λY hY=>by
  obtain⟨K,hK,hM⟩:=pH W (λv=>v=p) Y hY;obtain⟨b',p',hp',-,himp⟩:=hK a (jO ha hne (by rw[h1s];exact singleton_nonempty p));rw[insert_sdiff_of_mem _ (himp ⟨s,p,h1s,rfl⟩▸hp')]at hM;have:=card_le_card (sdiff_subset (s:=Y) (t:=K));omega
 have eng:=λ(Xs:Finset ℕ) hXs hM=>qB col hcol Z hU1U (λu v h=>d5 W h) he0 hq0 H hPb (Xs:=Xs) hXs 0 hM (Or.inl rfl);by_cases hz:∃k∈readers n C q,∃k'∈readers n C q,(gateAt C k).op=GateOp.or/\(gateAt C k').op=GateOp.or/\k≠k'
 ·obtain⟨k1,hk1,k2,hk2,ho1,ho2,h12⟩:=hz;obtain⟨k,hk,hko,hkm⟩:∃k∈readers n C q,(gateAt C k).op=GateOp.or/\k≠m0:=if h:k1=m0 then⟨k2,hk2,ho2,λe=>h12 (h.trans e.symm)⟩else⟨k1,hk1,ho1,h⟩;obtain⟨hkl,hin⟩:=mem_filter.mp hk;rw[mem_range]at hkl;have hq0':orIn n C (n+q)=∅:=b6 λ_=>by rw[hqop];simp
  have hx:=t8 Z H hkl hko (bD.mpr ⟨hkl,Or.inr ⟨hko,n+q,hin,dH hA hkl hin,bD.mpr ⟨hql,Or.inl rfl⟩⟩⟩) (by
    rw[bO (bZ.mp hA).1 hkl]at hin;simp only[List.mem_cons,List.not_mem_nil,or_false]at hin;rcases hin with h|h
    exacts[⟨0,h▸hq0'⟩,⟨1,h▸hq0'⟩]) hkm (Or.inr hin)
  exact eng {n+k} (λh hh=>mem_singleton.mp hh▸hx) λQ hQ=>by
   have:=hms Q hQ;rw[card_singleton];omega
 simp only[not_exists,not_and,not_not]at hz;by_cases hε:∃t∈orIn n C (opnd C q (1-o)),s(p,t)∉Ustar G C
 ·exact eng ∅ (by simp) λQ hQ=>by have:=hms Q hQ;have:=hb2 hε;simp;omega
 simp only[not_exists,not_and,not_not]at hε;have hOR:=hz;have hε0:=hε;have hpa:p∈orIn n C (opnd C a (1-s)):=by rw[h1s];exact by simp
 obtain⟨m,-,-,-,hrm,⟨z,hz⟩,hreach⟩:=s6 Z hOR
 have hza:z∈orIn n C (opnd C a s):=a6 hA (hreach _ hras λhe=>by
  obtain⟨v,hv⟩:=hne
  rw[he,b6 (λ_=>by rw[hqop];simp)]at hv;simp at hv) hz
 have hzC:z∈orIn n C (opnd C r b):=a6 hA hrm hz;have hpz:=aV hA ha s hpa hza;have hzB:z∉orIn n C (opnd C q (1-o)):=λh=>(mem_sdiff.mp (hε0 z h)).2 hpz.2;have hNa:∀a',∀t∈orIn n C (opnd C q (1-o)),∀t'∈orIn n C (opnd C q (1-o)),a'≠p ->G.Adj a' t ->G.Adj a' t' ->t=t':=λa' t ht t' ht' hap h1 h2=>aQ h4 hap h1 (hpB t ht) h2 (hpB t' ht');have hcz:col z≠col p:=λh=>hcol _ _ hpz.1 h.symm;have hrcd:∀c∈orIn n C (opnd C r b),∀d∈orIn n C (opnd C r (1-b)),gateVal n C r (pairInput c d)=true:=λc hc d hd=>(dK Z c d).mpr ⟨Or.inr (Or.inl hc),Or.inr hd⟩;obtain⟨b',hb'B,hb'b⟩:=exists_mem_ne (hW2 (1-o)) b0;have hDV:∀t∈orIn n C (opnd C r (1-b)),¬aC n G C r t:=λt ht hu=>by
  have hzt:G.Adj z t:=qS Z hu (hrcd z hzC t ht) (Or.inr rfl);by_cases htp:t=p
  ·obtain⟨t0,ht0,-,hn0⟩:=vH W;exact hn0 ⟨(dK Z p t0).mpr ⟨Or.inl (rE Z hpA ht0),Or.inl (htp▸ht)⟩,Or.inl (htp▸hu)⟩
  rcases eY (x:=a0) (y:=t) (z:=b') (bH hA hu _ ((dU Z _).mpr ⟨Or.inl ((bP Z.1 o _).mpr ⟨⟨a0,ha0,by simp⟩,b',hb'B,by simp⟩),t,ht,by simp⟩) (by simp))with h|h|h
  ·exact hcol _ _ h ((bB _ _ _ (hcol _ _ hab) (hcol _ _ (hpB b0 hb0))).trans (bB _ _ _ (λh=>hcol _ _ hzt h.symm) (Ne.symm hcz)).symm)
  ·exact hzB (aQ h4 htp hzt.symm hpz.1 h (hpB b' hb'B)▸hb'B)
  ·exact hb'b (hNa a0 b' hb'B b0 hb0 ha0p h hab)
 by_cases hD1:∀d∈orIn n C (opnd C r (1-b)),∀d'∈orIn n C (opnd C r (1-b)),d=d'
 ·obtain⟨d,hd⟩:=qR Z;have hy:∀e∈bE G C q o p,d∈e:=λe he=>by
   induction e using Sym2.ind with|_ u v=>
   rcases ((dK Z u v).mp (d5 W he).1).2 with h|h
   ·rw[hD1 u h d hd];exact by simp
   ·rw[hD1 v h d hd];exact by simp
  obtain⟨P,hP,hc⟩:=kB hA Rc (aE (bE G C q o p) d) λW' hW'=>(card_le_card (inter_subset_inter subset_rfl λx hx=>aD.mpr (hU1U (aD.mp hx)))).trans (aF h4 hE hW' d);have hLV:∀l∈aE (bE G C q o p) d,aC n G C r l:=λl hl=>by
   obtain⟨-,w,hw,hwu⟩:=d5 W (aD.mp hl);rcases hw with rfl|rfl;exacts[(hDV w hd hwu).elim,hwu]
  have h1:aE (bE G C q o p) d⊆(Rc.biUnion (orIn n C)∩aE (bE G C q o p) d)∪Ms.biUnion λm'=>Wg m'∩aE (bE G C q o p) d:=λl hl=>by
   rcases (hV l).mp (hLV l hl)with⟨w,hw,hlw⟩|⟨m',hm',hlm⟩
   ·exact mem_union_left _ (mem_inter.mpr ⟨mem_biUnion.mpr ⟨w,hw,hlw⟩,hl⟩)
   ·exact mem_union_right _ (mem_biUnion.mpr ⟨m',hm',mem_inter.mpr ⟨hlm,hl⟩⟩)
  have h2:=(card_le_card h1).trans (card_union_le _ _);have h3:(Ms.biUnion λm'=>Wg m'∩aE (bE G C q o p) d).card<=Ms.card:=card_biUnion_le.trans ((sum_le_card_nsmul Ms _ 1 λm' hm'=>aF h4 hU1E (bT hU1U subset_rfl (hMs m' hm').2.2.1) d).trans (by simp));have hρ:=kG hA H (Pp:=P) (λh hh=>⟨h,sG hA (hP h hh).1,λhf=>absurd (hP h hh).2.2 (not_lt.mpr (aF h4 hU1E hf d)),(hP h hh).1.2.2.1,(hP h hh).1.2.2.2, .refl⟩) hPb (Xs:=∅) (by simp);have hM:=hms {d} λe he=>⟨d,by simp,hy e he⟩;have:=uF hy;rw[card_singleton]at hM;rw[card_empty]at hρ;omega
 push Not at hD1;obtain⟨d1,hd1,d2,hd2,hd12⟩:=hD1;have hVD:∀w,aC n G C r w ->w∈orIn n C (opnd C r b) ->∀d∈orIn n C (opnd C r (1-b)),G.Adj w d:=λw hw hwC d hd=>qS Z hw (hrcd w hwC d hd) (Or.inl rfl);obtain⟨hr0',w0,hw0,hwu0⟩:=d5 W he0;obtain⟨h01,h02⟩:=(dK Z u0 v0).mp hr0';rw[hq0]at h01;obtain⟨v,hvC,hvV⟩:∃v∈orIn n C (opnd C r b),aC n G C r v:=by
  rcases hw0 with rfl|rfl<;>rcases h02 with h|h<;>rcases h01 with h'|h'|h'<;>first|cases h'|exact(hDV _ h hwu0).elim|exact⟨_,h',hwu0⟩|exact(disjoint_left.mp hCD h' h).elim
 have hvD:=hVD v hvV hvC;have hCV:∀v'∈orIn n C (opnd C r b),aC n G C r v' ->v'=v:=λv' hv' hu'=>by_contra λhne'=>hd12 (aQ h4 hne' (hVD v' hu' hv' d1 hd1) (hvD d1 hd1) (hVD v' hu' hv' d2 hd2) (hvD d2 hd2));have hvnD:v∉orIn n C (opnd C r (1-b)):=disjoint_left.mp hCD hvC;have hU2s:∀x y,s(x,y)∈bE G C q o p ->v≠x ->v≠y ->∃a'∈orIn n C (opnd C q o),∃b'∈orIn n C (opnd C q (1-o)),s(x,y)=s(a',b')/\G.Adj a' b'/\a'≠p/\((a'∈orIn n C (opnd C r (1-b))/\aC n G C r b')\/(b'∈orIn n C (opnd C r (1-b))/\aC n G C r a')):=by
  intro x y hxy hvx hvy;obtain⟨hrx,w,hw,hwu⟩:=d5 W hxy;obtain⟨g1,g2⟩:=(dK Z x y).mp hrx;have hwC:w∉orIn n C (opnd C r b):=λh=>by
   rcases hw with rfl|rfl;exacts[hvx (hCV _ h hwu).symm,hvy (hCV _ h hwu).symm]
  have hqx:gateVal n C q (pairInput x y)=true:=by
   rcases g1 with h|h|h
   ·exact h
   all_goals rcases g2 with h2|h2<;>rcases hw with rfl|rfl<;>first|exact(disjoint_left.mp hCD h h2).elim|exact(hwC h).elim|exact(hDV _ h2 hwu).elim
  obtain⟨⟨a',ha',hxa⟩,⟨b',hb',hxb⟩⟩:=(bP Z.1 o _).mp hqx;have e:=fP (aW hxa) (aW hxb) λe=>disjoint_left.mp (cJ Z.1 o) ha' (e▸hb');refine⟨a',ha',b',hb',e,by have:=hU1E hxy;rw[e]at this;simpa using this,λh=>(mem_sdiff.mp hxy).2 (mem_image.mpr ⟨b',hb',by rw[e,h]⟩),?_⟩;have hm:∀t,t∈s(x,y) ->t=a'\/t=b':=λt ht=>by rw[e]at ht;simpa using ht
  have g2':a'∈orIn n C (opnd C r (1-b))\/b'∈orIn n C (opnd C r (1-b)):=by
   rcases g2 with h|h
   ·rcases hm x (by simp)with h'|h'<;>rw[h']at h;exacts[Or.inl h,Or.inr h]
   ·rcases hm y (by simp)with h'|h'<;>rw[h']at h;exacts[Or.inl h,Or.inr h]
  rcases hm w (by rcases hw with rfl|rfl<;>simp)with rfl|rfl
  ·exact Or.inr ⟨g2'.resolve_left λh=>hDV _ h hwu,hwu⟩
  ·exact Or.inl ⟨g2'.resolve_right λh=>hDV _ h hwu,hwu⟩
 by_cases hU2:∃e∈bE G C q o p,v∉e
 swap
 ·push Not at hU2;obtain⟨Pm,hPm,hcm⟩:=nR W hU2 (λl hl=>((dK Z v l).mp (d5 W hl).1).2.resolve_left hvnD) hd1 (hvD d1 hd1);have hρ:=kG hA H hPm hPb (Xs:=∅) (by simp);have hM1:=hms {v} λe he=>⟨v,by simp,hU2 e he⟩;have:=t9 H hvV;rw[card_singleton]at hM1;rw[card_empty]at hρ;split_ifs at hcm<;>omega
 obtain⟨e',he',hve'⟩:=hU2
 induction e' using Sym2.ind with|_ x y=>
 obtain⟨as,has,bs,hbs,hes,hasbs,hasp,hDs⟩:=hU2s x y he' (λh=>hve' (h▸Sym2.mem_mk_left _ _)) (λh=>hve' (h▸Sym2.mem_mk_right _ _));rw[hes]at he' hve';have hcas:col as=col p:=bB _ _ _ (hcol _ _ hasbs) (hcol _ _ (hpB bs hbs));have hvas:v≠as:=λh=>hve' (h▸Sym2.mem_mk_left _ _);have hvbs:v≠bs:=λh=>hve' (h▸Sym2.mem_mk_right _ _);by_cases hcv:col v=col p
 ·rcases hDs with⟨h,-⟩|⟨h,hu⟩
  ·exact hcol _ _ (hvD as h) (hcv.trans hcas.symm)
  have hadD:∀d∈orIn n C (opnd C r (1-b)),G.Adj d as:=λd hd=>by
   rcases eY (x:=z) (y:=d) (z:=as) (bH hA hu _ ((dU Z _).mpr ⟨Or.inr ⟨z,hzC,by simp⟩,d,hd,by simp⟩) (by simp))with h'|h'|h'
   ·exact(hcol _ _ h' (bB _ _ _ hcz λh'=>hcol _ _ (hvD d hd) (hcv.trans h'.symm))).elim
   ·exact h'
   ·exact(hzB (aQ h4 hasp h'.symm hpz.1 hasbs (hpB bs hbs)▸hbs)).elim
  exact hd12 (aQ h4 hvas (hvD d1 hd1) (hadD d1 hd1).symm (hvD d2 hd2) (hadD d2 hd2).symm)
 have hcD:∀d∈orIn n C (opnd C r (1-b)),col d=col p:=λd hd=>bB _ _ _ (λh'=>hcol _ _ (hvD d hd) h'.symm) (Ne.symm hcv);obtain⟨hasD,hbsV⟩:as∈orIn n C (opnd C r (1-b))/\aC n G C r bs:=hDs.resolve_right λ⟨h,_⟩=>hcol _ _ (hpB bs hbs) (hcD bs h).symm;have hAB:∀x∈orIn n C (opnd C q o),∀y∈orIn n C (opnd C q (1-o)),x∈orIn n C (opnd C r (1-b)) ->aC n G C r y ->G.Adj x y:=λx hx y hy hxD hu=>qS Z hu ((dK Z x y).mpr ⟨Or.inl (rE Z hx hy),Or.inl hxD⟩) (Or.inr rfl);have hAD:∀a''∈orIn n C (opnd C q o),a''∈orIn n C (opnd C r (1-b)) ->a''=as:=λa'' ha'' hD''=>by_contra λhne'=>hvbs (aQ h4 hne' (hAB a'' ha'' bs hbs hD'' hbsV) hasbs (hvD a'' hD'').symm (hvD as hasD).symm).symm;have hcov:∀e∈bE G C q o p,v∈e\/e=s(as,bs):=λe he=>by
  induction e using Sym2.ind with|_ x' y'=>
  by_cases hv':v∈s(x',y')
  ·exact Or.inl hv'
  obtain⟨a',ha',b',hb',he'',-,-,hD'⟩:=hU2s x' y' he (λh=>hv' (h▸Sym2.mem_mk_left _ _)) (λh=>hv' (h▸Sym2.mem_mk_right _ _));rcases hD' with⟨h1',h2'⟩|⟨h1',-⟩
  ·exact Or.inr (by rw[he'',hAD a' ha' h1',hNa as b' hb' bs hbs hasp (hAB as has b' hb' hasD h2') hasbs])
  ·exact(hcol _ _ (hpB b' hb') (hcD b' h1').symm).elim
 obtain⟨PD,hPD,cD⟩:=fC hA hU1U (opnd C r (1-b)) (aE (bE G C q o p) v) λW' hW'=>aF h4 hU1E hW' v;rw[inter_eq_right.mpr λl hl=>((dK Z v l).mp (d5 W (aD.mp hl)).1).2.resolve_left hvnD]at cD;have hsp:∀U':Finset (Sym2 (Fin n)),s(as,bs)∈U' ->∀W',aB G U' W' ->¬(p∈W'/\as∈W'):=λU' hU' W' ⟨z',hz'⟩ ⟨hpW,haW⟩=>by
  have:=aQ h4 (Ne.symm hasp) (hz' p hpW).1.symm (hz' as haW).1.symm (hpB bs hbs) hasbs;subst this;exact(hz' as haW).2 (by rwa[Sym2.eq_swap])
 obtain⟨hA',hCh,hpA',hasA'⟩:=kN hA (Ne.symm hasp) hpA has (hsp _ (hU1U he'))
 have hρ:=kG hA H (Pp:=insert hA' PD) (λh hh=>by
  rcases mem_insert.mp hh with rfl|hh
  exacts[⟨_,hCh.1,λhf=>hsp _ he' _ hf ⟨hpA',hasA'⟩,hCh.2.2⟩,⟨_,hPD h hh⟩])
  hPb (Xs:=∅) (by simp)
 rw[card_insert_of_notMem λh=>(λh=>hasp (hAD p hpA h).symm) (aK (aJ hA) (hPD hA' h).2.2.2.2 hpA'),card_empty]at hρ
 have hu:(bE G C q o p).card<=(aE (bE G C q o p) v).card+1:=(card_le_card (t:=(aE (bE G C q o p) v).image (s(v,·))∪{s(as,bs)}) λe he=>by
    rcases hcov e he with h|h
    ·obtain⟨l,rfl⟩:=Sym2.mem_iff_exists.mp h;exact mem_union_left _ (mem_image_of_mem _ (aD.mpr he))
    ·exact mem_union_right _ (by rw[h];exact by simp)).trans
   ((card_union_le _ _).trans (by rw[card_singleton];exact Nat.add_le_add_right card_image_le 1))
 have hM:=hms {v,as} λe he=>(hcov e he).elim (⟨v,by simp,·⟩) λh=>⟨as,by simp,h▸Sym2.mem_mk_left _ _⟩;have h2c:({v,as}:Finset (Fin n)).card<=2:=card_le_two;rcases Nat.eq_zero_or_pos (centreless G C).card with h0|h0
 ·have hRc0:Rc=∅:=card_eq_zero.mp (by omega);obtain⟨m1,hm1,hbm1⟩:∃m'∈Ms,bs∈Wg m':=((hV bs).mp hbsV).resolve_left λ⟨w,hw,_⟩=>by simp[hRc0]at hw
  obtain⟨m2,hm2,hvm2⟩:∃m'∈Ms,v∈Wg m':=((hV v).mp hvV).resolve_left λ⟨w,hw,_⟩=>by simp[hRc0]at hw
  have hm12:m1≠m2:=by
   rintro rfl;obtain⟨z',hz'⟩:=(hMs m1 hm1).2.2.1;have:=aQ h4 (Ne.symm hvbs) (hz' bs hbm1).1.symm (hz' v hvm2).1.symm hasbs.symm (hvD as hasD);subst this;exact(hz' bs hbm1).2 (hU1U he')
  have:=one_lt_card.mpr ⟨m1,hm1,m2,hm2,hm12⟩;omega
 ·omega
end F
theorem l4_tf (hR1:cM) (col:Fin n ->Bool) (hcol:∀u v,G.Adj u v ->col u≠col v) (h4:NoFourCycle G) (hC:IsLeastAO G C) (hT:TopForm G C) (hj:(junk G C).card=2) (hoff:∀k∈junk G C,∀v:Fin n,gateVal n C k (unitInput v)=false):False:=by
 have hW:=p9 hR1 col hcol h4 hC hT hj hoff
 obtain⟨q,r,hqr,hJ,-,-,-,hA0,hA1,b,hb,hnb,hCne,-⟩:=jH hC hT hj hoff hW (λq r hqr hJ hnc=>by
   have hno:∀j∈junk G C,∀k∈junk G C,¬InCone n C j k:=λj hj k hk hc=>by
    have:=aP hc;rw[hJ,mem_insert,mem_singleton]at hj hk;rcases hj with rfl|rfl<;>rcases hk with rfl|rfl<;>first|omega|exact hnc hc
   refine fL hR1 col hcol ⟨hC,hT,h4,hj,hno,hoff,λj hjj B=>?_⟩;have hw:=eQ hR1 col hcol h4 hC hT hj hoff hjj λk hk=>hno k hk j hjj;fin_cases B
   exacts[hw.1,hw.2])
   (λq r hqr hJ h0 h1=>gI hR1 col hcol h4 hC hT q r hqr hJ hoff (hW q r hqr hJ) h0 h1)
   λq r b hqr hJ hb hnb he=>dZ hR1 col hcol h4 hC hT q r hqr hJ hoff (hW q r hqr hJ) b hb hnb he
 have Z:cI G C q r b:=⟨⟨hC,hT,h4,hqr,hJ,hoff,λB=>by
  fin_cases B
  exacts[hA0,hA1]⟩,hb,hnb,hCne⟩
 by_cases hg:b8 G C q r b
 ·exact jG hR1 col hcol Z hg
 have hfl:∀B:Fin 2,∀v∈orIn n C (opnd C q B),dX G C q v ->∀t∈orIn n C (opnd C q (1-B)),G.Adj v t:=λB v hv hu=>f8 Z.1 hv (bH hC.1 hu);by_cases h0:∃p∈orIn n C (opnd C q 0),dX G C q p
 ·obtain⟨p,hp,hpu⟩:=h0;by_cases h1:∃z∈orIn n C (opnd C q 1),dX G C q z
  ·obtain⟨z,hz,hzu⟩:=h1;exact eN hR1 col hcol Z ⟨p,hp,hpu,hfl 0 p hp hpu⟩ ⟨z,hz,hzu,λs hs=>(hfl 1 z hz hzu s hs).symm⟩
  ·exact uA hR1 col hcol Z hg 0 p hp hpu (hfl 0 p hp hpu) λz hz hu=>h1 ⟨z,hz,hu⟩
 ·by_cases h1:∃z∈orIn n C (opnd C q 1),dX G C q z
  ·obtain⟨z,hz,hzu⟩:=h1;exact uA hR1 col hcol Z hg 1 z hz hzu (hfl 1 z hz hzu) λp hp hu=>h0 ⟨p,hp,hu⟩
  ·refine nG hR1 col hcol Z λu v he=>?_;rcases uD Z hg he with⟨hx,w,hw,hu⟩|h
   ·rcases l8 Z.1 0 hx hw with h|h;exacts[(h0 ⟨w,h,hu⟩).elim,(h1 ⟨w,h,hu⟩).elim]
   ·exact h
end PEqualNP.Outside.L_meta_5126
theorem PEqualNP.Outside.L_meta_5126 :
  (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool),
    (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsLeastAO G C →
    (PEqualNP.TopForm.junk G C).card ≠ 1) →
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool),
    (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsLeastAO G C →
    (∀ k ∈ PEqualNP.TopForm.junk G C, ∀ v : Fin n, PEqualNP.EdgeOwnership.gateVal n C k (PEqualNP.SplitCount.unitInput v) = false) →
    (PEqualNP.TopForm.junk G C).card ≠ 2 := by
  intro hR1 n G _ C s hs h4 hC hoff hj
  obtain ⟨C', hC', hT', -, hj', hoff'⟩ := PEqualNP.Outside.L_meta_5126.l1_normalize G C hC hoff
  exact PEqualNP.Outside.L_meta_5126.l4_tf hR1 s hs h4 hC' hT' (hj' ▸ hj) hoff'
