import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_6026
open PEqualNP.CircuitLowerBounds
open List (mem_cons mem_map mem_map_of_mem map_cons map_map all_eq_true any_eq_true length_map getD_eq_getElem?_getD getElem_mem getElem?_map sum_cons nodup_cons mem_toFinset contains_eq_mem countP_cons mem_range mem_cons_self mem_cons_of_mem length_cons getElem_cons_succ map_nil foldr_cons foldr_nil foldl_cons getD_eq_getElem getD_eq_default mem_append length_ofFn)
open Bool (and_eq_true or_eq_true false_eq_true noConfusion)
open Finset (mem_insert_of_mem mem_insert_self mem_erase mem_insert insert_erase card_insert_of_notMem mem_union)
open Nat (beq_eq ble_eq add_eq testBit_and testBit_two_pow reduceAdd reduceSub reduceDiv testBit_or testBit_succ pow_succ pow_zero eq_of_testBit_eq ble land lor xor shiftLeft add_sub_of_le)
open BitVec (toNat_inj getLsbD_and getLsbD_or getLsbD_not getLsbD_allOnes toNat_and toNat_or eq_of_getLsbD_eq ofBoolListLE allOnes and_allOnes)
namespace Core
noncomputable section
class Width where
 wide:Bool
abbrev W [w:Width]:Nat:=if w.wide then 1024 else 512
abbrev N [w:Width]:Nat:=if w.wide then 10 else 9
instance [w:Width]:NeZero W:=⟨by rcases w with ⟨_|_⟩<;>decide⟩
lemma nY [w:Width]:W=2 ^ N:=by rcases w with ⟨_|_⟩<;>decide
abbrev aQ [Width]:=BitVec W
abbrev bW [Width]:=Fin W
section
variable [w : Width]
def zero:aQ:=0
def one:aQ:=allOnes W
def mK:Nat:=match w with|⟨false⟩=>0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff|⟨true⟩=>0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
lemma mL:mK=one.toNat:=by rcases w with ⟨_|_⟩<;>decide +kernel
def eh (a:aQ):aQ := ~~~a
def bM (d:Nat) (a b:aQ):aQ:=if d=0 then a&&&b else if d=1 then a|||b else if d=2 then a &&& ~~~b else ~~~a&&&b
def bg (a:aQ):Prop:=a≠zero/\a≠one
end
def bY (u:Bool) (d:Nat):Prop:=d<2\/(u=true/\d<4)
def gJ (d:Nat):=if d=2 then 3 else if d=3 then 2 else d
lemma cq {u d} (h:bY u d):d=0\/d=1\/(u=true/\d=2)\/(u=true/\d=3):=by
 rcases h with h|⟨h,j⟩
 . omega
 . have:d=0\/d=1\/d=2\/d=3:=by omega
   rcases this with h1|h1|h1|h1
   . exact Or.inl h1
   . exact Or.inr (Or.inl h1)
   . exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
   . exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
section
variable [w : Width]
lemma gE {u d} (h:bY u d) (a b:aQ):bM d a b=bM (gJ d) b a:=by rcases cq h with rfl|rfl|⟨_,rfl⟩|⟨_,rfl⟩<;>simp [bM,gJ,BitVec.and_comm,BitVec.or_comm]
end
lemma rY {u d} (h:bY u d):bY u (gJ d)/\gJ (gJ d)=d:=by
 rcases cq h with rfl|rfl|⟨hu,rfl⟩|⟨hu,rfl⟩
 all_goals simp_all [gJ,bY]
section
variable [w : Width]
def cL (u:Bool) (target:aQ):Nat->Finset aQ->Prop
 | 0,S=>S={target}/\bg target
 | k+1,S => ∃ (U:Finset aQ) (a b:aQ) (d:Nat),bY u d/\S=insert a (insert b U) /\
  bg a/\bg b/\a≠b /\
  bM d a b ∉ insert a (insert b U)/\cL u target k (insert (bM d a b) U)
lemma cL.stop {u} {target:aQ} (hp:bg target):cL u target 0 {target}:=⟨rfl,hp⟩
lemma cL.binary {u} {target:aQ} {k:Nat} {U:Finset aQ} {a b:aQ} {d:Nat} (hd:bY u d) (ha:bg a) (hb:bg b) (hab:a≠b) (hfresh:bM d a b ∉ insert a (insert b U)) (tail:cL u target k (insert (bM d a b) U)):cL u target (k+1) (insert a (insert b U)):=⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
lemma cL.ind {u} {target:aQ} {motive:∀ (k:Nat) (S:Finset aQ),cL u target k S->Prop} (stop:∀ (hp:bg target),motive 0 {target} (cL.stop hp)) (binary:∀ {k:Nat} {U:Finset aQ} {a b:aQ} {d:Nat} (hd:bY u d) (ha:bg a) (hb:bg b) (hab:a≠b) (hfresh:bM d a b ∉ insert a (insert b U)) (tail:cL u target k (insert (bM d a b) U)),motive k (insert (bM d a b) U) tail ->motive (k+1) (insert a (insert b U)) (cL.binary hd ha hb hab hfresh tail)) {k:Nat} {S:Finset aQ} (h:cL u target k S):motive k S h:=by
 induction k generalizing S with
 | zero =>
  obtain ⟨rfl,hp⟩:=h;exact stop hp
 | succ k ih =>
  obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩:=h;exact binary hd ha hb hab hf tail (ih tail)
lemma eI {u target k S} (h:cL u target k S):∀ a ∈ S,bg a:=by
 induction h using cL.ind with
 | stop hp=>simpa using hp
 | binary hd ha hb hab hf _ ih =>
  simp only [Finset.forall_mem_insert];exact ⟨ha,hb,fun a h=>ih a (mem_insert_of_mem h)⟩
lemma g9 {u target k S} (h:cL u target k S):S.card ≤ k+1:=by
 induction h using cL.ind with
 | stop hp=>simp
 | @binary k U a b d hd ha hb hab hf _ ih =>
  have hu:bM d a b ∉ U:=fun hm=>hf (mem_insert_of_mem (mem_insert_of_mem hm));rw [card_insert_of_notMem hu] at ih;have h1:=Finset.card_insert_le (a:=a) (s:=insert b U);have h2:=Finset.card_insert_le (a:=b) (s:=U);omega
def aV (i:bW) (a:aQ):Bool:=a.getLsbD i.val
lemma cn (i):aV i zero=false:=by simp [aV,zero]
lemma d0 (i):aV i one=true:=by unfold aV one;rw [getLsbD_allOnes];simp
lemma f6 (i) (a:aQ):aV i (eh a) = !(aV i a):=by simp [aV,eh,i.isLt]
lemma dQ (i d) (a b:aQ):aV i (bM d a b)=(if d=0 then aV i a&&aV i b else if d=1 then aV i a||aV i b else if d=2 then aV i a && !(aV i b) else !(aV i a)&&aV i b):=by
 unfold bM
 split_ifs<;>simp [aV]
lemma dA {a b:aQ} (h:∀ i,aV i a=aV i b):a=b:=eq_of_getLsbD_eq fun j hj=>h ⟨j,hj⟩
def fM (u:Bool) (a:aQ):aQ:=if u&&aV 0 a then eh a else a
lemma lS (a:aQ):fM false a=a:=rfl
lemma yd (a:aQ):aV 0 (fM true a)=false:=by cases h:aV 0 a<;>simp [fM,h,f6]
lemma kC {u} {a:aQ} (h:aV 0 a=false):fM u a=a:=by simp [fM,h]
lemma yc' (a:aQ):eh (eh a)=a:=by simp [eh]
lemma rg (a:aQ):fM true (eh a)=fM true a:=by cases h:aV 0 a<;>simp [fM,h,f6,yc']
lemma pi {a:aQ} (h:bg (eh a)):bg a:=by
 refine ⟨?_,?_⟩
 . rintro rfl;exact h.2 (by simp [eh,zero,one])
 . rintro rfl;exact h.1 (by simp [eh,zero,one])
lemma kI {u} {a:aQ} (h:bg (fM u a)):bg a:=by
 unfold fM at h
 split at h
 . exact pi h
 . exact h
def eM (d:Bool) (a b:aQ):=if d then a|||b else a&&&b
lemma ff (i) (d:Bool) (a b:aQ):aV i (eM d a b)=(if d then aV i a||aV i b else aV i a&&aV i b):=by cases d<;>simp [eM,aV]
lemma sp (d:Bool) (a b:aQ):∃ e,e<4/\fM true (eM d a b)=bM e (fM true a) (fM true b):=by
 refine ⟨if d then (if aV 0 a then (if aV 0 b then 0 else 2) else (if aV 0 b then 3 else 1))
  else (if aV 0 a then (if aV 0 b then 1 else 3) else (if aV 0 b then 2 else 0)),?_,?_⟩
 . split_ifs<;>omega
 . apply dA;intro i
   cases d<;>cases ha:aV 0 a<;>cases hb:aV 0 b <;>
    simp only [fM,ff,ha,hb,dQ,f6,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
     Bool.or_false,Bool.true_or,Bool.or_true,false_eq_true,ite_true,ite_false] <;>
    cases hx:aV i a<;>cases hy:aV i b<;>simp [hx,hy,f6,ff]
def gv (w:List aQ) (g:Gate):aQ:=
 let xs:=g.inputs.map (fun i=>w.getD i zero)
 match g.op with
 | .and=>xs.foldr (eM false) one
 | .or=>xs.foldr (eM true) zero
 | .not=>eh (xs.headD zero)
 | _=>zero
def dB (gs:List Gate) (w:List aQ):List aQ:=gs.foldl (fun l g=>l ++ [gv l g]) w
def cK (w:List aQ) (v:aQ):Prop:=v ∈ w\/¬bg v
def gA (u:Bool) (w:List aQ) (v:aQ):Prop:=cK w (fM u v)
lemma fm (a:aQ):bM 0 a one=a/\bM 1 a zero=a/\bM 0 a zero=zero/\bM 1 a one=one/\bM 0 a a=a/\bM 1 a a=a/\bM 2 a a=zero/\bM 3 a a=zero/\bM 2 a zero=a/\bM 3 zero a=a/\bM 2 zero a=zero/\bM 3 a zero=zero/\bM 0 zero a=zero/\bM 1 zero a=a/\bM 0 one a=a/\bM 1 one a=one:=by
 refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩<;>apply dA<;>intro i <;>
  simp [dQ,cn,d0]
lemma wh:eh zero=one/\eh one=zero:=by simp [eh,zero,one]
lemma hK {w:List aQ} {a:aQ} (h:cK w a):a=zero\/a=one\/a ∈ w/\bg a:=by
 by_cases hz:a=zero
 . exact Or.inl hz
 by_cases ho:a=one
 . exact Or.inr (Or.inl ho)
 exact Or.inr (Or.inr ⟨h.resolve_right (fun x=>x ⟨hz,ho⟩),hz,ho⟩)
def hD (u:Bool) (w:List aQ) (z:aQ):Prop := ∃ d a b,bY u d/\a ∈ w/\b ∈ w/\bg a/\bg b/\a≠b/\z=bM d a b
lemma q8 {u w a b} (d:Nat) (hd:bY u d) (ha:cK w a) (hb:cK w b) (no:u=true->a≠one/\b≠one):cK w (bM d a b)\/hD u w (bM d a b):=by
 have rz:cK w zero:=Or.inr (fun h=>h.1 rfl);have ro:cK w one:=Or.inr (fun h=>h.2 rfl);obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩:=fm a;obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,yW,b11,b12,b13,b14,b15,b16⟩:=fm b
 by_cases he:a=b
 . subst b;left
   rcases cq hd with rfl|rfl|⟨_,rfl⟩|⟨_,rfl⟩
   . exact a5.symm ▸ ha
   . exact a6.symm ▸ ha
   . exact a7.symm ▸ rz
   . exact a8.symm ▸ rz
 rcases hK ha with rfl|rfl|⟨ham,hap⟩
 . left
   rcases cq hd with rfl|rfl|⟨_,rfl⟩|⟨_,rfl⟩
   . exact b13.symm ▸ rz
   . exact b14.symm ▸ hb
   . exact b11.symm ▸ rz
   . exact yW.symm ▸ hb
 . left
   rcases cq hd with rfl|rfl|⟨hu,rfl⟩|⟨hu,rfl⟩
   . exact b15.symm ▸ hb
   . exact b16.symm ▸ ro
   . exact absurd rfl (no hu).1
   . exact absurd rfl (no hu).1
 rcases hK hb with rfl|rfl|⟨hbm,hbp⟩
 . left
   rcases cq hd with rfl|rfl|⟨_,rfl⟩|⟨_,rfl⟩
   . exact a3.symm ▸ rz
   . exact a2.symm ▸ ha
   . exact a9.symm ▸ ha
   . exact a12.symm ▸ rz
 . left
   rcases cq hd with rfl|rfl|⟨hu,rfl⟩|⟨hu,rfl⟩
   . exact a1.symm ▸ ha
   . exact a4.symm ▸ ro
   . exact absurd rfl (no hu).2
   . exact absurd rfl (no hu).2
 exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩
lemma jk (a:aQ):fM true a≠one:=by
 intro h;have:=yd a;rw [h,d0] at this;exact noConfusion this
lemma lW {u w a b} (d:Bool) (ha:gA u w a) (hb:gA u w b):gA u w (eM d a b)\/hD u w (fM u (eM d a b)):=by
 cases u
 . have e:eM d a b=bM (if d then 1 else 0) a b:=by cases d<;>rfl
   have h:=q8 (u:=false) (if d then 1 else 0) (Or.inl (by split<;>omega)) ha hb (by simp)
   unfold gA;simp only [lS] at h ⊢;rwa [e]
 . obtain ⟨e,he,eq⟩:=sp d a b;unfold gA;rw [eq];exact q8 e (Or.inr ⟨rfl,he⟩) ha hb (fun _=>⟨jk a,jk b⟩)
lemma fB {u w} {v:aQ} (h:v=zero\/v=one):gA u w v:=by
 refine Or.inr fun hp => ?_
 have:=kI hp
 rcases h with rfl|rfl
 . exact this.1 rfl
 . exact this.2 rfl
lemma g6 {u} (w:List aQ) (i:Nat):gA u (w.map (fM u)) (w.getD i zero):=by
 simp only [getD_eq_getElem?_getD]
 cases h:w[i]? with
 | none=>exact fB (Or.inl rfl)
 | some a=>exact Or.inl (mem_map_of_mem (List.mem_of_getElem? h))
lemma wt {w a} (h:gA true w a):gA true w (eh a):=by
 unfold gA;rwa [rg]
def eH (g:Gate):Bool:=match g.op with
 | .not=>true
 | _=>false
lemma uh (u:Bool) (w:List aQ) (g:Gate) (h:g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\g.inputs.length≤2) (mono:u=false->eH g=false):gA u (w.map (fM u)) (gv w g)\/(eH g=false/\hD u (w.map (fM u)) (fM u (gv w g))):=by
 obtain ⟨o,l⟩:=g;simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h;obtain ⟨ho,hl⟩:=h
 have prim (d:Bool):gA u (w.map (fM u)) ((l.map (fun i=>w.getD i zero)).foldr (eM d) (if d then zero else one)) \/
  hD u (w.map (fM u)) (fM u ((l.map (fun i=>w.getD i zero)).foldr (eM d) (if d then zero else one))):=by
  have unit (v:aQ):eM d v (if d then zero else one)=v:=by
   apply dA;intro i
   cases d<;>simp [ff,cn,d0]
  cases l with
  | nil=>exact Or.inl (fB (by cases d<;>simp))
  | cons i l =>
   cases l with
   | nil =>
    simp only [map_cons,map_nil,foldr_cons,foldr_nil,unit];exact Or.inl (g6 w i)
   | cons j l =>
    cases l with
    | cons a l=>simp at hl
    | nil =>
     simp only [map_cons,map_nil,foldr_cons,foldr_nil,unit];exact lW d (g6 w i) (g6 w j)
 rcases ho with rfl|rfl|rfl
 . exact (prim false).imp id (fun h=>⟨rfl,h⟩)
 . exact (prim true).imp id (fun h=>⟨rfl,h⟩)
 . cases u
   . exact absurd (mono rfl) (by simp [eH])
   left
   cases l with
   | nil=>exact fB (Or.inr (by simp [gv,wh]))
   | cons i l=>exact wt (g6 w i)
lemma lX {u target} {w:List aQ} {z:aQ} {k S c} (h:cL u target k S) (hz:cK w z\/(c=1/\hD u w z)) (sub:∀ a ∈ S,a ∈ w++[z]):∃ k' S',k' ≤ k+c/\cL u target k' S'/\∀ a ∈ S',a ∈ w:=by
 by_cases hm:z ∈ S
 . by_cases hw:z ∈ w
   . refine ⟨k,S,by omega,h,?_⟩
     intro a ha
     have hu:a ∈ w\/a=z:=by simpa using sub a ha
     rcases hu with hu|rfl
     . exact hu
     . exact hw
   . have hp:=eI h z hm
     rcases hz with hr|⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
     . exact False.elim ((hr.resolve_left hw) hp)
     . subst z;let U:=S.erase (bM d a b)
       have ht:cL u target k (insert (bM d a b) U):=by simpa [U,insert_erase hm] using h
       have hu:∀ v ∈ U,v ∈ w:=by
        intro v hv;obtain ⟨hne,hm⟩:=mem_erase.mp hv;simpa [hne] using sub v hm
       have hf:bM d a b ∉ insert a (insert b U):=by
        intro hh
        rcases mem_insert.mp hh with eq|u
        . exact hw (eq.symm ▸ ha)
        rcases mem_insert.mp u with eq|u
        . exact hw (eq.symm ▸ hb)
        . exact hw (hu _ u)
       exact ⟨_,_,Nat.le_refl _,cL.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
 . refine ⟨k,S,by omega,h,?_⟩
   intro a ha;have hn:a≠z:=fun hh=>hm (hh ▸ ha);simpa [hn] using sub a ha
lemma ra {u target} (gs:List Gate) (w:List aQ) (legal:∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\g.inputs.length≤2) (mono:u=false->∀ g ∈ gs,eH g=false) (hp:bg target) (hout:target ∈ (dB gs w).map (fM u)):∃ k S,k ≤ gs.countP (fun g => !eH g)/\cL u target k S/\∀ a ∈ S,a ∈ w.map (fM u):=by
 induction gs generalizing w with
 | nil=>exact ⟨0,{target},by simp,cL.stop hp,by simpa [dB] using hout⟩
 | cons g gs ih =>
  obtain ⟨k,S,hk,ht,hs⟩:=ih (w++[gv w g]) (fun a ha=>legal a (by simp [ha]))
   (fun hu a ha=>mono hu a (by simp [ha])) hout
  have rep:=uh u w g (legal g (by simp)) (fun hu=>mono hu g (by simp));rw [List.map_append] at hs
  have rep':cK (w.map (fM u)) (fM u (gv w g)) \/
   ((if eH g then 0 else 1)=1/\hD u (w.map (fM u)) (fM u (gv w g))):=
   rep.imp id (fun h=>⟨by simp [h.1],h.2⟩)
  obtain ⟨l,T,hl,hu,hT⟩:=lX ht rep' hs
  refine ⟨l,T,?_,hu,hT⟩
  rw [countP_cons]
  cases hn:eH g<;>simp [hn] at hl ⊢<;>omega
lemma oG (i) (w:List aQ) (j:Nat):(w.map (aV i)).getD j false=aV i (w.getD j zero):=by
 simp only [getD_eq_getElem?_getD,getElem?_map]
 cases w[j]? with
 | none=>exact (cn _).symm
 | some a=>rfl
lemma yg (i) (g:Gate) (w:List aQ) (hg:g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)):aV i (gv w g)=g.op.eval (g.inputs.map fun j=>(w.map (aV i)).getD j false):=by
 obtain ⟨o,l⟩:=g;simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg;simp only [oG]
 rcases hg with rfl|rfl|rfl
 . induction l with
   | nil=>exact d0 _
   | cons a l ih =>
    change aV i (eM false _ _)=(_&&_);rw [ff];exact congrArg (fun x=>aV i (w.getD a zero)&&x) ih
 . induction l with
   | nil=>exact cn _
   | cons a l ih =>
    change aV i (eM true _ _)=(_||_);rw [ff];exact congrArg (fun x=>aV i (w.getD a zero)||x) ih
 . cases l with
   | nil =>
    change aV i (eh zero) = !false;rw [f6,cn]
   | cons a l=>exact f6 _ _
lemma io (gs:List Gate) (i) (w:List aQ) (hg:∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)):(dB gs w).map (aV i)=gs.foldl (fun (l:List Bool) g=>l++[g.op.eval (g.inputs.map fun j=>l.getD j false)]) (w.map (aV i)):=by
 induction gs generalizing w with
 | nil=>rfl
 | cons g gs ih =>
  change (dB gs (w++[gv w g])).map _=_;rw [ih _ (fun a ha=>hg a (by simp [ha]))];simp only [foldl_cons,List.map_append,List.map_singleton,yg i g w (hg g (by simp))]
end
abbrev bL (R:Type):=R->Bool
def ln {R} (a:bL R):bL R:=fun r => !(a r)
def cd {R} (isOr:Bool) (a b:bL R):bL R:=if isOr then fun r=>a r||b r else fun r=>a r&&b r
def jp {R} (d:Nat) (a b:bL R):bL R:=
 if d=0 then cd false a b else if d=1 then cd true a b else
  if d=2 then cd false a (ln b) else cd false (ln a) b
def bw {R} (a:bL R):Prop := ∃ b:Bool,a=fun _=>b
def eV {R} (a:bL R):Nat:=by classical exact if bw a then 1 else 0
def ga {R} (xs:List (bL R)):Nat:=(xs.map eV).sum
def aO {R} (u:Bool) (pool:List (bL R)) (v:bL R):Prop:=v ∈ pool\/bw v\/(u=true/\ln v ∈ pool)
def h9 {R} (u:Bool) (pool xs:List (bL R)) := ∀ a ∈ xs,aO u pool a
def bH {R} (u:Bool) (roots:List (bL R)):Nat->List (bL R)->Prop
 | 0,b=>b=roots
 | p+1,c => ∃ (op:Bool) (bank:List (bL R)) (a b:bL R),bH u roots p bank/\aO u bank a /\
  aO u bank b/\c=cd op a b :: bank
lemma bH.start {R u} {roots:List (bL R)}:bH u roots 0 roots:=rfl
lemma bH.two {R u} {roots:List (bL R)} {p bank a b} (op:Bool) (h:bH u roots p bank) (ha:aO u bank a) (hb:aO u bank b):bH u roots (p+1) (cd op a b :: bank):=⟨op,bank,a,b,h,ha,hb,rfl⟩
lemma bH.ind {R u} {roots:List (bL R)} {motive:∀ p bank,bH u roots p bank->Prop} (start:motive 0 roots bH.start) (two:∀ {p bank a b} (op:Bool) (h:bH u roots p bank) (ha:aO u bank a) (hb:aO u bank b),motive p bank h ->motive (p+1) (cd op a b :: bank) (bH.two op h ha hb)) {p bank} (h:bH u roots p bank):motive p bank h:=by
 induction p generalizing bank with
 | zero =>
  obtain rfl:=h;exact start
 | succ p ih =>
  obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩:=h;exact two op h ha hb (ih h)
def cT {α:Type} (save:Bool) (x : α) (xs:List α):=if save then x::xs else xs
def g2 {R} (u:Bool) (goal:bL R):Nat->List (bL R)->Prop
 | 0,zs=>List.Perm [goal] zs
 | s+1,zs => ∃ (op:Nat) (ka kb:Bool) (a b:bL R) (rest:List (bL R)),bY u op/\(a::b::rest).Perm zs /\
  g2 u goal s (jp op a b :: cT ka a (cT kb b rest))
lemma g2.stop {R u} {goal:bL R}:g2 u goal 0 [goal]:=List.Perm.refl _
lemma g2.perm {R u} {goal:bL R} {s:Nat} {xs zs:List (bL R)} (p:xs.Perm zs) (h:g2 u goal s xs):g2 u goal s zs:=by
 cases s with
 | zero=>exact List.Perm.trans h p
 | succ s =>
  obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩:=h;exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
lemma g2.two {R u} {goal:bL R} {s:Nat} {a b:bL R} {rest:List (bL R)} (op:Nat) (hd:bY u op) (ka kb:Bool) (h:g2 u goal s (jp op a b :: cT ka a (cT kb b rest))):g2 u goal (s+1) (a::b::rest):=⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
lemma g2.ind {R u} {goal:bL R} {motive:∀ s ws,g2 u goal s ws->Prop} (stop:motive 0 [goal] g2.stop) (perm:∀ {s xs zs} (p:List.Perm xs zs) (h:g2 u goal s xs),motive s xs h->motive s zs (g2.perm p h)) (two:∀ {s a b rest} (op:Nat) (hd:bY u op) (ka kb:Bool) (h:g2 u goal s (jp op a b :: cT ka a (cT kb b rest))),motive s _ h->motive (s+1) (a::b::rest) (g2.two op hd ka kb h)) {s ws} (h:g2 u goal s ws):motive s ws h:=by
 induction s generalizing ws with
 | zero=>exact perm h g2.stop stop
 | succ s ih =>
  obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩:=h;exact perm p (g2.two op hd ka kb h) (two op hd ka kb h (ih h))
lemma fh {R} (a:bL R) (xs):ga (a::xs)=eV a+ga xs:=by simp [ga]
lemma lP {R} (a:bL R) (xs) (k:Bool):ga xs ≤ ga (cT k a xs):=by cases k<;>simp [cT,fh]
lemma f8 {R} {a:bL R} (h:bw a):bw (ln a):=by
 obtain ⟨v,rfl⟩:=h;exact ⟨!v,rfl⟩
lemma rd' {R} (a:bL R):ln (ln a)=a:=by
 funext r
 simp [ln]
lemma mR {R} (a:bL R):eV (ln a)=eV a:=by
 have:bw (ln a) ↔ bw a:=⟨fun h=>rd' a ▸ f8 h,f8⟩
 by_cases h:bw a
 . simp only [eV,if_pos h,if_pos (this.mpr h)]
 . simp only [eV,if_neg h,if_neg (fun x=>h (this.mp x))]
lemma iQ {R u} {bank:List (bL R)} {a} (hu:u=true) (h:aO u bank a):aO u bank (ln a):=by
 rcases h with h|h|⟨_,h⟩
 . exact Or.inr (Or.inr ⟨hu,(rd' a).symm ▸ h⟩)
 . exact Or.inr (Or.inl (f8 h))
 . exact Or.inl h
lemma kY {R} {a b:bL R} (op) (h:bw a) (g:bw b):bw (cd op a b):=by
 obtain ⟨v,rfl⟩:=h;obtain ⟨w,rfl⟩:=g
 cases op<;>exact ⟨_,rfl⟩
lemma k1 {R u} (op) {a b:bL R} {bank} (h:bw a\/bw b) (ha:aO u bank a) (hb:aO u bank b):aO u bank (cd op a b):=by
 rcases h with ⟨v,rfl⟩|⟨v,rfl⟩
 . cases op<;>cases v
   . exact Or.inr (Or.inl ⟨false,by funext x;simp [cd]⟩)
   . simpa [cd] using hb
   . simpa [cd] using hb
   . exact Or.inr (Or.inl ⟨true,by funext x;simp [cd]⟩)
 . cases op<;>cases v
   . exact Or.inr (Or.inl ⟨false,by funext x;simp [cd]⟩)
   . simpa [cd] using ha
   . simpa [cd] using ha
   . exact Or.inr (Or.inl ⟨true,by funext x;simp [cd]⟩)
lemma gD {R u} {bank v} (w:bL R) (h:aO u bank v):aO u (w::bank) v:=h.imp (mem_cons_of_mem _) (Or.imp id (And.imp id (mem_cons_of_mem _)))
lemma oJ {R u} (roots:List (bL R)) {p bank a b} (op) (hp:bH u roots p bank) (ha:aO u bank a) (hb:aO u bank b):∃ q next,bH u roots q next/\aO u next (cd op a b)/\(∀ v,aO u bank v->aO u next v)/\q+eV a+eV b ≤ p+1+eV (cd op a b):=by
 classical
 by_cases c:bw a\/bw b
 . refine ⟨p,bank,hp,k1 op c ha hb,fun _ h=>h,?_⟩
   by_cases ca:bw a<;>by_cases cb:bw b
   . simp [eV,ca,cb,kY op ca cb]
   . simp [eV,ca,cb]
   . simp [eV,ca,cb]
   . exact False.elim (c.elim ca cb)
 . have ca:¬bw a:=fun h=>c (Or.inl h);have cb:¬bw b:=fun h=>c (Or.inr h)
   exact ⟨p+1,_,bH.two op hp ha hb,Or.inl (by simp),fun _ h=>gD _ h,
    by simp [eV,ca,cb]⟩
lemma jL {R u} {bank:List (bL R)} {d a b} (hd:bY u d) (ha:aO u bank a) (hb:aO u bank b):∃ op x y,jp d a b=cd op x y/\aO u bank x/\aO u bank y/\eV x=eV a/\eV y=eV b:=by
 rcases cq hd with rfl|rfl|⟨hu,rfl⟩|⟨hu,rfl⟩
 . exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
 . exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
 . exact ⟨false,a,ln b,rfl,ha,iQ hu hb,rfl,mR b⟩
 . exact ⟨false,ln a,b,rfl,iQ hu ha,hb,mR a,rfl⟩
lemma mW {R u} (roots:List (bL R)) {p bank a b} (d) (hd:bY u d) (hp:bH u roots p bank) (ha:aO u bank a) (hb:aO u bank b):∃ q next,bH u roots q next/\aO u next (jp d a b)/\(∀ v,aO u bank v->aO u next v)/\q+eV a+eV b ≤ p+1+eV (jp d a b):=by
 obtain ⟨op,x,y,e,hx,hy,cx,cy⟩:=jL hd ha hb;rw [e,<-cx,<-cy];exact oJ roots op hp hx hy
lemma nt {α:Type} {k:Bool} {x a : α} {xs} (h:x ∈ cT k a xs):x=a\/x∈xs:=by cases k<;>simp_all [cT]
lemma mQ {R u} {goal:bL R} (nc:¬bw goal) {s ws} (h:g2 u goal s ws) (roots:List (bL R)) {p bank} (hp:bH u roots p bank) (hs:h9 u bank ws):∃ q next,bH u roots q next/\aO u next goal/\q+ga ws ≤ p+s:=by
 classical
 induction h using g2.ind generalizing p bank with
 | stop =>
  exact ⟨p,bank,hp,hs _ (by simp),by simp [ga,eV,nc]⟩
 | perm eq _ ih =>
  have hsub:h9 u bank _:=fun v hv=>hs v (eq.mem_iff.mp hv);obtain ⟨q,W,hW,hv,hl⟩:=ih hp hsub;exact ⟨q,W,hW,hv,by simpa only [ga,<-(eq.map eV).sum_eq] using hl⟩
 | @two s a b rest op hd ka kb _ ih =>
  obtain ⟨r,T,hT,hz,inc,le⟩:=mW roots op hd hp (hs a (by simp)) (hs b (by simp))
  have ht:h9 u T (jp op a b :: cT ka a (cT kb b rest)):=by
   intro v h
   rcases mem_cons.mp h with rfl|hh
   . exact hz
   . apply inc v;apply hs
     rcases nt hh with rfl|hh
     . simp
     . exact mem_cons_of_mem _ (mem_cons.mpr (nt hh))
  obtain ⟨q,W,hW,hv,hl⟩:=ih hT ht;have hlen:=lP a (cT kb b rest) ka;have hlen':=lP b rest kb;rw [fh] at hl
  refine ⟨q,W,hW,hv,?_⟩
  rw [fh,fh];omega
def au {R S:Type} (rows:S->R) (a:bL R):bL S:=fun r=>a (rows r)
lemma k4 {R S:Type} (rows:S->R) (k:Bool) (a:bL R) (ws):(cT k a ws).map (au rows)=cT k (au rows a) (ws.map (au rows)):=by cases k<;>simp [cT]
lemma hQ {R S:Type} (rows:S->R) (d) (a b:bL R):au rows (jp d a b)=jp d (au rows a) (au rows b):=by
 unfold jp
 split_ifs<;>rfl
lemma mr {R S:Type} {u} (rows:S->R) {goal s ws} (h:g2 u goal s ws):g2 u (au rows goal) s (ws.map (au rows)):=by
 induction h using g2.ind with
 | stop=>exact g2.stop
 | perm p _ ih=>exact g2.perm (p.map _) ih
 | two op hd ka kb _ ih =>
  simp only [map_cons,k4,hQ] at ih ⊢;exact g2.two op hd ka kb ih
lemma eP {R S:Type} {u} (rows:S->R) {goal s ws} (h:g2 u goal s ws) (nc:¬bw (au rows goal)) {roots:List (bL S)} {p bank L} (hp:bH u roots p bank) (hs:h9 u bank (ws.map (au rows))) (hl:∀ q bs,bH u roots q bs->aO u bs (au rows goal)->L ≤ q):L+ga (ws.map (au rows)) ≤ p+s:=by
 obtain ⟨q,bs,hq,ht,hle⟩:=mQ nc (mr rows h) roots hp hs;have hqle:=hl q bs hq ht;omega
lemma fk {R S u} (rows:S->R) {bank:List (bL R)} {a:bL R} (h:aO u bank a):aO u (bank.map (au rows)) (au rows a):=by
 rcases h with h|⟨c,rfl⟩|⟨hu,h⟩
 . exact Or.inl (mem_map_of_mem h)
 . exact Or.inr (Or.inl ⟨c,rfl⟩)
 . exact Or.inr (Or.inr ⟨hu,mem_map_of_mem h⟩)
lemma kK {R S u} (rows:S->R) {roots:List (bL R)} {p bank} (h:bH u roots p bank):bH u (roots.map (au rows)) p (bank.map (au rows)):=by
 induction h using bH.ind with
 | start=>exact bH.start
 | @two p bank a b op _ ha hb ih =>
  have hc:au rows (cd op a b)=cd op (au rows a) (au rows b):=by
   cases op<;>rfl
  rw [map_cons,hc];exact bH.two op ih (fk rows ha) (fk rows hb)
section
variable [w : Width]
def aG (a:aQ):bL bW:=fun r=>aV r a
def eT (f:bL bW):aQ:=(ofBoolListLE (List.ofFn f)).cast (length_ofFn)
lemma d6 (f:bL bW) (r:bW):aV r (eT f)=f r:=by simp only [aV,eT,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,getD_eq_getElem?_getD,List.getElem?_ofFn];simp [r.isLt]
lemma fR (v:aQ):eT (aG v)=v:=by
 apply eq_of_getLsbD_eq;intro j hj;exact d6 (aG v) ⟨j,hj⟩
lemma k2 (f:bL bW):aG (eT f)=f:=by
 funext r
 exact d6 f r
lemma ri (a:aQ):aG (eh a)=ln (aG a):=by
 funext r
 exact f6 _ _
lemma rh (d:Nat) (a b:aQ):aG (bM d a b)=jp d (aG a) (aG b):=by
 funext r
 simp only [aG,dQ,jp]
 split_ifs<;>rfl
lemma np {α β:Type} (f : α -> β) (d:Bool) (a : α) (l:List α):(cT d a l).map f=cT d (f a) (l.map f):=by cases d<;>rfl
lemma g7 {α:Type} (k:Bool) (a : α) (l:List α) (hn:l.Nodup) (ha:a ∉ l):(cT k a l).Nodup:=by cases k<;>simp [cT,hn,ha]
lemma fY (k:Bool) (a:aQ) (l:List aQ):(cT k a l).toFinset=if k then insert a l.toFinset else l.toFinset:=by cases k<;>simp [cT]
lemma kq {u} {T:aQ} {k S} (h:cL u T k S) (v:List aQ) (hv:v.Nodup) (eqv:v.toFinset=S):g2 u (aG T) k (v.map aG):=by
 classical
 induction h using cL.ind generalizing v with
 | stop hp =>
  have eq:[T].Perm v:=by
   apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv;simpa [eqv]
  exact g2.perm (eq.map _) g2.stop
 | @binary k U a b d hd ha hb hab fresh _ ih =>
  let rest:=((U.erase a).erase b).toList;let ka:=decide (a ∈ U);let kb:=decide (b ∈ U);let mid:=cT kb b rest;let tail:=cT ka a mid
  have er:rest.toFinset=(U.erase a).erase b:=by simp [rest]
  have ar:a ∉ rest:=by simp [rest]
  have br:b ∉ rest:=by simp [rest]
  have hr:rest.Nodup:=Finset.nodup_toList _;have bm:=g7 kb b rest hr br
  have am:a ∉ mid:=by cases h:kb<;>simp [mid,cT,h,hab,ar]
  have nd:=g7 ka a mid bm am
  have ht:tail.toFinset=U:=by
   change (cT ka a (cT kb b rest)).toFinset=U;rw [fY,fY,er]
   ext j
   by_cases aa:a ∈ U<;>by_cases bb:b ∈ U<;>by_cases aj:j=a <;>
    by_cases bj:j=b<;>simp_all [ka,kb]
  have hf:bM d a b ∉ tail:=by
   intro hz;exact fresh (mem_insert_of_mem (mem_insert_of_mem (ht ▸ mem_toFinset.mpr hz)))
  have progress:=ih (bM d a b::tail) (nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht]);change g2 _ _ _ ((bM d a b::cT ka a (cT kb b rest)).map aG) at progress;rw [map_cons,np,np,rh] at progress
  have perm:(a::b::rest).Perm v:=by
   apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
   ext j
   by_cases ja:j=a<;>by_cases jb:j=b<;>simp_all [er]
  exact g2.perm (perm.map _) (g2.two d hd ka kb progress)
lemma sW (f:bL bW):eT (ln f)=eh (eT f):=by rw [<-fR (eh (eT f)),ri,k2]
lemma nO (d:Bool) (f g:bL bW):eT (cd d f g)=eM d (eT f) (eT g):=by
 apply dA;intro r;rw [d6,ff,d6,d6]
 cases d<;>rfl
lemma fK {u} {bank:List (bL bW)} {a} (h:aO u bank a):gA u ((bank.map eT).map (fM u)) (eT a):=by
 rcases h with hm|⟨b,rfl⟩|⟨rfl,hm⟩
 . exact Or.inl (mem_map_of_mem (mem_map_of_mem hm))
 . apply fB
   cases b
   . exact Or.inl (dA fun i=>(d6 _ i).trans (cn i).symm)
   . exact Or.inr (dA fun i=>(d6 _ i).trans (d0 i).symm)
 . have:=sW a
   refine Or.inl ?_
   rw [<-rg,<-this];exact mem_map_of_mem (mem_map_of_mem hm)
lemma kJ {u} {roots:List (bL bW)} {p bank} (h:bH u roots p bank) {T k S} (run:cL u T k S) (sub:∀ a ∈ S,a ∈ (bank.map eT).map (fM u)):∃ l V,l ≤ p+k/\cL u T l V/\∀ a ∈ V,a ∈ (roots.map eT).map (fM u):=by
 induction h using bH.ind generalizing k S with
 | start=>exact ⟨k,S,by omega,run,sub⟩
 | @two p bank a b d h ha hb ih =>
  rw [map_cons,map_cons,nO] at sub;have rep:=lW d (fK ha) (fK hb)
  obtain ⟨k',S',hk,run',sub'⟩:=lX (c:=1) run (rep.imp id (fun h=>⟨rfl,h⟩))
   (fun a hm=>by simpa [or_comm] using sub a hm)
  obtain ⟨l,V,hl,hr,hs⟩:=ih run' sub';exact ⟨l,V,by omega,hr,hs⟩
def bP (a:aQ):Bool := !(aV 0 a)
lemma rf {u} {w:List aQ} (h:w.all bP=true):w.map (fM u)=w:=by
 have e:w.map (fM u)=w.map id:=by
  apply List.map_congr_left;intro a ha;exact kC (by simpa [bP] using all_eq_true.mp h a ha)
 rw [e,List.map_id]
lemma gg {u} {roots:List aQ} {p bank T} (hp:bg T) (nT:bP T=true) (nR:roots.all bP=true) (h:bH u (roots.map aG) p bank) (hit:aO u bank (aG T)):∃ k S,k ≤ p/\cL u T k S/\∀ a ∈ S,a ∈ roots:=by
 have hm:=fK hit;rw [fR] at hm;unfold gA at hm;rw [kC (by simpa [bP] using nT)] at hm;have mem:=hm.resolve_right (fun hn=>hn hp);obtain ⟨l,V,hl,hr,hs⟩:=kJ h (cL.stop hp) (by simpa using mem)
 refine ⟨l,V,by omega,hr,?_⟩
 have e:(roots.map aG).map eT=roots:=by simp [map_map,Function.comp_def,fR]
 rw [e,rf nR] at hs;exact hs
lemma eR {u T k S} (h:cL u T k S) {r s:bW} (diff:aV r T≠aV s T):∃ a ∈ S,aV r a≠aV s a:=by
 induction h using cL.ind with
 | stop hp=>exact ⟨_,by simp,diff⟩
 | @binary k U a b d hd ha hb hab hf _ ih =>
  obtain ⟨v,hv,hd⟩:=ih
  rcases mem_insert.mp hv with rfl|hu
  . by_cases aeq:aV r a=aV s a
    . refine ⟨b,by simp,?_⟩
      intro beq;exact hd (by rw [dQ,dQ,aeq,beq])
    . exact ⟨a,by simp,aeq⟩
  . exact ⟨v,mem_insert_of_mem (mem_insert_of_mem hu),hd⟩
lemma cX {u T k S} (h:cL u T k S) (roots:List aQ) (a:aQ) (sub:∀ v ∈ S,v ∈ roots) (r s:bW) (diff:aV r T≠aV s T) (isolated:∀ v ∈ roots,v≠a->aV r v=aV s v):a ∈ S:=by
 obtain ⟨v,hv,hd⟩:=eR h diff
 by_cases veq:v=a
 . simpa [veq] using hv
 . exact False.elim (hd (isolated v (sub v hv) veq))
end
def d1:List (BitVec 512):=[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def de:List (BitVec 1024):=[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
def zF:BitVec 512:=0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def xq:BitVec 1024:=0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff8c8fffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
lemma t0:∀ r:Fin 512,(d1.getD 0 0).getLsbD r.val=r.val.testBit 0:=by decide +kernel
lemma t3:∀ r:Fin 512,(d1.getD 1 0).getLsbD r.val=r.val.testBit 1:=by decide +kernel
lemma t4:∀ r:Fin 512,(d1.getD 2 0).getLsbD r.val=r.val.testBit 2:=by decide +kernel
lemma t5:∀ r:Fin 512,(d1.getD 3 0).getLsbD r.val=r.val.testBit 3:=by decide +kernel
lemma t6:∀ r:Fin 512,(d1.getD 4 0).getLsbD r.val=r.val.testBit 4:=by decide +kernel
lemma t7:∀ r:Fin 512,(d1.getD 5 0).getLsbD r.val=r.val.testBit 5:=by decide +kernel
lemma t8:∀ r:Fin 512,(d1.getD 6 0).getLsbD r.val=r.val.testBit 6:=by decide +kernel
lemma t9:∀ r:Fin 512,(d1.getD 7 0).getLsbD r.val=r.val.testBit 7:=by decide +kernel
lemma ua:∀ r:Fin 512,(d1.getD 8 0).getLsbD r.val=r.val.testBit 8:=by decide +kernel
lemma rM:∀ r:Fin 1024,(de.getD 0 0).getLsbD r.val=r.val.testBit 0:=by decide +kernel
lemma rN:∀ r:Fin 1024,(de.getD 1 0).getLsbD r.val=r.val.testBit 1:=by decide +kernel
lemma rO:∀ r:Fin 1024,(de.getD 2 0).getLsbD r.val=r.val.testBit 2:=by decide +kernel
lemma rP:∀ r:Fin 1024,(de.getD 3 0).getLsbD r.val=r.val.testBit 3:=by decide +kernel
lemma rQ:∀ r:Fin 1024,(de.getD 4 0).getLsbD r.val=r.val.testBit 4:=by decide +kernel
lemma rR:∀ r:Fin 1024,(de.getD 5 0).getLsbD r.val=r.val.testBit 5:=by decide +kernel
lemma rS:∀ r:Fin 1024,(de.getD 6 0).getLsbD r.val=r.val.testBit 6:=by decide +kernel
lemma rT:∀ r:Fin 1024,(de.getD 7 0).getLsbD r.val=r.val.testBit 7:=by decide +kernel
lemma rU:∀ r:Fin 1024,(de.getD 8 0).getLsbD r.val=r.val.testBit 8:=by decide +kernel
lemma rV:∀ r:Fin 1024,(de.getD 9 0).getLsbD r.val=r.val.testBit 9:=by decide +kernel
section
variable [w : Width]
def inputs:List aQ:=match w with|⟨false⟩=>d1|⟨true⟩=>de
def co:aQ:=match w with|⟨false⟩=>zF|⟨true⟩=>xq
lemma h6:List.ofFn (fun j:Fin N=>inputs.getD j.val zero)=inputs:=by rcases w with ⟨_|_⟩<;>rfl
def cU (f:bW->bW) (a:aQ):=eT fun r=>aV (f r) a
lemma dD (f:bW->bW) (a:aQ) (r:bW):aV r (cU f a)=aV (f r) a:=d6 _ _
lemma dG (f:bW->bW) (a:aQ):aG (cU f a)=au f (aG a):=by funext r;exact dD f a r
lemma kL (f:bW->bW) (d:Nat) (a b:aQ):cU f (bM d a b)=bM d (cU f a) (cU f b):=by
 apply dA;intro r;simp only [dD,dQ]
lemma pj (f:bW->bW) (onto:Function.Surjective f):Function.Injective (cU f):=by
 intro a b h;apply eq_of_getLsbD_eq;intro j hj;obtain ⟨r,hr⟩:=onto ⟨j,hj⟩;have he:=congrArg (aV r) h;change aV ⟨j,hj⟩ a=aV ⟨j,hj⟩ b;rw [dD,dD,hr] at he;exact he
lemma f3 (f:bW->bW):cU f zero=zero/\cU f one=one:=by
 constructor<;>apply eq_of_getLsbD_eq<;>intro j hj
 . exact (dD f zero ⟨j,hj⟩).trans ((cn _).trans (cn ⟨j,hj⟩).symm)
 . exact (dD f one ⟨j,hj⟩).trans ((d0 _).trans (d0 ⟨j,hj⟩).symm)
lemma nm {u T k S} (h:cL u T k S) (f:bW->bW) (onto:Function.Surjective f):cL u (cU f T) k (S.image (cU f)):=by
 have inj:=pj f onto;obtain ⟨fz,fo⟩:=f3 f
 have pp (v) (p:bg v):bg (cU f v):=
  ⟨fun e=>p.1 (inj (e.trans fz.symm)),fun e=>p.2 (inj (e.trans fo.symm))⟩
 induction h using cL.ind with
 | stop hp=>simpa using cL.stop (pp _ hp)
 | @binary k U a b d hd ha hb hab hf _ ih =>
  have fresh:cU f (bM d a b) ∉ (insert a (insert b U)).image (cU f):=by
   intro hm;obtain ⟨v,hv,eq⟩:=Finset.mem_image.mp hm;exact hf (inj eq ▸ hv)
  simp only [Finset.image_insert,kL] at fresh ih ⊢;exact cL.binary hd (pp _ ha) (pp _ hb) (fun hh=>hab (inj hh)) fresh ih
lemma hE {u T k S} (h:cL u T k S) (none:u=false) {r s:bW} (pos:aV r T=true) (negRow:aV s T=false):∃ a ∈ S,aV r a=true/\aV s a=false:=by
 induction h using cL.ind with
 | stop hp=>exact ⟨_,by simp,pos,negRow⟩
 | @binary k U a b d hd ha hb hab hf _ ih =>
  obtain ⟨v,hv,hp,hn⟩:=ih
  rcases mem_insert.mp hv with rfl|hu
  . rw [dQ] at hp hn;subst none
    rcases cq hd with rfl|rfl|⟨h,_⟩|⟨h,_⟩
    . cases p:aV r a<;>cases q:aV s a<;>cases u:aV r b<;>cases z:aV s b<;>simp_all
    . cases p:aV r a<;>cases q:aV s a<;>cases u:aV r b<;>cases z:aV s b<;>simp_all
    . exact noConfusion h
    . exact noConfusion h
  . exact ⟨v,mem_insert_of_mem (mem_insert_of_mem hu),hp,hn⟩
def aR (u:Bool) (roots:List aQ) (T:aQ) (L:Nat):Prop := ∀ p bank,bH u (roots.map aG) p bank->aO u bank (aG T)->L ≤ p
lemma wr {R u} {roots:List (bL R)} {p bank} (h:bH false roots p bank):bH u roots p bank:=by
 have up {bank:List (bL R)} {a} (h:aO false bank a):aO u bank a:=
  h.imp id (Or.imp id (fun h=>noConfusion h.1))
 induction h using bH.ind with
 | start=>exact bH.start
 | two op h ha hb ih=>exact bH.two op ih (up ha) (up hb)
lemma kr {u roots T L} (h:aR true roots T L):aR u roots T L:=by
 cases u
 . exact fun p bank hr ha=>h p bank (wr hr) (ha.imp id (Or.imp id (fun h=>noConfusion h.1)))
 . exact h
def aB (u:Bool) (T:aQ) (cap:Nat) (S:Finset aQ):Prop := ∀ k,k ≤ cap->¬cL u T k S
def gZ (T:aQ) (roots:List aQ) (a:aQ):Prop := ∃ r s:bW,aV r T≠aV s T/\∀ v ∈ roots,v≠a->aV r v=aV s v
lemma i4 {u roots T L} (hp:bg T) (nT:bP T=true) (nR:roots.all bP=true) (essential:∀ a ∈ roots,gZ T roots a) (noRun:aB u T L roots.toFinset):aR u roots T (L+1):=by
 intro p bank h ha;obtain ⟨k,S,hk,run,hs⟩:=gg hp nT nR h ha
 have he:roots.toFinset=S:=by
  ext a
  rw [mem_toFinset]
  refine ⟨fun hm => ?_,hs a⟩
  obtain ⟨r,s,hd,iso⟩:=essential _ hm;exact cX run roots a hs r s hd iso
 by_contra! small
 exact noRun k (by omega) (he.symm ▸ run)
lemma fx {v:aQ} (hv:bg v):¬bw (aG v):=by
 rintro ⟨b,h⟩
 have hr:gA false [] v:=by
  apply fB
  cases b
  . exact Or.inl (dA fun i=>(congrFun h i).trans (cn i).symm)
  . exact Or.inr (dA fun i=>(congrFun h i).trans (d0 i).symm)
 have hr':cK [] v:=hr;exact (hr'.resolve_left (by simp)) hv
lemma nr {R} (a b:List (bL R)):ga (a++b)=ga a+ga b:=by simp [ga]
lemma ku {R} (xs:List (bL R)) (hc:∀ x ∈ xs,bw x):ga xs=xs.length:=by
 induction xs with
 | nil=>simp [ga]
 | cons a xs ih =>
  have ha:=hc a (by simp);simp only [fh,length_cons,eV,if_pos ha,ih (fun x hx=>hc x (by simp [hx]))];omega
lemma jh {u} {roots other:List aQ} {T G:aQ} (pT:bg T) (nT:bP T=true) (nR:roots.all bP=true) (pG:bg G) (r:bW->bW) (eq:cU r T=G) (dS:∀ a ∈ roots,aO u (other.map aG) (aG (cU r a))) (singles:Finset aQ) (necessary:∀ a ∈ singles,gZ T roots a) (constant:∀ a ∈ singles,bw (aG (cU r a))) (L:Nat) (prior:aR u other G L):aR u roots T (L+singles.card):=by
 classical
 intro p bank hh ha;obtain ⟨k,S,hk,run,sub⟩:=gg pT nT nR hh ha
 have subS:singles ⊆ S:=by
  intro a hs;obtain ⟨i,j,hd,hiso⟩:=necessary a hs;exact cX run roots a sub i j hd hiso
 let front:=singles.toList ++ (S \ singles).toList
 have nd:front.Nodup:=by
  simp only [front,List.nodup_append]
  refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
  intro a ha b hb he;subst b;exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
 have fe:front.toFinset=S:=by ext a;simp [front,Finset.union_sdiff_of_subset subS]
 have run':=kq run front nd fe;have gc:au r (aG T)=aG G:=(dG _ _).symm.trans (congrArg aG eq)
 have supp:h9 u (other.map aG) ((front.map aG).map (au r)):=by
  intro v hv;obtain ⟨_,hm,rfl⟩:=mem_map.mp hv;obtain ⟨a,hmem,rfl⟩:=mem_map.mp hm;rw [<-dG];exact dS a (sub _ (fe ▸ mem_toFinset.mpr hmem))
 have bound:=eP r run' (gc ▸ fx pG) bH.start supp
  (L:=L) (gc ▸ prior)
 have massLo:singles.card ≤ ga ((front.map aG).map (au r)):=by
  simp only [front,List.map_append,nr];let xs:=(singles.toList.map aG).map (au r)
  have only:∀ v ∈ xs,bw v:=by
   intro v hv;obtain ⟨_,hm,rfl⟩:=mem_map.mp hv;obtain ⟨a,hmem,rfl⟩:=mem_map.mp hm;rw [<-dG];exact constant _ (Finset.mem_toList.mp hmem)
  have sz:=ku xs only;simp only [xs,length_map,Finset.length_toList] at sz;change singles.card ≤ ga xs+_;rw [sz];omega
 omega
def cu (ws:List aQ) (a b:aQ) (d:Nat) (ka kb:Bool):List aQ:=bM d a b :: cT ka a (cT kb b ((ws.erase a).erase b))
lemma g4 {l:List aQ} (h:l.Nodup) (a:aQ):(l.erase a).toFinset=l.toFinset.erase a:=by
 ext x
 simp [h.mem_erase_iff]
lemma rX {u} {T:aQ} {cap:Nat} {ws:List aQ} (hn:ws.Nodup) (out:T ∉ ws) (twoStep:∀ a ∈ ws,∀ b ∈ ws,∀ d,bY u d->∀ ka kb,a≠b->bM d a b ∉ ws ->bg (bM d a b)->(cu ws a b d ka kb).length ≤ cap ->aB u T (cap-1) (cu ws a b d ka kb).toFinset):aB u T cap ws.toFinset:=by
 classical
 intro k hk h;generalize he:ws.toFinset=S at h
 induction h using cL.ind with
 | stop hp =>
  have mem:T ∈ ws.toFinset:=he.symm ▸ Finset.mem_singleton_self _;exact out (mem_toFinset.mp mem)
 | @binary k U a b d hd ha hb hab hf tail _ =>
  have am:a ∈ ws:=mem_toFinset.mp (he.symm ▸ mem_insert_self _ _);have bm:b ∈ ws:=mem_toFinset.mp (he.symm ▸ mem_insert_of_mem (mem_insert_self _ _));have fresh:bM d a b ∉ ws:=fun h=>hf (he ▸ mem_toFinset.mpr h);have hz:=eI tail _ (mem_insert_self _ _);let ka:=decide (a ∈ U);let kb:=decide (b ∈ U);let rest:=(ws.erase a).erase b
  have er:rest.toFinset=(ws.toFinset.erase a).erase b:=by
   rw [show rest=(ws.erase a).erase b by rfl,g4 (hn.erase _) b,
    g4 hn a]
  have ke:(cT ka a (cT kb b rest)).toFinset=U:=by
   rw [fY,fY,er,he]
   ext j
   by_cases aa:a ∈ U<;>by_cases bb:b ∈ U<;>by_cases ja:j=a <;>
    by_cases jb:j=b<;>simp_all [ka,kb]
  have rn:rest.Nodup:=(hn.erase _).erase _;have ar:a ∉ rest:=fun h=>(hn.not_mem_erase) (List.mem_of_mem_erase h);have br:b ∉ rest:=(hn.erase a).not_mem_erase;have nk:=g7 kb b rest rn br
  have ax:a ∉ cT kb b rest:=by cases kb<;>simp [cT,ar,hab]
  have nd:(cu ws a b d ka kb).Nodup:=by
   refine nodup_cons.mpr ⟨?_,g7 ka a _ nk ax⟩
   intro h;exact hf (mem_insert_of_mem (mem_insert_of_mem (ke ▸ mem_toFinset.mpr h)))
  have eq:(cu ws a b d ka kb).toFinset=insert (bM d a b) U:=by
   change (bM d a b::cT ka a (cT kb b rest)).toFinset=_;simp [ke]
  have sc:=g9 tail
  have len:(cu ws a b d ka kb).length ≤ cap:=by
   rw [<-List.toFinset_card_of_nodup nd,eq];omega
  exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)
def CF (T:aQ) (width:Nat) (pos negRow:Fin width->bW) (asig:aQ->BitVec width × BitVec width):Prop:=
 (∀ i,aV (pos i) T=true/\aV (negRow i) T=false) /\
 ∀ w i,(asig w).1.getLsbD i.val=aV (pos i) w /\
  (asig w).2.getLsbD i.val=aV (negRow i) w
def bU {n} (oriented:Bool) (s:BitVec n × BitVec n):BitVec n:=if oriented then s.1 &&& ~~~s.2 else s.1^^^s.2
def dS {n} (oriented:Bool) (sig:aQ->BitVec n × BitVec n):List aQ->BitVec n
 | []=>0
 | a::ws=>bU oriented (sig a)|||dS oriented sig ws
lemma mU {n:Nat} {oriented:Bool} {sig:aQ->BitVec n × BitVec n} {ws:List aQ} {i:Fin n}:(dS oriented sig ws).getLsbD i.val=true ↔ ∃ a ∈ ws,(bU oriented (sig a)).getLsbD i.val=true:=by
 induction ws with
 | nil=>simp [dS]
 | cons a ws ih =>
  simp only [dS,getLsbD_or,or_eq_true,ih,mem_cons,exists_eq_or_imp]
lemma mT {u T k S} (h:cL u T k S) {ws:List aQ} (he:ws.toFinset=S) {width:Nat} {r s:Fin width->bW} {sig} (correct:CF T width r s sig) (oriented:Bool) (zeroNot:oriented=true->u=false):dS oriented sig ws=allOnes width:=by
 apply eq_of_getLsbD_eq;intro j hj;let i:Fin width:=⟨j,hj⟩;have yes:=(correct.1 i).1;have no:=(correct.1 i).2;rw [getLsbD_allOnes];simp only [hj,decide_true];apply (mU (i:=i)).mpr
 cases oriented with
 | false =>
  obtain ⟨a,ha,hd⟩:=eR h (show aV (r i) T≠aV (s i) T by simp [yes,no])
  refine ⟨a,mem_toFinset.mp (he.symm ▸ ha),?_⟩
  simp only [bU,false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
  cases hx:aV (r i) a<;>cases hy:aV (s i) a<;>simp_all
 | true =>
  obtain ⟨a,ha,hp,hn⟩:=hE h (zeroNot rfl) yes no
  refine ⟨a,mem_toFinset.mp (he.symm ▸ ha),?_⟩
  simp only [bU,ite_true,getLsbD_and,getLsbD_not,i.isLt,decide_true,
   Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]
lemma jM {u T ws k} (h:cL u T k (List.toFinset ws)) {n:Nat} {r s:Fin n->bW} {sig} (correct:CF T n r s sig):dS (!u) sig ws=allOnes n:=by
 apply mT h rfl correct
 simp
def gB (u:Bool) (raw:List aQ) (T d:aQ) (L:Nat):Prop:=
 ∃ (f:bW->bW) (roots:List aQ),(∀ r,aV (f r) d=true) /\
  (∀ a ∈ raw,aO u (roots.map aG) (au f (aG a))) /\
  ¬bw (au f (aG T)) /\
  ∀ p bank,bH u (roots.map aG) p bank->aO u bank (au f (aG T))->L ≤ p
def cl (d a:aQ):=a&&&d
def bd (u:Bool) (d:aQ) (pool:List aQ) (a:aQ):=
 let m:=cl d a
 m==zero||m==d||(pool.map (cl d)).any (fun v=>v==m) ||
  (u&&(let c:=cl d (eh a);(pool.map (cl d)).any (fun v=>v==c)))
lemma lO {f:bW->bW} {d a b:aQ} (dom:∀ r,aV (f r) d=true) (eq:cl d a=cl d b):au f (aG a)=au f (aG b):=by
 funext r
 have h:=congrArg (aV (f r)) eq;change aV (f r) a=aV (f r) b
 simpa only [aV,cl,getLsbD_and,show d.getLsbD (f r).val=true from dom r,
  Bool.and_true] using h
lemma ji {f:bW->bW} {d a:aQ} (dom:∀ r,aV (f r) d=true) (eq:cl d a=zero):au f (aG a)=fun _=>false:=by
 funext r
 have he:=congrArg (aV (f r)) eq;change aV (f r) a=false;rw [cn] at he
 simpa only [aV,cl,getLsbD_and,show d.getLsbD (f r).val=true from dom r,
  Bool.and_true] using he
lemma kt {f:bW->bW} {d a:aQ} (dom:∀ r,aV (f r) d=true) (eq:cl d a=d):au f (aG a)=fun _=>true:=by
 funext r
 have he:=congrArg (aV (f r)) eq;change aV (f r) a=true;rw [dom r] at he
 simpa only [aV,cl,getLsbD_and,show d.getLsbD (f r).val=true from dom r,
  Bool.and_true] using he
def d4 (u:Bool) (f:bW->bW) (bank:List (bL bW)) (pool:List aQ) := ∀ a ∈ pool,aO u bank (au f (aG a))
lemma cM {u} {f:bW->bW} {d a:aQ} {bank pool} (dom:∀ r,aV (f r) d=true) (supplyB:d4 u f bank pool) (check:bd u d pool a=true):aO u bank (au f (aG a)):=by
 simp only [bd,List.any_map,Function.comp_def,or_eq_true,and_eq_true,beq_iff_eq,any_eq_true] at check
 rcases check with ((hz|ho)|⟨v,hv,he⟩)|⟨hu,v,hv,he⟩
 . exact Or.inr (Or.inl ⟨false,ji dom hz⟩)
 . exact Or.inr (Or.inl ⟨true,kt dom ho⟩)
 . exact lO dom he ▸ supplyB v hv
 . have h:=iQ hu (lO dom he ▸ supplyB v hv);rw [ri] at h
   have e:ln (au f (ln (aG a)))=au f (aG a):=by
    funext r
    simp [ln,au]
   rwa [e] at h
abbrev ej:=Nat × aQ × aQ
def bp (c:ej):=bM c.1 c.2.1 c.2.2
def fS (u:Bool) (d:Nat):=decide (d<2)||(u&&decide (d<4))
lemma mM {u d} (h:fS u d=true):bY u d:=by simpa [fS,bY] using h
def fn (u:Bool) (d:aQ) (pool:List aQ) (c:ej):=fS u c.1&&(bd u d pool c.2.1&&bd u d pool c.2.2)
lemma kH {u} {f:bW->bW} {d:aQ} {roots bank pool q} (dom:∀ r,aV (f r) d=true) (hp:bH u roots q bank) (hs:d4 u f bank pool) (c:ej) (valid:fn u d pool c=true):∃ next,bH u roots (q+1) next/\d4 u f next (bp c :: pool):=by
 simp only [fn,and_eq_true] at valid
 obtain ⟨op,x,y,e,hx,hy,_,_⟩:=jL (mM valid.1) (cM dom hs valid.2.1)
  (cM dom hs valid.2.2)
 refine ⟨_,bH.two op hp hx hy,?_⟩
 intro a hm
 rcases mem_cons.mp hm with rfl|hm
 . rw [bp,rh,hQ,e];exact Or.inl (by simp)
 . exact gD _ (hs _ hm)
def fw (u:Bool) (d:aQ) (pool:List aQ):List ej->Option (List aQ)
 | []=>some pool
 | c::cs=>if fn u d pool c then fw u d (bp c::pool) cs else none
lemma gQ {u} {d:aQ} {f:bW->bW} (dom:∀ r,aV (f r) d=true) {roots bank q pool} (hp:bH u roots q bank) (hs:d4 u f bank pool) (cs:List ej) {result} (ok:fw u d pool cs=some result):∃ next,bH u roots (q+cs.length) next/\d4 u f next result:=by
 induction cs generalizing bank q pool with
 | nil=>cases ok;exact ⟨_,hp,hs⟩
 | cons c cs ih =>
  simp only [fw] at ok
  split at ok
  next h =>
   obtain ⟨next,hr,sh⟩:=kH dom hp hs c h;obtain ⟨out,hr',sh'⟩:=ih hr sh ok;exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
  next=>contradiction
def ay (d a:aQ):=cl d a==zero||cl d a==d
lemma gu {d:aQ} {f:bW->bW} (dom:∀ r,aV (f r) d=true) (ws:List aQ):ws.countP (ay d) ≤ ga ((ws.map aG).map (au f)):=by
 classical
 induction ws with
 | nil=>simp [ga]
 | cons a ws ih =>
  simp only [countP_cons,map_cons,fh]
  cases h:ay d a
  . simpa using (Nat.le_add_left _ _ |> ih.trans)
  . have hc:bw (au f (aG a)):=by
     have hh:cl d a=zero\/cl d a=d:=by simpa only [ay,or_eq_true,beq_iff_eq] using h
     rcases hh with hz|ho
     . exact ⟨false,ji dom hz⟩
     . exact ⟨true,kt dom ho⟩
    simpa [eV,hc,Nat.add_comm] using Nat.succ_le_succ ih
def jF (u:Bool) (d:aQ) (L k p:Nat) (pool ws:List aQ):=decide (k+p<L+ws.countP (ay d))&&ws.all (bd u d pool)
lemma hP {u raw T d L} (slice:gB u raw T d L) (cs:List ej) {pool ws cap} (built:fw u d raw cs=some pool) (nd:ws.Nodup) (cut:jF u d L cap cs.length pool ws=true):aB u T cap ws.toFinset:=by
 intro k hk h;obtain ⟨f,roots,dom,base,nc,lo⟩:=slice;obtain ⟨bank,hr,hs⟩:=gQ dom (bH.start (roots:=roots.map aG)) base cs built;simp only [jF,and_eq_true,decide_eq_true_eq] at cut;obtain ⟨ineq,all⟩:=cut
 have coveredS:h9 u bank ((ws.map aG).map (au f)):=by
  intro v hv;obtain ⟨_,hm,rfl⟩:=mem_map.mp hv;obtain ⟨a,ha,rfl⟩:=mem_map.mp hm;exact cM dom hs (all_eq_true.mp all a ha)
 have b:=eP f (kq h ws nd rfl) nc hr coveredS lo;have massLo:=gu dom ws;have hu:=ineq;simp only [Nat.zero_add] at b;omega
abbrev ie:=aQ × aQ × bW
def jG (d r:bW):bW:=if h:r.val<W-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(W-d.val),by omega⟩
def ld (d:bW):bW:=Fin.ofNat W (W-d.val)
def mu (m:ie) (r:bW):bW:=if aV r m.1 then jG m.2.2 r else if aV r m.2.1 then jG (ld m.2.2) r else r
def CE (m a b:aQ):=(m&&&a)|||(~~~m&&&b)
def f4 (m:ie) (a:aQ):=CE m.1 (a.rotateRight m.2.2.val) (CE m.2.1 (a.rotateRight (ld m.2.2).val) a)
lemma rJ (d r:bW) (a:aQ):aV r (a.rotateRight d.val)=aV (jG d r) a:=by
 unfold aV;rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
 by_cases h:r.val<W-d.val<;>simp [jG,h,r.isLt]
lemma tY (p x y:Bool):(p&&x || !p&&y)=(if p then x else y):=by cases p<;>simp
lemma w7 (r:bW) (m a b:aQ):aV r (CE m a b)=if aV r m then aV r a else aV r b:=by
 simp only [aV,CE,getLsbD_and,getLsbD_or,getLsbD_not,r.isLt,
  decide_true,Bool.true_and]
 exact tY _ _ _
lemma tX (r:bW) (m:ie) (a:aQ):aV r (f4 m a)=aV (mu m r) a:=by
 simp only [f4,w7,rJ,mu]
 cases aV r m.1<;>cases aV r m.2.1<;>rfl
def cR (ms:List ie) (r:bW):=ms.foldl (fun j m=>mu m j) r
def bn (ms:List ie) (a:aQ):=ms.foldr f4 a
lemma fU (ms:List ie) (a:aQ) (r:bW):aV r (bn ms a)=aV (cR ms r) a:=by
 induction ms generalizing r with
 | nil=>rfl
 | cons m ms ih=>exact (tX r m _).trans (ih _)
lemma cF (ms:List ie) (a:aQ):bn ms a=cU (cR ms) a:=by
 apply eq_of_getLsbD_eq;intro j hj;exact (fU ms a ⟨j,hj⟩).trans (dD _ _ ⟨j,hj⟩).symm
def jU (roots:List aQ) (w:aQ):=w==zero||w==one||roots.contains w
lemma m0 {u roots w} (ok:jU roots w=true):aO u (roots.map aG) (aG w):=by
 simp only [jU,or_eq_true,beq_iff_eq,contains_eq_mem,decide_eq_true_eq] at ok
 rcases ok with (rfl|rfl)|hm
 . exact Or.inr (Or.inl ⟨false,funext cn⟩)
 . exact Or.inr (Or.inl ⟨true,funext d0⟩)
 . exact Or.inl (mem_map_of_mem hm)
def eG (ms:List ie) (raw:List aQ) (T:aQ) (base:List aQ) (G:aQ):=bn ms T==G&&raw.all (fun a=>jU base (bn ms a))
lemma gR {u ms raw T base G} (ok:eG ms raw T base G=true):cU (cR ms) T=G/\∀ a ∈ raw,aO u (base.map aG) (aG (cU (cR ms) a)):=by
 simp only [eG,and_eq_true,beq_iff_eq,all_eq_true,cF] at ok;exact ⟨ok.1,fun a ha=>m0 (ok.2 a ha)⟩
lemma sm {u ms raw T base G L} (ok:eG ms raw T base G=true) (pT:bg T) (nT:bP T=true) (nR:raw.all bP=true) (pG:bg G) (hL:aR u base G L):aR u raw T L:=by
 obtain ⟨eq,supp⟩:=gR ok;simpa using jh pT nT nR pG (cR ms) eq supp ∅ (by simp) (by simp) L hL
lemma k5 {u ms raw T base G L d} (ok:eG ms raw T base G=true) (all:bn ms d=one) (properG:bg G) (hL:aR u base G L):gB u raw T d L:=by
 obtain ⟨eq,supp⟩:=gR ok
 have obs:au (cR ms) (aG T)=aG G:=
  (dG _ _).symm.trans (congrArg aG eq)
 refine ⟨cR ms,base,?_,?_,?_,?_⟩
 . intro r;rw [<-fU,all,d0]
 . intro a ha;rw [<-dG];exact supp a ha
 . rw [obs];exact fx properG
 . rw [obs];exact hL
def kV (T:aQ) (roots:List aQ) (a:aQ) (rs:bW × bW):=
 (aV rs.1 T !=aV rs.2 T) &&
 roots.all (fun w=>w==a||aV rs.1 w==aV rs.2 w)
lemma kW {T roots a rs} (ok:kV T roots a rs=true):gZ T roots a:=by
 simp only [kV,and_eq_true,bne_iff_ne,all_eq_true,or_eq_true,beq_iff_eq] at ok;exact ⟨rs.1,rs.2,ok.1,fun w hw hne=>(ok.2 w hw).resolve_left hne⟩
def bZ (T:aQ) (raw:List aQ) (xs:List (aQ × bW × bW)):=bP T&&raw.all bP&&xs.all (fun a=>kV T raw a.1 a.2)
lemma eW {T raw xs} (ok:bZ T raw xs=true):∀ a ∈ (xs.map Prod.fst).toFinset,gZ T raw a:=by
 simp only [bZ,and_eq_true] at ok;intro a ha;obtain ⟨⟨a,r,s⟩,hm,rfl⟩:=mem_map.mp (mem_toFinset.mp ha);exact kW (all_eq_true.mp ok.2 _ hm)
lemma cg {T raw xs} (ok:bZ T raw xs=true):bP T=true/\raw.all bP=true:=by
 simp only [bZ,and_eq_true] at ok;exact ok.1
lemma gP {u raw T} (properT:bg T) (xs:List (aQ × bW × bW)) (ok:bZ T raw xs=true):aR u raw T ((xs.map Prod.fst).toFinset.card-1):=by
 intro p bank hr hit;obtain ⟨k,S,hk,run,sub⟩:=gg properT (cg ok).1 (cg ok).2 hr hit
 have le:(xs.map Prod.fst).toFinset.card ≤ S.card:=by
  apply Finset.card_le_card;intro a ha;obtain ⟨r,s,hd,iso⟩:=eW ok a ha;exact cX run raw a sub r s hd iso
 have bound:=g9 run;omega
def iS (ms:List ie) (T:aQ) (raw:List aQ) (base:List aQ) (G:aQ) (xs:List (aQ × bW × bW)):=
 eG ms raw T base G&&bZ T raw xs &&
  xs.all (fun a=>bn ms a.1==zero||bn ms a.1==one)
lemma xB {u ms T raw base G xs L} (ok:iS ms T raw base G xs=true) (properT:bg T) (properG:bg G) (low:aR u base G L):aR u raw T (L+(xs.map Prod.fst).toFinset.card):=by
 simp only [iS,and_eq_true] at ok;obtain ⟨eq,supp⟩:=gR ok.1.1;apply jh properT (cg ok.1.2).1 (cg ok.1.2).2 properG _ eq supp _ (eW ok.1.2) _ L low;intro a ha;obtain ⟨⟨v,r,s⟩,hm,rfl⟩:=mem_map.mp (mem_toFinset.mp ha);have hh:=all_eq_true.mp ok.2 _ hm;simp only [or_eq_true,beq_iff_eq,cF] at hh
 rcases hh with h|h
 . rw [h];exact ⟨false,funext cn⟩
 . rw [h];exact ⟨true,funext d0⟩
def dt (m:Nat):List (Nat × aQ):=(List.range N).filterMap fun i=>if m.testBit i then some (i,inputs.getD i zero) else none
def cB (m:Nat):=(dt m).map Prod.snd
def iJ (t:Nat):aQ:=bM (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def aN (m:Nat):List aQ:=if w.wide then cB m else if m<512 then cB m else cB m ++ [iJ (m/512-1)]
def eB (m j:Nat):=if m.testBit j then inputs.getD j zero else zero
def ac (m:Nat):aQ:=
 let x:=eB m
 let base:=(x 0&&&x 1)|||(x 1&&&x 2)|||(x 2&&&x 3)|||(x 3&&&x 4) |||
  (x 4&&&x 0)|||(x 0&&&x 5)|||(x 1&&&x 6)|||(x 2&&&x 7) |||
  (x 3&&&x 8)|||(x 5&&&x 7)|||(x 6&&&x 8)|||(x 8&&&x 5)
 if w.wide then base|||(x 4&&&x 9)|||(x 7&&&x 9)|||(x 9&&&x 6) else base
end
def Bv:Nat->Nat
 | 0=>0xff
 | 1=>0x55
 | 2=>0x33
 | 3=>0x11
 | 4=>0xf
 | 5=>0x5
 | 6=>0x3
 | _=>0x1
def Bw:Nat->Nat
 | 0=>0x101010101010101
 | 1=>0x1000100010001
 | 2=>0x10100000101
 | 3=>0x100000001
 | 4=>0x1010101
 | 5=>0x10001
 | 6=>0x101
 | _=>0x1
def Bx:Nat->Nat
 | 0=>0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
 | 1=>0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
 | 2=>0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
 | 3=>0x10000000000000000000000000000000000000000000000000000000000000001
 | 4=>0x1000000000000000100000000000000010000000000000001
 | 5=>0x100000000000000000000000000000001
 | 6=>0x10000000000000001
 | _=>0x1
section
variable [w : Width]
def dC (z o:Nat):aQ:=
 let fixed:=z|||o
 if z&&&o !=0 then zero else
  let base:=Bv (fixed&&&7)*Bw ((fixed>>>3)&&&7)*Bx ((fixed>>>6)&&&7)
  let full:=if w.wide && !(fixed.testBit 9) then base|||(base<<<512) else base
  BitVec.ofNat W (full<<<o)
def mf (z o:Nat):List ie:=
 (List.range N).filterMap fun j =>
  let x:=inputs.getD j zero
  let step:=Fin.ofNat W (1<<<j)
  if z.testBit j then some (zero,x,step)
  else if o.testBit j then some (~~~x,zero,step) else none
def dh (v:Nat):ie:=
 let i:=v&&&15
 let j:=v>>>4
 let a:=inputs.getD i zero
 let b:=inputs.getD j zero
 let d:=(1<<<j)-(1<<<i)
 (a &&& ~~~b,b &&& ~~~a,Fin.ofNat W d)
def iI (t:Nat) (mask:Nat):List (aQ × bW × bW):=
 (dt mask).map fun (i,a) =>
  let r:=if t/81==2&&i==t/9 % 9 then 1<<<(t % 9) else if t/81==2&&i==t % 9 then 1<<<(t/9 % 9) else 0
  (a,Fin.ofNat W r,Fin.ofNat W (r|||(1<<<i)))
def fu (m hints:Nat):List (aQ × bW × bW):=
 (dt m).map fun (i,a) =>
  let r:=1<<<((hints>>>(4*i))&&&15)
  (a,Fin.ofNat W r,Fin.ofNat W (r|||(1<<<i)))
def cE (T:aQ):=T !=zero&&T !=one
lemma cN (T:aQ) (h:cE T=true):bg T:=by simpa only [cE,bg,and_eq_true,bne_iff_ne] using h
end
abbrev aZ:=Nat × Nat × Nat × Nat × Nat
def ma (m z o:Nat):=m^^^(m&&&(z|||o))
section
variable [w : Width]
def dR (m:Nat):aQ:=ac m
def eZ (m:Nat) (c:aZ):Nat:=if w.wide then m % 1024 else m % 512+512*(c.1/512)
def fW (m:Nat) (c:aZ) (prior:Nat->Nat):Bool:=
 let (z,o,q,s,L):=c
 let ms:=mf z o
 let raw:=eZ m c
 let free:=ma raw (z % W) o
 let G:=bn ms (dR m)
 let xs:=iI (if w.wide then 0 else z/512+80) s
 let count:=(xs.map Prod.fst).toFinset.card
 cE G&&eG ms (aN raw) (dR m) (aN free) G &&
  (bn ms (dC z o)==one) &&
  (if q=0 then bZ G (aN free) xs&&decide (L ≤ count-1)
   else cE (ac q) &&
    iS (mf (ma free q 0) 0) G (aN free) (aN q) (ac q) xs &&
    decide (L ≤ prior q+count))
lemma en {u} {m:Nat} (c:aZ) (prior:Nat->Nat) (valid:∀ q,aR u (aN q) (ac q) (prior q)) (ok:fW m c prior=true):gB u (aN (eZ m c)) (dR m) (dC c.1 c.2.1) c.2.2.2.2:=by
 revert ok;obtain ⟨z,o,q,s,L⟩:=c;intro ok;let ms:=mf z o;let raw:=eZ m (z,o,q,s,L);let free:=ma raw (z % W) o;let G:=bn ms (dR m);let xs:=iI (if w.wide then 0 else z/512+80) s
 change (((cE G&&eG ms (aN raw) (dR m) (aN free) G) &&
  (bn ms (dC z o)==one))&&_)=true at ok
 simp only [and_eq_true,beq_iff_eq] at ok;apply k5 ok.1.1.2 ok.1.2 (cN _ ok.1.1.1);intro p bank hr ha;have hh:=ok.2
 by_cases hq:q=0
 . simp only [fW,hq,if_true,and_eq_true,decide_eq_true_eq] at hh;exact hh.2.trans (gP (cN _ ok.1.1.1) xs hh.1 p bank hr ha)
 . simp only [fW,hq,if_false,and_eq_true,decide_eq_true_eq] at hh;exact hh.2.trans (xB hh.1.2 (cN _ ok.1.1.1) (cN _ hh.1.1) (valid q) p bank hr ha)
def jx (old rep:Nat) (swaps:List Nat):=
 (cE (ac old)&&bP (ac old)&&(aN old).all bP)&&cE (ac rep) &&
  eG (swaps.map dh) (aN old) (ac old) (aN rep) (ac rep)
lemma mP {u old rep L swaps} (ok:jx old rep swaps=true) (h:aR u (aN rep) (ac rep) L):aR u (aN old) (ac old) L:=by
 simp only [jx,and_eq_true] at ok;exact sm ok.2 (cN _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (cN _ ok.1.2) h
end
def ai (entries:List (Nat × Nat)) (q:Nat):=((entries.find? (fun a=>a.1==q)).map Prod.snd).getD 0
section
variable [w : Width]
lemma ad {u} (entries:List (Nat × Nat)) (sound:∀ e ∈ entries,aR u (aN e.1) (ac e.1) e.2) (q:Nat):aR u (aN q) (ac q) (ai entries q):=by
 unfold ai
 cases h:entries.find? (fun a=>a.1==q) with
 | none=>exact fun _ _ _ _=>Nat.zero_le _
 | some e =>
  have he:=List.mem_of_find?_eq_some h;have hit:(fun a:Nat × Nat=>a.1==q) e=true:=List.find?_some (p:=fun a:Nat × Nat=>a.1==q) (a:=e) h;have eq:e.1=q:=beq_iff_eq.mp hit;simpa only [Option.map_some,Option.getD_some,eq] using sound e he
abbrev bu:=aQ × Nat × Nat × List aQ
def bu.d (c:bu):aQ:=c.1
def bu.b (c:bu):Nat:=c.2.1
def bu.p (c:bu):Nat:=c.2.2.1
def bu.wires (c:bu):List aQ:=c.2.2.2
def dx (u:Bool) (raw:List aQ) (T:aQ) (c:bu):=
 ∃ (f:bW->bW) (roots:List aQ) (bank:List (bL bW)),
  (∀ r,aV (f r) c.d=true)/\¬bw (au f (aG T)) /\
  (∀ q ws,bH u (roots.map aG) q ws->aO u ws (au f (aG T))->c.b ≤ q) /\
  bH u (roots.map aG) c.p bank/\d4 u f bank c.wires/\True
lemma mO {u raw T d lb} (h:gB u raw T d lb) (cs:List ej) {ws} (build:fw u d raw cs=some ws):dx u raw T ⟨d,lb,cs.length,ws⟩:=by
 obtain ⟨f,roots,dom,sup,nc,prior⟩:=h;obtain ⟨bank,hr,hs⟩:=gQ dom (bH.start (roots:=roots.map aG)) sup cs build;exact ⟨f,roots,bank,dom,nc,prior,by simpa [bu.p] using hr,hs,trivial⟩
lemma k8 {u raw T c} (valid:dx u raw T c) (k:Nat) (rest:List aQ) (choice:ej) (paid:Bool) (known:∀ a ∈ rest,bd u c.d c.wires a=true) (buy:if paid then fn u c.d c.wires choice=true else bd u c.d c.wires (bp choice)=true) (bound:k+c.p+paid.toNat<c.b+(bp choice :: rest).countP (ay c.d)) (nd:(bp choice :: rest).Nodup):aB u T k (bp choice :: rest).toFinset:=by
 intro t ht run;obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩:=valid;let ws:=bp choice::rest
 have done (n:Nat) (out:List (bL bW)) (reach:bH u (roots.map aG) n out)
  (zs:d4 u f out (bp choice::rest)) (le:n=c.p+paid.toNat):False:=by
  have dS:h9 u out ((ws.map aG).map (au f)):=by
   intro v hv;obtain ⟨_,hm,rfl⟩:=mem_map.mp hv;obtain ⟨a,ha,rfl⟩:=mem_map.mp hm;exact zs _ ha
  have b:=eP f (kq run ws nd rfl) nc reach dS lo;have cm:=gu dom ws;change k+c.p+paid.toNat<c.b+ws.countP (ay c.d) at bound;omega
 cases paid with
 | false =>
  apply done _ _ hp _ rfl;intro a h
  rcases mem_cons.mp h with rfl|hm
  . exact cM dom hs buy
  . exact cM dom hs (known _ hm)
 | true =>
  obtain ⟨out,hr,hc⟩:=kH dom hp hs choice buy;apply done _ _ hr _ rfl;intro a h
  rcases mem_cons.mp h with rfl|hm
  . exact hc _ (by simp)
  . have point:∀ v ∈ c.wires,aO u out (au f (aG v)):=
     fun v hu=>hc v (mem_cons_of_mem _ hu)
    exact cM dom point (known _ hm)
def ct (u:Bool) (c:bu) (k:Nat) (rest:List aQ) (op:ej):=
 let z:=bp op
 let extra := !(bd u c.d c.wires z)
 ((k+c.p+extra.toNat<c.b+(z::rest).countP (ay c.d)) &&
  rest.all (bd u c.d c.wires))&&(!extra||fn u c.d c.wires op)
lemma eS {u raw T c} (valid:dx u raw T c) {k rest op} (nd:(bp op::rest).Nodup) (cut:ct u c k rest op=true):aB u T k (bp op::rest).toFinset:=by
 let extra := !(bd u c.d c.wires (bp op));apply k8 valid k rest op extra _ _ _ nd
 . simp only [ct,and_eq_true,all_eq_true] at cut;exact cut.1.2
 . simp only [ct,and_eq_true,or_eq_true] at cut
   cases he:bd u c.d c.wires (bp op)<;>simp_all [extra]
 . simp only [ct,and_eq_true,decide_eq_true_eq] at cut;exact cut.1.1
def fH (u:Bool) (raw:List aQ) (cs:List ej) (d:aQ) (lb:Nat):Option bu:=(fw u d raw cs).map (fun pool=>⟨d,lb,cs.length,pool⟩)
lemma fI {u raw T d L cs c} (slice:gB u raw T d L) (h:fH u raw cs d L=some c):dx u raw T c:=by
 unfold fH at h
 cases he:fw u d raw cs with
 | none=>simp [he] at h
 | some pool =>
  simp only [he,Option.map_some,Option.some.injEq] at h;subst c;exact mO slice cs he
end
abbrev bt:=BitVec 152
abbrev jw:=bt × bt
section
variable [w : Width]
abbrev aI:=aQ × jw
def fy {n:Nat} (r:Fin n->bW) (v:aQ):BitVec n:=(ofBoolListLE (List.ofFn (fun i=>aV (r i) v))).cast length_ofFn
lemma dq {n:Nat} (r:Fin n->bW) (v:aQ) (i:Fin n):(fy r v).getLsbD i.val=aV (r i) v:=by
 simp only [fy,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,getD_eq_getElem?_getD,List.getElem?_ofFn];simp [i.isLt]
def eD (r s:Fin 152->bW) (a:aQ):jw:=(fy r a,fy s a)
def dH (T:aQ) (r s:Fin 152->bW) := ∀ i,aV (r i) T=true/\aV (s i) T=false
lemma wm {T r s} (h:dH T r s):CF T 152 r s (eD r s):=by exact ⟨h,fun a i=>⟨dq _ _ _,dq _ _ _⟩⟩
def cP (r s:Fin 152->bW) (x:aI):=x.2=eD r s x.1
def bv {n:Nat} (d:Nat) (a b:BitVec n):BitVec n:=if d=0 then a&&&b else if d=1 then a|||b else if d=2 then a &&& ~~~b else ~~~a&&&b
def fq (d:Nat) (x y:aI):aI:=(bM d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)
lemma pe {n:Nat} (r:Fin n->bW) (d:Nat) (a b:aQ):fy r (bM d a b)=bv d (fy r a) (fy r b):=by
 apply eq_of_getLsbD_eq;intro j hj;have h:=dq r (bM d a b) ⟨j,hj⟩;rw [dQ,<-dq r a ⟨j,hj⟩,<-dq r b ⟨j,hj⟩] at h;rw [h];unfold bv
 split_ifs<;>simp [hj]
lemma ip {r s x y} (d) (hx:cP r s x) (hy:cP r s y):cP r s (fq d x y):=by
 change x.2=_ at hx;change y.2=_ at hy;simp only [cP,fq,eD,pe,hx,hy]
def af:aI:=(zero,0,0)
lemma iX (r s):cP r s af:=by
 apply Prod.ext<;>apply eq_of_getLsbD_eq<;>intro j hj
 . change (0:bt).getLsbD j=(fy r zero).getLsbD j;rw [show (fy r zero).getLsbD j=aV (r ⟨j,hj⟩) zero from dq _ _ ⟨j,hj⟩,cn]
   simp
 . change (0:bt).getLsbD j=(fy s zero).getLsbD j;rw [show (fy s zero).getLsbD j=aV (s ⟨j,hj⟩) zero from dq _ _ ⟨j,hj⟩,cn]
   simp
lemma iq {r s ws} (all:∀ v ∈ ws,cP r s v) (i:Nat):cP r s (List.getD ws i af):=by
 simp only [getD_eq_getElem?_getD]
 cases e:ws[i]? with
 | none=>exact iX _ _
 | some v=>exact all _ (List.mem_of_getElem? e)
def ft (n:Nat) (bits:Nat) (ws:List aI):List aI:=
 match n with
 | 0=>ws
 | k+1 =>
  let a:=ws.getD (bits&&&15) af
  let b:=ws.getD ((bits>>>4)&&&15) af
  ft k (bits>>>10) (ws++[fq ((bits>>>8)&&&3) a b])
lemma gw (n bits) (ws) (r s) (base:∀ v ∈ ws,cP r s v):∀ v ∈ ft n bits ws,cP r s v:=by
 induction n generalizing ws bits with
 | zero=>exact base
 | succ n ih =>
  apply ih;intro v hv
  rcases mem_append.mp hv with hw|hz
  . exact base _ hw
  . obtain rfl:=List.mem_singleton.mp hz;exact ip _ (iq base _) (iq base _)
def fj (cols:Nat->bt) (i:Fin 152):bW:=
 (ofBoolListLE (List.ofFn (fun j:Fin N=>(cols j.val).getLsbD i.val))).toFin.cast
  (by rw [length_ofFn,<- nY])
lemma ee:∀ (j:Fin N) (r:bW),aV r (inputs.getD j.val zero)=r.val.testBit j.val:=by
 rcases w with ⟨_|_⟩
 . intro j r;fin_cases j
   . exact t0 r
   . exact t3 r
   . exact t4 r
   . exact t5 r
   . exact t6 r
   . exact t7 r
   . exact t8 r
   . exact t9 r
   . exact ua r
 . intro j r;fin_cases j
   . exact rM r
   . exact rN r
   . exact rO r
   . exact rP r
   . exact rQ r
   . exact rR r
   . exact rS r
   . exact rT r
   . exact rU r
   . exact rV r
lemma iO (cols:Nat->bt) (i:Fin 152) (j:Fin N):aV (fj cols i) (inputs.getD j.val zero)=(cols j.val).getLsbD i.val:=by
 rw [ee];change (ofBoolListLE (List.ofFn (fun h:Fin N=>(cols h.val).getLsbD i.val))).getLsbD j.val=_;simp only [BitVec.getLsbD_ofBoolListLE,getD_eq_getElem?_getD,List.getElem?_ofFn];simp [j.isLt]
def iH (m:Nat) (p q:Nat->bt):List aI:=(dt m).map (fun (j,a)=>(a,p j,q j))
lemma gV {m j a} (h:(j,a) ∈ dt m):j<N/\a=inputs.getD j zero:=by
 obtain ⟨v,hv,hh⟩:=List.mem_filterMap.mp h;simp only [mem_range] at hv
 split at hh
 next=>cases hh;exact ⟨hv,rfl⟩
 next=>contradiction
lemma mq (m) (p q:Nat->bt):∀ a ∈ iH m p q,cP (fj p) (fj q) a:=by
 intro a ha;obtain ⟨⟨j,v⟩,hv,rfl⟩:=mem_map.mp ha;obtain ⟨hj,rfl⟩:=gV hv
 apply Prod.ext<;>apply eq_of_getLsbD_eq<;>intro i hi
 . exact (iO p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (dq _ _ ⟨i,hi⟩).symm
 . exact (iO q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (dq _ _ ⟨i,hi⟩).symm
def iD (m:Nat) (v:Nat->bt):bt:=
 let x:=fun j=>if m.testBit j then v j else 0
 let base:=(x 0&&&x 1)|||(x 1&&&x 2)|||(x 2&&&x 3)|||(x 3&&&x 4) |||
  (x 4&&&x 0)|||(x 0&&&x 5)|||(x 1&&&x 6)|||(x 2&&&x 7) |||
  (x 3&&&x 8)|||(x 5&&&x 7)|||(x 6&&&x 8)|||(x 8&&&x 5)
 if w.wide then base|||(x 4&&&x 9)|||(x 7&&&x 9)|||(x 9&&&x 6) else base
lemma oH (m:Nat) (v:Nat->bt) (i:Fin 152) (j:Fin N):aV (fj v i) (eB m j.val)=((if m.testBit j.val then v j.val else 0):bt).getLsbD i.val:=by
 by_cases hh:m.testBit j.val=true
 . simpa [eB,hh] using iO v i j
 . simp [eB,hh,cn]
lemma l9 (m:Nat) (v:Nat->bt) (i:Fin 152):aV (fj v i) (ac m)=(iD m v).getLsbD i.val:=by
 have pos (j:Nat) (hj:j<N):(eB m j).getLsbD (fj v i).val=((if m.testBit j then v j else 0):bt).getLsbD i.val:=oH m v i ⟨j,hj⟩
 rcases w with ⟨_|_⟩
 . simp only [aV,ac,iD,false_eq_true,ite_false,getLsbD_and,getLsbD_or];simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
 . simp only [aV,ac,iD,ite_true,getLsbD_and,getLsbD_or];simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide),pos 9 (by decide)]
end
abbrev tU:=bt × bt × bt
def ek (z:bt) (c:tU):tU:=
 (z|||c.1,(z &&& ~~~c.1)|||(c.2.1 &&& ~~~z),
  (z&&&c.2.1)|||(c.2.2 &&& ~~~z))
section
variable [w : Width]
def bJ (d:Bool) (v:List aI):tU:=v.foldr (fun a c=>ek (bU d a.2) c) (0,0,0)
end
def e7 (c:tU) (a:bt):bt:=c.1 &&& ~~~(c.2.1&&&a)
def hC (c:tU) (a b:bt):bt:=c.1 &&& ~~~((c.2.1&&&(a|||b))|||(c.2.2&&&(a&&&b)))
section
variable [w : Width]
private theorem w8 (c:tU) (a:bt):e7 (ek a c) a=c.1:=by
 apply eq_of_getLsbD_eq;intro i hi;simp only [e7,ek,getLsbD_or,getLsbD_and,getLsbD_not,hi,decide_true,Bool.true_and]
 cases a.getLsbD i<;>cases c.1.getLsbD i<;>cases c.2.1.getLsbD i<;>rfl
private theorem w9 (c:tU) (a b:bt):hC (ek a (ek b c)) a b=c.1:=by
 apply eq_of_getLsbD_eq;intro i hi;simp only [hC,ek,getLsbD_or,getLsbD_and,getLsbD_not,hi,decide_true,Bool.true_and]
 cases a.getLsbD i<;>cases b.getLsbD i<;>cases c.1.getLsbD i <;>
  cases c.2.1.getLsbD i<;>cases c.2.2.getLsbD i<;>rfl
private theorem tV (c:tU) (a b:bt):ek a (ek b c)=ek b (ek a c):=by
 apply Prod.ext
 . apply eq_of_getLsbD_eq;intro i hi;simp only [ek,getLsbD_or]
   cases a.getLsbD i<;>cases b.getLsbD i<;>rfl
 . apply Prod.ext<;>apply eq_of_getLsbD_eq<;>intro i hi <;>
    simp only [ek,getLsbD_or,getLsbD_and,getLsbD_not,hi,decide_true,Bool.true_and] <;>
    cases a.getLsbD i<;>cases b.getLsbD i<;>cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i<;>cases c.2.2.getLsbD i<;>rfl
private theorem mS (d:Bool) {l r:List aI} (h:l.Perm r):bJ d l=bJ d r:=by
 induction h with
 | nil=>rfl
 | cons a _ ih=>exact congrArg (ek (bU d a.2)) ih
 | swap a b t=>exact tV _ _ _
 | trans _ _ h1 h2=>exact h1.trans h2
lemma ub (d:Bool) (v:List aI) {r s} (good:∀ a ∈ v,cP r s a):(bJ d v).1=dS d (eD r s) (v.map Prod.fst):=by
 induction v with
 | nil=>rfl
 | cons a v ih =>
  change (bU d a.2|||(bJ d v).1)=bU d (eD r s a.1)|||_;rw [show a.2=eD r s a.1 from good _ (by simp),ih (fun a ha=>good a (by simp [ha]))]
def eO (ws:List aI) (a:aI) (keep:Bool):=if keep then ws else ws.erase a
def cO (ws:List aI) (a b:aI) (ka kb:Bool):=eO (eO ws a ka) b kb
lemma gG {ws:List aI} (a:aI) (ha:a ∈ ws):ws.Perm (a::ws.erase a):=List.perm_cons_erase ha
lemma lh {ws:List aI} (d:Bool) (a:aI) (ha:a ∈ ws) (keep:Bool):(bJ d (eO ws a keep)).1=(if keep then (bJ d ws).1 else e7 (bJ d ws) (bU d a.2)):=by
 cases keep
 . change (bJ d (ws.erase a)).1=e7 (bJ d ws) _;rw [mS d (gG a ha)];exact (w8 _ _).symm
 . rfl
lemma mV {ws:List aI} (a b:aI) (ha:a ∈ ws) (hb:b ∈ ws) (hne:a≠b):ws.Perm (a::b::(ws.erase a).erase b):=by
 have hm:b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm hne)).mpr hb;exact (gG a ha).trans (List.Perm.cons _ (gG b hm))
lemma rW {ws:List aI} (d:Bool) (a b:aI) (ha:a ∈ ws) (hb:b ∈ ws) (ne:a≠b) (ka kb:Bool):(bJ d (cO ws a b ka kb)).1=(if ka then (if kb then (bJ d ws).1 else e7 (bJ d ws) (bU d b.2)) else if kb then e7 (bJ d ws) (bU d a.2) else hC (bJ d ws) (bU d a.2) (bU d b.2)):=by
 cases ka<;>cases kb
 . change (bJ d ((ws.erase a).erase b)).1=hC (bJ d ws) _ _;rw [mS d (mV a b ha hb ne)];exact (w9 _ _ _).symm
 . exact lh d a ha false
 . exact lh d b hb false
 . rfl
def fi (a b:List aQ):=(a.all (fun x=>b.contains x))&&(b.all (fun x=>a.contains x))
lemma d2 {xs ys} (h:fi xs ys=true):xs.toFinset=ys.toFinset:=by
 simp only [fi,and_eq_true,all_eq_true,contains_eq_mem,decide_eq_true_eq] at h
 ext a
 simp only [mem_toFinset];exact ⟨h.1 a,h.2 a⟩
def ef (v:aQ):=
 let n:=v.toNat % 2305843009213693951
 (n*(n+971)) % 2305843009213693951
def jW (xs:List aQ):=xs.foldl (fun v x=>v+ef x) 0
def em (u:Bool) (pools:List bu) (links:Nat->List (List aQ)) (k:Nat) (rest:List aQ) (op:ej):=
 let ws:=bp op::rest
 (links (jW ws)).any (fi ws)||pools.any (fun p=>ct u p k rest op)
lemma iU {u raw T pools links k rest op} (pValid:∀ p ∈ pools,dx u raw T p) (lValid:∀ tag xs,xs ∈ links tag->aB u T k (List.toFinset xs)) (nd:(bp op :: rest).Nodup) (h:em u pools links k rest op=true):aB u T k (bp op :: rest).toFinset:=by
 simp only [em,or_eq_true,any_eq_true] at h
 rcases h with ⟨xs,hx,ok⟩|⟨p,hp,ok⟩
 . rw [d2 ok];exact lValid _ _ hx
 . exact eS (pValid _ hp) nd ok
abbrev q7:=tU × Bool
def gS (u:Bool) (ws:List aI):q7:=(bJ (!u) ws,u)
def gh (v:tU) (a b:bt) (ka kb:Bool):=if ka then (if kb then v.1 else e7 v b) else if kb then e7 v a else hC v a b
lemma hV (ws:List aI) (a:aI) (k:Bool):(eO ws a k).Sublist ws:=by
 cases k
 . exact List.erase_sublist
 . exact List.Sublist.refl _
lemma vC (ws:List aI) (a b:aI) (ka kb:Bool):(cO ws a b ka kb).Sublist ws:=(hV _ _ _).trans (hV _ _ _)
lemma vF (ws:List aI) (a b:aI) (ka kb:Bool) (ha:a ∈ ws) (hb:b ∈ ws) (ne:a≠b):(cO ws a b ka kb).length=ws.length-(if ka then 0 else 1)-(if kb then 0 else 1):=by
 have hm:b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm ne)).mpr hb
 cases ka<;>cases kb<;>simp [cO,eO,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
def cj (op:Nat) (a b:aI):ej:=(op,a.1,b.1)
abbrev bc:=Nat × Nat × List aI × q7 × List bu × (Nat->List (List aQ))
def ec (c:bc) (op:Nat) (a b z:aI) (ka kb:Bool):=
 let (cap,n,ws,cov,pools,links):=c
 let len:=1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
 if len>cap then true else
  let d := !cov.2
  let rs:=gh cov.1 (bU d a.2) (bU d b.2) ka kb
  if (rs|||bU d z.2) !=allOnes 152 then true else
  if !cE z.1||ws.any (fun v=>v.1==z.1) then true else
   let rest:=(cO ws a b ka kb).map Prod.fst
   em cov.2 pools links (cap-1) rest (cj op a b)
def i5 (ws:List aI) (op:Nat) (a b:aI) (ka kb:Bool):=(fq op a b).1 :: (cO ws a b ka kb).map Prod.fst
lemma gH {u raw T r s ws pools links cap a b op ka kb} (pairs:dH T r s) (faith:∀ w ∈ ws,cP r s w) (nd:(ws.map Prod.fst).Nodup) (ha:a ∈ ws) (hb:b ∈ ws) (ne:a≠b) (hcap:0<cap) (pv:∀ p ∈ pools,dx u raw T p) (lv:∀ tag xs,xs ∈ links tag->aB u T (cap-1) (List.toFinset xs)) (pro:bg (fq op a b).1) (fresh:(fq op a b).1 ∉ ws.map Prod.fst) (test:ec (cap,ws.length,ws,gS u ws,pools,links) op a b (fq op a b) ka kb=true):aB u T (cap-1) (i5 ws op a b ka kb).toFinset:=by
 let z:=fq op a b;let rest:=cO ws a b ka kb;let child:=z.1 :: rest.map Prod.fst;have sub:rest.Sublist ws:=vC _ _ _ _ _
 have ndc:child.Nodup:=nodup_cons.mpr ⟨fun hm=>fresh ((sub.map _).subset hm),
  nd.sublist (sub.map _)⟩
 have fr:ws.any (fun v=>v.1==z.1)=false:=by
  apply Bool.eq_false_iff.mpr;intro hh;obtain ⟨x,hx,he⟩:=any_eq_true.mp hh;exact fresh (beq_iff_eq.mp he ▸ mem_map_of_mem hx)
 have pp:cE z.1=true:=by simpa [cE,bg] using pro
 have leq:1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1))=child.length:=by
  change _=(z.1::rest.map Prod.fst).length;rw [length_cons,length_map,vF _ _ _ _ _ ha hb ne,Nat.add_comm 1]
 intro k hk h;have hsz:=g9 h;change child.toFinset.card ≤ k+1 at hsz;rw [List.toFinset_card_of_nodup ndc] at hsz
 have len:child.length ≤ cap:=by omega
 unfold ec at test;change (if 1+(ws.length-_-_)>cap then true else _)=true at test;rw [leq,if_neg (by omega)] at test;have sep:=jM h (wm pairs);let d := !u
 have g:(bJ d rest).1=dS d (eD r s) (rest.map Prod.fst):=
  ub _ _ (fun v hv=>faith _ (sub.subset hv))
 have rz:(bJ d rest).1=gh (bJ d ws) (bU d a.2) (bU d b.2) ka kb:=
  rW d a b ha hb ne ka kb
 have hf:=ip op (faith _ ha) (faith _ hb);change bU d (eD r s z.1)|||dS d (eD r s) (rest.map Prod.fst)=_ at sep;change z.2=eD r s z.1 at hf;rw [<-hf,<-g,rz,BitVec.or_comm] at sep
 have be:((gh (bJ (!u) ws) (bU (!u) a.2) (bU (!u) b.2) ka kb|||bU (!u) z.2) !=allOnes 152)=false:=by
  simpa using sep
 change (if (gh (bJ (!u) ws) (bU (!u) a.2) (bU (!u) b.2) ka kb|||bU (!u) z.2) !=allOnes 152 then true else if !cE z.1||ws.any (fun v=>v.1==z.1) then true else _)=true at test;rw [be,pp,fr] at test;exact iU (op:=cj op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h
def dJ (ctx:bc) (a b:aI) (op:Nat):=
 let z:=fq op a b
 let attempt:=ec ctx op a b z
 attempt false false&&attempt true false&&attempt false true&&attempt true true
def kE (u:Bool):List Nat:=if u then [0,1,2,3] else [0,1]
lemma lT {u d} (h:bY u d):d ∈ kE u:=by
 rcases cq h with rfl|rfl|⟨rfl,rfl⟩|⟨rfl,rfl⟩
 . cases u<;>simp [kE]
 . cases u<;>simp [kE]
 . simp [kE]
 . simp [kE]
def mC (ctx:bc) (a:aI) (bs:List aI):=bs.all (fun b=>(kE ctx.2.2.2.1.2).all (dJ ctx a b))
def e8 (ctx:bc):List aI->Bool
 | []=>true
 | a::bs=>mC ctx a bs&&e8 ctx bs
lemma oE {ctx ws} (h:e8 ctx ws=true) {a b:aI} (ha:a∈ws) (hb:b∈ws) (ne:a≠b):(∀ d,bY ctx.2.2.2.1.2 d->dJ ctx a b d=true)\/(∀ d,bY ctx.2.2.2.1.2 d->dJ ctx b a d=true):=by
 induction ws with
 | nil=>simp at ha
 | cons w ws ih =>
  simp only [e8,and_eq_true,mC,all_eq_true] at h
  rcases mem_cons.mp ha with rfl|haTail
  . have bm:=(mem_cons.mp hb).resolve_left (Ne.symm ne);exact Or.inl fun d hd=>h.1 b bm d (lT hd)
  . rcases mem_cons.mp hb with rfl|hbTail
    . exact Or.inr fun d hd=>h.1 a haTail d (lT hd)
    . exact ih h.2 haTail hbTail
lemma jo {ctx a b d} (h:dJ ctx a b d=true) (ka kb:Bool):ec ctx d a b (fq d a b) ka kb=true:=by
 simp only [dJ,and_eq_true] at h
 cases ka<;>cases kb<;>first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
lemma nj {v:List aQ} {w:aQ} (a:aQ) (k:Bool):w ∈ cT k a v ↔ (w=a/\k=true)\/w∈v:=by cases k<;>simp [cT]
lemma kx {v:List aI} (nd:v.Nodup) (a w:aI) (k:Bool):w ∈ eO v a k ↔ w∈v/\(w≠a\/k=true):=by cases k<;>simp [eO,nd.mem_erase_iff,and_comm]
lemma iK {ws:List aI} (nd:(ws.map Prod.fst).Nodup) {a b:aI} (ha:a∈ws) (hb:b∈ws) (eq:a.1=b.1):a=b:=by
 induction ws with
 | nil=>simp at ha
 | cons w ws ih =>
  obtain ⟨hn,ht⟩:=nodup_cons.mp nd
  rcases mem_cons.mp ha with rfl|haTail<;>rcases mem_cons.mp hb with rfl|hbTail
  . rfl
  . exact False.elim (hn (eq ▸ mem_map_of_mem hbTail))
  . exact False.elim (hn (eq.symm ▸ mem_map_of_mem haTail))
  . exact ih ht haTail hbTail
lemma jV {ws:List aI} (nd:(ws.map Prod.fst).Nodup) {a b:aI} (ha:a ∈ ws) (hb:b ∈ ws) (ka kb:Bool) (v:aQ):v ∈ (cO ws a b ka kb).map Prod.fst ↔ v ∈ ws.map Prod.fst/\(v≠a.1\/ka=true)/\(v≠b.1\/kb=true):=by
 have wn:=nd.of_map;have dn:=wn.sublist (hV ws a ka);simp only [cO,mem_map,kx wn,kx dn];constructor
 . rintro ⟨w,hw,rfl⟩
   exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq=>ne (iK nd hw.1.1 ha eq)) id,
    hw.2.imp (fun ne eq=>ne (iK nd hw.1.1 hb eq)) id⟩
 . rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
   exact ⟨w,⟨⟨hm,h1.imp (fun ne eq=>ne (congrArg Prod.fst eq)) id⟩,
    h2.imp (fun ne eq=>ne (congrArg Prod.fst eq)) id⟩,rfl⟩
lemma ii {ws:List aI} (nd:(ws.map Prod.fst).Nodup) {a b:aI} (ha:a∈ws) (hb:b∈ws) (ne:a.1≠b.1) (d:Nat) (ka kb:Bool):(i5 ws d a b ka kb).toFinset=(cu (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
 ext v
 have av:=mem_map_of_mem (f:=Prod.fst) ha;have bv':=mem_map_of_mem (f:=Prod.fst) hb
 simp only [i5,cu,List.toFinset_cons,mem_insert,mem_toFinset,
  jV nd ha hb,nj,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,fq]
 by_cases va:v=a.1<;>by_cases vb:v=b.1<;>cases ka<;>cases kb<;>simp_all
lemma hF {u} (v:List aQ) (nd:v.Nodup) (a b:aQ) (d:Nat) (hd:bY u d) (ka kb:Bool):(cu v a b d ka kb).toFinset=(cu v b a (gJ d) kb ka).toFinset:=by
 ext x
 simp only [cu,List.toFinset_cons,mem_insert,mem_toFinset,
  nj,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,gE hd a b]
 tauto
lemma pd {u raw T r s ws pools links cap} (pairs:dH T r s) (faith:∀ w ∈ ws,cP r s w) (nd:(ws.map Prod.fst).Nodup) (out:T ∉ ws.map Prod.fst) (pv:∀ p ∈ pools,dx u raw T p) (lv:∀ tag xs,xs ∈ links tag->aB u T (cap-1) (List.toFinset xs)) (checks:e8 (cap,ws.length,ws,gS u ws,pools,links) ws=true):aB u T cap (ws.map Prod.fst).toFinset:=by
 by_cases hc:cap=0
 . intro k hk h
   have ke:k=0:=by omega
   subst k;generalize he:(ws.map Prod.fst).toFinset=S at h;obtain ⟨hS,_⟩:=h;exact out (mem_toFinset.mp (by rw [he,hS];exact Finset.mem_singleton_self _))
 have hc':0<cap:=by omega
 apply rX nd out;intro a ha b hb d hd ka kb ne fresh pro len;obtain ⟨a,haW,rfl⟩:=mem_map.mp ha;obtain ⟨b,hbW,rfl⟩:=mem_map.mp hb;have ab:a≠b:=fun e=>ne (congrArg Prod.fst e)
 have one (a b:aI) (d:Nat) (aa:a∈ws) (bb:b∈ws) (ne':a.1≠b.1) (ka kb:Bool)
  (pr:bg (bM d a.1 b.1)) (fr:bM d a.1 b.1 ∉ ws.map Prod.fst)
  (test:dJ (cap,ws.length,ws,gS u ws,pools,links) a b d=true):
  aB u T (cap-1) (cu (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
  rw [<-ii nd aa bb ne']
  exact gH pairs faith nd aa bb (fun e=>ne' (congrArg Prod.fst e)) hc' pv lv
   pr fr (jo test ka kb)
 rcases oE checks haW hbW ab with hh|hh
 . exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
 . rw [hF _ nd _ _ d hd]
   exact one b a (gJ d) hbW haW (Ne.symm ne) kb ka (gE hd a.1 b.1 ▸ pro)
    (gE hd a.1 b.1 ▸ fresh) (hh _ (rY hd).1)
lemma l4 (r s:bW) (h:∀ a ∈ inputs,aV r a=aV s a):r=s:=by
 apply Fin.ext;apply eq_of_testBit_eq;intro j
 by_cases hj:j<N
 . let i:Fin N:=⟨j,hj⟩;have hm:inputs.getD i.val zero ∈ List.ofFn (fun k:Fin N=>inputs.getD k.val zero):=List.mem_ofFn.mpr ⟨i,rfl⟩;rw [h6] at hm;exact (ee i r).symm.trans ((h _ hm).trans (ee i s))
 . have le:W ≤ 2^j:=by
    rw [nY];exact Nat.pow_le_pow_right (by decide) (by omega)
   exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
    (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm
def hU (p q:List ie):=inputs.all (fun a=>bn p (bn q a)==a)
lemma je {p q} (h:hU p q=true) (r:bW):cR q (cR p r)=r:=by
 apply l4;intro a ha;rw [<-fU,<-fU];have eq:=beq_iff_eq.mp (all_eq_true.mp h a ha);rw [eq]
def iP (T:aQ) (p:List ie):=(bn p T==T)&&hU p p.reverse&&hU p.reverse p
lemma ju {u T n} {ws:List aQ} (hi:aB u T n ws.toFinset) (p:List ie) (ok:iP T p=true):aB u T n (ws.map (bn p.reverse)).toFinset:=by
 simp only [iP,and_eq_true,beq_iff_eq] at ok;have onto:Function.Surjective (cR p):=fun r=>⟨cR p.reverse r,je ok.2 r⟩;intro k hk h;have run:=nm h (cR p) onto;have goal:cU (cR p) T=T:=(cF p T).symm.trans ok.1.1
 have ln (x:aQ):cU (cR p) (bn p.reverse x)=x:=by
  apply eq_of_getLsbD_eq;intro j hj;change aV ⟨j,hj⟩ _=aV ⟨j,hj⟩ _;rw [dD,fU,je ok.1.2]
 have back:(ws.map (bn p.reverse)).toFinset.image (cU (cR p))=ws.toFinset:=by
  ext a
  simp only [Finset.mem_image,mem_toFinset,mem_map];constructor
  . rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩;simpa only [ln] using hw
  . intro ha;exact ⟨_,⟨a,ha,rfl⟩,ln a⟩
 rw [goal,back] at run;exact hi k hk run
end
abbrev aF:=Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat->Nat)
def a0:aF:=(0,0,0,0,0,0,0,fun _=>0)
def bE (word:Nat->Nat) (pos len:Nat):=
 let i:=pos/8192
 let shift:=pos % 8192
 let lo:=word i>>>shift
 if shift+len ≤ 8192 then lo&&&((1<<<len)-1)
 else (lo|||(word (i+1)<<<(8192-shift)))&&&((1<<<len)-1)
def aK (nb slots sw vw iw pw:Nat) (data:Nat->Nat) (h:Nat):Option (Nat × Nat):=
 let a:=h % nb
 let sh:=bE data (a*sw) sw
 let row:=(h/nb+sh) % slots
 let word:=bE data (nb*sw+row*vw) vw
 if (word>>>(iw+pw))==h/(nb*slots) % 16 then
  some (word&&&((1<<<iw)-1),(word>>>iw)&&&((1<<<pw)-1))
 else none
def ch (nb slots sw vw iw pw:Nat) (data:Nat->Nat) (h:Nat):Option (Nat × Nat):=
 let a:=h % nb
 let sh:=bE data (a*sw) sw
 let row:=(h/nb+sh) % slots
 let word:=bE data (nb*sw+row*vw) vw
 if (word>>>(iw+pw))==h/(nb*slots) % 4 then
  some (word&&&((1<<<iw)-1),(word>>>iw)&&&((1<<<pw)-1))
 else none
abbrev aM:=Nat × Nat × (Nat->bt × bt) × List aZ × List (List Nat) ×
 (Nat->aF) × (Nat->Nat->Option (Nat × Nat))
def aM.m (g:aM):Nat:=g.1
section
variable [w : Width]
def aM.u (g:aM):Bool := !(g.1.testBit (if w.wide then 12 else 10))
end
def aM.cap (g:aM):Nat:=g.2.1
def aM.s (g:aM):Nat->bt × bt:=g.2.2.1
def aM.c (g:aM):List aZ:=g.2.2.2.1
def aM.a (g:aM):List (List Nat):=g.2.2.2.2.1
def aM.l (g:aM):Nat->aF:=g.2.2.2.2.2.1
def aM.x (g:aM):Nat->Nat->Option (Nat × Nat):=g.2.2.2.2.2.2
section
variable [w : Width]
def e9 (g:aM):=
 let ws:=iH g.m (fun j=>(g.s j).1) (fun j=>(g.s j).2)
 ws
lemma gY (g:aM):∀ a ∈ e9 g,cP (fj fun j=>(g.s j).1) (fj fun j=>(g.s j).2) a:=by exact mq g.m (fun j=>(g.s j).1) (fun j=>(g.s j).2)
def aY (g:aM):=dR g.m
def eb (m:Nat) (v:Nat->bt):=iD m v
lemma rK (m:Nat) (v:Nat->bt) (i:Fin 152):aV (fj v i) (dR m)=(eb m v).getLsbD i.val:=by exact l9 m v i
lemma eF {m:Nat} {p q:Nat->bt} (hp:eb m p=allOnes 152) (hq:eb m q=0):dH (dR m) (fj p) (fj q):=by
 intro i;simp only [rK,hp,hq,getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
 simp
end
def da {α:Type} (bits:Nat):List α->List α
 | []=>[]
 | w::ws=>if bits&&&1==1 then w::da (bits>>>1) ws else da (bits>>>1) ws
lemma gU {α:Type} (bits:Nat) (ws:List α):(da bits ws).Sublist ws:=by
 induction ws generalizing bits with
 | nil=>exact List.Sublist.slnil
 | cons a ws ih =>
  unfold da
  split
  . exact List.Sublist.cons₂ _ (ih _)
  . exact List.Sublist.cons _ (ih _)
def eL (d:Nat):=10*(d-1)
def hH (d flags:Nat):=flags % 16+(if d=0 then 0 else 10)+flags/16
def hG (d raw dict:Nat):=(dict % 65536)*eL d+(dict/65536)*(raw+d)
def it (tab:aF) (raw i:Nat):Nat:=
 let (_,d,_,dict,flags,_,marker,word):=tab
 let width:=10*d+raw+d
 if marker<1024 then bE word (i*width) width else
  let off:=hG d raw dict+i*hH d flags
  let pre:=bE word off (flags % 16)
  let lastBits:=if d=0 then 0 else 10
  let last:=bE word (off+flags % 16) lastBits
  let mask:=bE word (off+flags % 16+lastBits) (flags/16)
  let base:=(dict % 65536)*eL d
  bE word (pre*eL d) (eL d) |||
   (last<<<eL d)|||(bE word (base+mask*(raw+d)) (raw+d)<<<(10*d))
section
variable [w : Width]
def jm (_g:aM) (depth:Nat):=depth
def f1 (g:aM) (k i:Nat):Nat × List aI × List aI:=
 let raw:=e9 g
 let (_,depth,_,_,_,_,_,data):=g.l k
 let len:=10*jm g depth
 let width:=len+raw.length+depth
 let recp:=it (g.l k) raw.length i
 let stored:=recp&&&((1<<<len)-1)
 let ops:=stored
 let bank:=ft depth ops raw
 (ops,bank,da (recp>>>len) bank)
end
def lm (x pos width:Nat):=(x>>>pos)&&&((1<<<width)-1)
section
variable [w : Width]
def jd (bank:List aI) (ops paid:Nat):Nat->List ej
 | 0=>[]
 | n+1 =>
  let more:=jd bank (ops>>>10) (paid>>>1) n
  if paid&&&1==0 then more else
   (lm ops 8 2,(bank.getD (ops&&&15) af).1,
    (bank.getD (lm ops 4 4) af).1) :: more
def fV (g:aM) (ops d:Nat) (bank:List aI) (idx paid:Nat):Option bu:=
 (g.c[idx]?).bind fun ci =>
  fH g.u (aN (eZ g.m ci)) (jd bank ops paid d) (dC ci.1 ci.2.1) ci.2.2.2.2
lemma gr (g:aM) (cols:∀ ci ∈ g.c,gB g.u (aN (eZ g.m ci)) (aY g) (dC ci.1 ci.2.1) ci.2.2.2.2) {i ops depth bank paid c} (h:fV g ops depth bank i paid=some c):dx g.u (cB g.m) (aY g) c:=by
 unfold fV at h
 cases e:g.c[i]? with
 | none=>simp [e] at h
 | some ci =>
  simp only [e,Option.bind_some] at h;apply fI _ h;exact cols ci (List.mem_of_getElem? e)
end
def ni (data:Nat->Nat) (w v:Nat):Nat->Nat->List (Nat × Nat)
 | 0,_=>[]
 | n+1,pos =>
  let x:=bE data pos (w+v)
  (x&&&((1<<<w)-1),x>>>w) :: ni data w v n (pos+w+v)
def ep {α:Type}:Nat->(Nat -> α) -> α
 | 0,next=>next 0
 | n+1,next=>next (n+1)
def eQ (data:Nat->Nat) (dict cw d gapBits:Nat):Nat->Nat->Nat->List (Nat × Nat)
 | 0,_,_=>[]
 | left+1,st,first =>
  ep st fun pos=>ep first fun base =>
  ep (bE data pos 32) fun head =>
  ep (Nat.log2 (head^^^(head+1))) fun ones =>
  ep (base+(ones<<<gapBits)+bE data (pos+ones+1) gapBits) fun key =>
  ep (bE data (dict+key*(cw+d)) (cw+d)) fun pair =>
   (pair&&&((1<<<cw)-1),pair>>>cw) ::
    eQ data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)
def mn {α:Type} (a b:Nat) (xs:List α):List α:=
 let rec collect:List α->Nat->List α->List α->List α->List α
  | [],_,first,second,other=>first ++ second ++ other.reverse
  | x::tail,i,first,second,other =>
   if i=a then collect tail (i+1) [x] second other
   else if i=b then collect tail (i+1) first [x] other
   else collect tail (i+1) first second (x::other)
 collect xs 0 [] [] []
def gM (tab:aF) (raw i:Nat):List (Nat × Nat):=
 let (num,d,cw,dict,flags,ow,marker,data):=tab
 if marker<1024 then
  let start:=num*(10*d+raw+d)
  let pos:=start+num*ow+bE data (start+i*ow) ow
  ni data cw d (bE data pos 5) (pos+5+marker)
 else
  let off:=hG d raw dict+num*hH d flags
  let pairs:=off+num*ow
  let priority:=decide (4096≤marker)
  let pos:=pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+bE data (off+i*ow) ow
  let n:=bE data pos 5
  let gap:=bE data (pos+5) 3
  if !priority||decide (n≤1) then eQ data pairs cw d gap n (pos+8) 0 else
   let width:=(n-1).log2+1
   let a:=bE data (pos+8) width
   let b:=if n=2 then 1-a else bE data (pos+8+width) width
   let extra:=if n=2 then width else 2*width
   let xs:=eQ data pairs cw d gap n (pos+8+extra) 0
   mn a b xs
section
variable [w : Width]
def bK (g:aM) (k i:Nat):=(f1 g k i).2.2.map Prod.fst
def dT (g:aM) (k:Nat) (pair:Nat × Nat):Option (List aQ):=
 if pair.1 ≥ (g.l k).1 then none else
  (g.a[pair.2]?).map fun perm=>(bK g k pair.1).map (bn (perm.map dh).reverse)
lemma gx (g:aM) (k:Nat) (names:∀ x ∈ g.a,iP (aY g) (x.map dh)=true) (earlier:∀ i<(g.l k).1,aB g.u (aY g) k (bK g k i).toFinset) {pair out} (h:dT g k pair=some out):aB g.u (aY g) k out.toFinset:=by
 unfold dT at h
 split at h
 . contradiction
 next valid =>
  cases e:g.a[pair.2]? with
  | none=>simp [e] at h
  | some perm =>
   simp only [e,Option.map_some,Option.some.injEq] at h;subst out;exact ju (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))
def cW (g:aM) (k i:Nat):=
 let raw:=e9 g
 let (num,depth,cw,iw,pw,offw,lw,data):=g.l k
 let (ops,bank,ws):=f1 g k i
 let values:=ws.map Prod.fst
 let rules:=(gM (g.l k) raw.length i).filterMap (fun (a,b)=>fV g ops depth bank a b)
 let ls:=fun tag=>((g.x k tag).bind (dT g (k-1))).toList
 decide values.Nodup && !(values.contains (aY g)) &&
  (if k=0 then true else e8 (k,ws.length,ws,gS g.u ws,rules,ls) ws)
lemma dp (g:aM) (k i:Nat) (samples:dH (aY g) (fj fun j=>(g.s j).1) (fj fun j=>(g.s j).2)) (cols:∀ ci ∈ g.c,gB g.u (aN (eZ g.m ci)) (aY g) (dC ci.1 ci.2.1) ci.2.2.2.2) (names:∀ x ∈ g.a,iP (aY g) (x.map dh)=true) (prior:k>0->∀ j<(g.l (k-1)).1,aB g.u (aY g) (k-1) (bK g (k-1) j).toFinset) (checked:cW g k i=true):aB g.u (aY g) k (bK g k i).toFinset:=by
 simp only [cW,and_eq_true,decide_eq_true_eq,Bool.not_eq_true',contains_eq_mem] at checked;have hN:=checked.1.1
 have hT:aY g ∉ bK g k i:=by simpa [bK] using checked.1.2
 by_cases h0:k=0
 . subst k;intro t lo h
   have ht:t=0:=by omega
   subst t;generalize he:(bK g 0 i).toFinset=S at h;obtain ⟨hS,_⟩:=h;exact hT (mem_toFinset.mp (by rw [he,hS];exact Finset.mem_singleton_self _))
 apply pd (raw:=cB g.m) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
 . intro v hv;apply gw _ _ _ _ _ (gY g) v;exact (gU _ _).subset hv
 . intro p hp;obtain ⟨⟨a,b⟩,_,h⟩:=List.mem_filterMap.mp hp;exact gr g cols h
 . intro tag xs hx
   have e:((g.x k tag).bind (dT g (k-1)))=some xs:=by simpa using hx
   obtain ⟨pair,_,h⟩:=Option.bind_eq_some_iff.mp e;exact gx g _ names (prior (by omega)) h
def aP (g:aM) (k start:Nat):Nat->Bool
 | 0=>true
 | n+1=>cW g k (start+n)&&aP g k start n
lemma ik {g k start n} (h:aP g k start n=true) (j:Nat) (lo:start≤j) (hi:j<start+n):cW g k j=true:=by
 induction n with
 | zero=>omega
 | succ n ih =>
  simp only [aP,and_eq_true] at h
  by_cases eq:j=start+n
  . simpa [eq] using h.1
  . exact ih h.2 (by omega)
lemma aJ {g k start a b} (h:aP g k start a=true) (h':aP g k (start+a) b=true):aP g k start (a+b)=true:=by
 induction b with
 | zero=>simpa using h
 | succ b ih =>
  simp only [aP,and_eq_true] at h';simp only [Nat.add_succ,aP,and_eq_true];exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩
def bo (g:aM) (top:Nat) := ∀ k ≤ top,aP g k 0 (g.l k).1=true
def aD (g:aM) (prior:Nat->Nat):=
 (eb g.m (fun j=>(g.s j).1)==allOnes 152) &&
 (eb g.m (fun j=>(g.s j).2)==0) &&
 g.c.all (fun c=>fW g.m c prior) &&
 g.a.all (fun p=>iP (aY g) (p.map dh))
lemma jT (g:aM) (top:Nat) (prior:Nat->Nat) (lower:∀ q,aR g.u (aN q) (ac q) (prior q)) (geometry:aD g prior=true) (rows:bo g top):∀ k ≤ top,∀ i<(g.l k).1,aB g.u (aY g) k (bK g k i).toFinset:=by
 simp only [aD,and_eq_true,all_eq_true,beq_iff_eq] at geometry;intro k
 induction k with
 | zero =>
  intro hk i hi
  apply dp g 0 i (eF geometry.1.1.1 geometry.1.1.2)
   (fun x hx=>en _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
  exact ik (rows 0 hk) i (by omega) (by omega)
 | succ k ih =>
  intro hk i hi
  apply dp g _ i (eF geometry.1.1.1 geometry.1.1.2)
   (fun x hx=>en _ prior lower (geometry.1.2 x hx)) geometry.2
   (fun _=>by simpa using ih (by omega))
  exact ik (rows _ hk) i (by omega) (by omega)
def dl (g:aM) (k i:Nat) (ws:List aQ):=decide (i<(g.l k).1)&&fi (bK g k i) ws
lemma gk {g top prior k i ws} (low:∀ q,aR g.u (aN q) (ac q) (prior q)) (geom:aD g prior=true) (blocks:bo g top) (le:k ≤ top) (idx:dl g k i ws=true):aB g.u (aY g) k ws.toFinset:=by
 simp only [dl,and_eq_true,decide_eq_true_eq] at idx;rw [<-d2 idx.2];exact jT g top prior low geom blocks _ le i idx.1
def aX (u:Bool) (entries:List (Nat × Nat)) := ∀ e ∈ entries,aR u (aN e.1) (ac e.1) e.2
end
def ak (old:List (Nat × Nat)) (L:Nat) (carries:List (Nat × List Nat)):=carries.map (fun v=>(v.1,L)) ++ old
section
variable [w : Width]
lemma aC {u old L m carries} (previous:aX u old) (main:aR u (aN m) (ac m) L) (ok:carries.all (fun v=>jx v.1 m v.2)=true):aX u (ak old L carries):=by
 intro e he
 rcases mem_append.mp he with hx|h
 . obtain ⟨v,hv,rfl⟩:=mem_map.mp hx
   exact mP (all_eq_true.mp ok _ hv) main
 . exact previous e h
lemma lf:aX true []:=by simp [aX]
lemma oX {u es} (h:aX true es):aX u es:=fun e he=>kr (h e he)
end
abbrev dd:=Nat × Nat × Nat × List Nat
def eJ (rows:List dd) (base:List (Nat × Nat)):=rows.map (fun e=>(e.1,e.2.1)) ++ base
section
variable [w : Width]
def gW (base:List (Nat × Nat)) (e:dd):=(ai base e.2.2.1==e.2.1)&&jx e.1 e.2.2.1 e.2.2.2
lemma gb {u base rows} (h:aX u base) (cert:rows.all (gW base)=true):aX u (eJ rows base):=by
 intro e he
 rcases mem_append.mp he with hm|hb
 . obtain ⟨r,hr,rfl⟩:=mem_map.mp hm;have hh:=all_eq_true.mp cert r hr;simp only [gW,and_eq_true,beq_iff_eq] at hh;exact mP hh.2 (hh.1 ▸ ad base h r.2.2.1)
 . exact h e hb
end
def cf (v:Nat) (upper:Nat):=2^153*upper+v
def aS {α:Type} (f : α->bt):List α->Nat
 | []=>0
 | x::xs=>cf (f x).toNat (aS f xs)
def kT:Nat->Nat
 | 0=>0
 | n+1=>cf 1 (kT n)
lemma i3 (x:bt):x.toNat<2^153:=lt_trans x.isLt (by decide +kernel)
lemma sr (a b:bt) (u v:Nat):cf a.toNat u&&&cf b.toNat v=cf (a&&&b).toNat (u&&&v):=by
 apply eq_of_testBit_eq;intro i;simp only [cf,testBit_and,Nat.testBit_two_pow_mul_add _ (i3 _)]
 by_cases h:i<153<;>simp only [h,ite_true,ite_false,toNat_and,testBit_and]
lemma wq (a b:bt) (u v:Nat):cf a.toNat u|||cf b.toNat v=cf (a|||b).toNat (u|||v):=by
 apply eq_of_testBit_eq;intro i;simp only [cf,testBit_or,Nat.testBit_two_pow_mul_add _ (i3 _)]
 by_cases h:i<153<;>simp only [h,ite_true,ite_false,toNat_or,testBit_or]
lemma ss (a b:bt) (u v:Nat):cf a.toNat u^^^cf b.toNat v=cf (a^^^b).toNat (u^^^v):=by
 apply eq_of_testBit_eq;intro i;simp only [cf,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (i3 _)]
 by_cases h:i<153<;>simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
lemma fZ {α} (f g : α->bt) (xs):aS f xs&&&aS g xs=aS (fun x=>f x&&&g x) xs:=by
 induction xs with
 | nil=>simp [aS]
 | cons a xs ih=>simp only [aS,sr,ih]
lemma km {α} (f g : α->bt) (xs):aS f xs|||aS g xs=aS (fun x=>f x|||g x) xs:=by
 induction xs with
 | nil=>simp [aS]
 | cons a xs ih=>simp only [aS,wq,ih]
lemma g8 {α} (f g : α->bt) (xs):aS f xs^^^aS g xs=aS (fun x=>f x^^^g x) xs:=by
 induction xs with
 | nil=>simp [aS]
 | cons a xs ih=>simp only [aS,ss,ih]
def g5 (r packed:Nat):=((packed+r)>>>152)&&&r
lemma wM (n i:Nat) (hi:i<n):(kT n).testBit (153*i)=true:=by
 induction n generalizing i with
 | zero=>omega
 | succ n ih =>
  rw [kT,cf,Nat.testBit_two_pow_mul_add _ (by decide +kernel:1<2^153)]
  cases i with
  | zero=>simp
  | succ i =>
   have di:153*(i+1)-153=153*i:=by omega
   have ge:¬153*(i+1)<153:=by omega
   simp only [ge,ite_false,di];exact ih _ (by omega)
set_option maxRecDepth 8192 in
lemma ur (a:bt):(a.toNat+1).testBit 152=(a==allOnes 152):=by
 by_cases h:a=allOnes 152
 . subst a;decide +kernel
 . have lim:=a.isLt
   have ne:a.toNat≠2^152-1:=by
    intro eq;apply h;apply BitVec.eq_of_toNat_eq;simpa only [BitVec.toNat_allOnes] using eq
   have lt:a.toNat+1<2^152:=by omega
   rw [Nat.testBit_eq_false_of_lt lt];exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 8192 in
lemma ya {α} (f : α->bt) (xs:List α) (i:Nat) (hi:i<xs.length):(g5 (kT xs.length) (aS f xs)).testBit (153*i)=(f xs[i]==allOnes 152):=by
 simp only [g5,testBit_and,Nat.testBit_shiftRight,wM _ _ hi,Bool.and_true]
 induction xs generalizing i with
 | nil=>simp at hi
 | cons a xs ih =>
  simp only [aS,length_cons,kT,cf]
  have sum (u v x:Nat):2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1):=by omega
  rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have:=(f a).isLt;omega)];have hi':i<xs.length+1:=hi
  cases i with
  | zero=>simpa using ur (f a)
  | succ i =>
   have ge:¬153*(i+1)+152<153:=by omega
   have di:153*(i+1)+152-153=153*i+152:=by omega
   simp only [ge,ite_false,di,getElem_cons_succ];apply ih i (by omega)
abbrev fc:=Nat × Nat
abbrev iN:=Nat × Nat × Nat
def dg {α} (s : α->jw) (xs:List α):fc:=(aS (fun x=>(s x).1) xs,aS (fun x=>(s x).2) xs)
def hA {α} (c : α->tU) (xs:List α):iN:=
 (aS (fun x=>(c x).1) xs,aS (fun x=>(c x).2.1) xs,
  aS (fun x=>(c x).2.2) xs)
def ce (d:Bool) (a:fc):=if d then a.1^^^(a.1&&&a.2) else a.1^^^a.2
lemma iM (a b:bt):a^^^(a&&&b)=a &&& ~~~b:=by
 apply eq_of_getLsbD_eq;intro i hi;simp only [BitVec.getLsbD_xor,getLsbD_and,getLsbD_not,hi,decide_true,Bool.true_and]
 cases a.getLsbD i<;>cases b.getLsbD i<;>rfl
section
variable [w : Width]
lemma fN {α} (s : α->jw) (xs:List α) (d:Bool):ce d (dg s xs)=aS (fun x=>bU d (s x)) xs:=by cases d<;>simp only [ce,dg,bU,false_eq_true,ite_false,ite_true,fZ,g8,iM]
end
def eK (op:Nat) (a b:fc):fc:=
 if op=0 then (a.1&&&b.1,a.2&&&b.2) else if op=1 then (a.1|||b.1,a.2|||b.2)
 else if op=2 then (a.1^^^(a.1&&&b.1),a.2^^^(a.2&&&b.2))
 else (b.1^^^(b.1&&&a.1),b.2^^^(b.2&&&a.2))
section
variable [w : Width]
lemma sq {α} (a b : α->aI) (xs:List α) (op:Nat):eK op (dg (fun x=>(a x).2) xs) (dg (fun x=>(b x).2) xs)=dg (fun x=>(fq op (a x) (b x)).2) xs:=by
 by_cases h0:op=0
 . simp only [eK,h0,ite_true,dg,fZ,fq,bv]
 by_cases h1:op=1
 . simp [eK,h1,dg,km,fq,bv]
 by_cases h2:op=2
 . simp [eK,h2,dg,fZ,g8,iM,fq,bv]
 . have e (x y:bt) : ~~~x&&&y=y &&& ~~~x:=BitVec.and_comm _ _;simp only [eK,h0,h1,h2,ite_false,dg,fZ,g8,iM,fq,bv,e]
end
def gp (c:iN) (a b:Nat) (ka kb:Bool):=
 let without1:=fun w=>c.1^^^(c.1&&&(c.2.1&&&w))
 let without2:=c.1^^^(c.1&&&((c.2.1&&&(a|||b))|||(c.2.2&&&(a&&&b))))
 if ka then (if kb then c.1 else without1 b)
 else if kb then without1 a else without2
section
variable [w : Width]
lemma k6 {α} (c : α->tU) (a b : α->bt) (xs:List α) (ka kb:Bool):gp (hA c xs) (aS a xs) (aS b xs) ka kb=aS (fun x=>gh (c x) (a x) (b x) ka kb) xs:=by
 cases ka<;>cases kb <;>
  simp only [gp,hA,fZ,km,g8,iM,gh,e7,hC,
   false_eq_true,ite_false,ite_true]
def az (c:bc) (i:Nat):=c.2.2.1.getD i af
def eU (c:bc) (i j op:Nat) (ka kb:Bool):=
 let a:=az c i
 let b:=az c j
 ec c op a b (fq op a b) ka kb
def iV (c:bc) (d ka kb:Bool) (op i j:Nat):=
 let a:=az c i
 let b:=az c j
 gh c.2.2.2.1.1 (bU d a.2) (bU d b.2) ka kb |||
  bU d (fq op a b).2
end
def iE {α:Type} (f : α->Bool) (mask:Nat):List α->Bool
 | []=>true
 | x::xs=>if mask=0 then true else
  ((mask&&&1==0)||f x)&&iE f (mask>>>153) xs
lemma so {α} (f : α->Bool) (mask:Nat) (xs:List α) (i:Nat) (hi:i<xs.length) (bitOn:mask.testBit (153*i)=true) (ok:iE f mask xs=true):f xs[i]=true:=by
 induction xs generalizing mask i with
 | nil=>simp at hi
 | cons x xs ih =>
  have ne:mask≠0:=by intro e;simp [e] at bitOn
  simp only [iE,ne,ite_false,and_eq_true,or_eq_true,beq_iff_eq] at ok
  cases i with
  | zero =>
   have nonzero:mask&&&1≠0:=by
    intro he;have at0:=congrArg (fun n:Nat=>n.testBit 0) he;simp only [testBit_and] at at0;change mask.testBit 0=true at bitOn;simp [bitOn] at at0
   exact ok.1.resolve_left nonzero
  | succ i =>
   apply ih (mask:=mask>>>153) (i:=i) (by simpa using hi) _ ok.2;simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn
abbrev la:=Nat × Nat × Nat × List fc × iN
section
variable [w : Width]
def cC (k n:Nat) (xs:List bc):la:=
 (k,n,kT xs.length,(List.range n).map (fun i=>dg (fun c=>(az c i).2) xs),
  hA (fun c=>c.2.2.2.1.1) xs)
end
def dY (b:la) (i:Nat):=b.2.2.2.1.getD i (0,0)
section
variable [w : Width]
lemma jg (k n) (xs) {i:Nat} (h:i<n):dY (cC k n xs) i=dg (fun c=>(az c i).2) xs:=by simp [dY,cC,getD_eq_getElem?_getD,getElem?_map,List.getElem?_range,h]
lemma nq (d x:aQ):cl d (eh x)=d^^^cl d x:=by
 apply dA;intro r;simp only [cl,eh,aV,getLsbD_and,getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
 cases d.getLsbD r.val<;>cases x.getLsbD r.val<;>rfl
def bi (p:aI->Bool) (a:aI) (keep:Bool):=if keep then 0 else (p a).toNat
lemma lN (p:aI->Bool) (ws:List aI) (a:aI) (keep:Bool):ws.countP p ≤ (eO ws a keep).countP p+bi p a keep:=by
 cases keep
 . simp only [eO,false_eq_true,ite_false,bi,List.countP_erase]
   split
   next h=>simp [h.2];omega
   next=>omega
 . simp [eO,bi]
lemma sf (p:aI->Bool) (ws:List aI) (a b:aI) (ka kb:Bool):ws.countP p-bi p a ka-bi p b kb ≤ (cO ws a b ka kb).countP p:=by
 have h1:=lN p ws a ka;have h2:=lN p (eO ws a ka) b kb;simp only [cO];omega
end
def gK {β:Type} (n:Nat) (f:Nat -> β) : β:=Nat.rec (f 0) (fun k _=>f (Nat.succ k)) n
lemma gL {β:Type} (n:Nat) (f:Nat -> β):gK n f=f n:=by cases n<;>rfl
def mX {α β:Type} (f : α->Nat) (l:List α):(List Nat -> β) -> β:=List.rec (fun k=>k []) (fun a _ ih k=>gK (f a) fun x=>ih fun xs=>k (x::xs)) l
lemma yO {α β:Type} (f : α->Nat) (l:List α) (k:List Nat -> β):mX f l k=k (l.map f):=by
 induction l generalizing k with
 | nil=>rfl
 | cons a l ih =>
  change gK (f a) (fun x=>mX f l fun xs=>k (x::xs))=_;rw [gL,ih];rfl
section
variable [w : Width]
def aU (d:Nat) (a:aQ):Nat:=land a.toNat d
end
def gC (m:Nat) (l:List Nat):Bool:=List.rec false (fun v _ ih=>or (Nat.beq m v) ih) l
def eg (d m:Nat):Bool:=or (Nat.beq m 0) (Nat.beq m d)
def dF (u:Bool) (d:Nat) (pm:List Nat) (m:Nat):Bool:=or (or (eg d m) (gC m pm)) (and u (gC (xor d m) pm))
section
variable [w : Width]
lemma f0 (d a:aQ):aU d.toNat a=(cl d a).toNat:=(toNat_and _ _).symm
lemma iR (a b:aQ):Nat.beq a.toNat b.toNat=(a==b):=by
 rw [Bool.eq_iff_iff,beq_eq,beq_iff_eq];exact toNat_inj
lemma i6 (d a:aQ):eg d.toNat (aU d.toNat a)=ay d a:=by
 rw [f0]
 have e:Nat.beq (cl d a).toNat 0=(cl d a==zero):=by
  have z0:zero.toNat=0:=by simp [zero]
  rw [<-iR,z0]
 rw [eg,e,iR];rfl
lemma mN (x d:aQ) (pool:List aQ):gC x.toNat (pool.map (aU d.toNat))=(pool.map (cl d)).any (fun v=>v==x):=by
 induction pool with
 | nil=>rfl
 | cons a l ih =>
  change or (Nat.beq x.toNat (aU d.toNat a)) (gC x.toNat (l.map (aU d.toNat)))=_;rw [ih,f0,iR,map_cons,List.any_cons,Bool.beq_comm]
lemma lR (u:Bool) (d a:aQ) (pool:List aQ):dF u d.toNat (pool.map (aU d.toNat)) (aU d.toNat a)=bd u d pool a:=by
 have x:xor d.toNat (cl d a).toNat=(cl d (eh a)).toNat:=by
  rw [nq];exact (BitVec.toNat_xor _ _).symm
 rw [dF,i6,f0,x,mN,mN];simp only [bd,ay]
def k7 (u:Bool) (p:bu) (w:aI):Nat:=cond (bd u p.d p.wires w.1) 0 1
def eN (u:Bool) (p:bu) (ws:List aI) (k:Nat) (a b:aI) (op:Nat) (ka kb:Bool):Bool:=
 let const:=fun w:aI=>ay p.d w.1
 let z:=bM op a.1 b.1
 let cm:=ws.countP const-bi const a ka-bi const b kb+(ay p.d z).toNat
 (((ws.map (k7 u p)).sum==cond ka 0 (k7 u p a)+cond kb 0 (k7 u p b)) &&
  decide (k+p.p+(!bd u p.d p.wires z).toNat<p.b+cm)) &&
  (bd u p.d p.wires z||(bd u p.d p.wires a.1&&bd u p.d p.wires b.1))
end
def zN (op x y:Nat):Nat:=cond (Nat.beq op 0) (land x y) (cond (Nat.beq op 1) (lor x y)
 (cond (Nat.beq op 2) (xor x (land x y)) (xor y (land x y))))
section
variable [w : Width]
lemma yV (op:Nat) (d a b:aQ):zN op (aU d.toNat a) (aU d.toNat b)=aU d.toNat (bM op a b):=by
 have tn (x y:aQ):land x.toNat y.toNat=(x&&&y).toNat:=(toNat_and x y).symm;have tx (x y:aQ):xor x.toNat y.toNat=(x^^^y).toNat:=(BitVec.toNat_xor x y).symm;have tor (x y:aQ):lor x.toNat y.toNat=(x|||y).toNat:=(toNat_or x y).symm;simp only [f0];unfold zN
 by_cases h0:op=0
 . subst h0;change land _ _=_;rw [tn]
   congr 1
   apply dA;intro r;simp only [cl,bM,aV,ite_true,getLsbD_and]
   cases a.getLsbD r.val<;>cases b.getLsbD r.val<;>cases d.getLsbD r.val<;>rfl
 by_cases h1:op=1
 . subst h1;change lor _ _=_;rw [tor]
   congr 1
   apply dA;intro r;simp only [cl,bM,aV,Nat.one_ne_zero,ite_true,ite_false,getLsbD_and,getLsbD_or]
   cases a.getLsbD r.val<;>cases b.getLsbD r.val<;>cases d.getLsbD r.val<;>rfl
 have e0:Nat.beq op 0=false:=Bool.eq_false_iff.mpr (fun h=>h0 (Nat.eq_of_beq_eq_true h));have e1:Nat.beq op 1=false:=Bool.eq_false_iff.mpr (fun h=>h1 (Nat.eq_of_beq_eq_true h))
 by_cases h2:op=2
 . subst h2;change xor _ (land _ _)=_;rw [tn,tx]
   congr 1
   apply dA;intro r;simp only [cl,bM,aV,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,getLsbD_and,BitVec.getLsbD_xor,getLsbD_not,r.isLt,decide_true,Bool.true_and]
   cases a.getLsbD r.val<;>cases b.getLsbD r.val<;>cases d.getLsbD r.val<;>rfl
 have e2:Nat.beq op 2=false:=Bool.eq_false_iff.mpr (fun h=>h2 (Nat.eq_of_beq_eq_true h));rw [e0,e1,e2];change xor _ (land _ _)=_;rw [tn,tx]
 congr 1
 apply dA;intro r;simp only [cl,bM,aV,h0,h1,h2,ite_false,getLsbD_and,BitVec.getLsbD_xor,getLsbD_not,r.isLt,decide_true,Bool.true_and]
 cases a.getLsbD r.val<;>cases b.getLsbD r.val<;>cases d.getLsbD r.val<;>rfl
end
def kz (d x:Nat) (keep:Bool):Nat:=cond keep 0 (cond (eg d x) 1 0)
section
variable [w : Width]
lemma kA (d:aQ) (a:aI) (keep:Bool):kz d.toNat (aU d.toNat a.1) keep=bi (fun w:aI=>ay d w.1) a keep:=by
 rw [kz,i6,bi]
 cases keep
 . cases ay d a.1<;>rfl
 . rfl
end
def bf:Nat->Nat
 | 0=>1|1=>2|2=>4|3=>8|4=>16|5=>32|6=>64|7=>128
 | 8=>256|9=>512|10=>1024|11=>2048|12=>4096|13=>8192|14=>16384|15=>32768
 | n=>1<<<n
lemma dy (n:Nat):bf n=2 ^ n:=by
 match n with
 | 0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15=>rfl
 | n+16=>simp [bf,Nat.shiftLeft_eq]
def df (f:Nat->Bool):List Nat->Nat
 | []=>0
 | x::xs=>(if f x then 1 else 0)|||(df f xs<<<1)
lemma ey (f:Nat->Bool) (l:List Nat) (i:Nat):(df f l).testBit i=(if i<l.length then f (l.getD i 0) else false):=by
 induction l generalizing i with
 | nil=>simp [df]
 | cons x xs ih =>
  cases i with
  | zero =>
   simp only [df,testBit_or,Nat.testBit_shiftLeft,length_cons,Nat.zero_lt_succ,ite_true,List.getD_cons_zero]
   cases f x<;>simp
  | succ i =>
   have h0:(if f x then 1 else 0).testBit (i+1)=false:=by cases f x<;>simp [testBit_succ]
   simp only [df,testBit_or,Nat.testBit_shiftLeft,length_cons,Nat.succ_lt_succ_iff,List.getD_cons_succ,ge_iff_le,Nat.le_add_left,Nat.add_sub_cancel,decide_true,Bool.true_and,h0,Bool.false_or,ih]
lemma ei (m i:Nat):Nat.beq (land m (bf i)) 0 = !(m.testBit i):=by
 rw [dy];change Nat.beq (m&&&2 ^ i) 0 = !(m.testBit i)
 cases hb:m.testBit i
 . simp only [Bool.not_false,beq_eq];apply eq_of_testBit_eq;intro k;simp only [testBit_and,testBit_two_pow,Nat.zero_testBit]
   by_cases hk:i=k
   . subst hk;simp [hb]
   . simp [hk]
 . simp only [Bool.not_true,Bool.eq_false_iff,ne_eq,beq_eq];intro h;have h1:=congrArg (fun n=>n.testBit i) h;simp [testBit_and,testBit_two_pow,hb] at h1
lemma dj {i j k:Nat} (hne:i≠j):(2 ^ i+2 ^ j).testBit k=(decide (k=i)||decide (k=j)):=by
 induction k generalizing i j with
 | zero =>
  cases i with
  | zero =>
   cases j with
   | zero=>exact absurd rfl hne
   | succ j =>
    have hm:(2 ^ 0+2 ^ (j+1)) % 2=1:=by simp only [pow_zero,pow_succ];omega
    rw [Nat.testBit_zero,hm];rfl
  | succ i =>
   cases j with
   | zero =>
    have hm:(2 ^ (i+1)+2 ^ 0) % 2=1:=by simp only [pow_zero,pow_succ];omega
    rw [Nat.testBit_zero,hm];rfl
   | succ j =>
    have hm:(2 ^ (i+1)+2 ^ (j+1)) % 2=0:=by simp only [pow_succ];omega
    rw [Nat.testBit_zero,hm];rfl
 | succ k ih =>
  cases i with
  | zero =>
   cases j with
   | zero=>exact absurd rfl hne
   | succ j =>
    have hd:(2 ^ 0+2 ^ (j+1))/2=2 ^ j:=by simp only [pow_zero,pow_succ];omega
    rw [testBit_succ,hd,testBit_two_pow];simp [eq_comm]
  | succ i =>
   cases j with
   | zero =>
    have hd:(2 ^ (i+1)+2 ^ 0)/2=2 ^ i:=by simp only [pow_zero,pow_succ];omega
    rw [testBit_succ,hd,testBit_two_pow];simp [eq_comm]
   | succ j =>
    have hd:(2 ^ (i+1)+2 ^ (j+1))/2=2 ^ i+2 ^ j:=by simp only [pow_succ];omega
    rw [testBit_succ,hd,ih (fun e=>hne (congrArg Nat.succ e))];simp
lemma gX {α:Type} (f : α->Nat) {l:List α} {i j:Nat} (hi:i<l.length) (hj:j<l.length) (hne:i≠j):f (l[i])+f (l[j]) ≤ (l.map f).sum:=by
 induction l generalizing i j with
 | nil=>simp at hi
 | cons x xs ih =>
  cases i with
  | zero =>
   cases j with
   | zero=>exact absurd rfl hne
   | succ j =>
    simp only [List.getElem_cons_zero,getElem_cons_succ,map_cons,sum_cons];have hjb:j<xs.length:=Nat.lt_of_succ_lt_succ hj;have hle:f (xs[j]'hjb) ≤ (xs.map f).sum:=List.le_sum_of_mem (mem_map_of_mem (getElem_mem hjb));omega
  | succ i =>
   cases j with
   | zero =>
    simp only [List.getElem_cons_zero,getElem_cons_succ,map_cons,sum_cons];have hib:i<xs.length:=Nat.lt_of_succ_lt_succ hi;have hle:f (xs[i]'hib) ≤ (xs.map f).sum:=List.le_sum_of_mem (mem_map_of_mem (getElem_mem hib));omega
   | succ j =>
    simp only [getElem_cons_succ,map_cons,sum_cons];have h:=ih (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj) (fun e=>hne (congrArg Nat.succ e));omega
lemma kD {α:Type} (f : α->Nat) {l:List α} {i:Nat} (hi:i<l.length):f (l[i]) ≤ (l.map f).sum:=List.le_sum_of_mem (mem_map_of_mem (getElem_mem hi))
def g3 (bm v:Nat):Nat:=lor bm (shiftLeft 1 (Nat.mod v 251))
def o9 (u:Bool) (d:Nat) (pw:List Nat):Nat:=
 let b0:=g3 (g3 0 0) d
 pw.foldl (fun acc v=>let a1:=g3 acc v;if u then g3 a1 (xor d v) else a1) b0
def dz (d:Nat):List Nat->Nat × Nat
 | []=>(0,0)
 | m::ms =>
  let r:=dz d ms
  cond (eg d m) (Nat.succ r.1,lor 1 (shiftLeft r.2 1)) (r.1,shiftLeft r.2 1)
lemma mw (d:Nat) (ms:List Nat):dz d ms=(ms.countP (eg d),df (eg d) ms):=by
 induction ms with
 | nil=>rfl
 | cons m ms ih =>
  simp only [dz,ih,countP_cons,df]
  cases eg d m
  . simp only [cond_false,false_eq_true,ite_false,Nat.add_zero];exact Prod.ext rfl (by change _=0|||_;rw [Nat.zero_or];rfl)
  . rfl
def dI (u:Bool) (d:Nat) (pm:List Nat):Nat->List Nat->Nat × Nat
 | _,[]=>(0,0)
 | cap,m::ms =>
  if dF u d pm m then
   let r:=dI u d pm cap ms;(r.1,shiftLeft r.2 1)
  else match cap with
   | 0=>(3,0)
   | cap'+1=>let r:=dI u d pm cap' ms;(Nat.succ r.1,lor 1 (shiftLeft r.2 1))
lemma nG (u:Bool) (d:Nat) (pm:List Nat) (ms:List Nat):∀ cap,(dI u d pm cap ms).1 ≤ cap ->dI u d pm cap ms=((ms.map fun m=>cond (dF u d pm m) 0 1).sum,df (fun m => !dF u d pm m) ms):=by
 induction ms with
 | nil=>intro _ _;rfl
 | cons m ms ih =>
  intro cap hle;simp only [dI] at hle ⊢
  cases hv:dF u d pm m
  . simp only [hv,false_eq_true,ite_false] at hle ⊢
    cases cap with
    | zero=>simp at hle
    | succ cap' =>
     simp only [Nat.succ_le_succ_iff] at hle;have r:=ih cap' hle;simp only [r,map_cons,sum_cons,df,hv,cond_false,Bool.not_false,ite_true];exact Prod.ext (by omega) rfl
  . simp only [hv,ite_true] at hle ⊢;have r:=ih cap hle;simp only [r,map_cons,sum_cons,df,hv,cond_true,Bool.not_true,false_eq_true,ite_false,Nat.zero_add];exact Prod.ext rfl (by change _=0|||_;rw [Nat.zero_or];rfl)
structure QS where
 um:Nat
 cm:Nat
 bhi:Nat
 lo:Nat
 d:Nat
 pw:List Nat
 bm:Nat
 u:Bool
def Bu (v:Nat):Nat:=
 let n:=v % 2305843009213693951
 (n*(n+971)) % 2305843009213693951
def iT (s:QS) (zFull loss:Nat) (bothAv:Bool):Bool:=
 let hi:=Nat.sub s.bhi loss
 cond (ble (Nat.succ s.lo) hi)
  (cond (and bothAv (ble (Nat.add s.lo 2) hi)) true (dF s.u s.d s.pw (land zFull s.d)))
  (cond (ble s.lo hi) (eg s.d (land zFull s.d)) false)
def im (s:QS) (zFull loss:Nat):Bool:=
 let hi:=Nat.sub s.bhi loss
 cond (ble (Nat.succ s.lo) hi)
  (cond (ble (Nat.add s.lo 2) hi) true
   (let z:=land zFull s.d
    cond (Nat.beq (land (Nat.shiftRight s.bm (Nat.mod z 251)) 1) 0) false (dF s.u s.d s.pw z)))
  (cond (ble s.lo hi) (eg s.d (land zFull s.d)) false)
lemma hR (s:QS) (zFull loss:Nat) (h:im s zFull loss=true):iT s zFull loss true=true:=by
 unfold im at h;unfold iT;dsimp only at h ⊢
 cases h1:ble (Nat.succ s.lo) (Nat.sub s.bhi loss)
 . rw [h1] at h;exact h
 . rw [h1] at h;simp only [cond_true,Bool.true_and] at h ⊢
   cases h2:ble (Nat.add s.lo 2) (Nat.sub s.bhi loss)
   . rw [h2] at h;simp only [cond_false] at h ⊢
     cases hb:Nat.beq (land (Nat.shiftRight s.bm (Nat.mod (land zFull s.d) 251)) 1) 0
     . rw [hb] at h;exact h
     . rw [hb] at h;exact noConfusion h
   . rfl
def gO (cm p2i p2j dropBits:Nat) (ka kb:Bool):Nat:=
 cond (Nat.beq (land cm dropBits) 0) 0
  (Nat.add (cond ka 0 (cond (Nat.beq (land cm p2i) 0) 0 1))
   (cond kb 0 (cond (Nat.beq (land cm p2j) 0) 0 1)))
lemma sk (cm i j:Nat) (hne:i≠j) (ka kb:Bool):gO cm (bf i) (bf j) (Nat.add (cond ka 0 (bf i)) (cond kb 0 (bf j))) ka kb=Nat.add (cond ka 0 (cond (cm.testBit i) 1 0)) (cond kb 0 (cond (cm.testBit j) 1 0)):=by
 unfold gO;rw [ei,ei]
 have hflip (b:Bool):cond (!b) 0 1=cond b 1 0:=by cases b<;>rfl
 rw [hflip,hflip]
 cases h0:Nat.beq (land cm (Nat.add (cond ka 0 (bf i)) (cond kb 0 (bf j)))) 0
 . rfl
 . simp only [cond_true];have hl:=beq_eq.mp h0
   have hbit (t:Nat) (ht:(Nat.add (cond ka 0 (bf i)) (cond kb 0 (bf j))).testBit t=true):
    cm.testBit t=false:=by
    have h1:=congrArg (fun n=>n.testBit t) hl;change (cm&&&Nat.add (cond ka 0 (bf i)) (cond kb 0 (bf j))).testBit t=(0:Nat).testBit t at h1;simp only [testBit_and,ht,Bool.and_true,Nat.zero_testBit] at h1;exact h1
   cases ka<;>cases kb
   . have hi:cm.testBit i=false:=hbit i (by simp [dy,dj hne]);have hj:cm.testBit j=false:=hbit j (by simp [dy,dj hne]);simp [hi,hj]
   . have hi:cm.testBit i=false:=hbit i (by simp [dy,testBit_two_pow]);simp [hi]
   . have hj:cm.testBit j=false:=hbit j (by simp [dy,testBit_two_pow]);simp [hj]
   . rfl
lemma f2 {α:Type} (f : α->Bool) (l:List α):List.rec false (fun s _ ih=>or (f s) ih) l=true ↔ ∃ s ∈ l,f s=true:=by
 induction l with
 | nil=>simp
 | cons x xs ih =>
  change or (f x) (List.rec false (fun s _ ih=>or (f s) ih) xs)=true ↔ _;rw [or_eq_true,ih];simp
def rL (ps:List QS) (zFull:Nat):Bool:=List.rec false (fun s _ ih=>or (im s zFull 0) ih) ps
def il (ps:List QS) (zFull p2i p2j dropBits:Nat) (ka kb:Bool):Bool:=List.rec false (fun s _ ih=>or (im s zFull (gO s.cm p2i p2j dropBits ka kb)) ih) ps
def jy (ps:List QS) (zFull p2i p2j dropBits:Nat) (ka kb:Bool):Bool:=List.rec false (fun s _ ih=>or (cond (Nat.beq (land s.um dropBits) s.um) (iT s zFull (gO s.cm p2i p2j dropBits ka kb) false) false) ih) ps
def q9 (ps:List QS) (zFull p2i p2j pairBits:Nat):Bool:=List.rec false (fun s _ ih=>or (cond (Nat.beq s.um pairBits) (iT s zFull (gO s.cm p2i p2j pairBits false false) false) false) ih) ps
section
variable [w : Width]
def eE (u:Bool) (k:Nat) (ws:List aI) (p:bu) (target:Nat) (q:QS):Prop:=
 let d:=p.d.toNat
 let ms:=ws.map (fun w:aI=>aU d w.1)
 let pm:=p.wires.map (aU d)
 let av:=dF u d pm
 q.um=df (fun m => !av m) ms /\
 q.cm=df (eg d) ms /\
 q.bhi=Nat.add p.b (ms.countP (eg d)) /\
 q.lo=Nat.add k p.p /\
 q.d=d/\q.pw=pm/\q.u=u /\
 (ms.map fun m=>cond (av m) 0 1).sum=target
def bz (u:Bool) (k:Nat) (ws:List aI):List bu->List QS × List QS × List QS × List QS
 | []=>([],[],[],[])
 | p::ps =>
  let b:=bz u k ws ps
  let lo:=Nat.add k p.p
  let d:=p.d.toNat
  let ms:=ws.map (fun w:aI=>aU d w.1)
  let cc:=dz d ms
  let bhi:=Nat.add p.b cc.1
  if ble lo bhi then
   let pm:=p.wires.map (aU d)
   let uu:=dI u d pm 2 ms
   if Nat.beq uu.1 0 then
    let bm:=if ble (Nat.succ lo) bhi then o9 u d pm else 0
    let q:QS:=⟨uu.2,cc.2,bhi,lo,d,pm,bm,u⟩
    if ble (Nat.add lo 2) bhi then (q::b.1,b.2.1,b.2.2.1,b.2.2.2)
    else (b.1,q::b.2.1,b.2.2.1,b.2.2.2)
   else if Nat.beq uu.1 1 then (b.1,b.2.1,⟨uu.2,cc.2,bhi,lo,d,pm,0,u⟩::b.2.2.1,b.2.2.2)
   else if Nat.beq uu.1 2 then (b.1,b.2.1,b.2.2.1,⟨uu.2,cc.2,bhi,lo,d,pm,0,u⟩::b.2.2.2)
   else b
  else b
lemma el (u:Bool) (k:Nat) (ws:List aI) (ps:List bu):let b:=bz u k ws ps
 (∀ q ∈ b.1 ++ b.2.1,∃ p ∈ ps,eE u k ws p 0 q) /\
 (∀ q ∈ b.2.2.1,∃ p ∈ ps,eE u k ws p 1 q) /\
 (∀ q ∈ b.2.2.2,∃ p ∈ ps,eE u k ws p 2 q):=by
 induction ps with
 | nil=>simp [bz]
 | cons p ps ih =>
  obtain ⟨ih0,ih1,ih2⟩:=ih
  have lift0:∀ q ∈ (bz u k ws ps).1 ++ (bz u k ws ps).2.1,∃ p' ∈ p::ps,eE u k ws p' 0 q:=
   fun q hq=>let ⟨p',hp',hs⟩:=ih0 q hq;⟨p',mem_cons_of_mem _ hp',hs⟩
  have lift1:∀ q ∈ (bz u k ws ps).2.2.1,∃ p' ∈ p::ps,eE u k ws p' 1 q:=
   fun q hq=>let ⟨p',hp',hs⟩:=ih1 q hq;⟨p',mem_cons_of_mem _ hp',hs⟩
  have lift2:∀ q ∈ (bz u k ws ps).2.2.2,∃ p' ∈ p::ps,eE u k ws p' 2 q:=
   fun q hq=>let ⟨p',hp',hs⟩:=ih2 q hq;⟨p',mem_cons_of_mem _ hp',hs⟩
  simp only [bz]
  have hcc:=mw p.d.toNat (ws.map fun w:aI=>aU p.d.toNat w.1)
  have hcc1:(dz p.d.toNat (ws.map fun w:aI=>aU p.d.toNat w.1)).1 =
   (ws.map fun w:aI=>aU p.d.toNat w.1).countP (eg p.d.toNat):=congrArg Prod.fst hcc
  have hcc2:(dz p.d.toNat (ws.map fun w:aI=>aU p.d.toNat w.1)).2 =
   df (eg p.d.toNat) (ws.map fun w:aI=>aU p.d.toNat w.1):=congrArg Prod.snd hcc
  have mkS (t:Nat) (ht:t ≤ 2) (bm:Nat)
   (heq:(dI u p.d.toNat (p.wires.map (aU p.d.toNat)) 2 (ws.map fun w:aI=>aU p.d.toNat w.1)).1=t):
   eE u k ws p t ⟨(dI u p.d.toNat (p.wires.map (aU p.d.toNat)) 2 (ws.map fun w:aI=>aU p.d.toNat w.1)).2,
    (dz p.d.toNat (ws.map fun w:aI=>aU p.d.toNat w.1)).2,
    Nat.add p.b (dz p.d.toNat (ws.map fun w:aI=>aU p.d.toNat w.1)).1,
    Nat.add k p.p,p.d.toNat,p.wires.map (aU p.d.toNat),bm,u⟩:=by
   have hu:=nG u p.d.toNat (p.wires.map (aU p.d.toNat)) (ws.map fun w:aI=>aU p.d.toNat w.1) 2 (by omega)
   exact ⟨congrArg Prod.snd hu,hcc2,congrArg (Nat.add p.b) hcc1,rfl,rfl,rfl,rfl,(congrArg Prod.fst hu).symm.trans heq⟩
  by_cases hlo:ble (Nat.add k p.p) (Nat.add p.b (dz p.d.toNat (ws.map fun w:aI=>aU p.d.toNat w.1)).1)=true
  . simp only [hlo,ite_true]
    by_cases hu0:Nat.beq (dI u p.d.toNat (p.wires.map (aU p.d.toNat)) 2 (ws.map fun w:aI=>aU p.d.toNat w.1)).1 0=true
    . simp only [hu0,ite_true]
      have hs (bm:Nat):=mkS 0 (by decide) bm (beq_eq.mp hu0)
      by_cases hhi:ble (Nat.add (Nat.add k p.p) 2) (Nat.add p.b (dz p.d.toNat (ws.map fun w:aI=>aU p.d.toNat w.1)).1)=true
      . simp only [hhi,ite_true]
        refine ⟨fun q hq => ?_,lift1,lift2⟩
        rcases mem_cons.mp hq with rfl|hq
        . exact ⟨p,mem_cons_self,hs _⟩
        . exact lift0 q hq
      . simp only [hhi,ite_false]
        refine ⟨fun q hq => ?_,lift1,lift2⟩
        rcases mem_append.mp hq with hq|hq
        . exact lift0 q (List.mem_append_left _ hq)
        . rcases mem_cons.mp hq with rfl|hq
          . exact ⟨p,mem_cons_self,hs _⟩
          . exact lift0 q (List.mem_append_right _ hq)
    . simp only [hu0,ite_false]
      by_cases hu1:Nat.beq (dI u p.d.toNat (p.wires.map (aU p.d.toNat)) 2 (ws.map fun w:aI=>aU p.d.toNat w.1)).1 1=true
      . simp only [hu1,ite_true]
        have hs:=mkS 1 (by decide) 0 (beq_eq.mp hu1)
        refine ⟨lift0,fun q hq => ?_,lift2⟩
        rcases mem_cons.mp hq with rfl|hq
        . exact ⟨p,mem_cons_self,hs⟩
        . exact lift1 q hq
      . simp only [hu1,ite_false]
        by_cases hu2:Nat.beq (dI u p.d.toNat (p.wires.map (aU p.d.toNat)) 2 (ws.map fun w:aI=>aU p.d.toNat w.1)).1 2=true
        . simp only [hu2,ite_true]
          have hs:=mkS 2 (by decide) 0 (beq_eq.mp hu2)
          refine ⟨lift0,lift1,fun q hq => ?_⟩
          rcases mem_cons.mp hq with rfl|hq
          . exact ⟨p,mem_cons_self,hs⟩
          . exact lift2 q hq
        . simp only [hu2,ite_false];exact ⟨lift0,lift1,lift2⟩
  . simp only [hlo,ite_false];exact ⟨lift0,lift1,lift2⟩
structure l3 where
 ctx:bc
 n:Nat
 ops:Nat
 p0:List QS
 p1:List QS
 p2:List QS
 ws:List Nat
 tag:Nat
def dE (c:bc):l3:=
 let ws:=c.2.2.1.map (fun w:aI=>w.1.toNat)
 let b:=bz c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1
 ⟨c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,b.1 ++ b.2.1,b.2.2.1,b.2.2.2,ws,(ws.map Bu).sum⟩
def jS {β:Type} (cs:List bc) (f:List l3 -> β) : β:=f (cs.map dE)
lemma hI {β:Type} (cs) (f:List l3 -> β):jS cs f=f (cs.map dE):=rfl
lemma kQ {d:Nat} (ws:List aI) (i:Nat) (hd:aU d zero=0):(ws.map (fun w:aI=>aU d w.1)).getD i 0=aU d (ws.getD i af).1:=by
 simp only [getD_eq_getElem?_getD,getElem?_map]
 cases ws[i]? with
 | none=>exact hd.symm
 | some v=>rfl
lemma gF {u k p ws i j op ka kb bothAv target} {q:QS} (hs:eE u k ws p target q) (hi:i<ws.length) (hj:j<ws.length) (hne:i≠j) (hu:target=Nat.add (cond ka 0 (cond (dF u p.d.toNat (p.wires.map (aU p.d.toNat)) (aU p.d.toNat (ws.getD i af).1)) 0 1)) (cond kb 0 (cond (dF u p.d.toNat (p.wires.map (aU p.d.toNat)) (aU p.d.toNat (ws.getD j af).1)) 0 1))) (hb:bothAv=true->dF u p.d.toNat (p.wires.map (aU p.d.toNat)) (aU p.d.toNat (ws.getD i af).1)=true/\dF u p.d.toNat (p.wires.map (aU p.d.toNat)) (aU p.d.toNat (ws.getD j af).1)=true) (h:iT q (zN op (ws.getD i af).1.toNat (ws.getD j af).1.toNat) (gO q.cm (bf i) (bf j) (Nat.add (cond ka 0 (bf i)) (cond kb 0 (bf j))) ka kb) bothAv=true):eN u p ws k (ws.getD i af) (ws.getD j af) op ka kb=true:=by
 obtain ⟨_,hcm,hbhi,hlo,hd,hpw,hqu,hsum⟩:=hs
 have z0:aU p.d.toNat zero=0:=by simp [aU,zero]
 have su:(((ws.map (fun w:aI=>aU p.d.toNat w.1)).map fun m=>cond (dF u p.d.toNat (p.wires.map (aU p.d.toNat)) m) 0 1).sum) =
  (ws.map (k7 u p)).sum:=by
  rw [map_map];refine congrArg List.sum (List.map_congr_left fun w _ => ?_);change cond (dF u p.d.toNat (p.wires.map (aU p.d.toNat)) (aU p.d.toNat w.1)) 0 1=_;rw [lR];rfl
 have hloss:gO q.cm (bf i) (bf j) (Nat.add (cond ka 0 (bf i)) (cond kb 0 (bf j))) ka kb =
  kz p.d.toNat (aU p.d.toNat (ws.getD i af).1) ka +
  kz p.d.toNat (aU p.d.toNat (ws.getD j af).1) kb:=by
  rw [sk _ _ _ hne,hcm];simp only [ey,length_map,hi,hj,ite_true,kQ _ _ z0,kz,add_eq]
 have hle_cnt:kz p.d.toNat (aU p.d.toNat (ws.getD i af).1) ka +
  kz p.d.toNat (aU p.d.toNat (ws.getD j af).1) kb ≤
  ws.countP (fun w=>ay p.d w.1):=by
  have hcnt:∀ l:List aI,l.countP (fun w=>ay p.d w.1)=(l.map (fun w:aI=>cond (ay p.d w.1) 1 0)).sum:=by
   intro l;induction l with
   | nil=>rfl
   | cons x xs ih=>simp only [countP_cons,map_cons,sum_cons,ih];cases ay p.d x.1<;>simp<;>omega
  rw [hcnt ws,kA,kA];have h1:=gX (fun w:aI=>cond (ay p.d w.1) 1 0) hi hj hne
  have gi:ws.getD i af=ws[i]:=by simp [getD_eq_getElem?_getD,hi]
  have gj:ws.getD j af=ws[j]:=by simp [getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  cases hmi:ay p.d ws[i].1<;>cases hmj:ay p.d ws[j].1<;>cases ka<;>cases kb <;>
   simp only [hmi,hmj,bi,cond_true,cond_false,ite_true,ite_false,false_eq_true,Bool.and_true,Bool.and_false,Bool.toNat_true,Bool.toNat_false] at h1 ⊢<;>omega
 have hzmask:land (zN op (ws.getD i af).1.toNat (ws.getD j af).1.toNat) p.d.toNat =
  aU p.d.toNat (bM op (ws.getD i af).1 (ws.getD j af).1):=by
  have e (v:aQ):aU one.toNat v=v.toNat:=by rw [f0];congr 1;exact and_allOnes
  have h1:=yV op one (ws.getD i af).1 (ws.getD j af).1;rw [e,e,e] at h1;rw [h1];rfl
 rw [hloss] at h;unfold iT at h;rw [hbhi,hlo,hd,hpw,hqu,hzmask] at h;rw [<- hsum,su] at hu;simp only [List.countP_map,Function.comp_def,i6,lR,kA,add_eq,Nat.sub_eq,Nat.succ_eq_add_one] at h hu hb hle_cnt
 have hsub:p.b+ws.countP (fun w=>ay p.d w.1) -
  (bi (fun w=>ay p.d w.1) (ws.getD i af) ka +
   bi (fun w=>ay p.d w.1) (ws.getD j af) kb) =
  p.b+(ws.countP (fun w=>ay p.d w.1) -
   bi (fun w=>ay p.d w.1) (ws.getD i af) ka -
   bi (fun w=>ay p.d w.1) (ws.getD j af) kb):=by omega
 rw [hsub] at h;have hu':(ws.map (k7 u p)).sum=cond ka 0 (k7 u p (ws.getD i af))+cond kb 0 (k7 u p (ws.getD j af)):=hu
 have ca:ay p.d (bM op (ws.getD i af).1 (ws.getD j af).1)=true  ->
  bd u p.d p.wires (bM op (ws.getD i af).1 (ws.getD j af).1)=true:=by
  intro zc;simp only [bd,ay,or_eq_true] at zc ⊢;exact Or.inl (Or.inl zc)
 simp only [eN,and_eq_true,beq_iff_eq,decide_eq_true_eq]
 refine ⟨⟨hu',?_⟩,?_⟩
 all_goals
  generalize ws.countP (fun w=>ay p.d w.1)-bi (fun w:aI=>ay p.d w.1) (ws.getD i af) ka -
   bi (fun w:aI=>ay p.d w.1) (ws.getD j af) kb=c at h ⊢
  generalize ay p.d (bM op (ws.getD i af).1 (ws.getD j af).1)=r at h ca ⊢;generalize bd u p.d p.wires (bM op (ws.getD i af).1 (ws.getD j af).1)=qv at h ca ⊢
  cases h1:ble (k+p.p+1) (p.b+c)
  . rw [h1] at h
    cases h2:ble (k+p.p) (p.b+c)
    . simp [h2] at h
    . have l2:=ble_eq.mp h2;simp only [h2,cond_true,cond_false] at h;subst h;rw [ca rfl];simp<;>omega
  . rw [h1] at h;have l1:=ble_eq.mp h1;simp only [cond_true] at h
    cases hba:bothAv&&ble (k+p.p+2) (p.b+c)
    . rw [hba,cond_false] at h;subst h;simp<;>omega
    . simp only [and_eq_true,ble_eq] at hba;obtain ⟨ha,hb'⟩:=hb hba.1
      first
      | (have:(!qv).toNat ≤ 1:=Bool.toNat_le _;omega)
      | (rw [ha,hb'];simp)
end
lemma lc (m:Nat) (l:List Nat):gC m l=true ↔ m ∈ l:=by
 induction l with
 | nil=>simp [gC]
 | cons a l ih =>
  change or (Nat.beq m a) (gC m l)=true ↔ _;rw [or_eq_true,ih,beq_eq,mem_cons]
section
variable [w : Width]
def ko (fl:Nat->Option (List Nat)) (l:l3) (x y z:Nat) (ka kb:Bool):Bool:=
 Option.rec false (fun ys =>
  and (gC z ys) (and (l.ws.all fun v=>or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (gC v ys)))
   (ys.all fun v=>or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (gC v l.ws)))))
  (fl (Nat.add (Bu z) (Nat.sub (Nat.sub l.tag (cond ka 0 (Bu x))) (cond kb 0 (Bu y)))))
lemma oW (xs:List aQ):jW xs=(xs.map ef).sum:=by
 have go (a:Nat):xs.foldl (fun v x=>v+ef x) a=a+(xs.map ef).sum:=by
  induction xs generalizing a with
  | nil=>rfl
  | cons x xs ih=>rw [foldl_cons,ih,map_cons,sum_cons,Nat.add_assoc]
 exact (go 0).trans (Nat.zero_add _)
lemma jN (f:aI->Nat) {ws:List aI} {a b:aI} (ha:a ∈ ws) (hb:b ∈ ws) (ne:a≠b) (ka kb:Bool):((cO ws a b ka kb).map f).sum=(ws.map f).sum-(cond ka 0 (f a))-(cond kb 0 (f b)):=by
 have er {l:List aI} {x:aI} (hx:x ∈ l):(l.map f).sum=f x+((l.erase x).map f).sum:=by
  have:=((List.perm_cons_erase hx).map f).sum_eq;rwa [map_cons,sum_cons] at this
 have hm:b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm ne)).mpr hb;have e1:=er ha;have e2:=er hb;have e3:=er hm
 cases ka<;>cases kb<;>simp only [cO,eO,false_eq_true,ite_true,ite_false,cond_true,cond_false]<;>omega
lemma k0 {u p k ws a b op ka kb} (ha:a∈ws) (hb:b∈ws) (ne:a≠b) (al:fS u op=true) (h:eN u p ws k a b op ka kb=true):ct u p k ((cO ws a b ka kb).map Prod.fst) (cj op a b)=true:=by
 let const:=fun w:aI=>ay p.d w.1;let z:=bM op a.1 b.1;let rest:=cO ws a b ka kb;have ck:=sf const ws a b ka kb;change ws.countP const-bi const a ka-bi const b kb ≤ rest.countP const at ck;simp only [eN,and_eq_true,beq_iff_eq,decide_eq_true_eq] at h;obtain ⟨⟨hu,hc⟩,hz⟩:=h;have sum:=jN (k7 u p) ha hb ne ka kb;rw [hu] at sum
 have zs:((cO ws a b ka kb).map (k7 u p)).sum=0:=by omega
 have hs:(rest.map Prod.fst).all (bd u p.d p.wires)=true:=by
  apply all_eq_true.mpr;intro _ hm;obtain ⟨w,hw,rfl⟩:=mem_map.mp hm;have v:=List.sum_eq_zero_iff.mp zs _ (mem_map_of_mem hw)
  cases e:bd u p.d p.wires w.1
  . simp [k7,e] at v
  . rfl
 have opOK:(!(!bd u p.d p.wires z)||fn u p.d p.wires (cj op a b))=true:=by
  simp only [or_eq_true,and_eq_true] at hz
  rcases hz with hz|⟨x,y⟩
  . simp [z,hz]
  . simp [fn,cj,x,y,al]
 change k+p.p+(!bd u p.d p.wires z).toNat<p.b+(ws.countP const-bi const a ka -
  bi const b kb+(ay p.d z).toNat) at hc
 dsimp only [rest] at hs;have ez:bp (cj op a b)=z:=rfl
 simp only [ct,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,countP_cons,
  List.countP_map,Function.comp_def]
 change k+p.p+(!bd u p.d p.wires z).toNat <
  p.b+(rest.countP const+if ay p.d z then 1 else 0)
 cases hc':ay p.d z<;>simp [hc'] at hc ⊢<;>omega
lemma mE (op:Nat) (a b:aQ):zN op a.toNat b.toNat=(bM op a b).toNat:=by
 have e (v:aQ):aU one.toNat v=v.toNat:=by
  rw [f0]
  congr 1
  exact and_allOnes
 have:=yV op one a b;rwa [e,e,e] at this
lemma zE (ws:List aI) (i:Nat):(ws.map (fun w:aI=>w.1.toNat)).getD i 0=(ws.getD i af).1.toNat:=by
 simp only [getD_eq_getElem?_getD,getElem?_map]
 cases ws[i]? with
 | none =>
  have z0:zero.toNat=0:=by simp [zero]
  exact z0.symm
 | some v=>rfl
lemma rD {c:bc} {i j} (nd:(c.2.2.1.map Prod.fst).Nodup) (hi:i<c.2.2.1.length) (hj:j<c.2.2.1.length) (hij:i≠j):(az c i).1≠(az c j).1:=by
 have gi:az c i=c.2.2.1[i]:=by simp [az,getD_eq_getElem?_getD,hi]
 have gj:az c j=c.2.2.1[j]:=by simp [az,getD_eq_getElem?_getD,hj]
 rw [gi,gj];intro e;apply hij;apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp;simpa using e
lemma o8 {c:bc} {fl i j op ka kb} (nd:(c.2.2.1.map Prod.fst).Nodup) (hfl:∀ tag ys,fl tag=some ys->∃ xs ∈ c.2.2.2.2.2 tag,ys=xs.map BitVec.toNat) (hi:i<c.2.2.1.length) (hj:j<c.2.2.1.length) (hij:i≠j) (h:ko fl (dE c) ((dE c).ws.getD i 0) ((dE c).ws.getD j 0) (zN op ((dE c).ws.getD i 0) ((dE c).ws.getD j 0)) ka kb=true):(c.2.2.2.2.2 (jW (bp (cj op (az c i) (az c j)) :: (cO c.2.2.1 (az c i) (az c j) ka kb).map Prod.fst))).any (fi (bp (cj op (az c i) (az c j)) :: (cO c.2.2.1 (az c i) (az c j) ka kb).map Prod.fst))=true:=by
 have mem (t) (ht:t<c.2.2.1.length):az c t ∈ c.2.2.1:=by
  simp [az,getD_eq_getElem?_getD,ht]
 have hne:=rD nd hi hj hij;have ha:=mem i hi;have hb:=mem j hj;have hab:az c i≠az c j:=fun e=>hne (congrArg Prod.fst e);have kv (v:aQ):=jV nd ha hb ka kb v;have sum:=jN (fun w:aI=>ef w.1) ha hb hab ka kb;have wi:az c i=c.2.2.1.getD i af:=rfl;have wj:az c j=c.2.2.1.getD j af:=rfl;simp only [ko,dE,zE,<-wi,<-wj,mE] at h
 generalize az c i=a at *
 generalize az c j=b at *
 change Option.rec false _ (fl (ef (bM op a.1 b.1)+(((c.2.2.1.map (fun w:aI=>w.1.toNat)).map Bu).sum -
  (cond ka 0 (ef a.1))-(cond kb 0 (ef b.1)))))=true at h
 have tot:((c.2.2.1.map (fun w:aI=>w.1.toNat)).map Bu).sum=(c.2.2.1.map (fun w:aI=>ef w.1)).sum:=by
  rw [map_map];rfl
 rw [tot,<-sum] at h
 have tag:jW (bp (cj op a b) :: (cO c.2.2.1 a b ka kb).map Prod.fst) =
  ef (bM op a.1 b.1)+((cO c.2.2.1 a b ka kb).map (fun w:aI=>ef w.1)).sum:=by
  rw [oW,map_cons,sum_cons,map_map];rfl
 rw [<-tag] at h;generalize jW (bp (cj op a b) :: (cO c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
 cases hf:fl t with
 | none=>simp [hf] at h
 | some ys =>
  obtain ⟨xs,hx,rfl⟩:=hfl t ys hf;rw [hf] at h;simp only [and_eq_true,all_eq_true,or_eq_true,lc,beq_eq,Bool.not_eq_true'] at h;obtain ⟨h1,h2,h3⟩:=h
  have back {v:aQ} (hv:v.toNat ∈ xs.map BitVec.toNat):v ∈ xs:=by
   obtain ⟨w,hw,e⟩:=mem_map.mp hv;exact toNat_inj.mp e ▸ hw
  apply any_eq_true.mpr;refine ⟨xs,hx,?_⟩;simp only [fi,and_eq_true,all_eq_true,contains_eq_mem,decide_eq_true_eq];constructor
  . intro v hv
    rcases mem_cons.mp hv with rfl|hv
    . exact back h1
    . obtain ⟨hw,va,vb⟩:=(kv v).mp hv;obtain ⟨w,hm,rfl⟩:=mem_map.mp hw
      rcases h2 _ (mem_map_of_mem hm) with ⟨x,y⟩|⟨x,y⟩|x
      . rcases va with va|va
        . exact absurd (toNat_inj.mp y) va
        . simp [va] at x
      . rcases vb with vb|vb
        . exact absurd (toNat_inj.mp y) vb
        . simp [vb] at x
      . exact back x
  . intro v hv
    rcases h3 _ (mem_map_of_mem hv) with x|⟨⟨x,y⟩,m⟩
    . exact mem_cons.mpr (Or.inl (toNat_inj.mp x))
    . refine mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
      . obtain ⟨w,hw,e⟩:=mem_map.mp m;exact toNat_inj.mp e ▸ mem_map_of_mem hw
      . rcases x with x|x
        . exact Or.inr x
        . refine Or.inl fun e => ?_;subst e;simp at x
      . rcases y with x|x
        . exact Or.inr x
        . refine Or.inl fun e => ?_;subst e;simp at x
def hY (fl:Nat->Option (List Nat)) (l:l3) (i j op p2i p2j dropBits pairBits:Nat) (ka kb:Bool):Bool:=
 or (and (and (ble (Nat.succ i) l.n) (and (ble (Nat.succ j) l.n) (and (ble (Nat.succ op) l.ops) (not (Nat.beq i j)))))
  (let x:=l.ws.getD i 0;let y:=l.ws.getD j 0;let z:=zN op x y
   or (cond ka
    (cond kb (rL l.p0 z)
     (or (il l.p0 z p2i p2j dropBits true false) (jy l.p1 z p2i p2j dropBits true false)))
    (cond kb (or (il l.p0 z p2i p2j dropBits false true) (jy l.p1 z p2i p2j dropBits false true))
     (or (il l.p0 z p2i p2j pairBits false false)
      (or (jy l.p1 z p2i p2j pairBits false false) (q9 l.p2 z p2i p2j pairBits)))))
    (or (or (Nat.beq z 0) (or (Nat.beq z mK) (gC z l.ws)))
     (ko fl l x y z ka kb)))) (eU l.ctx i j op ka kb)
lemma iF {u k i j op ka kb} {ws:List aI} {ps:List bu} (hi:i<ws.length) (hj:j<ws.length) (hij:i≠j) (h0:il ((bz u k ws ps).1 ++ (bz u k ws ps).2.1) (zN op (ws.getD i af).1.toNat (ws.getD j af).1.toNat) (bf i) (bf j) (Nat.add (cond ka 0 (bf i)) (cond kb 0 (bf j))) ka kb=true):∃ p ∈ ps,eN u p ws k (ws.getD i af) (ws.getD j af) op ka kb=true:=by
 obtain ⟨q,hqm,hqok⟩:=(f2 _ _).mp h0;obtain ⟨p,hp,hs⟩:=(el u k ws ps).1 q hqm;have hsum:=hs.2.2.2.2.2.2.2;let d:=p.d.toNat;let ms:=ws.map (fun w:aI=>aU d w.1);let av:=dF u d (p.wires.map (aU d))
 have hall:∀ t<ws.length,av (aU d (ws.getD t af).1)=true:=by
  intro t ht;have hle:=kD (fun m=>cond (av m) 0 1) (l:=ms) (i:=t) (by simpa [ms] using ht)
  have hm0:ms[t]'(by simpa [ms] using ht)=aU d (ws.getD t af).1:=by simp [ms,getD_eq_getElem?_getD,ht]
  rw [hm0] at hle;have hus':(ms.map fun m=>cond (av m) 0 1).sum=0:=hsum;rw [hus'] at hle
  cases hv:av (aU d (ws.getD t af).1)
  . rw [hv] at hle;exact absurd hle (by decide)
  . rfl
 dsimp only [av,d] at hall
 exact ⟨p,hp,gF hs hi hj hij (by rw [hall i hi,hall j hj];cases ka<;>cases kb<;>rfl) (fun _=>⟨hall i hi,hall j hj⟩) (hR _ _ _ hqok)⟩
lemma kF {u k i j op ka kb} {ws:List aI} {ps:List bu} (hi:i<ws.length) (hj:j<ws.length) (hij:i≠j) (h1:jy (bz u k ws ps).2.2.1 (zN op (ws.getD i af).1.toNat (ws.getD j af).1.toNat) (bf i) (bf j) (Nat.add (cond ka 0 (bf i)) (cond kb 0 (bf j))) ka kb=true):∃ p ∈ ps,eN u p ws k (ws.getD i af) (ws.getD j af) op ka kb=true:=by
 obtain ⟨q,hqm,hqok⟩:=(f2 _ _).mp h1;obtain ⟨p,hp,hs⟩:=(el u k ws ps).2.1 q hqm;have hum_eq:=hs.1;have hsum:=hs.2.2.2.2.2.2.2;let db:=Nat.add (cond ka 0 (bf i)) (cond kb 0 (bf j));change cond (Nat.beq (land q.um db) q.um) _ false=true at hqok
 cases hland:Nat.beq (land q.um db) q.um
 . rw [hland] at hqok;exact noConfusion hqok
 . simp only [hland,cond_true] at hqok;have hle:=beq_eq.mp hland;let d:=p.d.toNat;let ms:=ws.map (fun w:aI=>aU d w.1);let av:=dF u d (p.wires.map (aU d))
   have z0:aU p.d.toNat zero=0:=by simp [aU,zero]
   have hex:∃ t<ws.length,av (aU d (ws.getD t af).1)=false:=by
    by_contra hnone;push_neg at hnone
    have hz:(ms.map fun m=>cond (av m) 0 1).sum=0:=by
     apply List.sum_eq_zero_iff.mpr;intro x hx;obtain ⟨m,hm,rfl⟩:=mem_map.mp hx;obtain ⟨t,ht,rfl⟩:=List.getElem_of_mem hm
     have ht':t<ws.length:=by simpa [ms] using ht
     have heq:ms[t]'ht=aU d (ws.getD t af).1:=by simp [ms,getD_eq_getElem?_getD,ht']
     rw [heq,Bool.eq_true_of_not_eq_false (hnone t ht')];rfl
    have hus':(ms.map fun m=>cond (av m) 0 1).sum=1:=hsum;omega
   obtain ⟨t,ht,htf⟩:=hex
   have hum:q.um.testBit t=true:=by
    rw [hum_eq];simp only [ey,length_map,ht,ite_true,kQ _ _ z0];change !av (aU d (ws.getD t af).1)=true;rw [htf];rfl
   have hdb:db.testBit t=true:=by
    have hb1:=congrArg (fun n=>n.testBit t) hle;change (q.um&&&db).testBit t=_ at hb1;simp only [testBit_and,hum,Bool.true_and] at hb1;exact hb1
   have hge1:1 ≤ Nat.add (cond ka 0 (cond (av (aU d (ws.getD i af).1)) 0 1)) (cond kb 0 (cond (av (aU d (ws.getD j af).1)) 0 1)):=by
    cases ka<;>cases kb
    . simp only [db,cond_false,dy,add_eq,dj hij,or_eq_true,decide_eq_true_eq] at hdb ⊢
      rcases hdb with rfl|rfl<;>rw [htf]<;>simp
    . simp only [db,cond_false,cond_true,add_eq,Nat.add_zero,dy,testBit_two_pow,decide_eq_true_eq] at hdb ⊢;rw [hdb,htf];decide
    . simp only [db,cond_false,cond_true,add_eq,Nat.zero_add,dy,testBit_two_pow,decide_eq_true_eq] at hdb ⊢;rw [hdb,htf];decide
    . simp [db] at hdb
   have hle1:Nat.add (cond ka 0 (cond (av (aU d (ws.getD i af).1)) 0 1)) (cond kb 0 (cond (av (aU d (ws.getD j af).1)) 0 1)) ≤ 1:=by
    have h2:=gX (fun m=>cond (av m) 0 1) (l:=ms) (by simpa [ms] using hi) (by simpa [ms] using hj) hij
    have gi:ms[i]'(by simpa [ms] using hi)=aU d (ws.getD i af).1:=by simp [ms,getD_eq_getElem?_getD,hi]
    have gj:ms[j]'(by simpa [ms] using hj)=aU d (ws.getD j af).1:=by simp [ms,getD_eq_getElem?_getD,hj]
    rw [gi,gj] at h2;have hus':(ms.map fun m=>cond (av m) 0 1).sum=1:=hsum
    cases ka<;>cases kb<;>simp only [cond_true,cond_false,add_eq]<;>omega
   exact ⟨p,hp,gF hs hi hj hij (by dsimp only [av,d] at hge1 hle1;simp only [add_eq] at hge1 hle1 ⊢;omega) (fun hf=>noConfusion hf) hqok⟩
lemma wl {u k i j op} {ws:List aI} {ps:List bu} (hi:i<ws.length) (hj:j<ws.length) (hij:i≠j) (h2:q9 (bz u k ws ps).2.2.2 (zN op (ws.getD i af).1.toNat (ws.getD j af).1.toNat) (bf i) (bf j) (Nat.add (bf i) (bf j))=true):∃ p ∈ ps,eN u p ws k (ws.getD i af) (ws.getD j af) op false false=true:=by
 obtain ⟨q,hqm,hqok⟩:=(f2 _ _).mp h2;obtain ⟨p,hp,hs⟩:=(el u k ws ps).2.2 q hqm;have hum_eq:=hs.1
 cases heq:Nat.beq q.um (Nat.add (bf i) (bf j))
 . rw [heq] at hqok;exact noConfusion hqok
 . simp only [heq,cond_true] at hqok;have hum:=beq_eq.mp heq
   have z0:aU p.d.toNat zero=0:=by simp [aU,zero]
   have hti:q.um.testBit i=true:=by rw [hum];simp [dy,add_eq,dj hij]
   have htj:q.um.testBit j=true:=by rw [hum];simp [dy,add_eq,dj hij]
   rw [hum_eq] at hti htj;simp only [ey,length_map,hi,hj,ite_true,kQ _ _ z0,Bool.not_eq_true'] at hti htj;exact ⟨p,hp,gF hs hi hj hij (by rw [hti,htj];rfl) (fun hf=>noConfusion hf) hqok⟩
lemma jR {c:bc} {fl i j op ka kb} (nd:(c.2.2.1.map Prod.fst).Nodup) (hfl:∀ tag ys,fl tag=some ys->∃ xs ∈ c.2.2.2.2.2 tag,ys=xs.map BitVec.toNat) (h:hY fl (dE c) i j op (bf i) (bf j) (Nat.add (cond ka 0 (bf i)) (cond kb 0 (bf j))) (Nat.add (bf i) (bf j)) ka kb=true):eU c i j op ka kb=true:=by
 simp only [hY,or_eq_true,and_eq_true] at h
 rcases h with ⟨⟨hi,hj,ho,hn⟩,h|h|h⟩|h
 . have hi:i<c.2.2.1.length:=ble_eq.mp hi;have hj:j<c.2.2.1.length:=ble_eq.mp hj;have ho:Nat.succ op ≤ cond c.2.2.2.1.2 4 2:=ble_eq.mp ho
   have hij:i≠j:=fun e=>by simp [e] at hn
   have al:fS c.2.2.2.1.2 op=true:=by
    cases hu:c.2.2.2.1.2<;>simp [hu] at ho<;>simp [fS]<;>omega
   have mem (t) (ht:t<c.2.2.1.length):az c t ∈ c.2.2.1:=by
    simp [az,getD_eq_getElem?_getD,ht]
   have hne:=rD nd hi hj hij
   have finish (ex:∃ p ∈ c.2.2.2.2.1,eN c.2.2.2.1.2 p c.2.2.1 (c.1-1) (c.2.2.1.getD i af) (c.2.2.1.getD j af) op ka kb=true):
    eU c i j op ka kb=true:=by
    obtain ⟨p,hp,hs⟩:=ex;have closed:=k0 (mem i hi) (mem j hj) (fun e=>hne (congrArg Prod.fst e)) al hs
    have cut:c.2.2.2.2.1.any (fun p=>ct c.2.2.2.1.2 p (c.1-1)
     ((cO c.2.2.1 (az c i) (az c j) ka kb).map Prod.fst)
     (cj op (az c i) (az c j)))=true:=
     any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [eU,ec,em,cut,Bool.or_true]
    repeat' split
    all_goals rfl
   simp only [dE,zE] at h
   cases ka<;>cases kb
   . simp only [cond_false,or_eq_true] at h
     rcases h with h0|h1|h2
     . exact finish (iF hi hj hij h0)
     . exact finish (kF hi hj hij h1)
     . exact finish (wl hi hj hij h2)
   . simp only [cond_false,cond_true,or_eq_true] at h
     rcases h with h0|h1
     . exact finish (iF hi hj hij h0)
     . exact finish (kF hi hj hij h1)
   . simp only [cond_false,cond_true,or_eq_true] at h
     rcases h with h0|h1
     . exact finish (iF hi hj hij h0)
     . exact finish (kF hi hj hij h1)
   . simp only [cond_true] at h
     have h0:il ((bz c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1).1 ++ (bz c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1).2.1)
      (zN op (c.2.2.1.getD i af).1.toNat (c.2.2.1.getD j af).1.toNat) (bf i) (bf j) 0 true true=true:=by
      obtain ⟨q,hqm,hqok⟩:=(f2 _ _).mp h;exact (f2 _ _).mpr ⟨q,hqm,by simpa [gO] using hqok⟩
     exact finish (iF hi hj hij h0)
 . simp only [dE,zE,mE,or_eq_true,beq_eq,lc,mL] at h
   have hbad:(!cE (fq op (az c i) (az c j)).1 ||
    c.2.2.1.any (fun v=>v.1==(fq op (az c i) (az c j)).1))=true:=by
    simp only [fq,or_eq_true,Bool.not_eq_true',any_eq_true,beq_iff_eq]
    rcases h with hz|ho|hm
    . left;have ez:bM op (az c i).1 (az c j).1=zero:=toNat_inj.mp hz;simp [cE,ez]
    . left;have eo:bM op (az c i).1 (az c j).1=one:=toNat_inj.mp ho;simp [cE,eo]
    . right;obtain ⟨v,hv,he⟩:=mem_map.mp hm;exact ⟨v,hv,toNat_inj.mp he⟩
   simp only [eU,ec,hbad,ite_true]
   repeat' split
   all_goals rfl
 . have cut:=o8 nd hfl (ble_eq.mp hi) (ble_eq.mp hj) (fun e=>by simp [e] at hn) h;simp only [eU,ec,em,cut,Bool.true_or]
   repeat' split
   all_goals rfl
 . exact h
end
def gn (v t:Nat):Nat:=cond (Nat.beq t (v&&&15)) (v>>>4) (cond (Nat.beq t (v>>>4)) (v&&&15) t)
section
variable [w : Width]
def dU (v:Nat):Bool:=and (ble ((v&&&15)+1) (v>>>4)) (ble ((v>>>4)+1) N)
end
set_option maxRecDepth 8192 in
lemma nN:∀ v:Fin 144,@dU ⟨false⟩ v.val=true->∀ t:Fin 9,gn v.val t.val<9 /\ @f4 ⟨false⟩ (@dh ⟨false⟩ v.val) (d1.getD t.val 0)=d1.getD (gn v.val t.val) 0:=by decide +kernel
set_option maxRecDepth 8192 in
lemma mB:∀ v:Fin 160,@dU ⟨true⟩ v.val=true->∀ t:Fin 10,gn v.val t.val<10 /\ @f4 ⟨true⟩ (@dh ⟨true⟩ v.val) (de.getD t.val 0)=de.getD (gn v.val t.val) 0:=by decide +kernel
def vA (perm:List Nat) (t:Nat):Nat:=perm.foldl (fun t v=>gn v t) t
section
variable [w : Width]
lemma pZ {v t:Nat} (hv:dU v=true) (ht:t<N):gn v t<N/\f4 (dh v) (inputs.getD t zero)=inputs.getD (gn v t) zero:=by
 rcases w with ⟨_|_⟩
 . have lt:v<144:=by simp only [dU,N,false_eq_true,ite_false,and_eq_true,ble_eq,Nat.shiftRight_eq_div_pow] at hv;omega
   exact nN ⟨v,lt⟩ hv ⟨t,ht⟩
 . have lt:v<160:=by simp only [dU,N,ite_true,and_eq_true,ble_eq,Nat.shiftRight_eq_div_pow] at hv;omega
   exact mB ⟨v,lt⟩ hv ⟨t,ht⟩
lemma vB {perm:List Nat} (ok:perm.all dU=true) {t:Nat} (ht:t<N):bn (perm.map dh).reverse (inputs.getD t zero)=inputs.getD (vA perm t) zero:=by
 rw [bn,List.foldr_reverse,List.foldl_map]
 induction perm generalizing t with
 | nil=>rfl
 | cons v perm ih =>
  simp only [List.all_cons,and_eq_true] at ok;obtain ⟨lt,e⟩:=pZ ok.1 ht;rw [foldl_cons,e,ih ok.2 lt];rfl
end
def jz:Nat->Nat->List Nat->List Nat
 | 0,_,ws=>ws
 | n+1,bits,ws=>gK (zN ((bits>>>8)&&&3) (ws.getD (bits&&&15) 0) (ws.getD ((bits>>>4)&&&15) 0))
  fun z=>jz n (bits>>>10) (ws++[z])
section
variable [w : Width]
lemma oI (F:aQ->Nat) (F0:F zero=0) (Fb:∀ op a b,F (bM op a b)=zN op (F a) (F b)) (n bits:Nat) (ds:List aI):(ft n bits ds).map (fun w=>F w.1)=jz n bits (ds.map fun w=>F w.1):=by
 have gd (ds:List aI) (i:Nat):(ds.map fun w=>F w.1).getD i 0=F (ds.getD i af).1:=by
  simp only [getD_eq_getElem?_getD,getElem?_map]
  cases ds[i]? with
  | none=>exact F0.symm
  | some v=>rfl
 induction n generalizing bits ds with
 | zero=>rfl
 | succ n ih =>
  rw [jz,gL,ft,ih,gd,gd,<-Fb,List.map_append];rfl
end
lemma kO {α β:Type} (f : α -> β) (bits:Nat) (ws:List α):(da bits ws).map f=da bits (ws.map f):=by
 induction ws generalizing bits with
 | nil=>rfl
 | cons w ws ih =>
  rw [map_cons,da,da]
  split
  . rw [map_cons,ih]
  . exact ih _
section
variable [w : Width]
def iZ (g:aM) (k i:Nat) (perm:List Nat):List Nat:=
 let raw:=(dt g.m).map fun e=>(inputs.getD (vA perm e.1) zero).toNat
 let (_,depth,_,_,_,_,_,data):=g.l k
 let len:=10*depth
 gK (it (g.l k) (dt g.m).length i) fun rec =>
 da (rec>>>len) (jz depth (rec&&&((1<<<len)-1)) raw)
lemma me (g:aM) (k i:Nat) {perm:List Nat} (ok:perm.all dU=true):iZ g k i perm=((bK g k i).map (bn (perm.map dh).reverse)).map BitVec.toNat:=by
 let ms:=(perm.map dh).reverse;let F (a:aQ):Nat:=(bn ms a).toNat
 have F0:F zero=0:=by
  change (bn ms zero).toNat=0;rw [cF,(f3 _).1];simp [zero]
 have Fb (op a b):F (bM op a b)=zN op (F a) (F b):=by
  change (bn ms (bM op a b)).toNat=zN op (bn ms a).toNat (bn ms b).toNat;rw [mE,cF,kL,cF,cF]
 have raw:(e9 g).map (fun w=>F w.1)=(dt g.m).map fun e=>(inputs.getD (vA perm e.1) zero).toNat:=by
  simp only [e9,iH,map_map];apply List.map_congr_left;rintro ⟨j,a⟩ hm;obtain ⟨hj,rfl⟩:=gV hm;exact congrArg BitVec.toNat (vB ok hj)
 have len:(e9 g).length=(dt g.m).length:=by simp [e9,iH]
 unfold iZ bK f1
 rcases g.l k with ⟨a,depth,b,c,d,e,f,data⟩
 simp only [gL,jm,len];rw [map_map,map_map,kO,<-raw,<-oI F F0 Fb];rfl
def kp (g:aM) (k:Nat) (pair:Nat × Nat):Option (List Nat):=
 if pair.1 ≥ (g.l k).1 then none else
  (g.a[pair.2]?).bind fun perm=>cond (perm.all dU) (some (iZ g k pair.1 perm)) none
def oK (g:aM) (k:Nat):Nat->Option (List Nat):=fun tag=>(g.x k tag).bind (kp g (k-1))
def fT (fl:Nat->Option (List Nat)) (u:Bool) (b:la) (xs:List l3) (i j op p2i p2j dropBits pairBits pa pb pz:Nat) (ka kb:Bool):=
 let (k,n,r,_,cov):=b
 let len:=1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
 if len>k then true else
  let mask:=g5 r (gp cov pa pb ka kb|||pz)
  iE (fun c=>hY fl c i j op p2i p2j dropBits pairBits ka kb) mask xs
lemma l7 {fl u} (k n) (xs:List bc) {i j op:Nat} {ka kb} (hi:i<n) (hj:j<n) {q:Nat} (hq:q<xs.length) (budget:xs[q].1=k) (arity:xs[q].2.1=n) (mode:xs[q].2.2.2.1.2=u) (nd:(xs[q].2.2.1.map Prod.fst).Nodup) (hfl:∀ tag ys,fl tag=some ys->∃ zs ∈ xs[q].2.2.2.2.2 tag,ys=zs.map BitVec.toNat) (pass:fT fl u (cC k n xs) (xs.map dE) i j op (bf i) (bf j) (Nat.add (cond ka 0 (bf i)) (cond kb 0 (bf j))) (Nat.add (bf i) (bf j)) (ce (!u) (dY (cC k n xs) i)) (ce (!u) (dY (cC k n xs) j)) (ce (!u) (eK op (dY (cC k n xs) i) (dY (cC k n xs) j))) ka kb=true):eU xs[q] i j op ka kb=true:=by
 let len:=1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
 have eval:eU xs[q] i j op ka kb =
  if len>k then true else if iV xs[q] (!u) ka kb op i j !=allOnes 152 then true
  else if !cE (fq op (az xs[q] i) (az xs[q] j)).1 ||
   xs[q].2.2.1.any (fun v=>v.1==(fq op (az xs[q] i) (az xs[q] j)).1)
  then true else em u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
   ((cO xs[q].2.2.1 (az xs[q] i) (az xs[q] j) ka kb).map Prod.fst)
   (cj op (az xs[q] i) (az xs[q] j)):=by
  simp only [eU,ec,budget,arity,mode,len,iV]<;>rfl
 by_cases small:len>k
 . simp [eval,small]
 . let r:=kT xs.length;let a:=dY (cC k n xs) i;let b:=dY (cC k n xs) j;let cov:=hA (fun c:bc=>c.2.2.2.1.1) xs
   change (if len>k then true else iE _ (g5 r
    (gp cov (ce (!u) a) (ce (!u) b) ka kb |||
     ce (!u) (eK op a b))) (xs.map dE))=true at pass
   rw [if_neg small] at pass;have ca:a=_:=jg k n xs hi;have cb:b=_:=jg k n xs hj;dsimp only [r,cov] at pass;rw [ca,cb,sq,fN,fN,fN,k6,km] at pass
   by_cases hit:iV xs[q] (!u) ka kb op i j=allOnes 152
   . apply jR nd hfl
     have m:=so _ _ _ q (by simpa using hq) (by
      rw [ya _ _ _ hq]
      exact beq_iff_eq.mpr hit) pass
     simpa only [List.getElem_map] using m
   . rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]
def lg (fl:Nat->Option (List Nat)) (u:Bool) (b:la) (xs:List l3) (i j p2i p2j pairBits pa pb:Nat) (a b':fc) (op:Nat):=
 gK (ce (!u) (eK op a b')) fun pz =>
 fT fl u b xs i j op p2i p2j pairBits pairBits pa pb pz false false &&
 fT fl u b xs i j op p2i p2j p2j pairBits pa pb pz true false &&
 fT fl u b xs i j op p2i p2j p2i pairBits pa pb pz false true &&
 fT fl u b xs i j op p2i p2j 0 pairBits pa pb pz true true
def ig (fl:Nat->Option (List Nat)) (u:Bool) (b:la) (xs:List l3) (i:Nat) (js:List Nat):=
 gK (bf i) fun p2i =>
 let a:=dY b i
 gK (ce (!u) a) fun pa =>
 js.all (fun j =>
  gK (bf j) fun p2j =>
  gK (Nat.add p2i p2j) fun pairBits =>
  let b':=dY b j
  gK (ce (!u) b') fun pb =>
  (kE u).all (lg fl u b xs i j p2i p2j pairBits pa pb a b'))
def fd (fl:Nat->Option (List Nat)) (u:Bool) (b:la) (xs:List l3):List Nat->Bool
 | []=>true
 | i::js=>ig fl u b xs i js&&fd fl u b xs js
lemma l8 {fl u} (k n) (xs:List bc) {q:Nat} (hq:q<xs.length) (budget:xs[q].1=k) (arity:xs[q].2.1=n) (mode:xs[q].2.2.2.1.2=u) (nd:(xs[q].2.2.1.map Prod.fst).Nodup) (hfl:∀ tag ys,fl tag=some ys->∃ zs ∈ xs[q].2.2.2.2.2 tag,ys=zs.map BitVec.toNat) (js:List Nat) (bounds:∀ j ∈ js,j<n) (allRows:fd fl u (cC k n xs) (xs.map dE) js=true):e8 xs[q] (js.map (az xs[q]))=true:=by
 induction js with
 | nil=>rfl
 | cons i js ih =>
  simp only [fd,and_eq_true,ig,gL,all_eq_true] at allRows;simp only [map_cons,e8,mC,and_eq_true,all_eq_true,mem_map];have hi:=bounds i mem_cons_self
  refine ⟨?_,ih (fun j hj=>bounds j (mem_cons_of_mem _ hj)) allRows.2⟩
  rintro _ ⟨j,hj,rfl⟩ op hop;have hj':=bounds j (mem_cons_of_mem _ hj);rw [mode] at hop;have pass:=allRows.1 j hj op hop;have check := @l7 _ fl u k n xs i j op;simp only [lg,gL,and_eq_true] at pass;simp only [dJ,and_eq_true]
  exact ⟨⟨⟨check (ka:=false) (kb:=false) hi hj' hq budget arity mode nd hfl pass.1.1.1,
   check (ka:=true) (kb:=false) hi hj' hq budget arity mode nd hfl (by simpa [Nat.zero_add] using pass.1.1.2)⟩,
   check (ka:=false) (kb:=true) hi hj' hq budget arity mode nd hfl (by simpa [Nat.add_zero] using pass.1.2)⟩,
   check (ka:=true) (kb:=true) hi hj' hq budget arity mode nd hfl (by simpa using pass.2)⟩
def kN (fl:Nat->Option (List Nat)) (u:Bool) (k n:Nat) (xs:List bc):=fd fl u (cC k n xs) (xs.map dE) (List.range n)
lemma nF {fl u k n} {xs:List bc} {q} (hq:q<xs.length) (hb:xs[q].1=k) (ha:xs[q].2.1=n) (hm:xs[q].2.2.2.1.2=u) (nd:(xs[q].2.2.1.map Prod.fst).Nodup) (hfl:∀ tag ys,fl tag=some ys->∃ zs ∈ xs[q].2.2.2.2.2 tag,ys=zs.map BitVec.toNat) (hn:xs[q].2.2.1.length=n) (pass:kN fl u k n xs=true):e8 xs[q] xs[q].2.2.1=true:=by
 have all:=l8 k n xs hq hb ha hm nd hfl (List.range n) (fun _=>mem_range.mp) pass
 have eq:(List.range n).map (az xs[q])=xs[q].2.2.1:=by
  apply List.ext_getElem
  . simp [hn]
  . intro i h1 h2;simp [az,getD_eq_getElem?_getD,h2]
 rwa [eq] at all
def fg (g:aM) (k i:Nat):bc:=
 let raw:=e9 g
 let (num,depth,cw,iw,pw,offw,lw,data):=g.l k
 let (ops,bank,ws):=f1 g k i
 let rules:=(gM (g.l k) raw.length i).filterMap (fun (a,b)=>fV g ops depth bank a b)
 let ls:=fun tag=>((g.x k tag).bind (dT g (k-1))).toList
 (k,ws.length,ws,gS g.u ws,rules,ls)
lemma xb (g:aM) (k i tag:Nat) (ys) (h:oK g k tag=some ys):∃ xs ∈ (fg g k i).2.2.2.2.2 tag,ys=xs.map BitVec.toNat:=by
 change ∃ xs ∈ ((g.x k tag).bind (dT g (k-1))).toList,_;unfold oK at h
 cases hp:g.x k tag with
 | none=>simp [hp] at h
 | some pair =>
  simp only [hp,Option.bind_some,kp] at h;simp only [Option.bind_some,dT]
  split at h
  . contradiction
  next v =>
   cases ha:g.a[pair.2]? with
   | none=>simp [ha] at h
   | some perm =>
    simp only [ha,Option.bind_some] at h
    cases hv:perm.all dU with
    | false=>simp [hv] at h
    | true =>
     simp only [hv,cond_true,Option.some.injEq] at h
     refine ⟨(bK g (k-1) pair.1).map (bn (perm.map dh).reverse),?_,?_⟩
     . simp [v]
     . exact h.symm.trans (me g _ _ hv)
def ph (T:aQ) (c:bc):=
 let ws:=c.2.2.1.map Prod.fst
 decide ws.Nodup && !(ws.contains T)
lemma mg (g:aM) (k i:Nat):cW g k i=(ph (aY g) (fg g k i)&&(if k=0 then true else e8 (fg g k i) (fg g k i).2.2.1)):=rfl
lemma sn {g k start n} (h:∀ (i:Nat),start ≤ i->i<start+n->cW g k i=true):aP g k start n=true:=by
 induction n with
 | zero=>rfl
 | succ n ih =>
  simp only [aP,and_eq_true];exact ⟨h _ (by omega) (by omega),ih (fun i le lt=>h i le (by omega))⟩
def fp (g:aM) (k start n:Nat):=((List.range n).map (start+·)).map (fg g k)
def oV (g:aM) (k start n ar:Nat):=(fp g k start n).all (fun c=>c.2.1==ar&&ph (aY g) c)
def fC (g:aM) (k start n ar lo len:Nat):=
 let xs:=fp g k start n
 let b:=cC k ar xs
 jS xs fun ys=>(List.range len).all (fun d =>
  let i:=lo+d
  ig (oK g k) g.u b ys i (List.range' (i+1) (ar-(i+1))))
lemma i8 {g k start n ar lo len} (h:fC g k start n ar lo len=true) (i:Nat) (l:lo ≤ i) (r:i<lo+len):ig (oK g k) g.u (cC k ar (fp g k start n)) ((fp g k start n).map dE) i (List.range' (i+1) (ar-(i+1)))=true:=by
 simp only [fC,hI] at h;have ha:=all_eq_true.mp h (i-lo) (mem_range.mpr (by omega));simpa only [add_sub_of_le l] using ha
lemma mt {g k start n ar lo a b} (h:fC g k start n ar lo a=true) (t:fC g k start n ar (lo+a) b=true):fC g k start n ar lo (a+b)=true:=by
 simp only [fC,hI];apply all_eq_true.mpr;intro j hj;have jlt:=mem_range.mp hj
 by_cases first:j<a
 . exact i8 h (lo+j) (by omega) (by omega)
 . exact i8 t (lo+j) (by omega) (by omega)
lemma xa {g k start n ar} (h:fC g k start n ar 0 ar=true):kN (oK g k) g.u k ar (fp g k start n)=true:=by
 let xs:=fp g k start n
 have go (lo num:Nat) (eq:lo+num=ar):
  fd (oK g k) g.u (cC k ar xs) (xs.map dE) (List.range' lo num)=true:=by
  induction num generalizing lo with
  | zero=>rfl
  | succ num ih =>
   simp only [List.range'_succ,fd,and_eq_true]
   refine ⟨?_,ih (lo+1) (by omega)⟩
   have ok:=i8 h lo (by omega) (by omega);simpa only [show ar-(lo+1)=num by omega] using ok
 unfold kN;rw [List.range_eq_range'];exact go 0 ar (by omega)
lemma lj {g k start n ar} (hd:oV g k start n ar=true) (h:fC g k start n ar 0 ar=true):aP g k start n=true:=by
 apply sn;intro i lo hi;let xs:=fp g k start n
 have hm:fg g k i ∈ xs:=by
  apply mem_map.mpr;exact ⟨i,mem_map.mpr ⟨i-start,mem_range.mpr (by omega),by omega⟩,rfl⟩
 obtain ⟨q,hq,e⟩:=List.getElem_of_mem hm;have one:=all_eq_true.mp hd _ hm;simp only [and_eq_true,beq_iff_eq] at one
 have hb:xs[q].1=k:=by rw [e];rfl
 have ha:xs[q].2.1=ar:=e ▸ one.1
 have nd:(xs[q].2.2.1.map Prod.fst).Nodup:=by
  have p:=one.2;simp only [ph,and_eq_true,decide_eq_true_eq] at p;rw [e];exact p.1
 have hfl:∀ tag ys,oK g k tag=some ys->∃ zs ∈ xs[q].2.2.2.2.2 tag,ys=zs.map BitVec.toNat:=by
  rw [e];exact fun tag ys h=>xb g k i tag ys h
 have hm:xs[q].2.2.2.1.2=g.u:=by rw [e];rfl
 have hn:xs[q].2.2.1.length=ar:=by rw [e];exact one.1
 rw [mg,and_eq_true]
 refine ⟨one.2,?_⟩
 split
 . rfl
 . exact e ▸ nF hq hb ha hm nd hfl hn (xa h)
def ba (g:aM) (k start n ar lo num:Nat):Nat->Prop
 | 0=>fC g k start n ar lo num=true
 | d+1=>ba g k start n ar lo (num/2) d/\ba g k start n ar (lo+num/2) (num-num/2) d
lemma tZ {g k start n ar lo num d} (h:ba g k start n ar lo num d):fC g k start n ar lo num=true:=by
 induction d generalizing lo num with
 | zero=>exact h
 | succ d ih =>
  have v:=mt (ih h.1) (ih h.2);simpa only [add_sub_of_le (Nat.div_le_self num 2)] using v
def aE (g:aM) (k start n ar rows:Nat):Nat->Prop
 | 0=>oV g k start n ar=true/\ba g k start n ar 0 ar rows
 | d+1=>aE g k start (n/2) ar rows d/\aE g k (start+n/2) (n-n/2) ar rows d
lemma aq {g k start n} (ar rows d:Nat) (h:aE g k start n ar rows d):aP g k start n=true:=by
 induction d generalizing start n with
 | zero=>exact lj h.1 (tZ h.2)
 | succ d ih =>
  have v:=aJ (ih h.1) (ih h.2);simpa only [add_sub_of_le (Nat.div_le_self n 2)] using v
end
def aW {α} (f : α->Bool) (xs:List α):Nat->Prop
 | 0=>xs.all f=true
 | d+1=>aW f (xs.take (xs.length/2)) d/\aW f (xs.drop (xs.length/2)) d
lemma aH {α f xs d} (h : @aW α f xs d):xs.all f=true:=by
 induction d generalizing xs with
 | zero=>exact h
 | succ d ih =>
  have ap:((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true:=by
   simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
  simpa only [List.take_append_drop] using ap
section
variable [w : Width]
lemma pY {u} {raw:List aQ} {T:aQ} {L:Nat} (pT:bg T) (h:aR u raw T L):gB u raw T one L:=by
 refine ⟨id,raw,fun r=>d0 r,fun a ha => ?_,fx pT,h⟩
 exact Or.inl (mem_map_of_mem ha)
lemma gf {u} {m q cap:Nat} {p:Nat->Nat} (low:∀ q,aR u (aN q) (ac q) (p q)) (e:(ac q==ac m&&(aN q==cB m)&&(p q==cap+1)&&cE (ac m)&&decide (cB m).Nodup&&jF u one (cap+1) cap 0 (cB m) (cB m))=true):aB u (ac m) cap (cB m).toFinset:=by
 simp only [and_eq_true,beq_iff_eq,decide_eq_true_eq] at e;obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩:=e;have h:=low q;rw [e1,e2,e3] at h;exact hP (pY (cN _ e4) h) [] rfl e5 e6
lemma bB {u} {m cap:Nat} {p:Nat->Nat} {ws:List aQ} (low:∀ q,aR u (aN q) (ac q) (p q)) (ci:aZ) (ok:fW m ci p=true) (cut:(decide ws.Nodup&&jF u (dC ci.1 ci.2.1) ci.2.2.2.2 cap 0 (aN (eZ m ci)) ws)=true):aB u (ac m) cap ws.toFinset:=by
 simp only [and_eq_true,decide_eq_true_eq] at cut;exact hP (en ci p low ok) [] rfl cut.1 cut.2
lemma eu {u} {g:aM} {m cap i:Nat} {prior:Nat->Nat} {ws:List aQ} (hm:g.m=m) (hu:g.u=u) (low:∀ q,aR u (aN q) (ac q) (prior q)) (geom:aD g prior=true) (blocks:bo g cap) (idx:dl g cap i ws=true):aB u (ac m) cap ws.toFinset:=by
 subst hm;subst hu;exact gk low geom blocks (Nat.le_refl _) idx
def yN (m hints:Nat):Bool:=
 let xs:=fu m hints
 cE (ac m)&&bZ (ac m) (cB m) xs&&(xs.map Prod.fst==cB m)
lemma cD {u} {m b cap:Nat} (ok:yN m b=true) (a:aB u (ac m) cap (cB m).toFinset):aR u (cB m) (ac m) (cap+1):=by
 simp only [yN,and_eq_true,beq_iff_eq] at ok;apply i4 (cN _ ok.1.1) (cg ok.1.2).1 (cg ok.1.2).2 _ a;intro v hv;apply eW ok.1.2 v;rw [ok.2];exact mem_toFinset.mpr hv
end
def jP (r : @bW ⟨false⟩) : @bW ⟨true⟩:=⟨r.val,Nat.lt_trans r.isLt (by decide)⟩
lemma gT (j:Fin 9):au jP (@aG ⟨true⟩ ((@inputs ⟨true⟩).getD j.val (@zero ⟨true⟩))) = @aG ⟨false⟩ ((@inputs ⟨false⟩).getD j.val (@zero ⟨false⟩)):=by
 funext r
 simp only [au,aG,jP]
 exact (@ee ⟨true⟩ ⟨j.val,Nat.lt_trans j.isLt (by decide)⟩ ⟨r.val,Nat.lt_trans r.isLt (by decide)⟩).trans
  (@ee ⟨false⟩ j r).symm
lemma jt {q:Nat} (j:Fin 9):au jP (@aG ⟨true⟩ (@eB ⟨true⟩ q j.val)) = @aG ⟨false⟩ (@eB ⟨false⟩ q j.val):=by
 by_cases ht:q.testBit j.val=true
 . simp only [eB,ht,ite_true];exact gT j
 . simp only [eB,ht,ite_false];funext r;simp [au,aG,cn]
lemma kM {q:Nat} (hq:q<512):((@aN ⟨true⟩ q).map (@aG ⟨true⟩)).map (au jP)=(@aN ⟨false⟩ q).map (@aG ⟨false⟩):=by
 have hq9:q.testBit 9=false:=Nat.testBit_eq_false_of_lt hq;have hvars : @aN ⟨true⟩ q = @cB ⟨true⟩ q:=rfl
 have hvars9 : @aN ⟨false⟩ q = @cB ⟨false⟩ q:=by simp [aN,hq]
 rw [hvars,hvars9]
 have hsel:(@dt ⟨true⟩ q).map (fun e=>au jP (@aG ⟨true⟩ e.2))=(@dt ⟨false⟩ q).map (fun e => @aG ⟨false⟩ e.2):=by
  change ((List.range 10).filterMap (fun i=>if q.testBit i=true then some (i,(@inputs ⟨true⟩).getD i (@zero ⟨true⟩)) else none)).map (fun e=>au jP (@aG ⟨true⟩ e.2)) =
   ((List.range 9).filterMap (fun i=>if q.testBit i=true then some (i,(@inputs ⟨false⟩).getD i (@zero ⟨false⟩)) else none)).map (fun e => @aG ⟨false⟩ e.2)
  rw [List.range_succ,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,hq9];simp only [false_eq_true,ite_false,List.append_nil]
  have go:∀ l:List Nat,(∀ i ∈ l,i<9)  ->
   (l.filterMap (fun i=>if q.testBit i=true then some (i,(@inputs ⟨true⟩).getD i (@zero ⟨true⟩)) else none)).map (fun e=>au jP (@aG ⟨true⟩ e.2)) =
   (l.filterMap (fun i=>if q.testBit i=true then some (i,(@inputs ⟨false⟩).getD i (@zero ⟨false⟩)) else none)).map (fun e => @aG ⟨false⟩ e.2):=by
   intro l hl
   induction l with
   | nil=>rfl
   | cons i l ih =>
    simp only [List.filterMap_cons]
    by_cases ht:q.testBit i=true
    . simp only [ht,ite_true,map_cons];exact congrArg₂ List.cons (gT ⟨i,hl i mem_cons_self⟩) (ih (fun x hx=>hl x (mem_cons_of_mem _ hx)))
    . simp only [ht,ite_false];exact ih (fun x hx=>hl x (mem_cons_of_mem _ hx))
  exact go (List.range 9) (fun _ h=>mem_range.mp h)
 simpa only [cB,map_map,Function.comp_def] using hsel
lemma k3 {q:Nat} (hq:q<512):au jP (@aG ⟨true⟩ (@ac ⟨true⟩ q)) = @aG ⟨false⟩ (@ac ⟨false⟩ q):=by
 have hq9:q.testBit 9=false:=Nat.testBit_eq_false_of_lt hq
 have hv9 : @eB ⟨true⟩ q 9=0:=by simp [eB,hq9,zero]
 funext r
 have pos (j:Nat) (hj:j<9):
  (@eB ⟨true⟩ q j).getLsbD r.val=(@eB ⟨false⟩ q j).getLsbD r.val:=
  congrFun (jt ⟨j,hj⟩) r
 simp [au,aG,ac,hv9,aV,jP,
  pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),
  pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
lemma fG {u q L} (hq:q<512) (h : @aR ⟨false⟩ u (@aN ⟨false⟩ q) (@ac ⟨false⟩ q) L) : @aR ⟨true⟩ u (@aN ⟨true⟩ q) (@ac ⟨true⟩ q) L:=by
 intro p bank hr ha;have hr':=kK jP hr;have ha':=fk jP ha;rw [kM hq] at hr';rw [k3 hq] at ha';exact h p _ hr' ha'
end
end Core
namespace S9
noncomputable section
open PEqualNP.Outside.L_meta_6026.Core
local instance : Width := ⟨false⟩
def wQ (m:Nat) (rs:List Nat):List (aQ × bW × bW):=((dt m).zip rs).map fun x=>(x.1.2,Fin.ofNat 512 x.2,Fin.ofNat 512 (x.2|||(1<<<x.1.1)))
def mh (m:Nat) (rs:List Nat):Bool:=
 let xs:=wQ m rs
 bZ (ac m) (aN m) xs&&(xs.map Prod.fst==cB m) &&
  cE (ac m)&&decide (aN m=cB m ++ [iJ (m/512-1)])
lemma oL {u} {m:Nat} {rs:List Nat} (ok:mh m rs=true) {k:Nat} {S:Finset aQ} (h:cL u (ac m) k S) (sub:∀ v ∈ S,v ∈ aN m):S=(cB m).toFinset\/S=(aN m).toFinset:=by
 simp only [mh,and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok;obtain ⟨⟨⟨ess,alls⟩,_⟩,hX⟩:=ok
 have rest:∀ v ∈ cB m,v ∈ S:=by
  intro v hv;rw [<-alls] at hv;obtain ⟨r,s,hd,hi⟩:=eW ess v (mem_toFinset.mpr hv);exact cX h (aN m) v sub r s hd hi
 have mem:∀ v,v ∈ aN m ↔ v ∈ cB m\/v=iJ (m/512-1):=by
  intro v;rw [hX];simp
 by_cases hs:iJ (m/512-1) ∈ S
 . refine Or.inr ?_
   ext v
   rw [mem_toFinset]
   refine ⟨sub v,fun hv => ?_⟩
   rcases (mem v).mp hv with hv|rfl
   . exact rest v hv
   . exact hs
 . refine Or.inl ?_
   ext v
   rw [mem_toFinset]
   refine ⟨fun hv => ?_,rest v⟩
   rcases (mem v).mp (sub v hv) with hv|rfl
   . exact hv
   . exact absurd hv hs
lemma aA {u} {m q cap:Nat} {rs:List Nat} (ok:mh m rs=true) (e:ac m=ac q) (ev:cB m=cB q) (a:aB u (ac q) cap (cB q).toFinset) (b:aB u (ac q) cap (aN m).toFinset):aR u (aN m) (ac m) (cap+1):=by
 have ok':=ok;simp only [mh,and_eq_true] at ok';intro p bank hr ha;obtain ⟨k,S,hk,run,hs⟩:=gg (cN _ ok'.1.2) (cg ok'.1.1.1).1 (cg ok'.1.1.1).2 hr ha
 by_contra! small
 rcases oL ok run hs with h|h
 . rw [ev] at h;rw [e,h] at run;exact a k (by omega) run
 . rw [e,h] at run;exact b k (by omega) run
structure d9 (S:Finset aQ) (T:aQ) where
 owns:aQ->bW->bW->Prop
 total:∀ p n,aV p T=true->aV n T=false->∃ v,owns v p n
 valid:∀ {v p n},owns v p n->v∈S/\aV p v=true/\aV n v=false
 unique:∀ {v w p n},owns v p n->owns w p n->v=w
 rect:∀ {v p n p' n'},owns v p n'->owns v p' n->owns v p n
def o7 (T:aQ):d9 {T} T where
 owns v p n:=v=T/\aV p T=true/\aV n T=false
 total p n hp hn:=⟨T,rfl,hp,hn⟩
 valid:=by rintro v p n ⟨rfl,hp,hn⟩;exact ⟨by simp,hp,hn⟩
 unique:=by rintro v w p n ⟨rfl,_,_⟩ ⟨eq,_,_⟩;exact eq.symm
 rect:=by rintro v p n p' n' ⟨e,hp,_⟩ ⟨_,_,hn⟩;exact ⟨e,hp,hn⟩
def vE {U:Finset aQ} {T a b:aQ} {d:Nat} (d01:d=0\/d=1) (ha:a∉U) (hb:b∉U) (hz:bM d a b∉U) (H:d9 (insert (bM d a b) U) T):d9 (insert a (insert b U)) T:=by
 let z:=bM d a b
 let sel:=fun p n:bW=>if d=0 then (if aV n a then b else a)
  else (if aV p a then a else b)
 have pick (p n):sel p n=a\/sel p n=b:=by
  dsimp only [sel];split<;>split<;>simp
 have outside (p n):sel p n ∉ U:=by
  rcases pick p n with eq|eq
  . simpa only [eq] using ha
  . simpa only [eq] using hb
 have separates (p n) (hp:aV p z=true) (hn:aV n z=false):
  aV p (sel p n)=true/\aV n (sel p n)=false:=by
  have b0 (r:bW):aV r (bM 0 a b)=(aV r a&&aV r b):=by simp [bM,aV]
  have b1 (r:bW):aV r (bM 1 a b)=(aV r a||aV r b):=by simp [bM,aV]
  rcases d01 with e|e<;>cases pA:aV p a<;>cases nA:aV n a <;>
   simp_all [sel,z]
 refine { owns:=fun v p n=>(v∈U/\H.owns v p n)\/(v=sel p n/\H.owns z p n)
          total := ?_
          valid := ?_
          unique := ?_
          rect := ?_ }
 . intro p n hp hn;obtain ⟨v,hv⟩:=H.total p n hp hn
   rcases mem_insert.mp (H.valid hv).1 with eq|mem
   . have vz:v=z:=eq
     refine ⟨sel p n,Or.inr ⟨rfl,?_⟩⟩
     rw [<-vz];exact hv
   . exact ⟨v,Or.inl ⟨mem,hv⟩⟩
 . intro v p n h
   rcases h with ⟨mem,hv⟩|⟨e,hv⟩
   . exact ⟨mem_insert_of_mem (mem_insert_of_mem mem),(H.valid hv).2⟩
   . subst v
     have inS:sel p n ∈ insert a (insert b U):=by
      rcases pick p n with eq|eq<;>simp [eq]
     exact ⟨inS,separates p n (H.valid hv).2.1 (H.valid hv).2.2⟩
 . intro v w p n h1 h2
   rcases h1 with ⟨vU,hv⟩|⟨ve,hv⟩<;>rcases h2 with ⟨wU,hw⟩|⟨we,hw⟩
   . exact H.unique hv hw
   . apply False.elim;apply hz;change z∈U;rw [<-H.unique hv hw];exact vU
   . apply False.elim;apply hz;change z∈U;rw [<-H.unique hw hv];exact wU
   . exact ve.trans we.symm
 . intro v p n p' n' h1 h2
   rcases h1 with ⟨vU,hv⟩|⟨ve,hv⟩<;>rcases h2 with ⟨wU,hw⟩|⟨we,hw⟩
   . exact Or.inl ⟨vU,H.rect hv hw⟩
   . exact False.elim (outside p' n (we ▸ vU))
   . exact False.elim (outside p n' (ve ▸ wU))
   . refine Or.inr ⟨?_,H.rect hv hw⟩
     by_cases h:d=0
     . simpa only [sel,h,ite_true] using we
     . simpa only [sel,h,ite_false] using ve
lemma ml {u T k S} (h:cL u T k S):S.card ≤ k+1:=by
 induction h using cL.ind with
 | stop hp=>simp
 | @binary k U a b d hd ha hb hab hf tail ih =>
  have hu:bM d a b ∉ U:=fun hm=>hf (mem_insert_of_mem (mem_insert_of_mem hm));rw [card_insert_of_notMem hu] at ih;have h1:=Finset.card_insert_le (a:=a) (insert b U);have h2:=Finset.card_insert_le (a:=b) U;omega
lemma mj {T k S} (run:cL false T k S) (tight:S.card=k+1):Nonempty (d9 S T):=by
 induction k generalizing S with
 | zero =>
  obtain ⟨rfl,_⟩:=run;exact ⟨o7 T⟩
 | succ k ih =>
  obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩:=run;have fresh:bM d a b∉U:=fun h=>hfresh (mem_insert_of_mem (mem_insert_of_mem h));have li:=ml tail;rw [card_insert_of_notMem fresh] at li;have le1:=Finset.card_insert_le (a:=a) (insert b U);have le2:=Finset.card_insert_le (a:=b) U
  have ha:a∉U:=by
   intro h;rw [Finset.insert_eq_of_mem (mem_insert_of_mem h:a∈insert b U)] at tight;omega
  have hb:b∉U:=by
   intro h;rw [Finset.insert_eq_of_mem h] at tight le1;omega
  have eq:(insert (bM d a b) U).card=k+1:=by
   rw [card_insert_of_notMem fresh];omega
  obtain ⟨H⟩:=ih tail eq
  have d01:d=0\/d=1:=by rcases hd with h|⟨h,_⟩<;>simp_all<;>omega
  exact ⟨vE d01 ha hb fresh H⟩
def bD (S:Finset aQ) (T v:aQ) (p n:bW):=aV p T=true/\aV n T=false/\∀ w∈S,aV p w=true->aV n w=false->w=v
lemma jf {S T v p n} (H:d9 S T) (one:bD S T v p n):H.owns v p n:=by
 obtain ⟨w,hw⟩:=H.total p n one.1 one.2.1;have eq:=one.2.2 w (H.valid hw).1 (H.valid hw).2.1 (H.valid hw).2.2;exact eq ▸ hw
lemma xA {S T k a b p n pa pb na nb} (size:k+1=S.card) (different:a≠b) (A:bD S T a p na) (B:bD S T b p nb) (C:bD S T a pa n) (D:bD S T b pb n):aB false T k S:=by
 intro j hj run;have lb:=ml run
 have tight:S.card=j+1:=by omega
 obtain ⟨H⟩:=mj run tight;exact different (H.unique (H.rect (jf H A) (jf H C)) (H.rect (jf H B) (jf H D)))
structure dP (S:Finset aQ) (T H:aQ) where
 owns:aQ->bW->bW->Prop
 total:∀ p n,aV p T=true->aV n T=false  ->
  (aV p H=true/\aV n H=false)\/∃ v,owns v p n
 valid:∀ {v p n},owns v p n->v∈S/\aV p v=true/\aV n v=false
 unique:∀ {v w p n},owns v p n->owns w p n->v=w
 rect:∀ {v p n p' n'},owns v p n'->owns v p' n->owns v p n
structure bF (S:Finset aQ) (T:aQ) where
 inner:Finset aQ
 outer:Finset aQ
 pivot:aQ
 cover:inner ∪ outer=S
 apart:Disjoint inner outer
 inside:d9 inner pivot
 outside:dP outer T pivot
def uc {S T} (D:d9 S T) (h:aQ):dP S T h where
 owns:=D.owns
 total p n hp hn:=Or.inr (D.total p n hp hn)
 valid:=D.valid
 unique:=D.unique
 rect:=D.rect
def mZ {S T h} (D:dP S T h):dP (S.erase h) T h where
 owns v p n:=v≠h/\D.owns v p n
 total:=by
  intro p n hp hn
  rcases D.total p n hp hn with yes|⟨v,hv⟩
  . exact Or.inl yes
  . by_cases eq:v=h
    . exact Or.inl (eq ▸ (D.valid hv).2)
    . exact Or.inr ⟨v,eq,hv⟩
 valid:=by
  rintro v p n ⟨ne,hv⟩
  exact ⟨mem_erase.mpr ⟨ne,(D.valid hv).1⟩,(D.valid hv).2⟩
 unique:=fun h1 h2=>D.unique h1.2 h2.2
 rect:=fun a b=>⟨a.1,D.rect a.2 b.2⟩
def md {S T} (D:d9 S T):bF S T where
 inner:=S
 outer := ∅
 pivot:=T
 cover:=by simp
 apart:=by simp
 inside:=D
 outside:={
  owns:=fun _ _ _=>False
  total:=fun p n hp hn=>Or.inl ⟨hp,hn⟩
  valid:=fun h=>h.elim
  unique:=fun h _=>h.elim
  rect:=fun h _=>h.elim }
def mY {h:aQ} {U:Finset aQ} {T a b:aQ} {d:Nat} (d01:d=0\/d=1) (ha:a∉U) (hb:b∉U) (hz:bM d a b∉U) (H:dP (insert (bM d a b) U) T h):dP (insert a (insert b U)) T h:=by
 let z:=bM d a b
 let sel:=fun p n:bW=>if d=0 then (if aV n a then b else a)
  else (if aV p a then a else b)
 have pick (p n):sel p n=a\/sel p n=b:=by
  dsimp only [sel];split<;>split<;>simp
 have outside (p n):sel p n ∉ U:=by
  rcases pick p n with eq|eq
  . simpa only [eq] using ha
  . simpa only [eq] using hb
 have separates (p n) (hp:aV p z=true) (hn:aV n z=false):
  aV p (sel p n)=true/\aV n (sel p n)=false:=by
  have b0 (r:bW):aV r (bM 0 a b)=(aV r a&&aV r b):=by simp [bM,aV]
  have b1 (r:bW):aV r (bM 1 a b)=(aV r a||aV r b):=by simp [bM,aV]
  rcases d01 with e|e<;>cases pA:aV p a<;>cases nA:aV n a <;>
   simp_all [sel,z]
 refine { owns:=fun v p n=>(v∈U/\H.owns v p n)\/(v=sel p n/\H.owns z p n)
          total := ?_
          valid := ?_
          unique := ?_
          rect := ?_ }
 . intro p n hp hn
   rcases H.total p n hp hn with closed|⟨v,hv⟩
   . exact Or.inl closed
   right
   rcases mem_insert.mp (H.valid hv).1 with eq|mem
   . have vz:v=z:=eq
     refine ⟨sel p n,Or.inr ⟨rfl,?_⟩⟩
     rw [<-vz];exact hv
   . exact ⟨v,Or.inl ⟨mem,hv⟩⟩
 . intro v p n h
   rcases h with ⟨mem,hv⟩|⟨e,hv⟩
   . exact ⟨mem_insert_of_mem (mem_insert_of_mem mem),(H.valid hv).2⟩
   . subst v
     have inS:sel p n ∈ insert a (insert b U):=by
      rcases pick p n with eq|eq<;>simp [eq]
     exact ⟨inS,separates p n (H.valid hv).2.1 (H.valid hv).2.2⟩
 . intro v w p n h1 h2
   rcases h1 with ⟨vU,hv⟩|⟨ve,hv⟩<;>rcases h2 with ⟨wU,hw⟩|⟨we,hw⟩
   . exact H.unique hv hw
   . apply False.elim;apply hz;change z∈U;rw [<-H.unique hv hw];exact vU
   . apply False.elim;apply hz;change z∈U;rw [<-H.unique hw hv];exact wU
   . exact ve.trans we.symm
 . intro v p n p' n' h1 h2
   rcases h1 with ⟨vU,hv⟩|⟨ve,hv⟩<;>rcases h2 with ⟨wU,hw⟩|⟨we,hw⟩
   . exact Or.inl ⟨vU,H.rect hv hw⟩
   . exact False.elim (outside p' n (we ▸ vU))
   . exact False.elim (outside p n' (ve ▸ wU))
   . refine Or.inr ⟨?_,H.rect hv hw⟩
     by_cases h:d=0
     . simpa only [sel,h,ite_true] using we
     . simpa only [sel,h,ite_false] using ve
lemma jn {A B U:Finset aQ} {a b z:aQ} (e:A∪B=insert z U) (disj:Disjoint A B) (za:z∈A) (freshA:a∉insert z U) (freshB:b∉insert z U) (freshZ:z∉U):(insert a (insert b (A.erase z))) ∪ B=insert a (insert b U)/\Disjoint (insert a (insert b (A.erase z))) B/\a∉A.erase z/\b∉A.erase z:=by
 have hb:z∉B:=fun h=>Finset.disjoint_left.mp disj za h
 have allmem (w:aQ):w∈A\/w∈B ↔ w=z\/w∈U:=by
  rw [<-mem_union,<-mem_insert,e]
 have aout:a∉A/\a∉B:=by
  have h:a∉A∪B:=by rw [e];exact freshA
  simpa using h
 have bout:b∉A/\b∉B:=by
  have h:b∉A∪B:=by rw [e];exact freshB
  simpa using h
 refine ⟨?_,?_,fun h=>aout.1 (Finset.mem_of_mem_erase h),fun h=>bout.1 (Finset.mem_of_mem_erase h)⟩
 . ext w
   have m:=allmem w
   by_cases eq:w=z
   . subst w;simp [freshZ,hb]
   . simp only [mem_union,mem_insert,mem_erase] at *
     tauto
 . apply Finset.disjoint_left.mpr;intro w hw hwB
   rcases mem_insert.mp hw with rfl|hw
   . exact aout.2 hwB
   rcases mem_insert.mp hw with rfl|hw
   . exact bout.2 hwB
   exact Finset.disjoint_left.mp disj (Finset.mem_of_mem_erase hw) hwB
def mb {U T a b d} (hd:d=0\/d=1) (freshA:a∉insert (bM d a b) U) (freshB:b∉insert (bM d a b) U) (freshZ:bM d a b∉U) (F:bF (insert (bM d a b) U) T):bF (insert a (insert b U)) T:=by
 classical
 let z:=bM d a b
 by_cases inn:z∈F.inner
 . obtain ⟨eq,apart,ha,hb⟩:=jn F.cover F.apart inn freshA freshB freshZ
   have old:d9 (insert z (F.inner.erase z)) F.pivot:=by
    rw [insert_erase inn];exact F.inside
   exact ⟨_,F.outer,F.pivot,eq,apart,vE hd ha hb (by simp [z]) old,F.outside⟩
 . have out:z∈F.outer:=by
    have m:z∈F.inner∪F.outer:=by rw [F.cover];exact mem_insert_self _ _
    exact (mem_union.mp m).resolve_left inn
   obtain ⟨eq,apart,ha,hb⟩:=jn ((Finset.union_comm _ _).trans F.cover) F.apart.symm out freshA freshB freshZ
   have old:dP (insert z (F.outer.erase z)) T F.pivot:=by
    rw [insert_erase out];exact F.outside
   exact ⟨F.inner,_,F.pivot,(Finset.union_comm _ _).trans eq,apart.symm,F.inside,
    mY hd ha hb (by simp [z]) old⟩
def jQ {U T a b d} (hd:d=0\/d=1) (ab:a≠b) (hb:b∉U) (fresh:bM d a b∉insert a (insert b U)) (H:d9 (insert (bM d a b) U) T):bF (insert a (insert b U)) T:=by
 let z:=bM d a b
 have za:z≠a:=by
  intro eq;apply fresh;exact mem_insert.mpr (Or.inl eq)
 have zU:z∉U:=fun h=>fresh (mem_insert_of_mem (mem_insert_of_mem h))
 have set0:(insert z U).erase a=insert z (U.erase a):=by
  ext v
  simp only [mem_erase,mem_insert]
  by_cases eq:v=z
  . subst v;simp [za]
  . tauto
 have H0:dP (insert z (U.erase a)) T a:=set0 ▸ mZ (uc H a)
 have H1:=mY hd (show a∉U.erase a by simp)
  (fun m=>hb (Finset.mem_of_mem_erase m)) (fun m=>zU (Finset.mem_of_mem_erase m)) H0
 have eq:insert a (insert b (U.erase a))=insert a (insert b U):=by
  ext v
  simp only [mem_insert,mem_erase]
  tauto
 have H1':dP (insert a (insert b U)) T a:=eq ▸ H1
 refine ⟨{a},(insert a (insert b U)).erase a,a,?_,?_,o7 a,mZ H1'⟩
 . ext v;simp only [mem_union,Finset.mem_singleton,mem_erase,mem_insert];tauto
 . simp
lemma wk {T k S} (r:cL false T k S) (budget:k≤S.card):Nonempty (bF S T):=by
 induction k generalizing S with
 | zero =>
  obtain ⟨rfl,_⟩:=r;exact ⟨md (o7 T)⟩
 | succ k ih =>
  obtain ⟨U,a,b,d,hd,rfl,_,_,ab,fresh,tail⟩:=r;let z:=bM d a b;have zU:z∉U:=fun m=>fresh (mem_insert_of_mem (mem_insert_of_mem m));have size:=ml tail;have zcard:(insert z U).card=U.card+1:=card_insert_of_notMem zU;change (insert z U).card ≤ k+1 at size
  have hd01:d=0\/d=1:=by rcases hd with q|⟨q,_⟩<;>simp_all<;>omega
  by_cases ain:a∈U
  . rw [Finset.insert_eq_of_mem (mem_insert_of_mem ain:a∈insert b U)] at budget
    by_cases bM':b∈U
    . rw [Finset.insert_eq_of_mem bM'] at budget;omega
    . rw [card_insert_of_notMem bM'] at budget;obtain ⟨H⟩:=mj tail (by change (insert z U).card=k+1;omega);exact ⟨jQ hd01 ab bM' fresh H⟩
  . by_cases bM':b∈U
    . rw [Finset.insert_eq_of_mem bM',card_insert_of_notMem ain] at budget;obtain ⟨H⟩:=mj tail (by change (insert z U).card=k+1;omega)
      have comm:bM d b a=z:=by
       rcases hd01 with eq|eq<;>subst d<;>simp [z,bM,BitVec.and_comm,BitVec.or_comm]
      have H':d9 (insert (bM d b a) U) T:=by simpa only [comm] using H
      have fr:bM d b a∉insert b (insert a U):=by simpa only [comm,Finset.insert_comm] using fresh
      have F:=jQ hd01 ab.symm ain fr H';exact ⟨by simpa only [Finset.insert_comm] using F⟩
    . have an:a∉insert b U:=by simp [ain,ab]
      rw [card_insert_of_notMem an,card_insert_of_notMem bM'] at budget;obtain ⟨F⟩:=ih tail (by change k≤(insert z U).card;omega);have neA:a≠z:=fun e=>fresh (mem_insert.mpr (Or.inl e.symm));have neB:b≠z:=fun e=>fresh (mem_insert_of_mem (mem_insert.mpr (Or.inl e.symm)))
      have fa:a∉insert z U:=fun h=>(mem_insert.mp h).elim neA ain
      have fb:b∉insert z U:=fun h=>(mem_insert.mp h).elim neB bM';exact ⟨mb hd01 fa fb zU F⟩
lemma mc {S:Finset aQ} {T:aQ} (F:bF S T) (p n:bW) (hp:aV p T=true) (hn:aV n T=false) (none:∀ v∈F.outer,aV p v=true->aV n v=false->False):aV p F.pivot=true/\aV n F.pivot=false:=by
 rcases F.outside.total p n hp hn with h|⟨v,hv⟩
 . exact h
 . exact False.elim (none v (F.outside.valid hv).1 (F.outside.valid hv).2.1 (F.outside.valid hv).2.2)
lemma ed {S:Finset aQ} {T:aQ} (F:bF S T) {a p n} (ao:a∈F.outer) (one:bD S T a p n):F.outside.owns a p n:=by
 rcases F.outside.total p n one.1 one.2.1 with hpivot|⟨w,hw⟩
 . obtain ⟨w,hw⟩:=F.inside.total p n hpivot.1 hpivot.2;obtain ⟨wi,wp,wn⟩:=F.inside.valid hw;have ws:w∈S:=F.cover ▸ Finset.mem_union_left _ wi;have eq:=one.2.2 w ws wp wn;rw [eq] at wi;exact False.elim (Finset.disjoint_left.mp F.apart wi ao)
 . obtain ⟨wo,wp,wn⟩:=F.outside.valid hw;have ws:w∈S:=F.cover ▸ Finset.mem_union_right _ wo;have eq:=one.2.2 w ws wp wn;exact eq ▸ hw
lemma i7 {S:Finset aQ} {T:aQ} (F:bF S T) {a b p n pa pb na nb} (aout:a∈F.outer) (bout:b∈F.outer) (different:a≠b) (A:bD S T a p na) (B:bD S T b p nb) (C:bD S T a pa n) (D:bD S T b pb n):False:=
 different (F.outside.unique (F.outside.rect (ed F aout A) (ed F aout C))
  (F.outside.rect (ed F bout B) (ed F bout D)))
lemma i2 {S:Finset aQ} {T:aQ} (F:bF S T) {a b p n pa pb na nb} (different:a≠b) (A:bD F.inner F.pivot a p na) (B:bD F.inner F.pivot b p nb) (C:bD F.inner F.pivot a pa n) (D:bD F.inner F.pivot b pb n):False:=
 different (F.inside.unique (F.inside.rect (jf F.inside A) (jf F.inside C))
  (F.inside.rect (jf F.inside B) (jf F.inside D)))
lemma d7 {S:Finset aQ} {T:aQ} (F:bF S T) {v p n} (hv:v∈F.inner) (only:bD S T v p n):bD F.inner F.pivot v p n:=by
 have h:aV p F.pivot=true/\aV n F.pivot=false:=by
  apply mc F p n only.1 only.2.1;intro w wo hp hn;have ws:w∈S:=F.cover ▸ Finset.mem_union_right _ wo;have eq:=only.2.2 w ws hp hn;exact Finset.disjoint_left.mp F.apart hv (eq ▸ wo)
 refine ⟨h.1,h.2,?_⟩
 intro w wi hp hn;exact only.2.2 w (F.cover ▸ Finset.mem_union_left _ wi) hp hn
lemma bC {S:Finset aQ} {T:aQ} (F:bF S T) {a b c p n pa na} (ar:bD S T a p na) (br:bD S T b pa n) (cr:bD S T c p n) (ia:a∈F.inner) (ib:b∈F.inner):c∈F.inner:=by
 have ah:=d7 F ia ar;have bh:=d7 F ib br;obtain ⟨w,hw⟩:=F.inside.total p n ah.1 bh.2.1;obtain ⟨wi,wp,wn⟩:=F.inside.valid hw;have ws:w∈S:=F.cover ▸ Finset.mem_union_left _ wi;exact (cr.2.2 w ws wp wn) ▸ wi
lemma bO {S:Finset aQ} {T:aQ} (F:bF S T) {a b p n pa pb na nb} (hs:a∈S) (ht:b∈S) (ne:a≠b) (h1:bD S T a p na) (h2:bD S T b p nb) (h3:bD S T a pa n) (h4:bD S T b pb n):((a∈F.inner/\b∈F.inner)\/(a∉F.inner/\b∉F.inner))->False:=by
 rintro (⟨ia,ib⟩|⟨oa,ob⟩)
 . exact i2 F ne (d7 F ia h1) (d7 F ib h2)
    (d7 F ia h3) (d7 F ib h4)
 . rw [<-F.cover,mem_union] at hs ht;exact i7 F (hs.resolve_left oa) (ht.resolve_left ob) ne h1 h2 h3 h4
def f9 (ws:List aQ) (T v:aQ) (p n:bW):Bool:=aV p T && !aV n T&&ws.all (fun w => !aV p w||aV n w||w==v)
lemma dX {ws T v p n} (h:f9 ws T v p n=true):bD ws.toFinset T v p n:=by
 simp only [f9,and_eq_true,Bool.not_eq_true',all_eq_true] at h
 refine ⟨h.1.1,h.1.2,?_⟩
 intro w hw hp hn
 simpa only [hp,hn,Bool.not_true,Bool.false_or,beq_iff_eq] using
  h.2 w (mem_toFinset.mp hw)
def fF (xs q:Nat):bW:=Fin.ofNat 512 ((xs>>>(9*q))&&&511)
def kl (pos eh:Nat) (T:aQ) (ws:List aQ) (k value:Nat):Bool:=
 let field:=fun i=>(value>>>(4*i))&&&15
 let a:=ws.getD (field 0) zero
 let b:=ws.getD (field 1) zero
 let p:=fF pos (field 2)
 let n:=fF eh (field 3)
 decide (k+1=ws.toFinset.card)&&decide (a≠b) &&
  f9 ws T a p (fF eh (field 4))&&f9 ws T b p (fF eh (field 5)) &&
  f9 ws T a (fF pos (field 6)) n&&f9 ws T b (fF pos (field 7)) n
lemma iC {pos eh T ws k v} (h:kl pos eh T ws k v=true):aB false T k ws.toFinset:=by
 simp only [kl,and_eq_true,decide_eq_true_eq] at h
 exact xA h.1.1.1.1.1 h.1.1.1.1.2 (dX h.1.1.1.2)
  (dX h.1.1.2) (dX h.1.2) (dX h.2)
def ag (g:aM) (k start n:Nat):Prop := ∀ j,start≤j->j<start+n->cW g k j=true\/aB g.u (aY g) k (bK g k j).toFinset
lemma cZ (g:aM) (k a:Nat):ag g k a 0:=by
 intro j lo hi;omega
lemma bR {g k a n} (h:aP g k a n=true):ag g k a n:=fun j lo hi=>Or.inl (ik h j lo hi)
lemma aw {g k a x y} (first:ag g k a x) (last:ag g k (a+x) y):ag g k a (x+y):=by
 intro j lo hi
 by_cases e:j<a+x
 . exact first j lo e
 . exact last j (by omega) (by omega)
def zQ (pos eh:Nat) (g:aM) (k a n:Nat) (data:Nat->Nat):=(List.range n).all (fun j=>kl pos eh (aY g) (bK g k (a+j)) k (bE data (32*j) 32))
lemma cJ {g k a n} (pos eh:Nat) (data:Nat->Nat) (mode:g.u=false) (h:zQ pos eh g k a n data=true):ag g k a n:=by
 intro j lo hi;right;rw [mode];have hh:=all_eq_true.mp h (j-a) (mem_range.mpr (by omega))
 have sum:a+(j-a)=j:=by omega
 change kl pos eh _ (bK g k (a+(j-a))) k _=true at hh;rw [sum] at hh;exact iC hh
def bT (g:aM) (top:Nat) := ∀ k ≤ top,ag g k 0 (g.l k).1
lemma nu (g:aM) (top:Nat) (prior:Nat->Nat) (lower:∀ q,aR g.u (aN q) (ac q) (prior q)) (geometry:aD g prior=true) (rows:bT g top):∀ k ≤ top,∀ i<(g.l k).1,aB g.u (aY g) k (bK g k i).toFinset:=by
 simp only [aD,and_eq_true,all_eq_true,beq_iff_eq] at geometry;intro k
 induction k with
 | zero =>
  intro hk i hi
  rcases rows 0 hk i (by omega) (by omega) with checked|done
  . exact dp g 0 i (eF geometry.1.1.1 geometry.1.1.2)
     (fun x hx=>en _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega) checked
  . exact done
 | succ k ih =>
  intro hk i hi
  rcases rows _ hk i (by omega) (by omega) with checked|done
  . exact dp g _ i (eF geometry.1.1.1 geometry.1.1.2)
     (fun x hx=>en _ prior lower (geometry.1.2 x hx)) geometry.2
     (fun _=>by simpa using ih (by omega)) checked
  . exact done
lemma lQ {g top prior k i ws} (lower:∀ q,aR g.u (aN q) (ac q) (prior q)) (geom:aD g prior=true) (blocks:bT g top) (le:k≤top) (idx:dl g k i ws=true):aB g.u (aY g) k ws.toFinset:=by
 simp only [dl,and_eq_true,decide_eq_true_eq] at idx;rw [<-d2 idx.2];exact nu g top prior lower geom blocks _ le i idx.1
abbrev ea:=Nat × Nat × Nat
def dm (arity:Nat) (tags:List ea):Prop:=
 ∀ {S T},(F:bF S T)->(w:Nat->aQ)->(p n:Nat->bW)  ->
  (∀ i<arity,w i∈S)->(∀ i<arity,∀ j<arity,i≠j->w i≠w j)  ->
  (∀ t∈tags,bD S T (w t.1) (p t.2.1) (n t.2.2))->False
structure jI where
 arity:Nat
 tags:List ea
 closed:dm arity tags
def rj:List ea:=[(0,0,2),(1,1,2),(2,2,3),(3,3,3),(0,4,1),(1,4,3),(2,5,0),(3,5,1),(3,5,2)]
lemma nw (A0 A1 A2 A3:Prop):(((A0/\A1)\/(¬A0/\¬A1))->False)->(((A2/\A3)\/(¬A2/\¬A3))->False)->(A1->A3->A0)->(A0->A2->A1)->(A0->A3->A1)->(A2->A1->A3)->False:=by
 intro r0 r1 r2 r3 r4 r5
 by_cases u1:A1
 . by_cases u0:A0
   . exact r0 (Or.inl ⟨u0,u1⟩)
   . by_cases u3:A3
     . exact u0 (r2 u1 u3)
     . by_cases u2:A2
       . exact u3 (r5 u2 u1)
       . exact r1 (Or.inr ⟨u2,u3⟩)
 . by_cases u0:A0
   . by_cases u3:A3
     . exact u1 (r4 u0 u3)
     . by_cases u2:A2
       . exact u1 (r3 u0 u2)
       . exact r1 (Or.inr ⟨u2,u3⟩)
   . exact r0 (Or.inr ⟨u0,u1⟩)
lemma z4:dm 4 rj:=by
 intro S T F w p n mem diff aE;have c0:=aE (0,0,2) (by decide);have c1:=aE (1,1,2) (by decide);have c2:=aE (2,2,3) (by decide);have c3:=aE (3,3,3) (by decide);have c4:=aE (0,4,1) (by decide);have c5:=aE (1,4,3) (by decide);have c6:=aE (2,5,0) (by decide);have c7:=aE (3,5,1) (by decide);have c8:=aE (3,5,2) (by decide);have r0:=bO F (mem 0 (by decide)) (mem 1 (by decide)) (diff 0 (by decide) 1 (by decide) (by decide)) c4 c5 c0 c1;have r1:=bO F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c6 c8 c2 c3;have r2:=bC F c5 c7 c4;have r3:=bC F c4 c2 c5;have r4:=bC F c4 c3 c5;have r5:=bC F c6 c1 c8;exact nw (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4 r5
def rk:List ea:=[(0,0,1),(1,1,3),(2,2,0),(1,2,2),(3,3,1),(2,3,3),(3,4,2),(0,4,3)]
lemma nx (A0 A1 A2 A3:Prop):(((A1/\A2)\/(¬A1/\¬A2))->False)->(((A0/\A3)\/(¬A0/\¬A3))->False)->(A2->A3->A1)->(A2->A0->A3)->(A3->A1->A2)->(A0->A1->A3)->False:=by
 intro r0 r1 r2 r3 r4 r5
 by_cases u3:A3
 . by_cases u0:A0
   . exact r1 (Or.inl ⟨u0,u3⟩)
   . by_cases u1:A1
     . by_cases u2:A2
       . exact r0 (Or.inl ⟨u1,u2⟩)
       . exact u2 (r4 u3 u1)
     . by_cases u2:A2
       . exact u1 (r2 u2 u3)
       . exact r0 (Or.inr ⟨u1,u2⟩)
 . by_cases u0:A0
   . by_cases u1:A1
     . exact u3 (r5 u0 u1)
     . by_cases u2:A2
       . exact u3 (r3 u2 u0)
       . exact r0 (Or.inr ⟨u1,u2⟩)
   . exact r1 (Or.inr ⟨u0,u3⟩)
lemma z5:dm 4 rk:=by
 intro S T F w p n mem diff aE;have c0:=aE (0,0,1) (by decide);have c1:=aE (1,1,3) (by decide);have c2:=aE (2,2,0) (by decide);have c3:=aE (1,2,2) (by decide);have c4:=aE (3,3,1) (by decide);have c5:=aE (2,3,3) (by decide);have c6:=aE (3,4,2) (by decide);have c7:=aE (0,4,3) (by decide);have r0:=bO F (mem 1 (by decide)) (mem 2 (by decide)) (diff 1 (by decide) 2 (by decide) (by decide)) c3 c2 c1 c5;have r1:=bO F (mem 0 (by decide)) (mem 3 (by decide)) (diff 0 (by decide) 3 (by decide) (by decide)) c7 c6 c0 c4;have r2:=bC F c2 c6 c3;have r3:=bC F c5 c0 c4;have r4:=bC F c4 c1 c5;have r5:=bC F c7 c3 c6;exact nx (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4 r5
def rl:List ea:=[(0,0,2),(1,1,1),(2,2,0),(1,2,2),(3,3,0),(0,3,1),(2,4,1),(3,4,2)]
lemma ny (A0 A1 A2 A3:Prop):(((A1/\A2)\/(¬A1/\¬A2))->False)->(((A0/\A3)\/(¬A0/\¬A3))->False)->(((A2/\A3)\/(¬A2/\¬A3))->False)->(A1->A3->A2)->(A2->A0->A1)->False:=by
 intro r0 r1 r2 r3 r4
 by_cases u2:A2
 . by_cases u1:A1
   . exact r0 (Or.inl ⟨u1,u2⟩)
   . by_cases u3:A3
     . exact r2 (Or.inl ⟨u2,u3⟩)
     . by_cases u0:A0
       . exact u1 (r4 u2 u0)
       . exact r1 (Or.inr ⟨u0,u3⟩)
 . by_cases u1:A1
   . by_cases u3:A3
     . exact u2 (r3 u1 u3)
     . exact r2 (Or.inr ⟨u2,u3⟩)
   . exact r0 (Or.inr ⟨u1,u2⟩)
lemma z6:dm 4 rl:=by
 intro S T F w p n mem diff aE;have c0:=aE (0,0,2) (by decide);have c1:=aE (1,1,1) (by decide);have c2:=aE (2,2,0) (by decide);have c3:=aE (1,2,2) (by decide);have c4:=aE (3,3,0) (by decide);have c5:=aE (0,3,1) (by decide);have c6:=aE (2,4,1) (by decide);have c7:=aE (3,4,2) (by decide);have r0:=bO F (mem 1 (by decide)) (mem 2 (by decide)) (diff 1 (by decide) 2 (by decide) (by decide)) c3 c2 c1 c6;have r1:=bO F (mem 0 (by decide)) (mem 3 (by decide)) (diff 0 (by decide) 3 (by decide) (by decide)) c5 c4 c0 c7;have r2:=bO F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c6 c7 c2 c4;have r3:=bC F c3 c4 c2;have r4:=bC F c2 c0 c3;exact ny (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4
def rm:List ea:=[(0,0,0),(1,1,0),(2,2,3),(3,3,3),(2,4,1),(3,4,2),(1,5,1),(1,5,2),(0,5,3)]
lemma nz (A0 A1 A2 A3:Prop):(((A2/\A3)\/(¬A2/\¬A3))->False)->(((A0/\A1)\/(¬A0/\¬A1))->False)->(A3->A1->A2)->(A2->A1->A3)->(A0->A2->A1)->(A0->A3->A1)->False:=by
 intro r0 r1 r2 r3 r4 r5
 by_cases u1:A1
 . by_cases u0:A0
   . exact r1 (Or.inl ⟨u0,u1⟩)
   . by_cases u2:A2
     . by_cases u3:A3
       . exact r0 (Or.inl ⟨u2,u3⟩)
       . exact u3 (r3 u2 u1)
     . by_cases u3:A3
       . exact u2 (r2 u3 u1)
       . exact r0 (Or.inr ⟨u2,u3⟩)
 . by_cases u0:A0
   . by_cases u2:A2
     . exact u1 (r4 u0 u2)
     . by_cases u3:A3
       . exact u1 (r5 u0 u3)
       . exact r0 (Or.inr ⟨u2,u3⟩)
   . exact r1 (Or.inr ⟨u0,u1⟩)
lemma z7:dm 4 rm:=by
 intro S T F w p n mem diff aE;have c0:=aE (0,0,0) (by decide);have c1:=aE (1,1,0) (by decide);have c2:=aE (2,2,3) (by decide);have c3:=aE (3,3,3) (by decide);have c4:=aE (2,4,1) (by decide);have c5:=aE (3,4,2) (by decide);have c6:=aE (1,5,1) (by decide);have c7:=aE (1,5,2) (by decide);have c8:=aE (0,5,3) (by decide);have r0:=bO F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c4 c5 c2 c3;have r1:=bO F (mem 0 (by decide)) (mem 1 (by decide)) (diff 0 (by decide) 1 (by decide) (by decide)) c8 c7 c0 c1;have r2:=bC F c5 c6 c4;have r3:=bC F c4 c7 c5;have r4:=bC F c8 c4 c6;have r5:=bC F c8 c5 c7;exact nz (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4 r5
def rp:List ea:=[(0,0,3),(1,1,3),(2,2,3),(3,3,3),(0,4,1),(1,4,2),(2,5,0),(3,5,1),(3,5,2)]
lemma nB (A0 A1 A2 A3:Prop):(((A0/\A1)\/(¬A0/\¬A1))->False)->(((A2/\A3)\/(¬A2/\¬A3))->False)->(A1->A3->A0)->(A0->A3->A1)->(A2->A0->A3)->(A2->A1->A3)->False:=by
 intro r0 r1 r2 r3 r4 r5
 by_cases u3:A3
 . by_cases u0:A0
   . by_cases u1:A1
     . exact r0 (Or.inl ⟨u0,u1⟩)
     . exact u1 (r3 u0 u3)
   . by_cases u1:A1
     . exact u0 (r2 u1 u3)
     . exact r0 (Or.inr ⟨u0,u1⟩)
 . by_cases u0:A0
   . by_cases u1:A1
     . exact r0 (Or.inl ⟨u0,u1⟩)
     . by_cases u2:A2
       . exact u3 (r4 u2 u0)
       . exact r1 (Or.inr ⟨u2,u3⟩)
   . by_cases u1:A1
     . by_cases u2:A2
       . exact u3 (r5 u2 u1)
       . exact r1 (Or.inr ⟨u2,u3⟩)
     . exact r0 (Or.inr ⟨u0,u1⟩)
lemma z8:dm 4 rp:=by
 intro S T F w p n mem diff aE;have c0:=aE (0,0,3) (by decide);have c1:=aE (1,1,3) (by decide);have c2:=aE (2,2,3) (by decide);have c3:=aE (3,3,3) (by decide);have c4:=aE (0,4,1) (by decide);have c5:=aE (1,4,2) (by decide);have c6:=aE (2,5,0) (by decide);have c7:=aE (3,5,1) (by decide);have c8:=aE (3,5,2) (by decide);have r0:=bO F (mem 0 (by decide)) (mem 1 (by decide)) (diff 0 (by decide) 1 (by decide) (by decide)) c4 c5 c0 c1;have r1:=bO F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c6 c8 c2 c3;have r2:=bC F c5 c7 c4;have r3:=bC F c4 c8 c5;have r4:=bC F c6 c4 c7;have r5:=bC F c6 c5 c8;exact nB (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4 r5
def rq:List ea:=[(0,0,2),(1,1,3),(2,2,0),(1,2,4),(3,3,1),(2,3,3),(0,3,4),(3,4,2),(4,4,3),(4,4,4)]
lemma nC (A0 A1 A2 A3 A4:Prop):(((A1/\A2)\/(¬A1/\¬A2))->False)->(((A0/\A3)\/(¬A0/\¬A3))->False)->(A2->A0->A1)->(A3->A1->A2)->(A0->A1->A2)->(A2->A4->A1)->(A3->A2->A4)->False:=by
 intro r0 r1 r2 r3 r4 r5 r6
 by_cases u2:A2
 . by_cases u1:A1
   . exact r0 (Or.inl ⟨u1,u2⟩)
   . by_cases u0:A0
     . exact u1 (r2 u2 u0)
     . by_cases u3:A3
       . by_cases u4:A4
         . exact u1 (r5 u2 u4)
         . exact u4 (r6 u3 u2)
       . exact r1 (Or.inr ⟨u0,u3⟩)
 . by_cases u1:A1
   . by_cases u0:A0
     . exact u2 (r4 u0 u1)
     . by_cases u3:A3
       . exact u2 (r3 u3 u1)
       . exact r1 (Or.inr ⟨u0,u3⟩)
   . exact r0 (Or.inr ⟨u1,u2⟩)
lemma z9:dm 5 rq:=by
 intro S T F w p n mem diff aE;have c0:=aE (0,0,2) (by decide);have c1:=aE (1,1,3) (by decide);have c2:=aE (2,2,0) (by decide);have c3:=aE (1,2,4) (by decide);have c4:=aE (3,3,1) (by decide);have c5:=aE (2,3,3) (by decide);have c6:=aE (0,3,4) (by decide);have c7:=aE (3,4,2) (by decide);have c8:=aE (4,4,3) (by decide);have c9:=aE (4,4,4) (by decide);have r0:=bO F (mem 1 (by decide)) (mem 2 (by decide)) (diff 1 (by decide) 2 (by decide) (by decide)) c3 c2 c1 c5;have r1:=bO F (mem 0 (by decide)) (mem 3 (by decide)) (diff 0 (by decide) 3 (by decide) (by decide)) c6 c4 c0 c7;have r2:=bC F c2 c6 c3;have r3:=bC F c4 c1 c5;have r4:=bC F c6 c1 c5;have r5:=bC F c2 c9 c3;have r6:=bC F c7 c5 c8;exact nC (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) (w 4∈F.inner) r0 r1 r2 r3 r4 r5 r6
def rr:List ea:=[(0,0,0),(1,1,0),(2,2,3),(2,3,1),(3,3,2),(1,4,2),(0,4,3),(1,5,1),(3,5,3)]
lemma nD (A0 A1 A2 A3:Prop):(((A2/\A3)\/(¬A2/\¬A3))->False)->(((A0/\A1)\/(¬A0/\¬A1))->False)->(((A1/\A3)\/(¬A1/\¬A3))->False)->(A2->A1->A3)->(A0->A3->A1)->False:=by
 intro r0 r1 r2 r3 r4
 by_cases u1:A1
 . by_cases u3:A3
   . exact r2 (Or.inl ⟨u1,u3⟩)
   . by_cases u0:A0
     . exact r1 (Or.inl ⟨u0,u1⟩)
     . by_cases u2:A2
       . exact u3 (r3 u2 u1)
       . exact r0 (Or.inr ⟨u2,u3⟩)
 . by_cases u3:A3
   . by_cases u0:A0
     . exact u1 (r4 u0 u3)
     . exact r1 (Or.inr ⟨u0,u1⟩)
   . exact r2 (Or.inr ⟨u1,u3⟩)
lemma Aa:dm 4 rr:=by
 intro S T F w p n mem diff aE;have c0:=aE (0,0,0) (by decide);have c1:=aE (1,1,0) (by decide);have c2:=aE (2,2,3) (by decide);have c3:=aE (2,3,1) (by decide);have c4:=aE (3,3,2) (by decide);have c5:=aE (1,4,2) (by decide);have c6:=aE (0,4,3) (by decide);have c7:=aE (1,5,1) (by decide);have c8:=aE (3,5,3) (by decide);have r0:=bO F (mem 2 (by decide)) (mem 3 (by decide)) (diff 2 (by decide) 3 (by decide) (by decide)) c3 c4 c2 c8;have r1:=bO F (mem 0 (by decide)) (mem 1 (by decide)) (diff 0 (by decide) 1 (by decide) (by decide)) c6 c5 c0 c1;have r2:=bO F (mem 1 (by decide)) (mem 3 (by decide)) (diff 1 (by decide) 3 (by decide) (by decide)) c7 c8 c5 c4;have r3:=bC F c3 c5 c4;have r4:=bC F c6 c4 c5;exact nD (w 0∈F.inner) (w 1∈F.inner) (w 2∈F.inner) (w 3∈F.inner) r0 r1 r2 r3 r4
def yf:Nat->jI
 | 0=>⟨4,rj,z4⟩
 | 1=>⟨4,rk,z5⟩
 | 2=>⟨4,rl,z6⟩
 | 3=>⟨4,rm,z7⟩
 | 4=>⟨4,rp,z8⟩
 | 5=>⟨5,rq,z9⟩
 | _=>⟨4,rr,Aa⟩
def pf (arity:Nat) (ws:List aQ) (w:Nat->aQ):=
 (List.range arity).all (fun i=>decide (w i∈ws) &&
  (List.range arity).all (fun j=>(i==j)||decide (w i≠w j)))
def kG (pc:jI) (ws:List aQ) (T:aQ) (w:Nat->aQ) (p n:Nat->bW):=
 pf pc.arity ws w &&
  pc.tags.all (fun t=>f9 ws T (w t.1) (p t.2.1) (n t.2.2))
lemma iG {a b:Bool} (h:(a&&b)=true):a=true/\b=true:=by simpa only [and_eq_true] using h
lemma h7 {pc ws T w p n} (F:bF (List.toFinset ws) T) (h:kG pc ws T w p n=true):False:=by
 have ij:=(iG h).1
 have hrow (i:Nat) (hi:i<pc.arity):=iG
  (all_eq_true.mp ij i (mem_range.mpr hi))
 apply pc.closed F w p n
 . intro i hi;exact mem_toFinset.mpr (of_decide_eq_true (hrow i hi).1)
 . intro i hi j hj ne;have one:=all_eq_true.mp (hrow i hi).2 j (mem_range.mpr hj);have diff:(i==j)=false:=beq_eq_false_iff_ne.mpr ne;simpa only [diff,Bool.false_or,decide_eq_true_eq] using one
 . intro t ht;exact dX (all_eq_true.mp (iG h).2 t ht)
def hB (pos eh:Nat) (ws:List aQ) (T:aQ) (k rec:Nat):=
 let field:=fun i=>(rec>>>(4*i))&&&15
 decide (k≤ws.toFinset.card)&&kG (yf (field 0)) ws T
  (fun i=>ws.getD (field (1+i)) zero)
  (fun i=>fF pos (field (6+i))) (fun i=>fF eh (field (12+i)))
lemma gy {pos eh ws T k rec} (ok:hB pos eh ws T k rec=true):aB false T k ws.toFinset:=by
 obtain ⟨bound,check⟩:=iG ok;intro j hj live;obtain ⟨F⟩:=wk live (hj.trans (of_decide_eq_true bound));exact h7 F check
def cA:Nat:=0x9050141084210842110c0300c03
def cz:Nat:=0xc9606290568325147434114642a
def jr (pos eh:Nat) (g:aM) (k start n:Nat) (data:Nat->Nat):=(List.range n).all (fun i=>hB pos eh (bK g k (start+i)) (aY g) k (bE data (68*i) 68))
lemma aL {g k start n} (pos eh:Nat) (data:Nat->Nat) (mode:g.u=false) (ok:jr pos eh g k start n data=true):ag g k start n:=by
 intro j lo hi;right;rw [mode];have h:=all_eq_true.mp ok (j-start) (mem_range.mpr (by omega))
 have e:start+(j-start)=j:=by omega
 change hB pos eh (bK g k (start+(j-start))) (aY g) k _=true at h;rw [e] at h;exact gy h
def ir (g:aM) (k i:Nat):Bool:=
 let ar:=(f1 g k i).2.2.length
 oV g k i 1 ar&&fC g k i 1 ar 0 ar
lemma gI {g k i} (h:ir g k i=true):cW g k i=true:=by
 simp only [ir,and_eq_true] at h;exact ik (lj h.1 h.2) i (Nat.le_refl i) (Nat.lt_succ_self i)
def iY (g:aM) (k start:Nat):Nat->Bool
 | 0=>true
 | n+1=>ir g k (start+n)&&iY g k start n
lemma bG {g k start n} (h:iY g k start n=true):ag g k start n:=by
 induction n with
 | zero=>exact bR rfl
 | succ n ih =>
  simp only [iY,and_eq_true] at h;exact aw (ih h.2) (bR (by simp [aP,gI h.1]))
def fO (pos eh:Nat) (g:aM) (k i:Nat) (kw panels:Nat->Nat) (tag:Nat):=
 if tag=0 then ir g k i else if tag<128 then
  kl pos eh (aY g) (bK g k i) k (bE kw (32*(tag-1)) 32)
 else hB pos eh (bK g k i) (aY g) k (bE panels (68*(tag-128)) 68)
def fA (pos eh:Nat) (g:aM) (k start n:Nat) (kw panels:Nat->Nat) (data:Nat):=(List.range n).all fun j=>fO pos eh g k (start+j) kw panels ((data>>>(8*j))&&&255)
lemma ae {g k start n} (pos eh:Nat) (kw panels:Nat->Nat) (data:Nat) (mode:g.u=false) (h:fA pos eh g k start n kw panels data=true):ag g k start n:=by
 intro j lo hi;have one:=all_eq_true.mp h (j-start) (mem_range.mpr (by omega))
 have eq:start+(j-start)=j:=by omega
 change fO pos eh g k (start+(j-start)) kw panels _=true at one;rw [eq] at one;unfold fO at one
 split at one
 . exact Or.inl (gI one)
 . right;rw [mode]
   split at one
   . exact iC one
   . exact gy one
def bk (pos eh:Nat) (g:aM) (k start n:Nat) (kw panels:Nat->Nat) (data:Nat):Nat->Prop
 | 0=>fA pos eh g k start n kw panels data=true
 | d+1=>bk pos eh g k start (n/2) kw panels data d /\
  bk pos eh g k (start+n/2) (n-n/2) kw panels (data>>>(8*(n/2))) d
lemma bA {g k start n} (pos eh:Nat) (kw panels:Nat->Nat) (data d:Nat) (mode:g.u=false) (h:bk pos eh g k start n kw panels data d):ag g k start n:=by
 induction d generalizing start n data with
 | zero=>exact ae pos eh kw panels data mode h
 | succ d ih =>
  simpa only [add_sub_of_le (Nat.div_le_self n 2)] using aw (ih data h.1) (ih (data>>>(8*(n/2))) h.2)
lemma aT {u} {g:aM} {m cap i:Nat} {prior:Nat->Nat} {ws:List aQ} (hm:g.m=m) (hu:g.u=u) (low:∀ q,aR u (aN q) (ac q) (prior q)) (geom:aD g prior=true) (blocks:bT g cap) (idx:dl g cap i ws=true):aB u (ac m) cap ws.toFinset:=by
 subst hm;subst hu;exact lQ low geom blocks (Nat.le_refl _) idx
def By (_:Nat):=0xf
def Bz:aF:=(1,0,1,0,0,0,0,By)
def oO:Array (bt × bt) := #[(0xfffffffffffffffffffffffffffffffffffff3,0x62),(0xffffffffffffffffffffffffffffffffffffbf,0xffffffffffffffffffffffffffffffffffff99),(0x4c,0x4),(0x70,0x70),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def oN:List aZ:=[]
def ue:List (List Nat):=[[],[48,33]]
def r8:Nat->aF
 | 3=>Bz
 | _=>a0
def uf:Nat->Nat->Option (Nat × Nat)
 | _=>fun _=>none
def CD:aM:=⟨15,3,fun j=>oO[j]?.getD (0,0),oN,ue,r8,uf⟩
lemma xo:aD CD (ai [])=true:=by simp only [aD,and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aH (d:=0) ?_⟩,aH (d:=0) ?_⟩<;>simp only [aW]<;>(try repeat' apply And.intro)<;>decide +kernel
lemma wB:aP CD 3 0 1=true:=by decide +kernel
lemma sX:bo CD 3:=by intro k hk;match k with|3=>exact wB|0|1|2=>rfl|_+4=>omega
lemma BK:aR true (cB 15) (ac 15) 4:=cD (b:=8449) (by decide +kernel) (eu (g:=CD) (i:=0) rfl rfl (ad [] lf) xo sX (by decide +kernel))
def jA:=ak [] 4 [(15,[]),(23,[64,48,32,16]),(27,[66,16]),(29,[50,65]),(30,[50,33,16,64]),(39,[80,64,48,32,16]),(57,[32,82,64,16]),(78,[96,80,64]),(83,[99,83,64,32,16]),(99,[48,96,83,64,32,16]),(135,[115,99,83,67]),(156,[112,96,48,50,33,81,64]),(163,[115,50,98,83,66,16]),(165,[114,33,97,82,50,65]),(166,[114,98,83,33,16,64]),(172,[114,50,99,48,33,81,64]),(177,[115,99,82,64,16]),(198,[115,96,83,64]),(281,[131,115,99,50,82,65]),(291,[131,115,50,98,83,66,16]),(300,[130,114,98,49,32,81,64]),(305,[131,115,99,82,64,16]),(312,[130,114,49,98,81,64]),(323,[131,115,98,83,66]),(326,[131,115,98,83,32,64]),(330,[130,114,97,82,16,64]),(332,[130,50,115,98,49,32,81,64]),(344,[130,50,115,49,98,81,64]),(353,[130,33,113,99,82,65]),(354,[130,33,50,113,99,82,16,64]),(396,[48,128,115,96,50,33,81,64]),(424,[129,33,115,48,98,81,64]),(480,[32,50,128,115,98,81,64])]
lemma ru:aX true jA:=aC (m:=15) lf BK (by decide +kernel)
def BC (_:Nat):=0x11a20bf
def BH:aF:=(1,0,3,0,0,0,0,BC)
def BE (_:Nat):=0x30be670208000065000016357504004755c084
def BB (_:Nat):=0x40828fd20fd10
def BG:aF:=(2,1,3,0,0,3,0,BB)
def BD (_:Nat):=0x300
def BA (_:Nat):=0x5dd4520
def BF:aF:=(1,2,3,0,0,0,0,BA)
def oS:Array (bt × bt) := #[(0x2e44,0x2c52),(0x5a8a,0x5208),(0xffffffffffffffffffffffffffffffffffb4f7,0xffffffffffffffffffffffffffffffffffa0c7),(0xffffffffffffffffffffffffffffffffffcf79,0x4f30),(0x718c,0x108c),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def oR:List aZ:=[(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4),(2,0,29,0,4)]
def m9:List (List Nat):=[[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]
def sd:Nat->aF
 | 6=>BH
 | 5=>BG
 | 4=>BF
 | _=>a0
def ug:Nat->Nat->Option (Nat × Nat)
 | 6=>aK 5 15 3 9 1 4 BE
 | 5=>aK 1 3 1 9 1 4 BD
 | _=>fun _=>none
def Bt:aM:=⟨31,6,fun j=>oS[j]?.getD (0,0),oR,m9,sd,ug⟩
lemma xp:aD Bt (ai jA)=true:=by simp only [aD,and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aH (d:=0) ?_⟩,aH (d:=1) ?_⟩<;>simp only [aW]<;>(try repeat' apply And.intro)<;>decide +kernel
lemma wE:aP Bt 6 0 1=true:=by decide +kernel
lemma wD:aP Bt 5 0 2=true:=by decide +kernel
lemma wC:aP Bt 4 0 1=true:=by decide +kernel
lemma sY:bo Bt 6:=by intro k hk;match k with|4=>exact wC|5=>exact wD|6=>exact wE|0|1|2|3=>rfl|_+7=>omega
lemma BL:aR true (cB 31) (ac 31) 7:=cD (b:=8449) (by decide +kernel) (eu (g:=Bt) (i:=0) rfl rfl (ad jA ru) xp sY (by decide +kernel))
def jB:=ak jA 7 [(31,[]),(167,[115,67,100,83]),(313,[131,115,65,50,98,81]),(334,[131,115,100,50,33,16,80]),(355,[131,50,66,116,99,82]),(428,[130,50,116,49,32,97,80])]
lemma rx:aX true jB:=aC (m:=31) ru BL (by decide +kernel)
lemma yP:aR true (cB 47) (ac 47) 5:=cD (b:=8449) (by decide +kernel) (bB (p:=ai jB) (ad jB rx) (8,0,39,0,4) (by decide +kernel) (by decide +kernel))
def jC:=ak jB 5 [(61,[50,65]),(91,[101,66,16]),(94,[101,50,33,16,64]),(181,[114,81,98,50,65]),(227,[83,82,114,99,66,16]),(230,[83,114,99,33,16,64])]
lemma ry:aX true jC:=aC (m:=47) rx yP (by decide +kernel)
lemma BM:aR true (cB 55) (ac 55) 5:=cD (b:=257) (by decide +kernel) (bB (p:=ai jC) (ad jC ry) (16,0,39,0,4) (by decide +kernel) (by decide +kernel))
def jD:=ak jC 5 [(55,[]),(59,[50,65]),(103,[82,98,66,16])]
lemma rA:aX true jD:=aC (m:=55) ry BM (by decide +kernel)
lemma BN:aR true (cB 63) (ac 63) 8:=cD (b:=8449) (by decide +kernel) (bB (p:=ai jD) (ad jD rA) (32,0,31,0,7) (by decide +kernel) (by decide +kernel))
def jE:=ak jD 8 [(63,[]),(95,[101,66,16]),(159,[117,101,67,32]),(359,[131,67,116,99,82,16]),(377,[128,81,67,112,97,32]),(462,[83,133,115,67,32,96]),(483,[83,80,132,115,96,32,16]),(492,[80,84,132,49,113,96])]
lemma rB:aX true jE:=aC (m:=63) rA BN (by decide +kernel)
def y5 (_:Nat):=0x7213f
def y8:aF:=(1,0,2,0,0,0,0,y5)
def y6 (_:Nat):=0x8000
def y4 (_:Nat):=0x17e51
def y7:aF:=(1,1,2,0,0,0,0,y4)
def m4:Array (bt × bt) := #[(0xffffffffffffffffffffffffffffffffffed93,0x2d12),(0xffffffffffffffffffffffffffffffffff9467,0xffffffffffffffffffffffffffffffffff9025),(0x6e38,0x6618),(0x1bd8,0x19c0),(0x0,0x0),(0x63e4,0x42e4),(0x7e44,0x6e40),(0x0,0x0),(0x0,0x0)]
def m3:List aZ:=[(1,32,78,0,4),(12,0,99,0,4),(96,0,15,0,4),(0,8,99,4,5)]
def rZ:List (List Nat):=[[],[32,83]]
def oM:Nat->aF
 | 6=>y8
 | 5=>y7
 | _=>a0
def r7:Nat->Nat->Option (Nat × Nat)
 | 6=>aK 1 3 1 6 1 1 y6
 | _=>fun _=>none
def ud:aM:=⟨111,6,fun j=>m4[j]?.getD (0,0),m3,rZ,oM,r7⟩
lemma ui:aD ud (ai jE)=true:=by simp only [aD,and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aH (d:=0) ?_⟩,aH (d:=0) ?_⟩<;>simp only [aW]<;>(try repeat' apply And.intro)<;>decide +kernel
lemma sG:aP ud 6 0 1=true:=by decide +kernel
lemma sF:aP ud 5 0 1=true:=by decide +kernel
lemma p4:bo ud 6:=by intro k hk;match k with|5=>exact sF|6=>exact sG|0|1|2|3|4=>rfl|_+7=>omega
lemma zR:aR true (cB 111) (ac 111) 7:=cD (b:=16785665) (by decide +kernel) (eu (g:=ud) (i:=0) rfl rfl (ad jE rB) ui p4 (by decide +kernel))
def iu:=ak jE 7 [(111,[]),(123,[101,66,16]),(187,[117,80,66,96,16]),(190,[114,83,48,33,97,64]),(215,[115,83,67]),(222,[101,117,50,33,16,64]),(238,[83,114,99,33,16,64]),(243,[82,98,115,66,16]),(311,[131,115,99,67,82,16]),(318,[128,112,96,49,64]),(343,[131,115,83,67,98]),(349,[128,80,117,32,16,98,65,48]),(365,[129,113,82,65,48]),(378,[129,33,97,81,16,114,49,64]),(437,[134,81,114,50,65]),(455,[83,133,115,67,32,96]),(476,[82,50,133,98,49,32,113,64]),(485,[80,81,129,114,50,65,96]),(490,[81,33,80,128,97,114,49,64]),(497,[98,99,81,131,114,65]),(504,[49,50,83,48,130,113,64])]
lemma nQ:aX true iu:=aC (m:=111) rB zR (by decide +kernel)
def zd (_:Nat):=0x163441bf
def zi:aF:=(1,0,3,0,0,0,0,zd)
def zf (_:Nat):=0x42f9f28c08140000000020f801630c00d0
def zb (_:Nat):=0x420a3fa41fd10
def zh:aF:=(2,1,3,0,0,3,0,zb)
def ze (_:Nat):=0x18000
def y9 (_:Nat):=0xb7d8d20
def zg:aF:=(1,2,3,0,0,0,0,y9)
def m6:Array (bt × bt) := #[(0xfffffffffffffffffffffffffffffffff55417,0xfffffffffffffffffffffffffffffffff46453),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffc60f7,0x44076),(0xfffffffffffffffffffffffffffffffff0bbcb,0xfffffffffffffffffffffffffffffffff03a89),(0xf8724,0xb8124),(0x21bb8,0x1ba0),(0x0,0x0),(0xbec28,0xba408),(0x0,0x0)]
def m5:List aZ:=[(160,0,29,0,4),(24,0,165,0,4),(132,0,57,0,4),(33,0,156,0,4),(17,0,172,0,4),(12,0,177,0,4)]
def lk:List (List Nat):=[[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]
def oP:Nat->aF
 | 7=>zi
 | 6=>zh
 | 5=>zg
 | _=>a0
def sa:Nat->Nat->Option (Nat × Nat)
 | 7=>aK 9 13 2 9 1 4 zf
 | 6=>aK 1 3 1 9 1 4 ze
 | _=>fun _=>none
def r9:aM:=⟨189,7,fun j=>m6[j]?.getD (0,0),m5,lk,oP,sa⟩
lemma uj:aD r9 (ai iu)=true:=by simp only [aD,and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aH (d:=1) ?_⟩,aH (d:=2) ?_⟩<;>simp only [aW]<;>(try repeat' apply And.intro)<;>decide +kernel
lemma sJ:aP r9 7 0 1=true:=by decide +kernel
lemma sI:aP r9 6 0 2=true:=by decide +kernel
lemma sH:aP r9 5 0 1=true:=by decide +kernel
lemma p5:bo r9 7:=by intro k hk;match k with|5=>exact sH|6=>exact sI|7=>exact sJ|0|1|2|3|4=>rfl|_+8=>omega
lemma zT:aR true (cB 189) (ac 189) 8:=cD (b:=536879876) (by decide +kernel) (eu (g:=r9) (i:=0) rfl rfl (ad iu nQ) uj p5 (by decide +kernel))
def iy:=ak iu 8 [(189,[]),(303,[135,50,65]),(347,[130,50,98,82,115,33,65]),(486,[115,83,82,130,99,66,16])]
lemma nU:aX true iy:=aC (m:=189) nQ zT (by decide +kernel)
lemma zS:aR true (cB 127) (ac 127) 9:=cD (b:=16785665) (by decide +kernel) (bB (p:=ai iy) (ad iy nU) (32,0,95,0,8) (by decide +kernel) (by decide +kernel))
def ix:=ak iy 9 [(127,[]),(382,[128,100,49,112]),(478,[99,132,84,48,33,112]),(508,[48,84,100,49,129,112])]
lemma nS:aX true ix:=aC (m:=127) nU zS (by decide +kernel)
def xc (_:Nat):=0x8201ff
def xe:aF:=(1,0,5,0,0,0,0,xc)
def xd (_:Nat):=0x99090000b500000001a152f05d5c000e4006080015749fa60141c73802b0a68137976081bca199eaaa3d961388c0f3a0002328c00084a05000089c2a
def zm (_:Nat):=0x288616180c48a1166c008c818588a2e004e68c2c214019ce18588b2410102944c300431c508936018138408051218b0c0328614b0a030139610c0803944862a8614888704038c28424018278d600745a25b53e43cce27c5e0bc00ff483fe30ff4c3fd10ff54ffe10ff903fe20ff4c7fc20ff58ffd40
def zu:aF:=(12,1,5,0,0,10,0,zm)
def zp (_:Nat):=0x140000000000000198cb0000a04e08a520001a51c20000531e80b64388d00078963d80a7524800343b41a670800007a7cc632d75239502d607286400000000060840000002a100028a67e35dbbd50001a6c315cd7a0d113ac27000121800052568158594ec000682af90000f6880000010b6fab800321ac31374a97c0018068243a2b09f06ef8c8000c984c7fad8000732e29d36fd3c9ba4660000003c50a43a2e72f0000037c5c484413000060966343d567081fd24000161fd8fb857db1616c2d70bc0001da504981c000a8cb68709baa54393350153817e93b2ee08a0b35c971e4812648c40cf0c890074a5b901b85c19b060f0f30f9c6d46f822909e468ae58b600010460007b00142a8dc0d2c800031c60005ad28d4a60000000000000046100000000000000005978000750c07fc419a5a33000612dc38451b04000033fe570000002d76000244c429f180a5d34b0ba1360001a731afd48a565b2f860060014b1d8111aaaac600056d800000000026c2da68678cd5b803ae00010d91906c6000000173ec82c4200058c80000000001b509c9847ce37e90001c466a9e954000000c99484d7ca82a800f93447182024f80000c48dc000596030083ad05a1c75006c10817410814060062c35820051841c00801071c96460c20000020c70c01c908b0c0000080000041016
def zl (_:Nat):=0x1f80354899e077b024a9159a24b911ac077e0465c892708574212ef090d670221e053c214e043b8235cc808a67d091c046f022c0a32623f7049522d15433a6477b08ce033e84719314e04222c097484381b79046f2083ea431f521b80ae446e02b90c91ffb0022ff500273ff780227d009160ad1a2b008a388648213e1129ec123701bbc02b6031f108e812788527a1372fef00a370177821af58220f98488d80ed11b79e031029f81224fe00116e08ea457911b013808784866ffa009e7c49103fc0098ee0495c8319f848269f5444bf2292df046e02b7ba00a2fc6c027b211cfe48667a04ad80ec912592247ef00ae68147aaa443fce6009d00860143e0495227c608ef0062ec24c9e99123806bc62448287a25ec8251c78110a11258898fc215345209610e8c3700843000414019102020c60a121c5c5ec5844fc4543ec3542cc25c1bc12409bfebf43e8be1bd8bcf3c73b9bae3a7b9eb9838f383b7d373369b6035934fb46b3ab3432bb24b1b311b072fcaf62edae72dc2ce2bf2b02a2294a8da83a7ca70a66a5ea54a4d24423c233a2aa192102069fa9ed9e61de9d29cd1c09b21aa1a399a99498e18397416815a14f94493712b11e91590f1000f10e88dd8d18ca0c08b70ab8a209508407d87606b86505b85104203883182501880d00042a470a82c2e250b1c428051315c2a4b0980c2c730b01c220f0b9942c37098142e430883428431b894240f098cc2a090881424370b12c240d090ac4e43090cc6e650994426530b0d44651090d4242f0b98c2a490b0242c570b1542c490b02c2408c3891ae246b94ba4107b92b6e24e8849aeb66b881ee82a983aa6486b951ae707b831ae0c6bad364307b893a2047b92324287b8ba6e867bb19ae0e6bb51ee2a7b909ae2c6ba49aed66b9c9ae607b8b1ee088a159ae50e9811ee4ea9821eea8c98c2a60c6b921ae086b8b9ee467bb29ee62e9849ae346b8d9ee647baa9ee0e6b993a4146b8caa64e6ba41eea67b89b2a286b959ae4e7bb216e242b9c86e87ffff7f7efefbfdf6ef6f902308821058d53501314c12044020
def zt:aF:=(113,2,5,589836,68,12,1057,zl)
def zo (_:Nat):=0x38d5055793c3679268754bc6188000001bef920589c626a6500070140c8d5de5f1d7a21d0344d98ee800183ee488000001119701a189f7ac18d073c41c5a460f2f6dbb0d3e90a06b82f5bcc02928e3aa852e880000109c34616429775d57a00841de8968c753cd4f7779436ba625de899899071c11166c07285d4158b1c40cba3819701ff1ed4e0000001d75e386545f25c03c4e3ccfe7905e2217770000000a100005011f8991186d800000144100008f313025a433c0cd88dae660be94000121c0000002c88000000655b0af52342fd8c3fbe11d039049a5a1e7325180004d4e9a308f4f4000000ef1802b07e014cea170acb800000009b4c4008e61bc79a059a0f70fccb137f85b2554dc0000000f21e93d1260001258003490000000000283ab340000000b1c0000000003185023a5319608aa0001913478000000000000000046621400000000000005b0dc8e000000426e6c726f99d415a6c3045000127023e070c8d80b889403631ef964fdd2196b35879ca860c0656093c9b66e604e1a08c20003c8494d7228964094caf59a8139a149ac000c151050440002c01002420821110471482078810951470800420470000020001001c02830c50400010400800405400402040000c00080070800c100000d0040151000c0040141188000004000
def zk (_:Nat):=0x23042421610002c21610208008384100000005848830400208084004181081508808200a81105842c340108081882c400010401610060400004128800006508824200028421410000c0162410800007085060424a100000220d0042c200002c20410018408210b0d0840000384082c412109080006109020848e84200508408200000000601881c2121000008bf14a22c388670ba10c1480f009fabe87c6f79ecbd479ef09d6ba8736e39c4b7c6ded69a6b48666c998cb0c5febe972ae05b6b3964abc56eaa952aa0536a1940a7c4ee9892aa504969191ca2c44e8890ea083f67d8f89ec3be748e29b83666b8d49a432e628be9782e65b8b095429e5089e9302464588890c20e3e8728d8196318608bc15e248428800f61b83085c0ae148268480860b81081401e02802800df4815ca209fd879c9109fd82dc163df5215c620aff8654931ff38148230fe92054930df7715c5209fd82dd530b7f8558140bf7815c520bbf844c1209ff815c163df771501209ff815c1539fd81dc163fe92048630df920dc530ff210dc5209fd825c640f755154131bf78148131df7815ca10df7815ca40ddf714c163bf7815cd209fd8798a409ff815ca20fd5514c131df97244220bf9809c910dbf74549309ff805c5639fd81dd930ded20dc963cfd764c620df4815ca40bf9808ca10b7f85581319fd82dc530df9205c630ff210481319fd80dc5539fd81dd530bbd849c910bf58158e109ff805c963aff8654940ddf714c963df7715cd209fd80dd9319fd82dc563df551dc131ddd215ce20df7714c120fe92050910df5315ca10df783dc5209fd825c630ded52dc931dbd425d640df610dd9319ff815cd20bf78148163df5515c1319fd82dc540ddf764c1319fd878ca109fd81dcd209fd80dc5639ff815ca40dbd54dc940ff110dc520dbf7458130ded215ca30df5615d210bbf844c110ff081482309fd82dd1109fd82dd540df471dcd20df77144120bbf845cd20dbd425c640bf7814ca10ff3714c120bdf8350910bf78148153df7215d210bf78158131fe52048531bf78154131ded7248640cfd764ca209ff815c963bbf845cd10df583dc520edd6358130df4715cd20df771dcd20ddf714c153ff0714c120fd5314ca109f7815c5209f7815cd209bf845c1539ef825c5639bf845c1639bf845ce10fe120c861097f855da408fd86dd5319bf845cd209bf845c1319f7815ca409f581dc163
def zr:aF:=(116,3,5,0,0,11,0,zk)
def zn (_:Nat):=0x30450ac641c0062400b2c00a0c8100000001c50000042a883a
def zj (_:Nat):=0xdf2b688de6543ca1408fb4c102b944193f85dd1604c23ef22c16eaa062fe1b7454930cdbc26e2982411f79161e6290336f0838ae69056de5183dc5208fb4c0e2b9a419b784dc5734823ef22c16ea9847de4582dd110
def zq:aF:=(12,4,5,0,0,6,0,zj)
def m8:Array (bt × bt) := #[(0xfffffffffffffffda8e81df4649a4aea03f353,0x1a8209cc44085084a802052),(0xfffffffffffffffe550627bdd1589ea381610f,0xfffffffffffffffe550c023b884896b1415109),(0xb876f0435535c500a8ea8c,0x2872300045166108a00a84),(0x2669d0fd182653b341a80c0,0x2428c0bdd82211a84129140),(0x1554172223bd2f53d4f48e0,0x15416022395ae5314d4aa0),(0x253ba08288d622045549630,0x2509e022805626105509220),(0x0,0x0),(0x38f01c59fba0814d3746c20,0x18701c597ba0892d2056500),(0x0,0x0)]
def m7:List aZ:=[(160,0,31,0,7),(24,0,167,0,7),(2,0,189,0,8),(19,0,172,0,4),(0,16,166,9,6),(4,0,187,0,7),(1,0,190,0,7),(36,128,27,0,4),(136,0,55,0,5),(129,32,30,0,4),(9,16,166,0,4),(20,8,163,0,4),(14,0,177,0,4),(35,0,156,0,4),(56,0,135,0,4),(26,0,165,0,4),(134,0,57,0,4),(162,0,29,0,4),(152,0,39,0,4),(25,0,166,0,4),(168,0,23,0,4)]
def i0:List (List Nat):=[[],[115,84],[32,67,117],[32,83,116]]
def oQ:Nat->aF
 | 10=>xe
 | 9=>zu
 | 8=>zt
 | 7=>zr
 | 6=>zq
 | _=>a0
def sb:Nat->Nat->Option (Nat × Nat)
 | 10=>aK 16 41 5 10 4 2 xd
 | 9=>aK 67 277 6 13 7 2 zp
 | 8=>aK 100 251 6 13 7 2 zo
 | 7=>aK 4 19 2 10 4 2 zn
 | _=>fun _=>none
def eX:aM:=⟨191,10,fun j=>m8[j]?.getD (0,0),m7,i0,oQ,sb⟩
set_option maxHeartbeats 0 in
lemma uk:aD eX (ai ix)=true:=by simp only [aD,and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aH (d:=3) ?_⟩,aH (d:=0) ?_⟩<;>simp only [aW]<;>(try repeat' apply And.intro)<;>decide +kernel
lemma pu:aP eX 10 0 1=true:=by decide +kernel
lemma sO:aP eX 9 0 12=true:=by apply aq 8 0 2;simp only [aE,ba,reduceDiv,reduceSub,reduceAdd];(repeat' apply And.intro)<;>decide +kernel
lemma sM:aP eX 8 0 3=true:=by decide +kernel
set_option maxHeartbeats 0 in
lemma sN:aP eX 8 3 36=true:=by apply aq 8 0 3;simp only [aE,ba,reduceDiv,reduceSub,reduceAdd];(repeat' apply And.intro)<;>decide +kernel
set_option maxHeartbeats 0 in
lemma pC:aP eX 8 39 31=true:=by apply aq 8 0 3;simp only [aE,ba,reduceDiv,reduceSub,reduceAdd];(repeat' apply And.intro)<;>decide +kernel
set_option maxHeartbeats 0 in
lemma pD:aP eX 8 70 36=true:=by apply aq 9 0 3;simp only [aE,ba,reduceDiv,reduceSub,reduceAdd];(repeat' apply And.intro)<;>decide +kernel
lemma nH:aP eX 8 106 7=true:=by apply aq 9 0 1;simp only [aE,ba,reduceDiv,reduceSub,reduceAdd];(repeat' apply And.intro)<;>decide +kernel
lemma rG:aP eX 8 0 113=true:=(@aJ _ eX 8 0 106 7 (@aJ _ eX 8 0 70 36 (@aJ _ eX 8 0 39 31 (@aJ _ eX 8 0 3 36 sM sN) pC) pD) nH)
lemma sL:aP eX 7 0 13=true:=by apply aq 7 0 2;simp only [aE,ba,reduceDiv,reduceSub,reduceAdd];(repeat' apply And.intro)<;>decide +kernel
set_option maxHeartbeats 0 in
lemma px:aP eX 7 13 36=true:=by apply aq 8 0 3;simp only [aE,ba,reduceDiv,reduceSub,reduceAdd];(repeat' apply And.intro)<;>decide +kernel
set_option maxHeartbeats 0 in
lemma py:aP eX 7 49 36=true:=by apply aq 8 0 3;simp only [aE,ba,reduceDiv,reduceSub,reduceAdd];(repeat' apply And.intro)<;>decide +kernel
set_option maxHeartbeats 0 in
lemma pB:aP eX 7 85 31=true:=by apply aq 8 0 3;simp only [aE,ba,reduceDiv,reduceSub,reduceAdd];(repeat' apply And.intro)<;>decide +kernel
lemma rF:aP eX 7 0 116=true:=(@aJ _ eX 7 0 85 31 (@aJ _ eX 7 0 49 36 (@aJ _ eX 7 0 13 36 sL px) py) pB)
lemma sK:aP eX 6 0 12=true:=by apply aq 7 0 2;simp only [aE,ba,reduceDiv,reduceSub,reduceAdd];(repeat' apply And.intro)<;>decide +kernel
lemma p6:bo eX 10:=by intro k hk;match k with|6=>exact sK|7=>exact rF|8=>exact rG|9=>exact sO|10=>exact pu|0|1|2|3|4|5=>rfl|_+11=>omega
lemma zV:aR true (cB 191) (ac 191) 11:=cD (b:=536879361) (by decide +kernel) (eu (g:=eX) (i:=0) rfl rfl (ad ix nS) uk p6 (by decide +kernel))
def iz:=ak ix 11 [(191,[]),(319,[135,50,65]),(351,[133,117,101,33,48]),(367,[128,16,64,100,80,113,33,48]),(379,[130,50,81,115,98,65]),(431,[113,129,97,82,32,65,48]),(445,[129,82,97,48]),(487,[115,83,82,130,99,66,16]),(494,[64,132,49,96])]
lemma nV:aX true iz:=aC (m:=191) nS zV (by decide +kernel)
lemma zW:aR true (cB 251) (ac 251) 8:=cD (b:=1358970881) (by decide +kernel) (bB (p:=ai iz) (ad iz nV) (128,0,123,0,7) (by decide +kernel) (by decide +kernel))
def iA:=ak iz 8 [(251,[])]
lemma nW:aX true iA:=aC (m:=251) nV zW (by decide +kernel)
lemma zX:aR true (cB 255) (ac 255) 12:=cD (b:=553656577) (by decide +kernel) (bB (p:=ai iA) (ad iA nW) (64,0,191,0,11) (by decide +kernel) (by decide +kernel))
def iB:=ak iA 12 [(255,[]),(479,[118,133,33,48]),(503,[115,82,98,131,66,16]),(507,[99,81,115,130,65]),(509,[82,129,48])]
lemma nX:aX true iB:=aC (m:=255) nW zX (by decide +kernel)
def xh (_:Nat):=0x1840804ff
def xn:aF:=(1,0,6,0,0,0,0,xh)
def xk (_:Nat):=0x2e190000e44028954b00129713b90021c5c400a24a286e030000000000d800006790000005048cec0c584c000029410000109
def xg (_:Nat):=0x1c1800c080840a80c160880850c1604287044044070d0e04282102a03050f061043070d0a08508680361365e17803fe087fc30ffa61ff443ff187fe10
def xm:aF:=(6,1,6,0,0,9,0,xg)
def xj (_:Nat):=0x605ec8c0000001117d3d8e632bfc434126a560a0c97cd1c2e0006879dce0130002029832241d31f89848e70800000000019dd990a81d83401050198b41ca520a2f40adbada290270002212000f0240555b3c62d0c010b44640b0000000000a02000000274e000193000140ac0e19590854ad62490de02102d21d6156142944000d8a4082dc48550007f7944400014100014220513068000058000991281875380f661504984eda4b2e787cc39625232a002653d245061c2fea2000000680400000024e94b1850b1ad217010100600b00017050301c050070e260404451400410
def xf (_:Nat):=0x2ff45022545810b0ebed2a0a0caa9a4a646170118bba1216fab28127d3e208a4fd3025756808373fd0139d909a4f77fc6205153e0263c3e095f7f520157b044d77c804c7e9c8080acf700959fa41af7f15139e7a243e4b049e3e72549ef82c4149a9b213cd771046be348414dff0820a1d72484df882050f8046fdd00eb5019eb3818801d311052ae460a7bcd01029a02900f738439afc1100200b730408c90182a2e28830c2c20863024850e8b0a261b081c11808f861e128c0d842217820e140a0933257c918e31461a4187eaf6de1ba2708d81a3b2d618bd16c2b1532a053124b45a834f71d2366648b895627049c860f91c23445d09f1081b43084b06209c0e800eb8beb9aeb83eb98e398eb9cf41aeb8df389e982e39ce41af982fc0bf40bf38de98ce98df39cf18dec0beb89e389fc1af98cec1ae40bfb8dbc23cb858c1a8c0d8c188c1d8c0c8c098c3dcb839c0b8c1c9c1a54180c316c156c104c183c23ffffefbeffbeef7bbebf8c2104c1100c010
def xl:aF:=(47,2,6,524294,51,11,1060,xf)
def xi (_:Nat):=0x71198115833604b01a0000606e88fc000242d7c1fb0faad280000000907200000000000000000011a60000c095e07a03c80000000207200b0000f0374218000083d74340000000000010fe000191d800038c8000000000050001a19c0000000f0d80002417105f0001002bc08ec1b0001e12c0000000f0e7e92d81a6801000081e2997c07b60460002f86e047b093591c0b42863642440b4814a40900000001016701f80992cbb0308000c10b416439d943b147aae0000000140000000051cc437e4b4604d43368120000516302b9f1000004067d0c8043000061b56b100000c580000000783f104c0003fbb80009070d07382c4f54000000014a410460001715080ea8740833a5880002404721a41d7010e870e0a6000041e7802d68a0000000000000016605c32d9336823a9a000d7e20d86d416e10a400828f5440c813b83e60a220d8fa1581020e4099e8197842301210c9aa808357404e01fd304041e1023c6482e6b2cf063e21e71a6056370a003201825400056b139c293c35f0f8311d9031132ca772115827b06218a0203561cf86910f5a5f4b8b233b382b58ee49dec3300d7802d8c0502fd10109b0c0a907ee0a0fc274022d3a10d5060b108505d001d3c31732301838cca1790204071480aad97c1b8000509cd0a402a9482901e3171c30000064ac78e80004854e040ddec841106f32a0420d715820cb2810092535383b24a5005e83218280109ecf40006a47e0540003c1d6c17800c84f7001b077b0900001c268000e088000143b221e2f0000390d00040c17340800211f04000c3852005c082b04030102880201024c3d0e17000f0511410100573e04001200070500016400040b010407000d00010204010004000a010e07000000003720
def zy (j:Nat):Nat:=(if j<1 then 0x90c4083f321d6cc55f504646019c44204dfc10cf28937f0432053910ce223b02400980bbc34c65818045e5f095406f016f31822b00f789912c221f5c0114f24249ce0e08c5fc120656c06b2083990d70859f22264171411812e90b633045ad93564ac98ac1927756b1df4473c74045ae40c7bc4213fdaa08c1dec4c97b82425ed04f3d690c2f0864391ec72208d390a7d7c922807c0191010fa1911e02bfb8240e4c43990d011c06bd692267e463b811dee091ec041cc873e3c9046de215e623de216f1097a08640ab2623f9804abea9226f20245bf630932fde02207c2399086b88877f60496e239ac50c021f5491180a7108bc843247a20643ec231f50022efe0c114fda0958225a38918c18c308840c70fd088c0683056b01e8ec1e8cc2c288d0b416286c21c0109148e1a828738784a282029c20384833040b05c2684e0814120e020441e0b05549d41d33d27d1c513d084fe4f74f14e5cdecd84d14ca4c34bccb4cab49f497c8747fc77c70c66c60c57c51442437c2fc26c1ec1440dc02bf9beb3e4bddbd73cc3c23b73b1ba83a139739238c37fb78b73b6635fb58b4ab44338331322317307af72efae7ade2d5ac72bcab6aae2a129328a280a74a6ba5d251a49237a29a1f211a061fb9f29e39dc1cc9be1b89ac1a519918f98618097996c96115894e14513b92b1229191109080fd8f80ef0e18d48c70b88aa8a109788d88187906e06905c05604e04083302901a80c00049718e4c0b36e11290e6d2997424c0b9261cf970e52b97315cb95261d8532e4ab97614cb9ca65cf532e6a997744cc1735c271330008982c5cc02266041130937948c5c8c8266017b0528b970cfc91846550c2628b983612c82e3e58513308c2711a9cabe265d58302aba833c4cc325e51382e23159451dc19c266176322389989d3c83c2e5cc7ce6137946d3c830e65c3372688b976da48ace60cf232a4259095ec14c2662673060a5900054c162a612172f0bd97886cb3afa462c1268bd9189c4b86f5cc2173103d8201fb9848644e7b050369159bc8acde1134322bd78445bc222c61857b271159411bc2251e61f1f2d03d829e140aac6188772e19f924dcc19226608830280998704cb8c2e6194b213c5837e0c0bc2e5c62f2853784553c8182661d7306eb784512c83aca4477f2460998808ca9a4654e3f24c3a970dec13d8cc513f24f0b9815f4bc574c555b0f009973ddc194de1106b22b0998943c9180e51b07291ff6febfbff77deefdbff7f6fddf7bdf77ebfcff7feff5fdbf77def7ddfb7f3fe7dcefdc6309c6308c63061e3060e3060a30606305c6305c2304c630cc6109ce1060e10606105ce104c6101ce10e1130e0530a0530605305c5305c13020530e0d10cc110a0d1060d105cd104c11020d109c43061830604305c4301c43060c10608105cc101cc10 else 0x23fc480cb7845bfa208a1e04c73d81137085d8158ef1090e22602dc5c887112c08e223888e2258134029f023bd8325d2859f446065d28576447019d81200235c08603afc001907c8877046f6022e212f4)
def zD:aF:=(136,3,6,1638440,86,12,1083,zy)
def zA (_:Nat):=0xa16f054972c28000915083d009e0b000184b4aa00070df9a0000000103800000000040895c7d1f430452c83b41000000066c401a931403589000181590e60c4006e970739878c268f4319a8a1e8a227410f80515a000677800202f029915b907440e6c7f8b08b068a9c416408c84be1fb32f040001432000000000000000000001daa0990d58b4800e1d917e01640581811720991cb65f653999ed0240cf0c80400004d08a6610820084081054000400010000a42100804
def zx (_:Nat):=0xa10200000e0858408185082e10440a10000c840000161001e1030a10000000000504000000000141001e10108102819120810282002820c8400001e10283e0edf5ba3ccdeebb539ac5dcadb68acd529f4a9dcda4f2289c3a13047fbe9eaf070b71aed266b2186be57aa93696439b8be50258f05a28118781e00dafe5b845c530cefe1f944c110aef69c91e1130afb68f7360810cefe119720530cef5c79460e30cfb61f924c610adfe9587e0d10cef5c79460e10cdb655821cc10f745c5315c1308fdea581205308efe91985c1308fb689981cc10caf619941c4308fbe89985cd108bf69a985c530afa6829760a30cafe5b845c530ccfe119520530cdb655829c630cfa609901cc10cebe539260d10aebe8991e1130af66809760c10cbbe59825c6308fb68b9161e308efe91989ce108bfe999760430af36889760c10ceb651828c6308efe91985ce108fb6a582dc6308bfe9b985c4308bfe99985c630c9f655869c430cebe139260530ad76949760c108bf6a3965c430acf69491e11308f7ea58320d10cfa609908c630af9a869760a30add6967160430aeb6929760a30af96869760a308ef6a784a0530ceb651821cc108dfe9597e0530aebe919360a30ccfe57845c130cee611901cc108fb6a3924c630
def zC:aF:=(53,4,6,0,0,9,0,zx)
def zz (_:Nat):=0x834601a000
def zw (_:Nat):=0xa295fdb2e3ca3070852bfb65c79460e30
def zB:aF:=(2,5,6,0,0,3,0,zw)
def ng:Array (bt × bt) := #[(0xffffffffffffffd8fd630dda8e8aa61c90014d,0xffffffffffffffd8d42304082801a102900145),(0x2762dfc636db2d3474067090,0x2120d82a34960818c4045090),(0x3ec100918c681557416c0816,0x1ec100818829154701680800),(0x19cee55353e34c9ba0a86e6,0xeea5424062a80ba0284c6),(0x3721940b48c0c06e80091ef8,0x2721140b40c0c04e00091a38),(0x30e98f28487160298718700,0x30a98f08487160298418600),(0xffffffffffffffcace0a51892172a62383f801,0xace02d1892132a62281a800),(0x0,0x0),(0xfffffffffffffffc3135226350618b47fd9801,0xfffffffffffffff43105024250c159053c1001)]
def nf:List aZ:=[(32,0,351,0,11),(64,0,319,0,11),(4,0,379,0,11),(16,0,367,0,11),(49,0,334,0,7),(70,0,313,0,7),(256,0,127,0,9),(24,0,359,0,8),(28,0,355,0,7),(83,0,300,0,4),(276,8,99,0,4),(69,2,312,0,4),(260,0,123,0,7),(2,1,332,48,6),(57,0,326,0,4),(50,1,332,0,4),(65,0,318,0,7),(104,256,23,0,4),(39,0,344,0,4),(300,0,83,0,4),(29,0,354,0,4),(5,0,378,0,7),(321,32,30,0,4),(262,64,57,0,4),(352,0,31,0,7),(74,4,305,0,4),(305,0,78,0,4),(80,0,303,0,8),(290,64,29,0,4),(72,0,311,0,7),(328,0,55,0,5),(18,0,365,0,7),(273,32,78,0,4),(41,16,326,0,4),(26,4,353,0,4),(51,0,332,0,4),(36,0,347,0,8),(344,0,39,0,4)]
def ll:List (List Nat):=[[],[98,131,84],[16,66,101],[16,82,131,100],[48,129,82],[48,129,98,16,66,84],[128,49,100],[128,49,66,16,82,98]]
def oT:Nat->aF
 | 12=>xn
 | 11=>xm
 | 10=>xl
 | 9=>zD
 | 8=>zC
 | 7=>zB
 | _=>a0
def se:Nat->Nat->Option (Nat × Nat)
 | 12=>aK 8 37 4 10 3 3 xk
 | 11=>aK 48 123 4 13 6 3 xj
 | 10=>aK 79 299 8 15 8 3 xi
 | 9=>aK 39 99 5 13 6 3 zA
 | 8=>aK 1 5 1 8 1 3 zz
 | _=>fun _=>none
def d8:aM:=⟨383,12,fun j=>ng[j]?.getD (0,0),nf,ll,oT,se⟩
set_option maxHeartbeats 0 in
lemma ul:aD d8 (ai iB)=true:=by simp only [aD,and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aH (d:=3) ?_⟩,aH (d:=1) ?_⟩<;>simp only [aW]<;>(try repeat' apply And.intro)<;>decide +kernel
lemma pI:aP d8 12 0 1=true:=by decide +kernel
lemma pH:aP d8 11 0 6=true:=by apply aq 9 0 1;simp only [aE,ba,reduceDiv,reduceSub,reduceAdd];(repeat' apply And.intro)<;>decide +kernel
lemma pE:aP d8 10 0 6=true:=by apply aq 8 0 1;simp only [aE,ba,reduceDiv,reduceSub,reduceAdd];(repeat' apply And.intro)<;>decide +kernel
lemma pF:aP d8 10 6 13=true:=by apply aq 9 0 2;simp only [aE,ba,reduceDiv,reduceSub,reduceAdd];(repeat' apply And.intro)<;>decide +kernel
set_option maxHeartbeats 0 in
lemma nI:aP d8 10 19 28=true:=by apply aq 10 0 3;simp only [aE,ba,reduceDiv,reduceSub,reduceAdd];(repeat' apply And.intro)<;>decide +kernel
lemma oF:aP d8 10 0 47=true:=(@aJ _ d8 10 0 19 28 (@aJ _ d8 10 0 6 13 pE pF) nI)
lemma sR:aP d8 9 0 3=true:=by decide +kernel
set_option maxHeartbeats 0 in
lemma sS:aP d8 9 3 36=true:=by apply aq 9 0 3;simp only [aE,ba,reduceDiv,reduceSub,reduceAdd];(repeat' apply And.intro)<;>decide +kernel
set_option maxHeartbeats 0 in
lemma pL:aP d8 9 39 36=true:=by apply aq 9 0 3;simp only [aE,ba,reduceDiv,reduceSub,reduceAdd];(repeat' apply And.intro)<;>decide +kernel
set_option maxHeartbeats 0 in
lemma pM:aP d8 9 75 36=true:=by apply aq 9 0 3;simp only [aE,ba,reduceDiv,reduceSub,reduceAdd];(repeat' apply And.intro)<;>decide +kernel
lemma nJ:aP d8 9 111 8=true:=by apply aq 9 0 1;simp only [aE,ba,reduceDiv,reduceSub,reduceAdd];(repeat' apply And.intro)<;>decide +kernel
lemma nK:aP d8 9 119 17=true:=by apply aq 10 0 2;simp only [aE,ba,reduceDiv,reduceSub,reduceAdd];(repeat' apply And.intro)<;>decide +kernel
lemma rI:aP d8 9 0 136=true:=(@aJ _ d8 9 0 119 17 (@aJ _ d8 9 0 111 8 (@aJ _ d8 9 0 75 36 (@aJ _ d8 9 0 39 36 (@aJ _ d8 9 0 3 36 sR sS) pL) pM) nJ) nK)
set_option maxHeartbeats 0 in
lemma sQ:aP d8 8 0 36=true:=by apply aq 8 0 3;simp only [aE,ba,reduceDiv,reduceSub,reduceAdd];(repeat' apply And.intro)<;>decide +kernel
lemma pJ:aP d8 8 36 8=true:=by apply aq 8 0 1;simp only [aE,ba,reduceDiv,reduceSub,reduceAdd];(repeat' apply And.intro)<;>decide +kernel
lemma pK:aP d8 8 44 9=true:=by apply aq 9 0 1;simp only [aE,ba,reduceDiv,reduceSub,reduceAdd];(repeat' apply And.intro)<;>decide +kernel
lemma rH:aP d8 8 0 53=true:=(@aJ _ d8 8 0 44 9 (@aJ _ d8 8 0 36 8 sQ pJ) pK)
lemma sP:aP d8 7 0 2=true:=by decide +kernel
lemma p7:bo d8 12:=by intro k hk;match k with|7=>exact sP|8=>exact rH|9=>exact rI|10=>exact oF|11=>exact pH|12=>exact pI|0|1|2|3|4|5|6=>rfl|_+13=>omega
lemma zY:aR true (cB 383) (ac 383) 13:=cD (b:=12901687553) (by decide +kernel) (eu (g:=d8) (i:=0) rfl rfl (ad iB nX) ul p7 (by decide +kernel))
def dW:=ak iB 13 [(383,[]),(447,[98,118,81,130,50,65]),(495,[116,83,32])]
lemma kU:aX true dW:=aC (m:=383) nX zY (by decide +kernel)
lemma mD:aX false dW:=oX kU
def Co (_:Nat):=0x1a230180fd10fc20
def Cr:aF:=(2,1,2,0,0,4,0,Co)
def Cp (_:Nat):=0x104451000a0200202082101c0c0071400
def Cn (_:Nat):=0x613110000e3d4507e48110bea9a217d53082faa4885f54420
def Cq:aF:=(5,2,2,0,0,5,0,Cn)
def qI:Array (bt × bt) := #[(0xfffffffffffffffffffffffffffffffffffc47,0xa86),(0xfffffffffffffffffffffffffffffffffff09b,0xfffffffffffffffffffffffffffffffffff531),(0x29c,0x8cc),(0xfffffffffffffffffffffffffffffffffff327,0xfffffffffffffffffffffffffffffffffff303),(0xd78,0x478),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def qH:List aZ:=[(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4)]
def wS:List (List Nat):=m9
def tE:Nat->aF
 | 6=>Cr
 | 5=>Cq
 | _=>a0
def wT:Nat->Nat->Option (Nat × Nat)
 | 6=>aK 8 11 1 11 3 4 Cp
 | _=>fun _=>none
def Be:aM:=⟨1055,6,fun j=>qI[j]?.getD (0,0),qH,wS,tE,wT⟩
lemma rb:aD Be (ai dW)=true:=by simp only [aD,and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aH (d:=0) ?_⟩,aH (d:=1) ?_⟩<;>simp only [aW]<;>(try repeat' apply And.intro)<;>decide +kernel
def C6:Nat:=0x110c0300c03
def C5:Nat:=0x14090281205
lemma sj:ag Be 6 0 2:=bG (by decide +kernel)
lemma si:ag Be 5 0 5:=cJ C6 C5 (fun _=>0x4224033220301121141340101413401031423232) rfl (by decide +kernel)
lemma lY:bT Be 6:=by intro k hk;match k with|5=>exact si|6=>exact sj|0|1|2|3|4=>exact cZ Be _ 0|_+7=>omega
lemma B6:aB false (ac 1055) 6 (cB 1055).toFinset:=gf (q:=31) (p:=ai dW) (ad dW mD) (by decide +kernel)
lemma xG:aR false (aN 1567) (ac 1567) 7:=
 aA (q:=1055) (rs:=[2,1,2,4,1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) B6
  (aT (g:=Be) (i:=0) rfl rfl (ad dW mD) rb lY (by decide +kernel))
def lx:=ak dW 7 [(1567,[]),(2079,[50,65]),(6687,[50,33,16,64]),(7199,[66,16]),(1703,[115,67,100,83]),(4263,[114,33,97,82,50,65]),(7847,[115,50,98,83,66,16]),(12455,[113,97,82,32,65,48]),(2361,[131,115,65,50,98,81]),(6990,[131,115,100,50,33,16,80]),(4963,[130,33,113,99,82,65]),(9571,[130,33,50,113,99,82,16,64])]
lemma s5:aX false lx:=aC (m:=1567) mD xG (by decide +kernel)
lemma vK:aR false (aN 42527) (ac 42527) 7:=
 aA (q:=1055) (rs:=[2,1,2,4,1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) B6
  (aT (g:=Be) (i:=1) rfl rfl (ad dW mD) rb lY (by decide +kernel))
def d3:=ak lx 7 [(42527,[]),(44063,[50,65]),(47647,[50,33,16,64]),(52767,[33,32,65,48]),(57887,[16,64,49,32]),(42663,[115,67,100,83]),(44711,[114,33,97,82,50,65]),(47783,[114,98,83,33,16,64]),(54951,[113,97,82,32,65,48]),(68775,[113,16,96,81,49,64]),(44345,[131,115,65,50,98,81]),(60217,[129,113,33,98,81,48]),(53070,[130,114,99,49,32,65,80]),(60238,[129,113,98,16,66,49,80]),(42851,[131,50,66,116,99,82]),(44899,[130,33,113,99,82,65]),(50019,[130,33,50,113,99,82,16,64]),(53164,[130,50,116,49,32,97,80]),(60332,[129,50,114,48,66,97,80]),(69548,[129,116,50,97,80])]
lemma gq:aX false d3:=aC (m:=42527) s5 vK (by decide +kernel)
def Ax (_:Nat):=0x1040a3fa21fd51
def AA:aF:=(2,1,1,0,0,3,0,Ax)
def Ay (_:Nat):=0x40000
def Aw (_:Nat):=0x102de54110
def Az:aF:=(1,2,1,0,0,0,0,Aw)
def n0:Array (bt × bt) := #[(0xfffffffffffffffffffffffffffffffffff9b5,0xe94),(0xfffffffffffffffffffffffffffffffffff0db,0xfffffffffffffffffffffffffffffffffff10b),(0x602,0xa80),(0x614,0x514),(0x0,0x0),(0x964,0x160),(0x78,0xef0),(0x0,0x0),(0x0,0x0)]
def nZ:List aZ:=[(96,0,15,0,4),(1,32,78,0,4)]
def tm:List (List Nat):=[[],[32,83]]
def qB:Nat->aF
 | 6=>AA
 | 5=>Az
 | _=>a0
def tp:Nat->Nat->Option (Nat × Nat)
 | 6=>aK 1 3 1 6 1 1 Ay
 | _=>fun _=>none
def qA:aM:=⟨1135,6,fun j=>n0[j]?.getD (0,0),nZ,tm,qB,tp⟩
lemma nh:aD qA (ai d3)=true:=by simp only [aD,and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aH (d:=0) ?_⟩,aH (d:=0) ?_⟩<;>simp only [aW]<;>(try repeat' apply And.intro)<;>decide +kernel
def yS:Nat:=0x42108300c03
def yR:Nat:=0x68321248a2a
lemma oZ:ag qA 6 0 2:=cJ yS yR (fun _=>0x2401212143203010) rfl (by decide +kernel)
lemma oY:ag qA 5 0 1:=cJ yS yR (fun _=>0x24012110) rfl (by decide +kernel)
lemma kR:bT qA 6:=by intro k hk;match k with|5=>exact oY|6=>exact oZ|0|1|2|3|4=>exact cZ qA _ 0|_+7=>omega
lemma yQ:aB false (ac 1135) 6 (cB 1135).toFinset:=gf (q:=111) (p:=ai d3) (ad d3 gq) (by decide +kernel)
lemma v2:aR false (aN 49775) (ac 49775) 7:=
 aA (q:=1135) (rs:=[2,64,2,4,1,2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) yQ
  (aT (g:=qA) (i:=0) rfl rfl (ad d3 gq) nh kR (by decide +kernel))
def kd:=ak d3 7 [(42683,[117,80,66,96,16]),(47806,[114,83,48,33,97,64]),(69498,[129,33,97,81,16,114,49,64]),(69557,[134,81,114,50,65])]
lemma qq:aX false kd:=aC (m:=49775) gq v2 (by decide +kernel)
lemma vM:aR false (aN 42607) (ac 42607) 7:=
 aA (q:=1135) (rs:=[2,1,2,4,1,2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) yQ
  (aT (g:=qA) (i:=1) rfl rfl (ad d3 gq) nh kR (by decide +kernel))
def bI:=ak kd 7 [(44155,[99,83,64,32,16]),(44219,[115,50,32,83,66,96,16]),(44731,[117,80,66,96,16]),(52926,[114,83,48,33,97,64]),(54974,[112,48,50,33,97,64]),(42711,[115,83,67]),(47838,[101,117,50,33,16,64]),(52958,[99,115,83,48,33,64]),(42739,[82,98,115,66,16]),(44787,[83,80,96,115,64,32,16]),(53054,[130,114,98,49,32,81,64]),(60253,[128,80,117,32,16,98,65,48]),(60282,[129,33,97,81,16,114,49,64]),(44981,[134,81,114,50,65]),(48071,[83,133,115,67,32,96]),(53212,[82,50,133,98,49,32,113,64]),(60408,[49,50,83,48,130,113,64]),(69624,[81,80,48,50,130,113,64])]
lemma dr:aX false bI:=aC (m:=42607) qq vM (by decide +kernel)
def Cv (_:Nat):=0x344640ac3f865fc10
def CC:aF:=(2,1,2,0,0,4,0,Cv)
def Cy (_:Nat):=0x1520079d85d46b7171000680020c0000f391436008009b010
def Cu (_:Nat):=0x1108482000804c8462023211880840401f7cb4e4b74a0b44658480fb48032fd4c410bf58032bf58c10bf590109f59432be580329f59410bd58432bb58810af59010b758c10
def CB:aF:=(12,2,2,0,0,7,0,Cu)
def Cx (_:Nat):=0x24f9400060ba8030352
def Ct (_:Nat):=0x108421184210872a1e50a03e498240196e52058432cea62b2821b54c1610cb5a98ac8086e53158810
def CA:aF:=(6,3,2,0,0,6,0,Ct)
def Cw (_:Nat):=0x20034000
def Cs (_:Nat):=0x3b04813058432
def Cz:aF:=(1,4,2,0,0,0,0,Cs)
def qL:Array (bt × bt) := #[(0xffffffffffffffffffffffffffffffffff209f,0xd8096),(0xfffffffffffffffffffffffffffffffff19c61,0xfffffffffffffffffffffffffffffffff03861),(0x97be,0x2c69c),(0xfffffffffffffffffffffffffffffffff04b47,0xfffffffffffffffffffffffffffffffffd3903),(0x44c78,0x24468),(0xa2f80,0x27f00),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def qK:List aZ:=[(1,32,30,0,4),(6,0,57,0,4),(40,0,23,0,4),(24,0,39,0,4)]
def wV:List (List Nat):=[[],[65,50]]
def tH:Nat->aF
 | 7=>CC
 | 6=>CB
 | 5=>CA
 | 4=>Cz
 | _=>a0
def wW:Nat->Nat->Option (Nat × Nat)
 | 7=>aK 7 21 2 9 4 1 Cy
 | 6=>aK 2 9 1 8 3 1 Cx
 | 5=>aK 1 5 1 6 1 1 Cw
 | _=>fun _=>none
def yF:aM:=⟨1087,7,fun j=>qL[j]?.getD (0,0),qK,wV,tH,wW⟩
lemma rc:aD yF (ai bI)=true:=by simp only [aD,and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aH (d:=0) ?_⟩,aH (d:=0) ?_⟩<;>simp only [aW]<;>(try repeat' apply And.intro)<;>decide +kernel
def rE (_:Nat):=0x3514243035142420351320403142355431423232203411211512401013243543
def iL (_:Nat):=0x3120043210043201024300234510350210243002345103402102430023451023051024300234010340210210341352003510002103413520030210
def yH:Nat:=0x42110c0300c03
def yG:Nat:=0x34190a81205
lemma wZ:ag yF 4 0 1:=ae yH yG rE iL 0x1 rfl (by decide +kernel)
lemma w0:ag yF 5 0 6:=ae yH yG rE iL 0x50008000607 rfl (by decide +kernel)
lemma w3:ag yF 6 0 12:=ae yH yG rE iL 0x803020482818600838580 rfl (by decide +kernel)
lemma w4:ag yF 7 0 2:=ae yH yG rE iL 0x84 rfl (by decide +kernel)
lemma lZ:bT yF 7:=by intro k hk;match k with|4=>exact wZ|5=>exact w0|6=>exact w3|7=>exact w4|0|1|2|3=>exact cZ yF _ 0|_+8=>omega
lemma pg:aB false (ac 1087) 7 (cB 1087).toFinset:=gf (q:=63) (p:=ai bI) (ad bI dr) (by decide +kernel)
lemma xU:aR false (aN 6719) (ac 6719) 8:=
 aA (q:=1087) (rs:=[2,1,2,4,1,1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pg
  (bB (p:=ai bI) (ad bI dr) (6688,0,6687,0,7) (by decide +kernel) (by decide +kernel))
def lK:=ak bI 8 [(2143,[101,66,16]),(2425,[128,80,84,66,16,114,97,48])]
lemma ti:aX false lK:=aC (m:=6719) dr xU (by decide +kernel)
lemma xC:aR false (aN 1087) (ac 1087) 8:=
 aA (q:=1087) (rs:=[16,4,2,4,1,1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pg
  (aT (g:=yF) (i:=0) rfl rfl (ad bI dr) rc lZ (by decide +kernel))
def lp:=ak lK 8 [(1087,[]),(2623,[50,65]),(1119,[101,66,16]),(6303,[117,101,67,32]),(11423,[117,101,33,32,65,48]),(6319,[116,100,83,32]),(13487,[113,97,82,32,65,48]),(1207,[115,84,99]),(3255,[114,81,98,50,65]),(1255,[83,82,114,99,66,16]),(18749,[129,113,82,97,48]),(11614,[132,116,84,48,33,96]),(18782,[129,33,114,82,16,66,49,96]),(18798,[128,64,116,49,96]),(1395,[131,84,115,98]),(18809,[128,80,84,66,16,114,97,48]),(11708,[132,67,84,48,33,113,96]),(3555,[83,80,132,115,96,32,16])]
lemma sZ:aX false lp:=aC (m:=1087) ti xC (by decide +kernel)
lemma vG:aR false (aN 11327) (ac 11327) 8:=
 aA (q:=1087) (rs:=[2,1,2,16,1,1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pg
  (aT (g:=yF) (i:=1) rfl rfl (ad bI dr) rc lZ (by decide +kernel))
def jX:=ak lp 8 [(2719,[117,101,67,32]),(13495,[115,84,99]),(3389,[132,116,65,48,80,97,32]),(8542,[132,116,84,48,33,96])]
lemma qc:aX false jX:=aC (m:=11327) sZ vG (by decide +kernel)
lemma xH:aR false (aN 1599) (ac 1599) 8:=
 aA (q:=1087) (rs:=[2,1,2,4,1,1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pg
  (bB (p:=ai bI) (ad bI dr) (1568,0,1567,0,7) (by decide +kernel) (by decide +kernel))
def ly:=ak jX 8 [(1599,[]),(12463,[113,97,82,32,65,48]),(1719,[115,84,99]),(2365,[132,116,65,48,80,97,32]),(9582,[128,16,113,65,49,33,96]),(4979,[130,50,81,115,98,65])]
lemma s6:aX false ly:=aC (m:=1599) qc xH (by decide +kernel)
lemma v0:aR false (aN 47679) (ac 47679) 8:=
 aA (q:=1087) (rs:=[2,4,2,4,1,1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pg
  (bB (p:=ai bI) (ad bI dr) (47648,0,47647,0,7) (by decide +kernel) (by decide +kernel))
def kc:=ak ly 8 [(47679,[]),(44127,[101,66,16]),(52831,[101,50,33,16,64]),(42671,[116,100,83,32]),(68783,[113,97,82,32,65,48]),(47799,[115,84,99]),(68791,[114,81,98,50,65]),(44349,[132,116,65,48,80,97,32]),(60366,[82,50,133,115,49,32,65,96])]
lemma qp:aX false kc:=aC (m:=47679) s6 v0 (by decide +kernel)
lemma vL:aR false (aN 42559) (ac 42559) 8:=
 aA (q:=1087) (rs:=[2,1,2,4,1,1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pg
  (bB (p:=ai bI) (ad bI dr) (42528,0,42527,0,7) (by decide +kernel) (by decide +kernel))
def j1:=ak kc 8 [(42559,[]),(42591,[101,66,16]),(47791,[116,100,83,32]),(54959,[113,97,82,32,65,48]),(42679,[115,84,99]),(44727,[114,81,98,50,65]),(60270,[128,64,116,49,96]),(60281,[128,80,84,66,16,114,97,48]),(69497,[128,81,67,112,97,32]),(48078,[83,133,115,67,32,96]),(69603,[81,80,128,113,98,49,64])]
lemma qg:aX false j1:=aC (m:=42559) qp vL (by decide +kernel)
lemma v3:aR false (aN 52799) (ac 52799) 8:=
 aA (q:=1087) (rs:=[2,1,8,4,1,1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pg
  (bB (p:=ai bI) (ad bI dr) (52768,0,52767,0,7) (by decide +kernel) (by decide +kernel))
def cY:=ak j1 8 [(44719,[116,100,83,32]),(54967,[115,84,99]),(60239,[131,115,100,50,33,16,80]),(50014,[132,116,84,48,33,96])]
lemma d5:aX false cY:=aC (m:=52799) qg v3 (by decide +kernel)
def AI (_:Nat):=0x8151108090c808420380cd31101fd30fe887f0c3f821fc20
def AN:aF:=(5,1,3,0,0,7,0,AI)
def AK (_:Nat):=0x74308515c76e77000000818435800000a71f02000000828c06fa8001025909670038579507803705e0482024814000001004000000
def AH (_:Nat):=0x10842000421000040820b764a0f19283c280fe48130bf58910bf58430fe54030fe48110bf58930bf594209f59420bb58830bd58430
def AM:aF:=(10,2,3,0,0,7,0,AH)
def AJ (_:Nat):=0x700009040000000000ddd0800002
def AG (_:Nat):=0x104208141ba541620c36698ac4186f15058430
def AL:aF:=(3,3,3,0,0,5,0,AG)
def n4:Array (bt × bt) := #[(0xfffffffffffffffffffffffffffffffff1880f,0xfffffffffffffffffffffffffffffffffe600d),(0x0,0x0),(0xfffffffffffffffffffffffffffffffff2619f,0x2a10e),(0xfffffffffffffffffffffffffffffffff60271,0xfffffffffffffffffffffffffffffffffc5851),(0x507e6,0x187a2),(0x89c78,0x9870),(0x0,0x0),(0x87780,0xd4680),(0x0,0x0)]
def n3:List aZ:=[(33,0,156,0,4),(24,0,165,0,4),(12,0,177,0,4),(132,0,57,0,4),(17,0,172,0,4),(160,0,29,0,4)]
def tu:List (List Nat):=lk
def qD:Nat->aF
 | 7=>AN
 | 6=>AM
 | 5=>AL
 | _=>a0
def tw:Nat->Nat->Option (Nat × Nat)
 | 7=>aK 23 29 4 12 4 4 AK
 | 6=>aK 2 11 1 10 2 4 AJ
 | _=>fun _=>none
def jc:aM:=⟨1213,7,fun j=>n4[j]?.getD (0,0),n3,tu,qD,tw⟩
lemma gN:aD jc (ai cY)=true:=by simp only [aD,and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aH (d:=1) ?_⟩,aH (d:=2) ?_⟩<;>simp only [aW]<;>(try repeat' apply And.intro)<;>decide +kernel
def yU:Nat:=0x1408410844300c
def yT:Nat:=0x90448d05005
lemma o5:ag jc 7 0 5:=by apply bR;apply aq 7 0 0;simp only [aE,ba];decide +kernel
lemma o3:ag jc 6 0 3:=bG (by decide +kernel)
lemma o4:ag jc 6 3 7:=cJ yU yT (fun _=>0x25234363203201322034013214234010432405431423402114234021) rfl (by decide +kernel)
lemma vD:ag jc 6 0 10:=(aw o3 o4)
lemma o2:ag jc 5 0 3:=cJ yU yT (fun _=>0x242340404324053241324040) rfl (by decide +kernel)
lemma fD:bT jc 7:=by intro k hk;match k with|5=>exact o2|6=>exact vD|7=>exact o5|0|1|2|3|4=>exact cZ jc _ 0|_+8=>omega
lemma nE:aB false (ac 1213) 7 (cB 1213).toFinset:=gf (q:=189) (p:=ai cY) (ad cY d5) (by decide +kernel)
lemma xM:aR false (aN 2237) (ac 2237) 8:=
 aA (q:=1213) (rs:=[16,8,4,1,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) nE
  (aT (g:=jc) (i:=0) rfl rfl (ad cY d5) gN fD (by decide +kernel))
def lD:=ak cY 8 [(2237,[]),(18109,[82,48,66,112]),(2395,[130,114,98,33,81]),(12774,[66,114,50,132,99,32,80,16])]
lemma tb:aX false lD:=aC (m:=2237) d5 xM (by decide +kernel)
lemma xI:aR false (aN 1725) (ac 1725) 8:=
 aA (q:=1213) (rs:=[16,8,4,1,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) nE
  (aT (g:=jc) (i:=1) rfl rfl (ad cY d5) gN fD (by decide +kernel))
def lz:=ak lD 8 [(1725,[]),(17085,[82,48])]
lemma s7:aX false lz:=aC (m:=1725) tb xI (by decide +kernel)
lemma xQ:aR false (aN 2749) (ac 2749) 8:=
 aA (q:=1213) (rs:=[32,8,4,8,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) nE
  (aT (g:=jc) (i:=2) rfl rfl (ad cY d5) gN fD (by decide +kernel))
def lH:=ak lz 8 [(2749,[]),(11453,[117,67,32]),(1371,[130,50,98,82,115,33,65]),(6630,[115,83,82,130,99,66,16]),(13798,[66,114,50,132,99,32,80,16])]
lemma tf:aX false lH:=aC (m:=2749) s7 xQ (by decide +kernel)
lemma vR:aR false (aN 43197) (ac 43197) 8:=
 aA (q:=1213) (rs:=[20,9,4,1,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) nE
  (aT (g:=jc) (i:=3) rfl rfl (ad cY d5) gN fD (by decide +kernel))
def j4:=ak lH 8 [(43197,[]),(58557,[82,48]),(64189,[83,114,64]),(43823,[135,50,65]),(46427,[130,50,98,82,115,33,65]),(48475,[135,101,50,33,16,64]),(49638,[115,83,82,130,99,66,16]),(55782,[117,130,99,32,64,16])]
lemma qj:aX false j4:=aC (m:=43197) tf vR (by decide +kernel)
lemma vW:aR false (aN 44221) (ac 44221) 8:=
 aA (q:=1213) (rs:=[16,8,4,1,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) nE
  (aT (g:=jc) (i:=4) rfl rfl (ad cY d5) gN fD (by decide +kernel))
def ew:=ak j4 8 [(44221,[]),(44733,[84,115]),(52925,[117,67,32]),(54973,[116,83,32]),(58045,[82,48]),(60207,[132,65,48,80,113,32]),(42843,[130,50,98,82,115,33,65]),(44379,[130,114,98,33,81]),(58203,[133,117,101,33,48]),(48102,[115,83,82,130,99,66,16]),(55270,[66,114,50,132,99,32,80,16]),(69606,[80,132,99,112,32,16])]
lemma ic:aX false ew:=aC (m:=44221) qj vW (by decide +kernel)
def A7 (_:Nat):=0x60bfd31
def A8:aF:=(1,1,1,0,0,0,0,A7)
def n8:Array (bt × bt) := #[(0xfffffffffffffffffffffffffffffffffffc91,0xfffffffffffffffffffffffffffffffffffc01),(0xe,0x2ee),(0x0,0x0),(0x64,0x2a4),(0x72,0x152),(0xffffffffffffffffffffffffffffffffffff8d,0x1ac),(0x16,0x110),(0x318,0x250),(0x0,0x0)]
def n7:List aZ:=[(88,0,163,0,4),(8,0,243,0,7)]
def tA:List (List Nat):=[[],[115,84],[65,99],[65,115,81,99],[81,118],[81,99,65,115]]
def qF:Nat->aF
 | 7=>A8
 | _=>a0
def tB:Nat->Nat->Option (Nat × Nat)
 | _=>fun _=>none
def wR:aM:=⟨1275,7,fun j=>n8[j]?.getD (0,0),n7,tA,qF,tB⟩
lemma uo:aD wR (ai ew)=true:=by simp only [aD,and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aH (d:=0) ?_⟩,aH (d:=1) ?_⟩<;>simp only [aW]<;>(try repeat' apply And.intro)<;>decide +kernel
def Cm:Nat:=0x14042108443003
def Cl:Nat:=0x68325248a381a0642a
lemma o6:ag wR 7 0 1:=cJ Cm Cl (fun _=>0x50634340) rfl (by decide +kernel)
lemma p9:bT wR 7:=by intro k hk;match k with|7=>exact o6|0|1|2|3|4|5|6=>exact cZ wR _ 0|_+8=>omega
lemma B5:aB false (ac 1275) 7 (cB 1275).toFinset:=gf (q:=251) (p:=ai ew) (ad ew ic) (by decide +kernel)
lemma v1:aR false (aN 48891) (ac 48891) 8:=
 aA (q:=1275) (rs:=[2,80,16,10,1,2,32]) (by decide +kernel) (by decide +kernel) (by decide +kernel) B5
  (aT (g:=wR) (i:=0) rfl rfl (ad ew ic) uo p9 (by decide +kernel))
def bN:=ak ew 8 [(59646,[116,100,49,81,32]),(43479,[115,83,133,99,50,66,16]),(55773,[99,132,84,48,33,112]),(46581,[67,80,100,131,112,32,16]),(58874,[84,100,49,128,113,32])]
lemma dL:aX false bN:=aC (m:=48891) ic v1 (by decide +kernel)
def AC (_:Nat):=0x1948817fd30
def AF:aF:=(1,1,3,0,0,0,0,AC)
def AD (_:Nat):=0x8e80
def AB (_:Nat):=0x24c269243a037eb0261df54530
def AE:aF:=(2,2,3,0,0,5,0,AB)
def n2:Array (bt × bt) := #[(0xffffffffffffffffffffffffffffffffff22a7,0xffffffffffffffffffffffffffffffffffa027),(0xffffffffffffffffffffffffffffffffff4759,0x4258),(0x942e,0x8424),(0xffffffffffffffffffffffffffffffffff99d3,0xffffffffffffffffffffffffffffffffff3bd3),(0x81c,0x4408),(0x21a0,0x5f80),(0x41c0,0xbd80),(0x0,0x0),(0x0,0x0)]
def n1:List aZ:=[(20,8,99,0,4),(96,0,31,0,7),(16,0,111,0,7),(66,0,61,0,5),(34,64,29,0,4),(1056,0,1119,0,8),(49,0,78,0,4)]
def tr:List (List Nat):=[[],[16,66,101]]
def qC:Nat->aF
 | 8=>AF
 | 7=>AE
 | _=>a0
def tt:Nat->Nat->Option (Nat × Nat)
 | 8=>aK 1 3 1 6 1 1 AD
 | _=>fun _=>none
def tq:aM:=⟨1151,8,fun j=>n2[j]?.getD (0,0),n1,tr,qC,tt⟩
lemma un:aD tq (ai bN)=true:=by simp only [aD,and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aH (d:=1) ?_⟩,aH (d:=0) ?_⟩<;>simp only [aW]<;>(try repeat' apply And.intro)<;>decide +kernel
def Ck:Nat:=0x10842110c0300c03
def Cj:Nat:=0xe86824914642a
lemma o1:ag tq 8 0 1:=bG (by decide +kernel)
lemma o0:ag tq 7 0 2:=cJ Ck Cj (fun _=>0x2615312126154121) rfl (by decide +kernel)
lemma p8:bT tq 8:=by intro k hk;match k with|7=>exact o0|8=>exact o1|0|1|2|3|4|5|6=>exact cZ tq _ 0|_+9=>omega
lemma lU:aB false (ac 1151) 8 (cB 1151).toFinset:=gf (q:=127) (p:=ai bN) (ad bN dL) (by decide +kernel)
lemma xL:aR false (aN 2175) (ac 2175) 9:=
 aA (q:=1151) (rs:=[2,1,2,4,1,1,2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) lU
  (bB (p:=ai bN) (ad bN dL) (2080,0,2143,0,8) (by decide +kernel) (by decide +kernel))
def lC:=ak bN 9 [(2429,[129,82,113,48]),(7038,[129,98,82,16,66,49,112]),(9598,[128,100,49,112])]
lemma ta:aX false lC:=aC (m:=2175) dL xL (by decide +kernel)
lemma xD:aR false (aN 1151) (ac 1151) 9:=
 aA (q:=1151) (rs:=[16,4,2,4,1,1,2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) lU
  (bB (p:=ai bN) (ad bN dL) (1056,0,1119,0,8) (by decide +kernel) (by decide +kernel))
def lq:=ak lC 9 [(18814,[129,98,82,16,66,49,112]),(11742,[82,133,99,49,32,65,112])]
lemma s0:aX false lq:=aC (m:=1151) ta xD (by decide +kernel)
lemma v4:aR false (aN 52863) (ac 52863) 9:=
 aA (q:=1151) (rs:=[2,1,8,4,1,1,2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) lU
  (bB (p:=ai bN) (ad bN dL) (52768,0,52831,0,8) (by decide +kernel) (by decide +kernel))
def kf:=ak lq 9 [(44925,[129,82,113,48]),(50046,[129,98,82,16,66,49,112])]
lemma qr:aX false kf:=aC (m:=52863) s0 v4 (by decide +kernel)
lemma vV:aR false (aN 44159) (ac 44159) 9:=
 aA (q:=1151) (rs:=[16,1,2,4,1,1,2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) lU
  (bB (p:=ai bN) (ad bN dL) (44064,0,44127,0,8) (by decide +kernel) (by decide +kernel))
def j7:=ak kf 9 [(44159,[]),(47743,[101,66,16]),(69501,[128,84,66,16,98,113,48]),(74110,[128,100,49,112]),(48094,[82,133,99,49,32,65,112])]
lemma qm:aX false j7:=aC (m:=44159) qr vV (by decide +kernel)
lemma vS:aR false (aN 43647) (ac 43647) 9:=
 aA (q:=1151) (rs:=[10,1,2,5,1,1,2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) lU
  (aT (g:=tq) (i:=0) rfl rfl (ad bN dL) un p8 (by decide +kernel))
def j5:=ak j7 9 [(43647,[]),(46455,[131,84,115,98]),(51063,[131,100,115,82,16]),(43901,[129,82,113,48]),(46461,[128,84,66,16,98,113,48]),(48510,[129,98,82,16,66,49,112]),(51070,[128,100,49,112]),(43423,[134,117,33,32,65,48]),(58811,[84,133,80,66,114,96,16]),(59900,[82,48,66,129,112])]
lemma qk:aX false j5:=aC (m:=43647) qm vS (by decide +kernel)
lemma vN:aR false (aN 42623) (ac 42623) 9:=
 aA (q:=1151) (rs:=[2,1,2,4,1,1,2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) lU
  (bB (p:=ai bN) (ad bN dL) (42528,0,42591,0,8) (by decide +kernel) (by decide +kernel))
def bS:=ak j5 9 [(42623,[]),(60285,[129,82,113,48]),(60286,[129,98,82,16,66,49,112])]
lemma cG:aX false bS:=aC (m:=42623) qk vN (by decide +kernel)
def yl (_:Nat):=0x28270019312920f8e91910020841c00602403e3031e1d18e0d8d0c8c0b8b0a888028504c483c3844400101e1c1a180e0060b0a090807003030282018100801fbb98bdd7a82ec539c87a00ff503fd43ff54ffd10ff083fc40ff0c3fc53ff18ffc31
def yn:aF:=(10,1,7,0,0,9,0,yl)
def ym (_:Nat):=0xa49b3289cfee0003c11e62e10c1e4000235000513996000090c91cf0a000013a78dac3f26c00039c5cb8000000000204a000000452c001633e0e551fc80b152f0f95a89a255e23881a8be81b938018248c665c070000000000b3bc9a800000031700028c3072b06ecfafc98375010470c01e16716e074d6b0bf948ee3ac9600036e0054814054a5d5892c4d40b354401d8907a8d086167486866b2610135be1dd11650170cee09f0f01bcb5800000010d202243f318eef1419c646e0a9a0079430db52928c52c5193c564cb39a6900028ec0012280375062865214c24898f806a2a5df5d43e1d42ba11a4fe586827629805dd992be81c8003761a6d0ec800000000072b8000c8986beae00000018581727cae660c1200068bc0011c561f0148000b8c0000001cb4c5e711000138985d121316f8741ed000000000000000009074020000004d29b7e000c0d671818d8a3e1049165c75b693b0000000c7511c313d41fc131606bb107a0d043607013300102070000030000000461000006da150300000025000000000210610700003013010000000a0020130090060020020100100240030000015000100100020072001010001104000000010000400000000001011
def AS (j:Nat):Nat:=(if j<1 then 0x4670b12533d10c75e8c8b58478714c78518d7ffe317a00012a9ac91478d191b210c32553e54c93f89481224ccae8c8db6fde254791fe4e848fbc887bfd7bf91489036fde2547dcf8012e849566e24b9fb14c8811a0e059e352b5153447cbd4232d7f49221033d272641407a231b409789c248c37effc18880013340f091678851c118ebe79ab9993d531d8dc499a05bd0c116be4b20866cfc8181973f508195bdbb50994f7c60a504f0c8428b9e9121c0ac4fc46a1120e04a60f4453fb885004944e5f860055bc6ff42c4127799d428024a1e7ce7ac1704adc7e20451ffc4244651f5f0228486f4f0a1954c1e8977ea4a053be12443c9c3c6580589afe03afe94c94489efffa830090fdb8d0417f449000ce5f928a32dffc2d0614d27f807b0a67cf1f4d91f647d4208fbfe3700101096bf0781268499f1f02000903ffe01040482fca44652ffe289a4fc122aff8d4941804bdf23604101297c7e2140124af7ee811a7f861011d78f7002c80953e381127d8e0211e7f299142fbf18650920df8cb8019cf270f30e0547938798702a5ebf9031120250f9f5818890128f270f30e05400fe351d6404a258208d1b924507a3c1d8e86f1d841349848218d86b128212494478f110820c0a8e62006815047c230948a42161f9088a0318c9c0a1707c9404221c0c881288b0503b15130a240108fc04381b1a0844030838cc0801088b84e07148944900150b4582b1787c010b2846416a08101e7fcbfa1f92fab7c5bddde64f0b778bb55d82e9e73db929c58e0c6f43739b5ad886b9b591a7ed1d68533b5996cb263d319988cc2b606af8d78aba05bcad9566ab10570ab25534a8d52fa8ed41e9ef4eba72935296e4a92505254906477a3591928ae444219908c8224009f80f6c78e3c09da0e727113711ad0d0066031e1840bdc5d52d89660ad254f29413e49b64b1247919c87c4161f88ef472036519c0c605f42df15609f849e22e105076437c19a0bf054424c0f9066025c0c4035000524114a83d264f4b885240f4b93d2a234983d2a4f4bb3d2e6f4b24d2813498352c034b1852c6d4902d242d4b93524094884d284d4aa3d26334a0bd2a614b0bd2c13498852eaf490352c734b1bd2a274b13d0e4f4b01d24134a13d2403499352e334b09d2407498b522014a8c52e2f4b08d2c114a84d26134ba4d2e8d4aa3528334b9b52e61498052c054384d0e4d4a0352a434a9152a474b84d282d4a8bd2c0f498bd24014a002ae4cab8c32846eb1caae10ab883282eab84aae22a393ca40cabb0c282cab91aae4aa3932ae0aab8caae2aab982aea4abb128e132983aaea6ab913a610ab8a3a612aba32ae6cabb1aae26abac2ae4eab822ae42caa3aaea2ababaae048b8a1ae462ba9a2e260bb192e660bb0ffffdfdfbfbeff7dbdddebf3f54d435011018c53100310c020 else 0x2a514f996be52268663fe3f325000b13ca8643f53090a16b2b1c08e6b231fc5008b7c382938e31a32317b310ffc6068f40910413efe1f6c01485ee44d9b654c87a249bf13a091bbf9e4f32ae0e4e3d3a92ab09fe26af3c9e651e04e8247ae7089a62f4408edf4ca44663e5120b04991818324)
def A6:aF:=(122,2,7,720906,68,13,1115,AS)
def AW (i:Nat):Nat:=(if i<1 then 0x8d2114ec42d555274bd2a00000161bc698a2be56e421c83e4eb400028745174e28a00000000000286640b140300000000000000029000001258a89ff00992fe0002b3da039c601254b5a7f81c0000a2dd89140da00006de2a4c59326092843a17450c9f98641eb8a6b0f032194d57899800010e20001c2208b800000002805000000000000000585b4e2b828d9a9b073f668000000008cd0000ca8dc8ad2baca4800000006ec3000060efc281810153c0000000217ef0d083fe87f00000001a1b8000781ec09a000246b324e0000a18c00039010001415c9baeb4c41fa947800010ac718343a800b516940168a70089713c725c00019a69eb0a0e0430e88f585868e0660223a8000a20e09dc8435154e1a3a209844215f52428c1cc67013432ca00034b5802270ffe195659f02531b064907608000e55761ca05e994bc50c000024e80003a02817f18688f76221a3d7d8af0df90eba87909b1876f302c105aa780000000000000060c0e190431ed5c5ec7000063d08b774286a09c1800006874a10ac3148761ac93451490187128de904f03084bb0000a1760000000300806afc2d7193f6fb0001841047b1299605400e8ea3fab29decc4b4cb3f14996518be8037c8c662106570000523a41e200014bda0cb8046d9e082a6aa400000259c4890f3613a227b440214710bd222cc55f95a52ee000384b99090001f43ac0db05dc2c380b606a4018e2c7c29000020e0b2c1c36d592581d405720e2070800051e58148179e57ec06e29fd94ff1596e576499887e93d52040000000000000000000000795500018280000403f0001612c0000000d17805980000000115f98a2c6b8000311dd8c356120d5b0c303bf0199866f08fe41a48e86705255e23385c8000b199fa7000050bf517da340801104c12de04508900000b134e067c961c1421cdc609488c1179277c579c8b767531636558089d347628365a2ca9e67f39dc94eff59cd5e90d481580b63f30a091557c001e97ce0ab2092d9b9923c13184648424ae092a2000251800e365b6ec4f892fb1b00c5dc12c482812e2f0e3ac0000000dd56a4e1cbce14af06045e8559b8202a28aa3599f78a280094d6254a491b0a46e5c4126684e456a0000c079b020000034f4b950b30000428604a800000012236482a88a00000000000000050ee000255e0000d1f600034aeaabb506cd2c00000502a8681003000e00140330401a0204c8b1a0000181040800456140030441602023011024280ba0254000865c1840010380140418f100c0150e04008001d0071a100802810081021810300000813204004060008e000c00e000c78710080080004291040029d2a44b0600006020a004820600003002c0042e002800c1808804104021e0c1810804080000440006000881824381004010402081091e001882208203 else 0x1b4a50500001d9fb975a15d240d09f665ca19400010148000d1120470000302ea103812ad92800041b8000000718e4000169580000000ec7a54fe07d532f9ea60000000191fd235ab94000005ceede82b68ac114331d200000002c309023e0d6a8e255930f60000c3e469200000000000300c89e400018b2000032dae49dca328dd0000a33c802b87e00000002020487dc8f05b1242c8cbf3068ec0c87758a5e2ae00033b16092dd50a395c36506b110702c1017c118ae2964af86cfc2179248c7f843873f929c843749a8d53e0a64b7917a78aa300f619f11a0a6c8001a2da47e4e380c952035c3c914c125e79dcb032d7fa52532f204a38c452e64523c2d6831f0269d1e3b6000046b502a1432594f8042e11bfb571400000a50987ce83cb1f0000031980004d6a0001094d53200010bf800016ed000074c40006015000000021b6800000000a15c1ea832e2e1639ec13384f000000004985c7752fb3484c94632b82150298cb54f6700000000000084291da000200d009f000000010a20000000144eac4c90ba0127cce6836cb09b02f9c9c5737045411fc4dc83c51313029e144400d939d939a26f84e6069a63962ca054f61f393ca2d000fd)
def AR (j:Nat):Nat:=(if j<1 then 0x6525d9a24904d89415292e2f4660a546a02949804e92e6012580e3841401982aa92a4d525c84a4901d496028e285512442340a129793064f2c6e9261e3aea93e49204ef2a521754a9a4b94249760e92407125d43a4bb2b5160ad12a2b066119c4a8b94954511aa4e1c508d249035714182e282f524812a4b9398d2068910f412482ca4b09d49727c92a44de58dc44409749204d1ac0e125825c4b0d4714236e2a8d866008a4c28e79317092e42925d820cc2b55d52a91ac2e1e4c2a24ba8349730292e8cd25d4224a8b6496366330539261d244a8ad8d845292e6cd248118cc2b4198224a2c03125ca7c6900b49406692e4f622063a4b954498244330ce125465bc982c4971871a60a52614a24a0598d2071110341e4c27a4b0351983511102dc6619a3cb1d44976583306a525c8424b88279537092407dc551724b0cb19855e92e42dc502a46c1a98d2034f2615d2614e82c1220487860b0e18161e182c33629523e090efd5551e8243be05821e0b06a0e5cc30243d75952a27ac274e480f36aa380580b20b0ec98212890b09039730a230754e20e282c14d05836682c270d50a6b4a0c20581408a4094160a314a94d05870a4302408585002c22821602c0b0ad8e4c260ac0b105802ceaa6e1048119ec01d05823e53047ca54878243b94572707b0a74858081c985904879e7ac0741604f9ca89e3d72328ae6a5b505c02c3ba40818a52c27ce548f02c14e21524042c0801605b20a0a861429052a538121e81aa12005849c130d38121d91aa11c4d63aaaaa50016013bea12935423eeac6e1654ab34a0ae21514082a2d0a480fba98504171307ae429a505c9cb1d805859882c0701606702c3835954ac52a23c848081cb09e05818c6ae500e580f20b8830487a6824070e4c268243ad41863882a471358ebb4a12f5554a70a82a41604810c0a005822a0b0ef0d5c9db2a117418538090ec0854483a904804878452a27c360600243b121204042a441d4c5c20b88929813e72e60ca580f9ea89d29522a8a40881604796a11e1d4240030d389508f98a11cffbfdff3fbfebf7fdbeffbbedfafe7f7fd7f3fbfedf7fdfb7ddef77dbf6dd9f5fd3f3fcbeffbf6f7bbebf9fe3f5c5535c1535915358d535815350553501534c5534c15348153441531c1535d5435c5435c14358143545434c143481435d5405c94058d405894058540581405514054940545405414050940505404c9404c5404c140481401c9405d1105cd105c91058d10551105091050510501104c9104c5104c11048510481101c9105c8635c4635c063480635c4535c053480535d8405d4405cc405c8405c44058440580405484054440480405d8315d4315c8315c03158031548315d8305d4305c8305c43058430580305483054430480305cc2058c2054c20500204c4204c0204802044020 else (if j<2 then 0x91681d011002a0fd070f4380c4270111f8940107c110cc0787d000a6000b8000b02b0bc2deb07517a69d25e8cf4179efcdae64f2cf94fc90e4271bb8b3c3fe1870a3833c0bdfe6fc77c5bd4ddceeb7743b8ddc2ede76c1b4bd966c7761faf6d6ceb0f569a9fd4aea174f7a6ad2de93b47ba2fd10e8273fb9e3ce566b3333987cbc65b32bb94cc9c64b72258fac6fe34f1898b1c4f625b101868c27e10b06d81fc065fdefc77d5be45ecaf3178dbbcddaeebb73eb925c2edf36ecb70db42d836b3b53da62cff673b2ed93ac8962fb0ad80ebe75dbae756d2b41595abed5d6adb553a9dd482a0b4eea6552be94f491a3cd19a883430a12503e8013f39f44f627953ac9cace1a6f135a99fccce63b30d97a4b9a5a52c29554a7650f27d934c97a49923a912c8624051e38e3c6ba34518e8c2c5b22b514289d448220b0f486b43261830ae84b421e0e506282b410e06701d807400dff6fee7f03f55f8efb77d5be7df2af827b83d89e9af367943c55e14efc7773b51d8ceb97513a4dcfce7272f3941c8ae39711b855c12df26f5377dba2dc56dd3689b18d776b5b579aa4d4769a34a1a2cd0a67933999a4cb6655b27190ec6c62f312186cc186052ffd7cebd25e12ec5740b8d5b62d3566ab28586ac0d5e8ae456a2af5556a9a53ca98d480a26503a7cd3cc9da4e026c534c98c4bf25b92b894749ea4892068ee46a231d1688a744821d90cc85341c20910207f43ef1f1cf5e79b3bd1d80e8c7383901c34df46db3659ad0d3869033f19acc94637311981cbe85d42dc16b8b445922be1574aa654229a9450a024ee26992dc94e494242117c87c42e2098fe07c43cf1d20e507043611a38ce864e31c1830bb05a42bd1508a0c4e425e12788fc456212101079c3a21b20d206342f81680aa84d424a10b079839016c08e03080cc00033031d25c9fc4b0bb71429292e21a3481924c3a1198262a2c111261e824b88549208c92ead525c6ba4904c71425e92403d2618e38a1188d20aa9304963481aa490228d2062f26142254578cc336198086910518660670cc32c71422ef2415925c8c0cc10c492096f24121248104440a45161831a413d2486324bb038d4253110284660d9a4b881498366330269c549dc4a8d249765a92e22925cd48cc22971418712a2ac6605224b09f493066baa501e4c24a4b94171423292c07466050a4b013893154e284c62204438a0c449529692e4dd25d5a0cc2b689525ee240edc551ca4bb2e1980191a4129754a4a4ba8289515d1a41046608da4b88b4920b092e22125ca224a9b35d529f12a20e25059bc9932198074930c4de4c5d46a8b849709e3305246601946902d49765e92e4312548a28b09a79609033012525cd50cc2ba89516a92e46521ca324c30d49202092c13125d8138904081207e3303112549a44408189516892e2 else 0x340a25a5322c508f112816314116c3de54064dca108c686c049ec18d808de0829e121cf18c88708802c913c053686908722a6065d5041b011814e2218030127c898cde1045fae0190e111e05df2863ef912326700c746877788680cc210053a42a3435615f2106c359147a03199093c85065f40630ff70992f091d6cc53108c84e116c50b5450d0144be0640f4a63c9700c86421c8b2da1d9923005f190e3e018ddc2106b41602dfc0867848d7a886ba887591588b5e282f71020d80ad4a19e0559147cba06417d1a0f6f8489bc215585808f90aad09a45a83b90a7f0488c046f0415a234057a887dfd531a78c4bc06dec8c6e021b3e9127810e9087b431800047f00c7de40c60f0020f47e8220fd0436fdb422651f810880159731d7a031d65625ffab00233cc0d8084f486748b682409780cb036fe60190bc0319c22c6073a780648790506c05730922f2153c2a0cb619e0431942af60636810f5886012d7219028958b78421d6a1d5867f443cfe000c8bfd44885f4a63302cf06200c7ca18cf2238fe26300e70020d7d79221ec0f3a78064581005af232f2863a703ba14336236020e0c4c7433e221eb8140400d02388980dc450684604c040147262de108b61677416403630d86eb91d21ac8ab222fc898de02581278463a3433d243d41da143b88a90981133c492c0a8147286300a43ec0a81521cf6663e2e18d7c486a05b415026026708d80bb262602ef806360213a43af362642048e06e1848ef10a0ee22a4c495ba625fd0811550340590e2c735843be223b11e6989f6022fe810118edf1613b79231b00efcc312a023810f888f88a78e219c84766235fd020232f848796c3d05967c0844edb498cb6e848c034039f021107021024fc218de029a42be08e62a86016d509453b7c584f35843ce68191c057109120798c18cbf80639a424ecc590e8190cb090cb0923c10193b3263ce48c75e24c72c904bfa04046ce68192fc402678083e018ee2121fa230fe404c97845b65511bc218cc0b78424ecc49dbe08655bc09b50863c8508bd0d8b035c91977fa0910023023e03ada98cedf16138047e0370147d309195f6021f023c8740c85fa44c97c44fb010b8133ca8100ccbfa0404698428f448c990e81917c2434ecc45fb1482819e690ad5245fd0202367340c96223e446808af9249f021127c08449ac21d72923227ca48c8bc4232c24ac467c0679c46be80443e039f5a089b2b221f790c26780b3a1319b810cb092f91187e1d0321f01b7ec0c7b59288708829e5ff3e22a9c6fd08248df7fcca0824053cbfe7c454be30c6f1a092a21088340e91013c2805841913414844b4961d8042140842076168d1128a002041230830042241c581bc54308404e071228552789d4186d154a02409604480450c))
def A5:aF:=(387,3,7,2359386,103,13,1105,AR)
def AV (_:Nat):=0x4048000b050c190000427c0b6c0ae0f8000000104ef11dc59702504c0002c1800020759179d2161bfc05f1f9c566d19c76b1d2c3080d1a07c04df1a00000003098000c08207790bc000d109d3bd0a68070018000312ec6ee1e603900c583a64be435318e5361509868521b480d14000061f544fe9a2085606fc212022422905f08741ac0000003c0b40dd01e10ec84011cbc52b0e0f51a123465808c85a1c0444660f4c1561b5c0ce444000812a82800f105b000286710ca054a1b085800014600000000307c483404304d4074c330000000c1ff0841038000484ec36f1c287a81ef449f20986a315ec62200000070b948101a6f5f2222844000041c0000000500a40d0002025706b864214c0000002043000145c203f51d0003c61000342b211600150a8000000000011e000081cc00059ff03f0001b45b17c01611c5424e00c00014dc05d0000b5a6c4444144b2c2c0147c7cb0440007013866515700a404048b3520eb08aa5695d0a755101400104110500d38b50100a080
def AQ (j:Nat):Nat:=(if j<1 then 0xcf10e13bf579aec5c2b756a2cd588b015e2b6560ab1536a0d39a634a690d19a21422804f49c9362684c39772ce52c8d8f91d23645c8a911e1d42e84d06608c057f4fc9f53da7a4f1ddfbb775ee8dcab8d6f6dadb1b4f684cdd9331961ac05792e65acb0d5baaf538a293f2744d09812aa464768bd13a0d40a7d4ef1cf38e6fcd91a933863cc39772de570aa1422684908e10b1f43c86f8d71922d85309b1242183e8710d0170268420660940d00f0001330942649c6ca0b0c541874ac3246645536a94785422c1330a026430ea90069c914e9a40da95064209034752033292241b508ce49842a9637a7930252481b8cc8a5119128790335f508906c899c930be52a544f206b8ccc250991c3ba413cf245206c91ad9417cfa844e250869e40a6d94158510f54e21ec0ccba19d601211318dc244b7098566d423052a54195806b2b08b85421213235e250829e48a9199501128433450821443dd6d4238c92274264a284c9533c984a1324d21480f4e48a38d510312e219f5088c4a0b128878cb28475b508dbea1145161327ae22275457b6ba8715911d324039c545ccc903919921b12c3136505704c95c6d422e2b243cf545598a11b7d730faa40d46644588c915454195192245b508b70984189710e2b303d9244164a0bfe52066bac251858471e40a230876ab2847cf206cc89857b154787b0eea2508518aa408942123930b784c26489014b952a942c983348192aa11dbd209c01300c1261290a952b520b6013080921f134a116348396f284470505d9643daad30bd028427fc7f4fe5fb3f57e9fd1f9bf2fe4fc5f6be97cef8dedbd6f87ef9debbcf76eebdb7b5f69ecfd8faf75de9fd2f9ef3be6fcbf95f1fdf9beb76e7ecfb9df3ae6fccf97f1be1fbf95f6bdd77abf1fe3ec3f4817154d635915321d6454d5458d535014154d54501535494054c87501535493054c844c15361d2054d304815321d2054c81481535491054d204415321d1054d861c1536107054d811c1535493050d424c14361d2050c8148143205725018158d405056250161581405c954501525454021d5150172505404c532501544c54054531500874c54058d30501614c14058130501524c1404c5305008148140549734408758d106095444181551105095444087551105494144142505105d94044184481105cd20441424811050520441404811060c72441541c9106017218d205c4634817018d87480634817114d825c0534817014d87480532052014d525d84054576101425d84048176101825d44060575101615d44058175101525d44054575101205d44058573101605cc4054973101515cc4048173101805c84058572101605c84061971101855c44058171101525c4404817110182584405096110142580405c5511008148040549760c1205d8305cd31081714c420 else 0x2a743e6105ac2095c0d7b8c6c040101078c50c0aaf41113c18a9815e610c03b2626c097a420000b213210020464200000000000100005023e22502001a0800026c21860c6f60300003e2200701380b50401682016424080000f88801808000004a0c3020152b14d2100078314584812e909c056432837488c866108be314a080073625f90ac8501b2100205748980990802c7a4880134853f090ee910000548802e02701004e210003762005e9093613e2200dd2168d08034c218058442710cec0e90804c8402c04016023244c04c91260748690992206610100a2784ed04271200030d019507a0004620e00c830008f90124ec020b004a828120fd1662d4548002c43e0b80002905e0ad0002dd73ac74e689ced99f28e46c7d8)
def AZ:aF:=(137,4,7,3801188,103,11,1064,AQ)
def AU (_:Nat):=0x247800a1c00085000a0de22d610c00000272000f1bc2ec1b90725c1d40191e0508b44d01001a1400000c080000000000042841210
def AP (_:Nat):=0x2c08168400e410815871042002c08000003504205c102f02d800181687ab67230efab6722e19d5c1ad9985712ce84403d49524c087481538fc2a520605544430dd636408759153de85089850520443f40a1481524c153f6848171509601039a92021d4255110f4a4814258175103d2542245205d4409dc6949850520443d8542245205cc40fe0509302052050f9a542261205c440f2950891481761039d1302048748153f625092058173103d6151481525cd10b0729d645516354e07ca9549861c153
def AY:aF:=(19,5,7,0,0,8,0,AP)
def AT (_:Nat):=0x81900
def AO (_:Nat):=0xa3390a134a4c28290221e50549302048748153
def AX:aF:=(2,6,7,0,0,3,0,AO)
def n6:Array (bt × bt) := #[(0x9017721c30,0x14b5bd0008),(0x500e080936,0x634240ff36),(0xffffffffffffffffffffffffffff4ca8886101,0xffffffffffffffffffffffffffff8c0d9a00c9),(0xdc001a04a,0x12b065ab12),(0xffffffffffffffffffffffffffff815101844f,0xffffffffffffffffffffffffffffe94a0254e5),(0x2200761284,0xca4842b0f4),(0x0,0x0),(0xffffffffffffffffffffffffffff2220844287,0x31b2254f02),(0x0,0x0)]
def n5:List aZ:=[(24,0,167,0,7),(2,0,189,0,8),(6816,0,6687,0,7),(1538,0,1725,0,8),(43010,0,43197,0,8),(44546,0,44733,0,8),(54786,0,54973,0,8),(160,0,31,0,7),(17922,0,18109,0,8),(1664,0,1599,0,8),(42624,0,42559,0,8),(47744,0,47679,0,8),(16898,0,17085,0,8),(1544,0,1719,0,8),(42504,0,42679,0,8),(47624,0,47799,0,8),(2208,0,2079,0,7),(1,0,190,0,7),(2050,0,2237,0,8),(44552,0,44727,0,8),(54792,0,54967,0,8),(2688,0,2623,0,8),(2562,0,2749,0,8),(12304,0,12463,0,8),(42512,0,42671,0,8),(44560,0,44719,0,8),(47632,0,47791,0,8),(54800,0,54959,0,8),(68624,0,68783,0,8),(1560,0,1703,0,7),(1696,0,1567,0,7),(42520,0,42663,0,7),(42656,0,42527,0,7),(58370,0,58557,0,8),(58016,0,57887,0,7),(57858,0,58045,0,8),(44568,0,44711,0,7),(47640,0,47783,0,7),(54808,0,54951,0,7),(44192,0,44063,0,7),(44034,0,44221,0,8),(35,0,156,0,4),(4,0,187,0,7),(9,16,166,0,4),(19,0,172,0,4),(129,32,30,0,4),(36,128,27,0,4),(20,8,163,0,4),(42500,0,42683,0,7),(47617,0,47806,0,7),(25,0,166,0,4),(14,0,177,0,4),(44036,0,44219,0,7),(13320,0,13495,0,8),(68616,0,68791,0,8),(64002,0,64189,0,8),(56,0,135,0,4),(7704,0,7847,0,7),(12312,0,12455,0,7),(68632,0,68775,0,7),(11296,0,11423,0,8),(26,0,165,0,4),(52738,0,52925,0,8),(54785,0,54974,0,7),(134,0,57,0,4),(2592,0,2719,0,8),(52896,0,52767,0,7),(13328,0,13487,0,8),(3080,0,3255,0,8),(168,0,23,0,4),(4120,0,4263,0,7),(1152,0,1087,0,8),(6160,0,6319,0,8),(47776,0,47647,0,7),(44548,0,44731,0,7),(152,0,39,0,4),(1032,0,1207,0,8),(6176,0,6303,0,8),(162,0,29,0,4),(164,0,27,0,4)]
def ty:List (List Nat):=i0
def qE:Nat->aF
 | 10=>yn
 | 9=>A6
 | 8=>A5
 | 7=>AZ
 | 6=>AY
 | 5=>AX
 | _=>a0
def tz:Nat->Nat->Option (Nat × Nat)
 | 10=>aK 177 223 4 13 7 2 ym
 | 9=>aK 185 697 7 15 9 2 AW
 | 8=>aK 39 199 6 14 8 2 AV
 | 7=>aK 11 35 3 11 5 2 AU
 | 6=>aK 1 3 1 7 1 2 AT
 | _=>fun _=>none
def dk:aM:=⟨1215,10,fun j=>n6[j]?.getD (0,0),n5,ty,qE,tz⟩
set_option maxHeartbeats 0 in
lemma dV:aD dk (ai bS)=true:=by simp only [aD,and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aH (d:=4) ?_⟩,aH (d:=0) ?_⟩<;>simp only [aW]<;>(try repeat' apply And.intro)<;>decide +kernel
def cI (_:Nat):=0x764260437506145074436550744365407443653074436254734362657236165272361651723616317236163071362652713626427136264170435540704355307042554070415550704155407003547070035450672465416714653065360765653607546536074360634121606341106060416160604121605341216050412160134121566307635663075453641483531322715313227053132261531022715310225051643070516430505135227147145542463462604606417142560343425603324256032142530343425303324246037342460371424603434246033242430376374316743743167337431663374316623743164337401475374014633734657337346572363562323635622136356210363462323634622135461480354614403546143035461420313522823135225231352232313522213134223231342221313122723131223231312221310522323101223231012221304656652434038317632675154630701546306015463050154630101545307015453010154230101541307015063460150630601506301014463010135322521313228213132275072455740724555207145574071455640606418106064161060541810605417103645676036456650364566403645483
def bq (_:Nat):=0x6453043210043201064500432100432010641306357005416106410043210043201064025174200502100640251742004610006402517420040210064025174200401700640251732003610006401517420050210064015174200301500640103457203042106324067501054021063200675010540210630120364103201006042537420030270052345207130072600523452071300523005234520713004270052344207130052400523052071300623005230520713005230052305207130042600523052071300412005046010432010421040351306420124300403113064201632004031130642012430040311306420123500315406417200162003120021053021061031200210530210310312002105301602103120021043021031030420315240103600304203152401034003041031524010340030410315240102300254064170302604002460057610056201024600576100341010241004321004320102036001674012501020340016740126010203400167400146101450057630012561014500576200451010145005761005620101450057610045201014500576100342010145005761003415101450057610012031014064135200402100140641352003021001402413520040210014024135200302100140241352003017001324023401034021013200234010630210132002340103402101304607241072010013046072410620100062435247003640000624352470034500006243524700273000062007561005620200620075610034102005123542700435000051235427003240000461735642056434004517156020561200045171460207412000412314602037120003247065140651000032470641202506000264362471037520002643624710365200026436247103462000214726531065320002147264310473200014236427104362000142364271043520001423642710325600014236427103251000134746530065400001257465300654000012474653006540000124746530054360001247465300543000012473654206543400124736542054324
def dw:Nat:=0x5021042110c0300c03
def du:Nat:=0x24914891a0c85405
lemma tI:ag dk 5 0 2:=ae dw du cI bq 0x7570 rfl (by decide +kernel)
lemma tJ:ag dk 6 0 19:=ae dw du cI bq 0x6f311660000238033954395f3a36481e4dbfb1 rfl (by decide +kernel)
lemma tK:ag dk 7 0 32:=ae dw du cI bq 0xf456a7442354b2f19185c5c34004fc7ad00d8a4cf9f00a4be00d000a7a99000 rfl (by decide +kernel)
lemma qN:ag dk 7 32 32:=ae dw du cI bq 0x6900281b446259441f4e1a250b186118056a663a0718715c536b661845495029 rfl (by decide +kernel)
lemma qO:ag dk 7 64 32:=ae dw du cI bq 0x5b4500305300182327273c18131712683b18185d1118451800442b005c472337 rfl (by decide +kernel)
lemma qP:ag dk 7 96 32:=ae dw du cI bq 0x1604440027000044006c5a5d511a583269584a182f1a180d1418491866454010 rfl (by decide +kernel)
lemma oi:ag dk 7 128 9:=ae dw du cI bq 0x1818403d3232183c18 rfl (by decide +kernel)
lemma yI:ag dk 7 0 137:=(aw (aw tK qN) (aw qO (aw qP oi)))
lemma tL:ag dk 8 0 32:=by apply bA dw du cI bq 0x930097c585d69c0000848a00a4008f0000b6a88700820088b6808a0000000000 2 rfl;simp only [bk];(repeat' apply And.intro)<;>decide +kernel
lemma qQ:ag dk 8 32 32:=ae dw du cI bq 0xb0d2a0cbd7a2000000b5b2a3bd008a84ca8981c4848e00829d00aa84c3bac898 rfl (by decide +kernel)
lemma qR:ag dk 8 64 32:=ae dw du cI bq 0xd5b5bfaaa4c00000b583a884d3c6bc84bbd984ac009fb400cc9e84cd92b8c100 rfl (by decide +kernel)
lemma qS:ag dk 8 96 32:=ae dw du cI bq 0x8484a997a3a5d48484c3ce9ac58084a18497c5d1bfa4aa00a6a88080b6b9b6d1 rfl (by decide +kernel)
lemma oj:ag dk 8 128 32:=ae dw du cI bq 0x2d5646645b00582828462842005b188684a4d6a4b9848b8a8484a3bf009600ae rfl (by decide +kernel)
lemma ol:ag dk 8 160 32:=ae dw du cI bq 0x181846063e5846581828564518155d28555b2863180a18185d00585b563e582a rfl (by decide +kernel)
lemma om:ag dk 8 192 32:=ae dw du cI bq 0x282846734500004626235b5d465a5b27671815186e18185823092a2d5e181828 rfl (by decide +kernel)
lemma on:ag dk 8 224 32:=ae dw du cI bq 0x16582818181846464667581c5818462346241826185e18585b2c586d334c0046 rfl (by decide +kernel)
lemma oo:ag dk 8 256 32:=ae dw du cI bq 0x58115842284618285b18211808181828465b5b410e732045082358005d15183e rfl (by decide +kernel)
lemma oq:ag dk 8 288 32:=ae dw du cI bq 0x2c6a4572183f581822416e585801235b083e182843461818232c0856575b1d6d rfl (by decide +kernel)
lemma os:ag dk 8 320 32:=ae dw du cI bq 0x465d00452852112d0c4558461858232c56234658330818285b182a5b1846185b rfl (by decide +kernel)
lemma ot:ag dk 8 352 32:=ae dw du cI bq 0x2e2d5246235b43283f18185e6546286a01574546000027181818282d5d004618 rfl (by decide +kernel)
lemma ou:ag dk 8 384 3:=ae dw du cI bq 0x181827 rfl (by decide +kernel)
lemma yJ:ag dk 8 0 387:=(aw (aw (aw tL (aw qQ qR)) (aw qS (aw oj ol))) (aw (aw om (aw on oo)) (aw (aw oq os) (aw ot ou))))
lemma tM:ag dk 9 0 32:=by apply bA dw du cI bq 0x0 2 rfl;simp only [bk];(repeat' apply And.intro)<;>decide +kernel
lemma qT:ag dk 9 32 32:=by apply bA dw du cI bq 0x8494bf9d84d6b6b6bba48c8dbfb381d600000000000000000000000000000000 2 rfl;simp only [bk];(repeat' apply And.intro)<;>decide +kernel
lemma qU:ag dk 9 64 32:=ae dw du cI bq 0xa49bc284d681a4d600d6d60000918184bdc5008484b4d697daa4ab9d8400c984 rfl (by decide +kernel)
lemma qV:ag dk 9 96 26:=ae dw du cI bq 0x8cbf8495d68a94b7d6d6c9af94bfa4a481848481a499ccb48c rfl (by decide +kernel)
lemma yK:ag dk 9 0 122:=(aw (aw tM qT) (aw qU qV))
lemma qM:ag dk 10 0 10:=ae dw du cI bq 0x0 rfl (by decide +kernel)
lemma dc:bT dk 10:=by intro k hk;match k with|5=>exact tI|6=>exact tJ|7=>exact yI|8=>exact yJ|9=>exact yK|10=>exact qM|0|1|2|3|4=>exact cZ dk _ 0|_+11=>omega
lemma hM:aB false (ac 1215) 10 (cB 1215).toFinset:=gf (q:=191) (p:=ai bS) (ad bS cG) (by decide +kernel)
lemma xV:aR false (aN 6847) (ac 6847) 11:=
 aA (q:=1215) (rs:=[2,1,2,4,1,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) hM
  (aT (g:=dk) (i:=0) rfl rfl (ad bS cG) dV dc (by decide +kernel))
def lL:=ak bS 11 [(6847,[]),(1887,[133,117,101,33,48]),(14175,[131,67,99,116,50,33,16,80]),(8059,[128,64,116,81,96,49,32]),(17275,[130,114,98,81]),(17390,[66,114,132,49,32,81,96])]
lemma tj:aX false lL:=aC (m:=6847) cG xV (by decide +kernel)
lemma vJ:aR false (aN 18111) (ac 18111) 11:=
 aA (q:=1215) (rs:=[2,1,2,4,1,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) hM
  (aT (g:=dk) (i:=1) rfl rfl (ad bS cG) dV dc (by decide +kernel))
def j0:=ak lL 11 [(14143,[135,50,65])]
lemma qf:aX false j0:=aC (m:=18111) tj vJ (by decide +kernel)
lemma vH:aR false (aN 17087) (ac 17087) 11:=
 aA (q:=1215) (rs:=[2,1,2,4,1,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) hM
  (aT (g:=dk) (i:=2) rfl rfl (ad bS cG) dV dc (by decide +kernel))
def jY:=ak j0 11 [(17087,[]),(9535,[133,117,16,64,49,32]),(4959,[133,117,101,33,48]),(2415,[128,16,64,100,80,113,33,48])]
lemma qd:aX false jY:=aC (m:=17087) qf vH (by decide +kernel)
lemma xN:aR false (aN 2239) (ac 2239) 11:=
 aA (q:=1215) (rs:=[2,1,2,4,1,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) hM
  (aT (g:=dk) (i:=3) rfl rfl (ad bS cG) dV dc (by decide +kernel))
def lE:=ak jY 11 [(2239,[]),(4927,[131,65,50,114,81]),(6975,[133,117,16,64,49,32]),(2399,[133,117,101,33,48]),(9567,[131,67,99,116,50,33,16,80]),(4975,[128,16,64,100,80,113,33,48]),(7023,[130,33,113,98,66,16,80]),(2427,[130,114,98,81]),(9595,[128,64,116,81,96,49,32]),(9703,[67,132,99,82,16]),(12782,[66,114,132,49,32,81,96])]
lemma tc:aX false lE:=aC (m:=2239) qd xN (by decide +kernel)
lemma xR:aR false (aN 2751) (ac 2751) 11:=
 aA (q:=1215) (rs:=[2,1,2,4,8,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) hM
  (aT (g:=dk) (i:=4) rfl rfl (ad bS cG) dV dc (by decide +kernel))
def lI:=ak lE 11 [(2751,[]),(1343,[135,50,65]),(18751,[132,65,48,80,113,32]),(1375,[135,101,50,33,16,64]),(18783,[132,67,100,84,48,33,112]),(1391,[130,50,97,115,82,16,64]),(18799,[128,97,65,49,33,112]),(1403,[130,50,81,115,98,65]),(18811,[128,80,81,67,96,113,32]),(28135,[80,132,99,112,32,16]),(6638,[50,117,131,49,32,65,96]),(28142,[80,84,132,49,113,96])]
lemma tg:aX false lI:=aC (m:=2751) tc xR (by decide +kernel)
lemma xJ:aR false (aN 1727) (ac 1727) 11:=
 aA (q:=1215) (rs:=[2,1,2,4,1,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) hM
  (aT (g:=dk) (i:=5) rfl rfl (ad bS cG) dV dc (by decide +kernel))
def lA:=ak lI 11 [(1727,[]),(2367,[135,50,65]),(7007,[135,101,50,33,16,64]),(9583,[130,50,97,115,82,16,64]),(4987,[130,50,81,115,98,65]),(17341,[129,82,97,48]),(14318,[50,117,131,49,32,65,96])]
lemma s8:aX false lA:=aC (m:=1727) tg xJ (by decide +kernel)
lemma vO:aR false (aN 42687) (ac 42687) 11:=
 aA (q:=1215) (rs:=[2,1,2,4,1,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) hM
  (aT (g:=dk) (i:=6) rfl rfl (ad bS cG) dV dc (by decide +kernel))
def j2:=ak lA 11 [(42687,[]),(44351,[135,50,65]),(47967,[135,101,50,33,16,64]),(53087,[133,117,101,33,48]),(44923,[130,50,81,115,98,65]),(69499,[128,64,116,81,96,49,32]),(60349,[129,82,97,48]),(69565,[129,80,48,50,114,97,64]),(42983,[115,83,82,130,99,66,16]),(45031,[84,117,80,132,96,48,32,16]),(53230,[50,117,131,49,32,65,96]),(60398,[64,132,49,96])]
lemma qh:aX false j2:=aC (m:=42687) s8 vO (by decide +kernel)
lemma v8:aR false (aN 58559) (ac 58559) 11:=
 aA (q:=1215) (rs:=[2,1,2,36,1,9,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) hM
  (aT (g:=dk) (i:=7) rfl rfl (ad bS cG) dV dc (by decide +kernel))
def kj:=ak j2 11 [(58559,[]),(64191,[117,67,32]),(51007,[133,117,16,64,49,32]),(54079,[135,50,65]),(46431,[133,117,101,33,48]),(43887,[128,16,64,100,80,113,33,48]),(54127,[128,97,65,49,33,112]),(48507,[128,64,116,81,96,49,32]),(43951,[113,129,97,82,32,65,48]),(43453,[129,82,97,48]),(64445,[129,80,48,50,114,97,64]),(49646,[64,132,49,96])]
lemma qx:aX false kj:=aC (m:=58559) qh v8 (by decide +kernel)
lemma v6:aR false (aN 58047) (ac 58047) 11:=
 aA (q:=1215) (rs:=[2,1,2,16,8,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) hM
  (aT (g:=dk) (i:=8) rfl rfl (ad bS cG) dV dc (by decide +kernel))
def kh:=ak kj 11 [(58047,[]),(47935,[133,117,16,64,49,32]),(69439,[132,65,48,80,113,32]),(44383,[133,117,101,33,48]),(74079,[132,67,100,84,48,33,112]),(50043,[128,64,116,81,96,49,32]),(58235,[130,114,98,81]),(69102,[66,114,132,49,32,81,96])]
lemma qu:aX false kh:=aC (m:=58047) qx v6 (by decide +kernel)
lemma vX:aR false (aN 44223) (ac 44223) 11:=
 aA (q:=1215) (rs:=[16,1,2,4,1,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) hM
  (aT (g:=dk) (i:=9) rfl rfl (ad bS cG) dV dc (by decide +kernel))
def bl:=ak kh 11 [(44223,[]),(44735,[84,115]),(52927,[117,67,32]),(54975,[116,83,32]),(42815,[135,50,65]),(44863,[131,65,50,114,81]),(53055,[133,117,16,64,49,32]),(60223,[132,65,48,80,113,32]),(42847,[135,101,50,33,16,64]),(50015,[131,67,99,116,50,33,16,80]),(58207,[133,117,101,33,48]),(60255,[132,67,100,84,48,33,112]),(42863,[130,50,97,115,82,16,64]),(47983,[130,33,113,98,66,16,80]),(60271,[128,97,65,49,33,112]),(69487,[128,16,64,100,80,113,33,48]),(42875,[130,50,81,115,98,65]),(44411,[130,114,98,81]),(60283,[128,80,81,67,96,113,32]),(74107,[128,64,116,81,96,49,32]),(44989,[129,80,48,50,114,97,64]),(69095,[84,117,80,132,96,48,32,16]),(69607,[80,132,99,112,32,16]),(48110,[50,117,131,49,32,65,96]),(55278,[66,114,132,49,32,81,96]),(69614,[80,84,132,49,113,96])]
lemma cH:aX false bl:=aC (m:=44223) qu vX (by decide +kernel)
def yp (_:Nat):=0x4c88f1a284060808057fc10
def yu:aF:=(1,1,6,0,0,0,0,yp)
def yr (_:Nat):=0x83800e3000c4814a28004c8280a80000001288072170108490827828b80af
def yo (_:Nat):=0x45e30d8a0c818140206a241064060040e1d00022e2050212800011103640685c1c10c04820d80802c260c58342c08544800504d78c021e1c0400087480d0b4609048382010050c640685848241c10080283c30342c27180a0c10040161a18161413918d06080200bbeabda425b7f9a15910f2e85d003ff5cc10ffd30043ff55010ffd42042ff60810bfd83042ff61010afd86042fb60810bbd84042f760c10
def yt:aF:=(11,2,6,0,0,10,0,yo)
def yq (_:Nat):=0x202000000380606397c47943e48901800297152608243b403c8700800082947f118001c3285b90ec41920000002c8c93c003182c4b157140c72130003050003410000003d1e537c6746e01704d44505c06907602c00110950282796c162857834001c1c40e912986200108200000514a043340004082000000144000
def Ba (_:Nat):=0x5e531855aca28df80d3485b10aff144a303b08ac2279015e40503fc243f74904e6f88cfe84131fd4095e405a6492532492f60487f42099e4055ba01ef5025bee9209cfec0916e8073ee9209c7a808879e449669080ff091d4057d0116e807bd81208116988c51b8c1680a003e0241874390b410783414020482f090886c0001070642100bd2d8b0ab2a8e8a9f66f9864f8f625819f3761bf6b59860d6e54d414ad153dcdf324ab2487719c4f0f42b054002c92cc12c983ca94cb84cc11eb80cca3ca134aa60cad8a94ab9b89846b856a15aaa38cbc0cbc4a168b846cad4986aa134b9e6c95a9836b9d0c958b9c8a146a956aa58aa46985aca3ffdbff7def7ddfafeffcff618106101060c10608105cc10550104c010
def Bd:aF:=(36,3,6,524295,51,10,1055,Ba)
def Bb (_:Nat):=0x4200118060050390014553e041769a0
def A9 (_:Nat):=0x190040e18320081c3064010386000418002029b9673502d1e1900abf6897361810afb6a57360810ebe5c13061810efa5c13060810eee5c13061010cfb649825cc10aef68973610108f72a54260c10
def Bc:aF:=(8,4,6,0,0,8,0,A9)
def oe:Array (bt × bt) := #[(0xffffffffffffffffffffffffffffffa8c12191,0x7c002100),(0x100d1cae,0x38d1cac),(0xffffffffffffffffffffffffffffffc4146207,0xffffffffffffffffffffffffffffffec000203),(0x5308cf8,0x139088f0),(0xffffffffffffffffffffffffffffffa160574f,0xffffffffffffffffffffffffffffff806f560f),(0xa82987e,0x390807e),(0x1008e070,0x7c72e050),(0x4202ff80,0x106f7d80),(0x0,0x0)]
def od:List aZ:=[(2,64,189,0,8),(33,0,222,0,7),(1048,0,1255,0,8),(1184,0,1119,0,8),(17,0,238,0,7),(52800,0,52927,0,11),(54848,0,54975,0,11),(58432,0,58559,0,11),(64064,0,64191,0,11),(43010,64,43197,0,8),(11266,64,11453,0,8),(52738,64,52925,0,8),(57858,64,58045,0,8),(58370,64,58557,0,8),(145,32,78,0,4),(64002,64,64189,0,8),(73,16,166,0,4),(162,64,29,0,4),(41,16,198,0,4),(1096,0,1207,0,8),(148,8,99,0,4),(160,0,95,0,8),(12,0,243,0,7),(177,0,78,0,4),(54786,64,54973,0,8),(59393,0,59646,0,8),(52801,0,52926,0,7),(78,0,177,0,4),(193,32,30,0,4),(90,0,165,0,4),(84,8,163,0,4),(54849,0,54974,0,7),(0,128,91,36,7)]
def tC:List (List Nat):=i0
def qG:Nat->aF
 | 11=>yu
 | 10=>yt
 | 9=>Bd
 | 8=>Bc
 | _=>a0
def tD:Nat->Nat->Option (Nat × Nat)
 | 11=>aK 5 23 3 10 4 2 yr
 | 10=>aK 27 69 6 12 6 2 yq
 | 9=>aK 2 13 4 9 3 2 Bb
 | _=>fun _=>none
def k9:aM:=⟨1279,11,fun j=>oe[j]?.getD (0,0),od,tC,qG,tD⟩
set_option maxHeartbeats 0 in
lemma uq:aD k9 (ai bl)=true:=by simp only [aD,and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aH (d:=3) ?_⟩,aH (d:=0) ?_⟩<;>simp only [aW]<;>(try repeat' apply And.intro)<;>decide +kernel
def kX (_:Nat):=0x847465507548287565753010647580103578044026643171266431212664311026523060
def f5 (_:Nat):=0x760215268407140007602152684021500076021526800214000756214263002130007502157680021400075021526800214000724013674201273007012142630021400070121426300213000641207854107502106412078541065021064120785410640710641207854106402106412078501064021041620746810017200405707468100162002305817562075120023058175620651200230581756206417002305817562064120007214135200402100041202345103702100412023401073021
def oc:Nat:=0xa04210842110c0300c03
def n9:Nat:=0xd064a49147434114642a
lemma tN:ag k9 8 0 8:=ae oc n9 kX f5 0x304020102040392 rfl (by decide +kernel)
lemma tO:ag k9 9 0 32:=ae oc n9 kX f5 0x60002090900008096919089008e8f8c9300858b82898494888e8a810087838b rfl (by decide +kernel)
lemma qY:ag k9 9 32 4:=ae oc n9 kX f5 0x3050807 rfl (by decide +kernel)
lemma yL:ag k9 9 0 36:=(aw tO qY)
lemma qW:ag k9 10 0 11:=ae oc n9 kX f5 0x9586008d00000000000000 rfl (by decide +kernel)
lemma qX:ag k9 11 0 1:=ae oc n9 kX f5 0x0 rfl (by decide +kernel)
lemma qa:bT k9 11:=by intro k hk;match k with|8=>exact tN|9=>exact yL|10=>exact qW|11=>exact qX|0|1|2|3|4|5|6|7=>exact cZ k9 _ 0|_+12=>omega
lemma hO:aB false (ac 1279) 11 (cB 1279).toFinset:=gf (q:=255) (p:=ai bl) (ad bl cH) (by decide +kernel)
lemma xO:aR false (aN 2303) (ac 2303) 12:=
 aA (q:=1279) (rs:=[2,1,2,4,1,1,2,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) hO
  (bB (p:=ai bl) (ad bl cH) (2112,0,2239,0,11) (by decide +kernel) (by decide +kernel))
def lF:=ak bl 12 [(27127,[67,80,100,131,112,32,16])]
lemma td:aX false lF:=aC (m:=2303) cH xO (by decide +kernel)
lemma vI:aR false (aN 17151) (ac 17151) 12:=
 aA (q:=1279) (rs:=[2,1,2,4,1,1,2,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) hO
  (bB (p:=ai bl) (ad bl cH) (16960,0,17087,0,11) (by decide +kernel) (by decide +kernel))
def jZ:=ak lF 12 [(17151,[])]
lemma qe:aX false jZ:=aC (m:=17151) td vI (by decide +kernel)
lemma xS:aR false (aN 2815) (ac 2815) 12:=
 aA (q:=1279) (rs:=[2,1,2,4,8,1,2,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) hO
  (bB (p:=ai bl) (ad bl cH) (2624,0,2751,0,11) (by decide +kernel) (by decide +kernel))
def lJ:=ak jZ 12 [(18911,[99,132,84,48,33,112]),(28151,[67,80,100,131,112,32,16])]
lemma th:aX false lJ:=aC (m:=2815) qe xS (by decide +kernel)
lemma xW:aR false (aN 6911) (ac 6911) 12:=
 aA (q:=1279) (rs:=[2,1,2,4,1,1,2,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) hO
  (bB (p:=ai bl) (ad bl cH) (6720,0,6847,0,11) (by decide +kernel) (by decide +kernel))
def lM:=ak lJ 12 [(17403,[118,130,81])]
lemma tk:aX false lM:=aC (m:=6911) th xW (by decide +kernel)
lemma xK:aR false (aN 1791) (ac 1791) 12:=
 aA (q:=1279) (rs:=[2,1,2,4,1,1,2,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) hO
  (bB (p:=ai bl) (ad bl cH) (1600,0,1727,0,11) (by decide +kernel) (by decide +kernel))
def lB:=ak lM 12 [(17405,[82,129,48])]
lemma s9:aX false lB:=aC (m:=1791) tk xK (by decide +kernel)
lemma xE:aR false (aN 1279) (ac 1279) 12:=
 aA (q:=1279) (rs:=[16,4,2,4,1,1,2,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) hO
  (aT (g:=k9) (i:=0) rfl rfl (ad bl cH) uq qa (by decide +kernel))
def lr:=ak lB 12 [(3579,[99,81,115,130,65]),(18941,[82,129,48]),(11774,[117,99,49,32,65,128]),(18942,[100,49,128])]
lemma s3:aX false lr:=aC (m:=1279) s9 xE (by decide +kernel)
lemma v9:aR false (aN 58623) (ac 58623) 12:=
 aA (q:=1279) (rs:=[2,1,2,36,1,9,2,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) hO
  (bB (p:=ai bl) (ad bl cH) (58432,0,58559,0,11) (by decide +kernel) (by decide +kernel))
def kk:=ak lr 12 [(58623,[]),(46559,[118,133,33,48]),(43517,[82,129,48])]
lemma qy:aX false kk:=aC (m:=58623) s3 v9 (by decide +kernel)
lemma v7:aR false (aN 58111) (ac 58111) 12:=
 aA (q:=1279) (rs:=[2,1,2,16,8,1,2,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) hO
  (bB (p:=ai bl) (ad bl cH) (57920,0,58047,0,11) (by decide +kernel) (by decide +kernel))
def ki:=ak kk 12 [(68863,[116,83,32])]
lemma qw:aX false ki:=aC (m:=58111) qy v7 (by decide +kernel)
lemma vY:aR false (aN 44287) (ac 44287) 12:=
 aA (q:=1279) (rs:=[16,1,2,4,1,1,2,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) hO
  (bB (p:=ai bl) (ad bl cH) (44096,0,44223,0,11) (by decide +kernel) (by decide +kernel))
def j8:=ak ki 12 [(44799,[84,115]),(42975,[118,101,133,50,33,16,64]),(58335,[118,133,33,48]),(60383,[99,132,84,48,33,112]),(48119,[115,82,98,131,66,16]),(69623,[67,80,100,131,112,32,16]),(45053,[80,48,50,114,129,64]),(58365,[82,129,48])]
lemma qn:aX false j8:=aC (m:=44287) qw vY (by decide +kernel)
lemma vP:aR false (aN 42751) (ac 42751) 12:=
 aA (q:=1279) (rs:=[2,1,2,4,1,1,2,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) hO
  (bB (p:=ai bl) (ad bl cH) (42560,0,42687,0,11) (by decide +kernel) (by decide +kernel))
def cQ:=ak j8 12 [(42751,[]),(47871,[117,67,32]),(42999,[115,82,98,131,66,16]),(60413,[82,129,48]),(69629,[80,48,50,114,129,64])]
lemma dK:aX false cQ:=aC (m:=42751) qn vP (by decide +kernel)
def yy (_:Nat):=0x5a2c1286c92b8843c484150a450271300c12251208c44210334401f0f074381b0d06430170b05402080a04c24110803c1c0d065c160a048200e063014080301004006f6f1294761d803fe887fd30ffa81ff54bfe087fc30
def yE:aF:=(6,1,8,0,0,9,0,yy)
def yB (_:Nat):=0x146100000004baed31538440c1ffdeb0f6183e06000a8c0b07e49b14e320002839810909504c00050a76d4868c1000068bfa4c000000000083709a00000028a800190dc14911063a64efd100000000007aed45560ed2b90b0000000c289281131c40021b72000000000000020b2031241808c49c032807502389b83e000b92e08c0009128422147ccdc24b299c6cd4889ec33b15a259e00915b38a81356660ac43d82820ca83712145fe1b30b939f002000f12fa0743b0039c1d0b445d640f035b1000194c0000001045e02d07502ddb960a713a47c0008c3e89f81470c20450413471001400820430050b11c35410032cc082000283
def yx (_:Nat):=0x6ffff64904012a7fcc020224b7f64e130f024d2bfafe40a032481e0294604de32d22ffc68564541281bff0144081a63d8b819409fff785350254fffe02f017139c88000001547ebf703c5804a327e1f3e4c0082f1cf1be89c1b0004ec7062909778125ffe0ca5ec0085e09fb70ef058a20000dc5fff81aae0670005ffd7000400fcfea2002aaffec8001025157aa85702d1ae1e9c8400000003ff3fc7f8990414d7fe7f00184005c15620000af597d0ca8a688f6fe300022685f554114bff14d63033dff85f00ccb9c800caef024afe865044340378275f91338fb400f3f404a0073c6fbb0870004c004ff0178007139c9224a93c6a8dbca09400dffea8819f3f0e0085a338ff5f0360058d98227afe40ec8c00004fe7ff61784cbbc09000001f000000138ffe14e3f504e40cc185538033003cfc0464a86819c66172268a04d84e148820c8404551112469184211b10d424450f4fc3981c641855454d52428511404f1394b0a82900c2809c090941f0c00486a170520e0086017c5e16e06490464743a41c6518c6289d565552c42c2487612872188442d0320f8340b1303c1762a1695855d3d4084844d304b51c082018260882e2d96540436024cd324c51488e038120a0bd2b11e2c86d204404a88a210da2550438caf100d43b0f8371270f0b8348900001c0697a94f9158e38c58a386e83a81a7e378274c7106d06b169b6616155e45835535255044aa44941c3e83ca39b3563403132e32b02a526c2151e51b618713f11d0dc0c607204902300090414ae2e57352b8391cd48e6253032c3c90c14ae12560729829619cae3248352c189609ca632570329859605cae2647132a8b9589cb06a48172c0994c04a40d98306c1a32059b060c8126c3c36199b0251862641a8481c2e0d5418ec107482830c498202c18ffffefeff7fbfbfbfefbbdebf549404c1100c010
def yD:aF:=(48,2,8,655366,67,12,1166,yx)
def yA (i:Nat):Nat:=(if i<1 then 0x46d2ef6d0e6207b000048f90000000054c6c4bb48ca6097d01f000000000000000000000000000000000c5ec8a4109c785902e500e5a00a0101c8f8501720d3781340b4e400a0ec00008421a0f450b500000000000000fe0000e073000050bcc298100850520000700e000020f098d1782814190000208e000062400000d60b0000b0321898c03bd8fe000072fc2033a028302eb0e1687968e540e720fca88a06d5d26d8087ea25b007a092e05b2009000000d5000008cb789a508ad0a1146feefc007882b700cd901988f070b8b0b9e0e320cb00d9e02a02cd80f500009039d00b0000000000003018c0eac65e48cd88655081d242041520ed982788a5fc223a4bc702a3026cd5d06d3084b0a4205624eb3ec6220b200110e47053b0d4d0ef8e90501120aec0756088e429327e20294067fa66306cc042f0f26098e03754c58ced6068122500437409000090bed0c8609500a9701428e870bf207fa08b00007072c0c790c3606a22c5a2e2d825a090d0e8da83f0699884f07a0000a0890000e047000000000000904d000000000000f071e05700000000361a000048375015302d30201025d010f410b8d8006240fab0ac0000000031020000b03e000014ca280300008079a8bec065d016e013104a000084180000dec50000385a000020abc8c6705050e0d87c282e5658a038d0a030dbe866b816ec277c0eb026303500e92005bed2d02356216076e0042d00b08f92226427686228b3e03a70307609e226a02f80d040aaca6c00baeac5064d065c528fe25c205de0b00000e0120849a027e09a204ba836c0589830486896dbb0550000000068a30000001d0000602c00000000000000000000f0bd9618b04e5021b083208d10700000f6960000000060cf0000206e000000000000f0c4589e9692e0b6f05aa0c0c8b1c886d2d792212a9b0415c004021000008902a0400000000c20c000a01b00000c0130001800000c40000c33002800420000000001c014000500000000004000008000000b00130e1800000060060820015021c00802000002810040000000004000120000000c10000000000000c03070000010000002400000002800800c70006810000440520401810000000020001c00030000800020c00010830040420001800002040c10010800800440000802800000c10010490c900000004000004000100000000000000b00000000d00000700108410000000d1400000010020000050400c00030000c00800000000030800c000a0800000000000800000010000cd00000000000100000c0020000080800030400000000000010000000800000040020071000010020000000031400000840000000000000000000060000002000800000000000000010802000000000000400020000000001c00000000030410000010000c0000000000 else 0xc2d40000e85f900d000010d80000a0d684eec100e44c70cef0de20021022603fd43900000000809908f2000000000000000000003811109f82992cda18eb909bb49b00a764c760c6304f0000c29400000000d47a00008875220e5622802ba8a0ec6c489f80bb08350000f0a5a60fc01a40df507d26e70a21b0c9e03d820c882df0f800000000000000000000e09e2091c2acc060c6f87031929ca074f422e0630cd022391e9be01ef05ffe6fe490bc9280820a90e890040b84d760d7e041f8f3383da210100fe252de2c9049a8316096d0fb70f644fc28531502da98a6da24e7f8b4a0f3540190cc407e5048b05e50d2429090347405206f000000000000000080fd0000804c229b70cabeeb80c5dcf8c05c40dc1287b84b2860626600001894a897407c9c2168da2000000010240000e0f1e8faa0f9d0ff0059fae56054b09314e2c0a3f0e24afc08f12b00e0ddb0c140a64061e09d0000600c886fd08508d65094d8c1e0ebd82140f7f682e06b1040682ca869c0af64205876442c203c60662086b08038290000d0b2cc83701b808c30ad00a2841e0000783300000000204420b1c077f8d500000000000000007e21dacd0000e8f49006b8920000b858000000000000000080ee401c203600000000a8f70000e885e046285120c280b3b045205120da8064000000000000760e70d15848000020b7f0a810031)
def yw (j:Nat):Nat:=(if j<1 then 0x53d58f2b3c28eb83a90e78393ce293768dc436c0d91359cd2233fccd432b8c9b31e8c563090c122ff0be22e5cb622d3cb392c18ada2a50a812994a3427f09d626f4992261496024dc8fa233c89b218c82b20607d21e947751d3c7121bb86c21a9467a198461f17d85bc162455014a050a13844ce128c480117842b0fd83d40e4037d0d102f70b4c29309a022507f01d106b417a053c118039c0da031c0b40284066016404600cc020003400095304255c6295717a5661894973e525d195317a5661095313e55c9595714e564629597725641695724a561d695654e55c4f94875a52618959072564df95718254c5595987e554d394918a55c5c95935255cd195515a55c9495315e565d4959872560569531825589795985a5641f95716a5662295656a55c0e9487565641894874652610949772558d394937da61d9688739a5cd169970da26102d9034b6622716559f4c5d698305a4c602d983645897698724b65d12d974a45c0f69516e45c012d9179a6055698744b261691604cb64cb68970cb641c91874e154d568972634c21716356164d490985da24e0688746364e17d9775a661669814da261f2d977235c9391206da649b699181a65d169811a154da91935da609490815da5c112d976a4605791725cb65cc7d7174b659391706da6608912060b655291315e45c1a698750b2614689744b65ce68816da65c969875a45c132d926da21d985313db5c5e689862324992d9649a605a7d4179a615369534a465d32d9169a61da698159a262269916da481b688169a6622689871a6155699381a4c112d987244857697180b646068874a154d3698121a604769706e421d3698569a24602d9189f64dd69816da21da8d718646593698704b644f69826e35c962d916cb64927d4181a6095698559a245b69874e35c9a90814e365e191514da66182d9131a61c769985245953716555a61c391814c465d11198004261035870c4660421932d765c21098604660d259784465c519954a04c571197384660f3d861cf604a81534c464d23d8618464e015963196053618120f644a59900d665c3119548a640d89724ca640051877595c1b5d8205625c3259235760805d820c42614119039764c23d8621d54611d9411e4c5d49850c465d2893085461017553844649b119820f244a59700d26141119180466223d86049648b019715061434d8408c61c305954816545458508264d2398609560830d9217ffffeff7febfbff6fdffb7edfbfeffbff7f6fddf7bdf79eefdd7b7f6ded7d7faef3fe77bff7fafddf7bdf77edfcff9f73de6fc7f4c1524815261d405c5405c140505404c5406193060930605305c5305c130589305813054530481302053060d105cd104c11020d101cd100c1100411061830604305c4305c0304c030204301c43060c10608104c0101cc10 else (if j<2 then 0x294b87d9e18125a4c0d94ff1102129ffd080042d275fc88cc7d08e32d5a4ca1d3e240ca037fc0042243d78c55d1318fe00895fff0e105d3009081b01d1fd4e20010e7b410dc82500e01ff0000d08c5060b310c019f4978ffef011359ed040b978a3df8cc2818025730485f341944407c3d214551e90632fde35400ce503bbfd64a14479ebd08198bf837d44a8044d40dfc218819dbe3fb489689a11fd4cfa8410a203b8c33a15081a8f482827f7a6d123c1044da94fef4220672ff8fda88267aebe1881981af92c46490191206189cd483f27d448490174c4a3c749363910d1e90630ef8780361ff911abdb383b610b5f13eba1b0203547ec9e824206907fb855000c14449c5d78852e1c8ad47cc58b8f0853da088ff1343221a0f764452011fdd10858604791431a4bbe9cd63940d22e1078c2057cbebd8aa49a3359ed0427c0af2080034400017c0bbe142f9501b60af51a91d3e015c308f48d5aaf7fb0e401527fcb0c8f4880466b0029f743c2871a470e26782bd46a479fea3fe0240932f282e30219bffe705d071346fc66140c0128a067b410f6821ed040efce05fa1e10d25033da087b410f6821ed04281c0e41a23c2e3080f21c82d0944b4cc4ab92ce2024c969130ec472814036174444546487c211c18800fa1ed3c6140189d9240742621c03786b6b0562abd2aa65822014464402444813026719d05a6686b1984442810b1861861dc22c9108c4700420840a0a125175b8d0fa8491844c10c39881a022281e0f2a006d41e96524896817824458500ca4084731d22819a8e88710c116154208188740800f0dc18d0622c43623134400c041dc3ab410e64af12e2d12b4c795a0211a4c89017184ac703384681383b00e220c8188a0d08a490d1a151cc378b28a70f0bc1ea0a42d09180e0385108e88686e0fc0813f0686165689024b11a661a3108784014819060ac461ff0584347c17695a070700e43604a0d216e0307c8499649f2066215043f30f06e0d2881070d40f81d83606a0bc2683ac4801c0004c00c0ba6cd9a72682994e633984a5e997565c39642569950a523942e4f4936a4c0925246e917643e908e4048f223ad8e4e3788d5a32f8c462db8aca27f895e23f88aa204874a1ba866e175854e13484520f9833a0b682ba09281f205780ae00f7fc9fd57ecdf9e7e21f357c11ef47b11ea87959e2c7871dfa7741da57601d607501d0e73d1ccf728dc83718dc4870b9c0b6f8db9f6dfdb596ccdb046b9dac76aa1a8a69c1a3267699c26695979652991363e18c86259878611981b5fd17d85eb57775d2d7275c216be5a8567e598962858455e256a558f559d51e53ad4d2529d49851f1456510541650013d74ead37c4d3d3384c4d2ee4b052a149c5249489120c47b91ce46bd18e455112744210ea430108b413901e402cfe43efcf8 else 0x2f02307bc14abdfc307b7cc69f38145081a23fe881901ef881084fe013a08547682bc08c9d1ec34420438ffa252847172f00810a97f7d114b9618fbd23190f884c4f4813469ff92003369f84009499a625fde088bd9571903cb803233ffc88b000204443891835f70913be00324f1dc2c8dded86c01980f500a327ffc4d185021e1eaea8810aefea20a20021c3a7c2c0199718110f88498f25040429bfca5410010e5d2cc70e2c3a137e3d9104747e100211bfe003255f98051aff1044a87d89218cffb7184019ca08c87321269f5983a927e8501b41251f09a0f6b1888a174c4a3578cfd210bcc0c3ed2197fffc5a3080e0854206d53f4482041535911d8fe7e60441647c503243e1da8c958204200811a1fe7da913334029feb118511ff95848330f73e7400488bfa10023cf83f022cfaa80230379971f140d0bd62a22ffcc0411b7fe140a09234f15091b7a4be1159fe903cc780896fed48a13dfa9b0021400d7b0dd44fa02228de1002133aacb806633f2003a90193ffd31033c7db499213760a107c56322af8e408a3437a247fe881e00c000d411ff87d00ad07f708804df7f90499f420643be040300a502e0cffc28cfdb7f8547a889a4efe012ede01555805373f061200010e3fa8822a3a7aa090010e1ff850001986fd2c68238d7c222ebfff2a428517fc9ba8410a1f71f44c041257e97c411b32a943297ffffd6190000804d75e700646fe1268cb5ff104ccfcff9208000445cd025064fff4c40ce5fc1be9a60a06959f41125d9df21a1483f1fded08000440da5ff84202501a17fb00de7c02061295c0253e904197a409b4cc798240ffe02840cc6e4128bfc82002175fe9da0021adfcfcc2a1437bfa24010219fec02de721f20a0b1e1050cc027924e7086cfd42065dbea0a2100a657b3a1c08577de82042d61ab1a8fe008b97fa808bb9e8091a5dd54108077c7d86cc024403fc56420a194fc88518f58c28b9e184a8033f3ff4214410a1e9ff6e9016358512bd7c54440093b110c3e3680033698595029012ff94541840888b876c06054c5fe564c819b9f40090801ff67a58611f58220371f4120e0af50952483fd0610217de28040850fffc0150dba624048da7c412d9a924df302a3bbec500))
def yC:aF:=(259,3,8,2490403,102,14,1251,yw)
def yz (i:Nat):Nat:=(if i<1 then 0xa087405c06c402f82ba83696c9af3800020581025c55122e2801908bb4a8000000010279141156dc2ea0bbe97b882043dd877c927e075027bc12c0b20000c016c9d214d30d80000000707200000000814000000000000000d18472f34d40000000141af8c80100a06ee07884c906413302cbad3f3a040001ae40000402d0000804382d35bc90b84270000000000000000000681fc17870980000000bb43422000000000000a2dfe230820e832a09a03edc80b169224400040122194e0c0000287fd0fc00000000000c2fc0066246c696615920d2807000080e051ead5198540000e26380880000000413941e80006b680002444e038214461a9a16103679540003456d853a85c0003c8b402b30923252c21f87c50cc00030140000615e41db244ea872034000083a461b0000000361c800000017177c2d8000713ba28f13bb09e00016c989b88095c8fb40600003132000000000004c17112c62370304c35b963604cc50a20cf77192b6d10e82a50f0631740ab2950001006d63651b4110921c40000000f2980000000000010742430000604d10a3d0b69457501415540fb0317108901300f1ca26ba6b88be0286581671518f8301a3a00000000f1eec2f0000804902c4e42645e5148000044038c3e0620eec85cb8165902a0d5e1c12bbd05e0184c438cb87943ad3ec2048a828787ab3655c4281941faef8ada8b374840002503606e46fd880104d7081c13778dcc2648bd60afae8f62d08a90000850800014517189001e8024846210400000007c65112471b40000000000000000347bc2107f6240000782c299202d9807d850c16ac016aa2590a10aa000000000000000000000000000000a08c449853210ebbae1437c85278ed02f9847369f1019400433e11227d0d60a563100bab4d2307d4428041e866819fd861848f089b0acc252897c044e037053e073a08b90a64000079818df30e02fa09fe0b0531d0591863ad48015abd1424360e4221b80e38a5b0ca72a4841bc7520f4801bc1df04718c7412d064b8c8000142fc44550ab00000003518383346af14c70608008d96be4c4639a02e0003040800000001001810020000001450c61532010002800261020800c000824d0002030000000c00430c020200600000000000108500038300004000100000000000810000000e04004100010d0801800c20000400400000041430010000001400000000010090000020000000010400020c000000000000000b0040020000010000000000000400000001030400010000000000430000000410060001000030870000000000800000000000400c6080080000040002040005082000080001000200000000042040040005080080080001000000040000000041000000040000001080006000001000001000000000000000000001000000000000000 else 0x2d08034fba781186efec4a1842490a80c8847a92012c1)
def Bj (j:Nat):Nat:=(if j<1 then 0x5a2c6b4e344b82353242352c282e4709b5145eb04a292e47c9b4afc2152e1f2e2a66aa76942a4e8cb494622e2e0cb491c9950529240a0c34b454330e5eae4cc9b511e6aa4717ae4989b4ed1a346149b4f20f341467a633e32a2c54130ed41512c234ebe2ae0e9632a5c9b4748215244f344d8f34cd8f152ddeae490e342ca7a831e12e485eae50cab46ad634460f34e654130a02352b89b517142604941317e12e300e344409b4375432ea54b2e5cf150dd62ca9cf34a69a302c4f34c68234c9dc30f354130d669536692e474f34268e344a89b4751b2a2d1c30f30234e9d41517d41312c9b42fdeb4e0e5aa7709b4af57b245cf150e423525e3ac079eae48dda635692e48272a27c13524c13449c1344e811503c135255ba63384b4d544b4e341353110b4662626160e942981352d013475d394318894318d34665332e1c19526c134380db44686349516a832933440863483049522d594060bb4a644b4e390b2b112350290b2a588344547b470972616d0aa69c8344f4834021ca630982e01a1ae2e0834424bb4ad90aa38252a271e241764aa47013509891511552a69c5b4b04b34761ba8320134c9d534661d263145b4a259ae01592e238db4464a34ed81352cc135314134e9cd342705b4af90aca9daae0105b4b0a0ae289e2a48de2e48c934154115359032a0202e2e001522c0b4408fb0c292b040642a470734024334a346b44243b4834534a244344342b4e351328011b0807ff3febfdbfcffb7f7bf6ff6bf5ff5bf4ff4befbe7fdfbdf7df3defdebdd3bfbbf7befbebbdfbdbbd7bbfbb7b7fb7baffafbaf79ff9fb7ef7eb7b777f77b75f5ff3ff3f73ef3eb3bf3bb3af37f36f2beffaff2feefeafdafbef7ef7af6eefedfabfebfabf6beebdebdabcebbeb7eb5eafeaeeabea7e8fe7fe7fa3fe3ee2fd984c15264530549714c15226130548914c15265d20549714815254d205495148152645875013161d4024d875009161d4064d71500985c54024d71501715c1405057050187505405c541501315054065d31501904c5405c531500984c54025d3150192619305c1864c15161930481864c09161930205864c1726093021d824c0816093021d814c1985c530641714c0985c530589704c1315c130485704c0815c13061d624c18558930605624c17258930595624c15158930261624c08758930615604c18258130595604c08758130609514c17254530261514c1964813061d204c18548130605204c172481305c5204c17048130595204c16348130581204c15348130545204c08748130205204c195205305c8814c1532053021c814c17360d105c183440985cd105c530440974c11065c834419161830245860c09760430619710c1941c43025d83041976081064d82041874c01061930041854c01060930041981cc1064073041821cc10 else 0x36285bf610c3eb16a0f78313259a16018b360a9f1020ef08ac84e1493586087710ef811806dc08f490f0c6a2601ae5091c1046648f7d2431b843c342afe64645d2134087bd144b9847522ee8c4dc189c047018f390d40b2e8594b1081edd0b3e0241dec472b4246af906806788830d068cb760514584df0120f2e850c1058f0f0212ae845fa09e01cca15e22d910c023488b22f7a20b6b88720e689161514304a0dbca8c60e8e20d8076910fd81107a90d80738421704153cc4838e04c75c018cfa233c22ea4d147229c443187434d85e01bbdd050c0a029f98a7213bd9053f810ce11201bc030704135d0af090ef113809617a19e1120378896350dbae58d7e021a7f93416538447e035025020fac5622cfe9244cb3f121cd550c7b8864c89013b01d795318f350dd01ba037a03b66826fc0477920b7f311117f8218f421cb2d5070ea9419d9157940032cf021d52c5bc14368113221798506e80d0127f446265d68920dec0680a3e0631c422051e818c991172c18eb8031da118bc40835e821bf00c4f086ce0733429aa12fec110fc119028f818f734260200e30411f80c9b234047fc04859147c0c63a843c721a0e384719239fc10ce05bef922003ffe3641203e90c6650ff58992bf5c4c93f1c110003813ff024e7f081932f1432f4d18f39aa643fe2240373ed140dcfb45df7c91013c18dcad880270dc441c26b480c20266c458909250d2e0e8874ac26092b88420217891a0d54742281b6482c81d0747281a198119450c3dc381a4a5e26c27825823e0d20001d02301746741d4c4443144021780780c17119a25e1755c6c3c25749010c0d501824c2079640e40f813e19f0901b344081825016c0035060181340e81fc01801f8901f81f01a81300bc0bbe2fdd3d87d57ce7cabc77c23bb3b73b43af3aa3a53a079e39a79538fb8c788382f7e378b73b6fb68b6476135ab55f52b4df49345f4273d33a335f3172e72a72371ef1ab13f10f0d304eff6fc2f52f0eebee42e02db2d76d36cfacb2c8ac52c1abc2b6eb0eab6a529ee98294e9168b286282e7ea79672a6ce67262a5ea59655a50a4ba4824463ee3b638e3423062ae2522161e61aa1561160c2086051ff5fb5f8df51f01ea1e45db9d7dd39d09cd9c8dc59bcdb75b21acda91a65a259c59719358f98b98698197c17516f56a563d5d55955154c547d4293f53b934d3112e52591f11ad1811290e90bd061024fc0f64f24eb8e64e20dccd8cd48d04ca0c54c28bd0b88b58b34ae4aa0a58a2c9cc99493c8e888083c7f87a076c7046505c85504dc4703b43402e82802181b81400c80600002353797ae57d433049fb027d634c6141314d634e609b4cf68ae2729ae26deae4b142e3814130f1eae4d18ae0ea2263428952709b4efa924178c34b714152d49b4cfdeae4949b4355b14ad)
def Bs:aF:=(203,4,8,5505121,119,12,1118,Bj)
def Bn (_:Nat):=0x23520a6010e441400000002b21a46000182e001301e1c617a1e0013ac000000208000000001c3062c000c03a1862803620c233810023c068ec35400191ca2600020efa5404820000a12000000224001208c05149e1
def Bi (_:Nat):=0x178405e10350405c07c1001805c203f01a84000004004c083a83e24100bc3d2400300b8604c035080fc02f1013005c200233ae2400300b8804d00300bc7d2402600b87e2401708002f0170a33be2400300b88006017080981adaa4a4a73952358c21e86607809e3745a561967521434f905364ad238891a83104800bcdb6c54aa6902a5fd24c0a954d2054bfa4a9a40b92a2985779b72819520530cebaa6d3930a8a61e795c971609514c2bbc5caa2b2a40986bb5a7504984c540cfe152b8aa290261f78545715c9204c2f6cdb152a9a40987dd1315c0985c530afd172902e4a8a61ad754da12613054bfa4982a6b8a40a96adda64c49361d40fec2e2982a2902a58eb691a2660730431b6cab4443902985739b42819520530aeb172a8aa690261ed254d202613054a3bc5cb4a40ae098636da5689981cc108f736854aa29026155e6dca0654814c2bb4d9140ca902986f49526855348130
def Br:aF:=(28,5,8,0,0,10,0,Bi)
def Bm (_:Nat):=0x2022120a00481835bb4200000707b100030
def Bh (_:Nat):=0x390805c1eb5c2b99303f5054d515c57248130e5e1722a571545204c3792549b62a553481309739c42e551595204c35d254cb9481725453083b8c86d0a9545204c31c654db42a55148130
def Bq:aF:=(7,6,8,0,0,6,0,Bh)
def Bl (_:Nat):=0x78001b2d178400008
def Bg (_:Nat):=0x3507340795054d722a571545204c22671b0e2172a8aca902614748da54cb94817254530
def Bp:aF:=(3,7,8,0,0,5,0,Bg)
def Bk (_:Nat):=0x1e0
def Bf (_:Nat):=0xd41d1505c4da54cb94817254530
def Bo:aF:=(1,8,8,0,0,0,0,Bf)
def oh:Array (bt × bt) := #[(0x840a108bec0006,0xd3584ac0e0a004),(0xffffffffffffffffffffffff24640550c50029,0xffffffffffffffffffffffff2c85b1021f1821),(0xffffffffffffffffffffffff61200154008957,0x503a0ef580c546),(0x4301e824009e18,0x874541086a3a18),(0xffffffffffffffffffffffff000b70212005e1,0xffffffffffffffffffffffff28a2b4371545e1),(0xffffffffffffffffffffffff8880028a0a427f,0xffffffffffffffffffffffff04a7252e0a5a3b),(0x105404001123be,0xd362442c60629e),(0x0,0x0),(0x1a908a001273c0,0x28189ad1958540)]
def og:List aZ:=[(28,0,355,0,7),(2080,0,2399,0,11),(2112,0,2367,0,11),(2064,0,2415,0,11),(2052,0,2427,0,11),(1,0,382,0,9),(49,0,334,0,7),(70,0,313,0,7),(1056,0,1375,0,11),(1040,0,1391,0,11),(1088,0,1343,0,11),(1028,0,1403,0,11),(36,0,347,0,8),(53824,0,54079,0,11),(53776,0,54127,0,11),(32,0,351,0,11),(4,0,379,0,11),(47648,0,47967,0,11),(52768,0,53087,0,11),(44548,0,44923,0,11),(69124,0,69499,0,11),(1568,0,1887,0,11),(4640,0,4959,0,11),(6688,0,7007,0,11),(9248,0,9567,0,11),(13856,0,14175,0,11),(18464,0,18783,0,11),(42528,0,42847,0,11),(46112,0,46431,0,11),(59936,0,60255,0,11),(7684,0,8059,0,11),(16900,0,17275,0,11),(48132,0,48507,0,11),(44096,0,44351,0,11),(44036,0,44411,0,11),(44064,0,44383,0,11),(43536,0,43887,0,11),(42512,0,42863,0,11),(4624,0,4975,0,11),(6672,0,7023,0,11),(9232,0,9583,0,11),(18448,0,18799,0,11),(59920,0,60271,0,11),(64,0,319,0,11),(42560,0,42815,0,11),(42500,0,42875,0,11),(50,1,332,0,4),(13,16,354,0,4),(4612,0,4987,0,11),(49668,0,50043,0,11),(59908,0,60283,0,11),(73732,0,74107,0,11),(43522,0,43901,0,9),(18433,0,18814,0,9),(59905,0,60286,0,9),(50689,0,51070,0,9),(9217,0,9598,0,9),(57,0,326,0,4),(69,2,312,0,4),(42524,0,42851,0,7),(42752,0,42623,0,9),(52800,0,53055,0,11),(352,0,31,0,7),(13888,0,14143,0,11),(47680,0,47935,0,11),(50752,0,51007,0,11),(49696,0,50015,0,11),(34,0,349,0,7),(73760,0,74079,0,11),(9244,0,9571,0,7),(2400,0,2079,0,7),(2050,0,2429,0,9),(50696,0,51063,0,9),(43776,0,43647,0,9),(46088,0,46455,0,9),(9220,0,9595,0,11),(276,8,99,0,4),(104,256,23,0,4),(6657,0,7038,0,9),(72,0,311,0,7),(49665,0,50046,0,9),(73729,0,74110,0,9),(4672,0,4927,0,11),(6720,0,6975,0,11),(9280,0,9535,0,11),(18496,0,18751,0,11),(44608,0,44863,0,11),(59968,0,60223,0,11),(69184,0,69439,0,11),(16,0,367,0,11),(44288,0,44159,0,9),(83,0,300,0,4),(65,0,318,0,7),(1036,0,1395,0,8),(18449,0,18798,0,8),(59921,0,60270,0,8),(9233,0,9582,0,8),(6705,0,6990,0,7),(46082,0,46461,0,9),(59906,0,60285,0,9),(69122,0,69501,0,9),(48129,0,48510,0,9),(1312,0,1119,0,8),(18498,0,18749,0,8),(42848,0,42527,0,7),(321,32,30,0,4),(74,4,305,0,4),(59909,0,60282,0,7),(262,64,57,0,4),(18,0,365,0,7),(44572,0,44899,0,7),(52801,0,53054,0,7),(44098,0,44349,0,8),(18436,0,18811,0,11),(71,0,312,0,4),(43600,0,43823,0,8),(53,0,330,0,4),(272,0,111,0,7),(44384,0,44063,0,7),(305,0,78,0,4),(44102,0,44345,0,7),(51,0,332,0,4),(52785,0,53070,0,7),(5,0,378,0,7),(273,32,78,0,4),(2114,0,2365,0,8),(290,64,29,0,4),(26,4,353,0,4),(80,0,303,0,8),(2118,0,2361,0,7),(8225,0,8542,0,8),(47632,0,47983,0,11),(47872,0,47743,0,9),(41,16,326,0,4),(18438,0,18809,0,8),(59910,0,60281,0,8),(4620,0,4979,0,8),(11297,0,11614,0,8),(4636,0,4963,0,7),(280,0,103,0,5),(260,0,123,0,7),(59953,0,60238,0,7),(59974,0,60217,0,7),(324,0,59,0,5),(49692,0,50019,0,7),(49697,0,50014,0,8),(44546,0,44925,0,9),(40,0,343,0,7),(102,0,281,0,4),(300,0,83,0,4),(344,0,39,0,4),(1344,0,1087,0,8),(78,0,305,0,4),(354,0,29,0,4),(92,0,291,0,4),(18465,0,18782,0,8),(284,0,99,0,4),(3138,0,3389,0,8),(326,0,57,0,4)]
def tF:List (List Nat):=ll
def qJ:Nat->aF
 | 12=>yE
 | 11=>yD
 | 10=>yC
 | 9=>Bs
 | 8=>Br
 | 7=>Bq
 | 6=>Bp
 | 5=>Bo
 | _=>a0
def tG:Nat->Nat->Option (Nat × Nat)
 | 12=>aK 35 135 6 13 6 3 yB
 | 11=>aK 470 589 6 16 9 3 yA
 | 10=>aK 338 423 6 15 8 3 yz
 | 9=>aK 9 55 5 12 5 3 Bn
 | 8=>aK 3 13 3 10 3 3 Bm
 | 7=>aK 4 7 1 9 2 3 Bl
 | 6=>aK 1 3 1 8 1 3 Bk
 | _=>fun _=>none
def dM:aM:=⟨1407,12,fun j=>oh[j]?.getD (0,0),og,tF,qJ,tG⟩
set_option maxHeartbeats 0 in
lemma fX:aD dM (ai cQ)=true:=by simp only [aD,and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aH (d:=4) ?_⟩,aH (d:=1) ?_⟩<;>simp only [aW]<;>(try repeat' apply And.intro)<;>decide +kernel
def cS (_:Nat):=0x965808769465755094657540946575309461755092462752855829948558298485582975855829648558295485582153824627738246275382462752823627738206276281756661817566518175664181756640817566206567401065614010656040106557417565574153655141856537501065374070653740106530401056854187568541655685314356784170567640705675419056754180567541705675316056752150560640805606407056064060560640405603408049568574495685734847668442482343424823324247233242452343424523324176809041768070318412323154128526783191267831212678311026763191267631212675412126184171261841612618412126083191260541812453237314678090146780101461801014608070146080501460801013451272
def bx (_:Nat):=0x82306318240152300810252493100532008015021683021531076255694810653000762326318002751007620569180038400076202691800762000750208924604653107361519420050210070352810670142300703228196702845006783004321004311067136584900463000670365849004830006350690857005460063406918570054600634069185700485006340691857004350063200786120761310632007861206502106320078612057021063200786120541810632007861205402106320078612043021063200786020850210632007860207502106320078602065191063200786020650210630531470204312006012648130040260054077183620671200540771836205217005267091485008530042654735820407300426007658201073004260076582010630042600765820096200426007658200862004260076582007510041730756930017300370208612004017103407907562037050031569275130642300307214263002140003016947530075400030121426300214000301214263001830002765068950056411027600689500564010276006895004530102713352490039400027133524900384000271335249003450002710352490034500025800543290032410240691856207512002406918562065120024069185620641800240671856204716002106928531075320021069285310642800210692853105726002106928531053260020569485300754000205694853006840002056948530064380020569485300643000205694853005320002036012780029611020360127800236110201694853007540002016948530068400020169485300674000201694853006540002016948530064800020169485300643000201694853005730002016948530053260016720598600576010167205986004650101620263180032610015360168920045110132681962007621001326819620068210013268196200651000123683962005428000765826713056230007628269170451200067283674206743000621463581040610006214635800305100054601687200346100346006875004571003284135200402100032681962007621000326817620076210003268176200659100032681762006521000321413520040210002674730820407300025683764207643000256837642065320
def dO:Nat:=0x241408410842110c0300c03
def dN:Nat:=0x11489414e86824914642a
lemma tP:ag dM 5 0 1:=ae dO dN cS bx 0x43 rfl (by decide +kernel)
lemma tQ:ag dM 6 0 3:=ae dO dN cS bx 0x2c1125 rfl (by decide +kernel)
lemma tR:ag dM 7 0 7:=ae dO dN cS bx 0x342d2111268edc rfl (by decide +kernel)
lemma tS:ag dM 8 0 28:=ae dO dN cS bx 0xc392711360349312e3522002836140833a799cededfcfa894bde2bc rfl (by decide +kernel)
lemma tT:ag dM 9 0 32:=by apply bA dO dN cS bx 0xb7bfcd9fa6b889a5b8cfa50098c8918700000000000000000000000000000000 2 rfl;simp only [bk];(repeat' apply And.intro)<;>decide +kernel
lemma q4:ag dM 9 32 32:=ae dO dN cS bx 0xcfd59c9d84b89aa3c5b89ae1a2cc009acf9e00e0aba6a4dba5c6d89fd0009ed1 rfl (by decide +kernel)
lemma q5:ag dM 9 64 32:=ae dO dN cS bx 0x36441a4c3a409f9f9f9f9fd992839fb88a009f9fa3a3d48b009fb4b290a99bb0 rfl (by decide +kernel)
lemma q6:ag dM 9 96 32:=ae dO dN cS bx 0x363638481036363624122438242f15383b2b1f1332194c3638301c3c0b383624 rfl (by decide +kernel)
lemma oB:ag dM 9 128 32:=ae dO dN cS bx 0x638384d0d45381230171d41023836003c060f242016183e4b4718120b241c36 rfl (by decide +kernel)
lemma oC:ag dM 9 160 32:=ae dO dN cS bx 0x5363715073a361e0b38361b1538123606363b060923361204013606004c3829 rfl (by decide +kernel)
lemma oD:ag dM 9 192 11:=ae dO dN cS bx 0x3838382a1238123800000a rfl (by decide +kernel)
lemma yM:ag dM 9 0 203:=(aw (aw tT (aw q4 q5)) (aw (aw q6 oB) (aw oC oD)))
lemma qZ:ag dM 10 0 32:=by apply bA dO dN cS bx 0x0 2 rfl;simp only [bk];(repeat' apply And.intro)<;>decide +kernel
lemma ox:ag dM 10 32 32:=by apply bA dO dN cS bx 0x0 2 rfl;simp only [bk];(repeat' apply And.intro)<;>decide +kernel
lemma oy:ag dM 10 64 32:=by apply bA dO dN cS bx 0xa6af00009fa60086c3b3c49fa68db6d6e500b09f9581c0a08cc0000000000000 2 rfl;simp only [bk];(repeat' apply And.intro)<;>decide +kernel
lemma oz:ag dM 10 96 32:=ae dO dN cS bx 0x86e381b8d786889fc3a681a686beaa93868600b1869fcbb000c9b5a6b19fbb86 rfl (by decide +kernel)
lemma mF:ag dM 10 128 32:=ae dO dN cS bx 0x84ca81d29586ca00b8b200cab000d300ca82d39fb8a6b9c3ca869f00dae485ae rfl (by decide +kernel)
lemma mG:ag dM 10 160 32:=ae dO dN cS bx 0xca81d286aa9f86009f9f86c0a19facadc7ca939f808fa68db0ddb6c1a6939f00 rfl (by decide +kernel)
lemma mH:ag dM 10 192 32:=ae dO dN cS bx 0x364d3f36060036360f12000f0f4d4606ba9fb8b8b8879fc29686979f00b09f00 rfl (by decide +kernel)
lemma mI:ag dM 10 224 32:=ae dO dN cS bx 0xf0f000f4e4600364d423d36420036004a060646063d0b4d0e0f4200000e4d rfl (by decide +kernel)
lemma mJ:ag dM 10 256 3:=ae dO dN cS bx 0xf0006 rfl (by decide +kernel)
lemma wX:ag dM 10 0 259:=(aw (aw (aw qZ ox) (aw oy oz)) (aw (aw mF mG) (aw mH (aw mI mJ))))
lemma q0:ag dM 11 0 32:=by apply bA dO dN cS bx 0x0 2 rfl;simp only [bk];(repeat' apply And.intro)<;>decide +kernel
lemma oA:ag dM 11 32 16:=by apply bA dO dN cS bx 0x0 2 rfl;simp only [bk];(repeat' apply And.intro)<;>decide +kernel
lemma wY:ag dM 11 0 48:=(aw q0 oA)
lemma q3:ag dM 12 0 6:=ae dO dN cS bx 0x0 rfl (by decide +kernel)
lemma eA:bT dM 12:=by intro k hk;match k with|5=>exact tP|6=>exact tQ|7=>exact tR|8=>exact tS|9=>exact yM|10=>exact wX|11=>exact wY|12=>exact q3|0|1|2|3|4=>exact cZ dM _ 0|_+13=>omega
lemma lV:aB false (ac 1407) 12 (cB 1407).toFinset:=gf (q:=383) (p:=ai cQ) (ad cQ dK) (by decide +kernel)
lemma xP:aR false (aN 2431) (ac 2431) 13:=
 aA (q:=1407) (rs:=[2,1,2,4,1,1,2,8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) lV
  (aT (g:=dM) (i:=0) rfl rfl (ad cQ dK) fX eA (by decide +kernel))
def lG:=ak cQ 13 [(9599,[100,131,82,16]),(17343,[114,67,84,48,33,97,128]),(9711,[100,131,116,50,33,16,80])]
lemma te:aX false lG:=aC (m:=2431) dK xP (by decide +kernel)
lemma xF:aR false (aN 1407) (ac 1407) 13:=
 aA (q:=1407) (rs:=[16,4,2,4,1,1,2,8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) lV
  (aT (g:=dM) (i:=1) rfl rfl (ad cQ dK) fX eA (by decide +kernel))
def lu:=ak lG 13 [(28143,[33,80,112,97,130,49,64])]
lemma s4:aX false lu:=aC (m:=1407) te xF (by decide +kernel)
lemma v5:aR false (aN 54143) (ac 54143) 13:=
 aA (q:=1407) (rs:=[2,1,34,4,1,5,2,8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) lV
  (aT (g:=dM) (i:=2) rfl rfl (ad cQ dK) fX eA (by decide +kernel))
def kg:=ak lu 13 [(54143,[]),(64447,[117,80,66,130,96,16]),(44015,[116,83,32])]
lemma qt:aX false kg:=aC (m:=54143) s4 v5 (by decide +kernel)
lemma vZ:aR false (aN 44415) (ac 44415) 13:=
 aA (q:=1407) (rs:=[16,1,2,4,1,1,2,8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) lV
  (aT (g:=dM) (i:=3) rfl rfl (ad cQ dK) fX eA (by decide +kernel))
def j9:=ak kg 13 [(44927,[84,131,98]),(47999,[101,66,16]),(53119,[98,82,16,66,49,128]),(58239,[82,129,48]),(69503,[84,66,16,98,129,48]),(58303,[118,133,33,48]),(60351,[114,67,84,48,33,97,128]),(69567,[117,80,66,130,96,16]),(42991,[83,114,99,33,16,64]),(60399,[80,81,114,66,50,129,96]),(69103,[116,50,129,80])]
lemma qo:aX false j9:=aC (m:=44415) qt vZ (by decide +kernel)
lemma vT:aR false (aN 43903) (ac 43903) 13:=
 aA (q:=1407) (rs:=[10,1,2,5,1,1,2,8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) lV
  (aT (g:=dM) (i:=4) rfl rfl (ad cQ dK) fX eA (by decide +kernel))
def j6:=ak j9 13 [(43903,[]),(46463,[84,131,98]),(48511,[101,66,16]),(51071,[100,131,82,16]),(43455,[98,118,81,130,50,65]),(43967,[118,130,81]),(54207,[116,100,49,32,81,128]),(58815,[114,67,84,48,33,97,128]),(49647,[83,114,99,33,16,64]),(51183,[100,131,116,50,33,16,80]),(54255,[116,83,32]),(55791,[83,133,115,67,32,96])]
lemma ql:aX false j6:=aC (m:=43903) qo vT (by decide +kernel)
lemma vQ:aR false (aN 42879) (ac 42879) 13:=
 aA (q:=1407) (rs:=[2,1,2,4,1,1,2,8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) lV
  (aT (g:=dM) (i:=5) rfl rfl (ad cQ dK) fX eA (by decide +kernel))
def j3:=ak j6 13 [(42879,[]),(60287,[82,129,48]),(44991,[98,118,81,130,50,65]),(69615,[33,80,112,97,130,49,64])]
lemma qi:aX false j3:=aC (m:=42879) ql vQ (by decide +kernel)
def C7:List (List Nat):=[[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def i9:List dd:=[(151,5,94,[48,33,133,118]),(173,5,61,[32,83,116]),(185,5,91,[81,130,118]),(188,5,91,[32,49,128,81,116,100]),(247,9,478,[48,33,133,118]),(339,5,91,[16,82,131,100]),(346,5,91,[128,49,100]),(369,5,94,[16,82,131,100]),(422,5,61,[32,49,128,81,116,100]),(440,5,94,[81,130,118]),(454,5,91,[16,32,48,128,100,80,116]),(460,5,94,[16,32,48,128,100,80,116]),(482,5,91,[128,81,32,49,100,116]),(484,5,91,[80,129,50,116])]
def At:=eJ i9 dW
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma Ci:aX true At:=by
 apply gb kU;apply aH (d:=6);simp only [aW]
 repeat' apply And.intro
 all_goals decide +kernel
def Dd:Array (bt × bt) := #[(0xf4e2669a6837f027081c0f22055df808222736,0x40209409843f007000c0720001df800000733),(0x601c324b069010597803f9010a2609fbe0181f,0x2080a02e269000187801f800000000fbe0180c),(0x250f0dd0188027ef8024025e13c1fd105e4930,0x22808d1092003e78000000e03c1fd001e4031),(0xc9c0d906874040901240ffc4fc1e1027e41fc0,0xc0c0010ec000000000007fc0fc1e0003e01fc0),(0x1028d4b1279c83fa01f1902f20e021fc806260,0x1028d4b1279c03f801f1800f00e001fc006000),(0x86910025492109002481248fff0841ffff8000,0x9100a343a000000000000fff0001ffff8000),(0x81412a020041fe000ffffffe01001009,0x814120000001fe000ffffffe00000001),(0x28004905ffc0481fffff04000804208c000,0x28004905ffc0001fffff000000000000000),(0x3a518020b05fffffff08400880910680110480,0x20aa0103c5ffffffe00000000000000000000)]
def Dc:List aZ:=[(64,0,447,0,13),(128,0,383,0,13),(256,0,255,0,12),(32,0,479,0,12),(4,0,507,0,12),(8,0,503,0,12),(2,0,509,0,12),(17,0,494,0,11),(7,0,504,0,7),(16,0,495,0,13),(3,0,508,0,9),(32,1,460,18,7),(16,2,424,69,7),(9,16,486,0,8),(0,32,94,385,8),(16,4,353,138,7),(4,8,227,272,7),(0,8,227,276,8),(2,1,460,48,7),(256,8,227,20,7),(14,0,497,0,7),(8,4,369,130,7),(5,2,440,64,6),(16,256,135,104,7),(10,4,369,128,6),(258,64,189,0,8),(34,1,460,16,6),(28,0,483,0,8),(0,16,486,9,10),(260,8,227,16,6),(0,64,189,258,10),(9,0,486,0,8),(36,128,347,0,8),(260,0,251,0,8),(35,0,476,0,7),(256,32,94,129,7),(4,2,440,65,7),(0,128,347,36,10),(56,0,455,0,7),(32,256,151,72,7),(1,32,94,384,7),(40,256,151,64,6),(11,16,484,0,5),(15,16,480,0,4),(36,0,347,0,8),(2,4,369,136,7),(258,0,189,0,8),(64,1,396,50,7),(268,0,243,0,7),(8,256,151,96,7),(13,16,482,0,5),(33,0,478,0,9),(11,0,484,0,5),(134,0,377,0,8),(13,0,482,0,5),(8,16,486,1,9),(273,0,238,0,7),(264,0,247,0,9),(44,128,339,0,5),(1,16,486,8,9),(352,0,159,0,8),(289,0,222,0,7),(2,16,484,9,7),(39,128,344,0,4),(256,64,189,2,9),(128,32,94,257,7),(3,128,344,36,6),(20,8,227,256,6),(48,1,460,2,6),(32,128,347,4,9),(37,128,346,0,5),(259,64,188,0,5),(265,16,230,0,5),(2,64,189,256,9),(4,128,347,32,9),(16,8,227,260,7),(296,0,215,0,7),(64,2,440,5,7),(64,256,151,40,7),(72,256,151,32,6),(96,256,151,8,6),(257,32,94,128,6),(41,16,454,0,5),(44,0,339,0,5),(69,2,440,0,5),(266,64,181,0,5),(19,0,492,0,8),(49,0,462,0,8),(152,0,359,0,8),(128,1,332,50,7),(256,16,230,9,7),(4,16,482,9,7),(8,128,339,36,7),(16,64,173,258,7),(6,16,480,9,6),(136,4,369,2,6),(272,8,227,4,6),(384,32,94,1,6),(73,0,422,0,5),(262,64,185,0,5),(265,0,230,0,5),(274,0,173,0,5),(274,64,173,0,5),(276,8,227,0,5),(292,128,91,0,5),(39,0,344,0,4)]
def Db:=C7
def CY (_:Nat):=0x1000090fd30b281002edebeda1759cedd17588f587f42ef25c4befc9513fe9b94549814c153549814c120f055354930483a454d524c120325535493048198edda54c910
def CZ (_:Nat):=0xd41b34204741039105268403991050687dc08000035a0a59104010c882ef4310000067a320057a1640060818013810000ee00cc600000e06504339883a8461d12300009020000d6071810004e6200037d944cd86b6100008d840000000001b6100007a21b040cbc70497c248c00000000022c200001d6090174194188a0ae1220a46f606496407a0b20804d9158ddc05c25881835e27c1360287f60f012425a06a0fa0547940142720dc000300bc023e00267e0487c048166021c94099e01470075e040680a3a00058063b2e8f8dddf68d834bcf32dc971dc22f3baed6b06b9a667a9ca619664a90a3a87e1783e007d1e072db66b9a5669926297c5b9665494a4b9204490a408f43b0e4370d4330be2d89d2307317054130440f03409c1f05c0089cbc22727089a9c0af06e8ba6b91e9ac6f94ae2e9aa8ba6a4771681fc89d1e9a42bc4899e9a22bc4848f2205ba67d16a5e45a9744f2dc10cb6d8e61a77b665eed987fb65e854d72dc658b71959bb7524e61431c64e8f052a0c949c2e5183b542a54903db8214ea0787a71d7e9c757a71daed063fb814f6e4427c40cf6602a18306960c009cbc46f1af0bcbb46f1ad19c6a05f1e705cb981f2e50dcb8cdf0529fa44a366101bc63c6f18e4ba5353e94c43b62c072ca03cb24ee9c797c703ff0ff63fd2ff0bf6afd63deaf3d39afe5bf7f4deeb7b6debb5fcd7b75ebd6f757ed5bf3afcdbf1efc77b1ddc6ff1afc5ff16fbf4afbabedadedb7aecfda7be9afa5be1ff87f61ef86fe17fea79460530e9b94605306eb94605306cb94605306a794605306d79260530ec59260530e519260530e515260530e63a464d20657a464d20aa7a6605206a7a6605206d79360520ea791605206cf916052064f916052054f9160520ed193605206dba154d206d8a954d206a4a954d20661a54c520edd954c120e91814c12054d814c120549814c120ec5534c1202e5534c120e91524c120e61524c12054d524c120605514c120605314c1206a3a464d10663a464d10ec5a564d10ec1a564d10ed1a960d10aa7a7549106a7a754910e9f9354910ed19354910ec99354910e9d9354910e9d835491064d8254910edda54c91054d52481105495148110
def C0 (_:Nat):=0xbb000000000000000000000000800000000000c300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000c500000000000044020000000000000000000000000000000000000000
def B7 (j:Nat):Nat:=(if j<2 then (if j<1 then 0x9c72fd9472fd9462fd9454fd24567d9c42dd9c42fd94459cc4421dbc32dd9c325db4258cc422dd8c183d24185d24069cc4089c9c01bdcbf1a5cbf2ddabe83d23e2cdabe8ac0be01dabd01d93d3fdb3c01dabc01d9bc01dc3b01dabb00dd3a00dab900d93900dc3800d93841d43741d2b740d43740d2b740cc3741d23600dc3600dab663d2354fd23511db3419d8b41bd83419d8b31bd83319d8b241d23215d9b100d9b000dc2f00daaf06daae42d42e42cc2e11db2d19d8ad13da2c19d8ac11db2b17d92b13da2a17d92a00dd2914d9a941da2815d9a801d92845d82800daa706d8a708d82700dca600dca500dd2400dd2300dd220cdc2216d9223fdb2101d9a117d92143d8a107d8a145d82109d82101dd1e13da1e08d81c3b5c9b3b549b3adc9b3ad49b00dc9a3bd39900dd1916d91803db9709d81701dd1513da1517d9153bd39500dc9200dd1100dd1014d99016d91001da8f41da0f17d90f43d88f01dc8e03db8e00dd0d32da8b8ea90b2fd90933d88921db8833d88829da0733d88725db062fd90633d88663da0529da0569d9052fd90571db8169c98168c9817ca9818ed9003dd37778a9c07aa900ffe7febff1ff6ffa7fcbfddfeaff37f7bfb7fdafec7f4bf7dfaffbdfdebbfddfdefdf7ebbeddefef776ffb7ddbdebff3fb9fbbfddfdefeb7ddbbfdd7edff3ff9fecfee7bf37f9afcbfe3feffd7fdbfe5feeff57f6bf7dfbaf7f7bebbfddfadfd5ffaff57f6bf75f7af7d6feaff4ff9ffcffa7fb3bf9bfc7fda1e51306a3914c1a5e453068b914c3a264530e81914c39464530e51814c39260530aa5814c1a960530649814c1526053068f98481a8e4d206979348198e4d206a391481a3e452064f9148153e4520e8598483a06612068598483a864d20e91934839864d20661934819564d2064d91483a960520e9981483a360520e4d814839160520aa581481a96052066181481936052054d81483a154d20aa553481a954d2068553480a954d20e9531483954c520aa531481a94c52069531480a94c520e9130483a14c120e6130483934c1206a130481a54c12068530481984c12065530481814c12054d30481524c12054530481314c1206a393441a8e491068f9244183e4910ea193443a564d10e9193443a264d10e8193441a864d1069593441a264d1066193443a864910e8d92443a1649106a192441a364910661924419364910aa583441a960d10ea582443a560910e8d824439560910e4d82442a9609106a582441a56091065582441936091054d82443a954910e9d52443a354910e4d52442a9549106a552441a35491064d52441835491060952443a54c910e5532442a94c9106a532441a54c91065532441854c910e852044393481106a120441a54811068d20441984811064d20441854811060d204415348110549204415148110 else 0x732dcb87285c74710dc116f71bb66df5b536ca1b036b45ab66a01a5968f5a0d67ed9df66e99a3661595664798f4633d8ae6209858608d8025f457a65e217765d657325c316f65b0969a599962a58355f057415ae562156b553151d53f54e152f94a751d945250713f74f713bf4e613744d493294bf52e54b212ad4a3125648b51fe47251a045e914744610e242e5083417104740c8fff3f08f8a3db4f3f3c20ef03b40eaa3a44e753974e423880deb3740da73604d4e34b0d0d33bccdc3338cbb32b0c993200c6d3178c1e2ff4bd12eb8b7f2da4b342c30ae42ab0a7d2940a2a27c89d526e0993259894024948f423748b4223885e20d48061f547be1e307621c906f11b406af1a1065118645ea16a457d152051113dc4de12e848d11ac44e109c3ef0ee439d0df835c0cf03170b7c2ba0a50275096422d07ec1d706d41990584142046c0fb033c08c011c00075d37764dd7764d97764d4f761d37647d2f61cdaf635d8f34dd37365ca7365ca720bdaf01ddaee1ddc6a0adae61cdae447d4620adade47d2dd1cdadd6cd9dc34d9dc6cc9dc6ca9dc2bda584dd3584dd3571d5cd61cdcd60adc5626db5646d4d647d4d51cd8d51dd8d41ddcd31c5cd326db5246d4d20adc511cdc500bdc4d46cc4d36dac937dc436fcc4377db4237dac287d24293c8c28ca9c290a9428dd8c18c5cc191cc406fcc3f92c0bf1ddaba46d2ba0adab954c1ae1dd9ab2ada270ad9a734d8a70ad9a647caa50adaa546caa51cdaa30bd9a135d8a123dba06fd81f37d81f1dda9e2bda1e0b5d1d0a5d1d0ad99c48d99b0adc1a1cdc1931d91649d3961ddc1565da152bda156bd91531d91547d4155bd39549d39549d3941cdc947fda9373d39353d1936bc9936ac9937ea9930adc121cdc111cda900bdc0e49db8e23db8e53d90e31d90e47cc0e46cc0e1ddc0d6fd80d37d80d47d40d46d40d46d48c92c28b92c18b92a98b6ec28a37d9866ec28537d98437da8337dc0236dc0280c2828cc18290c18192c18013dc7e13dafe13d97e40d47e40d17e01dafd01d97d01dc7c01d97c01dc7b01dafb41ca7a63ca7908dc7941d47841d2f841d4f74bd377415d7740dd7740d4f73fd37600dd7618d8f513da7419d8f401daf101d8f13ed37101daf001d8f001dc6f3bdbef0fdbef01d8ef01d9ed01dc6c01daec41da6c13da6c13da6b00dd6a00d9e951d16859cc6808d8e811db6741cc6541cae540cc6540cae510db6439d46313da6108d8603f5cdf3f54df3edcdf3ed4df00dcde3fd35d00dd5d0cdc5d43d4dc5dd35c56dc5c18d9dc56cc5c0cdc5b00d9db18d8db05db5a19d8da09d85a1fd85900dcd604db5600dc5514d9d515d9d400dcd108d85100dd5014d9d000dc4f00dacf14d9cf18d8cf19d8ce01dccd00dacc63cc4b62cc4b50a94a5edb4924db4983d2482cdac866cc482dd) else (if j<3 then 0xe4f6b20c7814441e1d451138b15a449c588f812716293ca51271623e05bff5e71e80004a953c8a9a459fe26100b479e6c1468ddfe98200ad9b491435fc749640392497af884632975f8851b2afaf290a0039a51fd71c00842adff313009a3afbd610a12bf3ea1000028954ab2c268c98892a9c0f0851b7fad640688f4f8ea51944788225cff6e4d44ab3473423dfe8544ea32fad612a1519571c001acf5f62000d6605b93ea1350bdc7f08e8ac6680ed451ff856c045b31974f00c6525f0db9a2b510b34dff2e9900732a9f140522a7f109d90bafb884e335ff2e9900232acebae2880030691fea3ac8568fd970d6e7a102216adfa19c03247bffe3b1a012155ffe6d8900252b6bc70151f280b4f7b0644e3f5c110354753c24268c7184688b5dfa10c26dcde451942361eeffc76340242bd9a58445fa11a890defd632456194b267895c699402c5f94242721d9f8398d0833e0f4ca2f61ce66484fa463668a5188b850fff406a0a99b9dd8706123ec50d6484fa463001dd5c92462875fa106881d3cc04d95de4e660f9d02d806a1403c230fe348813b497c71e746e180115a803d3f84143b0039b52ae0b416c330642372809290150513122a37602c251018081260a1089e1382084285c1b0a061841b60087104c0430a60c3018430c178271890642646040760887c15857876a103085f137c0a19a0ac14c964251ca0e483c178550746e42c82b12478800810a72041d03c09747c8fe890a013c5704da07218528aca04c180699c06aa7bc2051141607024831134264c806060a0306d04052a15c230a828109c0f8341a0f94c844086e19c4a0805c0841b01b814470208380584248550d07a09ac001fb0809e06804d02015c2d0a05e0d00e81460e0730302205a0c5c10250500934000ae0b6180d01e030059c060702a08f41b83b0404e04002b0b60c01812d0ba180b80bd05c134201002203fc4f0601003007707f01e07383cd6b329cbe72d9caef29dc9fb258c8a3200c7971ccc6cb19ec5f7157c50f12fc3e70d6c313097c1d7056c0a300fbfd2fe0bf42fbabe12f70bd66f42bc8eef1bb6eeabba6ee7eb9bae52b8eee1bb7eedd8b722da6b626d6bb556d37b466cffb3aacd5b302ca4b246c80b17ac48b0cec1db022becaf1abaaae2eb76ad82b47acdeb27ac22af1ab72aa2aa36a66a946a33a8729f4a75a9aea63296ba53a92aa40a8d5a2f6886a1fa866a17a84ea0ba826a0467fa9f9a7d19ec27979e1e7779d467299c4a7029bca6dd9b066919a2668199ca66a997664c98f662e987e61097e25e097625d096be59095b2542946a4e492a2472910e40b8f563b88e8a3828db63588cae2f28b3629e899e22d87fa1d786ca188852e11c83a20ab81c20338021ff57ee9f867d81f3b7c35ef37b65ea779c5e427859df17721d8b75d5d4a747dce6 else (if j<4 then 0x120c1a341832eea18f40f0481e622cf3147d30b1c7162e5e0c5daa6d462e8c16b960addc822f8b105b2931f31e2d03091f4c2c66f41a20f5cb056ee415cc87088e848e84de83441a3d1822f8b10000d7fe0b4030fae582bb91eba5485f162b2b9a20f6a5d13d539230d2581e050698af46a2cbe065e6c2607cba5919287107cc3265908a71b8211496d9b0356085e1d8c205392c0e83170e00319d4401338329be1106005f16207c904196c45f16202ee9251c8c930a570657040cf9f2d8462055d24a407c904474247434cc828fa616306347f5199850000170201341a9e0fb81f703ee07dc0f2de6170de61000049d5f1a8c58d5cc1909f50742057e27916ca00067ae3483f35e880031a4d7e5a7400002a348f8fda2000c4927fa87b018ca77e4f06c002512b7e751b000234997203419bd3054d87ccc96c38257cc163f340008a17a195aff4882ed00003e078400ff468018cd4fc40240002a1c13f84e5a4415683f924e00485231d0e24518dfa104f0879fc7c4d13c7ff83800001cda4feb2e002a152bf5dd120064377f863800001cda63f947000004234d7fd238000009da6bf82e045b2d76625fff8a9a8010693bfe68a0010892b76f84104d7dbc0b89dbe96a401c6611e990c47a64355fb658009926f9ff61b00842aef9f4d0046cc4fc0c00270a6eed00d841538591a239bfaa01878003a23df9821f88b204a8e3f40e40111d9d3e611a801d0e1d3dc9321b12de90404b67b00d42c317c8d8052180efcd2101c864ffdefc441133adbde1081209ffa4bab00c683fafc208ca33e18a04eb33be4401a123ff2c38919663f0dc499e1fb34a041b3c9d86a41a4b789425dff314003c483580f5e4060e9f2f1044eb7a4139c034833cce3d8106534ff0922420630fbad6b019238cdad08d1a6d68468bbf43320648fbe30a811a3afd6124801cd2adb793a4dbf34500028495d2eb004a8f49c4a931ac065c3e66358fdf0a6127cb780b13dd37444ff08082c270c17c808034845b7c03c02ace14b7eb8a50042d2ce1c6839e52e227759543227b7930c95db3930b2c3750a0e67ac4a2772f5b142166d3a76245d3cdd448cf961ac87ac88d1f90808c450d0d1b12d089fd25511813b40738a28d9503f331d3c6e20fae91206d2039f503424f284428a985de38366eb4305c4a66dd8dc2a78dc41a07e9634c3d17326fe31a8000e69371f10085298f63d64814cebfcea40007349bbc4804294afeb6050137fcba6401cca8fbbc48032950ffd1a8000e69371f10085295ff83500009d256bf5c3a04db0e095f3053dc7fd8402d239f062d190001711afc8c93000150f2e406835fefec00511e7fc50e00041a491d4d123e41341d9fb6c164f3ec1439e096445ec1435c12c891f5813322631e5e80071a27da1225de240214a57f5b02809bfe5d3200e6559f else 0x35dc301da928e045843494f16eb6ec185024fe49088a5271834836ff1a18d5bbe2838d254cc8afa7e714205ee1ae601d2ed91b4e9d275ba9632bc6d10d6a886186c4e59c62a382b6c7d210d508db298808feae8ea0386ef8e342c91a3133e3416a2e172f7304a3ec1072c8427d312ac42d0d73093d3331d32c11b117a0f0400031fe5d4543734c133e58267cb0505e2b99012fa25142286a75208df895ef70614d88a93ca2c66c44401e8c6c7a68a281a0a8fca33668daf580cd1cee0b43ea26c98f0a483b480ca0f51782068d)))
def Cc (_:Nat):=0xc00610b72b813515482944203880e207a351422c16800008701a0004eaa05fa2f400a0d0001237c1e000361303240f8000132821414a8a707e017956201f74b02a99f60b903701281ee061047806088800275c000000010617800281ccc88717bb381380b008934101d001005000081def00044000000489c03ba2d4058000151040c198025a80bbd408a4b3060008802a03b04d19900060af06a00cc1b40350218034a1e8e8001889ca0606606e59780a800000083e0002094028024807ec5f04100a8c0605800103100000009828e7428a14542800e000810e6819a12007908005916
def B8 (j:Nat):Nat:=(if j<1 then 0xbe0f07e2408e0381a80a9c2a5fe94ca46e8dba2ba88ca17e8189fa27c09e6a7589cda7169baa6b89a1a65c98e660f97ae5bd960654c949250193424af923646390f24158f8e3b48dd23388c3e2df8ada28889a223388221d4869e17f850211583a20b5822a0358019fd97ea1f7a7d41f287c1dedd7ac5e73791de257805dd576c5d86753dd127359c9f71c1c397011bd86e69b646c79ae06ab1a91699da2b67fd9bf668d980652d90f634d8ab61c185060557ee5e997895d857435c8d6f65b316a159e965358915ed570559555bd542549d5035351492518541a4f4938a4d5532c4bd12bb49a1234481d1d0467115f44c90fa433908140f900b3f60fae3e10f3f3bd4eca3a64e7038b8e0b378cda43594d26337cca03180c262fccbb02db8b2a2bb0aac2a1ca4728149ec26e097b252091c23e08b521e08341ff07cf1e747841cfc70b1b646a019e464418345cb165455914b851513784b51208442101c3d20e743660d083130b982c70a8827d08d4206073018e053c12a042c0e0028c06c00e0000d3533d3253d2a53d2a70d2a6dd326cd2a6cd742bd552bd352bd342bd152bd3065d3524d7523d74a3d7463d3523d34a3d3463d32a3d3263d2a63d3462d3262d3062d34a1d32a1d30a147514474b447454cf41473314732b4732549f29377253755337353373472434727351143511734b1434b17331173510435107347043470733107327072a704746f7742f4742fcf40f7342f4750e474ae9f48e4742e7730e772ae7330e732ae7330d7326d4752c8f4cc4746c7726cc722c7552c7352c4352c7b30c4742b7552b7352b474aa772aa7552a7352a434aacb40acf309cf2a9cf229cb509cb4a9cb429cb309cb2a9cb229cb029caa29730677750647506774a6474a69f4867744647446cf40673506734a67344673306735057346573305732a573265755247352447523474a347463772a377263755237352343523732a37326347522874e2474627726275522735224352273262b3042474a1772a17552173521434a1732a1cb500cb4a0cb460cb300cb2a0cb260cb0a0cb060caa605b43613515134b5134553f4145f2945f293534d2234d2134721343213511134b11343113510134701742f3f40f4f30f2f48e274cc6722c1552c1552b1152b1552a1152a974893f4296f309a72696b309a2a69aaa49a262913508134a81344813507134a71346717506174a65f4862f486174466f4063f406175051746567425374251352417523135231f4e213521bf4206f2606b260aaa40baa20034d20f486fffffeffdffcffbffaff6feffeefbff7feffdffdfedfddefdbfcffbffbfebfdbefbbfb7f9ff9ef9bfe5130e45306453060530e6120e4d20e45206612064d20645206052054d204c5204c120e4d10e491064d106491060d1060910549104c91048110 else (if j<2 then 0x8542afd71e6b0001ba52f32a1711238ebf7ff5900019256fc84a20ef8022451fe210c4033a489fdf9a32a01aa54ff9d546c4023a546f1303b14a434fce22a254693f9219251fbcaa48401349667f570b89f3fe98dc21988015dac77dd6892bf5c0388c3f133a274386132019fe5cc0e147f0fb81c46c3c7ae0468c7d61fab89efc9a20b945f7db09027299ff02a48006894bfea2802c8f3f1be002a8f332078ea32ff5c000511f31a0b1ccefe85a2d7961c802b662e4de5e45900215ab33f9a10046cf3f5cf8161c2400c93b7e7ff8030db40189377fffed4918b201a5317fcd41f4058903e67a02346effdd5880035684d3f9680000a344ebcffc1a9230090027505fe3cdf4015486fe2d5648b317a7c7e7088e67a4e4bc4488f684f0a1f860910bb4d70cb40095997f1baf9001e124b0f3eb22d957d7a4fb3604da00e4a1bff38138f3400992e312f6b400634373e862800568c0fc300699718c9f10a85d5deeeeb0c48001272fbb11e3d8c1a00849c7eff1005ca03a05d3c32ccf9e768b04664ff587950000099a7bba7b4b248f21b23238fe78c0c0200744b1fcf181804008e963f9e303008011d2c03ff113dcd30024b5c7c21267d400396acf8d1467d400396a9848fac4401492e381f10c01e3467fe3c48a0600786a4f3db1cfb1801e1a80bff70c70808185a833c3f1c202021698fcf40c02000536a3f3c00d13affff8a5820029a52f5febf0288010696741a0795af234006349def9a522a0049a61ff5b0e10922aec71c001c669fc002245ef98f9680cc00ced41dff8c0c0601769affd2450c0400826a5e56be300052495cfea000d23bbeb80000550c741a070ed79f8310000093597c32d02012b3cf88830004c923f903a5200784abfa7006451bf1534b4087499fc385c000d095b5fbe3dc202053a5df9f409c004e591fad02c44010cd23bf0a80751ce8340ebcac7cba0151247d99402c8fbf106d20159247ff1fca10401892a7caff00280212547e4fed141d8ae7f43fc6c01c91b1d78104024929b3fb454233f510c01a33cae7f000891df7a0d039fce00289cfe700144ebfea7fef0202002499313ffd00551d7958f1e400634a0fcfe7b0990a05a47dfc294020039a61fce00689df7a0d0387c5d40892a1f8e27406004925cf63660c00324b8ffb4301831671de3fc09801849c2604080631a2204f21b47e02200ae11603224341a6060f8671591c138c0820861304246e198d455064bc0e2891284041452a649e150060104911c46c0e81204844240e12031e183648017096800a0b9214370e9330fc334103b20d03c09020b82f08d0726d800782d0702c6041b8350d0cb05044266103000c020901f2082782805e118603e83280220ac99060290582a069894281007607e14210301502a8604813a11850500dc128260b82a170660c0 else 0x6793eb688648959a83db84618641099a63c740e409a479934f3f3214290c86effccaac81b307b7ad10a01a00b4fa2e200b4216d680b684ce5ebac8ab347f659b6ea4ab9476bced6888f666748473d1c6577aa891a102bc9cbc82839626a2f0aef5902b0fa5903fcca8341971d13a6892886c51cd17aeaa181e5210518597053a3085c82bba533230d968c235503e7852cdde12e1054384cd36f5eb152d5087ad577bd96597053a3080979abed48861dedce22cd713188a3e3bdc0e231cdb982328bd93305e50bffd5a740f240ff5b6202548eed6ff3ec60018698388e3e6cc0174a8bdfe00ea3484bdfe00f242e7f00051187dfe60016476edd4664dfcfa9e00112433962690c854a571ef6d0d675fe78800aa3edfa000b23d7fdb183000027699fce2e13a8dd40871d0b66dffb7e8002c913f9e1c2751a7ffff8deb89168800e69c7ee43840a0a674f18005c900eac208342861fe3c000d51f7ef000354795fae01c46087df3b2574eb8c98cac0186ad82cd9fc363b400013b4b393d9885c2bead62e10f8ad85013bfde0002a8f34efe348b35f7810311c08e9b3a901543f65f0da0488095a64ff23f0c000592b3ffa38440073457cb1ac01d66af973090005ed03ffd2f00016486e9100d0b669f32a37d4001152d3fccc050014686f84bf5c048000d5abbf949be800056699ff97e8802e480f2ccc78c64f8))
def Cd (j:Nat):Nat:=(if j<1 then 0x931828049fe42bc283841e02d972182e205d00b1c0aa0a6ea580092e0644ad55c4d284a03880fc040b33d80010027941c054eef74e2c00016b94095ca329413025e03495f80002ab801520a3400000002022117f049800000001c8a0000006842901a8000160d000001b7817007c6f400001003c03420dd023d028903294fe8079a28da44e527413c0003b160029d8ee000346776bd00e3912003ea0464207ad0400060e5416684f00006894c0f5dcc4233613e02400001b206136c1c182f488ce07302ae84a8449c0e81eab21f70a1e00c406c85a910be431803e824b68c8000096f913938c80cf8213c08c000494341268052054609952d40001b86406c1a0e52540002f4121438564241a148e880911406ce16e001c2214031e01c9d4c224a004a0495e9715160310e5f028881b40a2cc23003785603a0828c42a685a462f003781758258077e0d0c04a80ec000212c403100ce81ad7204892829841aa14ac05f01f1080e067c2c80002b116525c81a0001028211d42b4903204fa0400001dc8d30040ec829b5c90057a0ff415a1c1209de111d2cb821609be13f418d02db210887f081d82de203a16101e98441048813d89ef5c2b2904c7fc9b95c26681370b41c801fd0b780bcc9bb8168000012182ca22a3202000089c2a0110914172402dbd604516008000b831caa3062d0a0a256e76d2d6d000883470ad800000004813064c2869025a27d47ee900c0c20003020c0b2e5eea204000014e01e6911d097cf72ca579504000507700015c654578803000103e407380000100015b3172af9000000027a8e0b48a0600020666b002e2a857cb0c6052d941d370058c039c13a01200869530e0bcbd7776c6100025c03c04104146c1c4a51945ac8c5019704c922c972c81f601e7074800040993d1001fc0f251aa043c779494c5cf1113409a2027c143316d062e8ac0230825e20bae8e00950156034c076ee1004571a0ee8dd2801cf677c68a7e621dc3d779c112021da1ef0b3294280bc820c000085841e3985c441e08d95f5029c01ee00641b9008d270495f02d181830ab0948c2e0043105cf56c01fca0170420124480621e388d416d087e53cf047c0d6805c911840ae4f3e96c82286822130ae662bdb02e806e0156002db9380005176000aa22a139807c988e08b8135822635b962e02401130900028132a04800181b0341038078101800004502617008408a480700004040484c1607191205e731200418002280d404b0409016b9100841608070800008040082a20068497e8d02c84020e0b0dc0208010f4441c0a8186687148001608028a04411148088e3c0500c0a120501474200301c1c1604804642b010193a000180812011500c0e0b148183a0a0001c024604800120e080241c2f00884fa73060a400040f0000000000f80407010100048 else 0x403d05cc06901278235042c000484dc1120146043a0d5414a141a409c08280cd01614b420434a1d02534a4c0e1023f047000040c0c176b1e000d251881cd0313008642381fa836b7b5805942d981bd1410162c1ee221e0ae8138500e82c308de546029383d404e60fa002f83b409980004159853f57faca104fe80c8b0cc10480a7011c23e609b40e4023a09d2057c20c837d061a4fb82ce097502fe128405a2044000002b806b810b03bc0eb01a700c6027c12bee283a9407b457082a081ab44f015e0000325c066801941bd95b3b8892fa6c82002a07741084059a213082a119229b15c4026e52a52bd038c4a38f57828e520e01360ce029782fda7c467c4022a31d28a683900013a05022402ac28494020432114c0d682b80004003404982e345f609a510c00022920c9442800003094d32692c880740ae216b4024258a05f481402c1b36c0a88000c18484c60756081800e8116b11971a5ad6022c0270c6200009a6203c612dc22d31e800064b841b1829207e0000c0e8d2f706ba070ae0500a30aa60750194bd5a0aaa0c100600221091a0a3884f00840a6407b80400c5a40b6945c494805506414f6eac601500004098d83a82d6046403a412000030850000c)
def B9 (_:Nat):=0x1fffd8340260acff0e695c049961e62b073fe4c016141fe7000114a5dffad88930b3f9cc984002f0b5f5c41d0287ff9b1146197fcf3084026557f2fd08004a1607ffb22804a15b7b883a0517e79a0c051961fdc2650006565f397220392bbf61c200251597fd3800c50edf80c0eff6c42184bff980a812ec02a04ada80c20de782b849387810f730d4217a60040a67f00a40b4fe2128147eb4e000c520b0ec3464260a09054395c884403f158243e1c0206832990b06214830d81a0a35038350906c32190589c24110a0ac28220f82c1e07012b63b45b865015ebb9d6f2d318c2e255ca292b2243e6708cc1782a44b0870f119c2d04a87309e0b00046468c0d3986726ce458cc31936322c6058a9b131632646488c1918222a444c85ca47918f309e4d3c8a5985a609e4c3c905930b2434801ca5fffff7efbff7bd3048110
def Ce (_:Nat):=0x1094021e25e00490cc0ace241c14ea5b890b0ce4298000832c095c012604024e007811fbc0910205b0dd801f0a44000d42547e00014030212032800b034c2060d69b5a0978268000589140600032b100000008b2fab200000d44af1255010873a14ad051c028000026d08c410505f9d0109981104a6820c000503b250000000011fe0bcc294000ed6f05e09290c28180030000322b4242b4a41aa2b0c2ea7d4022f478c4e5a20593801e405309f8093a598e09050c08508880140cf9295bc51242010000306f00020d39f3f5a0920010940d604c428a0699e1e4afdecb10bd28f0bdc27b098d509009404f13fa5010270228017034b02d9ddf0b980f506d5a1002f59430be0003422c1f4000c18a016412b4aec95213a40de0d7c914476ed246bd0001b4ee82a4970a300bb402d77dc325956447b07e14b50c4011743002ce01510d9356c9641b30000275003b59d524c05490b97a20b00000c1d6076c1ba08280060a802d30396b1e0860c2200d989b485810d07942c164b8acb05943010c6c1fea5f9d044770c0804d45f10960001420c82701d0001008c170000aa40908d8fc028000107880fb04800e30d1d09800000030cd824800000030258184000413c00040fdb5fdc93bc8919f64d03057cb84be2bf000208eeb12a58806831e000204641f107429dc019ab2c19d5285bbd4060349029e24d01b106580e97d05e2327701c109d40f0bc719240bf015eb5841c976351230ae11e868503428830003a7581ae789415b479000002c40ec1499af201ca1432490214b50c226728d01c05a000249e00d903102acb6000000a0c08f02ac23c447c2db0b2a1610290124498d847b4f8329073c16263a000104e621b7d6534a0550002bc4107c080000205d493c0001d8848f49da077800c00000000001e0800082b1071c4910228b0c000cd437cddcfd08d000277548e624000030b1c4b4000012eb5501a00000001040c2a42440293000c2840000d4852f0b58000c14a0c3418f0aa804706641ee0af00030a341930c700016b2896a15000000ad82e301bc0aead600cc09c59280000322067c80c000409800659300b7290607aca0a1a0d2a400f96464968033020ac28686035702e02d568382479c15f4d68149990c50104002921771400253a01a1039b3e122e323b18a5010342351a2a03110000063202613702520603112a0e1a181d0665130005003b161e3d02160e02040c03200f01000009006d0c0e08010c0201130201070600011f08024b0509070c1c03010b1c0102002c
def Ca (_:Nat):=0xe802012c810082004024341410281a1a16120a0e06001f36804c120443ff
def Cf (_:Nat):=0x13ae07e26ca224c0000042410606e07dcc000000001c68540000090200000000c2e001030000000000000000130d6300090c000000000000000000000088c000000083f40000000000127e00caa0700000089a002370009ba000000000000000000000100e08c3c0848f4000000000020800000000000000c19ad500c0b000000000000011480009a00107400000000003448000000000000000185000000000000000000005bc000008348ac2280000084c002050008640b00800125c0061bc05038a780041200205000000c0c000000000000000000000397000d961100c44362122d0052001005
def Cb (_:Nat):=0x10090e08185081808013ff
def Cg (_:Nat):=0xc1009de4c0000284000045004a5c00c9005500000000000000000000000000000000000000000000008d0000000000d40000008c00000000009200
def wI:Nat->aF
 | 8=>(6,6,7,327686,51,6,4097,CY)
 | 9=>(69,5,7,2818098,102,10,4151,CZ)
 | 10=>(373,4,7,4849791,119,14,4299,B7)
 | 11=>(216,3,7,1769495,85,14,4244,B8)
 | 12=>(30,2,7,327683,50,11,4144,B9)
 | 13=>(3,1,7,65537,0,6,4109,Ca)
 | 14=>(1,0,7,65537,0,0,4105,Cb)
 | _=>a0
def yj:Nat->Nat->Option (Nat × Nat)
 | 9=>ch 1 113 0 8 3 3 C0
 | 10=>ch 26 127 7 13 7 4 Cc
 | 11=>ch 159 691 9 15 9 4 Cd
 | 12=>ch 102 467 8 14 8 4 Ce
 | 13=>ch 16 163 4 11 5 4 Cf
 | 14=>ch 3 59 0 8 2 4 Cg
 | _=>fun _=>none
def sg:aM:=⟨511,14,fun i=>Dd[i]?.getD (0,0),Dc,Db,wI,yj⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma kP:aD sg (ai At)=true:=by simp only [aD,and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aH (d:=6) ?_⟩,aH (d:=3) ?_⟩<;>simp only [aW]<;>(try repeat' apply And.intro)<;>decide +kernel
lemma sT:aP sg 8 0 6=true:=by apply aq 9 0 0;simp only [aE,ba];decide +kernel
lemma sU:aP sg 9 0 21=true:=by apply aq 9 0 2;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
set_option maxHeartbeats 0 in
lemma pW:aP sg 9 21 48=true:=by apply aq 10 0 3;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
lemma yi:aP sg 9 0 69=true:=(@aJ _ sg 9 0 21 48 sU pW)
lemma pN:aP sg 10 0 3=true:=by apply aq 9 0 0;simp only [aE,ba];decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pO:aP sg 10 3 128=true:=by apply aq 10 0 4;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma mx:aP sg 10 131 111=true:=by apply aq 10 0 4;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma my:aP sg 10 242 128=true:=by apply aq 11 0 4;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
lemma mz:aP sg 10 370 3=true:=by apply aq 11 0 0;simp only [aE,ba];decide +kernel
lemma wF:aP sg 10 0 373=true:=(@aJ _ sg 10 0 131 242 (@aJ _ sg 10 0 3 128 pN pO) (@aJ _ sg 10 131 111 131 mx (@aJ _ sg 10 242 128 3 my mz)))
lemma pP:aP sg 11 0 2=true:=by apply aq 9 0 0;simp only [aE,ba];decide +kernel
set_option maxHeartbeats 0 in
lemma pQ:aP sg 11 2 62=true:=by apply aq 10 0 3;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma nL:aP sg 11 64 123=true:=by apply aq 11 0 4;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
lemma mA:aP sg 11 187 29=true:=by apply aq 12 0 2;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
lemma wG:aP sg 11 0 216=true:=(@aJ _ sg 11 0 64 152 (@aJ _ sg 11 0 2 62 pP pQ) (@aJ _ sg 11 64 123 29 nL mA))
lemma pR:aP sg 12 0 1=true:=by apply aq 9 0 0;simp only [aE,ba];decide +kernel
lemma pS:aP sg 12 1 12=true:=by apply aq 10 0 1;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
lemma nM:aP sg 12 13 17=true:=by apply aq 11 0 1;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
lemma wH:aP sg 12 0 30=true:=(@aJ _ sg 12 0 1 29 pR (@aJ _ sg 12 1 12 17 pS nM))
lemma pU:aP sg 13 0 3=true:=by apply aq 10 0 0;simp only [aE,ba];decide +kernel
lemma pV:aP sg 14 0 1=true:=by apply aq 9 0 0;simp only [aE,ba];decide +kernel
lemma wJ:bo sg 14:=by intro k hk;match k with|8=>exact sT|9=>exact yi|10=>exact wF|11=>exact wG|12=>exact wH|13=>exact pU|14=>exact pV|0|1|2|3|4|5|6|7=>rfl|_+15=>omega
lemma pX:aB true co 14 inputs.toFinset:=by
 rw [show co=aY sg by decide +kernel];exact gk (g:=sg) (top:=14) (i:=0) (ad At Ci) kP wJ (by decide) (by decide +kernel)
lemma re:aR true (cB 511) (ac 511) 15:=
 cD (b:=13438558465) (by decide +kernel) (by
  have e1:ac 511=co:=by decide +kernel
  have e2:cB 511=inputs:=by decide +kernel
  rw [e1,e2];exact pX)
lemma zZ:aR false (cB 511) (ac 511) 15:=kr re
def nl:=ak j3 15 [(511,[])]
lemma wN:aX false nl:=aC (m:=511) qi zZ (by decide +kernel)
def nP:List dd:=[(151,5,94,[48,33,133,118]),(185,5,91,[81,130,118]),(188,5,91,[32,49,128,81,116,100]),(223,9,478,[80,16,33,50,116,131,100]),(239,9,127,[32,83,116]),(247,9,478,[48,33,133,118]),(254,8,251,[32,83,116]),(339,5,91,[16,82,131,100]),(346,5,91,[128,49,100]),(350,8,95,[128,49,100]),(369,5,94,[16,82,131,100]),(371,8,95,[16,82,131,100]),(375,9,127,[16,82,131,100]),(381,9,127,[48,129,82]),(440,5,94,[81,130,118]),(444,8,95,[32,49,128,81,116,100]),(446,9,127,[32,49,128,81,116,100]),(454,5,91,[16,32,48,128,100,80,116]),(460,5,94,[16,32,48,128,100,80,116]),(463,9,127,[16,32,48,128,100,80,116]),(471,8,251,[16,82,131,100]),(477,8,251,[48,33,133,118]),(482,5,91,[128,81,32,49,100,116]),(484,5,91,[80,129,50,116]),(491,9,127,[128,81,32,49,100,116]),(493,9,127,[80,129,50,116]),(499,9,478,[32,83,116]),(501,8,251,[80,16,33,50,116,131,100]),(505,9,478,[16,82,131,100]),(506,8,251,[128,49,100]),(510,12,255,[32,49,128,81,116,100]),(1279,12,3579,[81,130,118]),(1407,13,28143,[32,49,128,81,116,100]),(1503,12,18911,[128,49,100]),(1527,12,3579,[16,32,48,128,100,80,116]),(1531,12,18911,[48,129,82]),(1791,12,17405,[48,129,82]),(1967,11,4927,[32,49,128,81,116,100]),(1983,13,17343,[48,129,82]),(2015,12,17403,[48,129,82]),(2039,12,17403,[80,129,50,116]),(2045,12,17151,[48,129,82]),(2431,13,9599,[16,82,131,100]),(2493,11,2239,[48,129,82]),(2495,13,9599,[32,49,128,81,116,100]),(3263,11,1375,[80,16,33,50,116,131,100]),(3391,11,1343,[81,130,118]),(3519,13,28143,[16,32,48,128,100,80,116]),(3571,9,11742,[32,83,116]),(4955,8,1725,[81,130,118]),(4991,13,17343,[16,32,48,128,100,80,116]),(5053,11,6847,[48,129,82]),(5111,12,17403,[16,32,48,128,100,80,116]),(5115,12,17405,[16,32,48,128,100,80,116]),(5117,12,17403,[48,33,133,118]),(6511,11,1343,[16,32,48,128,100,80,116]),(6606,8,1119,[16,32,48,128,100,80,116]),(6639,13,28143,[81,130,118]),(6654,12,18911,[80,129,50,116]),(7039,13,17343,[81,130,118]),(7150,11,6847,[128,49,100]),(7166,12,17403,[128,81,32,49,100,116]),(8167,11,1727,[16,82,131,100]),(8175,13,17343,[32,49,128,81,116,100]),(8183,12,17405,[32,49,128,81,116,100]),(8190,12,17151,[32,49,128,81,116,100]),(8679,11,2751,[16,82,131,100]),(9702,8,2237,[16,82,131,100]),(9710,11,2239,[128,49,100]),(11710,9,18814,[81,130,118]),(11711,13,28143,[16,82,131,100]),(11773,12,18911,[81,130,118]),(12716,7,2079,[32,49,128,81,116,100]),(12719,11,2367,[32,83,116]),(12733,11,2239,[80,129,50,116]),(12735,13,9599,[81,130,118]),(12781,9,2429,[32,83,116]),(12783,13,9599,[16,32,48,128,100,80,116]),(13310,12,27127,[48,129,82]),(13806,11,2751,[32,49,128,81,116,100]),(14191,11,4927,[128,81,32,49,100,116]),(14269,11,6847,[80,129,50,116]),(14303,12,17403,[16,82,131,100]),(14310,8,1725,[32,49,128,81,116,100]),(14319,13,17343,[16,82,131,100]),(14333,12,17403,[80,16,33,50,116,131,100]),(14334,12,17405,[16,82,131,100]),(17342,9,7038,[81,130,118]),(17406,12,17403,[32,83,116]),(18429,12,27127,[128,81,32,49,100,116]),(18779,8,11453,[81,130,118]),(18815,13,28143,[32,83,116]),(18939,12,18911,[16,82,131,100]),(18940,9,11742,[81,130,118]),(27623,11,2751,[80,16,33,50,116,131,100]),(28079,11,1343,[80,129,50,116]),(28134,8,11453,[16,82,131,100]),(28155,12,3579,[128,49,100]),(28157,12,3579,[80,16,33,50,116,131,100]),(28158,12,18911,[16,32,48,128,100,80,116]),(32750,11,2751,[128,49,100]),(37374,12,27127,[48,33,133,118]),(42719,9,48094,[80,16,33,50,116,131,100]),(42727,8,42679,[16,82,131,100]),(42867,8,42591,[16,82,131,100]),(42943,13,44927,[81,130,118]),(42951,7,42683,[16,82,131,100]),(42995,9,48094,[32,83,116]),(43003,12,44799,[81,130,118]),(43447,9,46455,[81,130,118]),(44287,12,58335,[48,33,133,118]),(44415,13,58239,[48,129,82]),(44479,13,58239,[48,33,133,118]),(44511,12,68863,[16,32,48,128,100,80,116]),(44539,12,58335,[48,129,82]),(44541,12,68863,[80,129,50,116]),(44791,9,48094,[128,81,32,49,100,116]),(44915,8,42679,[81,130,118]),(45039,13,44927,[80,129,50,116]),(45041,7,42711,[81,130,118]),(45047,12,42751,[80,16,33,50,116,131,100]),(45051,12,42751,[81,130,118]),(48063,13,44927,[32,49,128,81,116,100]),(48079,9,42623,[16,32,48,128,100,80,116]),(48095,12,42751,[16,32,48,128,100,80,116]),(48111,13,42879,[16,32,48,128,100,80,116]),(48126,12,44799,[32,49,128,81,116,100]),(48635,12,58623,[81,130,118]),(49403,8,43479,[16,82,131,100]),(49643,9,46455,[80,129,50,116]),(49662,12,58623,[32,49,128,81,116,100]),(50047,13,58239,[128,49,100]),(50143,12,58335,[128,49,100]),(50158,11,58047,[128,49,100]),(50159,13,58239,[128,81,32,49,100,116]),(50167,12,58335,[128,81,32,49,100,116]),(50174,12,68863,[32,49,128,81,116,100]),(51135,13,54143,[81,130,118]),(51151,9,43647,[16,32,48,128,100,80,116]),(53086,8,42679,[48,33,133,118]),(53183,13,42879,[32,49,128,81,116,100]),(53198,8,42679,[32,49,128,81,116,100]),(53215,12,42751,[48,33,133,118]),(53229,9,44925,[32,83,116]),(53231,13,44927,[32,83,116]),(53244,9,48094,[16,32,48,128,100,80,116]),(53245,12,44799,[48,129,82]),(53246,12,42751,[32,49,128,81,116,100]),(54206,9,43647,[32,49,128,81,116,100]),(54253,9,43647,[80,129,50,116]),(55039,12,58335,[80,16,33,50,116,131,100]),(55231,13,58239,[80,16,33,50,116,131,100]),(55279,13,58239,[80,129,50,116]),(55287,12,68863,[16,82,131,100]),(55294,12,58335,[80,129,50,116]),(55789,9,46455,[128,81,32,49,100,116]),(55799,12,58623,[16,82,131,100]),(58111,12,68863,[32,83,116]),(58301,11,44223,[48,129,82]),(58363,12,68863,[128,81,32,49,100,116]),(58814,9,46455,[48,33,133,118]),(60251,8,44733,[48,33,133,118]),(60380,7,42711,[128,49,100]),(60382,9,48094,[80,129,50,116]),(60396,8,42679,[128,49,100]),(60409,9,48094,[32,49,128,81,116,100]),(60411,12,44799,[128,81,32,49,100,116]),(60414,12,42751,[128,49,100]),(63871,13,64447,[81,130,118]),(69053,11,44223,[80,129,50,116]),(69055,13,58239,[32,49,128,81,116,100]),(69094,8,44221,[80,16,33,50,116,131,100]),(69111,12,58335,[32,83,116]),(69118,12,68863,[128,49,100]),(69561,8,42679,[80,129,50,116]),(69617,7,42711,[128,81,32,49,100,116]),(69619,9,48094,[48,129,82]),(69627,12,42751,[128,81,32,49,100,116]),(69628,9,48094,[81,130,118]),(69630,12,44799,[128,49,100]),(73703,11,64191,[16,82,131,100]),(73710,11,64191,[32,49,128,81,116,100]),(74214,8,44221,[128,49,100]),(74218,7,44155,[128,81,32,49,100,116]),(74222,11,44223,[128,49,100]),(74223,13,58239,[16,32,48,128,100,80,116]),(74238,12,58335,[16,32,48,128,100,80,116])]
def CT:=eJ nP nl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma C4:aX false CT:=by
 apply gb wN;apply aH (d:=6);simp only [aW]
 repeat' apply And.intro
 all_goals decide +kernel
def Da:Array (bt × bt) := #[(0xffffffffffffffff0247102040c820c0830811,0x3f03f81ff800001f8000),(0xffffffffffffffff04c1040881096109041223,0xffffffffffffffffffc000000007e000007fff),(0x888245902104218288206,0xfff800001ff81f8000),(0x111008902432803260844c,0xffffffffffffffff000000001fffe007e001ff),(0x302182060608060410c08,0xffc0fc07e0001ff8007e00),(0xa004820208841484826190,0xffffffffffffffff0000000000001fffe07fff),(0x4420410491010901141020,0x7fff81fffff8000),(0x280820430a040604082080,0xffff0007ffffe000000000),(0xd030c38414021802104140,0xfffffff800000000000000)]
def C9:List aZ:=[(43072,0,43455,0,13),(43010,0,43517,0,12),(42512,0,42991,0,13),(42624,0,42879,0,13),(42560,0,42943,0,13),(59905,0,60414,0,12),(43648,0,43903,0,13),(256,0,255,0,12),(42504,0,42999,0,12),(2,0,509,0,12),(42752,0,42751,0,12),(43536,0,44015,0,13),(69121,0,69630,0,12),(42500,0,43003,0,12),(49153,0,49662,0,12),(32,0,479,0,12),(42528,0,42975,0,12),(17,0,494,0,11),(53776,0,54255,0,13),(1152,0,1407,0,13),(50704,0,51183,0,13),(66,0,445,0,11),(52737,0,53246,0,12),(1056,0,1503,0,12),(4,0,507,0,12),(48256,0,48511,0,13),(8,0,503,0,12),(16,0,495,0,13),(1032,0,1527,0,12),(1,0,510,0,12),(1028,0,1531,0,12),(53824,0,54207,0,13),(128,0,383,0,13),(1600,0,1983,0,13),(132,0,379,0,11),(2180,0,2427,0,11),(0,1,460,50,8),(24,0,487,0,11),(69136,0,69615,0,13),(47617,0,48126,0,12),(48132,0,48635,0,12),(50816,0,51071,0,13),(55305,16,55782,0,8),(11265,0,11774,0,12),(9,16,486,0,8),(49168,0,49647,0,13),(55312,0,55791,0,13),(1280,0,1279,0,12),(12305,0,12782,0,11),(43584,0,43967,0,13),(58624,0,58623,0,12),(59920,0,60399,0,13),(34,1,460,16,6),(47633,0,48110,0,11),(68624,0,69103,0,13),(7,0,504,0,7),(36,128,347,0,8),(40,256,151,64,6),(58432,0,58815,0,13),(13825,0,14334,0,12),(13841,0,14318,0,11),(160,0,351,0,11),(260,8,227,16,6),(1538,0,2045,0,12),(18433,0,18942,0,12),(1544,0,2039,0,12),(1568,0,2015,0,12),(32,1,460,18,7),(10,4,369,128,6),(46208,0,46463,0,13),(60032,0,60287,0,13),(6145,0,6654,0,12),(27649,0,28158,0,12),(5,2,440,64,6),(27664,0,28143,0,13),(2112,0,2495,0,13),(1792,0,1791,0,12),(52753,0,53230,0,11),(44676,0,44923,0,11),(18560,0,18815,0,13),(47744,0,47999,0,13),(55304,0,55799,0,12),(43266,64,43197,0,8),(57984,0,58239,0,13),(16897,0,17406,0,12),(0,4,369,138,8),(0,8,227,276,8),(58373,0,58874,0,8),(12297,16,12774,0,8),(49161,16,49638,0,8),(54800,0,55279,0,13),(44608,0,44991,0,13),(2208,0,2399,0,11),(46084,128,46427,32,9),(0,2,440,69,8),(52800,0,53183,0,13),(42628,0,42875,0,11),(3,0,508,0,9),(44096,0,44479,0,13),(57920,0,58303,0,13),(2176,0,2431,0,13),(6657,0,7166,0,12),(44164,0,44411,0,11),(12304,0,12783,0,13),(0,64,189,258,10),(5,0,506,0,8),(2,4,369,136,7),(47632,0,48111,0,13),(69184,0,69567,0,13),(73233,0,73710,0,11),(4740,0,4987,0,11),(55297,16,55782,8,9),(258,64,189,0,8),(1,32,94,384,7),(47680,0,48063,0,13),(69128,0,69623,0,12),(2084,128,2395,0,8),(42532,128,42843,0,8),(40,0,471,0,8),(43048,0,43479,0,8),(8,4,369,130,7),(257,32,94,128,6),(52752,0,53231,0,13),(3136,0,3519,0,13),(54848,0,55231,0,13),(59968,0,60351,0,13),(53888,0,54143,0,13),(32273,0,32750,0,11),(54801,0,55278,0,11),(0,128,347,36,10),(1,16,486,8,9),(4,128,347,32,9),(46116,128,46427,0,8),(13840,0,14319,0,13),(50752,0,51135,0,13),(4736,0,4991,0,13),(6784,0,7039,0,13),(69248,0,69503,0,13),(7681,0,8190,0,12),(47624,0,48119,0,12),(73745,0,74222,0,11),(320,0,191,0,11),(2,64,189,256,9),(32,128,347,4,9),(264,0,247,0,9),(6153,16,6630,0,8),(15,16,480,0,4),(9232,0,9711,0,13),(54785,0,55294,0,12),(13826,0,14333,0,12),(69122,0,69629,0,12),(27656,0,28151,0,12),(8,16,486,1,9),(47625,16,48102,0,8),(48164,128,48475,0,8),(296,0,215,0,7),(64064,0,64447,0,13),(63616,0,63871,0,13),(44546,0,45053,0,12),(3076,0,3579,0,12),(44548,0,45051,0,12),(57888,0,58335,0,12),(47872,0,47871,0,12),(2114,0,2493,0,11),(68674,0,69053,0,11),(1216,0,1343,0,11),(1,2,440,68,7),(4,8,227,272,7),(11328,0,11711,0,13),(68672,0,69055,0,13),(73729,0,74238,0,12),(27650,0,28157,0,12),(52738,0,53245,0,12),(44552,0,45047,0,12),(46112,0,46559,0,12),(58112,0,58111,0,12),(6161,0,6638,0,11),(12354,0,12733,0,11),(2240,0,2367,0,11),(2368,0,2239,0,11),(0,16,486,9,10),(12,0,499,0,9),(18,0,493,0,9),(33,0,478,0,9),(256,64,189,2,9),(0,256,151,104,8),(13833,16,14310,0,8),(69129,16,69606,0,8),(7696,0,8175,0,13),(49680,0,50159,0,13),(12352,0,12735,0,13),(16960,0,17343,0,13),(9344,0,9599,0,13),(59906,0,60413,0,12),(44036,0,44539,0,12),(68616,0,69111,0,12),(13329,0,13806,0,11),(69144,0,69607,0,11),(64066,0,64445,0,11),(69123,0,69628,0,9),(27657,16,28134,0,8),(46090,0,46581,0,8),(59923,0,60396,0,8),(1060,128,1371,0,8),(69127,0,69624,0,7),(256,8,227,20,7),(130,1,332,48,6),(49792,0,50047,0,13),(68609,0,69118,0,12),(69124,0,69627,0,12),(47648,0,48095,0,12),(17152,0,17151,0,12),(9233,0,9710,0,11),(27160,0,27623,0,11),(144,0,367,0,11),(60064,0,60255,0,11),(4800,0,4927,0,11),(42688,0,42815,0,11),(64320,0,64191,0,11),(58368,64,58557,258,10),(58370,64,58557,256,9),(59910,0,60409,0,9),(49160,16,49638,1,9),(10,0,501,0,8),(59940,128,60251,0,8),(52897,0,53086,0,8),(257,0,254,0,8),(58626,64,58557,0,8),(260,0,251,0,8),(2,1,460,48,7),(8,256,151,96,7),(18,1,460,32,6),(136,4,369,2,6),(39,128,344,0,4),(0,0,511,0,15),(6160,0,6639,0,13),(44560,0,45039,0,13),(64,0,447,0,13),(44160,0,44415,0,13),(44672,0,44927,0,13),(11266,0,11773,0,12),(16898,0,17405,0,12),(44034,0,44541,0,12),(4612,0,5115,0,12),(27652,0,28155,0,12),(57860,0,58363,0,12),(4616,0,5111,0,12),(44064,0,44511,0,12),(59936,0,60383,0,12),(44288,0,44287,0,12),(6673,0,7150,0,11),(7704,0,8167,0,11),(68632,0,69095,0,11),(73240,0,73703,0,11),(80,0,431,0,11),(1616,0,1967,0,11),(1156,0,1403,0,11),(1168,0,1391,0,11),(58016,0,58207,0,11),(44544,64,44733,258,10),(47617,16,48102,8,9),(52739,0,53244,0,9),(42508,0,42995,0,9),(52754,0,53229,0,9),(48160,128,48475,4,9),(11297,0,11742,0,9),(48,0,463,0,9),(65,0,446,0,9),(50817,0,51070,0,9),(288,0,223,0,9),(0,32,94,385,8),(54793,16,55270,0,8),(69190,0,69561,0,8),(258,0,189,0,8),(17154,64,17085,0,8),(44802,64,44733,0,8),(49412,0,49403,0,8),(59911,0,60408,0,7),(69134,0,69617,0,7),(35,0,476,0,7),(42552,0,42951,0,7),(44700,0,44899,0,7),(256,32,94,129,7),(44812,0,44787,0,7),(53025,0,52958,0,7),(24,4,353,130,6),(160,1,332,18,6),(13,16,482,0,5),(152,4,353,2,5),(141,16,354,0,4),(73744,0,74223,0,13),(52864,0,53119,0,13),(12801,0,13310,0,12),(36865,0,37374,0,12),(49665,0,50174,0,12),(17922,0,18429,0,12),(18434,0,18941,0,12),(18436,0,18939,0,12),(26632,0,27127,0,12),(13856,0,14303,0,12),(18464,0,18911,0,12),(68864,0,68863,0,12),(49681,0,50158,0,11),(68625,0,69102,0,11),(8216,0,8679,0,11),(9240,0,9703,0,11),(42520,0,42983,0,11),(4674,0,5053,0,11),(13890,0,14269,0,11),(57922,0,58301,0,11),(12368,0,12719,0,11),(27728,0,28079,0,11),(4752,0,4975,0,11),(42640,0,42863,0,11),(18592,0,18783,0,11),(47776,0,47967,0,11),(52896,0,53087,0,11),(3264,0,3391,0,11),(18624,0,18751,0,11),(44736,0,44863,0,11),(1856,0,1727,0,11),(3392,0,3263,0,11),(55104,0,54975,0,11),(52736,64,52925,258,10),(44546,64,44733,256,9),(18435,0,18940,0,9),(6,0,505,0,9),(3084,0,3571,0,9),(69132,0,69619,0,9),(12306,0,12781,0,9),(53778,0,54253,0,9),(55314,0,55789,0,9),(20,0,491,0,9),(59937,0,60382,0,9),(50736,0,51151,0,9),(11329,0,11710,0,9),(16961,0,17342,0,9),(53825,0,54206,0,9),(58433,0,58814,0,9),(43080,0,43447,0,9),(129,0,382,0,9),(130,0,381,0,9),(58624,64,58557,2,9),(272,0,239,0,9),(42784,0,42719,0,9),(9,0,486,0,8),(47625,0,48102,0,8),(55305,0,55782,0,8),(68617,16,69094,0,8),(36,0,347,0,8),(4644,128,4955,0,8),(18468,128,18779,0,8),(44068,128,44379,0,8),(57892,128,58203,0,8),(67,0,444,0,8),(134,0,377,0,8),(140,0,371,0,8),(4748,0,4979,0,8),(42636,0,42867,0,8),(44684,0,44915,0,8),(161,0,350,0,8),(52994,64,52925,0,8),(58114,64,58045,0,8),(42776,0,42727,0,8),(47944,0,47799,0,8),(14,0,497,0,7),(44558,0,45041,0,7),(21,0,490,0,7),(73749,0,74218,0,7),(47672,0,48071,0,7),(74,0,437,0,7),(12371,0,12716,0,7),(168,0,343,0,7),(268,0,243,0,7),(18,4,353,136,6),(48,1,460,2,6),(272,8,227,4,6),(272,32,78,129,6),(384,8,99,20,6),(21,2,424,64,5),(41,16,454,0,5),(50,1,460,0,5),(133,2,312,64,5),(138,4,369,0,5),(266,64,181,0,5),(321,32,30,128,5),(270,64,177,0,4)]
def CS (_:Nat):=0x30a206102004e8a0e8c6c0b2eb28da986d9ada8efa1d3d389edfd2bf251de8cb5cd425c1206ddb62a531480c954d524c120661814c53048152605314c120
def BT (j:Nat):Nat:=(if j<1 then 0xad8b0aad8b06ad8aa6adc30aaacb30a6cb2aa6cb0aa6c96aa6c94aa5d302a1ab0299c3029603028ebb926ebb906ebb306eb9946eb9926ed306683b8534438b3212cb300b8b291b012502a524d34f20d34320bb4f1cbb4b1d4aa51cb35114bb4b101b83051309050aa7057260fcbb52f8bb40f94260f80b90f4e302f40b90f0ea60f00b90e8b350e4b340e53b02e53260e4bb70e0bb6ae0bb40e14260e00b90dcc30adceb62d87b82d5e994d26186d26b30caa2a6c92b02c48b8cc2a392bea382bc9382bea360bea342be8330bea322bea300bea220bea192bea174bea152bc2196b98172b02390ad538cad6b88ad7386ad72a6ad7330a97192a9bb6aa69330a6c2a4a52342a1b262a0fb429d53309d92629d134299a262983382951b4295733095db0291f2a28cbb708a0aa2880b8a840b8a800b8080daa480c2a67c0b8a78d2a6780b90740b8472a3066dcb666ab34a6ab39266b38666b36666b34666b32666b30666b17464bb6a600b8a5c5b8a58e35054a36a500b8a4e4b02480b8244a30244c39640c3663c738639636638cb70340b903223502c4b96284b9026430424539020db461c53861a2aa619e3461652a615fb461272a6121b460c73860a2b460a3346067aa606439402838a00299700ab6ee25b30a4119498038247ff8ffd3ff0ff6bfd8ff4ffd2fbf3ef4f7f3dd3f72fd5bf3ebcf6f3d3cdbe7d79f3e7bf9ebe76f9d7e6ef9afe67f97fe5ef95fe3fb8fbe1ff7fadfe37f6dfd37f2dfbb7e6defb7b6d7fb5fcd7df5f6d7bb5dbd6ff5bed6ef5b7d5f7577d3fb3facfdb3eecf7b3d7cefb1ffc7fb1fdc7ef1f7c7bf1dfc6ff17fc4ff0ffbfdafd3bedadfdb7daddbaffa9ffa7f69fba7de9efa6fe7f69dea5fe8ffa3ee87fe1fd2a563505602a542505606c8a9505606c8a9605306cda5245302cda4661206d8a3661206e99564d206dc93645206d893645206c553605206cca9605202e9545c1205cd425c1202e5a154d206d8a954d206c4a954d202e5a54c5202e1a54c5202e9944c5206dca94c5206d8a94c5206d4a94c5202e9984c1202cd984c120661814c12054d814c120549814c1206e5804c1202e5534c12054d524c120661514c120609514c120605514c1202e5514c1206d5314c120605314c1206c8a54c1206d8954c1206d0954c1206cc954c120661a724d2069d9524d206999524d206c8a960d102e993609106d4a9609106cca9609106e9954c9106e5a54c11054d52481106c951481105495148110659a2604306e9926043068991604306c55364420661a3604206e9936042064da154c202e99854c20655a3608106e995608106c99560810651a3548106e993548106d593548106a1935481068d935481068d92548106e582548106a58254810661825481065d825481065982548106558254810651825481064d8254810 else 0x3be9190000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c2305002fffec004058000000000000000000000007ffcb004a5200000000000000000000000000c0081c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000fff619148001ffc827bf200584e0ffbc0c200ffc80600f84dbc8c807710e102c029d632d006e32506181d0177035c0f361415300380572c00037f091a14989ae8940cc114815b81a749f0d3815ae10b841d133c21d08b411015c03900d3c0101e40490113a0be81bc00d8dafb5b696d1da1b3f676cdd99b2f656c9d91b1f636c5d89b0f616c1d81aff5f6bdd79aef5d6b9d71adf5b6b5d69acf596b1d61abf576add59aaf556a9d51a9f536a5d49a8f516a1d41a7f4f69dd39a6f4d699d31a5f4b695d29a4f49691d21a3f4768dd19a2f45689d11a1f43685d09a083d97a2f25e0bb9762ea5d0b99722e25c0b51692d059cb31652c858cb11612c057caf15d2b49652c2574ac9552a2534a49452824f49c9352624b4949252424748c915222434849052023f47c8f51e23b4748e51c23746c8d51a2334648c51822f45c8b51622b4548a51422744c895122234448851021f43c8750e21b4348650c217422c3204103c0023b0f30f30f2cf3031881930cf2a508f350fd7b06fd5b22f99a20f86392ec6b80ecf172ecf306ddc364cdd366c9d172c89b82c2ab02bd8972b6d364b29b04b2d2a4b28972b18b90)
def BZ (_:Nat):=0x6000005c000000000000000080000041000000000000428000000000000000000000000021ff0042000000002c0000080000000000007a03000000001
def BU (j:Nat):Nat:=(if j<3 then (if j<1 then 0x13747209b53804dc9bb864ca24aa65151b2272ecb91186588813743e71a21f3ad28f1d6887813743829b11c2ccc0d026e860db262a09ba142cd40a022e85043702425b31112dc081c6a040b3301c5d970e30cb071965438d3281c65ba0a62d9051b6e8201374106da30838d1839765c14c32c0a69940536dd01026e809836a046da80236d1811c6a004e3460225b90038d4802966001632e00b9960062ca803365001ab2600fd748002db3d016d9b22aa6c1215227025d10002e813ffdffdffe7fefff5ff8ffbffdbfebff4ff9ffbffddfeafef7f6ffb5fd8febff4ffa5fbffd7fdffefdf7afb57cffdfddffeff77f7bf7dfaefbf7dbbe7defef5f77fbb7dd7edff6efaffd7be7ff3fb9f7bffdff6ff77f7bf7defeeff6ffaffcffe7fb3fb9fbcfbe7bf3bf9bfcbfe3fefff7febfddfeafef7f6bf75efef7d5ffaff57f6bf75f7adfd5fe7ff3fe9fbc7fe37f17f69573581655c56058d71581715c16058d70581655096058d4158142505602a5415819864530655914c192645306a5814c152605302a5814c1a824530694914c1a224530660914c19524530648914c1a46612068598480a366120661944819864d2065d934819564d2026193481986452064d9148153645202619148093645206a58448195611206a581481986052054d81480a9605206898048131601206a174481985d12065d73481935cd2061d73481985c12064d70481845c1205cd70481715c12055170481535c12054570481425c12050570481a954d2068553481a054d2065153480a954d20695434819550d2061143481a75052066141481955052065141481845052054d41481a94c52069531481a04c52065131480a94c5206a130481a54c12068930481a14c12066130481954c12064530481824c12060530481804c12054d30481524c12054530481314c1202a530480a84c12029530480984c12025530481a32612068498481a824d2069c93481a624d2069493481a124d20660934819524d2025493481a564d10689934419864d1068d9244198649106559244193649106a583440a960d106a582441956091064d82440a96091064d8044131601106a552441935491060952440a9549106a532441a54c91065532440a94c91069530441984c11060130441534c1104c530441a84811069520441a34811066120441954811064d20441854811060d20441804811054d2044152481105452044150481104c120441a8644306a5810c1a26043065d810c19660430649810c191604306859808153644206a581081a3604206618108193604206a553081a854c20685530819854c2064d53081a564c106a192041a5648106a582041a36081066182041976081065982041956081065182041936081064982041a95481068d520419754810651520419354810649520418254810 else (if j<2 then 0xaa4bd48b95e6e5caf522d57a914abd48955e28dc2e946d570a364b851b15c28dc2d946c96ca362b651b55a28d9ad146c5693b42b451b85928d9ac946c5653b42b2ed98594898ac056cd5d3262ae81815642cc2aa1655550b02aa85515544cc2a226555112a2a87d985346a8a9856e1482b6aa47d98523ecaa9266054932a2a47da85118dc281f6a140fb4aa07da84e3ed4269f69534fb50967da54b18dc241f6c91cfaa48c7db3453ed2a29f68d14fb408a7d95453ec9a29f6e9106374887dba4318dd218c6d50cf9748631b5423ed2a11f68508fb40847d534218d9209f68cfcfb407e7d933f3edd1f0c6e8f863707c7cba3e72dc9eb96a4f5cb267b29533d725c9e9f6d4ecfb50767da53b3edc9d056e4e8fb30747cb93a3edd1c8c6e8e46370727da8393edc9b856e0dc2b626e7cb93718da9b0c6c8d9eb026b495335a4989ab76e4d1bb30691d52346e5c9a116d4cdbb306615b3320adc18a76a0c4fb30629da83018da97bb660b9db705a31b82d76da96bb6a0b4fb505aeda52d3ed296bb660b5db2a5aed852d28dd16146e4b0a3745651b92b76c99555548a8a3745215ba2928dc948c6e4a4a370532d8529a4c194d56e4a1cb725155b828aad994556a0a12b505155a328aacc1439660a2ab2650e59328aac1944a54ca2bb744f5db327aed193d764c9ebb064f5cba274ed4133b66099db264c51b5254ed412bb6609692a64b55522518d9121f6c88cfb44467db9220ada912d6e8856b4442bd52203edd0f8c6e87c636a3e7da51f72d10fba69479d3443ce9521e18d98e9f6e87063743831b81c74d88e1f6cc6cfb46367d531b3edc8d056d4695b4632ad53193edd0c0c6e860636a307da5186ea98c1f6e05cfb622e7da8173ed08b9f6e458fb722a7d98154cc08a9f6e850637428ada8146ed409b76844dbb7024ddb21272da88b96cc45cb7020e5b31072d4081f6a040fb6a1e7db30f3ed2879f68c3cfb721c7d950e56d286ab68c356b4a18b5a30c5aa9862f6942d7b4616c9ba0a3edd050c6e829936614e5b20a64d2853268c29917414d1a50968d184b454c25bb741031ba086eda840c6d421bb4a10dda3086ea984396d41dcb4a0ee5a30772a9839f6cc18fb460c7db9050adc02b46a00da34606ddba023edd010c6e809936a04dda8023ed4013768c09cb7002e5a80172d180b96e401cb520095a30072c9804a54c00c1536268a9b004d9d7826cabc13755809b2a906d9d3882ce883b6d4009ba9c0cdbcb076da5813672008b98d085d41c05ce026284fe61b67a0edb3d026c5e81172f208b976045cb7822e9b4336ed861b66c0edb36026d5b0f174ced8b36754cc318b6e58a32a6c02cb95f20daaf50605789364b635b6591eda2c906cd64bb30aa6198542ed3a8186994013749e61a64f04d923022e91011748609b54204d9a1026ccf else 0xc34db2612ad930d36c5869b04c34d8161acdc30566cd82b362c1598160aca9b0564c582b170c165b85fb2d9afd96c97ecb04bf64985f50caac28545614362aca1985650caab286055942a2aca1985350c0a9bc60541e2a498f1534a78c1a4bc61521e2a48ea1534578a822bc4c115e37488f1b34478d1a23c2e911e34a86f1a14378d021bc54905434480f1833f50c19fbc4c0fde3747cf1b83e78d41f3c684f9e3407d59b93dacd99ed66c4f6b3607b59a93dacd19ed6684f6b3407b59933dac989ed64c0f6b1727af1853b50dc9d286e0e9433074f1ba3978dc1cbc6a0e543046ea1813778a91b59548d69b70694db234a6d89a53608d29b02694d8233a6a919d9614c2cb0a5b65ba2cb2dc96596ccb2cb745765b92bb2da95d9694aecb2a5765532ab2dd14a86e8a6cb7252f1b929b2dc14956e0a6cb605365a82950d414d9660a5e3305364ba29b25c94d66e0a2b36650f1522378da8fbc6e871e37038f1a81c78da8c3c69461e3022ef1ba0a78d9853c68c282b616e7d98b77cb2da3e58ed0736366f973b31cd8d943596c0fae75e7da2ab3e51559f2a6a923674e7d98a746a953856d698fb314c7d95a63ed4529f6a290fb4b487da8a33ed2d19f68a8cfb4f447da4a13ed1d09f28e846363407da7a018d8cf8c6e274fb513a7da19d18dacd8c6c66cfb4b3631b99818d9cb8c6e258636b2c7d87953edd4a0c6c650f975287da3933ec9c99f24e4d5b2724ac9392185cc8856ce40fb27207d30900ad9c7856c63c29751c30b98e18d8c62d64e2c637114b5878a18d9c4146c62063631051b88728d8c3bb6621e0aeb0e51b98682c9c2c1612160b27090584849ac241946e608a361052d548228dc40d566202aaa70051b37f9ac23fc15cdfda168fc7da97d185cbe9f2a5f46372f87da97c3e54be1f6a5ec736cf431b17a3ed4bd1f6e9e06370f031b17868cabb8c6ddd4f974ea7dba7418dc3a1f2e9d1a32ae6d1957218dcb89f6a1c1a168e07ca8703e52b81f6e5bc2b72de7da96f3ecc379f2e5bc6172de7ca96f4ed43727695ba9326dc9ca96e4e543727295b8fb50da31b86c3edab60c6d5b0fb50d87da06c3ec2b61f541b0f90ad8ecb96b4e54b5a76a1a9d972d4ed98694ed43427695a1db30d1495368aaa9343b2e5a13950d09ca56876d9b3bb6c59d3974ceecb567a459b3bb661993974cced9865a4a9b2d5549953b42c8ed986428dd31946e58deb30c6f58263a4a9b1d55498ca172c651b2627ac0b1524c58a9372c231b961a4d930d26c5869360c31d5261a45cb0b72e5869152c355ba604add30556cd809b62c155b060aad4305566181cb30c13d536094a9b0552e982a952c154a860aa4c30146e97ca372bf49b35faad92fbb6617e5b2abf5d815fa4a9afbb2e57ca172bf49b95ea4daaf116d57a934abcdd985ea4caaf516057a7)) else (if j<5 then (if j<4 then 0xd65ad969659d965658d961657d95d656d959655d955654d951653d94d652d949651d945650d94164fd93d64ed93964dd93564cd93164bd92d64ad929649d925648d921647d91d646d919645d915644d911643d90d642d909641d905640d90163fd8fd63ed8f963dd8f563cd8f163bd8ed63ad8e9639d8e5638d8e1637d8dd636d8d9635d8d5634d8d1633d8cd632d8c9631d8c5630d8c162fd8bd62ed8b962dd8b562cd8b162bd8ad62ad8a9629d8a5628d8a1627d89d626d899625d895624d891623d88d622d889621d885620d88161fd87d61ed87961dd87561cd87161bd86d61ad869619d865618d861617d85d616d859615d855614d851613d84d612d849611d845610d84160fd83d60ed83960dd83560cd83160bd82d60ad829609d825608d821607d81d606d819605d815604d811603d80d602d809601d805600d8015ffd7fd5fed7f95fdd7f55fcd7f15fbd7ed5fad7e95f9d7e55f8d7e15f7d7dd5f6d7d95f5d7d55f4d7d15f3d7cd5f2d7c95f1d7c55f0d7c15efd7bd5eed7b95edd7b55ecd7b15ebd7ad5ead7a95e9d7a55e8d7a15e7d79d5e6d7995e5d7955e4d7915e3d78d5e2d7895e1d7855e0d7815dfd77d5ded7795ddd7755dcd7715dbd76d5dad7695d9d7655d8d7615d7d75d5d6d7595d5d7555d4d7515d3d74d5d2d7495d1d7455d0d7415cfd73d5ced7395cdd7355ccd7315c7f7081bbe6d49afa6aa1a5567819a2658993764318ba61d98165f197625cc16f25abd66458cd5e9567556954994e3525544c503d3c44de932c4b792a1497922047791a5455d12643bd0b141b90404034fc43e1cf453c28ecd3a58e50384cdcc35e4d3d33d4cab31d4c342fa4baa2d90b252ba8aa32964a1f278c9ac25dc93d24188d4226486720f87ff1f007871d1c6fb1b08690195c61217705a615c452d13e44b311b443f10103b00dec3380bb02b60a1023407f81b7055c118037c0b201cc03e000143056f1142b688aa5ac450ad622e7653987b078c0d73c54ab9e2435cf181ad7890d6bc616b1e30358f150ab78d4d52854aa143654ea152a750dad32854a99e2a54af152a478c3cf3c61679e3073cf1819e78c1ce3c60671e15138f1519b78c1cd3c61665e30732a1ba9878dccc3c66261e32730f0b99850c3cabc4c651430726f15093789849bc6e646c36322a1a99178dcc7156e238ab6b1d65b08e78a8c54264e26130913094189b2cc43596e60acb6105659382b2c2415954dfe7168fca1a97d785cbe956c9f1434ef8a1a27c50d0be3c6a5ecab62f539957778c3babc2e1d2732ae539877278dcb8bc655c5e30ae0f1507078cc37a864dbd4170dea0a86fb2c2b73c6059ec970cd64a866b24c33596e98ecb72c765b563b2d9b1d96c98ecb50c765a563b2d131d96618ecb2ac7658263b254b1d92958ec92ac7658262b2c0b1594c58a9b7 else 0x180081d40d58634b5a67040841c19b03581e04120b211506f04200e00c957b18c985045203482640b149f369029d0a4a2504c70400c2024a4f302014cc5ca0d5197044c18e2170ff085841a115130190e076060439839454a2450bc23403c3137ba81b610305c38cb8c8077d1b70c780c03806603700b3428307839a44a05204260ac137c1dc056022847a09d03e0ff453c4cc02d05d85e0e060770228a3440b0a01e7830078c11801f8b9c4ba20d03a82206805cb0ad82360782c01d686002ac06d0400ed815037c1d305109180700dc0bd415a0e01c685740502bd004092043022511d82b801d0cf02b843811e0bf0be813e2001f685345cc0503500e4068c09016015a819817e0e786f804055e02700f803a0bc0f687f425a06e09f0035f9d7c75e9d7875d9d7475c9d7075b9d6c75a9d687599d647589d607579d5c7569d587559d547549d507539d4c7529d487519d447509d4074f9d3c74e9d3874d9d3474c9d3074b9d2c74a9d287475d1b7465d177423d06f413d02f403cfef3f3cfaf3e3cf6f3d3cf2f3c3ceef3b3ceaf3a3ce6f393ce2f383cdef373cdaf363cd6f353cd2f343ccef333ccaf2f6cbbb2e6cb7b2d6cb3b2c6cafb2b6cabb2a6ca7b296ca3b286c9fb276c9bb266c97b256c93b246c8fb236c8bb226c87b216c83b206c7fb1f6c7bb1e6c77b1d6c73b1c6c6fb192c62b182c5eb172c5ab162c56b152c52b142c4eb132c4ab122c46b112c42b102c3eb0f2c3ab0e2c36b0d2c32b0c2c2eb0b2c2ab0a2c26b092c22b082c1eb072c1ab062c16b052c12b042c0eb032c0ab022c06b012c02b002bfeaff2bfaafe2bf6afd2bf2afc2beeafb2beaafa2be6af92be2af82bdeaf72bdaaf62bd6af52bd2af42bceaf32bcaaf22bc6af12bc2af02bbeaef2bbaaee2bb6aed2bb2aec2baeaeb2baaaea2ba6ae92ba2ae82b9eae72b9aae62b96ae52b92add0b722dc0b6e2db0b6a2da0b662d90b622d80b5e2d70b5a2d60b562d50b522d40b4e2d30b4a2d20b462d10b422d00b3e2cf0b3a2ce0b362cd0b322cc0b2e2cb0b2a2ca0b262c90b222c80b1e2c70b1a2c60b162c50b122c40b0e2c30b0a2c20b062c10b022c00afe2bf0afa2be0af62bd0af22bc0aee2bb0aea2ba0ae62b90ae22b80ade2b70ada2b60ad62b50ad22b40ace2adbab4eacbab0eabbaacea79a9c6a69a986a59a946a49a906a39a8c6a29a886a19a846a09a8069f9a7c69e9a7869d9a7469c9a7069b9a6c69a9a686999a646989a606979a5c6969a586959a546949a506939a4c6929a486919a446909a4068f9a3c68e9a3868d9a3468c9a3068b9a2c68a9a286899a246889a206879a1c6869a186859a0aa7d99dfe7779dbe7679d7e7579d3e7479cfe7379cbe6f49bb26e49b726d49b326c49af26b49ab26a49a726949a3268499f267499b26649972654985a60e96) else (if j<6 then 0x99f821d9fa046c0068900008fcdf90b0602589153f02bb02c8617f96ae0f011c7b104702ad1020a18d6a29ffb4c883c046c0478a0fe1c136f683104a3543c2067c18404e219ffc9901060c2041c4a3f060df84b40800913effa61909c80c200bc50016ffdf823830806f1415fc2b51620536917e6fcfa24c202710005fae490101653835f3039ffa623d10027a64e8100587f7c0001bf97a610096280803ffe046cd27801594688e9800bc12344c025a70035f00baa097bb115e627be14b30baac6501e086f7c9c0c978000809c48bf87db188105a1c00d7fe3d42041588279c33ac4082f10017370d02041688020fe16008094c01ff690ee3200813563fc9c2888105a1c1cfffb96304081244821f37c5010488810958beffe6851900456837fdd6038708100389000000005f053fcca241eff66f38548608f82619e61e9b34d3f468e00a16d14428ae783ca0cd2d09d11cf073140cb30f3444fbf988157c0e7088e78382af81cd10fcf06300a616c8462279f8c02ab44321e128a073f1b3ef01aa1c801bf837e43a9a00006b885fad43c181c54bbeae9adfc18bbae09a8742ffec130946ce11fb0d0251b387c2bf61a049c6813d6aabf2d1200dbb91b3491fd32d517589d5a71fe4cac2f185e4457f2cb5dd6299a113fe8099798819a400f921e6244eb08162b7f8bac85e4ce9257f7733b3414eff17590bc99d279f8f2694e4404ad12cfeaf2d00c2c36f1cae8d240c933f75d86220849afff812050022106a3ee5f330a102ab7fc5a0718020822275f8f1715000420889b87e3c2820a73e1882501103b4817ffff0ae06c501103b66ffec2284941273d3fb3025011483513fd3808604002144c503ffba2003190d3f1c485a4324025eae9c044400213ac58dff1301c4b0922ff7602184e2096224000000003fc3bfb7970009bc00f100de0ef0b440057f0e847175a21f80c20150a6fcda028881042200017fa6db970c2fcdf310000c3c448c81c409a69484f414b8aac4a603a432c6c61d31c986324511e929346509a8162060870607c0d606116c88191348da45d25a909492816c1520a8053c2d401ae1d689b46614b0a5052791a0e8007aa58c30af0e0582ec28c0a2084c80652a14d94b58dacb562db35da16c2461a0671b0e89d84d36a9bf42260b500b04481c7a9396b589609b633d278c282c205d011da4c6020b0d22ea1cc6c84ed1ee80c2e0156d57ca874a760fb13592a9840df0b9051014082ab5720b099615908f886817472b37c0248e58e0f41185794e66ed074e3042ea114e04846f0200ca06380630cb00d83a917884690c951120d8778a366ab2282d943be11b08f019442623d06287ec220aff079880c6d08e12df05e0dd07090b022d01ed07c32d8ca8b740b90a806a0c4522a80d50e614316a8f409c14304740061670a30a8855 else 0x8df904283c4000000abf939119a6629800000000000000000000000000000000000000000000000000000000000000cffd08b59234a000000000000000000000000000000000000000000000000000000000000000000000000000001dbcb1665b880000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffe4d7eff252488000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000029fff80d9e40694eb01163000000000001e0f0a08946a87000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000057fe4c20470a01d7e3fc33449620026c0031ffabfc400746100822c00000000000000000003b8ff24eac40ab400000000000000000000000000000000000000003bfec8060c202710000013fffebe900c1840028b000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005be029164d068632a00000000013ff57fb60290460000f7fc0005393f0060c531a00000000010ff829f9e6940c91e00000affd3830a8b668d160013ffa603601cfa2b4500000055f9008296054aa000000001efffc852172c4b0093c8a5fdcf09c154574e009e17c019806b4f6396bc0371057195306620000023ffd96277022b14071f281c06400675000000047f01bcdb72b010f1a000bf829f1b7930049140000000025ff07be19040c31cf7d48d568e52cbff6a6a23bc650e0033db84bab0022240067e0fd7882c022c4c7edc0c302d9)))
def B0 (j:Nat):Nat:=(if j<1 then 0x1caa00019150000000000000000000000000000000084ae2cf80b68a0000000000060accd2000100f800000000000000000000241400060be000609e00000000000000000000000000000000000000214a00044940000000000607603580000000000000641200040660000000000615c00000000000000000000123d000041b80010210000000000000061060000000000000000000000000000000000000001680578000000000083f0000000000120260500000000000000000000000000000000000000000000000097022a4a602d000000040b80448000000214000020e40000001841000000000000000001834800001680000000000000000101e000000000018068001b2ea15a0000001056000022e00000000000000000000000008178000000200400000000120eb782f26a2000000000000008388000000000000000000520001a398000150813800000a800040f60000000000000000000000000000000000000000000000000d508034000000000000010c1800000000010250eb8000000000062cc0000000000494000000000000000000000000000000000000000000094fc12200000900000001a3be03c000000000020298330000000000100940018230000000000000000000004162000000000000000000000000000080380004ad80000000000000000000060f2000000180892b40000000000204a00020d80000000000407400280000000000000000000000001038000848000025581660002143009a0a000000003ac8000000000000000000000000000000000032b800000000000000000000085900d00000c0800c00da0000000cd68001846c01c81c800200000000000000000000000000000004f5c00000000000000000000000000000000000000000000000000000000000013181b800103eeebc8238000000000000060ae0000000000000000000ea00000b7019000000048b600000000000000000000000000000000000000000000000000000000000614400041460000000000000000000000000000000207e000000000060700000000000000000000000000000000000104300000000000000000000060bb829331aa56800000000000000000000000000000000003094000000000000000000001843800023c00000000000000000000000000000000000000000040aa00000000000000000000000060438110000000011c0004010000095e00000f800000000000000000000080a80000000000000000085860a20000000000402e000000000000000000000000000101a00008058000baa60ee000000000000000000000822000000000000000000000006c000626200000000000000000000002c8000a46a06284f80008498000000000000000440182400c12288180091c125021a08803120000b00a200 else 0x401f853000084d8000000604c0000000000000000000f0000000000000018268434000000008160060000001840000000000000000000000205400000000000000000000000000000000000000245200060400000056811800131200000050000000094e0000000000000104b603600000000000000000000004c80000004f49847c108000000000000000000008000000000000000000000031204e000000000000000002058000000000041020000000000000084b800000000000000c6e030c1560000000000000000ec0de00028a800000018b080000538001bd40000000000000000000000000000000000000000000000000000000000000000000000213400040e600000000000000000000000000008458000916000000000000000000000000000000fe0000000000000000e00000000000000000000000000000000000000000000000000000224000080c8000000000102c00000000000000000000061100000001998800000000012520000398800000000000000000000000081e800010e84320000000000000000020c000022f800000000000000000000000000000000000000000000000000000000000209c0000000000000000020dc0000000115800083b0000000000110a80000000000000000000000000000000814800000060c6000000000000015ad000000000ce000607c0000000000205c00000000000000000000000000000000000000024d84a015400000000000000000000115020e800041520000001a30206a0000000000409800000000004018000000015100c800040d4000000000000000002f5a832a11584f0020144e2c890dce95042a0800b2e124020a69f004ec040000000000000185ae0920000000000000100300009be800000064380000f4a000000000000008298000854000104ee0e0000000022200f400000000000000000000000000000000000021800000000000006061046000)
def BV (j:Nat):Nat:=(if j<3 then (if j<1 then 0xd308fe9547f4cc3da54ded352ee9a1774d03ba651dd2e8ee8a9774cc39a655cd330de9956f4c3b7a5cdbd2a6de9a96b4d2b5a681ad32ad69946b4aa35a2a5ad14ad68956b4d2b3a6859d330ce995674c133a6059d2a6ce95267498b3a6617d32abe9a85b4d2ada6896d330b69a8574d2aba68d5d330ae995574c9aba60d5d352a69a94f4d2a7a68d3d3429e9a04f4caa7a64d3d2a69e8a94f4d125a64d2d2a6969524b498a5a6a51d3468e9a0474c9a3a60d1d34486993434c121a6a4fd34a7e9953f4c29fa694ed330769823b4c09da548ed3506e9a5374cc1ba64cdd2a66e9a22b4a915a68c6d2a6369a8174d08ba6941d3460e953074d180369706b317c187be4b2df258ef82e374963ba4b2d9258eb9a855b598a9acad4d64aa6b5348da8a06d2d0368a86b3143595a1ac950d69276b433b4a39dacc4cd66256b2f2b59595a4c4ad66246b272349891a49c836a636b2b1b5a9886d4c4e6622195310da2846d440d66201b52fc1977dac9bf061df82e8fe59879acc3d964decb08f41737a0b8bd9551ecaa6f65517b2a0bcd6a5d6952e8da571acc38d655c9b08e0da76dacc36d655b9b28dcd846dad4b43695acb40d359469a54b596a19cb4ace5a2672d0b3966196b30ce595672c8b396099cb02ce58066aa9b375499caa2cd53167254b392a19c94ace4986724ab2368d81b42c0da85c6d2ae368576b30bb5955da4aaed6a166b4ab35a259acc2cd6a156b46ab59855acaaad64d56b52a35a94c6d4a6d65536b269b4a94dac9a4d6a511b528b59346ec122d6a4f1b4a7b5953c6d29cd660ecb00755533aa989d96a0d1b506e5a5346d29b968cdcb306b598372ca9b964cd6b266e585372c19b9600dcaa66dd52372a81b94c0d6b505b5a9286d114d648a6b424b5a521ad40ed54c76b5230da319ac98cd6a451b5028da115acc0ad69436b50135a509ad482368c16b2a0b59305ad480368c06b2605d82000d4e0565ef8b09681a9b22b25602a6b0153481a98c054c406a610352f95977debabcf5d1e7ae6f3d717aca13c02a5d4328d80a9698cc33454d9b2a4cd131642d3ae269970352a00a9500d4a602a530152881a93c0549ec64cdb2a46e15134cd11806a4a2b2e51996296c89406a462330301a9152c98a568c44b4a1a9a8094d28406a4123300959704ccb027654143280a593054c90206a402b2e02194012c980a6480fffffeffcffbffaff7ff6feffbffaff7ff7eeffdffdfedfddfbdf7defddfdbfd7fcffbffbbfb7f9ff5cd605c5605c160591605096050560645306053024530661206512064d20645206112060520601205d1205cd205c12054d2050d20505204c5204c1202612024d2064d106491060d10609106011054910541104c9104c110481106583064430604306602064c20644206042054c2065c1064c10648106081054810 else (if j<2 then 0x1d02328b823c5cc4281508341160905ea25246a45614632208c4b43008f817409c09a2d21924f069c18a1f049044a2605882b80aa07a09a2ec0b83b21a059c31c2f039c06c0dc1703e40a05d80841541604340842802c40180c034e2003881e40e037c1d410c2182780ee1bc1ca2980581640ca12a19811a14c08a0b60f405c13c0a60702ac10a0680d024801c02c01c03c04c00ad375a4eb45d683acf759ceb35d663acb7594eb25d643ac7758ceb15d623ac37584eadf55b6ab5d569aacf5596ab1d561aabf5576aadd559aaaf5556aa9d551aa9f5536aa5d549aa8f5516aa1d5316a5ed4b5a95b5296a4ed495a91b50eea19d42ba847506e9c65384a6f94dd29b65364a6b94bbe941522aa35d44ca862508da10b41f683ad06da0cb41767e5cfc39f013de27b84f689ec13d627a84f489e813ce27984f289e413c62750ce999d233a26740ce799ce339a6730ce599ca33926720ce399c6338a6710ce199c233826700cdf99be337a66f0cdd99ba337266e0cdb99a7734ce695cd239a37344e685cd0399f733ce675cce399b7334e665ccc3997732ce655cca39937324e60ecc15981b30165fecbf597db2f965eecbd5979b2cfe5684a2d93692472433c7b08e011aa230cc5bd8ac313c624c444e87f50ec21b3c3148571090e0f0c18a82670322026bffa7f6afda9f91bee67d50f8c9ee4bd7f7a78f40de62bc627814ef15dab3af57516e89dcee397c7258e309c15b7af6ea6db1db2db5e96a96d37da47b4326794cda198332a86478c7158b7b10f6172c1b98132fb35eb8bc2d762ae6f5c56b7616bc2d2d59beb1e560f2baf56baabe1557aa6253eaa6dd4b6291c518ca17d40e27b24e909be136326764c7897f92dea5724a6893fd266249948da90ed1f8a3a746d28c5115f22744468879d0cea14041f482a50269feb3f387ce4f641e633bd076d4ebf9d533a0e7354e511c63386e7014dde1b65361c6a88d389a1f3370659cc8c98d1311460c8bee97962e965bb0b5696582bee56d0ab8952f29ae5224a2513fe27904de898d92e3252e49248f511942288442084e104820183e4c7a20ed71d0438dc6ec8d8e1a5433446378c1316fa2c405670a84148a28004df899b1266239444d086310641fec3e1077a0e7a1c4036786a80cd418882e4059a0aa4143c2660491089c106c1e9038e06a60c74173829304ba08240e7019b029804400678094007800034d4e1a6970d3097e942bf4c3d9a5cebd351569a5ab4d155a662ad32b56992ab45455a296ad145569a9a74d053a64a9d2a54e8a9a744953a6927d3473e9a19f451cfa6626d3512e9a7974d2cba6865d3312e997974cacba61e5d1512e8a59744c4ba6a24d34726998934c9c9a54e4d3311e9878f4d4c5a68e2d341169988b4c9c5a54e2d127169a2874d0c3a60a1d2630e998834cc3fa64df else 0x27f317c0c4100a442dfdd0d2280dffe2d584088135eea4016470197f03001883e0a6f524fffd90cf1020080a279f64531004b43eff3ea88241239fce441004b4381fef4880021698dffbb4208820080a249ffab1104012d0f3fc4820a24817ffd21801004fc45f99988227038005ed9d96b29c1eab0e002db6650e280007be0e717b2cf593518b440cf5932e141eab0e000e36650e2b3f9dbe68466caa3567f3b7cd08cd9456a260d10536fcd30e0d1053eece77212279e0b5bbac5431bff5a3f700656986241ffe1c220195a3a22bf1f1c81aab8b42c42c7b42eac92b10b1ed0bab2493f07bff76804a16e3a452c42c7b42eac926ff1fffc04a067034ad159f0050b705619a442f4744983a4bdff48802418e01a45a9133ef1a3217404a03aff302b8639553b4332d85a150869b7fffc0ce6940c301a3a8b133ae7a3217044a87027043823842cc0f16d17c16fc20a201768b04f04ac14517433cacfc8606810b33a181c7c1554b348c5420d845b0a42ef2872644a446c4a948647242147d4a813eaef0b28c488c49c47b1370ffa8513686daeb90b22e25a28508c06d07fc7b218c1a0adab1a96aab65a66b6850b917717f68964667e62963d61946011c6d367369715717941a11fad621b1671662c344d16533820330a6bc160a4f17e33b0cb30169333917a1784201718f520b2af17d8828fa3320df3314c217b0de18011616e2514526ae03b6a26f86d210d20a2d32900a000da7311446111b87510690590686504808a00852885455856bc48c5114844284c182c2b4b715dc05c0e93485b80087b82126b8042eba9d08d69dc8d16911311272d27e62e04e1091470200111642d51532fd4d045c10c8b316344843b4404658cb6202fc8a4c7247c4624310c644bc6c2452228aa41f8944686180c8a9511e46e8801202da61b0e81212812c03020e111911811daaf2a1aa1abc2360b041b0cd64a2fb0c9a1b81a82c4f44f30e941d8091174f18400400650542a283f11143f0e244c0dd110c15c47c63c62c7d22d0b8a7aa6b0e3aae01b10f4806c31000800c40918c10ca8514948a3c1e42f82f46d0b70a7a88c5f45f46343ac5b2962ab2012952b181d84d0ce60243c4352882d78660b4a930e703040760b8184d149f86e83c49e0278480e502b0b5441c220790e405506a267a670b6a4a06606e25324a4660188ac0c7075081841a22c1f0a5400209a8909aa7e2c50822ad4a00ba22540da188610a6c3a0bb23d060a8709b22600700f01a09081087f08e427c2342241c20661a84ea3244ec0701600c00500e830c1107605607120209923282262663604d625074098a1a297061423c64c41842417077a0f084860a0206f40f078847212a33a5a62d03c035273052070451c4cc3fa5083541805720f092207a36a46229250a53633612a3da030098280)) else (if j<4 then 0x7219fe1f007f080bb477f7fde5f082840286acbd5dce06080e38068a9006ff8ec55d8e204021aa81efe4f03bea90c0cd1e4049c685f80139fd76148a7a7fff240b56da0601f752017238dfd5ff86e9594189335c80bc8e43fc1ab202c9804071a9ead39ed40d59e2f47c49415555401cea5193f01ac183187dff14f3f1208092b7be9789ea9044e96efe1f0d210420080a2b7fc53cfc482024abff7ef01110155f9fe6022022adff500104a0937e660444a527fff30111294abfe3f6b788100405129ffff56bcf410103356feff3ea090440954f87bffa935220802108b47fdffd328c88820089e2c001ee87f43080085a8dec79627c482a24c164fee37c4384010b4507ffeff3100440442d4f71bcaf3069881020022aabf51fd20f30200822248fd6dbea084040045153efff37fbfe7510410054317afe9e847ffc10941040115c617ffefc7483a2202026bc7ffffe410a046882100405180f7ecf378048fba414310802248ff7fff1f1ee43848b384011446821f829e087ae9fb024041220084991dff50010446927fe7ef01111955f99811099497ffa364400010109b61fffcc0444653bfea00208152771f15d4004110265f9981112949fffcc0444a535ffb2742000202526b4bffbc134904004004475487ff292b8208008008e6a814f07800057fc42000020088e3ef8ff9c4446525fffff42364601010bb6025e2f0005fe4a00000802378e00affff3a100010111b673a3c13cd4c370633115deb0f5805b76e686d4025fc8b72f56e49aa1deafeb30e01465b66522309ffb43533e404641b2117e7f0a0449742b0caa15f97b435738a06b3c4c3f97a3f550879f0520d608ccfe7e6f346264ad277382cafdd484832427aa77eef02bfc9dc6410c6e2dc67054414dbb9dc83893391e8905567e695087245d4d45df99d401de8fa8749bb59cee42c613fa93ad1f209128b11404dff010629a369dde8f93f88806568622660858f617754963e4d64b5d27aa68dea5dff2d5fc7f012819c0d43460f10b1f449b02483fe0671172180d20454bff35e2570dd3b41314affff1f03058d2b4c0685a3002ffe7eff12ada1da688a01116fcdf9099c6d458a5bd8f7d6292e9a6000000000037e6fc7cd93cb508e37bb4626830e7f08d678b33e17a1ce6948a637e4f050dc70030c1aa759011a26c8d27afcbd020113e9266b6ffaf00f6c32f66afd20ca005b800009d0dee164e4c901ea89fe6fa7a84184001c4811fe36d9e51b89009016b1baffe546200af20212240aff5f013a6036d2e32024a37dfc0e8093652d81900e518015ebfe014b403b43da001b7eb8018fe14c42e342901946857ff847ff0f000cc00b0000e877f6c20026ee0023ffc44007bcc5e835520328f0be078358f2008a9f9f003f4e3671001889b7ece800904007100ff2cce0620802489 else (if j<5 then 0xe20022f3725ec44a491013ff8000020df1000ae2013e6d025ec44e59500006ffe00005aa749ad2c1e1495ce0858006db409c4e00000000000016ffc0001be28725d2f07a5c0aeb42519c000000000cffe9c10821e9a6a002ad9cae43c426539bdbe77b330a506c67aa42aa0000000008fffeead9ed349b273335010729cffa33ca2e6212ca07cc519cffa73c1c86212ca46cc7198ffffc5f0fb218842098c9acf51d27ff8189810c10140136aa00000b7d5fb29d102264fe00000017e62950c2a4000025f77eca744089dbf4f499e7314a9e54025f669c3fa8c4a74248a034fcbf36fb94308a5484ab000024fe47c2a90e9951060805157d9e241f0a5a3594760e00135937f97b380a534304024aab1fca4dccb24221840594628df013fcb2e529015338808c8f000000015ff27d5f67e836971013120afabdb420d64ce2026a2dcfa0ccafbd880274fd849b39ff1daa01d5ac936efc563b5404bb59adb6578a0000718024fb44580019c687e9fa452105b8c804de270807964414fffe53766eecef60e100711ba7fe909d46191012d4161fc553d9180046a6fc2bc7230173449ff0675d992274d0f9199be9e008340c4202523a5ffba91488c9c9a29a8a2d0f014fe8e7183334e0fffe68fc550aded0120120316381fcf1db20852d2d81901a51c000000c7fad825319100804c56957ce7f00a5a01da1ef2002380006ffcdb100c80328906bf0f164b89ef744280a88d0fd3a7ff00122440596b57f8b92782b95f8420ce2027a3d9ff0ffc410000c800280000781ef641000acb33fd5fc7c35654b0354b31462401248e3ff7370e551c6c189009c68008ffc6bedeb103120009013ee090008ca2be0b6001bd802837712a4004478000b7fff8035053055f8d500b71e003bff1e4c78f0201320012005196cdb3812acc0016fe087bf2eec13f1e6403cc771e4f38d02c647c02bd483dfc1e00640d5c582015e331fc80fffa45b3b590582025e340017c1cdea8b67707080658d03ae376c62ba11115c4019eb3adfd376c934e0bb7d80b36ed7f07dd77d00ab36bea2100d28e05bffc001228ecddd9c0e49201d1214f039a593189f3680414602da3a7a59333e6954800a4683de0fa1936dcfe20009179fa53a36be41600d9adeffd6f22e9c2007aa0000029fc1af03be4f30b2cd05d4780065d085f690cc98007aa97ffcc2ceca818e01a450bf0b3b2a8238069131ffffccefcd58327022b6774c74dd8327023b5cbff91aa80c012080378b87ff77f1120181812080038d2ffbf8cadd709c068d55fdffead81832703cb5e3fdbc12ffdf6e954241006d1b9763e34be80b8030e00eaac02ff87901e00001ff7088401247175cb8e0a0c19d0806edce07fff571047180c720809d8e67ffa044aa08e0324487e5f28640018f82a5ac14f03b013dfd43c954241000 else 0x61ffafe309544aa400000000000000000000000000000000000000000003ba27dcbf2c2100ecd4000000000000006fff79d6f98b308010458000000000dfffc9278bff8248110248018d0500699300000000000047f18006f655b6d759388e07d483aef17f42580a3c86041d200823c1e0e02a76ec09254829233dffffb7aaca4b0328e0d39c42001e411ffffc50979cea0c08e1ccc4202d643de2843078e0a644021196406f9093b6c96570590e00000000000000005ffe0355a7e307eab1f1a1004200134a001bffedab106a0068800000000000000000000000000effff3e39c0fcee1378089150112e400000000000000000000000000000000000000000000000000000000000023fff8386267fe8f101204a0105c80000000000000000000000000000000000000000001bffb75fe32842460c00004010912200000000000000000000000000001dffc5efed5880efde6f800a5c98000147fcc0c2040c696a2e8a3ae013ff814007a582d35a583c217b36001c69040d30000010f880c)))
def B1 (j:Nat):Nat:=(if j<2 then (if j<1 then 0x4cc2da88830172831e002d02b281d3822485b0ad35c11a443bc1bfc2fa80de2ec2c2c98298826ceabb815c024ccc4e88e80d2582b9083602635225c116851d01b41c4d0577c05ec2a199d0014381e95c4fddfa8176a608831c82f8057841ff805a0122429d08f00160c2c0400bc4e390f742ef8016c1860729c19dc01ac0ce801800a0c266810c8333914e99fac03e42b61da642e1c86a992e402ec11fd1af413ec2c6c86f00f4031f412f429300000000821d001c826f0000d9e881ac10ee8d94c934a9030000000000008076000042c39e690000c09842614180d1ff0000000049940000ae81df0601e600004232000081a9c2010950821300ae424e919741bc1170000081ad902bc274c30142f409f00000c147020e2532813a0000010e91a48316000059dd403b81a1c1dd40f01804d1f0ae9592160d93c107018a81c8009dc03100004abb0090504ec50b4008c59b9db9812e0b25086c1a1a00051a5d5048000000ebc17321e8850140ed9f2b8525c0d1c899904a4d0981a6806841460000c26742f240d400008086051511710841915300000000c1a59c3300000325000000110000c2dfea0caaea66c142f642530000000042ee84fc893b00b3408ec1330000c896428801528ebbd0ea000000006e1300005172cd372226401400001038494825f800000000492504e1000042e0000000004538461b0300c0f71918031500b601de02cd52e4414e5f0f00c341054132c1b2d0605cd784d3c280d9300230803801c91e4a00000000015400c8000002dba305921f017f0a00405282d5d0500000ae8c9100c11182e2000002fd0037c2fe480dc135000000d808fd130b0000c81ecde3c007d02d826800008089804f00004637427d00a7c318c16781af000000000000c0e0019a863a42dec0bbc144c24f405b00004907526d52c3823c2e0609002302010a881c054a2502014110031026012e0b453e277704033e0011803e0700020910004f1c273a16170f6b0100090104001d1b0b0c122305130020012e1b0812000a1001035c4d0d070e0013043b032e1e200739100200000800051a3147000e0b2501000101020105000803112300100a02052202100217241a0f00090918000102004600001808186a056e353a250c1522074300030014031412190200280005101708000f080220001e43090a1e0e1a090a0f1006013f0601000b10390e3f00091e06190102061303002307000507002a0f09000b03010a1d0b0d60090004090520300e1e170c670409030b141707030b01261c000d2a061103310507020504101a0d0f040300380b010d02061318130103040505050e18050300170a00190806130d0829041a4e01010009063e0219220038001e0b03002d010515022001010500010400240302110500010c000702021d13000a051503021606 else 0x2cc126000002144071016c400ec00681484271102c125f828a82e68e054206c01580e3a250c312c27a8211088c00000000d83ac191dd0292ca4187e6c69985c32cc292972599389ef19c5c61e2000080f8c2a9846642eb0000a8fb023610f4486e827fc222000081f7d1bc1e7f8681ca020000c2c1427840b881c69980818b85ac41b3c1fb0f311e494219010d91914083810411b18294d042000000001839822100f5032640652d3c55041f26404a0de49223d98742ca000000c60000000092604ac20000a9441da76e4d00009986126c88975e6d000080e8000081ee00000000000000009efcc2814209480c411900006437426bef30000000000000c2d482570000000010f5d220000024ec1e7b42cba1e581cf0000c171c1f16e940000c192c25c8225c18d00000000c269584c0054830b000001490000830449b0c2834d284072405602d96d45e1d92d4d002741258323d5050073418f01c3c311c1fe80e202628168e10ba662000082e55a8140ee0000c03dca0102318d3bc1b8dd8dd2c200e982169ecb923901d622c28151000042aa4075294c02f0c60a0000c19f01f90725c2d682aec0db9f0e82b8c25b01c7813dd30f41e50000c1ed91a9c02a0000091395b08123c6094a9f0000000000000010000010cdc1cc00008cfc000005ae113b5928c0ecc1415ac2815390f626f300da48fc919d0000000080cc018907050000016f10c0ed339e7dc20a000000000000920901c00000000009270000429bca26401385c081ca50c700000000000082b700000000404100000000000051eb00002ac282ac0303000082720000c0340000c23400008ae3c04702730242000000d38917011852c8acf39ec6dec98170523a51b4030640fc83070000c1b041900000000042d7c85f0000429c998800000000000080b0424b0000024dda7a00000000809fc0ddc30800004a9c4202031452c481f0028b80b7e2a00000c0794208006cd16e9b05c1360000809201d5000029455e62e6c200006d2f41b6531712810000dd7b0000df1200001db0402200008d1c1ec8c10f1f08419c80e4000080590000009a40330000000000005ef60000814fdd7a813f82ea832702f30a855ef00000954bc30dc4e2407e828541a351a882e48036c06100000000000002ecc1280000e669c17b9da10000c09b021fc91bc032c1888243083c030c02a300008195416ad2c5c1fcd6a0a665032e49100000401f6dfa099201da00002f2e410900000000c2569d1a422d82b1c12d41210000021b00004181c30e00004094491a0137c1abc082d22251a00a4a0254c0b4027b021744d640f6c91ce85000b24d92dda98028c060c302d0bec28caebbc11d624a82a02d34008b00000320029e81650159c15f42a81b27c2b4c1d7844b41124062eaa5c24783175c35018c28ed6affc1) else (if j<3 then 0x40d2024985a1e2a148ea000081010023000041d8000001ce010000000000c3210000a6810000431d000082be020f5063a470000051991e08c26e0a6a40f342a681e340b5005f0265dcff41a7454b41e4c25f02288070881002ed4296c8148e48010643316d9bc14b4332889080fa80660134411c0244c8ecc27c44e002e7de7e80f282b3da7958cec83bc00a4cf7c0b152bb415bdacc00000000c087d97f803a11ae000000000000000059e2000066f0c2dd000011f9000002d80045000000fd80dfc01d80e700009ec2dc315d22d4fbe9b5c1b7000080cb99e50000014a0000088542904919d9dc02ff40bf0237022680968003ddc681db01a400000124403f0000402540bc0329400900000000018380350000c0c180fb00000000000010c80000c17e0000644fc0c081e8992fc06d00008019c1ef000081a201970000c0cd4812d50681df81bd513c829a817901b5401b486d00001d1800009d1c8115008000000000c83700000dfa822e82c7d19bd1a501c200005315000086e581f2819e000049b5e95100004309000c00005eca00000000c5c780cae94d11760000812a80a5820b832b8002c2230000c026c92919d81e6300e61d7cc1f8c8792117008101ecc88942339114ed2d01a80461c21e423e8064c20500001dcc8313402f000042c512f089440088800d0000a902022bc21cdae5821000004284000099a102158299000000000000000000e10000000081aa00000000000040f9cd3c00000030c2f5cd8bc039416b00002e911afe009e190b5de300914e81017c82c242cf00008c3b02480097c451521d431a82708204116bc16411be8220422c804349909ef95236c1eb828704e4425980c545ca0000422ac00f1e6500000000c255ddf8451f84679d88ca81464f807a02cc853702dc5681c32ac2f11dc300ea0000402b00000000000041a000005f0700001231423d91b3e1dd80c4420c000082290000e138c1829196c2ce4663c2bc000001c400006e8dd319d2265036c218030f8aa68108c1408156d3098142a66dd2bf01e2c0a882b58166c1174150c1ae1d51c139051b1dfe424a457902951d1b00000000413180d980d749e400f1828fc5c2c10a4103893cc94a815e4085521e01d98d29806f00004816432d80c745ccc8844069c264c10202bb41d0104dc238000002fb1ec1c90848e90000031b026d990c808a425a614500004638c68300460000c1750000019900008162e18600004004487c000042910000000040530c02c1f6e6cb40a90d8f11b90000c80ac5099f11472a817dc07712c60260c02980b940930057c80f4a4bc11e01fa5989c5864938e663c80b4130c15a422f00cfc08c0000c03cc196518cc04c827e40abc02442768a5596c2c2770000029f1aa046c240bdc12700000000420351c002a240fe8811c08f89 else 0x11a100afc23a000082ab9a1be29f0169621b4145428602d200000000821200a4d856c0ba12630000000000be426ac32f0000917481f401cb42af806a00000000000042fc0000e03901dc22e212e902ad40dc561b105f86e0ee930000c1140000881d025d41e181fd01bb81f3000040ad59d7829740c2d2f110ec46cd8ec205f30000c528000000001efa65fa428901130000020d516c91ba5e0700004310d1f8d8540809523880d00000c15d00000000e666ee909cd240a60048000059834178006302a48058c04dc2c8d18311925224000048399325ddc94319c1579da3de814044018ed30ac049023b407dde7c0000992742d0c30a0000c06bd2bd417a92c00000425e00000000408d81850000823f00005cd48240e990c07fc1b9c0ac81e0df1005fa000040d541c541bed97e00008817c2ba891d0406009c8818e1e6819840504055880e80a3819ba2814227016d0000aa2611fa00004279aa4a416e0000000024ff000080e5c252000090f38db045ad624906cc41d20158000002c4419300008095000010370000001ec20029b685c8d19e823542bfa1845262493a00000000c12bed4cdef28250c2821d25404b5ef348f7025841775ec7051742a7451e813b813802468239c11b1233e04c10f082a5092b866ee51a6e8f10495cdbc1b1d22dc021d98450f225a141948275c2f982e900748110c12990c30000c06702e381554120c099000049490084c91f421a41e7c12cdde940c94d8d82e84078d84d402083229e66024151c541741e2ec0ff82d1d9d5006e00002a810012818483300000926aed2ec52095ad014de6fcd2fc4c610f25807c00a29230000081c182b00a6340d681cd40a141f541ba0000d1ab0000c20700001234eec7c245000002d30000ae8800008328d86082f71eef000000000000c07b00000000c28d000042bdc1d1864800005da8000080aac02c9cdcdee4800101d4c10bc1ea000000004947805c000086a012f7000081612dbe83248042887300ef80400000428e904f192c004e005dc1634251000000008702c0515c34413c455a8305001700))
def BW (j:Nat):Nat:=(if j<1 then 0x99ff8fe7880a0e00018eec0cbbe6603945800007e0761dd4180851602fac46c0a44f8e2d41b00a483df013c0af006010662c3e1f5a5adc83308350ff9f0b1f8d1000804bea0ce0e7e965500318662b3feffe92f8480004004badc007bff2b4900108c51165e1ffe7881054a5d7ff1cdf102095cb80000392ada6fa910000bc82e3a85d04e2400f00b0c2007190c4805fa49a23320605120073c12905ef828ac56787c001b824009295d200ea1b900000000000bfc00001bfcf3d7bc035b9ffffe000000005e1557d71a0060baa96800000000005fe00000dfe79ebde01ad80000000000007dbfb7fc09be1bbc06a3301887aff5a413aa80182181f5bc0004e06d602c2e6fc00d5377af1541e980d4400beb11b02913e38b506c02933e38b11b1a91045f04f5b40b10536d91f0ca7cc0aa980a51b1be194f981553014a36027f3506f64d602936cefff8f4800562012a358f5fe00e16604a8960001f002f846b5b40b104d538817c33f00fde620122b6463d241140243691ff98016604a894bfc01c2cc09512a54cbf97d2a0a094017036840b2314912c998a52d0588978ff26a4b8b987052c80555a9503aac41505255cb5841a874c884d01aaf5423d549abc16101c86a0a5a6a8939a8b410a5c608ca0ea2785a8ac20b17211c5186110a20c2881810817c1685e05d0f93f1fc0981982e0241e81680b9f33de610f29dc3e8078180384c09312425449c92acf9391ec6348d05886104c1a580a21190610202cc6c06c1522703e01f0be218390be0fa1885f8a80962345a01a14613020c4c07e144550d41a02523e08e8c696a05c0610103c1b890015016070d98fb21a392bd50a99d4e85b0620e8318000081ec10a894fc940370230c10621f82203c11e3241c105026360b24f49ae312460cc1381407f83d05e2fa2282a2303442282294d0d4080ca22a2da3640507c1e22949f86e0ec0d01108436a2e40e1341aa4540c82c0683b05704e18a0fc409291e801874866080300901500a81142489919a2d81410013a1444b00e0100e02d00602005019002b9f587a75d14a771327944c7ee36f15b88843861230628143f19eecf1974f3891b34d6167d31dd858bf65d2ad4d64aaf155029654069b84ada42d19688c425a010f7a7773969b04c845bc29e937094444c1f90ed470e3531918b5c5182410fb06a42ce10105881d80760009663cb2fe584f2b9f95c7cae1e542f2a0f9646cb036491b2cc496524b27259192c2496064b01257492b9c95c24aa7254392a0c94c64a6124989249c964dcb24e58372c139601caa4e5507299394c1ca40e58152c09954ccb0425520acbf6597b2c9d963eea0e56622b29217090984564dab24e1206ac8a5660ab2655912ac9856480b2c819704ca0364c23243ffffefdfefeffdfbbef7bedfd7f581404c1204403008010 else 0x25fe2067259934a6b1ccffb7406a1e14a4f13bfffff9ff85c09f851030b02684d0060b0726ba37ffffc2fbf9c6df106850640b0b901f81125d004fffffa81fe04c2cc7da27100b9c86f8d6574003ff64f4a800270048252a141005d05e4f43ffffc4ffc2e04fe0a2068989a1340182c13f2f8077fc0be9f0048400a0926e000600822cf2003b043cd207231120f800066015b0d520722f1a00000001bf819fcca2425f35fe1423eef53135440180e0b7a8c5e16bfc03472f5cb20b170cda37fcfc21a1242880301c00f54b7cbb71810137a401a8b4ffffff60cd040010000436a7fff1f6d01241398a00018218014750ffff800006401a50028151b60039d0002bfc33e70094ab048205212602008d79c7c02c541810438037ffffe4411300060860c27000efff6f4e041204c02680006008018eeeff1c8da185c800822)
def B2 (j:Nat):Nat:=(if j<2 then (if j<1 then 0x8ae000001c40000000516800000000000000000000000000d8ea0001041a14ad94ba2f9110b467000184ac0000000d05054a506a80fa000180fc000204c49b7085c00042fcc1fe00030ae80000000000000054eba9e1317f16b00000001833e0a08000012a0000000000000000000000771488e40000000207400000000000000002fc047800070e6000001380000000000182480000000000000000000a5e00011186b3380000000000000000000000000000000000000000307e80000001525c0000000000000000000000000184b400000008150000000009538c4e232000000000000d55126300000000000000000000000000344600000000857d039c2b444c4000000060e4000131bc05680000000028000000008163817000000000000000103d40140001022400061240000000000000001166000000000000000000000000000000000070a800081fc232757300000000000000000002dfe000145e0000000000000006099c0cda2c874b80000001335400000000000000000000000000000095730720000000000000000001b4bf1868000e9f59a520148000401c04040000000000182060108000511c000000000000000810000000000000000000100001a660000000000000000001498c046d26600000006f70000000000000000109c000242d4f40c80400030a00000ca3600000000000985f051c0000000000000000000000000104c80000000000103300000000c1105be8000692a00000000000000082ac0000000408a00000000000000000000000000494e000000000000000000000000000000000000000000000000104f00000000000082d4000000000010600000606c000000020218148000005f000000000000b28400000000000000000000000000000004b00000000a19c00060d2000000000b00000000015f00000000c1be000000000000000000000000000001830800060390000000005a010ac15e000000000006e0e0000000011984da808c04d00000001005400000000000000000000000000000000000004091844c45680000001056c0000000000002c120d914b01900419a3d00008006025f21f4f714d68000005480000000000328880000000000000026310000bcdc00000000000bbb80000409124f8b0a00900000000000027c410000019c0d0550000000012c713a8959000034c745d80000000000000000000000392815b80000000000107a207708da908400040900460000303b00000000bd100000000d1a112a800000002d2880f4000600d34004122460351060000227330202013212740045132070000005072a301113130020210b81043010000000c000016100010064028024520010120056011014402310003150401010300103010012031250001300100100201006000220001001100210 else 0x200030ac0000516a5be3699000000008a3c00000000000000002a000000000002022c2e30000048400060a1000024a007c00009174000000000009d48000000000000000000000000000000000000008990000000000000000000b9744310000c2c2000000000004d48000233766b2000094140840000d9d1896646880f60000000341480005eb000024798000000000030a8e0dd0000000006c80000001807b419600c000083012a9e09b000000000000000ad3000000000000000000000000b0a0000256c00000000000000000060cd00000000000000000000000000208542d000016b80000c8dc000000000d60001102c000217b000082939a00000000084dc00000000000b3fc000000000000000000202f822a29d70b50000000000023498000022c000365e40056ae20d2c0000000000000024330000000003a66b68000000084da22d800002ed004c0000000c296000000000ea000000000000000106c09ac0000000e1e4000000041140000a26000001460000000000060172682000000000000000000300fc07d00000000000217ac8de00200000939407c000000060500001821d03cc11f000184cc000000002a000000000000009382ac00000000000000130d00005864000000e0000000120b805fe92300000001b15c14d00ac000000000004254000000016ec0001b1b800028970000000000051350000000102ee6f8c9e60000000609800000000000493a00012ce40006267000000030aba1281ca80000007800000000000000000000000002495800000000000000000000000000000000000000000000000000000000000685b00000000000000000000000000415381f7225400000000001bab80006b560001017800000000000829c0000000c29200000000000000139b000000000001db85002000042c6000000040a20000000119300000001cd10000245dd2ae000207be03000012b08759800000000000171000000012c340000000c25e840a0988e7b81580515a8c0000594483c800020e0000110fc00061674246000000000bd000000000000000594680a800000000000000000002b6000000000000000000081840000000004800010a78000000184b80000000d26f88b4000000000000000000000048c44baa086e03400000000062000000000001235000000000002697000000000000000000000000000000000040e4000000028bf000139aa00304790221a51055e0000407501fc0002084821c00000000000a8f0a88518500000000000001b000002980000000000000000000897e13000010412048cf420000d1b00006107822e45fa02b800000018298000610f0000000000000000000000218180000000011c06e2d350000000046580000001142eb397671000000000000000aa2925a000000000000000344e) else (if j<3 then 0x41d00000184b66e000000000000000000000000000000829c839e169800042da000201ac0b6000182380000000c61732da469349800000000000007c81ae00000000000ddda00000000000000000020b880000000000000000000000000000000000000000000020c700000000000000092c684600000000c1dc02c900500000000a04400000000000000323c0000000000000000000000000000004c700001ad2c0004152416e80880000000add200020380000c05c00000000000ccca000000000db00000000000000000000000000296c0000000102f800000000001221e0ce000181a811944fe00018129a89a064de30000041d00000000000000000650000000000000008a0e0000000000080d200036390000000000000948000000182e00000000000000020000000000180760ba0000000000000002ac1017c81f843f800000000000000286881f8000000060820000000000000180000000103a800000000001068e0bba1ca05700000000ae2a000000000000000000000022f800000000000211a00000000000000008003a8000000000000000000060d381dea5240000000000000000000000000000020b340372a8e0000000703c000000000000000d93d8183049b2b300000001052800088bc000229c800000013bca0310000614a000123649240001022c00000005d200327abf8000028400000004cfe20ea00030bbe89400000000000667400000002779804180b6000000020f1d28301e0a94095d5277c1df09a80b3000000000000000000083980000000000000000002f0b88ca000201d80000000000376be22ed10c000001980000001806d02a800000000000000294581c70278000000044d8000323180008948000000000000001d2990aa0051c0b00000000000098a9cbcc000000000000003634f6b90000814c0006962000183b220400000000000244deeaf00010059089530f86040000000000000000000031e03841b40000000000002bc000000000002ae00000000000000003ac20c0a08f00010564000600b0000000000000008146000000060eb82d680ad0b60000d5520000000606b000000010aaa0d000000003046000000000000000000000000000000044000000003a5ce493013a13d485ac06700000000000000094ce0000000000000000000000000000000000000000000000001972a746000002e6b1900000000a3da0008000020a000104300000000000160e004b4238048802200000000000374aa26eddf200000000000444e00024b58000000000020618000000005cc494c16e000000024b4f45d00000002649202540a424f0000029f81b050a59708000004f04e2418800000000000000000000000000000295480da00000002960c0b2000228528330000db7c000000042c800000000000827 else 0x544a7a0967a00d00000000000048b4049aa4dc81b266f832a755e4975a6891a603de0f30000000205d0000007800000006b0984ca937c08d8000c23a000172dc12082c485110bc0000d135004146a00009caa0ad712e422f02180000000000000b400000006020000090400000000000000018bf800000000001b8900000000000270c800000000000000000000008064000000000000003037a17f009a000202100000001842c00010e40000c96c0000032c11a000109d250600000000000000000000000b1f42724ae000020848000000083d449700000a5013ec1a6f63a000000000000080000103b40000000c27a0000000000000009029a3b80000000000309a000000000000000000000005ca4000000000000000000016f455284440000000000000033830000000005c80000000000000034268000c94c0001777ad7c000000010960672815c5bac00000009a96000000020c10000a07a443d02e0001a501018895100004a54770000042fa00030780000413800000000000000185c00000000418a0000000413f000000000000000024fa24c07c8000119b23c7274a8a98528000000000000000000067c402880dc00b40000000c85785e4000166f82cb849400000001dc48cb400000000000000104a440c0001c38f200a56d48e2809811e00000000a2e40000000000000000000ee4000085680004f6d000132500000000000000000000000409e000000000000000000000000000000827f003800041c5a33c0000000000000000000000000000000000000000180b000000002ada000000000000000000000040094ae391f800036770001a0c00000000c1ca00020658223000000000000000000105a4000000000012b4c00008f700000000000000041a92d3400005180000000106300004034000000000000000000079400000001838769c00000000000000000000000000209f6cbb000000010ba800009c000000000000d1e0000339300000000253f49e8103c28600014468000000083780000000000000000000000c022000105e0d80000184ec00))
def BX (_:Nat):=0x7ffffe000017e010944e400000002fff97991d6494e800fff0000bf2a0c06404fe000b950499fc055100a38000fe26242400007ff2f09a1617fe00190c05617fe060020549117a2510a3384a4e9fc361524e0fa3e03e2f90c3917e5f1502d8f646c410d9f27b984791dc0c01203002050200401a01860138764508e288c86a0501f82c0f0261d0c613066170243d028168d6760620381e0d03a02096070421100a200a83101600004060900a823d1bacb1eeca4d18860005916050130481100c020043ff
def B3 (_:Nat):=0xd07800000000010b16ef035b8d00060d400000041c0000000000000000000100a00000000000000000000000000000247b7329af1074e2801b30d892800173a92a812c0b102511f000a24021bab101200006500000000001016000000002201800088e6a840008155ca08d000081c24b80024100000000002054000447800000000000000000000000000000000c3d456800107600000060f4000000000000204200048c2287204000000289800010be8a000000000000000000000000000e38000000000000300c2320000000000000c02800000000000060d20238200000000000000013800000000000480000000000000000000a1c0cb9688000000c19c4741080008018000a3000040200000000020000248000a2900060fc00000001f0000000000000401c000000e990cac65c000811808800000040c80000019054908003750000000000145c00000020c00000000000000536000516e8a80000000098003078000c8d000203a0000000002456000000000063b836000000000000000000000000000001058000000914000000000000000000000000000000000000c5cc274000bb9000000000000000020c5114000000000000000000000000000004830000000000000000000002600000000000005080ce400000069160ca1363b7017000102f039000645346000001480006151a0650000016e1010000001050000000206c0000144076040b30037c07c0022620000000000001bab88000af05a0000002cdc000000000000000012200042a315e000105800208308e0000000000000000406000000002060e80000000004c380000006c860bc24800008d8003534000000103503d10cc0b000000000091a80000000000000000000000000000000000000062e000088d000244800181f00c600880508000114000100510020081c0084222500080020
def BY (_:Nat):=0x403103b437ff
def B4 (_:Nat):=0x3040022200000000000004200000000000006700107c08000000000000000000020500000000008cc000000000000951970000095f06002310000000000000005c40000000000000d000000000000000145000000000084c00000000000061c0000000000000000000000000000000000127000000000000000001140000000000000000037300000000004dc0000000894000000000000000000000000000000000000000090000000000000110000000000000000000000000000000000000000000000c44000000000024000000000000000edc000000085c0000000000000000000293000000000054000000000000000000d1c000000000318000005dc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004e000e980000000000000000000000000000000000000003a70000000000000000000000000000000000000000000001c03000000000000024600000000000000000000c0c000000000000000000000000000000000000000000000000017400000000000012100253000000000000000001860000000000000000035100000000000000000000c04000000000000003080000000000000000000000000000000000000000000000000000000000000000009800000000000000000000000000000000000000000000366000000000000000400
def wd:Nat->aF
 | 9=>(7,6,9,393221,51,6,4096,CS)
 | 10=>(182,5,9,5963854,119,11,4144,BT)
 | 11=>(820,4,9,5898424,120,14,4465,BU)
 | 12=>(386,3,9,1769521,86,15,4664,BV)
 | 13=>(66,2,9,655368,67,13,4360,BW)
 | 14=>(9,1,9,65537,0,9,4180,BX)
 | 15=>(1,0,9,65537,0,0,4099,BY)
 | _=>a0
def yb:Nat->Nat->Option (Nat × Nat)
 | 10=>ch 3 61 1 8 3 3 BZ
 | 11=>ch 65 977 3 14 8 4 B0
 | 12=>ch 353 1741 8 16 10 4 B1
 | 13=>ch 199 1993 4 15 9 4 B2
 | 14=>ch 40 409 5 13 7 4 B3
 | 15=>ch 12 431 1 10 4 4 B4
 | _=>fun _=>none
def mo:aM:=⟨1535,15,fun i=>Da[i]?.getD (0,0),C9,C7,wd,yb⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma mm:aD mo (ai CT)=true:=by simp only [aD,and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aH (d:=6) ?_⟩,aH (d:=3) ?_⟩<;>simp only [aW]<;>(try repeat' apply And.intro)<;>decide +kernel
lemma BI:ag mo 9 0 6:=aL cA cz (fun _=>0x7b44819a306751009a5093b784047230032800865a200437000b64002b510562020ba8451937002508043b60092163274655) rfl (by decide +kernel)
lemma BJ:ag mo 9 6 1:=cJ cA cz (fun _=>0x31401265) rfl (by decide +kernel)
lemma C8:ag mo 9 0 7:=(aw BI BJ)
lemma zG:ag mo 10 0 5:=by apply bR;apply aq 9 0 0;simp only [aE,ba];decide +kernel
lemma zH:ag mo 10 5 67:=aL cA cz (fun _=>0x20159475300532700250885a2900592600801264a1300803700b6245194200471000253885a2900593600801264a130040870080359a7b6804235006308b089650630700801264a1300402700628b1807a20016800ba84519470050210020169475300894000201694753006540002016947530059400020159475300754000201a9475300754000b8262631a003261002018b4a5300743000201a94753006940002015947530075400060b214263002130002015947530075400020159475300754000801264a1300201600801264a13003917002018b4a13004716002018b4a13004716002018b4a1300471600601bb48230048160032844b36a001547002018b4a1300471600801264a1300271600801264ab32027160020159475300654000201594753007540002015947530064300060141426300193000601414263002140002015947530075400060141426300192000201594753007540002015947530075400020159475300684000201a947530069400060121426300713000801264a13004130006b02152690021400020159475300754000201a947530058300020159475300643000201594753006430006012142630091200008257691a0068510008257691a0068510060121426300813000801264a130041300008257691a0067510008214635a0030410065121426300713000851264a130041300006214135200307100801264a1300413000601214263007130002051374291082570008214635a1080310060121426300712000801264a130031200) rfl (by decide +kernel)
lemma xr:ag mo 10 72 1:=bG (by decide +kernel)
lemma xt:ag mo 10 73 13:=aL cA cz (fun _=>0x32800865a20054800832008a602042081035a27a2986016750009457592140509700850265a190050490035a27a2986015690035a27a298601564000748a2867406417000748a286740641700064b0218a00176020630bb0896506309063b4003506917682506a84b25670028070) rfl (by decide +kernel)
lemma xu:ag mo 10 86 1:=bG (by decide +kernel)
lemma xw:ag mo 10 87 11:=aL cA cz (fun _=>0xba84519470047100032800865a2006580032800865a200548000638006a820024510430b81a362057160032800865a2005480032800865a20054800628b1805a20175800862008a6020420810862008a6020420810862008a602042081) rfl (by decide +kernel)
lemma xx:ag mo 10 98 2:=bG (by decide +kernel)
lemma ut:ag mo 10 100 39:=aL cA cz (fun _=>0x8045947b350654000810368a13b051370002844865a208063002015947530075400065021526900103900230881a5620681200b62451942004021006502152690021400065b2142630021400060121426300214000b4262037410290100201594753008540002015947530065400085709ab76804657007b8106ab90046301095b264a19004087000638006a85004681060121426300214000201594753006540000628a1862006821006014142630021400060141426300193000b68451942005021006308b089650740800b68051942005021002570945730058400025b09457300584000257094573004830000268a9867506584009a5093b78405634008351374892043620002814835a204073000268a9867506854006014142630021400060141426300214000601214263001038006a84b25a780361900ba845194700491000ba84519370036100) rfl (by decide +kernel)
lemma uw:ag mo 10 139 39:=cJ cA cz (fun _=>0x65a530108746a23284b6838365ab401003ba0473656b4010a36b4872374672326561301009365573565a30707868a29109065573314312767b4b8964654b3196891b5ba3654131968786a2108786a2218786a2218786a221929b0761565630708786a280656030966565309665653096656530967868a2918786a2218786a29114a1901053341271533412715334127113ba04725334127126b43076) rfl (by decide +kernel)
lemma ux:ag mo 10 178 1:=bG (by decide +kernel)
lemma uy:ag mo 10 179 3:=cJ cA cz (fun _=>0x76b97121426b234314a59010) rfl (by decide +kernel)
lemma CJ:ag mo 10 0 182:=(aw (aw (aw zG zH) (aw xr (aw xt xu))) (aw (aw xw (aw xx ut)) (aw uw (aw ux uy))))
lemma zI:ag mo 11 0 7:=by apply bR;apply aq 9 0 0;simp only [aE,ba];decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma zJ:ag mo 11 7 96:=by apply bR;apply aq 10 0 4;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
lemma uz:ag mo 11 103 9:=by apply bR;apply aq 10 0 0;simp only [aE,ba];decide +kernel
lemma uA:ag mo 11 112 96:=aL cA cz (fun _=>0x201594753006430009102524b3100421006012142630021400060121426300214000201594753007540006018b485300854000601414263001830002015947530075400020159475300754000801264a13006140002015947530075400060141426300214000201594753007540000a814135700402100201594753007540002015947530075400020159475300754000801364a13006140000a81413570030210020159475300754000201594753007540006012142630021400060141426300214000601214263002140006014142630021400060141426300214000601414263001a30006012142630021400060121426300214000601214263002140006012142630021300060141426300213000601214263002130006012142630021300008214635a0030510008214635a0030510008214635a0030510008214635a0030510008214635a0030510008214635a0040610008214635a0040610008214635a0040610008214635a0040610008214635a004061002015947530075400060b2142630021400008214635a0040610008214635a00406100851264a1300614000851264a1300614000851264a130061400008214635a1040910008214635a10409100801264a1300514000801264a1300614000801264a1300614000801264a1300514000801264a1300513000801264a1300514000801264a1300514000801264a13005140002b1035249003940002b40352490039400008214635a10905100801264a1300513000801264a1300614000801264a1300513000801264a1300614000801264a1300513000801264a1300513000801264a130051300008214635a0030510008214635a0030510008214635a0030510008214635a003051002018b4a53008540002018b4a530085400020159475300754000205137429104372002108b2a53107432002108b2a53107432002018b4a5300743000201594753007540002018b4a53008540002018b4a53007a40002018b4a5300743000201a94753007540002018b4a530074300008214635a0030510008214635a0030510008214635a0030510008214635a00305100801264a130051300020513742910326900801264a130051300008214635a1030410) rfl (by decide +kernel)
lemma uB:ag mo 11 208 96:=aL cA cz (fun _=>0x2015947530075400020159475300754000201594753007540002015947530075400020159475300754000201594753007540002015947530075400020159475300754000201594753007540002015947530075400020159475300754000201594753007540002015947530075400020159475300754000250885a2900835000250885a2900835000a502257890012490065021526900103900a50225789001a39006502152690021400065021526900214000862008a602064191065021526900214000205887a29107a6200250885a290079400060b214263002140002016947530075400020169475300643a002016947530075400025043542900324a000248a386420864300801264a1300503800801264a13005038000892a368420684300801264a130050380068b4b358420473200b8262631a003261002016947530064380020169475300754000801264a1300503800801264a1300503800801264a130050380020169475300643900801264a130050390080b264a1300503900801264a1300503900a230690a570054600082b4631a002840002015947530064390020159475300754000801264a13005039000248a386420864300801264a1300503900801264a1300403800801264a13004028002018b4a530063280018202631a002851002018b4a53006328002018b4a53006328004986852a4b016730018202631a002a51000248a3864206421002018b4a530063280018202631a002851002018b4a530063280018202631a00285100801264a130040280008200a6b50046a120801264a1300492800436b84a26306172000248a386420642100801264a1300492800801264a13004928000248a38642064210020169475300643a00201694753006438002016947530064380020159475300643900850265a1900504a00250885a2900724800862008a6020640a10862008a6020640110201594753007540002015947530075400020159475300754000201594753007540002015947530075400080159475300954000201594753009540009102524b310053200801264a13006140002015947530075400020169475300754000801364a1300614000201594753006430008015947530064300) rfl (by decide +kernel)
lemma uC:ag mo 11 304 94:=aL cA cz (fun _=>0xa6020a827606a141035a27a2986016750080359a7b680645700250885a2900693700630bb089650630700a6020a827607a2510250885a29006937006a84b25a7804729000268a98675064530026a00279500153910a6020a8276069a4100268a9867506453000268a986750756400250885a29006937006308b08965063070080359a7b680534600a230690a57005460032800865a20087200850265a1900504800250885a2900724800850265a1900504800250885a290072480080359a7b68064570032800865a20087200850265a1900504800250885a2900724800801264a130050380086a002795801642106308b08965074080080359a7b6806457006018b489300743800628b1807a200172000892a368420573a000892a3684206843000268a9867507564005890b3984205943009a5093b78405934009a6093b78405934009a5093b78405934000892a36b4806743009230631a2401934000248a3864207943000248a386420794300648b1807a201283000892a36b4805743000896a3684206843000892a36b4806843008b403584900345000201694753007540009a5093b78404623000892a36b480573200b6245194200502100201694753007540006012142630021400060121426300214000201594753007540002015947530075400020159475300754000201594753007540002015947530075400020159475300754000201594753007540002018b4a530085400020159475300754000201a947530075400020159475300754000b6245194200502100201594753007540002015947530075400020159475300754000801264a130061400020159475300754000801264a1300614000801264a1300614000801264a1300614000801264a1300614000201a947530075400020159475300754000b6245194200502100801264a130061400008257691a00726100201594753007540002016947530075400020159475300754000201594753007540002018b4a53008540002018b4a530085400020159475300754000801264a1300513000801264a1300513000801264a1300513000801264a1300413000801264a13005130002015947530075400) rfl (by decide +kernel)
lemma uD:ag mo 11 398 1:=bG (by decide +kernel)
lemma uE:ag mo 11 399 1:=aL cA cz (fun _=>0x268a98675064590) rfl (by decide +kernel)
lemma uF:ag mo 11 400 1:=bG (by decide +kernel)
lemma uG:ag mo 11 401 20:=aL cA cz (fun _=>0x628a186200752100832008a602064091032800865a2007610018202631a0028510032800865a2007610008257691a0068510032800865a2007610032800865a20076100862008a6020640110628b1807a20197200832008a6020641a102308b1a56206a170032800865a20076100832008a60206401102308b0a562063070032800865a20076100250885a2900724800250885a2900724800a6020a827606a1410205887a290061570) rfl (by decide +kernel)
lemma uH:ag mo 11 421 1:=bG (by decide +kernel)
lemma uI:ag mo 11 422 10:=aL cA cz (fun _=>0x268a986750756400a230690a57005460026a0027958016421026a00279580153a1032800865a20076900250885a290083500032800865a200769000638006a85004671032800865a20076900832008a602064191) rfl (by decide +kernel)
lemma uJ:ag mo 11 432 3:=bG (by decide +kernel)
lemma uK:ag mo 11 435 68:=aL cA cz (fun _=>0x601414263002140006012142630021400020169475300754000601214263002140006012142630021400060121426300219000b9452637a10326100b9262637a1032610020169475300754000206887a2910837200206887a29108372006890b35842047830021069275310643200a5022578900235000201594753007540002015947530064a0002015947530075400020159475300754000601414263002140000248a38642086430060141426300214000064b0218a00238120b6040a8276083261080359a7b6807568001328a4b6530860400801364a1300503800601bb485300743800250885a29006837001328a4b6530758300801264a1300503800801264a1300503800b68151942005021008015947b3507540001328a4b65308604001328a4b65308604001368a4b65308604001328a4b6530860400801a947b3507540001328a4b65308604000268a986750867500250885a2900724a000892a368420573200250885a2900724800250885a2900724a00850265a1900504a0080b264a130050380020159475300643800850265a1900504a0032800865a20076a0032800865a20076100250885a2900724a00801264a1300503800801264a1300503800850265a1900504900850265a19005049006894b358420473200628b1807a20017200b8245693a003840008306907b650640a000248a386420753200850265a1900504a00862008a6020640a10862008a6020640110801264a1300503800850265a1900504a00250885a2900724800250885a29007248006a84b25a78049120) rfl (by decide +kernel)
lemma uL:ag mo 11 503 1:=bG (by decide +kernel)
lemma uM:ag mo 11 504 5:=aL cA cz (fun _=>0x601414263002140006012142630021400020159475300754000601214263002140001628a1b620086210) rfl (by decide +kernel)
lemma uN:ag mo 11 509 1:=bG (by decide +kernel)
lemma uO:ag mo 11 510 83:=aL cA cz (fun _=>0x2048b3a5420654340062ba1862007821005a80b198700562100026ba9867507865007412079541054021020b71ba576085213020159475300754000201594753007540002018b4a5300854000205887a29107a620060b214263002140002308b1a5620791200250885a290083500080b264a13006140002015947530075400060b214263002140002015947530075400060121426300214000204594753007540002054374291043720020459475300754000b62451942005021001628a1b620086210020459475300754000601214263002140004b8609b837058371065b214263002140001628a1b62008621005628a18620086210025b4945730057400025b49457300574000804a9475300754000204594753007540002015947530075400020159475300754000201594753007540006012142630021400060121426300214000b62151942005021002016947530075400065021526900215000801264a13006140002015947530075400020459475300754000201594753007540005890b398420594300ba8451947005021008015947b3007540000892a36842068430008244635a0040610008257692a007261000248a3864208643000248a3864208643000248a3b64208643009a5093b7840573400651214263002140005628a1862007621002048b4a53008540006502152690021500065b2142630021400085b264a130050380065b2142630021400085b264a130050380085b264a13005038006894b35842047320008244639a003850006891b35842047320008244639a003850007b8106ab9005640100a644639a00385000a9462587b402148007b8106ab9004630100248a3864207532000248a3864207532007b8006ab90046901085b364a1300503800a9462587b401938005278006a84004671095036ba1980504700a9462587b4021380090359a4b6808456006012142630021a0006014142630021400) rfl (by decide +kernel)
lemma uP:ag mo 11 593 1:=bG (by decide +kernel)
lemma uQ:ag mo 11 594 2:=aL cA cz (fun _=>0x1a80813b700382100ba635694a0050610) rfl (by decide +kernel)
lemma uR:ag mo 11 596 96:=cJ cA cz (fun _=>0x8796a2328746a2328746a23214a190103183123214ab901065ab401076b8612165ab301076b8612165a1401070b9a12165ab301065ab301065ab301065ab301065ab301070b8a12170b8a12126183121754b297565ab301076b8612165a5301065ab301065ab301065ab3010658b301065a1301070b8a19170b8a19170b8a19170b8a19170b8a191133912a2133912a2133912a270b8a19135ab043070b8a19170b8a19165ab301076586121765861217658612165ab301065ab301065ab301070b8a12170b8a121a1b68661a1b6865076b86121765861213146129270b8a12170b8a12190a055403bb618978796a2218786a2218796a2218796a2218796a2218796a2218796a2218796a2218796a2218796a221a1b68650531a04937658612153ba0493a1b6866153ba04938796a232531a0493a1b6865076b8612153ba0493a1b6866103ba049353ba0493133912921339129214ab901014ab901031461232314612323146123214ab901014ab901014ab9010426b234335ab0440426b2343) rfl (by decide +kernel)
lemma uS:ag mo 11 692 7:=cJ cA cz (fun _=>0x8786a2218796a2328796a2328796a2328796a2328796a2328796a232) rfl (by decide +kernel)
lemma uT:ag mo 11 699 1:=bG (by decide +kernel)
lemma uU:ag mo 11 700 39:=cJ cA cz (fun _=>0xb67b0a8656b6308070b9a121560a3080560a3080560a30808786a2218786a2218786a2218786a221093a55848786a2218786a2218786a2218786a2218786a221093a55848786a2218786a2218786a221a1b786508786a221754b29648786a2a2a1b78651a1b78661b67b0a75a1b786518786a2a22619318126193181261931817868a2a226193181b67b0a75261931818786a221b67b0a75a26a2872) rfl (by decide +kernel)
lemma uV:ag mo 11 739 1:=bG (by decide +kernel)
lemma uW:ag mo 11 740 31:=cJ cA cz (fun _=>0x754b296426543121b4a49550b4a49550b4a495508796a221a1b78650a1b78650a1b7865046ba7080a1b79650a1b78651b67b0a86b67b0a86a1b786618746a23242642343b67b0a8665a14010b67b0a86b4a495408796a232319612328796a2328796a2323146123231461232656b301065613010b464b550b67b0a86) rfl (by decide +kernel)
lemma uX:ag mo 11 771 1:=bG (by decide +kernel)
lemma uY:ag mo 11 772 3:=cJ cA cz (fun _=>0xa1b68661929b07728796a232) rfl (by decide +kernel)
lemma uZ:ag mo 11 775 1:=bG (by decide +kernel)
lemma u5:ag mo 11 776 44:=cJ cA cz (fun _=>0x70b9a121946475503746723294a4755076b9712176b9712170b8a12165ab30108785b23270b8a1213185123265a530107058a12170b9a12114ab901065a530102659312126193121658530106585301026193121261931218796a2328796a2328796a2328796a23265a0301014a0901065a030102654312165ab401065a5401065a54010a1b6866165a5401065ab401065a5401065ab40108796a232656130108796a23270b9a12170b9a12114a59010) rfl (by decide +kernel)
lemma CK:ag mo 11 0 820:=(aw (aw (aw (aw zI (aw zJ uz)) (aw (aw uA uB) (aw uC uD))) (aw (aw (aw uE uF) (aw uG uH)) (aw (aw uI uJ) (aw uK uL)))) (aw (aw (aw uM (aw uN uO)) (aw (aw uP uQ) (aw uR uS))) (aw (aw (aw uT uU) (aw uV uW)) (aw (aw uX uY) (aw uZ u5)))))
set_option maxHeartbeats 0 in
lemma zK:ag mo 12 0 62:=by apply bR;apply aq 10 0 3;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma xy:ag mo 12 62 96:=by apply bR;apply aq 11 0 4;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma u6:ag mo 12 158 75:=by apply bR;apply aq 11 0 4;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
lemma u7:ag mo 12 233 10:=aL cA cz (fun _=>0x201594753007540009102524b310053200201594753007540000a814135700402100601214263002140006014142630021400008214635a1040610008214635a1040610008214635a104061002108b2a531085320) rfl (by decide +kernel)
lemma u8:ag mo 12 243 1:=bG (by decide +kernel)
lemma u9:ag mo 12 244 21:=aL cA cz (fun _=>0x2018b4a53008540002018b4a53008540002018b4a53008540002018b4a5300854000801264a1300614000201694753007540002016947530075400020169475300754000201594753007540002015947530075400020159475300754000801264a1300614000250885a2900835000250885a2900835000850265a1900615000a5022578900235000862008a60208613106894b3584205843000248a3864208643000892a36842068430008b2a36842068430) rfl (by decide +kernel)
lemma vc:ag mo 12 265 1:=bG (by decide +kernel)
lemma vd:ag mo 12 266 29:=aL cA cz (fun _=>0x832008a60208613100268a9867508675009a5093b78405734009a6093b7840573400201594753007540002015947530075400020159475300754000201594753007540002015947530075400020159475300754000201594753007540002015947530075400020159475300754000201594753007540002015947530075400020159475300754000801264a1300614000801264a1300614000801264a1300614000801264a13006140009a5093b7840573400801264a1300614000801264a1300614000801264a1300614000801264a1300614000b8262631a0032610008257691a0072610008257691a0072610018202631a0032610) rfl (by decide +kernel)
lemma vf:ag mo 12 295 1:=bG (by decide +kernel)
lemma vg:ag mo 12 296 13:=aL cA cz (fun _=>0x268a9867508675000268a9867508675000268a98675086750090379a7b6807568000268a9867508675000268a98675086750080359a7b6807568000268a9867508675000268a986750867500a230690a5701657000268a986750867500a230690a57016570026a0027958027531) rfl (by decide +kernel)
lemma vh:ag mo 12 309 1:=bG (by decide +kernel)
lemma vi:ag mo 12 310 1:=aL cA cz (fun _=>0x268a98675086750) rfl (by decide +kernel)
lemma vj:ag mo 12 311 1:=bG (by decide +kernel)
lemma vk:ag mo 12 312 6:=aL cA cz (fun _=>0xa230690a5701657000268a986750867500a9462587b40325000a9462587b40325000a9462587b4032500095046ba198061580) rfl (by decide +kernel)
lemma vl:ag mo 12 318 7:=by apply bR;apply aq 12 0 0;simp only [aE,ba];decide +kernel
lemma vm:ag mo 12 325 6:=aL cA cz (fun _=>0xa9462587b4032500086406b0a58016580085026ba09806158007b8106ab9006851107b8006a83006831106894b35842058430) rfl (by decide +kernel)
lemma vn:ag mo 12 331 1:=bG (by decide +kernel)
lemma vo:ag mo 12 332 4:=aL cA cz (fun _=>0x9a5093b78405734009230631a2401634009260631a2401634009230631a24016340) rfl (by decide +kernel)
lemma vq:ag mo 12 336 1:=bG (by decide +kernel)
lemma vr:ag mo 12 337 7:=aL cA cz (fun _=>0xa9462587b40325000a9462587b403250005890b3984205843005890b3984205843005890b398420584300a9462587b403250005890b39842058430) rfl (by decide +kernel)
lemma vt:ag mo 12 344 1:=bG (by decide +kernel)
lemma vu:ag mo 12 345 22:=aL cA cz (fun _=>0xa50225789002350005a80b1987005821006894b3584205843006894b3584205843006894b358420584300a230690a5701657006894b3584205843000248a3864208643000248a3864208643000248a3864208643000248a3864208643006894b3584205843000248a3864208643000248a3864208643005896a3684206843000248a3b64208643000248a3864208643000248a3864208643000248a3864208643000248a3864208643006894b3584205843000248a38642086430) rfl (by decide +kernel)
lemma vx:ag mo 12 367 1:=bG (by decide +kernel)
lemma vy:ag mo 12 368 18:=aL cA cz (fun _=>0x5a80b198700582100634ab489350854000a43752874903205304687b58294083506076835894a3050834059471b98670581230250885a2900835000250885a2900835000250885a2900835000250885a2900835000250885a2900835000250885a2900835000650215269002150000628a186200862100250885a2900835000a5022578900235000a5022578900235000a502257890023500) rfl (by decide +kernel)
lemma CL:ag mo 12 0 386:=(aw (aw (aw (aw zK (aw xy u6)) (aw u7 (aw u8 u9))) (aw (aw vc (aw vd vf)) (aw vg (aw vh vi)))) (aw (aw (aw vj (aw vk vl)) (aw vm (aw vn vo))) (aw (aw vq (aw vr vt)) (aw vu (aw vx vy)))))
lemma zL:ag mo 13 0 5:=by apply bR;apply aq 9 0 0;simp only [aE,ba];decide +kernel
lemma zM:ag mo 13 5 18:=by apply bR;apply aq 10 0 1;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
set_option maxHeartbeats 0 in
lemma xz:ag mo 13 23 43:=by apply bR;apply aq 11 0 3;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
lemma CM:ag mo 13 0 66:=(aw zL (aw zM xz))
lemma zO:ag mo 14 0 9:=by apply bR;apply aq 10 0 0;simp only [aE,ba];decide +kernel
lemma zP:ag mo 15 0 1:=bG (by decide +kernel)
lemma wf:bT mo 15:=by intro k hk;match k with|9=>exact C8|10=>exact CJ|11=>exact CK|12=>exact CL|13=>exact CM|14=>exact zO|15=>exact zP|0|1|2|3|4|5|6|7|8=>exact cZ mo _ 0|_+16=>omega
lemma wg:aB false co 15 inputs.toFinset:=by
 rw [show co=aY mo by decide +kernel];exact lQ (g:=mo) (top:=15) (i:=0) (ad CT C4) mm wf (by decide) (by decide +kernel)
lemma xT:aR false (cB 511) (ac 511) 16:=
 cD (b:=13438558465) (by decide +kernel) (by
  have e1:ac 511=co:=by decide +kernel
  have e2:cB 511=inputs:=by decide +kernel
  rw [e1,e2];exact wg)
end
end S9
namespace S10
open PEqualNP.Outside.L_meta_6026.Core
local instance : Width := ⟨true⟩
def gm (r:bW) (j:Fin 10):=aV r (inputs.getD j.val zero)
def jq (x:Fin 10->Bool):Bool:=
 (x 0&&x 1)||(x 1&&x 2)||(x 2&&x 3)||(x 3&&x 4)||(x 4&&x 0) ||
 (x 0&&x 5)||(x 1&&x 6)||(x 2&&x 7)||(x 3&&x 8)||(x 4&&x 9) ||
 (x 5&&x 7)||(x 7&&x 9)||(x 9&&x 6)||(x 6&&x 8)||(x 8&&x 5)
lemma jO:∀ r:bW,aV r co=jq (gm r):=by decide +kernel
lemma eY:bg co:=by unfold bg;decide +kernel
lemma rt (r:bW):List.ofFn (gm r)=inputs.map (aV r):=by rw [<- h6,List.map_ofFn];rfl
lemma p3 (C:Circuit) (h:PEqualNP.MetaComplexity.FanInTwo C) (i:Nat) (r:bW):aV r ((dB C.gates inputs).getD i zero)=(C.wires (List.ofFn (gm r))).getD i false:=by rw [<- oG,io _ _ _ (fun g hg=>(h g hg).1),rt];rfl
def jj (i:Fin 10):Nat:=[1,0,3,2,3,7,8,5,6,7].getD i.val 0
def cp (i:Fin 10):bW:=Fin.ofNat 1024 (1<<<jj i)
def bX (i:Fin 10):bW:=Fin.ofNat 1024 ((1<<<i.val)|||(1<<<jj i))
set_option maxHeartbeats 1000000 in
lemma bQ:(∀ i:Fin 10,aV (cp i) co≠aV (bX i) co)/\(∀ i j:Fin 10,i≠j ->aV (cp i) (inputs.getD j.val zero)=aV (bX i) (inputs.getD j.val zero)):=by decide +kernel
def qz:aQ:=inputs.getD 0 zero&&&inputs.getD 2 zero
def dZ:List aQ:=inputs ++ [qz]
def w5 (u:Bool) (T:aQ) (k:Nat) (S:Finset aQ):Prop:=
 ∃ (U:Finset aQ) (a b:aQ),S=insert a (insert b U) /\
  bg a/\bg b/\a≠b /\
  bM 0 a b ∉ S/\cL u T k (insert (bM 0 a b) U)
def bV (u:Bool) (T:aQ) (cap:Nat) (S:Finset aQ):Prop := ∀ k ≤ cap,¬ w5 u T k S
def kS (ctx:bc) (a:aI) (bs:List aI):=bs.all (fun b=>dJ ctx a b 0)
def fE (ctx:bc):List aI->Bool
 | []=>true
 | a::bs=>kS ctx a bs&&fE ctx bs
lemma jJ {ctx ws} (h:fE ctx ws=true) {a b:aI} (ha:a ∈ ws) (hb:b ∈ ws) (ne:a≠b):dJ ctx a b 0=true\/dJ ctx b a 0=true:=by
 induction ws with
 | nil=>simp at ha
 | cons w ws ih =>
  simp only [fE,and_eq_true,kS,all_eq_true] at h
  rcases mem_cons.mp ha with rfl|haTail
  . have bm:=(mem_cons.mp hb).resolve_left (Ne.symm ne);exact Or.inl (h.1 b bm)
  . rcases mem_cons.mp hb with rfl|hbTail
    . exact Or.inr (h.1 a haTail)
    . exact ih h.2 haTail hbTail
lemma kZ {u} {T:aQ} {cap:Nat} {ws:List aQ} (hn:ws.Nodup) (hc:0<cap) (twoStep:∀ a ∈ ws,∀ b ∈ ws,∀ ka kb,a≠b->bM 0 a b ∉ ws ->bg (bM 0 a b)->(cu ws a b 0 ka kb).length ≤ cap ->aB u T (cap-1) (cu ws a b 0 ka kb).toFinset):bV u T (cap-1) ws.toFinset:=by
 classical
 intro k hk h;obtain ⟨U,a,b,he,ha,hb,hab,hf,tail⟩:=h;have am:a ∈ ws:=mem_toFinset.mp (he ▸ mem_insert_self _ _);have bm:b ∈ ws:=mem_toFinset.mp (he ▸ mem_insert_of_mem (mem_insert_self _ _));have fresh:bM 0 a b ∉ ws:=fun hm=>hf (mem_toFinset.mpr hm);have hz:=eI tail _ (mem_insert_self _ _);let ka:=decide (a ∈ U);let kb:=decide (b ∈ U);let rest:=(ws.erase a).erase b
 have er:rest.toFinset=(ws.toFinset.erase a).erase b:=by
  rw [show rest=(ws.erase a).erase b by rfl,g4 (hn.erase _) b,g4 hn a]
 have ke:(cT ka a (cT kb b rest)).toFinset=U:=by
  rw [fY,fY,er,he]
  ext j
  by_cases aa:a ∈ U<;>by_cases bb:b ∈ U<;>by_cases ja:j=a <;>
   by_cases jb:j=b<;>simp_all [ka,kb]
 have rn:rest.Nodup:=(hn.erase _).erase _;have ar:a ∉ rest:=fun hm=>hn.not_mem_erase (List.mem_of_mem_erase hm);have br:b ∉ rest:=(hn.erase a).not_mem_erase;have nk:=g7 kb b rest rn br
 have ax:a ∉ cT kb b rest:=by cases kb<;>simp [cT,ar,hab]
 have nd:(cu ws a b 0 ka kb).Nodup:=by
  refine nodup_cons.mpr ⟨?_,g7 ka a _ nk ax⟩
  intro hm;exact hf (he ▸ mem_insert_of_mem (mem_insert_of_mem (ke ▸ mem_toFinset.mpr hm)))
 have eq:(cu ws a b 0 ka kb).toFinset=insert (bM 0 a b) U:=by
  change (bM 0 a b :: cT ka a (cT kb b rest)).toFinset=_;simp [ke]
 have sc:=g9 tail
 have len:(cu ws a b 0 ka kb).length ≤ cap:=by
  rw [<- List.toFinset_card_of_nodup nd,eq];omega
 exact twoStep a am b bm ka kb hab fresh hz len k hk (eq.symm ▸ tail)
lemma kB {u raw T r s ws pools links cap} (pairs:dH T r s) (faith:∀ w ∈ ws,cP r s w) (nd:(ws.map Prod.fst).Nodup) (hc':0<cap) (pv:∀ p ∈ pools,dx u raw T p) (lv:∀ tag xs,xs ∈ links tag->aB u T (cap-1) (List.toFinset xs)) (checks:fE (cap,ws.length,ws,gS u ws,pools,links) ws=true):bV u T (cap-1) (ws.map Prod.fst).toFinset:=by
 apply kZ nd hc';intro a ha b hb ka kb ne fresh pro len;obtain ⟨a,haW,rfl⟩:=mem_map.mp ha;obtain ⟨b,hbW,rfl⟩:=mem_map.mp hb;have ab:a≠b:=fun e=>ne (congrArg Prod.fst e)
 have one (a b:aI) (aa:a ∈ ws) (bb:b ∈ ws) (ne':a.1≠b.1) (ka kb:Bool)
  (pr:bg (bM 0 a.1 b.1)) (fr:bM 0 a.1 b.1 ∉ ws.map Prod.fst)
  (test:dJ (cap,ws.length,ws,gS u ws,pools,links) a b 0=true):
  aB u T (cap-1) (cu (ws.map Prod.fst) a.1 b.1 0 ka kb).toFinset:=by
  rw [<- ii nd aa bb ne']
  exact gH pairs faith nd aa bb (fun e=>ne' (congrArg Prod.fst e)) hc' pv lv
   pr fr (jo test ka kb)
 have hd0:bY u 0:=Or.inl (by decide)
 rcases jJ checks haW hbW ab with hh|hh
 . exact one a b haW hbW ne ka kb pro fresh hh
 . rw [hF _ nd _ _ 0 hd0]
   exact one b a hbW haW (Ne.symm ne) kb ka (gE hd0 a.1 b.1 ▸ pro)
    (gE hd0 a.1 b.1 ▸ fresh) hh
def cV (g:aM) (k i:Nat):=
 let raw:=e9 g
 let (ops,bank,ws):=f1 g k i
 let values:=ws.map Prod.fst
 let (_,depth,_,_,_,_,_,_):=g.l k
 let rules:=(gM (g.l k) raw.length i).filterMap (fun (a,b)=>fV g ops depth bank a b)
 let ls:=fun tag=>((g.x k tag).bind (dT g (k-1))).toList
 decide values.Nodup&&decide (0<k)&&fE (k,ws.length,ws,gS g.u ws,rules,ls) ws
lemma gz (g:aM) (k i:Nat) (samples:dH (aY g) (fj fun j=>(g.s j).1) (fj fun j=>(g.s j).2)) (cols:∀ ci ∈ g.c,gB g.u (aN (eZ g.m ci)) (aY g) (dC ci.1 ci.2.1) ci.2.2.2.2) (names:∀ x ∈ g.a,iP (aY g) (x.map dh)=true) (prior:∀ j<(g.l (k-1)).1,aB g.u (aY g) (k-1) (bK g (k-1) j).toFinset) (checked:cV g k i=true):bV g.u (aY g) (k-1) (bK g k i).toFinset:=by
 simp only [cV,and_eq_true,decide_eq_true_eq] at checked;apply kB (raw:=cB g.m) samples _ checked.1.1 checked.1.2 _ _ checked.2
 . intro v hv;apply gw _ _ _ _ _ (gY g) v;exact (gU _ _).subset hv
 . intro p hp;obtain ⟨⟨a,b⟩,_,h⟩:=List.mem_filterMap.mp hp;exact gr g cols h
 . intro tag xs hx
   have e:((g.x k tag).bind (dT g (k-1)))=some xs:=by simpa using hx
   obtain ⟨pair,_,h⟩:=Option.bind_eq_some_iff.mp e;exact gx g _ names prior h
lemma fP {g:aM} {prior k i ws} (lower:∀ q,aR g.u (aN q) (ac q) (prior q)) (geom:aD g prior=true) (blocks:bo g (k-1)) (checked:cV g k i=true) (idx:dl g k i ws=true):bV g.u (aY g) (k-1) ws.toFinset:=by
 simp only [dl,and_eq_true,decide_eq_true_eq] at idx;rw [<- d2 idx.2];have g0:=geom;simp only [aD,and_eq_true,all_eq_true,beq_iff_eq] at geom
 exact gz g k i (eF geom.1.1.1 geom.1.1.2)
  (fun x hx=>en _ prior lower (geom.1.2 x hx)) geom.2
  (fun j hj=>jT g (k-1) prior lower g0 blocks (k-1) (Nat.le_refl _) j hj)
  checked
lemma CN:aR true (aN 3) (ac 3) 1:=by
 have h:=gP (u:=true) (raw:=aN 3) (T:=ac 3) (cN _ (by decide +kernel)) (fu 3 1) (by decide +kernel)
 have hc:((fu 3 1).map Prod.fst).toFinset.card-1=1:=by decide +kernel
 rwa [hc] at h
lemma CO:aR true (aN 7) (ac 7) 2:=by
 have h:=gP (u:=true) (raw:=aN 7) (T:=ac 7) (cN _ (by decide +kernel)) (fu 7 257) (by decide +kernel)
 have hc:((fu 7 257).map Prod.fst).toFinset.card-1=2:=by decide +kernel
 rwa [hc] at h
def kn:List (Nat × Nat):=[(15,4),(31,7),(63,8),(111,7),(127,9),(189,8),(191,11),(251,8),(255,12),(383,13)]
lemma tl:aX true kn:=by
 have hsub:kn.all (fun e=>decide (e ∈ S9.dW)&&decide (e.1<512))=true:=by decide
 intro e he;have h1:=all_eq_true.mp hsub e he;simp only [and_eq_true,decide_eq_true_eq] at h1;exact fG h1.2 (S9.kU e h1.1)
def l6:List (Nat × Nat):=(3,1)::(7,2)::(47,5)::(511,15)::kn
lemma wP:aX true l6:=by
 intro e he;simp only [l6,mem_cons] at he
 rcases he with rfl|rfl|rfl|rfl|hm
 . exact CN
 . exact CO
 . exact fG (by decide) S9.yP
 . exact fG (by decide) S9.re
 . exact tl e hm
def l5:List (Nat × Nat):=[(511,16)]
lemma wO:aX false l5:=by
 intro e he;simp only [l5,List.mem_singleton] at he;subst he;exact fG (by decide) S9.xT
def wL:List dd:=[(27,4,15,[66,16]),(31,7,31,[]),(78,4,15,[99,83,48,33,64]),(83,4,15,[99,83,64,32,16]),(91,5,47,[101,66,16]),(99,4,15,[48,96,83,64,32,16]),(111,7,111,[]),(123,7,111,[101,66,16]),(127,9,127,[]),(166,4,15,[114,98,83,33,16,64]),(167,7,31,[115,67,100,83]),(175,8,63,[116,100,83,32]),(189,8,189,[]),(191,11,191,[]),(198,4,15,[115,96,83,64]),(230,5,47,[83,114,99,33,16,64]),(238,7,111,[83,114,99,33,16,64]),(255,12,255,[]),(270,4,15,[131,115,99,83,50,33,16,64]),(281,4,15,[131,115,99,50,82,65]),(283,5,47,[133,117,101,16,64,49,32]),(287,8,63,[133,117,101,16,64,49,32]),(297,4,15,[130,114,33,97,82,65]),(299,5,47,[128,112,96,81,64,49,32]),(300,4,15,[130,114,98,49,32,81,64]),(302,5,47,[128,112,96,49,64]),(303,8,189,[135,50,65]),(311,7,111,[133,117,80,96,64,48,32,16]),(313,7,31,[131,115,65,50,98,81]),(315,8,63,[131,115,65,50,98,81]),(318,7,111,[128,112,96,49,64]),(319,11,191,[133,117,16,64,49,32]),(320,1,3,[129,113,96,81,64,49,32]),(330,4,15,[130,114,97,82,16,64]),(334,7,31,[131,115,100,50,33,16,80]),(347,8,189,[130,114,98,33,81]),(355,7,31,[131,50,66,116,99,82]),(363,8,63,[128,64,116,81,96,49,32]),(366,8,63,[128,16,113,65,49,33,96]),(367,11,191,[128,16,64,100,80,113,33,48]),(377,8,63,[128,81,67,112,97,32]),(379,11,191,[128,64,116,81,96,49,32]),(399,7,111,[101,134,117,33,48]),(420,4,15,[131,33,114,99,32,81,64]),(422,5,47,[81,129,80,112,97,49,64]),(427,7,111,[96,134,112,81,64,49,32]),(428,7,31,[49,129,115,67,32,97,80]),(429,8,63,[65,129,116,97,80]),(430,8,63,[49,129,33,115,67,32,81,96]),(431,11,191,[113,129,97,82,32,65,48]),(445,11,191,[129,82,97,48]),(447,13,383,[118,133,33,48]),(486,8,189,[115,83,82,130,99,66,16]),(492,8,63,[80,84,132,49,113,96]),(494,11,191,[64,132,49,96]),(495,13,383,[100,116,81,128,49,32]),(507,12,255,[100,116,81,128,49,32]),(510,12,255,[100,49,128]),(511,15,511,[]),(576,1,3,[145,129,113,96,81,64,49,32]),(579,4,15,[147,131,115,98,83,66]),(582,4,15,[147,131,115,98,83,32,64]),(590,5,47,[149,133,117,96,64]),(591,7,111,[149,133,117,96]),(595,7,31,[147,131,50,114,99,82]),(603,8,63,[148,132,67,115,64,83,96,32,16]),(606,8,189,[151,135,101,66,16]),(607,11,191,[149,133,117,101,64,48,32,16]),(615,7,111,[149,133,83,115,67,96,32]),(623,8,251,[151,135,101,66,16]),(627,8,63,[147,131,115,98]),(635,9,127,[148,132,99,64,83,112,32,16]),(639,12,255,[149,133,117,101,64,48,32,16]),(668,7,31,[147,131,116,66,49,32,97,80]),(670,8,63,[147,67,132,115,66,49,32,81,96]),(671,11,191,[151,117,133,101,33,32,65,48]),(689,7,31,[147,50,130,115,98,81]),(691,8,63,[147,50,130,115,98,81]),(701,11,191,[145,129,66,112,82,97,48]),(703,13,383,[149,133,117,101,64,48,32,16]),(710,7,31,[147,50,67,130,116,99,33,16,80]),(718,8,63,[147,131,116,83,32,96]),(731,9,127,[145,98,129,81,114,49,64]),(732,8,63,[144,80,133,113,96]),(734,11,191,[144,64,132,84,113,49,96]),(739,8,189,[146,130,99,33,65]),(742,8,63,[148,48,132,115,33,96]),(743,11,191,[149,112,84,132,96,33,48]),(748,7,111,[144,101,128,113,64]),(751,12,255,[149,112,84,132,96,33,48]),(753,8,63,[144,64,84,83,65,131,112,97,32]),(755,11,191,[144,64,117,65,129,96,49,32]),(763,12,255,[144,117,65,97,128,49,32]),(765,12,255,[145,66,112,82,129,48]),(767,15,511,[149,133,117,101,64,48,32,16]),(798,7,111,[149,134,117,49,64]),(819,7,111,[83,147,133,82,32,115,66,96,16]),(825,8,63,[149,131,82,48,67,114,96,16]),(827,9,127,[99,147,134,65,50,114,81]),(830,8,251,[151,129,97,81,16,64,49,32]),(831,12,255,[101,149,134,117,16,64,49,32]),(832,2,7,[32,144,16,130,113,96,82,65,48]),(840,4,15,[147,129,115,48,98,81,64]),(843,7,111,[150,97,128,113,80,65,33,48]),(846,8,63,[84,148,133,116,96]),(859,11,191,[145,16,133,33,112,98,65,48]),(867,8,63,[149,83,132,115,96,32]),(870,7,111,[150,97,128,113,49,33,64]),(873,7,111,[149,82,129,96,114,65,48]),(876,7,111,[81,145,80,101,128,50,113,64]),(878,9,127,[96,144,97,129,65,49,33,112]),(889,11,191,[151,80,84,66,16,130,97,48]),(891,13,383,[150,97,64,132,80,113,33,48]),(895,15,511,[151,101,66,16]),(910,7,111,[83,147,133,112,50,33,97,64]),(931,7,111,[101,80,150,81,128,113,64,49,32]),(934,7,111,[150,80,128,113,49,64]),(937,7,111,[82,32,144,81,129,114,65,96]),(939,8,251,[113,117,145,80,128,97,49,64]),(940,8,63,[83,48,144,84,132,50,33,113,96]),(942,9,127,[150,33,131,67,32,81,112]),(943,12,255,[113,150,129,82,32,65,48]),(952,8,189,[116,114,148,67,84,48,130,96,16]),(953,11,191,[117,149,80,66,130,96,16]),(955,12,255,[117,149,80,66,130,96,16]),(956,11,191,[116,112,144,67,50,33,129,96]),(958,12,255,[112,148,67,50,33,97,128]),(959,15,511,[118,117,150,133,33,32,65,48]),(974,11,191,[149,132,96]),(990,13,383,[64,97,148,84,129,49,33,112]),(991,15,511,[135,118,101,149,50,33,16,64]),(995,11,191,[81,80,82,145,128,98,65,48]),(998,11,191,[113,112,32,146,129,66,49,96]),(1004,11,191,[114,80,81,146,66,50,129,96]),(1006,13,383,[128,97,145,65,49,33,112]),(1007,15,511,[117,33,80,144,97,130,49,64]),(1011,13,383,[101,97,133,144,113,33,48]),(1015,15,511,[135,115,82,98,147,66,16]),(1016,11,191,[32,16,117,146,129,96]),(1017,13,383,[128,101,81,67,144,113,32]),(1019,15,511,[82,129,96,146,65,48]),(1020,13,383,[16,101,145,112]),(1021,15,511,[130,114,83,49,98,145,64]),(1022,15,511,[82,16,117,97,130,50,65,144])]
def fQ:=eJ wL l6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma jH:aX true fQ:=by
 apply gb wP;apply aH (d:=5);simp only [aW]
 repeat' apply And.intro
 all_goals decide +kernel
def wK:List dd:=[(511,16,511,[]),(895,16,511,[151,101,66,16]),(959,16,511,[118,117,150,133,33,32,65,48]),(991,16,511,[135,118,101,149,50,33,16,64]),(1007,16,511,[117,33,80,144,97,130,49,64]),(1015,16,511,[135,115,82,98,147,66,16]),(1019,16,511,[82,129,96,146,65,48]),(1021,16,511,[130,114,83,49,98,145,64]),(1022,16,511,[82,16,117,97,130,50,65,144])]
def ky:=eJ wK l5
set_option maxHeartbeats 0 in
lemma rC:aX false ky:=by
 apply gb wO;apply aH (d:=2);simp only [aW]
 repeat' apply And.intro
 all_goals decide +kernel
def ye:List (List Nat):=[[]]
def yZ:Array (bt × bt) := #[(0x22110041c0e0900d8da8126892098,0x6211004140c0800d0ca8106812018),(0xffffffffe2002209e1fe05810a886870a5d021,0xffffffffe0002209c1a201810800607024d001),(0x400006208f10a3014300a46230118,0x620851023004300806030018),(0x1c06041c1306d2043101220a004622,0x1c06041c1306d00411002208000222),(0x94001e06700a002e1141950560e8c,0x14001406000200220101850520c84),(0x1180e001a30004326061084188800,0x180e000a30000326041080180000),(0xffffffffe0ff4011e04826b102426781482061,0x24b40102048261002420780080060),(0x80fe0200015c0e4020c4a0821f14,0x880600000005c084000c420800f04),(0x11e0819c8080114884e1040950c002,0x1a08180808001c880a1000140c000),(0x1ff9e30400607c090d9019243044,0x101498a304018064090d0009243000)]
def CG:List aZ:=[(1,0,1022,0,15),(2,0,1021,0,15),(8,0,1015,0,15),(16,0,1007,0,15),(32,0,991,0,15),(64,0,959,0,15),(256,0,767,0,15),(512,0,511,0,15),(132,0,891,0,13)]
def yX (_:Nat):=0x8765432104bff
def CI:Nat->aF
 | 16=>(1,0,4,0,0,1,0,yX)
 | _=>a0
def CH:Nat->Nat->Option (Nat × Nat)
 | _=>fun _=>none
def yW:aM:=⟨1023,16,fun i=>yZ[i]?.getD (0,0),CG,ye,CI,CH⟩
set_option maxHeartbeats 0 in
lemma w6:aD yW (ai fQ)=true:=by simp only [aD,and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aH (d:=2) ?_⟩,aH (d:=0) ?_⟩<;>simp only [aW]<;>(try repeat' apply And.intro)<;>decide +kernel
lemma tW:aP yW 16 0 1=true:=by decide +kernel
lemma yY:bo yW 16:=by intro k hk;match k with|16=>exact tW|0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15=>rfl|_+17=>omega
def C1:List aZ:=[(1,0,1022,0,15),(2,0,1021,0,15),(4,0,1019,0,15),(8,0,1015,0,15),(16,0,1007,0,15),(32,0,991,0,15),(64,0,959,0,15),(128,0,895,0,15),(512,0,511,0,15)]
def Au (_:Nat):=0x8765432104bff
def C3:Nat->aF
 | 17=>(1,0,4,0,0,1,0,Au)
 | _=>a0
def C2:Nat->Nat->Option (Nat × Nat)
 | _=>fun _=>none
def Ch:aM:=⟨1023,17,fun i=>yZ[i]?.getD (0,0),C1,ye,C3,C2⟩
set_option maxHeartbeats 0 in
lemma yk:aD Ch (ai fQ)=true:=by simp only [aD,and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aH (d:=2) ?_⟩,aH (d:=0) ?_⟩<;>simp only [aW]<;>(try repeat' apply And.intro)<;>decide +kernel
set_option maxHeartbeats 0 in
lemma qb:cV Ch 17 0=true:=by decide +kernel
lemma Av:bo Ch 16:=by
 intro k hk
 interval_cases k
 all_goals rfl
def BP:Array (bt × bt) := #[(0x3fffffff000000000007fff,0xa29145228a45148a29145228a45148a2914522),(0x1fffc000000000000003fffffff,0x5908b2116422c845908b2116422c845908b211),(0xfffe000000000000001fffffff8000,0xa445488a9115222a445488a9115222a445488a),(0x7fff000000000000000fffffffc0000000,0xa1a1434286850d0a1a1434286850d0a1a1434),(0x3fff8000000000000007ffffffe00000000000,0x416482c905920b2416482c905920b2416482c9),(0xc000000000000003fff8000000000000000000,0x4c06980d301a6034c06980d301a6034c06980d),(0x1fffc0000000000000000000000,0x8037006e00dc01b8037006e00dc01b8037006e),(0xc0000000fffe00000000000000000000000000,0x1b8037006e00dc01b8037006e00dc01b80370),(0x7fff000000000000000000000000000000,0x31c06380c7018e031c06380c7018e031c06380),(0x3fff8000000000000000000000000000000000,0x3e007c00f801f003e007c00f801f003e007c00)]
def CP:List aZ:=[(1,0,1022,0,16),(2,0,1021,0,16),(4,0,1019,0,16),(8,0,1015,0,16),(16,0,1007,0,16),(32,0,991,0,16),(64,0,959,0,16),(128,0,895,0,16),(512,0,511,0,16)]
def z2 (_:Nat):=0x8765432104bff
def CR:Nat->aF
 | 17=>(1,0,4,0,0,1,0,z2)
 | _=>a0
def CQ:Nat->Nat->Option (Nat × Nat)
 | _=>fun _=>none
def BO:aM:=⟨5119,17,fun i=>BP[i]?.getD (0,0),CP,ye,CR,CQ⟩
set_option maxHeartbeats 0 in
lemma xX:aD BO (ai ky)=true:=by simp only [aD,and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aH (d:=2) ?_⟩,aH (d:=0) ?_⟩<;>simp only [aW]<;>(try repeat' apply And.intro)<;>decide +kernel
lemma wa:aP BO 17 0 1=true:=by decide +kernel
lemma z3:bo BO 17:=by intro k hk;match k with|17=>exact wa|0|1|2|3|4|5|6|7|8|9|10|11|12|13|14|15|16=>rfl|_+18=>omega
def BQ:List aZ:=[(1,0,1022,0,16),(2,0,1021,0,16),(4,0,1019,0,16),(8,0,1015,0,16),(16,0,1007,0,16),(32,0,991,0,16),(64,0,959,0,16),(128,0,895,0,16),(512,0,511,0,16)]
def xY (_:Nat):=0x8765432104bff
def BS:Nat->aF
 | 18=>(1,0,4,0,0,1,0,xY)
 | _=>a0
def BR:Nat->Nat->Option (Nat × Nat)
 | _=>fun _=>none
def wb:aM:=⟨5119,18,fun i=>BP[i]?.getD (0,0),BQ,ye,BS,BR⟩
set_option maxHeartbeats 0 in
lemma wc:aD wb (ai ky)=true:=by simp only [aD,and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aH (d:=2) ?_⟩,aH (d:=0) ?_⟩<;>simp only [aW]<;>(try repeat' apply And.intro)<;>decide +kernel
set_option maxHeartbeats 0 in
lemma nn:cV wb 18 0=true:=by decide +kernel
lemma xZ:bo wb 17:=by
 intro k hk
 interval_cases k
 all_goals rfl
def CV:List aZ:=[(1,0,1022,0,15),(256,0,767,0,15),(3,0,1020,0,13),(6,0,1017,0,13),(12,0,1011,0,13),(17,0,1006,0,13),(33,0,990,0,13),(132,0,891,0,13),(320,0,703,0,13),(528,0,495,0,13),(576,0,447,0,13),(65,0,958,0,12),(68,0,955,0,12),(80,0,943,0,12),(192,0,831,0,12),(258,0,765,0,12),(260,0,763,0,12),(272,0,751,0,12),(384,0,639,0,12),(513,0,510,0,12),(516,0,507,0,12),(768,0,255,0,12),(0,16,486,521,11),(0,128,347,548,11),(0,512,303,208,11),(7,0,1016,0,11),(19,0,1004,0,11),(25,0,998,0,11),(28,0,995,0,11),(49,0,974,0,11),(67,0,956,0,11),(70,0,953,0,11),(134,0,889,0,11),(164,0,859,0,11),(268,0,755,0,11),(280,0,743,0,11),(289,0,734,0,11),(322,0,701,0,11),(352,0,671,0,11),(416,0,607,0,11),(529,0,494,0,11),(578,0,445,0,11),(592,0,431,0,11),(644,0,379,0,11),(656,0,367,0,11),(704,0,319,0,11),(832,0,191,0,11),(1,2,952,68,10),(1,16,486,520,10),(4,2,952,65,10),(4,8,739,272,10),(4,128,347,544,10),(8,16,486,513,10),(16,512,303,192,10),(32,128,347,516,10),(64,2,952,5,10),(64,512,303,144,10),(128,512,303,80,10),(512,16,486,9,10),(512,128,347,36,10),(9,16,486,512,9),(20,8,739,256,9),(36,128,347,512,9),(65,2,952,4,9),(68,2,952,1,9),(80,512,303,128,9),(81,0,942,0,9),(144,512,303,64,9),(145,0,878,0,9),(192,512,303,16,9),(196,0,827,0,9),(257,32,606,128,9),(258,64,189,512,9),(260,8,739,16,9),(292,0,731,0,9),(388,0,635,0,9),(513,16,486,8,9),(514,64,189,256,9),(516,128,347,32,9),(520,16,486,1,9),(544,128,347,4,9),(896,0,127,0,9),(256,128,91,548,8),(84,0,939,0,8),(193,0,830,0,8),(276,0,739,0,8),(400,0,623,0,8),(69,2,952,0,8),(83,0,940,0,8),(156,0,867,0,8),(177,0,846,0,8),(198,0,825,0,8),(208,512,303,0,8),(270,0,753,0,8),(276,8,739,0,8),(281,0,742,0,8),(284,0,739,0,8),(291,0,732,0,8),(305,0,718,0,8),(332,0,691,0,8),(353,0,670,0,8),(385,32,606,0,8),(396,0,627,0,8),(417,0,606,0,8),(420,0,603,0,8),(521,16,486,0,8),(531,0,492,0,8),(548,128,347,0,8),(593,0,430,0,8),(594,0,429,0,8),(646,0,377,0,8),(657,0,366,0,8),(660,0,363,0,8),(708,0,315,0,8),(720,0,303,0,8),(736,0,287,0,8),(770,64,189,0,8),(848,0,175,0,8),(86,0,937,0,7),(89,0,934,0,7),(92,0,931,0,7),(113,0,910,0,7),(147,0,876,0,7),(150,0,873,0,7),(153,0,870,0,7),(180,0,843,0,7),(204,0,819,0,7),(225,0,798,0,7),(275,0,748,0,7),(408,0,615,0,7),(432,0,591,0,7),(596,0,427,0,7),(624,0,399,0,7),(705,0,318,0,7),(712,0,311,0,7),(785,0,238,0,7),(900,0,123,0,7),(912,0,111,0,7),(313,0,710,0,7),(334,0,689,0,7),(355,0,668,0,7),(428,0,595,0,7),(595,0,428,0,7),(668,0,355,0,7),(689,0,334,0,7),(710,0,313,0,7),(856,0,167,0,7),(992,0,31,0,7),(100,128,283,512,6),(193,512,302,16,6),(196,512,299,16,6),(289,16,198,520,6),(292,128,91,512,6),(324,128,27,544,6),(577,16,422,8,6),(578,128,281,36,6),(584,16,422,1,6),(769,16,230,8,6),(772,128,91,32,6),(776,16,230,1,6),(832,16,166,9,6),(75,16,420,512,5),(83,512,300,128,5),(102,128,281,512,5),(297,16,198,512,5),(300,128,83,512,5),(329,16,166,512,5),(356,128,27,512,5),(401,32,590,0,5),(433,0,590,0,5),(579,16,420,8,5),(582,128,281,32,5),(585,16,422,0,5),(610,128,281,4,5),(612,128,283,0,5),(721,0,302,0,5),(724,0,299,0,5),(777,16,230,0,5),(780,128,83,32,5),(804,128,91,0,5),(808,16,198,1,5),(808,128,83,4,5),(836,128,27,32,5),(864,128,27,4,5),(176,5,832,10,4),(182,1,840,0,4),(211,512,300,0,4),(214,512,297,0,4),(241,512,270,0,4),(409,32,582,0,4),(436,8,579,0,4),(441,0,582,0,4),(444,0,579,0,4),(587,16,420,0,4),(614,128,281,0,4),(693,0,330,0,4),(723,0,300,0,4),(726,0,297,0,4),(809,16,198,0,4),(812,128,83,0,4),(841,16,166,0,4),(868,128,27,0,4),(913,32,78,0,4),(916,8,99,0,4),(924,0,99,0,4),(945,0,78,0,4),(402,5,576,40,3),(56,773,0,194,2),(74,773,0,176,2),(82,773,0,168,2),(98,773,0,152,2),(146,773,0,104,2),(152,773,0,98,2),(168,773,0,82,2),(176,773,0,74,2),(178,69,0,776,2),(194,773,0,56,2),(306,517,0,200,2),(312,517,0,194,2),(330,517,0,176,2),(338,517,0,168,2),(354,517,0,152,2),(394,517,0,112,2),(402,69,0,552,2),(402,517,0,104,2),(408,517,0,98,2),(410,5,576,32,2),(424,517,0,82,2),(432,517,0,74,2),(434,5,576,8,2),(450,517,0,56,2),(658,69,0,296,2),(658,261,0,104,2),(666,5,320,32,2),(690,5,320,8,2),(696,5,320,2,2)]
def CU:List (List Nat):=[[],[115,84,152],[32,83,116],[32,67,117,152],[128,97,146,67],[144,97,130,117]]
def Af (_:Nat):=0x1be02140418c062b410100c40168201a00258403400558806180bb010a01b08030405f0807000850106301bc0268403600438071180ca018a201be021c0388c05b8091100b601220238603440428072180c9011c201b20348403480578806480a2100e000e201b06039006088073008e00e63019202884032004d8806d80b0100d0016e201900314403200558806f00a1100df010a020c602ec0b90807280c500e201b0803800488087180d8010a01b06030405f8806800b3100db016e2018202d8403240608807080e0100df012201b0602ec0b908073808700e2301b802100388c05d80a8100dd013e201ba02f0403a805508074008300e2301c002e0403600498087180bb013a2018202a44034004a8806d80ca100e90184201820278403500670a3a231628a1fe17206dfe1f19e8ddc5d39c71be5b1da559c993d8b182575d6d160957d4f14653d934d2c123516d0e0fdcf14e4cdc0d34ca8c1cb90b04a3c9b08e882079470867c5f052849c3d43482bc2301a411808c00303fefebd56e372ba10c10507fdfafb5dc6e57421820a8f7bf56e3a8dcae843041c1efff5ca751b95d08608383df6e394ea372ba10c10683fffe7b1b96a17421820d877dd8f2372d42e843041a1bfff9ec6e5a65d086083635f763c8dcb4cba10c10687bffe7b1b96917421820d8b7dd8f3b72d22e84304191f77e5eaf65746cc86082a3eefd7d2ecae8d990c10743dff9765a85d1b321820e8bbff2ecb4eba3664304171777ebd965d746cc86083a2eeed7b2cbae8d990c10745dff9769975d1b321820f83bfb2d432eba36643041d1b7fe5d9699746cc86083e26fecb2ed32e8d990c107479ff9765a45d1b321820f8b3fb2cbb48ba3664304171e77ebd9651746cc86083a3ceed7b2ca2e8d990c107479ff9769945d1b321820f873fb2d4328ba36643041f167f65a7651746cc86083e34fecb4cca2e8d990c10647f5f97abd95d1b121820a8febf5f4bb2ba36243041d0fdfe5d96a1746c486083a37bfcbb2d32e8d890c10747b7f9765a45d1b121820b8f6bf5ecb28ba36243041d1ed76bd9651746c486083a3dbfcbb4ca2e8d890c107c3b7d96a1945d1b121820f8b6fb2d3b28ba36243041f1adf65a6651746c48608323fcfcbd5ecae8d810c10547f9fafa5d95d1b021820e87f7f2ecb50ba36043041d17efe5d969d746c086082e2fcfd7b2cbae8d810c10745f9daf65975d1b021820e8bf7f2ed32eba36043041f07ef65a865d746c086083a37dfcbb2d32e8d810c107c4fbd965da65d1b021820e8f77f2ecb48ba36043041f16ef6597691746c086082e3dcfd7b2ca2e8d810c10747b9daf65945d1b021820e8f77f2ed328ba36043041f0eef65a8651746c086083e2ddecb4eca2e8d810c107c6bbd9699945d1b021820
def Ag (j:Nat):Nat:=(if j<2 then (if j<1 then 0xfa5d95d1b121820d3fd769d95d1b121820f2fdf65a85d1b121820f2fd765a85d1b121820f3bdf65a65d1b121820f3bd765a65d1b121820f3edf65a45d1b121820f3ed765a45d1b121820f5edf65945d1b121820f3ed769945d1b121820d3fe7abd95d1b021820b3fe7abd95d1b021820d3fe76bd95d1b021820d3fefa5da5d1b021820d3fe7a5da5d1b021820d5fefa5d95d1b021820d3fe769d95d1b021820f2fef65a85d1b021820f2fe765a85d1b021820f37ef65a75d1b021820f37e765a75d1b021820f57ef65975d1b021820f37e769975d1b021820f3bef65a65d1b021820f3be765a65d1b021820f3eef65a45d1b021820f3ee765a45d1b021820f5eef65945d1b021820f3ee769945d1b021820a1ff7abc96e57421820a1ff7aadc6e57421820e1ef729d46e57421820e0fff25b96a17421820e0ffbb1b96a17421820e0ff7b1b96a17421820e0ff725b96a17421820f0ef791b96a17421820e1bff25b96997421820e1bfbb1b96997421820e1bf7b1b96997421820e1bf725b96997421820f1af791b96997421820e1eff25b96917421820e1efbb1b96917421820e1ef7b1b96917421820e1ef725b96917421820f16f79db96917421820e1ef729b96517421820f0ef6e5a86517421820f16f6e5a76517421820f1af6e5a6651742182093f77abd95d1b321820d2f7f65a85d1b321820d2f7765a85d1b321820d377f65a75d1b321820d377765a75d1b321820d377769975d1b321820f2776a1975d1b321820d3b7f65a65d1b321820d3b7765a65d1b321820f33765da65d1b321820d3e7f65a45d1b321820d3e7765a45d1b321820f36765da45d1b321820d3e7769945d1b321820f2e76a1945d1b321820f36769d945d1b321820f3a7699945d1b32182093fd7abd95d1b121820d2fdf65a85d1b121820d2fd765a85d1b121820d3bdf65a65d1b121820d3bd765a65d1b121820d3edf65a45d1b121820d3ed765a45d1b121820d3ed769945d1b121820f2ed6a1945d1b121820f36d69d945d1b121820f3ad699945d1b12182093fe7abd95d1b021820d2fef65a85d1b021820d2fe765a85d1b021820d37ef65a75d1b021820d37e765a75d1b021820d37e769975d1b021820f27e6a1975d1b021820d3bef65a65d1b021820d3be765a65d1b021820f33e65da65d1b021820d3eef65a45d1b021820d3ee765a45d1b021820f36e65da45d1b021820d3ee769945d1b021820f2ee6a1945d1b021820f36e69d945d1b021820f3ae699945d1b021820c3bdf73c6699b126020c3bdf1bd1699b126020c3bdf72dc699b126020b3b578cdc699b126020c1eff73c96a5b421820c1eff27d46a5b421820c1efb73d46a5b421820c1eff72dc6a5b421820b16f79cdc6a5b421820b1cf794dc6a5b421820b1e778cdc6a5b421820b1ed784dc6a5b421820 else 0x11e8222818c04880bd412100d5023806560888063811c032b0444031c08e01958222018e04700cac111008c01b806a1811603500c83033c0910190606b0408e018005c1811c02f0072302380620180604701140300c0910188404880be2024408a101220450ac52afe6b92ad8eb18ab6ea9ea9869faa6be964a49e8dca27e854a0967e89e767289b766a0998e61896c656694a64ec928643a8fbe3b28dd63388b7e29489261fe8706168843e0c4821e04a8035fc27dddf1e7b85ea4799de1c777dda27595d2873adca0718dc186f35b906d4db166b2da8068659dc667d96264958e862ad86e608d7e65ea576c5cbd6e45a65640580d5c6562554c543d4c4521d44a50353c24e1533a4bbd2b249d523847ed1be460513643e50bc41fd0423fdcfba3dbcf243b64e8e3944e0636ecd703494ce832acc6e308cbd82e6cb5e2c84ae42a9ca5c28449d4265c95a24748e0228c86620a47ec1ebc7641c646dc1a7c66218945e816ac56e148c4d8126c45e10843e40e9c35c0c442d40a5c25a08741e006c4182054c14004440e202cc084018c0420084000c9ff7a5daf257421820a9ff7abd97257421820e1ff6ebd97257421820e1ff7abc96e57421820b1ff7abc96e57421820e1ff72bc96e57421820e1ff7aadc6e57421820b1ff7aadc6e57421820c5fffb5dc6e57421820e1fffb5ca6e57421820e1fffa5ca6e57421820e1ffb71ca6e57421820e1ff7b5ca6e57421820e1ff771ca6e57421820e1ff7a5ca6e57421820e1ff729c96e57421820d5efb71d46e57421820f1ef729d46e57421820e8fffa5c96a17421820f0fff25b96a17421820f0ffbb1b96a17421820f0ff7b1b96a17421820f0ff725b96a17421820e9bffa5c96997421820f1bff25b96997421820f1bfbb1b96997421820f1bf7b1b96997421820f1bf725b96997421820e9effa5c96917421820f1eff25b96917421820f1efbb1b96917421820f1ef7b1b96917421820f1ef725b96917421820b9ef7abc96517421820e9ef72bc96517421820f1ef6ebc96517421820e9effa5ca6517421820f1ef729b96517421820f8eff25a86517421820f96ff25a76517421820f9aff25a66517421820d3f77abd95d1b321820b3f77abd95d1b321820d3f776bd95d1b321820d3f7fa5da5d1b321820d3f77a5da5d1b321820d5f7fa5d95d1b321820d3f7769d95d1b321820f2f7f65a85d1b321820f2f7765a85d1b321820f377f65a75d1b321820f377765a75d1b321820f577f65975d1b321820f377769975d1b321820f3b7f65a65d1b321820f3b7765a65d1b321820f3e7f65a45d1b321820f3e7765a45d1b321820f5e7f65945d1b321820f3e7769945d1b321820d3fd7abd95d1b121820b3fd7abd95d1b121820d3fd76bd95d1b121820d3fdfa5da5d1b121820d3fd7a5da5d1b121820d5fd) else (if j<3 then 0x802ec28f01e82500130c068052003d00d601e140c80a3c08e09ac05c281b614800f603580d25032009109bc05820188060011e03d00d6034980c7031008f01e806b01a4c070051e03d04d601e140c902e809101708063017404880ec403140b302380382019005f81220450082503240a1024406c00e0a0648142044810e03880b8603240c5024404120176058812203b100c8028c08e02148062816a04700ce022940c9030407101b08064818204480b8403240c1024405c201c8071012202a900e0031c091020c8063818803880a6022940c8031008301c48064018404080e4020940c80310071017003d2817605700d801c100ba02cc0710178806201620388082403180bb02380710170a060814e047011001c140c402f8087021408201c80453818e060811c02e100c602ec09101e0806401840470110403880c701fc06c201c0052010a036100c902e806c01048064014604700e2403200c201c80560104a06581820470082403140a001b005c2019005d011c042900c502d408e0114805d816a047011a01c140c1029408e01c40452818e05d011204400d802e180c903100710114806b815604700b64039c098024406c2018a05f8122022900c6030808301c48064818204080e4022940c9031407101708070018403f00d8403a0094021406c2018c05d012202a8082503200a302380732019005c811203900b8503240c1024405c0160a0488098a1228444024408e5091422201aa04700caa111009101a64249088804880d921248444023808890924222012204180fb21248445031c08e01964222011c035c8492111009101b242490888048811d21248444024408e01664249088a063811c032c8444035408e01ac0659088a071812204700cb211140e3023808501964222818e047008e196484450318091017a424201c604700f603298445031c08e01bc0653088a063811c03280b4611140c702380650164c22281220363048c111009101b2824a0888047010b4125044402f40910238032a090a06d0122041807b412140da024405e60908066012282f304840238071a0928222011c038d049411100ac024605ea090805f011c03880cb411140e30238051011e82228138048c0bd412100e3023806560888063011c832b044402b408e41958222014804720cac111009101b182460888048811d41250444024406ca09282220122047504941110091023a824a0888060011c038808f411140c7024c08e011e8222818e04700cac11100c7023806560888063811c032b0444031c08e0195822201220473048c111009101b2824a0888048810f4125044402fc09101b0049a090a06d01220438093412140cf024405e60908075812202f304840238071a0928222011c0445049411100c6024405ea090806a812204700cb411140e3024c08e0 else 0x1be048851e03d84a001d0450702ec29001ec2690139c2430174147810603884d601a3a02702ec08009406062811403884d2128140bb024426b09a48062016e04700704031c0bb021406c20176052012204181020390030703100b4023805c0150a05d811003604d2128140c9031408e00d48064818804880d8021940cd030808e01148060815c047010a137940c80a3c08e1818e05d011202e100c9030408301c405c2818e062051e04280f41358060114200bb01c4269018024e2818806000d8025900c20290091020c806101320488520043940e00a4007a01b026900cc22b381c00488100134809c5034c0b301c4042201c0052011c042900d30318091020c07a281b0147810c03d00d8135806070310091020c26b09a4a06381880470082403200c202380712018204b810e196100c))
def Ah (j:Nat):Nat:=(if j<3 then (if j<1 then 0x317ff92d436843041cbbdc96a1b421820a7dfed38eda10c1063ef729c76d0860838f7b52e3b6843041cbbda871db421820e75fe4b4cda10c1063bff25a66d0860839d7f8ed3368430418effc7699b421820e75ee4b4cda10c1073af71da66d0860821fffb2e5b48430410fffd772da421820c3feee372d210c1071ef751b9690860831bfbb8dbb4843041cdbdd46dda421820a7dfecb68d210c1053eff5db4690860821ffbb8dd3284304187fdca6e59421820a3feedb52ca10c1061ff72da96508608317fb96d432843041c3fdb96a19421820c6fee536eca10c10717f6a5b76508608393fb50dbb28430418efdcb6999421820e37edcb4cca10c10733f6dda6650860831f7b94da32843041c7bda96d19421820e5ded4368ca10c1073af699b4650860829f7bb6d2328430418fbdcb6919421820e3dedcb48ca10c10736f6dda4650860821ffbb5e5ae8430410ffddbf29742182087ffed396ba10c1043fff6dca5d0860821ffbb8dd2e84304187ffca6e57421820c3fee5372ba10c1061fff2da95d0860828ffbb6d4ae84304187fdcb6a57421820c5ffe5b50ba10c1062ff72da85d08608387fb72d42e8430418effcb6997421820c77ee5b4cba10c1071bf6e5a65d0860831f7f94da2e8430418fbdca6d17421820e3ded4b68ba10c1072ef6a1b45d0860839d7b4cda2e8430418fbfcb6917421820a7deedb48ba10c1063ef72da45d0860838f7b72d22e843041cdbdb76917421820e3efebb52d990c1053f7f5da96cc860838fbfa8d4b66430414fdfd46a5b321820e3eeebb52d990c1071f7751a96cc860829fbbb4cbb6643041c7dda965db321820e5eed432ed990c10737769d976cc860839dbb2ed3366430414fddda651b321820e3eed4b28d990c1072f76a1946cc860839dbb4cca36643041cf9da4651b321820a7efed2e8d990c1053f7769746cc860838fbb52ba36643041cbdda85d1b321820e6eed3ae8d990c1073b7699746cc860839f3b48ba36643041c7f7d46a5b121820a7fbea352d890c1071fd751a96c4860829febb4ca36243041c7f5a9651b121820e5fad4328d890c1073bd699946c4860839f6b48ca362430414ff7da5d1b121820a7faed2e8d890c1071fd6a5746c48608397eb50ba36243041cef5a65d1b121820e7dad22e8d890c1071fef5da96c0860829ff7aed4b6043041c7fbd46a5b021820a7fdea352d810c1071fe75da96c0860838ff3a8d4b60430414ff9da65db021820e3fcd4b2ed810c1072fe6a1976c0860839bf34ecbb6043041cef997699b021820a7fced328d810c1071fe6a5946c08608397f350ca36043041cef9a6651b021820e7dcd2328d810c1053fef69746c0860829ff3b4ba36043041c7f9a95d1b021820e5fcd42e8d810c10737e69d746c0860839df34cba36043041cfb9a45d1b021820 else (if j<2 then 0xe6feecb6ed210c10737f769b76508608397fb50dbb28430414ffddb69d9421820c7fee5b4eca10c1071ff6e5a7650860839bfb6ed3b2843041cefdb76999421820e7ded3b68ca10c1073ef6dda4650860825ffbb5e4ae8430418ffdbaf257421820c7fedd392ba10c1065fff25b95d0860832ffdb8dcae84304197fddc6e57421820e3fee5372ba10c1063ff729b95d0860832ffb92dcae843041d7bdd46e57421820d5ffe4b50ba10c106aff725a85d08608397fb72d42e843041aeffc96997421820d77ee4b4cba10c1073bf6e5a65d0860835f7f92d22e843041afbdc96917421820e7dedcb48ba10c106bef729945d0860839f7b74ca2e843041d7bdb96517421820f5ded4328ba10c107b6f69d945d086083dd7b4cca2e843041cfdd97691b321820e7eed3b28d990c1057f7f65746cc860839fbbb4ba366430415fddd95d1b321820eeeecbae8d990c1077e7651746cc860839feb4eca362430415ff7d95d1b121820e7faed2e8d890c1057fd765746c486083bf6b28ba36243041cff997691b021820e7fcd3b28d810c1057fef65746c0860839ff3b4ba360430415ff9d95d1b021820eefccbae8d810c1077ee651746c0860829febb5e33624c0410ffddaf19b126020c7fae578cd89301053fdf59ca6c4980831feb94e33624c0414ff7dc699b126020e77be334cd89301053fdf45a66c4980839dedb8d33624c041cef5dc699b126020a7faee34cd89301073bd719a66c4980839de9b8d33624c0410fffd672da126020a7fbeb362d09301043ff771ba584980831feb94d8ac24c041cef5a66c56126020a7faedb42b09301063fd72da1584980839deb6cd0ac24c041cefbd1699b026020a7fde8b4cd81301073be745a66c0980829ff3b4b0b604c041cbf9a8585b026020e77cd32c2d81301073fc685616c0980828fffa8e53724304187fdca711b921820a3feedf88d490c1043ff76fc46a4860830ffb97e23524304187fdb9f11a921820c3ffea396d490c1051fff51cb6a4860821fffa8e5b524304187fdd472da921820c3fee5b88d490c1070ff751b96a0860838dfba8dcb4c430414fbddaf25b42182087feed792da10c1063ef72bc96d0860829f7bb5e3b68430410ffddaf1db421820c7dee578eda10c1071ef6a7c76d0860830ffb53e3b6843041cbbda8f1db421820c5fed478eda10c1053eff65ca6d0860829f7faee5368430418fbdca725b421820e3dfee352da10c1053eff71a96d0860838f7f92d4b684304187ffc96a5b421820e3dfebb52da10c1053eff5da96d0860838f7fa8d4b68430414fbfd46a5b421820e3df6e352da10c1061ffb71a96d0860838f7bb8d4b684304187fddc6a5b421820a7deee352da10c1071ef725a96d0860838f7baed4b6843041c7bdd46a5b421820e3de6e352da10c1072eff25a86d08608 else 0x22088605c412208903e4036010504882240f981cc0a702e209104481e201b00ca0624112078c0e6053824411a05e412207cc0e6053823811406502e208903c6073823811a05c3039012205c812181c80910470228082205282380b90221029012205c8120c11c0458110c1220414120c12205c4120c1220604122088809141220886091036409204440470115044304701710443047012d048822202380968244111011c8244110c0b88244112078809101c209104481f3038814e05c412208903c404701a00ca82240f181c40a704881980bc05c412207c40a703881980bc82440f981c40a704701940c405c4112078c0e79901304e5d34b469599294a4e5c96b9217227a425c7eb8ee31c4635246378baf15de27ec49088610f421bec31d859509aa10bc1b782e3051608cc0e08135018600dbfe27f38fd59f8ebee47d56f8f9ee8bd647a08f291e223bca76a0eb8dd41ba167352e4f1c67b8626feade21b8db6ae6c68d751ab3b4fa6900d0199e0337a664ecab5926b1ed631ac51d87a307a6034bee97ba2f2e5db6b9516fa2d945a68b3ed6612c7c5886b0295e8ab9856beac99576aab454f6a86d4f1299c52c6a4a9478a8b850fea11940027ba4f029d21387a6d64d3a999131c25ff4b8c96352aa251b49c492a523ea45148308f7d1d3236d464e8bb915aa27c446c87f50dba17e428a846507020b44110813d00b1fdd3f487de0fa61f133db47ab8f411e563c5477f8ee91d653a3e7364e501c67385c6fd4dde1b7636606ba8d589a78347e6818ced19ae33046524c8818ca313c61c8c23181a2fdc5ed4bbe17502e485bacb5916792c805850af415af2aec54f4a8214d8293e51cca1d140127aa4e709b1930325ae4a789329239240046808ba113b21b6428883490301fee3ef87c90f591e403b007438e4e1c2a37706d18d771a96347c6798cba191c31546148bfd17882e2c5af8b26158c2a3451689cd12da243446a089b10de210c40b87de0f4a1de43a006e00d4e191c2f385870a9c1454267849608d410f820903e6075a0e041a4031c05e00adc13f0252043206e40c00120018001800006bff76bc95d086082dffbb5e4ae843041affdcaf257421820e7fedd792ba10c106bfff65ca5d0860835ffbb2e52e843041b7ffd97257421820d7fee5392ba10c1073ff6e9c95d086083afff92dcae843041d7fedc6e57421820ebfeee372ba10c1073ff729b95d086083affb92dcae843041ebffc96a17421820f5fee4b50ba10c107bbff25a65d086083ddfb92d32e843041efbfc96917421820f7dee4b48ba10c107deff25945d086083df7b94ca2e843041dfdfd95d1b321820efeeecae8d990c1077fdf65746c486083bfebb2ba36243041dffbd95d1b021820effcecae8d810c1071ff75db9690860839bffb2dbb48430414fffd96dda42182)) else (if j<4 then 0x120809104702301164048823811808b202301160744141011c08c0272088808e02e4088c0a404701150443047010d045205202380b88229029012208a02188a0808e021a08803440470172044a05202440790245029011c0438112814808e022c088608e01ca088608e02dc09204440470196049022202380c404f4111011c08a01d2088808e031017807402d2823811a08a3039011c08d04500cc808e0468228c0e404701940bc04a3039411c06b411181c808e04681940bc607282380d68223039011c08a0300170808e045181c608e018209104440470172044304701720443047013008b022202380d20438111012205c812181c809102e4090c0e4047017204430470172044304702280bc05c202381140438111011c05c8110c11c0458110c11c05c8110c11c0458110c1220418120c11c0458110c12208a012008803c10a3038815008e031017809890a2823811404c8112428a08e034c092044402e00f104881f201a504881f303900b803c41120788069412207cc0e404701a40c40600851411c08a034c088214504701a00ca0603039411c06b811181c808e01840920444034c09203e607202380c405e0219011c08a0198c11c0438110c11d0248110c0d60688114078806b021408a03c404701880c004f0171411c06b02f8c11c05c2110c11c0392110c11c0432110c11c0452110c11c0692121088808e03310908444047017084430470114844304701ac0ca422202380984242111011c04b2121088808e03581948444047011484430470114844304700c0848422202380604242111011c0342121088808e01e109084440471090844304701ac08e4222024084441f181c809842220f100b803e2111078808f21210786069019909083e4039109084441e201c484842220f806140ea053823c84841e1817084842220f900d205c212107c8090211107c606b018108883c404882280bc42420fc81e40a7047909083c3034813884841f2023811a065211107a40f205381c809842220f100d205f212107c806902e109083e4034909083ea07201a484841f5039012042220f8c0d242420fc81c8069027109083e404501b00ca045211107a40e704501ac84441e202440b90243039012205c812181c808e02e4088c0a4047017204460520244083024182380b9022182440b8824182440b8824182440be824411101228244110c12208a8124088808e022a088608e022a088608e02da09104440470195048822202390488221817104882240f1011c038412208903e6073029c0b8824411207c807103000f504881f3039814e08a038817808282440f9814e08e046819504481e3039814e06c033819408a82240f181ce08e02e4088c0a40470172044605202380b9022182380b88221823808a8221823808c8244111011c04b4122088808e41 else (if j<5 then 0x503a81520c906402441120830228cb0e0c706201f00f607603889ac098806082cc51e07111f00f04510204039451e08003d81c40d60693838012228f02608f8451020382e816407c03d01c44d605e02280d120c104c8a3c10a26b01808a2034806081ec4d604101e0cb3a0270640a3c11c26b02280c00347062030011c0890388170c0c905302381121720388104e0c605d824411208302e181840a6048823811217202e1c1800ba04481b00b804b3032414809104702242e40453824411c0438124088a08e0468138608e04681ac608e02880fa044404881b00a04242111412206c0359088809103600ec848422282440ea0692121012208e01c9090844504881b00d64242111412208e0359088809103680f0848404882380d64222024412006c0278139848c224102012206f036013c09c0386123089008e03901c40d605c02630918448048817009812aa12408e844704701c80e20382175092844704701c80e3424a11006082a706482280d8065022908883ca07502a411c06f02780d484842200ba81d40a904881c80e006c022d092047422402380e405c096d0928440113824412008e03581a684942280d2011e08e03881ac079424a114081008e03801a409c424211481e40a804782380e206b026509284501a4024011c08501e00ce8494228102011c05902700c0848422903c815009104782380d604ca12508a0408048823c11c06b02650928450204024011c06b034019408a422903a012008e13581ac0ca0346123088034904701ac0b822b6123088012704701c80de05c096b090046c224024011c06b01e08ad848c2200d2012008e13581ac0d20656123088034904802384d606b0348195848c2200d2412208e01c4092044504881b00b88244111411c05c41704b70498223032411c067032810504481e3039815209104701c80b9824c112054e09102e00b4255824c110048e08e02e04b4055824c110044e09103600e1048822282380b812dc12608a024606102380cc05e022a09103e607302a412208e03901730498228089c11c05c09680ab048023c111c11c071020c092044504882380828244111411c05c096e0920478223030412408e02f817808a82440f981c40aa04882380e405cc12408f0447048817005a12a013e0930447047017025a02ac12008f0447047023011682b2022c0c203f4141012208b03500fc04c504882300ba03f2024411c02f4111012208b0244090809104700fe048404581d00e30282024411606102b9011c08c04580bc809104702300804047023005f02b2022e05702881200882102023824411c08c01b9012208e030817405c504882381180372023811803f2159011808b03a10a0808e04600c48444047023005e42b2024411c08c0459012208e0318134404504581c40910281011412208e0460 else 0x6201f00f626b0260105844705d02c811007c03d81b04d60694031016407c03d01c44d60380182019008e03889c04d606902e1c1840b114801ec0d824f02700e045690608a400e206c029093808a03c80d2417a0bb047822410607b03881ac0d205c5032452008e035810447881a3832051e08e038810447c0303831818a09104481e409c04101e2017e0bb04481dc0e20453032012e09104485c80d805c3832418206c02d00e806a033)))
def Ai (j:Nat):Nat:=(if j<1 then 0x4804403d214c0ec0a602402201e10a607605301201100fb039029409008807e42981c814c04804403e214c0e40a69dca7019aa2643971a53192a241f8e5a3498bf22c789ea215872217b84ba0e182520477fe9f897c91efb7a29e257701d737499cf17261c336f99b996ca1acf6979a116711953638988960617bf5d697195ad1667571954953614734f793494bf125b48391c1454110342490453fe0f873ce8ee13a20e2f3758d8934c0ce331f8c252f60b8b2cc8acd29d0a0f26a894523e08ab21187ed1e807531be86ad195060716e858514e04f7130848d11304170f283950d203130b48291094020306d817504a00db026804d0003ffff257421820fffdc95d0860837ff6dd9421820effda765086082ffff257421820effdca5d086082fff7257421820dffdb95d086083fef6517421820dff7c66c4980827fff19b126020cffdca6c4980837fd719b126020cffda66c4980833ff6d9a126020affdca584980833ff6e96126020dff5b158498083bfd6856126020dff9616c0980835ff711b921820e7ffc46a486082bfff11a921820cffdcb6a4860839ff711a921820dfbfc96d0860827fff25b421820dfbfc76d0860827fff1db421820cffdca6d0860837ef725b421820cffda96d0860837ef71db421820cffdb9690860833ff6dda4218209ffdcb65086082bff7299421820cffdba650860835ff6e59421820e7fda965086083aff6a19421820ddfdb765086083bbf6999421820dfbdb465086083bef69194218209fffcb5d086082bfff2974218209ffdcb5d086082bff7297421820cffdba5d0860835ff6e57421820e7fda95d086083aff6a17421820eefda65d0860837ef6d17421820efbda45d0860837f765db321820dfdd946cc860837f75d1b321820dff5946c4860837fd5d1b121820dff9976c0860837fe651b021820dff9746c0860833fd729b126020cff5a66c4980823ff72da126020cff5b1684980833fe699b026020cff9a16c0980831ff729b921820c7fdcb6a4860823ff72da921820c7fdb96a4860832ff6e5a821820cefdb9698860833ef729b421820cfbda96d0860831ff6a5b421820cbfda86d0860833bf699b4218208ffdcb690860831ff6e5a421820cdfdb7690860833ef6d1a421820cfdda96cc860833f769db321820cfdda46cc860833fd6a5b121820cff5a46c4860833fe6a5b021820cff9a76c0860833fe691b021820cef5a66c4980832fe6a1b026020cef9a66c0980821ff72ab92182087ffcb6a4860821ff72da921820c3feb96a0860830ff6e5a821820c6feb9698860831bf6e5a621820c7bda96d0860832ef6a1b421820cebda66d0860831f76a5b321820cbdda86cc860833b7699b321820c7f5a96c4860832fd6a1b121820cef5a66c4860831fe6a5b021820cbf9a86c0860833be699b021820 else (if j<2 then 0x8846045a14012806182442382300a508803cc12211c11884403c006609108e08c02582200a304709681541241100a982440ac8a2092088074070068815211c45704904403a03603440a808e045022184702e01581441241100e80e00d242382281301140b80aa088429011c0c409808605504402a214808e06202a0278226073047035815011c11303982382281a4088811c0b809805504904402a708e05c04c02201401110a2054034816c1240f808b03982380b409008a81e814c11c0d608a04804403e01c40f40a908e05c04c02e02a424422384702e01581421221100e80e00d242381980ac0a9091088c11c25a054848046844608e04502b02842442201d01b01a484703381581421221100e80d80d242381ac4b40a909008d088e11c08c05605084884403a036034908e05c04c02a424023422384701581421221100e80e00d2023c0b1091079020a0e405884884404283c036034806b06902d02342241e302c82281b11401421221101081020f00d903902b417013c0b04a809d09108907c81c81540b825405484884483e02540f40a905c02842442202141e01b01a402d02611401421221101081020f80e103902b02400f88a00a109108808507c06c06881c81580d205a84883e02340e604504403e02b22842442202041e01d01b207205684881689541241100a982384b40aa09008e088c0b825405504904503e024c0ec0a908e12d02a824822015302e09501541241140f009303b02a42440b44a809e092088c11c05c25a055049044605c12d02a82482281e0126072054846016815814012011182300ac0a009008803c420e11805605004a048044404708c02b02a02802402220338488158140120110851011c0ac0a009409008980cc0b804804403c214c0ec0a705c02402201ea07a05302181601201100f885503d02a010c09008807c42a81e814e04804403ca1540f40a602402201e10aa07a05304702789501201100fb039c1c41a44a809008807c42981d00b805604804403cc0e40a706c03c02402201e90a607205403603481201100f885303902a01a41604a809008807e81c815025404804403f40f40a612a02702402201fa05304701a01201100f005503902a017009008807c42981d814e25a04804403cc0ec0a612a02402201f607605302e01201100f885303b029c4a809008807d81d814c0b804804403c214c0e40a712d02402201e607205309501201100f303902980ac0a00900888056050048044210404602b028024022202281581201100f900ac090088078804804403d40f40a502b02802401e201201100f285503d02980a0090088078804804403e21540f40a602402201f607201201100f4853039409008807842981ca04804403cc0ec0a502402201e90a607605301201100f885303b029809008807981d814a else 0x6205f04103d03582e01e09699611428320244a402382241a41140fa069211c0e40d60b825a84402a709109008f05c22842442201a404884803482e02709561261140d40928244a4023c1ac10509108907806805881c815812211e11c0e40d20b807d84984503482ab09107004303e03c12a424422011a07a05584804703902e02701e096e1261100d008ac22c1b81840a60a0420c1221160c305004a214609105d02f0242048846045817014c141824423823022c0a403042080d012211c118116052032609108e08b42401e00c304))
def Aj (_:Nat):=0x9111c2301482584407c0f204712d0560a8144248440740d81a022b11e1701982d4560ae1242283c0740d81a02281d02bc4582b0520a0128240444210124158280480880f00a40670480880f81502203885607c0a90b80ac1402404407c8520700c8140200260690b00b41502404407c85008c0e81564a8140240440790380700c81402003582b0500901110801080c01a0158280480880790a01402100ac140250480888500a40400520ac140240440780500838240440788500a40e8140220168240440780890a01402303e0550280480880f20700e0190280500800960901101f0274290380700c81402804004c0480880f81421481c0380640a0140200260240460880f01221402804607482a0480880f00e21402804607c0aa04e0901101f01a42805008c0f81540b41502404407c8500ac0e81400aa59239a0f1f51e09c69a4584d6554e136d1cd084f10d44b4c9287045643981cc003ffeb0930107ffd9421820fffae8430417ff6c4980837fed0930105ffdb921820dffb52430417ff6d0860837fed210c104ffdba26020bfeb624c0417fe6c098082bff5c90c104ffdba21820affb72430419ff6a4860835fed410c106efda621820bf7b68430417f76cc86082ffad890c105ff9b021820
def Ak (_:Nat):=0x2b0a4280902202c094200880c030098168481103c0981a850150380e0340a02808010030a500fff26020fff21820
def Al (_:Nat):=0x70301408030019ffc20
def Am (_:Nat):=0xa12024783a00094a1aa5868000f5530dbc3401f0005298000a06000000312b08c306b83111b8ac3103806421e89b0388dfc00000a1772d705e2b6b4b0a3c405a1bf0c42bf47329374bb0c0843613312a00cc24a14018f0884570a3000289e44c000b0890cf1574ad05280000018b7b166a19871015814202081c4a71477a41510604f0e7814000e29000302a8128355543a29c2dab0b58985f15c62ac07a88f432c98905c24a916a32d59b87a05a381821800001020410c02009800e180010818001000c408002c0000004481001400606001840e00104
def An (_:Nat):=0x14038000a13141a691cc09a000181425108000103d200a92b28200001e08654da05c7021e98c000000024b8a9e2d1d2817a062007000010840001a9f800058360001824e84af21c9470000284e4a3c110600000006067409cc86c000706a8036a0d7434582ef14d4992c482828842ae28d83be88e1105a217418088ab1432283432d8a460feea39c1db0625521812c51bd09e74cbca27d301108b0dd2a71015e07bf0cd405643e4847301de1200148a164015c0b582af0787111606911ac034643f88c8d044a1a9433c11b82b0861848e68c7d30806410db20e511b5283a093604894358765152a032c21086064614a2d40c9a13a50fe106d0a305de00b42b340a421d90b5e9ff917d28244bb290500228a8401f81d0426a001e6118113831884360f588fac4bd04c74b4c8f4006b06be023c842840ca1ec430000383a921724f9006101d6899207c409e5163a207469a0fe01e6a3300000000000000050648a11d1fd24201016150000787350e2000252a0000c0b3412a43c80000000000292cd026d0fb802fc4a2276550a0003444aa7bc04960f404b60520007811692c382f54f4a2a8d40b03360b12932c4d9a8aa0bee9d7c28f053011fa1ca12fa81fd519215f129f0a780594a3d43f186f214be021d206825d124424540b3809910e61c2544284f1071a10002f488b84f2e88b411725ed4ae6230d2aca3b113ba16c455b81de11b696e13120a29501c9dc0000006851be08e036609f906ee04c443182a64fa10000080000018047a00268040c01058a800000290c24000000000160d80038001088c0c020013000020280014000f000000f0001030000001c6e06128c0121c000000a000180844200001400010203c1a0009854060a000600801010bc00001680c08140080006010100016000480002080000400020080002000000400000000002000100000040080000000100c0000018044600
def Ao (j:Nat):Nat:=(if j<1 then 0xa0e1414a8097a153a0b200f12214e0522103416b515c20dc68478854c8840842811621f3c99a603c015b217800016068a1320000681da9a329a8201341de093f804c614889f6605009f86038694a80ca694328d16955c0f7e9b1019f4126c195287d2947ca08a228682b20baa2026174421e2027aa0be1a141e8a0b980bee9b821658948e066c877417720e5a120c9ece19a117be883a091602e613c00014010495200000000612f01dc80cee0218818295a09b4a18fa0c0203421d7402ae221c23180a068da8199c21a29c180a4807ac20a218820b7e22e0868a84060e8000000002993400c49f1e1922181880dc9fe01b960d62118ca1069ee41710995812421c381fe0062e20f4865a032a1042110886b813ac9020001612c098ee1864000880469d1c18c49b600000000e21c00000000283e0001210c8150000148084123000841fd011e8888e8c6000140b4000000000000000000014115a9fb801e606c89ea20d9c0ab40fe20f9a0fb0108c09341be8006007f4880e12861cec8d922160000000001d0e1eb886748c82054c031408a0000c8060000000161b768cc0000555e000169b2000035560000c1340001483dc1a9c91600000000000188740000e5580001001c0000000000000000000000000001204e0000c9f2c0ec618281ae620940e7008781ca206e00000001e08c00ea421381c9a064e8cbd15e0001e2336072a86388c5b15600000001a04468bee09be802000081b2000000006159a00200000001e9f5c11be17a000080778a0d68cf80a949aba84e40ac418aa856201880856036c93c29ad80c65166c10e81f4ea060001e9e8000100c409bd08c3019dc1a2a1c4a22c0000e90929a6618429bac16808c0f17d2060a10b40fc682ea1d8407dc11ca20d217301fbe059a20521446852c824a0498157014e80230098c0da809fc0d341daa05ee227a082000000008141887a80c2000041e021d30225e93a00000000000121bc880a00000000e1ec400a28bda0de2991ea0f41bae9504137e19129c341c1684489140000c223e85000000001c8488094000060ee00000000e998205c000021b4aa0062008197400521d40d000042611028382a01050080436020000c09298180016018080607008082e03010040006000201a0600800000002010040600880000000058000c018440404068a8020601018400b0c8000803008000c020000000020182800010100004030a80004000400c000100804000000000000205804000000000000900008000c0000400150201804000180c00000000800010000402010000000000200400000003802010101c0001000000200000080c08038040004008140201000000405020000001000000200000000000000140005008000200010000001000000000000000001010080800008000c00 else 0x1c210556180bc6235216da9450130516a000000000000e1ef6029a01ae161a82d003a00706100c9e640420000000020a780f429bf0162000000000001c040000161cc0001d55c0001287ee84c413f888a81f081a7808e00002089a22a0001d160c06a2024c9fc00000001205a417c00012075d164802c61b020af2057015f2878021901f8000040b0281b60d04080c0a280794107201788d3e1e481e7403fc1aa80f300cc4941009da14d68214886a167e00fc142a1ade15d620660c88146a16ee81f4155611281c7c86fe0e34046a01568df00d421e2e17fa1a441f60000204a0001c1380001c12a00)
def Ap (_:Nat):=0xa1a5402b53e854a57115031440190002170000213c000286030780002037a60257f118a5bc4230470038000222ed57502a2055824b4274180001041a19a03d198cc06415ec164578000000344441858705985c035161c2bd10e917d0b3c21e14dc3edab8d238493c40104c53b507344971b4c65f10b0319b7c40f70f3d0b009880c40d985c317f81171afc5b90ec80750e643a1521138d121c08054e90a6a4e8099174613913703fd5340004481d0600004620002827204ac63497c00055aa5193485859e13b9337497c3331c840e413214ce141c710000014c47c500f1bfc1d5253852719fc6c90df5372002c2ec547047d4b78460526c6e601190794ea40ab01684f052ad08507f04ae02c45a112d54bd06c00090a0000a8c354e000382900cbc2f00000003088000405d82534d4000000046880d4c1a4159c3040d3845056a4550405502317a6312190d1d1007410c08046a448b42d000325090001000429061604090001190000000a0007000f000104050d000c000608011e081526070300000202020804020e0000000001000c0100010001090700000b0e05000900090502000002000000020008000100
def Aq (_:Nat):=0x3648d38002c34002d0c00203ac44000000406d28001c0c000003a4740283000000000001bea800395000000190b83d135c20c57c0a82a901427815c48c4c41c01384285342f62ba2c30001440000001c00442c1002
def Ar (_:Nat):=0x400000920000e10
def CX:Nat->aF
 | 11=>(58,7,8,0,0,12,0,Af)
 | 12=>(173,6,8,0,0,14,0,Ag)
 | 13=>(283,5,8,0,0,15,0,Ah)
 | 14=>(115,4,8,0,0,14,0,Ai)
 | 15=>(22,3,8,0,0,12,0,Aj)
 | 16=>(2,2,8,0,0,8,0,Ak)
 | 17=>(1,1,8,0,0,1,0,Al)
 | _=>a0
def CW:Nat->Nat->Option (Nat × Nat)
 | 12=>aK 47 107 7 13 6 3 Am
 | 13=>aK 133 295 9 15 8 3 An
 | 14=>aK 209 511 9 16 9 3 Ao
 | 15=>aK 87 196 8 14 7 3 Ap
 | 16=>aK 17 48 6 12 5 3 Aq
 | 17=>aK 1 10 4 8 1 3 Ar
 | _=>fun _=>none
def gl:aM:=⟨1023,18,fun i=>yZ[i]?.getD (0,0),CV,CU,CX,CW⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma yh:aD gl (ai fQ)=true:=by simp only [aD,and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,aH (d:=5) ?_⟩,aH (d:=2) ?_⟩<;>simp only [aW]<;>(try repeat' apply And.intro)<;>decide +kernel
set_option maxHeartbeats 0 in
lemma pt:cV gl 17 0=true:=by decide +kernel
set_option maxHeartbeats 0 in
lemma wu:aP gl 11 0 58=true:=by apply aq 11 0 3;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
lemma ww:aP gl 12 0 12=true:=by apply aq 10 0 1;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma sx:aP gl 12 12 67=true:=by apply aq 11 0 4;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma sy:aP gl 12 79 94=true:=by apply aq 12 0 4;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
lemma Ab:aP gl 12 0 173=true:=(@aJ _ gl 12 0 12 161 ww (@aJ _ gl 12 12 67 94 sx sy))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma wx:aP gl 13 0 96=true:=by apply aq 11 0 4;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma sA:aP gl 13 96 96=true:=by apply aq 11 0 4;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
lemma pk:aP gl 13 192 6=true:=by apply aq 11 0 0;simp only [aE,ba];decide +kernel
set_option maxHeartbeats 0 in
lemma pl:aP gl 13 198 57=true:=by apply aq 12 0 3;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
lemma pn:aP gl 13 255 28=true:=by apply aq 13 0 2;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
lemma Ac:aP gl 13 0 283=true:=(@aJ _ gl 13 0 192 91 (@aJ _ gl 13 0 96 96 wx sA) (@aJ _ gl 13 192 6 85 pk (@aJ _ gl 13 198 57 28 pl pn)))
lemma wy:aP gl 14 0 22=true:=by apply aq 10 0 2;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
lemma sB:aP gl 14 22 29=true:=by apply aq 11 0 2;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
set_option maxHeartbeats 0 in
lemma sC:aP gl 14 51 55=true:=by apply aq 12 0 3;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
lemma po:aP gl 14 106 7=true:=by apply aq 13 0 0;simp only [aE,ba];decide +kernel
lemma pq:aP gl 14 113 2=true:=by apply aq 14 0 0;simp only [aE,ba];decide +kernel
lemma Ad:aP gl 14 0 115=true:=(@aJ _ gl 14 0 51 64 (@aJ _ gl 14 0 22 29 wy sB) (@aJ _ gl 14 51 55 9 sC (@aJ _ gl 14 106 7 2 po pq)))
lemma wz:aP gl 15 0 13=true:=by apply aq 11 0 1;simp only [aE,ba];(repeat' apply And.intro)<;>decide +kernel
lemma sD:aP gl 15 13 6=true:=by apply aq 12 0 0;simp only [aE,ba];decide +kernel
lemma sE:aP gl 15 19 3=true:=by apply aq 13 0 0;simp only [aE,ba];decide +kernel
lemma Ae:aP gl 15 0 22=true:=(@aJ _ gl 15 0 13 9 wz (@aJ _ gl 15 13 6 3 sD sE))
lemma wA:aP gl 16 0 2=true:=by apply aq 12 0 0;simp only [aE,ba];decide +kernel
lemma As:bo gl 16:=by intro k hk;match k with|11=>exact wu|12=>exact Ab|13=>exact Ac|14=>exact Ad|15=>exact Ae|16=>exact wA|0|1|2|3|4|5|6|7|8|9|10=>rfl|_+17=>omega
lemma i1:aB true co 16 inputs.toFinset:=by
 rw [show co=aY yW by decide +kernel];exact gk (g:=yW) (top:=16) (i:=0) (ad fQ jH) w6 yY (by decide) (by decide +kernel)
lemma f7:bV true co 16 inputs.toFinset:=by
 rw [show co=aY Ch by decide +kernel];exact fP (g:=Ch) (k:=17) (i:=0) (ad fQ jH) yk Av qb (by decide +kernel)
lemma mi:aB false co 17 inputs.toFinset:=by
 rw [show co=aY BO by decide +kernel];exact gk (g:=BO) (top:=17) (i:=0) (ad ky rC) xX z3 (by decide) (by decide +kernel)
lemma hZ:bV false co 17 inputs.toFinset:=by
 rw [show co=aY wb by decide +kernel];exact fP (g:=wb) (k:=18) (i:=0) (ad ky rC) wc xZ nn (by decide +kernel)
lemma et:bV true co 16 dZ.toFinset:=by
 rw [show co=aY gl by decide +kernel];exact fP (g:=gl) (k:=17) (i:=0) (ad fQ jH) yh As pt (by decide +kernel)
lemma fL:aB true co 16 (qz :: inputs).toFinset:=by
 have sl:gB true (aN 1022) co (dC 1 0) 15:=by
  have cc:fW 1023 (1,0,1022,0,15) (ai fQ)=true:=by decide +kernel
  have h:=en (u:=true) (m:=1023) (c:=(1,0,1022,0,15)) (ai fQ) (ad fQ jH) cc
  have eq1:dR 1023=co:=by decide +kernel
  have eq2:eZ 1023 (1,0,1022,0,15)=1023:=by decide
  have h1:gB true (aN 1023) co (dC 1 0) 15:=by simpa only [eq1,eq2] using h
  obtain ⟨f,roots,dom,sup,nc,pr⟩:=h1
  refine ⟨f,roots,dom,?_,nc,pr⟩
  intro v hv;apply sup
  have hsub:(aN 1022).all (fun a=>(aN 1023).contains a)=true:=by decide +kernel
  exact by simpa [contains_eq_mem] using all_eq_true.mp hsub v hv
 have vp:dx true (aN 1022) co ⟨dC 1 0,15,0,aN 1022⟩:=
  fI sl (by decide +kernel:fH true (aN 1022) [] (dC 1 0) 15=some ⟨dC 1 0,15,0,aN 1022⟩)
 have cut:ct true ⟨dC 1 0,15,0,aN 1022⟩ 16 inputs (0,inputs.getD 0 zero,inputs.getD 2 zero)=true:=by decide +kernel
 have hcv:bp (0,inputs.getD 0 zero,inputs.getD 2 zero)=qz:=by
  simp [bp,bM,qz]
 have nd:(bp (0,inputs.getD 0 zero,inputs.getD 2 zero) :: inputs).Nodup:=by
  rw [hcv];decide +kernel
 rw [<- hcv];exact eS vp nd cut
lemma h8:dZ.all bP=true:=by decide +kernel
lemma eC:∀ a ∈ inputs,bg a:=by
 have h:inputs.all cE=true:=by decide +kernel
 exact fun a ha=>cN a (all_eq_true.mp h a ha)
lemma jl:∀ a ∈ dZ,bg a:=by
 have h:dZ.all cE=true:=by decide +kernel
 exact fun a ha=>cN a (all_eq_true.mp h a ha)
lemma l0:∀ i:Fin 10,aV (cp i) qz=aV (bX i) qz:=by decide +kernel
lemma oU:aV 0 co=false:=by decide +kernel
lemma iW (x:Fin 10->Bool) (hx:jq x=true):∃ y:Fin 10->Bool,(∀ i,y i=true->x i=true)/\jq y=true/\(y 0&&y 2)=false:=by
 have he:([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]:List (Fin 10 × Fin 10)).any (fun e=>x e.1&&x e.2)=true:=by
  simpa [jq,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc] using hx
 obtain ⟨e,hmem,hev⟩:=any_eq_true.mp he;have h12:=Bool.and_eq_true_iff.mp hev
 refine ⟨fun i=>decide (i=e.1\/i=e.2),?_,?_,?_⟩
 . intro i hi;simp only [decide_eq_true_eq] at hi
   rcases hi with rfl|rfl
   . exact h12.1
   . exact h12.2
 . have hall:∀ p ∈ ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]:List (Fin 10 × Fin 10)),
    jq (fun i=>decide (i=p.1\/i=p.2))=true:=by decide
   exact hall e hmem
 . have hall:∀ p ∈ ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]:List (Fin 10 × Fin 10)),
    (decide ((0:Fin 10)=p.1\/(0:Fin 10)=p.2)&&decide ((2:Fin 10)=p.1\/(2:Fin 10)=p.2))=false:=by decide
   exact hall e hmem
lemma fJ (a b:aQ):eM false a b=bM 0 a b:=rfl
lemma jK {w:List aQ} {g:Gate} (hop:g.op=GateOp.and) (hl:g.inputs.length ≤ 2) (hnot:gv w g ∉ w) (hpr:bg (gv w g)):∃ a ∈ w,∃ b ∈ w,a≠b/\gv w g=bM 0 a b:=by
 have hpo (x:aQ):eM false x one=x:=by rw [fJ];exact (fm x).1
 have hpz (x:aQ):bM 0 x zero=zero:=(fm x).2.2.1;have hzp (x:aQ):bM 0 zero x=zero:=(fm x).2.2.2.2.2.2.2.2.2.2.2.2.1
 rcases h:g.inputs with _|⟨i,_|⟨j,_|⟨k,l⟩⟩⟩
 . exfalso;apply hpr.2;simp [gv,hop,h]
 . exfalso
   have hv:gv w g=w.getD i zero:=by
    simp only [gv,hop,h,map_cons,map_nil,foldr_cons,foldr_nil];exact hpo _
   by_cases hi:i<w.length
   . apply hnot;rw [hv,getD_eq_getElem _ _ hi];exact getElem_mem hi
   . apply hpr.1;rw [hv,getD_eq_default _ _ (Nat.le_of_not_lt hi)]
 . have hv:gv w g=bM 0 (w.getD i zero) (w.getD j zero):=by
    simp only [gv,hop,h,map_cons,map_nil,foldr_cons,foldr_nil];rw [hpo,fJ]
   by_cases hi:i<w.length
   . by_cases hj:j<w.length
     . have ha:w.getD i zero ∈ w:=by rw [getD_eq_getElem _ _ hi];exact getElem_mem hi
       have hb:w.getD j zero ∈ w:=by rw [getD_eq_getElem _ _ hj];exact getElem_mem hj
       have hne:w.getD i zero≠w.getD j zero:=by
        intro eq;apply hnot;rw [hv,eq,(fm _).2.2.2.2.1];exact hb
       exact ⟨_,ha,_,hb,hne,hv⟩
     . exfalso;apply hpr.1;rw [hv,getD_eq_default _ _ (Nat.le_of_not_lt hj)];exact hpz _
   . exfalso;apply hpr.1;rw [hv,getD_eq_default _ _ (Nat.le_of_not_lt hi)];exact hzp _
 . rw [h] at hl;simp at hl
lemma hJ (gs:List Gate) (hm:∀ g ∈ gs,g.op=GateOp.and\/g.op=GateOp.or) (w1 w2:List Bool) (hlen:w1.length=w2.length) (hle:∀ i,w1.getD i false=true->w2.getD i false=true):∀ i,((Circuit.mk gs 0).wires w1).getD i false=true ->((Circuit.mk gs 0).wires w2).getD i false=true:=by
 induction gs generalizing w1 w2 with
 | nil=>exact hle
 | cons g rest ih =>
  have hg:=hm g mem_cons_self
  have hstep:g.op.eval (g.inputs.map fun i=>w1.getD i false)=true  ->
   g.op.eval (g.inputs.map fun i=>w2.getD i false)=true:=by
   rcases hg with h|h<;>rw [h]<;>intro hv
   . simp only [GateOp.eval,all_eq_true,mem_map,id_eq,forall_exists_index,and_imp,
      forall_apply_eq_imp_iff₂] at hv ⊢
     exact fun i hi=>hle i (hv i hi)
   . simp only [GateOp.eval,any_eq_true,mem_map,id_eq] at hv ⊢;obtain ⟨_,⟨i,hi,rfl⟩,h1⟩:=hv;exact ⟨_,⟨i,hi,rfl⟩,hle i h1⟩
  change ∀ i,((Circuit.mk rest 0).wires (w1 ++ [_])).getD i false=true  ->
   ((Circuit.mk rest 0).wires (w2 ++ [_])).getD i false=true
  apply ih (fun g' hg'=>hm g' (mem_cons_of_mem _ hg')) _ _ (by simp [hlen]);intro i hi
  by_cases hlt:i<w1.length
  . rw [List.getD_append _ _ _ _ hlt] at hi;rw [List.getD_append _ _ _ _ (by omega)];exact hle i hi
  . rw [List.getD_append_right _ _ _ _ (by omega)] at hi;rw [List.getD_append_right _ _ _ _ (by omega),<- hlen]
    rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt hlt) with rfl|hgt
    . simp only [Nat.sub_self,List.getD_cons_zero] at hi ⊢;exact hstep hi
    . have hpos:1 ≤ i-w1.length:=by omega
      rw [getD_eq_default [_] false (by simpa using hpos)] at hi
      cases hi
lemma sV (mi:aB false co 17 inputs.toFinset) (hZ:bV false co 17 inputs.toFinset) (i1:aB true co 16 inputs.toFinset) (f7:bV true co 16 inputs.toFinset) (fL:aB true co 16 (qz :: inputs).toFinset) (et:bV true co 16 dZ.toFinset):∀ (x1:Circuit) (x2:Fin 10->Fin 10),PEqualNP.MetaComplexity.FanInTwo x1->x1.size ≤ 18 ->(∃ (x5:Gate) (x6:List Gate),x1.gates=x5 :: x6/\x5.op=GateOp.and) ->∃ (x6:Fin 10->Bool),x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 0&&x6 2])≠jq x6:=by
 classical
 intro C p hfan hsize ⟨g0,gs0,hg0,hop0⟩
 by_contra hcon
 have hcon':∀ x:Fin 10->Bool,C.eval (List.ofFn (x ∘ p) ++ [x 0&&x 2])=jq x:=by
  intro x
  by_contra hne
  exact hcon ⟨x,hne⟩
 let renameI (i : ℕ) : ℕ:=if hi:i<10 then (p ⟨i,hi⟩).val else i
 have early (i : ℕ) (hi:i<10):renameI i<10:=by simp [renameI,hi]
 have late (i : ℕ) (hi:10 ≤ i):renameI i=i:=by simp [renameI,Nat.not_lt.mpr hi]
 let mapGate (g:Gate):Gate:=⟨g.op,g.inputs.map renameI⟩;let E:Circuit:=⟨C.gates.map mapGate,renameI C.output⟩
 have eFan:PEqualNP.MetaComplexity.FanInTwo E:=by
  intro g hg;obtain ⟨g',hg',rfl⟩:=mem_map.mp hg;exact ⟨(hfan g' hg').1,by simpa [mapGate] using (hfan g' hg').2⟩
 have eSize:E.size ≤ 18:=by simpa [E,Circuit.size] using hsize
 have runR (gs:List Gate) (x y:List Bool) (len:x.length=y.length)
  (lo:10 ≤ x.length) (agree:∀ i,y.getD (renameI i) false=x.getD i false):
  ∀ i,((Circuit.mk (gs.map mapGate) 0).wires y).getD (renameI i) false =
   ((Circuit.mk gs 0).wires x).getD i false:=by
  induction gs generalizing x y with
  | nil=>exact agree
  | cons g rest ih =>
   let b:=g.op.eval (g.inputs.map fun i=>x.getD i false)
   have next:(mapGate g).op.eval ((mapGate g).inputs.map fun i=>y.getD i false)=b:=by
    simp only [b,mapGate,map_map,Function.comp_def,agree]
   change ∀ i,((Circuit.mk (rest.map mapGate) 0).wires (y ++ [_])).getD (renameI i) false =
    ((Circuit.mk rest 0).wires (x ++ [b])).getD i false
   rw [next];apply ih _ _ (by simp [len]) (by simp;omega);intro i
   by_cases hi:i<x.length
   . have hy:renameI i<y.length:=by
      by_cases hn:i<10
      . have:=early i hn;omega
      . rw [late i (by omega)];omega
     rw [List.getD_append _ _ _ _ hy,List.getD_append _ _ _ _ hi];exact agree i
   . rw [late i (by omega),List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega),len]
 have eComp:∀ x:Fin 10->Bool,E.eval (List.ofFn x ++ [x 0&&x 2])=jq x:=by
  intro x
  have h1:E.eval (List.ofFn x ++ [x 0&&x 2])=C.eval (List.ofFn (x ∘ p) ++ [x 0&&x 2]):=by
   apply runR C.gates _ _ (by simp) (by simp) _ C.output;intro i
   by_cases hi:i<10
   . have hx:renameI i<(List.ofFn x).length:=by simpa using early i hi
     have hy:i<(List.ofFn (x ∘ p)).length:=by simpa using hi
     rw [List.getD_append _ _ _ _ hx,List.getD_append _ _ _ _ hy,
      getD_eq_getElem _ _ hx,getD_eq_getElem _ _ hy]
     simp only [List.getElem_ofFn,Function.comp_apply]
     congr 1;apply Fin.ext;exact dite_eq_left hi
   . rw [late i (by omega),List.getD_append_right _ _ _ _ (by simpa using Nat.not_lt.mp hi),
      List.getD_append_right _ _ _ _ (by simpa using Nat.not_lt.mp hi)]
     simp
  exact h1.trans (hcon' x)
 have eGates:E.gates=mapGate g0 :: gs0.map mapGate:=by simp [E,hg0]
 have eOp:(mapGate g0).op=GateOp.and:=hop0
 have idxIn (a:aQ) (ha:a ∈ inputs):∃ i:Fin 10,inputs.getD i.val zero=a:=by
  rw [<- h6] at ha;exact List.mem_ofFn.mp ha
 by_cases hmono:∀ h ∈ E.gates,eH h=false
 . have hmoOp:∀ h ∈ E.gates,h.op=GateOp.and\/h.op=GateOp.or:=by
    intro h hh;have h1:=(eFan h hh).1;have h2:=hmono h hh;simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h1
    rcases h1 with h1|h1|h1
    . exact Or.inl h1
    . exact Or.inr h1
    . simp [eH,h1] at h2
   have hfalse:∀ x:Fin 10->Bool,E.eval (List.ofFn x ++ [false])=jq x:=by
    intro x
    have hup:E.eval (List.ofFn x ++ [false])=true->jq x=true:=by
     intro ht;rw [<- eComp x];apply hJ E.gates hmoOp _ _ (by simp) _ E.output ht;intro i hi
     by_cases h10:i<10
     . rw [List.getD_append _ _ _ _ (by simpa using h10)] at hi ⊢;exact hi
     . by_cases heq:i=10
       . subst i;rw [List.getD_append_right _ _ _ _ (by simp)] at hi;simp at hi
       . rw [getD_eq_default _ _ (by simp;omega)] at hi;cases hi
    cases hex:jq x with
    | false =>
     cases hcv:E.eval (List.ofFn x ++ [false]) with
     | false=>rfl
     | true=>exact absurd (hup hcv) (by simp [hex])
    | true =>
     obtain ⟨y,hyx,hey,hy02⟩:=iW x hex
     have hy:E.eval (List.ofFn y ++ [false])=true:=by
      rw [<- hy02,eComp y,hey]
     apply hJ E.gates hmoOp _ _ (by simp) _ E.output hy;intro i hi
     by_cases h10:i<10
     . rw [List.getD_append _ _ _ _ (by simpa using h10)] at hi ⊢;rw [getD_eq_getElem _ _ (by simpa using h10)] at hi ⊢;simp only [List.getElem_ofFn] at hi ⊢;exact hyx ⟨i,h10⟩ hi
     . by_cases heq:i=10
       . subst i;rw [List.getD_append_right _ _ _ _ (by simp)] at hi;simp at hi
       . rw [getD_eq_default _ _ (by simp;omega)] at hi;cases hi
   let shift (i : ℕ) : ℕ:=if i<10 then i else if i=10 then 100 else i-1;let shGate (g:Gate):Gate:=⟨g.op,g.inputs.map shift⟩;let D:Circuit:=⟨E.gates.map shGate,shift E.output⟩
   have runS (gs:List Gate) (u w:List Bool) (hlu:11 ≤ u.length) (hlw:w.length+1=u.length)
    (hcap:w.length+gs.length<100)
    (agree:∀ i,w.getD (shift i) false=u.getD i false):
    ∀ i,((Circuit.mk (gs.map shGate) 0).wires w).getD (shift i) false =
     ((Circuit.mk gs 0).wires u).getD i false:=by
    induction gs generalizing u w with
    | nil=>exact agree
    | cons g rest ih =>
     let b:=g.op.eval (g.inputs.map fun i=>u.getD i false)
     have next:(shGate g).op.eval ((shGate g).inputs.map fun i=>w.getD i false)=b:=by
      simp only [b,shGate,map_map,Function.comp_def,agree]
     change ∀ i,((Circuit.mk (rest.map shGate) 0).wires (w ++ [_])).getD (shift i) false =
      ((Circuit.mk rest 0).wires (u ++ [b])).getD i false
     rw [next];simp only [length_cons] at hcap;apply ih _ _ (by simp;omega) (by simp;omega) (by simp;omega);intro i
     by_cases hi:i<u.length
     . rw [List.getD_append _ _ _ _ hi,<- agree i]
       by_cases h10:i<10
       . rw [show shift i=i by simp [shift,h10],List.getD_append _ _ _ _ (by omega)]
       . by_cases heq:i=10
         . subst i
           rw [show shift 10=100 by rfl,
            getD_eq_default (w ++ [b]) false (by simp;omega),
            getD_eq_default w false (by omega)]
         . rw [show shift i=i-1 by simp [shift,h10,heq],
            List.getD_append _ _ _ _ (by omega)]
     . have h11:11 ≤ i:=by omega
       rw [show shift i=i-1 by simp [shift,show ¬ i<10 by omega,show i≠10 by omega]];rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega)]
       congr 1;omega
   have dFan:PEqualNP.MetaComplexity.FanInTwo D:=by
    intro g hg;obtain ⟨g',hg',rfl⟩:=mem_map.mp hg;exact ⟨(eFan g' hg').1,by simpa [shGate] using (eFan g' hg').2⟩
   have dMono:∀ g ∈ D.gates,eH g=false:=by
    intro g hg;obtain ⟨g',hg',rfl⟩:=mem_map.mp hg;exact hmono g' hg'
   have dComp:∀ x:Fin 10->Bool,D.eval (List.ofFn x)=jq x:=by
    intro x
    have h1:D.eval (List.ofFn x)=E.eval (List.ofFn x ++ [false]):=by
     apply runS E.gates (List.ofFn x ++ [false]) (List.ofFn x) (by simp) (by simp)
      (by change (List.ofFn x).length+E.size<100;simp;omega) _ E.output
     intro i
     by_cases h10:i<10
     . rw [show shift i=i by simp [shift,h10],List.getD_append _ _ _ _ (by simpa using h10)]
     . by_cases heq:i=10
       . subst i
         rw [show shift 10=100 by rfl,getD_eq_default _ _ (by simp),
          List.getD_append_right _ _ _ _ (by simp)]
         simp
       . rw [show shift i=i-1 by simp [shift,h10,heq],
          getD_eq_default _ _ (by simp;omega),
          getD_eq_default _ _ (by simp;omega)]
    exact h1.trans (hfalse x)
   let gd:=shGate (mapGate g0);let gsd:=(gs0.map mapGate).map shGate
   have dGates:D.gates=gd :: gsd:=by simp [D,eGates,gd,gsd]
   have dLen:gsd.length ≤ 17:=by
    have:D.gates.length ≤ 18:=by simpa [D,Circuit.size] using eSize
    rw [dGates,length_cons] at this;omega
   have dGoal:(dB gsd (inputs ++ [gv inputs gd])).getD D.output zero=co:=by
    have h0:(dB D.gates inputs).getD D.output zero=co:=by
     apply eq_of_getLsbD_eq;intro j hj;let r:bW:=⟨j,hj⟩;exact (p3 D dFan D.output r).trans ((dComp (gm r)).trans (jO r).symm)
    simpa only [dGates,dB,foldl_cons] using h0
   have gsdFan:PEqualNP.MetaComplexity.FanInTwo ⟨gsd,D.output⟩:=fun g hg =>
    dFan g (by rw [dGates];exact mem_cons_of_mem _ hg)
   have gsdMono:∀ g ∈ gsd,eH g=false:=fun g hg =>
    dMono g (by rw [dGates];exact mem_cons_of_mem _ hg)
   have outM:=g6 (u:=false) (dB gsd (inputs ++ [gv inputs gd])) D.output;rw [dGoal] at outM;unfold Core.gA at outM;rw [lS] at outM
   obtain ⟨k,S,hk,run,sub⟩:=ra gsd (inputs ++ [gv inputs gd]) gsdFan (fun _=>gsdMono)
    eY (outM.resolve_right (fun h=>h eY))
   have hmapF:(inputs ++ [gv inputs gd]).map (fM false)=inputs ++ [gv inputs gd]:=by
    change (inputs ++ [gv inputs gd]).map id=inputs ++ [gv inputs gd];exact List.map_id _
   rw [hmapF] at sub;have hk17:k ≤ 17:=le_trans hk (le_trans (List.countP_le_length) dLen);let v:=gv inputs gd
   by_cases hv:v ∈ S/\v ∉ inputs/\bg v
   . obtain ⟨hvS,hvNot,hvPr⟩:=hv;have hgd_op:gd.op=GateOp.and:=eOp;have hgd_len:gd.inputs.length ≤ 2:=(dFan gd (by rw [dGates];exact mem_cons_self)).2;obtain ⟨a,haIn,b,hbIn,hab,hvEq⟩:=jK hgd_op hgd_len hvNot hvPr;change v=bM 0 a b at hvEq;let U:=S.erase v
     have hSeq:S=insert (bM 0 a b) U:=by
      rw [<- hvEq];exact (insert_erase hvS).symm
     have hInEq:inputs.toFinset=insert a (insert b U):=by
      ext w
      constructor
      . intro hw;have hwL:=mem_toFinset.mp hw
        by_cases hwa:w=a
        . simp [hwa]
        . by_cases hwb:w=b
          . simp [hwb]
          . apply mem_insert_of_mem;apply mem_insert_of_mem
            refine mem_erase.mpr ⟨fun he=>hvNot (he ▸ hwL),?_⟩
            obtain ⟨i,rfl⟩:=idxIn w hwL
            apply cX run (inputs ++ [v]) (inputs.getD i.val zero) sub
             (cp i) (bX i) (bQ.1 i)
            intro z hz hzne
            rcases mem_append.mp hz with hzIn|hzV
            . obtain ⟨j,rfl⟩:=idxIn z hzIn;exact bQ.2 i j (fun he=>hzne (by rw [he]))
            . simp only [List.mem_singleton] at hzV;rw [hzV,hvEq,dQ,dQ];obtain ⟨ia,hia⟩:=idxIn a haIn;obtain ⟨ib,hib⟩:=idxIn b hbIn
              have e1:aV (cp i) a=aV (bX i) a:=by
               rw [<- hia];exact bQ.2 i ia (fun he=>hwa (by rw [<- hia,he]))
              have e2:aV (cp i) b=aV (bX i) b:=by
               rw [<- hib];exact bQ.2 i ib (fun he=>hwb (by rw [<- hib,he]))
              simp [e1,e2]
      . intro hw;simp only [mem_insert,U,mem_erase] at hw
        rcases hw with rfl|rfl|⟨hwv,hwS⟩
        . exact mem_toFinset.mpr haIn
        . exact mem_toFinset.mpr hbIn
        . rcases mem_append.mp (sub w hwS) with h1|h1
          . exact mem_toFinset.mpr h1
          . simp only [List.mem_singleton] at h1;exact absurd h1 hwv
     exact hZ k hk17 ⟨U,a,b,hInEq,eC a haIn,eC b hbIn,hab,
      fun hm=>hvNot (hvEq ▸ mem_toFinset.mp hm),hSeq ▸ run⟩
   . have subIn:∀ w ∈ S,w ∈ inputs:=by
      intro w hw
      rcases mem_append.mp (sub w hw) with h1|h1
      . exact h1
      . simp only [List.mem_singleton] at h1;subst w
        by_cases h1':v ∈ inputs
        . exact h1'
        . exact False.elim (hv ⟨hw,h1',eI run _ hw⟩)
     have hEq:S=inputs.toFinset:=by
      ext w
      constructor
      . exact fun hw=>mem_toFinset.mpr (subIn w hw)
      . intro hw;obtain ⟨i,rfl⟩:=idxIn w (mem_toFinset.mp hw)
        apply cX run inputs (inputs.getD i.val zero) subIn
         (cp i) (bX i) (bQ.1 i)
        intro z hz hzne;obtain ⟨j,rfl⟩:=idxIn z hz;exact bQ.2 i j (fun he=>hzne (by rw [he]))
     exact mi k hk17 (hEq ▸ run)
 . -- SIGNED BRANCH: at least one NOT gate in E.gates
   let ge:=mapGate g0;let gse:=gs0.map mapGate
   have hnot_gs:∃ h ∈ gse,eH h=true:=by
    by_contra hall
    apply hmono;intro h hh;rw [eGates] at hh
    rcases mem_cons.mp hh with rfl|hh'
    . simp [eH,eOp]
    . cases hn:eH h with
      | false=>rfl
      | true=>exact False.elim (hall ⟨h,hh',hn⟩)
   have hcnt:gse.countP (fun g => !eH g) ≤ 16:=by
    obtain ⟨h,hh,hnt⟩:=hnot_gs
    have hlen:gse.length ≤ 17:=by
     have h1:E.gates.length ≤ 18:=eSize;rw [eGates,length_cons] at h1;change gse.length+1 ≤ 18 at h1;omega
    have hlt:gse.countP (fun g => !eH g)<gse.length:=by
     rcases Nat.lt_or_ge (gse.countP (fun g => !eH g)) gse.length with hlt|hge
     . exact hlt
     . have heq:=List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length hge) h hh;simp [hnt] at heq
    omega
   have raw1_bits (r:bW):dZ.map (aV r)=List.ofFn (gm r) ++ [gm r 0&&gm r 2]:=by
    simp only [dZ,List.map_append,List.map_singleton,rt]
    congr 1;congr 1
    change aV r (inputs.getD 0 zero&&&inputs.getD 2 zero)=_;simp [aV,gm]
   have eGoal:(dB gse (dZ ++ [gv dZ ge])).getD E.output zero=co:=by
    have h0:(dB E.gates dZ).getD E.output zero=co:=by
     apply eq_of_getLsbD_eq;intro j hj;let r:bW:=⟨j,hj⟩
     have hb:aV r ((dB E.gates dZ).getD E.output zero) =
      (E.wires (dZ.map (aV r))).getD E.output false:=by
      rw [<- oG,io _ _ _ (fun g hg=>(eFan g hg).1)];rfl
     exact hb.trans (by rw [raw1_bits r];exact (eComp (gm r)).trans (jO r).symm)
    simpa only [eGates,dB,foldl_cons] using h0
   have gseFan:PEqualNP.MetaComplexity.FanInTwo ⟨gse,E.output⟩:=fun g hg =>
    eFan g (by rw [eGates];exact mem_cons_of_mem _ hg)
   let v:=gv dZ ge;have outS:=g6 (u:=true) (dB gse (dZ ++ [v])) E.output;rw [eGoal] at outS;unfold Core.gA at outS;rw [kC oU] at outS
   obtain ⟨k,S,hk,run,sub⟩:=ra gse (dZ ++ [v]) gseFan (by simp)
    eY (outS.resolve_right (fun h=>h eY))
   have hk16:k ≤ 16:=le_trans hk hcnt
   have hraw1_map:dZ.map (fM true)=dZ:=rf h8
   have hmap:(dZ ++ [v]).map (fM true)=dZ ++ [fM true v]:=by
    simp [hraw1_map]
   rw [hmap] at sub
   have hv_plain:bg v->aV 0 v=false:=by
    intro hpr
    have hpo (x:aQ):eM false x one=x:=by rw [fJ];exact (fm x).1
    rcases h:ge.inputs with _|⟨i,_|⟨j,_|⟨k',l⟩⟩⟩
    . exfalso;apply hpr.2;simp [v,gv,ge,eOp,h]
    . have hv1:v=dZ.getD i zero:=by
       simp only [v,gv,ge,eOp,h,map_cons,map_nil,foldr_cons,foldr_nil];exact hpo _
      by_cases hi:i<dZ.length
      . rw [hv1,getD_eq_getElem _ _ hi];exact beq_iff_eq.mp (all_eq_true.mp h8 _ (getElem_mem hi))
      . rw [hv1,getD_eq_default _ _ (Nat.le_of_not_lt hi)];exact cn 0
    . have hv2:v=bM 0 (dZ.getD i zero) (dZ.getD j zero):=by
       simp only [v,gv,ge,eOp,h,map_cons,map_nil,foldr_cons,foldr_nil];rw [hpo,fJ]
      have hbi:aV 0 (dZ.getD i zero)=false:=by
       by_cases hi:i<dZ.length
       . rw [getD_eq_getElem _ _ hi];exact beq_iff_eq.mp (all_eq_true.mp h8 _ (getElem_mem hi))
       . rw [getD_eq_default _ _ (Nat.le_of_not_lt hi)];exact cn 0
      rw [hv2,dQ];simp only [ite_true,hbi,Bool.false_and]
    . have hl:=(eFan ge (by rw [eGates];exact mem_cons_self)).2;rw [h] at hl;simp at hl
   by_cases hv:fM true v ∈ S/\v ∉ dZ/\bg v
   . obtain ⟨hvS,hvNot,hvPr⟩:=hv;have hnv:fM true v=v:=kC (hv_plain hvPr);rw [hnv] at hvS;have hge_len:ge.inputs.length ≤ 2:=(eFan ge (by rw [eGates];exact mem_cons_self)).2;obtain ⟨a,haR,b,hbR,hab,hvEq⟩:=jK eOp hge_len hvNot hvPr;change v=bM 0 a b at hvEq;let U:=S.erase v
     have hSeq:S=insert (bM 0 a b) U:=by
      rw [<- hvEq];exact (insert_erase hvS).symm
     have hInMem (w:aQ) (hw:w ∈ inputs) (hwa:w≠a) (hwb:w≠b):w ∈ S:=by
      obtain ⟨i,rfl⟩:=idxIn w hw
      apply cX run (dZ ++ [v]) (inputs.getD i.val zero) (hnv ▸ sub)
       (cp i) (bX i) (bQ.1 i)
      intro z hz hzne
      have hEqR (q:aQ) (hq:q ∈ dZ) (hqne:q≠inputs.getD i.val zero):
       aV (cp i) q=aV (bX i) q:=by
       rcases mem_append.mp hq with hqIn|hqX
       . obtain ⟨j,rfl⟩:=idxIn q hqIn;exact bQ.2 i j (fun he=>hqne (by rw [he]))
       . simp only [List.mem_singleton] at hqX;rw [hqX];exact l0 i
      rcases mem_append.mp hz with hzR|hzV
      . exact hEqR z hzR hzne
      . simp only [List.mem_singleton] at hzV;rw [hzV,hvEq,dQ,dQ];have e1:=hEqR a haR (Ne.symm hwa);have e2:=hEqR b hbR (Ne.symm hwb);simp [e1,e2]
     by_cases hx:qz ∈ S\/qz=a\/qz=b
     . have hRawEq:dZ.toFinset=insert a (insert b U):=by
        ext w
        constructor
        . intro hw;have hwR:=mem_toFinset.mp hw
          by_cases hwa:w=a
          . simp [hwa]
          . by_cases hwb:w=b
            . simp [hwb]
            . apply mem_insert_of_mem;apply mem_insert_of_mem
              refine mem_erase.mpr ⟨fun he=>hvNot (he ▸ hwR),?_⟩
              rcases mem_append.mp hwR with hwIn|hwX
              . exact hInMem w hwIn hwa hwb
              . simp only [List.mem_singleton] at hwX;subst w
                rcases hx with hxS|hxa|hxb
                . exact hxS
                . exact absurd hxa hwa
                . exact absurd hxb hwb
        . intro hw;simp only [mem_insert,U,mem_erase] at hw
          rcases hw with rfl|rfl|⟨hwv,hwS⟩
          . exact mem_toFinset.mpr haR
          . exact mem_toFinset.mpr hbR
          . rcases mem_append.mp ((hnv ▸ sub) w hwS) with h1|h1
            . exact mem_toFinset.mpr h1
            . simp only [List.mem_singleton] at h1;exact absurd h1 hwv
       exact et k hk16 ⟨U,a,b,hRawEq,jl a haR,jl b hbR,hab,
        fun hm=>hvNot (hvEq ▸ mem_toFinset.mp hm),hSeq ▸ run⟩
     . have hxNotS:qz ∉ S:=fun h=>hx (Or.inl h);have hxa:a≠qz:=fun h=>hx (Or.inr (Or.inl h.symm));have hxb:b≠qz:=fun h=>hx (Or.inr (Or.inr h.symm));have haIn:a ∈ inputs:=(mem_append.mp haR).resolve_right (by simpa using hxa);have hbIn:b ∈ inputs:=(mem_append.mp hbR).resolve_right (by simpa using hxb)
       have hInEq:inputs.toFinset=insert a (insert b U):=by
        ext w
        constructor
        . intro hw;have hwIn:=mem_toFinset.mp hw
          by_cases hwa:w=a
          . simp [hwa]
          . by_cases hwb:w=b
            . simp [hwb]
            . apply mem_insert_of_mem;apply mem_insert_of_mem
              refine mem_erase.mpr ⟨fun he=>hvNot (he ▸ List.mem_append_left _ hwIn),?_⟩
              exact hInMem w hwIn hwa hwb
        . intro hw;simp only [mem_insert,U,mem_erase] at hw
          rcases hw with rfl|rfl|⟨hwv,hwS⟩
          . exact mem_toFinset.mpr haIn
          . exact mem_toFinset.mpr hbIn
          . rcases mem_append.mp ((hnv ▸ sub) w hwS) with h1|h1
            . rcases mem_append.mp h1 with h2|h2
              . exact mem_toFinset.mpr h2
              . simp only [List.mem_singleton] at h2;exact absurd (h2 ▸ hwS) hxNotS
            . simp only [List.mem_singleton] at h1;exact absurd h1 hwv
       exact f7 k hk16 ⟨U,a,b,hInEq,eC a haIn,eC b hbIn,hab,
        fun hm=>hvNot (hvEq ▸ List.mem_append_left _ (mem_toFinset.mp hm)),hSeq ▸ run⟩
   . have subRaw1:∀ w ∈ S,w ∈ dZ:=by
      intro w hw
      rcases mem_append.mp (sub w hw) with h1|h1
      . exact h1
      . simp only [List.mem_singleton] at h1;have hpr_nv:bg (fM true v):=h1 ▸ eI run _ hw;have hpr_v:bg v:=kI hpr_nv;have hnv:fM true v=v:=kC (hv_plain hpr_v)
        by_cases h1':v ∈ dZ
        . rw [h1,hnv];exact h1'
        . exact False.elim (hv ⟨h1 ▸ hw,h1',hpr_v⟩)
     have hInSub:∀ w ∈ inputs,w ∈ S:=by
      intro w hw;obtain ⟨i,rfl⟩:=idxIn w hw
      apply cX run dZ (inputs.getD i.val zero) subRaw1
       (cp i) (bX i) (bQ.1 i)
      intro z hz hzne
      rcases mem_append.mp hz with hzIn|hzX
      . obtain ⟨j,rfl⟩:=idxIn z hzIn;exact bQ.2 i j (fun he=>hzne (by rw [he]))
      . simp only [List.mem_singleton] at hzX;rw [hzX];exact l0 i
     by_cases hx:qz ∈ S
     . have hEq:S=(qz :: inputs).toFinset:=by
        ext w
        constructor
        . intro hw
          rcases mem_append.mp (subRaw1 w hw) with h1|h1
          . exact mem_toFinset.mpr (mem_cons_of_mem _ h1)
          . simp only [List.mem_singleton] at h1;rw [h1];simp
        . intro hw
          rcases mem_cons.mp (mem_toFinset.mp hw) with rfl|h1
          . exact hx
          . exact hInSub w h1
       exact fL k hk16 (hEq ▸ run)
     . have hEq:S=inputs.toFinset:=by
        ext w
        constructor
        . intro hw
          rcases mem_append.mp (subRaw1 w hw) with h1|h1
          . exact mem_toFinset.mpr h1
          . simp only [List.mem_singleton] at h1;exact absurd (h1 ▸ hw) hx
        . intro hw;exact hInSub w (mem_toFinset.mp hw)
       exact i1 k hk16 (hEq ▸ run)
end S10
end PEqualNP.Outside.L_meta_6026
theorem PEqualNP.Outside.L_meta_6026 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∃ (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : List PEqualNP.CircuitLowerBounds.Gate), x1.gates = x5 :: x6 ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 (0 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by
 exact PEqualNP.Outside.L_meta_6026.S10.sV
  PEqualNP.Outside.L_meta_6026.S10.mi
  PEqualNP.Outside.L_meta_6026.S10.hZ
  PEqualNP.Outside.L_meta_6026.S10.i1
  PEqualNP.Outside.L_meta_6026.S10.f7
  PEqualNP.Outside.L_meta_6026.S10.fL
  PEqualNP.Outside.L_meta_6026.S10.et
