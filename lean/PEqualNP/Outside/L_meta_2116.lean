import Mathlib
import PEqualNP.Defs

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1674.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_2116
open PEqualNP.CircuitLowerBounds
abbrev Sig:=BitVec 512
def zero:Sig:=0
def one:Sig:=BitVec.allOnes 512
def neg (a:Sig):Sig := ~~~a
def bin (d:Nat) (a b:Sig):Sig :=
 if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a:Sig):Prop:=a ≠ zero ∧ a ≠ one
def allowed (u:Bool) (d:Nat):Prop:=d<2 ∨ (u=true ∧ d<4)
def qm (d:Nat):=if d=2 then 3 else if d=3 then 2 else d
theorem zS {u d} (h:allowed u d):d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3):=by
 rcases h with h | ⟨h,j⟩
 · omega
 · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3:=by omega
   rcases this with h1 | h1 | h1 | h1
   · exact Or.inl h1
   · exact Or.inr (Or.inl h1)
   · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
   · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem vX {u d} (h:allowed u d) (a b:Sig):bin d a b=bin (qm d) b a:=by
 rcases zS h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩<;>simp [bin,qm,BitVec.and_comm,BitVec.or_comm]
theorem yb {u d} (h:allowed u d):allowed u (qm d) ∧ qm (qm d)=d:=by
 rcases zS h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
 all_goals simp_all [qm,allowed]
def Live (u:Bool) (target:Sig):Nat → Finset Sig → Prop
 | 0,S=>S={target} ∧ proper target
 | k+1,S => ∃ (U:Finset Sig) (a b:Sig) (d:Nat),allowed u d ∧ S=insert a (insert b U) ∧
     proper a ∧ proper b ∧ a ≠ b ∧
     bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target:Sig} (hp:proper target):Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target:Sig} {k:Nat} {U:Finset Sig} {a b:Sig} {d:Nat} (hd:allowed u d)
   (ha:proper a) (hb:proper b) (hab:a ≠ b)
   (hfresh:bin d a b ∉ insert a (insert b U)) (tail:Live u target k (insert (bin d a b) U)) :
   Live u target (k+1) (insert a (insert b U)) :=
 ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target:Sig} {motive : ∀ (k:Nat) (S:Finset Sig),Live u target k S → Prop}
   (stop : ∀ (hp:proper target),motive 0 {target} (Live.stop hp))
   (binary : ∀ {k:Nat} {U:Finset Sig} {a b:Sig} {d:Nat} (hd:allowed u d)
     (ha:proper a) (hb:proper b) (hab:a ≠ b)
     (hfresh:bin d a b ∉ insert a (insert b U)) (tail:Live u target k (insert (bin d a b) U)),
     motive k (insert (bin d a b) U) tail →
     motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
   {k:Nat} {S:Finset Sig} (h:Live u target k S):motive k S h:=by
 induction k generalizing S with
 | zero =>
   obtain ⟨rfl,hp⟩:=h
   exact stop hp
 | succ k ih =>
   obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩:=h
   exact binary hd ha hb hab hf tail (ih tail)
private lemma jZ {u target k S} (h:Live u target k S) : ∀ a ∈ S,proper a:=by
 induction h using Live.ind with
 | stop hp=>simpa using hp
 | binary hd ha hb hab hf _ ih =>
   simp only [Finset.forall_mem_insert]
   exact ⟨ha,hb,fun a h=>ih a (Finset.mem_insert_of_mem h)⟩
private lemma vg {u target k S} (h:Live u target k S):S.card ≤ k+1:=by
 induction h using Live.ind with
 | stop hp=>simp
 | @binary k U a b d hd ha hb hab hf _ ih =>
   have hu:bin d a b ∉ U:=fun hm=>hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
   rw [Finset.card_insert_of_notMem hu] at ih
   have h1:=Finset.card_insert_le (a:=a) (s:=insert b U)
   have h2:=Finset.card_insert_le (a:=b) (s:=U)
   omega
def bit (i:Fin 512) (a:Sig):Bool:=a.getLsbD i.val
private lemma zv (i):bit i zero=false:=by simp [bit,zero]
private lemma qP (i):bit i one=true:=by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma je (i) (a:Sig):bit i (neg a) = !(bit i a):=by simp [bit,neg,i.isLt]
private lemma zX (i d) (a b:Sig):bit i (bin d a b) =
   (if d=0 then bit i a&&bit i b else if d=1 then bit i a||bit i b else
     if d=2 then bit i a && !(bit i b) else !(bit i a)&&bit i b):=by
 unfold bin
 split_ifs<;>simp [bit]
theorem zF {a b:Sig} (h : ∀ i,bit i a=bit i b):a=b :=
 BitVec.eq_of_getLsbD_eq fun j hj=>h ⟨j,hj⟩
def nrm (u:Bool) (a:Sig):Sig:=if u&&bit 0 a then neg a else a
theorem y8 (a:Sig):nrm false a=a:=rfl
theorem z216 (a:Sig):bit 0 (nrm true a)=false:=by
 cases h:bit 0 a<;>simp [nrm,h,je]
theorem z367 {u} {a:Sig} (h:bit 0 a=false):nrm u a=a:=by simp [nrm,h]
theorem neg_neg' (a:Sig):neg (neg a)=a:=by simp [neg]
theorem q117 (a:Sig):nrm true (neg a)=nrm true a:=by
 cases h:bit 0 a<;>simp [nrm,h,je,neg_neg']
theorem z364 {a:Sig} (h:proper (neg a)):proper a:=by
 refine ⟨?_,?_⟩
 · rintro rfl
   exact h.2 (by simp [neg,zero,one])
 · rintro rfl
   exact h.1 (by simp [neg,zero,one])
theorem z363 {u} {a:Sig} (h:proper (nrm u a)):proper a:=by
 unfold nrm at h
 split at h
 · exact z364 h
 · exact h
def prime (d:Bool) (a b:Sig):=if d then a ||| b else a &&& b
theorem jk (i) (d:Bool) (a b:Sig):bit i (prime d a b) =
   (if d then bit i a||bit i b else bit i a&&bit i b):=by cases d<;>simp [prime,bit]
theorem q168 (d:Bool) (a b:Sig) :
   ∃ e,e<4 ∧ nrm true (prime d a b)=bin e (nrm true a) (nrm true b):=by
 refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
   else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
 · split_ifs<;>omega
 · apply zF
   intro i
   cases d<;>cases ha:bit 0 a<;>cases hb:bit 0 b <;>
     simp only [nrm,jk,ha,hb,zX,je,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
       Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
     cases hx:bit i a<;>cases hy:bit i b<;>simp [hx,hy,je,jk]
def gv (w:List Sig) (g:Gate):Sig :=
 let xs:=g.inputs.map (fun i=>w.getD i zero)
 match g.op with
 | .and=>xs.foldr (prime false) one
 | .or=>xs.foldr (prime true) zero
 | .not=>neg (xs.headD zero)
 | _=>zero
def execute (gs:List Gate) (w:List Sig):List Sig :=
 gs.foldl (fun l g=>l ++ [gv l g]) w
def represented (w:List Sig) (v:Sig):Prop:=v ∈ w ∨ ¬proper v
def Repr (u:Bool) (w:List Sig) (v:Sig):Prop:=represented w (nrm u v)
private lemma z309 (a:Sig) :
   bin 0 a one=a ∧ bin 1 a zero=a ∧
   bin 0 a zero=zero ∧ bin 1 a one=one ∧
   bin 0 a a=a ∧ bin 1 a a=a ∧ bin 2 a a=zero ∧ bin 3 a a=zero ∧ bin 2 a zero=a ∧
   bin 3 zero a=a ∧ bin 2 zero a=zero ∧ bin 3 a zero=zero ∧ bin 0 zero a=zero ∧ bin 1 zero a=a ∧
   bin 0 one a=a ∧ bin 1 one a=one:=by
 refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩<;>apply zF<;>intro i <;>
   simp [zX,zv,qP]
private lemma wg {w:List Sig} {a:Sig} (h:represented w a) :
   a=zero ∨ a=one ∨ a ∈ w ∧ proper a:=by
 by_cases hz:a=zero
 · exact Or.inl hz
 by_cases ho:a=one
 · exact Or.inr (Or.inl ho)
 exact Or.inr (Or.inr ⟨h.resolve_right (fun x=>x ⟨hz,ho⟩),hz,ho⟩)
def witness (u:Bool) (w:List Sig) (z:Sig):Prop :=
 ∃ d a b,allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z=bin d a b
private lemma q124 {u w a b} (d:Nat) (hd:allowed u d) (ha:represented w a) (hb:represented w b)
   (no:u=true → a ≠ one ∧ b ≠ one) :
   represented w (bin d a b) ∨ witness u w (bin d a b):=by
 have rz:represented w zero:=Or.inr (fun h=>h.1 rfl)
 have ro:represented w one:=Or.inr (fun h=>h.2 rfl)
 obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩:=z309 a
 obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩:=z309 b
 by_cases he:a=b
 · subst b
   left
   rcases zS hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
   · exact a5.symm ▸ ha
   · exact a6.symm ▸ ha
   · exact a7.symm ▸ rz
   · exact a8.symm ▸ rz
 rcases wg ha with rfl | rfl | ⟨ham,hap⟩
 · left
   rcases zS hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
   · exact b13.symm ▸ rz
   · exact b14.symm ▸ hb
   · exact b11.symm ▸ rz
   · exact b10.symm ▸ hb
 · left
   rcases zS hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
   · exact b15.symm ▸ hb
   · exact b16.symm ▸ ro
   · exact absurd rfl (no hu).1
   · exact absurd rfl (no hu).1
 rcases wg hb with rfl | rfl | ⟨hbm,hbp⟩
 · left
   rcases zS hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
   · exact a3.symm ▸ rz
   · exact a2.symm ▸ ha
   · exact a9.symm ▸ ha
   · exact a12.symm ▸ rz
 · left
   rcases zS hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
   · exact a1.symm ▸ ha
   · exact a4.symm ▸ ro
   · exact absurd rfl (no hu).2
   · exact absurd rfl (no hu).2
 exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩
theorem jY (a:Sig):nrm true a ≠ one:=by
 intro h
 have:=z216 a
 rw [h,qP] at this
 exact Bool.noConfusion this
theorem q165 {u w a b} (d:Bool) (ha:Repr u w a) (hb:Repr u w b) :
   Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)):=by
 cases u
 · have e:prime d a b=bin (if d then 1 else 0) a b:=by cases d<;>rfl
   have h:=q124 (u:=false) (if d then 1 else 0) (Or.inl (by split<;>omega)) ha hb (by simp)
   unfold Repr
   simp only [y8] at h ⊢
   rwa [e]
 · obtain ⟨e,he,eq⟩:=q168 d a b
   unfold Repr
   rw [eq]
   exact q124 e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨jY a,jY b⟩)
theorem wt {u w} {v:Sig} (h:v=zero ∨ v=one):Repr u w v:=by
 refine Or.inr fun hp=>?_
 have:=z363 hp
 rcases h with rfl | rfl
 · exact this.1 rfl
 · exact this.2 rfl
private lemma q120 {u} (w:List Sig) (i:Nat):Repr u (w.map (nrm u)) (w.getD i zero):=by
 simp only [List.getD_eq_getElem?_getD]
 cases h:w[i]? with
 | none=>exact wt (Or.inl rfl)
 | some a=>exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
def wV (g:Gate):Bool:=match g.op with
 | .not=>true
 | _=>false
private lemma q164 {u target} {w:List Sig} {z:Sig} {k S c} (h:Live u target k S)
   (hz:represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S,a ∈ w++[z]) :
   ∃ k' S',k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S',a ∈ w:=by
 by_cases hm:z ∈ S
 · by_cases hw:z ∈ w
   · refine ⟨k,S,by omega,h,?_⟩
     intro a ha
     have hu:a ∈ w ∨ a=z:=by simpa using sub a ha
     rcases hu with hu | rfl
     · exact hu
     · exact hw
   · have hp:=jZ h z hm
     rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
     · exact False.elim ((hr.resolve_left hw) hp)
     · subst z
       let U:=S.erase (bin d a b)
       have ht:Live u target k (insert (bin d a b) U):=by simpa [U,Finset.insert_erase hm] using h
       have hu : ∀ v ∈ U,v ∈ w:=by
         intro v hv
         obtain ⟨hne,hm⟩:=Finset.mem_erase.mp hv
         simpa [hne] using sub v hm
       have hf:bin d a b ∉ insert a (insert b U):=by
         intro hh
         rcases Finset.mem_insert.mp hh with eq | u
         · exact hw (eq.symm ▸ ha)
         rcases Finset.mem_insert.mp u with eq | u
         · exact hw (eq.symm ▸ hb)
         · exact hw (hu _ u)
       exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
 · refine ⟨k,S,by omega,h,?_⟩
   intro a ha
   have hn:a ≠ z:=fun hh=>hm (hh ▸ ha)
   simpa [hn] using sub a ha
private lemma z233 (i) (w:List Sig) (j:Nat) :
   (w.map (bit i)).getD j false=bit i (w.getD j zero):=by
 simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
 cases w[j]? with
 | none=>exact (zv _).symm
 | some a=>rfl
private lemma wH (i) (g:Gate) (w:List Sig)
   (hg:g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
   bit i (gv w g)=g.op.eval (g.inputs.map fun j=>(w.map (bit i)).getD j false):=by
 obtain ⟨o,l⟩:=g
 simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
 simp only [z233]
 rcases hg with rfl | rfl | rfl
 · induction l with
   | nil=>exact qP _
   | cons a l ih =>
     change bit i (prime false _ _)=(_&&_)
     rw [jk]; exact congrArg (fun x=>bit i (w.getD a zero)&&x) ih
 · induction l with
   | nil=>exact zv _
   | cons a l ih =>
     change bit i (prime true _ _)=(_||_)
     rw [jk]; exact congrArg (fun x=>bit i (w.getD a zero)||x) ih
 · cases l with
   | nil =>
     change bit i (neg zero) = !false
     rw [je,zv]
   | cons a l=>exact je _ _
private lemma z224 (gs:List Gate) (i) (w:List Sig)
   (hg : ∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
   (execute gs w).map (bit i) =
   gs.foldl (fun (l:List Bool) g=>l++[g.op.eval (g.inputs.map fun j=>l.getD j false)]) (w.map (bit i)):=by
 induction gs generalizing w with
 | nil=>rfl
 | cons g gs ih =>
   change (execute gs (w++[gv w g])).map _=_
   rw [ih _ (fun a ha=>hg a (by simp [ha]))]
   simp only [List.foldl_cons,List.map_append,List.map_singleton,wH i g w (hg g (by simp))]
abbrev Wire (R:Type):=R → Bool
def inv {R} (a:Wire R):Wire R:=fun r => !(a r)
def combine {R} (isOr:Bool) (a b:Wire R):Wire R :=
 if isOr then fun r=>a r||b r else fun r=>a r&&b r
def comb {R} (d:Nat) (a b:Wire R):Wire R :=
 if d=0 then combine false a b else if d=1 then combine true a b else
   if d=2 then combine false a (inv b) else combine false (inv a) b
def Constant {R} (a:Wire R):Prop := ∃ b:Bool,a=fun _=>b
noncomputable def cost {R} (a:Wire R):Nat:=by
 classical exact if Constant a then 1 else 0
noncomputable def mass {R} (xs:List (Wire R)):Nat:=(xs.map cost).sum
def Available {R} (u:Bool) (pool:List (Wire R)) (v:Wire R):Prop :=
 v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)
def supply {R} (u:Bool) (pool xs:List (Wire R)) := ∀ a ∈ xs,Available u pool a
def Reach {R} (u:Bool) (roots:List (Wire R)):Nat → List (Wire R) → Prop
 | 0,b=>b=roots
 | p+1,c => ∃ (op:Bool) (bank:List (Wire R)) (a b:Wire R),Reach u roots p bank ∧ Available u bank a ∧
     Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots:List (Wire R)} : Reach u roots 0 roots:=rfl
theorem Reach.two {R u} {roots:List (Wire R)} {p bank a b} (op:Bool) (h:Reach u roots p bank)
   (ha:Available u bank a) (hb:Available u bank b):Reach u roots (p+1) (combine op a b :: bank) :=
 ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots:List (Wire R)} {motive : ∀ p bank,Reach u roots p bank → Prop}
   (start:motive 0 roots Reach.start)
   (two : ∀ {p bank a b} (op:Bool) (h:Reach u roots p bank) (ha:Available u bank a)
     (hb:Available u bank b),motive p bank h →
     motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
   {p bank} (h:Reach u roots p bank):motive p bank h:=by
 induction p generalizing bank with
 | zero =>
   obtain rfl:=h
   exact start
 | succ p ih =>
   obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩:=h
   exact two op h ha hb (ih h)
def kept {α : Type} (save:Bool) (x : α) (xs:List α):=if save then x::xs else xs
def Run {R} (u:Bool) (goal:Wire R):Nat → List (Wire R) → Prop
 | 0,zs=>List.Perm [goal] zs
 | s+1,zs => ∃ (op:Nat) (ka kb:Bool) (a b:Wire R) (rest:List (Wire R)),allowed u op ∧ (a::b::rest).Perm zs ∧
     Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal:Wire R} : Run u goal 0 [goal]:=List.Perm.refl _
theorem Run.perm {R u} {goal:Wire R} {s:Nat} {xs zs:List (Wire R)} (p:xs.Perm zs)
   (h:Run u goal s xs):Run u goal s zs:=by
 cases s with
 | zero=>exact List.Perm.trans h p
 | succ s =>
   obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩:=h
   exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal:Wire R} {s:Nat} {a b:Wire R} {rest:List (Wire R)} (op:Nat) (hd:allowed u op) (ka kb:Bool)
   (h:Run u goal s (comb op a b :: kept ka a (kept kb b rest))):Run u goal (s+1) (a::b::rest) :=
 ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal:Wire R} {motive : ∀ s ws,Run u goal s ws → Prop}
   (stop:motive 0 [goal] Run.stop)
   (perm : ∀ {s xs zs} (p:List.Perm xs zs) (h:Run u goal s xs),motive s xs h → motive s zs (Run.perm p h))
   (two : ∀ {s a b rest} (op:Nat) (hd:allowed u op) (ka kb:Bool) (h:Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
     motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
   {s ws} (h:Run u goal s ws):motive s ws h:=by
 induction s generalizing ws with
 | zero=>exact perm h Run.stop stop
 | succ s ih =>
   obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩:=h
   exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))
theorem jD {R} (a:Wire R) (xs):mass (a::xs)=cost a + mass xs:=by
 simp [mass]
theorem z148 {R} (a:Wire R) (xs) (k:Bool):mass xs ≤ mass (kept k a xs):=by
 cases k<;>simp [kept,jD]
theorem vx {R} {a:Wire R} (h:Constant a):Constant (inv a):=by
 obtain ⟨v,rfl⟩:=h
 exact ⟨!v,rfl⟩
theorem inv_inv' {R} (a:Wire R):inv (inv a)=a:=by
 funext r
 simp [inv]
theorem z296 {R} (a:Wire R):cost (inv a)=cost a:=by
 have : Constant (inv a) ↔ Constant a := ⟨fun h=>inv_inv' a ▸ vx h,vx⟩
 by_cases h:Constant a
 · simp only [cost,if_pos h,if_pos (this.mpr h)]
 · simp only [cost,if_neg h,if_neg (fun x=>h (this.mp x))]
theorem yi {R u} {bank:List (Wire R)} {a} (hu:u=true) (h:Available u bank a):Available u bank (inv a):=by
 rcases h with h | h | ⟨_,h⟩
 · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
 · exact Or.inr (Or.inl (vx h))
 · exact Or.inl h
theorem z141 {R} {a b:Wire R} (op) (h:Constant a) (g:Constant b) :
   Constant (combine op a b):=by
 obtain ⟨v,rfl⟩:=h
 obtain ⟨w,rfl⟩:=g
 cases op<;>exact ⟨_,rfl⟩
theorem z137 {R u} (op) {a b:Wire R} {bank}
   (h:Constant a ∨ Constant b) (ha:Available u bank a) (hb:Available u bank b) :
   Available u bank (combine op a b):=by
 rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
 · cases op<;>cases v
   · exact Or.inr (Or.inl ⟨false,by funext x; simp [combine]⟩)
   · simpa [combine] using hb
   · simpa [combine] using hb
   · exact Or.inr (Or.inl ⟨true,by funext x; simp [combine]⟩)
 · cases op<;>cases v
   · exact Or.inr (Or.inl ⟨false,by funext x; simp [combine]⟩)
   · simpa [combine] using ha
   · simpa [combine] using ha
   · exact Or.inr (Or.inl ⟨true,by funext x; simp [combine]⟩)
theorem vY {R u} {bank v} (w:Wire R) (h:Available u bank v) :
   Available u (w::bank) v :=
 h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))
theorem z387 {R u} (roots:List (Wire R)) {p bank a b} (op) (hp:Reach u roots p bank)
   (ha:Available u bank a) (hb:Available u bank b) :
   ∃ q next,Reach u roots q next ∧ Available u next (combine op a b) ∧
       (∀ v,Available u bank v → Available u next v) ∧
       q+cost a+cost b ≤ p+1+cost (combine op a b):=by
 classical
 by_cases c:Constant a ∨ Constant b
 · refine ⟨p,bank,hp,z137 op c ha hb,fun _ h=>h,?_⟩
   by_cases ca:Constant a<;>by_cases cb:Constant b
   · simp [cost,ca,cb,z141 op ca cb]
   · simp [cost,ca,cb]
   · simp [cost,ca,cb]
   · exact False.elim (c.elim ca cb)
 · have ca : ¬Constant a:=fun h=>c (Or.inl h)
   have cb : ¬Constant b:=fun h=>c (Or.inr h)
   exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h=>vY _ h,
     by simp [cost,ca,cb]⟩
theorem z125 {R u} {bank:List (Wire R)} {d a b} (hd:allowed u d) (ha:Available u bank a) (hb:Available u bank b) :
   ∃ op x y,comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b:=by
 rcases zS hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
 · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
 · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
 · exact ⟨false,a,inv b,rfl,ha,yi hu hb,rfl,z296 b⟩
 · exact ⟨false,inv a,b,rfl,yi hu ha,hb,z296 a,rfl⟩
theorem z290 {R u} (roots:List (Wire R)) {p bank a b} (d) (hd:allowed u d) (hp:Reach u roots p bank)
   (ha:Available u bank a) (hb:Available u bank b) :
   ∃ q next,Reach u roots q next ∧ Available u next (comb d a b) ∧
       (∀ v,Available u bank v → Available u next v) ∧
       q+cost a+cost b ≤ p+1+cost (comb d a b):=by
 obtain ⟨op,x,y,e,hx,hy,cx,cy⟩:=z125 hd ha hb
 rw [e,←cx,←cy]
 exact z387 roots op hp hx hy
theorem z271 {α : Type} {k:Bool} {x a : α} {xs} (h:x ∈ kept k a xs) :
   x=a ∨ x∈xs:=by cases k<;>simp_all [kept]
theorem contraction {R u} {goal:Wire R} (nc : ¬Constant goal) {s ws}
   (h:Run u goal s ws) (roots:List (Wire R)) {p bank}
   (hp:Reach u roots p bank) (hs:supply u bank ws) :
   ∃ q next,Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s:=by
 classical
 induction h using Run.ind generalizing p bank with
 | stop =>
   exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
 | perm eq _ ih =>
   have hsub:supply u bank _:=fun v hv=>hs v (eq.mem_iff.mp hv)
   obtain ⟨q,W,hW,hv,hl⟩:=ih hp hsub
   exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
 | @two s a b rest op hd ka kb _ ih =>
   obtain ⟨r,T,hT,hz,inc,le⟩:=z290 roots op hd hp (hs a (by simp)) (hs b (by simp))
   have ht:supply u T (comb op a b :: kept ka a (kept kb b rest)):=by
     intro v h
     rcases List.mem_cons.mp h with rfl | hh
     · exact hz
     · apply inc v
       apply hs
       rcases z271 hh with rfl | hh
       · simp
       · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (z271 hh))
   obtain ⟨q,W,hW,hv,hl⟩:=ih hT ht
   have hlen:=z148 a (kept kb b rest) ka
   have hlen':=z148 b rest kb
   rw [jD] at hl
   refine ⟨q,W,hW,hv,?_⟩
   rw [jD,jD]
   omega
def zf {R S:Type} (rows:S → R) (a:Wire R):Wire S :=
 fun r=>a (rows r)
theorem z132 {R S:Type} (rows:S → R) (k:Bool) (a:Wire R) (ws) :
   (kept k a ws).map (zf rows) =
   kept k (zf rows a) (ws.map (zf rows)):=by
 cases k<;>simp [kept]
theorem we {R S:Type} (rows:S → R) (d) (a b:Wire R) :
   zf rows (comb d a b)=comb d (zf rows a) (zf rows b):=by
 unfold comb
 split_ifs<;>rfl
theorem z214 {R S:Type} {u} (rows:S → R) {goal s ws} (h:Run u goal s ws) :
   Run u (zf rows goal) s (ws.map (zf rows)):=by
 induction h using Run.ind with
 | stop=>exact Run.stop
 | perm p _ ih=>exact Run.perm (p.map _) ih
 | two op hd ka kb _ ih =>
   simp only [List.map_cons,z132,we] at ih ⊢
   exact Run.two op hd ka kb ih
theorem ju {R S:Type} {u} (rows:S → R) {goal s ws} (h:Run u goal s ws)
   (nc : ¬Constant (zf rows goal)) {roots:List (Wire S)} {p bank L}
   (hp:Reach u roots p bank) (hs:supply u bank (ws.map (zf rows)))
   (hl : ∀ q bs,Reach u roots q bs → Available u bs (zf rows goal) → L ≤ q) :
   L + mass (ws.map (zf rows)) ≤ p+s:=by
 obtain ⟨q,bs,hq,ht,hle⟩:=contraction nc (z214 rows h) roots hp hs
 have hqle:=hl q bs hq ht
 omega
abbrev Row:=Fin 512
def observe (a:Sig):Wire Row:=fun r=>bit r a
def table (f:Wire Row):Sig :=
 (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
theorem j7 (f:Wire Row) (r:Row):bit r (table f)=f r:=by
 simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]
theorem v4 (v:Sig):table (observe v)=v:=by
 apply BitVec.eq_of_getLsbD_eq
 intro j hj
 exact j7 (observe v) ⟨j,hj⟩
theorem z134 (f:Wire Row):observe (table f)=f:=by
 funext r
 exact j7 f r
theorem q115 (a:Sig):observe (neg a)=inv (observe a):=by
 funext r
 exact je _ _
theorem q116 (d:Nat) (a b:Sig) :
   observe (bin d a b)=comb d (observe a) (observe b):=by
 funext r
 simp only [observe,zX,comb]
 split_ifs<;>rfl
theorem z275 {α β : Type} (f : α → β) (d:Bool) (a : α) (l:List α) :
   (kept d a l).map f=kept d (f a) (l.map f):=by cases d<;>rfl
theorem w5 {α : Type} (k:Bool) (a : α) (l:List α)
   (hn:l.Nodup) (ha:a ∉ l):(kept k a l).Nodup:=by cases k<;>simp [kept,hn,ha]
theorem vi (k:Bool) (a:Sig) (l:List Sig) :
   (kept k a l).toFinset=if k then insert a l.toFinset else l.toFinset:=by
 cases k<;>simp [kept]
theorem z100 {u} {T:Sig} {k S} (h:Live u T k S) (v:List Sig)
   (hv:v.Nodup) (eqv:v.toFinset=S):Run u (observe T) k (v.map observe):=by
 classical
 induction h using Live.ind generalizing v with
 | stop hp =>
   have eq:[T].Perm v:=by
     apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
     simpa [eqv]
   exact Run.perm (eq.map _) Run.stop
 | @binary k U a b d hd ha hb hab fresh _ ih =>
   let rest:=((U.erase a).erase b).toList
   let ka:=decide (a ∈ U)
   let kb:=decide (b ∈ U)
   let mid:=kept kb b rest
   let tail:=kept ka a mid
   have er:rest.toFinset=(U.erase a).erase b:=by simp [rest]
   have ar:a ∉ rest:=by simp [rest]
   have br:b ∉ rest:=by simp [rest]
   have hr:rest.Nodup:=Finset.nodup_toList _
   have bm:=w5 kb b rest hr br
   have am:a ∉ mid:=by cases h:kb<;>simp [mid,kept,h,hab,ar]
   have nd:=w5 ka a mid bm am
   have ht:tail.toFinset=U:=by
     change (kept ka a (kept kb b rest)).toFinset=U
     rw [vi,vi,er]
     ext j
     by_cases aa:a ∈ U<;>by_cases bb:b ∈ U<;>by_cases aj:j=a <;>
       by_cases bj:j=b<;>simp_all [ka,kb]
   have hf:bin d a b ∉ tail:=by
     intro hz
     exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
   have progress:=ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
   change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
   rw [List.map_cons,z275,z275,q116] at progress
   have perm:(a::b::rest).Perm v:=by
     apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
     ext j
     by_cases ja:j=a<;>by_cases jb:j=b<;>simp_all [er]
   exact Run.perm (perm.map _) (Run.two d hd ka kb progress)
theorem q157 (f:Wire Row):table (inv f)=neg (table f):=by
 rw [←v4 (neg (table f)),q115,z134]
theorem z253 (d:Bool) (f g:Wire Row) :
   table (combine d f g)=prime d (table f) (table g):=by
 apply zF
 intro r
 rw [j7,jk,j7,j7]
 cases d<;>rfl
theorem v7 {u} {bank:List (Wire Row)} {a} (h:Available u bank a) :
   Repr u ((bank.map table).map (nrm u)) (table a):=by
 rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
 · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
 · apply wt
   cases b
   · exact Or.inl (zF fun i=>(j7 _ i).trans (zv i).symm)
   · exact Or.inr (zF fun i=>(j7 _ i).trans (qP i).symm)
 · have:=q157 a
   refine Or.inl ?_
   rw [←q117,←this]
   exact List.mem_map_of_mem (List.mem_map_of_mem hm)
theorem yT {u} {roots:List (Wire Row)} {p bank}
   (h:Reach u roots p bank) {T k S} (run:Live u T k S)
   (sub : ∀ a ∈ S,a ∈ (bank.map table).map (nrm u)) :
   ∃ l V,l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V,a ∈ (roots.map table).map (nrm u):=by
 induction h using Reach.ind generalizing k S with
 | start=>exact ⟨k,S,by omega,run,sub⟩
 | @two p bank a b d h ha hb ih =>
   rw [List.map_cons,List.map_cons,z253] at sub
   have rep:=q165 d (v7 ha) (v7 hb)
   obtain ⟨k',S',hk,run',sub'⟩:=q164 (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
     (fun a hm=>by simpa [or_comm] using sub a hm)
   obtain ⟨l,V,hl,hr,hs⟩:=ih run' sub'
   exact ⟨l,V,by omega,hr,hs⟩
def zU (a:Sig):Bool := !(bit 0 a)
theorem q118 {u} {w:List Sig} (h:w.all zU=true):w.map (nrm u)=w:=by
 have e:w.map (nrm u)=w.map id:=by
   apply List.map_congr_left
   intro a ha
   exact z367 (by simpa [zU] using List.all_eq_true.mp h a ha)
 rw [e,List.map_id]
theorem vt {u} {roots:List Sig} {p bank T} (hp:proper T) (nT:zU T=true) (nR:roots.all zU=true)
   (h:Reach u (roots.map observe) p bank) (hit:Available u bank (observe T)) :
   ∃ k S,k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S,a ∈ roots:=by
 have hm:=v7 hit
 rw [v4] at hm
 unfold Repr at hm
 rw [z367 (by simpa [zU] using nT)] at hm
 have mem:=hm.resolve_right (fun hn=>hn hp)
 obtain ⟨l,V,hl,hr,hs⟩:=yT h (Live.stop hp) (by simpa using mem)
 refine ⟨l,V,by omega,hr,?_⟩
 have e:(roots.map observe).map table=roots:=by simp [List.map_map,Function.comp_def,v4]
 rw [e,q118 nR] at hs
 exact hs
theorem jy {u T k S} (h:Live u T k S) {r s:Row}
   (diff:bit r T ≠ bit s T) : ∃ a ∈ S,bit r a ≠ bit s a:=by
 induction h using Live.ind with
 | stop hp=>exact ⟨_,by simp,diff⟩
 | @binary k U a b d hd ha hb hab hf _ ih =>
   obtain ⟨v,hv,hd⟩:=ih
   rcases Finset.mem_insert.mp hv with rfl | hu
   · by_cases aeq:bit r a=bit s a
     · refine ⟨b,by simp,?_⟩
       intro beq
       exact hd (by rw [zX,zX,aeq,beq])
     · exact ⟨a,by simp,aeq⟩
   · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩
theorem j8 {u T k S} (h:Live u T k S) (roots:List Sig) (a:Sig)
   (sub : ∀ v ∈ S,v ∈ roots) (r s:Row) (diff:bit r T ≠ bit s T)
   (isolated : ∀ v ∈ roots,v ≠ a → bit r v=bit s v):a ∈ S:=by
 obtain ⟨v,hv,hd⟩:=jy h diff
 by_cases veq:v=a
 · simpa [veq] using hv
 · exact False.elim (hd (isolated v (sub v hv) veq))
def inputs:List Sig:=[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph:Sig:=0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def sample (r:Row) (j:Fin 9):=bit r (inputs.getD j.val zero)
def edge (x:Fin 9 → Bool):Bool :=
 (x 0&&x 1)||(x 1&&x 2)||(x 2&&x 3)||(x 3&&x 4)||(x 4&&x 0) ||
 (x 0&&x 5)||(x 1&&x 6)||(x 2&&x 7)||(x 3&&x 8)||(x 5&&x 7) ||
 (x 6&&x 8)||(x 8&&x 5)
theorem z123 : ∀ r:Row,bit r graph=edge (sample r):=by decide +kernel
theorem jB:proper graph:=by unfold proper; decide +kernel
theorem z116:List.ofFn (fun j:Fin 9=>inputs.getD j.val zero)=inputs:=rfl
theorem sampled (r:Row):List.ofFn (sample r)=inputs.map (bit r):=by
 rw [←z116]
 rw [List.map_ofFn]
 rfl
theorem vr (C:Circuit) (h:PEqualNP.MetaComplexity.FanInTwo C)
   (i:Nat) (r:Row):bit r ((execute C.gates inputs).getD i zero) =
     (C.wires (List.ofFn (sample r))).getD i false:=by
 rw [←z233,z224 _ _ _ (fun g hg=>(h g hg).1),sampled]
 rfl
theorem zO (gs:List Gate) (ws:List Sig) : ∃ l,execute gs ws=ws ++ l:=by
 induction gs generalizing ws with
 | nil=>exact ⟨[],by simp [execute]⟩
 | cons g gs ih =>
   obtain ⟨l,hl⟩:=ih (ws++[gv ws g])
   exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩
def rename (f:Row → Row) (a:Sig):=table fun r=>bit (f r) a
theorem qA (f:Row → Row) (a:Sig) (r:Row) :
   bit r (rename f a)=bit (f r) a:=j7 _ _
theorem qK (f:Row → Row) (a:Sig) :
   observe (rename f a)=zf f (observe a):=by funext r; exact qA f a r
theorem ji (f:Row → Row) (d:Nat) (a b:Sig) :
   rename f (bin d a b)=bin d (rename f a) (rename f b):=by
 apply zF
 intro r
 simp only [qA,zX]
theorem yS (f:Row → Row) (onto:Function.Surjective f) :
   Function.Injective (rename f):=by
 intro a b h
 apply BitVec.eq_of_getLsbD_eq
 intro j hj
 obtain ⟨r,hr⟩:=onto ⟨j,hj⟩
 have he:=congrArg (bit r) h
 change bit ⟨j,hj⟩ a=bit ⟨j,hj⟩ b
 rw [qA,qA,hr] at he
 exact he
theorem jh (f:Row → Row):rename f zero=zero ∧ rename f one=one:=by
 constructor<;>apply BitVec.eq_of_getLsbD_eq<;>intro j hj
 · exact (qA f zero ⟨j,hj⟩).trans ((zv _).trans (zv ⟨j,hj⟩).symm)
 · exact (qA f one ⟨j,hj⟩).trans ((qP _).trans (qP ⟨j,hj⟩).symm)
theorem z277 {u T k S} (h:Live u T k S) (f:Row → Row) (onto:Function.Surjective f) :
   Live u (rename f T) k (S.image (rename f)):=by
 have inj:=yS f onto
 obtain ⟨fz,fo⟩:=jh f
 have pp (v) (p:proper v):proper (rename f v) :=
   ⟨fun e=>p.1 (inj (e.trans fz.symm)),fun e=>p.2 (inj (e.trans fo.symm))⟩
 induction h using Live.ind with
 | stop hp=>simpa using Live.stop (pp _ hp)
 | @binary k U a b d hd ha hb hab hf _ ih =>
   have fresh:rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f):=by
     intro hm
     obtain ⟨v,hv,eq⟩:=Finset.mem_image.mp hm
     exact hf (inj eq ▸ hv)
   simp only [Finset.image_insert,ji] at fresh ih ⊢
   exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh=>hab (inj hh)) fresh ih
theorem w8 {u T k S} (h:Live u T k S) (none:u=false) {r s:Row}
   (pos:bit r T=true) (negRow:bit s T=false) :
   ∃ a ∈ S,bit r a=true ∧ bit s a=false:=by
 induction h using Live.ind with
 | stop hp=>exact ⟨_,by simp,pos,negRow⟩
 | @binary k U a b d hd ha hb hab hf _ ih =>
   obtain ⟨v,hv,hp,hn⟩:=ih
   rcases Finset.mem_insert.mp hv with rfl | hu
   · rw [zX] at hp hn
     subst none
     rcases zS hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
     · cases p:bit r a<;>cases q:bit s a<;>cases u:bit r b<;>cases z:bit s b<;>simp_all
     · cases p:bit r a<;>cases q:bit s a<;>cases u:bit r b<;>cases z:bit s b<;>simp_all
     · exact Bool.noConfusion h
     · exact Bool.noConfusion h
   · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩
def Lower (u:Bool) (roots:List Sig) (T:Sig) (L:Nat):Prop :=
 ∀ p bank,Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem q260 {R u} {roots:List (Wire R)} {p bank} (h:Reach false roots p bank):Reach u roots p bank:=by
 have up {bank:List (Wire R)} {a} (h:Available false bank a):Available u bank a :=
   h.imp id (Or.imp id (fun h=>Bool.noConfusion h.1))
 induction h using Reach.ind with
 | start=>exact Reach.start
 | two op h ha hb ih=>exact Reach.two op ih (up ha) (up hb)
theorem z369 {u roots T L} (h:Lower true roots T L):Lower u roots T L:=by
 cases u
 · exact fun p bank hr ha=>h p bank (q260 hr) (ha.imp id (Or.imp id (fun h=>Bool.noConfusion h.1)))
 · exact h
def Impossible (u:Bool) (T:Sig) (cap:Nat) (S:Finset Sig):Prop :=
 ∀ k,k ≤ cap → ¬Live u T k S
def Essential (T:Sig) (roots:List Sig) (a:Sig):Prop :=
 ∃ r s:Row,bit r T ≠ bit s T ∧ ∀ v ∈ roots,v ≠ a → bit r v=bit s v
theorem y9 {u roots T L} (hp:proper T) (nT:zU T=true) (nR:roots.all zU=true)
   (essential : ∀ a ∈ roots,Essential T roots a)
   (noRun:Impossible u T L roots.toFinset):Lower u roots T (L+1):=by
 intro p bank h ha
 obtain ⟨k,S,hk,run,hs⟩:=vt hp nT nR h ha
 have he:roots.toFinset=S:=by
   ext a
   rw [List.mem_toFinset]
   refine ⟨fun hm=>?_,hs a⟩
   obtain ⟨r,s,hd,iso⟩:=essential _ hm
   exact j8 run roots a hs r s hd iso
 by_contra! small
 exact noRun k (by omega) (he.symm ▸ run)
theorem jP {v:Sig} (hv:proper v) : ¬Constant (observe v):=by
 rintro ⟨b,h⟩
 have hr:Repr false [] v:=by
   apply wt
   cases b
   · exact Or.inl (zF fun i=>(congrFun h i).trans (zv i).symm)
   · exact Or.inr (zF fun i=>(congrFun h i).trans (qP i).symm)
 have hr' : represented [] v:=hr
 exact (hr'.resolve_left (by simp)) hv
theorem z272 {R} (a b:List (Wire R)):mass (a++b)=mass a + mass b:=by
 simp [mass]
theorem yW {R} (xs:List (Wire R)) (hc : ∀ x ∈ xs,Constant x) :
   mass xs=xs.length:=by
 induction xs with
 | nil=>simp [mass]
 | cons a xs ih =>
   have ha:=hc a (by simp)
   simp only [jD,List.length_cons,cost,if_pos ha,ih (fun x hx=>hc x (by simp [hx]))]
   omega
theorem yp {u} {roots other:List Sig} {T G:Sig} (pT:proper T) (nT:zU T=true) (nR:roots.all zU=true) (pG:proper G)
   (r:Row → Row) (eq:rename r T=G)
   (covered : ∀ a ∈ roots,Available u (other.map observe) (observe (rename r a)))
   (singles:Finset Sig) (necessary : ∀ a ∈ singles,Essential T roots a)
   (constant : ∀ a ∈ singles,Constant (observe (rename r a)))
   (L:Nat) (prior:Lower u other G L):Lower u roots T (L + singles.card):=by
 classical
 intro p bank hh ha
 obtain ⟨k,S,hk,run,sub⟩:=vt pT nT nR hh ha
 have subS:singles ⊆ S:=by
   intro a hs
   obtain ⟨i,j,hd,hiso⟩:=necessary a hs
   exact j8 run roots a sub i j hd hiso
 let front:=singles.toList ++ (S \ singles).toList
 have nd:front.Nodup:=by
   simp only [front,List.nodup_append]
   refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
   intro a ha b hb he
   subst b
   exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
 have fe:front.toFinset=S:=by ext a; simp [front,Finset.union_sdiff_of_subset subS]
 have run':=z100 run front nd fe
 have gc:zf r (observe T)=observe G:=(qK _ _).symm.trans (congrArg observe eq)
 have supp:supply u (other.map observe) ((front.map observe).map (zf r)):=by
   intro v hv
   obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
   obtain ⟨a,hmem,rfl⟩:=List.mem_map.mp hm
   rw [←qK]
   exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
 have bound:=ju r run' (gc ▸ jP pG) Reach.start supp
   (L:=L) (gc ▸ prior)
 have massLo:singles.card ≤ mass ((front.map observe).map (zf r)):=by
   simp only [front,List.map_append,z272]
   let xs:=(singles.toList.map observe).map (zf r)
   have only : ∀ v ∈ xs,Constant v:=by
     intro v hv
     obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
     obtain ⟨a,hmem,rfl⟩:=List.mem_map.mp hm
     rw [←qK]
     exact constant _ (Finset.mem_toList.mp hmem)
   have sz:=yW xs only
   simp only [xs,List.length_map,Finset.length_toList] at sz
   change singles.card ≤ mass xs + _
   rw [sz]
   omega
 omega
def q6 (ws:List Sig) (a b:Sig) (d:Nat) (ka kb:Bool):List Sig :=
 bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
theorem w7 {l:List Sig} (h:l.Nodup) (a:Sig):(l.erase a).toFinset=l.toFinset.erase a:=by
 ext x
 simp [h.mem_erase_iff]
theorem q188 {u} {T:Sig} {cap:Nat} {ws:List Sig} (hn:ws.Nodup) (out:T ∉ ws)
   (twoStep : ∀ a ∈ ws,∀ b ∈ ws,∀ d,allowed u d → ∀ ka kb,a ≠ b → bin d a b ∉ ws →
     proper (bin d a b) → (q6 ws a b d ka kb).length ≤ cap →
     Impossible u T (cap-1) (q6 ws a b d ka kb).toFinset) :
   Impossible u T cap ws.toFinset:=by
 classical
 intro k hk h
 generalize he:ws.toFinset=S at h
 induction h using Live.ind with
 | stop hp =>
   have mem:T ∈ ws.toFinset:=he.symm ▸ Finset.mem_singleton_self _
   exact out (List.mem_toFinset.mp mem)
 | @binary k U a b d hd ha hb hab hf tail _ =>
   have am:a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
   have bm:b ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
   have fresh:bin d a b ∉ ws:=fun h=>hf (he ▸ List.mem_toFinset.mpr h)
   have hz:=jZ tail _ (Finset.mem_insert_self _ _)
   let ka:=decide (a ∈ U)
   let kb:=decide (b ∈ U)
   let rest:=(ws.erase a).erase b
   have er:rest.toFinset=(ws.toFinset.erase a).erase b:=by
     rw [show rest=(ws.erase a).erase b by rfl,w7 (hn.erase _) b,
       w7 hn a]
   have ke:(kept ka a (kept kb b rest)).toFinset=U:=by
     rw [vi,vi,er,he]
     ext j
     by_cases aa:a ∈ U<;>by_cases bb:b ∈ U<;>by_cases ja:j=a <;>
       by_cases jb:j=b<;>simp_all [ka,kb]
   have rn:rest.Nodup:=(hn.erase _).erase _
   have ar:a ∉ rest:=fun h=>(hn.not_mem_erase) (List.mem_of_mem_erase h)
   have br:b ∉ rest:=(hn.erase a).not_mem_erase
   have nk:=w5 kb b rest rn br
   have ax:a ∉ kept kb b rest:=by cases kb<;>simp [kept,ar,hab]
   have nd:(q6 ws a b d ka kb).Nodup:=by
     refine List.nodup_cons.mpr ⟨?_,w5 ka a _ nk ax⟩
     intro h
     exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
   have eq:(q6 ws a b d ka kb).toFinset=insert (bin d a b) U:=by
     change (bin d a b::kept ka a (kept kb b rest)).toFinset=_
     simp [ke]
   have sc:=vg tail
   have len:(q6 ws a b d ka kb).length ≤ cap:=by
     rw [←List.toFinset_card_of_nodup nd,eq]
     omega
   exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)
def Sep (T:Sig) (width:Nat) (pos negRow:Fin width → Row)
   (asig:Sig → BitVec width × BitVec width):Prop :=
 (∀ i,bit (pos i) T=true ∧ bit (negRow i) T=false) ∧
 ∀ w i,(asig w).1.getLsbD i.val=bit (pos i) w ∧
   (asig w).2.getLsbD i.val=bit (negRow i) w
def column {n} (oriented:Bool) (s:BitVec n × BitVec n):BitVec n :=
 if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2
def covered {n} (oriented:Bool) (sig:Sig → BitVec n × BitVec n):List Sig → BitVec n
 | []=>0
 | a::ws=>column oriented (sig a) ||| covered oriented sig ws
theorem z292 {n:Nat} {oriented:Bool} {sig:Sig → BitVec n × BitVec n} {ws:List Sig} {i:Fin n} :
   (covered oriented sig ws).getLsbD i.val=true ↔
   ∃ a ∈ ws,(column oriented (sig a)).getLsbD i.val=true:=by
 induction ws with
 | nil=>simp [covered]
 | cons a ws ih =>
   simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]
theorem z293 {u T k S} (h:Live u T k S) {ws:List Sig} (he:ws.toFinset=S)
   {width:Nat} {r s:Fin width → Row} {sig} (correct:Sep T width r s sig)
   (oriented:Bool) (zeroNot:oriented=true → u=false) :
   covered oriented sig ws=BitVec.allOnes width:=by
 apply BitVec.eq_of_getLsbD_eq
 intro j hj
 let i:Fin width := ⟨j,hj⟩
 have yes:=(correct.1 i).1
 have no:=(correct.1 i).2
 rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
 apply (z292 (i:=i)).mpr
 cases oriented with
 | false =>
   obtain ⟨a,ha,hd⟩:=jy h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
   refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
   simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
   cases hx:bit (r i) a<;>cases hy:bit (s i) a<;>simp_all
 | true =>
   obtain ⟨a,ha,hp,hn⟩:=w8 h (zeroNot rfl) yes no
   refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
   simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
     Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]
theorem vW {u T ws k} (h:Live u T k (List.toFinset ws)) {n:Nat} {r s:Fin n → Row} {sig}
   (correct:Sep T n r s sig) :
   covered (!u) sig ws=BitVec.allOnes n:=by
 apply z293 h rfl correct
 simp
def Slice (u:Bool) (raw:List Sig) (T d:Sig) (L:Nat):Prop :=
 ∃ (f:Row → Row) (roots:List Sig),(∀ r,bit (f r) d=true) ∧
   (∀ a ∈ raw,Available u (roots.map observe) (zf f (observe a))) ∧
   ¬Constant (zf f (observe T)) ∧
   ∀ p bank,Reach u (roots.map observe) p bank → Available u bank (zf f (observe T)) → L ≤ p
def masked (d a:Sig):=a &&& d
def zw (u:Bool) (d:Sig) (pool:List Sig) (a:Sig) :=
 let m:=masked d a
 m == zero||m == d||(pool.map (masked d)).any (fun v=>v==m) ||
   (u&&(let c:=masked d (neg a); (pool.map (masked d)).any (fun v=>v==c)))
theorem z149 {f:Row → Row} {d a b:Sig} (dom : ∀ r,bit (f r) d=true)
   (eq:masked d a=masked d b) :
   zf f (observe a)=zf f (observe b):=by
 funext r
 have h:=congrArg (bit (f r)) eq
 change bit (f r) a=bit (f r) b
 simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
   Bool.and_true] using h
theorem yo {f:Row → Row} {d a:Sig} (dom : ∀ r,bit (f r) d=true)
   (eq:masked d a=zero):zf f (observe a)=fun _=>false:=by
 funext r
 have he:=congrArg (bit (f r)) eq
 change bit (f r) a=false
 rw [zv] at he
 simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
   Bool.and_true] using he
theorem yX {f:Row → Row} {d a:Sig} (dom : ∀ r,bit (f r) d=true)
   (eq:masked d a=d):zf f (observe a)=fun _=>true:=by
 funext r
 have he:=congrArg (bit (f r)) eq
 change bit (f r) a=true
 rw [dom r] at he
 simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
   Bool.and_true] using he
def qW (u:Bool) (f:Row → Row) (bank:List (Wire Row)) (pool:List Sig) :=
 ∀ a ∈ pool,Available u bank (zf f (observe a))
theorem qd {u} {f:Row → Row} {d a:Sig} {bank pool}
   (dom : ∀ r,bit (f r) d=true) (supplyB:qW u f bank pool)
   (check:zw u d pool a=true):Available u bank (zf f (observe a)):=by
 simp only [zw,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
 rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
 · exact Or.inr (Or.inl ⟨false,yo dom hz⟩)
 · exact Or.inr (Or.inl ⟨true,yX dom ho⟩)
 · exact z149 dom he ▸ supplyB v hv
 · have h:=yi hu (z149 dom he ▸ supplyB v hv)
   rw [q115] at h
   have e:inv (zf f (inv (observe a)))=zf f (observe a):=by
     funext r
     simp [inv,zf]
   rwa [e] at h
abbrev Choice:=Nat × Sig × Sig
def zE (c:Choice):=bin c.1 c.2.1 c.2.2
def vn (u:Bool) (d:Nat):=decide (d<2)||(u&&decide (d<4))
theorem z311 {u d} (h:vn u d=true):allowed u d:=by
 simpa [vn,allowed] using h
def jV (u:Bool) (d:Sig) (pool:List Sig) (c:Choice) :=
 vn u c.1&&(zw u d pool c.2.1&&zw u d pool c.2.2)
theorem yU {u} {f:Row → Row} {d:Sig} {roots bank pool q}
   (dom : ∀ r,bit (f r) d=true) (hp:Reach u roots q bank) (hs:qW u f bank pool)
   (c:Choice) (valid:jV u d pool c=true) :
   ∃ next,Reach u roots (q+1) next ∧ qW u f next (zE c :: pool):=by
 simp only [jV,Bool.and_eq_true] at valid
 obtain ⟨op,x,y,e,hx,hy,_,_⟩:=z125 (z311 valid.1) (qd dom hs valid.2.1)
   (qd dom hs valid.2.2)
 refine ⟨_,Reach.two op hp hx hy,?_⟩
 intro a hm
 rcases List.mem_cons.mp hm with rfl | hm
 · rw [zE,q116,we,e]
   exact Or.inl (by simp)
 · exact vY _ (hs _ hm)
def jR (u:Bool) (d:Sig) (pool:List Sig):List Choice → Option (List Sig)
 | []=>some pool
 | c::cs=>if jV u d pool c then jR u d (zE c::pool) cs else none
theorem vQ {u} {d:Sig} {f:Row → Row} (dom : ∀ r,bit (f r) d=true)
   {roots bank q pool} (hp:Reach u roots q bank) (hs:qW u f bank pool)
   (cs:List Choice) {result} (ok:jR u d pool cs=some result) :
   ∃ next,Reach u roots (q+cs.length) next ∧ qW u f next result:=by
 induction cs generalizing bank q pool with
 | nil=>cases ok; exact ⟨_,hp,hs⟩
 | cons c cs ih =>
   simp only [jR] at ok
   split at ok
   next h =>
     obtain ⟨next,hr,sh⟩:=yU dom hp hs c h
     obtain ⟨out,hr',sh'⟩:=ih hr sh ok
     exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
   next=>contradiction
def zg (d a:Sig):=masked d a == zero||masked d a == d
theorem vF {d:Sig} {f:Row → Row} (dom : ∀ r,bit (f r) d=true)
   (ws:List Sig):ws.countP (zg d) ≤ mass ((ws.map observe).map (zf f)):=by
 classical
 induction ws with
 | nil=>simp [mass]
 | cons a ws ih =>
   simp only [List.countP_cons,List.map_cons,jD]
   cases h:zg d a
   · simpa using (Nat.le_add_left _ _ |> ih.trans)
   · have hc:Constant (zf f (observe a)):=by
       have hh:masked d a=zero ∨ masked d a=d:=by simpa only [zg,Bool.or_eq_true,beq_iff_eq] using h
       rcases hh with hz | ho
       · exact ⟨false,yo dom hz⟩
       · exact ⟨true,yX dom ho⟩
     simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih
def yA (u:Bool) (d:Sig) (L k p:Nat) (pool ws:List Sig) :=
 decide (k+p < L+ws.countP (zg d))&&ws.all (zw u d pool)
theorem wf {u raw T d L} (slice:Slice u raw T d L) (cs:List Choice)
   {pool ws cap} (built:jR u d raw cs=some pool)
   (nd:ws.Nodup) (cut:yA u d L cap cs.length pool ws=true) :
   Impossible u T cap ws.toFinset:=by
 intro k hk h
 obtain ⟨f,roots,dom,base,nc,lo⟩:=slice
 obtain ⟨bank,hr,hs⟩:=vQ dom (Reach.start (roots:=roots.map observe)) base cs built
 simp only [yA,Bool.and_eq_true,decide_eq_true_eq] at cut
 obtain ⟨ineq,all⟩:=cut
 have coveredS:supply u bank ((ws.map observe).map (zf f)):=by
   intro v hv
   obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
   obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hm
   exact qd dom hs (List.all_eq_true.mp all a ha)
 have b:=ju f (z100 h ws nd rfl) nc hr coveredS lo
 have massLo:=vF dom ws
 have hu:=ineq
 simp only [Nat.zero_add] at b
 omega
abbrev Move:=Sig × Sig × Row
def shifted (d r:Row):Row :=
 if h:r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d:Row):Row:=Fin.ofNat 512 (512-d.val)
def z212 (m:Move) (r:Row):Row :=
 if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b:Sig):=(m &&& a) ||| (~~~m &&& b)
def vI (m:Move) (a:Sig) :=
 mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)
theorem q191 (d r:Row) (a:Sig):bit r (a.rotateRight d.val)=bit (shifted d r) a:=by
 unfold bit
 rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
 by_cases h:r.val < 512-d.val<;>simp [shifted,h,r.isLt]
theorem q300 (p x y:Bool):(p&&x || !p&&y)=(if p then x else y):=by cases p<;>simp
theorem q365 (r:Row) (m a b:Sig) :
   bit r (mux m a b)=if bit r m then bit r a else bit r b:=by
 simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
   decide_true,Bool.true_and]
 exact q300 _ _ _
theorem q301 (r:Row) (m:Move) (a:Sig):bit r (vI m a)=bit (z212 m r) a:=by
 simp only [vI,q365,q191,z212]
 cases bit r m.1<;>cases bit r m.2.1<;>rfl
def zA (ms:List Move) (r:Row):=ms.foldl (fun j m=>z212 m j) r
def zj (ms:List Move) (a:Sig):=ms.foldr vI a
theorem jI (ms:List Move) (a:Sig) (r:Row) :
   bit r (zj ms a)=bit (zA ms r) a:=by
 induction ms generalizing r with
 | nil=>rfl
 | cons m ms ih=>exact (q301 r m _).trans (ih _)
theorem zt (ms:List Move) (a:Sig):zj ms a=rename (zA ms) a:=by
 apply BitVec.eq_of_getLsbD_eq
 intro j hj
 exact (jI ms a ⟨j,hj⟩).trans (qA _ _ ⟨j,hj⟩).symm
def z120 (roots:List Sig) (w:Sig):=w==zero||w==one||roots.contains w
theorem z288 {u roots w} (ok:z120 roots w=true) :
   Available u (roots.map observe) (observe w):=by
 simp only [z120,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
 rcases ok with (rfl | rfl) | hm
 · exact Or.inr (Or.inl ⟨false,funext zv⟩)
 · exact Or.inr (Or.inl ⟨true,funext qP⟩)
 · exact Or.inl (List.mem_map_of_mem hm)
def jt (ms:List Move) (raw:List Sig) (T:Sig) (base:List Sig) (G:Sig) :=
 zj ms T == G&&raw.all (fun a=>z120 base (zj ms a))
theorem vP {u ms raw T base G} (ok:jt ms raw T base G=true) :
   rename (zA ms) T=G ∧
   ∀ a ∈ raw,Available u (base.map observe) (observe (rename (zA ms) a)):=by
 simp only [jt,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,zt] at ok
 exact ⟨ok.1,fun a ha=>z288 (ok.2 a ha)⟩
theorem q174 {u ms raw T base G L} (ok:jt ms raw T base G=true)
   (pT:proper T) (nT:zU T=true) (nR:raw.all zU=true) (pG:proper G)
   (hL:Lower u base G L):Lower u raw T L:=by
 obtain ⟨eq,supp⟩:=vP ok
 simpa using yp pT nT nR pG (zA ms) eq supp ∅ (by simp) (by simp) L hL
theorem z130 {u ms raw T base G L d} (ok:jt ms raw T base G=true)
   (all:zj ms d=one) (properG:proper G) (hL:Lower u base G L) :
   Slice u raw T d L:=by
 obtain ⟨eq,supp⟩:=vP ok
 have obs:zf (zA ms) (observe T)=observe G :=
   (qK _ _).symm.trans (congrArg observe eq)
 refine ⟨zA ms,base,?_,?_,?_,?_⟩
 · intro r
   rw [←jI,all,qP]
 · intro a ha
   rw [←qK]
   exact supp a ha
 · rw [obs]
   exact jP properG
 · rw [obs]
   exact hL
def yK (T:Sig) (roots:List Sig) (a:Sig) (rs:Row × Row) :=
 (bit rs.1 T != bit rs.2 T) &&
 roots.all (fun w=>w == a||bit rs.1 w == bit rs.2 w)
theorem yJ {T roots a rs} (ok:yK T roots a rs=true):Essential T roots a:=by
 simp only [yK,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
 exact ⟨rs.1,rs.2,ok.1,fun w hw hne=>(ok.2 w hw).resolve_left hne⟩
def q0 (T:Sig) (raw:List Sig) (xs:List (Sig × Row × Row)) :=
 zU T&&raw.all zU&&xs.all (fun a=>yK T raw a.1 a.2)
theorem jd {T raw xs} (ok:q0 T raw xs=true) :
   ∀ a ∈ (xs.map Prod.fst).toFinset,Essential T raw a:=by
 simp only [q0,Bool.and_eq_true] at ok
 intro a ha
 obtain ⟨⟨a,r,s⟩,hm,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp ha)
 exact yJ (List.all_eq_true.mp ok.2 _ hm)
theorem q3 {T raw xs} (ok:q0 T raw xs=true) :
   zU T=true ∧ raw.all zU=true:=by
 simp only [q0,Bool.and_eq_true] at ok
 exact ok.1
theorem z276 {u raw T} (properT:proper T) (xs:List (Sig × Row × Row))
   (ok:q0 T raw xs=true) :
   Lower u raw T ((xs.map Prod.fst).toFinset.card-1):=by
 intro p bank hr hit
 obtain ⟨k,S,hk,run,sub⟩:=vt properT (q3 ok).1 (q3 ok).2 hr hit
 have le:(xs.map Prod.fst).toFinset.card ≤ S.card:=by
   apply Finset.card_le_card
   intro a ha
   obtain ⟨r,s,hd,iso⟩:=jd ok a ha
   exact j8 run raw a sub r s hd iso
 have bound:=vg run
 omega
def yg (ms:List Move) (T:Sig) (raw:List Sig) (base:List Sig) (G:Sig)
   (xs:List (Sig × Row × Row)) :=
 jt ms raw T base G&&q0 T raw xs &&
   xs.all (fun a=>zj ms a.1 == zero||zj ms a.1 == one)
theorem q352 {u ms T raw base G xs L} (ok:yg ms T raw base G xs=true)
   (properT:proper T) (properG:proper G) (low:Lower u base G L) :
   Lower u raw T (L+(xs.map Prod.fst).toFinset.card):=by
 simp only [yg,Bool.and_eq_true] at ok
 obtain ⟨eq,supp⟩:=vP ok.1.1
 apply yp properT (q3 ok.1.2).1 (q3 ok.1.2).2 properG _ eq supp _ (jd ok.1.2) _ L low
 intro a ha
 obtain ⟨⟨v,r,s⟩,hm,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp ha)
 have hh:=List.all_eq_true.mp ok.2 _ hm
 simp only [Bool.or_eq_true,beq_iff_eq,zt] at hh
 rcases hh with h | h
 · rw [h]
   exact ⟨false,funext zv⟩
 · rw [h]
   exact ⟨true,funext qP⟩
def selected (m:Nat):List (Nat × Sig) :=
 (List.range 9).filterMap fun i=>if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m:Nat):=(selected m).map Prod.snd
def wD (t:Nat):Sig:=bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def zq (m:Nat):List Sig:=if m<512 then vars m else vars m ++ [wD (m/512-1)]
def vertex (m j:Nat):=if m.testBit j then inputs.getD j zero else zero
def z1 (m:Nat):Sig :=
 let x:=vertex m
 (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
   (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
   (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def j169:Nat → Nat
 | 0=>0xff
 | 1=>0x55
 | 2=>0x33
 | 3=>0x11
 | 4=>0xf
 | 5=>0x5
 | 6=>0x3
 | _=>0x1
def j168:Nat → Nat
 | 0=>0x101010101010101
 | 1=>0x1000100010001
 | 2=>0x10100000101
 | 3=>0x100000001
 | 4=>0x1010101
 | 5=>0x10001
 | 6=>0x101
 | _=>0x1
def j167:Nat → Nat
 | 0=>0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
 | 1=>0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
 | 2=>0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
 | 3=>0x10000000000000000000000000000000000000000000000000000000000000001
 | 4=>0x1000000000000000100000000000000010000000000000001
 | 5=>0x100000000000000000000000000000001
 | 6=>0x10000000000000001
 | _=>0x1
def subcube (z o:Nat):Sig :=
 let fixed:=z ||| o
 if z &&& o != 0 then zero else
   BitVec.ofNat 512 ((j169 (fixed &&& 7)*j168 ((fixed >>> 3) &&& 7)*j167 ((fixed >>> 6) &&& 7)) <<< o)
def z223 (z o:Nat):List Move :=
 (List.range 9).filterMap fun j =>
   let x:=inputs.getD j zero
   let step:=Fin.ofNat 512 (1 <<< j)
   if z.testBit j then some (zero,x,step)
   else if o.testBit j then some (~~~x,zero,step) else none
def qe (v:Nat):Move :=
 let i:=v &&& 15
 let j:=v >>> 4
 let a:=inputs.getD i zero
 let b:=inputs.getD j zero
 let d:=(1 <<< j)-(1 <<< i)
 (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)
def wF (t:Nat) (mask:Nat):List (Sig × Row × Row) :=
 (selected mask).map fun (i,a) =>
   let r:=if t/81==2&&i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2&&i==t % 9 then 1 <<< (t/9 % 9) else 0
   (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def z375 (m hints:Nat):List (Sig × Row × Row) :=
 (selected m).map fun (i,a) =>
   let r:=1 <<< ((hints >>> (4*i)) &&& 15)
   (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def qa (T:Sig):=T != zero&&T != one
theorem qM (T:Sig) (h:qa T=true):proper T:=by
 simpa only [qa,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev zK:=Nat × Nat × Nat × Nat × Nat
def z227 (m z o:Nat):=m ^^^ (m &&& (z ||| o))
def j6 (m:Nat):Sig:=z1 m
def jX (m:Nat) (c:zK):Nat:=m % 512+512*(c.1/512)
def vl (m:Nat) (c:zK) (prior:Nat → Nat):Bool :=
 let (z,o,q,s,L):=c
 let ms:=z223 z o
 let raw:=jX m c
 let free:=z227 raw (z % 512) o
 let G:=zj ms (j6 m)
 let xs:=wF (z/512+80) s
 let count:=(xs.map Prod.fst).toFinset.card
 qa G&&jt ms (zq raw) (j6 m) (zq free) G &&
   (zj ms (subcube z o)==one) &&
   (if q=0 then q0 G (zq free) xs&&decide (L ≤ count-1)
    else qa (z1 q) &&
      yg (z223 (z227 free q 0) 0) G (zq free) (zq q) (z1 q) xs &&
      decide (L ≤ prior q+count))
theorem vk {u} {m:Nat} (c:zK) (prior:Nat → Nat)
   (valid : ∀ q,Lower u (zq q) (z1 q) (prior q))
   (ok:vl m c prior=true):Slice u (zq (jX m c)) (j6 m) (subcube c.1 c.2.1) c.2.2.2.2:=by
 revert ok
 obtain ⟨z,o,q,s,L⟩:=c
 intro ok
 let ms:=z223 z o
 let raw:=jX m (z,o,q,s,L)
 let free:=z227 raw (z % 512) o
 let G:=zj ms (j6 m)
 let xs:=wF (z/512+80) s
 change (((qa G&&jt ms (zq raw) (j6 m) (zq free) G) &&
   (zj ms (subcube z o)==one))&&_)=true at ok
 simp only [Bool.and_eq_true,beq_iff_eq] at ok
 apply z130 ok.1.1.2 ok.1.2 (qM _ ok.1.1.1)
 intro p bank hr ha
 have hh:=ok.2
 by_cases hq:q=0
 · simp only [vl,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
   exact hh.2.trans (z276 (qM _ ok.1.1.1) xs hh.1 p bank hr ha)
 · simp only [vl,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
   exact hh.2.trans (q352 hh.1.2 (qM _ ok.1.1.1) (qM _ hh.1.1) (valid q) p bank hr ha)
def z228 (old rep:Nat) (swaps:List Nat) :=
 (qa (z1 old)&&zU (z1 old)&&(zq old).all zU)&&qa (z1 rep) &&
   jt (swaps.map qe) (zq old) (z1 old) (zq rep) (z1 rep)
theorem q298 {u old rep L swaps} (ok:z228 old rep swaps=true)
   (h:Lower u (zq rep) (z1 rep) L):Lower u (zq old) (z1 old) L:=by
 simp only [z228,Bool.and_eq_true] at ok
 exact q174 ok.2 (qM _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (qM _ ok.1.2) h
def z9 (entries:List (Nat × Nat)) (q:Nat) :=
 ((entries.find? (fun a=>a.1 == q)).map Prod.snd).getD 0
theorem z5 {u} (entries:List (Nat × Nat))
   (sound : ∀ e ∈ entries,Lower u (zq e.1) (z1 e.1) e.2) (q:Nat) :
   Lower u (zq q) (z1 q) (z9 entries q):=by
 unfold z9
 cases h:entries.find? (fun a=>a.1 == q) with
 | none=>exact fun _ _ _ _=>Nat.zero_le _
 | some e =>
   have he:=List.mem_of_find?_eq_some h
   have hit:(fun a:Nat × Nat=>a.1 == q) e=true:=List.find?_some (p:=fun a:Nat × Nat=>a.1 == q) (a:=e) h
   have eq:e.1=q:=beq_iff_eq.mp hit
   simpa only [Option.map_some,Option.getD_some,eq] using sound e he
abbrev BoundPool:=Sig × Nat × Nat × List Sig
def BoundPool.domain (c:BoundPool):Sig:=c.1
def BoundPool.bound (c:BoundPool):Nat:=c.2.1
def BoundPool.paid (c:BoundPool):Nat:=c.2.2.1
def BoundPool.wires (c:BoundPool):List Sig:=c.2.2.2
def qq (u:Bool) (raw:List Sig) (T:Sig) (c:BoundPool) :=
 ∃ (f:Row → Row) (roots:List Sig) (bank:List (Wire Row)),
   (∀ r,bit (f r) c.domain=true) ∧ ¬Constant (zf f (observe T)) ∧
   (∀ q ws,Reach u (roots.map observe) q ws → Available u ws (zf f (observe T)) → c.bound ≤ q) ∧
   Reach u (roots.map observe) c.paid bank ∧ qW u f bank c.wires ∧ True
theorem z306 {u raw T d lb} (h:Slice u raw T d lb) (cs:List Choice) {ws}
   (build:jR u d raw cs=some ws):qq u raw T ⟨d,lb,cs.length,ws⟩:=by
 obtain ⟨f,roots,dom,sup,nc,prior⟩:=h
 obtain ⟨bank,hr,hs⟩:=vQ dom (Reach.start (roots:=roots.map observe)) sup cs build
 exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩
theorem z126 {u raw T c} (valid:qq u raw T c) (k:Nat) (rest:List Sig)
   (choice:Choice) (paid:Bool)
   (known : ∀ a ∈ rest,zw u c.domain c.wires a=true)
   (buy:if paid then jV u c.domain c.wires choice=true
      else zw u c.domain c.wires (zE choice)=true)
   (bound:k+c.paid+paid.toNat <
     c.bound+(zE choice :: rest).countP (zg c.domain))
   (nd:(zE choice :: rest).Nodup) :
   Impossible u T k (zE choice :: rest).toFinset:=by
 intro t ht run
 obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩:=valid
 let ws:=zE choice::rest
 have done (n:Nat) (out:List (Wire Row)) (reach:Reach u (roots.map observe) n out)
     (zs:qW u f out (zE choice::rest)) (le:n=c.paid+paid.toNat):False:=by
   have covered:supply u out ((ws.map observe).map (zf f)):=by
     intro v hv
     obtain ⟨_,hm,rfl⟩:=List.mem_map.mp hv
     obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hm
     exact zs _ ha
   have b:=ju f (z100 run ws nd rfl) nc reach covered lo
   have cm:=vF dom ws
   change k+c.paid+paid.toNat < c.bound+ws.countP (zg c.domain) at bound
   omega
 cases paid with
 | false =>
   apply done _ _ hp _ rfl
   intro a h
   rcases List.mem_cons.mp h with rfl | hm
   · exact qd dom hs buy
   · exact qd dom hs (known _ hm)
 | true =>
   obtain ⟨out,hr,hc⟩:=yU dom hp hs choice buy
   apply done _ _ hr _ rfl
   intro a h
   rcases List.mem_cons.mp h with rfl | hm
   · exact hc _ (by simp)
   · have point : ∀ v ∈ c.wires,Available u out (zf f (observe v)) :=
       fun v hu=>hc v (List.mem_cons_of_mem _ hu)
     exact qd dom point (known _ hm)
def qb (u:Bool) (c:BoundPool) (k:Nat) (rest:List Sig) (op:Choice) :=
 let z:=zE op
 let extra := !(zw u c.domain c.wires z)
 ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (zg c.domain)) &&
   rest.all (zw u c.domain c.wires))&&(!extra||jV u c.domain c.wires op)
theorem jw {u raw T c} (valid:qq u raw T c) {k rest op}
   (nd:(zE op::rest).Nodup) (cut:qb u c k rest op=true) :
   Impossible u T k (zE op::rest).toFinset:=by
 let extra := !(zw u c.domain c.wires (zE op))
 apply z126 valid k rest op extra _ _ _ nd
 · simp only [qb,Bool.and_eq_true,List.all_eq_true] at cut
   exact cut.1.2
 · simp only [qb,Bool.and_eq_true,Bool.or_eq_true] at cut
   cases he:zw u c.domain c.wires (zE op)<;>simp_all [extra]
 · simp only [qb,Bool.and_eq_true,decide_eq_true_eq] at cut
   exact cut.1.1
def materialize (u:Bool) (raw:List Sig) (cs:List Choice) (d:Sig) (lb:Nat):Option BoundPool :=
 (jR u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem wL {u raw T d L cs c} (slice:Slice u raw T d L)
   (h:materialize u raw cs d L=some c):qq u raw T c:=by
 unfold materialize at h
 cases he:jR u d raw cs with
 | none=>simp [he] at h
 | some pool =>
   simp only [he,Option.map_some,Option.some.injEq] at h
   subst c
   exact z306 slice cs he
abbrev Bits:=BitVec 768
abbrev Signals:=Bits × Bits
abbrev Decor:=Sig × Signals
def jO {n:Nat} (r:Fin n → Row) (v:Sig):BitVec n :=
 (BitVec.ofBoolListLE (List.ofFn (fun i=>bit (r i) v))).cast List.length_ofFn
theorem qv {n:Nat} (r:Fin n → Row) (v:Sig) (i:Fin n) :
   (jO r v).getLsbD i.val=bit (r i) v:=by
 simp only [jO,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
 simp [i.isLt]
def qG (r s:Fin 768 → Row) (a:Sig):Signals:=(jO r a,jO s a)
def qr (T:Sig) (r s:Fin 768 → Row) :=
 ∀ i,bit (r i) T=true ∧ bit (s i) T=false
theorem z269 {T r s} (h:qr T r s):Sep T 768 r s (qG r s):=by
 exact ⟨h,fun a i => ⟨qv _ _ _,qv _ _ _⟩⟩
def faithful (r s:Fin 768 → Row) (x:Decor):=x.2=qG r s x.1
def bv {n:Nat} (d:Nat) (a b:BitVec n):BitVec n :=
 if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d:Nat) (x y:Decor):Decor:=(bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)
theorem z366 {n:Nat} (r:Fin n → Row) (d:Nat) (a b:Sig) :
   jO r (bin d a b)=bv d (jO r a) (jO r b):=by
 apply BitVec.eq_of_getLsbD_eq
 intro j hj
 have h:=qv r (bin d a b) ⟨j,hj⟩
 rw [zX,←qv r a ⟨j,hj⟩,←qv r b ⟨j,hj⟩] at h
 rw [h]
 unfold bv
 split_ifs<;>simp [hj]
theorem vA {r s x y} (d) (hx:faithful r s x) (hy:faithful r s y) :
   faithful r s (dbin d x y):=by
 change x.2=_ at hx
 change y.2=_ at hy
 simp only [faithful,dbin,qG,z366,hx,hy]
def zH:Decor:=(zero,0,0)
theorem yd (r s):faithful r s zH:=by
 apply Prod.ext<;>apply BitVec.eq_of_getLsbD_eq<;>intro j hj
 · change (0:Bits).getLsbD j=(jO r zero).getLsbD j
   rw [show (jO r zero).getLsbD j=bit (r ⟨j,hj⟩) zero from qv _ _ ⟨j,hj⟩,zv]
   simp
 · change (0:Bits).getLsbD j=(jO s zero).getLsbD j
   rw [show (jO s zero).getLsbD j=bit (s ⟨j,hj⟩) zero from qv _ _ ⟨j,hj⟩,zv]
   simp
theorem wZ {r s ws} (all : ∀ v ∈ ws,faithful r s v) (i:Nat) :
   faithful r s (List.getD ws i zH):=by
 simp only [List.getD_eq_getElem?_getD]
 cases e:ws[i]? with
 | none=>exact yd _ _
 | some v=>exact all _ (List.mem_of_getElem? e)
def jU (n:Nat) (bits:Nat) (ws:List Decor):List Decor :=
 match n with
 | 0=>ws
 | k+1 =>
   let a:=ws.getD (bits &&& 15) zH
   let b:=ws.getD ((bits >>> 4) &&& 15) zH
   jU k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
theorem vE (n bits) (ws) (r s) (base : ∀ v ∈ ws,faithful r s v) :
   ∀ v ∈ jU n bits ws,faithful r s v:=by
 induction n generalizing ws bits with
 | zero=>exact base
 | succ n ih =>
   apply ih
   intro v hv
   rcases List.mem_append.mp hv with hw | hz
   · exact base _ hw
   · obtain rfl:=List.mem_singleton.mp hz
     exact vA _ (wZ base _) (wZ base _)
def jW (cols:Nat → Bits) (i:Fin 768):Row :=
 (BitVec.ofBoolListLE (List.ofFn (fun j:Fin 9=>(cols j.val).getLsbD i.val))).toFin.cast
   (by simp [List.length_ofFn])
theorem z305 : ∀ r:Row,bit r (inputs.getD 0 zero)=r.val.testBit 0:=by decide +kernel
theorem z304 : ∀ r:Row,bit r (inputs.getD 1 zero)=r.val.testBit 1:=by decide +kernel
theorem z303 : ∀ r:Row,bit r (inputs.getD 2 zero)=r.val.testBit 2:=by decide +kernel
theorem z302 : ∀ r:Row,bit r (inputs.getD 3 zero)=r.val.testBit 3:=by decide +kernel
theorem z301 : ∀ r:Row,bit r (inputs.getD 4 zero)=r.val.testBit 4:=by decide +kernel
theorem z300 : ∀ r:Row,bit r (inputs.getD 5 zero)=r.val.testBit 5:=by decide +kernel
theorem z299 : ∀ r:Row,bit r (inputs.getD 6 zero)=r.val.testBit 6:=by decide +kernel
theorem z298 : ∀ r:Row,bit r (inputs.getD 7 zero)=r.val.testBit 7:=by decide +kernel
theorem z297 : ∀ r:Row,bit r (inputs.getD 8 zero)=r.val.testBit 8:=by decide +kernel
theorem zZ : ∀ (j:Fin 9) (r:Row),
   bit r (inputs.getD j.val zero)=r.val.testBit j.val:=by
 intro j r
 fin_cases j
 · exact z305 r
 · exact z304 r
 · exact z303 r
 · exact z302 r
 · exact z301 r
 · exact z300 r
 · exact z299 r
 · exact z298 r
 · exact z297 r
theorem yj (cols:Nat → Bits) (i:Fin 768) (j:Fin 9) :
   bit (jW cols i) (inputs.getD j.val zero)=(cols j.val).getLsbD i.val:=by
 rw [zZ]
 change (BitVec.ofBoolListLE (List.ofFn (fun h:Fin 9=>(cols h.val).getLsbD i.val))).getLsbD j.val=_
 simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
 simp [j.isLt]
def wI (m:Nat) (p q:Nat → Bits):List Decor :=
 (selected m).map (fun (j,a)=>(a,p j,q j))
theorem vK {m j a} (h:(j,a) ∈ selected m) :
   j<9 ∧ a=inputs.getD j zero:=by
 obtain ⟨v,hv,hh⟩:=List.mem_filterMap.mp h
 simp only [List.mem_range] at hv
 split at hh
 next =>
   cases hh
   exact ⟨hv,rfl⟩
 next=>contradiction
theorem z215 (m) (p q:Nat → Bits) :
   ∀ a ∈ wI m p q,faithful (jW p) (jW q) a:=by
 intro a ha
 obtain ⟨⟨j,v⟩,hv,rfl⟩:=List.mem_map.mp ha
 obtain ⟨hj,rfl⟩:=vK hv
 apply Prod.ext<;>apply BitVec.eq_of_getLsbD_eq<;>intro i hi
 · exact (yj p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (qv _ _ ⟨i,hi⟩).symm
 · exact (yj q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (qv _ _ ⟨i,hi⟩).symm
def z101 (m:Nat) (v:Nat → Bits):Bits :=
 let x:=fun j=>if m.testBit j then v j else 0
 (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
   (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
   (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem z390 (m:Nat) (v:Nat → Bits) (i:Fin 768) (j:Fin 9) :
   bit (jW v i) (vertex m j.val) =
   ((if m.testBit j.val then v j.val else 0):Bits).getLsbD i.val:=by
 by_cases hh:m.testBit j.val=true
 · simpa [vertex,hh] using yj v i j
 · simp [vertex,hh,zv]
theorem z230 (m:Nat) (v:Nat → Bits) (i:Fin 768) :
   bit (jW v i) (z1 m)=(z101 m v).getLsbD i.val:=by
 have pos (j:Nat) (hj:j<9):(vertex m j).getLsbD (jW v i).val=((if m.testBit j then v j else 0):Bits).getLsbD i.val:=z390 m v i ⟨j,hj⟩
 simp only [bit,z1,z101,BitVec.getLsbD_and,BitVec.getLsbD_or]
 simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov:=Bits × Bits × Bits
def jm (z:Bits) (c:Cov):Cov :=
 (z ||| c.1,(z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
  (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))
def coverage (d:Bool) (v:List Decor):Cov :=
 v.foldr (fun a c=>jm (column d a.2) c) (0,0,0)
def jA (c:Cov) (a:Bits):Bits:=c.1 &&& ~~~(c.2.1 &&& a)
def vZ (c:Cov) (a b:Bits):Bits :=
 c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))
private theorem q364 (c:Cov) (a:Bits):jA (jm a c) a=c.1:=by
 apply BitVec.eq_of_getLsbD_eq
 intro i hi
 simp only [jA,jm,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
 cases a.getLsbD i<;>cases c.1.getLsbD i<;>cases c.2.1.getLsbD i<;>rfl
private theorem q363 (c:Cov) (a b:Bits):vZ (jm a (jm b c)) a b=c.1:=by
 apply BitVec.eq_of_getLsbD_eq
 intro i hi
 simp only [vZ,jm,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
 cases a.getLsbD i<;>cases b.getLsbD i<;>cases c.1.getLsbD i <;>
   cases c.2.1.getLsbD i<;>cases c.2.2.getLsbD i<;>rfl
private theorem q312 (c:Cov) (a b:Bits):jm a (jm b c)=jm b (jm a c):=by
 apply Prod.ext
 · apply BitVec.eq_of_getLsbD_eq
   intro i hi
   simp only [jm,BitVec.getLsbD_or]
   cases a.getLsbD i<;>cases b.getLsbD i<;>rfl
 · apply Prod.ext<;>apply BitVec.eq_of_getLsbD_eq<;>intro i hi <;>
     simp only [jm,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
     cases a.getLsbD i<;>cases b.getLsbD i<;>cases c.1.getLsbD i <;>
     cases c.2.1.getLsbD i<;>cases c.2.2.getLsbD i<;>rfl
private theorem z295 (d:Bool) {l r:List Decor} (h:l.Perm r):coverage d l=coverage d r:=by
 induction h with
 | nil=>rfl
 | cons a _ ih=>exact congrArg (jm (column d a.2)) ih
 | swap a b t=>exact q312 _ _ _
 | trans _ _ h1 h2=>exact h1.trans h2
theorem z294 (d:Bool) (v:List Decor) {r s} (good : ∀ a ∈ v,faithful r s a) :
   (coverage d v).1=covered d (qG r s) (v.map Prod.fst):=by
 induction v with
 | nil=>rfl
 | cons a v ih =>
   change (column d a.2 ||| (coverage d v).1)=column d (qG r s a.1) ||| _
   rw [show a.2=qG r s a.1 from good _ (by simp),ih (fun a ha=>good a (by simp [ha]))]
def jv (ws:List Decor) (a:Decor) (keep:Bool) :=
 if keep then ws else ws.erase a
def q8 (ws:List Decor) (a b:Decor) (ka kb:Bool) :=
 jv (jv ws a ka) b kb
theorem vV {ws:List Decor} (a:Decor) (ha:a ∈ ws) :
   ws.Perm (a::ws.erase a):=List.perm_cons_erase ha
theorem z172 {ws:List Decor} (d:Bool) (a:Decor) (ha:a ∈ ws) (keep:Bool) :
   (coverage d (jv ws a keep)).1 =
     (if keep then (coverage d ws).1 else jA (coverage d ws) (column d a.2)):=by
 cases keep
 · change (coverage d (ws.erase a)).1=jA (coverage d ws) _
   rw [z295 d (vV a ha)]
   exact (q364 _ _).symm
 · rfl
theorem z291 {ws:List Decor} (a b:Decor) (ha:a ∈ ws) (hb:b ∈ ws) (hne:a≠b) :
   ws.Perm (a::b::(ws.erase a).erase b):=by
 have hm:b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm hne)).mpr hb
 exact (vV a ha).trans (List.Perm.cons _ (vV b hm))
theorem z171 {ws:List Decor} (d:Bool) (a b:Decor) (ha:a ∈ ws) (hb:b ∈ ws)
   (ne:a ≠ b) (ka kb:Bool) :
   (coverage d (q8 ws a b ka kb)).1 =
     (if ka then (if kb then (coverage d ws).1 else jA (coverage d ws) (column d b.2))
      else if kb then jA (coverage d ws) (column d a.2)
      else vZ (coverage d ws) (column d a.2) (column d b.2)):=by
 cases ka<;>cases kb
 · change (coverage d ((ws.erase a).erase b)).1=vZ (coverage d ws) _ _
   rw [z295 d (z291 a b ha hb ne)]
   exact (q363 _ _ _).symm
 · exact z172 d a ha false
 · exact z172 d b hb false
 · rfl
def jC (a b:List Sig):=(a.all (fun x=>b.contains x))&&(b.all (fun x=>a.contains x))
theorem qU {xs ys} (h:jC xs ys=true):xs.toFinset=ys.toFinset:=by
 simp only [jC,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
 ext a
 simp only [List.mem_toFinset]
 exact ⟨h.1 a,h.2 a⟩
def jc (v:Sig) :=
 let n:=v.toNat % 2305843009213693951
 (n*(n+971)) % 2305843009213693951
def z114 (xs:List Sig):=xs.foldl (fun v x=>v+jc x) 0
def qy (u:Bool) (pools:List BoundPool) (links:Nat → List (List Sig)) (k:Nat)
   (rest:List Sig) (op:Choice) :=
 let ws:=zE op::rest
 (links (z114 ws)).any (jC ws)||pools.any (fun p=>qb u p k rest op)
theorem yf {u raw T pools links k rest op}
   (pValid : ∀ p ∈ pools,qq u raw T p)
   (lValid : ∀ tag xs,xs ∈ links tag → Impossible u T k (List.toFinset xs))
   (nd:(zE op :: rest).Nodup)
   (h:qy u pools links k rest op=true) :
   Impossible u T k (zE op :: rest).toFinset:=by
 simp only [qy,Bool.or_eq_true,List.any_eq_true] at h
 rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
 · rw [qU ok]
   exact lValid _ _ hx
 · exact jw (pValid _ hp) nd ok
abbrev q125:=Cov × Bool
def jN (u:Bool) (ws:List Decor):q125:=(coverage (!u) ws,u)
def jo (v:Cov) (a b:Bits) (ka kb:Bool) :=
 if ka then (if kb then v.1 else jA v b) else if kb then jA v a else vZ v a b
theorem wy (ws:List Decor) (a:Decor) (k:Bool):(jv ws a k).Sublist ws:=by
 cases k
 · exact List.erase_sublist
 · exact List.Sublist.refl _
theorem z279 (ws:List Decor) (a b:Decor) (ka kb:Bool) :
   (q8 ws a b ka kb).Sublist ws:=(wy _ _ _).trans (wy _ _ _)
theorem z278 (ws:List Decor) (a b:Decor) (ka kb:Bool) (ha:a ∈ ws) (hb:b ∈ ws) (ne:a≠b) :
   (q8 ws a b ka kb).length =
     ws.length - (if ka then 0 else 1) - (if kb then 0 else 1):=by
 have hm:b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm ne)).mpr hb
 cases ka<;>cases kb<;>simp [q8,jv,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
def zT (op:Nat) (a b:Decor):Choice:=(op,a.1,b.1)
abbrev zl:=Nat × Nat × List Decor × q125 × List BoundPool × (Nat → List (List Sig))
def qC (c:zl) (op:Nat) (a b z:Decor) (ka kb:Bool) :=
 let (cap,n,ws,cov,pools,links):=c
 let len:=1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
 if len>cap then true else
   let d := !cov.2
   let rs:=jo cov.1 (column d a.2) (column d b.2) ka kb
   if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
   if !qa z.1||ws.any (fun v=>v.1==z.1) then true else
     let rest:=(q8 ws a b ka kb).map Prod.fst
     qy cov.2 pools links (cap-1) rest (zT op a b)
def w3 (ws:List Decor) (op:Nat) (a b:Decor) (ka kb:Bool) :=
 (dbin op a b).1 :: (q8 ws a b ka kb).map Prod.fst
theorem z122 {u raw T r s ws pools links cap a b op ka kb}
   (pairs:qr T r s) (faith : ∀ w ∈ ws,faithful r s w)
   (nd:(ws.map Prod.fst).Nodup) (ha:a ∈ ws) (hb:b ∈ ws)
   (ne:a≠b) (hcap:0<cap)
   (pv : ∀ p ∈ pools,qq u raw T p)
   (lv : ∀ tag xs,xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
   (pro:proper (dbin op a b).1) (fresh:(dbin op a b).1 ∉ ws.map Prod.fst)
   (test:qC (cap,ws.length,ws,jN u ws,pools,links) op a b (dbin op a b) ka kb=true) :
   Impossible u T (cap-1) (w3 ws op a b ka kb).toFinset:=by
 let z:=dbin op a b
 let rest:=q8 ws a b ka kb
 let child:=z.1 :: rest.map Prod.fst
 have sub:rest.Sublist ws:=z279 _ _ _ _ _
 have ndc:child.Nodup:=List.nodup_cons.mpr ⟨fun hm=>fresh ((sub.map _).subset hm),
   nd.sublist (sub.map _)⟩
 have fr:ws.any (fun v=>v.1==z.1)=false:=by
   apply Bool.eq_false_iff.mpr
   intro hh
   obtain ⟨x,hx,he⟩:=List.any_eq_true.mp hh
   exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
 have pp:qa z.1=true:=by simpa [qa,proper] using pro
 have leq:1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1))=child.length:=by
   change _=(z.1::rest.map Prod.fst).length
   rw [List.length_cons,List.length_map,z278 _ _ _ _ _ ha hb ne,Nat.add_comm 1]
 intro k hk h
 have hsz:=vg h
 change child.toFinset.card ≤ k+1 at hsz
 rw [List.toFinset_card_of_nodup ndc] at hsz
 have len:child.length ≤ cap:=by omega
 unfold qC at test
 change (if 1+(ws.length-_ - _) > cap then true else _)=true at test
 rw [leq,if_neg (by omega)] at test
 have sep:=vW h (z269 pairs)
 let d := !u
 have g:(coverage d rest).1=covered d (qG r s) (rest.map Prod.fst) :=
   z294 _ _ (fun v hv=>faith _ (sub.subset hv))
 have rz:(coverage d rest).1=jo (coverage d ws) (column d a.2) (column d b.2) ka kb :=
   z171 d a b ha hb ne ka kb
 have hf:=vA op (faith _ ha) (faith _ hb)
 change column d (qG r s z.1) ||| covered d (qG r s) (rest.map Prod.fst)=_ at sep
 change z.2=qG r s z.1 at hf
 rw [←hf,←g,rz,BitVec.or_comm] at sep
 have be:((jo (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 768)=false:=by
   simpa using sep
 change (if (jo (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 768 then true else if !qa z.1||ws.any (fun v=>v.1==z.1) then true else _)=true at test
 rw [be,pp,fr] at test
 exact yf (op:=zT op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h
def jL (ctx:zl) (a b:Decor) (op:Nat) :=
 let z:=dbin op a b
 let attempt:=qC ctx op a b z
 attempt false false&&attempt true false&&attempt false true&&attempt true true
def wJ (u:Bool):List Nat:=if u then [0,1,2,3] else [0,1]
theorem w0 {u d} (h:allowed u d):d ∈ wJ u:=by
 rcases zS h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
 · cases u<;>simp [wJ]
 · cases u<;>simp [wJ]
 · simp [wJ]
 · simp [wJ]
def z178 (ctx:zl) (a:Decor) (bs:List Decor) :=
   bs.all (fun b=>(wJ ctx.2.2.2.1.2).all (jL ctx a b))
def jz (ctx:zl):List Decor → Bool
 | []=>true
 | a::bs=>z178 ctx a bs&&jz ctx bs
theorem q107 {ctx ws} (h:jz ctx ws=true) {a b:Decor} (ha:a∈ws) (hb:b∈ws)
   (ne:a≠b):(∀ d,allowed ctx.2.2.2.1.2 d → jL ctx a b d=true) ∨
     (∀ d,allowed ctx.2.2.2.1.2 d → jL ctx b a d=true):=by
 induction ws with
 | nil=>simp at ha
 | cons w ws ih =>
   simp only [jz,Bool.and_eq_true,z178,List.all_eq_true] at h
   rcases List.mem_cons.mp ha with rfl | haTail
   · have bm:=(List.mem_cons.mp hb).resolve_left (Ne.symm ne)
     exact Or.inl fun d hd=>h.1 b bm d (w0 hd)
   · rcases List.mem_cons.mp hb with rfl | hbTail
     · exact Or.inr fun d hd=>h.1 a haTail d (w0 hd)
     · exact ih h.2 haTail hbTail
theorem z252 {ctx a b d} (h:jL ctx a b d=true) (ka kb:Bool) :
   qC ctx d a b (dbin d a b) ka kb=true:=by
 simp only [jL,Bool.and_eq_true] at h
 cases ka<;>cases kb<;>first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
theorem z280 {v:List Sig} {w:Sig} (a:Sig) (k:Bool) :
   w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v:=by cases k<;>simp [kept]
theorem yV {v:List Decor} (nd:v.Nodup) (a w:Decor) (k:Bool) :
   w ∈ jv v a k ↔ w∈v ∧ (w≠a ∨ k=true):=by
 cases k<;>simp [jv,nd.mem_erase_iff,and_comm]
theorem wC {ws:List Decor} (nd:(ws.map Prod.fst).Nodup) {a b:Decor}
   (ha:a∈ws) (hb:b∈ws) (eq:a.1=b.1):a=b:=by
 induction ws with
 | nil=>simp at ha
 | cons w ws ih =>
   obtain ⟨hn,ht⟩:=List.nodup_cons.mp nd
   rcases List.mem_cons.mp ha with rfl | haTail<;>rcases List.mem_cons.mp hb with rfl | hbTail
   · rfl
   · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
   · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
   · exact ih ht haTail hbTail
theorem z115 {ws:List Decor} (nd:(ws.map Prod.fst).Nodup) {a b:Decor}
   (ha:a ∈ ws) (hb:b ∈ ws) (ka kb:Bool) (v:Sig) :
   v ∈ (q8 ws a b ka kb).map Prod.fst ↔
   v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true):=by
 have wn:=nd.of_map
 have dn:=wn.sublist (wy ws a ka)
 simp only [q8,List.mem_map,yV wn,yV dn]
 constructor
 · rintro ⟨w,hw,rfl⟩
   exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq=>ne (wC nd hw.1.1 ha eq)) id,
         hw.2.imp (fun ne eq=>ne (wC nd hw.1.1 hb eq)) id⟩
 · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
   exact ⟨w,⟨⟨hm,h1.imp (fun ne eq=>ne (congrArg Prod.fst eq)) id⟩,
       h2.imp (fun ne eq=>ne (congrArg Prod.fst eq)) id⟩,rfl⟩
theorem y2 {ws:List Decor} (nd:(ws.map Prod.fst).Nodup) {a b:Decor}
   (ha:a∈ws) (hb:b∈ws) (ne:a.1≠b.1) (d:Nat) (ka kb:Bool) :
   (w3 ws d a b ka kb).toFinset =
     (q6 (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
 ext v
 have av:=List.mem_map_of_mem (f:=Prod.fst) ha
 have bv':=List.mem_map_of_mem (f:=Prod.fst) hb
 simp only [w3,q6,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
   z115 nd ha hb,z280,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
 by_cases va:v=a.1<;>by_cases vb:v=b.1<;>cases ka<;>cases kb<;>simp_all
theorem wo {u} (v:List Sig) (nd:v.Nodup) (a b:Sig) (d:Nat) (hd:allowed u d) (ka kb:Bool) :
   (q6 v a b d ka kb).toFinset=(q6 v b a (qm d) kb ka).toFinset:=by
 ext x
 simp only [q6,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
   z280,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,vX hd a b]
 tauto
theorem z368 {u raw T r s ws pools links cap}
   (pairs:qr T r s) (faith : ∀ w ∈ ws,faithful r s w)
   (nd:(ws.map Prod.fst).Nodup) (out:T ∉ ws.map Prod.fst)
   (pv : ∀ p ∈ pools,qq u raw T p)
   (lv : ∀ tag xs,xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
   (checks:jz (cap,ws.length,ws,jN u ws,pools,links) ws=true) :
   Impossible u T cap (ws.map Prod.fst).toFinset:=by
 by_cases hc:cap=0
 · intro k hk h
   have ke:k=0:=by omega
   subst k
   generalize he:(ws.map Prod.fst).toFinset=S at h
   obtain ⟨hS,_⟩:=h
   exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
 have hc' : 0<cap:=by omega
 apply q188 nd out
 intro a ha b hb d hd ka kb ne fresh pro len
 obtain ⟨a,haW,rfl⟩:=List.mem_map.mp ha
 obtain ⟨b,hbW,rfl⟩:=List.mem_map.mp hb
 have ab:a≠b:=fun e=>ne (congrArg Prod.fst e)
 have one (a b:Decor) (d:Nat) (aa:a∈ws) (bb:b∈ws) (ne' : a.1≠b.1) (ka kb:Bool)
     (pr:proper (bin d a.1 b.1)) (fr:bin d a.1 b.1 ∉ ws.map Prod.fst)
     (test:jL (cap,ws.length,ws,jN u ws,pools,links) a b d=true) :
     Impossible u T (cap-1) (q6 (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
   rw [←y2 nd aa bb ne']
   exact z122 pairs faith nd aa bb (fun e=>ne' (congrArg Prod.fst e)) hc' pv lv
     pr fr (z252 test ka kb)
 rcases q107 checks haW hbW ab with hh | hh
 · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
 · rw [wo _ nd _ _ d hd]
   exact one b a (qm d) hbW haW (Ne.symm ne) kb ka (vX hd a.1 b.1 ▸ pro)
     (vX hd a.1 b.1 ▸ fresh) (hh _ (yb hd).1)
theorem z234 (r s:Row) (h : ∀ a ∈ inputs,bit r a=bit s a):r=s:=by
 apply Fin.ext
 apply Nat.eq_of_testBit_eq
 intro j
 by_cases hj:j<9
 · let i:Fin 9 := ⟨j,hj⟩
   have hm:inputs.getD i.val zero ∈ inputs:=by
     rw [← z116]
     exact List.mem_ofFn.mpr ⟨i,rfl⟩
   exact (zZ i r).symm.trans ((h _ hm).trans (zZ i s))
 · have le:512 ≤ 2^j:=by
     change 2^9 ≤ 2^j
     exact Nat.pow_le_pow_right (by decide) (by omega)
   exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
     (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm
def wz (p q:List Move):=inputs.all (fun a=>zj p (zj q a) == a)
theorem v1 {p q} (h:wz p q=true) (r:Row) :
   zA q (zA p r)=r:=by
 apply z234
 intro a ha
 rw [←jI,←jI]
 have eq:=beq_iff_eq.mp (List.all_eq_true.mp h a ha)
 rw [eq]
def wA (T:Sig) (p:List Move) :=
 (zj p T == T)&&wz p p.reverse&&wz p.reverse p
theorem yu {u T n} {ws:List Sig} (hi:Impossible u T n ws.toFinset)
   (p:List Move) (ok:wA T p=true):Impossible u T n (ws.map (zj p.reverse)).toFinset:=by
 simp only [wA,Bool.and_eq_true,beq_iff_eq] at ok
 have onto:Function.Surjective (zA p):=fun r => ⟨zA p.reverse r,v1 ok.2 r⟩
 intro k hk h
 have run:=z277 h (zA p) onto
 have goal:rename (zA p) T=T:=(zt p T).symm.trans ok.1.1
 have inv (x:Sig):rename (zA p) (zj p.reverse x)=x:=by
   apply BitVec.eq_of_getLsbD_eq
   intro j hj
   change bit ⟨j,hj⟩ _=bit ⟨j,hj⟩ _
   rw [qA,jI,v1 ok.1.2]
 have back:(ws.map (zj p.reverse)).toFinset.image (rename (zA p))=ws.toFinset:=by
   ext a
   simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
   constructor
   · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
     simpa only [inv] using hw
   · intro ha
     exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
 rw [goal,back] at run
 exact hi k hk run
abbrev Packing:=Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def zP:Packing:=(0,0,0,0,0,0,0,fun _=>0)
def q5 (word:Nat → Nat) (pos len:Nat) :=
 let i:=pos/8192
 let shift:=pos % 8192
 let lo:=word i >>> shift
 if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
 else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)
def zk (nb slots sw vw iw pw:Nat) (data:Nat → Nat) (h:Nat):Option (Nat × Nat) :=
 let a:=h % nb
 let sh:=q5 data (a*sw) sw
 let row:=(h/nb+sh) % slots
 let word:=q5 data (nb*sw+row*vw) vw
 if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
   some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
 else none
abbrev Forest:=Nat × Nat × (Nat → Bits × Bits) × List zK × List (List Nat) ×
 (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (g:Forest):Nat:=g.1
def Forest.mode (g:Forest):Bool := !(g.1.testBit 10)
def Forest.cap (g:Forest):Nat:=g.2.1
def Forest.samples (g:Forest):Nat → Bits × Bits:=g.2.2.1
def Forest.cols (g:Forest):List zK:=g.2.2.2.1
def Forest.autos (g:Forest):List (List Nat):=g.2.2.2.2.1
def Forest.levels (g:Forest):Nat → Packing:=g.2.2.2.2.2.1
def Forest.index (g:Forest):Nat → Nat → Option (Nat × Nat):=g.2.2.2.2.2.2
def jn (g:Forest) :=
 let ws:=wI g.mask (fun j=>(g.samples j).1) (fun j=>(g.samples j).2)
 ws
theorem vJ (g:Forest) : ∀ a ∈ jn g,
   faithful (jW fun j=>(g.samples j).1) (jW fun j=>(g.samples j).2) a:=by
 exact z215 g.mask (fun j=>(g.samples j).1) (fun j=>(g.samples j).2)
def zz (g:Forest):=j6 g.mask
def qz (m:Nat) (v:Nat → Bits) :=
 z101 m v
theorem q190 (m:Nat) (v:Nat → Bits) (i:Fin 768) :
   bit (jW v i) (j6 m)=(qz m v).getLsbD i.val:=by
 exact z230 m v i
theorem v2 {m:Nat} {p q:Nat → Bits}
   (hp:qz m p=BitVec.allOnes 768) (hq:qz m q=0) :
   qr (j6 m) (jW p) (jW q):=by
 intro i
 simp only [q190,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
 simp
def qj {α : Type} (bits:Nat):List α → List α
 | []=>[]
 | w::ws=>if bits &&& 1 == 1 then w::qj (bits >>> 1) ws else qj (bits >>> 1) ws
theorem vL {α : Type} (bits:Nat) (ws:List α):(qj bits ws).Sublist ws:=by
 induction ws generalizing bits with
 | nil=>exact List.Sublist.slnil
 | cons a ws ih =>
   unfold qj
   split
   · exact List.Sublist.cons₂ _ (ih _)
   · exact List.Sublist.cons _ (ih _)
def j4 (_g:Forest) (depth:Nat):=depth
def v9 (g:Forest) (k i:Nat):Nat × List Decor × List Decor :=
 let raw:=jn g
 let (_,depth,_,_,_,_,_,data):=g.levels k
 let len:=10*j4 g depth
 let width:=len+raw.length+depth
 let recp:=q5 data (i*width) width
 let stored:=recp &&& ((1 <<< len)-1)
 let ops:=stored
 let bank:=jU depth ops raw
 (ops,bank,qj (recp >>> len) bank)
def z169 (x pos width:Nat):=(x >>> pos) &&& ((1 <<< width)-1)
def yq (bank:List Decor) (ops paid:Nat):Nat → List Choice
 | 0=>[]
 | n+1 =>
   let more:=yq bank (ops >>> 10) (paid >>> 1) n
   if paid &&& 1 == 0 then more else
     (z169 ops 8 2,(bank.getD (ops &&& 15) zH).1,
       (bank.getD (z169 ops 4 4) zH).1) :: more
def jH (g:Forest) (ops d:Nat) (bank:List Decor) (idx paid:Nat):Option BoundPool :=
 (g.cols[idx]?).bind fun ci =>
   materialize g.mode (zq (jX g.mask ci)) (yq bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2
theorem vG (g:Forest)
   (cols : ∀ ci ∈ g.cols,Slice g.mode (zq (jX g.mask ci)) (zz g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
   {i ops depth bank paid c} (h:jH g ops depth bank i paid=some c) :
   qq g.mode (vars g.mask) (zz g) c:=by
 unfold jH at h
 cases e:g.cols[i]? with
 | none=>simp [e] at h
 | some ci =>
   simp only [e,Option.bind_some] at h
   apply wL _ h
   exact cols ci (List.mem_of_getElem? e)
def vR (data:Nat → Nat) (w v:Nat):Nat → Nat → List (Nat × Nat)
 | 0,_=>[]
 | n+1,pos =>
   let x:=q5 data pos (w+v)
   (x &&& ((1 <<< w)-1),x >>> w) :: vR data w v n (pos+w+v)
def zY (g:Forest) (k i:Nat):=(v9 g k i).2.2.map Prod.fst
def qF (g:Forest) (k:Nat) (pair:Nat × Nat):Option (List Sig) :=
 if pair.1 ≥ (g.levels k).1 then none else
   (g.autos[pair.2]?).map fun perm=>(zY g k pair.1).map (zj (perm.map qe).reverse)
theorem yv (g:Forest) (k:Nat)
   (names : ∀ x ∈ g.autos,wA (zz g) (x.map qe)=true)
   (earlier : ∀ i < (g.levels k).1,Impossible g.mode (zz g) k (zY g k i).toFinset)
   {pair out} (h:qF g k pair=some out) :
   Impossible g.mode (zz g) k out.toFinset:=by
 unfold qF at h
 split at h
 · contradiction
 next valid =>
   cases e:g.autos[pair.2]? with
   | none=>simp [e] at h
   | some perm =>
     simp only [e,Option.map_some,Option.some.injEq] at h
     subst out
     exact yu (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))
def qN (g:Forest) (k i:Nat) :=
 let raw:=jn g
 let (num,depth,cw,iw,pw,offw,lw,data):=g.levels k
 let (ops,bank,ws):=v9 g k i
 let values:=ws.map Prod.fst
 let start:=num*(10*j4 g depth+raw.length+depth)
 let pos:=start+num*offw+q5 data (start+i*offw) offw
 let nr:=q5 data pos 5
 let nl:=q5 data (pos+5) lw
 let st:=pos+5+lw
 let rules:=(vR data cw depth nr st).filterMap (fun (a,b)=>jH g ops depth bank a b)
 let ls:=fun tag=>((g.index k tag).bind (qF g (k-1))).toList
 decide values.Nodup && !(values.contains (zz g)) &&
   (if k=0 then true else jz (k,ws.length,ws,jN g.mode ws,rules,ls) ws)
theorem jQ (g:Forest) (k i:Nat)
   (samples:qr (zz g) (jW fun j=>(g.samples j).1) (jW fun j=>(g.samples j).2))
   (cols : ∀ ci ∈ g.cols,Slice g.mode (zq (jX g.mask ci)) (zz g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
   (names : ∀ x ∈ g.autos,wA (zz g) (x.map qe)=true)
   (prior:k>0 → ∀ j < (g.levels (k-1)).1,Impossible g.mode (zz g) (k-1) (zY g (k-1) j).toFinset)
   (checked:qN g k i=true):Impossible g.mode (zz g) k (zY g k i).toFinset:=by
 simp only [qN,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
 have hN:=checked.1.1
 have hT:zz g ∉ zY g k i:=by simpa [zY] using checked.1.2
 by_cases h0:k=0
 · subst k
   intro t lo h
   have ht:t=0:=by omega
   subst t
   generalize he:(zY g 0 i).toFinset=S at h
   obtain ⟨hS,_⟩:=h
   exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
 apply z368 (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
 · intro v hv
   apply vE _ _ _ _ _ (vJ g) v
   exact (vL _ _).subset hv
 · intro p hp
   obtain ⟨⟨a,b⟩,_,h⟩:=List.mem_filterMap.mp hp
   exact vG g cols h
 · intro tag xs hx
   have e:((g.index k tag).bind (qF g (k-1)))=some xs:=by simpa using hx
   obtain ⟨pair,_,h⟩:=Option.bind_eq_some_iff.mp e
   exact yv g _ names (prior (by omega)) h
def block (g:Forest) (k start:Nat):Nat → Bool
 | 0=>true
 | n+1=>qN g k (start+n)&&block g k start n
theorem z308 {g k start n} (h:block g k start n=true) (j:Nat) (lo:start≤j) (hi:j<start+n) :
   qN g k j=true:=by
 induction n with
 | zero=>omega
 | succ n ih =>
   simp only [block,Bool.and_eq_true] at h
   by_cases eq:j=start+n
   · simpa [eq] using h.1
   · exact ih h.2 (by omega)
theorem zn {g k start a b} (h:block g k start a=true)
   (h' : block g k (start+a) b=true):block g k start (a+b)=true:=by
 induction b with
 | zero=>simpa using h
 | succ b ih =>
   simp only [block,Bool.and_eq_true] at h'
   simp only [Nat.add_succ,block,Bool.and_eq_true]
   exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩
def zD (g:Forest) (top:Nat) :=
 ∀ k ≤ top,block g k 0 (g.levels k).1=true
def zp (g:Forest) (prior:Nat → Nat) :=
 (qz g.mask (fun j=>(g.samples j).1) == BitVec.allOnes 768) &&
 (qz g.mask (fun j=>(g.samples j).2) == 0) &&
 g.cols.all (fun c=>vl g.mask c prior) &&
 g.autos.all (fun p=>wA (zz g) (p.map qe))
theorem z384 (g:Forest) (top:Nat) (prior:Nat → Nat)
   (lower : ∀ q,Lower g.mode (zq q) (z1 q) (prior q))
   (geometry:zp g prior=true) (rows:zD g top) :
   ∀ k ≤ top,∀ i < (g.levels k).1,Impossible g.mode (zz g) k (zY g k i).toFinset:=by
 simp only [zp,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
 intro k
 induction k with
 | zero =>
   intro hk i hi
   apply jQ g 0 i (v2 geometry.1.1.1 geometry.1.1.2)
     (fun x hx=>vk _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
   exact z308 (rows 0 hk) i (by omega) (by omega)
 | succ k ih =>
   intro hk i hi
   apply jQ g _ i (v2 geometry.1.1.1 geometry.1.1.2)
     (fun x hx=>vk _ prior lower (geometry.1.2 x hx)) geometry.2
     (fun _=>by simpa using ih (by omega))
   exact z308 (rows _ hk) i (by omega) (by omega)
def j5 (g:Forest) (k i:Nat) (ws:List Sig) :=
 decide (i < (g.levels k).1)&&jC (zY g k i) ws
theorem z362 {g top prior k i ws} (low : ∀ q,Lower g.mode (zq q) (z1 q) (prior q))
   (geom:zp g prior=true) (blocks:zD g top) (le:k ≤ top)
   (idx:j5 g k i ws=true):Impossible g.mode (zz g) k ws.toFinset:=by
 simp only [j5,Bool.and_eq_true,decide_eq_true_eq] at idx
 rw [←qU idx.2]
 exact z384 g top prior low geom blocks _ le i idx.1
def Known (u:Bool) (entries:List (Nat × Nat)) := ∀ e ∈ entries,Lower u (zq e.1) (z1 e.1) e.2
def za (old:List (Nat × Nat)) (L:Nat) (carries:List (Nat × List Nat)) :=
 carries.map (fun v=>(v.1,L)) ++ old
theorem z6 {u old L m carries} (previous:Known u old)
   (main:Lower u (zq m) (z1 m) L)
   (ok:carries.all (fun v=>z228 v.1 m v.2)=true) :
   Known u (za old L carries):=by
 intro e he
 rcases List.mem_append.mp he with hx | h
 · obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hx
   exact q298 (List.all_eq_true.mp ok _ hv) main
 · exact previous e h
theorem z175:Known true []:=by simp [Known]
theorem z372 {u es} (h:Known true es):Known u es:=fun e he=>z369 (h e he)
def q1 (v:Nat) (upper:Nat):=2^769*upper+v
def zm {α : Type} (f : α → Bits):List α → Nat
 | []=>0
 | x::xs=>q1 (f x).toNat (zm f xs)
def units:Nat → Nat
 | 0=>0
 | n+1=>q1 1 (units n)
theorem ya (x:Bits):x.toNat < 2^769 :=
 lt_trans x.isLt (by decide +kernel)
theorem q167 (a b:Bits) (u v:Nat) :
   q1 a.toNat u &&& q1 b.toNat v=q1 (a &&& b).toNat (u &&& v):=by
 apply Nat.eq_of_testBit_eq
 intro i
 simp only [q1,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (ya _)]
 by_cases h:i<769<;>simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem q261 (a b:Bits) (u v:Nat) :
   q1 a.toNat u ||| q1 b.toNat v=q1 (a ||| b).toNat (u ||| v):=by
 apply Nat.eq_of_testBit_eq
 intro i
 simp only [q1,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (ya _)]
 by_cases h:i<769<;>simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem q166 (a b:Bits) (u v:Nat) :
   q1 a.toNat u ^^^ q1 b.toNat v=q1 (a ^^^ b).toNat (u ^^^ v):=by
 apply Nat.eq_of_testBit_eq
 intro i
 simp only [q1,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (ya _)]
 by_cases h:i<769<;>simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem vh {α} (f g : α → Bits) (xs) :
   zm f xs &&& zm g xs=zm (fun x=>f x &&& g x) xs:=by
 induction xs with
 | nil=>simp [zm]
 | cons a xs ih=>simp only [zm,q167,ih]
theorem wP {α} (f g : α → Bits) (xs) :
   zm f xs ||| zm g xs=zm (fun x=>f x ||| g x) xs:=by
 induction xs with
 | nil=>simp [zm]
 | cons a xs ih=>simp only [zm,q261,ih]
theorem w4 {α} (f g : α → Bits) (xs) :
   zm f xs ^^^ zm g xs=zm (fun x=>f x ^^^ g x) xs:=by
 induction xs with
 | nil=>simp [zm]
 | cons a xs ih=>simp only [zm,q166,ih]
def jE (r packed:Nat):=((packed+r) >>> 768) &&& r
theorem q257 (n i:Nat) (hi:i<n):(units n).testBit (769*i)=true:=by
 induction n generalizing i with
 | zero=>omega
 | succ n ih =>
   rw [units,q1,Nat.testBit_two_pow_mul_add _ (by decide +kernel:1 < 2^769)]
   cases i with
   | zero=>simp
   | succ i =>
     have di:769*(i+1)-769=769*i:=by omega
     have ge : ¬769*(i+1)<769:=by omega
     simp only [ge,ite_false,di]
     exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem q285 (a:Bits):(a.toNat+1).testBit 768=(a==BitVec.allOnes 768):=by
 by_cases h:a=BitVec.allOnes 768
 · subst a
   decide +kernel
 · have lim:=a.isLt
   have ne:a.toNat ≠ 2^768-1:=by
     intro eq
     apply h
     apply BitVec.eq_of_toNat_eq
     simpa only [BitVec.toNat_allOnes] using eq
   have lt:a.toNat+1<2^768:=by omega
   rw [Nat.testBit_eq_false_of_lt lt]
   exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 8192 in
theorem q119 {α} (f : α → Bits) (xs:List α) (i:Nat) (hi:i<xs.length) :
   (jE (units xs.length) (zm f xs)).testBit (769*i) =
     (f xs[i]==BitVec.allOnes 768):=by
 simp only [jE,Nat.testBit_and,Nat.testBit_shiftRight,q257 _ _ hi,Bool.and_true]
 induction xs generalizing i with
 | nil=>simp at hi
 | cons a xs ih =>
   simp only [zm,List.length_cons,units,q1]
   have sum (u v x:Nat):2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1):=by omega
   rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have:=(f a).isLt; omega)]
   have hi' : i < xs.length+1:=hi
   cases i with
   | zero=>simpa using q285 (f a)
   | succ i =>
     have ge : ¬769*(i+1)+768<769:=by omega
     have di:769*(i+1)+768-769=769*i+768:=by omega
     simp only [ge,ite_false,di,List.getElem_cons_succ]
     apply ih i (by omega)
abbrev vo:=Nat × Nat
abbrev yl:=Nat × Nat × Nat
def qo {α} (s : α → Signals) (xs:List α):vo :=
 (zm (fun x=>(s x).1) xs,zm (fun x=>(s x).2) xs)
def vd {α} (c : α → Cov) (xs:List α):yl :=
 (zm (fun x=>(c x).1) xs,zm (fun x=>(c x).2.1) xs,
  zm (fun x=>(c x).2.2) xs)
def zM (d:Bool) (a:vo) :=
 if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2
theorem wB (a b:Bits):a ^^^ (a &&& b)=a &&& ~~~b:=by
 apply BitVec.eq_of_getLsbD_eq
 intro i hi
 simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
 cases a.getLsbD i<;>cases b.getLsbD i<;>rfl
theorem qE {α} (s : α → Signals) (xs:List α) (d:Bool) :
   zM d (qo s xs)=zm (fun x=>column d (s x)) xs:=by
 cases d<;>simp only [zM,qo,column,Bool.false_eq_true,ite_false,ite_true,vh,w4,wB]
def j9 (op:Nat) (a b:vo):vo :=
 if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
 else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
 else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))
theorem z147 {α} (a b : α → Decor) (xs:List α) (op:Nat) :
   j9 op (qo (fun x=>(a x).2) xs) (qo (fun x=>(b x).2) xs) =
   qo (fun x=>(dbin op (a x) (b x)).2) xs:=by
 by_cases h0:op=0
 · simp only [j9,h0,ite_true,qo,vh,dbin,bv]
 by_cases h1:op=1
 · simp [j9,h1,qo,wP,dbin,bv]
 by_cases h2:op=2
 · simp [j9,h2,qo,vh,w4,wB,dbin,bv]
 · have e (x y:Bits) : ~~~x &&& y=y &&& ~~~x:=BitVec.and_comm _ _
   simp only [j9,h0,h1,h2,ite_false,qo,vh,w4,wB,dbin,bv,e]
def jg (c:yl) (a b:Nat) (ka kb:Bool) :=
 let without1:=fun w=>c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
 let without2:=c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
 if ka then (if kb then c.1 else without1 b)
 else if kb then without1 a else without2
theorem wd {α} (c : α → Cov) (a b : α → Bits) (xs:List α) (ka kb:Bool) :
   jg (vd c xs) (zm a xs) (zm b xs) ka kb =
   zm (fun x=>jo (c x) (a x) (b x) ka kb) xs:=by
 cases ka<;>cases kb <;>
   simp only [jg,vd,vh,wP,w4,wB,jo,jA,vZ,
     Bool.false_eq_true,ite_false,ite_true]
def z4 (c:zl) (i:Nat):=c.2.2.1.getD i zH
def vB (c:zl) (i j op:Nat) (ka kb:Bool) :=
 let a:=z4 c i
 let b:=z4 c j
 qC c op a b (dbin op a b) ka kb
def jG (c:zl) (d ka kb:Bool) (op i j:Nat) :=
 let a:=z4 c i
 let b:=z4 c j
 jo c.2.2.2.1.1 (column d a.2) (column d b.2) ka kb |||
   column d (dbin op a b).2
def vu {α : Type} (f : α → Bool) (mask:Nat):List α → Bool
 | []=>true
 | x::xs=>if mask=0 then true else
   ((mask &&& 1 == 0)||f x)&&vu f (mask >>> 769) xs
theorem z150 {α} (f : α → Bool) (mask:Nat) (xs:List α) (i:Nat) (hi:i<xs.length)
   (bitOn:mask.testBit (769*i)=true) (ok:vu f mask xs=true):f xs[i]=true:=by
 induction xs generalizing mask i with
 | nil=>simp at hi
 | cons x xs ih =>
   have ne:mask≠0:=by intro e; simp [e] at bitOn
   simp only [vu,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
   cases i with
   | zero =>
     have nonzero:mask &&& 1 ≠ 0:=by
       intro he
       have at0:=congrArg (fun n:Nat=>n.testBit 0) he
       simp only [Nat.testBit_and] at at0
       change mask.testBit 0=true at bitOn
       simp [bitOn] at at0
     exact ok.1.resolve_left nonzero
   | succ i =>
     apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
     simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn
abbrev Batch:=Nat × Nat × Nat × List vo × yl
def zV (k n:Nat) (xs:List zl):Batch :=
 (k,n,units xs.length,(List.range n).map (fun i=>qo (fun c=>(z4 c i).2) xs),
   vd (fun c=>c.2.2.2.1.1) xs)
def qR (b:Batch) (i:Nat):=b.2.2.2.1.getD i (0,0)
theorem v0 (k n) (xs) {i:Nat} (h:i<n) :
   qR (zV k n xs) i=qo (fun c=>(z4 c i).2) xs:=by
 simp [qR,zV,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]
theorem z273 (d x:Sig):masked d (neg x)=d ^^^ masked d x:=by
 apply zF
 intro r
 simp only [masked,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
 cases d.getLsbD r.val<;>cases x.getLsbD r.val<;>rfl
def zL (p:Decor → Bool) (a:Decor) (keep:Bool) :=
 if keep then 0 else (p a).toNat
theorem z151 (p:Decor → Bool) (ws:List Decor) (a:Decor) (keep:Bool) :
   ws.countP p ≤ (jv ws a keep).countP p + zL p a keep:=by
 cases keep
 · simp only [jv,Bool.false_eq_true,ite_false,zL,List.countP_erase]
   split
   next h=>simp [h.2]; omega
   next=>omega
 · simp [jv,zL]
theorem q175 (p:Decor → Bool) (ws:List Decor) (a b:Decor) (ka kb:Bool) :
   ws.countP p - zL p a ka - zL p b kb ≤
   (q8 ws a b ka kb).countP p:=by
 have h1:=z151 p ws a ka
 have h2:=z151 p (jv ws a ka) b kb
 simp only [q8]
 omega
noncomputable def force {β : Type} (n:Nat) (f:Nat → β) : β:=Nat.rec (f 0) (fun k _=>f (Nat.succ k)) n
theorem qT {β : Type} (n:Nat) (f:Nat → β):force n f=f n:=by cases n<;>rfl
noncomputable def jS {α β : Type} (f : α → Nat) (l:List α):(List Nat → β) → β :=
 List.rec (fun k=>k []) (fun a _ ih k=>force (f a) fun x=>ih fun xs=>k (x::xs)) l
theorem vT {α β : Type} (f : α → Nat) (l:List α) (k:List Nat → β):jS f l k=k (l.map f):=by
 induction l generalizing k with
 | nil=>rfl
 | cons a l ih =>
   change force (f a) (fun x=>jS f l fun xs=>k (x::xs))=_
   rw [qT,ih]
   rfl
def nmask (d:Nat) (a:Sig):Nat:=Nat.land a.toNat d
noncomputable def vH (m:Nat) (l:List Nat):Bool:=List.rec false (fun v _ ih=>or (Nat.beq m v) ih) l
def nconst (d m:Nat):Bool:=or (Nat.beq m 0) (Nat.beq m d)
noncomputable def navail (u:Bool) (d:Nat) (pm:List Nat) (m:Nat):Bool :=
 or (or (nconst d m) (vH m pm)) (and u (vH (Nat.xor d m) pm))
theorem vO (d a:Sig):nmask d.toNat a=(masked d a).toNat:=(BitVec.toNat_and _ _).symm
theorem jl (a b:Sig):Nat.beq a.toNat b.toNat=(a==b):=by
 rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
 exact BitVec.toNat_inj
theorem w1 (d a:Sig):nconst d.toNat (nmask d.toNat a)=zg d a:=by
 rw [vO]
 have e:Nat.beq (masked d a).toNat 0=(masked d a == zero):=by
   have z0:zero.toNat=0:=by simp [zero]
   rw [←jl,z0]
 rw [nconst,e,jl]
 rfl
theorem z310 (x d:Sig) (pool:List Sig):vH x.toNat (pool.map (nmask d.toNat))=(pool.map (masked d)).any (fun v=>v==x):=by
 induction pool with
 | nil=>rfl
 | cons a l ih =>
   change or (Nat.beq x.toNat (nmask d.toNat a)) (vH x.toNat (l.map (nmask d.toNat)))=_
   rw [ih,vO,jl,List.map_cons,List.any_cons,Bool.beq_comm]
theorem w2 (u:Bool) (d a:Sig) (pool:List Sig) :
   navail u d.toNat (pool.map (nmask d.toNat)) (nmask d.toNat a)=zw u d pool a:=by
 have x:Nat.xor d.toNat (masked d a).toNat=(masked d (neg a)).toNat:=by
   rw [z273]
   exact (BitVec.toNat_xor _ _).symm
 rw [navail,w1,vO,x,z310,z310]
 simp only [zw,zg]
def unav (u:Bool) (p:BoundPool) (w:Decor):Nat:=cond (zw u p.domain p.wires w.1) 0 1
def wG (u:Bool) (p:BoundPool) (ws:List Decor) (k:Nat) (a b:Decor) (op:Nat) (ka kb:Bool):Bool :=
 let const:=fun w:Decor=>zg p.domain w.1
 let z:=bin op a.1 b.1
 let cm:=ws.countP const - zL const a ka - zL const b kb + (zg p.domain z).toNat
 (((ws.map (unav u p)).sum == cond ka 0 (unav u p a) + cond kb 0 (unav u p b)) &&
   decide (k+p.paid+(!zw u p.domain p.wires z).toNat < p.bound+cm)) &&
   (zw u p.domain p.wires z||(zw u p.domain p.wires a.1&&zw u p.domain p.wires b.1))
def zN (op x y:Nat):Nat:=cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
 (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))
theorem q366 (op:Nat) (d a b:Sig):zN op (nmask d.toNat a) (nmask d.toNat b)=nmask d.toNat (bin op a b):=by
 have tn (x y:Sig):Nat.land x.toNat y.toNat=(x &&& y).toNat:=(BitVec.toNat_and x y).symm
 have tx (x y:Sig):Nat.xor x.toNat y.toNat=(x ^^^ y).toNat:=(BitVec.toNat_xor x y).symm
 have tor (x y:Sig):Nat.lor x.toNat y.toNat=(x ||| y).toNat:=(BitVec.toNat_or x y).symm
 simp only [vO]
 unfold zN
 by_cases h0:op=0
 · subst h0
   change Nat.land _ _=_
   rw [tn]
   congr 1
   apply zF
   intro r
   simp only [masked,bin,bit,ite_true,BitVec.getLsbD_and]
   cases a.getLsbD r.val<;>cases b.getLsbD r.val<;>cases d.getLsbD r.val<;>rfl
 by_cases h1:op=1
 · subst h1
   change Nat.lor _ _=_
   rw [tor]
   congr 1
   apply zF
   intro r
   simp only [masked,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
   cases a.getLsbD r.val<;>cases b.getLsbD r.val<;>cases d.getLsbD r.val<;>rfl
 have e0:Nat.beq op 0=false:=Bool.eq_false_iff.mpr (fun h=>h0 (Nat.eq_of_beq_eq_true h))
 have e1:Nat.beq op 1=false:=Bool.eq_false_iff.mpr (fun h=>h1 (Nat.eq_of_beq_eq_true h))
 by_cases h2:op=2
 · subst h2
   change Nat.xor _ (Nat.land _ _)=_
   rw [tn,tx]
   congr 1
   apply zF
   intro r
   simp only [masked,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
   cases a.getLsbD r.val<;>cases b.getLsbD r.val<;>cases d.getLsbD r.val<;>rfl
 have e2:Nat.beq op 2=false:=Bool.eq_false_iff.mpr (fun h=>h2 (Nat.eq_of_beq_eq_true h))
 rw [e0,e1,e2]
 change Nat.xor _ (Nat.land _ _)=_
 rw [tn,tx]
 congr 1
 apply zF
 intro r
 simp only [masked,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
 cases a.getLsbD r.val<;>cases b.getLsbD r.val<;>cases d.getLsbD r.val<;>rfl
def nloss (d x:Nat) (keep:Bool):Nat:=cond keep 0 (cond (nconst d x) 1 0)
theorem z270 (d:Sig) (a:Decor) (keep:Bool) :
   nloss d.toNat (nmask d.toNat a.1) keep=zL (fun w:Decor=>zg d w.1) a keep:=by
 rw [nloss,w1,zL]
 cases keep
 · cases zg d a.1<;>rfl
 · rfl
abbrev QS:=Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool
noncomputable def vc (u:Bool) (k:Nat) (ws:List Decor) (p:BoundPool):QS :=
 let d:=p.domain.toNat
 let ms:=ws.map (fun w:Decor=>nmask d w.1)
 (d,ms.countP (nconst d),p.bound,Nat.add k p.paid,(ms.map fun m=>cond (navail u d (p.wires.map (nmask d)) m) 0 1).sum,ms,p.wires.map (nmask d),u)
noncomputable def z170 {β : Type} (b:Bool) (f:Bool → β) : β:=Bool.rec (f false) (f true) b
noncomputable def w6 {β : Type} (u:Bool) (k:Nat) (ws:List Decor) (p:BoundPool) (f:QS → β) : β :=
 force p.domain.toNat fun d=>jS (nmask d) p.wires fun pm=>jS (fun w:Decor=>nmask d w.1) ws fun ms =>
 force (ms.countP (nconst d)) fun c=>force p.bound fun l=>force (Nat.add k p.paid) fun t =>
 force (ms.map fun m=>cond (navail u d pm m) 0 1).sum fun v=>z170 u fun u=>f (d,c,l,t,v,ms,pm,u)
theorem z222 {β : Type} (u k ws p) (f:QS → β):w6 u k ws p f=f (vc u k ws p):=by
 have e (b:Bool) (f:Bool → β):z170 b f=f b:=by cases b<;>rfl
 simp only [w6,qT,vT,e]
 rfl
noncomputable def vy {β : Type} (u:Bool) (k:Nat) (ws:List Decor) (ps:List BoundPool):(List QS → β) → β :=
 List.rec (fun f=>f []) (fun p _ ih f=>w6 u k ws p fun q=>ih fun qs=>f (q::qs)) ps
theorem z139 {β : Type} (u k ws ps) (f:List QS → β):vy u k ws ps f=f (ps.map (vc u k ws)):=by
 induction ps generalizing f with
 | nil=>rfl
 | cons p ps ih =>
   change w6 u k ws p (fun q=>vy u k ws ps fun qs=>f (q::qs))=_
   rw [z222,ih]
   rfl
def kwN (v:Nat):Nat :=
 let n:=v % 2305843009213693951
 (n*(n+971)) % 2305843009213693951
abbrev Lane:=zl × Nat × Nat × List QS × List Nat × Nat
noncomputable def qx (c:zl):Lane :=
 let ws:=c.2.2.1.map (fun w:Decor=>w.1.toNat)
 (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (vc c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)
noncomputable def vz {β : Type} (cs:List zl):(List Lane → β) → β :=
 List.rec (fun f=>f []) (fun c _ ih f=>force c.2.2.1.length fun n=>force (cond c.2.2.2.1.2 4 2) fun l =>
   jS (fun w:Decor=>w.1.toNat) c.2.2.1 fun ws=>force (ws.map kwN).sum fun t =>
   vy c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs=>ih fun ys=>f ((c,n,l,qs,ws,t)::ys)) cs
theorem jq {β : Type} (cs) (f:List Lane → β):vz cs f=f (cs.map qx):=by
 induction cs generalizing f with
 | nil=>rfl
 | cons c cs ih =>
   change force c.2.2.1.length (fun n=>force (cond c.2.2.2.1.2 4 2) fun l =>
     jS (fun w:Decor=>w.1.toNat) c.2.2.1 fun ws=>force (ws.map kwN).sum fun t =>
     vy c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs=>vz cs fun ys=>f ((c,n,l,qs,ws,t)::ys))=_
   rw [qT,qT,vT,qT,z139,ih]
   rfl
noncomputable def z121 (s:QS) (i j op:Nat) (ka kb:Bool):Bool :=
 force (s.2.2.2.2.2.1.getD i 0) fun x=>force (s.2.2.2.2.2.1.getD j 0) fun y =>
 let av:=navail s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
 let hi:=Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (nloss s.1 x ka)) (nloss s.1 y kb))
 let lo:=s.2.2.2.1
 and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
 (cond (Nat.ble (Nat.succ lo) hi)
   (force (zN op x y) fun z=>or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
   (cond (Nat.ble lo hi) (nconst s.1 (zN op x y)) false))
theorem q258 {d:Nat} (ws:List Decor) (i:Nat) (hd:nmask d zero=0) :
   (ws.map (fun w:Decor=>nmask d w.1)).getD i 0=nmask d (ws.getD i zH).1:=by
 simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
 cases ws[i]? with
 | none=>exact hd.symm
 | some v=>rfl
theorem q186 {u k p ws i j op ka kb} (h:z121 (vc u k ws p) i j op ka kb=true) :
   wG u p ws k (ws.getD i zH) (ws.getD j zH) op ka kb=true:=by
 have z0:nmask p.domain.toNat zero=0:=by
   have : zero.toNat=0:=by simp [zero]
   simp [nmask,this]
 have su:(((ws.map (fun w:Decor=>nmask p.domain.toNat w.1)).map fun m=>cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) m) 0 1).sum) =
     (ws.map (unav u p)).sum:=by
   rw [List.map_map]
   refine congrArg List.sum (List.map_congr_left ?_)
   intro w _
   change cond (navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat)) (nmask p.domain.toNat w.1)) 0 1=_
   rw [w2]
   rfl
 simp only [z121,vc,qT,q258 _ _ z0,su,List.countP_map,Function.comp_def,w1] at h
 generalize ws.getD i zH=a at h ⊢
 generalize ws.getD j zH=b at h ⊢
 replace h:and (Nat.beq (ws.map (unav u p)).sum (Nat.add (cond ka 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)) 0 1))))
  (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w:Decor=>zg p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb))))
   (or ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w:Decor=>zg p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (and ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat a.1)) ((navail u p.domain.toNat (p.wires.map (nmask p.domain.toNat))) (nmask p.domain.toNat b.1)))))
   (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w:Decor=>zg p.domain w.1)) (nloss p.domain.toNat (nmask p.domain.toNat a.1) ka)) (nloss p.domain.toNat (nmask p.domain.toNat b.1) kb)))) (nconst p.domain.toNat (zN op (nmask p.domain.toNat a.1) (nmask p.domain.toNat b.1))) false))=true:=h
 rw [q366,w1,w2,w2,w2,z270,z270] at h
 have ca:zg p.domain (bin op a.1 b.1)=true → zw u p.domain p.wires (bin op a.1 b.1)=true:=by
   intro zc
   simp only [zw,zg,Bool.or_eq_true] at zc ⊢
   exact Or.inl (Or.inl zc)
 simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
 obtain ⟨hu,h⟩:=h
 simp only [wG,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
 refine ⟨⟨hu,?_⟩,?_⟩
 all_goals
   generalize ws.countP (fun w=>zg p.domain w.1) - zL (fun w:Decor=>zg p.domain w.1) a ka -
     zL (fun w:Decor=>zg p.domain w.1) b kb=c at h ⊢
   generalize zg p.domain (bin op a.1 b.1)=r at h ca ⊢
   generalize zw u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
   cases h1:Nat.ble (k+p.paid+1) (p.bound+c)
   · rw [h1] at h
     cases h2:Nat.ble (k+p.paid) (p.bound+c)
     · simp [h2] at h
     · have:=Nat.ble_eq.mp h2
       simp only [h2,cond_true,cond_false] at h
       subst h
       rw [ca rfl]
       simp<;>omega
   · rw [h1] at h
     have l1:=Nat.ble_eq.mp h1
     simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
     rcases h with rfl | ⟨l2,ha,hb⟩
     · simp<;>omega
     · first
       | (have : (!q).toNat ≤ 1:=Bool.toNat_le _
          omega)
       | simp [ha,hb]
theorem z176 (m:Nat) (l:List Nat):vH m l=true ↔ m ∈ l:=by
 induction l with
 | nil=>simp [vH]
 | cons a l ih =>
   change or (Nat.beq m a) (vH m l)=true ↔ _
   rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]
noncomputable def z371 (fl:Nat → Option (List Nat)) (l:Lane) (i j op:Nat) (ka kb:Bool):Bool :=
 force (l.2.2.2.2.1.getD i 0) fun x=>force (l.2.2.2.2.1.getD j 0) fun y=>force (zN op x y) fun z =>
 Option.rec false (fun ys=>jS (fun v=>v) ys fun ys =>
   and (vH z ys) (and (l.2.2.2.2.1.all fun v=>or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (vH v ys)))
     (ys.all fun v=>or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (vH v l.2.2.2.2.1)))))
   (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))
theorem z373 (xs:List Sig):z114 xs=(xs.map jc).sum:=by
 have go (a:Nat):xs.foldl (fun v x=>v+jc x) a=a+(xs.map jc).sum:=by
   induction xs generalizing a with
   | nil=>rfl
   | cons x xs ih=>rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
 exact (go 0).trans (Nat.zero_add _)
theorem z124 (f:Decor → Nat) {ws:List Decor} {a b:Decor} (ha:a ∈ ws) (hb:b ∈ ws) (ne:a≠b) (ka kb:Bool) :
   ((q8 ws a b ka kb).map f).sum=(ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)):=by
 have er {l:List Decor} {x:Decor} (hx:x ∈ l):(l.map f).sum=f x + ((l.erase x).map f).sum:=by
   have:=((List.perm_cons_erase hx).map f).sum_eq
   rwa [List.map_cons,List.sum_cons] at this
 have hm:b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm ne)).mpr hb
 have e1:=er ha
 have e2:=er hb
 have e3:=er hm
 cases ka<;>cases kb<;>simp only [q8,jv,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false]<;>omega
theorem z140 {u p k ws a b op ka kb} (ha:a∈ws) (hb:b∈ws) (ne:a≠b) (al:vn u op=true)
   (h:wG u p ws k a b op ka kb=true) :
   qb u p k ((q8 ws a b ka kb).map Prod.fst) (zT op a b)=true:=by
 let const:=fun w:Decor=>zg p.domain w.1
 let z:=bin op a.1 b.1
 let rest:=q8 ws a b ka kb
 have ck:=q175 const ws a b ka kb
 change ws.countP const - zL const a ka - zL const b kb ≤ rest.countP const at ck
 simp only [wG,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
 obtain ⟨⟨hu,hc⟩,hz⟩:=h
 have sum:=z124 (unav u p) ha hb ne ka kb
 rw [hu] at sum
 have zs:((q8 ws a b ka kb).map (unav u p)).sum=0:=by omega
 have hs:(rest.map Prod.fst).all (zw u p.domain p.wires)=true:=by
   apply List.all_eq_true.mpr
   intro _ hm
   obtain ⟨w,hw,rfl⟩:=List.mem_map.mp hm
   have v:=List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
   cases e:zw u p.domain p.wires w.1
   · simp [unav,e] at v
   · rfl
 have opOK:(!(!zw u p.domain p.wires z)||jV u p.domain p.wires (zT op a b))=true:=by
   simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
   rcases hz with hz | ⟨x,y⟩
   · simp [z,hz]
   · simp [jV,zT,x,y,al]
 change k+p.paid+(!zw u p.domain p.wires z).toNat < p.bound+(ws.countP const - zL const a ka -
       zL const b kb+(zg p.domain z).toNat) at hc
 dsimp only [rest] at hs
 have ez:zE (zT op a b)=z:=rfl
 simp only [qb,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
     List.countP_map,Function.comp_def]
 change k+p.paid+(!zw u p.domain p.wires z).toNat <
     p.bound+(rest.countP const + if zg p.domain z then 1 else 0)
 cases hc' : zg p.domain z<;>simp [hc'] at hc ⊢<;>omega
theorem q108 (op:Nat) (a b:Sig):zN op a.toNat b.toNat=(bin op a b).toNat:=by
 have e (v:Sig):nmask one.toNat v=v.toNat:=by
   rw [vO]
   congr 1
   exact BitVec.and_allOnes
 have:=q366 op one a b
 rwa [e,e,e] at this
theorem j156 (ws:List Decor) (i:Nat) :
   (ws.map (fun w:Decor=>w.1.toNat)).getD i 0=(ws.getD i zH).1.toNat:=by
 simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
 cases ws[i]? with
 | none =>
   have z0:zero.toNat=0:=by simp [zero]
   exact z0.symm
 | some v=>rfl
theorem q109 {c:zl} {i j} (nd:(c.2.2.1.map Prod.fst).Nodup)
   (hi:i<c.2.2.1.length) (hj:j<c.2.2.1.length) (hij:i≠j):(z4 c i).1 ≠ (z4 c j).1:=by
 have gi:z4 c i=c.2.2.1[i]:=by simp [z4,List.getD_eq_getElem?_getD,hi]
 have gj:z4 c j=c.2.2.1[j]:=by simp [z4,List.getD_eq_getElem?_getD,hj]
 rw [gi,gj]
 intro e
 apply hij
 apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
 simpa using e
theorem z370 {c:zl} {fl i j op ka kb} (nd:(c.2.2.1.map Prod.fst).Nodup)
   (hfl : ∀ tag ys,fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag,ys=xs.map BitVec.toNat)
   (hi:i<c.2.2.1.length) (hj:j<c.2.2.1.length) (hij:i≠j) (h:z371 fl (qx c) i j op ka kb=true) :
   (c.2.2.2.2.2 (z114 (zE (zT op (z4 c i) (z4 c j)) ::
     (q8 c.2.2.1 (z4 c i) (z4 c j) ka kb).map Prod.fst))).any (jC
     (zE (zT op (z4 c i) (z4 c j)) ::
     (q8 c.2.2.1 (z4 c i) (z4 c j) ka kb).map Prod.fst))=true:=by
 have mem (t) (ht:t<c.2.2.1.length):z4 c t ∈ c.2.2.1:=by
   simp [z4,List.getD_eq_getElem?_getD,ht]
 have hne:=q109 nd hi hj hij
 have ha:=mem i hi
 have hb:=mem j hj
 have hab:z4 c i ≠ z4 c j:=fun e=>hne (congrArg Prod.fst e)
 have kv (v:Sig):=z115 nd ha hb ka kb v
 have sum:=z124 (fun w:Decor=>jc w.1) ha hb hab ka kb
 have wi:z4 c i=c.2.2.1.getD i zH:=rfl
 have wj:z4 c j=c.2.2.1.getD j zH:=rfl
 simp only [z371,qx,qT,j156,←wi,←wj,q108] at h
 generalize z4 c i=a at *
 generalize z4 c j=b at *
 change Option.rec false _ (fl (jc (bin op a.1 b.1)+(((c.2.2.1.map (fun w:Decor=>w.1.toNat)).map kwN).sum -
   (cond ka 0 (jc a.1)) - (cond kb 0 (jc b.1)))))=true at h
 have tot:((c.2.2.1.map (fun w:Decor=>w.1.toNat)).map kwN).sum=(c.2.2.1.map (fun w:Decor=>jc w.1)).sum:=by
   rw [List.map_map]
   rfl
 rw [tot,←sum] at h
 have tag:z114 (zE (zT op a b) :: (q8 c.2.2.1 a b ka kb).map Prod.fst) =
     jc (bin op a.1 b.1)+((q8 c.2.2.1 a b ka kb).map (fun w:Decor=>jc w.1)).sum:=by
   rw [z373,List.map_cons,List.sum_cons,List.map_map]
   rfl
 rw [←tag] at h
 generalize z114 (zE (zT op a b) :: (q8 c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
 cases hf:fl t with
 | none=>simp [hf] at h
 | some ys =>
   obtain ⟨xs,hx,rfl⟩:=hfl t ys hf
   rw [hf] at h
   simp only [vT,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,z176,Nat.beq_eq,Bool.not_eq_true'] at h
   obtain ⟨h1,h2,h3⟩:=h
   have back {v:Sig} (hv:v.toNat ∈ xs.map BitVec.toNat):v ∈ xs:=by
     obtain ⟨w,hw,e⟩:=List.mem_map.mp hv
     exact BitVec.toNat_inj.mp e ▸ hw
   apply List.any_eq_true.mpr
   refine ⟨xs,hx,?_⟩
   simp only [jC,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
   constructor
   · intro v hv
     rcases List.mem_cons.mp hv with rfl | hv
     · exact back h1
     · obtain ⟨hw,va,vb⟩:=(kv v).mp hv
       obtain ⟨w,hm,rfl⟩:=List.mem_map.mp hw
       rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
       · rcases va with va | va
         · exact absurd (BitVec.toNat_inj.mp y) va
         · simp [va] at x
       · rcases vb with vb | vb
         · exact absurd (BitVec.toNat_inj.mp y) vb
         · simp [vb] at x
       · exact back x
   · intro v hv
     rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
     · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
     · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
       · obtain ⟨w,hw,e⟩:=List.mem_map.mp m
         exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
       · rcases x with x | x
         · exact Or.inr x
         · refine Or.inl fun e=>?_
           subst e
           simp at x
       · rcases y with x | x
         · exact Or.inr x
         · refine Or.inl fun e=>?_
           subst e
           simp at x
noncomputable def jT (fl:Nat → Option (List Nat)) (l:Lane) (i j op:Nat) (ka kb:Bool):Bool :=
 or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
   (or (l.2.2.2.1.any fun s=>z121 s i j op ka kb) (z371 fl l i j op ka kb))) (vB l.1 i j op ka kb)
theorem vU {c:zl} {fl i j op ka kb} (nd:(c.2.2.1.map Prod.fst).Nodup)
   (hfl : ∀ tag ys,fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag,ys=xs.map BitVec.toNat)
   (h:jT fl (qx c) i j op ka kb=true) :
   vB c i j op ka kb=true:=by
 simp only [jT,Bool.or_eq_true,Bool.and_eq_true] at h
 rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
 · have hi:=Nat.ble_eq.mp hi
   have hj:=Nat.ble_eq.mp hj
   have ho:=Nat.ble_eq.mp ho
   change Nat.succ i ≤ c.2.2.1.length at hi
   change Nat.succ j ≤ c.2.2.1.length at hj
   change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
   have al:vn c.2.2.2.1.2 op=true:=by
     cases hu:c.2.2.2.1.2<;>simp [hu] at ho<;>simp [vn]<;>omega
   have mem (t) (ht:t<c.2.2.1.length):z4 c t ∈ c.2.2.1:=by
     simp [z4,List.getD_eq_getElem?_getD,ht]
   obtain ⟨_,hm,ok⟩:=List.any_eq_true.mp h
   obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hm
   have hne:=q109 nd hi hj (fun e=>by simp [e] at hn)
   have closed:=z140 (mem i hi) (mem j hj) (fun e=>hne (congrArg Prod.fst e)) al (q186 ok)
   have cut:c.2.2.2.2.1.any (fun p=>qb c.2.2.2.1.2 p (c.1-1)
       ((q8 c.2.2.1 (z4 c i) (z4 c j) ka kb).map Prod.fst)
       (zT op (z4 c i) (z4 c j)))=true :=
     List.any_eq_true.mpr ⟨p,hp,closed⟩
   simp only [vB,qC,qy,cut,Bool.or_true]
   repeat' split
   all_goals rfl
 · have cut:=z370 nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e=>by simp [e] at hn) h
   simp only [vB,qC,qy,cut,Bool.true_or]
   repeat' split
   all_goals rfl
 · exact h
def wE (v t:Nat):Nat:=cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)
def j3 (v:Nat):Bool:=and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)
set_option maxRecDepth 8192 in
theorem z355 : ∀ v:Fin 144,j3 v.val=true → ∀ t:Fin 9,wE v.val t.val<9 ∧
   vI (qe v.val) (inputs.getD t.val zero)=inputs.getD (wE v.val t.val) zero:=by decide +kernel
theorem z356 {v t:Nat} (hv:j3 v=true) (ht:t<9):wE v t<9 ∧
   vI (qe v) (inputs.getD t zero)=inputs.getD (wE v t) zero:=by
 have lt:v<144:=by
   simp only [j3,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
   omega
 exact z355 ⟨v,lt⟩ hv ⟨t,ht⟩
def q284 (perm:List Nat) (t:Nat):Nat:=perm.foldl (fun t v=>wE v t) t
theorem q283 {perm:List Nat} (ok:perm.all j3=true) {t:Nat} (ht:t<9) :
   zj (perm.map qe).reverse (inputs.getD t zero)=inputs.getD (q284 perm t) zero:=by
 rw [zj,List.foldr_reverse,List.foldl_map]
 induction perm generalizing t with
 | nil=>rfl
 | cons v perm ih =>
   simp only [List.all_cons,Bool.and_eq_true] at ok
   obtain ⟨lt,e⟩:=z356 ok.1 ht
   rw [List.foldl_cons,e,ih ok.2 lt]
   rfl
noncomputable def yG:Nat → Nat → List Nat → List Nat
 | 0,_,ws=>ws
 | n+1,bits,ws=>force (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
     fun z=>yG n (bits >>> 10) (ws++[z])
theorem z388 (F:Sig → Nat) (F0:F zero=0) (Fb : ∀ op a b,F (bin op a b)=zN op (F a) (F b))
   (n bits:Nat) (ds:List Decor) :
   (jU n bits ds).map (fun w=>F w.1)=yG n bits (ds.map fun w=>F w.1):=by
 have gd (ds:List Decor) (i:Nat):(ds.map fun w=>F w.1).getD i 0=F (ds.getD i zH).1:=by
   simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
   cases ds[i]? with
   | none=>exact F0.symm
   | some v=>rfl
 induction n generalizing bits ds with
 | zero=>rfl
 | succ n ih =>
   rw [yG,qT,jU,ih,gd,gd,←Fb,List.map_append]
   rfl
theorem yP {α β : Type} (f : α → β) (bits:Nat) (ws:List α) :
   (qj bits ws).map f=qj bits (ws.map f):=by
 induction ws generalizing bits with
 | nil=>rfl
 | cons w ws ih =>
   rw [List.map_cons,qj,qj]
   split
   · rw [List.map_cons,ih]
   · exact ih _
noncomputable def yc (g:Forest) (k i:Nat) (perm:List Nat):List Nat :=
 let raw:=(selected g.mask).map fun e=>(inputs.getD (q284 perm e.1) zero).toNat
 let (_,depth,_,_,_,_,_,data):=g.levels k
 let len:=10*depth
 force (q5 data (i*(len+(selected g.mask).length+depth)) (len+(selected g.mask).length+depth)) fun rec =>
 qj (rec >>> len) (yG depth (rec &&& ((1 <<< len)-1)) raw)
theorem wY (g:Forest) (k i:Nat) {perm:List Nat} (ok:perm.all j3=true) :
   yc g k i perm=((zY g k i).map (zj (perm.map qe).reverse)).map BitVec.toNat:=by
 let ms:=(perm.map qe).reverse
 let F (a:Sig):Nat:=(zj ms a).toNat
 have F0:F zero=0:=by
   change (zj ms zero).toNat=0
   rw [zt,(jh _).1]
   simp [zero]
 have Fb (op a b):F (bin op a b)=zN op (F a) (F b):=by
   change (zj ms (bin op a b)).toNat=zN op (zj ms a).toNat (zj ms b).toNat
   rw [q108,zt,ji,zt,zt]
 have raw:(jn g).map (fun w=>F w.1)=(selected g.mask).map fun e=>(inputs.getD (q284 perm e.1) zero).toNat:=by
   simp only [jn,wI,List.map_map]
   apply List.map_congr_left
   rintro ⟨j,a⟩ hm
   obtain ⟨hj,rfl⟩:=vK hm
   exact congrArg BitVec.toNat (q283 ok hj)
 have len:(jn g).length=(selected g.mask).length:=by simp [jn,wI]
 unfold yc zY v9
 rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
 simp only [qT,j4,len]
 rw [List.map_map,List.map_map,yP,←raw,←z388 F F0 Fb]
 rfl
noncomputable def ww (g:Forest) (k:Nat) (pair:Nat × Nat):Option (List Nat) :=
 if pair.1 ≥ (g.levels k).1 then none else
   (g.autos[pair.2]?).bind fun perm=>cond (perm.all j3) (some (yc g k pair.1 perm)) none
noncomputable def wX (g:Forest) (k:Nat):Nat → Option (List Nat):=fun tag=>(g.index k tag).bind (ww g (k-1))
noncomputable def z174 (fl:Nat → Option (List Nat)) (u:Bool) (b:Batch) (xs:List Lane) (i j op:Nat) (ka kb:Bool) :=
 let (k,n,r,_,cov):=b
 let len:=1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
 if len>k then true else
   let a:=qR b i
   let b':=qR b j
   let z:=j9 op a b'
   let mask:=jE r (jg cov (zM (!u) a) (zM (!u) b') ka kb ||| zM (!u) z)
   vu (fun c=>jT fl c i j op ka kb) mask xs
theorem z232 {fl u} (k n) (xs:List zl) {i j op:Nat} {ka kb}
   (hi:i<n) (hj:j<n) {q:Nat} (hq:q<xs.length)
   (budget:xs[q].1=k) (arity:xs[q].2.1=n) (mode:xs[q].2.2.2.1.2=u) (nd:(xs[q].2.2.1.map Prod.fst).Nodup)
   (hfl : ∀ tag ys,fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag,ys=zs.map BitVec.toNat)
   (pass:z174 fl u (zV k n xs) (xs.map qx) i j op ka kb=true) :
   vB xs[q] i j op ka kb=true:=by
 let len:=1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
 have eval:vB xs[q] i j op ka kb =
     if len>k then true else if jG xs[q] (!u) ka kb op i j != BitVec.allOnes 768 then true
     else if !qa (dbin op (z4 xs[q] i) (z4 xs[q] j)).1 ||
       xs[q].2.2.1.any (fun v=>v.1==(dbin op (z4 xs[q] i) (z4 xs[q] j)).1)
     then true else qy u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
       ((q8 xs[q].2.2.1 (z4 xs[q] i) (z4 xs[q] j) ka kb).map Prod.fst)
       (zT op (z4 xs[q] i) (z4 xs[q] j)):=by
   simp only [vB,qC,budget,arity,mode,len,jG]<;>rfl
 by_cases small:len>k
 · simp [eval,small]
 · let r:=units xs.length
   let a:=qR (zV k n xs) i
   let b:=qR (zV k n xs) j
   let cov:=vd (fun c:zl=>c.2.2.2.1.1) xs
   change (if len>k then true else vu _ (jE r
      (jg cov (zM (!u) a) (zM (!u) b) ka kb |||
       zM (!u) (j9 op a b))) (xs.map qx))=true at pass
   rw [if_neg small] at pass
   have ca:a=_:=v0 k n xs hi
   have cb:b=_:=v0 k n xs hj
   dsimp only [r,cov] at pass
   rw [ca,cb,z147,qE,qE,qE,wd,wP] at pass
   by_cases hit:jG xs[q] (!u) ka kb op i j=BitVec.allOnes 768
   · apply vU nd hfl
     have m:=z150 _ _ _ q (by simpa using hq) (by
       rw [q119 _ _ _ hq]
       exact beq_iff_eq.mpr hit) pass
     simpa only [List.getElem_map] using m
   · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]
noncomputable def z173 (fl:Nat → Option (List Nat)) (u:Bool) (b:Batch) (xs:List Lane) (i j op:Nat) :=
 let f:=z174 fl u b xs i j op
 f false false&&f true false&&f false true&&f true true
noncomputable def y3 (fl:Nat → Option (List Nat)) (u:Bool) (b:Batch) (xs:List Lane) (i:Nat) (js:List Nat) :=
   js.all (fun j=>(wJ u).all (z173 fl u b xs i j))
noncomputable def jJ (fl:Nat → Option (List Nat)) (u:Bool) (b:Batch) (xs:List Lane):List Nat → Bool
 | []=>true
 | i::js=>y3 fl u b xs i js&&jJ fl u b xs js
theorem z231 {fl u} (k n) (xs:List zl) {q:Nat} (hq:q<xs.length)
   (budget:xs[q].1=k) (arity:xs[q].2.1=n) (mode:xs[q].2.2.2.1.2=u) (nd:(xs[q].2.2.1.map Prod.fst).Nodup)
   (hfl : ∀ tag ys,fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag,ys=zs.map BitVec.toNat)
   (js:List Nat)
   (bounds : ∀ j ∈ js,j<n) (allRows:jJ fl u (zV k n xs) (xs.map qx) js=true) :
   jz xs[q] (js.map (z4 xs[q]))=true:=by
 induction js with
 | nil=>rfl
 | cons i js ih =>
   simp only [jJ,Bool.and_eq_true,y3,List.all_eq_true] at allRows
   simp only [List.map_cons,jz,z178,Bool.and_eq_true,List.all_eq_true,List.mem_map]
   have hi:=bounds i List.mem_cons_self
   refine ⟨?_,ih (fun j hj=>bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
   rintro _ ⟨j,hj,rfl⟩ op hop
   have hj':=bounds j (List.mem_cons_of_mem _ hj)
   rw [mode] at hop
   have pass:=allRows.1 j hj op hop
   have check := @z232 fl u k n xs i j op
   simp only [z173,Bool.and_eq_true] at pass
   simp only [jL,Bool.and_eq_true]
   exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
     check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩
noncomputable def yR (fl:Nat → Option (List Nat)) (u:Bool) (k n:Nat) (xs:List zl) :=
   jJ fl u (zV k n xs) (xs.map qx) (List.range n)
theorem z267 {fl u k n} {xs:List zl} {q} (hq:q<xs.length)
   (hb:xs[q].1=k) (ha:xs[q].2.1=n) (hm:xs[q].2.2.2.1.2=u) (nd:(xs[q].2.2.1.map Prod.fst).Nodup)
   (hfl : ∀ tag ys,fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag,ys=zs.map BitVec.toNat)
   (hn:xs[q].2.2.1.length=n)
   (pass:yR fl u k n xs=true):jz xs[q] xs[q].2.2.1=true:=by
 have all:=z231 k n xs hq hb ha hm nd hfl (List.range n) (fun _=>List.mem_range.mp) pass
 have eq:(List.range n).map (z4 xs[q])=xs[q].2.2.1:=by
   apply List.ext_getElem
   · simp [hn]
   · intro i h1 h2
     simp [z4,List.getD_eq_getElem?_getD,h2]
 rwa [eq] at all
def jF (g:Forest) (k i:Nat):zl :=
 let raw:=jn g
 let (num,depth,cw,iw,pw,offw,lw,data):=g.levels k
 let (ops,bank,ws):=v9 g k i
 let start:=num*(10*j4 g depth+raw.length+depth)
 let pos:=start+num*offw+q5 data (start+i*offw) offw
 let nr:=q5 data pos 5
 let nl:=q5 data (pos+5) lw
 let st:=pos+5+lw
 let rules:=(vR data cw depth nr st).filterMap (fun (a,b)=>jH g ops depth bank a b)
 let ls:=fun tag=>((g.index k tag).bind (qF g (k-1))).toList
 (k,ws.length,ws,jN g.mode ws,rules,ls)
theorem q361 (g:Forest) (k i tag:Nat) (ys) (h:wX g k tag=some ys) :
   ∃ xs ∈ (jF g k i).2.2.2.2.2 tag,ys=xs.map BitVec.toNat:=by
 change ∃ xs ∈ ((g.index k tag).bind (qF g (k-1))).toList,_
 unfold wX at h
 cases hp:g.index k tag with
 | none=>simp [hp] at h
 | some pair =>
   simp only [hp,Option.bind_some,ww] at h
   simp only [Option.bind_some,qF]
   split at h
   · contradiction
   next v =>
     cases ha:g.autos[pair.2]? with
     | none=>simp [ha] at h
     | some perm =>
       simp only [ha,Option.bind_some] at h
       cases hv:perm.all j3 with
       | false=>simp [hv] at h
       | true =>
         simp only [hv,cond_true,Option.some.injEq] at h
         refine ⟨(zY g (k-1) pair.1).map (zj (perm.map qe).reverse),?_,?_⟩
         · simp [v]
         · exact h.symm.trans (wY g _ _ hv)
def prelim (T:Sig) (c:zl) :=
 let ws:=c.2.2.1.map Prod.fst
 decide ws.Nodup && !(ws.contains T)
theorem z221 (g:Forest) (k i:Nat) :
   qN g k i=(prelim (zz g) (jF g k i) &&
     (if k=0 then true else jz (jF g k i) (jF g k i).2.2.1)):=rfl
theorem q173 {g k start n} (h : ∀ (i:Nat),start ≤ i → i < start + n → qN g k i=true) :
   block g k start n=true:=by
 induction n with
 | zero=>rfl
 | succ n ih =>
   simp only [block,Bool.and_eq_true]
   exact ⟨h _ (by omega) (by omega),ih (fun i le lt=>h i le (by omega))⟩
def contexts (g:Forest) (k start n:Nat) :=
 ((List.range n).map (start+·)).map (jF g k)
def header (g:Forest) (k start n ar:Nat) :=
 (contexts g k start n).all (fun c=>c.2.1==ar&&prelim (zz g) c)
noncomputable def v5 (g:Forest) (k start n ar lo len:Nat) :=
 let xs:=contexts g k start n
 let b:=zV k ar xs
 vz xs fun ys=>(List.range len).all (fun d =>
   let i:=lo+d
   y3 (wX g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))
theorem y7 {g k start n ar lo len} (h:v5 g k start n ar lo len=true)
   (i:Nat) (l:lo ≤ i) (r:i < lo+len) :
   y3 (wX g k) g.mode (zV k ar (contexts g k start n)) ((contexts g k start n).map qx)
     i (List.range' (i+1) (ar-(i+1)))=true:=by
 simp only [v5,jq] at h
 have ha:=List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
 simpa only [Nat.add_sub_of_le l] using ha
theorem z213 {g k start n ar lo a b}
   (h:v5 g k start n ar lo a=true) (t:v5 g k start n ar (lo+a) b=true) :
   v5 g k start n ar lo (a+b)=true:=by
 simp only [v5,jq]
 apply List.all_eq_true.mpr
 intro j hj
 have jlt:=List.mem_range.mp hj
 by_cases first:j<a
 · exact y7 h (lo+j) (by omega) (by omega)
 · exact y7 t (lo+j) (by omega) (by omega)
theorem q362 {g k start n ar} (h:v5 g k start n ar 0 ar=true) :
   yR (wX g k) g.mode k ar (contexts g k start n)=true:=by
 let xs:=contexts g k start n
 have go (lo num:Nat) (eq:lo+num=ar) :
     jJ (wX g k) g.mode (zV k ar xs) (xs.map qx) (List.range' lo num)=true:=by
   induction num generalizing lo with
   | zero=>rfl
   | succ num ih =>
     simp only [List.range'_succ,jJ,Bool.and_eq_true]
     refine ⟨?_,ih (lo+1) (by omega)⟩
     have ok:=y7 h lo (by omega) (by omega)
     simpa only [show ar-(lo+1)=num by omega] using ok
 unfold yR
 rw [List.range_eq_range']
 exact go 0 ar (by omega)
theorem q189 {g k start n ar} (hd:header g k start n ar=true)
   (h:v5 g k start n ar 0 ar=true):block g k start n=true:=by
 apply q173
 intro i lo hi
 let xs:=contexts g k start n
 have hm:jF g k i ∈ xs:=by
   apply List.mem_map.mpr
   exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
 obtain ⟨q,hq,e⟩:=List.getElem_of_mem hm
 have one:=List.all_eq_true.mp hd _ hm
 simp only [Bool.and_eq_true,beq_iff_eq] at one
 have hb:xs[q].1=k:=by rw [e]; rfl
 have ha:xs[q].2.1=ar:=e ▸ one.1
 have nd:(xs[q].2.2.1.map Prod.fst).Nodup:=by
   have p:=one.2
   simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
   rw [e]
   exact p.1
 have hfl : ∀ tag ys,wX g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag,ys=zs.map BitVec.toNat:=by
   rw [e]
   exact fun tag ys h=>q361 g k i tag ys h
 have hm:xs[q].2.2.2.1.2=g.mode:=by rw [e]; rfl
 have hn:xs[q].2.2.1.length=ar:=by rw [e]; exact one.1
 rw [z221,Bool.and_eq_true]
 refine ⟨one.2,?_⟩
 split
 · rfl
 · exact e ▸ z267 hq hb ha hm nd hfl hn (q362 h)
def boxes (g:Forest) (k start n ar lo num:Nat):Nat → Prop
 | 0=>v5 g k start n ar lo num=true
 | d+1=>boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem q299 {g k start n ar lo num d} (h:boxes g k start n ar lo num d) :
   v5 g k start n ar lo num=true:=by
 induction d generalizing lo num with
 | zero=>exact h
 | succ d ih =>
   have v:=z213 (ih h.1) (ih h.2)
   simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
def cells (g:Forest) (k start n ar rows:Nat):Nat → Prop
 | 0=>header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
 | d+1=>cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem z7 {g k start n ar rows d} (h:cells g k start n ar rows d) :
   block g k start n=true:=by
 induction d generalizing start n with
 | zero=>exact q189 h.1 (q299 h.2)
 | succ d ih =>
   have v:=zn (ih h.1) (ih h.2)
   simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
def zQ {α} (f : α → Bool) (xs:List α):Nat → Prop
 | 0=>xs.all f=true
 | d+1=>zQ f (xs.take (xs.length/2)) d ∧ zQ f (xs.drop (xs.length/2)) d
theorem zh {α f xs d} (h : @zQ α f xs d):xs.all f=true:=by
 induction d generalizing xs with
 | zero=>exact h
 | succ d ih =>
   have ap:((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true:=by
     simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
   simpa only [List.take_append_drop] using ap
theorem z357 {u} {raw:List Sig} {T:Sig} {L:Nat} (pT:proper T) (h:Lower u raw T L) :
   Slice u raw T one L:=by
 refine ⟨id,raw,fun r=>qP r,fun a ha=>?_,jP pT,h⟩
 exact Or.inl (List.mem_map_of_mem ha)
theorem vN {u} {m q cap:Nat} {prior:Nat → Nat} (low : ∀ q,Lower u (zq q) (z1 q) (prior q))
   (e:(z1 q == z1 m&&(zq q == vars m)&&(prior q == cap+1)&&qa (z1 m) &&
     decide (vars m).Nodup&&yA u one (cap+1) cap 0 (vars m) (vars m))=true) :
   Impossible u (z1 m) cap (vars m).toFinset:=by
 simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at e
 obtain ⟨⟨⟨⟨⟨e1,e2⟩,e3⟩,e4⟩,e5⟩,e6⟩:=e
 have h:=low q
 rw [e1,e2,e3] at h
 exact wf (z357 (qM _ e4) h) [] rfl e5 e6
theorem zW {u} {m cap:Nat} {prior:Nat → Nat} {ws:List Sig}
   (low : ∀ q,Lower u (zq q) (z1 q) (prior q)) (ci:zK)
   (ok:vl m ci prior=true)
   (cut:(decide ws.Nodup&&yA u (subcube ci.1 ci.2.1) ci.2.2.2.2 cap 0 (zq (jX m ci)) ws)=true) :
   Impossible u (z1 m) cap ws.toFinset:=by
 simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
 exact wf (vk ci prior low ok) [] rfl cut.1 cut.2
theorem zu {u} {g:Forest} {m cap i:Nat} {prior:Nat → Nat} {ws:List Sig}
   (hm:g.mask=m) (hu:g.mode=u) (low : ∀ q,Lower u (zq q) (z1 q) (prior q))
   (geom:zp g prior=true) (blocks:zD g cap)
   (idx:j5 g cap i ws=true):Impossible u (z1 m) cap ws.toFinset:=by
 subst hm
 subst hu
 exact z362 low geom blocks (Nat.le_refl _) idx
def q123 (m hints:Nat):Bool :=
 let xs:=z375 m hints
 qa (z1 m)&&q0 (z1 m) (vars m) xs&&(xs.map Prod.fst == vars m)
theorem qn {u} {m hints cap:Nat} (ok:q123 m hints=true)
   (a:Impossible u (z1 m) cap (vars m).toFinset):Lower u (vars m) (z1 m) (cap+1):=by
 simp only [q123,Bool.and_eq_true,beq_iff_eq] at ok
 apply y9 (qM _ ok.1.1) (q3 ok.1.2).1 (q3 ok.1.2).2 _ a
 intro v hv
 apply jd ok.1.2 v
 rw [ok.2]
 exact List.mem_toFinset.mpr hv
def q256 (m:Nat) (rs:List Nat):List (Sig × Row × Row) :=
 ((selected m).zip rs).map fun x=>(x.1.2,Fin.ofNat 512 x.2,Fin.ofNat 512 (x.2 ||| (1 <<< x.1.1)))
def z220 (m:Nat) (rs:List Nat):Bool :=
 let xs:=q256 m rs
 q0 (z1 m) (zq m) xs&&(xs.map Prod.fst == vars m) &&
   qa (z1 m)&&decide (zq m=vars m ++ [wD (m/512-1)])
theorem z383 {u} {m:Nat} {rs:List Nat} (ok:z220 m rs=true) {k:Nat} {S:Finset Sig}
   (h:Live u (z1 m) k S) (sub : ∀ v ∈ S,v ∈ zq m) :
   S=(vars m).toFinset ∨ S=(zq m).toFinset:=by
 simp only [z220,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
 obtain ⟨⟨⟨ess,alls⟩,_⟩,hX⟩:=ok
 have rest : ∀ v ∈ vars m,v ∈ S:=by
   intro v hv
   rw [←alls] at hv
   obtain ⟨r,s,hd,hi⟩:=jd ess v (List.mem_toFinset.mpr hv)
   exact j8 h (zq m) v sub r s hd hi
 have mem : ∀ v,v ∈ zq m ↔ v ∈ vars m ∨ v=wD (m/512-1):=by
   intro v; rw [hX]; simp
 by_cases hs:wD (m/512-1) ∈ S
 · refine Or.inr ?_
   ext v
   rw [List.mem_toFinset]
   refine ⟨sub v,fun hv=>?_⟩
   rcases (mem v).mp hv with hv | rfl
   · exact rest v hv
   · exact hs
 · refine Or.inl ?_
   ext v
   rw [List.mem_toFinset]
   refine ⟨fun hv=>?_,rest v⟩
   rcases (mem v).mp (sub v hv) with hv | rfl
   · exact hv
   · exact absurd hv hs
theorem zi {u} {m q cap:Nat} {rs:List Nat} (ok:z220 m rs=true)
   (e:z1 m=z1 q) (ev:vars m=vars q)
   (a:Impossible u (z1 q) cap (vars q).toFinset)
   (b:Impossible u (z1 q) cap (zq m).toFinset) :
   Lower u (zq m) (z1 m) (cap+1):=by
 have ok':=ok
 simp only [z220,Bool.and_eq_true] at ok'
 intro p bank hr ha
 obtain ⟨k,S,hk,run,hs⟩:=vt (qM _ ok'.1.2) (q3 ok'.1.1.1).1 (q3 ok'.1.1.1).2 hr ha
 by_contra! small
 rcases z383 ok run hs with h | h
 · rw [ev] at h; rw [e,h] at run; exact a k (by omega) run
 · rw [e,h] at run; exact b k (by omega) run
def j166 (i:Nat):Nat:=0xf
def j165:Packing:=(1,0,1,0,0,0,0,j166)
def z380:Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe47473,0x173652),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe97a7f,0x8c829),(0x1f8f9c,0x21714),(0x168de0,0x1de8e0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def z381:List zK:=[]
def q296:List (List Nat):=[[],[48,33]]
def q183:Nat → Packing
 | 3=>j165
 | _=>zP
def q295:Nat → Nat → Option (Nat × Nat)
 | _=>fun _=>none
def g15:Forest := ⟨15,3,fun j=>z380[j]?.getD (0,0),z381,q296,q183,q295⟩
set_option maxHeartbeats 0 in
theorem q357:zp g15 (z9 [])=true:=by
 simp only [zp,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,zh (d:=0) ?_⟩,zh (d:=0) ?_⟩
 all_goals simp only [zQ]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q259:block g15 3 0 1=true:=by
 apply z7 (ar:=4) (rows:=0) (d:=0)
 simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
 repeat' apply And.intro
 all_goals decide +kernel
theorem q311:block g15 3 0 1=true:=q259
theorem q156:zD g15 3:=by
 intro k hk
 interval_cases k
 · exact (rfl:block g15 0 0 0=true)
 · exact (rfl:block g15 1 0 0=true)
 · exact (rfl:block g15 2 0 0=true)
 · exact q311
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j155:Lower true (vars 15) (z1 15) 4:=qn (hints:=8449) (by decide +kernel) (zu (g:=g15) (i:=0) rfl rfl (z5 [] z175) q357 q156 (by decide +kernel))
def unitMask:Sig:=0x10000000000000000000000000000000100000000000000010000000100010116
def maskForbid4:Sig:=0x2000000000000000000000000000000220000000000000302000000000000070200000100000003220000050000000722
def maskForbid6:Sig:=0x50007000000000000000000000000001500370000000000000000000000000004040400000000000000000004040400040404
def maskForbid7:Sig:=0x1000300000000000000000000000000000000000110111001000300015051500100030
def zI (v:Nat):Sig :=
 if v == 4 then maskForbid4 else if v == 6 then maskForbid6 else if v == 7 then maskForbid7 else zero
def in4:Sig:=inputs.getD 4 zero
def in6:Sig:=inputs.getD 6 zero
def in7:Sig:=inputs.getD 7 zero
def qH (a:Sig):Bool:=(a == in4)||(a == in6)||(a == in7)
def zr (a:Sig):Sig :=
 if a == in4 then maskForbid4 else if a == in6 then maskForbid6 else if a == in7 then maskForbid7 else zero
def qZ (a:Sig):Bool:=inputs.contains a
def q7 (u:Bool) (v other:Sig) (op:Nat) (kv:Bool):Bool :=
 if qH v then
   (!kv) &&
     (if u then ((op == 1)&&((other &&& zr v) == zero))||((op == 3)&&((other &&& zr v) == zr v))
      else (op == 1)&&(!qZ other)&&((other &&& unitMask) == zero)&&((other &&& zr v) == zero))
 else true
def zy (u:Bool) (a b:Sig) (op:Nat) (ka kb:Bool):Bool :=
 q7 u a b op ka&&q7 u b a (qm op) kb
theorem y6 (u:Bool) (a b:Sig) (op:Nat) (ka kb:Bool) (hd:allowed u op) :
   zy u a b op ka kb=zy u b a (qm op) kb ka:=by
 simp only [zy,(yb hd).2,Bool.and_comm]
def q355:Nat:=in4.toNat
def q354:Nat:=in6.toNat
def q353:Nat:=in7.toNat
def z144:Nat:=unitMask.toNat
def wO:Nat:=maskForbid4.toNat
def wN:Nat:=maskForbid6.toNat
def wM:Nat:=maskForbid7.toNat
def z219:List Nat:=inputs.map BitVec.toNat
def z374 (a:Nat):Bool:=Nat.beq a q355||Nat.beq a q354||Nat.beq a q353
def vf (a:Nat):Nat :=
 if Nat.beq a q355 then wO else if Nat.beq a q354 then wN else if Nat.beq a q353 then wM else 0
noncomputable def vv (u:Bool) (v other op:Nat) (kv:Bool):Bool :=
 if z374 v then
   (!kv) &&
     (if u then (Nat.beq op 1&&Nat.beq (Nat.land other (vf v)) 0) ||
                (Nat.beq op 3&&Nat.beq (Nat.land other (vf v)) (vf v))
      else Nat.beq op 1&&(!vH other z219) &&
             Nat.beq (Nat.land other z144) 0&&Nat.beq (Nat.land other (vf v)) 0)
 else true
noncomputable def v8 (u:Bool) (a b op:Nat) (ka kb:Bool):Bool :=
 vv u a b op ka&&vv u b a (qm op) kb
theorem q176 (a:Sig):z374 a.toNat=qH a:=by
 simp only [z374,qH,q355,q354,q353,jl]
theorem z274 (a:Sig):vf a.toNat=(zr a).toNat:=by
 have z0:(0:Nat)=zero.toNat:=by simp [zero]
 simp only [vf,zr,q355,q354,q353,wO,wN,wM,jl]
 cases (a == in4)<;>cases (a == in6)<;>cases (a == in7)<;>simp [z0]
theorem z142 (x:Sig):vH x.toNat z219=qZ x:=by
 rw [Bool.eq_iff_iff,z176,z219,List.mem_map]
 simp only [qZ,List.contains_eq_mem,decide_eq_true_eq]
 exact ⟨fun ⟨y,hy,he⟩ => BitVec.toNat_inj.mp he ▸ hy,fun hx => ⟨x,hx,rfl⟩⟩
theorem z133 (u:Bool) (a b:Sig) (op:Nat) (k:Bool) :
   vv u a.toNat b.toNat op k=q7 u a b op k:=by
 have tn (x y:Sig):Nat.land x.toNat y.toNat=(x &&& y).toNat:=(BitVec.toNat_and x y).symm
 have hb0 (x:Sig):Nat.beq x.toNat 0=(x == zero):=by
   have z0:(0:Nat)=zero.toNat:=by simp [zero]
   rw [z0,jl]
 have h1:Nat.beq op 1=(op == 1):=by rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
 have h3:Nat.beq op 3=(op == 3):=by rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
 simp only [vv,q7,q176,z142,z274,z144,tn,hb0,jl,h1,h3]
theorem yk (u:Bool) (a b:Sig) (op:Nat) (ka kb:Bool) :
   v8 u a.toNat b.toNat op ka kb=zy u a b op ka kb:=by
 simp only [v8,zy,z133]
theorem inputs_nodup:inputs.Nodup:=by decide +kernel
theorem z119:in4 ≠ in6:=by decide +kernel
theorem z118:in4 ≠ in7:=by decide +kernel
theorem z117:in6 ≠ in7:=by decide +kernel
theorem q172:zr in4=zI 4:=by decide +kernel
theorem q171:zr in6=zI 6:=by decide +kernel
theorem q170:zr in7=zI 7:=by decide +kernel
theorem wh : ∀ v:Fin 9,v ∈ ([4,6,7]:List (Fin 9)) →
   zr (inputs.getD v.val zero)=zI v.val:=by decide +kernel
theorem yw : ∀ u:Fin 9,bit (Fin.ofNat 512 (1 <<< u.val)) (inputs.getD u.val zero)=true:=by decide +kernel
theorem z229 : ∀ u:Fin 9,bit (Fin.ofNat 512 (1 <<< u.val)) unitMask=true:=by decide +kernel
theorem yh : ∀ r:Row,bit r unitMask=(List.finRange 9).any (fun j=>decide (r.val=1 <<< j.val)):=by decide +kernel
theorem vp : ∀ (r:Row) (v:Fin 9),r.val ^^^ (1 <<< v.val) < 512:=by decide +kernel
theorem yN : ∀ (r:Row) (t v:Fin 9),t ≠ v →
   (r.val ^^^ (1 <<< v.val)).testBit t.val=r.val.testBit t.val:=by
 intro r t v hne
 have hlt:t.val ≠ v.val:=Fin.val_ne_of_ne hne
 rw [Nat.testBit_xor,Nat.shiftLeft_eq,Nat.one_mul,Nat.testBit_two_pow]
 simp [hlt,Eq.comm]
theorem j2 : ∀ v:Fin 9,∃ r:Row,bit r graph ≠ bit r (inputs.getD v.val zero):=by decide +kernel
theorem y1 : ∀ v ∈ ([4,6,7]:List (Fin 9)),∀ r:Row,
   bit r (zI v.val)=true →
   sample r v=false ∧ bit r graph=false ∧
     bit (Fin.ofNat 512 (r.val ^^^ (1 <<< v.val))) graph=true:=by decide +kernel
set_option maxRecDepth 8192 in
theorem wb : ∀ v ∈ ([4,6,7]:List (Fin 9)),∀ u:Fin 9,u ≠ v →
   ∃ r:Row,bit r (zI v.val)=true ∧ (r.val &&& (1 <<< u.val))=(1 <<< u.val):=by decide +kernel
def wK (u:Bool) (U:Finset Sig) (a b:Sig) (d:Nat):Prop :=
 zy u a b d (decide (a ∈ U)) (decide (b ∈ U))=true
def Live467 (u:Bool) (target:Sig):Nat → Finset Sig → Prop
 | 0,S=>S = {target} ∧ proper target
 | k + 1,S => ∃ (U:Finset Sig) (a b:Sig) (d:Nat),allowed u d ∧
     wK u U a b d ∧ S=insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
     bin d a b ∉ insert a (insert b U) ∧ Live467 u target k (insert (bin d a b) U)
theorem Live467.stop {u} {target:Sig} (hp:proper target):Live467 u target 0 {target} := ⟨rfl,hp⟩
theorem Live467.binary {u} {target:Sig} {k:Nat} {U:Finset Sig} {a b:Sig} {d:Nat}
   (hd:allowed u d) (hok:wK u U a b d) (ha:proper a) (hb:proper b) (hab:a ≠ b)
   (hfresh:bin d a b ∉ insert a (insert b U)) (tail:Live467 u target k (insert (bin d a b) U)) :
   Live467 u target (k + 1) (insert a (insert b U)) :=
 ⟨U,a,b,d,hd,hok,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live467.ind {u} {target:Sig} {motive : ∀ (k:Nat) (S:Finset Sig),Live467 u target k S → Prop}
   (stop : ∀ (hp:proper target),motive 0 {target} (Live467.stop hp))
   (binary : ∀ {k:Nat} {U:Finset Sig} {a b:Sig} {d:Nat} (hd:allowed u d)
     (hok:wK u U a b d) (ha:proper a) (hb:proper b) (hab:a ≠ b)
     (hfresh:bin d a b ∉ insert a (insert b U)) (tail:Live467 u target k (insert (bin d a b) U)),
     motive k (insert (bin d a b) U) tail →
     motive (k + 1) (insert a (insert b U)) (Live467.binary hd hok ha hb hab hfresh tail))
   {k:Nat} {S:Finset Sig} (h:Live467 u target k S):motive k S h:=by
 induction k generalizing S with
 | zero =>
   obtain ⟨rfl,hp⟩:=h
   exact stop hp
 | succ k ih =>
   obtain ⟨U,a,b,d,hd,hok,rfl,ha,hb,hab,hf,tail⟩:=h
   exact binary hd hok ha hb hab hf tail (ih tail)
theorem q2 {u target k S} (h:Live467 u target k S):Live u target k S:=by
 induction h using Live467.ind with
 | stop hp=>exact Live.stop hp
 | binary hd _ ha hb hab hf _ ih=>exact Live.binary hd ha hb hab hf ih
def zo (u:Bool) (T:Sig) (cap:Nat) (S:Finset Sig):Prop :=
 ∀ k,k ≤ cap → ¬Live467 u T k S
theorem z136 {u T cap S} (h:Impossible u T cap S):zo u T cap S :=
 fun k hk hl=>h k hk (q2 hl)
def vm (T:Sig) (p:List Move):Bool :=
 wA T p &&
 inputs.all (fun a=>inputs.contains (zj p a)) &&
 (zj p unitMask == unitMask) &&
 ([4,6,7]:List Nat).all fun v =>
   let y:=zj p (inputs.getD v zero)
   qH y&&(zj p (zI v) == zr y)
theorem yZ {u T k S} (h:Live467 u T k S) (f:Row → Row) (onto:Function.Surjective f)
   (hin : ∀ a ∈ inputs,rename f a ∈ inputs)
   (hu:rename f unitMask=unitMask)
   (h4:qH (rename f in4)=true ∧ rename f maskForbid4=zr (rename f in4))
   (h6:qH (rename f in6)=true ∧ rename f maskForbid6=zr (rename f in6))
   (h7:qH (rename f in7)=true ∧ rename f maskForbid7=zr (rename f in7)) :
   Live467 u (rename f T) k (S.image (rename f)):=by
 have inj:=yS f onto
 obtain ⟨fz,fo⟩:=jh f
 have pp (v) (p:proper v):proper (rename f v) :=
   ⟨fun e=>p.1 (inj (e.trans fz.symm)),fun e=>p.2 (inj (e.trans fo.symm))⟩
 have hraw : ∀ x,qZ (rename f x)=qZ x:=by
   have hsub:(inputs.map (rename f)).toFinset ⊆ inputs.toFinset:=by
     intro y hy
     rw [List.mem_toFinset,List.mem_map] at hy
     obtain ⟨a,ha,rfl⟩:=hy
     exact List.mem_toFinset.mpr (hin a ha)
   have hnd:(inputs.map (rename f)).Nodup:=inputs_nodup.map inj
   have heq:(inputs.map (rename f)).toFinset=inputs.toFinset:=by
     apply Finset.eq_of_subset_of_card_le hsub
     rw [List.toFinset_card_of_nodup hnd,List.toFinset_card_of_nodup inputs_nodup,List.length_map]
   intro x
   apply Bool.eq_iff_iff.mpr
   simp only [qZ,List.contains_eq_mem,decide_eq_true_eq]
   constructor
   · intro hx
     have hm:rename f x ∈ (inputs.map (rename f)).toFinset:=by rw [heq]; exact List.mem_toFinset.mpr hx
     rw [List.mem_toFinset,List.mem_map] at hm
     obtain ⟨a,ha,e⟩:=hm
     exact inj e ▸ ha
   · intro hx
     exact hin x hx
 let g3:Fin 3 → Sig:=fun
   | 0=>in4
   | 1=>in6
   | _=>in7
 have hg3_inj:Function.Injective g3:=by
   intro i j hij
   fin_cases i<;>fin_cases j<;>dsimp [g3] at hij
   · rfl
   · exact False.elim (z119 hij)
   · exact False.elim (z118 hij)
   · exact False.elim (z119 hij.symm)
   · rfl
   · exact False.elim (z117 hij)
   · exact False.elim (z118 hij.symm)
   · exact False.elim (z117 hij.symm)
   · rfl
 have hm_iff (y:Sig):qH y=true ↔ ∃ k:Fin 3,g3 k=y:=by
   simp only [qH,Bool.or_eq_true,beq_iff_eq]
   constructor
   · rintro ((rfl | rfl) | rfl)
     · exact ⟨0,rfl⟩
     · exact ⟨1,rfl⟩
     · exact ⟨2,rfl⟩
   · rintro ⟨k,rfl⟩
     fin_cases k<;>simp [g3]
 have hex_phi (k:Fin 3) : ∃ j:Fin 3,g3 j=rename f (g3 k):=by
   apply (hm_iff _).mp
   fin_cases k
   · exact h4.1
   · exact h6.1
   · exact h7.1
 choose φ hφ using hex_phi
 have hφ_inj:Function.Injective φ:=fun i j e =>
   hg3_inj (inj (by rw [← hφ i,← hφ j,e]))
 have hφ_surj:Function.Surjective φ:=Finite.injective_iff_surjective.mp hφ_inj
 have his467 : ∀ x,qH (rename f x)=qH x:=by
   intro x
   apply Bool.eq_iff_iff.mpr
   rw [hm_iff,hm_iff]
   constructor
   · rintro ⟨j,hj⟩
     obtain ⟨k,rfl⟩:=hφ_surj j
     exact ⟨k,inj ((hφ k).symm.trans hj)⟩
   · rintro ⟨k,rfl⟩
     exact ⟨φ k,hφ k⟩
 have hmask : ∀ x,qH x=true → rename f (zr x)=zr (rename f x):=by
   intro x hx
   simp only [qH,Bool.or_eq_true,beq_iff_eq] at hx
   rcases hx with (rfl | rfl) | rfl
   · rw [q172,show zI 4=maskForbid4 by rfl,h4.2]
   · rw [q171,show zI 6=maskForbid6 by rfl,h6.2]
   · rw [q170,show zI 7=maskForbid7 by rfl,h7.2]
 have hside (a b:Sig) (op:Nat) (k:Bool):q7 u (rename f a) (rename f b) op k=q7 u a b op k:=by
   simp only [q7,his467]
   by_cases ha:qH a=true
   · simp only [ha,if_true,hraw]
     have eu:((rename f b &&& unitMask) == zero)=((b &&& unitMask) == zero):=by
       conv_lhs=>rw [← hu,show rename f b &&& rename f unitMask=rename f (b &&& unitMask) from (ji f 0 b unitMask).symm,← fz]
       simp [beq_iff_eq,inj.eq_iff]
     have em:((rename f b &&& zr (rename f a)) == zero)=((b &&& zr a) == zero):=by
       conv_lhs=>rw [← hmask a ha,show rename f b &&& rename f (zr a)=rename f (b &&& zr a) from (ji f 0 b (zr a)).symm,← fz]
       simp [beq_iff_eq,inj.eq_iff]
     have emm:((rename f b &&& zr (rename f a)) == zr (rename f a))=((b &&& zr a) == zr a):=by
       conv_lhs=>rw [← hmask a ha,show rename f b &&& rename f (zr a)=rename f (b &&& zr a) from (ji f 0 b (zr a)).symm]
       simp [beq_iff_eq,inj.eq_iff]
     cases u<;>simp [eu,em,emm]
   · simp [ha]
 induction h using Live467.ind with
 | stop hp=>simpa using Live467.stop (pp _ hp)
 | @binary k U a b d hd hok ha hb hab hf _ ih =>
   have fresh:rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f):=by
     intro hm
     obtain ⟨v,hv,eq⟩:=Finset.mem_image.mp hm
     exact hf (inj eq ▸ hv)
   have hok' : wK u (U.image (rename f)) (rename f a) (rename f b) d:=by
     simp only [wK,zy,Finset.mem_image,inj.eq_iff,exists_eq_right,hside] at hok ⊢
     exact hok
   simp only [Finset.image_insert,ji] at fresh ih ⊢
   exact Live467.binary hd hok' (pp _ ha) (pp _ hb) (fun hh=>hab (inj hh)) fresh ih
theorem wr {u T n} {ws:List Sig} (hi:zo u T n ws.toFinset)
   (p:List Move) (ok:vm T p=true):zo u T n (ws.map (zj p.reverse)).toFinset:=by
 simp only [vm,wA,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,List.mem_cons,
   List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] at ok
 obtain ⟨⟨⟨⟨⟨ht,hc1⟩,hc2⟩,hin⟩,hu⟩,h4,h6,h7⟩:=ok
 have onto:Function.Surjective (zA p):=fun r => ⟨zA p.reverse r,v1 hc2 r⟩
 have hin' : ∀ a ∈ inputs,rename (zA p) a ∈ inputs:=fun a ha=>by
   have h:=hin a ha
   simp only [List.contains_eq_mem,decide_eq_true_eq] at h
   exact (zt p a) ▸ h
 have hu' : rename (zA p) unitMask=unitMask:=(zt p unitMask).symm.trans hu
 have hf4:qH (rename (zA p) in4)=true ∧ rename (zA p) maskForbid4=zr (rename (zA p) in4):=by
   have h4' : qH (zj p in4)=true ∧ zj p maskForbid4=zr (zj p in4):=h4
   rw [zt,zt] at h4'
   exact h4'
 have hf6:qH (rename (zA p) in6)=true ∧ rename (zA p) maskForbid6=zr (rename (zA p) in6):=by
   have h6' : qH (zj p in6)=true ∧ zj p maskForbid6=zr (zj p in6):=h6
   rw [zt,zt] at h6'
   exact h6'
 have hf7:qH (rename (zA p) in7)=true ∧ rename (zA p) maskForbid7=zr (rename (zA p) in7):=by
   have h7' : qH (zj p in7)=true ∧ zj p maskForbid7=zr (zj p in7):=h7
   rw [zt,zt] at h7'
   exact h7'
 intro k hk h
 have run:=yZ h (zA p) onto hin' hu' hf4 hf6 hf7
 have goal:rename (zA p) T=T:=(zt p T).symm.trans ht
 have inv (x:Sig):rename (zA p) (zj p.reverse x)=x:=by
   apply BitVec.eq_of_getLsbD_eq
   intro j hj
   change bit ⟨j,hj⟩ _=bit ⟨j,hj⟩ _
   rw [qA,jI,v1 hc1]
 have back:(ws.map (zj p.reverse)).toFinset.image (rename (zA p))=ws.toFinset:=by
   ext a
   simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
   constructor
   · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
     simpa only [inv] using hw
   · intro ha
     exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
 rw [goal,back] at run
 exact hi k hk run
theorem z225 {u:Bool} {T:Sig} {cap:Nat} {ws:List Sig} (hn:ws.Nodup) (out:T ∉ ws)
   (twoStep : ∀ a ∈ ws,∀ b ∈ ws,∀ d,allowed u d → ∀ ka kb,a ≠ b → bin d a b ∉ ws →
     proper (bin d a b) → (q6 ws a b d ka kb).length ≤ cap →
     zy u a b d ka kb=true →
     zo u T (cap - 1) (q6 ws a b d ka kb).toFinset) :
   zo u T cap ws.toFinset:=by
 classical
 intro k hk h
 generalize he:ws.toFinset=S at h
 induction h using Live467.ind with
 | stop hp =>
   have mem:T ∈ ws.toFinset:=he.symm ▸ Finset.mem_singleton_self _
   exact out (List.mem_toFinset.mp mem)
 | @binary k U a b d hd hok ha hb hab hf tail _ =>
   have am:a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
   have bm:b ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
   have fresh:bin d a b ∉ ws:=fun h=>hf (he ▸ List.mem_toFinset.mpr h)
   have hz:=jZ (q2 tail) _ (Finset.mem_insert_self _ _)
   let ka:=decide (a ∈ U)
   let kb:=decide (b ∈ U)
   let rest:=(ws.erase a).erase b
   have er:rest.toFinset=(ws.toFinset.erase a).erase b:=by
     rw [show rest=(ws.erase a).erase b by rfl,w7 (hn.erase _) b,w7 hn a]
   have ke:(kept ka a (kept kb b rest)).toFinset=U:=by
     rw [vi,vi,er,he]
     ext j
     by_cases aa:a ∈ U<;>by_cases bb:b ∈ U<;>by_cases ja:j=a <;>
       by_cases jb:j=b<;>simp_all [ka,kb]
   have rn:rest.Nodup:=(hn.erase _).erase _
   have ar:a ∉ rest:=fun h=>hn.not_mem_erase (List.mem_of_mem_erase h)
   have br:b ∉ rest:=(hn.erase a).not_mem_erase
   have nk:=w5 kb b rest rn br
   have ax:a ∉ kept kb b rest:=by cases kb<;>simp [kept,ar,hab]
   have nd:(q6 ws a b d ka kb).Nodup:=by
     refine List.nodup_cons.mpr ⟨?_,w5 ka a _ nk ax⟩
     intro h
     exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
   have eq:(q6 ws a b d ka kb).toFinset=insert (bin d a b) U:=by
     change (bin d a b :: kept ka a (kept kb b rest)).toFinset=_
     simp [ke]
   have sc:=vg (q2 tail)
   have len:(q6 ws a b d ka kb).length ≤ cap:=by
     rw [← List.toFinset_card_of_nodup nd,eq]
     omega
   exact twoStep a am b bm d hd ka kb hab fresh hz len hok k (by omega) (eq.symm ▸ tail)
theorem wc {u raw T pools links k rest op}
   (pValid : ∀ p ∈ pools,qq u raw T p)
   (lValid : ∀ tag xs,xs ∈ links tag → zo u T k (List.toFinset xs))
   (nd:(zE op :: rest).Nodup)
   (h:qy u pools links k rest op=true) :
   zo u T k (zE op :: rest).toFinset:=by
 simp only [qy,Bool.or_eq_true,List.any_eq_true] at h
 rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
 · rw [qU ok]
   exact lValid _ _ hx
 · exact z136 (jw (pValid _ hp) nd ok)
def qg (c:zl) (op:Nat) (a b z:Decor) (ka kb:Bool) :=
 if !zy c.2.2.2.1.2 a.1 b.1 op ka kb then true else qC c op a b z ka kb
theorem y0 {u raw T r s ws pools links cap a b op ka kb}
   (pairs:qr T r s) (faith : ∀ w ∈ ws,faithful r s w)
   (nd:(ws.map Prod.fst).Nodup) (ha:a ∈ ws) (hb:b ∈ ws)
   (ne:a ≠ b) (hcap:0 < cap)
   (pv : ∀ p ∈ pools,qq u raw T p)
   (lv : ∀ tag xs,xs ∈ links tag → zo u T (cap - 1) (List.toFinset xs))
   (pro:proper (dbin op a b).1) (fresh:(dbin op a b).1 ∉ ws.map Prod.fst)
   (hok:zy u a.1 b.1 op ka kb=true)
   (test:qg (cap,ws.length,ws,jN u ws,pools,links) op a b (dbin op a b) ka kb=true) :
   zo u T (cap - 1) (w3 ws op a b ka kb).toFinset:=by
 rw [qg] at test
 change (if !zy u a.1 b.1 op ka kb then true else qC (cap,ws.length,ws,jN u ws,pools,links) op a b (dbin op a b) ka kb)=true at test
 rw [if_neg (by simp [hok])] at test
 let z:=dbin op a b
 let rest:=q8 ws a b ka kb
 let child:=z.1 :: rest.map Prod.fst
 have sub:rest.Sublist ws:=z279 _ _ _ _ _
 have ndc:child.Nodup:=List.nodup_cons.mpr ⟨fun hm=>fresh ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
 have fr:ws.any (fun v=>v.1 == z.1)=false:=by
   apply Bool.eq_false_iff.mpr
   intro hh
   obtain ⟨x,hx,he⟩:=List.any_eq_true.mp hh
   exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
 have pp:qa z.1=true:=by simpa [qa,proper] using pro
 have leq:1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1))=child.length:=by
   change _=(z.1 :: rest.map Prod.fst).length
   rw [List.length_cons,List.length_map,z278 _ _ _ _ _ ha hb ne,Nat.add_comm 1]
 intro k hk h
 have hsz:=vg (q2 h)
 change child.toFinset.card ≤ k + 1 at hsz
 rw [List.toFinset_card_of_nodup ndc] at hsz
 have len:child.length ≤ cap:=by omega
 unfold qC at test
 change (if 1 + (ws.length - _ - _) > cap then true else _)=true at test
 rw [leq,if_neg (by omega)] at test
 have sep:=vW (q2 h) (z269 pairs)
 let d := !u
 have g:(coverage d rest).1=covered d (qG r s) (rest.map Prod.fst) :=
   z294 _ _ (fun v hv=>faith _ (sub.subset hv))
 have rz:(coverage d rest).1=jo (coverage d ws) (column d a.2) (column d b.2) ka kb :=
   z171 d a b ha hb ne ka kb
 have hf:=vA op (faith _ ha) (faith _ hb)
 change column d (qG r s z.1) ||| covered d (qG r s) (rest.map Prod.fst)=_ at sep
 change z.2=qG r s z.1 at hf
 rw [← hf,← g,rz,BitVec.or_comm] at sep
 dsimp only [d] at sep
 have be:((jo (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 768)=false:=by
   simp only [sep,bne_self_eq_false]
 change (if (jo (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 768 then true else if !qa z.1||ws.any (fun v=>v.1 == z.1) then true else _)=true at test
 rw [be,pp,fr] at test
 exact wc (op:=zT op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h
def qI (ctx:zl) (a b:Decor) (op:Nat) :=
 let z:=dbin op a b
 let attempt:=qg ctx op a b z
 attempt false false&&attempt true false&&attempt false true&&attempt true true
def wq (ctx:zl) (a:Decor) (bs:List Decor) :=
 bs.all (fun b=>(wJ ctx.2.2.2.1.2).all (qI ctx a b))
def qu (ctx:zl):List Decor → Bool
 | []=>true
 | a :: bs=>wq ctx a bs&&qu ctx bs
theorem z143 {ctx ws} (h:qu ctx ws=true) {a b:Decor} (ha:a ∈ ws) (hb:b ∈ ws)
   (ne:a ≠ b):(∀ d,allowed ctx.2.2.2.1.2 d → qI ctx a b d=true) ∨
     (∀ d,allowed ctx.2.2.2.1.2 d → qI ctx b a d=true):=by
 induction ws with
 | nil=>simp at ha
 | cons w ws ih =>
   simp only [qu,Bool.and_eq_true,wq,List.all_eq_true] at h
   rcases List.mem_cons.mp ha with rfl | haTail
   · have bm:=(List.mem_cons.mp hb).resolve_left (Ne.symm ne)
     exact Or.inl fun d hd=>h.1 b bm d (w0 hd)
   · rcases List.mem_cons.mp hb with rfl | hbTail
     · exact Or.inr fun d hd=>h.1 a haTail d (w0 hd)
     · exact ih h.2 haTail hbTail
theorem yM {ctx a b d} (h:qI ctx a b d=true) (ka kb:Bool) :
   qg ctx d a b (dbin d a b) ka kb=true:=by
 simp only [qI,Bool.and_eq_true] at h
 cases ka<;>cases kb<;>first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
theorem z135 {u raw T r s ws pools links cap}
   (pairs:qr T r s) (faith : ∀ w ∈ ws,faithful r s w)
   (nd:(ws.map Prod.fst).Nodup) (out:T ∉ ws.map Prod.fst)
   (pv : ∀ p ∈ pools,qq u raw T p)
   (lv : ∀ tag xs,xs ∈ links tag → zo u T (cap - 1) (List.toFinset xs))
   (checks:qu (cap,ws.length,ws,jN u ws,pools,links) ws=true) :
   zo u T cap (ws.map Prod.fst).toFinset:=by
 by_cases hc:cap=0
 · intro k hk h
   have ke:k=0:=by omega
   subst k
   generalize he:(ws.map Prod.fst).toFinset=S at h
   obtain ⟨hS,_⟩:=h
   exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
 have hc' : 0 < cap:=by omega
 apply z225 nd out
 intro a ha b hb d hd ka kb ne fresh pro len hok
 obtain ⟨a,haW,rfl⟩:=List.mem_map.mp ha
 obtain ⟨b,hbW,rfl⟩:=List.mem_map.mp hb
 have ab:a ≠ b:=fun e=>ne (congrArg Prod.fst e)
 have one (a b:Decor) (d:Nat) (aa:a ∈ ws) (bb:b ∈ ws) (ne' : a.1 ≠ b.1) (ka kb:Bool)
     (pr:proper (bin d a.1 b.1)) (fr:bin d a.1 b.1 ∉ ws.map Prod.fst)
     (hok' : zy u a.1 b.1 d ka kb=true)
     (test:qI (cap,ws.length,ws,jN u ws,pools,links) a b d=true) :
     zo u T (cap - 1) (q6 (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
   rw [← y2 nd aa bb ne']
   exact y0 pairs faith nd aa bb (fun e=>ne' (congrArg Prod.fst e)) hc' pv lv
     pr fr hok' (yM test ka kb)
 rcases z143 checks haW hbW ab with hh | hh
 · exact one a b d haW hbW ne ka kb pro fresh hok (hh d hd)
 · have hok' : zy u b.1 a.1 (qm d) kb ka=true:=by
     rw [← y6 u a.1 b.1 d ka kb hd]
     exact hok
   rw [wo _ nd _ _ d hd]
   exact one b a (qm d) hbW haW (Ne.symm ne) kb ka (vX hd a.1 b.1 ▸ pro)
     (vX hd a.1 b.1 ▸ fresh) hok' (hh _ (yb hd).1)
def qw (g:Forest) (k:Nat) (pair:Nat × Nat):Option (List Sig) :=
 qF g k pair
theorem wu (g:Forest) (k:Nat)
   (names : ∀ x ∈ g.autos,vm (zz g) (x.map qe)=true)
   (earlier : ∀ i < (g.levels k).1,zo g.mode (zz g) k (zY g k i).toFinset)
   {pair out} (h:qw g k pair=some out) :
   zo g.mode (zz g) k out.toFinset:=by
 unfold qw qF at h
 split at h
 · contradiction
 next valid =>
   cases e:g.autos[pair.2]? with
   | none=>simp [e] at h
   | some perm =>
     simp only [e,Option.map_some,Option.some.injEq] at h
     subst out
     exact wr (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))
def qf (g:Forest) (k i:Nat) :=
 let raw:=jn g
 let (num,depth,cw,iw,pw,offw,lw,data):=g.levels k
 let (ops,bank,ws):=v9 g k i
 let values:=ws.map Prod.fst
 let start:=num * (10 * j4 g depth + raw.length + depth)
 let pos:=start + num * offw + q5 data (start + i * offw) offw
 let nr:=q5 data pos 5
 let nl:=q5 data (pos + 5) lw
 let st:=pos + 5 + lw
 let rules:=(vR data cw depth nr st).filterMap (fun (a,b)=>jH g ops depth bank a b)
 let ls:=fun tag=>((g.index k tag).bind (qw g (k - 1))).toList
 decide values.Nodup && !(values.contains (zz g)) &&
   (if k=0 then true else qu (k,ws.length,ws,jN g.mode ws,rules,ls) ws)
theorem jf (g:Forest) (k i:Nat)
   (samples:qr (zz g) (jW fun j=>(g.samples j).1) (jW fun j=>(g.samples j).2))
   (cols : ∀ ci ∈ g.cols,Slice g.mode (zq (jX g.mask ci)) (zz g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
   (names : ∀ x ∈ g.autos,vm (zz g) (x.map qe)=true)
   (prior:k > 0 → ∀ j < (g.levels (k - 1)).1,zo g.mode (zz g) (k - 1) (zY g (k - 1) j).toFinset)
   (checked:qf g k i=true):zo g.mode (zz g) k (zY g k i).toFinset:=by
 simp only [qf,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
 have hN:=checked.1.1
 have hT:zz g ∉ zY g k i:=by simpa [zY] using checked.1.2
 by_cases h0:k=0
 · subst k
   intro t lo h
   have ht:t=0:=by omega
   subst t
   generalize he:(zY g 0 i).toFinset=S at h
   obtain ⟨hS,_⟩:=h
   exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
 apply z135 (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
 · intro v hv
   apply vE _ _ _ _ _ (vJ g) v
   exact (vL _ _).subset hv
 · intro p hp
   obtain ⟨⟨a,b⟩,_,h⟩:=List.mem_filterMap.mp hp
   exact vG g cols h
 · intro tag xs hx
   have e:((g.index k tag).bind (qw g (k - 1)))=some xs:=by simpa using hx
   obtain ⟨pair,_,h⟩:=Option.bind_eq_some_iff.mp e
   exact wu g _ names (prior (by omega)) h
def z8 (g:Forest) (k start:Nat):Nat → Bool
 | 0=>true
 | n + 1=>qf g k (start + n)&&z8 g k start n
theorem yr {g k start n} (h:z8 g k start n=true) (j:Nat) (lo:start ≤ j) (hi:j < start + n) :
   qf g k j=true:=by
 induction n with
 | zero=>omega
 | succ n ih =>
   simp only [z8,Bool.and_eq_true] at h
   by_cases eq:j=start + n
   · simpa [eq] using h.1
   · exact ih h.2 (by omega)
theorem z3 {g k start a b} (h:z8 g k start a=true)
   (h' : z8 g k (start + a) b=true):z8 g k start (a + b)=true:=by
 induction b with
 | zero=>simpa using h
 | succ b ih =>
   simp only [z8,Bool.and_eq_true] at h'
   simp only [Nat.add_succ,z8,Bool.and_eq_true]
   exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩
def qp (g:Forest) (top:Nat) :=
 ∀ k ≤ top,z8 g k 0 (g.levels k).1=true
def qc (g:Forest) (prior:Nat → Nat) :=
 (qz g.mask (fun j=>(g.samples j).1) == BitVec.allOnes 768) &&
 (qz g.mask (fun j=>(g.samples j).2) == 0) &&
 g.cols.all (fun c=>vl g.mask c prior) &&
 g.autos.all (fun p=>vm (zz g) (p.map qe))
noncomputable def j1 (c:zl) (i j op:Nat) (ka kb:Bool) :=
 qg c op (z4 c i) (z4 c j) (dbin op (z4 c i) (z4 c j)) ka kb
noncomputable def v6 (u:Bool) (fl:Nat → Option (List Nat)) (l:Lane) (i j op:Nat) (ka kb:Bool):Bool :=
 force (l.2.2.2.2.1.getD i 0) fun x=>force (l.2.2.2.2.1.getD j 0) fun y =>
 or (not (v8 u x y op ka kb)) (jT fl l i j op ka kb)
theorem wa {u} {c:zl} {fl i j op ka kb} (mode:c.2.2.2.1.2=u) (nd:(c.2.2.1.map Prod.fst).Nodup)
   (hfl : ∀ tag ys,fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag,ys=xs.map BitVec.toNat)
   (h:v6 u fl (qx c) i j op ka kb=true) :
   j1 c i j op ka kb=true:=by
 simp only [v6,qT,qx,j156,yk,Bool.or_eq_true] at h
 change (!zy u (z4 c i).1 (z4 c j).1 op ka kb)=true ∨ jT fl (qx c) i j op ka kb=true at h
 rcases h with hno | hfb
 · simp [j1,qg,mode,hno]
 · by_cases hallow:zy u (z4 c i).1 (z4 c j).1 op ka kb=true
   · have hf:=vU nd hfl hfb
     simp only [j1,qg,mode,hallow,Bool.not_true,Bool.false_eq_true,if_false]
     exact hf
   · simp [j1,qg,mode,hallow]
noncomputable def y5 (fl:Nat → Option (List Nat)) (u:Bool) (b:Batch) (xs:List Lane) (i j op:Nat) (ka kb:Bool) :=
 let (k,n,r,_,cov):=b
 let len:=1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
 if len > k then true else
   let a:=qR b i
   let b':=qR b j
   let z:=j9 op a b'
   let mask:=jE r (jg cov (zM (!u) a) (zM (!u) b') ka kb ||| zM (!u) z)
   vu (fun c=>v6 u fl c i j op ka kb) mask xs
theorem yz {fl u} (k n) (xs:List zl) {i j op:Nat} {ka kb}
   (hi:i < n) (hj:j < n) {q:Nat} (hq:q < xs.length)
   (budget:xs[q].1=k) (arity:xs[q].2.1=n) (mode:xs[q].2.2.2.1.2=u) (nd:(xs[q].2.2.1.map Prod.fst).Nodup)
   (hfl : ∀ tag ys,fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag,ys=zs.map BitVec.toNat)
   (pass:y5 fl u (zV k n xs) (xs.map qx) i j op ka kb=true) :
   j1 xs[q] i j op ka kb=true:=by
 let len:=1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
 have eval:j1 xs[q] i j op ka kb =
     if !zy u (z4 xs[q] i).1 (z4 xs[q] j).1 op ka kb then true
     else if len > k then true else if jG xs[q] (!u) ka kb op i j != BitVec.allOnes 768 then true
     else if !qa (dbin op (z4 xs[q] i) (z4 xs[q] j)).1 ||
       xs[q].2.2.1.any (fun v=>v.1 == (dbin op (z4 xs[q] i) (z4 xs[q] j)).1)
     then true else qy xs[q].2.2.2.1.2 xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k - 1)
       ((q8 xs[q].2.2.1 (z4 xs[q] i) (z4 xs[q] j) ka kb).map Prod.fst)
       (zT op (z4 xs[q] i) (z4 xs[q] j)):=by
   simp only [j1,qg,qC,budget,arity,mode,len,jG]<;>rfl
 by_cases small:len > k
 · rw [eval]
   split<;>simp [small]
 · let r:=units xs.length
   let a:=qR (zV k n xs) i
   let b:=qR (zV k n xs) j
   let cov:=vd (fun c:zl=>c.2.2.2.1.1) xs
   change (if len > k then true else vu _ (jE r
      (jg cov (zM (!u) a) (zM (!u) b) ka kb |||
       zM (!u) (j9 op a b))) (xs.map qx))=true at pass
   rw [if_neg small] at pass
   have ca:a=_:=v0 k n xs hi
   have cb:b=_:=v0 k n xs hj
   dsimp only [r,cov] at pass
   rw [ca,cb,z147,qE,qE,qE,wd,wP] at pass
   by_cases hit:jG xs[q] (!u) ka kb op i j=BitVec.allOnes 768
   · apply wa mode nd hfl
     have m:=z150 _ _ _ q (by simpa using hq) (by
       rw [q119 _ _ _ hq]
       exact beq_iff_eq.mpr hit) pass
     simpa only [List.getElem_map] using m
   · rw [eval]
     by_cases hallow:zy u (z4 xs[q] i).1 (z4 xs[q] j).1 op ka kb=true
     · rw [if_neg (by simp [hallow]),if_neg small,if_pos (bne_iff_ne.mpr hit)]
     · simp [hallow]
noncomputable def y4 (fl:Nat → Option (List Nat)) (u:Bool) (b:Batch) (xs:List Lane) (i j op:Nat) :=
 let f:=y5 fl u b xs i j op
 f false false&&f true false&&f false true&&f true true
noncomputable def v3 (fl:Nat → Option (List Nat)) (u:Bool) (b:Batch) (xs:List Lane) (i:Nat) (js:List Nat) :=
 js.all (fun j=>(wJ u).all (y4 fl u b xs i j))
noncomputable def qQ (fl:Nat → Option (List Nat)) (u:Bool) (b:Batch) (xs:List Lane):List Nat → Bool
 | []=>true
 | i :: js=>v3 fl u b xs i js&&qQ fl u b xs js
theorem yy {fl u} (k n) (xs:List zl) {q:Nat} (hq:q < xs.length)
   (budget:xs[q].1=k) (arity:xs[q].2.1=n) (mode:xs[q].2.2.2.1.2=u) (nd:(xs[q].2.2.1.map Prod.fst).Nodup)
   (hfl : ∀ tag ys,fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag,ys=zs.map BitVec.toNat)
   (js:List Nat)
   (bounds : ∀ j ∈ js,j < n) (allRows:qQ fl u (zV k n xs) (xs.map qx) js=true) :
   qu xs[q] (js.map (z4 xs[q]))=true:=by
 induction js with
 | nil=>rfl
 | cons i js ih =>
   simp only [qQ,Bool.and_eq_true,v3,List.all_eq_true] at allRows
   simp only [List.map_cons,qu,wq,Bool.and_eq_true,List.all_eq_true,List.mem_map]
   have hi:=bounds i List.mem_cons_self
   refine ⟨?_,ih (fun j hj=>bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
   rintro _ ⟨j,hj,rfl⟩ op hop
   have hj':=bounds j (List.mem_cons_of_mem _ hj)
   rw [mode] at hop
   have pass:=allRows.1 j hj op hop
   have check := @yz fl u k n xs i j op
   simp only [y4,Bool.and_eq_true] at pass
   simp only [qI,Bool.and_eq_true]
   exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
     check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩
noncomputable def vM (fl:Nat → Option (List Nat)) (u:Bool) (k n:Nat) (xs:List zl) :=
 qQ fl u (zV k n xs) (xs.map qx) (List.range n)
theorem yQ {fl u k n} {xs:List zl} {q} (hq:q < xs.length)
   (hb:xs[q].1=k) (ha:xs[q].2.1=n) (hm:xs[q].2.2.2.1.2=u) (nd:(xs[q].2.2.1.map Prod.fst).Nodup)
   (hfl : ∀ tag ys,fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag,ys=zs.map BitVec.toNat)
   (hn:xs[q].2.2.1.length=n)
   (pass:vM fl u k n xs=true):qu xs[q] xs[q].2.2.1=true:=by
 have all:=yy k n xs hq hb ha hm nd hfl (List.range n) (fun _=>List.mem_range.mp) pass
 have eq:(List.range n).map (z4 xs[q])=xs[q].2.2.1:=by
   apply List.ext_getElem
   · simp [hn]
   · intro i h1 h2
     simp [z4,List.getD_eq_getElem?_getD,h2]
 rwa [eq] at all
def qO (g:Forest) (k i:Nat):zl :=
 let raw:=jn g
 let (num,depth,cw,iw,pw,offw,lw,data):=g.levels k
 let (ops,bank,ws):=v9 g k i
 let start:=num * (10 * j4 g depth + raw.length + depth)
 let pos:=start + num * offw + q5 data (start + i * offw) offw
 let nr:=q5 data pos 5
 let nl:=q5 data (pos + 5) lw
 let st:=pos + 5 + lw
 let rules:=(vR data cw depth nr st).filterMap (fun (a,b)=>jH g ops depth bank a b)
 let ls:=fun tag=>((g.index k tag).bind (qw g (k - 1))).toList
 (k,ws.length,ws,jN g.mode ws,rules,ls)
theorem z385 (g:Forest) (k i tag:Nat) (ys) (h:wX g k tag=some ys) :
   ∃ xs ∈ (qO g k i).2.2.2.2.2 tag,ys=xs.map BitVec.toNat:=by
 change ∃ xs ∈ ((g.index k tag).bind (qw g (k - 1))).toList,_
 unfold wX at h
 cases hp:g.index k tag with
 | none=>simp [hp] at h
 | some pair =>
   simp only [hp,Option.bind_some,ww] at h
   simp only [Option.bind_some,qw,qF]
   split at h
   · contradiction
   next v =>
     cases ha:g.autos[pair.2]? with
     | none=>simp [ha] at h
     | some perm =>
       simp only [ha,Option.bind_some] at h
       cases hv:perm.all j3 with
       | false=>simp [hv] at h
       | true =>
         simp only [hv,cond_true,Option.some.injEq] at h
         refine ⟨(zY g (k - 1) pair.1).map (zj (perm.map qe).reverse),?_,?_⟩
         · simp [v]
         · exact h.symm.trans (wY g _ _ hv)
theorem yx (g:Forest) (k i:Nat) :
   qf g k i=(prelim (zz g) (qO g k i) &&
     (if k=0 then true else qu (qO g k i) (qO g k i).2.2.1)):=rfl
theorem z217 {g k start n} (h : ∀ (i:Nat),start ≤ i → i < start + n → qf g k i=true) :
   z8 g k start n=true:=by
 induction n with
 | zero=>rfl
 | succ n ih =>
   simp only [z8,Bool.and_eq_true]
   exact ⟨h _ (by omega) (by omega),ih (fun i le lt=>h i le (by omega))⟩
def qL (g:Forest) (k start n:Nat) :=
 ((List.range n).map (start + ·)).map (qO g k)
def z168 (g:Forest) (k start n ar:Nat) :=
 (qL g k start n).all (fun c=>c.2.1 == ar&&prelim (zz g) c)
noncomputable def qD (g:Forest) (k start n ar lo len:Nat) :=
 let xs:=qL g k start n
 let b:=zV k ar xs
 vz xs fun ys=>(List.range len).all (fun d =>
   let i:=lo + d
   v3 (wX g k) g.mode b ys i (List.range' (i + 1) (ar - (i + 1))))
theorem vs {g k start n ar lo len} (h:qD g k start n ar lo len=true)
   (i:Nat) (l:lo ≤ i) (r:i < lo + len) :
   v3 (wX g k) g.mode (zV k ar (qL g k start n)) ((qL g k start n).map qx)
     i (List.range' (i + 1) (ar - (i + 1)))=true:=by
 simp only [qD,jq] at h
 have ha:=List.all_eq_true.mp h (i - lo) (List.mem_range.mpr (by omega))
 simpa only [Nat.add_sub_of_le l] using ha
theorem yt {g k start n ar lo a b}
   (h:qD g k start n ar lo a=true) (t:qD g k start n ar (lo + a) b=true) :
   qD g k start n ar lo (a + b)=true:=by
 simp only [qD,jq]
 apply List.all_eq_true.mpr
 intro j hj
 have jlt:=List.mem_range.mp hj
 by_cases first:j < a
 · exact vs h (lo + j) (by omega) (by omega)
 · exact vs t (lo + j) (by omega) (by omega)
theorem z389 {g k start n ar} (h:qD g k start n ar 0 ar=true) :
   vM (wX g k) g.mode k ar (qL g k start n)=true:=by
 let xs:=qL g k start n
 have go (lo num:Nat) (eq:lo + num=ar) :
     qQ (wX g k) g.mode (zV k ar xs) (xs.map qx) (List.range' lo num)=true:=by
   induction num generalizing lo with
   | zero=>rfl
   | succ num ih =>
     simp only [List.range'_succ,qQ,Bool.and_eq_true]
     refine ⟨?_,ih (lo + 1) (by omega)⟩
     have ok:=vs h lo (by omega) (by omega)
     simpa only [show ar - (lo + 1)=num by omega] using ok
 unfold vM
 rw [List.range_eq_range']
 exact go 0 ar (by omega)
theorem z226 {g k start n ar} (hd:z168 g k start n ar=true)
   (h:qD g k start n ar 0 ar=true):z8 g k start n=true:=by
 apply z217
 intro i lo hi
 let xs:=qL g k start n
 have hm:qO g k i ∈ xs:=by
   apply List.mem_map.mpr
   exact ⟨i,List.mem_map.mpr ⟨i - start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
 obtain ⟨q,hq,e⟩:=List.getElem_of_mem hm
 have one:=List.all_eq_true.mp hd _ hm
 simp only [Bool.and_eq_true,beq_iff_eq] at one
 have hb:xs[q].1=k:=by rw [e]; rfl
 have ha:xs[q].2.1=ar:=e ▸ one.1
 have nd:(xs[q].2.2.1.map Prod.fst).Nodup:=by
   have p:=one.2
   simp only [prelim,Bool.and_eq_true,decide_eq_true_eq] at p
   rw [e]
   exact p.1
 have hfl : ∀ tag ys,wX g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag,ys=zs.map BitVec.toNat:=by
   rw [e]
   exact fun tag ys h=>z385 g k i tag ys h
 have hm' : xs[q].2.2.2.1.2=g.mode:=by rw [e]; rfl
 have hn:xs[q].2.2.1.length=ar:=by rw [e]; exact one.1
 rw [yx,Bool.and_eq_true]
 refine ⟨one.2,?_⟩
 split
 · rfl
 · exact e ▸ yQ hq hb ha hm' nd hfl hn (z389 h)
def zd (g:Forest) (k start n ar lo num:Nat):Nat → Prop
 | 0=>qD g k start n ar lo num=true
 | d + 1=>zd g k start n ar lo (num / 2) d ∧ zd g k start n ar (lo + num / 2) (num - num / 2) d
theorem z307 {g k start n ar lo num d} (h:zd g k start n ar lo num d) :
   qD g k start n ar lo num=true:=by
 induction d generalizing lo num with
 | zero=>exact h
 | succ d ih =>
   have v:=yt (ih h.1) (ih h.2)
   simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v
def ze (g:Forest) (k start n ar rows:Nat):Nat → Prop
 | 0=>z168 g k start n ar=true ∧ zd g k start n ar 0 ar rows
 | d + 1=>ze g k start (n / 2) ar rows d ∧ ze g k (start + n / 2) (n - n / 2) ar rows d
theorem z2 {g k start n ar rows d} (h:ze g k start n ar rows d) :
   z8 g k start n=true:=by
 induction d generalizing start n with
 | zero=>exact z226 h.1 (z307 h.2)
 | succ d ih =>
   have v:=z3 (ih h.1) (ih h.2)
   simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
theorem z138 (g:Forest) (top:Nat) (prior:Nat → Nat)
   (lower : ∀ q,Lower g.mode (zq q) (z1 q) (prior q))
   (geometry:qc g prior=true) (rows:qp g top) :
   ∀ k ≤ top,∀ i < (g.levels k).1,zo g.mode (zz g) k (zY g k i).toFinset:=by
 simp only [qc,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
 intro k
 induction k with
 | zero =>
   intro hk i hi
   apply jf g 0 i (v2 geometry.1.1.1 geometry.1.1.2)
     (fun x hx=>vk _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
   exact yr (rows 0 hk) i (by omega) (by omega)
 | succ k ih =>
   intro hk i hi
   apply jf g _ i (v2 geometry.1.1.1 geometry.1.1.2)
     (fun x hx=>vk _ prior lower (geometry.1.2 x hx)) geometry.2
     (fun _=>by simpa using ih (by omega))
   exact yr (rows _ hk) i (by omega) (by omega)
theorem z131 {u g top prior k i ws} (hu:g.mode=u)
   (low : ∀ q,Lower u (zq q) (z1 q) (prior q))
   (geom:qc g prior=true) (blocks:qp g top) (le:k ≤ top)
   (idx:j5 g k i ws=true):zo u (zz g) k ws.toFinset:=by
 subst hu
 simp only [j5,Bool.and_eq_true,decide_eq_true_eq] at idx
 rw [← qU idx.2]
 exact z138 g top prior low geom blocks _ le i idx.1
theorem wk {u:Bool} {g:Forest} {m cap i:Nat} {prior:Nat → Nat} {ws:List Sig}
   (hm:g.mask=m) (hu:g.mode=u) (low : ∀ q,Lower u (zq q) (z1 q) (prior q))
   (geom:qc g prior=true) (blocks:qp g cap)
   (idx:j5 g cap i ws=true):zo u (z1 m) cap ws.toFinset:=by
 subst hm
 exact z131 hu low geom blocks (Nat.le_refl _) idx
theorem q187:q123 511 13438558465=true:=by decide +kernel
theorem yL:vars 511=inputs:=by decide +kernel
theorem z245:vars 1535=inputs:=by decide +kernel
theorem q368:graph=z1 511:=by decide +kernel
theorem z218:inputs.all zU=true:=by decide +kernel
theorem z391:bit 0 graph=false:=by decide +kernel
theorem wl {u k S} (run:Live u (z1 511) k S) (sub : ∀ a ∈ S,a ∈ inputs) :
   S=(vars 511).toFinset:=by
 have ok:=q187
 simp only [q123,Bool.and_eq_true,beq_iff_eq] at ok
 have sub' : ∀ a ∈ S,a ∈ vars 511:=fun a ha=>yL ▸ sub a ha
 ext a
 rw [List.mem_toFinset]
 refine ⟨sub' a,fun hm=>?_⟩
 obtain ⟨r,s,hd,iso⟩:=jd ok.1.2 a (List.mem_toFinset.mpr (ok.2 ▸ hm))
 exact j8 run (vars 511) a sub' r s hd iso
theorem zC (gs:List Gate) (w:List Sig):(execute gs w).length=w.length + gs.length:=by
 induction gs generalizing w with
 | nil=>simp [execute]
 | cons g gs ih =>
   change (execute gs (w ++ [gv w g])).length=w.length + (gs.length + 1)
   rw [ih]
   simp
   omega
theorem zx (a b:List Gate) (w:List Sig):execute (a ++ b) w=execute b (execute a w):=by
 induction a generalizing w with
 | nil=>rfl
 | cons g a ih=>exact ih (w ++ [gv w g])
theorem zb {α : Type} [Inhabited α] (a b:List α) (d : α) (i:Nat) (hi:i < a.length) :
   (a ++ b).getD i d=a.getD i d:=by
 simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left hi]
theorem zB {α : Type} [Inhabited α] (a b:List α) (d : α) (i:Nat) (hi:a.length ≤ i) :
   (a ++ b).getD i d=b.getD (i - a.length) d:=by
 simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right hi]
def jp:GateOp → Bool
 | .and=>true
 | _=>false
theorem j0 (wm:List Sig) (g:Gate) (ia ib:Nat)
   (hinp:g.inputs=[ia,ib]) (hop:g.op=GateOp.and ∨ g.op=GateOp.or) :
   gv wm g=bin (if jp g.op then 0 else 1) (wm.getD ia zero) (wm.getD ib zero):=by
 apply zF
 intro r
 rcases hop with ha | ho
 · simp [gv,hinp,ha,jp,jk,zX,qP]
 · simp [gv,hinp,ho,jp,jk,zX,zv]
theorem ye (idx p:Nat) (hp:p < 9 + idx) (preW:List Sig) (hpre:preW.length=9 + idx)
   (z:Sig) (hz:preW.getD p zero=z) (suf:List Gate) (post:List Sig) :
   ∃ tail:List Sig,
     execute suf (preW ++ [z] ++ post)=preW ++ [z] ++ (post ++ tail) ∧
     execute (suf.map fun g => ⟨g.op,g.inputs.map fun r=>if r == 9 + idx then p else if 9 + idx < r then r - 1 else r⟩)
       (preW ++ post)=preW ++ (post ++ tail):=by
 let remap (r:Nat):Nat:=if r == 9 + idx then p else if 9 + idx < r then r - 1 else r
 induction suf generalizing post with
 | nil=>exact ⟨[],by simp [execute]⟩
 | cons g suf ih =>
   have get_eq (r:Nat):(preW ++ post).getD (remap r) zero=(preW ++ [z] ++ post).getD r zero:=by
     rcases Nat.lt_trichotomy r (9 + idx) with hr | rfl | hr
     · have hne:(r == 9 + idx)=false:=beq_false_of_ne (Nat.ne_of_lt hr)
       have hnot : ¬ (9 + idx < r):=by omega
       have hrm:remap r=r:=by simp only [remap,hne,Bool.false_eq_true,if_false,if_neg hnot]
       rw [hrm,List.append_assoc,zb _ _ _ _ (hpre ▸ hr),zb _ _ _ _ (hpre ▸ hr)]
     · have hrm:remap (9 + idx)=p:=by simp [remap]
       rw [hrm,zb _ _ _ _ (hpre ▸ hp),hz,List.append_assoc,
           zB _ _ _ _ (by rw [hpre])]
       simp [hpre]
     · have hne:(r == 9 + idx)=false:=beq_false_of_ne (Nat.ne_of_gt hr)
       have hrm:remap r=r - 1:=by simp only [remap,hne,Bool.false_eq_true,if_false,if_pos hr]
       rw [hrm,zB _ _ _ _ (by rw [hpre]; omega),
           List.append_assoc,zB _ _ _ _ (by rw [hpre]; omega)]
       rw [hpre]
       have hpos:r - (9 + idx)=(r - 1 - (9 + idx)) + 1:=by omega
       rw [hpos]
       rfl
   have hgv:gv (preW ++ post) ⟨g.op,g.inputs.map remap⟩ = gv (preW ++ [z] ++ post) g:=by
     have hxs:List.map (fun x=>(preW ++ post).getD (remap x) zero) g.inputs =
         List.map (fun i=>(preW ++ [z] ++ post).getD i zero) g.inputs:=by
       apply List.map_congr_left
       intro r _
       exact get_eq r
     simp only [gv,List.map_map,Function.comp_def,hxs]
   let v:=gv (preW ++ [z] ++ post) g
   obtain ⟨tail,ht1,ht2⟩:=ih (post ++ [v])
   refine ⟨v :: tail,?_,?_⟩
   · change execute suf ((preW ++ [z] ++ post) ++ [v])=_
     simpa only [v,List.append_assoc,List.cons_append,List.nil_append] using ht1
   · change execute (suf.map _) ((preW ++ post) ++ [gv (preW ++ post) ⟨g.op,g.inputs.map remap⟩])=_
     rw [hgv]
     simpa only [v,List.append_assoc,List.cons_append,List.nil_append] using ht2
theorem z211 (x:Fin 9 → Bool) : ∃ r:Row,sample r=x:=by
 let rv:=(BitVec.ofBoolListLE (List.ofFn x)).toNat
 have hlt:rv < 512:=by
   have:=(BitVec.ofBoolListLE (List.ofFn x)).isLt
   simpa [List.length_ofFn] using this
 refine ⟨⟨rv,hlt⟩,funext fun j=>?_⟩
 change bit ⟨rv,hlt⟩ (inputs.getD j.val zero)=x j
 rw [zZ]
 change (BitVec.ofBoolListLE (List.ofFn x)).getLsbD j.val=x j
 rw [BitVec.getLsbD_ofBoolListLE]
 simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,j.isLt,↓reduceDIte,Option.getD_some]
theorem w9 (C:Circuit) (hmin:PEqualNP.MetaComplexity.IsMinimalCircuit 9 C)
   (hnorm : ∀ i:Fin C.size,
     (∀ w ∈ (C.gates.get i).inputs,w < 9 + i.val) ∧
     (C.gates.get i).inputs.Nodup ∧
     ((C.gates.get i).op=GateOp.not ∧ (C.gates.get i).inputs.length=1 ∨
      (C.gates.get i).op ≠ GateOp.not ∧ (C.gates.get i).inputs.length=2)) :
   (execute C.gates inputs).Nodup:=by
 by_contra hnd
 rw [List.nodup_iff_injective_getElem] at hnd
 simp only [Function.Injective,not_forall,not_imp] at hnd
 obtain ⟨a,b,heq,hab⟩:=hnd
 let W:=execute C.gates inputs
 have hlen:W.length=9 + C.gates.length:=by
   simpa [W,inputs] using zC C.gates inputs
 have wlog_pair : ∃ p q,p < q ∧ q < W.length ∧ W.getD p zero=W.getD q zero:=by
   have heq' : W.getD a.val zero=W.getD b.val zero:=by
     simpa [W,List.getD_eq_getElem?_getD,a.isLt,b.isLt] using heq
   rcases Nat.lt_trichotomy a.val b.val with hlt | hev | hgt
   · exact ⟨a.val,b.val,hlt,b.isLt,heq'⟩
   · exact absurd (Fin.ext hev) hab
   · exact ⟨b.val,a.val,hgt,a.isLt,heq'.symm⟩
 obtain ⟨p,q,hpq,hql,hweq⟩:=wlog_pair
 have hq9:9 ≤ q:=by
   by_contra hqlt
   obtain ⟨tail,hW⟩:=zO C.gates inputs
   have ha' : W.getD p zero=inputs.getD p zero:=by
     change (execute C.gates inputs).getD p zero=_; rw [hW]; exact zb _ _ _ _ (by simp [inputs]; omega)
   have hb' : W.getD q zero=inputs.getD q zero:=by
     change (execute C.gates inputs).getD q zero=_; rw [hW]; exact zb _ _ _ _ (by simp [inputs]; omega)
   rw [ha',hb'] at hweq
   have hnd_in:=inputs_nodup
   have hpi:inputs[p]'(by simp [inputs]; omega)=inputs[q]'(by simp [inputs]; omega):=by
     simpa [List.getD_eq_getElem?_getD,show p < inputs.length by simp [inputs]; omega,
       show q < inputs.length by simp [inputs]; omega] using hweq
   have heq_idx:=(List.nodup_iff_injective_getElem.mp hnd_in)
     (show (fun i:Fin inputs.length=>inputs[i.val]) ⟨p,by simp [inputs]; omega⟩ =
       (fun i:Fin inputs.length=>inputs[i.val]) ⟨q,by simp [inputs]; omega⟩ from hpi)
   have hval:p=q:=congrArg Fin.val heq_idx
   omega
 let idx:=q - 9
 have hidx:idx < C.gates.length:=by omega
 have hqeq:q=9 + idx:=by omega
 rw [hqeq] at hpq hweq
 let pref:=C.gates.take idx
 let g_idx:=C.gates[idx]
 let suf:=C.gates.drop (idx + 1)
 have hsplit:pref ++ [g_idx] ++ suf=C.gates:=by
   simp [pref,g_idx,suf,List.take_append_getElem,List.append_assoc]
 let preW:=execute pref inputs
 have hprelen:preW.length=9 + idx:=by
   have : pref.length=idx:=List.length_take_of_le (Nat.le_of_lt hidx)
   simpa [preW,this,inputs] using zC pref inputs
 let z:=gv preW g_idx
 let remap (r:Nat):Nat:=if r == 9 + idx then p else if 9 + idx < r then r - 1 else r
 let D:Circuit := ⟨pref ++ suf.map fun g => ⟨g.op,g.inputs.map remap⟩,remap C.output⟩
 have hD_size:D.size < C.size:=by
   simp only [Circuit.size,D,pref,suf,List.length_append,List.length_map,
     List.length_take_of_le (Nat.le_of_lt hidx),List.length_drop]
   omega
 have hD_fan:PEqualNP.MetaComplexity.FanInTwo D:=by
   intro g hg
   simp only [D,List.mem_append,List.mem_map] at hg
   rcases hg with hp_mem | ⟨g',hsuf_mem,rfl⟩
   · exact hmin.1 g (List.mem_of_mem_take hp_mem)
   · have hg':=hmin.1 g' (List.mem_of_mem_drop hsuf_mem)
     exact ⟨hg'.1,by simpa using hg'.2⟩
 have hWsplit:W=execute suf (preW ++ [z]):=by
   have : W=execute (pref ++ [g_idx] ++ suf) inputs:=congrArg (fun gs=>execute gs inputs) hsplit.symm
   rw [zx,zx] at this
   exact this
 have hz_eq:preW.getD p zero=z:=by
   obtain ⟨tail',htail'⟩:=zO suf (preW ++ [z])
   have hp_val:W.getD p zero=preW.getD p zero:=by
     rw [hWsplit,htail',List.append_assoc]
     exact zb _ _ _ _ (by rw [hprelen]; exact hpq)
   have hq_val:W.getD (9 + idx) zero=z:=by
     rw [hWsplit,htail']
     rw [zb _ _ _ _ (by simp [hprelen]),zB _ _ _ _ (by rw [hprelen])]
     simp [hprelen]
   rw [← hp_val,← hq_val,hweq]
 obtain ⟨tail,hWtail,hDtail⟩:=ye idx p hpq preW hprelen z hz_eq suf []
 have hW_eq:W=preW ++ [z] ++ tail:=by simpa [hWsplit] using hWtail
 have hD_eq:execute D.gates inputs=preW ++ tail:=by
   simpa only [D,preW,remap,zx,List.append_nil,List.nil_append] using hDtail
 have hD_out:(execute D.gates inputs).getD D.output zero=W.getD C.output zero:=by
   rw [hD_eq,hW_eq]
   change (preW ++ tail).getD (remap C.output) zero=(preW ++ [z] ++ tail).getD C.output zero
   rcases Nat.lt_trichotomy C.output (9 + idx) with hr | hr | hr
   · have hne:(C.output == 9 + idx)=false:=beq_false_of_ne (Nat.ne_of_lt hr)
     have hnot : ¬ (9 + idx < C.output):=by omega
     have hrm:remap C.output=C.output:=by simp only [remap,hne,Bool.false_eq_true,if_false,if_neg hnot]
     rw [hrm,List.append_assoc,zb _ _ _ _ (hprelen ▸ hr),zb _ _ _ _ (hprelen ▸ hr)]
   · have hrm:remap C.output=p:=by simp [remap,hr]
     rw [hrm,hr,zb _ _ _ _ (hprelen ▸ hpq),hz_eq,
         List.append_assoc,zB _ _ _ _ (by rw [hprelen])]
     simp [hprelen]
   · have hne:(C.output == 9 + idx)=false:=beq_false_of_ne (Nat.ne_of_gt hr)
     have hrm:remap C.output=C.output - 1:=by simp only [remap,hne,Bool.false_eq_true,if_false,if_pos hr]
     rw [hrm,zB _ _ _ _ (by rw [hprelen]; omega),
         List.append_assoc,zB _ _ _ _ (by rw [hprelen]; omega),hprelen]
     have hpos:C.output - (9 + idx)=(C.output - 1 - (9 + idx)) + 1:=by omega
     rw [hpos]
     rfl
 have hD_fun:PEqualNP.MetaComplexity.circuitFun 9 D=PEqualNP.MetaComplexity.circuitFun 9 C:=by
   funext x
   obtain ⟨r,hr⟩:=z211 x
   rw [← hr]
   change (D.wires (List.ofFn (sample r))).getD D.output false=(C.wires (List.ofFn (sample r))).getD C.output false
   rw [← vr D hD_fan D.output r,← vr C hmin.1 C.output r,hD_out]
 have hle:=hmin.2 D hD_fan hD_fun
 omega
theorem wW : ∀ b ∈ inputs,bit 0 b=false ∧ bit ⟨511,by decide⟩ b=true:=by
 have key : ∀ fj:Fin 9,
     bit 0 (inputs.getD fj.val zero)=false ∧ bit ⟨511,by decide⟩ (inputs.getD fj.val zero)=true:=by
   intro fj
   have c0:=zZ fj 0
   have c1:=zZ fj ⟨511,by decide⟩
   change bit 0 (inputs.getD fj.val zero)=_ at c0
   change bit ⟨511,by decide⟩ (inputs.getD fj.val zero)=_ at c1
   rw [c0,c1]
   refine ⟨Nat.zero_testBit _,?_⟩
   fin_cases fj<;>decide
 intro b hb
 obtain ⟨j,hj,hbj⟩:=List.getElem_of_mem hb
 have hj9:j < 9:=by simpa [inputs] using hj
 have hbj' : b=inputs.getD j zero:=by rw [← hbj,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]; rfl
 rw [hbj']
 exact key ⟨j,hj9⟩
theorem vC (C:Circuit)
   (hGate : ∀ i:Fin C.size,(C.gates.get i).inputs.length=2 ∧
     (∀ w ∈ (C.gates.get i).inputs,w < 9 + i.val) ∧
     ((C.gates.get i).op=GateOp.and ∨ (C.gates.get i).op=GateOp.or)) :
   ∀ m ≤ C.size,∀ a ∈ execute (C.gates.take m) inputs,
     bit 0 a=false ∧ bit ⟨511,by decide⟩ a=true ∧
     ∀ r s:Row,(r.val &&& s.val=r.val) → bit r a=true → bit s a=true:=by
 intro m hm
 induction m with
 | zero =>
   intro a ha
   change a ∈ inputs at ha
   have hin:=wW
   refine ⟨(hin a ha).1,(hin a ha).2,fun r s hrs hra=>?_⟩
   obtain ⟨j,hj,haj⟩:=List.getElem_of_mem ha
   have hle9:j < 9:=by simpa [inputs] using hj
   have haj' : a=inputs.getD j zero:=by rw [← haj,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj]; rfl
   rw [haj'] at hra ⊢
   have hb1:=zZ ⟨j,hle9⟩ r
   have hb2:=zZ ⟨j,hle9⟩ s
   change bit r (inputs.getD (⟨j,hle9⟩ : Fin 9).val zero)=_ at hb1
   change bit s (inputs.getD (⟨j,hle9⟩ : Fin 9).val zero)=_ at hb2
   rw [hb1] at hra
   rw [hb2]
   have htb:=congrArg (fun n=>n.testBit j) hrs
   rw [Nat.testBit_and] at htb
   dsimp only at hra ⊢
   rw [hra] at htb
   simpa using htb
 | succ m ih =>
   have hm_lt:m < C.size:=by omega
   have hm_lt' : m < C.gates.length:=hm_lt
   have ih':=ih (Nat.le_of_lt hm_lt)
   rw [List.take_succ_eq_append_getElem hm_lt',zx]
   let gm:=C.gates.get ⟨m,hm_lt⟩
   let wm:=execute (C.gates.take m) inputs
   have hwm_len:wm.length=9 + m:=by
     simp [wm,zC,inputs,List.length_take_of_le (Nat.le_of_lt hm_lt)]
   change ∀ a ∈ wm ++ [gv wm gm],_
   intro a ha
   rcases List.mem_append.mp ha with haw | haz
   · exact ih' a haw
   · simp only [List.mem_singleton] at haz
     subst a
     obtain ⟨hlen2,hltm,hop⟩:=hGate ⟨m,hm_lt⟩
     obtain ⟨ia,ib,hinp⟩:=List.length_eq_two.mp hlen2
     have hia_mem:wm.getD ia zero ∈ wm:=by
       have hlt_ia:ia < wm.length:=by rw [hwm_len]; exact hltm ia (by simp [hinp])
       simp [List.getD_eq_getElem?_getD,hlt_ia]
     have hib_mem:wm.getD ib zero ∈ wm:=by
       have hlt_ib:ib < wm.length:=by rw [hwm_len]; exact hltm ib (by simp [hinp])
       simp [List.getD_eq_getElem?_getD,hlt_ib]
     obtain ⟨ia0,ia511,iamono⟩:=ih' _ hia_mem
     obtain ⟨ib0,ib511,ibmono⟩:=ih' _ hib_mem
     have hbin:=j0 wm gm ia ib hinp hop
     rw [hbin]
     rcases hop with h_and | h_or
     · have hd0:(if jp gm.op then 0 else 1)=0:=by
         have hgm:gm.op=GateOp.and:=h_and
         rw [hgm]
         rfl
       rw [hd0]
       have hba (r:Row):bit r (bin 0 (wm.getD ia zero) (wm.getD ib zero)) =
           (bit r (wm.getD ia zero)&&bit r (wm.getD ib zero)):=BitVec.getLsbD_and
       refine ⟨by rw [hba,ia0,ib0]; rfl,by rw [hba,ia511,ib511]; rfl,fun r s hrs hra=>?_⟩
       rw [hba,Bool.and_eq_true] at hra ⊢
       exact ⟨iamono r s hrs hra.1,ibmono r s hrs hra.2⟩
     · have hd1:(if jp gm.op then 0 else 1)=1:=by
         have hgm:gm.op=GateOp.or:=h_or
         rw [hgm]
         rfl
       rw [hd1]
       have hbo (r:Row):bit r (bin 1 (wm.getD ia zero) (wm.getD ib zero)) =
           (bit r (wm.getD ia zero)||bit r (wm.getD ib zero)):=BitVec.getLsbD_or
       refine ⟨by rw [hbo,ia0,ib0]; rfl,by rw [hbo,ia511,ib511]; rfl,fun r s hrs hra=>?_⟩
       rw [hbo,Bool.or_eq_true] at hra ⊢
       rcases hra with hra | hra
       · exact Or.inl (iamono r s hrs hra)
       · exact Or.inr (ibmono r s hrs hra)
theorem ve (a:Sig) (h0:bit 0 a=false) (h511:bit ⟨511,by decide⟩ a=true) :
   proper a:=by
 refine ⟨fun hz=>?_,fun ho=>?_⟩
 · have:=congrArg (bit ⟨511,by decide⟩) hz
   rw [h511,zv] at this
   exact Bool.noConfusion this
 · have:=congrArg (bit 0) ho
   rw [h0,qP] at this
   exact Bool.noConfusion this
theorem qX (C:Circuit) (hmin:PEqualNP.MetaComplexity.IsMinimalCircuit 9 C)
   (hfun:PEqualNP.MetaComplexity.circuitFun 9 C=edge)
   (hnorm : ∀ i:Fin C.size,
     (∀ w ∈ (C.gates.get i).inputs,w < 9 + i.val) ∧
     (C.gates.get i).inputs.Nodup ∧
     ((C.gates.get i).op=GateOp.not ∧ (C.gates.get i).inputs.length=1 ∨
      (C.gates.get i).op ≠ GateOp.not ∧ (C.gates.get i).inputs.length=2))
   (hndW:(execute C.gates inputs).Nodup)
   (v:Fin 9) (hv:v ∈ ([4,6,7]:List (Fin 9))) (i:Fin C.size) (w:Nat)
   (hw_lt:w < 9 + i.val) (hw_ne:w ≠ v.val) (hor:(C.gates.get i).op=GateOp.or)
   (hinp:(C.gates.get i).inputs=[v.val,w] ∨ (C.gates.get i).inputs=[w,v.val])
   (huniq : ∀ k:Fin C.size,k ≠ i → v.val ∉ (C.gates.get k).inputs) :
   let W:=execute C.gates inputs
   let wv:=W.getD w zero
   (wv &&& zI v.val)=zero ∧
     (∀ t < 9 + C.size,t ≠ v.val → nrm true (W.getD t zero) ≠ inputs.getD v.val zero) ∧
     (∀ r:Row,bit r wv=bit ⟨r.val ^^^ (1 <<< v.val),vp r v⟩ wv):=by
 let W:=execute C.gates inputs
 let wv:=W.getD w zero
 let flipV (r:Row):Row := ⟨r.val ^^^ (1 <<< v.val),vp r v⟩
 have hindep : ∀ m ≤ i.val,∀ t < 9 + m,t ≠ v.val → ∀ r:Row,
     bit r ((execute (C.gates.take m) inputs).getD t zero) =
     bit (flipV r) ((execute (C.gates.take m) inputs).getD t zero):=by
   intro m hm
   induction m with
   | zero =>
     intro t ht9 htne r
     simp only [Nat.add_zero] at ht9
     change bit r (inputs.getD t zero)=bit (flipV r) (inputs.getD t zero)
     have hb1:=zZ ⟨t,ht9⟩ r
     have hb2:=zZ ⟨t,ht9⟩ (flipV r)
     change bit r (inputs.getD (⟨t,ht9⟩ : Fin 9).val zero)=_ at hb1
     change bit (flipV r) (inputs.getD (⟨t,ht9⟩ : Fin 9).val zero)=_ at hb2
     rw [hb1,hb2]
     exact (yN r ⟨t,ht9⟩ v (fun e=>htne (congrArg Fin.val e))).symm
   | succ m ih =>
     have hm_lt:m < C.size:=by omega
     have ih':=ih (by omega)
     rw [List.take_succ_eq_append_getElem hm_lt,zx]
     let gm:=C.gates.get ⟨m,hm_lt⟩
     let wm:=execute (C.gates.take m) inputs
     have hwm_len:wm.length=9 + m:=by
       simp [wm,zC,inputs,List.length_take_of_le (Nat.le_of_lt hm_lt)]
     intro t ht_lt ht_ne r
     change bit r ((wm ++ [gv wm gm]).getD t zero)=bit (flipV r) ((wm ++ [gv wm gm]).getD t zero)
     rcases Nat.lt_or_eq_of_le (show t ≤ 9 + m from by omega) with ht_old | rfl
     · rw [zb _ _ _ _ (by rw [hwm_len]; exact ht_old)]
       exact ih' t ht_old ht_ne r
     · rw [zB _ _ _ _ (by rw [hwm_len]),hwm_len,Nat.sub_self]
       simp only [List.getD_eq_getElem?_getD,List.getElem?_cons_zero,Option.getD_some]
       have hm_ne:(⟨m,hm_lt⟩ : Fin C.size) ≠ i:=by
         intro e
         have hmv:m=i.val:=congrArg Fin.val e
         omega
       have hv_not:v.val ∉ gm.inputs:=huniq ⟨m,hm_lt⟩ hm_ne
       have hgm_fan:gm.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp):=(hmin.1 gm (C.gates.get_mem _)).1
       have harg:gm.inputs.map (fun p=>(wm.map (bit r)).getD p false) =
                   gm.inputs.map (fun p=>(wm.map (bit (flipV r))).getD p false):=by
         apply List.map_congr_left
         intro p hp
         simp only [z233]
         have hp_lt:=(hnorm ⟨m,hm_lt⟩).1 p hp
         exact ih' p hp_lt (fun he=>hv_not (he ▸ hp)) r
       rw [wH r gm wm hgm_fan,wH (flipV r) gm wm hgm_fan,harg]
 have hw_agree (r:Row):bit r wv=bit (flipV r) wv:=by
   have hW_split:execute C.gates inputs=execute (C.gates.drop i.val) (execute (C.gates.take i.val) inputs):=by
     conv_lhs=>rw [← List.take_append_drop i.val C.gates]
     exact zx _ _ _
   obtain ⟨tail,htail⟩:=zO (C.gates.drop i.val) (execute (C.gates.take i.val) inputs)
   have hlen_i:(execute (C.gates.take i.val) inputs).length=9 + i.val:=by
     simp [zC,inputs,List.length_take_of_le (Nat.le_of_lt i.isLt)]
   have heqw:wv=(execute (C.gates.take i.val) inputs).getD w zero:=by
     change W.getD w zero=_
     rw [show W=execute C.gates inputs from rfl,hW_split,htail,zb _ _ _ _ (by rw [hlen_i]; exact hw_lt)]
   rw [heqw]
   exact hindep i.val (Nat.le_refl _) w hw_lt hw_ne r
 have hprop_ge_at (r:Row) (hwt' : bit r wv=true) :
     ∀ m,i.val < m → m ≤ C.size → ∀ t < 9 + m,t ≠ v.val →
       bit r ((execute (C.gates.take m) inputs).getD t zero) =
       bit (flipV r) ((execute (C.gates.take m) inputs).getD t zero):=by
   have hwf:bit (flipV r) wv=true:=(hw_agree r).symm.trans hwt'
   intro m him
   induction m with
   | zero=>omega
   | succ m ih =>
     intro hm_le
     have hm_lt:m < C.size:=by omega
     rw [List.take_succ_eq_append_getElem hm_lt,zx]
     let gm:=C.gates.get ⟨m,hm_lt⟩
     let wm:=execute (C.gates.take m) inputs
     have hwm_len:wm.length=9 + m:=by
       simp [wm,zC,inputs,List.length_take_of_le (Nat.le_of_lt hm_lt)]
     by_cases hmi:m=i.val
     · subst m
       intro t ht_lt ht_ne
       change bit r ((wm ++ [gv wm gm]).getD t zero)=bit (flipV r) ((wm ++ [gv wm gm]).getD t zero)
       rcases Nat.lt_or_eq_of_le (show t ≤ 9 + i.val from by omega) with ht_old | rfl
       · rw [zb _ _ _ _ (by rw [hwm_len]; exact ht_old)]
         exact hindep i.val (Nat.le_refl _) t ht_old ht_ne r
       · rw [zB _ _ _ _ (by rw [hwm_len]),hwm_len,Nat.sub_self]
         simp only [List.getD_eq_getElem?_getD,List.getElem?_cons_zero,Option.getD_some]
         have hW_split' : execute C.gates inputs=execute (C.gates.drop i.val) (execute (C.gates.take i.val) inputs):=by
           conv_lhs=>rw [← List.take_append_drop i.val C.gates]
           exact zx _ _ _
         obtain ⟨tail,htail⟩:=zO (C.gates.drop i.val) wm
         have hwi_w:wm.getD w zero=wv:=by
           change _=W.getD w zero
           rw [show W=execute C.gates inputs from rfl,hW_split']
           change _=(execute (C.gates.drop i.val) wm).getD w zero
           rw [htail,zb _ _ _ _ (by rw [hwm_len]; exact hw_lt)]
         have hd1:(if jp gm.op then 0 else 1)=1:=by
           have hgm:gm.op=GateOp.or:=hor
           rw [hgm]
           rfl
         have hgv_side (q:Row) (hq:bit q wv=true):bit q (gv wm gm)=true:=by
           have hbo (x y:Sig):bit q (bin 1 x y)=(bit q x||bit q y):=BitVec.getLsbD_or
           rcases hinp with hvw | hwv
           · rw [j0 wm gm v.val w hvw (Or.inr hor),hd1,hbo,hwi_w,hq]
             simp
           · rw [j0 wm gm w v.val hwv (Or.inr hor),hd1,hbo,hwi_w,hq]
             simp
         rw [hgv_side r hwt',hgv_side (flipV r) hwf]
     · have ih':=ih (by omega) (by omega)
       intro t ht_lt ht_ne
       change bit r ((wm ++ [gv wm gm]).getD t zero)=bit (flipV r) ((wm ++ [gv wm gm]).getD t zero)
       rcases Nat.lt_or_eq_of_le (show t ≤ 9 + m from by omega) with ht_old | rfl
       · rw [zb _ _ _ _ (by rw [hwm_len]; exact ht_old)]
         exact ih' t ht_old ht_ne
       · rw [zB _ _ _ _ (by rw [hwm_len]),hwm_len,Nat.sub_self]
         simp only [List.getD_eq_getElem?_getD,List.getElem?_cons_zero,Option.getD_some]
         have hm_ne:(⟨m,hm_lt⟩ : Fin C.size) ≠ i:=by intro e; exact hmi (congrArg Fin.val e)
         have hv_not:v.val ∉ gm.inputs:=huniq ⟨m,hm_lt⟩ hm_ne
         have hgm_fan:gm.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp):=(hmin.1 gm (C.gates.get_mem _)).1
         have harg:gm.inputs.map (fun p=>(wm.map (bit r)).getD p false) =
                     gm.inputs.map (fun p=>(wm.map (bit (flipV r))).getD p false):=by
           apply List.map_congr_left
           intro p hp
           simp only [z233]
           have hp_lt:=(hnorm ⟨m,hm_lt⟩).1 p hp
           exact ih' p hp_lt (fun he=>hv_not (he ▸ hp))
         rw [wH r gm wm hgm_fan,wH (flipV r) gm wm hgm_fan,harg]
 have hforb:(wv &&& zI v.val)=zero:=by
   apply zF
   intro r
   rw [zv,show bit r (wv &&& zI v.val)=(bit r wv&&bit r (zI v.val)) from BitVec.getLsbD_and]
   cases hm_bit:bit r (zI v.val)
   · simp
   · suffices bit r wv=false by simp [this]
     by_contra hwt
     have hwt' : bit r wv=true:=Bool.eq_true_of_not_eq_false hwt
     obtain ⟨_,hg0,hg1⟩:=y1 v hv r hm_bit
     have hgoalEq:W.getD C.output zero=graph:=by
       apply zF
       intro q
       exact (vr C hmin.1 C.output q).trans ((congrFun hfun (sample q)).trans (z123 q).symm)
     have hout_ne:C.output ≠ v.val:=by
       intro heq_out
       obtain ⟨q,hq⟩:=j2 v
       obtain ⟨tail,hW⟩:=zO C.gates inputs
       have hin_v:W.getD v.val zero=inputs.getD v.val zero:=by
         change (execute C.gates inputs).getD v.val zero=_
         rw [hW]
         exact zb _ _ _ _ (by simp [inputs])
       rw [← hgoalEq,heq_out,hin_v] at hq
       exact hq rfl
     have h_agree_all:bit r (W.getD C.output zero)=bit (flipV r) (W.getD C.output zero):=by
       by_cases hlt:C.output < 9 + C.size
       · have heqC:=hprop_ge_at r hwt' C.size i.isLt (Nat.le_refl _) C.output hlt hout_ne
         simpa [W,Circuit.size,List.take_length] using heqC
       · have hlenW:W.length ≤ C.output:=by
           have:=zC C.gates inputs
           change (execute C.gates inputs).length ≤ C.output
           rw [zC]
           simp [Circuit.size,inputs] at hlt ⊢
           omega
         simp [List.getD_eq_getElem?_getD,List.getElem?_eq_none hlenW,zv]
     have hflip_eq:flipV r=Fin.ofNat 512 (r.val ^^^ (1 <<< v.val)) :=
       Fin.ext (by simp [flipV,Nat.mod_eq_of_lt (vp r v)])
     rw [hgoalEq,hflip_eq,hg0,hg1] at h_agree_all
     exact Bool.noConfusion h_agree_all
 have hno_alias : ∀ t < 9 + C.size,t ≠ v.val → nrm true (W.getD t zero) ≠ inputs.getD v.val zero:=by
   intro t ht ht_ne heq
   have nrm_flip_diff (r:Row) (x:Sig) (hx:nrm true x=inputs.getD v.val zero) :
       bit r x ≠ bit (flipV r) x:=by
     have hbit_in (q:Row):bit q (inputs.getD v.val zero)=q.val.testBit v.val:=zZ v q
     have hdiff_in:bit r (inputs.getD v.val zero) ≠ bit (flipV r) (inputs.getD v.val zero):=by
       rw [hbit_in r,hbit_in (flipV r)]
       change r.val.testBit v.val ≠ (r.val ^^^ (1 <<< v.val)).testBit v.val
       rw [Nat.testBit_xor,Nat.shiftLeft_eq,Nat.one_mul,Nat.testBit_two_pow]
       simp
     have hcases:x=inputs.getD v.val zero ∨ x=neg (inputs.getD v.val zero):=by
       unfold nrm at hx
       split at hx
       · right; rw [← hx,neg_neg']
       · left; exact hx
     rcases hcases with rfl | rfl
     · exact hdiff_in
     · rw [je,je]
       intro hc
       exact hdiff_in (Bool.not_inj hc)
   by_cases ht_early:t < 9 + i.val
   · have hW_split:W=execute (C.gates.drop i.val) (execute (C.gates.take i.val) inputs):=by
       change execute C.gates inputs=_
       conv_lhs=>rw [← List.take_append_drop i.val C.gates]
       exact zx _ _ _
     obtain ⟨tail,htail⟩:=zO (C.gates.drop i.val) (execute (C.gates.take i.val) inputs)
     have hlen_i:(execute (C.gates.take i.val) inputs).length=9 + i.val:=by
       simp [zC,inputs,List.length_take_of_le (Nat.le_of_lt i.isLt)]
     have hWt:W.getD t zero=(execute (C.gates.take i.val) inputs).getD t zero:=by
       rw [hW_split,htail,zb _ _ _ _ (by rw [hlen_i]; exact ht_early)]
     have hag:=hindep i.val (Nat.le_refl _) t ht_early ht_ne 0
     rw [← hWt] at hag
     exact nrm_flip_diff 0 (W.getD t zero) heq hag
   · have hwv_ne:wv ≠ zero:=by
       intro hwvz
       have hW_split:W=execute (C.gates.drop (i.val + 1)) (execute (C.gates.take (i.val + 1)) inputs):=by
         change execute C.gates inputs=_
         conv_lhs=>rw [← List.take_append_drop (i.val + 1) C.gates]
         exact zx _ _ _
       obtain ⟨tail,htail⟩:=zO (C.gates.drop (i.val + 1)) (execute (C.gates.take (i.val + 1)) inputs)
       have htake1:C.gates.take (i.val + 1)=C.gates.take i.val ++ [C.gates.get i] :=
         List.take_succ_eq_append_getElem i.isLt
       let wm:=execute (C.gates.take i.val) inputs
       have hwm_len:wm.length=9 + i.val:=by
         simp [wm,zC,inputs,List.length_take_of_le (Nat.le_of_lt i.isLt)]
       have hW_split' : W=execute (C.gates.drop i.val) wm:=by
         change execute C.gates inputs=_
         conv_lhs=>rw [← List.take_append_drop i.val C.gates]
         exact zx _ _ _
       obtain ⟨tail',htail'⟩:=zO (C.gates.drop i.val) wm
       have hv_wm:wm.getD v.val zero=inputs.getD v.val zero:=by
         obtain ⟨l,hl⟩:=zO (C.gates.take i.val) inputs
         change _=inputs.getD v.val zero
         rw [show wm=execute (C.gates.take i.val) inputs from rfl,hl]
         exact zb _ _ _ _ (by simp [inputs])
       have hw_wm:wm.getD w zero=zero:=by
         have h1:wm.getD w zero=W.getD w zero:=by
           rw [hW_split',htail',zb _ _ _ _ (by rw [hwm_len]; exact hw_lt)]
         exact h1.trans hwvz
       have hgv_eq:gv wm (C.gates.get i)=inputs.getD v.val zero:=by
         have hd1:(if jp (C.gates.get i).op then 0 else 1)=1:=by rw [hor]; rfl
         apply zF
         intro r
         rcases hinp with hvw | hwv
         · rw [j0 wm (C.gates.get i) v.val w hvw (Or.inr hor),hd1,zX,hv_wm,hw_wm,zv]; simp
         · rw [j0 wm (C.gates.get i) w v.val hwv (Or.inr hor),hd1,zX,hv_wm,hw_wm,zv]; simp
       have hstep_i:execute (C.gates.take (i.val + 1)) inputs=wm ++ [gv wm (C.gates.get i)]:=by
         rw [htake1,zx]; rfl
       have hstep_len:(execute (C.gates.take (i.val + 1)) inputs).length=9 + i.val + 1:=by
         rw [hstep_i,List.length_append,List.length_singleton,hwm_len]
       have hW_at_i:W.getD (9 + i.val) zero=inputs.getD v.val zero:=by
         rw [hW_split,htail,zb _ _ _ _ (by rw [hstep_len]; omega),
           hstep_i,zB _ _ _ _ (by rw [hwm_len]),hwm_len,Nat.sub_self]
         simpa using hgv_eq
       have hW_at_v:W.getD v.val zero=inputs.getD v.val zero:=by
         obtain ⟨l,hl⟩:=zO C.gates inputs
         change (execute C.gates inputs).getD v.val zero=_
         rw [hl]
         exact zb _ _ _ _ (by simp [inputs])
       have hlenW:W.length=9 + C.size:=by
         simpa [W,inputs,Circuit.size] using zC C.gates inputs
       have hv_ltW:v.val < W.length:=by rw [hlenW]; have:=v.isLt; omega
       have hi_ltW:9 + i.val < W.length:=by rw [hlenW]; have:=i.isLt; omega
       have hgel:W[v.val]'hv_ltW=W[9 + i.val]'hi_ltW:=by
         simpa [List.getD_eq_getElem?_getD,hv_ltW,hi_ltW] using hW_at_v.trans hW_at_i.symm
       have heqv:v.val=9 + i.val:=congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hndW)
         (show (fun k:Fin W.length=>W[k.val]) ⟨v.val,hv_ltW⟩ =
           (fun k:Fin W.length=>W[k.val]) ⟨9 + i.val,hi_ltW⟩ from hgel))
       have:=v.isLt
       omega
     have ex_r0 : ∃ r0:Row,bit r0 wv=true:=by
       by_contra hnone
       push Not at hnone
       apply hwv_ne
       apply zF
       intro r
       rw [zv]
       exact Bool.eq_false_iff.mpr (hnone r)
     obtain ⟨r0,hr0⟩:=ex_r0
     have hag:=hprop_ge_at r0 hr0 C.size i.isLt (Nat.le_refl _) t ht ht_ne
     simp only [W,Circuit.size,List.take_length] at hag
     exact nrm_flip_diff r0 (W.getD t zero) heq hag
 exact ⟨hforb,hno_alias,hw_agree⟩
theorem yY (C:Circuit) (hmin:PEqualNP.MetaComplexity.IsMinimalCircuit 9 C)
   (hfun:PEqualNP.MetaComplexity.circuitFun 9 C=edge)
   (hGate : ∀ i:Fin C.size,(C.gates.get i).inputs.length=2 ∧
     (∀ w ∈ (C.gates.get i).inputs,w < 9 + i.val) ∧
     ((C.gates.get i).op=GateOp.and ∨ (C.gates.get i).op=GateOp.or))
   (hndW:(execute C.gates inputs).Nodup)
   (hnorm : ∀ i:Fin C.size,
     (∀ w ∈ (C.gates.get i).inputs,w < 9 + i.val) ∧
     (C.gates.get i).inputs.Nodup ∧
     ((C.gates.get i).op=GateOp.not ∧ (C.gates.get i).inputs.length=1 ∨
      (C.gates.get i).op ≠ GateOp.not ∧ (C.gates.get i).inputs.length=2))
   (v:Fin 9) (hv:v ∈ ([4,6,7]:List (Fin 9))) (i:Fin C.size) (w:Nat)
   (hw_lt:w < 9 + i.val) (hw_ne:w ≠ v.val) (hor:(C.gates.get i).op=GateOp.or)
   (hinp:(C.gates.get i).inputs=[v.val,w] ∨ (C.gates.get i).inputs=[w,v.val])
   (huniq : ∀ k:Fin C.size,k ≠ i → v.val ∉ (C.gates.get k).inputs) :
   let wv:=(execute C.gates inputs).getD w zero
   wv ∉ inputs ∧ (wv &&& unitMask)=zero ∧ (wv &&& zI v.val)=zero:=by
 let W:=execute C.gates inputs
 let wv:=W.getD w zero
 let flipV (r:Row):Row := ⟨r.val ^^^ (1 <<< v.val),vp r v⟩
 obtain ⟨hforb,-,hw_agree⟩:=qX C hmin hfun hnorm hndW v hv i w hw_lt hw_ne hor hinp huniq
 have hunit:(wv &&& unitMask)=zero:=by
   apply zF
   intro r
   rw [zv,show bit r (wv &&& unitMask)=(bit r wv&&bit r unitMask) from BitVec.getLsbD_and]
   cases hu_bit:bit r unitMask
   · simp
   · suffices bit r wv=false by simp [this]
     by_contra hwt
     have hwt' : bit r wv=true:=Bool.eq_true_of_not_eq_false hwt
     have hur:=yh r ▸ hu_bit
     simp only [List.any_eq_true,List.mem_finRange,decide_eq_true_eq,true_and] at hur
     obtain ⟨u,hr_val⟩:=hur
     have hw_mem:wv ∈ W:=by
       have hlenW:w < W.length:=by
         have:=i.isLt
         change w < (execute C.gates inputs).length
         rw [zC]
         simp [Circuit.size,inputs] at this ⊢
         omega
       change W.getD w zero ∈ W
       simp [List.getD_eq_getElem?_getD,hlenW]
     have hprops:=vC C hGate C.size (Nat.le_refl _) wv (by simpa [W,Circuit.size,List.take_length] using hw_mem)
     by_cases huv:u=v
     · subst u
       have hr_eq:r=flipV ⟨0,by decide⟩:=Fin.ext (by simp [flipV,hr_val])
       have hw0:=hw_agree ⟨0,by decide⟩
       rw [hr_eq,← hw0] at hwt'
       change bit (0:Row) wv=true at hwt'
       rw [hprops.1] at hwt'
       exact Bool.noConfusion hwt'
     · obtain ⟨r',hrm,hr_sub⟩:=wb v hv u huv
       have hr_le:r.val &&& r'.val=r.val:=by rw [hr_val,Nat.and_comm]; exact hr_sub
       have hr'_true:=hprops.2.2 r r' hr_le hwt'
       have hz:=congrArg (bit r') hforb
       rw [show bit r' (wv &&& zI v.val)=(bit r' wv&&bit r' (zI v.val)) from BitVec.getLsbD_and,
         zv,hr'_true,hrm] at hz
       exact Bool.noConfusion hz
 have hnot_in:wv ∉ inputs:=by
   intro hm
   obtain ⟨u,hu,heq⟩:=List.getElem_of_mem hm
   have hu9:u < 9:=by simpa [inputs] using hu
   let r0:Row:=Fin.ofNat 512 (1 <<< u)
   have hb1:bit r0 wv=true:=by
     have hwu:wv=inputs.getD u zero:=by rw [← heq,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hu]; rfl
     rw [hwu]
     exact yw ⟨u,hu9⟩
   have hb2:bit r0 unitMask=true:=z229 ⟨u,hu9⟩
   have hz:=congrArg (bit r0) hunit
   rw [show bit r0 (wv &&& unitMask)=(bit r0 wv&&bit r0 unitMask) from BitVec.getLsbD_and,
     zv,hb1,hb2] at hz
   exact Bool.noConfusion hz
 exact ⟨hnot_in,hunit,hforb⟩
theorem z386 (C:Circuit) (hmin:PEqualNP.MetaComplexity.IsMinimalCircuit 9 C)
   (hfun:PEqualNP.MetaComplexity.circuitFun 9 C=edge)
   (hnorm : ∀ i:Fin C.size,
     (∀ w ∈ (C.gates.get i).inputs,w < 9 + i.val) ∧
     (C.gates.get i).inputs.Nodup ∧
     ((C.gates.get i).op=GateOp.not ∧ (C.gates.get i).inputs.length=1 ∨
      (C.gates.get i).op ≠ GateOp.not ∧ (C.gates.get i).inputs.length=2))
   (hS : ∀ v:Fin 9,v ∈ ([4,6,7]:List (Fin 9)) →
     ({i:Fin C.size | v.val ∈ (C.gates.get i).inputs} : Finset (Fin C.size)).card=1 ∧
     ∀ i ∈ ({i:Fin C.size | v.val ∈ (C.gates.get i).inputs} : Finset (Fin C.size)),(C.gates.get i).op=GateOp.or)
   (hndW:(execute C.gates inputs).Nodup)
   (hGate : ∀ i:Fin C.size,(C.gates.get i).inputs.length=2 ∧
     (∀ w ∈ (C.gates.get i).inputs,w < 9 + i.val) ∧
     ((C.gates.get i).op=GateOp.and ∨ (C.gates.get i).op=GateOp.or)) :
   ∀ gs pref:List Gate,pref ++ gs=C.gates →
     graph ∈ execute gs (execute pref inputs) →
     ∃ k S,k ≤ gs.length ∧ Live467 false graph k S ∧ (∀ a ∈ S,a ∈ execute pref inputs) ∧
       ∀ v ∈ ([4,6,7]:List (Fin 9)),inputs.getD v.val zero ∈ S → ∃ j:Fin gs.length,v.val ∈ (gs.get j).inputs:=by
 intro gs
 induction gs with
 | nil =>
   intro pref _ hmem
   change graph ∈ execute [] (execute pref inputs) at hmem
   change graph ∈ execute pref inputs at hmem
   refine ⟨0,{graph},by omega,Live467.stop jB,fun a ha=>?_,fun v _ hvS=>?_⟩
   · simpa [Finset.mem_singleton.mp ha] using hmem
   · simp only [Finset.mem_singleton] at hvS
     obtain ⟨r,hr⟩:=j2 v
     exact False.elim (hr (congrArg (bit r) hvS.symm))
 | cons g gs ih =>
   intro pref hsplit hmem
   let m:=pref.length
   have hm_lt:m < C.size:=by
     have:=congrArg List.length hsplit
     simp only [Circuit.size,List.length_append,List.length_cons] at this ⊢
     omega
   have hpref_take:pref=C.gates.take m:=by
     have h:=congrArg (List.take m) hsplit
     simpa [m,List.take_left] using h
   have hg_eq:g=C.gates.get ⟨m,hm_lt⟩:=by
     have h:=congrArg (fun l=>l[m]?) hsplit
     have hg1:(pref ++ g :: gs)[m]? = some g:=by simp [m]
     have hg2:C.gates[m]? = some (C.gates.get ⟨m,hm_lt⟩):=by simp [hm_lt]
     rw [hg1,hg2] at h
     exact Option.some.inj h
   let pref':=pref ++ [g]
   have hsplit' : pref' ++ gs=C.gates:=by simpa [pref',List.append_assoc] using hsplit
   have hexec' : execute pref' inputs=execute pref inputs ++ [gv (execute pref inputs) g]:=by
     simp [pref',zx,execute]
   have hmem' : graph ∈ execute gs (execute pref' inputs):=by
     rw [hexec']
     exact hmem
   obtain ⟨k,S,hk,hlive,hsub,h4⟩:=ih pref' hsplit' hmem'
   rw [hexec'] at hsub
   let wm:=execute pref inputs
   let z:=gv wm g
   by_cases hzS:z ∈ S
   · obtain ⟨tail,hW⟩ : ∃ tail,execute C.gates inputs=wm ++ ([z] ++ tail):=by
       have hst:execute C.gates inputs=execute gs (wm ++ [z]):=by
         rw [← hsplit,zx]
         rfl
       obtain ⟨tail,ht⟩:=zO gs (wm ++ [z])
       exact ⟨tail,by rw [hst,ht,List.append_assoc]⟩
     have hnd_wm:wm.Nodup:=(List.nodup_append.mp (hW ▸ hndW)).1
     have hz_not_wm:z ∉ wm:=fun hm=>(List.nodup_append.mp (hW ▸ hndW)).2.2 z hm z List.mem_cons_self rfl
     have wm_len:wm.length=9 + m:=by simp [wm,zC,inputs,m]
     have hwm_ext : ∃ l,wm=inputs ++ l:=zO pref inputs
     have idx_of_input (idx:Nat) (hidx:idx < wm.length) (v:Fin 9)
         (heq:wm.getD idx zero=inputs.getD v.val zero):idx=v.val:=by
       obtain ⟨l,hl⟩:=hwm_ext
       have hv_lt:v.val < wm.length:=by rw [wm_len]; have:=v.isLt; omega
       have hin_wm:wm.getD v.val zero=inputs.getD v.val zero:=by
         rw [hl]; exact zb _ _ _ _ (by simp [inputs])
       rw [← hin_wm] at heq
       have hgi:wm[idx]'hidx=wm[v.val]'hv_lt:=by
         simpa [List.getD_eq_getElem?_getD,hidx,hv_lt] using heq
       exact congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hnd_wm)
         (show (fun k:Fin wm.length=>wm[k.val]) ⟨idx,hidx⟩ =
           (fun k:Fin wm.length=>wm[k.val]) ⟨v.val,hv_lt⟩ from hgi))
     obtain ⟨hlen2,hltm,hop⟩:=hg_eq ▸ hGate ⟨m,hm_lt⟩
     have hg_nd:g.inputs.Nodup:=hg_eq ▸ (hnorm ⟨m,hm_lt⟩).2.1
     obtain ⟨ia,ib,hinp⟩:=List.length_eq_two.mp hlen2
     have hia_ne_ib:ia ≠ ib:=by simpa [hinp] using hg_nd
     have hia_lt:ia < wm.length:=by rw [wm_len]; exact hltm ia (by simp [hinp])
     have hib_lt:ib < wm.length:=by rw [wm_len]; exact hltm ib (by simp [hinp])
     let d:=if jp g.op then 0 else 1
     let a:=wm.getD ia zero
     let b:=wm.getD ib zero
     have hz_bin:z=bin d a b:=j0 wm g ia ib hinp hop
     have hd:allowed false d:=by dsimp [d]; split<;>exact Or.inl (by omega)
     have ha_mem:a ∈ wm:=by change wm.getD ia zero ∈ wm; simp [List.getD_eq_getElem?_getD,hia_lt]
     have hb_mem:b ∈ wm:=by change wm.getD ib zero ∈ wm; simp [List.getD_eq_getElem?_getD,hib_lt]
     have hw_props : ∀ w ∈ wm,bit 0 w=false ∧ bit ⟨511,by decide⟩ w=true ∧
         ∀ r s:Row,(r.val &&& s.val=r.val) → bit r w=true → bit s w=true:=by
       simpa [wm,hpref_take] using vC C hGate m (Nat.le_of_lt hm_lt)
     have ha_p:proper a:=ve a (hw_props a ha_mem).1 (hw_props a ha_mem).2.1
     have hb_p:proper b:=ve b (hw_props b hb_mem).1 (hw_props b hb_mem).2.1
     have hab:a ≠ b:=by
       intro hab_eq
       have hgi:wm[ia]'hia_lt=wm[ib]'hib_lt:=by
         simpa [a,b,List.getD_eq_getElem?_getD,hia_lt,hib_lt] using hab_eq
       exact hia_ne_ib (congrArg Fin.val ((List.nodup_iff_injective_getElem.mp hnd_wm)
         (show (fun k:Fin wm.length=>wm[k.val]) ⟨ia,hia_lt⟩ =
           (fun k:Fin wm.length=>wm[k.val]) ⟨ib,hib_lt⟩ from hgi)))
     let U:=S.erase z
     have hU_sub : ∀ y ∈ U,y ∈ wm:=by
       intro y hy
       obtain ⟨hne,hyS⟩:=Finset.mem_erase.mp hy
       rcases List.mem_append.mp (hsub y hyS) with hyw | hyz
       · exact hyw
       · exact False.elim (hne (by simpa using hyz))
     have hfresh:bin d a b ∉ insert a (insert b U):=by
       rw [← hz_bin]
       intro hm_in
       rcases Finset.mem_insert.mp hm_in with e | hm_in
       · exact hz_not_wm (e ▸ ha_mem)
       · rcases Finset.mem_insert.mp hm_in with e | hm_in
         · exact hz_not_wm (e ▸ hb_mem)
         · exact hz_not_wm (hU_sub _ hm_in)
     have check_side (ix iy:Nat) (hix:ix < wm.length) (hiy:iy < wm.length)
         (hne_i:ix ≠ iy) (hinp_pair:g.inputs=[ix,iy] ∨ g.inputs=[iy,ix]) :
         let x:=wm.getD ix zero
         let y:=wm.getD iy zero
         q7 false x y (if ix == ia then d else qm d) (decide (x ∈ U))=true:=by
       intro x y
       by_cases hx467:qH x=true
       · have hvx : ∃ v:Fin 9,v ∈ ([4,6,7]:List (Fin 9)) ∧ x=inputs.getD v.val zero:=by
           simp only [qH,in4,in6,in7,Bool.or_eq_true,beq_iff_eq] at hx467
           rcases hx467 with (e | e) | e
           · exact ⟨4,by simp,e⟩
           · exact ⟨6,by simp,e⟩
           · exact ⟨7,by simp,e⟩
         obtain ⟨v,hv,hxv⟩:=hvx
         have hix_eq:ix=v.val:=idx_of_input ix hix v hxv
         have hv_mem_g:v.val ∈ (C.gates.get ⟨m,hm_lt⟩).inputs:=by
           rw [← hg_eq,← hix_eq]
           rcases hinp_pair with h1 | h2
           · simp [h1]
           · simp [h2]
         obtain ⟨hcard1,hall_or⟩:=hS v hv
         let readers:Finset (Fin C.size):=Finset.univ.filter fun j=>v.val ∈ (C.gates.get j).inputs
         have hmem_r:(⟨m,hm_lt⟩ : Fin C.size) ∈ readers:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv_mem_g⟩
         have hreaders_eq:readers = {⟨m,hm_lt⟩}:=by
           obtain ⟨r0,hr0⟩:=Finset.card_eq_one.mp hcard1
           have hm0:(⟨m,hm_lt⟩ : Fin C.size)=r0:=Finset.mem_singleton.mp (hr0 ▸ hmem_r)
           exact hm0 ▸ hr0
         have hor_m:(C.gates.get ⟨m,hm_lt⟩).op=GateOp.or:=hall_or ⟨m,hm_lt⟩ hmem_r
         have hd1:d=1:=by dsimp [d]; rw [hg_eq,hor_m]; rfl
         have hfd1:(if ix == ia then d else qm d)=1:=by split<;>simp [hd1,qm]
         have huniq : ∀ k:Fin C.size,k ≠ ⟨m,hm_lt⟩ → v.val ∉ (C.gates.get k).inputs:=by
           intro k hne hmemk
           have : k ∈ readers:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,hmemk⟩
           rw [hreaders_eq,Finset.mem_singleton] at this
           exact hne this
         have hx_not_U:x ∉ U:=by
           intro hxU
           have hxS:inputs.getD v.val zero ∈ S:=hxv ▸ Finset.mem_of_mem_erase hxU
           obtain ⟨j,hj⟩:=h4 v hv hxS
           have hj_lt:m + 1 + j.val < C.size:=by
             have:=congrArg List.length hsplit
             simp only [Circuit.size,List.length_append,List.length_cons] at this ⊢
             omega
           have hj_eq:gs.get j=C.gates.get ⟨m + 1 + j.val,hj_lt⟩:=by
             have h:=congrArg (fun l=>l[m + 1 + j.val]?) hsplit
             have h1:(pref ++ g :: gs)[m + 1 + j.val]? = some (gs.get j):=by
               have hex_j:m + 1 + j.val=(pref ++ [g]).length + j.val:=by simp [m]
               rw [show pref ++ g :: gs=(pref ++ [g]) ++ gs by simp,hex_j,List.getElem?_append_right (by omega)]
               simp [j.isLt]
             have h2:C.gates[m + 1 + j.val]? = some (C.gates.get ⟨m + 1 + j.val,hj_lt⟩):=by simp [hj_lt]
             rw [h1,h2] at h
             exact Option.some.inj h
           have hv_later:v.val ∈ (C.gates.get ⟨m + 1 + j.val,hj_lt⟩).inputs:=hj_eq ▸ hj
           exact huniq ⟨m + 1 + j.val,hj_lt⟩ (by intro e; have : m + 1 + j.val=m:=congrArg Fin.val e; omega) hv_later
         have hiy_lt_m:iy < 9 + m:=by rw [← wm_len]; exact hiy
         have hiy_ne_v:iy ≠ v.val:=hix_eq ▸ hne_i.symm
         have hinp_v:(C.gates.get ⟨m,hm_lt⟩).inputs=[v.val,iy] ∨ (C.gates.get ⟨m,hm_lt⟩).inputs=[iy,v.val]:=by
           rw [← hg_eq,← hix_eq]; exact hinp_pair
         obtain ⟨hnot_in,hunit,hforb⟩:=yY C hmin hfun hGate hndW hnorm v hv ⟨m,hm_lt⟩ iy hiy_lt_m hiy_ne_v hor_m hinp_v huniq
         have hy_eq_W:y=(execute C.gates inputs).getD iy zero:=by
           change wm.getD iy zero=_; rw [hW,zb _ _ _ _ hiy]
         have hmask_x:zr x=zI v.val:=by rw [hxv]; exact wh v hv
         have hx_dec:decide (x ∈ U)=false:=decide_eq_false hx_not_U
         simp only [q7,hx467,↓reduceIte,hfd1,beq_self_eq_true,Bool.false_eq_true,hx_dec,Bool.not_false,
           Bool.true_and,qZ,List.contains_eq_mem,decide_eq_true_eq,hy_eq_W,hnot_in,decide_false,
           hmask_x,hunit,hforb]
       · simp [q7,hx467]
     have hok:wK false U a b d:=by
       unfold wK zy
       rw [Bool.and_eq_true]
       refine ⟨?_,?_⟩
       · have hs:=check_side ia ib hia_lt hib_lt hia_ne_ib (Or.inl hinp)
         simp only [beq_self_eq_true,↓reduceIte] at hs
         exact hs
       · have hs:=check_side ib ia hib_lt hia_lt hia_ne_ib.symm (Or.inr hinp)
         have hne_ba:(ib == ia)=false:=beq_false_of_ne hia_ne_ib.symm
         simp only [hne_ba,Bool.false_eq_true,↓reduceIte] at hs
         exact hs
     have hlive_new:Live467 false graph (k + 1) (insert a (insert b U)):=by
       refine Live467.binary hd hok ha_p hb_p hab hfresh ?_
       dsimp only [U]
       rw [← hz_bin,Finset.insert_erase hzS]
       exact hlive
     refine ⟨k + 1,insert a (insert b U),by change k + 1 ≤ gs.length + 1; omega,hlive_new,?_,fun v hv hv_in=>?_⟩
     · intro y hy
       rcases Finset.mem_insert.mp hy with rfl | hy
       · exact ha_mem
       · rcases Finset.mem_insert.mp hy with rfl | hy
         · exact hb_mem
         · exact hU_sub y hy
     · rcases Finset.mem_insert.mp hv_in with hv_a | hv_in
       · have hva:=idx_of_input ia hia_lt v hv_a.symm
         exact ⟨0,by simp [hinp,hva]⟩
       · rcases Finset.mem_insert.mp hv_in with hv_b | hv_in
         · have hvb:=idx_of_input ib hib_lt v hv_b.symm
           exact ⟨0,by simp [hinp,hvb]⟩
         · obtain ⟨j,hj⟩:=h4 v hv (Finset.mem_of_mem_erase hv_in)
           exact ⟨j.succ,hj⟩
   · refine ⟨k,S,?_,hlive,fun y hy=>?_,fun v hv hvS=>?_⟩
     · change k ≤ gs.length + 1; omega
     · rcases List.mem_append.mp (hsub y hy) with hyw | hyz
       · exact hyw
       · have hy_eq:y=z:=by simpa using hyz
         exact False.elim (hzS (hy_eq ▸ hy))
     · obtain ⟨j,hj⟩:=h4 v hv hvS
       exact ⟨j.succ,hj⟩
theorem q169 (op_or:Bool) (a_raw b_raw:Sig) :
   let d:=if op_or then
     (if bit 0 a_raw then (if bit 0 b_raw then 0 else 2) else (if bit 0 b_raw then 3 else 1))
   else
     (if bit 0 a_raw then (if bit 0 b_raw then 1 else 3) else (if bit 0 b_raw then 2 else 0))
   nrm true (if op_or then a_raw ||| b_raw else a_raw &&& b_raw)=bin d (nrm true a_raw) (nrm true b_raw):=by
 intro d
 apply zF
 intro r
 have hrm (x:Sig):bit r (nrm true x)=((bit 0 x) != bit r x):=by
   unfold nrm
   simp only [Bool.true_and]
   cases h0:bit 0 x<;>simp [h0,je]
 have hz0:bit 0 (if op_or then a_raw ||| b_raw else a_raw &&& b_raw) =
     (if op_or then bit 0 a_raw||bit 0 b_raw else bit 0 a_raw&&bit 0 b_raw):=by
   cases op_or<;>simp [bit,BitVec.getLsbD_or,BitVec.getLsbD_and]
 have hzr:bit r (if op_or then a_raw ||| b_raw else a_raw &&& b_raw) =
     (if op_or then bit r a_raw||bit r b_raw else bit r a_raw&&bit r b_raw):=by
   cases op_or<;>simp [bit,BitVec.getLsbD_or,BitVec.getLsbD_and]
 rw [hrm,hz0,hzr,zX,hrm,hrm]
 dsimp only [d]
 by_cases ha0:bit 0 a_raw=true<;>by_cases hb0:bit 0 b_raw=true <;>
   by_cases har:bit r a_raw=true<;>by_cases hbr:bit r b_raw=true <;>
   cases op_or<;>simp [ha0,hb0,har,hbr]
theorem jx (y m:Sig) (hz:(y &&& m)=zero) :
   ((neg y &&& m) == m)=true:=by
 rw [beq_iff_eq]
 apply zF
 intro r
 have h1:=congrArg (bit r) hz
 rw [zv,show bit r (y &&& m)=(bit r y&&bit r m) from BitVec.getLsbD_and] at h1
 rw [show bit r (neg y &&& m)=(bit r (neg y)&&bit r m) from BitVec.getLsbD_and,je]
 cases hy:bit r y<;>cases hm:bit r m<;>simp_all
theorem vD (C:Circuit) (hmin:PEqualNP.MetaComplexity.IsMinimalCircuit 9 C)
   (hfun:PEqualNP.MetaComplexity.circuitFun 9 C=edge)
   (hnorm : ∀ i:Fin C.size,
     (∀ w ∈ (C.gates.get i).inputs,w < 9 + i.val) ∧
     (C.gates.get i).inputs.Nodup ∧
     ((C.gates.get i).op=GateOp.not ∧ (C.gates.get i).inputs.length=1 ∨
      (C.gates.get i).op ≠ GateOp.not ∧ (C.gates.get i).inputs.length=2))
   (hS : ∀ v:Fin 9,v ∈ ([4,6,7]:List (Fin 9)) →
     ({i:Fin C.size | v.val ∈ (C.gates.get i).inputs} : Finset (Fin C.size)).card=1 ∧
     ∀ i ∈ ({i:Fin C.size | v.val ∈ (C.gates.get i).inputs} : Finset (Fin C.size)),(C.gates.get i).op=GateOp.or)
   (hndW:(execute C.gates inputs).Nodup)
   (v:Fin 9) (hv:v ∈ ([4,6,7]:List (Fin 9))) :
   ∃ (i:Fin C.size) (w:Nat),
     w < 9 + i.val ∧ w ≠ v.val ∧ (C.gates.get i).op=GateOp.or ∧
     ((C.gates.get i).inputs=[v.val,w] ∨ (C.gates.get i).inputs=[w,v.val]) ∧
     (∀ k:Fin C.size,k ≠ i → v.val ∉ (C.gates.get k).inputs) ∧
     ((execute C.gates inputs).getD w zero &&& zI v.val)=zero ∧
     ∀ t < 9 + C.size,t ≠ v.val → nrm true ((execute C.gates inputs).getD t zero) ≠ inputs.getD v.val zero:=by
 obtain ⟨hcard1,hall_or⟩:=hS v hv
 obtain ⟨i,hi_eq⟩:=Finset.card_eq_one.mp hcard1
 have hi_mem_set:i ∈ ({j:Fin C.size | v.val ∈ (C.gates.get j).inputs} : Finset (Fin C.size)):=hi_eq ▸ Finset.mem_singleton_self i
 have hi_mem:v.val ∈ (C.gates.get i).inputs:=by simpa using hi_mem_set
 have hor:(C.gates.get i).op=GateOp.or:=hall_or i (hi_eq ▸ Finset.mem_singleton_self i)
 have huniq : ∀ k:Fin C.size,k ≠ i → v.val ∉ (C.gates.get k).inputs:=by
   intro k hne hmk
   have hk_mem:k ∈ ({j:Fin C.size | v.val ∈ (C.gates.get j).inputs} : Finset (Fin C.size)):=by simpa using hmk
   rw [hi_eq,Finset.mem_singleton] at hk_mem
   exact hne hk_mem
 have hi_norm:=hnorm i
 have hlen2:(C.gates.get i).inputs.length=2:=by
   rcases hi_norm.2.2 with ⟨hn,_⟩ | ⟨_,hl⟩
   · rw [hor] at hn; cases hn
   · exact hl
 obtain ⟨p,q,hpq⟩:=List.length_eq_two.mp hlen2
 have hpq_ne:p ≠ q:=by simpa [hpq] using hi_norm.2.1
 have hvp:v.val=p ∨ v.val=q:=by simpa [hpq] using hi_mem
 rcases hvp with rfl | rfl
 · have res:=qX C hmin hfun hnorm hndW v hv i q (hi_norm.1 q (by simp [hpq])) hpq_ne.symm hor (Or.inl hpq) huniq
   exact ⟨i,q,hi_norm.1 q (by simp [hpq]),hpq_ne.symm,hor,Or.inl hpq,huniq,res.1,res.2.1⟩
 · have res:=qX C hmin hfun hnorm hndW v hv i p (hi_norm.1 p (by simp [hpq])) hpq_ne hor (Or.inr hpq) huniq
   exact ⟨i,p,hi_norm.1 p (by simp [hpq]),hpq_ne,hor,Or.inr hpq,huniq,res.1,res.2.1⟩
theorem z289 (C:Circuit) (hmin:PEqualNP.MetaComplexity.IsMinimalCircuit 9 C)
   (hfun:PEqualNP.MetaComplexity.circuitFun 9 C=edge)
   (hnorm : ∀ i:Fin C.size,
     (∀ w ∈ (C.gates.get i).inputs,w < 9 + i.val) ∧
     (C.gates.get i).inputs.Nodup ∧
     ((C.gates.get i).op=GateOp.not ∧ (C.gates.get i).inputs.length=1 ∨
      (C.gates.get i).op ≠ GateOp.not ∧ (C.gates.get i).inputs.length=2))
   (hS : ∀ v:Fin 9,v ∈ ([4,6,7]:List (Fin 9)) →
     ({i:Fin C.size | v.val ∈ (C.gates.get i).inputs} : Finset (Fin C.size)).card=1 ∧
     ∀ i ∈ ({i:Fin C.size | v.val ∈ (C.gates.get i).inputs} : Finset (Fin C.size)),(C.gates.get i).op=GateOp.or)
   (hndW:(execute C.gates inputs).Nodup) :
   ∀ gs pref:List Gate,pref ++ gs=C.gates →
     graph ∈ (execute gs (execute pref inputs)).map (nrm true) →
     ∃ k S,k ≤ gs.countP (fun g => !wV g) ∧ Live467 true graph k S ∧
       (∀ a ∈ S,a ∈ (execute pref inputs).map (nrm true)) ∧
       ∀ v ∈ ([4,6,7]:List (Fin 9)),inputs.getD v.val zero ∈ S → ∃ j:Fin gs.length,v.val ∈ (gs.get j).inputs:=by
 intro gs
 induction gs with
 | nil =>
   intro pref _ hmem
   change graph ∈ (execute [] (execute pref inputs)).map (nrm true) at hmem
   change graph ∈ (execute pref inputs).map (nrm true) at hmem
   refine ⟨0,{graph},by simp,Live467.stop jB,fun a ha=>?_,fun v _ hvS=>?_⟩
   · simpa [Finset.mem_singleton.mp ha] using hmem
   · simp only [Finset.mem_singleton] at hvS
     obtain ⟨r,hr⟩:=j2 v
     exact False.elim (hr (congrArg (bit r) hvS.symm))
 | cons g gs ih =>
   intro pref hsplit hmem
   let m:=pref.length
   have hm_lt:m < C.size:=by
     have:=congrArg List.length hsplit
     simp only [Circuit.size,List.length_append,List.length_cons] at this ⊢
     omega
   have hg_eq:g=C.gates.get ⟨m,hm_lt⟩:=by
     have h:=congrArg (fun l=>l[m]?) hsplit
     have hg1:(pref ++ g :: gs)[m]? = some g:=by simp [m]
     have hg2:C.gates[m]? = some (C.gates.get ⟨m,hm_lt⟩):=by simp [hm_lt]
     rw [hg1,hg2] at h
     exact Option.some.inj h
   let pref':=pref ++ [g]
   have hsplit' : pref' ++ gs=C.gates:=by simpa [pref',List.append_assoc] using hsplit
   have hexec' : execute pref' inputs=execute pref inputs ++ [gv (execute pref inputs) g]:=by
     simp [pref',zx,execute]
   have hmem' : graph ∈ (execute gs (execute pref' inputs)).map (nrm true):=by
     rw [hexec']
     exact hmem
   obtain ⟨k,S,hk,hlive,hsub,h4⟩:=ih pref' hsplit' hmem'
   rw [hexec',List.map_append,List.map_singleton] at hsub
   let wm:=execute pref inputs
   let z_raw:=gv wm g
   let z:=nrm true z_raw
   have wm_len:wm.length=9 + m:=by simp [wm,zC,inputs,m]
   have hW_prefix : ∃ tail,execute C.gates inputs=wm ++ tail:=by
     have hst:execute C.gates inputs=execute (g :: gs) wm:=by
       rw [← hsplit,zx]
     rw [hst]
     exact zO (g :: gs) wm
   obtain ⟨W_tail,hW_eq⟩:=hW_prefix
   by_cases hzw:z ∈ wm.map (nrm true)
   · refine ⟨k,S,?_,hlive,fun y hy=>?_,fun v hv hvS=>?_⟩
     · rw [List.countP_cons]; cases wV g<;>simp<;>omega
     · rcases List.mem_append.mp (hsub y hy) with hyw | hyz
       · exact hyw
       · have hy_eq:y=z:=by simpa using hyz
         exact hy_eq ▸ hzw
     · obtain ⟨j,hj⟩:=h4 v hv hvS
       exact ⟨j.succ,hj⟩
   · by_cases hzS:z ∈ S
     · have hnot_not:g.op ≠ GateOp.not:=by
         intro hnot
         have hln:=hg_eq ▸ (hnorm ⟨m,hm_lt⟩).2.2
         rcases hln with ⟨_,hl1⟩ | ⟨hne,_⟩
         · rcases hg1:g.inputs with _ | ⟨ia,rest⟩
           · simp [hg1] at hl1
           · cases rest with
             | cons _ _=>simp [hg1] at hl1
             | nil =>
               have hia_lt:ia < wm.length:=by
                 rw [wm_len]; exact (hg_eq ▸ (hnorm ⟨m,hm_lt⟩).1) ia (by simp [hg1])
               have hia_mem:wm.getD ia zero ∈ wm:=by
                 change wm.getD ia zero ∈ wm; simp [List.getD_eq_getElem?_getD,hia_lt]
               have hgv_not:z_raw=neg (wm.getD ia zero):=by
                 simp [z_raw,gv,hnot,hg1]
               have hz_eq:z=nrm true (wm.getD ia zero):=by
                 change nrm true z_raw=_; rw [hgv_not,q117]
               exact hzw (hz_eq ▸ List.mem_map_of_mem hia_mem)
         · exact hne hnot
       have hfan:=hmin.1 g (hg_eq ▸ C.gates.get_mem ⟨m,hm_lt⟩)
       have hor_and:g.op=GateOp.and ∨ g.op=GateOp.or:=by
         rcases hfan.1 with h1 | h2 | h3
         · exact Or.inl h1
         · exact Or.inr h2
         · exact absurd h3 hnot_not
       have hlen2:g.inputs.length=2:=by
         rcases hg_eq ▸ (hnorm ⟨m,hm_lt⟩).2.2 with ⟨hn,_⟩ | ⟨_,hl2⟩
         · exact absurd hn hnot_not
         · exact hl2
       have hg_nd:g.inputs.Nodup:=hg_eq ▸ (hnorm ⟨m,hm_lt⟩).2.1
       obtain ⟨ia,ib,hinp⟩:=List.length_eq_two.mp hlen2
       have hia_ne_ib:ia ≠ ib:=by simpa [hinp] using hg_nd
       have hia_lt:ia < wm.length:=by
         rw [wm_len]; exact (hg_eq ▸ (hnorm ⟨m,hm_lt⟩).1) ia (by simp [hinp])
       have hib_lt:ib < wm.length:=by
         rw [wm_len]; exact (hg_eq ▸ (hnorm ⟨m,hm_lt⟩).1) ib (by simp [hinp])
       let a_raw:=wm.getD ia zero
       let b_raw:=wm.getD ib zero
       let a:=nrm true a_raw
       let b:=nrm true b_raw
       have ha_mem:a ∈ wm.map (nrm true):=by
         apply List.mem_map_of_mem
         change wm.getD ia zero ∈ wm; simp [List.getD_eq_getElem?_getD,hia_lt]
       have hb_mem:b ∈ wm.map (nrm true):=by
         apply List.mem_map_of_mem
         change wm.getD ib zero ∈ wm; simp [List.getD_eq_getElem?_getD,hib_lt]
       let isOr:=match g.op with | .or=>true | _=>false
       let d:=if isOr then
         (if bit 0 a_raw then (if bit 0 b_raw then 0 else 2) else (if bit 0 b_raw then 3 else 1))
       else
         (if bit 0 a_raw then (if bit 0 b_raw then 1 else 3) else (if bit 0 b_raw then 2 else 0))
       have hzr_eq:z_raw=(if isOr then a_raw ||| b_raw else a_raw &&& b_raw):=by
         have hb:=j0 wm g ia ib hinp hor_and
         rcases hor_and with h_and | h_or
         · simp only [isOr,h_and,↓reduceIte]
           simp only [jp,h_and,↓reduceIte,bin] at hb
           exact hb
         · simp only [isOr,h_or,↓reduceIte]
           simp only [jp,h_or,↓reduceIte,bin,Nat.one_ne_zero] at hb
           exact hb
       have hz_bin:z=bin d a b:=by
         change nrm true z_raw=bin d (nrm true a_raw) (nrm true b_raw)
         rw [hzr_eq]
         exact q169 isOr a_raw b_raw
       have hd:allowed true d:=Or.inr ⟨rfl,by
         dsimp [d]
         by_cases ha0:bit 0 a_raw=true<;>by_cases hb0:bit 0 b_raw=true <;>
           cases isOr<;>simp [ha0,hb0]⟩
       have hzp:proper z:=jZ (q2 hlive) z hzS
       have ha_b0:bit 0 a=false:=z216 a_raw
       have hb_b0:bit 0 b=false:=z216 b_raw
       have ha_p:proper a:=by
         refine ⟨fun haz=>?_,jY a_raw⟩
         rw [haz] at hz_bin
         have hz_bad:z=zero ∨ z=b:=by
           rcases zS hd with hd0 | hd1 | ⟨_,hd2⟩ | ⟨_,hd3⟩
           · left; apply zF; intro r; rw [hz_bin,hd0,zX,zv]; simp
           · right; apply zF; intro r; rw [hz_bin,hd1,zX,zv]; simp
           · left; apply zF; intro r; rw [hz_bin,hd2,zX,zv]; simp
           · right; apply zF; intro r; rw [hz_bin,hd3,zX,zv]; simp
         rcases hz_bad with h0 | hb'
         · exact hzp.1 h0
         · exact hzw (hb' ▸ hb_mem)
       have hb_p:proper b:=by
         refine ⟨fun hbz=>?_,jY b_raw⟩
         rw [hbz] at hz_bin
         have hz_bad:z=zero ∨ z=a:=by
           rcases zS hd with hd0 | hd1 | ⟨_,hd2⟩ | ⟨_,hd3⟩
           · left; apply zF; intro r; rw [hz_bin,hd0,zX,zv]; simp
           · right; apply zF; intro r; rw [hz_bin,hd1,zX,zv]; simp
           · right; apply zF; intro r; rw [hz_bin,hd2,zX,zv]; simp
           · left; apply zF; intro r; rw [hz_bin,hd3,zX,zv]; simp
         rcases hz_bad with h0 | ha'
         · exact hzp.1 h0
         · exact hzw (ha' ▸ ha_mem)
       have hab:a ≠ b:=by
         intro hab_eq
         rw [hab_eq] at hz_bin
         have hz_bad:z=b ∨ z=zero:=by
           rcases zS hd with hd0 | hd1 | ⟨_,hd2⟩ | ⟨_,hd3⟩
           · left; apply zF; intro r; rw [hz_bin,hd0,zX]; simp
           · left; apply zF; intro r; rw [hz_bin,hd1,zX]; simp
           · right; apply zF; intro r; rw [hz_bin,hd2,zX,zv]; simp
           · right; apply zF; intro r; rw [hz_bin,hd3,zX,zv]; simp
         rcases hz_bad with hzb | hz0
         · exact hzw (hzb ▸ hb_mem)
         · exact hzp.1 hz0
       let U:=S.erase z
       have hU_sub : ∀ y ∈ U,y ∈ wm.map (nrm true):=by
         intro y hy
         obtain ⟨hne,hyS⟩:=Finset.mem_erase.mp hy
         rcases List.mem_append.mp (hsub y hyS) with hyw | hyz
         · exact hyw
         · exact False.elim (hne (by simpa using hyz))
       have hfresh:bin d a b ∉ insert a (insert b U):=by
         rw [← hz_bin]
         intro hm_in
         rcases Finset.mem_insert.mp hm_in with e | hm_in
         · exact hzw (e ▸ ha_mem)
         · rcases Finset.mem_insert.mp hm_in with e | hm_in
           · exact hzw (e ▸ hb_mem)
           · exact hzw (hU_sub _ hm_in)
       have check_side (ix iy:Nat) (hix:ix < wm.length) (hiy:iy < wm.length)
           (hne_i:ix ≠ iy) (hinp_pair:g.inputs=[ix,iy] ∨ g.inputs=[iy,ix]) :
           let x:=nrm true (wm.getD ix zero)
           let y:=nrm true (wm.getD iy zero)
           q7 true x y (if ix == ia then d else qm d) (decide (x ∈ U))=true:=by
         intro x y
         by_cases hx467:qH x=true
         · have hvx : ∃ v:Fin 9,v ∈ ([4,6,7]:List (Fin 9)) ∧ x=inputs.getD v.val zero:=by
             simp only [qH,in4,in6,in7,Bool.or_eq_true,beq_iff_eq] at hx467
             rcases hx467 with (e | e) | e
             · exact ⟨4,by simp,e⟩
             · exact ⟨6,by simp,e⟩
             · exact ⟨7,by simp,e⟩
           obtain ⟨v,hv,hxv⟩:=hvx
           obtain ⟨i_v,w_v,_,_,hor_v,hinp_v,huniq_v,hforb_v,hno_alias_v⟩ :=
             vD C hmin hfun hnorm hS hndW v hv
           have hix_eq:ix=v.val:=by
             by_contra hne_v
             have hW_ix:(execute C.gates inputs).getD ix zero=wm.getD ix zero:=by
               rw [hW_eq,zb _ _ _ _ hix]
             have hix_lt_C:ix < 9 + C.size:=by rw [wm_len] at hix; omega
             exact hno_alias_v ix hix_lt_C hne_v (by rw [hW_ix]; exact hxv)
           have hv_mem_m:v.val ∈ (C.gates.get ⟨m,hm_lt⟩).inputs:=by
             rw [← hg_eq,← hix_eq]
             rcases hinp_pair with h | h<;>simp [h]
           have hm_eq_iv:(⟨m,hm_lt⟩ : Fin C.size)=i_v:=by
             by_contra hm_ne
             exact huniq_v ⟨m,hm_lt⟩ hm_ne hv_mem_m
           have hg_eq_iv:g=C.gates.get i_v:=hg_eq.trans (congrArg C.gates.get hm_eq_iv)
           have hor_m:g.op=GateOp.or:=hg_eq_iv ▸ hor_v
           have hisOr_T:isOr=true:=by simp [isOr,hor_m]
           have hiy_eq_wv:iy=w_v:=by
             have hg_in_iv:g.inputs=[v.val,w_v] ∨ g.inputs=[w_v,v.val]:=hg_eq_iv ▸ hinp_v
             rcases hinp_pair with h1 | h2<;>rcases hg_in_iv with h3 | h4
             · rw [h1,hix_eq] at h3; simp only [List.cons.injEq,and_true] at h3; exact h3.2
             · rw [h1,hix_eq] at h4; simp only [List.cons.injEq,and_true] at h4; exact absurd h4.2 (hix_eq ▸ hne_i.symm)
             · rw [h2,hix_eq] at h3; simp only [List.cons.injEq,and_true] at h3; exact absurd h3.1 (hix_eq ▸ hne_i.symm)
             · rw [h2,hix_eq] at h4; simp only [List.cons.injEq,and_true] at h4; exact h4
           have hW_iy:(execute C.gates inputs).getD iy zero=wm.getD iy zero:=by
             rw [hW_eq,zb _ _ _ _ hiy]
           have hyraw_forb:(wm.getD iy zero &&& zr x)=zero:=by
             rw [hxv,wh v hv,← hW_iy,hiy_eq_wv]
             exact hforb_v
           have hx_not_U:x ∉ U:=by
             intro hxU
             have hxS:inputs.getD v.val zero ∈ S:=hxv ▸ Finset.mem_of_mem_erase hxU
             obtain ⟨j,hj⟩:=h4 v hv hxS
             have hj_lt:m + 1 + j.val < C.size:=by
               have:=congrArg List.length hsplit
               simp only [Circuit.size,List.length_append,List.length_cons] at this ⊢
               omega
             have hj_eq:gs.get j=C.gates.get ⟨m + 1 + j.val,hj_lt⟩:=by
               have h:=congrArg (fun l=>l[m + 1 + j.val]?) hsplit
               have h1:(pref ++ g :: gs)[m + 1 + j.val]? = some (gs.get j):=by
                 have hex_j:m + 1 + j.val=(pref ++ [g]).length + j.val:=by simp [m]
                 rw [show pref ++ g :: gs=(pref ++ [g]) ++ gs by simp,hex_j,List.getElem?_append_right (by omega)]
                 simp [j.isLt]
               have h2:C.gates[m + 1 + j.val]? = some (C.gates.get ⟨m + 1 + j.val,hj_lt⟩):=by simp [hj_lt]
               rw [h1,h2] at h
               exact Option.some.inj h
             exact huniq_v ⟨m + 1 + j.val,hj_lt⟩ (by intro e; have h1:=congrArg Fin.val (e.trans hm_eq_iv.symm); dsimp at h1; omega) (hj_eq ▸ hj)
           have hx_dec:decide (x ∈ U)=false:=decide_eq_false hx_not_U
           have hx_wm:wm.getD ix zero=inputs.getD v.val zero:=by
             obtain ⟨l,hl⟩:=zO pref inputs
             change wm.getD ix zero=_
             rw [hix_eq,show wm=execute pref inputs from rfl,hl]
             exact zb _ _ _ _ (by simp [inputs])
           have hx_b0:bit 0 (wm.getD ix zero)=false:=by
             rw [hx_wm]
             have hv_mem_in:inputs.getD v.val zero ∈ inputs:=by
               change inputs.getD v.val zero ∈ inputs; simp [List.getD_eq_getElem?_getD,inputs,v.isLt]
             exact (wW _ hv_mem_in).1
           have hy_case:(bit 0 (wm.getD iy zero)=false ∧ (if ix == ia then d else qm d)=1 ∧ (y &&& zr x)=zero) ∨
                          (bit 0 (wm.getD iy zero)=true ∧ (if ix == ia then d else qm d)=3 ∧ (y &&& zr x)=zr x):=by
             rcases hinp_pair with hpair | hpair
             · have hia_eq:ix=ia:=by rw [hinp] at hpair; simp only [List.cons.injEq] at hpair; exact hpair.1.symm
               have hib_eq:iy=ib:=by rw [hinp] at hpair; simp only [List.cons.injEq,and_true] at hpair; exact hpair.2.symm
               subst hia_eq hib_eq
               have ha0:bit 0 a_raw=false:=hx_b0
               cases hb0:bit 0 b_raw
               · left
                 refine ⟨rfl,?_,?_⟩
                 · dsimp [d]; simp [hisOr_T,ha0,hb0]
                 · change (nrm true b_raw &&& zr x)=zero
                   unfold nrm; simp only [Bool.true_and,hb0,Bool.false_eq_true,↓reduceIte]; exact hyraw_forb
               · right
                 refine ⟨rfl,?_,?_⟩
                 · dsimp [d]; simp [hisOr_T,ha0,hb0]
                 · change (nrm true b_raw &&& zr x)=zr x
                   unfold nrm; simp only [Bool.true_and,hb0,↓reduceIte]
                   exact beq_iff_eq.mp (jx _ _ hyraw_forb)
             · rw [hinp] at hpair
               simp only [List.cons.injEq,and_true] at hpair
               have hia_eq:iy=ia:=hpair.1.symm
               have hib_eq:ix=ib:=hpair.2.symm
               have hne_ix_ia:(ix == ia)=false:=beq_false_of_ne (by rw [← hia_eq]; exact hne_i)
               subst hib_eq hia_eq
               have hb0:bit 0 b_raw=false:=hx_b0
               cases ha0:bit 0 a_raw
               · left
                 refine ⟨rfl,?_,?_⟩
                 · rw [if_neg (by simp [hne_ix_ia])]; dsimp [d]; simp [hisOr_T,ha0,hb0,qm]
                 · change (nrm true a_raw &&& zr x)=zero
                   unfold nrm; simp only [Bool.true_and,ha0,Bool.false_eq_true,↓reduceIte]; exact hyraw_forb
               · right
                 refine ⟨rfl,?_,?_⟩
                 · rw [if_neg (by simp [hne_ix_ia])]; dsimp [d]; simp [hisOr_T,ha0,hb0,qm]
                 · change (nrm true a_raw &&& zr x)=zr x
                   unfold nrm; simp only [Bool.true_and,ha0,↓reduceIte]
                   exact beq_iff_eq.mp (jx _ _ hyraw_forb)
           rcases hy_case with ⟨_,hd_eq,hm_eq⟩ | ⟨_,hd_eq,hm_eq⟩
           · rw [hd_eq]; simp [q7,hx467,hx_dec,hm_eq]
           · rw [hd_eq]; simp [q7,hx467,hx_dec,hm_eq]
         · simp [q7,hx467]
       have hok:wK true U a b d:=by
         unfold wK zy
         rw [Bool.and_eq_true]
         refine ⟨?_,?_⟩
         · have hs:=check_side ia ib hia_lt hib_lt hia_ne_ib (Or.inl hinp)
           simp only [beq_self_eq_true,↓reduceIte] at hs
           exact hs
         · have hs:=check_side ib ia hib_lt hia_lt hia_ne_ib.symm (Or.inr hinp)
           have hne_ba:(ib == ia)=false:=beq_false_of_ne hia_ne_ib.symm
           simp only [hne_ba,Bool.false_eq_true,↓reduceIte] at hs
           exact hs
       have hlive_new:Live467 true graph (k + 1) (insert a (insert b U)):=by
         refine Live467.binary hd hok ha_p hb_p hab hfresh ?_
         dsimp only [U]
         rw [← hz_bin,Finset.insert_erase hzS]
         exact hlive
       have hnot_not_true:(!wV g)=true:=by
         rcases hor_and with h | h<;>simp [wV,h]
       refine ⟨k + 1,insert a (insert b U),?_,hlive_new,?_,fun v hv hv_in=>?_⟩
       · rw [List.countP_cons,hnot_not_true]; simp; omega
       · intro y hy
         rcases Finset.mem_insert.mp hy with rfl | hy
         · exact ha_mem
         · rcases Finset.mem_insert.mp hy with rfl | hy
           · exact hb_mem
           · exact hU_sub y hy
       · have hv_idx (idx:Nat) (hidx:idx < wm.length) (hveq:inputs.getD v.val zero=nrm true (wm.getD idx zero)):idx=v.val:=by
           by_contra hne_v
           obtain ⟨_,_,_,_,_,_,_,_,hno_alias_v⟩:=vD C hmin hfun hnorm hS hndW v hv
           have hW_idx:(execute C.gates inputs).getD idx zero=wm.getD idx zero:=by
             rw [hW_eq,zb _ _ _ _ hidx]
           have hidx_lt_C:idx < 9 + C.size:=by rw [wm_len] at hidx; omega
           exact hno_alias_v idx hidx_lt_C hne_v (by rw [hW_idx]; exact hveq.symm)
         rcases Finset.mem_insert.mp hv_in with hv_a | hv_in
         · have hva:=hv_idx ia hia_lt hv_a
           exact ⟨0,by simp [hinp,hva]⟩
         · rcases Finset.mem_insert.mp hv_in with hv_b | hv_in
           · have hvb:=hv_idx ib hib_lt hv_b
             exact ⟨0,by simp [hinp,hvb]⟩
           · obtain ⟨j,hj⟩:=h4 v hv (Finset.mem_of_mem_erase hv_in)
             exact ⟨j.succ,hj⟩
     · refine ⟨k,S,?_,hlive,fun y hy=>?_,fun v hv hvS=>?_⟩
       · rw [List.countP_cons]; cases wV g<;>simp<;>omega
       · rcases List.mem_append.mp (hsub y hy) with hyw | hyz
         · exact hyw
         · have hy_eq:y=z:=by simpa using hyz
           exact False.elim (hzS (hy_eq ▸ hy))
       · obtain ⟨j,hj⟩:=h4 v hv hvS
         exact ⟨j.succ,hj⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem bound_2116
   (hU14:zo true (z1 511) 14 (vars 511).toFinset)
   (hM15:zo false (z1 511) 15 (vars 1535).toFinset)
   (C:Circuit)
   (hmin:PEqualNP.MetaComplexity.IsMinimalCircuit 9 C)
   (hsize:C.size ≤ 15)
   (hfun:PEqualNP.MetaComplexity.circuitFun 9 C=edge)
   (hnorm : ∀ i:Fin C.size,
     (∀ w ∈ (C.gates.get i).inputs,w < 9 + i.val) ∧
     (C.gates.get i).inputs.Nodup ∧
     ((C.gates.get i).op=GateOp.not ∧ (C.gates.get i).inputs.length=1 ∨
      (C.gates.get i).op ≠ GateOp.not ∧ (C.gates.get i).inputs.length=2))
   (hS : ∀ v:Fin 9,v ∈ ([4,6,7]:List (Fin 9)) →
     ({i:Fin C.size | v.val ∈ (C.gates.get i).inputs} : Finset (Fin C.size)).card=1 ∧
     ∀ i ∈ ({i:Fin C.size | v.val ∈ (C.gates.get i).inputs} : Finset (Fin C.size)),(C.gates.get i).op=GateOp.or):False:=by
 have hfun' : PEqualNP.MetaComplexity.circuitFun 9 C=edge:=hfun
 have goalEq:(execute C.gates inputs).getD C.output zero=graph:=by
   apply zF
   intro r
   exact (vr C hmin.1 C.output r).trans ((congrFun hfun' (sample r)).trans (z123 r).symm)
 have hndW:=w9 C hmin hnorm
 by_cases hNoNot : ∀ i:Fin C.size,(C.gates.get i).op ≠ GateOp.not
 · have hGate : ∀ i:Fin C.size,(C.gates.get i).inputs.length=2 ∧
       (∀ w ∈ (C.gates.get i).inputs,w < 9 + i.val) ∧
       ((C.gates.get i).op=GateOp.and ∨ (C.gates.get i).op=GateOp.or):=by
     intro i
     have hi:=hnorm i
     have hfan:=hmin.1 _ (C.gates.get_mem i)
     refine ⟨?_,hi.1,?_⟩
     · rcases hi.2.2 with ⟨hn,_⟩ | ⟨_,h2⟩
       · exact absurd hn (hNoNot i)
       · exact h2
     · rcases hfan.1 with h1 | h2 | h3
       · exact Or.inl h1
       · exact Or.inr h2
       · exact absurd h3 (hNoNot i)
   have htarget:graph ∈ execute C.gates inputs:=by
     have out:=q120 (u:=false) (execute C.gates inputs) C.output
     unfold Repr represented at out
     rw [goalEq,y8] at out
     rcases List.mem_map.mp (out.resolve_right (fun hn=>hn jB)) with ⟨x,hx,hxq⟩
     rw [y8] at hxq
     exact hxq ▸ hx
   obtain ⟨k,S,hk,hlive,hsub,-⟩:=z386 C hmin hfun' hnorm hS hndW hGate C.gates [] rfl htarget
   have hk15:k ≤ 15:=le_trans hk hsize
   have hlive':=q2 hlive
   rw [q368] at hlive hlive'
   have hsub' : ∀ a ∈ S,a ∈ inputs:=fun a ha=>by simpa [execute] using hsub a ha
   have eqS:=wl hlive' hsub'
   have eqV:vars 511=vars 1535:=by rw [yL,z245]
   rw [eqV] at eqS
   exact hM15 k hk15 (eqS ▸ hlive)
 · push Not at hNoNot
   obtain ⟨i0,hi0⟩:=hNoNot
   have lt_cnt:C.gates.countP (fun g => !wV g) < C.gates.length:=by
     rcases Nat.lt_or_ge (C.gates.countP (fun g => !wV g)) C.gates.length with h | h
     · exact h
     · have eq:=List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) (C.gates.get i0) (C.gates.get_mem i0)
       simp only [wV,hi0,Bool.not_true] at eq
       exact Bool.noConfusion eq
   have hc14:C.gates.countP (fun g => !wV g) ≤ 14:=by
     change C.gates.length ≤ 15 at hsize
     omega
   have out:=q120 (u:=true) (execute C.gates inputs) C.output
   unfold Repr represented at out
   rw [goalEq,z367 z391] at out
   have targetIn:=out.resolve_right (fun hn=>hn jB)
   obtain ⟨k,S,hk,hlive,hsub,-⟩:=z289 C hmin hfun' hnorm hS hndW C.gates [] rfl targetIn
   have hk14:k ≤ 14:=le_trans hk hc14
   have hlive':=q2 hlive
   rw [q368] at hlive hlive'
   change ∀ a ∈ S,a ∈ inputs.map (nrm true) at hsub
   rw [q118 z218] at hsub
   have eqS:=wl hlive' hsub
   exact hU14 k hk14 (eqS ▸ hlive)
def yF:=za [] 4 [(15,[]),(23,[64,48,32,16]),(27,[66,16]),(29,[50,65]),(30,[50,33,16,64]),(39,[80,64,48,32,16]),(57,[32,82,64,16]),(78,[96,80,64]),(83,[99,83,64,32,16]),(99,[48,96,83,64,32,16]),(135,[115,99,83,67]),(156,[112,96,48,50,33,81,64]),(163,[115,50,98,83,66,16]),(165,[114,33,97,82,50,65]),(166,[114,98,83,33,16,64]),(172,[114,50,99,48,33,81,64]),(177,[115,99,82,64,16]),(198,[115,96,83,64]),(281,[131,115,99,50,82,65]),(305,[131,115,99,82,64,16]),(312,[130,114,49,98,81,64]),(323,[131,115,98,83,66]),(326,[131,115,98,83,32,64]),(330,[130,114,97,82,16,64]),(332,[130,50,115,98,49,32,81,64]),(344,[130,50,115,49,98,81,64]),(353,[130,33,113,99,82,65]),(354,[130,33,50,113,99,82,16,64]),(396,[48,128,115,96,50,33,81,64]),(424,[129,33,115,48,98,81,64]),(480,[32,50,128,115,98,81,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q114:Known true yF:=z6 (m:=15) z175 j155 (by decide +kernel)
def j162 (i:Nat):Nat:=0x11a20bf
def j157:Packing:=(1,0,3,0,0,0,0,j162)
def j160 (i:Nat):Nat:=0x30be670208000065000016357504004755c084
def j163 (i:Nat):Nat:=0x40828fd20fd10
def j158:Packing:=(2,1,3,0,0,3,0,j163)
def j161 (i:Nat):Nat:=0x300
def j164 (i:Nat):Nat:=0x5dd4520
def j159:Packing:=(1,2,3,0,0,0,0,j164)
def z376:Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd15d16630b273,0x11525c6a12412),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe90c286464e7f,0x2c2d009524869),(0x18c06d986cd9c,0x1290662058794),(0x27e6c59e90980,0x2166995b04820),(0x3ebbb2079b000,0xe892284e92c0),(0,0),(0,0),(0,0),(0,0)]
def z377:List zK:=[(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4),(2,0,29,0,4)]
def q294:List (List Nat):=[[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]
def q177:Nat → Packing
 | 6=>j157
 | 5=>j158
 | 4=>j159
 | _=>zP
def q293:Nat → Nat → Option (Nat × Nat)
 | 6=>zk 5 15 3 9 1 4 j160
 | 5=>zk 1 3 1 9 1 4 j161
 | _=>fun _=>none
def g31:Forest := ⟨31,6,fun j=>z376[j]?.getD (0,0),z377,q294,q177,q293⟩
set_option maxHeartbeats 0 in
theorem q356:zp g31 (z9 yF)=true:=by
 simp only [zp,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,zh (d:=0) ?_⟩,zh (d:=1) ?_⟩
 all_goals simp only [zQ]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q308:block g31 6 0 1=true:=by refine (z7 (ar:=5) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q309:block g31 5 0 2=true:=by refine (z7 (ar:=6) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q310:block g31 4 0 1=true:=by refine (z7 (ar:=5) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem q155:zD g31 6:=by
 intro k hk
 interval_cases k
 · rfl
 · rfl
 · rfl
 · rfl
 · exact q310
 · exact q309
 · exact q308
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j154:Lower true (vars 31) (z1 31) 7:=qn (hints:=8449) (by decide +kernel) (zu (g:=g31) (i:=0) rfl rfl (z5 yF q114) q356 q155 (by decide +kernel))
def yE:=za yF 7 [(31,[]),(167,[115,67,100,83]),(334,[131,115,100,50,33,16,80]),(355,[131,50,66,116,99,82]),(428,[130,50,116,49,32,97,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q113:Known true yE:=z6 (m:=31) q114 j154 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j153:Lower true (vars 47) (z1 47) 5:=qn (hints:=8449) (by decide +kernel) (zW (prior:=z9 yE) (z5 yE q113) (8,0,39,0,4) (by decide +kernel) (by decide +kernel))
def yD:=za yE 5 [(91,[101,66,16]),(94,[101,50,33,16,64]),(181,[114,81,98,50,65]),(227,[83,82,114,99,66,16]),(230,[83,114,99,33,16,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q112:Known true yD:=z6 (m:=47) q113 j153 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j152:Lower true (vars 55) (z1 55) 5:=qn (hints:=257) (by decide +kernel) (zW (prior:=z9 yD) (z5 yD q112) (16,0,39,0,4) (by decide +kernel) (by decide +kernel))
def yC:=za yD 5 [(55,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q111:Known true yC:=z6 (m:=55) q112 j152 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j151:Lower true (vars 63) (z1 63) 8:=qn (hints:=8449) (by decide +kernel) (zW (prior:=z9 yC) (z5 yC q111) (32,0,31,0,7) (by decide +kernel) (by decide +kernel))
def yB:=za yC 8 [(63,[]),(95,[101,66,16]),(159,[117,101,67,32]),(359,[131,67,116,99,82,16]),(377,[128,81,67,112,97,32]),(462,[83,133,115,67,32,96]),(483,[83,80,132,115,96,32,16]),(492,[80,84,132,49,113,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q110:Known true yB:=z6 (m:=63) q111 j151 (by decide +kernel)
def j131 (i:Nat):Nat:=0x7213f
def j128:Packing:=(1,0,2,0,0,0,0,j131)
def j130 (i:Nat):Nat:=0x8000
def j132 (i:Nat):Nat:=0x17e51
def j129:Packing:=(1,1,2,0,0,0,0,j132)
def z286:Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffad506dc8c692839f653,0xf04d190d4828112652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9aa3b7e53917e26487f,0xa02a6201004224829),(0x544c503731eb1c38f9c,0x1449d09c60531818514),(0x6d8c223200ec1fc0fc0,0x6bb62f6391ac07c0ac0),(0,0),(0x71d0482cce001fff020,0x70fb0c6f2b181eed020),(0x7fe3c2000ee7f040020,0x7f5fd599feffb040000),(0,0),(0,0)]
def z287:List zK:=[(1,32,78,0,4),(12,0,99,0,4),(96,0,15,0,4),(0,8,99,4,5)]
def q185:List (List Nat):=[[],[32,83]]
def z382:Nat → Packing
 | 6=>j128
 | 5=>j129
 | _=>zP
def q184:Nat → Nat → Option (Nat × Nat)
 | 6=>zk 1 3 1 6 1 1 j130
 | _=>fun _=>none
def q297:Forest := ⟨111,6,fun j=>z286[j]?.getD (0,0),z287,q185,z382,q184⟩
set_option maxHeartbeats 0 in
theorem q292:zp q297 (z9 yB)=true:=by
 simp only [zp,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,zh (d:=0) ?_⟩,zh (d:=0) ?_⟩
 all_goals simp only [zQ]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q217:block q297 6 0 1=true:=by refine (z7 (ar:=6) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q218:block q297 5 0 1=true:=by refine (z7 (ar:=6) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem z340:zD q297 6:=by
 intro k hk
 interval_cases k
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · exact q218
 · exact q217
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j108:Lower true (vars 111) (z1 111) 7:=qn (hints:=16785665) (by decide +kernel) (zu (g:=q297) (i:=0) rfl rfl (z5 yB q110) q292 z340 (by decide +kernel))
def wU:=za yB 7 [(111,[]),(123,[101,66,16]),(187,[117,80,66,96,16]),(190,[114,83,48,33,97,64]),(215,[115,83,67]),(222,[101,117,50,33,16,64]),(238,[83,114,99,33,16,64]),(243,[82,98,115,66,16]),(378,[129,33,97,81,16,114,49,64]),(437,[134,81,114,50,65]),(476,[82,50,133,98,49,32,113,64]),(485,[80,81,129,114,50,65,96]),(490,[81,33,80,128,97,114,49,64]),(497,[98,99,81,131,114,65]),(504,[49,50,83,48,130,113,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z251:Known true wU:=z6 (m:=111) q110 j108 (by decide +kernel)
def j125 (i:Nat):Nat:=0x163441bf
def j120:Packing:=(1,0,3,0,0,0,0,j125)
def j123 (i:Nat):Nat:=0x42f9f28c08140000000020f801630c00d0
def j126 (i:Nat):Nat:=0x420a3fa41fd10
def j121:Packing:=(2,1,3,0,0,3,0,j126)
def j124 (i:Nat):Nat:=0x18000
def j127 (i:Nat):Nat:=0xb7d8d20
def j122:Packing:=(1,2,3,0,0,0,0,j127)
def z284:Array (Bits × Bits) := #[(0x1da64108012bd832f47c,0x1d85960021199906a42c),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffac458a9750042f2dc84f,0x4c61e4544061425c84a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9958e417a60021ce0f8f,0x1909e00a3a18e18a0685),(0x67780400a62f50f10f70,0x627201f4c42600710950),(0x52c2796909d080fbf080,0x4042684f5e8240f95000),(0,0),(0x7b3dbae059d52e010080,0x3b3981b0a179ab000080),(0,0)]
def z285:List zK:=[(160,0,29,0,4),(24,0,165,0,4),(132,0,57,0,4),(33,0,156,0,4),(17,0,172,0,4),(12,0,177,0,4)]
def q181:List (List Nat):=[[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]
def z379:Nat → Packing
 | 7=>j120
 | 6=>j121
 | 5=>j122
 | _=>zP
def q180:Nat → Nat → Option (Nat × Nat)
 | 7=>zk 9 13 2 9 1 4 j123
 | 6=>zk 1 3 1 9 1 4 j124
 | _=>fun _=>none
def q182:Forest := ⟨189,7,fun j=>z284[j]?.getD (0,0),z285,q181,z379,q180⟩
set_option maxHeartbeats 0 in
theorem q291:zp q182 (z9 wU)=true:=by
 simp only [zp,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,zh (d:=1) ?_⟩,zh (d:=2) ?_⟩
 all_goals simp only [zQ]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q214:block q182 7 0 1=true:=by refine (z7 (ar:=6) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q215:block q182 6 0 2=true:=by refine (z7 (ar:=7) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q216:block q182 5 0 1=true:=by refine (z7 (ar:=6) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem z339:zD q182 7:=by
 intro k hk
 interval_cases k
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · exact q216
 · exact q215
 · exact q214
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j106:Lower true (vars 189) (z1 189) 8:=qn (hints:=536879876) (by decide +kernel) (zu (g:=q182) (i:=0) rfl rfl (z5 wU z251) q291 z339 (by decide +kernel))
def wS:=za wU 8 [(189,[]),(347,[130,50,98,82,115,33,65]),(486,[115,83,82,130,99,66,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z249:Known true wS:=z6 (m:=189) z251 j106 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j107:Lower true (vars 127) (z1 127) 9:=qn (hints:=16785665) (by decide +kernel) (zW (prior:=z9 wS) (z5 wS z249) (32,0,95,0,8) (by decide +kernel) (by decide +kernel))
def wT:=za wS 9 [(127,[]),(382,[128,100,49,112]),(478,[99,132,84,48,33,112]),(508,[48,84,100,49,129,112]),(223,[32,67,117]),(239,[32,83,116]),(247,[115,84])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z250:Known true wT:=z6 (m:=127) z249 j107 (by decide +kernel)
def q360 (i:Nat):Nat:=0x8201ff
def q358:Packing:=(1,0,5,0,0,0,0,q360)
def q359 (i:Nat):Nat:=0x99090000b500000001a152f05d5c000e4006080015749fa60141c73802b0a68137976081bca199eaaa3d961388c0f3a0002328c00084a05000089c2a
def j116 (i:Nat):Nat:=0x288616180c48a1166c008c818588a2e004e68c2c214019ce18588b2410102944c300431c508936018138408051218b0c0328614b0a030139610c0803944862a8614888704038c28424018278d600745a25b53e43cce27c5e0bc00ff483fe30ff4c3fd10ff54ffe10ff903fe20ff4c7fc20ff58ffd40
def j109:Packing:=(12,1,5,0,0,10,0,j116)
def j113 (i:Nat):Nat:=0x140000000000000198cb0000a04e08a520001a51c20000531e80b64388d00078963d80a7524800343b41a670800007a7cc632d75239502d607286400000000060840000002a100028a67e35dbbd50001a6c315cd7a0d113ac27000121800052568158594ec000682af90000f6880000010b6fab800321ac31374a97c0018068243a2b09f06ef8c8000c984c7fad8000732e29d36fd3c9ba4660000003c50a43a2e72f0000037c5c484413000060966343d567081fd24000161fd8fb857db1616c2d70bc0001da504981c000a8cb68709baa54393350153817e93b2ee08a0b35c971e4812648c40cf0c890074a5b901b85c19b060f0f30f9c6d46f822909e468ae58b600010460007b00142a8dc0d2c800031c60005ad28d4a60000000000000046100000000000000005978000750c07fc419a5a33000612dc38451b04000033fe570000002d76000244c429f180a5d34b0ba1360001a731afd48a565b2f860060014b1d8111aaaac600056d800000000026c2da68678cd5b803ae00010d91906c6000000173ec82c4200058c80000000001b509c9847ce37e90001c466a9e954000000c99484d7ca82a800f93447182024f80000c48dc000596030083ad05a1c75006c10817410814060062c35820051841c00801071c96460c20000020c70c01c908b0c0000080000041016
def j117 (i:Nat):Nat:=(if i<1 then 0x50b30a062068860c1071620828188001141c88038918b140c61c40b1a0821c49040b10a18885a12900e2468610b144063043858908b143122d10c2a20e20596046182c82c608322160c8246088071094438590503146400c68a00c1a1022c6305831c01630640389281160c82460840710c140c6090090e404803892100e1864038618c162401c48c60b160180d111103182838b1239014302141c48b3a5181c5091708320507124c195160c316314389160c90448d187120c6110890e34514481802c80858c1c1041c48b281142c624708082122c8246892c61458c2b0610e2c48e44a0c1c5a2065c02c60d3011630900487244022858c10714310040020e2cc1c4884930e0c81c48b280ca8848b18a062002438c50b10c1620e2470c62616044871e70a1c08a2250e2c5421260c1d08b262102c626102022859800f12308301250228a0048b18c1621898487020210b4051306022161ce1858a1930e0c61c00d160ca0458a1c1121c1920890e0c8083a1122ca0500b0624a0a007244181c482424459c607122c82c087120cb00007164140c48060a1240e251001628c306c54c090413820f044901871630c3c38c2458d8309030a1a24597160142c9badb87b53b11aebaa9a75a41a0d9cb9a59559218df8b989385f82b7db79977373170b6e56a367d6496155e15ad5795535114eb4c549144f40d3d93a537f34b3252e32691fd1831330e30a106d02afdaf98f64f14ee0ebae78e52e2cd96d46d12cd0c8ec5ac26bc8ba2b60b10adcab6a82a5ca36a029969548f68b48808227e079075c7366bc65061c5e85985645224e04904403fe3923503002be2982561f818c14a1160d4092042001ff54930ffaa0a07fd71483feb1c21ff50120ffcc5207fd52503fe98221ff58e20ffac0987fd1058ffeb9a41ff58640ffa60907fd72443fe882a7ff50910ffee2907fd2058ffe98c41ff54131ffa20907fd21903feb1281ff48153ffa42a07fe72443fe90c41ffdcd20ffa65087fd32883feb0c61ff8ca10ffa43187fd2158ffeb9a21ff54931ffac098ffd62903feb1461ff58931ffac0a07fd204c7fa38a417f5c520bfae5107f920842ffb9281fddc520ff221105fd75902feb88417fdd110fba60b1fdd324c6feb94617f5ce10bfee0a9dfd7054efebac61fdc8610bfee2907f910482ffb9263fd48531bfee2b1fbf744c2ffbb2617f5c163bfaed185ff71502ffb92217f5c553bfae9105fd76902feb9c417f5cc20bfee2a9dff704c7dea14817f5ca10ff260905ff7258fee982637fdd531fea63087dd3054efeb92637f5c131bfae2b1dff724c2ffbb2817fdcd10ff261105fd718c2feb8c817fdcd20bfeeaa05ff7058efeb9a41fe48230bfae3107dd3258efeba4217fdd530bfee2987f5514c6feb94817f5c963bfeec98df771482eeb9c416fdd130 else 0x10410e24)
def j110:Packing:=(113,2,5,0,0,12,0,j117)
def j114 (i:Nat):Nat:=0x38d5055793c3679268754bc6188000001bef920589c626a6500070140c8d5de5f1d7a21d0344d98ee800183ee488000001119701a189f7ac18d073c41c5a460f2f6dbb0d3e90a06b82f5bcc02928e3aa852e880000109c34616429775d57a00841de8968c753cd4f7779436ba625de899899071c11166c07285d4158b1c40cba3819701ff1ed4e0000001d75e386545f25c03c4e3ccfe7905e2217770000000a100005011f8991186d800000144100008f313025a433c0cd88dae660be94000121c0000002c88000000655b0af52342fd8c3fbe11d039049a5a1e7325180004d4e9a308f4f4000000ef1802b07e014cea170acb800000009b4c4008e61bc79a059a0f70fccb137f85b2554dc0000000f21e93d1260001258003490000000000283ab340000000b1c0000000003185023a5319608aa0001913478000000000000000046621400000000000005b0dc8e000000426e6c726f99d415a6c3045000127023e070c8d80b889403631ef964fdd2196b35879ca860c0656093c9b66e604e1a08c20003c8494d7228964094caf59a8139a149ac000c151050440002c01002420821110471482078810951470800420470000020001001c02830c50400010400800405400402040000c00080070800c100000d0040151000c0040141188000004000
def j118 (i:Nat):Nat:=0x23042421610002c21610208008384100000005848830400208084004181081508808200a81105842c340108081882c400010401610060400004128800006508824200028421410000c0162410800007085060424a100000220d0042c200002c20410018408210b0d0840000384082c412109080006109020848e84200508408200000000601881c2121000008bf14a22c388670ba10c1480f009fabe87c6f79ecbd479ef09d6ba8736e39c4b7c6ded69a6b48666c998cb0c5febe972ae05b6b3964abc56eaa952aa0536a1940a7c4ee9892aa504969191ca2c44e8890ea083f67d8f89ec3be748e29b83666b8d49a432e628be9782e65b8b095429e5089e9302464588890c20e3e8728d8196318608bc15e248428800f61b83085c0ae148268480860b81081401e02802800df4815ca209fd879c9109fd82dc163df5215c620aff8654931ff38148230fe92054930df7715c5209fd82dd530b7f8558140bf7815c520bbf844c1209ff815c163df771501209ff815c1539fd81dc163fe92048630df920dc530ff210dc5209fd825c640f755154131bf78148131df7815ca10df7815ca40ddf714c163bf7815cd209fd8798a409ff815ca20fd5514c131df97244220bf9809c910dbf74549309ff805c5639fd81dd930ded20dc963cfd764c620df4815ca40bf9808ca10b7f85581319fd82dc530df9205c630ff210481319fd80dc5539fd81dd530bbd849c910bf58158e109ff805c963aff8654940ddf714c963df7715cd209fd80dd9319fd82dc563df551dc131ddd215ce20df7714c120fe92050910df5315ca10df783dc5209fd825c630ded52dc931dbd425d640df610dd9319ff815cd20bf78148163df5515c1319fd82dc540ddf764c1319fd878ca109fd81dcd209fd80dc5639ff815ca40dbd54dc940ff110dc520dbf7458130ded215ca30df5615d210bbf844c110ff081482309fd82dd1109fd82dd540df471dcd20df77144120bbf845cd20dbd425c640bf7814ca10ff3714c120bdf8350910bf78148153df7215d210bf78158131fe52048531bf78154131ded7248640cfd764ca209ff815c963bbf845cd10df583dc520edd6358130df4715cd20df771dcd20ddf714c153ff0714c120fd5314ca109f7815c5209f7815cd209bf845c1539ef825c5639bf845c1639bf845ce10fe120c861097f855da408fd86dd5319bf845cd209bf845c1319f7815ca409f581dc163
def j111:Packing:=(116,3,5,0,0,11,0,j118)
def j115 (i:Nat):Nat:=0x30450ac641c0062400b2c00a0c8100000001c50000042a883a
def j119 (i:Nat):Nat:=0xdf2b688de6543ca1408fb4c102b944193f85dd1604c23ef22c16eaa062fe1b7454930cdbc26e2982411f79161e6290336f0838ae69056de5183dc5208fb4c0e2b9a419b784dc5734823ef22c16ea9847de4582dd110
def j112:Packing:=(12,4,5,0,0,6,0,j119)
def z282:Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffda8e80efa31334f8b77110a294fa2c140112476e217263,0x1a8204e622010a10823154424006181028000900212202),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe550613dee46b171e50184200e13000163a237ccc4483f,0x2550c011dc22916965caaa243f59e4c1d3e726bcc44879),(0xb8767821ad46b844808258e2a3253cf6ea13881040d8c,0x287218002942c96181045804080031c00109841008504),(0x2669d07e8c08ca07a98c101ac024d2c2804ca411f909a0,0x2428c05eec0a4201a424385293645c4328c32710b10ae0),(0x1554139111eda5cf49d49289dc948100804cc031fe5240,0x154130111e4b5ce49ca82ad2c98a38c923cd0654ed000),(0x253ba84144b4c40e1226cad10169ac341018648a03a410,0x2509e8114094c4ae18468a9400a0a6cc00bdf6de028450),(0,0),(0x38f01e2cfde810414683fb572913092a5d010800038410,0x1870162cbd68114126a930633d5f5823ff420120010200),(0,0)]
def z283:List zK:=[(160,0,31,0,7),(24,0,167,0,7),(2,0,189,0,8),(19,0,172,0,4),(0,16,166,9,6),(4,0,187,0,7),(1,0,190,0,7),(36,128,27,0,4),(136,0,55,0,5),(129,32,30,0,4),(9,16,166,0,4),(20,8,163,0,4),(14,0,177,0,4),(35,0,156,0,4),(56,0,135,0,4),(26,0,165,0,4),(134,0,57,0,4),(162,0,29,0,4),(152,0,39,0,4),(25,0,166,0,4),(168,0,23,0,4)]
def q179:List (List Nat):=[[],[115,84],[32,67,117],[32,83,116]]
def z378:Nat → Packing
 | 10=>q358
 | 9=>j109
 | 8=>j110
 | 7=>j111
 | 6=>j112
 | _=>zP
def q178:Nat → Nat → Option (Nat × Nat)
 | 10=>zk 16 41 5 10 4 2 q359
 | 9=>zk 67 277 6 13 7 2 j113
 | 8=>zk 100 251 6 13 7 2 j114
 | 7=>zk 4 19 2 10 4 2 j115
 | _=>fun _=>none
def vj:Forest := ⟨191,10,fun j=>z282[j]?.getD (0,0),z283,q179,z378,q178⟩
set_option maxHeartbeats 0 in
theorem q290:zp vj (z9 wT)=true:=by
 simp only [zp,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,zh (d:=3) ?_⟩,zh (d:=0) ?_⟩
 all_goals simp only [zQ]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q106:block vj 10 0 1=true:=by refine (z7 (ar:=7) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q210:block vj 9 0 12=true:=by refine (z7 (ar:=8) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q162:block vj 8 0 39=true:=by refine (@zn vj 8 0 3 36 (z7 (ar:=7) (rows:=0) (d:=0) ?_) (z7 (ar:=8) (rows:=0) (d:=1) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z359:block vj 8 39 31=true:=by refine (z7 (ar:=8) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z358:block vj 8 70 43=true:=by refine (z7 (ar:=9) (rows:=0) (d:=1) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem q211:block vj 8 0 113=true:=(@zn vj 8 0 70 43 (@zn vj 8 0 39 31 q162 z359) z358)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q163:block vj 7 0 49=true:=by refine (@zn vj 7 0 13 36 (z7 (ar:=7) (rows:=0) (d:=0) ?_) (z7 (ar:=8) (rows:=0) (d:=1) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z361:block vj 7 49 36=true:=by refine (z7 (ar:=8) (rows:=0) (d:=1) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z360:block vj 7 85 31=true:=by refine (z7 (ar:=8) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem q212:block vj 7 0 116=true:=(@zn vj 7 0 85 31 (@zn vj 7 0 49 36 q163 z361) z360)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q213:block vj 6 0 12=true:=by refine (z7 (ar:=7) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem z338:zD vj 10:=by
 intro k hk
 interval_cases k
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · exact q213
 · exact q212
 · exact q211
 · exact q210
 · exact q106
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j105:Lower true (vars 191) (z1 191) 11:=qn (hints:=536879361) (by decide +kernel) (zu (g:=vj) (i:=0) rfl rfl (z5 wT z250) q290 z338 (by decide +kernel))
def wR:=za wT 11 [(191,[]),(351,[133,117,101,33,48]),(367,[128,16,64,100,80,113,33,48]),(379,[130,50,81,115,98,65]),(445,[129,82,97,48]),(487,[115,83,82,130,99,66,16]),(494,[64,132,49,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z248:Known true wR:=z6 (m:=191) z250 j105 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j104:Lower true (vars 251) (z1 251) 8:=qn (hints:=1358970881) (by decide +kernel) (zW (prior:=z9 wR) (z5 wR z248) (128,0,123,0,7) (by decide +kernel) (by decide +kernel))
def wQ:=za wR 8 [(251,[]),(254,[32,67,117]),(477,[48,33,133,118])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z247:Known true wQ:=z6 (m:=251) z248 j104 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j103:Lower true (vars 255) (z1 255) 12:=qn (hints:=553656577) (by decide +kernel) (zW (prior:=z9 wQ) (z5 wQ z247) (64,0,191,0,11) (by decide +kernel) (by decide +kernel))
def qS:=za wQ 12 [(255,[]),(479,[118,133,33,48]),(503,[115,82,98,131,66,16]),(507,[99,81,115,130,65]),(509,[82,129,48]),(510,[128,49,100])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z246:Known true qS:=z6 (m:=255) z247 j103 (by decide +kernel)
def q229 (i:Nat):Nat:=0xa101820200dff
def q219:Packing:=(1,0,7,0,0,0,0,q229)
def q224 (i:Nat):Nat:=0xf7000e77c103400000000000000000b280000000001a4b0b8c000000000000015000008480000000000000000000194112c500000000000000000009001c000000000000000
def q230 (i:Nat):Nat:=0x78483828105003c2c241c081001a16120e08040018fc9e80ffd30ffd20ffd10
def q220:Packing:=(3,1,7,0,0,7,0,q230)
def q225 (i:Nat):Nat:=0x1a0061e14c19d5c5a27598680000000000003207a09d00f06fca2604001a05747a000c02a0632a3a120000109d96845565091300d62b409a8344e000080700011c7a19f03f077c040000000822823e0c5119904c28000f438003db8c0a34a9070001c8a000305800000000000000004850000002c9a000000000117400067e3258001171927a10d1320000000000000000000002dc5501700000000000000002040000000000783f09c0000006b0c6030438102340410100180000e040021000083
def q231 (i:Nat):Nat:=0x38620f83c121103058026140e0361305834086c0e80d0660485c2604230041a43098c2e0e04818021016905e13070242a0600104617068405902e16c0e0e0185812101c0b500b09834282cb000b604238303e1204850702d602006150384c182ce810601b0b84c182ce060ae0f050142c0109064aa82806c2e0e008280a10169098192785c220e010141049411034050584c1c010a0b08281e07c1e13040e4281900c03617098305981b84c1e0b0208361307824081ca00c260f020781214e018161707004202cf85c1e06050042180302806130685059e0585c260e0081059c0c00c2e1306828082d184c1e090a06281c0d84c1e0a028580230b84c1a080c50601a030041617098305a41409c260f0581041e0edfb9e61d09bd5b319b58ed74d63d52d3b12590dcf60e2cd40c54b8ca7c96c88077066052c464330268110003ffb02987ff46530ffea9a41ffd81483ffa62907ffa2520ffec4a41ffe39483ffa72907ff86520ffe8ca41ffd83443ffb04887ff54910ffe99221ffd39443ffa52887ef92530bff0ca61ff930482ffd12905ff62520bff1ca417fe19483ff240885ff8e510bfe9ca217fe29442ffa52885ef92530
def q221:Packing:=(30,2,7,0,0,12,0,q231)
def q226 (i:Nat):Nat:=(if i<1 then 0xc0699c07a0000f6a00000d0a00000d0a41a7310817080100800008266d0af00007b6d0030008ec08b0000741e0000303297bc87424243b0c7624c10564a700000749a04439091e0a73065106d165400000000ca280000067630ae14350000124a4006a062000000000000247e548200000000791b20cd0000a49d05560256000000004319348e596ed611e010f06bf6de361e27dd40c0e26d50abf0128094d09bd334e48a0000fbc580ac7bccc06af4a8a0724abc8767931b208a000020401087b070641a00000000c7a1c0b4e0a10038c49f103714a027a6a42bc2c5444070a2aaad573e8732d6b80000736eb07400008b703aa8e4d2f0930000c082c743200a0096c495006c55976020000000000000c2bd109d000043a70000e47bd061304ec09555c1405580cf84761492c03ba537405220681092b10f6076040460a80b73000000000000000080ce00002562000000004568000080d1648c00000000d0390000000085ae00000000c01e00000000bb742033e02c40010000000085050000c0d400007a43a08c204ab7a8e24dc2bf000062bb0000b2ba17250000f4d9e0980000b059b428504100000000875b000060bf7496904bc84330169197305f0000f01bc254b01a07d0641d000030d9c13f103d668d009e70512466e42aa05034adeac950b782a7824b67afc0b884a376d4624223def0900b6f2b1cc026c045c0bbb73ad0c352b940db1a55a04480d0db5540753262b05b503ca0ccb0d8109cc5bd60d23a1c113ad0d500000000721a3035b00d5088b0b6d2b3802b509a1029b02d10baf02ec04f3071b0df30244049641820da505d04d4f134726720adf06000006054f0dc28550000323fb9cd0000f04ca0c6608f502af0a3a63ec403a003c775c04210369077c105307e40de126fd391903460c98069c49c0000c956e0470000a1b9000060230000608380beb00fa07f87d5e464d085000020bcf0c2503a0354e4a20099e05a0002301c10c56073124607cf50dd41324019eaca503e836aa4d3554d259890b362375004846500000000dbc90000a60be1a5000044a7006f000000000000000000000000447800000000e0d300000000609f000020138053d0d7000000000000000042ae0000000000000000305826a94a2a90572043b42ff6448078f07bc1981bde525f9097308400001044020080502c0000c0200806000310181000c0800c020040000800008001341803c020c0040000e0000000400024000185103802060050000400c000741d000020240900c0505001060070040800c00148000400b01804060010180302c09070020001e0080a01c060340001000030040081f0040e0080101415000010080200405020020180c01002004010040101008008170000001c1f018090080600c060140308400040000181e0040400015 else 0xd00e0205c046877d908d000010c8e02500003154f0a9507c41b837d680b50000e0aa8028e63a4bb8b07dd06692a8549145291079000000000000b0b2f05ee6690199a0d6e2aa547a30a6d04df0483009100011de0000d85473b8200c0000c0e0eb549022e260e13e0015000002491018b74c3499142df12942bc00bd5064a0cb2786e089800bd03f7bcb50310000e027202f601dc005e2680a67000090a58014000040ca89667007000000007086476600b1cbca3480000010c160b09021848bd01ff06eb0b9f011aa4c02c18017c0c473d23067763200009063e05)
def q232 (i:Nat):Nat:=(if i<2 then (if i<1 then 0x3ffd9a4c910fff61539443ffd824e510fff54939443ffe8a4e510fff61529443ffd834a510fff54d29442ffe9a60530fef606494c37fd5286530dff625194c37fd5946530dff4a5194c2ffe8a46530bff629194c2ffe5a46530bff8a9194c3ffa0a46530bffa6953483efe6a60520bff8e9814837ff9a60520bffa69814837fd9a60520bffa6931483ff9814c120ffe54530483ff98a4c120ffe56930483ff91a4c120ffe4c289482ffd3aa2520dff54e894837fd31a2520dff4ea89483bfd8162520ffe4c189482ffe3a62520bff86989483ffa0a62520dff4c5894837fe1a62520dff46989483fed528e520dff62639482ffd8a8e520bff56a394837fd818e520dff546394837fd8a8e520dff56a39483fed524e520ff74c5394837fe894e520dff625394837fe594e520dff56539482ffe8a4e520bff96939482ffd5a4e520fef92939482ffe1a4e520ffd60619483ff93086520dff626194837fd3986520bff62a19482ffd3a86520dff54e194837fd8a86520dff4ea19483ff93046520dff625194837fd3946520bff62919482ffd3a46520bffa6983442ffe5a60910bff8e9824437ff9a60910bffa69824437fd9a60910ffb60952443dfe7a54910bff8e9524437ff9a54910bffa69524437fd9a54910bffa6932443ff98548110ffe60d20443ff95348110ffe62920443ff95a48110ffe4e9204437fd858e510dff60a394437fd528e510ffd54539443ff9204e510dff62539442ffe8a4e510bff62939442ffe5a4e510fef92939442ffe2a4e510ffe829394437fd854e510dff609394437fd524e510dffa29394437fd8a4e510dff969394437fd5a4e510dff8a9394437fd2a4e510dff616294437fd838a510dff54e29443ff5514a510dff625294437fd594a510dff4e529442ffd8a4a510bff56929442ffd3a4a510dff60d294437fd534a510dff629294437fd3a4a510def606494c37bd1a925309ff62a194c27fd5a865309ff4aa194c37be4946530bfe829194c27fc9a54d20bbf9a9814827fc9a4c520ff654d30483fe9524c120ff64c530483fba4a4c120bfe86930482efd6aa2520dfe4c2894836fd6aa25209ff4ea894827fd1aa2520bfe829894837f930625209ff869894837fa0a62520ff64c2394827fd8a8e5209ff96a394827fd5a8e5209ff46a39482fbe4a4e520dfd606194827fe8a865209ff62a194827fe3a865209ff4ea194827fe9a60910b7f9e952443fe95248110ffc54520443ff21a48110dfe482394427fd8a8e5109ff56a394427fd2a8e510bef92939442ffa0a4e510dfe481394427fe8a4e5109ff629394427fe5a4e510def929394427fe2a4e510dfe829394427fd8a8a5109ff56a294427fd3a8a510bfd869294427fe8a4a5109ff629294427fe3a4a5109ff4e9294437f61a4a5109bf5aa894827be4a4e510 else 0xe088070408108160c8f85e0cb82eb02c00b982d1c1854098300d020606819c098301c1c06ce0885bc202ec1c0e89d0a0e270202c10604070701b383781038041384c09810700b01cc50f0bc19700596846140b41f0207c1b3f0bc183e5c06e1b01676170000f020d68407c0b470bc1d0805901a4001c0c88806054230a1903860b30006702606840801c41080e064306c070380b20441a601c1d0ac2016162004a158302c9803060986605d0a128588e1383a140b2035c1f03c26040e00e701b85e0c98c0b00610204308108320f816505019c0a8107c0b070fc2706c2816407810c081d06a8106c1c46038003c01838191831c0385e10b0c04af0b91c205a0712780b06058588e178403c1260e8202c1c47081601c05901b04a8502c8158040950a0d80c6e100ba141227080950a059384e0f8201c2328540900c081029c040b01d820701b3d0a13e03803080f8367c0700a15840841e0a0270981c06d6070098070580d0ac184a8e1383e082408c1c06c0747074283b80e000bb0405836901c0e01822040a108334103e031785e128204880b808095040d80c600385e101202cac20320f8164c07000840ba08190582007d3c2706c2816407b01a080b074100701b4001c202e070165e1783c0b00068183709c1f058080e5d113403cf0b381cd03313cb9b2d7cb232b9ca5b24bc8f31f1c78b1abc5ab129c3a30bbc23b04dc05afd5becaf85bd12f0dbb5ae95b9cae45b862dd7b6aad7db542d23b402cb5b1aac33aff2bc5ae12b57ac82adfaacaa85a962a0da7aa9bda642977a4b28ffa322887a11a8059f6278d9d0a71f9ba26b1999a62597e25b79602549949a4ef92e248b912a3ff8f4a3a58d9232d8bb22bf8a4a25b881a1bb85ea14384320d582ca07b813a00d7f81f637cd9f097b99eb97a31e557879dfb7621d297419ce37289c4d7009bad6e29b676cc1b0d6ae1a6368119cd663195564518e7629987960e180b5f0176b5c816e95aa167158495d155c952753e94af51e144150013bf4dd13294bf12cf4a8927548f9211476917143d10c742690453fe8faf3db8f233b38ea139f8e2937a0d9d34f8cf33318c853138c032ee0b632cd8b092b20a732940a2327389a1253091f235087f21207fd1f4077b1ce86e51a4063b18385e11680573151850f138849711303d90e1032f0b40299098823507d01bd064013104100af01e00370003ffd5260530fff669814c3ffd5246530fffa6953483ffd9a54d20fff26953483ffd5360520fff4e981483ffd9a60520fff66931483ffd53a2520fff54d89483ffd3162520fff60539483ffd514e520fffa2939483ffd5386520fff54d19483ffd9a60d10fff54d82443ffe5a60910fff56982443ffe3a60910fff4e982443ffe9a60910fff66982443ffd8354910fff4e952443ffd9a54910fff6153244) else (if i<3 then 0x40120c8190ccc03816080c3381c1211490382022816481c9303c100380b340e4ac0c22920c02c121149030200588a402c100484520820e036366050e0f8261181820e2184fc230740b05039c07019840701b280e033060e036501c066081c06cac205216d030383660e4410701b23061900d038385608290b68181c1b300c0700e0d901fe101707082783e5c84041141ae0f0061702260e2103e100c840e4200708210161003e40801c130903e040e3034281670ca85c081c20220382a0d8385064070b70206c1c3052030220d80e0e190707c320398502cdc1d08c28164080191380bc0b0007ce0d085c18534230a101c0507c0b1b02020400583850528461417070b8130bc186580508161c34604200c80b070c42034190384c0b830a700a102c330205d081603856040b1341607ca81034160e004b4150682c2908168280d0585050130682c225a2250a1c81610182210c4ea141d02c2038080d04416102200c1a0b08198221680e0705860801101c0b0b0b038360708819016613584a141c2032198340e13841342da141c2f02100898050a0e604c221830f4080cf02a141c383226083c202e0e1b84044070382c282204302100585e178300584080a80038058d840e42c02c1c2930148340e10840b0340c81a070c1900e0d0384c09832601f6141a10e8144c190b3006308160380590980141a0708030160e0d8405c0b07084c30a058384a043905c0b070a0a082080160e140f4181c1d090603604088125040586580306ba1045c058507c120cb00a09222016160c0702c1c1d0425e00058940f9893c040c127000b184a0d02408fc2f0980e00539d850e424018220430024d023058128c950481c1816230241604a50e40b070616a3180858c18414102488191801c0b03985c0682405a8c08b80b061030b410249808140b00b070a8c05a16026058386460070440b070a138574283a0d82460538302c1b208613f080950a05981801c1208090c0520380c058386a140f6101c20362208b42926c240c7a1584108410540f8181c450ac18720600e090387e100e01c23080ac105219d0a0584060a80704006070a1584813c0e21e000e836092582e0c14c030106cd0381c0804f8087a0d824c1270081c44610280701b380ec20380d9382c003d0498306c1c3b06038240e03650a7836082006cac1016038200e036610c1061019a0812306a09032c2d04c240c707c434601961682048e0600c1201640418402c1c2306058240e11186140b07080a010210160e14272541207081c882080160e158581b01a083502c0e065840414c2a300fe02c18160b8320704408024c0101702c1c2230080160e1198e0f8282a096118182102007808f06c087e041c3e00e81e0984070073824027041ed0203980f00e81e1182070073d021e076088460e03604200 else 0x103a2649c308393060a83e0982241c98301c081260940e2918171441a0640e148c0d0320980e0b8a46068191144324304c03e1010200840108034203e0d0e8407c170c81a0cc0e3858160607260320800b058e0e060708a850c84528581385b408340e1a8105c100480b038c1507c038308312a60b68207c1b2508c18880a128260c930cc49134c1cd04c284c0a16826149504032134c22894058c450601402c9099260940c4a83261281204093144a070a20592609140b0))
def q222:Packing:=(225,3,7,0,0,14,0,q232)
def q227 (i:Nat):Nat:=(if i<1 then 0x162c394547813402c00000508ea82ac1a81b473db348b2ec0000c13000005a2b8c133e13ab65580001c1ae00004007902740206612700004301c0266000080b495c60407a00000000005feca344502000000000000168c1560204c698343a0e5d090c1e809126000060ab04e680001a0f8d073005c4402000003720a01fa80e060e2b0cfc839d024400000000602f6823fe89fe06c05d5cc06140ba90c09a17009fe0000b2a6193d351e60000e00fb021052caec382039b00a7003ac0525407b0469c1455747000075d15c0c8019a201912aa442af61a5804990594c151a5a7000000001e0800120303b801c5c0060000000000003413c685e60bf485b66dce017d50b78000341f73748f464c90ffc1f8a45d9053811dbc33c000000000000000018002000000000009944cfaba57935400000000607480002c2f765325083ddd2442a80000518a5841a888ea015f2a10000000000000c05ae52a9c0aa005d000040352661561632085781ed1ebe4040c0d40951d93356075000048053826e8efa00005867400000000000000003116e698100005de8000ca40d3c09b20588667b098690a4a002481e940e800002015c00000000a040002fa429cef3d00007919e0323600e00000000242a4000080ae7a2fa184c610b0000782c680a800000000381f41df0111850c100000d2e7a046d0cc126494f460000000040578000060630000410f40001c8f9a08050098000000000000703fb8136000050768000000000000407c80000000000000000000000000a04b0000438f682a1e15510d1d010e8050959000007020e6eaba0f7500d206380000809100003346102f321732423002ce00cfc44b00243030e42906714a052580ba4246000087831181a087cf4d49155985990278000077c8a80fc19860000b00bb82a942ee0000c0810000000000000d05000000c34c00008092c11980001819500000000000000000e02200000000000000000000009e7616920000000000001a0960000283fc0000c07400000000083180000000000000080000202c06000130080100001024000240300c0000400010000000000c0102c110000200c010000000401000040180b01801008000040100806000010100100402000020180302c050000101801008000000700809030000140c00400000020100200c0901c060080e00002010020000b0000201400020020140301000028040040a0040500808028030040004405008000000000001084030200100c040240100001000040000a034000080a0040000406000010040001c01004050440200003004030740200002020040180204005000000000000407000000000200c0601c090000001c0000002000000200401001000020080000001038000040a00c030040801000000000040004002004090000001401 else (if i<2 then 0x5c5269c00000000e01df022c02c265a8044318602c0f0005cf023d85d212e3414740ca301a79b4a000000004062c00004031d408c0014c9f161316000b0625d121371b00c38000000006128000000000c06c6987000c00002554be1750000183b80138000060a5e3e2f00a6000000003c46b51ed811240ae80000814c00610000504b400000000e3238000001f4000000000000281a20000507a800000001a4066066000039723e0240000385d8687a0000c47a0000141de0000000000003421c0000b02f9006f002200000000084580000e600801a53102023c0000000000003016dd00d000000003c34800000a52c013c00000000c028981144558006ab06580003526cc206102d4061400000000100380000000000000000000000001e0f100001002000000000908600000028a205e820ec2c59c15a606660a3381b000000000aba6552ac426520c2aa9e00002c72242c51075fa185c015c09464579dd1a00ece168d430480dc802d65910024f8672c4eb608f44b968214073f61097070781e4000060dc000040567009c0000f0cb8000000000000206f60237e190a186a0ccd88e4000000001b23f02080001e0210000502dc00000000703f80001c231c16bd1be00001c14a68b290b900002421a0000e04b80000000021530000000020125a5aa402800001434ea0fd9037800000000000050962263c00018590729e000015b3e0000682380001818301240000204f40001e03e00006037e028500bb7a7980000000000000000580ea424c00000009800000000000000003a64e42d900d080a243bc400004101f0be00001ae9b60dd409c300940165a03cf09a5a29c000123a50000705aa810e000000003826302dc0000000000003901b685bc62380000000000007016382324ab5f75600d000001c1908533fb3a000000000e8d000000836c018fc0cda01c99417805be44f40571043c0000000000007309c01120000a0c27031bc1ab20ea00003033b13048027508dc84a641e15316545c8000340da0000200cb038d52c40000605c886280001218300000844000000000d04479c600001453d50035a62f401b402af0c9683daeeb0e06004bc6854490b08086e0358000183520000d0c68000190bfb537984180003c0e400000000000000001055620604a57912c80000b025000000001612f00002008c00002033000000000000000000000501e881c9e13900005c984c11428d7000000000d19400000000202a710bae167720c784d69db9cebd10c7a1b9c8d9264561069284fd01954012a0b20000092dc8105eb39e831000016062c0a780000000048c30000000000001666a0000584f990280000000000000000074ca705601e44413400006763b02fd40d1886290b82215c42220000b0c423be48226000000000000241d8000046643016c else 0x20505932c000090bc6027f822fc020f09d9066e88c02518c59c0000202080000757a2c045df1b205900afa065800004114049d404af416802a489a7794b24019406e1152e11089e78000000000000000000000802093b1800000000000062641025d087f405e72e3cc3547594ea49705280344000000000828c0001408180ac000000001c8bdf02c2850c00000000d0c80000000000000802150314000000009bd180002003984ef6058000010a88e884a0709033c81420000e4bd800000000801e0000604579996000040c98000000000000098e8000000000000206c800000000802fb265621e00001e08eb0648000181e6000000004815901e5c140c4418000000000000000008240004400000000000000000e108000000003c2b400000000581f00000e8a38230c80d4d11646650000705e80000815b30020000041ac0000501c1cd67815f2095b983e802e4057a11cf2a5000018233af9af0a61836a4254e14de))
def q233 (i:Nat):Nat:=(if i<3 then (if i<1 then 0x56a394833bea8ab51ca411ffa2d5a8e520cbfcf6ad4729047fe1b56a394823fec5a351ca411ff56d1a8e520adfad744a729063fd89a29394837b6a94b49ca413fe82d5a4e520df5aa5252729067be89929394833dec4c949ca419ef9664a4e520cf7ab3252729057f69b606194839fac0b130ca415ef92d3986520edecd6c0c329047fd3ba2a194839fac0b150ca411ff8ed8a86520cfeb031d4329047fd8b8ea194823feadc750ca415ef92d3a86520cfeb029d4329047fe8b4ea194823ff2da750ca411ff56d3a86520cf7c969d4329057be4b4e51948277f35b148ca413fe82d8a465209fdc569d232904ff90ba69834423fecdd34c1a211ff66e5a609108ffb371d3048853fd8be6982442bf695f34c12213fd46e9a609109ff2174d3048847fd9ba69824423feadd34c12215fb8ad9a60910cbff373d2a48865fd9b9e9524423fecdc74a922197f9eb9a54910afda57cd2a4884ff90ba69524432ff3d334a92213fd46e9a4c9109ff2174d2648847fd9ba6932443fb4a9aa490221f7a9ed5248110bfd456c5240885ff21b62920443fb8a8ab49022177e9ed5a48110bfe436ad240885fba4b4e920442ff90da7490221ff854a1a48110bfe2b70d2408855fe7b54a39443bf4a92411ca211ff96d8a8e5108ffc56c54728847fd8b56a394423fec5a551ca211ff56d2a8e5109ff416c5272886f7551969394437daa8c949ca21bee4824a4e510cf7b1325272886fe9208a9394437dd254149ca21bfc5460a4e510abfcf6a92728877e952481394423feadd149ca211ff4ae8a4e510adfcd6c52728857de3b62939442bfb0db149ca215fe82d8a4e510cf7c96c52728847fe2b629394433fd05b149ca211ffa2e5a4e5108ffb172d2728847fd2b96939442bfb0dab49ca215fe82d5a4e510ef7241252728867be8a929394433dec54949ca219ef96a4a4e510cf7ab5252728867bd85929394433dec14949ca219ef54a4a4e510efd241152728867be4a8a9394433f6a94549ca211ffa2e2a4e5108ffb17152728847fe5b8a9394423feadc549ca219ef9292a4e510afec36952728877ba4a8293944337f35b1514a211ff96d8a8a5108ffc76c54528847fd8b56a294423ff45a7514a211ff62d3a8a5108ffcb69d4528847fd5b4ea29442b7f35b1294a215ef92d394a5109fec36c5252884ffa0b629294426ff3dab494a213fe82d5a4a5109fec369d2528867f589869294427faadc3494a211ff4ee8a4a510adfcd6c52528857f61b62929442bfd05b1494a219bf9ad8a4a5108ffc76c52528867f61b629294433fd05b1494a211ff62e3a4a5108ffab71d2528857be4b4e929442bf715a7494a215fd86d3a4a5108ffcb69d2528847fd5b4e9294433df25a7494a219fd86d3a4a510cfeb150d2528856be6b606494c3fa4a9aa498241fd85495148110 else (if i<2 then 0x21dfb609528e510affd16a94728875fe7b54a39443bfcc2a411ca219ff5498a8e510cffb04ad4728867fd854aa394427fe55b049ca2177f9ed524e510dfeaa345272886ff920a29394427feadd149ca213ff4ae8a4e5109ffd172d272886fbe8a929394437dec2c949ca21bef60a4a4e510df7aa525272886fed528a9394427ff45c549ca213ff96e2a4e510dff51505272886ff98582939442bff15b0a9ca215ff2ad854e510efdb04a92728857fe8b54939442bfec5aa49ca21d7f9ed524e510aff956a92728877f985481394433fea95149ca219ff5498a4e510cffd152d2728857fe8b969394433fec14b49ca21def6164a4e510ef7aa5252728877ed528a9394433ff2d4549ca215ff96e2a4e510cffb0b152728877f98582939442bff1db0b14a215ff96d838a510eefb0aa9c528877dd8354e29442bff45aa714a219ff60d5a8a510cffb0a9d4528857fe3b62529442bff45a7294a213ff8ed8a4a5109ffc76ad252884ffe8b4e9294437fac2c3494a21bfd60e1a4a510dfeaa70d2528857fe5b60d29443beec1aa694a215ffa2d534a510affb16a9a528867fd858e929442bff45a7494a219ff6153a4a510efeb070d2528877f553869294427fc85d34c0a615efa6d8192530ed7cd6c0c929857beab606494c33dec523524a619ef4a91a92530af7d168d4929857bd8b46a494c2bdf2da3524a615ef8ad1a92530abfcf6a94329847fe5b62a194c23ff15b150ca611ffa2d5a865308ffc56ad4329847fe8b4aa194c23ff2da550ca611ff56d2a86530cf7c93452329867be49629194c277f35b148ca613fe82d8a46530cf7c932d2329867be498a9194c3bdd24c148ca613fe62e0a465309ff2174d2a69066ff9b9a98148337ecdcd4c0a411ff66e3a60520cdfcd5cd3029053fd8be6981482bfa8df34c0a413fe42e9a60520cdfcd4cd3029057f61b669814827f695d3498a413fe42e9a4c5208ffab64d262905efa6b60530482bfc4daa298241ff4605314c120bfb476c5260905fea2b62930482ff515ab498241fe654e4a4c120ff52a525260907f9931929304837f4a943498241bee9291a4c120bfd4568d260906ef9305aa89483beca9a6144a41dfa54930a2520efb262985129077ba4b4c289483b7c982d544a419bf54d6aa2520cdfad49d5129067dd314ea894823ff2da7544a411ff56d3aa25208ffc369d5129047fd3b46a894837ec98474c4a41bfa8aa0a62520dfd2a505312906bf981829894827fc8dc14c4a41cfe6053062520efb262983129077ba4b4c1894839fac0c34c4a411ff8ee1a625208ffa770d3129056fe6b469894839fcc0c14c4a41dfa8aa0a62520ff92a498472907f9a4b4c239483bec983131ca41bf64c15a8e520adfcd6c0c729063fd8162a394823ff2db151ca411ff86d8a8e5208ffb172d4729055fe7b else 0x93ba4a291b243690023ca8e523328bf22b089ea218878a1ac852a0fe83220928119ffa7eb9f4c7c01eb479f9e4877f1dc675e9d4473e1cac71d9c406fd1ba86dc9b3c6c19ad06a11a4e68619e266b194a63f98de624985c60417f05e9176e5ce17025b3169659295fe572159255194e452b946250b13b44da13324bf12c649e924448391c2463115644810ea42d10684070fd03e68f383c08eb639a8e083640d5a3490cc23230c2a2f78b922d18afa2b10a782908a0c270098a24f88f2229887020e87ee1ee07821cd86ea1a7866818c85fc1718590151050e13604a211b04200fa839e0d4831c0ae826e08881ec04c80a40005fde3b669814c3f5f35b0324a61def66d8192530ef7aa4c0c929877bdab606494c3bdea923524a615ffa2d5286530ebfcf6a94329867fd5262a194c33ff15ab50ca6177f9ed5246530ef7aa524a32986fed528a9194c27ff2dc548ca619ffe6a9a54d209ffb174d2a6905ffa0b669534833fecd134a9a417bf5ac9a54d20ddfaa735302906efd3b9a98148377ecdcd4c0a413ff56e3a60520ffb136a9a60907fd95360530483ff4a930298241fbe9ad814c120bff4b6c0a60907ff18154530483fdcc0c94982413ffaad53a2520ffb2a698512907fe9524c289483fdd25a6144a41bbf54d6aa2520ddfc76b5512906fed524ea894827ff2da7544a413ff56d3aa2520affcb698d129077f9514c2894833fea8a7544a419ff54d1aa25209ff956a9b12904ffe5b8e989482bfeada62c4a419ff54e1a62520affcb6c4c72904ffe5b62a394827ff45ab51ca415ff96d818e520affd16a8c729067fd5162a39482bff45ab51ca419ff6055a8e520bdfcd6c0a729077ed52a2539482bfeadd129ca41bfb54a8a4e520cffcb3452729067fd59a29394827feadd149ca419ffa265a4e5209ffd172d2729067fe89569394827ff45ab49ca41defa264a4e520df7d1525272906fbd8192939483ff8c0a610ca41dfd6053986520affd169cc32906ff5814ea194827ff45a750ca415ffa2d5386520efeaa6c0c329077f5814ea19482bff45a750ca415ffa2d39465209ffd169d232905fde3b669834427fe55aa6c12213ff4ee5a60910bbfcf6ad304884ffe5b8e9824427feadc74c12217ef52e9a60910bfea374d304884ffd3ba6982442ff715b34c12217fd86d9a60910bff416cd304887f6d5360952443fb72db04a9221f7b60a7a54910dbfb073d2a4886dfd3b9e9524437f6c1474a92213ff62e3a54910dbfcf49d2a4885fee2b4e952442bff4da74a92213ff4ee9a54910dbfcf4cd2a4885ffa0b669524427fec5d34992217fd86d9a4c910fef30aa9a40887fd98354d20442ffd45aa690221ffa60d5248110ffe306a8a40885ffa8b56920442ffd45a7490221ffc6161a48110ffe3070d240887ff15386920442bff15b0b1ca)) else (if i<4 then 0xe04030000382a0c0780003830420780e01b202104007c60841001f180b03e20160b0414405820180b038204202c0f8c2186410560160b0618c3105318610a6208a14c405c1e853180007a14c60002988160601010038201007040780e01b182d058205814c40b00e080581c100e05a01829902284c0a630a610220382a0c0581c102c03414c614c3a142f8531812058202406c405c2b0821856101b0582062094160c0005e0383024080408c10081180e0a8301e0d42a05d205203820480782a0c03020160709010c2e04928020580706110128811054101c0b620000a00d8f8001b1207036201a07c100c2681b1701044207a15040f40e0826854105202407061480901c1b8201c15060882a082800e04408080382a082d01c07e304603c2c8dc10200380fc8e081185801f01ca1482a0829054104470603816102205410210880800d901883d0a8308606c100c2b81c07e306a0002a0c0f054103a05615861102b0829056102103e08060882a081081f04030620f42a0c21822040381607041142a082880b040301608041142988228000a630000382a0c0200b038301c14c40d42a0a0581c1045016208a02c40e81005518260362016080402c10081102c103108614c61142a08228000a8308a0002a0c1e854103103c0b012900681c07e306a0002a0dc2020160ac126e0dd783f05820dca00d01940e44c0e025302c03409c0900e04a14cf8a2e23f87761a7856e0f9830e07781060217f55f737cf5f1d7b9deb17a45e5b7895def773ddaf75e5d437435ced7285c81712dbff6ecdb7d6d1db276bc5ad16ac5a91696da3b68159cf666593763ad89f61a58335ff57dd5e9d7875d457315b9569959e5643588d603573559755dd557542d4d552d549551254134f753bd4e1d3674cc52fb4b152a54a1526549151e346b516144ad0f542fd089414d0333ff4fdd3f4cfc93e4cf5d3c44ef13aece6f38e4e19378cdc3368cd6d3534d173384cc132dccad3234c6d318cc5930e4c192fe4bd92ee4baf2de4b432c34aed2a84a812984a2b282c9eb272c995257c91323748bd227487d21748111fc47a51dbc7391bb46cd1ab467717fc5df16fc58914f44db1294485119442f103c3ef0ee43990de43430c342d70a84281092c22b082c1eb072c1ab05d4155047c0e902cc093017403d0073fe6fec3f0cfb5be74f84bddcf69bd70f4ebcc2f1dbc40f02bbd4ee23b52ebc3abaea13a4ee80b9cce65b960e4ab8dee2a3872e09b7f0deeb784dce3702dadb66ad87b5e8d56b4f8d30b48cd15b420cfab39ecd4b31ccb4329ac93b218c78b1acc5db140c323092c11b010bf6af8ebd62f22bb5aea0b9aae1eb74ad9cb542d1ab392c98b132c16af2ab7ead22b12ab72a7aa912a0ea7629a2a5b2920a3aa89ea14a7f09e3a7429bda6c099d262897ca5a695c2524 else (if i<5 then 0x308609c41e820b024607184a022150071008052105408510a42028114419021c03c880d019101f04020ca10ca10ac10c40680c880e01b101c082008a0986064207c0d880d816078309a117420c0701a100e03420ea103e06841e0206821d0211742082a0410012104309c203210c42840b81a01c403205c290c1001c04a303210c40d40b88220511053084407220a61044110414c30c41c8201e070401dc61d020d43a0822043a040ee851045b0820e810e810e01d80c8c0a045107508750b8103405860580588148221074081601620e81032088426011080b0221074085408540845082400e114399022806104d0e41c46114030822848107001e20160504018228807840584d105e0800094298837848106e0c212060e4211403087686408630a200041902018228829842984030451035081300e20220b440c8200053083208000b021582088214c214c2005606c40481e882181d10540e070581206110206c2116c2082a042a042a0422823102301e201e08c070c0780e1054085408220803085406a160615021340a022183d04e209210c41b01382c18540827082208828430782684304e50a810a8101c0f441402a0351b820ae15007100100e10540854084303a200610ac108805440402048203c03081a815104303a202361041502018228829842a04018402040184220151012080b08a203210c410c0e882a042185810040803090703620380fc5e0fc161e09f82b049b9385d07e207808c2e83f20110d608c2a1035054105d07e20d215041a02a0b408430b81270394218440b2309416440f42c8825059102108815060f42a081883d02e07080882a080e03f101b03820000d42f0c0705410520a8201215040980d880001b03830aa19441942a882281f058303e194409005881200b100002e08060802a880001f040309a0002a0c268000a8307a14c5a14dd026e0581c10181301200e15080800d881a01c101b03820a407040701f8808c080ba303806c2a0c0e02c100e02215061480e080d0550a8303e06c40680f880d854101b0a820aa150408381700016154a1542a08008220a8307a150407c12881081f0a830a806c406c0e081903403830280b040800e082503204030580980e0c0d81c100903617460800f881601b101e03806c61341301c181403e20640d00e0c0b81a038303417440680e082981c168505619c32900581f1044036205806c40880f880b853100107a14c60f42988178430a630480b0298c108440160b080c4000430a640886e02a0c07032058304a0b040000b81c184101c0b060382a080d00e058301c15041980702c180604020720800e0c0b05411b80ca206a150405810081301b103d00808810101102c103107a14c60582a081e81502c06c80882a081e854103103c0b01290068220a8308a15040800e0800 else 0x3987041b909e33301503987c21933302080198cc0e0f0400d664c805804083d827058)))
def q223:Packing:=(427,4,7,0,0,14,0,q233)
def q228 (i:Nat):Nat:=0x2d31e04e409441e80000001c06f00380000000000100c3816e56a0003010a1b2a03200030208026f04420ab5cf80000001a0e280ae8350000e00c000000000000002c17223600000000917ca39f06306f581e0000144aa0270140000b08884c5c46301e70000003cc30000000080bfccd800000004d0380fb014307e6049819800e071b40d3116623380100003c07b830d65a0000821083b3015c10e8015dbd4046a0b7c590000606d68b6c1c8000000000000000000000080700000000792e000000000000000005c0000000d080000100353b000010010000281d0001803349ac0010000000000000000000000000000004023e26ec058000202707030100000b41c80f941950377049a0a501d730c005600020068dc0b02000000006a21f18640b180d68c0d00a000000000000600000007010c060226000107010100000001000004000001040100020300050803
def q316 (i:Nat):Nat:=0x3f839880342107e0e0f040ec2004a081a8400e00f22000d00c8807009440000070094464e103c080700d0800341025080d8408006c094786210700761000000330408820cc10000000308707840fa106608000d8103508358400002284081003807e301b02501f181000e080001608360400a6100000003a0e6f8ade768d5f52d0730caf0ec26ecb3ecab16c0a8e92a066497e4e8f62c80df2755d072dc6705b067d8e625845fd7a5d57054d424c52c49d16414f43bcea394d433ca61f46016c56114340bc1e0641403c0a01400d6be6b66d8192530d6bd529ad8192530d6bdac9ad8192530d6be6b6ad8192530b5be7c5491a92530d7ad528ad1a92530a5fe7c5498a86530b5be7c54a4946530e7ad529262a4653087febc6689a54d20c6fd9a5ac9a54d20bed96c26d534c120ff489c54d524c120ff4953549814c120ded9539ad814c120dee9529ad814c120d7f18126d514c120ffc152605314c120fdaa7c54a4a4c120beba6c6064a4c120ff495354930a2520eed9534c16aa2520eee9524c16aa2520f7c9524c530a2520f7a95292d30a252087fcac56d3162520a6fe6c6055a8e520a6fd6ca255a4e520aebe6c6064a4e520e7ad52a264a4e520a7bd5ca264a4e520a7be8c5664a4e520d7b58192d3986520b3f68c54d8186520d7b58192d3a86520e6f66c6053a86520ff498354d5248110ff61835495148110a5fe7c5498a8e510adbe7c54a4a4e510a5fe7c54a8a4e510a5fe7c5498a4e510b5be7c54a4a4e510e7ad8254a4a4e510a7be8c54a4a4e510a7bd8c54a4a4e510e5be7c54a4a4e510e7ad5292a2a4e51087bdaca6d819253096be6c62d1a9253087bfbc9258a46530c6be499ad8a4653086fdbc9ab9a6052086ffbc9a99a60520ff095354a4a4c120f7495354930a2520f3d1814c53062520a6bd6ca264a4e520a5be7c5664a4e52087f5aca6d818652085fdbc9eb9a5491085ffbc9e99a54910fd627c5495148110a6be6c6264a4e510c3f68a86d8a4e510c6be6b92d8a4e510c7765a86d5a4e510a6be6c62a4a4e510a5be7c54a4a4e510
def q313:Packing:=(69,5,7,0,0,10,0,q316)
def q315 (i:Nat):Nat:=0x30500000281800000e0a8248100120000000000
def q317 (i:Nat):Nat:=0x64e1002685c28502a97cfaa94d6c0c92985f925b49c54d524c120ef24a9aa535b0298241fd09539f15292930483dc92a6a9260b551290496f9f58c54a4a4e510
def q314:Packing:=(6,6,7,0,0,6,0,q317)
def xusamples:Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc5d08196a6ab94f2cc0a2ac25680a4208344800af404600baf816401410012b19a81841c60c000c42020805074b337509a3308401433e21f673,0xd0800682ea0c92840000c0048172150480931233116251411ce40830401291860184746083044020a0801024b220801232884808224212652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd845701f1d11913202dc0733613022d37320007400800ad1afe020260200042200c22a0182ce0e23c1a30c625943a822604c0ef4400c8c6487f,0x180450191c01810002588723414c8c02232008a5840c9da018e001c34a80042210c21a81837c418141120c6259418c644008042442088c44829),(0x24838aa0756a21466e610150ba833388387300602bdb8190000420200120421c041c13c6063acc2b68c012038e7c000204603082518f1078f9c,0x24038ba0014e004660200050988072894082174842410058c50060381174421c001c0546040082603ee110010028109a0470218011471038514),(0x197c742262611d0db214d4442210696c0a51cd90211b80201007090088c098c000603967fd2100181402e03c0e0000a007807e0da9f01f80fe0,0x194874026221140882068084264d01702b41c810a41a00a00a3e0f44420a18c0026020a1513105064002e2580e0024208300de050ab00b00ae0),(0x24239f791d94e161f9b06f2bd910880890006d8ccca42002000100228941cd201b010e18010000c4004c003fe000c10007ef000dbc401fff000,0x24230b791d14e16179b06f3bd91288089008248d48e49506b4c100b38d95c52019101b08040c4ab9965d0027d000d35c04cd0100b44014ed000),(0x9292ca9480cd64d0bf20125add4044a265eb203100058084008c4f9441f200001eec0000000b000005efd800080df7bf810800597bfe000000,0x12924a94800904c0bb20102a85c0548225204a14442950806e00b35419b280001ea60000530a0a7504b5b4000000132e8000105959da000000),(0x336b26e0e8f854fcc5a748cca028013148c3c0162820064c00763206330137dfe00020000004b300ab010000010001267fef3ff000000000000,0x236b24a0e0f8547cc5a748cca0231131484bd7126873001c271e2e14151bbac94a0024000401bc3eb801020000002392bff7bbd008000000000),(0x3adc5057929368b0852dfca4026310028d2dc2073ae461020007108a80325000041000800010f000294effbfef7fc8090000c00262000000000,0x1ad45056929168b0840dfca4022300168d2dc806b9bc62a7381f94c2ae0090001e011080000f5d188114a4beffd7ee450000c00a6a000000000),(0x696cb5c93062b8b3008b689c98c626490e3304010243c24501a9b52b4ad77dfe1eeca3ffac10110161000000100c8850000410260000000000,0x4948b5411062b8330081610118062869480204813042a41d000d08a28644536b4159b5eaace424006b000001180d84d0000000a60400000000)]
def xucolumns:List zK:=[(1,0,510,0,12),(2,0,509,0,12),(4,0,507,0,12),(32,0,479,0,12),(256,0,255,0,12),(8,0,503,0,12),(3,0,508,0,9),(9,16,486,0,8),(9,0,486,0,8),(24,0,487,0,11),(17,0,494,0,11),(7,0,504,0,7),(134,0,377,0,8),(144,0,367,0,11),(96,1,396,18,6),(132,2,312,65,6),(14,0,497,0,7),(28,0,483,0,8),(35,0,476,0,7),(36,128,347,0,8),(260,0,251,0,8),(264,0,247,0,9),(130,1,332,48,6),(24,4,353,130,6),(258,64,189,0,8),(296,0,215,0,7),(21,0,490,0,7),(260,8,227,16,6),(98,1,396,16,5),(288,0,223,0,9),(0,16,486,9,10),(168,256,23,64,5),(21,2,424,64,5),(0,64,189,258,10),(256,8,227,20,7),(19,0,492,0,8),(16,2,424,69,7),(257,32,94,128,6),(136,256,23,96,6),(36,0,347,0,8),(129,2,312,68,6),(26,0,485,0,7),(266,64,181,0,5),(16,256,135,104,7),(26,4,353,128,5),(33,0,478,0,9),(35,128,344,4,5),(132,0,379,0,11),(160,0,351,0,11),(0,128,347,36,10),(268,0,243,0,7),(289,0,222,0,7),(257,0,254,0,8),(0,8,227,276,8),(224,256,23,8,5),(200,256,23,32,5),(320,0,191,0,11),(258,0,189,0,8),(66,0,445,0,11),(49,0,462,0,8),(344,0,167,0,7),(256,32,94,129,7),(281,0,230,0,5),(276,8,227,0,5),(6,16,480,9,6),(1,16,486,8,9),(2,64,189,256,9),(0,32,94,385,8),(160,256,23,72,6),(64,1,396,50,7),(32,128,347,4,9),(129,0,382,0,9),(3,128,344,36,6),(292,128,91,0,5),(18,4,353,136,6),(256,64,189,2,9),(4,128,347,32,9),(64,4,305,138,7),(34,0,477,0,8),(83,0,428,0,7),(272,0,239,0,9),(1,32,94,384,7),(4,8,227,272,7),(167,0,344,0,4),(15,16,480,0,4),(120,256,135,0,4),(355,0,156,0,4),(20,0,483,0,8),(288,16,198,9,6),(297,16,198,0,4),(48,0,462,0,8),(324,8,163,16,5),(154,4,353,0,4),(178,1,332,0,4),(334,0,177,0,4),(416,0,95,0,8),(385,32,94,0,5),(128,32,94,257,7),(384,32,94,1,6),(200,4,305,2,5),(428,0,83,0,4),(197,2,312,0,4),(256,16,230,9,7),(352,0,159,0,8),(20,8,227,256,6),(112,1,396,2,5),(272,8,227,4,6),(16,8,227,260,7),(128,1,332,50,7),(152,0,359,0,8),(24,128,323,36,6),(264,128,83,36,6),(7,16,480,8,5),(7,128,344,32,5),(388,0,123,0,7),(275,64,172,0,4),(157,0,354,0,4),(141,0,354,0,4),(21,128,330,32,5),(12,64,177,258,6),(199,0,312,0,4),(56,128,323,4,5),(185,0,326,0,4),(128,2,312,69,7),(265,0,230,0,5),(156,0,355,0,7),(320,16,166,9,6),(329,16,166,0,4)]
def xuautos:List (List Nat):=[[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def xulevels:Nat → Packing
 | 14=>q219
 | 13=>q220
 | 12=>q221
 | 11=>q222
 | 10=>q223
 | 9=>q313
 | 8=>q314
 | _=>zP
def xuindex:Nat → Nat → Option (Nat × Nat)
 | 14=>zk 6 53 6 10 2 4 q224
 | 13=>zk 22 107 7 13 5 4 q225
 | 12=>zk 142 533 10 16 8 4 q226
 | 11=>zk 221 1001 10 17 9 4 q227
 | 10=>zk 34 161 8 15 7 4 q228
 | 9=>zk 3 13 4 11 3 4 q315
 | _=>fun _=>none
def qB:Forest := ⟨511,14,fun j=>xusamples[j]?.getD (0,0),xucolumns,xuautos,xulevels,xuindex⟩
set_option maxHeartbeats 0 in
theorem q286:qc qB (z9 qS)=true:=by
 simp only [qc,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,zh (d:=4) ?_⟩,zh (d:=2) ?_⟩
 all_goals simp only [zQ]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z392:z8 qB 14 0 1=true:=by refine (z2 (ar:=9) (rows:=1) (d:=0) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z393:z8 qB 13 0 3=true:=by refine (z2 (ar:=10) (rows:=0) (d:=0) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z394:z8 qB 12 0 30=true:=by refine (@z3 qB 12 0 13 17 (@z3 qB 12 0 1 12 (z2 (ar:=9) (rows:=0) (d:=0) ?_) (z2 (ar:=10) (rows:=0) (d:=0) ?_)) (z2 (ar:=11) (rows:=0) (d:=1) ?_)); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z342:z8 qB 11 0 64=true:=by refine (@z3 qB 11 0 2 62 (z2 (ar:=9) (rows:=0) (d:=0) ?_) (z2 (ar:=10) (rows:=0) (d:=1) ?_)); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z254:z8 qB 11 64 64=true:=by refine (z2 (ar:=11) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z180:z8 qB 11 128 59=true:=by refine (z2 (ar:=11) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z179:z8 qB 11 187 38=true:=by refine (z2 (ar:=12) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem z395:z8 qB 11 0 225=true:=(@z3 qB 11 0 187 38 (@z3 qB 11 0 128 59 (@z3 qB 11 0 64 64 z342 z254) z180) z179)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z344:z8 qB 10 0 3=true:=by refine (z2 (ar:=9) (rows:=0) (d:=0) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z343:z8 qB 10 3 64=true:=by refine (z2 (ar:=10) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z255:z8 qB 10 67 64=true:=by refine (z2 (ar:=10) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z185:z8 qB 10 131 64=true:=by refine (z2 (ar:=10) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z184:z8 qB 10 195 47=true:=by refine (z2 (ar:=10) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z183:z8 qB 10 242 64=true:=by refine (z2 (ar:=11) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z182:z8 qB 10 306 64=true:=by refine (z2 (ar:=11) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z181:z8 qB 10 370 57=true:=by refine (z2 (ar:=11) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem z396:z8 qB 10 0 427=true:=(@z3 qB 10 0 370 57 (@z3 qB 10 0 306 64 (@z3 qB 10 0 242 64 (@z3 qB 10 0 195 47 (@z3 qB 10 0 131 64 (@z3 qB 10 0 67 64 (@z3 qB 10 0 3 64 z344 z343) z255) z185) z184) z183) z182) z181)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q158:z8 qB 9 0 21=true:=by refine (z2 (ar:=9) (rows:=0) (d:=0) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z341:z8 qB 9 21 48=true:=by refine (z2 (ar:=10) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem q192:z8 qB 9 0 69=true:=(@z3 qB 9 0 21 48 q158 z341)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q193:z8 qB 8 0 6=true:=by refine (z2 (ar:=9) (rows:=0) (d:=0) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem z334:qp qB 14:=by
 intro k hk
 interval_cases k
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · exact q193
 · exact q192
 · exact z396
 · exact z395
 · exact z394
 · exact z393
 · exact z392
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem caseU14:zo true (z1 511) 14 (vars 511).toFinset :=
 wk (g:=qB) (i:=0) rfl rfl (z5 qS z246) q286 z334 (by decide +kernel)
theorem z177:Known false qS:=z372 z246
def j147 (i:Nat):Nat:=0x1a230180fd10fc20
def j144:Packing:=(2,1,2,0,0,4,0,j147)
def j146 (i:Nat):Nat:=0x104451000a0200202082101c0c0071400
def j148 (i:Nat):Nat:=0x613110000e3d4507e48110bea9a217d53082faa4885f54420
def j145:Packing:=(5,2,2,0,0,5,0,j148)
def z314:Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffec04a3a21f673,0x2a912c2212652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8a05bac6487f,0x56291cc44829),(0x2f8585078f9c,0x309c463038514),(0x135b045f80fe0,0xb41b88b00ae0),(0x3507a41fff000,0x142e4354ed000),(0,0),(0,0),(0,0),(0,0)]
def z315:List zK:=[(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4)]
def q255:List (List Nat):=[[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]
def q127:Nat → Packing
 | 6=>j144
 | 5=>j145
 | _=>zP
def q254:Nat → Nat → Option (Nat × Nat)
 | 6=>zk 8 11 1 11 3 4 j146
 | _=>fun _=>none
def x31:Forest := ⟨1055,6,fun j=>z314[j]?.getD (0,0),z315,q255,q127,q254⟩
set_option maxHeartbeats 0 in
theorem q122:zp x31 (z9 qS)=true:=by
 simp only [zp,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,zh (d:=0) ?_⟩,zh (d:=1) ?_⟩
 all_goals simp only [zQ]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q306:block x31 6 0 2=true:=by refine (z7 (ar:=6) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q307:block x31 5 0 5=true:=by refine (z7 (ar:=6) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem z146:zD x31 6:=by
 intro k hk
 interval_cases k
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · exact q307
 · exact q306
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j149:Impossible false (z1 1055) 6 (vars 1055).toFinset:=vN (q:=31) (prior:=z9 qS) (z5 qS z177) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q348:Lower false (zq 1567) (z1 1567) 7 :=
 zi (q:=1055) (rs:=[2,1,2,4,1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) j149
   (zu (g:=x31) (i:=0) rfl rfl (z5 qS z177) q122 z146 (by decide +kernel))
def z164:=za qS 7 [(1567,[]),(2079,[50,65]),(6687,[50,33,16,64]),(1703,[115,67,100,83]),(4263,[114,33,97,82,50,65]),(7847,[115,50,98,83,66,16]),(12455,[113,97,82,32,65,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q151:Known false z164:=z6 (m:=1567) z177 q348 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q279:Lower false (zq 42527) (z1 42527) 7 :=
 zi (q:=1055) (rs:=[2,1,2,4,1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) j149
   (zu (g:=x31) (i:=1) rfl rfl (z5 qS z177) q122 z146 (by decide +kernel))
def qY:=za z164 7 [(42527,[]),(44063,[50,65]),(47647,[50,33,16,64]),(52767,[33,32,65,48]),(57887,[16,64,49,32]),(42663,[115,67,100,83]),(44711,[114,33,97,82,50,65]),(47783,[114,98,83,33,16,64]),(54951,[113,97,82,32,65,48]),(68775,[113,16,96,81,49,64]),(42851,[131,50,66,116,99,82]),(44899,[130,33,113,99,82,65]),(53164,[130,50,116,49,32,97,80]),(60332,[129,50,114,48,66,97,80]),(69548,[129,116,50,97,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vq:Known false qY:=z6 (m:=42527) q151 q279 (by decide +kernel)
def j101 (i:Nat):Nat:=0x1040a3fa21fd51
def q398:Packing:=(2,1,1,0,0,3,0,j101)
def j100 (i:Nat):Nat:=0x40000
def j102 (i:Nat):Nat:=0x102de54110
def q399:Packing:=(1,2,1,0,0,0,0,j102)
def z243:Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa1c017c36792839f673,0x6456218245928112652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc38e7cc981ff26487f,0x1021104810085244829),(0x627e830e1e31c78f9c,0x474a42a0e1430838514),(0x207083f01fc1f80fe0,0x38b5bd5f00bc1780ae0),(0,0),(0x21c0103ffe001fff000,0x1ba9de7dba001eed000),(0x5818003fffffe000000,0x6fdeefb7eff7a000000),(0,0),(0,0)]
def z244:List zK:=[(96,0,15,0,4),(1,32,78,0,4)]
def q137:List (List Nat):=[[],[32,83]]
def z320:Nat → Packing
 | 6=>q398
 | 5=>q399
 | _=>zP
def q136:Nat → Nat → Option (Nat × Nat)
 | 6=>zk 1 3 1 6 1 1 j100
 | _=>fun _=>none
def q138:Forest := ⟨1135,6,fun j=>z243[j]?.getD (0,0),z244,q137,z320,q136⟩
set_option maxHeartbeats 0 in
theorem z281:zp q138 (z9 qY)=true:=by
 simp only [zp,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,zh (d:=0) ?_⟩,zh (d:=0) ?_⟩
 all_goals simp only [zQ]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q208:block q138 6 0 2=true:=by refine (z7 (ar:=7) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q209:block q138 5 0 1=true:=by refine (z7 (ar:=6) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem yO:zD q138 6:=by
 intro k hk
 interval_cases k
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · exact q209
 · exact q208
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q367:Impossible false (z1 1135) 6 (vars 1135).toFinset:=vN (q:=111) (prior:=z9 qY) (z5 qY vq) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q266:Lower false (zq 49775) (z1 49775) 7 :=
 zi (q:=1135) (rs:=[2,64,2,4,1,2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) q367
   (zu (g:=q138) (i:=0) rfl rfl (z5 qY vq) z281 yO (by decide +kernel))
def z104:=za qY 7 [(42683,[117,80,66,96,16]),(47806,[114,83,48,33,97,64]),(69498,[129,33,97,81,16,114,49,64]),(69557,[134,81,114,50,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z323:Known false z104:=z6 (m:=49775) vq q266 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q277:Lower false (zq 42607) (z1 42607) 7 :=
 zi (q:=1135) (rs:=[2,1,2,4,1,2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) q367
   (zu (g:=q138) (i:=1) rfl rfl (z5 qY vq) z281 yO (by decide +kernel))
def zR:=za z104 7 [(44219,[115,50,32,83,66,96,16]),(44731,[117,80,66,96,16]),(52926,[114,83,48,33,97,64]),(54974,[112,48,50,33,97,64]),(42711,[115,83,67]),(42739,[82,98,115,66,16]),(44981,[134,81,114,50,65]),(53212,[82,50,133,98,49,32,113,64]),(60408,[49,50,83,48,130,113,64]),(69624,[81,80,48,50,130,113,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qt:Known false zR:=z6 (m:=42607) z323 q277 (by decide +kernel)
def j140 (i:Nat):Nat:=0x344640ac3f865fc10
def j133:Packing:=(2,1,2,0,0,4,0,j140)
def j137 (i:Nat):Nat:=0x1520079d85d46b7171000680020c0000f391436008009b010
def j141 (i:Nat):Nat:=0x1108482000804c8462023211880840401f7cb4e4b74a0b44658480fb48032fd4c410bf58032bf58c10bf590109f59432be580329f59410bd58432bb58810af59010b758c10
def j134:Packing:=(12,2,2,0,0,7,0,j141)
def j138 (i:Nat):Nat:=0x24f9400060ba8030352
def j142 (i:Nat):Nat:=0x108421184210872a1e50a03e498240196e52058432cea62b2821b54c1610cb5a98ac8086e53158810
def j135:Packing:=(6,3,2,0,0,6,0,j142)
def j139 (i:Nat):Nat:=0x20034000
def j143 (i:Nat):Nat:=0x3b04813058432
def j136:Packing:=(1,4,2,0,0,0,0,j143)
def z312:Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc87d813f01c73e21f673,0x765c43000224212652),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe10600dd66a4c8c6487f,0x3601a1ac64a488c44829),(0x238268c08738f1078f9c,0x9aa0e13831071038514),(0x16807e00f83f01f80fe0,0x125451e4502f00b00ae0),(0x1c109622ffc001fff000,0x2d89a218afc0014ed000),(0x690100fffffe000000,0x3f89a3bcfffdda000000),(0,0),(0,0),(0,0)]
def z313:List zK:=[(1,32,30,0,4),(6,0,57,0,4),(40,0,23,0,4),(24,0,39,0,4)]
def q253:List (List Nat):=[[],[65,50]]
def q126:Nat → Packing
 | 7=>j133
 | 6=>j134
 | 5=>j135
 | 4=>j136
 | _=>zP
def q252:Nat → Nat → Option (Nat × Nat)
 | 7=>zk 7 21 2 9 4 1 j137
 | 6=>zk 2 9 1 8 3 1 j138
 | 5=>zk 1 5 1 6 1 1 j139
 | _=>fun _=>none
def x63:Forest := ⟨1087,7,fun j=>z312[j]?.getD (0,0),z313,q253,q126,q252⟩
set_option maxHeartbeats 0 in
theorem q121:zp x63 (z9 zR)=true:=by
 simp only [zp,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,zh (d:=0) ?_⟩,zh (d:=0) ?_⟩
 all_goals simp only [zQ]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q302:block x63 7 0 2=true:=by refine (z7 (ar:=7) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q303:block x63 6 0 12=true:=by refine (@zn x63 6 0 7 5 (z7 (ar:=6) (rows:=0) (d:=0) ?_) (z7 (ar:=7) (rows:=0) (d:=0) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q304:block x63 5 0 6=true:=by refine (z7 (ar:=6) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q305:block x63 4 0 1=true:=by refine (z7 (ar:=5) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem z145:zD x63 7:=by
 intro k hk
 interval_cases k
 · rfl
 · rfl
 · rfl
 · rfl
 · exact q305
 · exact q304
 · exact q303
 · exact q302
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z365:Impossible false (z1 1087) 7 (vars 1087).toFinset:=vN (q:=63) (prior:=z9 zR) (z5 zR qt) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q337:Lower false (zq 6719) (z1 6719) 8 :=
 zi (q:=1087) (rs:=[2,1,2,4,1,1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) z365
   (zW (prior:=z9 zR) (z5 zR qt) (6688,0,6687,0,7) (by decide +kernel) (by decide +kernel))
def z153:=za zR 8 []
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q140:Known false z153:=z6 (m:=6719) qt q337 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q351:Lower false (zq 1087) (z1 1087) 8 :=
 zi (q:=1087) (rs:=[16,4,2,4,1,1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) z365
   (zu (g:=x63) (i:=0) rfl rfl (z5 zR qt) q121 z145 (by decide +kernel))
def z167:=za z153 8 [(1087,[]),(2623,[50,65]),(1119,[101,66,16]),(6303,[117,101,67,32]),(11423,[117,101,33,32,65,48]),(6319,[116,100,83,32]),(13487,[113,97,82,32,65,48]),(1207,[115,84,99]),(3255,[114,81,98,50,65]),(1255,[83,82,114,99,66,16]),(18809,[128,80,84,66,16,114,97,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q154:Known false z167:=z6 (m:=1087) q140 q351 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q282:Lower false (zq 11327) (z1 11327) 8 :=
 zi (q:=1087) (rs:=[2,1,2,16,1,1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) z365
   (zu (g:=x63) (i:=1) rfl rfl (z5 zR qt) q121 z145 (by decide +kernel))
def z113:=za z167 8 [(2719,[117,101,67,32]),(13495,[115,84,99])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z333:Known false z113:=z6 (m:=11327) q154 q282 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q347:Lower false (zq 1599) (z1 1599) 8 :=
 zi (q:=1087) (rs:=[2,1,2,4,1,1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) z365
   (zW (prior:=z9 zR) (z5 zR qt) (1568,0,1567,0,7) (by decide +kernel) (by decide +kernel))
def z163:=za z113 8 [(1599,[]),(12463,[113,97,82,32,65,48]),(1719,[115,84,99])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q150:Known false z163:=z6 (m:=1599) z333 q347 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q268:Lower false (zq 47679) (z1 47679) 8 :=
 zi (q:=1087) (rs:=[2,4,2,4,1,1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) z365
   (zW (prior:=z9 zR) (z5 zR qt) (47648,0,47647,0,7) (by decide +kernel) (by decide +kernel))
def z105:=za z163 8 [(47679,[]),(44127,[101,66,16]),(42671,[116,100,83,32]),(68783,[113,97,82,32,65,48]),(47799,[115,84,99]),(68791,[114,81,98,50,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z324:Known false z105:=z6 (m:=47679) q150 q268 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q278:Lower false (zq 42559) (z1 42559) 8 :=
 zi (q:=1087) (rs:=[2,1,2,4,1,1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) z365
   (zW (prior:=z9 zR) (z5 zR qt) (42528,0,42527,0,7) (by decide +kernel) (by decide +kernel))
def z110:=za z105 8 [(42559,[]),(42591,[101,66,16]),(47791,[116,100,83,32]),(54959,[113,97,82,32,65,48]),(42679,[115,84,99]),(44727,[114,81,98,50,65]),(60281,[128,80,84,66,16,114,97,48]),(69497,[128,81,67,112,97,32]),(69603,[81,80,128,113,98,49,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z330:Known false z110:=z6 (m:=42559) z324 q278 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q265:Lower false (zq 52799) (z1 52799) 8 :=
 zi (q:=1087) (rs:=[2,1,8,4,1,1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) z365
   (zW (prior:=z9 zR) (z5 zR qt) (52768,0,52767,0,7) (by decide +kernel) (by decide +kernel))
def qk:=za z110 8 [(44719,[116,100,83,32]),(54967,[115,84,99])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qV:Known false qk:=z6 (m:=52799) z330 q265 (by decide +kernel)
def q395 (i:Nat):Nat:=0x8151108090c808420380cd31101fd30fe887f0c3f821fc20
def q390:Packing:=(5,1,3,0,0,7,0,q395)
def q393 (i:Nat):Nat:=0x74308515c76e77000000818435800000a71f02000000828c06fa8001025909670038579507803705e0482024814000001004000000
def q396 (i:Nat):Nat:=0x10842000421000040820b764a0f19283c280fe48130bf58910bf58430fe54030fe48110bf58930bf594209f59420bb58830bd58430
def q391:Packing:=(10,2,3,0,0,7,0,q396)
def q394 (i:Nat):Nat:=0x700009040000000000ddd0800002
def q397 (i:Nat):Nat:=0x104208141ba541620c36698ac4186f15058430
def q392:Packing:=(3,3,3,0,0,5,0,q397)
def z241:Array (Bits × Bits) := #[(0x98543c01121d833f4fc,0x1e6c550011215802a4ac),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc268201f82067f2cc8cf,0xa9854a582041528c8ca),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe6400c361c3861cf0f0f,0x146729421c3060870605),(0x25004de0e03f81f00ff0,0x219082bde00e81700950),(0x18979200ffc001fff000,0x9328e7ca8001fd5000),(0,0),(0x103ab009fffffe000000,0x35648318357bea000000),(0,0)]
def z242:List zK:=[(33,0,156,0,4),(24,0,165,0,4),(12,0,177,0,4),(132,0,57,0,4),(17,0,172,0,4),(160,0,29,0,4)]
def q135:List (List Nat):=[[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]
def z319:Nat → Packing
 | 7=>q390
 | 6=>q391
 | 5=>q392
 | _=>zP
def q134:Nat → Nat → Option (Nat × Nat)
 | 7=>zk 23 29 4 12 4 4 q393
 | 6=>zk 2 11 1 10 2 4 q394
 | _=>fun _=>none
def yI:Forest := ⟨1213,7,fun j=>z241[j]?.getD (0,0),z242,q135,z319,q134⟩
set_option maxHeartbeats 0 in
theorem vS:zp yI (z9 qk)=true:=by
 simp only [zp,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,zh (d:=1) ?_⟩,zh (d:=2) ?_⟩
 all_goals simp only [zQ]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q205:block yI 7 0 5=true:=by refine (z7 (ar:=7) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q206:block yI 6 0 10=true:=by refine (@zn yI 6 0 3 7 (z7 (ar:=6) (rows:=0) (d:=0) ?_) (z7 (ar:=7) (rows:=0) (d:=0) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q207:block yI 5 0 3=true:=by refine (z7 (ar:=6) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem jM:zD yI 7:=by
 intro k hk
 interval_cases k
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · exact q207
 · exact q206
 · exact q205
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z268:Impossible false (z1 1213) 7 (vars 1213).toFinset:=vN (q:=189) (prior:=z9 qk) (z5 qk qV) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q343:Lower false (zq 2237) (z1 2237) 8 :=
 zi (q:=1213) (rs:=[16,8,4,1,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) z268
   (zu (g:=yI) (i:=0) rfl rfl (z5 qk qV) vS jM (by decide +kernel))
def z159:=za qk 8 [(2237,[]),(18109,[82,48,66,112]),(2395,[130,114,98,33,81]),(12774,[66,114,50,132,99,32,80,16]),(12477,[32,83,116])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q146:Known false z159:=z6 (m:=2237) qV q343 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q346:Lower false (zq 1725) (z1 1725) 8 :=
 zi (q:=1213) (rs:=[16,8,4,1,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) z268
   (zu (g:=yI) (i:=1) rfl rfl (z5 qk qV) vS jM (by decide +kernel))
def z162:=za z159 8 [(1725,[]),(17085,[82,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q149:Known false z162:=z6 (m:=1725) q146 q346 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q340:Lower false (zq 2749) (z1 2749) 8 :=
 zi (q:=1213) (rs:=[32,8,4,8,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) z268
   (zu (g:=yI) (i:=2) rfl rfl (z5 qk qV) vS jM (by decide +kernel))
def z156:=za z162 8 [(2749,[]),(11453,[117,67,32]),(1371,[130,50,98,82,115,33,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q143:Known false z156:=z6 (m:=2749) q149 q340 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q273:Lower false (zq 43197) (z1 43197) 8 :=
 zi (q:=1213) (rs:=[20,9,4,1,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) z268
   (zu (g:=yI) (i:=3) rfl rfl (z5 qk qV) vS jM (by decide +kernel))
def z108:=za z156 8 [(43197,[]),(58557,[82,48]),(64189,[83,114,64]),(46427,[130,50,98,82,115,33,65]),(48475,[135,101,50,33,16,64]),(49638,[115,83,82,130,99,66,16]),(55782,[117,130,99,32,64,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z327:Known false z108:=z6 (m:=43197) q143 q273 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q271:Lower false (zq 44221) (z1 44221) 8 :=
 zi (q:=1213) (rs:=[16,8,4,1,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) z268
   (zu (g:=yI) (i:=4) rfl rfl (z5 qk qV) vS jM (by decide +kernel))
def jj:=za z108 8 [(44221,[]),(44733,[84,115]),(52925,[117,67,32]),(54973,[116,83,32]),(58045,[82,48]),(42843,[130,50,98,82,115,33,65]),(48102,[115,83,82,130,99,66,16]),(69606,[80,132,99,112,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem wp:Known false jj:=z6 (m:=44221) z327 q271 (by decide +kernel)
def q375 (i:Nat):Nat:=0x60bfd31
def q374:Packing:=(1,1,1,0,0,0,0,q375)
def z237:Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0021ee01fffe490e402109fc2670e40ff27f,0x208080808080490a402108a80450a401222a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe488e110001fe0033fcc6313cd9833fca4c4f,0x156067666666600212cc63114910212ca4c45),(0,0),(0x1000fe000071c380f83e331e1c38f38f8c,0x66caaaaaaaaa718380f82c321e1838a38b0c),(0x1000fffe0181fc0f003fc3e01fc0fc0ff0,0x199355555555580740f001341e007405c04d0),(0x1b761ee000001fe000fffc003ffe000fff000,0x1036e0f1e1e1f24000a948003fba000fed000),(0x488e11000001fffff0000003ffffff000000,0xa9f989999999ffded00000036efded000000),(0x1b74000000001fffffffffffc000000000000,0xfc91f0e1e1e0dbfff56b7ffc000000000000),(0,0)]
def z238:List zK:=[(88,0,163,0,4),(8,0,243,0,7)]
def q131:List (List Nat):=[[],[115,84],[65,99],[65,115,81,99],[81,118],[81,99,65,115]]
def z317:Nat → Packing
 | 7=>q374
 | _=>zP
def q130:Nat → Nat → Option (Nat × Nat)
 | _=>fun _=>none
def q332:Forest := ⟨1275,7,fun j=>z237[j]?.getD (0,0),z238,q131,z317,q130⟩
set_option maxHeartbeats 0 in
theorem q289:zp q332 (z9 jj)=true:=by
 simp only [zp,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,zh (d:=0) ?_⟩,zh (d:=1) ?_⟩
 all_goals simp only [zQ]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q199:block q332 7 0 1=true:=by refine (z7 (ar:=8) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem z337:zD q332 7:=by
 intro k hk
 interval_cases k
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · exact q199
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem j150:Impossible false (z1 1275) 7 (vars 1275).toFinset:=vN (q:=251) (prior:=z9 jj) (z5 jj wp) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q267:Lower false (zq 48891) (z1 48891) 8 :=
 zi (q:=1275) (rs:=[2,80,16,10,1,2,32]) (by decide +kernel) (by decide +kernel) (by decide +kernel) j150
   (zu (g:=q332) (i:=0) rfl rfl (z5 jj wp) q289 z337 (by decide +kernel))
def ql:=za jj 8 [(59646,[116,100,49,81,32]),(43479,[115,83,133,99,50,66,16]),(46581,[67,80,100,131,112,32,16]),(58874,[84,100,49,128,113,32]),(48382,[32,67,117]),(49403,[115,84])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem jK:Known false ql:=z6 (m:=48891) wp q267 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q262:Impossible false (z1 1151) 8 (vars 1151).toFinset:=vN (q:=127) (prior:=z9 ql) (z5 ql jK) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q350:Lower false (zq 1151) (z1 1151) 9 :=
 zi (q:=1151) (rs:=[16,4,2,4,1,1,2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) q262
   (zW (prior:=z9 ql) (z5 ql jK) (1056,0,1119,0,8) (by decide +kernel) (by decide +kernel))
def z166:=za ql 9 [(18814,[129,98,82,16,66,49,112]),(1271,[115,84])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q153:Known false z166:=z6 (m:=1151) jK q350 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q272:Lower false (zq 44159) (z1 44159) 9 :=
 zi (q:=1151) (rs:=[16,1,2,4,1,1,2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) q262
   (zW (prior:=z9 ql) (z5 ql jK) (44064,0,44127,0,8) (by decide +kernel) (by decide +kernel))
def z107:=za z166 9 [(52959,[32,67,117])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z326:Known false z107:=z6 (m:=44159) q153 q272 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q276:Lower false (zq 42623) (z1 42623) 9 :=
 zi (q:=1151) (rs:=[2,1,2,4,1,1,2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) q262
   (zW (prior:=z9 ql) (z5 ql jK) (42528,0,42591,0,8) (by decide +kernel) (by decide +kernel))
def q4:=za z107 9 [(60285,[129,82,113,48]),(42743,[115,84])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qi:Known false q4:=z6 (m:=42623) z326 q276 (by decide +kernel)
def q335 (i:Nat):Nat:=0x28270019312920f8e91910020841c00602403e3031e1d18e0d8d0c8c0b8b0a888028504c483c3844400101e1c1a180e0060b0a090807003030282018100801fbb98bdd7a82ec539c87a00ff503fd43ff54ffd10ff083fc40ff0c3fc53ff18ffc31
def q333:Packing:=(10,1,7,0,0,9,0,q335)
def q334 (i:Nat):Nat:=0xa49b3289cfee0003c11e62e10c1e4000235000513996000090c91cf0a000013a78dac3f26c00039c5cb8000000000204a000000452c001633e0e551fc80b152f0f95a89a255e23881a8be81b938018248c665c070000000000b3bc9a800000031700028c3072b06ecfafc98375010470c01e16716e074d6b0bf948ee3ac9600036e0054814054a5d5892c4d40b354401d8907a8d086167486866b2610135be1dd11650170cee09f0f01bcb5800000010d202243f318eef1419c646e0a9a0079430db52928c52c5193c564cb39a6900028ec0012280375062865214c24898f806a2a5df5d43e1d42ba11a4fe586827629805dd992be81c8003761a6d0ec800000000072b8000c8986beae00000018581727cae660c1200068bc0011c561f0148000b8c0000001cb4c5e711000138985d121316f8741ed000000000000000009074020000004d29b7e000c0d671818d8a3e1049165c75b693b0000000c7511c313d41fc131606bb107a0d043607013300102070000030000000461000006da150300000025000000000210610700003013010000000a0020130090060020020100100240030000015000100100020072001010001104000000010000400000000001011
def q385 (i:Nat):Nat:=(if i<1 then 0xc845e2d1218282a8801c24251480104a170b0541d28c2411f02104a1f15004282d1700020915c80581f207008240f85e2d150d894222f00304a1f088046607001c0633148045e2e160a9108128a88e1f1681c008088a80f00000845a2f40a88e250f8cc0e0038045f1e19874a0415044022d120a4000248105c111500428400000923114910570008840e26128c8562f93800e1b1289054010387052411680161412046040702004800048984a240f8ac5f220020222a0607c4a290380110703c845a2f28a8502b900b03e6154045f200f944a1f1501c021c0d8545c2d002c381b8a87c54071285852005094481f15044722f1588920180002512715981e1f150045207001c08240f844020f0a44066005002502b13901e2d150045200081c55281589c48503014550203810022900249a4c0e8943e07001c2e1c0d8904a1f8b4542200505c381b120943f168a84400a2407036251207e8315088014430e06c4a240fd062c110028381b0b894481f8b454220050d86a14078903e108904400af98fbdbd0be5cf07f72fb57d79e9af3eb9c7c57e00ef1b73bb74d9cec1f551a6dd1de7df379978c9ee4531d789ec2460a2fed7a0bc05c86df16bdb4a59aec2b5daacb554aa654e5a50d10a8213c39d64d7e65b2e994e49f24cb22a8dcc61e2e115088ac3d61750a3838c0da008fd27d03d4de0ce9e728b8e9c22db26a9b3f593cc3f606af4970ab535952b51556a3a4fb26a52b890f465a2650867ed3d49d94dfa6a732d1834bb65a02b7141894e45120b0f486e634a1830b504fc23a0ed85f023a0be02f8003fe90287ff54140ffa64a07fd71083fe90281ff5c940ffaa2187fd30503fea9281ff5d940ffae6a07fd6454ffea02a7ff4c110ffac0187fd63083feb1a21ff48063ffa42887fd72443fe900a7ff44153ffa84887fd54503fe98aa7ff50540ffaa6107fd61503feb02a7ff4c420ffaeaa07fd20443feb1aa7ff58d40ffaa2207fd62503fe39281ff58040ffa40a9ffd42503fe90061ff4c910ffae2a9ffd61103fe90081ff4c510ffa20107fd5150ffeb8a81ff58430ffac0a1ffd5054ffe982a7ff5d153ffae8887fd54443fea0aa7ff5cd10ffae6107fd30083feb0063ff1c153ff8e4887fd40443fea9061ff54831ffaa4207fd7054ffea0a21ff54540ffac0a07fd31503fe90041ff50020bfae4885fd7150fdea1081f758d53bfae0a1dfd71083dea0a817f5c153bfae2185fc72503fc902217f5d830fea82885fd72102feb90c77f1c910bfae031dfd7154efeb88c77f5cc20bfaea18dfd760c6fe382a7fe4c140bfaea205fd720c7ee982877f5c453fba60a9dfd74442feb9a217f5d840bfae2205fd7550efeb92817f5c053bfae4187bd54502feba8617f5d540bfae018df57114ef6b90815f5d440beae2204fd76102eeb98813f5d830 else 0x4963e2311400a4a1a0a4582712184c241287c662c158bc84270e801840148cc584020aa002813c1c560040d250001449c4e2b3c00522d18903e00190acb0116c005c2b1609ce34940b858271598642b11084c021089c484b1c0b8562d178880e0078d0421f1c0bc582413801230100bc53070f987e10800b482a160b85e4181145e2c1007cd258f8220f0028187c051412440250f80c08a1801240208f87cd258f8320f0028c04238178b0401f38805707178a43e60e8d059010009c5672241c5a21038bcc1f008b0564150b05a2f20d08100170b0502b13a02020138ba020717c005a9150cc5e31a4a058271594602a900823e1f83c00089039145e31a07c5901130ac5e4613801411800a45a4170ac802c1309cc34170c85841f906002d2010222a83c00422d228bd22c808744f0715987e128f8c4522d801c4033210f85e290f9c422d178e3616928bc5c2916c0103f0b47c622916c00e0518080422f1f01053070fa85c2f180a45859247c5e2d1588c450040b0562094524a33170b4210040f45c2f11400a3c108a45e24000b4e211241c5701038005e8178e05a30f8b04301c0ac58200f98763a1089449070f8bc562d1c80183017c80401f28cc5e20e8ac5e3820cc5d0101400c071c0b462f17004602916183e2c10405900000b4b04160b6020280182a2c800005a590884002d17946e050207c5851a0a6002d160a0562740d0582e15c06000013a06824140044a27838cc641f002c6230018bc5c2d1584502c158861200247c826120943e111508e442b17aa2c1c0d8904a1f8a8bc560051248420138b400451781d226128c854011207e442b17aa3d1d018040e00200a4662c50024e28160aca2a03)
def q376:Packing:=(122,2,7,0,0,13,0,q385)
def q381 (i:Nat):Nat:=(if i<1 then 0x8d2114ec42d555274bd2a00000161bc698a2be56e421c83e4eb400028745174e28a00000000000286640b140300000000000000029000001258a89ff00992fe0002b3da039c601254b5a7f81c0000a2dd89140da00006de2a4c59326092843a17450c9f98641eb8a6b0f032194d57899800010e20001c2208b800000002805000000000000000585b4e2b828d9a9b073f668000000008cd0000ca8dc8ad2baca4800000006ec3000060efc281810153c0000000217ef0d083fe87f00000001a1b8000781ec09a000246b324e0000a18c00039010001415c9baeb4c41fa947800010ac718343a800b516940168a70089713c725c00019a69eb0a0e0430e88f585868e0660223a8000a20e09dc8435154e1a3a209844215f52428c1cc67013432ca00034b5802270ffe195659f02531b064907608000e55761ca05e994bc50c000024e80003a02817f18688f76221a3d7d8af0df90eba87909b1876f302c105aa780000000000000060c0e190431ed5c5ec7000063d08b774286a09c1800006874a10ac3148761ac93451490187128de904f03084bb0000a1760000000300806afc2d7193f6fb0001841047b1299605400e8ea3fab29decc4b4cb3f14996518be8037c8c662106570000523a41e200014bda0cb8046d9e082a6aa400000259c4890f3613a227b440214710bd222cc55f95a52ee000384b99090001f43ac0db05dc2c380b606a4018e2c7c29000020e0b2c1c36d592581d405720e2070800051e58148179e57ec06e29fd94ff1596e576499887e93d52040000000000000000000000795500018280000403f0001612c0000000d17805980000000115f98a2c6b8000311dd8c356120d5b0c303bf0199866f08fe41a48e86705255e23385c8000b199fa7000050bf517da340801104c12de04508900000b134e067c961c1421cdc609488c1179277c579c8b767531636558089d347628365a2ca9e67f39dc94eff59cd5e90d481580b63f30a091557c001e97ce0ab2092d9b9923c13184648424ae092a2000251800e365b6ec4f892fb1b00c5dc12c482812e2f0e3ac0000000dd56a4e1cbce14af06045e8559b8202a28aa3599f78a280094d6254a491b0a46e5c4126684e456a0000c079b020000034f4b950b30000428604a800000012236482a88a00000000000000050ee000255e0000d1f600034aeaabb506cd2c00000502a8681003000e00140330401a0204c8b1a0000181040800456140030441602023011024280ba0254000865c1840010380140418f100c0150e04008001d0071a100802810081021810300000813204004060008e000c00e000c78710080080004291040029d2a44b0600006020a004820600003002c0042e002800c1808804104021e0c1810804080000440006000881824381004010402081091e001882208203 else 0x1b4a50500001d9fb975a15d240d09f665ca19400010148000d1120470000302ea103812ad92800041b8000000718e4000169580000000ec7a54fe07d532f9ea60000000191fd235ab94000005ceede82b68ac114331d200000002c309023e0d6a8e255930f60000c3e469200000000000300c89e400018b2000032dae49dca328dd0000a33c802b87e00000002020487dc8f05b1242c8cbf3068ec0c87758a5e2ae00033b16092dd50a395c36506b110702c1017c118ae2964af86cfc2179248c7f843873f929c843749a8d53e0a64b7917a78aa300f619f11a0a6c8001a2da47e4e380c952035c3c914c125e79dcb032d7fa52532f204a38c452e64523c2d6831f0269d1e3b6000046b502a1432594f8042e11bfb571400000a50987ce83cb1f0000031980004d6a0001094d53200010bf800016ed000074c40006015000000021b6800000000a15c1ea832e2e1639ec13384f000000004985c7752fb3484c94632b82150298cb54f6700000000000084291da000200d009f000000010a20000000144eac4c90ba0127cce6836cb09b02f9c9c5737045411fc4dc83c51313029e144400d939d939a26f84e6069a63962ca054f61f393ca2d000fd)
def q386 (i:Nat):Nat:=(if i<2 then (if i<1 then 0xd855c830fdd314c140dfd7254830dfd7650020bfd855d110f7d5250553ff9614c140fdd3050553dfd754c420dfd7348020dfd745c910dfd7550020dfd511c940dfd635c910bfd821c153dfd8748063ff5514c910ff98448110dfd735c910dfd205c453bfd855cd10bfd8258031efd6058430dfd7244153ff92058030dfd405c910dfd7254140ff48148143dfd7250553dfd825c053bfd864c140dfd515c143fdd304c510dfd7158940ff93048110dfd855c831dfd405c553ff9204c140ff48148153fdd3044153dfd605d110bfd831c910ff48148140bfd865cd10fdd6350553dfd764c510bfd8348110dfd7248030dfd714c020fdd534c140dfd205d440fbd5450110dfd615c143bfd8550510dfd7258030fbd4050553ff98348110ff92058040fdd3059153dfd855c8409fd825c0539fc87589409fd8758c209fd87589409fd861c940d7d525d4409fc8754940f3d54541409fc87545409fd825d4309fd831c910ddd7358c209fc8759153f5d524c153ded615c840ddd205cc40fb9544c1409fd805c5539fd8758d10f9c844c153cfd615d830ddd7354c20bdd8358153ddc835c9409fd825d5439fd835c910df5615c440dbd425d543fb541585409fd815d840df9205c0639fd825d540d7d525d5439fd8754c20cfd815d830cfd615d8409fd841c910cfd605d8319fd851c940ddd305c543bf581551109fd805d831fd9534c140df5205c453ded805c8409fd825d440d7d825d440d7d525d4309fc874c540df9724c140ded855c840cfd605d830ddd305c5539fc8744153ded605c8409fd815d440ddd515cc40ded7254840df97348110fb9414c1409fd874c940df4815c940d7d615d440ddd525cc409fd821c153cfd525d840cfd605d8409fd811c940df5411c910f9d424c143d7d521c1539fc8748153dbd425d8409fd841c153afd861c1539fc8758d10dbd425c440edd6358153f3d52551409fd805c863fe94248110dbd425d440fd9634c140f5d5258d53fb54150110cfd515d840df5515cd10d7d205d440fd93048153df57154440ded7254830fb5414c540ddd635c1539fd855c543df5605c4409fd811c1539fd874c420f5d5458d53d7d515d430cfd205d830ddd615cc409fd815d540dbd7255140ddd605cc40df5714c4209fc8750153df5205c440ddd305d5439fc874c910df5865c440df5525c440edd6359153fb54250510f3d5450153ff141481109fd815d830cfd815d8409fd825d4319fd8750940dbd7250540fad4248040df5855c4409fc8750910cfd515d830fd9204c1439fc8758540d7d515d440bbd81551409fc8755110cfd205d840cfd525d830fd9314c140df57154430d7d815d440ddd734c420d7d605d440ded515c840d7d525d431df9205c0539fd815d430d9d425cc40cbd425d8408fd861c153d3d425d440db5425c440 else 0x4a2c4cae62b34ab42a44a6e288ca0a279c9ce265c96a251c91a23b48d4229c87a20e47f81f7c7b21e147621d246fe1b946b819dc64a18c460e17d45c8166c56e152c51e13c44d812ac488119444210543f20f143980d5c33e0c6c2ee0b0429e09c424e08ac1fe079417c049c0d201a4000bfd8148143dfd7254940ff56150540fbd4254543dfd7158c20ff92058d10dfd8748053bfd8255110efd6058d40dfd8748153dfd7154c20dfd205d540dfd755d110dfd7159153dfd205c543fbd4250510dfd205d430dfd865c440fbd4254440ff92058153dfd825c063ff9205d110dfd205c053ff92055110fdd3048153ff55150510bfd861c940bfd8058940dfc825d540bfd811c153bfd864c510fbd4248040fdd2058d53dfd7254440bfd8258430dfd205c143fdd204c143dfd205d840ff48148063efd6158140ff92044153dfd215d540dfd764c420ff94248110ff48148053bfd835c910dfd7148020dfd835c910bfd8158040fbd5250540ff5514c553dfd764c910dfd7154830dfd7348110bfd8448110fbd4158940ff5514c110bfd8148063dfd615d440dfd305c910f7d5255140fdd3054543dfd7258140fbd4254840dfd605c840bfd8148053dfd605c031ff53148510fbd4255110ff48148030fbd4158d40dfd525c143dfd7248140dfd755cd10bfd851c940ff55250510fbd2050540fbd544c540dfd7650110bfd8058430ff92058143f7d5254543dfd754c020ff55150110ff92058140bfd8258440dfd7158030dfd205c153dfd7148030dfd7258d40dfd535c910f7d5244153ff5514c420ff5415c910fdd3258d10bfd804c940dfd865c031fdd314c940ff9514c140dfd7044153bfd8254543bfd8058d10ff9204c910dfd7650510dfd7258430dfd525c831efd6158040fdd604c143bfd8054543dfd7348510bfd854c940ff5515d110dfd7254840dfc725d540dfd865c430dfd205d830dfd605c543dfd764c020fbd2055140fed2054940bfd8158d40dfd525cd10ff48148020ff5515cd10dfd7154840dfd765cd10dfd205d543ff54148110dfd7154140bfd8258143ff94048110dfd805c863dfd7344020dfd605c440fbc8255140bfd8258153dfd525d110dfd7254430dfd205c840dfd605c831fbd4250553dfd105d540fed4248110fdd3058d10fdd634c940dfd8748143f7d5254540dfd205c863fdd524c143f7d5250153dfd7258540dfd765cc20dfd205c440dfd755cc20dfd764c110efd6058d53ff5514c510bfd845c910ff5514c540dfd541c910ff9524c140fbd4258040dfd205d110fbd4158140fbd4154140dfd205c063dfd724c540ff9205cd10dfc8748153dfd205c553dfd615c840dfd7254540dfd525c031fdd634c140ff48148040dfd205c463ff9604c140dfd605c143ff56150553fbd4258440fbd541c940bfd8054831df) else (if i<3 then 0xe31382b14371285e1485b0019158003d0b48170621485e1585a60b82d12821685c30b42e0b03320021605e30742b0002f200e1688110a82e0e080042a170c2c0ac41c05a21142c105c0f84a0042c501d000b42e24001385a3006070a42d800b0223e20902b07000904a15a4e0005e40bc2d1058158a000a42d185d0fa4030fd1687c310a42d800e1685e2400290b460005a28d033004000aca038001685e40442d0bc61fa830005a40bc318402c20661788070002d0bc814c000005a487d120c42e0b60034371285e1485b0018330b451380e0005640fd418002d20561505e30b045107e0b43e1885216c0070442f105c1985216121b8942f0a42d800c8ac001e85a40b82f105e0f85630ac2d1008158028f902d800320b8816c001905c401c3d0b46008002705648a0010002b223e158811800290b4817052178e000a42d1c4b0005e30b42f1002c24001485a34a0110b42b2022170581c121f0c5160b42e800c1705a24a0000bc614a000005a4046000a42d20021585e30fc418002d24001485a3008000b4712c3f03c0040a42d10380de2c1204a0fe2a0005e15ab160902507c2f0002e0ad01882008c88160561705a80731506c240941fc58000bc2b56820e0361204a0fe2a0005e15ab1c4c65f17ec59714cc4cf124c3df0dec2ef0a2c1ff066c13702abff6fe4bf7efc6beb6f9ebe3ef76bd9ef44bcaef12bbbeeeabb46eaeba56e68b93ee36b84ede6b70edb4b646d82b5a6d50b4ded28b466d00b3c6cd8b2d6ca6b20ec60b0cec10afdebdeaf3ebb6ae76b7aad86b34ac46ae4ab56abcaa66a76a9c6a4ea8aea08a7e69e0a6f699aa5de954a4ee922a4268e6a35e8b4a26e882a156832a0167ec9f767ce9ed67a69e3677e9d967389c7e7069b8e6d49ac668e99d665298be61697a65c696de594963e58a959e54494864f4934649a91b6468911642290263c88e9638c8da63508d063288c162e28ad629289e626a88f621a88061d486ee1988626166853612a84460ee83560b28266080819e04480d60127f95fb87e55f7c7d8df547cc5f0e7badee67b0de9679cde4678b5e287815de2774ddb07635d74756dd4c74a5d1a7405cfc738dcca72edca27225c70715dc3e7095c0c6ff5be46f05bb26e3db806d9db4e6cadb126be5ad66b1daa46a55a726965a4a68c5a0467d59dc66e59b4669599665f596e652d92864158ec63758c462d589261e5860611d824602d7e85eed7a25e4d7665d0d72a5bcd6da5a8d680599d644588560857955cc567d55e544d4f05335496521d45a510542850153e24efd37e4d6d3244bdd2c04a4d270493522047cd1da46dd19e461516244fd12643bd0a4420505440ed00e3facfc83e94f8c3dccf463c64eec3afce9c39e4e5638f4dfc373cd8e35d4d523494d023354cbc323cc6c314cc3a3084bea2ef4b9a2d8cb else (if i<4 then 0xb440005c248e000006918570000044582d0b878004274042b185e10cc2d105a17891f0bc580041f085802091f08521709270b02d18001108330bc708058168c2a8042f40080f858158c400b0415c3e200021485a247c00104e0380030ac2d12028044e1692150b900187ea085c1690000c0014880407c3318520f856302021600034882d0b8714008800e1f08581689200b02d182216056341c2b000613856000c2e0a441705e20882f143a1585a30ac213c00800c000b841705224842a0b600224a0205834042b1142f207016881f0856147c2c104018002c105210cc2c10641585f00102d0b041689620a42f0b061785070ac001a4a1985c380040105c1485a34882b8006168002810250a82f204e1605a30b030aa00000c004482d0b8691056168e1d0b42f1a51038561692070ac2d1868808590005e54802d8002e201200a61f1c2a1605a34821f12461c0221585e1699000b02b185816883d0bc381a0016083308561788290b82d185c1580030842e0e02d22401685c30a42d122c140a040b82d20740005e30b02d123e1605680101f0b040e84e170c04084e1605a38003312440005a30bc0010568008030b42f143e1606230ac2f120f0f882d0e0483c3e148c1f08650005638042b0bc2d224e17c000012410b9001856160a270b441685088000018561786630c21f0bc600842d0bc70dc4a1705e4400290ac6814081685c40ac001022587c331a4f000003488283c00000c2f4002e185816882d10048805010ac2c1c2010ac2d1002f000417c0020ac21485e240033105616082c0b441785a21142f10701688040884148a0447c041a3e18961f0a4616042e0a441705220802c0bc61705a20ac001048148563c0028385e160c29084f0000030a42f105810ac2c123e0fa001790400858178928800001802c0a4010b02f105810c0290b0622a0e000d070bc00185e160833085817882b08221485a30b02d105e20082d0b050805c168c2c0b448f85e020e414582e0bc817856245420085a1740040bc4f0b061485e200407000290aca2005c24542c800000b4a1785c160c2b0b4408864270c070f42d18661788070b82f185c1c08070002f0b490dc4a178530005a60fd1687c310a42d800e0024e158c2d0002f1854038001705e50bc30005a0005c401c2f100e1788331142b180e1605a3000070bc70dc4a1785216c0060a82f0ac71a0508000313942d800320b8912c3e8440f001407004000b4817800168c2c0bc2d185b000641712000b4000b88178562008000b861705a20442f10221585a301c3d0b861685e28942987e07800a1fa2d0f8621485b001c070f42d1a2b0007a1690000b441705a1985840002f0ac68a87a168c100b42e18221788450b041fa830005a4046000a42d2023000521692150b0000b4902054178c004a02b18022705 else 0x5e000901402270b880080020bd0010581788300bc402042007c2c0b4813c0020110740061605a24a02a0b461605a212c2d10561e85e38101f0b00020521688015a0020b42e121010b03000522404310a0e168c2c0b4416056209c2b0b0600b02d10601605e38590012430385a171029)))
def q377:Packing:=(387,3,7,0,0,14,0,q386)
def q382 (i:Nat):Nat:=0x4048000b050c190000427c0b6c0ae0f8000000104ef11dc59702504c0002c1800020759179d2161bfc05f1f9c566d19c76b1d2c3080d1a07c04df1a00000003098000c08207790bc000d109d3bd0a68070018000312ec6ee1e603900c583a64be435318e5361509868521b480d14000061f544fe9a2085606fc212022422905f08741ac0000003c0b40dd01e10ec84011cbc52b0e0f51a123465808c85a1c0444660f4c1561b5c0ce444000812a82800f105b000286710ca054a1b085800014600000000307c483404304d4074c330000000c1ff0841038000484ec36f1c287a81ef449f20986a315ec62200000070b948101a6f5f2222844000041c0000000500a40d0002025706b864214c0000002043000145c203f51d0003c61000342b211600150a8000000000011e000081cc00059ff03f0001b45b17c01611c5424e00c00014dc05d0000b5a6c4444144b2c2c0147c7cb0440007013866515700a404048b3520eb08aa5695d0a755101400104110500d38b50100a080
def q387 (i:Nat):Nat:=(if i<1 then 0x9b9c399b91b8f38cb84b71b5eb5c359b4c349b3c32eb26b2431c319b11b04301aff2f1aef2e72e4ae22dfad7acfacd2bfab22afaa229a28ca7f271a69a61a5424c23ea31229226a1920ba039fb9f39f11e39d61ce1c61c39ab1a899b18817a97817596816015294514293513292512291510d0ff8fd0ef8e20df8cc8ca0bc8a989688e88687e87686906105384603e03081d81580d80047f661205c4538fec910eb1a21fb14161120443f2a8298a64a07ad5854158940afac8aa839221d3d525c954503b5a84902ea2047f661205c4638fec810eb22a7fa92050960103be122902e031efc4818155110f5aa0ac2b02819f92021d54443af240b02ea20779245805c840e9ea12c0ba881f993055131503db2c6b0260a067d261205c440df490304aa2215f5914817114ebbb22b02e62067d2058748143ecea12a2b988157d9158175103f3260a0282a9e5f549841c153cfa4090e902a75f5984817114e3fb2243ac8a9ff2481524c143cfa48b04b80a757d9258575103f6282b0a60a0767509525cc40edaa130cb88819f48161d2018ff6282a02408865f21d5244153cee43a60902a75f5972052014fbe2c0902e22047f261205c553eba48a40ba881fd1302052054fa7a84a92ea2065f549811c153e7ab030cb8881cf56158171103b5a84902e22047f6448748153edaa12e2a88819f4916017218ebeb2ab8a621076d509855c440fd2a11029008197c875494054fa7a84c12ea2073d245205d8408fec910ea8a811fd9221d1054f3e930902e229c7f6488755110ed690284bb081df0914817014fbaaa2b9a621076d5c54258040ecea1240b9881db5415d9404432f90ea92a2a072f509205d840e9ea1302ba881d9d42581731038fac2b02ea2067d5c58258440ef8a8ae690221d3d7550961102bdb22b02e42077a481605c840ebaa8aa4b9a21de92054973442beb24c32e22076d5857250540fd8a0a84902211fd9221d4054fa7a84a8aea2057b649615c840cfaa8b06392219bd4260575103b3ae6a12c2207ea4814255110afac8ac0b88815dd925857310376a82c0ac6a0775245205cc40e9ea1240ba881fd13054531503b6ae2a12c22057b661615c840e7a48a40bb061f994158d30503fc240a928288737585605cc40e76b0ac0b90819f48161d2014f3790ea12a88872f509515d840cfa40b0e902a7dd93021d2054fe72a8a9260a067d61c8148140edaa12a4b88819bd5421d31503b6a84902e2205fc2614148110fe89810290287dd92058173103ed2a490220a9f875915458d53fd090284a0a21cad4248176103f1240a1260a1c3f261525d8308fa4c240b88a787d526187054fe9240a9260a9c3f261525d840c6e43ac6b22a7d2d42481751033a90640ae4a0763509205cc40fc8a0a629828199c872113054fe3260aa280a9f69509205c440 else 0x10200423e30660b04100160900851382e80030561002b05a2c820b8580020448082b05a484e0b4404431058b02d18220a00102b000224e800400000082908015a0010290800000016840005e8005455000817a001001604006001683058168c1602f05a30028aa001001482d102905a243e10100080000415a001001455000800ac20000170700041904800a8b2001002702d1516082b4002a8280040a41688000417041790010290b1605a22400b840b820003000447c178800050004000400ad000817900102b08290821a10105e80080a2c80040c815a00182f200200017800102d082905a20520b44083e0ac40a0f4004024e8004c0034550008105900080202c102a0b1605a3002e05a240907c158c1721f056305e105a1052105a105e0b440b420b417890f82b102b0a1f05620000bc158c178417850f82b14f04edcdaccd4bfcb7ca4c9cc9a48cc7f47745ec51449436433c26418c0b408c063fe3f63f3be63de3dbbd93d6bd43d1bc9bc73c4bb73a)
def q378:Packing:=(137,4,7,0,0,12,0,q387)
def q383 (i:Nat):Nat:=0x247800a1c00085000a0de22d610c00000272000f1bc2ec1b90725c1d40191e0508b44d01001a1400000c080000000000042841210
def q388 (i:Nat):Nat:=0x2c08168400e410815871042002c08000003504205c102f02d800181687ab67230efab6722e19d5c1ad9985712ce84403d49524c087481538fc2a520605544430dd636408759153de85089850520443f40a1481524c153f6848171509601039a92021d4255110f4a4814258175103d2542245205d4409dc6949850520443d8542245205cc40fe0509302052050f9a542261205c440f2950891481761039d1302048748153f625092058173103d6151481525cd10b0729d645516354e07ca9549861c153
def q379:Packing:=(19,5,7,0,0,8,0,q388)
def q384 (i:Nat):Nat:=0x81900
def q389 (i:Nat):Nat:=0xa3390a134a4c28290221e50549302048748153
def q380:Packing:=(2,6,7,0,0,3,0,q389)
def z239:Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc402ee4723402700821075b301c73e21f673,0x516b7a00004108082102532000224212652),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9401c100011c87330c6249c366a4c8c6487f,0x38c8481ffffae3330c6248c164a488c44829),(0x133511089c9ec04010038e7c8738f1078f9c,0x4321b34000011cc010010028831071038514),(0x235800308c800883e07c0f80f83f01f80fe0,0x24960cb3b52cc103e0580f80502f00b00ae0),(0x604a2032204028fc007ff000ffc001fff000,0x5a69404c4ad32e7c0027d000afc0014ed000),(0x8800ec54221107fff800000fffffe000000,0x52a908506683ef6a59000000fffdda000000),(0,0),(0x8a410885023507fffffffff000000000000,0x2c5644af997c0015a6feffd7000000000000),(0,0)]
def z240:List zK:=[(24,0,167,0,7),(2,0,189,0,8),(6816,0,6687,0,7),(1538,0,1725,0,8),(43010,0,43197,0,8),(44546,0,44733,0,8),(54786,0,54973,0,8),(160,0,31,0,7),(17922,0,18109,0,8),(1664,0,1599,0,8),(42624,0,42559,0,8),(47744,0,47679,0,8),(16898,0,17085,0,8),(1544,0,1719,0,8),(42504,0,42679,0,8),(47624,0,47799,0,8),(2208,0,2079,0,7),(1,0,190,0,7),(2050,0,2237,0,8),(44552,0,44727,0,8),(54792,0,54967,0,8),(2688,0,2623,0,8),(2562,0,2749,0,8),(12304,0,12463,0,8),(42512,0,42671,0,8),(44560,0,44719,0,8),(47632,0,47791,0,8),(54800,0,54959,0,8),(68624,0,68783,0,8),(1560,0,1703,0,7),(1696,0,1567,0,7),(42520,0,42663,0,7),(42656,0,42527,0,7),(58370,0,58557,0,8),(58016,0,57887,0,7),(57858,0,58045,0,8),(44568,0,44711,0,7),(47640,0,47783,0,7),(54808,0,54951,0,7),(44192,0,44063,0,7),(44034,0,44221,0,8),(35,0,156,0,4),(4,0,187,0,7),(9,16,166,0,4),(19,0,172,0,4),(129,32,30,0,4),(36,128,27,0,4),(20,8,163,0,4),(42500,0,42683,0,7),(47617,0,47806,0,7),(25,0,166,0,4),(14,0,177,0,4),(44036,0,44219,0,7),(13320,0,13495,0,8),(68616,0,68791,0,8),(64002,0,64189,0,8),(56,0,135,0,4),(7704,0,7847,0,7),(12312,0,12455,0,7),(68632,0,68775,0,7),(11296,0,11423,0,8),(26,0,165,0,4),(52738,0,52925,0,8),(54785,0,54974,0,7),(134,0,57,0,4),(2592,0,2719,0,8),(52896,0,52767,0,7),(13328,0,13487,0,8),(3080,0,3255,0,8),(168,0,23,0,4),(4120,0,4263,0,7),(1152,0,1087,0,8),(6160,0,6319,0,8),(47776,0,47647,0,7),(44548,0,44731,0,7),(152,0,39,0,4),(1032,0,1207,0,8),(6176,0,6303,0,8),(162,0,29,0,4),(164,0,27,0,4)]
def q133:List (List Nat):=[[],[115,84],[32,67,117],[32,83,116]]
def z318:Nat → Packing
 | 10=>q333
 | 9=>q376
 | 8=>q377
 | 7=>q378
 | 6=>q379
 | 5=>q380
 | _=>zP
def q132:Nat → Nat → Option (Nat × Nat)
 | 10=>zk 177 223 4 13 7 2 q334
 | 9=>zk 185 697 7 15 9 2 q381
 | 8=>zk 39 199 6 14 8 2 q382
 | 7=>zk 11 35 3 11 5 2 q383
 | 6=>zk 1 3 1 7 1 2 q384
 | _=>fun _=>none
def q9:Forest := ⟨1215,10,fun j=>z239[j]?.getD (0,0),z240,q133,z318,q132⟩
set_option maxHeartbeats 0 in
theorem jr:zp q9 (z9 q4)=true:=by
 simp only [zp,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,zh (d:=4) ?_⟩,zh (d:=0) ?_⟩
 all_goals simp only [zQ]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q105:block q9 10 0 10=true:=by refine (z7 (ar:=8) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q159:block q9 9 0 48=true:=by refine (@zn q9 9 0 7 41 (z7 (ar:=7) (rows:=0) (d:=0) ?_) (z7 (ar:=8) (rows:=0) (d:=1) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z350:block q9 9 48 36=true:=by refine (z7 (ar:=9) (rows:=0) (d:=1) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z349:block q9 9 84 38=true:=by refine (z7 (ar:=9) (rows:=0) (d:=1) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem q200:block q9 9 0 122=true:=(@zn q9 9 0 84 38 (@zn q9 9 0 48 36 q159 z350) z349)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q160:block q9 8 0 41=true:=by refine (@zn q9 8 0 5 36 (z7 (ar:=7) (rows:=0) (d:=0) ?_) (z7 (ar:=8) (rows:=0) (d:=1) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z352:block q9 8 41 36=true:=by refine (z7 (ar:=8) (rows:=0) (d:=1) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z351:block q9 8 77 36=true:=by refine (z7 (ar:=8) (rows:=0) (d:=1) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z266:block q9 8 113 32=true:=by refine (z7 (ar:=8) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z265:block q9 8 145 36=true:=by refine (z7 (ar:=9) (rows:=0) (d:=1) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z264:block q9 8 181 36=true:=by refine (z7 (ar:=9) (rows:=0) (d:=1) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z263:block q9 8 217 36=true:=by refine (z7 (ar:=9) (rows:=0) (d:=1) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z262:block q9 8 253 36=true:=by refine (z7 (ar:=9) (rows:=0) (d:=1) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z261:block q9 8 289 36=true:=by refine (z7 (ar:=9) (rows:=0) (d:=1) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z260:block q9 8 325 62=true:=by refine (z7 (ar:=9) (rows:=0) (d:=1) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem q201:block q9 8 0 387=true:=(@zn q9 8 0 325 62 (@zn q9 8 0 289 36 (@zn q9 8 0 253 36 (@zn q9 8 0 217 36 (@zn q9 8 0 181 36 (@zn q9 8 0 145 36 (@zn q9 8 0 113 32 (@zn q9 8 0 77 36 (@zn q9 8 0 41 36 q160 z352) z351) z266) z265) z264) z263) z262) z261) z260)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q161:block q9 7 0 53=true:=by refine (@zn q9 7 0 17 36 (z7 (ar:=7) (rows:=0) (d:=0) ?_) (z7 (ar:=8) (rows:=0) (d:=1) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z354:block q9 7 53 36=true:=by refine (z7 (ar:=8) (rows:=0) (d:=1) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z353:block q9 7 89 48=true:=by refine (z7 (ar:=8) (rows:=0) (d:=1) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem q202:block q9 7 0 137=true:=(@zn q9 7 0 89 48 (@zn q9 7 0 53 36 q161 z354) z353)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q203:block q9 6 0 19=true:=by refine (@zn q9 6 0 2 17 (z7 (ar:=6) (rows:=0) (d:=0) ?_) (z7 (ar:=7) (rows:=0) (d:=0) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q204:block q9 5 0 2=true:=by refine (z7 (ar:=6) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem qJ:zD q9 10:=by
 intro k hk
 interval_cases k
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · exact q204
 · exact q203
 · exact q202
 · exact q201
 · exact q200
 · exact q105
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem yn:Impossible false (z1 1215) 10 (vars 1215).toFinset:=vN (q:=191) (prior:=z9 q4) (z5 q4 qi) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q336:Lower false (zq 6847) (z1 6847) 11 :=
 zi (q:=1215) (rs:=[2,1,2,4,1,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) yn
   (zu (g:=q9) (i:=0) rfl rfl (z5 q4 qi) jr qJ (by decide +kernel))
def z152:=za q4 11 [(1887,[133,117,101,33,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q139:Known false z152:=z6 (m:=6847) qi q336 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q281:Lower false (zq 17087) (z1 17087) 11 :=
 zi (q:=1215) (rs:=[2,1,2,4,1,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) yn
   (zu (g:=q9) (i:=2) rfl rfl (z5 q4 qi) jr qJ (by decide +kernel))
def z112:=za z152 11 [(17087,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z332:Known false z112:=z6 (m:=17087) q139 q281 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q342:Lower false (zq 2239) (z1 2239) 11 :=
 zi (q:=1215) (rs:=[2,1,2,4,1,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) yn
   (zu (g:=q9) (i:=3) rfl rfl (z5 q4 qi) jr qJ (by decide +kernel))
def z158:=za z112 11 [(2239,[]),(2399,[133,117,101,33,48]),(12782,[66,114,132,49,32,81,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q145:Known false z158:=z6 (m:=2239) z332 q342 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q339:Lower false (zq 2751) (z1 2751) 11 :=
 zi (q:=1215) (rs:=[2,1,2,4,8,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) yn
   (zu (g:=q9) (i:=4) rfl rfl (z5 q4 qi) jr qJ (by decide +kernel))
def z155:=za z158 11 [(2751,[]),(1375,[135,101,50,33,16,64]),(1403,[130,50,81,115,98,65]),(28142,[80,84,132,49,113,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q142:Known false z155:=z6 (m:=2751) q145 q339 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q345:Lower false (zq 1727) (z1 1727) 11 :=
 zi (q:=1215) (rs:=[2,1,2,4,1,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) yn
   (zu (g:=q9) (i:=5) rfl rfl (z5 q4 qi) jr qJ (by decide +kernel))
def z161:=za z155 11 [(1727,[]),(2367,[135,50,65]),(14318,[50,117,131,49,32,65,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q148:Known false z161:=z6 (m:=1727) q142 q345 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q275:Lower false (zq 42687) (z1 42687) 11 :=
 zi (q:=1215) (rs:=[2,1,2,4,1,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) yn
   (zu (g:=q9) (i:=6) rfl rfl (z5 q4 qi) jr qJ (by decide +kernel))
def z109:=za z161 11 [(42687,[]),(47967,[135,101,50,33,16,64]),(53087,[133,117,101,33,48]),(69499,[128,64,116,81,96,49,32]),(45031,[84,117,80,132,96,48,32,16]),(53230,[50,117,131,49,32,65,96]),(60398,[64,132,49,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z329:Known false z109:=z6 (m:=42687) q148 q275 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q264:Lower false (zq 58559) (z1 58559) 11 :=
 zi (q:=1215) (rs:=[2,1,2,36,1,9,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) yn
   (zu (g:=q9) (i:=7) rfl rfl (z5 q4 qi) jr qJ (by decide +kernel))
def z103:=za z109 11 [(58559,[]),(64191,[117,67,32]),(48507,[128,64,116,81,96,49,32]),(43453,[129,82,97,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z322:Known false z103:=z6 (m:=58559) z329 q264 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q270:Lower false (zq 44223) (z1 44223) 11 :=
 zi (q:=1215) (rs:=[16,1,2,4,1,1,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) yn
   (zu (g:=q9) (i:=9) rfl rfl (z5 q4 qi) jr qJ (by decide +kernel))
def zJ:=za z103 11 [(44223,[]),(52927,[117,67,32]),(54975,[116,83,32]),(42875,[130,50,81,115,98,65]),(60283,[128,80,81,67,96,113,32]),(48110,[50,117,131,49,32,65,96]),(69614,[80,84,132,49,113,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qh:Known false zJ:=z6 (m:=44223) z322 q270 (by decide +kernel)
def q330 (i:Nat):Nat:=0x4c88f1a284060808057fc10
def q326:Packing:=(1,1,6,0,0,0,0,q330)
def q328 (i:Nat):Nat:=0x83800e3000c4814a28004c8280a80000001288072170108490827828b80af
def q331 (i:Nat):Nat:=0x45e30d8a0c818140206a241064060040e1d00022e2050212800011103640685c1c10c04820d80802c260c58342c08544800504d78c021e1c0400087480d0b4609048382010050c640685848241c10080283c30342c27180a0c10040161a18161413918d06080200bbeabda425b7f9a15910f2e85d003ff5cc10ffd30043ff55010ffd42042ff60810bfd83042ff61010afd86042fb60810bbd84042f760c10
def q327:Packing:=(11,2,6,0,0,10,0,q331)
def q329 (i:Nat):Nat:=0x202000000380606397c47943e48901800297152608243b403c8700800082947f118001c3285b90ec41920000002c8c93c003182c4b157140c72130003050003410000003d1e537c6746e01704d44505c06907602c00110950282796c162857834001c1c40e912986200108200000514a043340004082000000144000
def q372 (i:Nat):Nat:=0x200005068b4c0503680286a12040a400206080504120c88021b072002050c8041c30dc0041b80081c018005c205070060017081507000e8709188586c321207400e040807861f848043300071805000004420507006001708140019090788000c8483c4414002210207e12010cc001c607006001708143509020640300081d050008800205a342c36190903a007014002210206a12040c80600103f1a161b0c8481d00385a0011081202000c8043c50a0404838007438407400001708141d000b84081a84810320180040e8280044204cc38befa5ddb8d652ba55da8d452714b98eb1560d3e876ce35b233b600b39452584287acd3963274420788c812c1b414800bfec92e6086ff609730437fa60c1021bfd5260c10dfeb8306086ff60954043ff2e098021bfd9460810dfea1304086bf551860427fb2ac2021bdd5260c10df6b9b04086f74c18304377ae0c2021bbd4261010df6aa304086f765d830427fb2ec1821afd4261810deeb8306086ef655840435fa60c3021bed4260810d7eb9b0c086ef649840437da60c1021bbd73610109fec9308086f75cd830437ba84c1821bbd5261010ddeaa308086f75518304377a60c2021bed9460810
def q369:Packing:=(36,3,6,0,0,11,0,q372)
def q371 (i:Nat):Nat:=0x4200118060050390014553e041769a0
def q373 (i:Nat):Nat:=0x190040e18320081c3064010386000418002029b9673502d1e1900abf6897361810afb6a57360810ebe5c13061810efa5c13060810eee5c13061010cfb649825cc10aef68973610108f72a54260c10
def q370:Packing:=(8,4,6,0,0,8,0,q373)
def z235:Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff981017018004f68c0077c4481d3200821075b3090d9a33c9401c73e21f673,0x7892404800340000422904481532008210253200091222c94000224212652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff848d107200410000f6f7c00061c3b30c6249c31632604c0ff66a4c8c6487f,0x30db990d14ace6f3090c0004081330c6248c10420400804264a488c44829),(0x6401400c52820973fe802081863c4010038e7c98c38470f188738f1078f9c,0x2c32446006102010020520810028401001002898838470a18831071038514),(0x260480809b801730000070e07c003e07c0f80e0fc0780fe0f83f01f80fe0,0x50c43b9c31a55a2554aa470c07c003e0580f80407c03005e0502f00b00ae0),(0x1a6008010938f6000000380ff8007c007ff000ff0007ff000ffc001fff000,0x7298423ce4aa5daa954b803e8007c0027d000bf0004dd000afc0014ed000),(0x112a780a404008c01083ff000007fff800000fffff800000fffffe000000,0x469af34f68936130486f2a000006a59000000fff6e800000fffdda000000),(0x8c00720041000000003fffffff8000000000fffffffffff000000000000,0x7cf2466f2eb53190cf6f3fffbf7e8000000000fbdfbff7fbd000000000000),(0x6102a0847602080009083fffffffffffffffff00000000000000000000000,0x5384108b0966c9ecf9780d5effd795a6feffd700000000000000000000000),(0,0)]
def z236:List zK:=[(2,64,189,0,8),(33,0,222,0,7),(1048,0,1255,0,8),(1184,0,1119,0,8),(17,0,238,0,7),(52800,0,52927,0,11),(54848,0,54975,0,11),(58432,0,58559,0,11),(64064,0,64191,0,11),(43010,64,43197,0,8),(11266,64,11453,0,8),(52738,64,52925,0,8),(57858,64,58045,0,8),(58370,64,58557,0,8),(145,32,78,0,4),(64002,64,64189,0,8),(73,16,166,0,4),(162,64,29,0,4),(41,16,198,0,4),(1096,0,1207,0,8),(148,8,99,0,4),(160,0,95,0,8),(12,0,243,0,7),(177,0,78,0,4),(54786,64,54973,0,8),(59393,0,59646,0,8),(52801,0,52926,0,7),(78,0,177,0,4),(193,32,30,0,4),(90,0,165,0,4),(84,8,163,0,4),(54849,0,54974,0,7),(0,128,91,36,7)]
def q129:List (List Nat):=[[],[115,84],[32,67,117],[32,83,116]]
def z316:Nat → Packing
 | 11=>q326
 | 10=>q327
 | 9=>q369
 | 8=>q370
 | _=>zP
def q128:Nat → Nat → Option (Nat × Nat)
 | 11=>zk 5 23 3 10 4 2 q328
 | 10=>zk 27 69 6 12 6 2 q329
 | 9=>zk 2 13 4 9 3 2 q371
 | _=>fun _=>none
def yH:Forest := ⟨1279,11,fun j=>z235[j]?.getD (0,0),z236,q129,z316,q128⟩
set_option maxHeartbeats 0 in
theorem q288:zp yH (z9 zJ)=true:=by
 simp only [zp,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,zh (d:=3) ?_⟩,zh (d:=0) ?_⟩
 all_goals simp only [zQ]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q103:block yH 11 0 1=true:=by refine (z7 (ar:=9) (rows:=0) (d:=0) ?_); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q104:block yH 10 0 11=true:=by refine (@zn yH 10 0 7 4 (@zn yH 10 0 4 3 (z7 (ar:=8) (rows:=0) (d:=0) ?_) (z7 (ar:=9) (rows:=0) (d:=0) ?_)) (z7 (ar:=10) (rows:=0) (d:=0) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q197:block yH 9 0 36=true:=by refine (@zn yH 9 0 27 9 (z7 (ar:=9) (rows:=0) (d:=0) ?_) (z7 (ar:=10) (rows:=0) (d:=0) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q198:block yH 8 0 8=true:=by refine (@zn yH 8 0 1 7 (z7 (ar:=8) (rows:=0) (d:=0) ?_) (z7 (ar:=9) (rows:=0) (d:=0) ?_)); all_goals simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem z336:zD yH 11:=by
 intro k hk
 interval_cases k
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · exact q198
 · exact q197
 · exact q104
 · exact q103
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ym:Impossible false (z1 1279) 11 (vars 1279).toFinset:=vN (q:=255) (prior:=z9 zJ) (z5 zJ qh) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q341:Lower false (zq 2303) (z1 2303) 12 :=
 zi (q:=1279) (rs:=[2,1,2,4,1,1,2,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ym
   (zW (prior:=z9 zJ) (z5 zJ qh) (2112,0,2239,0,11) (by decide +kernel) (by decide +kernel))
def z157:=za zJ 12 [(2303,[]),(2555,[81,130,118])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q144:Known false z157:=z6 (m:=2303) qh q341 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q280:Lower false (zq 17151) (z1 17151) 12 :=
 zi (q:=1279) (rs:=[2,1,2,4,1,1,2,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ym
   (zW (prior:=z9 zJ) (z5 zJ qh) (16960,0,17087,0,11) (by decide +kernel) (by decide +kernel))
def z111:=za z157 12 [(17151,[]),(2045,[48,129,82]),(8190,[128,49,100])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z331:Known false z111:=z6 (m:=17151) q144 q280 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q338:Lower false (zq 2815) (z1 2815) 12 :=
 zi (q:=1279) (rs:=[2,1,2,4,8,1,2,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ym
   (zW (prior:=z9 zJ) (z5 zJ qh) (2624,0,2751,0,11) (by decide +kernel) (by decide +kernel))
def z154:=za z111 12 [(28151,[67,80,100,131,112,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q141:Known false z154:=z6 (m:=2815) z331 q338 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q344:Lower false (zq 1791) (z1 1791) 12 :=
 zi (q:=1279) (rs:=[2,1,2,4,1,1,2,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ym
   (zW (prior:=z9 zJ) (z5 zJ qh) (1600,0,1727,0,11) (by decide +kernel) (by decide +kernel))
def z160:=za z154 12 [(1791,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q147:Known false z160:=z6 (m:=1791) q141 q344 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q349:Lower false (zq 1279) (z1 1279) 12 :=
 zi (q:=1279) (rs:=[16,4,2,4,1,1,2,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ym
   (zu (g:=yH) (i:=0) rfl rfl (z5 zJ qh) q288 z336 (by decide +kernel))
def z165:=za z160 12 [(11774,[117,99,49,32,65,128]),(18942,[100,49,128]),(1279,[]),(28157,[80,129,50,116])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q152:Known false z165:=z6 (m:=1279) q147 q349 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q263:Lower false (zq 58623) (z1 58623) 12 :=
 zi (q:=1279) (rs:=[2,1,2,36,1,9,2,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ym
   (zW (prior:=z9 zJ) (z5 zJ qh) (58432,0,58559,0,11) (by decide +kernel) (by decide +kernel))
def z102:=za z165 12 [(58623,[]),(46559,[118,133,33,48]),(43517,[82,129,48]),(49662,[128,49,100])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z321:Known false z102:=z6 (m:=58623) q152 q263 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q269:Lower false (zq 44287) (z1 44287) 12 :=
 zi (q:=1279) (rs:=[16,1,2,4,1,1,2,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ym
   (zW (prior:=z9 zJ) (z5 zJ qh) (44096,0,44223,0,11) (by decide +kernel) (by decide +kernel))
def z106:=za z102 12 [(44799,[84,115]),(42975,[118,101,133,50,33,16,64]),(60383,[99,132,84,48,33,112]),(48119,[115,82,98,131,66,16]),(69623,[67,80,100,131,112,32,16]),(45053,[80,48,50,114,129,64]),(52991,[32,67,117])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z325:Known false z106:=z6 (m:=44287) z321 q269 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q274:Lower false (zq 42751) (z1 42751) 12 :=
 zi (q:=1279) (rs:=[2,1,2,4,1,1,2,4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) ym
   (zW (prior:=z9 zJ) (z5 zJ qh) (42560,0,42687,0,11) (by decide +kernel) (by decide +kernel))
def wx:=za z106 12 [(42751,[]),(47871,[117,67,32]),(42999,[115,82,98,131,66,16]),(60413,[82,129,48]),(69629,[80,48,50,114,129,64]),(45051,[81,130,118])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem z328:Known false wx:=z6 (m:=42751) z325 q274 (by decide +kernel)
def q246 (i:Nat):Nat:=0x1ff
def q234:Packing:=(1,0,9,0,0,0,0,q246)
def q240 (i:Nat):Nat:=0x4a80004900000000000000e0400000c28000000000000000011a000000000000000000000072bcebc01881144a0000000000024cb3b001c6e1c80000000000000000000002a9c0806305e82000000005b800000000000f4a001c9e8900000000705001e48000000000036472b000000006a42060000004040020600000
def q247 (i:Nat):Nat:=0x58150300105c003038090360d0320c02e0020170581503000050c09824088200781c0681800240002c0a02408280e0300a02006010020023032c75a30aa00ffd30ffc30ffd20ffc20ffd10ffc10
def q235:Packing:=(6,1,9,0,0,9,0,q247)
def q241 (i:Nat):Nat:=0x19cf703e9eb00000000001c1e81200002263868820b0a67480c1c401a815d341966000084f00021950000c05908c0000000000000000001546daa0665ce1038a91318c000948d5d5000240b000000055700000000de3b1390880001c9787234802942168747cc9380418d9d03582552719ab5207109000300c000000070a400090b1c210001418000000092140009250403b77400000011570002c22849786a6050c1af112c1fd0ae02a00000002490000000081b005c0000003c24c008000d0580000000000000069a0003809c15e8281044c860000000000118800000000000000026bad1e1b1a59e00110ef09d426325ac6b6254820000000000014872450000101000077a858e0001092b020000e24790b000198f0000000a04c00000000000000000b00400086aa807d074000622680aa8200a8b68e01206010000010200030008020205030a03010000040c120108000000000e070b00000201000004
def q248 (i:Nat):Nat:=0x82b0310aa0c0420ca0bc0042c80548590aa0c01280410990a24007e0901f00040208510481141a0320601ec0082e88380f2094180320ee0bc00440c80085d0aa33828682f0550ba158190000a03a441682a8590ac0042e04c0a220ba1702401c088168180980800c42c0011cc14741682a8590a81200e0441c01081809806414000085e85d0ac0c80085a0a190423746c8d51a2330640c41700c0000950b350b21500f0320021782874128c10e22f437050170000180950bad0ba1642a050129609c1082303a0680f819001104e0902181e0380682d819001208a05c0a0120200880605888030001140a812020059e000228130200580a05678150200482a01601c149c1300702004a0580081502411008501200e04605c090010201400a04ea04c0400940b00102a0402201290240440840a81302005800028095502e05408012088b02a04c08016094b01e0340380001001024802880c0860100400608e00c00401b02b0640e0128300000b82248170190310bc14281702b0320021682860260480881002f03e0680c00003940480881002b03809c0d00003010a8098120220401101781f0380600001ab8150260400b028580102e05408012580102a04c08016500b0100380680700810801000900e0180282002f00e01001000011406c0e0128350600f817000800e01802c0200800c00800401e00e01802c038040040ea20200580700800800300600b00e01001000680ebf59ef2f1c75fb9e1c36dbe68fb1d585cb9a5a42b2951ca314e4a5b12348c843b200cf2072835a99e4c7a5e02c1946c9be4982128ec86682f815e0a004301a50a403ac11c0470007ff60530ffe8ca61ffc194c3ffb04187ff60430ffea9a41ffd81483ffa62907ff60120ffe98241ffd89483ff912907ff4e520ffe1ca41ffd19483ffaa6107ff60420ffec1a21ffd82443ffaa4887ff4c910ffec0221ffd50443ffa60887ff48110ffe9ca21ffd29443ffb04087ff54810bfe8c861ff930482ffb12905ff62420bfe9c8417fd19083ff240885ff4e510bfe94a217fd39042ffa52085bf5a430afebc8217bd49042fba72085fb4a410
def q236:Packing:=(45,2,9,0,0,13,0,q248)
def q242 (i:Nat):Nat:=(if i<2 then (if i<1 then 0x302f0000000000000000000000000144eb00000000000000000201f80000000000000000400d80001892a00000000000000000d432c0259c1dc8447105a0000000000000a18518184000102e70000000000000000000000000248d4000052080000000000000000000003a0cc00003131800000001c23c00004dc6000000000f832481f0000000000000082840000000000000000382ba002000000000000000000b05d8000000000000000000000000000000000000000000aeb9527c800000000000000000000020ca0000709a00003413fa11a1340099980006e0ed235e92bec00000000000000000000000000000000000000000071afd020289ddc950000000001c26400000000604c00000000000007a544000000009a8c58252d2880000000000000000000000000000038197c06c0000684e4000000000000000000000000010ab0000000000000003680003c10400000055f04fd0004000000000000000018d60000030b4082a680bc104f131f4000000005116800000001005a000000000000000000000090580000000036a9f83f0d04d4eb830498a4da480e00000000000000000000000000000000000000448f00000000ef067000000001dcce0000162c7106045e9e4e5000000003c14b2062000000000000000000000000000000000000000000000004135000000000000000000000000000000000000006055000000000a0728000148afd0f6000000000000041222029621c756a6266300003a4ec000000000000000000000000000002001a415ca1400000382d704d1e84f70a7f042cc24e00006018725040000830b563110af501be002e000000000c13800894094381000a260000000000000000000000000285880000000000000000000000000609c00001d046c05f00000000281b600009834000000000000000002024ac08de13b0000711cc0000000020850000100560000a0a6b81900180000000000000000004000000000100100000e0000000100400000004008000008000000000080000a0080000100000000000000000000000040040100000600c000000000140000300200805800000004010000000000000000c000000000020000000000600000800000000010010000080000500000000000006000010000020040000000401403800000000008000000040000100600c0000000200400000000000000000000000200100000000004004008000010040040100000200004002000000000000000000000000000000000004004018000020000100c0000040080000800c010000000000000000000c000000040000000900200000000008004018030020040000000000000000006000008000020040080000600000001004008018020000040200300a00001002002014000000020040000000000002000 else 0x61c059203230478000000000000b0341039d8a16a4ed00000000000003683f043800000000000000000000000000000000000003006e000000007838709b8c0760000000000000000074a18000281b283070000000000000000000004d1a4000080d10000000009158000000000000000000000000003a4c0000000000006b9f80000c0ef0000080ef8071a05500004a298000000003027000000001cf6ba4ac00001524e00000000000000294e0f5000000000c1520000000000003c11a000000000000248dc0000d58580002c69f2ebf000000000006800000000000031e9c4ecf00000000000000000f06a0000211760000000000000000000000000000000001cf28000060028000000000000000000000000042860000240d2c12b000000002528a636c000078357420600000000682c0a8560000001400000000140de00000000088ccc8b1528a00000415a000000002043c000160e9809b8016c00000000247e80000000000000000000000001a1630000085a800000000a99fb3d24000000000000000000000081e00000000000000000e1a5d094d1253a147f063e257b28aee06b00000104400000000d0b2000000001e0860000000024099292cf7a60000251360000000030b3ec2530023000043b5c000000000000193abc02000000000000006e360000f00f800000000000000000000182d2000000000000382ab60a8000000000000000000000000034221f4b00000481fb8043aa76907bb4c7000000000816b00001d28c000000000000000000000000069538000000000000000000000000000001846c80f2000000000000000000000000000000000000000000000000000b48330397c57400000000e0928000000000000020d000000000000000000d46602580000000000002cd76c0220a33f0360d114a0a3a04a80003c011c10ee06173b1c0001c41300000000000000000e0214b8dc00000000000033c30000024e92040e803c0000e8190000000004ed8000000000000000014252207c6019400000000000000000000000007b8d000000000073b0000381c000000000468200000000180b902ac000000001e09700000000000000000000000000000000000000100d4c4c8000000001915800000000202080000000120c3000000001c0260000b45900000425a000000000000000000000a05f80001c81a00000000000000001606a00000000000000000708c5017009b000000000000000001246700000000110e00000208ad84cc0000000000003d468416f607700001059800008ea3d004800000000000000001d1cc00000000c239700bc0000000000000024000000000000020374000000000000485ac0000000000003b4000000000000000000280b004f6275e722a780f60000000000000000148fe000000000000000) else (if i<3 then 0xd08a5032501a76088d0684a1d800000000766aa4afc0001e01c0000000380000000020ac800000000000000000000000000000000060d800001833983960000000000000b450800000000e01a706659132004e815c0000111d0000000000000000038180ca7400000000000000000000001168000000000000582b28022000000000847e86a716760000404258223a0bdc0510000388ba0000000000000000000008b6ea88f6deba000000000000000fe000000000000000000000000000001c0b2a15f00000000000000000c053a39c80001205d00000000301edd669000013cff01fe00000000000000000000000000000000000704000000000000000000065082e800000000000058560000000000000680580001c93ed00a193b000000000703700001802a0000361a8000228ec0000a15680003d27f800b0000592f0000000001095000000000002ac16100000000160fb50668325400008481000050391c98c00000000000000001ac6435770000249f000fd00007dc10000000008009604200000000000002853000000000000000002597a0000b05f0000000000000000000000114a0000e03a80000000000004012e0c21ed7c000000007023000000000000000002003c6713a0860000000006151000000000011c000000001026c000000000000000000000000011860000322a60000000000000000148841052000024896000000003011000000000a0a5800015c748e7306667bc0c00000000a098800000000204f0000280e541220000000000001a0d2c82e000000000000060f104a000000000000002b8a00002aa3c0000a05c493ec80a7356b70b70000000000000749e8000000018ca700000000000000000d03880000c0ac0000f09b000000000000000000000000000000109ecb9ad41829750000039020000140b60000000000000a47a000000001cc3a641450ad780b40000814166541ac28803a0000000000000000043090000000000000a102a09080000000000000000481240000000090a18000000000000a08913c080001e922603a302bc00000000723e8000000002017509d000000000e8982935000010ec0b668c03000000000000000000000001e3fc0f2f0b0d059c000000000000000000000000000003018c000000000000784588ad7293c0000000008240000000000000282020000000000000000080b20000721e924e540857062000000000000000000bbb7955a00007634000020106a2cd0000000000000000000000000000000000f09f301cc0000a40474930228800000000000058144000000000000000000000210d00000000000000000442a483cfc0a161060000000000000000000000000000000000000030490000082afd0a7000000001b681106775af4000000000000000000000a2b110abf80 else (if i<4 then 0xedb920430000000000001ce56000000000018d34bed1666011c0001245e1070501500001811ce0a2384f00001c0d70000008680000000000000000000000000103d0000000000000000030410000040e8000000002c24c00000000322b800000000313b000000001203e0000183b18037e123000000003a9da000000000000000000000908ed29919962814600002840000000000000000001cc5a0000000000001d2b25054906280003d1fe60d650a4c00f40000000000003009000000000915b0812c000000000000000000000000000004009800000000000000000000000000000000019156c0fe803300000000000006aa800000000000000000000000000000000000000000000000c07800000000000000000000000001404800000000180940f200000422f7a5fe0000607a5821000010504f69d5ac2611600000949bd0c11020a0000b6a09022e0003776000007395c000000000000491f800000000000000003c886000000000000081a5a4ff705300002022e00000000000000000000000000000000000000000001151019e0000000000003ac980000b07300000000100c80026f00cc40ce641ec0589a28000000000000078388000080ea0000000000000000000000b8e79dff4a6a204ea041c00000000000068514407440b3a05000000000000000000000000000000064a3f04780000000010a11859400000000000000000000160f900004a4b8423348bcd180d3073598800000000000000001e16f000058012000a0000000000000000000000000000000000c045655780000000000000000000002978000000000000000000000c055735b00000000000000000000180000000000002825de27900002286800000000065d683ac0001a09a00000000000000000000000000000000000000000000000674f000000000000000000000000000000821ba448f9196403200000000000000001ab07f0a44a25c82dbb4dd0000000000000207814390000000000000000000003aed8173e922a808f8000000000000000000000000000000000101b8000020b65a4b4000084bb00000000190ae00000000483e80000000000001003400000000000000000000000000000000000001b54ed6a3800000000000010b400000000044f7b195800022e0b032700000000000000000e0ad8038c0000000000005223800000000a41580003011400000000000000000cd380000404bc00000000744a80000000000000000000000000000042340000000000000000000000000000002b6f00000000000000000000000000c057000000000000000000000789e000000000813e0000000fa00000000000000001305700003cb7dc2c00000000000000000000000000281be2a0a000000006057800000000000000000000000000000000002ab2000 else 0x7209d8062000000000000000000000000000000000000006329480a7c2a5cf2100002026400000000000000000000000000000500f0822600007492000000000000000000000000000000000000001ccd000000000000000001c0da00000000000000000f45f00001056e0000504c4253800000000000000000117e000040a80000)))
def q249 (i:Nat):Nat:=(if i<3 then (if i<1 then 0x2ffd8a4c120dff66930482ffd9a4c120ffe54d30483ff9824c120ffe54930483ff9814c120ffe54530483ff9314c120ffe62930483ff88a4c120ffe56930483ff85a4c120ffe46930483ff89a4c120eff60589483ff93062520dff4c5894837fd3062520dff481894837fc3a62520dff46989483ff93022520bff4e889482ffd1a22520ffb54939483fdd314e520ffe4c1394837fd894e520dff225394837fd594e520bff56939483fed520e520dff624394837fd590e520dff16439482ffd8a0e520bff56839482ffd1a0e520ffe4c1194837fd8946520dff225194837fd3946520dff0e519482ffd8a46520bff4e919482ffd8a54c20bff469530837fd9a54c20bff4e9810837fd9a60420dff54d890837fd3a62420dff0e9890837fd1a62420dff54d390837fd814e420dff629390837fd5a4e420dff469390837fd5346420dff629190837fd3a46420dff669824437fc9a60910ffb609524437fd9a54910ff74c532443fdd534c110ff74c530443ff9804c110bff62930443fed5248110ffe60120443ff95048110ffe4c120442ffd8a48110bff4e920443ff98548110ffe60d20443ff95348110ffe62920443ff95a48110ffe4e920443ff5514e510ffe481394437fd894e510bff629394437fd854e510dff609394437fd524e510dff605394437fd514e510dff485394437fd804e510dff541394437fd204e510dff629394437fd5a4e510dff4a939443ff5514a510dff625294437fd594a510dff4e529442ffd8a4a510bff56929442ffd3a4a510dff60d294437fd534a510dff605294437fd314a510dff601294437fd504a510dff4c1294437fd8a4a510dff4e929442ffd3a60810dff66982043fed8254810bff4e9520437fd9a54810dff54d390437fd824e410dff549390437fd8a4e410dff569390437fd2a4e410dff54d290437fd8a4a410dff569290437fd3a4a4109ff269814c37ed2960830dbf609690c36fd525a430dbf605690c36fd2a5a430dbf469690c36fc1a5a430dfd605190c27fd8a464309ff569190c27fd2a464309ff269534827fc9a605209ff269314827fd9a601209ff66930483fd9534c120ffa54930483fd9314c120dfe4c189482dfd7a0e520bbf5a8394833fd8162420df754d390827fd8a4e4209ff569390827fd8a464209ff4e9190827fc9a60d109ff269824427fc9a549109ff26932443fe95248110ffc545204437f9204e5109ff629394427fd8a4a5109ff4e9294435fd825e410d7f549790435fd3a5e410d7f0e9790435fd2a5e410def54d490437bd8252410def549490437dd534e4109ff629390437dd824e410df7549390437dd8a4e410df7569390437dd2a4e410dfb609290437ed524a4109ff629290427fd5a4a4109ff4e9290437ed534a410dfb629290437ed5a4a410dfb4e9290437ec3a4a410 else (if i<2 then 0x123911f811ab114610ed1088102f0fbe0f7d0f0c0e9b0e4e0e0d0df00daf0d320ccd0c740c270bc20b690af80a930a6a0a350a0009cb098a0955091408d30892085107ec07ab075e073506f4068f062a05c50578051f04d20479043803eb0392034502e0027b021601b1014c00f3009a00410000fff549814c3ffd9a60530fff269814c3ffd5246530fff605194c3ffd8946530fff565194c3ffd2946530fff629194c3ffc8a46530fff569194c3ffc5a46530fff4a9194c3ffc2a46530fff208194c3ffd5206530fff469820c3ffd5260430fff4a9810c3ffd9a54d20fff26953483ffd5360520fff4e981483ffd0a60520fff66981483ffd9a4c520fff26931483ffd8260120fff4c580483ffc9a60120fff54d30483ffd824c120fff54930483ffd814c120fff4c530483ffd8a4c120fff56930483ffd1a4c120fff54d89483ffd8162520fff4c589483ffd8062520fff4c189483ffd3a62520fff0e989483ffd1a62520fff4c489483ffd3022520fff54d39483ffd824e520fff54939483ffd814e520fff54539483ffd314e520fff60139483ffd304e520fff62539483ffc894e520fff56539483ffd8a4e520fff22939483ffd5a4e520fff16939483ffd1a4e520fff60839483ffd520e520fff60439483ffd510e520fff60039483ffd890e520fff56439483ffd5346520fff60119483ffd3046520fff62519483ffd3946520fff62919483ffd3a46520fff62953083ffd1a54c20fff54d81083ffd3a60420fff66983443ffd5360910fff56982443ffd3a60910fff46982443ffd0a60910fff66982443ffc9a60910fff60d52443ffd3a54910fff42952443ffd9a54910fff61532443ffd814c910fff54532443ffd1a4c910fff66932443ffd5360110fff54980443ffd3160110fff56980443ffd3a60110fff4a980443ffd8254110fff60930443ffd524c110fff60530443ffd8a4c110fff56930443ffd2a4c110fff54d20443ffd8a48110fff56920443ffd3a48110fff61539443ffd824e510fff54939443ffd814e510fff54539443ffd214e510fff60139443ffd504e510fff48139443ffd894e510fff62939443ffd5a4e510fff4a939443ffd854a510fff60d29443ffd534a510fff60529443ffd514a510fff4c529443ffd804a510fff54129443ffd304a510fff62529443ffd594a510fff4e529443ffd8a4a510fff56929443ffd3a4a510fff54d82043ffd5a60810fff4e982043ffd3a54810dff625194c37fd5946530dff4a5194c2ffd8a46530dff624194c37fd5906530dff4a4194c2ffd8a06530bff568194c2ffd2a06530dff669820c3bfd8260430bff4a9810c37fd9a60430dff609190c37fd5246430dff605190c37fd8a46430dff569190c37fd2a46430bff269534837fd9a60520bff26981482ffc9a4c520ffe6013048 else 0xa05b0190007810c0ec0d40f80c8003409c0900ae06a0740640001ea204e04703b03503e032000f02702402f01a81d81e05b019000981183881080d03180c80004340280110160e02e0200f4088981009e044056404e03d0220292015e04e0420540a1702702202d02898158108290128165c00c0bc0a8094082e00605604c05a041700302b02202d024b00d00e80404804100100209a884c8068018000472c0302581940081082398084128080609209100004008e5807805806c0440380104481d4403c03601a02201023400c0ea201811700901100d08e006075100b8088070020890006807c04402c030428018003e01a022014000124009808700901100d08e006000f8098068050030005805c04c02403801800340281e601202400c000219e01b00d00a000092004d00c0420408078040470030008807806017c03804402800801440300bc02201e01011c00c002201a1020160100c600600010d100a04204100c8070020890008806021020c034028008013c03010810601201c00c001e01a0140f300a00600010ce8840820080420405806f800a7fbd7f4c7ee77eb27e7d7e487e1f7dd27da97d447d1b7cce7c8d7c347bf37b767b297ac47aa77a427a01799c793778d2789d77fc7773773e768575fc752b74a2740173c07373732672c1725c71f7719e71457110709f706a70296fd06f476eee6e896e246db36d2a6cdd6c9c6c5b6c266bd96ba46b276ae66a756a3469e769a6694d690c68b3687e684967e467bb6792675d672866ff66d666a1666c65ef65ba6585651464af649264216398633f63226299625861ff61be612960dc609b6072603d5fb45f1f5e665e195dcc5d735cde5c6d5bf05b675b0e5aa95a5059bb59865939590458ab584657d55794575f571256d15684564f561a55f155bc5593555e552954c45483544e540d53d853975362532d52f852c3529a5265523c51cb5172513d51145097501a4f9d4f444ec74e564de54d684cf74c7a4c454bec4b874b2e4abd4a584a0b49a64971493048e3489648614808474f46ae4631459c452b44a2441943b4436742ea4291422c41c7415640e5406840273fb63f513ea43e3f3dce3d693cf83c633c223bbd3b883b0b3a8e3a2939ac394738be384d37dc37a737123689363c35d73566353134c0347f342633cd3368331b32aa325d31f8316f312e30f930702fff2f8e2f4d2ef42ebf2e2a2dc52d842d1f2cd22c852c502bf72b922b212ab02a3f29ce296928f82893283a27c9277c272f26e22689263025e3258a253d24e42473240e23a9234422df227a22092198214b20f22099204c1ff31f9a1f411ee81e9b1e421de91d901d1f1cba1c611bfc1b971b321acd1a741a1b19ce19691904189f183a17c9177016ff169a162915dc155314ee14891454142b13de136d12fc12bb126e)) else (if i<5 then (if i<4 then 0x22028c0638120ca056440505700907104380b02a3c13408004e05e04205034813a20990520481e70200241e01dc089287204c0200240458160d30128109826001c0a812c0b8094088220694c09408e04e04015834c0a012a05240480400af0250201a602e05100220258130178100d902804a8149012010c0ac0840906980b8144409605604c05a04034c0a1e04a04302a02d0270200a41a605138130168110288140ec6c0a81440840980b06d3012e04204a0540a405980a40ac0950201d41a6050e05204a0d98108140eb028702b80bc084090698143015e04209404813838a051f0290530220241a502cc0458178150120e20d28107c0bc0a06f80902b40807102c0694818e05a05204404a02a0803a200901cc08b02902102e024191180009a0458108148170128568428c0b414022c0a809071408420a605a09404e04039038a052105101702b02109a0241bc10d02d282484c8218140458170120d28109428c0bc0880907040a320860560420a404834a059d02302f0280b01bc1a4190f8178100e00de8140c86070c0ac0840b06f0690643e04e04209405835812a051f02a02c1af0241a4095020f0160d78138100d804a8147c0a06fc0840906980b3605035e04c05a040348129c1af0270210281b202c09cf8140d78110168120d204a702ec0a41140680b40940806e06d4e00828600012e04205204c05a10a302b02602c1ad020094e85080b8158110160d681204a8412410c0ac0980b0694080254208e04a14405e04036205012a104904302b02202c1a502409518158120d60c48100d204a7c0a06b06ac084090690253833e01c024016008121901d01809201300d0010041a1180d8008040ce8490060cb8028c06803066c01804065043c00420303102e818a00200832811a201e01900c0c80800f8192004085300f00d8068088050020487806423021c024044038018000434c0381201f010601832400810a201e01900c0c80800f8192004085300c04807c0c604208668078050208060508010444038000438045c03824010e01a010314000102201c12008700900c18a0000811080083000086403f0210321a30a0940ca0ba0001e9a04807c0f10601480f600205c0c930240b703e8348300648c102f000981205f81780003b2a0c02f01e40002e81d9817205c16c0ec804e0b40a4044076585941902203b817800340e60d40920ce0c01dc0bc002207005b06106a00205c09cf02505f03683006302f000086803201701500c000025050382c02b82b02200600080002a81d241540c604e05010ca82702446602e42c0a9000818074941381222f21b031c1480040c217480b80060630ab19e0a1803000285d857050a8268282c0c017a16617c142e0a10490e11810d81702990b812826a88248c087086c14809485c145102702581e81 else 0x21900810a90481f10000f4807b8240d007780083182e781906fc00418c1a068025c174209018e0c03e20ba0001d9c08b06a04906106605c0f600010d302409b83283500083102e04e881c81202781702203b340e40902ea0c813838c0b8112207010e05c09c90240f204e044086521721506d08d082025303881881703e03401d182380500e8094811c0da11a01802808604a7c0c41601100701263980c21602601061640cc140210697e0ae06409403c0804601e41330b00660a010834b504c1c80f81a40f00bb05103019008558288270244124384361020780d442e0d204ac61605d00021c21bc140822170644b0aa09a45a4520a10b8000060120420322d85922d22905008400104c1751350302116c2b02e04301981942e828874861661580cc0c414072330b30a90e10d81082190ba09a0a0322985605c0850330501a4190ec660e407a42e112874c2c042861641481706940c021070064422690b812000044834e0a30a810a703185985605c0850301a505019138288261120e407c05c0d281804a042a03a0250880874142e0650ae0a20610bd0b30b842034a585421821700185d0500e904d0c2a82484c80e82282081807942c02f8288008420d2e2336176152160624140690254304b1821082803160a03401eb0ba700185d8540e81a81a10501a5146d46701807a00005d42c04a0c8920823723603203c03102e23321721602503d611a11980a01d0129685a0530010008541881a419d082604a0f08284a16a1521c41321b814069217084064560050ab0a90be0a10b50bb0b033834a98dd0310000f40c418c095859181942cc2c42b82980042ec2a0c40e0ac14c0ca17c0003a6150620704504d1850de0a400041010806031012d0bae8c20001880f41420301a009685d343700010610405d0180c404b42e904d021050025260a10491810e02801e01710d90b10b81281eb30508248c08702040b886c85420885c095643845e0ec82842e04a6a16a1540c217062814069025450bd0ab0bb0a840812831034c0a258d18cc0e8094942d42ac2a0740420c404a0d3028962f40c076617025281d01081e03140a0348129d85c2040f018a0501a4094f01e10181881d81a0fe07b8008073c0c80f40d064c003208a0801e60703f606a00206032a603b03e034193003030c82682405d81e0d081880005a8810064811050c0d80c40f80e80003d0655c0940803ec0001e940000381741f4981f02702502302004281b0000d10180fab81381107203d03e04306380005d4c09409a07607819406206c0001ea604c1c810c0840f4b02607a81e0860c7018042703e0630210432409c08021811408e07207c06828400406013b204e0490381ac10c09c080089102408204e0440865c09c01c00808c0a06707c06e4200a0003d83d0128371b0070000af025) else (if i<6 then 0x5616216062069070283203eb0b012928598588541881a41c0c0c4c2c0d20e0463660821706403d07d06a43a06c616530b0310318348381585485c1e027c2081f41ab0501a52c2c0c40c60e00d2502400c80003d025062301ec00026831012950520302081441a285c094f41301807a0e404a5a3003e08206880c0210253c06041031012920300f41880948c2ec2a0c4c661050280d204a8062025069181d0348128e0501880941a4902807404a0d24062025069181d0128348c1fb03703019480fc81b8180ca480d09640f06407102d065c0c80ec00503ee00016838900a425413c0b0812e0c804a04e8148130110160e89c09c01c0009002506740a06e403e0370b0250190001af02a02c1f01b8095282282480e8020480560ce0d20f80dc04abc0906c071c0a80b02506e38128370a13413c0ad04501902502202e0281b41d1612a13c81204e056580a020c09c0841206902b3e04e040388348159413827425501601e02e0250290201b81d81d1881004f0130160540ae603240a80980b09c2c038150218c0ac0b00a80a490200ca04e1340e9816044812136815010b05406509a02081202bc0902240b09940a808620a21441340901503c81281383583602183ec042048113e0201501c01a01f41a4c0450118160580e00d26098070022c098080250693c08c0940383d04b812036414205a04013c05330560480f41a602408902d02009120450248560438108160d204a815012a41481206b06c0960250270328094080225c048380128320110108349e0240b01c00941900880841a510120580e00c80440420d2781181008207406cc0881440902540a80080b6010c0a034812920480e80860501a4094c0750280d204a402b40807180940a095079383620460520581140484a037210ac0ac1a702008a02502824d02d204204e8100440e2503240a027071220a013819205812838980840950200881a4a82404a0fa81404e0d2603a40b0250692204038816034900b01c41a470120d38100e24c080290691814a0420503b1009d0250201b480e80d78110168120d281404a80290274080250712a050138358129102009d0240941c4a05281004a0d2441240a0270250692a04204812834910200a40941a4881404a04e0d2440940802506920148128348d0200a40941a4881004a0d23c068044030640230920650440244849048848600201c120339c24300c09019c804008e0ca3a15a0c61560c201021216a01069064550b50630b30610081090ad008348322a85a8558598548040848328041a41915402c2c0ba0790420d20c8780003f02403e02008f232070a01021540001201f033010038013d00810a69020000f819823c10c19e804085242842c07e07c0ba078048464402042a21421502405d02e03e027201021492010601f01e01710a0120 else 0x82183244d42124d232330ab0621091904403b854032208e91c90909110848c8d42d402c2ac1841849a1320420c89a15a0c2140880772320640214100838034832100f080408419084020e00d20c84070069064191910083e836010832181c01a4190649a4020f004e0fa0fc0420d2807006906419269008218360108321891029c8ca08410cb4290490004641094030427c0006207d03d0682e0920d05320c049832c0c83060be00290601bc1f40880ec1a0d4678280d210012411c1040ca808e082102201d047041012828119c0a218541f01a00940e8ac2ec2a8240f80d00400e0074861761581407c06806707003a405001d03c032012821c09c0a2029405009410c841046c46e46a91691409a04200007407a0fa42cd8268100a4043055a390210a3078414413590b04d012834930058588260448c201c2240f81a420200009414085c085f82a81682694504c81807805d8280c4048bc16c01a1661681240b4134a282680705d44d09908402180040c8e0ad0ac09406010a1d410844012a0a4002f05585a0448c085c2241542141a418d04d050085a05c8180e00420d2561606340c069021070330b031a060380108349985d8570501a42081548cc249142f42a0f80d08280ce0e007486170a003a043055413078414403103402a81090b0380349d0868590310000841a41c0f42c0c40d20e0461721608707508203dc1406c062481d031038034928d81f40e8190094b46e11c0fa0c701942c04a721c20921b215633c14069064055092082590b034826a0001e8310339e85985913500013503018819d142f42a0741100aa87410e828861661507203a0270554120a14144b0b10e05001d02183203482aa0990ba0a2d8590308580841a41c0d42c0c60e00420d2)))
def q237:Packing:=(368,3,9,0,0,16,0,q249)
def q243 (i:Nat):Nat:=(if i<4 then (if i<2 then (if i<1 then 0xa00000000000300000a00000400100000800000200100200000200600000500000100000001600d00400000000b00000600000000100100a00000001000500c00000000200000000000600900000000700400000000000900000400100000600200101d00000300200102000700000101800100100000000000300200300200b00400100000d00100200100a00600100400000000700400000400200000300400a00600100100400200000301400300d00200000100402b01700500200000800300400b00200000000000000801600e01b01400200300100602300300700300000200000400400100300200000400d00000300400100000100000100200000800100000100300600000100800000100100001a00200100000000200700000300a00100100b00000300000000300400001e00000000000201600a00200100100002600300100000300000300700100100100000300600400100301100000000102100100a00e00401400000600401301000000200100300800000100700500901600000500000200100400400701f00000500600000a00200000f01700300000101602d00700600100000600000000000100500000500d00000200000201200e00800200000100500800401500400000500000000100201900000300500000300300100100400700400200000000700400000f00400001300000b00000300000f00f00100500300500a00d00000400100000200400000200000100501b00600100300000000000100400000000200100500300300000b00000100100700300200a00000600000200600500100100800200100200200100a00900100a00100000900000500200300500600000a00b00c00401200100000000100f00000301800000700100000000200100000200400001600201100100800000800000000000100800900300100000600400000000200000100000300000101b00400200000a00100000100300200000100000100500300001500000e00300100000000200100800400000400300000000100000000900000400500002c00700000000400300000000200100100200200000000600000100000400d00200000100700000100000000000100000b00100800100101900200100100200b00100000500400100000000000000100000400100000000900000600000000200000200300000000300900000000000500101800d00200801300800100000700300900000b00100000500200000100100200000500200400700300b00002a00000000800100800200000300000100100300900300300200300000000000500000200000200000600200000d00300000000400100100b00400000200a00000000000200000300100100000000300300100a00a00400401800100e008000004001001000000002000002 else 0x4880dd281b52663aa0373d1ec602da00001c01cc000000000c0345e07f60212403eb1a6a0c6718000000000000002000400000000000001a0d940000102180000070a74000000000316c781008085f7834da96cd2035000006810b0000000001412e800003033962b59409380000310f0e014fc1cd583c90000000000000012970e04710046991f9b00a89075d40fdd124980000e03d4343ec000019b1f876b9000efc06c383dd000010c8b80000383ba0000000001c053380b6d421760654000040244f692800000000000000000000000380dc80000e051000001de22f0970e6642a0f90000000000000000000000000000000001e81abc24400000002ac60ac68036000000000000001856a8000000001c0958000000000b41e740105012be3a77f01fbc087f00ba102720000000f828898a1a7db0933603d86dbfb00b500000e02f001ed000005b26b6086d4159a221aa075f410168242804633a66ea70f5a09ae826c070ee00000c174681e8e048f683ec0982993490000120ac2422610198201a074623c1b4cd97e000000000000000000000000e04540000000000068400003421d80000825ea04280000000000836ffc003d42052829c4012400003c17e21104000000000241ee5925c500580000188a86807dc48c40000140484013400001a05874991fbb590480d208c48e1e13c3690771c0d7f507ae0186f9704c03eb023bf035030831c259000005ac4bc049f6908e6dc29029f0000040d1340689910d4031bc10ab00d490450805d500b83c0ec40039d02b060fb341c780000044df00e6241109842c415d200000000022987000000f0f9c11ac90fb66545a01c8804dd01b60000000000000000000000016eaf400001240700000000000000323444653e0000000000000060289c092240e100000903da00002819b40114000008125f41eb80000e011be1114000000000464840000255200013100001766274154023ee547df2012d6220203a9e37e9c4480001e80000301940000100d5e003c2018804e0a8214c8378111f480ec3c22eca12ba449a842be00f93a232e20308076a9d2d2841330712a8ce82836640f11076a602b30c99000008080200000000038116248a9c8f7f2cabc0213d863a8e40501d089345d18672070cd028800004048d4044981d8da3c99059d6105450df63a70d11fee052381de80000000010a622c18680000701632048429928000000000000008219983c70000000003021780000b088260df000443215b706f26855c00000000000000f6c7c1d37102ab5408e40480000000000000000013911d7680690a62e0000000000000000000000019a13739093a8886126ac13e00000912a80000000000000010524000000000181502432340c840000000006020b20d600000000000000020c080000302840010) else (if i<3 then 0x41a0381901fc0000091d580000cb64c0000040dbd82afc0416000000000412fc00000ec1f000000000000000812268a31cc3f72208400001c221281cd000000000341736809d014694030151ff980c5ea67cd6e6cc08f21359000012107900a5f81a1d72d48e9f502058000000000802cc0000382d92021d36d475a27f80ec478b34111c000000000160c200000000008af100000008dc00002013800000b24980000103bf000004060a2a2f800004528c4438c00006db2404282a11d5c1039307ad03060000000000000000000406c6c814ba3ed000000000000001101a000000eda181efd807a000000000180c3803fa7b7286029c0da8cdb8100001e069b81ca302a0f760e40b91c035000000000180b8749893826af3244e0170998fbd398f03f28009f414c0000040085a0a3400007a1cc537f000a5440b500000878bca0d0c000000000a0528005ff40720000090806c4c4e416200000f07a760fce015082345e19060000000006aa7d50693e05ac098c00000902ec00000000065451a76b5a0a680000000008039800001a4ae80000a033f0f0b0558c7819300000a02728147c02efc441380f49909af039c4a6af0113c00000a422a058200000699fdd397501e1486e0000060493000000000040b6238fca11f800001cc9aec0690029ee8941009c981d000000a0e32edac6a15d326ce000000000703c2528012910c449478098c044d60c0e1dd9d81287b41f40a666a1e50266c566a2024611119315f400cb17268004bb0368305704078da18f0000000001e0ea100f5981e0f0133e08a781c82847e9206e00003021b800000000164c3c000000000a028f20349c8228000000000a085f914300000004dc000000000282a7d226000002013d0000000000000000168b04860000196d54000000000000000000000000000000000e882800001840c0000000e1a4137c83b630113c326b29ca381fa1263e0ad0500548101d70318a11ac000048225cb315e88c581feb9454e762f80dc89112350659050ea072641c38000040070cea0880e7698060000000001c11dd0300b72b560a09dd8fe02f70000000000edc5510fa4015b08a1dc008b8168000000123a811d11350518ed205bf40000000088886c8fb34045000007441600000000000000702ea00000e594700878206b811b004fb4822c000008052981c71538ee045fa6f4810e680000b6584821ddc0b3800006659b92e1000000000000001809390e1d68162005acc0cec49860535800000000000000501e7265d3a261c000000000a20400000000002d396000006019a0d78a034ac03778d20a9084703fb000000000141f500000a0396000000000000000000000002019e7324a336fd80dcc00007844340515407f80000000000000000e9e80c5f033000001a0a3800000ba71121abe11 else 0x2c9c0213a01b646421817780069a3216814b7830b6002b011c14649b5b427160200000c13268b6290403644469d85a0068000000000241c20038287102009d480cde9117406ec621da405c8000000000000015ceb604063074600003d222a823d0653cc44b400000000000000c0d6400000000085884000000000000e8000018092c000010255000000000000000000000000a003000002834100001a11f4000000000108d40000001fc723fda012be0b1f559b00000e037e0000246268394c00001e04cc000000000b142d42b3c50b6d84570000180cb40000180824070b488440000323b1f37fbaa4b6995f7823fc08f068ce4000078a7d401f2000000011c903f00001e0e540000000000000000003816503b056767ae0125c0f490312000008c1bc0000000008b72a84c4040638828b7443de0114000000000b48846110398b400000aa71a00001819d482c2000000000000000000000444470e4458ec046d0000000001a59e80000a437200000000000000000002d0708084503880000142556d13e3812c322292439000000000061255a0a4c5d37d80df791da80f9a410c90178f07b080c4e0842d0417844f160f97d21d9823900254000000000003aac4351208d24229a0140b76c200000000000a3680038801f0009f5842700000c51980138000008b8b8a42a1c03c8517e00001a0be00000000000000160980000000000000000000000007bb3900001445e400005837e000016f0f400000a216403af6ca77c0f7d0c1800001e900c000000000447a200000000014c451046de03ccc121a82534b9362e1fc000068290336a42017800000b2ab0000100b9d1909b8164f9673e0a06022d5aa38d219a00003024aad31e0000000002d11600000f075a850e000000000000000000000000433f50000120ad3024000000d065f80f3a62140000000000608140116f82cd804ce2297f000d50882503ed44425051e38a97892d40000369c9892ffe04788652e00d500000a1936aecfe09cd0000000001d0fe400000000010522e0db76daba81d96000a0000241e80000000000e4cf480f148007d0090040e1609831108b189da088d402ab02a43227e286b208bd000000000140d810e4d7a159d05c6431c80000300250000000003c0a18000000000c10580000180fb0020e000028072fb008000000000000fc48380000014ec24000000000f21ae0000000003045100000211f000005903e2b73000000000000000bb73a000000000588f9000000000050d6800007018200000c09d00000334b8c90a400002835bf068e02aeb01517149cd43a560697c16c781f7d759b411d0c0bda9a800000084e74000000000000000000000007804de04a404cbe8009a2c4d00000000016dc4000000000000000000021033a05bde510d00753837500001c096341)) else (if i<6 then (if i<5 then 0x47f5803a4c18d6810081470229786097902dcb077c40d38420e8016e00420000000000302a5d931800000258ff0472b08960000000004241000000000000000490d000001a00b95e43882ee074c3870e00000703c80000000000000000000943fd4117c000020400704fcc31d4000000000351e728897819e80000000000000081ed80000000000000000002800800001aed9fc815b84072439c0000040b87334c3055a00000c8b3204664006446529898cb822400000c063f10258000000000e86ac91469a200e093800000000000000000016b10f119c00000d03a900cca85a58000000001202de5ca8000000000000002501f3b44ac04f3a0d500000000000000000003c16d8000000001a0f870101a81f300001804d79d0abbb489087e00000000000000804c600003ca328000054850c20e80000000000000000000c1ab30496308f2000000000540fb7480868a68000000000c44c400003d493000000000140fbfd9efb8335007bc0000000007b418c158fc8f300000000000000000000000000000e01dc00001c01b70a0f000008eca40000682ec004f100d570858f810c667ece04afc22f683cf301da20bc5022c03069707a9ec3bbc6279397184849e08440134681e6204a2e710dc22b503f6f0050801d8006bc03c3a05ec000008151800000000000000000000000f1081e11b80000000002a2a000000000000000a024c00001522f8000042039e81c8000000000341ee0000000000134d40864a0f18000000000000000000349a458865347fc00001417980000302f8a21a0000000000d03b62040d814ec01c58019c0000090caa5242b2310a038985630000058311489c719a69003ee07770c9d8c88800000a40d8000028105000003b71c84c5f021f00000000000000000001046800000870c4000011360d0156e028000002cb0af064a000014171202d3000000000000001244c00000c04c8c08ea02df943ff40afbd1910000000001a0928000000000a2264000000000000004442546f440000000000000046c840000000008203200000000008171b215c04d49810b102b5d02996d10c4180902d4203fe000010a326204a6069ea12099101c011170042a0db2c1d5800001048164e00000050081039364005fd1029003f00574e0c76860c80000369340000356281828910629806b800006807fe08e6a06f15d654590d021ac2115688559b214d050b0444b064ca8254b00560640c00000916b7074b40c989e448b209e01b4c0d8d405c3848aa479040bc100b4e134e907410074e554eb9bff80698ae93489ae393062086220c57c1286cb23a22d880e4f00d79829ee041aa03ae517efc3225b87840e67400109a81726cc604ff014dc3ab9d0812a0232c0d818050f22f62c9a8c1e28ab62b03f8224a61dbdb805fb0559c055401fe78 else 0x20bec00000000034391c05e800000000000001a096f815e0130057855a6c7800001a3d70000101053c88779362000000000211da80000b0565c0f37c1bf80000b962b08fc8000038352e00520000000005809ab00b000003404580000d188600003802ed93d474508e0fba01a8e9133b06bca0906d22680000000012453f82497597a000000000309aa5a276405a000002c0053296fd01de24d3c404358345f0484a0ec800003004400000007c64162a21ca704da2448400002b0415033a8ac6525add82d500000000ce81e5e82fd707e9803dea5a31004f3a2674a59a001218a096268e00000000000b1c602a9200ab821b783a4d05f4000025232800000000000000000040160798860000000000000000000000019228883d900000000000000781105092040fb70193d034b5254a00000000072221a022660c28000038348a182a0000151f4202c6000000000000006848b6438e2ed1c000030498d03bc00000000000000403328853b406180000116bac65b0000003065d008e0000000b180000b04fee90e9454e800000000120db9c01d400e34788d007b8000000000e2623ac85d4879c0422f0492000001d8a6004c0000000002899dd01916488c603800000380c80000000000000000000a0799a0489d0bd3a03c83074000004cbce819750030a6ffa1102398efb063c00000000000000ea8860000000000000000001a09700000000003267840759408300000c26f820c651202d21aa948220000281cfd04089a712009af9962200afe28ab0eea040fd99135f768c00000c030f811bb74d30056b40cd683c01563bd09d42d7e61453b30d5401bd8224691158010b8101281313031c908412425400003837dea480a1070d985481b8606f580d75c0075bbe042659e2afac096800000034e8006c4097c03ca0000000003c22d8000034364e0cd3021aa845cc287d42ac94199fbc37b08ce0000340b6902c0f0325043e400003823e043960000180a758145f002000000000000000e06ee00003c628000008b73420504c8a25041fc084b6001b019f58062b47ca608740187581b4b051840ed00000501f00000040af440c0800000000100cb2000fa010f2463e36c780238f0179f2227410d009a6500fc00000c00d7c01bb1c9357521c000e024da910f8068c00000000000000904f6a4375c0fa000000072c00002d079000000000000003443379c14121cf090f0424a75391201280000000005228f000000000005406044600000000000000000009988c0000300a4c0331875a1001c618b2c2b40726852109800003038be091a64d6c0000581c100000c106d086d4820f614d2a10c2de30b801600000602fbda4dd040e2a89aa4c0a410f183677b614000038e4cf84114045000b2d480f881a4b03d9200c7c1a9b03a6d08d204d1a511050c322) else (if i<7 then 0x4c1d6610fc7a54a0106801cec00540065de057d0080a086361244c0930000000000b01cf4e4308172b597bf786800c3c0000000000000000002015cb431f00001a0c2000007214f0000000000000043a6c0000000002409b80000e05e4000014a1af016600001c05199d5f401290000000000c00a3032a401b200003456c001dc000008c9dc5e362001d108dfa06b2e098b80a100001607d4000018316d03a32053400000997aa31f46c1d800000127d7561400000915280000504ca80f59c049f308100000000000000140f2f64cfe44180d01800004a47f680ffc2310000050922b4184000000000a146460294c490e83f2000000000000007032b826c20000052205013dd74dbe10ba817fc3c4e80454829a34009583c1d035a0000000000827700000a00b400004019600000000028138d82f56481c0000210e9a0064000000000180ca000007684fc01c000001025f0000000000000000000306c2c8837c07fb8476634f6c8f2c420900000f04566e1ce86185817200000c0c908041f844d00000a0e7a50ae2022e708fee0784c21e302aa27764629940246180c2d0461c055ec897e02b7806c8486c1421c8523ca060dc23bc0000200e10000000001c035c00bd000000000000003813000000e02c800005240100000000001d300000000000e0720019448173000000000000003c108a00c6000034d0f0000000000000000000000009721600000000010903a0246806f84047b0051e944260857489ee224b9050040ad941911da860040cc015800005030700001029920020200f2a07c6a120680e95931ec07f2f20fc000064b18c08f7123a6a98f8000000000602c20d8e00000a2160000000000483a2a158400000110a0000000000000000000003404168400000000000000000016073c000012283a968e0000000000000000000000000000303b9812dd40c1000007103a80312000010113990df000000000200296827d308c0045761152401a00000000000000000000d00ee00c800000000007a25080936c1f880000326fbe04f341f380000000000000241fad011c0062260f880000684289055220cfc00000000027886283c400002033910598e11900000000008683d6115000000000050285e027c0000000000000060c8cc2419229b0000080756088ff0a6b568c0000000000042a51054c00000c817a00de3447200002c0179809694468a041152068000000000623c10066800005482f88185c1f4b80a3b0586171368247c3a5da02b2601829c35a44540000000002d649f81df000000000099d580000c15020000000001b87a000006cbbd01b7b9148c40d600000000000000e057e202d219fc0000010894000000000183719018c810b400005042300000a0e488078f8020b001200000498b43a63526d000000000000000f2062 else (if i<8 then 0xf7837bf626a20a1b01b580000305e84ebbc000000000c72c5b462944b6800005751c0000000005a2330000028e901cb400000000006027a85335040d00001b5107983730374501e8e1213c20800000000010028a806a9116a186f4000000000102697447ec0be68562f8357002b8c03d400006a14700001602ff013080000000000000001b858391c264560ef0000000000b021a00000000000000400eb750f80000400800000020ca784b10021ca00b724c280000000009019e0000268a1183f0d062e00ecdc1020000000000802100000621b7ca2180000000005835a000000000068c480000e92fec29080000000000000000000000078030000000000311e50000000000089fd81010000000001a0e0c0000681806563e00000806580000b0892000000000283c40000060165c9970000000000e054c00001042b3019200002c12cd83d1305d26056dc0d9084610000160d700000782ed904240000000002d356f26b4b0941d1e7902c83268200a5fec9bb008ef04100000000007915c000000000140c208acbc05a40000000003a1d60000000000000000000000000000000000000000000000000000000000247e00000000000000d479a00003210cf01882024924c1c000000000366f4c0e5dd948000000000000003020ce80bb6970000000000000000d02ba00000000028362b001a410e00000402fe00000000000000000000000000544000000000000000000381758000030044c0777922c80000701a740ede122c3819e200cf60da8000048b4300000228e400005820c144b3606f4000069b80e061800000000000000304ec0071800a9000000000000000c1196a148000000000000000000000000000000000001850000000002c4b880000000006e59dc15d800000000000000689c80000701f0000000000000000451980800c139f038dc229a8437a40c50a1060025c0000041cda843a9487f20cdc0000102dd00001885e4cc93b820ef02cbc28fbdd3d9092c000018002c00000000000000000000000781e400000000000000403fec52da24cfcc1829023300001a0ce2c0be800000000008d490d3cd9c3b411fa0000341f47913c4015c00000000040004000000000290a4cbc2de0381404ee464aaa9042055c601faa083780e600000805f800002005a304bca085050c98226b200f704cd701c50000060087a0794000000000b04136046000000042154873acfec0000180aa00001243260023000000000000000000068366c0233250f0816bd1181d039580c26406b0831b000012eed200c755c43122ca00002022cf0136c043460292003c28190947aa80914000000000b0095211eb402ba8444000000000254b10000000000c071d406ed011f00001c8fc40000000000000000000000000000b034600002412d78019f205b6441 else 0xf64e62191c0125a227600001c13a5a1c9d41f080880c06d981b30000068898299260b1f200e9605781d9d300cc0000060b3d818f80000c00dc000021dd6201a8f72d9810f74188000008443ee02e80000000000220fe81671a291846500000a103d4085000000b6aca887681ea9a12400001c290202272031800000000000000481c400001886234013701021090f2045e01ff84b3a4292600003800))))
def q250 (i:Nat):Nat:=(if i<9 then (if i<4 then (if i<2 then (if i<1 then 0x4e929042bfeada74948219ff54d3a4a410cffb169d2520867fd5b4e929043bf6c5aa694821dfb6ad534a410efd956a9a520877ed5362929043bf6adb1494821dfb4ed8a4a410efd876c52520877ed8a56929043bf6c5ab494821dfb4ed5a4a410efd876ad2520877ed534e929043bf6c527494821dfb5693a4a410efdb169d2520877ed5b4e9290423fe95934c0a613f74ed5a06530e7da52c13021876ed82549690c2b7e8daa4b4861cbf609815a430adfa56c0ad21856fd5b069690c2b7e95834b48615fd46d5246430e7eb04c0a321857f55b605190c2bfa95b028c8618ff6098a46430cfeb02ad2321847fd5b4a9190c277eb5934a9a419bf5ac9a54d208ffa364d2a69047fd3b269814826febd93498a413bf5ac9a4c520cdfad64d2629047fd5b269314823fe8db34982415fe66d824c120ff92a6a92609057f89b54530483fe8c0a62982417fa4ac5a4c1208ff95698b129073f9814c189483bec98a60c4a41df64c03a62520adfad61d3129057f90b0e9894823fed5b129ca41b7b5497a0e520cbfb12bd0729065fd595e8394836f615af41ca41bbb5496a0e520cdfb12b50729066fd595a83948337e2cad41ca41bdb5495a0e5208ff936ad072904ff90b46839482afebd8728ca415bf5ac3946520a7fb16a9b121047fcab54d890829fe9db02c484157f5ec3a62420adfad61d31210577d5b0e989082bdea5874c48415fd46c3a62420afba36a9a721067dd53629390823fec5ab49c8415fd46d53464208ffb169d2321047fd5b4e9190823fe95934c1a211ff56c9a609108ffa764d3048847fd3b269524423fead934992211ff66d8a4c110fed2a6a9240887f7151569204423fe55b049ca21dfa549204e5108ff956a9a528847fd5b4e929442afe9db04bc821d7b609525e410abfa76a92f20855fd8b0e979042bdec5aa6a48215ef4ed8252410ee7aa6a92920877ad8254949042bdec5aa4a48215ef4ed5252410afbb16a9a720857dd3b60939043baea9aa49c8215f74ed524e410c7fb04c52720877cd8254939042beec5aa49c821cf76098a4e410eebaa4ad2720867dd8a56939042beec5ab49c821df36092a4e410afbb16952720857dd5b4a939042bf69db0494821ddb54d524a410afdb16a92520857ed3b549290433f6a9314948219fb6095a4a410cfdb049d2520847fd8b4e9290423feada74948215fb62d534a410eedaa6ad2520867ed8a56929042bf6c5ab4948219fb6293a4a410afdb169d2520857ed5b4e929042bf6c5874948215fb56c3a4a4108df956c0ad21852fd8b069690c2a7ebd834b486159f56c1a5a430ad7a960d2d21856ed2b069690c237eb5934a9a411bf5ac9a4c520fe92a6a9260907f6152545204422fe55aa4bc8214fb62c3a4a410abdaf61d2520856ed6b0e929042bb6ad874948215eb52c3a4a410 else 0x215ff2ad524e510e7fb04c0a7288777d5254539443bfac0aa29ca215ff62d514e510efeaa290a728857fd5b485394439fec0b009ca21dfe601504e510efdaa4902728877f98048139443bfca82409ca215ff62d204e510affab6902728877f98548139443bfcc5a409ca21dfe56d204e510eff240c52728867fd52629394433fea83149ca219ff4818a4e510cffa56c52728877f920569394433fec52b49ca215ff62d5a4e510cffb14952728867fd5a4a939442bfec5a549ca215ff56d2a4e510efeaa2c4a528877f5514e529442bfec5a7294a21bfd5458a4a510cffab2c52528867fd39629294433fe9cab494a21bfd5453a4a510cffb129d2528867fd594e9294427feada7494a219ff6ad834a510efbb06a9a528857fd8b54d294433fed5aa694a21dfd605314a510efeaa298a528857fd8b4c529442bfeada6294a21cff605804a510eff300a82528857fd8b54129443beea9a6094a21df74c5304a510eff300982528857fd8b4c129442bfeada6094a219ff54d8a4a510cffa62c52528867fd50629294433fe9831494a219ff4ed8a4a510cffb149d2528867fd5a4e929442bfec5a7494a215ff56d3a4a510cffb0a9d2528867fd814e9294433fea8a7494a219ff6013a4a510cffaa09d2528867fd5b4e9294427fe55aa6c10219ff66d3a60810cffab4cd3040867fd3a66982043fb6a9b04a9021dfb66d8254810dfdb049d2a4084ffd8b4e9520433fecda74a9021dfb6099a54810cffa74cd2a40875fd5360979043afeadb04bc821d7f4ed825e410ef7b16a9a920877bd2b54d49043bdea9b04a4821def56d8252410ef7a76c12920877bd8b54949043bde9daa4a48215ff62d534e410efbb16a9a720877dd2b54d39043beea9b049c821df74ed824e410cffb56c127208777d5354939043bf6c12a49c8215ff62d524e410efba76a92720857fd3b549390433fed5aa49c821df754d8a4e410cffaa6c52720867fd52629390433fe95b149c821ddf5495a4e410cffb14ad2720857fd8b56939043beea9a549c8219ff6292a4e410cffab4952720857fd8b4a939042bfeada549c821df756d824e410efbb56c12720877dd8b54939043beed5aa49c821df75498a4e410efbab6c52720877dd2b62939043beec12b49c821df76295a4e410efbb16ad2720877dd2b56939043beec52549c821df75692a4e410efbb16952720877dd5b4a939042bfec5aa694821dfb4ad534a410cffb56a9a520877ed5360929043bf6adb0494821dfb4ed824a410efdb16a92520877ed3b54929043bf6a9314948219ff54d8a4a410cffab6c52520867fd3b629290433fe1db1494821ddf54d5a4a410efdb04ad2520867fd8a56929042bfec5ab4948219ff4ed5a4a410cff876ad2520877ed824e929043bf6a9274948219ff6293a4a410cffab49d2520857fd8b) else (if i<3 then 0xb61ca32906ff930629194833fe9cb148ca419ff0e58a46520dfdaa49d2329067fd894e9194833fe44a748ca419ff5653a46520cff8b29d232904ffd5b4e9194833fecdb14a98419ff66d1a54c20cffb14cd2a61067fd1a66953082ffa8daa6c08413ff56d3a60420cffb369d3021067fd3a669810839fec5aa6c48415ff46d5362420cffb56a9b121073fd53605890839fe9db02c4841df754d3a62420e7fb029d3121067fd5a4e989082bfeada74c4841cff6043a62420affa361d3121067fd3a469890833fe1d234c48415ff4ed1a62420affb16a9a721057fd1b54d39083beec5aa69c841df746d534e420efbaa6c0a721057fd5b60539082bfe9db029c8419ff6ad814e420efbaa6c52721067fd53629390833feadb149c8419ff46d8a4e420cffb14ad2721057fd8b569390833fec0ab49c8419ff62d5a4e420cffa36ad2721077dd53469390833fec52349c8419ff5691a4e420affb168d2721057fd5b46939082bfec5aa68c841dfd46d5346420cffb56a9a321067fd53629190833fe9db148c8419ff0ed8a46420cffb149d2321067fd5a4e919082bfec5a748c8415ff56d3a46420cffaa69d2321067fd8b4e9190833feada748c8413ff2ad5360910aff936ad3048867fd5a669824433fe9d334c12219ff4699a60910cffa14cd3048867fd9a269824433fead134c12219ff4689a60910cffa144d3048857fd5b269824433fea9934c12215ff26d8354910fedaa6c12a48877ed9b60952443bf64db04a92215ff26d3a54910efdb04cd2a48867fd3a669524433fe85334a9221efb609814c910ff9b0498a64887fd5814c532443feaa8a6299221df7625314c910efbab298a648877dd9a4c5324427fe55aa6c02213ff2ad3160110affb36ad3008857fd9b4e980442bfecda54c0221df766d534c110efb936a9a60887f5d53549304437ee95262982217f756d314c110ffb2a6c0260887bf98160130443fec98b00982215ff66d8a4c110dfbaa6c52608867fd9b629304427fecdb14982219ff26d8a4c110affb36ad2608857fd9b4a930443fb6a9aa490221dfb66d5248110ffd2a4c0240887fd9534c120443ff4a9260902217fe62d3048110dfdaa4c5240886ff950629204437fc9831490221bfe6013a481109ffb169d240887f798554d20443fecc1aa690221ffa60d5248110ffd316a9240887fe93b54920443ff4cdaa490221ffc60d5148110ffe356a8a40887ff0ab54520443ff4a931490221ffc5458a48110dff314ad240885ff98b56920443ff4a927490221ffc5453a48110dff3149d240885ff98b4e920442ffcada74902213ff2ad824e510feeaa4a8a72887fe95248139443ff8a8a409ca21dfe481894e510dff240c52728857fcab615394433fed5b049ca215ff2ad824e510efdb04a92728857fd8b549394433fed5aa49ca else 0x4837fcc52b498241dfe26d5a4c120ffb2622d260905ff98b16930482ffc958b4982417fe46c5a4c120ffb2a68d260907fe952469304837fcc523498241bfe2291a4c120dff2b48d260906ff85a46930482ffcc5a34982417fe56d1a4c120eff1368d260907fd95326930483ff4a913498241bfe6289a4c120dff2b44d260906ff91a26930482ffcc5934982417fe56c9a4c120bff2364d2609057fc9b54d894827fe55aa6c4a41efd6053162520aff93698b12904ffcab4c589483feca9a60c4a41ffa5493062520f7f30298312907fd9314c189483bfc4da60c4a41ff64c03a62520bbfaf61d312905efd6b0e989482ffc85874c4a415ff56d3162520aff95698b129077dd314c189483bfcc1260c4a41dfe6053062520eff2a2983129077f9314c189483bfc2da60c4a41dfe46d3062520eff356983129077f8ab4c189482ffc98240c4a41cff6043a62520efba601d3129057fd1b0e989482bfe85874c4a41dfe4c11a62520cffa748d3129067fc3a46989482bfe9da34c4a415ff66d3022520ffd2a498112907fd9314c089482ffc8da6044a41bfb5493a22520dfba629d112906ff9304e8894827feada7444a413ff4ad3a225209ffa169d112906ff531468894837fc9823444a413ff4ed1a22520aff936a9a729057fd9b54939483fb6a9aa49ca41dfb26d524e520aff936c0a72907f6d5254539482bfe4daa29ca413ff2ad514e520aff93698a72907fcd524c539483feac0a629ca41ff642d314e520efb93698a729057fd9b60139483feca9a609ca41ffa549304e520bff236982729077ed52625394839fec0b129ca41df74c5894e520eff260c4a729077dd3122539482bfead9129ca415ff4ec894e520affa3644a729077dd31565394837fc982b49ca419ff6255a4e520cff912ad272905fed2b16939482bfecdaa41ca41dfb26d520e520fedaa4a8872905fed2b54439482bfecdb001ca41dfb549890e520e7fb02c487290777d5156439482bfec5ab21ca41aff6098a0e520dfdaa4c5072906bfd81628394833feacb141ca413ff4ad8a0e5209ffa16c50729067fd9b628394836fec12f41ca41b7f6057a0e520dbfaa2bd072906dfd805e8394836fec4af41ca41b7f5657a0e520ddfb04b5072906efd525a83948377ea8ad41ca41bbf6016a0e520ddfb12b5072906efd595a83948377e2dad41ca41bdf5495a0e520dfdaa4ad072906f7d51568394833fec4ab41ca413ff62d5a0e5209ffa56ad072904ffd0b568394833fecdab41ca41bfb5491a0e520dfeb028d072906ff551468394833fec4a341ca419ff5651a0e5209ffb168d072904ffd5b46839482bfecdb008ca413ff6ad8046520affb3698232907fd9534c119483ff4a92608ca41dfe26d3046520eff260c4a329057fd3b22519482bfeada728ca415ff62c3946520affa)) else (if i<6 then (if i<5 then 0xf6ad534a510eff956a9a528877fd5360529443bfea9b0094a21dff4c5804a510effb02982528877fd5362929443bfec2a7494a217ff2ad5360810effaa6cd3040877fd5b60939043bfec5aa49c821dff4ed524e410effb56a92720877fd5262939043bfec5aa694821dff6ad534a410effaa6c52520867fd9a269814c33fea9134c0a613ff2ad5246530cffa52c5232985ff90b208194c2bfecd9040ca613ff6ac8206530affb16ac8329857fd8b4a4194c2bfeada520ca619ff5658a06530cffa52c50329867fd9b628194c37bea92b40ca619ff6255a06530cffa52ad032984ffd8b568194c37ee9dab40ca619ff66d5a06530cffb12950329867fd594a8194c27fec5a540ca613ff56d2a06530cffb36950329877ed5b4a5820c3bf68da52c1061cff6251a60830efda528d3041867fd1a669820c39fecdb04c0861efb60952604309ffab6953021867fd9b4a9810c39fec1334c08619ff4a99a60430edfab6c12d21876fd1b609690c3b7e8daa4b4861dbf6ad525a430edfaa4c0ad21876fd52469690c3b7ea9034b4861dfd46d8246430cffb56c12321877ed82549190c2bfec5aa48c861dfd46d5246430affa36a92321867fdab549190c39fec13028c8615ff56d8146430affa56c0a321877f552605190c3bfaadb028c861dfd4ad8146430e7fb04c52321867fd52629190c33fe95b148c861ddf5495a46430efeb02ad2321867fd8a569190c2bfec5ab48c8619ff6095a46430cffb02ad2321867fd2b569190c3bfac0a548c8619ff6292a46430cffab4952321857fd8b4a9190c2bfeada548c8619ff6052a46430cffab6952321867fd9a26953482f7eb5934a9a413ff62c9a54d20aff936a9b029057fc9b4e9814833fe9d334c0a413ff4ec9a60520cffb344d262905efd6b269314827fec593498a413ff56c9a4c520cffab64d2629057fc9b4c5804827fe55a62c02419ff0ed9a60120aff936a9a609057fc9b60530482bfe4da62982419ff26d8a4c120eff300cd2609067fd8a669304833fead334982419ff4699a4c120cffb02cd2609067fc8b669304833fe2db3498241bfe469534c120bff136a9a60905ff9ab54d30483feccdaa698241ff626d534c120ffd264c1260906ff91a60930483fec1db0498241fde54d524c120ffb2a6a9260907fe982549304837fc8d2a4982417fe62d524c120bff336a9260907fe95354930483ff4d5aa498241ffa2ad524c120ffb2a6c0a60907bf98260530483ff4a9302982417fe26d814c120ffb2a6a8a60907ff18154530483bfc4daa2982417fe26d514c120ffb2a698a60907fe9524c530483ff8c0a62982417fe26d314c120ffb33698a60907fd89b4c530483ff4a931498241dfe26d8a4c120ffd2a445260905ff95b22930482ffc95914982417fe46c8a4c120ffd2a4ad260907fd9315693 else 0xa321077fd5362919083fbea9ab4c1221dff26d5a60910dffab49d304885ffd5b4e982443ff699234c1221bff5691a60910dffa748d3048877fc9b469824437fead214c1221bff4e90a60910dffa3485304885ffd9b42982443bfe4da14c1221bff5699a60910dffa74cd3048877fd5366982443bfe98b34c1221bff5689a60910bffab64d304887fed3b60952443ff68db04a9221ffb42d8254910ffdb36c12a4887fec9b60952443ff6c1274a9221bff6293a54910eff9369d2a4887f7d5342952443ff6c1214a9221bff6290a54910dffa74852a4886ffd1a42952443ff6c1334a9221bff4e99a54910effb06cd2a48877fd3166952443bfeacb0299221dff669814c910ffdb04a8a64887ff58154532443bfec4aa299221dff669514c910bffb16a8a64887fdd8a4c532443feead26299221ffb6091a4c910ffeaa28d2648877fd8946932443bfeaca3499221bff6291a4c910dffab48d264885ffd8b46932442ffeada3499221ffe42d5360110dffb56a9b00887f7d5354980442ffe9daa4c02217ff46d5260110fff216a9300886ffdab54980442ffeada62c02217ff4ad3160110bffa76c12a0887ff90b609504437fed5b04a8221ff762d534c110ffba56a9a60887fdd1b54d30443feea9b0498221ffe42d824c110effb36c1260886ffdab60930443ff6c12a4982217ff62d524c110bffa36a92608877fd9b549304437fed5aa498221eff609814c110bffab6c0a60885ffd2b60530443feec126298221ff7549314c110fff2a4c0260886ffd5262930442ffec5aa690221ffe42d5348110effb36a9a40886ffdab54d20443ff6c5aa490221ffb4ed5248110fff2a6c0240886ffd5362920443ffccdb0a90221ffe6ad8548110fff336c1a40887ff9ab60d20443ffcc5aa690221ffe66d5348110fff136a9a40887ff9ab54d20443ffc55aa690221ffe54d8a48110fff306ad240887ff9854e920443bfecdb0a9ca217ff2ad854e510effb36c1272886ffdab60939442ffe55b049ca21ffb609524e510effb36a9272886ffdab54939442ffe55aa49ca21ffd609514e510fff30a902728877fd52625394437fea93149ca21dff4ad854e510effb56c2a728877fd5b60939443bfe8db049ca21dff42d824e510effb16a92728877fd1b54939443bfe85aa49ca21dff6ad524e510effaa4c0a728877fd8254539443bfea93009ca21dff609504e510effaa4c52728877fd854a939443bfecdb0a94a21bff6ad854a510effb36c1a52886ffdab60d29443fbec2aa694a21ff760d534a510effb36a9a528877fc9b54d294437fed5aa694a21ffd60d514a510effaa6c4a528877fd8356529443bfec2a7294a21bff54d8a4a510dffb06ad252886ffd854e929443bfeadb0694a21dff6ad834a510effb16a9a528877fd1b54d29443bfe85aa694a21df) else (if i<7 then 0xffc4daa298241ffe6ad514c120fff2a4c5260907ff98162930483ffca8b1498241ffe5488a4c120fff2a4ad260907ff98156930483ffca8ab498241ffe6045a4c120fff2a48d260907ff98126930483bfecdaa6c4a41dff26d5362520bff956a9b12907bfd5360589483dfe9db02c4a41ffd6053162520effb3698b129077fc9b4c589482ffe55a62c4a41ffe54d3062520fff30298312907ff9514c189483ffc98a60c4a417ff56c3a62520bffa361d3129077fd534c589483bfe9d262c4a41dff56d3162520effb5698b129077fcab4c589483bfec0a60c4a41dff4c53062520effaa21d3129077fc5a0e989483bfea9a34c4a417ff56d3122520dffb5698912905ffd5b4c089483ffca926044a41ffe5453022520fff0b698112906ffd524e8894837fea8a7444a41bff4c53a22520dffa609d112906ffd5b4e8894837fe8da7444a41bff42d3a22520ffdaa6a9272907fec8b54939483ff6a93029ca41dff66d814e520dffb56c0a72905ffcab60539483ff6a92a29ca41ffd605514e520effb36a8a729077fc9b545394837fed5aa29ca417ff2ad514e520ffbaa698a72907fed524c539483ffac0a629ca417ff56d314e520ffbb1698a72907fdd5b4c539483ffcc0a609ca41ffe545304e520effaa6c4a729077fd8162539483bfea8b129ca41dff4c5894e520ffdaa444a72905ffd5b22539483bfea91129ca41dff544894e520eff912aca729077fd5356539483bfec0ab29ca41dff4c5594e520ffdaa445272907fdd3122939483bfeac9149ca417ff56c8a4e520bffa3645272906ffc8a569394837fea9ab49ca41bff6055a4e520dffa62ad272906ffc89569394837fe45ab49ca41dff2245a4e520bffb162d272905ffd1b169394837fe452349ca41ffb22d520e520ffdaa4c0872906ffdab60439483ff6a92a21ca41ffd605510e520bffb16a8872907fed2b54439483bfecdaa21ca41bff6ad510e520ffdaa4c0072905ffd5b60039483bfea8b121ca41dff16d890e520effb02ac8729077fd5156439483bfec02b21ca41dff22d590e520dffaa4c5072906ffd81628394837fea8b141ca41bff6018a0e520dffab2c5072906ffd5b628394837fe8db141ca41bff42d8a0e520dffb04ad072906ffd52568394837fec0ab41ca41bff5455a0e520dffb00ad072906ffd89568394837fec5ab41ca41bff4ad5a0e520dffa36ad072906ffd0b568394837fecdab41ca41dff66d5346520eff936a9a32906ffdab54d19483ffca9a608ca41ffe22d3046520effaa6c4a329077fd534e519483bfe45a728ca41bff54d8a46520dffaa69d232906ffc8b4e919483bfecdaa6c0841bff2ad5360420effaa6cd3021077fd5346989083bfea9b029c841dff56d814e420effa76c0a721077fdab60539083bfec0ab49c841dff62d5346420effb56a9 else (if i<8 then 0x620c61ce614260d0607860205f2c5ed45e965dd65d7e5d265cce5c765c1e5b785b3a5ac85a3c59ca5972591a58dc589e582c57ba572e56bc563055d85580550e54b6545e540653c853085248520a5198510c50b4507650384fc64f204eae4e224dca4d584ccc4c404b804aa649e649404880484247ea4744469e4612458644c644204360430842ca428c4198412640b43ff43f4e3ea83e023d763cd03c443bb83af83a5239ac3920386037a03714365435ae34ee3462338832c832083196310a30b230262f9a2f422e9c2df62d6a2d122cba2c7c2c242be62b5a2a9a29da2934288e27ce2790271e26e0266e263025be253224a62400232622e8225c219c211020501ff81f521ec61e201d601ca01be01b541aae1a08196218f0184a178a16fe165815b2150c146613c0131a128e11ce110e104e0fa80ee80e420d9c0cf60c500b760ab609f6095008c40804079207060694062205b0053e04e6047403e803420304027801ec0194012200ca007200017ff4ac9a60530effb36a92329877fc9b549194c37fed5aa48ca617ff2ad5246530effaa4c4a329877fd81625194c3bfec0ab28ca61dff6052946530dffaa4c5232986ffd81629194c2ffead9148ca617ff62c5a46530bffa562d232987fed520a9194c2ffead8548ca617ff56c8206530bffb16a9032986ffdab548194c3bfea93120ca61dff16d8906530eff856c48329877fc82564194c3bfea92b20ca61dff22d5906530eff856ac8329877fc8b4a4194c3bfe2da520ca61bff5498a06530dffab6c5032986ffd2b628194c37fe412b40ca61bff5495a06530dffb16ad032986ffd2b568194c37fea92540ca61bff62d2a06530dffab6950329877fd52669810c3bfeadb048c861dff46d8246430effb56c12321877fd8b549190c3bfe8daa48c861dff6ad5246430effaa4c0a321877fd52629190c3bfec12b48c8617ff46c9a54d20f7fb049d302907bfd804e9814837fead274c0a41dff26d3a60520f7fb04853029077fd39429814837fead214c0a41bff4e90a60520dffa5485302906ffd3a66981483bfea9b34c0a417ff56c9a4c520bffa76c1300905ffd8b54d30483bfe8cb0498241bff569824c120dffa34c12609077fd1954930482ffe9daa4982417ff46d524c120bffab6c0a60905ffd2b60530483ffc85b0298241dff66d814c120dffb56c0a60905ffd8b4c530483ffcc130098241ffe605804c120fff262c0260906ffd53629304837fec131498241bff5498a4c120dffb02c5260906ffd3162930483bfec0b3498241bff6059a4c120dff916cd260907ff95354930483ffca9b0298241ffe609814c120fff2a4c0a60907ff95b60530483ffc9db0298241ffe4ad814c120fff336c0a60907ff9ab60530483ffca9aa298241ffe609514c120fff2a4a8a60907ff99b54530483 else 0x3ded3d953d573c7d3c253be73ba93b373ac53a6d3a1539a3394b38a5381937c13769371136b93613356d3515348933fd3357327d320b317f310d304d2fa72f692f112eb92e612e092d152ca32c312bbf2b4d2adb2a9d2a1129b92961290928b127d7274b26f3269b2629253524dd2451235d2305222b219f216120bb207d1ff11f4b1f0d1eb51e291deb1d931d211ce31c3d1b7d1b251a7f1a0d199b192918d1185f1785174716bb162f15a3153114bf143313c1136912f7129f1247120911b1113f10cd105b0fe90f770f1f0e5f0e210d950cef0c630ba30b170abf0a670a0f099d092b08d307f907a1072f06bd066505d9058104f5049d045f040703af032302e50259021b01dd0185011300d5007cfff0ff98ff5afe80fdf4fd9cfc74fc02fbaafb38fac6fa3af9c8f93cf8caf858f7ccf774f6e8f676f5eaf592f554f4e2f470f418f3c0f34ef2f6f26af1f8f1a0f148f10af030efbeef32eedaee82ee2aedd2ed7aed08ec96ec24ebb2eb40eaceea5cea04e9ace96ee82ce7a0e6ace63ae5c8e58ae518e472e3cce374e31ce2c4e252e1fae16ee0c8e070e018dfa6df68df10de84dddedcb6dc5edbecdb94db22dab0da72d9e6d95ad8b4d828d7b6d75ed6ecd67ad5eed57cd4f0d44ad3bed318d258d200d1a8d136d0c4d06cd014cf88cf16cebece66ce28cdd0cd78cd06cc94cc56cbfecba6cb34cadcca6aca12c9a0c962c8f0c898c826c7cec75cc6eac692c620c5c8c570c518c43ec37ec30cc2cec290c21ec1c6c16ec0fcc0a4bfcabf72bf34bef6be84be2cbdd4bd96bca2bc4abc0cbb80bb42baeaba78ba06b9aeb956b8feb8a6b868b7c2b71cb6c4b66cb62eb5f0b598b526b4ceb476b41eb3e0b388b2e2b2a4b218b1c0b182b12ab0ecb07aafeeaf96af58aee6aea8ae50adc4ad52acfaacbcac7eac40abceab0eaab6aa5ea9d2a97aa908a8caa83ea800a7c2a784a746a708a62ea5d6a54aa4a4a418a3c0a31aa2a8a236a1dea186a114a0a29fe29f8a9f189ec09e349dc29d509cde9c869c2e9bd69b4a9af29a9a9a5c9a049992993a98ae982297ca978c971a96dc966a95c4950494c6943a93ae932292ca927292009174911c90aa901e8fac8f3a8efc8e8a8de48d8c8d348cf68c1c8baa8b528b148abc8a7e8a4089e889aa896c892e88a2884a87f28780870e86b6862a85b8856084ee847c843e839882be826681f4819c814480d2807a80087f967f0a7eb27e5a7e027d907d047c927c207bc87ba47b4c7af47ab67a5e799e791278a0784877d67798772676ce7676761e75c6756e751674be7480742873d072f6729e7260722271e4712470e6707470366ff86fa06f486ef06e7e6e266dce6d5c6cd06c446bec6b946b566afe6a8c69b2695a69026890683867c6673a66c86670661865da658265446506642c63d4634862d66264)))) else (if i<13 then (if i<11 then (if i<10 then 0x2899c67c141702501640ae0400aca0ac0558080154023291080420201810408e021010100400210190c8840210100c8840a901000849d6a1d663d63fd601d5c3d537d4f9d487d3fbd389d331d2d9d281d229d1ebd193d121d0c9d071cfffcfdbcfb7cf5fcf21cee3cebfce9bce77cdebcdadcd6fcd17ccbfcc67cc0fcbd1cb93cb55cafdcad9cab5ca91ca6dca49ca25c999c941c8e9c8c5c8a1c87dc859c835c811c7d3c7afc78bc767c743c71fc6c7c689c631c5d9c581c50fc49dc45fc3edc37bc309c2b1c23fc21bc1c3c185c12dc087c015bfd7bf7fbf27beb5be43bdb7bd93bd21bcafbc3dbbcbbb8dbb4fbaf7ba9fba47ba09b97db93fb91bb8f7b8d3b861b7efb7cbb773b71bb68fb66bb613b587b4e1b489b465b3f3b381b35db339b315b2f1b2cdb241b1cfb1abb187b115b0f1b04bb027afb5af91af6daefbaea3ae31ae0dade9adc5ada1ad49acd7ac99ac5babe9ab77ab1faae1aaa3aa65aa27a9cfa991a91fa8e1a8bda87fa85ba837a813a7efa7cba7a7a71ba6f7a685a62da609a5e5a573a54fa4dda49fa47ba457a419a3c1a369a345a307a2c9a257a233a1dba169a111a0b9a061a0239fcb9f739f4f9f459f079ee39e8b9e679e299db79d119ced9c7b9c579c339c0f9beb9bc79b3b9ae39a719a4d99c19969991198d3987b982397b19773971b96dd969f966195ef95b1950b94b3940d93b59377933992fb92bd927f9241920391ab913990fb908990178fd98f678f0f8ed18e798e3b8e178df38d818d298ceb8cad8c558c178bd98b9b8b5d8b398ae18a898a4b89d9899b8977890588c7888988658841880387c587a1877d8759873586f7869f862d860985e5858d8535851184b9844783d5836382f182b38275820381df816d811580d780657ff37fb57f437f057ec77e897e4b7e0d7dcf7d917d537d157cd77c7f7c417c037b917b397ae17a6f79fd79a5793378db7883784577ed77af775776ff76a776697611759f752d74bb744973f1737f730d72b5725d71d1714570ed70af703d6fe56f736f016e8f6e1d6df96dd56db16d8d6d696d456d216ce36cbf6c816c296bd16b936b6f6b316af36acf6aab6a6d6a1569f169b3694168b56843680567e167a36765672766e966ab666d662f65a3653164bf644d63f563b76379633b62fd62bf629b62776239621561f161b3615b60e96077601f5fc75f6f5f315f0d5ecf5e915e535e495e3f5de75d755d035c915c535bfb5b555b315b0d5ae95ac55aa15a4959f159b3595b58e95877579d574556d3566155ef557d550b5499538b52cb528d51e7512750674fc14f4f4ef74e034d0f4c834bc34b514af94abb4a634a0b49b34975491d48c54887482f47d74799472746e946ab460545ad453b44fd44bf443343a7436942f742b9424741ef417d40bd4065400d3fb53ec13e833e2b else 0x8204080946025028080a00251016008805d010805418805504000e9206d021813404a4047010c1020252604c11a0c406403040aa04338134135813c0a010c0ca690d81a806206f05b8190d4133198188c2c0b70121889a08230a819416e580941ca82802101282dcc21721d504c170064291340c461505b8084bc00052031c18c0c5062010cfc0c41d30501640b105b99826017058b05016e064301880d003d30b82dca63003100f40a00b230b8144e05004281880d061701e82dce06a04781a00c80b72f0500a802b012c85c16204d3c8c01872178268094164602a030805c02590b82c409a7010817404a04d05f9641323090d808642e0258288301123003100f40a00b290b8144f21b041830404b2178288300e02105f014004a4904809642e0b10329417c0250280c082069006485c04a503b02fcc2e44d01294c2e0510128f81b80004002cb018065302f817a04d01700f40fa6038e0301658000321409a02105e0c05a0bb03e8c0ba07d101f40ba0ba181740fa2c06503d81b8000321681c03dc00303f0180b20329c12007ec06703700003d0329f000080013e0300ca0b83018c02b80cc0002c81706c0601ac02c064c00010c0ca701101b8404d01880f404e401101b840160318088056402e827040b903882dc0584015f023028c090589781081405882e016e581201ec0f402105b01b8c42b034e027811414205b028162801281d0401603582001620652d0080ce0aa826e0040480b53e01b003800058811cb80603302ab001801032811ce04a2210080780701001fc168044c0e9a804067e01e0040485c03600680981d05882ccd80603ee007000c0205982c4ec0203e8117002065c0e82c4f806021819b00381d05882cce020a0182030000442d0080cfc030326004048604060068098000588194c04303360000c98010329980807cc008090807dc00e0018040650589980407f04b600300207d0589f8060b10326004048504060058098000588194c07dc00300b002064032980fa020c000193002065330080ce04303260040486601700f002064c0002c4c066c0081930000430329a80406ae01e0040485021e01b003004c0002c40ca760101f412d801032e0001627c03010c0cd80003160040ca7c03600180780103282c4d80603ee007000c0203282c4ec0202181a80c9801012180c6015c0082cb0000b13005b002064c00010c0ca681081fc041403c000110c043010e01b002020c0002c40ca8c0301f70038006010194162760101fc12d800c0081f41627c03700f00380060102c4dc03c00b00b0000b12e0180d4066c00e00008606538104042020221100824420328084040505801480b60a62014808602201d900a402225780ec80520218088076401380880a43029010c04403b202b415c0550280144b81305681780aa0430) else (if i<12 then 0x1a80fc06c06900940a0803802000ca3014814005c0b82034d8140b81f02805c0b81825c04a05005c100de02505b8c05602101882dc805002180c416e4a08602c05605005b940de02505b8c05202e05b8c04002e05b8c12e05001002dc806b02801880d20b22823d8120b105c1012cc0a03702dc809760482dc60b20810d8100691f022812069181b80d2203170200d2304801880de0d205b8190062760401a408603105c158140b701882e08c0803702dc6c0a01881b816e4034818c5804a01c3460484012010c0f83018d000162303e00901623e0302c40ca301901f416230330194162300002c40ca30218194403c03e82c4605da0081947806068033c162065022009009a801002d8162305a833840b4059880860b3160180400b40588194088024381f41622e0180900fa0b1201f4162202182cc40448108190607d02201906043c000190602403281100c84e018090162303201f4162320182581000b12601904806560102c4ac02c0001fc12c0b1280f00860651e0000860641810c0ca203e81100c8301e0110164064203101620b20328190173801c002204204303e0c12c0800588c10b4030108190800181081906c0304b010c0c846010091078043032158060960218190803c03f02c460000218190607d058880c807d0588c0fa0b11010c0ca2a0102c41880652118193003800440c80fa0801f00e04204303e8200a024032e0040c84042d00c042064220c81000651810c0ca26010091078043032158060960218190883c021819c6096021818c780703501f804180003f8140089804480f00860651810c0ca2c0300800780620328110048703ee0001623e018090162303ee0001623c000194162360181f41623c030140088062c0002c8c07d0588904207c03e82c4802001920841640b12c12011c0620219180407d0588d80407d0588c0fa0b11010c0ca201183300400b1220f00480430589180683204b010c162560120f00860b12300c0c609602182c4a03c02182c4609a02182c46c0304b010c0c8441e010c0ce304b010c0c63022010c0ca302181944841424411019a021047010ce03cc03010f0000620328110e07d0588b80682103e82c49c0301900810420b12b0080fa0b1181f416220218194482106600801624c0320c807cc03010810ccc0241e010c1624601a0c812c043058950780430338d064096021819c803f00a81a80420322c85007d20103200f0ac1260002c807ac1705c02c4f81203e832f00181740f8324180805f605c1700cac0003001927c0902c702f80005900ecc06202d80f302f80005900ece052013880440320218f02e062035e0000860653008b0000b1c0b82c81706c0b81970000b205c170000b1c0b82c81705c09600007b81760c02e0164704f605f000c1905902e0c06b035005b02f8000218194e else 0xf1042064202c8170201e81904c0f05900f40c84e0681f4100303e80f41003607408807a0642008a0420641825981c06ba07818f0198000332381a03d0328c0860651010c0c8260701f407a0642303c04e064180f20420641809c0c82c06600012006b03f8094100050c06a40780430328c086065101ac0a180cc0002c8a0b205c090420430590d81c02702182e08c0f03e809c170401e010c1703039809c1703607809c0c83013810c17030138190406b036008406409703a1885406d03200c404a0b6300958140b11b0240dc0b218094164201282c8402701281b87401a0002d807a401380940dc301380940dc301882d807a3013819040d20128140740860482780560b20321b0140b11300580007b04f00f4b02ba04809c6c080588804ec090328c13c0b11019c0d1809815100ce071031815e054502b80a8170301502e0409c02e815c170404e02e0409c0148190705403583580640742835406404303e900e607d0590c0dc0b71009416428050190408201e009c0a0440b913417007fc00502c0c870380094170305b809c170380801900a140805b9701202205b8e81102601102dc80b70320a81008001e01d00d2504002dc406e0348807a0b71009c0c8205b81905811041013702806560482c7000801581f41623809405016202b05b9602008203200af0160b73404b81082ba0482dcb80101002dc781242681880fa03c05b9902403a01382dc802260480f416e440a00c816e3c0a00f416e3c0a0193016c082605181180ba051005606760481a404b814a051c0fe0270588c92a07f01382c4849503f82c4607101282df01740a281c807407105b9002401405c02dc981401582c416e4039019c16e340a00e816e3010e05016e380a12540560b105b9407406705b8d02803a05b8f0280b7160300740b7182d80d8021037100ca02b05c0c857c08c0480ac16e520000e80e202b05b9501602905b8d8160b7102d80d802103a100c80b2102d80d8021032100d209e035602416cc08302401a4070c0482c40de0b6382c40ca205b01b00420222159701207301880a41705a0a02e4062c0b05c1405803105c0c12c03105c0c82802902682e0941403183500420b8280881700b7181e805803105b9301207d026d00016e504c02040520b72019009a02905b900dc0b7101f405804d05b92828c0a05c60240e140b340300420b7181b809a0b71b02c16e2605302c1a40b205c02dc0c80b94302809a06e05b918160b805b8c100069101918160b71d0280c820348190408060401a46c0a032080c8069101a40c8201582c80e209505b9501402b05c0f01602c0348c0e807160502dc807460501b80d2460481b80d23604809413c02c0349580007104a82dc8c0801481a46c0ae0400a40d2403101980c8069201b80f82034827b01607e0283020c0900358)) else (if i<15 then (if i<14 then 0x70059148420b71014182807003402c4a03d05b88c2e0b715050c2e0b71814416206c059100d00b7100c404a064181880d2055d19e858ba36012819060800128a4100b9919c8580aa03105b8195123610b81f80740b828b6807a0641c82246d03205c01a80fe06c90b020004a0505814004203d0589013405d05b8c07406402a82e0923381d019004a401d015410007d05c141640500410094861503e818c0420b7282080ca06905890c2a03122682c49a1520a01f80aa43a2819416e0b11c0e882807e01082dcb07202a808416e4850105018805d058958010140588c8280b8112960280b70321094a0b105c0094809630b02dc6a1505b81907a16010818816e4032017416e390b2854c2a07d058940740b160a02dc803a05b82c4603d01082dc606301288c2c06c30a81881a40250188191006601880f40c8420a00c404a06321d150280630588d42e03d05b8c0c408105b8c0cc0640328c0fa02105b8c1a402e02682c4805001e11341624d04a0301620b8220300c407f0129010209805902c4805040602c81624c06014404a0b2260301700251e0301640b1181541622e0a482643721603481fc0f805005cc85c0aa0b16305007409090b82e0b21b90b834a42c069048009405c0b14820400007d0589010200c01e82dc80250590804804d01283648c14034015409b21706c1805605501e81340e40d83008404a0541813417e0b1180f417e0b1182040a003d0601007a0550600e4120550390144170591800f81040550108144c08202a8300603d02a830064d70408140180402a82c4460a0410194720910a83480e40b82c8540a008503601881646e0a48264380b804801a80d807f90b80940a0b03e80f0162301e00f40aa0b7202141040651d0500fe0250589082806890b82e0807205c080740500340094162580a034805c0250589407409002a80f242e0b8301540e607f90b82e0a03a021809416e404b009416e330b80e804a0b7202080c806205b9342d21750a818816e530b908404a0b72285cc2f01401e82dca63330b809c0fc03a0129b02806203180e816e503b00e804e09030b8094c61503b00e81640d230b8094ec0c01082dc603a01082dc6c0c0288094164460001f40780b12010c1020b7180c404a0641810c0fa06301e02dca07e018b00016e403982e016e3e0681f4100304001945c0da060194608fa06019460630398194170403581f8018065201f01702a0002c8170301e02c80ca303981c40c80652703407a065181c7019800059130000b80590f02003c03e0194803d0590981e03d03e82c8802003e82c8602202180b4164401101f40863a06825807a0b22600008602d0591000003d0590f0000228108190980081081906027c0001906027c000190607103f025807940ec060197000803e01fa81b800c0602580ca7c000 else 0x17010c17040218194441901101c41624c0001401703c0000f00860b8202c816381703281c4189800381f702e0b81e0001640b8180880e20b11e04816207106201940f80b9c0be0012025059080440710588c04e0b8130640a00b818140170205901c70000b104f01cc04f817430640a00b81810c0ca202182e04c19013810c170460d00f40860b8200f00860b8180b80860b81b06404e04305c1007a0430378c1640b8012814011c082302c81704dc0470208a082519809460c802802e0602e81d02e0602e01282c8608e01080f00740800129a14a8a080a03101620b8302141700c01823410403a0480094a08d01e00f40fe0252e04f02808d0620154086685002340ca09001902901300254036c10207d0589013008103602c8162502e80f004a0502685411c07e01101748640253829011c05d0114084086601e82dc402101702dc602ea0602dc740c05b8190740c05b81907413c0902598280b105b81f00c8066481740cc0310321004207e01882dc8c1401281740c840591854104025200f404205d05b9016e064102c81700800470208a06402e82c4600c03202c4602401e82c4606250b819066dea4518540c407f034820089a850ba084c2a40c058940c940c0588e8180210588c07a04d01082dc8a1b36e985416407f04001880d20824b8581000b7192810e40694109134a8174000238104021319d05016e0644b04d8180b11c08501880022682c80c40b7a0a2087408e20a020004a5a0a02dc40b2032605cc2c0b805b980e40b71105010002102a82dca21c04700940794140321a8280b1102c642e064182380aa0b120a010ca0b7032088280b105c0cc2a44d04002dc8c0c05b8ac2d21783958cc0c5021302240e4633031185804a021381900420b1198cc82807203100848746b0b10301000b7212948280b703212818c0c30a82dc8021038019060b1800022416e404480900c406802a985416e02141134162220a018811202105b9681861540002dc0c85b0b113481808005b9681841460602dc8a1721d01cc0c84a06303082806405b941620b940002dc981702e82dc781701e817416e4010819016e301f023816e381082dc540c01702dc6073028503016e4a0601cc04a0b7200ba81802105b9007a02102e82dc802160a009416e404080941643e0a0370170062034c8cc104705882e050a004810300a20b1282041880db0380154162604102c80c4a3305b9742c40c200485d42a06205b9e81883a058b05016e503202c416e330b908416e301e818816e301e91341b20b12020816403d0601081803d05b8c164064028026a82741405b8195007003402c46c13042d00016e4012019007a0b1200b90740b21834c0c80b205882dca01703202c4640003102581640b72808407a0b71985c16e230b908416e301e985c16e30288214162) else (if i<16 then 0xce07f01e00ac80650138804ec09100ac0c405004f101621a0440c807a0712019c0dc063180ca814260400a80d60572502808609c0389013807e1601c08609c038900fc06e101f81382031810c402a021880fc06e101fa052203581b8407e04e080fc06e1010f00e240801b00e8306901d04021c0408134022c0401b08c0104d02dc60692158194605403480800fe405b819413406f250040d809a1e04b01402703611024058c050c0f40200350c0fc074100ac0fc0271809f0002012809c0d2301201b00dc381201b00dc303601b85812c0481a4609601101b3012401002dc0de096200ac0d205d03f9089a06901001fc80b80385004603205b81bc12c403600800de096201c004a0b8182dc04e0b81e006024022a0401a4b81241100ac04e0692e02c04a06c1820b016205c01fc0ba0802020804e0d2180ac0d207f0139005606903f809c901080a01100d2403a009c1640692602c3814081b8203d08200380b0809c20b1c0a0811c1c0a02c4406e03660506495036013860d203a0b012103601b840640360b0121013840d242b110ac0d207f1e02420240358912a02b03c81b08071a0420ac8560692a0880e202b0349016c0d2101d020b6035080d406e101b00dc205882d840b1215880d242b101a48562a0a10ca81084d038940f603103201c4940821581500d2403d00c40c806c2302c856069181d00fc206912544076069080fc06e101b80fc20148404e103a602c405008348206b036880580b20360e81402703a01b0940924a81d00d8403a00940d83016009c0d8301281f40d8302801f8406e081401a4202803484050069080005911100d63a0802c80a00692010c0e002e0379086407001701bc80250360892a0250360c1c00cf03202c8065024302c820b1082c420b1082c420b10620200780402801fc604303f8a0900200310dc2ae0c21088c8806a06940860644d008a804a80b6036025804424d4018c0ba0b71829c19804305b9214e04306602dc82440170330086404800830000b7260001200b105b9300006605882dc921601202001a402090082c816e0210332a42c24d03381f00cd2010109c1980b2148520480b190081fe042690a80f812007e010023c16e790a80f80fc066047819c16e790a01740d007f900c084c0b701e009c0ca4010009c0ca3906009011e0cc03548040f8020010a641802403300f00d520104f0080042901e01880d12018109642902401701880ff2018109c0cc08f02182c4803c03e82c460430588807ac000590c164c000588c0414000590c07a0b2170481640b118000162065180941642011009416430105000164303e8300405201e81f41804021832440650600b0240b1032e05f0010323037e1960c0192be0b40430649007a0b1100941642c09002c0cac190589405606803f8088162523002c458 else (if i<17 then 0xb8036025880b821d01a0603a03780b80d0405c0642e0550360c05c024101b00d043a1822414804303600840c8603600f00a0080200300482c0001a8172305c10e8120304481b0040080201c012c4320319182803a05c00940e0590b84dc208050b8174843a04102c80c8450b81880c80682304c04044d05890170068101900d0250b82e00d0305c285c0d0360601900d0304001c8407205b80800c80b128189818205b8416e105b858180690401134806401081c005c405b840c90210310c0d20806060f02f40c03210e80e0505b8600005005b8c89a080010b0300d2560a485c17005504b01c0c069041019460b2082040c40550349016341405c02dc80b8080e820b1082c420b10820816406230b81a4a06890b81b1074405b84162104101880aa069202c43414059014010a0b103218162105882e010a064202c420b1081b005c06841d1010a0b10380c0a20b205882dc80b2082c820b8082e0206303601cc606402e818807a40320094405002a8811c0b902a81a8920802a82dc170416d0094100302e80f4405003f0804a07e101f807a203481fcc2a303511344c0050ac0e80ce405c10e840b808154042205b8416e105b8416e105b8416e110e023816208001294162100a02e00c80b1202c40aa0b7182e020b80c85c0c883a0381016e10310208164069201c0874205b84162102a81f4405503e81b06031035018c6063081f40c620109854521541d10e80d840588580007d0350ec6c03a03802e0807d036018c605503e81b060b803610e860630360810407f0400d82803a0380c16210018c0d82031840aa07d0360c16e103181b04881031019489a4a0a41450180b105c0094c0b8098280fe04d01290170105c04170105c04170104101880ca05502a140d005d02a0c0a20b805b82c480b20e0310a20c405c0094a04d0690094602e0310150780c440881720550310c04a09021d0e41205505b82e0806c01e880aa03d0360c12005010094120203600f440b203981400c4403f81544c1490a80e80aa0b205c18c1407f0128c07c0b203282680a006c302080aa062181400fe202801fc402503f880a007f101fc0aa2041605040b80280817007f0400cc2e0620400208806c2108a02806205901a4806c01080940fc403620e8408203100940d2403100940d2303181b0580e022018c605003e8816410590700042d01e818c803d03301c460660388807a063110b407a06318140100201381ac4022035880d006e102d82c0a03701a8602501e81a860320370a80006b01281a8806b037080e61a0081a804a06c201b00dc2012b0044025081cc20256050804ac09102c820b1080882c0a081a80dc260001a8064360930040d580a260282027082540560651819d81007f1d02420b101280ac606503480f00564036013404e07f201b009a02703f90 else 0x60c21088c8624d058881721034820040960110a402a0c30a81a410050111858406b01088c80e0403801ac0422320319504206912682008232034018c607d04b018c607d04b01a4609612681a460690400849a0960400c48807003e825898000380258606241081fc7800066023c0e0405b84198103180800e0381081fc40700318810010318416e190a485a04903206616042068140840d0281082dc0fa305b81fe042305b81fe042305b81fe0423031408450210310a042062101c418807c182c420b1082c420b1082c420b10e0001620c401381c4a0b106201c460b101381c46c14082e020b8082e020c4082e020b881d08170105c04170105c04164105c009416230170090521702a81b0606481201b0606403601cc606a03980940d8481081a804a06920189042204b60000c4025202e00aa09605b900d4)))))
def q238:Packing:=(1181,4,9,0,0,16,0,q250)
def q244 (i:Nat):Nat:=(if i<1 then 0x6db71b00004d4ccc27ba094000018a4d0012000000000000342baa2920013f86ae03446022c756c84080142843384b57020903720000b0a93020fc2ab6fb8228b883670383a1cd70ac101c94190810d3047e0683060021605001a82bfc2b6416ae040e368e82f320aee0d69021b85bd46bc000060607c03068b9d0a5203f0cfc682b1b08288750a651006bc02330732c2b5698210065bef3c1e0e0dd0030d26fd8f55c03a50d2805f800008076c0d4e80740001809947cf8000000000000000020070429ba110607cb8172c2d8a00bd0aa184440201045600001a600000000002036800019c942fd100006be8900468986c03624a240000000080d9800000001c502f04dd058cd2f400000000000000000c1467754803b8033195b110e9a4c680001f173000000002c211801e0000000010892a39cb669b801b83a546460000000008342e0ef0029787600001a0d300003a701c3868f26a422800010209c708309bd8b70db3a4969700d80001800060a5909f232d1cc8ea19d00000000000000000a0ba00000023c251e0000000000000a0e1000058362839e00000000000019b88c97c4049e0b6f511fa10cf072c071080fe009ea0d40000181688970000048034014f54a3d019682de8316000010cd0a32ec336611d40c7d233680808979f0bac0356012e000000000c69c0000e1e5f05b0000000000000908d0000000000000905e50a528152000000000a72180200000c0b780002c0bc000000001d0f7411309b50000000000000000003d5800000000850830424009a81c0d3163092fbe86026a896250b9784f281b5a85a40d5236a1417a28bf328c182ec43c4041f64dc684e9019d402f001803c850f60c10efb847071c433c81610000183ec00000000106e0000000000109000000000000000000000204ed41c8e098000000000000000000000402778249b25600402c000000040000000300a00401004000030008000000040000200000803001006000000020000000000000003c0b80201c0080280102a008018010020000300e00000002800000048038030020040100200e000018000020040280000001001000008000018010220000d806000000000010080240001600601000004006028018000080000000a0040040100d0020180000000a0000100f0020000001e0040040100100c00000800016004000040000000680600000c0000000200c00800006000008060080200000e000000010060040040e80700401000000016028018090000000200401a0040000000000001000000010000000000040180000000c04000014004000010000000000a0040200680001c004000050000140180200000c000010080000100100a07c0700000a00c0e800000054008020000040000f000000050000060000000000202c0100d00000c02809 else (if i<2 then 0x6885400000e136c076e072400002128c0b40000000000000235f00002825d81b2f07c000000001e11c000000000018e01290000681bf0043216d6008c05f4000101d90000682c800006fbf00001250482f80000f03c437180000208e00000000101e6000020bb23a24e34c0000f05c6a6a400018194f4c1f8405ae4800006025a140c00000000003f33377c2e6c09af98e205b800000000005f29494000160a4824e80003837960d6a0c9f02e702178143e093a0716831a6f98e0bb8819bc83840e93066800016767a171000050720000000001956800024273810fd0652824a02670059f0b5e46300001a06e000000000000140f26b99f01a800006f97000000003c1e8603c3098c45c000000000b0e5ab5be42300000000000000000000000000000000000a134000000001404a00000000100080000000000002803c0000000070c1801894c77658e000003b5800000000f0198000193320000d214483b000000000000000000000080dec29100000000028a100002822000000000000000001c0ba82b200004861182ce0000000000000000062ae2220c81d40000a164000000001c13e615128ca380ee0158000000001801c000140fa24a119ee400010868a0b8000000001d2b8000048280c319212f393750112c836b51300006ae300587e130e28d8000387c6000000005070800000000d090905a580f4000074d58000001e3c199c02508499c20ce9a8e014b01e5cd74ea4d020f0246a883bc1a7f05d384afc14c64fa000048700028b8103e0c7402ce0255407d708fd845cc1a4725590a108090807da7b20000183fc000000006062403080001a0bf50689b8ec00000000000000000000161df00005014e00bfe1ca40eb0a5f8c160000040e3000001182000009579949301a000000757800039967e058f45690e2181bea05656e380001432200000000180d0000001de24c080000c2ae00000000723280001015c90dfd06d40000000070329832c0001ce6b00003a6dc00000000000000000000060d7000053b06806e019f00007b67800000000004b3b62fd8080000000000001809a0000c0afa83040000e2e80000000000000000000001845180a84f1e264fb148f81fb00eab32473d180000c01760ca8053000000000000000000805c0000000000002c0980000b18e800000000000000000000000000edda00400002863e000010c51245a5e520000f2170000282cbc4420000504480035605a30df68e6800000000701ae80d801a8666e0000181d04240e0ad00001053ec374c3ba6071b84b00001c063000000002c7368080000030780000161b6a014652640147accc809c283a399b54050504e00001c28e4001e0b14235c5fc3204800630000242f58122f0661044c000000000000581ec04080000e45a9b7380001450f0000726b188 else 0x4362a5770005000000000000090a000000c0d0000000000000000000000000000000000000000000000000000000050c4400c702cce0f6000000000000000000000000012159814800006427a81b780914a4e4a10c000101d550f24010766330fb2b002106d140f8000000002d27800000000000040455802a0000000013c68000181e1709900000c1160149e45d8054c807e0000406288741c155a29fa01ce804c0000a18543222019d9112a08a00000000083c669675293482ac000000b500000000380ee0000b0dda227d83a328b880648813f011b8012e4bb20558c32f496b97d0106e005bae049e046386c1432ce0b10000385e0c040a1bdd032000030b63e02dc01c126ba435961cea091d111712f700e640274245681214d8670af00000c3246187a4da196bf19a400006645e10b4c304000090c8705ff420e000000003493201ef2119011d80002052a843bab8480003882961dc106054ed0000041ae0000134880000000000005856400000000807a80000000000001284fd4251f6669680000786998f5b0051964f70670ca3281a3a49f40428000000000000000000000402b0000180f40001802a000000000000000000000706bcd15e000000004810d830c629880ebe8691c2f7e42c407f490ab01ce000062898000280e24070f4bfca27580c00000c1cb580b0000021b70000183ac00002432b0a5800000000000080ee80003408a0000000052453c88c000000000000000000042b14be816d80e6051584477050641440869d02ae833d90e800003b4f9076fc29c0000000000000803e4016b0715015c012b611600004811f427e853080c4a001711800000e2f2a21279313c1440000387694a4ea11b00000000141500000d0429830fc03282e970c0300521154c978d034c269e95400000c00700003885e8431000000002810e0000909))
def q251 (i:Nat):Nat:=(if i<3 then (if i<1 then 0xa6fd9c5496a0e520e6ec9c5496a0e520ee6d525456a0e520aeed2c5456a0e520e6ed526256a0e520e67d515656a0e520a6fd8c5656a0e520aeed2c16d6a0e520e76c9c5495a0e520af6d2c5455a0e520e76d526255a0e52087fd9c62d5a0e520ef65525451a0e520afe52c5451a0e520e3f5816251a0e520e775515651a0e520cf6d5256d1a0e52087fd9c56d1a0e520cfe95242d1a0e520cff15142d1a0e520ff49535493046520a5fd7c0e58a46520a6fd6c1653a46520a7bd4c1653a4652087fd1c2ad5362420b3f51c54d8162420a3fcac54d816242093fd5c4ed8162420e75d535693a62420d1fd815ec3a62420d37d8156c3a62420d3bd8152c3a62420d3f58146c3a62420d3f58c46c3a62420a5fd7c0e91a62420a77d5c0e91a62420a7bd4c0e91a62420b7d51c54d814e420a7f51c54d8a46420a7f51c0ed8a4642087fd8c56d3a464208ff90c2ad536091087fd9c2ad5360910c77d5356c9a60910c7dd534ec9a6091087fd5c4ec9a6091087fdac26d835491087fd8c4ec9a54910fbc582605314c91087fd8c56c9a4c910fbd1814c5804c110ff49535493048110ff498354d5248110ff61835495148110ff613c5495148110ff61526ad5148110ff61522ad5148110bfb14c2ad5148110ff61525458a48110ff612c5455a48110ef71516295a48110ff61525453a48110ff6152545204e51087fd5c2ad824e510a7ecac609524e51087fcac62d524e51087fcac62d204e510a7f8ac62d204e51087fdac56d304a51087fd8c56d3a4a51087fd9c2ad536081095fcbc54d825e410f56d53609525e410d5ed824ed525e41095fd8c4ed525e410c5fcac4ed525e41097bcbc54d8252410f72d536095252410d73d5362d5252410d7ad824ed525241097bd8c4ed525241097dcbc54d824e410f74d53609524e410d75d5362d524e410d7cd824ed524e41097dd8c4ed524e410e3dd536098a4e410e3ed825498a4e410f3cd825498a4e41097dcbc6095a4e410f74d825495a4e410b75d8c5495a4e410e3dd826295a4e410e75d526295a4e410d7cd8256d2a4e41097dd8c56d2a4e41097ecbc54d824a410d76d5362d524a41097ed8c4ed524a410e76d535498a4a410a7ed3c5498a4a410a5fd7c0ed8a4a410a77d5c0ed8a4a410a7bd4c0ed8a4a410a7f51c0ed8a4a410a7f90c0ed8a4a410e76d536095a4a410c7ed8256d3a4a41087fd8c56d3a4a41097ecbc54d8a4a410b5ed7c0ed8a4a410b76d5c0ed8a4a410b7ad4c0ed8a4a410b7e51c0ed8a4a410b7e90c0ed8a4a410e76d536295a4a410d76d5362d5a4a410c7ed8a56d3a4a41097ed8c56d3a4a410d3ed5c62c3a4a41097ed8c56c3a4a410d76d8c56c3a4a410c4fd7b5ac9a4c520f3d1814c530625208decbc5497a0e520ad6d5c0ad7a0e520ade51c0ad7a0e52087f51c2ad5362420 else (if i<2 then 0x97fcbc54d8a4a510a7fcbc6153a4a51097fd9c2ad5360810c7fd9c2ad5360810b7bcbc54d8252410d7ecbc54d824a410b7ecbc54d824a41097fcbc54d8a4a410a7fd8c0ed5a4a410d7ecac62d534a410d7ed8b2ad534a410b7ed8c2ad534a410d7ecbc54d8a4a410b7ecbc54d8a4a410b7ed5c0ed8a4a410b7ed8c0ed5a4a410b7ed8c54d3a4a410e7ed536293a4a410d7ed5362d3a4a41087fd5c4ac9a60530cf5d524ed5a06530c7dd894ed5a06530f2ed82549815a43096fd5c4ad815a430c6fcac4ad815a430c6fd522ad815a430d2fd5262c1a5a430d67d5256c1a5a430d67d2c56c1a5a430d6bd5252c1a5a430d6ed524ac1a5a43096fd5c4ac1a5a430d6ed5c4ac1a5a430f3e582549814643097f55c4ad8146430e3ed825498a46430e3f5826055a46430e775526055a4643087fd8c56d2a46430c6fd9a5ac9a54d2087fd3c46c9a54d2097f51c26d536052087fdac26d536052087fd5c4ec9a60520c6fd9a5ac9a4c520c5fd7b56c9a4c520c6fd6b56c9a4c52087fd3c56c9a4c520e7d9300ed9a60120a7f90c0ed9a6012096fd6c26d534c12096fd6c26d314c1209ef96c26d534c120bed96c26d534c120bf595c0ed824c120bf994c0ed824c120bfd11c0ed824c120ff489c54d524c120ff49536ad524c120ff49532ad524c120b3f99c609814c120ff4953549814c120dfc92b54d514c1209ef96c26d514c1209fd93c26d514c120d7d95326d514c120d7f18126d514c12097f98c26d514c120d6f96c26d514c120d7b94c26d514c120d7d93c26d514c120ff4953549314c1209df97c26d314c1209ef96c26d314c120ffc152605314c120bed96c26d314c120dfc9314ac5a4c1209fd93c46c5a4c1209fe92c46c5a4c12097f89c46c5a4c120ff49535491a4c120afe92c1691a4c120ff49535489a4c120d3f58126d316252095fd7c26d3162520afd8ac54d3062520ff49535493062520fbd1814c53062520afd8ac4c5306252087fcac56d316252095fd7c2ad316252087fd5c2ad3162520a7dcac4c53062520f3e9526053062520a7f8ac5453062520f3f1814c53062520f7c9524c53062520f7d1814c53062520b7d95c4c53062520b7d8ac4c53062520b3f98c16d3062520b7e92c16d3062520a7f8ac46d3062520f3d9814c03a62520d6ed525ac3a62520d3f58146c3a62520d7d93046c3a62520d3f98142c3a62520a5fd7c0e91a62520a7f90c0e91a6252087fd9c56d3a22520efd1314c11a2252096fd6c26d534e52096fd6c26d514e52095fd7c26d314e52096fd6c26d314e520b5dd7c26d314e520b6dd6c26d314e520ff4953549304e520f3d5814c5894e520d7d53146c894e520ed6d525457a0e520aded2c5457a0e520e5ed526257a0e520e1fd816257a0e520e57d515657a0e520a5fd8c5657a0e520c5fcbc5657a0e520 else 0xefcd524c53a22520efe9524c13a22520efe9524c11a22520eff1514c11a22520cfed524ed1a2252097fd8c26d534e52097fd5c26d814e520ff6552605514e520d7f58126d514e52097fd8c26d514e520cff5812ad514e5208ffd8c2ad514e520d7f58126d314e52097fd8c26d314e52097fd5c26d314e520ffc552605314e520b7dd8c26d314e520b7dd5c26d314e520f7d5814c5894e520a7fcac544894e520d77d5156c894e520d7dd3156c894e520d7f55146c894e52097fd5c46c894e520f7d5814c5594e520a7fc9c6055a4e520a7fd1c2255a4e52097fdbc2245a4e520afedac22d520e52097fcbc545890e520a7fd9c5498a0e520ebed526058a0e520ef6d525458a0e520afed2c5458a0e520e3fd815658a0e520e77d515658a0e520c7fcbc5658a0e520eded526057a0e520e5fd516257a0e520e5fd815657a0e520e5fc8c5657a0e520eeed525456a0e520eeed526016a0e520aefd5c6016a0e520e6fd515656a0e520e6fd805656a0e520aefd0c16d6a0e520ef6d526055a0e520e77d516255a0e520efe5526051a0e520efe5525451a0e520e7f5516251a0e520e7f5815651a0e520e7f5515651a0e520cfed5262d1a0e520c7fd5962d1a0e520c7fd8956d1a0e520b6fd6c26d534652097fcbc54d894652097fd5c4ec894652097fd8c56c3946520a7fd5c2253a46520a7fd8c1653a46520c7fd9b2ad5360420a7fd9c2ad5360420d7dcbc54d814e420c7fcac56d814e420a7fcbc6055a4e42097fcbc54d8a46420a7fc9c5693a60910c7fd9a56c9a60910a7fd5c4689a60910a7fd5c4289a60910c7fd1a56c9a60910c7fd0a56c9a6091097fd1c56c9a6091097fd0c56c9a60910d7ed0b26d8254910d7ed8226d3a54910c7fd8a26d3a5491097fd8c26d3a54910f3ed82565814c910fbe582605514c910ffc51c609314c910ffc582545314c910f7cd82565314c9108ffd2c2ad5360110af7cac54d5260110b7dd2c26d534c1109fdcbc54d824c110f75c9c54d524c110ff4d53609524c110df5d5362d524c1109fdcbc609314c110ff5953549804c110ef5d535498a4c110c7fd5266d8a4c110ff690c54d52481109ff8bc54d8048110ff69535498048110ef6d535498a48110bef96c2ad5348110ff698c54d5248110ff699c54d5248110ff689c54d5248110ff68ac54d5248110bff13c2ad51481109ff8bc54d8a48110ff71835455a481108ffd5c2ad824e510afecac609524e510aff4ac609514e510ff6582549514e51097fd2c2ad854e51097fd5c2ad824e510b7ecac609524e51097fcac62d524e51097fd8c2ad524e510f3ed82549814e510f76d82549514e510b7f8ac615204e510a7fcac5498a4e510a7fcbc5498a4e510a7fcac6152a4e510c7fc9b6ad534a51097fcbc54d894a510c7fdab2ad534a51097fcbc54d804a510)) else (if i<5 then (if i<4 then 0xcc42e50a64215072417d04c40ad00a3f6cfc83e2cf783d5cf283c1cef43b14eb23a7ce7e3974e3c386cdfa3764db8365cd84358cd4234bcd0e33b4ccc32acc8a31a4c48309cc062f94b9a2de4b4a2ca4b082b9cac62a94a8429c4a42284c9f2270c9a22604960253494824648ea22ec89a21e485820a47fa1f647b81e5c7681d1c7261c146e41b0c6a21a0465218c461017bc5ce16b458c157453c146c4ec132c4aa11ec44c10743fc0f343ac0e2c34e0cb42fe0b3c2a009fc25008bc20e07b41cc06ac18a04fc0f4026c05e0084000c7fd9a4ac9a60530c7fc5c4ac9a60530c7fc9b6ad52465308ffd8c2ad524653097fcbc5498946530a7fdac2095906530e3fc8c5658a06530c7fcbc5658a06530a7fd5c4a58a06530c7fcbc4a58a06530af7d5c2095a065308ffdbc2095a06530af7d8c5495a06530e77d526255a06530c7fd2962d5a06530a7fd8c5652a06530c7fcbc5652a06530c7fd5962d2a06530c7fd8956d2a065308ffd8c56d2a06530c7fd9a46c9a54d2097fd5c26d3a605208ffd5c4ec9a60520c7fd9a56c9a4c5208ffd8c56c9a4c5208ffd3c56c9a4c520c7fd8b56c9a4c520a7fd8c56c9a4c520c7fd5a26d814c12097fd5c26d814c12097fd5c26d314c120a7fc9c4c58a4c120a7fd5c6059a4c120a7fcbc6059a4c120a7fd5c22d9a4c120a7fd1c22d9a4c120a7fd8c16d9a4c1209ff98c26d534c120bfd91c26d534c120bfd95c0ed824c120cff8bc469524c120bfe98c54d524c120f7e9892ad524c120bfe98c2ad524c120bfe91c2ad524c120ffc953549814c120b7f89c56d814c120dfe95226d814c1209ff95c26d814c120dfe92b54d514c120dfd92b54d514c120ff5953549514c120fbf182605514c120b7f98c26d514c120dff18126d514c1209ff98c26d514c120d7f95326d514c120d7f98226d514c120d7f95226d514c120d7f98c26d514c120d7f93c26d514c120ffc953549314c120ffe152605314c120dff18126d314c1209ff98c26d314c1209ff95c26d314c120bfd95c26d314c120bfe91c5488a4c120dfe95256c8a4c120dfe95246c8a4c1209ff95c46c8a4c120ffd1814c45a4c120dfd93162c5a4c120dfe9814ac5a4c120dff18146c5a4c1209ff98c46c5a4c120efe8ac5491a4c120efe9522291a4c120aff95c2291a4c120aff98c1691a4c120abfcac54d8162520d7f58126d316252097fd5c26d3162520cff5812ad31625208ffd5c2ad3162520ffd1814c53062520a7fcac56d316252097fcac56d316252097fd5c2ad3162520f3f5814c53062520f7d5814c53062520d5fd7b5443a62520a7fcac5443a62520d7f55146c3a6252097fd5c46c3a62520ffc9524c53022520bfe92c16d3022520aff9ac16d3022520dfe95246d3022520a7fd9c5493a22520ef6d525453a22520afed2c5453a22520 else 0xc4426810401580ca05b950f000ac403480fe0778c0250194405880ca280500ef1016e05c080b102dc440900ca202dc203380ca05b8c06500ac0b7181a40768807b01a403d181dc0768803d02dc4006016e2018c2000c902403a06010c1a20718f80602c40eb180cc0730802003b0401001d6201160d103887c0301620328c045019440330162200040ea1006501201d0302c40651012c0328806602c440000162201f0064100f80588806502c4401940480740c0b10194404b00ca20194064101000328806602c4400080fe200ca02403a0604b00ca200000671700c05880ca301980b1101d205908821038c0b1191ca0720162320840e302c4607181622e0180b10194600b01622000407f101c60190042074100e70398441081c60588c8e503900b11904207181623038c0b11700c05880ca30258065100cc0588800101fc501001c4201fc0e2100fe0710808d03100c102fc04329074038016205900c8500ac0d802c40b9014c0bf3004a02e809a05f90025017404d02fc801e80fa2f03fc0af017be4ef0fbb0ee77b98eddfb72ed7fb4cece7b18ebdfad6eb47ab0ea3fa6ee96fa3ae8679f8e75f9a8e5e7958e4df916e3d78c6e2978a0e1ff86ce12f82ae05f7e8df577c2def77aade5f776dd57726dc176f2db476a2d9cf652d8575f4d7875c0d67f57ed5af54ad4a74fad3674aad227468d157426d0173e4cf0f3b0ce3f36ecd6f33acc9f314cb5f2c4ca8f282c94f240c8471e2c6cf1a0c5ff150c3df0d6c29f094c23f07cc1a7048c09f014bfcefe0bf36facbe66f86bd96f52bcfef1ebbf6edcbb26ea8ba1ee58b8dee24b846dfeb7aedd8b716da4b646d7eb5aed66b54ed40b47ece2b2ceca0b1fec5eb166c1cafb6bccaee6ba6ae16b64ad46b3eacaeb0aabdeabaaa9ea94aa06a6ea936a2ca7f69dca6ee99aa5e6958a4de924a4468fea3e68f4a3868cea2ee8b6a2c689ea22e86aa126836a08e8109ff67ea9f5e7c49ec679e9df676a9d5e7369c8e7109bf66ea9b266a89a1e67498de616980e5f097ae5d8974e5c096ee58c961e566958654094ee5289456510942e4f893964c492c64ac929e4a2927648a9216456910e43e90ae41890163f28f7e3cc8eae3a68e4e3808db635a8ce63188bde2d68b0e2a28a0626088fe21e87f61dc86ee19a85e615884a6108839e0c682ce09281c605080be0007f7dfbe7e75f7c7d6df2c7bf5edc7aede9a79ade3c7835dd07685d72750dcea7325c9a71e5c046f8dbb46e4db566cd5b066b95aa86a1da5868dd9fa66f599c662595a64e590a636d8ba626586a612581a5f3d7ae5e357185bdd6d65ad5694595d636581d5e65715596560d570553d52e54354ec52f549c5225476515544250854004f7d3b04e053604cfd31e4bf52ce4ab528c49ad24a48a5208479d1c6465d17645551344485100437d) else (if i<6 then 0x6201b0203e02077840ef02c8403400ba200942840840ef08162032880b20c82805880ca012900ef0816210094201e040b8009440620170203bc0b80194605c00a020140051100a006908050034840690062201f8031100c6103b42076840003d0207686c0a080160506c0a081a4039880d201cc4013840ed081da103b42038840b20807a1028020388402201b0408284022080de01088082080d21025820108406501a440348078203480b910162104100f4040c069200ca03488069081da1000561001da10020807681623001a401108005b00d62001dc170282003810101c4203d80e2202d8200001a0404026402060348f4080800e8081c6103a02071840e8081d0100b80621000e2081c41038c2074040e30194406200c4201a80201700c03289c030810a0328b2140194404000fa2e0480c0101be081080df040040808180203240c01010a06488101030040808162200c80270300604d0180203240c01013c0588b8000f0240588807102c8403880ca2005c07f101700800064300f00641002c05c0805002e0401000ca203fc0fc1011a04281de302340c103bc601000ca200f40b71002e05b880be00940e21811c26581dc302c808200946047016405c01044009003d02c4607f007a0588c02400f40b11811c059017003f8100041180b70194403481002268ec1302dc4810889a0470104b19e82805b80ca8c04807f1090202a816e302dc0641016401380420471301250505a0a012c0590f012009c5a0a00aa83901fa4c0480271682805880c8311340e6109020470162012900b201940b102e0805881f8202dc2044816e0320e02102dc403401ca0138c44d90300641817205b8808e02dc404280a20588c0f90398404100c405b8c08202c806501880b72817005b8804302dc405880ca059017005b80c802180fa803e40e6100860328808502dc4058816e203940b202c4027200c8059080b201900b718164032080b70190405880d005b8c0b70816e1005c0b7100e00590805002c4403801642018806802dc60428164202c8205904001018c40320408211444240816e203ec0e61016207d08a2302c40b8010c602188a2202c4064118280588806300944015816206c0c0bf0398407c81cc202140b2100aa06c080c30398407c01cc200b80c0101980600b20902e00b1180c40128805002c44012a0a220300204b01802025806510162102c42058840b102e04058840b208170102c40651002e04f080b100300b7181de1020806201940b720164100c4069101ee01881ec300f40f110170101400cb01f47c0004065081b60590809602c840728164202580b21012c059080f502c8407a0164203cc0f210170101cc0b8100a005c080b80800205b8807101d04013807a201f803d10040032880850194403f01da280a8071101a40788802202d else 0x41c07e100003f012c201f80b9101c4101c0200348066100063081c41019020478100203c40d2101a401008007181a4203300d2101a404b0ac140813c033080550348407781a4201540d2100fe02a8100302340c403487c09f02820198070100fe04b0809601f84265810a0400c0f10348400348031101dc101f8031100a00360808008164031007a303b82040040041040b70816e032880b801a04047016e02a8c08e0154401e0407f00f0404700fe0400c0b102dc0b818164013880b701900251144803600aa20084208381fc2023a02116829809081070810005b880b101904058810a2288c08501b04058810002a8c0b102004031012c201fc3319c0e40348c0550140405b80c8202240b71016e102c8064100aa034080b9080d203988073081721d05010402c40b7200a2103bc065100d0042880b7015407f180c8102e00b101906059016205b8c0b202dc065180d010190068101640830162302c810802c410601140b73016205b880b802dc065180ca1000a0101cc2069005c2c8200651013410194025101001c8cc2032004a200942b19840f10348403384451081e203f080b7023c402a80d821144206200fc2041c0d21402805c00ce302e00851010a100e8207884063080cc1041c207881a422050203805c140800ef081de1034802e1582805c00f80129320901940b81812c102e00251010a05c08160a016202a81b0402c410602e06)))
def q239:Packing:=(486,5,9,0,0,14,0,q251)
def q245 (i:Nat):Nat:=0x341e500f10b5023019000000000000000000000e039d99a054c0df04e010a1200003000000f06000000020060003de33089802a6940000000000878800000000008082c01124290c00025060001409e26e405c0759a4744400023788230468000511c25100024cc0000000000000010978110002e17807f6520003c0a8421882e0700000000000000189f0002c045051886244c000f06e4dc0000000309309d24434da0002021201dc0f0003c1200024c2405980be05d1e10000c0c000001a162000000000000000180000400300040050000280000c180061c001
def q323 (i:Nat):Nat:=0x80080047040470400682802e0401543c04820016e1000650806808068080b800c801946019420414200000328405900b81005501fa201fa1004e1010402dc4019005b8805b8064100b700c82016202dc402dc2008020002c6b06adaa294a027b9da538fe2b89a12835f9795d167d8b5dd725b56855131438fa398c32807d1683708c0f028050030dfad6c62b64d26290497f5f49c4c58a4c120bfa48e938a9aa498241f74953624ab549304837e92a68e156a9260904dfa2751c2ad524c120e9f8c13024daa29824196f98c5b09b54530483af6302a6136a8a609065ee6314c26d514c120ebe8c0a784daa29824197d98c4f09b54530483bf830298a562d2609065fc6049c46c5a4c120c9fac0ab84da62c4a41afd1812b1314c1894834fab0256262983129041ff2b55c46c3a62520f7e0a92629823444a415f68bd54d5260120442fcd2da562a6a9240886fd85493c2ad5148110b7b256b04a92a29ca21e3658254981569190c2fc92da4e2a6a92609065ae5b14c26d514c120cbcca62784daa29824113f98d2711b16930482de915aa9aa498312907cf0549814c53062520d9e8c0ab898a60c4a4127d8ad571314c18948367a30256262983129074f46053046c3a62520e7b0a92a285a341ca41bf2152530ab54520443c69aa6c12a4c52720878d3609526295a4e410
def q318:Packing:=(38,6,9,0,0,10,0,q323)
def q321 (i:Nat):Nat:=0x12100000000000340e920018094000000000000003a10000000400
def q324 (i:Nat):Nat:=0x2e002dc400005b803288019001945527ca4a0396b1815b14c26d514c120e4f46058c4f09b545304839791815313c26d514c120ecd054981571314c18948323d1812b55c4c53062520
def q319:Packing:=(5,7,9,0,0,7,0,q324)
def q322 (i:Nat):Nat:=0x34000000000000000
def q325 (i:Nat):Nat:=0x1c8d0549812b55c4c53062520
def q320:Packing:=(1,8,9,0,0,0,0,q325)
def xmsamples:Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc93c600104800f00033a821010a4040000e784c10398cc00b1801080fc64c4481d3200821075b3090d9a33c9401c73e21f673,0x2a2c892948494384049443e911490019504944c10118c800b1801080946484481532008210253200091222c94000224212652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc03000c538c42003890004200000001bf8e7a10a52610c040206430b2187c00061c3b30c6249c31632604c0ff66a4c8c6487f,0x1092049602b0045b1b60a410c4864fe48810a10a526104040206430a218240004081330c6248c10420400804264a488c44829),(0x26010014d0082046000004200913f9d3b00800001c01f2583c181c13c6072081863c4010038e7c98c38470f188738f1078f9c,0xd485220dd0e2184e48942ed2940800050c500000800a2583c181c11c60520810028401001002898838470a18831071038514),(0x30030208803b402c44c001474203e88004100600607e0080c000601c07f8070e07c003e07c0f80e0fc0780fe0f83f01f80fe0,0x20332dc802e0524012408c02d4a45a41ad0a460000540080c00060000150070c07c003e0580f80407c03005e0502f00b00ae0),(0xe420804100c080000035552a400000400380c7f80031f001f801ff800380ff8007c007ff000ff0007ff000ffc001fff000,0x15c05216b516ac3be92b30142a12a5a602b4b80c7e80031f001f801f68003803e8007c0027d000bf0004dd000afc0014ed000),(0x9803c2203009310323fc888000806200200400f800003e0001fffe000003ff000007fff800000fffff800000fffffe000000,0x58336c48484301962402c12a02457c025168000000003e000156a40000032a000006a59000000fff6e800000fffdda000000),(0x4081c02844008188003000a440000c49003ff0000003ffffe0000000003fffffff8000000000fffffffffff000000000000,0x2d293b48ac4cfaa06402188b33303003372f56a0000003f2e940000000003fffbf7e8000000000fbdfbff7fbd000000000000),(0x6000c1040009050300540080910116000083ffffffffc000000000000003fffffffffffffffff00000000000000000000000,0x3234891b2271ce6219369100569b283f8a287ffff7ff5c000000000000000d5effd795a6feffd700000000000000000000000),(0x10c09122032340a044c03882a448020403107fffffffffffffffffffffffc0000000000000000000000000000000000000000,0x1244c0335113050689bd4364084b803c40c0295fffabfc0d16aa95bffeafc0000000000000000000000000000000000000000)]
def xmcolumns:List zK:=[(1,0,510,0,12),(2,0,509,0,12),(1280,0,1279,0,12),(1184,0,1375,0,11),(1156,0,1403,0,11),(69122,0,69629,0,12),(59906,0,60413,0,12),(52753,0,53230,0,11),(42752,0,42751,0,12),(42504,0,42999,0,12),(42528,0,42975,0,12),(42628,0,42875,0,11),(4,0,507,0,12),(1538,0,2045,0,12),(1792,0,1791,0,12),(1696,0,1887,0,11),(69137,0,69614,0,11),(59921,0,60398,0,11),(49153,0,49662,0,12),(48260,0,48507,0,11),(43010,0,43517,0,12),(32,0,479,0,12),(256,0,255,0,12),(8,0,503,0,12),(2052,0,2555,0,12),(2304,0,2303,0,12),(2208,0,2399,0,11),(69128,0,69623,0,12),(47624,0,48119,0,12),(17,0,494,0,11),(11265,0,11774,0,12),(2368,0,2239,0,11),(134,0,377,0,8),(9,16,486,0,8),(3,0,508,0,9),(1188,0,1371,0,8),(55305,16,55782,0,8),(7,0,504,0,7),(47633,0,48110,0,11),(35,0,476,0,7),(44546,0,45053,0,12),(42652,0,42851,0,7),(52819,0,53164,0,7),(42532,128,42843,0,8),(42760,0,42743,0,9),(1794,64,1725,0,8),(264,0,247,0,9),(27656,0,28151,0,12),(44568,0,45031,0,11),(288,0,223,0,9),(258,64,189,0,8),(58624,0,58623,0,12),(17152,0,17151,0,12),(52992,0,52991,0,12),(47872,0,47871,0,12),(44800,0,44799,0,12),(27665,0,28142,0,11),(46112,0,46559,0,12),(43330,0,43197,0,8),(2306,64,2237,0,8),(33,0,478,0,9),(268,0,243,0,7),(69129,16,69606,0,8),(12297,16,12774,0,8),(27650,0,28157,0,12),(69254,0,69497,0,8),(1288,0,1271,0,9),(14,0,497,0,7),(58690,0,58557,0,8),(8,16,486,1,9),(55304,16,55782,1,9),(1060,128,1371,0,8),(60038,0,60281,0,8),(18566,0,18809,0,8),(177,0,334,0,7),(46080,128,46427,36,10),(18433,0,18942,0,12),(36,128,347,0,8),(69148,0,69603,0,8),(59987,0,60332,0,7),(296,0,215,0,7),(43266,64,43197,0,8),(344,0,167,0,7),(156,0,355,0,7),(46116,128,46427,0,8),(21,0,490,0,7),(17154,64,17085,0,8),(52994,64,52925,0,8),(44802,64,44733,0,8),(12305,0,12782,0,11),(2240,0,2367,0,11),(83,0,428,0,7),(12288,64,12477,258,10),(28,0,483,0,8),(58368,64,58557,258,10),(12546,64,12477,0,8),(2212,0,2395,0,8),(7681,0,8190,0,12),(24,4,353,130,6),(256,8,227,20,7),(260,8,227,16,6),(257,32,94,128,6),(258,0,189,0,8),(18,4,353,136,6),(136,256,23,96,6),(96,1,396,18,6),(64,4,305,138,7),(16,2,424,69,7),(64,1,396,50,7),(59911,0,60408,0,7),(42764,0,42739,0,7),(129,2,312,68,6),(130,1,332,48,6),(132,2,312,65,6),(49161,16,49638,0,8),(260,0,251,0,8),(42792,0,42711,0,7),(42520,4,353,130,6),(69127,0,69624,0,7),(43652,2,312,65,6),(48224,1,396,18,6),(69203,0,69548,0,7),(44868,0,44731,0,7),(49412,0,49403,0,8),(160,256,23,72,6),(289,0,222,0,7),(0,8,227,276,8),(1,32,94,384,7),(4,8,227,272,7),(43264,64,43197,2,9),(43048,0,43479,0,8),(44700,0,44899,0,7),(43538,4,353,136,6),(26,0,485,0,7),(48160,128,48475,4,9),(50760,4,305,130,6),(50784,1,396,18,6),(47641,0,48102,0,8),(69252,0,69499,0,11),(60036,0,60283,0,11),(59905,0,60398,0,11),(69253,0,69498,0,7),(58373,0,58874,0,8),(34,0,477,0,8),(16,256,135,104,7),(59970,4,305,136,6),(58434,4,305,136,6),(53777,2,424,68,6),(55425,2,312,68,6),(42912,0,42591,0,8),(9,0,486,0,8),(42820,0,42683,0,7),(46084,128,46427,32,9),(53826,1,396,48,6),(257,0,254,0,8),(58498,1,332,48,6),(52771,0,53212,0,7),(53024,0,52959,0,9),(256,32,94,129,7),(47712,1,396,18,6),(48292,0,48475,0,8),(49224,4,305,130,6),(44548,0,45051,0,12),(48385,0,48382,0,8),(46090,0,46581,0,8),(48132,0,48507,0,11),(2306,0,2237,0,8),(13825,0,14318,0,11),(43568,256,135,72,6),(69121,16,69606,8,9),(129,0,382,0,9),(60034,0,60285,0,9),(18561,0,18814,0,9),(44544,64,44733,258,10),(52736,64,52925,258,10),(2084,128,2395,0,8),(12546,0,12477,0,8),(26,4,353,128,5),(168,256,23,64,5),(273,32,78,128,5),(296,16,198,1,5),(268,128,83,32,5),(292,128,91,0,5),(98,1,396,16,5),(21,2,424,64,5),(36,0,347,0,8),(273,0,238,0,7),(1864,0,1719,0,8),(388,0,123,0,7),(0,16,486,9,10),(0,64,189,258,10),(133,0,378,0,7),(74,4,305,128,5),(74,0,437,0,7),(152,0,359,0,8),(136,0,359,0,8),(266,64,181,0,5),(0,128,347,36,10),(69194,0,69557,0,7),(44618,0,44981,0,7),(2,64,189,256,9),(321,32,30,128,5),(328,0,167,0,7),(256,64,189,2,9),(281,0,230,0,5),(58370,64,58557,256,9),(194,4,305,8,5),(260,128,91,32,6),(56,128,323,4,5),(58626,64,58557,0,8),(0,32,94,385,8),(49160,16,49638,1,9),(47968,0,47647,0,7),(42496,128,42843,36,10),(42528,128,42843,4,9),(43074,0,43453,0,11),(133,2,312,64,5),(200,4,305,2,5),(47944,0,47799,0,8),(4,128,347,32,9),(43008,64,43197,258,10),(59936,0,60383,0,12),(47776,0,47967,0,11),(67,0,428,0,7),(388,64,57,2,5),(52896,0,53087,0,11),(297,16,198,0,4),(185,0,326,0,4),(289,16,198,8,5),(1,16,486,8,9),(154,4,353,0,4),(49,128,330,4,5),(334,0,177,0,4),(3,128,344,36,6),(17,32,78,384,6),(385,32,94,0,5),(129,32,94,256,6),(428,0,83,0,4),(15,16,480,0,4),(167,0,344,0,4),(59908,0,60283,0,11),(291,64,156,0,4),(56,256,135,64,5),(7,16,480,8,5),(275,64,172,0,4),(21,128,330,32,5),(112,1,396,2,5),(48,0,462,0,8),(456,0,55,0,5),(32,128,347,4,9),(160,64,29,258,6),(288,128,91,4,6),(85,2,424,0,4),(178,1,332,0,4),(55297,16,55782,8,9),(416,64,29,2,5),(120,256,135,0,4),(321,0,190,0,7),(72,4,305,130,6),(7,128,344,32,5),(43010,64,43197,256,9),(39,128,344,0,4),(98,128,281,4,5),(157,0,354,0,4),(162,64,29,256,5)]
def xmautos:List (List Nat):=[[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def xmlevels:Nat → Packing
 | 15=>q234
 | 14=>q235
 | 13=>q236
 | 12=>q237
 | 11=>q238
 | 10=>q239
 | 9=>q318
 | 8=>q319
 | 7=>q320
 | _=>zP
def xmindex:Nat → Nat → Option (Nat × Nat)
 | 15=>zk 11 85 7 11 3 4 q240
 | 14=>zk 38 179 8 14 6 4 q241
 | 13=>zk 234 1837 11 17 9 4 q242
 | 12=>zk 684 3083 12 19 11 4 q243
 | 11=>zk 248 1123 11 17 9 4 q244
 | 10=>zk 24 113 7 14 6 4 q245
 | 9=>zk 3 19 5 11 3 4 q321
 | 8=>zk 1 7 3 9 1 4 q322
 | _=>fun _=>none
def zG:Forest := ⟨1535,15,fun j=>xmsamples[j]?.getD (0,0),xmcolumns,xmautos,xmlevels,xmindex⟩
set_option maxHeartbeats 0 in
theorem q287:qc zG (z9 wx)=true:=by
 simp only [qc,Bool.and_eq_true]
 refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,zh (d:=5) ?_⟩,zh (d:=2) ?_⟩
 all_goals simp only [zQ]
 all_goals repeat' apply And.intro
 all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z397:z8 zG 15 0 1=true:=by refine (z2 (ar:=9) (rows:=1) (d:=0) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z398:z8 zG 14 0 6=true:=by refine (z2 (ar:=10) (rows:=1) (d:=0) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z399:z8 zG 13 0 45=true:=by refine (@z3 zG 13 0 16 29 (@z3 zG 13 0 5 11 (z2 (ar:=9) (rows:=0) (d:=0) ?_) (z2 (ar:=10) (rows:=0) (d:=0) ?_)) (z2 (ar:=11) (rows:=0) (d:=1) ?_)); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z345:z8 zG 12 0 64=true:=by refine (z2 (ar:=10) (rows:=0) (d:=2) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z256:z8 zG 12 64 64=true:=by refine (z2 (ar:=11) (rows:=0) (d:=2) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z190:z8 zG 12 128 64=true:=by refine (z2 (ar:=11) (rows:=0) (d:=2) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z189:z8 zG 12 192 28=true:=by refine (z2 (ar:=11) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z188:z8 zG 12 220 64=true:=by refine (z2 (ar:=12) (rows:=0) (d:=2) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z187:z8 zG 12 284 64=true:=by refine (z2 (ar:=12) (rows:=0) (d:=2) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z186:z8 zG 12 348 20=true:=by refine (z2 (ar:=12) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem q100:z8 zG 12 0 368=true:=(@z3 zG 12 0 348 20 (@z3 zG 12 0 284 64 (@z3 zG 12 0 220 64 (@z3 zG 12 0 192 28 (@z3 zG 12 0 128 64 (@z3 zG 12 0 64 64 z345 z256) z190) z189) z188) z187) z186)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z346:z8 zG 11 0 16=true:=by refine (z2 (ar:=9) (rows:=0) (d:=0) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z258:z8 zG 11 16 64=true:=by refine (z2 (ar:=10) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z257:z8 zG 11 80 54=true:=by refine (z2 (ar:=10) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z204:z8 zG 11 134 64=true:=by refine (z2 (ar:=11) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z203:z8 zG 11 198 64=true:=by refine (z2 (ar:=11) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z202:z8 zG 11 262 64=true:=by refine (z2 (ar:=11) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z201:z8 zG 11 326 64=true:=by refine (z2 (ar:=11) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z200:z8 zG 11 390 64=true:=by refine (z2 (ar:=11) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z199:z8 zG 11 454 64=true:=by refine (z2 (ar:=11) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z198:z8 zG 11 518 64=true:=by refine (z2 (ar:=11) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z197:z8 zG 11 582 64=true:=by refine (z2 (ar:=11) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z196:z8 zG 11 646 64=true:=by refine (z2 (ar:=11) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z195:z8 zG 11 710 45=true:=by refine (z2 (ar:=11) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z194:z8 zG 11 755 64=true:=by refine (z2 (ar:=12) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z193:z8 zG 11 819 64=true:=by refine (z2 (ar:=12) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z192:z8 zG 11 883 64=true:=by refine (z2 (ar:=12) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z191:z8 zG 11 947 64=true:=by refine (z2 (ar:=12) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z129:z8 zG 11 1011 64=true:=by refine (z2 (ar:=12) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z128:z8 zG 11 1075 64=true:=by refine (z2 (ar:=12) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z127:z8 zG 11 1139 42=true:=by refine (z2 (ar:=12) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem q101:z8 zG 11 0 1181=true:=(@z3 zG 11 0 1139 42 (@z3 zG 11 0 1075 64 (@z3 zG 11 0 1011 64 (@z3 zG 11 0 947 64 (@z3 zG 11 0 883 64 (@z3 zG 11 0 819 64 (@z3 zG 11 0 755 64 (@z3 zG 11 0 710 45 (@z3 zG 11 0 646 64 (@z3 zG 11 0 582 64 (@z3 zG 11 0 518 64 (@z3 zG 11 0 454 64 (@z3 zG 11 0 390 64 (@z3 zG 11 0 326 64 (@z3 zG 11 0 262 64 (@z3 zG 11 0 198 64 (@z3 zG 11 0 134 64 (@z3 zG 11 0 80 54 (@z3 zG 11 0 16 64 z346 z258) z257) z204) z203) z202) z201) z200) z199) z198) z197) z196) z195) z194) z193) z192) z191) z129) z128) z127)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z348:z8 zG 10 0 6=true:=by refine (z2 (ar:=9) (rows:=0) (d:=0) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z347:z8 zG 10 6 64=true:=by refine (z2 (ar:=10) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z259:z8 zG 10 70 64=true:=by refine (z2 (ar:=10) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z210:z8 zG 10 134 64=true:=by refine (z2 (ar:=10) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z209:z8 zG 10 198 39=true:=by refine (z2 (ar:=10) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z208:z8 zG 10 237 64=true:=by refine (z2 (ar:=11) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z207:z8 zG 10 301 64=true:=by refine (z2 (ar:=11) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z206:z8 zG 10 365 64=true:=by refine (z2 (ar:=11) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem z205:z8 zG 10 429 57=true:=by refine (z2 (ar:=11) (rows:=0) (d:=1) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem q102:z8 zG 10 0 486=true:=(@z3 zG 10 0 429 57 (@z3 zG 10 0 365 64 (@z3 zG 10 0 301 64 (@z3 zG 10 0 237 64 (@z3 zG 10 0 198 39 (@z3 zG 10 0 134 64 (@z3 zG 10 0 70 64 (@z3 zG 10 0 6 64 z348 z347) z259) z210) z209) z208) z207) z206) z205)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q194:z8 zG 9 0 38=true:=by refine (@z3 zG 9 0 15 23 (z2 (ar:=9) (rows:=0) (d:=0) ?_) (z2 (ar:=10) (rows:=0) (d:=0) ?_)); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q195:z8 zG 8 0 5=true:=by refine (@z3 zG 8 0 2 3 (z2 (ar:=8) (rows:=0) (d:=0) ?_) (z2 (ar:=9) (rows:=0) (d:=0) ?_)); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q196:z8 zG 7 0 1=true:=by refine (z2 (ar:=7) (rows:=0) (d:=0) ?_); all_goals simp only [ze,zd,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]; all_goals (repeat' apply And.intro); all_goals decide +kernel
theorem z335:qp zG 15:=by
 intro k hk
 interval_cases k
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · rfl
 · exact q196
 · exact q195
 · exact q194
 · exact q102
 · exact q101
 · exact q100
 · exact z399
 · exact z398
 · exact z397
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem caseM15:zo false (z1 511) 15 (vars 1535).toFinset:=by
 have h:=wk (u:=false) (g:=zG) (m:=1535) (i:=0) (ws:=vars 1535) rfl rfl (z5 wx z328) q287 z335 (by decide +kernel)
 have eg:z1 1535=z1 511:=by decide +kernel
 exact eg ▸ h

end PEqualNP.Outside.L_meta_2116

theorem PEqualNP.Outside.L_meta_2116 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); have x2 : (x2 : PEqualNP.CircuitLowerBounds.Circuit) → Fin (9 : ℕ) → Finset (Fin x2.size) := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Fin (9 : ℕ)) => {x4 : Fin x2.size | ↑x3 ∈ (x2.gates.get x4).inputs}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) =>   PEqualNP.MetaComplexity.IsMinimalCircuit (9 : ℕ) x3 ∧     x3.size ≤ (15 : ℕ) ∧       PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x3 = x1 ∧         (∀ (x4 : Fin x3.size),             have x5 : PEqualNP.CircuitLowerBounds.Gate := x3.gates.get x4;             (∀ x6 ∈ x5.inputs, x6 < (9 : ℕ) + ↑x4) ∧ x5.inputs.Nodup ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (1 : ℕ) ∨ x5.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x5.inputs.length = (2 : ℕ))) ∧           ∀ x4 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x3 x4).Nonempty ∧ (x2 x3 x4).card ≤ (2 : ℕ) ∧ ((x2 x3 x4).card = (2 : ℕ) → ∀ x7 ∈ x2 x3 x4, (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or); ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → (∀ x6 ∈ [(4 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))], (x2 x4 x6).card = (1 : ℕ) ∧ ∀ x8 ∈ x2 x4 x6, (x4.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or) → False := by
  dsimp only
  intro C hP hS
  exact PEqualNP.Outside.L_meta_2116.bound_2116 PEqualNP.Outside.L_meta_2116.caseU14 PEqualNP.Outside.L_meta_2116.caseM15 C hP.1 hP.2.1 (hP.2.2.1.trans rfl) hP.2.2.2.1 hS
