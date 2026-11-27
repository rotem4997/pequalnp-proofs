import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_5316
open PEqualNP.CircuitLowerBounds
abbrev Sig:=BitVec 512
def zero : Sig:=0
def one : Sig:=BitVec.allOnes 512
def neg (a:Sig) : Sig := ~~~a
def bin (d:Bool) (a b:Sig) : Sig:=if d then a ||| b else a &&& b
def proper (a:Sig) : Prop:=a ≠ zero∧a ≠ one
lemma k4 (d:Bool) (a b:Sig) : bin d a b=bin d b a:=by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]
def Live (fh:Sig) : Nat→ Nat→ Finset Sig→ Prop:=fun k t S =>
  ∀ (M:(Nat→ Nat→ Finset Sig→ Prop)),(proper fh→ M 0 0 {fh}) →
  (∀ {k t:Nat} {U:Finset Sig} {a:Sig},proper a→ neg a ∉ insert a U→ M k t (insert (neg a) U)→ M (k+1) (t+1) (insert a U)) →
  (∀ {k t:Nat} {U:Finset Sig} {a b:Sig} {d:Bool},proper a→ proper b→ a ≠ b→ bin d a b ∉ insert a (insert b U)→ M k t (insert (bin d a b) U)→ M (k+1) t (insert a (insert b U))) →
  M k t S
lemma Live.stop {fh:Sig}  (h0:proper fh) : Live fh 0 0 {fh}:=fun M stop unary binary => @stop  h0
lemma Live.unary {fh:Sig} {k t:Nat} {U:Finset Sig} {a:Sig} (h0:proper a) (h1:neg a ∉ insert a U) (h2:Live fh k t (insert (neg a) U)) : Live fh (k+1) (t+1) (insert a U):=fun M stop unary binary => @unary k t U a h0 h1 (h2 M stop unary binary)
lemma Live.binary {fh:Sig} {k t:Nat} {U:Finset Sig} {a b:Sig} {d:Bool} (h0:proper a) (h1:proper b) (h2:a ≠ b) (h3:bin d a b ∉ insert a (insert b U)) (h4:Live fh k t (insert (bin d a b) U)) : Live fh (k+1) t (insert a (insert b U)):=fun M stop unary binary => @binary k t U a b d h0 h1 h2 h3 (h4 M stop unary binary)
lemma Live.induct {fh:Sig} {M:(Nat→ Nat→ Finset Sig→ Prop)} {k t S} (h:Live fh k t S)
  (stop:proper fh→ M 0 0 {fh})
  (unary:∀ {k t:Nat} {U:Finset Sig} {a:Sig},proper a→ neg a ∉ insert a U→ Live fh k t (insert (neg a) U)→ M k t (insert (neg a) U)→ M (k+1) (t+1) (insert a U))
  (binary:∀ {k t:Nat} {U:Finset Sig} {a b:Sig} {d:Bool},proper a→ proper b→ a ≠ b→ bin d a b ∉ insert a (insert b U)→ Live fh k t (insert (bin d a b) U)→ M k t (insert (bin d a b) U)→ M (k+1) t (insert a (insert b U))) : M k t S :=
  (h (fun k t S => Live fh k t S∧M k t S)
  (fun h0 => ⟨@Live.stop fh  h0,@stop  h0⟩)
  (@fun k t U a h0 h1 h2 => ⟨@Live.unary fh k t U a h0 h1 h2.1,@unary k t U a h0 h1 h2.1 h2.2⟩)
  (@fun k t U a b d h0 h1 h2 h3 h4 => ⟨@Live.binary fh k t U a b d h0 h1 h2 h3 h4.1,@binary k t U a b d h0 h1 h2 h3 h4.1 h4.2⟩)).2
lemma Live.recurse {fh:Sig} {M:∀ (k t:Nat) (S:Finset Sig) (proof:Live fh k t S),Prop}
  (stop:∀ (h0:proper fh),M 0 0 {fh} (@Live.stop fh  h0))
  (unary:∀ {k t:Nat} {U:Finset Sig} {a:Sig} (h0:proper a) (h1:neg a ∉ insert a U) (h2:Live fh k t (insert (neg a) U)) (ih:M k t (insert (neg a) U) h2),M (k+1) (t+1) (insert a U) (@Live.unary fh k t U a h0 h1 h2))
  (binary:∀ {k t:Nat} {U:Finset Sig} {a b:Sig} {d:Bool} (h0:proper a) (h1:proper b) (h2:a ≠ b) (h3:bin d a b ∉ insert a (insert b U)) (h4:Live fh k t (insert (bin d a b) U)) (ih:M k t (insert (bin d a b) U) h4),M (k+1) t (insert a (insert b U)) (@Live.binary fh k t U a b d h0 h1 h2 h3 h4))
  {k t S} (h:Live fh k t S) : M k t S h:=by
  have r:=Live.induct (M:=fun k t S => ∀ hh : Live fh k t S,M k t S hh) h
    (fun h0 _ => @stop  h0)
    (@fun k t U a h0 h1 h2 h3 _ => @unary k t U a h0 h1 h2 (h3 h2))
    (@fun k t U a b d h0 h1 h2 h3 h4 h5 _ => @binary k t U a b d h0 h1 h2 h3 h4 (h5 h4))
  exact r h
lemma Live.zeroSet {T t S} (h:Live T 0 t S) : S={T}:=by
  have hh:=h (fun k _ W => k=0→ W={T}) (fun _ _ => rfl)
    (@fun _ _ _ _ _ _ _ e => by omega)
    (@fun _ _ _ _ _ _ _ _ _ _ _ e => by omega)
  exact hh rfl
lemma live_proper {k t S} (h:Live fh k t S) : ∀ a ∈ S,proper a:=by
  induction h using Live.recurse with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert];exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩
lemma mi {k t S} (h:Live fh k t S) : t ≤ k∧S.card+t ≤ k+1:=by
  induction h using Live.recurse with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U:=fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc:=Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U:=fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1:=Finset.card_insert_le (a:=a) (s:=insert b U)
    have h2:=Finset.card_insert_le (a:=b) (s:=U)
    exact ⟨by omega,by omega⟩
def gv (w:List Sig) (g:Gate) : Sig :=
  let xs:=g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def execute (gs:List Gate) (w:List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
def fg (w:List Sig) (v:Sig) : Prop:=v ∈ w ∨ ¬proper v
lemma get_rep (w:List Sig) (i:Nat) : fg w (w.getD i zero):=by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)
lemma bin_laws (a:Sig) :
    bin false a one=a∧bin true a zero=a ∧
    bin false a zero=zero∧bin true a one=one ∧
    bin false a a=a∧bin true a a=a:=by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp
lemma m0 : neg zero=one∧neg one=zero:=by simp [neg,zero,one]
lemma h6 {w:List Sig} {a:Sig} (h:fg w a) :
    a=zero∨a=one∨a ∈ w∧proper a:=by
  by_cases hz : a=zero
  · exact Or.inl hz
  by_cases ho : a=one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)
def pi (w:List Sig) (z:Sig) : Prop :=
  (∃ a ∈ w,proper a∧z=neg a) ∨
  (∃ d a b,a ∈ w∧b ∈ w∧proper a∧proper b∧a ≠ b∧z=bin d a b)
lemma y8 {w a b} (d:Bool) (ha:fg w a) (hb:fg w b) :
    fg w (bin d a b)∨pi w (bin d a b):=by
  have rz : fg w zero:=Or.inr (fun h => h.1 rfl)
  have ro : fg w one:=Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases h6 ha with rfl | rfl | ⟨ham,hap⟩
  · rw [k4];cases d <;> simp_all
  · rw [k4];cases d <;> simp_all
  rcases h6 hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b;cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)
def isNotT (op:GateOp) : Bool :=
  match op with
  | .not => true
  | _ => false
lemma ve (w:List Sig) (g:Gate)
    (hg:g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)∧g.inputs.length≤2) :
    fg w (gv w g) ∨
      (if isNotT g.op then ∃ a,a∈w∧proper a∧gv w g=neg a
       else ∃ d a b,a∈w∧b∈w∧proper a∧proper b∧a≠b∧gv w g=bin d a b):=by
  have nx (a:Sig) (ha:fg w a) : fg w (neg a) ∨ ∃ x,x∈w∧proper x∧neg a=neg x:=by
    rcases h6 ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (Or.inr fun h => h.2 m0.1)
    · exact Or.inl (Or.inr fun h => h.1 m0.2)
    · exact Or.inr ⟨a,hm,hp,rfl⟩
  have bn (d:Bool) (a b:Sig) (ha:fg w a) (hb:fg w b) :
      fg w (bin d a b) ∨ ∃ d' x y,x∈w∧y∈w∧proper x∧proper y∧x≠y∧bin d a b=bin d' x y:=by
    have bzero : ∀ v,bin false v zero=zero∧bin true v zero=v:=fun v => ⟨(bin_laws v).2.2.1,(bin_laws v).2.1⟩
    have bone : ∀ v,bin false v one=v∧bin true v one=one:=fun v => ⟨(bin_laws v).1,(bin_laws v).2.2.2.1⟩
    rcases h6 ha with rfl | rfl | ⟨hma,hpa⟩
    · rw [k4]
      cases d
      · exact Or.inl (Or.inr fun h => h.1 (bzero b).1)
      · rw [(bzero b).2];exact Or.inl hb
    · rw [k4]
      cases d
      · rw [(bone b).1];exact Or.inl hb
      · exact Or.inl (Or.inr fun h => h.2 (bone b).2)
    · rcases h6 hb with rfl | rfl | ⟨hmb,hpb⟩
      · cases d
        · exact Or.inl (Or.inr fun h => h.1 (bzero a).1)
        · rw [(bzero a).2];exact Or.inl (Or.inl hma)
      · cases d
        · rw [(bone a).1];exact Or.inl (Or.inl hma)
        · exact Or.inl (Or.inr fun h => h.2 (bone a).2)
      · by_cases eq : a=b
        · subst b
          cases d
          · rw [(bin_laws a).2.2.2.2.1];exact Or.inl (Or.inl hma)
          · rw [(bin_laws a).2.2.2.2.2];exact Or.inl (Or.inl hma)
        · exact Or.inr ⟨d,a,b,hma,hmb,hpa,hpb,eq,rfl⟩
  obtain ⟨ho,hl⟩ := hg
  rcases ho with ho | ho | ho
  · simp only [ho,isNotT,Bool.false_eq_true,ite_false]
    cases hi : g.inputs with
    | nil => exact Or.inl (Or.inr fun h => h.2 (by simp [gv,ho,hi]))
    | cons i t =>
      cases t with
      | nil => exact Or.inl (by simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using get_rep w i)
      | cons j u =>
        cases u with
        | cons _ _ => simp [hi] at hl
        | nil => simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bn false _ _ (get_rep w i) (get_rep w j)
  · simp only [ho,isNotT,Bool.false_eq_true,ite_false]
    cases hi : g.inputs with
    | nil => exact Or.inl (Or.inr fun h => h.1 (by simp [gv,ho,hi]))
    | cons i t =>
      cases t with
      | nil => exact Or.inl (by simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using get_rep w i)
      | cons j u =>
        cases u with
        | cons _ _ => simp [hi] at hl
        | nil => simpa only [gv,ho,hi,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bn true _ _ (get_rep w i) (get_rep w j)
  · rw [Set.mem_singleton_iff] at ho
    simp only [ho,isNotT,ite_true]
    cases hi : g.inputs with
    | nil =>
      have hgv : gv w g=one:=by simp only [gv,ho,hi,List.map_nil,List.headD_nil,m0.1]
      exact Or.inl (Or.inr fun h => h.2 hgv)
    | cons i t =>
      have hgv : gv w g=neg (w.getD i zero):=by simp only [gv,ho,hi,List.map_cons,List.headD_cons]
      rw [hgv];exact nx _ (get_rep w i)
lemma ld {w:List Sig} {z:Sig} {k t S} (isN:Bool) (h:Live fh k t S)
    (hz:fg w z ∨
      (if isN then ∃ a,a∈w∧proper a∧z=neg a
       else ∃ d a b,a∈w∧b∈w∧proper a∧proper b∧a≠b∧z=bin d a b))
    (sub:∀ a ∈ S,a ∈ w++[z]) :
    ∃ k' t' S',k' ≤ k+1∧t' ≤ t+isN.toNat∧Live fh k' t' S' ∧ ∀ a ∈ S',a ∈ w:=by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,by cases isN <;> simp,h,?_⟩
      intro a ha
      rcases (by simpa using sub a ha:a ∈ w∨a=z) with hu | rfl
      · exact hu
      · exact hw
    · have hp:=live_proper h z hm
      rcases hz with hr | hwit
      · exact False.elim ((hr.resolve_left hw) hp)
      · cases isN with
        | true =>
          simp only [ite_true] at hwit
          obtain ⟨a,ha,hp',eq⟩ := hwit
          subst z
          let U:=S.erase (neg a)
          have ht : Live fh k t (insert (neg a) U):=by simpa [U,Finset.insert_erase hm] using h
          have hu : ∀ v ∈ U,v ∈ w:=fun v hv => by
            obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv;simpa [hne] using sub v hm
          have hf : neg a ∉ insert a U:=fun hh => by
            rcases Finset.mem_insert.mp hh with eq | u
            · exact hw (eq.symm ▸ ha)
            · exact hw (hu _ u)
          exact ⟨k+1,t+1,insert a U,Nat.le_refl _,by simp,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
        | false =>
          simp only [Bool.false_eq_true,ite_false] at hwit
          obtain ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩ := hwit
          subst z
          let U:=S.erase (bin d a b)
          have ht : Live fh k t (insert (bin d a b) U):=by simpa [U,Finset.insert_erase hm] using h
          have hu : ∀ v ∈ U,v ∈ w:=fun v hv => by
            obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv;simpa [hne] using sub v hm
          have hf : bin d a b ∉ insert a (insert b U):=fun hh => by
            rcases Finset.mem_insert.mp hh with eq | u
            · exact hw (eq.symm ▸ ha)
            rcases Finset.mem_insert.mp u with eq | u
            · exact hw (eq.symm ▸ hb)
            · exact hw (hu _ u)
          exact ⟨k+1,t,insert a (insert b U),Nat.le_refl _,by simp,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,by cases isN <;> simp,h,?_⟩
    intro a ha
    have hn : a ≠ z:=fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha
lemma extractT (gs:List Gate) (w:List Sig)
    (b6:∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)∧g.inputs.length≤2)
    (hp:proper fh) (hout:fh ∈ execute gs w) :
    ∃ k t S,k ≤ gs.length∧t ≤ gs.countP (fun g => isNotT g.op)∧Live fh k t S ∧ ∀ a ∈ S,a ∈ w:=by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{fh},by simp,by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hl,hs⟩ := ih (w++[gv w g]) (fun a ha => b6 a (by simp [ha])) hout
    obtain ⟨l,u,T,hl',hu',hlu,hT⟩ := ld (isNotT g.op) hl (ve w g (b6 g (by simp))) hs
    refine ⟨l,u,T,by simp;omega,?_,hlu,hT⟩;simp only [List.countP_cons]
    cases h : isNotT g.op <;> simp [h] at hu' ⊢ <;> omega
lemma vf {w:List Sig} {z:Sig} {k t S} (h:Live fh k t S)
    (hz:fg w z∨pi w z) (sub:∀ a ∈ S,a ∈ w ++ [z]) :
    ∃ k' t' S',k' ≤ k+1∧Live fh k' t' S' ∧ ∀ a ∈ S',a ∈ w:=by
  rcases hz with hr | (hu | hb)
  · obtain ⟨k',t',S',hk,_,hl,hs⟩ := ld false h (Or.inl hr) sub;exact ⟨k',t',S',hk,hl,hs⟩
  · obtain ⟨k',t',S',hk,_,hl,hs⟩ := ld true h (Or.inr hu) sub;exact ⟨k',t',S',hk,hl,hs⟩
  · obtain ⟨k',t',S',hk,_,hl,hs⟩ := ld false h (Or.inr hb) sub;exact ⟨k',t',S',hk,hl,hs⟩
def bit (i:Fin 512) (a:Sig) : Bool:=a.getLsbD i.val
lemma gx (i) : bit i zero=false:=by simp [bit,zero]
lemma lf (i) : bit i one=true:=by unfold bit one;rw [BitVec.getLsbD_allOnes];simp
lemma bit_neg (i) (a:Sig) : bit i (neg a) = !(bit i a):=by simp [bit,neg,i.isLt]
lemma bit_bin (i d) (a b:Sig) : bit i (bin d a b) =
    (if d then bit i a||bit i b else bit i a&&bit i b):=by cases d <;> simp [bit,bin]
lemma b_read (i) (w:List Sig) (j:Nat) :
    (w.map (bit i)).getD j false=bit i (w.getD j zero):=by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (gx _).symm
  | some a => rfl
lemma y9 (i) (g:Gate) (w:List Sig)
    (hg:g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g)=g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false):=by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg;simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact lf _
    | cons a l ih =>
      change bit i (bin false _ _)=(_&&_);rw [bit_bin];exact congrArg (fun x => bit i (w.getD a zero)&&x) ih
  · induction l with
    | nil => exact gx _
    | cons a l ih =>
      change bit i (bin true _ _)=(_||_);rw [bit_bin];exact congrArg (fun x => bit i (w.getD a zero)||x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false;rw [bit_neg,gx]
    | cons a l => exact bit_neg _ _
lemma execute_bits (gs:List Gate) (i) (w:List Sig)
    (hg:∀ g ∈ gs,g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l:List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)):=by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _=_;rw [ih _ (fun a ha => hg a (by simp [ha]))];simp only [List.foldl_cons,List.map_append,List.map_singleton,y9 i g w (hg g (by simp))]
abbrev fd (R:Type):=R→ Bool
def rm {R} (a:fd R) : fd R:=fun r => !(a r)
def fq {R} (isOr:Bool) (a b:fd R) : fd R :=
  if isOr then fun r => a r||b r else fun r => a r&&b r
def fj {R} (a:fd R) : Prop := ∃ b : Bool,a=fun _ => b
noncomputable def m1 {R} (a:fd R) : Nat:=by
  classical exact if fj a then 1 else 0
noncomputable def lg {R} (xs:List (fd R)) : Nat:=(xs.map m1).sum
def f7 {R} (pool:List (fd R)) (v:fd R) : Prop:=v ∈ pool∨fj v
def m2 {R} (pool xs:List (fd R)) := ∀ a ∈ xs,f7 pool a
def fi {R} (roots:List (fd R)) : Nat→ List (fd R)→ Prop:=fun p f5 =>
  ∀ (M:(Nat→ List (fd R)→ Prop)),(M 0 roots) →
  (∀ {p:Nat} {f5:List (fd R)} {a:fd R},M p f5→ f7 f5 a→ M (p+1) (rm a :: f5)) →
  (∀ {p:Nat} {f5:List (fd R)} {a b:fd R} (op:Bool),M p f5→ f7 f5 a→ f7 f5 b→ M (p+1) (fq op a b :: f5)) →
  M p f5
lemma fi.start {R} {roots:List (fd R)}   : fi roots 0 roots:=fun M start one two => @start
lemma fi.one {R} {roots:List (fd R)} {p:Nat} {f5:List (fd R)} {a:fd R} (h0:fi roots p f5) (h1:f7 f5 a) : fi roots (p+1) (rm a :: f5):=fun M start one two => @one p f5 a (h0 M start one two) h1
lemma fi.two {R} {roots:List (fd R)} {p:Nat} {f5:List (fd R)} {a b:fd R} (op:Bool) (h0:fi roots p f5) (h1:f7 f5 a) (h2:f7 f5 b) : fi roots (p+1) (fq op a b :: f5):=fun M start one two => @two p f5 a b op (h0 M start one two) h1 h2
lemma fi.induct {R} {roots:List (fd R)} {M:(Nat→ List (fd R)→ Prop)} {p f5} (h:fi roots p f5)
  (start:M 0 roots)
  (one:∀ {p:Nat} {f5:List (fd R)} {a:fd R},fi roots p f5→ M p f5→ f7 f5 a→ M (p+1) (rm a :: f5))
  (two:∀ {p:Nat} {f5:List (fd R)} {a b:fd R} (op:Bool),fi roots p f5→ M p f5→ f7 f5 a→ f7 f5 b→ M (p+1) (fq op a b :: f5)) : M p f5 :=
  (h (fun p f5 => fi roots p f5∧M p f5)
  (⟨@fi.start R roots  ,@start  ⟩)
  (@fun p f5 a h0 h1 => ⟨@fi.one R roots p f5 a h0.1 h1,@one p f5 a h0.1 h0.2 h1⟩)
  (@fun p f5 a b op h0 h1 h2 => ⟨@fi.two R roots p f5 a b op h0.1 h1 h2,@two p f5 a b op h0.1 h0.2 h1 h2⟩)).2
lemma fi.recurse {R} {roots:List (fd R)} {M:∀ (p:Nat) (f5:List (fd R)) (proof:fi roots p f5),Prop}
  (start:M 0 roots (@fi.start R roots  ))
  (one:∀ {p:Nat} {f5:List (fd R)} {a:fd R} (h0:fi roots p f5) (ih:M p f5 h0) (h2:f7 f5 a),M (p+1) (rm a :: f5) (@fi.one R roots p f5 a h0 h2))
  (two:∀ {p:Nat} {f5:List (fd R)} {a b:fd R} (op:Bool) (h0:fi roots p f5) (ih:M p f5 h0) (h2:f7 f5 a) (h3:f7 f5 b),M (p+1) (fq op a b :: f5) (@fi.two R roots p f5 a b op h0 h2 h3))
  {p f5} (h:fi roots p f5) : M p f5 h:=by
  have r:=fi.induct (M:=fun p f5 => ∀ hh : fi roots p f5,M p f5 hh) h
    (fun  _ => @start  )
    (@fun p f5 a h0 h1 h2 _ => @one p f5 a h0 (h1 h0) h2)
    (@fun p f5 a b op h0 h1 h2 h3 _ => @two p f5 a b op h0 (h1 h0) h2 h3)
  exact r h
def fw {α : Type} (save:Bool) (x : α) (xs:List α):=if save then x::xs else xs
def k8 {R} (goal:fd R) : Nat→ List (fd R)→ Prop:=fun s ws =>
  ∀ (M:(Nat→ List (fd R)→ Prop)),(M 0 [goal]) →
  (∀ {s:Nat} {xs zs:List (fd R)},xs.Perm zs→ M s xs→ M s zs) →
  (∀ {s:Nat} {a:fd R} {rest:List (fd R)} (save:Bool),M s (rm a :: fw save a rest)→ M (s+1) (a::rest)) →
  (∀ {s:Nat} {a b:fd R} {rest:List (fd R)} (op ka kb:Bool),M s (fq op a b :: fw ka a (fw kb b rest))→ M (s+1) (a::b::rest)) →
  M s ws
lemma k8.stop {R} {goal:fd R}   : k8 goal 0 [goal]:=fun M stop perm one two => @stop
lemma k8.perm {R} {goal:fd R} {s:Nat} {xs zs:List (fd R)} (h0:xs.Perm zs) (h1:k8 goal s xs) : k8 goal s zs:=fun M stop perm one two => @perm s xs zs h0 (h1 M stop perm one two)
lemma k8.one {R} {goal:fd R} {s:Nat} {a:fd R} {rest:List (fd R)} (save:Bool) (h0:k8 goal s (rm a :: fw save a rest)) : k8 goal (s+1) (a::rest):=fun M stop perm one two => @one s a rest save (h0 M stop perm one two)
lemma k8.two {R} {goal:fd R} {s:Nat} {a b:fd R} {rest:List (fd R)} (op ka kb:Bool) (h0:k8 goal s (fq op a b :: fw ka a (fw kb b rest))) : k8 goal (s+1) (a::b::rest):=fun M stop perm one two => @two s a b rest op ka kb (h0 M stop perm one two)
lemma k8.induct {R} {goal:fd R} {M:(Nat→ List (fd R)→ Prop)} {s ws} (h:k8 goal s ws)
  (stop:M 0 [goal])
  (perm:∀ {s:Nat} {xs zs:List (fd R)},xs.Perm zs→ k8 goal s xs→ M s xs→ M s zs)
  (one:∀ {s:Nat} {a:fd R} {rest:List (fd R)} (save:Bool),k8 goal s (rm a :: fw save a rest)→ M s (rm a :: fw save a rest)→ M (s+1) (a::rest))
  (two:∀ {s:Nat} {a b:fd R} {rest:List (fd R)} (op ka kb:Bool),k8 goal s (fq op a b :: fw ka a (fw kb b rest))→ M s (fq op a b :: fw ka a (fw kb b rest))→ M (s+1) (a::b::rest)) : M s ws :=
  (h (fun s ws => k8 goal s ws∧M s ws)
  (⟨@k8.stop R goal  ,@stop  ⟩)
  (@fun s xs zs h0 h1 => ⟨@k8.perm R goal s xs zs h0 h1.1,@perm s xs zs h0 h1.1 h1.2⟩)
  (@fun s a rest save h0 => ⟨@k8.one R goal s a rest save h0.1,@one s a rest save h0.1 h0.2⟩)
  (@fun s a b rest op ka kb h0 => ⟨@k8.two R goal s a b rest op ka kb h0.1,@two s a b rest op ka kb h0.1 h0.2⟩)).2
lemma k8.recurse {R} {goal:fd R} {M:∀ (s:Nat) (ws:List (fd R)) (proof:k8 goal s ws),Prop}
  (stop:M 0 [goal] (@k8.stop R goal  ))
  (perm:∀ {s:Nat} {xs zs:List (fd R)} (h0:xs.Perm zs) (h1:k8 goal s xs) (ih:M s xs h1),M s zs (@k8.perm R goal s xs zs h0 h1))
  (one:∀ {s:Nat} {a:fd R} {rest:List (fd R)} (save:Bool) (h0:k8 goal s (rm a :: fw save a rest)) (ih:M s (rm a :: fw save a rest) h0),M (s+1) (a::rest) (@k8.one R goal s a rest save h0))
  (two:∀ {s:Nat} {a b:fd R} {rest:List (fd R)} (op ka kb:Bool) (h0:k8 goal s (fq op a b :: fw ka a (fw kb b rest))) (ih:M s (fq op a b :: fw ka a (fw kb b rest)) h0),M (s+1) (a::b::rest) (@k8.two R goal s a b rest op ka kb h0))
  {s ws} (h:k8 goal s ws) : M s ws h:=by
  have r:=k8.induct (M:=fun s ws => ∀ hh : k8 goal s ws,M s ws hh) h
    (fun  _ => @stop  )
    (@fun s xs zs h0 h1 h2 _ => @perm s xs zs h0 h1 (h2 h1))
    (@fun s a rest save h0 h1 _ => @one s a rest save h0 (h1 h0))
    (@fun s a b rest op ka kb h0 h1 _ => @two s a b rest op ka kb h0 (h1 h0))
  exact r h
lemma ju {R} (a:fd R) (xs) : lg (a::xs)=m1 a+lg xs:=by
  simp [lg]
lemma nq {R} (a:fd R) (xs) (k:Bool) : lg xs ≤ lg (fw k a xs):=by
  cases k <;> simp [fw,ju]
lemma n5 {R} {a:fd R} (h:fj a) : fj (rm a):=by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩
lemma qt {R} {a b:fd R} (op) (h:fj a) (g:fj b) :
    fj (fq op a b):=by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩
lemma qu {R} (op) {a b:fd R} {f5}
    (h:fj a∨fj b) (ha:f7 f5 a) (hb:f7 f5 b) :
    f7 f5 (fq op a b):=by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false,by funext x;simp [fq]⟩
    · simpa [fq] using hb
    · simpa [fq] using hb
    · exact Or.inr ⟨true,by funext x;simp [fq]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false,by funext x;simp [fq]⟩
    · simpa [fq] using ha
    · simpa [fq] using ha
    · exact Or.inr ⟨true,by funext x;simp [fq]⟩
lemma kj {R} {f5 v} (w:fd R) (h:f7 f5 v) :
    f7 (w::f5) v:=by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr
lemma tf {R} (roots:List (fd R)) {p f5 a} (hp:fi roots p f5)
    (ha:f7 f5 a) :
    ∃ q next,fi roots q next∧f7 next (rm a) ∧
        (∀ v,f7 f5 v→ f7 next v)∧q+m1 a ≤ p+1+m1 (rm a):=by
  classical
  by_cases c : fj a
  · exact ⟨p,f5,hp,Or.inr (n5 c),fun _ h => h,by simp [m1,c,n5 c]⟩
  · exact ⟨p+1,_,fi.one hp ha,Or.inl (by simp),fun _ h => kj _ h,by simp [m1,c]⟩
lemma tg {R} (roots:List (fd R)) {p f5 a b} (op) (hp:fi roots p f5)
    (ha:f7 f5 a) (hb:f7 f5 b) :
    ∃ q next,fi roots q next∧f7 next (fq op a b) ∧
        (∀ v,f7 f5 v→ f7 next v) ∧
        q+m1 a+m1 b ≤ p+1+m1 (fq op a b):=by
  classical
  by_cases c : fj a∨fj b
  · refine ⟨p,f5,hp,qu op c ha hb,fun _ h => h,?_⟩
    by_cases ca : fj a <;> by_cases cb : fj b
    · simp [m1,ca,cb,qt op ca cb]
    · simp [m1,ca,cb]
    · simp [m1,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬fj a:=fun h => c (Or.inl h)
    have cb : ¬fj b:=fun h => c (Or.inr h)
    exact ⟨p+1,_,fi.two op hp ha hb,Or.inl (by simp),fun _ h => kj _ h,
      by simp [m1,ca,cb]⟩
lemma ps {α : Type} {k:Bool} {x a : α} {xs} (h:x ∈ fw k a xs) :
    x=a∨x∈xs:=by cases k <;> simp_all [fw]
lemma sf {R} {goal:fd R} (nc : ¬fj goal) {s ws}
    (h:k8 goal s ws) (roots:List (fd R)) {p f5}
    (hp:fi roots p f5) (hs:m2 f5 ws) :
    ∃ q next,fi roots q next∧f7 next goal∧q+lg ws ≤ p+s:=by
  classical
  induction h using k8.recurse generalizing p f5 with
  | stop =>
    exact ⟨p,f5,hp,hs _ (by simp),by simp [lg,m1,nc]⟩
  | perm eq _ ih =>
    have hsub : m2 f5 _:=fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [lg,←(eq.map m1).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := tf roots hp (hs a (by simp))
    have ht : m2 T (rm a :: fw save a rest):=by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (ps hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen:=nq a rest save
    rw [ju] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := tg roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : m2 T (fq op a b :: fw ka a (fw kb b rest)):=by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases ps hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (ps hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen:=nq a (fw kb b rest) ka
    have hlen' := nq b rest kb
    rw [ju] at hl;refine ⟨q,W,hW,hv,?_⟩;rw [ju,ju];omega
def f0 {R S:Type} (rows:S→ R) (a:fd R) : fd S :=
  fun r => a (rows r)
lemma my {R S:Type} (rows:S→ R) (k:Bool) (a:fd R) (ws) :
    (fw k a ws).map (f0 rows) =
    fw k (f0 rows a) (ws.map (f0 rows)):=by
  cases k <;> simp [fw]
lemma rp {R S:Type} (rows:S→ R) {goal s ws} (h:k8 goal s ws) :
    k8 (f0 rows goal) s (ws.map (f0 rows)):=by
  induction h using k8.recurse with
  | stop => exact k8.stop
  | perm p _ ih => exact k8.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,my] at ih ⊢
    exact k8.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,my] at ih ⊢
    cases op
    · exact k8.two false ka kb ih
    · exact k8.two true ka kb ih
lemma k9 {R S:Type} (rows:S→ R) {goal s ws} (h:k8 goal s ws)
    (nc : ¬fj (f0 rows goal)) {roots:List (fd S)} {p f5 L}
    (hp:fi roots p f5) (hs:m2 f5 (ws.map (f0 rows)))
    (hl:∀ q bs,fi roots q bs→ f7 bs (f0 rows goal)→ L ≤ q) :
    L+lg (ws.map (f0 rows)) ≤ p+s:=by
  obtain ⟨q,bs,hq,ht,hle⟩ := sf nc (rp rows h) roots hp hs
  have hqle:=hl q bs hq ht
  omega
abbrev Row:=Fin 512
def f4 (a:Sig) : fd Row:=fun r => bit r a
def jo (f:fd Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
lemma kw (f:fd Row) (r:Row) : bit r (jo f)=f r:=by
  simp only [bit,jo,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn];simp [r.isLt]
lemma jc (v:Sig) : jo (f4 v)=v:=by
  apply BitVec.eq_of_getLsbD_eq;intro j hj;exact kw (f4 v) ⟨j,hj⟩
lemma kt (f:fd Row) : f4 (jo f)=f:=by
  funext r;exact kw f r
lemma rq (a:Sig) : f4 (neg a)=rm (f4 a):=by
  funext r;exact bit_neg _ _
lemma rr (d:Bool) (a b:Sig) :
    f4 (bin d a b)=fq d (f4 a) (f4 b):=by
  funext r
  cases d <;> exact bit_bin _ _ _ _
lemma pt {α β : Type} (f : α → β) (d:Bool) (a : α) (l:List α) :
    (fw d a l).map f=fw d (f a) (l.map f):=by cases d <;> rfl
lemma j4 {α : Type} (k:Bool) (a : α) (l:List α)
    (hn:l.Nodup) (ha:a ∉ l) : (fw k a l).Nodup:=by cases k <;> simp [fw,hn,ha]
lemma kx (k:Bool) (a:Sig) (l:List Sig) :
    (fw k a l).toFinset=if k then insert a l.toFinset else l.toFinset:=by
  cases k <;> simp [fw]
lemma pu {T:Sig} {k u S} (h:Live T k u S) (v:List Sig)
    (hv:v.Nodup) (eqv:v.toFinset=S) : k8 (f4 T) k (v.map f4):=by
  classical
  induction h using Live.recurse generalizing v with
  | stop hp =>
    have eq : [T].Perm v:=by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv;simpa [eqv]
    exact k8.perm (eq.map _) k8.stop
  | @unary k u U a ha gj _ ih =>
    let rest:=(U.erase a).toList
    let save:=decide (a ∈ U)
    let tail:=fw save a rest
    have er : rest.toFinset=U.erase a:=by simp [rest]
    have hm : a ∉ rest:=by simp [rest]
    have hr : rest.Nodup:=Finset.nodup_toList _
    have ht : tail.toFinset=U:=by
      rw [show tail=fw save a rest by rfl,kx,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd:=j4 save a rest hr hm
    have hf : neg a ∉ tail:=by
      intro hz;exact gj (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress:=ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,pt,rq] at progress
    have perm : (a::rest).Perm v:=by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv;simp [er,eqv]
    exact k8.perm (perm.map _) (k8.one save progress)
  | @binary k u U a b d ha hb hab gj _ ih =>
    let rest:=((U.erase a).erase b).toList
    let ka:=decide (a ∈ U)
    let kb:=decide (b ∈ U)
    let mid:=fw kb b rest
    let tail:=fw ka a mid
    have er : rest.toFinset=(U.erase a).erase b:=by simp [rest]
    have ar : a ∉ rest:=by simp [rest]
    have br : b ∉ rest:=by simp [rest]
    have hr : rest.Nodup:=Finset.nodup_toList _
    have bm:=j4 kb b rest hr br
    have am : a ∉ mid:=by cases h : kb <;> simp [mid,fw,h,hab,ar]
    have nd:=j4 ka a mid bm am
    have ht : tail.toFinset=U:=by
      change (fw ka a (fw kb b rest)).toFinset=U;rw [kx,kx,er];ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail:=by
      intro hz;exact gj (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress:=ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change k8 _ _ ((bin d a b::fw ka a (fw kb b rest)).map f4) at progress;rw [List.map_cons,pt,pt,rr] at progress
    have perm : (a::b::rest).Perm v:=by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv;ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact k8.perm (perm.map _) (k8.two d ka kb progress)
lemma vg (f:fd Row) : jo (rm f)=neg (jo f):=by
  rw [←jc (neg (jo f)),rq,kt]
lemma vh (d:Bool) (f g:fd Row) :
    jo (fq d f g)=bin d (jo f) (jo g):=by
  rw [←jc (bin d (jo f) (jo g)),rr,kt,kt]
lemma jd {f5:List (fd Row)} {a} (h:f7 f5 a) :
    fg (f5.map jo) (jo a):=by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : jo (fun _ => false)=zero:=by
        apply BitVec.eq_of_getLsbD_eq;intro j hj;exact (kw _ ⟨j,hj⟩).trans (gx ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : jo (fun _ => true)=one:=by
        apply BitVec.eq_of_getLsbD_eq;intro j hj;exact (kw _ ⟨j,hj⟩).trans (lf ⟨j,hj⟩).symm
      exact fun hp => hp.2 z
lemma ya {w a} (ha:fg w a) :
    fg w (neg a)∨pi w (neg a):=by
  rcases h6 ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 m0.1)
  · exact Or.inl (Or.inr fun h => h.1 m0.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
lemma r8 {w:List Sig} {z:Sig} {T k t S} (h:Live T k t S)
    (hz:fg w z∨pi w z) (hs:∀ a ∈ S,a ∈ z::w) :
    ∃ k' t' S',k' ≤ k+1∧Live T k' t' S' ∧ ∀ a ∈ S',a ∈ w:=by
  apply vf h hz;intro a hm;simpa [or_comm] using hs a hm
lemma px {roots:List (fd Row)} {p f5}
    (h:fi roots p f5) {T k t S} (run:Live T k t S)
    (sub:∀ a ∈ S,a ∈ f5.map jo) :
    ∃ l v U,l ≤ p+k∧Live T l v U ∧ ∀ a ∈ U,a ∈ roots.map jo:=by
  induction h using fi.recurse generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p f5 a h ih ha =>
    rw [List.map_cons,vg] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := r8 run (ya (jd ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p f5 a b d h ih ha hb =>
    rw [List.map_cons,vh] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := r8 run (y8 d (jd ha) (jd hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
lemma n0 {roots:List Sig} {p f5 T} (hp:proper T)
    (h:fi (roots.map f4) p f5) (hit:f7 f5 (f4 T)) :
    ∃ k t S,k ≤ p∧Live T k t S ∧ ∀ a ∈ S,a ∈ roots:=by
  have hm:=jd hit
  rw [jc] at hm
  have mem:=hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := px h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩;simpa [List.map_map,Function.comp_def,jc] using hs
lemma kc {T k t S} (h:Live T k t S) {r s:Row}
    (diff:bit r T ≠ bit s T) : ∃ a ∈ S,bit r a ≠ bit s a:=by
  induction h using Live.recurse with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a=bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq;exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩
lemma raw_required {T k t S} (h:Live T k t S) (roots:List Sig) (a:Sig)
    (sub:∀ v ∈ S,v ∈ roots) (r s:Row) (diff:bit r T ≠ bit s T)
    (y3:∀ v ∈ roots,v ≠ a→ bit r v=bit s v) : a ∈ S:=by
  obtain ⟨v,hv,hd⟩ := kc h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (y3 v (sub v hv) veq))
def inputs : List Sig:=[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig:=0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def sample (r:Row) (j:Fin 9):=bit r (inputs.getD j.val zero)
def edge (x:Fin 9→ Bool) : Bool :=
  (x 0&&x 1)||(x 1&&x 2)||(x 2&&x 3)||(x 3&&x 4)||(x 4&&x 0) ||
  (x 0&&x 5)||(x 1&&x 6)||(x 2&&x 7)||(x 3&&x 8)||(x 5&&x 7) ||
  (x 6&&x 8)||(x 8&&x 5)
lemma edge_table : ∀ r : Row,bit r graph=edge (sample r):=by decide +kernel
lemma graph_proper : proper graph:=by unfold proper;decide +kernel
lemma input_list : List.ofFn (fun j:Fin 9 => inputs.getD j.val zero)=inputs:=rfl
lemma sampled (r:Row) : List.ofFn (sample r)=inputs.map (bit r):=by
  rw [←input_list];rw [List.map_ofFn];rfl
def neighbor (i:Fin 9) : Nat:=[4,2,1,2,0,0,1,2,3].getD i.val 0
def absentRow (i:Fin 9) : Row:=Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i:Fin 9) : Row:=Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))
def fv (f:Row→ Row) (a:Sig):=jo fun r => bit (f r) a
lemma g5 (f:Row→ Row) (a:Sig) (r:Row) :
    bit r (fv f a)=bit (f r) a:=kw _ _
lemma j2 (f:Row→ Row) (a:Sig) :
    f4 (fv f a)=f0 f (f4 a):=by funext r;exact g5 f a r
lemma py (f:Row→ Row) (a:Sig) : fv f (neg a)=neg (fv f a):=by
  apply BitVec.eq_of_getLsbD_eq;intro j hj;change bit ⟨j,hj⟩ (fv f (neg a))=bit ⟨j,hj⟩ (neg (fv f a));rw [g5,bit_neg,bit_neg,g5]
lemma pz (f:Row→ Row) (d:Bool) (a b:Sig) :
    fv f (bin d a b)=bin d (fv f a) (fv f b):=by
  apply BitVec.eq_of_getLsbD_eq;intro j hj;change bit ⟨j,hj⟩ (fv f (bin d a b))=bit ⟨j,hj⟩ (bin d (fv f a) (fv f b));rw [g5,bit_bin,bit_bin,g5,g5]
lemma th (f:Row→ Row) (onto:Function.Surjective f) :
    Function.Injective (fv f):=by
  intro a b h;apply BitVec.eq_of_getLsbD_eq;intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he:=congrArg (bit r) h
  change bit ⟨j,hj⟩ a=bit ⟨j,hj⟩ b;rw [g5,g5,hr] at he;exact he
lemma ky (f:Row→ Row) : fv f zero=zero∧fv f one=one:=by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (g5 f zero ⟨j,hj⟩).trans ((gx _).trans (gx ⟨j,hj⟩).symm)
  · exact (g5 f one ⟨j,hj⟩).trans ((lf _).trans (lf ⟨j,hj⟩).symm)
lemma sg {T k t S} (h:Live T k t S) (f:Row→ Row) (onto:Function.Surjective f) :
    Live (fv f T) k t (S.image (fv f)):=by
  have inj:=th f onto
  obtain ⟨fz,fo⟩ := ky f
  have pp (v) (p:proper v) : proper (fv f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.recurse with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have gj : fv f (neg a) ∉ (insert a U).image (fv f):=by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,py] at gj ih ⊢
    exact Live.unary (pp _ hp) gj ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have gj : fv f (bin d a b) ∉ (insert a (insert b U)).image (fv f):=by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,pz] at gj ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) gj ih
lemma mr {T k t S} (h:Live T k t S) (none:t=0) {r s:Row}
    (pos:bit r T=true) (negRow:bit s T=false) :
    ∃ a ∈ S,bit r a=true∧bit s a=false:=by
  induction h using Live.recurse with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩
def gq (roots:List Sig) (T:Sig) (L:Nat) : Prop :=
  ∀ p f5,fi (roots.map f4) p f5→ f7 f5 (f4 T)→ L ≤ p
def jv (T:Sig) (cap:Nat) (S:Finset Sig) : Prop :=
  ∀ k t,k ≤ cap→ ¬Live T k t S
def mj (T:Sig) (roots:List Sig) (a:Sig) : Prop :=
  ∃ r s : Row,bit r T ≠ bit s T ∧ ∀ v ∈ roots,v ≠ a→ bit r v=bit s v
lemma kz {roots T L} (hp:proper T)
    (x8:∀ a ∈ roots,mj T roots a)
    (noRun:jv T L roots.toFinset) : gq roots T (L+1):=by
  intro p f5 h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := n0 hp h ha
  have he : roots.toFinset=S:=by
    ext a;rw [List.mem_toFinset];refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := x8 _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! qq
  exact noRun k t (by omega) (he.symm ▸ run)
lemma m3 {v:Sig} (hv:proper v) : ¬fj (f4 v):=by
  rintro ⟨b,h⟩
  have hr : fg ([] : List Sig) v:=by
    have avail : f7 ([] : List (fd Row)) (f4 v):=Or.inr ⟨b,h⟩
    simpa only [List.map_nil,jc] using jd avail
  exact (hr.resolve_left (by simp)) hv
lemma si {R} (a b:List (fd R)) : lg (a++b)=lg a+lg b:=by
  simp [lg]
lemma q0 {R} (xs:List (fd R)) (hc:∀ x ∈ xs,fj x) :
    lg xs=xs.length:=by
  induction xs with
  | nil => simp [lg]
  | cons a xs ih =>
    have ha:=hc a (by simp)
    simp only [ju,List.length_cons,m1,if_pos ha,ih (fun x hx => hc x (by simp [hx]))];omega
lemma p6 {roots y5:List Sig} {T G:Sig} (pT:proper T) (pG:proper G)
    (r:Row→ Row) (eq:fv r T=G)
    (jg:∀ a ∈ roots,f7 (y5.map f4) (f4 (fv r a)))
    (ki:Finset Sig) (x7:∀ a ∈ ki,mj T roots a)
    (constant:∀ a ∈ ki,fj (f4 (fv r a)))
    (L:Nat) (j0:gq y5 G L) : gq roots T (L+ki.card):=by
  classical
  intro p f5 hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := n0 pT hh ha
  have subS : ki ⊆ S:=by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := x7 a hs
    exact raw_required run roots a sub i j hd hiso
  let pf:=ki.toList ++ (S \ ki).toList
  have nd : pf.Nodup:=by
    simp only [pf,List.nodup_append];refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩;intro a ha b hb he;subst b;exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : pf.toFinset=S:=by ext a;simp [pf,Finset.union_sdiff_of_subset subS]
  have run' := pu run pf nd fe
  have gc : f0 r (f4 T)=f4 G:=(j2 _ _).symm.trans (congrArg f4 eq)
  have supp : m2 (y5.map f4) ((pf.map f4).map (f0 r)):=by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←j2];exact jg a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound:=k9 r run' (gc ▸ m3 pG) fi.start supp
    (L:=L) (gc ▸ j0)
  have massLo : ki.card ≤ lg ((pf.map f4).map (f0 r)):=by
    simp only [pf,List.map_append,si]
    let xs:=(ki.toList.map f4).map (f0 r)
    have only : ∀ v ∈ xs,fj v:=by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←j2];exact constant _ (Finset.mem_toList.mp hmem)
    have sz:=q0 xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz;change ki.card ≤ lg xs+_;rw [sz];omega
  omega
def g9 (ws:List Sig) (a:Sig) (keep:Bool) : List Sig :=
  neg a :: fw keep a (ws.erase a)
def fk (ws:List Sig) (a b:Sig) (d ka kb:Bool) : List Sig :=
  bin d a b :: fw ka a (fw kb b ((ws.erase a).erase b))
lemma ns {l:List Sig} (h:l.Nodup) (a:Sig) : (l.erase a).toFinset=l.toFinset.erase a:=by
  ext x;simp [h.mem_erase_iff]
def Sep (T:Sig) (ks:Nat) (pos negRow:Fin ks→ Row)
    (asig:Sig→ BitVec ks × BitVec ks) : Prop :=
  (∀ i,bit (pos i) T=true∧bit (negRow i) T=false) ∧
  ∀ w i,(asig w).1.getLsbD i.val=bit (pos i) w ∧
    (asig w).2.getLsbD i.val=bit (negRow i) w
def g0 {n} (oriented:Bool) (s:BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2
def jg {n} (oriented:Bool) (sig:Sig→ BitVec n × BitVec n) : List Sig→ BitVec n
  | [] => 0
  | a::ws => g0 oriented (sig a) ||| jg oriented sig ws
lemma sj {n:Nat} {oriented:Bool} {sig:Sig→ BitVec n × BitVec n} {ws:List Sig} {i:Fin n} :
    (jg oriented sig ws).getLsbD i.val=true ↔
    ∃ a ∈ ws,(g0 oriented (sig a)).getLsbD i.val=true:=by
  induction ws with
  | nil => simp [jg]
  | cons a ws ih =>
    simp only [jg,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]
lemma sk {T k t S} (h:Live T k t S) {ws:List Sig} (he:ws.toFinset=S)
    {ks:Nat} {r s:Fin ks→ Row} {sig} (correct:Sep T ks r s sig)
    (oriented:Bool) (zeroNot:oriented=true→ t=0) :
    jg oriented sig ws=BitVec.allOnes ks:=by
  apply BitVec.eq_of_getLsbD_eq;intro j hj
  let i : Fin ks:=⟨j,hj⟩
  have yes:=(correct.1 i).1
  have no:=(correct.1 i).2
  rw [BitVec.getLsbD_allOnes];simp only [hj,decide_true];apply (sj (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := kc h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩;simp only [g0,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mr h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩;simp only [g0,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]
def p7 (raw:List Sig) (T d:Sig) (L:Nat) : Prop :=
  ∃ (f:Row→ Row) (roots:List Sig),(∀ r,bit (f r) d=true) ∧
    (∀ a ∈ raw,f7 (roots.map f4) (f0 f (f4 a))) ∧
    ¬fj (f0 f (f4 T)) ∧
    ∀ p f5,fi (roots.map f4) p f5→ f7 f5 (f0 f (f4 T))→ L ≤ p
def ga (d a:Sig):=a &&& d
def ff (d:Sig) (pool:List Sig) (a:Sig) :=
  let m:=ga d a
  m == zero||m == d||(pool.map (ga d)).any (fun v => v==m)
lemma vi {f:Row→ Row} {d a b:Sig} (dom:∀ r,bit (f r) d=true)
    (eq:ga d a=ga d b) :
    f0 f (f4 a)=f0 f (f4 b):=by
  funext r
  have h:=congrArg (bit (f r)) eq
  change bit (f r) a=bit (f r) b;simpa only [bit,ga,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using h
lemma p8 {f:Row→ Row} {d a:Sig} (dom:∀ r,bit (f r) d=true)
    (eq:ga d a=zero) : f0 f (f4 a)=fun _ => false:=by
  funext r
  have he:=congrArg (bit (f r)) eq
  change bit (f r) a=false;rw [gx] at he;simpa only [bit,ga,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using he
lemma q1 {f:Row→ Row} {d a:Sig} (dom:∀ r,bit (f r) d=true)
    (eq:ga d a=d) : f0 f (f4 a)=fun _ => true:=by
  funext r
  have he:=congrArg (bit (f r)) eq
  change bit (f r) a=true;rw [dom r] at he;simpa only [bit,ga,BitVec.getLsbD_and,show d.getLsbD (f r).val=true from dom r,
    Bool.and_true] using he
def jh (f:Row→ Row) (f5:List (fd Row)) (pool:List Sig) :=
  ∀ a ∈ pool,f7 f5 (f0 f (f4 a))
lemma g2 {f:Row→ Row} {d a:Sig} {f5 pool}
    (dom:∀ r,bit (f r) d=true) (supplyB:jh f f5 pool)
    (check:ff d pool a=true) : f7 f5 (f0 f (f4 a)):=by
  simp only [ff,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,p8 dom hz⟩
  · exact Or.inr ⟨true,q1 dom ho⟩
  · exact vi dom he ▸ supplyB v hv
abbrev jw:=Nat × Sig × Sig
def fb (c:jw) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def kk (d:Sig) (pool:List Sig) (c:jw) :=
  ff d pool c.2.1&&(c.1==2||ff d pool c.2.2)
lemma q2 {f:Row→ Row} {d:Sig} {roots f5 pool q}
    (dom:∀ r,bit (f r) d=true) (hp:fi roots q f5) (hs:jh f f5 pool)
    (c:jw) (l9:kk d pool c=true) :
    ∃ next,fi roots (q+1) next∧jh f next (fb c :: pool):=by
  have ok : ff d pool c.2.1=true∧(c.1==2||ff d pool c.2.2)=true:=by simpa only [kk,Bool.and_eq_true] using l9
  have ha:=g2 dom hs ok.1
  let z:=f0 f (f4 (fb c))
  have hz : fi roots (q+1) (z::f5):=by
    by_cases unary : c.1=2
    · change fi _ _ (f0 f (f4 (fb c)) :: _)
      rw [fb,if_pos unary,rq];exact fi.one hp ha
    · have hb : ff d pool c.2.2=true:=by simpa [unary] using ok.2
      have hz' := fi.two (c.1==1) hp ha (g2 dom hs hb)
      change fi _ _ (f0 f (f4 (fb c)) :: _);rw [fb,if_neg unary,rr]
      have comm (b:Bool) (v w:fd Row) : f0 f (fq b v w)=fq b (f0 f v) (f0 f w):=by cases b <;> rfl
      rw [comm];exact hz'
  refine ⟨_,hz,?_⟩;intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact kj _ (hs _ hm)
def kl (d:Sig) (pool:List Sig) : List jw→ Option (List Sig)
  | [] => some pool
  | c::cs => if kk d pool c then kl d (fb c::pool) cs else none
lemma m4 {d:Sig} {f:Row→ Row} (dom:∀ r,bit (f r) d=true)
    {roots f5 q pool} (hp:fi roots q f5) (hs:jh f f5 pool)
    (cs:List jw) {result} (ok:kl d pool cs=some result) :
    ∃ next,fi roots (q+cs.length) next∧jh f next result:=by
  induction cs generalizing f5 q pool with
  | nil => cases ok;exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [kl] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := q2 dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction
def f2 (d a:Sig):=ga d a == zero||ga d a == d
lemma lw {d:Sig} {f:Row→ Row} (dom:∀ r,bit (f r) d=true)
    (ws:List Sig) : ws.countP (f2 d) ≤ lg ((ws.map f4).map (f0 f)):=by
  classical
  induction ws with
  | nil => simp [lg]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,ju]
    cases h : f2 d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : fj (f0 f (f4 a)):=by
        have hh : ga d a=zero∨ga d a=d:=by simpa only [f2,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,p8 dom hz⟩
        · exact ⟨true,q1 dom ho⟩
      simpa [m1,hc,Nat.add_comm] using Nat.succ_le_succ ih
def pj (d:Sig) (L k p:Nat) (pool ws:List Sig) :=
  decide (k+p < L+ws.countP (f2 d))&&ws.all (ff d pool)
lemma qv {raw T d L} (slice:p7 raw T d L) (cs:List jw)
    {pool ws cap} (built:kl d raw cs=some pool)
    (nd:ws.Nodup) (cut:pj d L cap cs.length pool ws=true) :
    jv T cap ws.toFinset:=by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨f5,hr,hs⟩ := m4 dom (fi.start (roots:=roots.map f4)) base cs built
  simp only [pj,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : m2 f5 ((ws.map f4).map (f0 f)):=by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact g2 dom hs (List.all_eq_true.mp all a ha)
  have b:=k9 f (pu h ws nd rfl) nc hr coveredS lo
  have massLo:=lw dom ws
  have hu:=ineq
  simp only [Nat.zero_add] at b;omega
abbrev mu:=Sig × Sig × Row
def pk (d r:Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def r9 (d:Row) : Row:=Fin.ofNat 512 (512-d.val)
def rt (m:mu) (r:Row) : Row :=
  if bit r m.1 then pk m.2.2 r else if bit r m.2.1 then pk (r9 m.2.2) r else r
def mux (m a b:Sig):=(m &&& a) ||| (~~~m &&& b)
def q3 (m:mu) (a:Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (r9 m.2.2).val) a)
lemma vj (d r:Row) (a:Sig) : bit r (a.rotateRight d.val)=bit (pk d r) a:=by
  unfold bit;rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [pk,h,r.isLt]
lemma x9 (p x y:Bool) : (p&&x || !p&&y)=(if p then x else y):=by cases p <;> simp
lemma yb (r:Row) (m a b:Sig) :
    bit r (mux m a b)=if bit r m then bit r a else bit r b:=by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact x9 _ _ _
lemma xa (r:Row) (m:mu) (a:Sig) : bit r (q3 m a)=bit (rt m r) a:=by
  simp only [q3,yb,vj,rt]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl
def g6 (ms:List mu) (r:Row):=ms.foldl (fun j m => rt m j) r
def movedWord (ms:List mu) (a:Sig):=ms.foldr q3 a
lemma l0 (ms:List mu) (a:Sig) (r:Row) :
    bit r (movedWord ms a)=bit (g6 ms r) a:=by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (xa r m _).trans (ih _)
lemma gy (ms:List mu) (a:Sig) : movedWord ms a=fv (g6 ms) a:=by
  apply BitVec.eq_of_getLsbD_eq;intro j hj;exact (l0 ms a ⟨j,hj⟩).trans (g5 _ _ ⟨j,hj⟩).symm
def q4 (roots:List Sig) (w:Sig):=w==zero||w==one||roots.contains w
lemma sl {roots w} (ok:q4 roots w=true) :
    f7 (roots.map f4) (f4 w):=by
  simp only [q4,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext gx⟩
  · exact Or.inr ⟨true,funext lf⟩
  · exact Or.inl (List.mem_map_of_mem hm)
def k5 (ms:List mu) (raw:List Sig) (T:Sig) (base:List Sig) (G:Sig) :=
  movedWord ms T == G&&raw.all (fun a => q4 base (movedWord ms a))
lemma m5 {ms raw T base G} (ok:k5 ms raw T base G=true) :
    fv (g6 ms) T=G ∧
    ∀ a ∈ raw,f7 (base.map f4) (f4 (fv (g6 ms) a)):=by
  simp only [k5,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,gy] at ok;exact ⟨ok.1,fun a ha => sl (ok.2 a ha)⟩
lemma vk {ms raw T base G L} (ok:k5 ms raw T base G=true)
    (pT:proper T) (pG:proper G) (hL:gq base G L) : gq raw T L:=by
  obtain ⟨eq,supp⟩ := m5 ok
  simpa using p6 pT pG (g6 ms) eq supp ∅ (by simp) (by simp) L hL
lemma qw {ms raw T base G L d} (ok:k5 ms raw T base G=true)
    (all:movedWord ms d=one) (properG:proper G) (hL:gq base G L) :
    p7 raw T d L:=by
  obtain ⟨eq,supp⟩ := m5 ok
  have obs : f0 (g6 ms) (f4 T)=f4 G :=
    (j2 _ _).symm.trans (congrArg f4 eq)
  refine ⟨g6 ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←l0,all,lf]
  · intro a ha
    rw [←j2];exact supp a ha
  · rw [obs]
    exact m3 properG
  · rw [obs]
    exact hL
def q5 (T:Sig) (roots:List Sig) (a:Sig) (rs:Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a||bit rs.1 w == bit rs.2 w)
lemma q6 {T roots a rs} (ok:q5 T roots a rs=true) : mj T roots a:=by
  simp only [q5,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok;exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩
def g4 (T:Sig) (raw:List Sig) (xs:List (Sig × Row × Row)) :=
  xs.all (fun a => q5 T raw a.1 a.2)
lemma kg {T raw xs} (ok:g4 T raw xs=true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset,mj T raw a:=by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact q6 (List.all_eq_true.mp ok _ hm)
lemma p9 {raw T} (properT:proper T) (xs:List (Sig × Row × Row))
    (ok:g4 T raw xs=true) :
    gq raw T ((xs.map Prod.fst).toFinset.card-1):=by
  intro p f5 hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := n0 properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card:=by
    apply Finset.card_le_card;intro a ha
    obtain ⟨r,s,hd,iso⟩ := kg ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound:=(mi run).2
  omega
def nt (ms:List mu) (T:Sig) (raw:List Sig) (base:List Sig) (G:Sig)
    (xs:List (Sig × Row × Row)) :=
  k5 ms raw T base G&&g4 T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero||movedWord ms a.1 == one)
lemma yc {ms T raw base G xs L} (ok:nt ms T raw base G xs=true)
    (properT:proper T) (properG:proper G) (low:gq base G L) :
    gq raw T (L+(xs.map Prod.fst).toFinset.card):=by
  simp only [nt,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := m5 ok.1.1
  apply p6 properT properG _ eq supp _ (kg ok.1.2) _ L low;intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh:=List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,gy] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext gx⟩
  · rw [h]
    exact ⟨true,funext lf⟩
def m6 (m:Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m:Nat):=(m6 m).map Prod.snd
def q7 (m j:Nat):=if m.testBit j then inputs.getD j zero else zero
def graphGoal (m:Nat) : Sig :=
  let x:=q7 m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def cube0 : Nat→ Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat→ Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat→ Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def kh (z o:Nat) : Sig :=
  let fixed:=z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def ru (z o:Nat) : List mu :=
  (List.range 9).filterMap fun j =>
    let x:=inputs.getD j zero
    let step:=Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v:Nat) : mu :=
  let i:=v &&& 15
  let j:=v >>> 4
  let a:=inputs.getD i zero
  let b:=inputs.getD j zero
  let d:=(1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)
def n6 (mask:Nat) : List (Sig × Row × Row) :=
  (m6 mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))
def ji (m hints:Nat) : List (Sig × Row × Row) :=
  (m6 m).map fun (i,a) =>
    let r:=1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))
def gr (T:Sig):=T != zero&&T != one
lemma j5 (T:Sig) (h:gr T=true) : proper T:=by
  simpa only [gr,proper,Bool.and_eq_true,bne_iff_ne] using h
def q8 (m hints L:Nat) :=
  let xs:=ji m hints
  gr (graphGoal m)&&g4 (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
lemma size_of {m hints L} (h:q8 m hints L=true) :
    gq (vars m) (graphGoal m) L:=by
  simp only [q8,Bool.and_eq_true,decide_eq_true_eq] at h;intro p f5 hr ha;exact h.2.trans (p9 (j5 _ h.1.1) _ h.1.2 p f5 hr ha)
abbrev ColumnInfo:=Nat × Nat × Nat × Nat × Nat
def rv (m z o:Nat):=m ^^^ (m &&& (z ||| o))
def l1 (m:Nat) (c:ColumnInfo) (j0:Nat→ Nat) : Bool :=
  let (z,o,q,s,L):=c
  let ms:=ru z o
  let free:=rv m z o
  let G:=movedWord ms (graphGoal m)
  let xs:=n6 s
  let count:=(xs.map Prod.fst).toFinset.card
  gr G&&k5 ms (vars m) (graphGoal m) (vars free) G &&
    (movedWord ms (kh z o)==one) &&
    (if q=0 then g4 G (vars free) xs&&decide (L ≤ count-1)
     else gr (graphGoal q) &&
       nt (ru (rv free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ j0 q+count))
lemma ra {m:Nat} (c:ColumnInfo) (j0:Nat→ Nat)
    (l9:∀ q,gq (vars q) (graphGoal q) (j0 q))
    (ok:l1 m c j0=true) : p7 (vars m) (graphGoal m) (kh c.1 c.2.1) c.2.2.2.2:=by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms:=ru z o
  let free:=rv m z o
  let G:=movedWord ms (graphGoal m)
  let xs:=n6 s
  change (((gr G&&k5 ms (vars m) (graphGoal m) (vars free) G) &&
    (movedWord ms (kh z o)==one))&&_)=true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok;apply qw ok.1.1.2 ok.1.2 (j5 _ ok.1.1.1);intro p f5 hr ha
  have hh:=ok.2
  by_cases hq : q=0
  · simp only [l1,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (p9 (j5 _ ok.1.1.1) xs hh.1 p f5 hr ha)
  · simp only [l1,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (yc hh.1.2 (j5 _ ok.1.1.1) (j5 _ hh.1.1) (l9 q) p f5 hr ha)
def ml (old rep:Nat) (swaps:List Nat) :=
  gr (graphGoal old)&&gr (graphGoal rep) &&
    k5 (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
lemma ti {old rep L swaps} (ok:ml old rep swaps=true)
    (h:gq (vars rep) (graphGoal rep) L) : gq (vars old) (graphGoal old) L:=by
  simp only [ml,Bool.and_eq_true] at ok;exact vk ok.2 (j5 _ ok.1.1) (j5 _ ok.1.2) h
def boundsBefore (lu:List (Nat × Nat)) (q:Nat) :=
  ((lu.find? (fun a => a.1 == q)).map Prod.snd).getD 0
lemma before_sound (lu:List (Nat × Nat))
    (sound:∀ e ∈ lu,gq (vars e.1) (graphGoal e.1) e.2) (q:Nat) :
    gq (vars q) (graphGoal q) (boundsBefore lu q):=by
  unfold boundsBefore
  cases h : lu.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he:=List.mem_of_find?_eq_some h
    have hit : (fun a:Nat × Nat => a.1 == q) e=true:=List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q:=beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he
abbrev fs:=(Sig) × (Nat) × (Nat) × (List Sig)
abbrev fs.domain (c:fs) : Sig:=c.1
abbrev fs.bound (c:fs) : Nat:=c.2.1
abbrev fs.paid (c:fs) : Nat:=c.2.2.1
abbrev fs.wires (c:fs) : List Sig:=c.2.2.2
def jm (raw:List Sig) (T:Sig) (c:fs) :=
  ∃ (f:Row→ Row) (roots:List Sig) (f5:List (fd Row)),
    (∀ r,bit (f r) c.domain=true) ∧ ¬fj (f0 f (f4 T)) ∧
    (∀ q ws,fi (roots.map f4) q ws→ f7 ws (f0 f (f4 T))→ c.bound ≤ q) ∧
    fi (roots.map f4) c.paid f5∧jh f f5 c.wires∧True
lemma sm {raw T d lb} (h:p7 raw T d lb) (cs:List jw) {ws}
    (build:kl d raw cs=some ws) : jm raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,j0⟩ := h
  obtain ⟨f5,hr,hs⟩ := m4 dom (fi.start (roots:=roots.map f4)) sup cs build
  exact ⟨f,roots,f5,dom,nc,j0,by simpa using hr,hs,trivial⟩
lemma qx {raw T c} (l9:jm raw T c) (k:Nat) (rest:List Sig)
    (mh:jw) (paid:Bool)
    (known:∀ a ∈ rest,ff c.domain c.wires a=true)
    (buy:if paid then kk c.domain c.wires mh=true
       else ff c.domain c.wires (fb mh)=true)
    (bound:k+c.paid+paid.toNat <
      c.bound+(fb mh :: rest).countP (f2 c.domain))
    (nd:(fb mh :: rest).Nodup) :
    jv T k (fb mh :: rest).toFinset:=by
  intro t num ht run
  obtain ⟨f,roots,f5,dom,nc,lo,hp,hs,_⟩ := l9
  let ws:=fb mh::rest
  have done (n:Nat) (out:List (fd Row)) (reach:fi (roots.map f4) n out)
      (zs:jh f out (fb mh::rest)) (le:n=c.paid+paid.toNat) : False:=by
    have jg : m2 out ((ws.map f4).map (f0 f)):=by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b:=k9 f (pu run ws nd rfl) nc reach jg lo
    have cm:=lw dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (f2 c.domain) at bound;omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl;intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact g2 dom hs buy
    · exact g2 dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := q2 dom hp hs mh buy
    apply done _ _ hr _ rfl;intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have avail:=g2 dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : ff c.domain c.wires a=true:=known _ hm
        have point : ∀ u ∈ c.wires,f7 out (f0 f (f4 u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact g2 dom point ha
      · exact Or.inr con
def gn (c:fs) (k:Nat) (rest:List Sig) (op:jw) :=
  let z:=fb op
  let te := !(ff c.domain c.wires z)
  ((k+c.paid+te.toNat < c.bound+(z::rest).countP (f2 c.domain)) &&
    rest.all (ff c.domain c.wires))&&(!te||kk c.domain c.wires op)
lemma kd {raw T c} (l9:jm raw T c) {k rest op}
    (nd:(fb op::rest).Nodup) (cut:gn c k rest op=true) :
    jv T k (fb op::rest).toFinset:=by
  let te := !(ff c.domain c.wires (fb op))
  apply qx l9 k rest op te _ _ _ nd
  · simp only [gn,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [gn,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : ff c.domain c.wires (fb op) <;> simp_all [te]
  · simp only [gn,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1
def m7 (raw:List Sig) (cs:List jw) (d:Sig) (lb:Nat) : Option fs :=
  (kl d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
lemma n7 {raw T d L cs c} (slice:p7 raw T d L)
    (h:m7 raw cs d L=some c) : jm raw T c:=by
  unfold m7 at h
  cases he : kl d raw cs with
  | none => simp [he,Option.map] at h
  | some pool =>
    rw [he] at h;change some _=some c at h
    injection h with h
    subst c;exact sm slice cs he
abbrev Bits:=BitVec 768
abbrev pl:=Bits × Bits
abbrev f9:=Sig × pl
def jj {n:Nat} (r:Fin n→ Row) (v:Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
lemma gb {n:Nat} (r:Fin n→ Row) (v:Sig) (i:Fin n) :
    (jj r v).getLsbD i.val=bit (r i) v:=by
  simp only [jj,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn];simp [i.isLt]
def jp (r s:Fin 768→ Row) (a:Sig) : pl:=(jj r a,jj s a)
def k6 (T:Sig) (r s:Fin 768→ Row) :=
  ∀ i,bit (r i) T=true∧bit (s i) T=false
lemma xb {T r s} (h:k6 T r s) : Sep T 768 r s (jp r s):=by
  exact ⟨h,fun a i => ⟨gb _ _ _,gb _ _ _⟩⟩
def fx (r s:Fin 768→ Row) (x:f9):=x.2=jp r s x.1
def tj (x:f9) : f9:=(neg x.1,~~~x.2.1,~~~x.2.2)
def tk (d:Bool) (x y:f9) : f9 :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)
lemma tl (r:Fin 768→ Row) (a:Sig) : jj r (neg a) = ~~~jj r a:=by
  apply BitVec.eq_of_getLsbD_eq;intro j hj
  have h:=gb r (neg a) ⟨j,hj⟩
  rw [bit_neg,←gb r a ⟨j,hj⟩] at h;simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
lemma tn (r:Fin 768→ Row) (d:Bool) (a b:Sig) :
    jj r (bin d a b)=if d then jj r a ||| jj r b else jj r a &&& jj r b:=by
  apply BitVec.eq_of_getLsbD_eq;intro j hj
  have h:=gb r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←gb r a ⟨j,hj⟩,←gb r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
lemma n8 {r s x} (h:fx r s x) : fx r s (tj x):=by
  change x.2=_ at h;simp only [fx,tj,jp,tl,h]
lemma n9 {r s x y} (d) (hx:fx r s x) (hy:fx r s y) :
    fx r s (tk d x y):=by
  change x.2=_ at hx;change y.2=_ at hy
  cases d <;> simp only [fx,tk,Bool.false_eq_true,ite_false,ite_true,jp,tn,hx,hy]
def gk (op:Nat) (x y:f9):=if op=2 then tj x else tk (op==1) x y
def f3 : f9:=(zero,0,0)
lemma nu (r s) : fx r s f3:=by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0:Bits).getLsbD j=(jj r zero).getLsbD j
    rw [show (jj r zero).getLsbD j=bit (r ⟨j,hj⟩) zero from gb _ _ ⟨j,hj⟩,gx]
    simp
  · change (0:Bits).getLsbD j=(jj s zero).getLsbD j
    rw [show (jj s zero).getLsbD j=bit (s ⟨j,hj⟩) zero from gb _ _ ⟨j,hj⟩,gx]
    simp
lemma lh {r s ws} (all:∀ v ∈ ws,fx r s v) (i:Nat) :
    fx r s (List.getD ws i f3):=by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact nu _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def lx (cols:Nat→ Bits) (i:Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j:Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
lemma li : ∀ (j:Fin 9) (r:Row),bit r (inputs.getD j.val zero)=r.val.testBit j.val:=by decide +kernel
lemma nv (cols:Nat→ Bits) (i:Fin 768) (j:Fin 9) :
    bit (lx cols i) (inputs.getD j.val zero)=(cols j.val).getLsbD i.val:=by
  rw [li];change (BitVec.ofBoolListLE (List.ofFn (fun h:Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val=_;simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn];simp [j.isLt]
def q9 (m:Nat) (p q:Nat→ Bits) : List f9 :=
  (m6 m).map (fun (j,a) => (a,p j,q j))
lemma qa {m j a} (h:(j,a) ∈ m6 m) :
    j<9∧a=inputs.getD j zero:=by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
lemma rx (m) (p q:Nat→ Bits) :
    ∀ a ∈ q9 m p q,fx (lx p) (lx q) a:=by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := qa hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (nv p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (gb _ _ ⟨i,hi⟩).symm
  · exact (nv q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (gb _ _ ⟨i,hi⟩).symm
def l2 (m:Nat) (v:Nat→ Bits) : Bits :=
  let x:=fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
lemma tp (m:Nat) (v:Nat→ Bits) (i:Fin 768) (j:Fin 9) :
    bit (lx v i) (q7 m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val:=by
  by_cases hh : m.testBit j.val=true
  · simpa [q7,hh] using nv v i j
  · simp [q7,hh,gx]
lemma ry (m:Nat) (v:Nat→ Bits) (i:Fin 768) :
    bit (lx v i) (graphGoal m)=(l2 m v).getLsbD i.val:=by
  have pos (j:Nat) (hj:j<9) : (q7 m j).getLsbD (lx v i).val=((if m.testBit j then v j else 0) : Bits).getLsbD i.val:=tp m v i ⟨j,hj⟩
  simp only [bit,graphGoal,l2,BitVec.getLsbD_and,BitVec.getLsbD_or];simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev vl:=Bits × Bits × Bits
def jx (z:Bits) (c:vl) : vl :=
  (z ||| c.1,(z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))
def ft (d:Bool) (v:List f9) : vl :=
  v.foldr (fun a c => jx (g0 d a.2) c) (0,0,0)
def k2 (c:vl) (a:Bits) : Bits:=c.1 &&& ~~~(c.2.1 &&& a)
def mm (c:vl) (a b:Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))
lemma yd (c:vl) (a:Bits) : k2 (jx a c) a=c.1:=by
  apply BitVec.eq_of_getLsbD_eq;intro i hi;simp only [k2,jx,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl
lemma ye (c:vl) (a b:Bits) : mm (jx a (jx b c)) a b=c.1:=by
  apply BitVec.eq_of_getLsbD_eq;intro i hi;simp only [mm,jx,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
lemma xc (c:vl) (a b:Bits) : jx a (jx b c)=jx b (jx a c):=by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi;simp only [jx,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [jx,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl
lemma sn (d:Bool) {l r:List f9} (h:l.Perm r) : ft d l=ft d r:=by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (jx (g0 d a.2)) ih
  | swap a b t => exact xc _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
lemma xd (d:Bool) (v:List f9) {r s} (good:∀ a ∈ v,fx r s a) :
    (ft d v).1=jg d (jp r s) (v.map Prod.fst):=by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (g0 d a.2 ||| (ft d v).1)=g0 d (jp r s a.1) ||| _;rw [show a.2=jp r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]
def jy (ws:List f9) (a:f9) (keep:Bool) :=
  if keep then ws else ws.erase a
def qb (ws:List f9) (a b:f9) (ka kb:Bool) :=
  jy (jy ws a ka) b kb
lemma m8 {ws:List f9} (a:f9) (ha:a ∈ ws) :
    ws.Perm (a::ws.erase a):=List.perm_cons_erase ha
lemma nw {ws:List f9} (d:Bool) (a:f9) (ha:a ∈ ws) (keep:Bool) :
    (ft d (jy ws a keep)).1 =
      (if keep then (ft d ws).1 else k2 (ft d ws) (g0 d a.2)):=by
  cases keep
  · change (ft d (ws.erase a)).1=k2 (ft d ws) _
    rw [sn d (m8 a ha)];exact (yd _ _).symm
  · rfl
lemma sp {ws:List f9} (a b:f9) (ha:a ∈ ws) (hb:b ∈ ws) (hne:a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b):=by
  have hm : b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (m8 a ha).trans (List.Perm.cons _ (m8 b hm))
lemma vm {ws:List f9} (d:Bool) (a b:f9) (ha:a ∈ ws) (hb:b ∈ ws)
    (ne:a ≠ b) (ka kb:Bool) :
    (ft d (qb ws a b ka kb)).1 =
      (if ka then (if kb then (ft d ws).1 else k2 (ft d ws) (g0 d b.2))
       else if kb then k2 (ft d ws) (g0 d a.2)
       else mm (ft d ws) (g0 d a.2) (g0 d b.2)):=by
  cases ka <;> cases kb
  · change (ft d ((ws.erase a).erase b)).1=mm (ft d ws) _ _
    rw [sn d (sp a b ha hb ne)];exact (ye _ _ _).symm
  · exact nw d a ha false
  · exact nw d b hb false
  · rfl
def sameWords (a b:List Sig):=(a.all (fun x => b.contains x))&&(b.all (fun x => a.contains x))
lemma sameWords_sound {xs ys} (h:sameWords xs ys=true) : xs.toFinset=ys.toFinset:=by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h;ext a;simp only [List.mem_toFinset];exact ⟨h.1 a,h.2 a⟩
def h9 (v:Sig) :=
  let n:=v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
abbrev s0:=vl × vl
def n1 (ws:List f9) : s0:=(ft false ws,ft true ws)
def n2 (c:s0) (d:Bool):=if d then c.2 else c.1
lemma tq (ws) (d:Bool) : n2 (n1 ws) d=ft d ws:=by cases d <;> rfl
def lj (v:vl) (a b:Bits) (un ka kb:Bool) :=
  if un then (if ka then v.1 else k2 v a) else
    if ka then (if kb then v.1 else k2 v b)
    else if kb then k2 v a else mm v a b
def jk (un ka kb:Bool) (a b:f9) (ws:List f9) :=
  if un then jy ws a ka else qb ws a b ka kb
lemma qy {ws:List f9} {a b:f9} (ha:a ∈ ws) (hb:b ∈ ws)
    (un ka kb d:Bool) (ne:un=false→ a≠b) :
    (ft d (jk un ka kb a b ws)).1 =
      lj (n2 (n1 ws) d) (g0 d a.2) (g0 d b.2) un ka kb:=by
  rw [tq]
  cases un
  · exact vm d a b ha hb (ne rfl) ka kb
  · exact nw d a ha ka
lemma lk (ws:List f9) (a:f9) (k:Bool) : (jy ws a k).Sublist ws:=by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
lemma nf (ws:List f9) (a b:f9) (un ka kb:Bool) :
    (jk un ka kb a b ws).Sublist ws:=by
  cases un
  · exact (lk _ _ _).trans (lk _ _ _)
  · exact lk _ _ _
lemma xe (ws:List f9) (a b:f9) (un ka kb:Bool) (ha:a ∈ ws) (hb:b ∈ ws)
    (ne:un=false→ a≠b) :
    (jk un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un||kb then 0 else 1):=by
  cases un
  · have hm : b ∈ ws.erase a:=(List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [jk,qb,jy,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [jk,jy,List.length_erase_of_mem ha]
def fc (op:Nat) (a b:f9):=gk op a b
def fl (op:Nat) (a b:f9) : jw:=(op,a.1,b.1)
lemma qc (op) (a b:f9) :
    (fc op a b).1=fb (fl op a b):=by
  by_cases h : op=2
  · simp [fc,gk,h,tj,fb,fl]
  · cases hh : op==1 <;> simp [fc,gk,h,hh,tk,fb,fl]
lemma qd {r s a b} (ha:fx r s a) (hb:fx r s b) (op:Nat) :
    fx r s (fc op a b):=by
  unfold fc gk;split
  · exact n8 ha
  · exact n9 _ ha hb
def gl (ws:List f9) (op:Nat) (a b:f9) (ka kb:Bool) :=
  (fc op a b).1 :: (jk (op==2) ka kb a b ws).map Prod.fst
lemma je {v:List Sig} {w:Sig} (a:Sig) (k:Bool) :
    w ∈ fw k a v ↔ (w=a∧k=true)∨w∈v:=by cases k <;> simp [fw]
lemma qe {v:List f9} (nd:v.Nodup) (a w:f9) (k:Bool) :
    w ∈ jy v a k ↔ w∈v∧(w≠a∨k=true):=by
  cases k <;> simp [jy,nd.mem_erase_iff,and_comm]
lemma ll {ws:List f9} (nd:(ws.map Prod.fst).Nodup) {a b:f9}
    (ha:a∈ws) (hb:b∈ws) (eq:a.1=b.1) : a=b:=by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail
lemma qf {ws:List f9} (nd:(ws.map Prod.fst).Nodup) {a b:f9}
    (ha:a ∈ ws) (hb:b ∈ ws) (un ka kb:Bool) (v:Sig) :
    v ∈ (jk un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst∧(v≠a.1∨ka=true)∧(un=true∨v≠b.1∨kb=true):=by
  have wn:=nd.of_map
  have dn:=wn.sublist (lk ws a ka)
  cases un <;> simp only [jk,Bool.false_eq_true,ite_false,ite_true,qb,List.mem_map,
    qe wn,qe dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (ll nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (ll nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (ll nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
lemma sq {ws:List f9} (nd:(ws.map Prod.fst).Nodup) {a:f9} (ha:a∈ws)
    (keep:Bool) :
    (gl ws 2 a a keep keep).toFinset=(g9 (ws.map Prod.fst) a.1 keep).toFinset:=by
  ext v;simp only [gl,g9,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    qf nd ha ha,je,nd.mem_erase_iff,fc,gk,tj,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av:=List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all
lemma s1 {ws:List f9} (nd:(ws.map Prod.fst).Nodup) {a b:f9}
    (ha:a∈ws) (hb:b∈ws) (ne:a.1≠b.1) (d ka kb:Bool) :
    (gl ws (if d then 1 else 0) a b ka kb).toFinset =
      (fk (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
  ext v
  have av:=List.mem_map_of_mem (f:=Prod.fst) ha
  have bv:=List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [gl,fk,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    qf nd ha hb,je,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,fc,gk,tk,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all
lemma qz (v:List Sig) (nd:v.Nodup) (a b:Sig) (d ka kb:Bool) :
    (fk v a b d ka kb).toFinset=(fk v b a d kb ka).toFinset:=by
  ext x;simp only [fk,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    je,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,k4 d b a]
  tauto
lemma s2 (r s:Row) (h:∀ a ∈ inputs,bit r a=bit s a) : r=s:=by
  apply Fin.ext;apply Nat.eq_of_testBit_eq;intro j
  by_cases hj : j<9
  · let i : Fin 9:=⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs:=by
      rw [← input_list];exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (li i r).symm.trans ((h _ hm).trans (li i s))
  · have le : 512 ≤ 2^j:=by
      change 2^9 ≤ 2^j;exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm
def n3 (p q:List mu):=inputs.all (fun a => movedWord p (movedWord q a) == a)
lemma pc {p q} (h:n3 p q=true) (r:Row) :
    g6 q (g6 p r)=r:=by
  apply s2;intro a ha;rw [←l0,←l0]
  have eq:=beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]
def qg (T:Sig) (p:List mu) :=
  (movedWord p T == T)&&n3 p p.reverse&&n3 p.reverse p
def fy (v:Nat) (upper:Nat):=2^769*upper+v
def f6 {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => fy (f x).toNat (f6 f xs)
def m9 : Nat→ Nat
  | 0 => 0
  | n+1 => fy 1 (m9 n)
lemma ny (x:Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
lemma vn (a b:Bits) (u v:Nat) :
    fy a.toNat u &&& fy b.toNat v=fy (a &&& b).toNat (u &&& v):=by
  apply Nat.eq_of_testBit_eq;intro i;simp only [fy,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (ny _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
lemma xf (a b:Bits) (u v:Nat) :
    fy a.toNat u ||| fy b.toNat v=fy (a ||| b).toNat (u ||| v):=by
  apply Nat.eq_of_testBit_eq;intro i;simp only [fy,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (ny _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
lemma vo (a b:Bits) (u v:Nat) :
    fy a.toNat u ^^^ fy b.toNat v=fy (a ^^^ b).toNat (u ^^^ v):=by
  apply Nat.eq_of_testBit_eq;intro i;simp only [fy,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (ny _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
lemma nz {α} (f g : α → Bits) (xs) :
    f6 f xs &&& f6 g xs=f6 (fun x => f x &&& g x) xs:=by
  induction xs with
  | nil => simp [f6]
  | cons a xs ih => simp only [f6,vn,ih]
lemma qh {α} (f g : α → Bits) (xs) :
    f6 f xs ||| f6 g xs=f6 (fun x => f x ||| g x) xs:=by
  induction xs with
  | nil => simp [f6]
  | cons a xs ih => simp only [f6,xf,ih]
lemma p0 {α} (f g : α → Bits) (xs) :
    f6 f xs ^^^ f6 g xs=f6 (fun x => f x ^^^ g x) xs:=by
  induction xs with
  | nil => simp [f6]
  | cons a xs ih => simp only [f6,vo,ih]
lemma vp {α} (a:Bits) (xs:List α) :
    m9 xs.length*a.toNat=f6 (fun _ => a) xs:=by
  induction xs with
  | nil => simp [m9,f6]
  | cons v xs ih => simp only [List.length_cons,m9,f6,fy,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]
def mn (r packed:Nat):=((packed+r) >>> 768) &&& r
lemma xg (n i:Nat) (hi:i<n) : (m9 n).testBit (769*i)=true:=by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [m9,fy,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i:=by omega
      have ge : ¬769*(i+1)<769:=by omega
      simp only [ge,ite_false,di];exact ih _ (by omega)
set_option maxRecDepth 8192 in
lemma xh (a:Bits) : (a.toNat+1).testBit 768=(a==BitVec.allOnes 768):=by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim:=a.isLt
    have ne : a.toNat ≠ 2^768-1:=by
      intro eq;apply h;apply BitVec.eq_of_toNat_eq;simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768:=by omega
    rw [Nat.testBit_eq_false_of_lt lt];exact (beq_eq_false_iff_ne.mpr h).symm
set_option maxRecDepth 8192 in
lemma yf {α} (f : α → Bits) (xs:List α) (i:Nat) (hi:i<xs.length) :
    (mn (m9 xs.length) (f6 f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768):=by
  simp only [mn,Nat.testBit_and,Nat.testBit_shiftRight,xg _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [f6,List.length_cons,m9,fy]
    have sum (u v x:Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1):=by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have:=(f a).isLt;omega)]
    have hi' : i < xs.length+1:=hi
    cases i with
    | zero => simpa using xh (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769:=by omega
      have di : 769*(i+1)+768-769=769*i+768:=by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ];apply ih i (by omega)
abbrev l3:=Nat × Nat
abbrev mo:=Nat × Nat × Nat
def j6 {α} (s : α → pl) (xs:List α) : l3 :=
  (f6 (fun x => (s x).1) xs,f6 (fun x => (s x).2) xs)
def jz {α} (c : α → vl) (xs:List α) : mo :=
  (f6 (fun x => (c x).1) xs,f6 (fun x => (c x).2.1) xs,
   f6 (fun x => (c x).2.2) xs)
def gm (d:Bool) (a:l3) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2
lemma sr (a b:Bits) : a ^^^ (a &&& b)=a &&& ~~~b:=by
  apply BitVec.eq_of_getLsbD_eq;intro i hi;simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
lemma ku {α} (s : α → pl) (xs:List α) (d:Bool) :
    gm d (j6 s xs)=f6 (fun x => g0 d (s x)) xs:=by
  cases d <;> simp only [gm,j6,g0,Bool.false_eq_true,ite_false,ite_true,nz,p0,sr]
def mc (full:Nat) (op:Nat) (a b:l3) : l3 :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
lemma yg (a:Bits) : BitVec.allOnes 768 ^^^ a = ~~~a:=BitVec.allOnes_xor
lemma vq {α} (a b : α → f9) (xs:List α) (op:Nat) :
    mc (m9 xs.length*(BitVec.allOnes 768).toNat) op
      (j6 (fun x => (a x).2) xs) (j6 (fun x => (b x).2) xs) =
    j6 (fun x => (fc op (a x) (b x)).2) xs:=by
  by_cases un : op=2
  · simp only [mc,un,ite_true,j6,vp,p0,yg,fc,gk,tj]
  · by_cases one : op=1 <;> simp [mc,un,one,j6,qh,nz,fc,gk,tk]
def lm (c:mo) (a b:Nat) (un ka kb:Bool) :=
  let qs:=fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let y6:=c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else qs a)
  else if ka then (if kb then c.1 else qs b)
  else if kb then qs a else y6
lemma r1 {α} (c : α → vl) (a b : α → Bits) (xs:List α) (un ka kb:Bool) :
    lm (jz c xs) (f6 a xs) (f6 b xs) un ka kb =
    f6 (fun x => lj (c x) (a x) (b x) un ka kb) xs:=by
  cases un <;> cases ka <;> cases kb <;>
    simp only [lm,jz,nz,qh,p0,sr,lj,k2,mm,
      Bool.false_eq_true,ite_false,ite_true]
def ng {α : Type} (f : α → Bool) (mask:Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0)||f x)&&ng f (mask >>> 769) xs
lemma vr {α} (f : α → Bool) (mask:Nat) (xs:List α) (i:Nat) (hi:i<xs.length)
    (bitOn:mask.testBit (769*i)=true) (ok:ng f mask xs=true) : f xs[i]=true:=by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0:=by intro e;simp [e] at bitOn
    simp only [ng,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0:=by
        intro he
        have at0:=congrArg (fun n:Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0;change mask.testBit 0=true at bitOn;simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2;simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn
abbrev rb:=Nat × Nat × Nat × List l3 × mo × mo
def l4 (b:rb) (i:Nat):=b.2.2.2.1.getD i (0,0)
def fm (p:f9→ Bool) (a:f9) (keep:Bool) :=
  if keep then 0 else (p a).toNat
lemma rc (p:f9→ Bool) (ws:List f9) (a:f9) (keep:Bool) :
    ws.countP p ≤ (jy ws a keep).countP p+fm p a keep:=by
  cases keep
  · simp only [jy,Bool.false_eq_true,ite_false,fm,List.countP_erase]
    split
    next h => simp [h.2];omega
    next => omega
  · simp [jy,fm]
lemma vs (p:f9→ Bool) (ws:List f9) (a b:f9) (un ka kb:Bool) :
    ws.countP p - fm p a ka - fm p b (un||kb) ≤
    (jk un ka kb a b ws).countP p:=by
  have h1:=rc p ws a ka
  have h2:=rc p (jy ws a ka) b kb
  cases un <;> simp only [jk,qb,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [fm];omega
def listPieces {α} (f : α → Bool) (xs:List α) : Nat→ Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d∧listPieces f (xs.drop (xs.length/2)) d
lemma listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true:=by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true:=by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
def opW (nraw d:Nat) : Nat:=if nraw+d ≤ 17 then 8 else 9
def qi : Nat→ Nat→ Nat→ Nat × Nat
  | 0,idx,b => (idx,b)
  | n+1,idx,b => if idx < b then (idx,b) else qi n (idx - b) (b+1)
def rd (ow c:Nat) : Nat × Nat × Nat :=
  if ow == 8 then
    if c < 16 then (2,c,c)
    else if c < 136 then let (a,b):=qi 15 (c - 16) 1;(0,a,b)
    else let (a,b):=qi 15 (c - 136) 1;(1,a,b)
  else
    if c < 22 then (2,c,c)
    else if c < 253 then let (a,b):=qi 21 (c - 22) 1;(0,a,b)
    else let (a,b):=qi 21 (c - 253) 1;(1,a,b)
def k0 (ow:Nat) : Nat→ Nat→ List f9→ List f9
  | 0,_,ws => ws
  | k+1,bits,ws =>
    let (op,ia,ib):=rd ow (bits &&& ((1 <<< ow) - 1))
    k0 ow k (bits >>> ow) (ws ++ [gk op (ws.getD ia f3) (ws.getD ib f3)])
lemma pg (ow n bits:Nat) (ws:List f9) (r s) (base:∀ v ∈ ws,fx r s v) :
    ∀ v ∈ k0 ow n bits ws,fx r s v:=by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    simp only [k0]
    rcases rd ow (bits &&& ((1 <<< ow) - 1)) with ⟨op,ia,ib⟩
    apply ih;intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl:=List.mem_singleton.mp hz
      unfold gk;split
      · exact n8 (lh base _)
      · exact n9 _ (lh base _) (lh base _)
def jl (ow:Nat) : Nat→ Nat→ List Sig→ List Sig
  | 0,_,ws => ws
  | k+1,bits,ws =>
    let (op,ia,ib):=rd ow (bits &&& ((1 <<< ow) - 1))
    let z:=if op=2 then neg (ws.getD ia zero) else bin (op == 1) (ws.getD ia zero) (ws.getD ib zero)
    jl ow k (bits >>> ow) (ws ++ [z])
lemma r2 (ow n bits:Nat) (ws:List f9) :
    jl ow n bits (ws.map Prod.fst)=(k0 ow n bits ws).map Prod.fst:=by
  induction n generalizing bits ws with
  | zero => rfl
  | succ k ih =>
    simp only [jl,k0]
    have hget : ∀ i,(ws.map Prod.fst).getD i zero=(ws.getD i f3).1:=by
      intro i;rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_map]
      cases ws[i]? <;> rfl
    rcases rd ow (bits &&& ((1 <<< ow) - 1)) with ⟨op,ia,ib⟩
    dsimp only
    have hcode : (if op=2 then neg ((ws.map Prod.fst).getD ia zero)
        else bin (op == 1) ((ws.map Prod.fst).getD ia zero) ((ws.map Prod.fst).getD ib zero)) =
        (gk op (ws.getD ia f3) (ws.getD ib f3)).1:=by
      rw [hget,hget];unfold gk tk tj;split
      · rfl
      · split <;> rfl
    rw [hcode,← List.map_singleton,← List.map_append];exact ih (bits >>> ow) _
lemma md (ow:Nat) (ms:List mu) (n bits:Nat) (ws:List Sig) :
    jl ow n bits (ws.map (movedWord ms))=(jl ow n bits ws).map (movedWord ms):=by
  induction n generalizing bits ws with
  | zero => rfl
  | succ k ih =>
    simp only [jl]
    have hget (i:Nat) : (ws.map (movedWord ms)).getD i zero=movedWord ms (ws.getD i zero):=by
      rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_map]
      cases ws[i]? with
      | none => exact ((gy ms zero).trans (ky (g6 ms)).1).symm
      | some x => rfl
    rcases rd ow (bits &&& ((1 <<< ow) - 1)) with ⟨op,ia,ib⟩
    dsimp only;rw [hget,hget]
    have hop : (if op=2 then neg (movedWord ms (ws.getD ia zero))
        else bin (op == 1) (movedWord ms (ws.getD ia zero)) (movedWord ms (ws.getD ib zero))) =
        movedWord ms (if op=2 then neg (ws.getD ia zero)
        else bin (op == 1) (ws.getD ia zero) (ws.getD ib zero)):=by
      simp only [gy];split
      · exact (py _ _).symm
      · exact (pz _ _ _ _).symm
    rw [hop,← List.map_singleton,← List.map_append];exact ih (bits >>> ow) _
def km (word:Nat→ Nat) (pos len:Nat) :=
  let i:=pos >>> 16
  let y7:=pos &&& 65535
  let lo:=word i >>> y7
  if y7+len ≤ 65536 then lo &&& ((1 <<< len) - 1)
  else (lo ||| (word (i+1) <<< (65536 - y7))) &&& ((1 <<< len) - 1)
def lw0 (nb slots sw vw iw pw:Nat) (data:Nat→ Nat) (h:Nat) : Option (Nat × Nat) :=
  let a:=h % nb
  let sh:=km data (a*sw) sw
  let row:=(h / nb+sh) % slots
  let word:=km data (nb*sw+row*vw) vw
  some (word &&& ((1 <<< iw) - 1),(word >>> iw) &&& ((1 <<< pw) - 1))
def IndexTree (α : Type):=List α
def IndexTree.leaf {α} (xs:List α) : IndexTree α := xs
def IndexTree.fork {α} (_:Nat) (a b:IndexTree α) : IndexTree α := List.append a b
def IndexTree.read {α} (tree:IndexTree α) (i:Nat):=(show List α from tree)[i]?
def IndexTree.values {α} (tree:IndexTree α) : List α := tree
lemma IndexTree.read_mem {α} (tree:IndexTree α) {i x} (e:tree.read i=some x) :
    x ∈ tree.values:=List.mem_of_getElem? e
abbrev PT:=Nat × Nat × Nat × Nat × (Nat→ Nat)
def ePT : PT:=(0,0,0,0,fun _ => 0)
def Forest:=Nat × Nat × (Nat→ Bits × Bits) × IndexTree ColumnInfo × Array (List Nat)
def Forest.mask (c:Forest) : Nat:=c.1
def Forest.cap (c:Forest) : Nat:=c.2.1
def Forest.samples (c:Forest) : Nat→ Bits × Bits:=c.2.2.1
def Forest.cols (c:Forest) : IndexTree ColumnInfo:=c.2.2.2.1
def Forest.autos (c:Forest) : Array (List Nat):=c.2.2.2.2
def k3 (g:Forest) : List f9 :=
  q9 g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
lemma qj (g:Forest) : ∀ a ∈ k3 g,
    fx (lx fun j => (g.samples j).1) (lx fun j => (g.samples j).2) a :=
  rx g.mask _ _
lemma pd (g:Forest) : (k3 g).map Prod.fst=vars g.mask:=by
  simp [k3,q9,vars,List.map_map,Function.comp_def]
lemma ss (g:Forest) : (k3 g).length=(vars g.mask).length:=by
  rw [← pd g,List.length_map]
lemma su {m:Nat} {p q:Nat→ Bits}
    (hp:l2 m p=BitVec.allOnes 768) (hq:l2 m q=0) :
    k6 (graphGoal m) (lx p) (lx q):=by
  intro i;simp only [ry,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def gw {α : Type} (bits:Nat) : List α → List α
  | [] => []
  | w :: ws => if bits &&& 1 == 1 then w :: gw (bits >>> 1) ws else gw (bits >>> 1) ws
lemma qk {α : Type} (bits:Nat) (ws:List α) : (gw bits ws).Sublist ws:=by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold gw;split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)
lemma me {α β : Type} (f : α → β) (bits:Nat) (ws:List α) :
    gw bits (ws.map f)=(gw bits ws).map f:=by
  induction ws generalizing bits with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,gw];split <;> simp [ih]
def pe (ow:Nat) (f5:List f9) (ops paid:Nat) : Nat→ List jw
  | 0 => []
  | n+1 =>
    let more:=pe ow f5 (ops >>> ow) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      let (op,ia,ib):=rd ow (ops &&& ((1 <<< ow) - 1))
      (op,(f5.getD ia f3).1,(f5.getD ib f3).1) :: more
def p1 (g:Forest) (ow ops d:Nat) (f5:List f9) (idx paid:Nat) : Option fs :=
  (g.cols.read idx).bind fun ci =>
    m7 (vars g.mask) (pe ow f5 ops paid d) (kh ci.1 ci.2.1) ci.2.2.2.2
lemma ph (g:Forest)
    (cols:∀ ci ∈ g.cols.values,p7 (vars g.mask) (graphGoal g.mask) (kh ci.1 ci.2.1) ci.2.2.2.2)
    {ow i ops jn f5 paid c} (h:p1 g ow ops jn f5 i paid=some c) :
    jm (vars g.mask) (graphGoal g.mask) c:=by
  unfold p1 at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h;exact n7 (cols ci (g.cols.read_mem e)) h
def sv (data:Nat→ Nat) (w v:Nat) : Nat→ Nat→ List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x:=km data pos (w+v)
    (x &&& ((1 <<< w) - 1),x >>> w) :: sv data w v n (pos+w+v)
def graphValid (g:Forest) (j0:Nat→ Nat) :=
  (l2 g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (l2 g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => l1 g.mask c j0) &&
  g.autos.toList.all (fun p => qg (graphGoal g.mask) (p.map swapRows))
lemma r3 {m cap j0 ci hints} (low:∀ q,gq (vars q) (graphGoal q) (j0 q))
    (ok:l1 m ci j0=true)
    (hp:gr (graphGoal m)=true)
    (ess:g4 (graphGoal m) (vars m) (ji m hints)=true)
    (all:(ji m hints).map Prod.fst=vars m)
    (nd:(vars m).Nodup)
    (cut:pj (kh ci.1 ci.2.1) ci.2.2.2.2 cap 0 (vars m) (vars m)=true) :
    gq (vars m) (graphGoal m) (cap+1):=by
  apply kz (j5 _ hp) _ (qv (ra ci j0 low ok) [] rfl nd cut);intro a ha;apply kg ess a;rw [all];exact List.mem_toFinset.mpr ha
def jq (lu:List (Nat × Nat)) := ∀ e ∈ lu,gq (vars e.1) (graphGoal e.1) e.2
def fp (old:List (Nat × Nat)) (L:Nat) (ko:List (Nat × List Nat)) :=
  ko.map (fun v => (v.1,L)) ++ old
lemma gd {old L m ko} (y2:jq old)
    (main:gq (vars m) (graphGoal m) L)
    (ok:ko.all (fun v => ml v.1 m v.2)=true) :
    jq (fp old L ko):=by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact ti (List.all_eq_true.mp ok _ hv) main
  · exact y2 e h
lemma re : jq []:=by simp [jq]
def ImpossibleT (T:Sig) (cap tm:Nat) (S:Finset Sig) : Prop :=
  ∀ k t,k ≤ cap→ (tm < 3→ t ≤ tm)→ ¬Live T k t S
lemma impT3_to_imp {T cap S} (h:ImpossibleT T cap 3 S) : jv T cap S :=
  fun k t hk => h k t hk (fun hlt => by omega)
lemma imp_to_impT {T cap tm S} (h:jv T cap S) : ImpossibleT T cap tm S :=
  fun k t hk _ => h k t hk
lemma impT_mono {T cap tm1 tm2 S} (hle:tm1 ≤ tm2) (h:ImpossibleT T cap tm2 S) :
    ImpossibleT T cap tm1 S :=
  fun k t hk ht => h k t hk (fun hlt => Nat.le_trans (ht (by omega)) hle)
lemma p2 {T n tm} {ws:List Sig} (hi:ImpossibleT T n tm ws.toFinset)
    (p:List mu) (ok:qg T p=true) :
    ImpossibleT T n tm (ws.map (movedWord p.reverse)).toFinset:=by
  simp only [qg,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (g6 p):=fun r => ⟨g6 p.reverse r,pc ok.2 r⟩
  intro k t hk ht h
  have run:=sg h (g6 p) onto
  have goal : fv (g6 p) T=T:=(gy p T).symm.trans ok.1.1
  have rm (x:Sig) : fv (g6 p) (movedWord p.reverse x)=x:=by
    apply BitVec.eq_of_getLsbD_eq;intro j hj;change bit ⟨j,hj⟩ _=bit ⟨j,hj⟩ _;rw [g5,l0,pc ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (fv (g6 p))=ws.toFinset:=by
    ext a;simp only [Finset.mem_image,List.mem_toFinset,List.mem_map];constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩;simpa only [rm] using hw
    · intro ha;exact ⟨_,⟨a,ha,rfl⟩,rm a⟩
  rw [goal,back] at run;exact hi k t hk ht run
def gu (tm cap len:Nat) (isNot:Bool) : Nat :=
  if len == cap then 0 else if tm == 3 then 3 else if isNot then tm - 1 else tm
lemma tr {T:Sig} {cap tm:Nat} {ws:List Sig} (hn:ws.Nodup) (out:T ∉ ws)
    (a8:tm > 0→ ∀ a ∈ ws,∀ keep,neg a ∉ ws→ proper (neg a) →
      (g9 ws a keep).length ≤ cap →
      ImpossibleT T (cap - 1) (gu tm cap (g9 ws a keep).length true) (g9 ws a keep).toFinset)
    (a9:∀ a ∈ ws,∀ b ∈ ws,∀ d ka kb,a ≠ b→ bin d a b ∉ ws →
      proper (bin d a b)→ (fk ws a b d ka kb).length ≤ cap →
      ImpossibleT T (cap - 1) (gu tm cap (fk ws a b d ka kb).length false)
        (fk ws a b d ka kb).toFinset) :
    ImpossibleT T cap tm ws.toFinset:=by
  classical
  intro k t hk ht h
  generalize he : ws.toFinset=S at h
  induction h using Live.recurse with
  | stop hp => exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  | @unary k t U a ha hf tail _ =>
    have am : a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have gj : neg a ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=live_proper tail _ (Finset.mem_insert_self _ _)
    let keep:=decide (a ∈ U)
    have er:=ns hn a
    have rest : (fw keep a (ws.erase a)).toFinset=U:=by
      rw [kx,er,he];by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (g9 ws a keep).Nodup:=by
      have na : a ∉ ws.erase a:=hn.not_mem_erase
      refine List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h)),
        j4 keep a (ws.erase a) (hn.erase _) na⟩
    have eq : (g9 ws a keep).toFinset=insert (neg a) U:=by simp [g9,rest]
    have sc:=(mi tail).2
    have len : (g9 ws a keep).length ≤ cap:=by rw [← List.toFinset_card_of_nodup nd,eq];omega
    have htm_pos : tm > 0:=by by_contra h0;have:=ht (by omega);omega
    have ht' : gu tm cap (g9 ws a keep).length true < 3→ t ≤ gu tm cap (g9 ws a keep).length true:=by
      intro hlt
      by_cases hlen : (g9 ws a keep).length=cap
      · simp only [gu,hlen,beq_self_eq_true,ite_true] at hlt ⊢
        rw [← List.toFinset_card_of_nodup nd,eq] at hlen;omega
      · by_cases h3 : tm=3
        · simp [gu,hlen,h3] at hlt
        · simp only [gu,beq_eq_false_iff_ne.mpr hlen,beq_eq_false_iff_ne.mpr h3,Bool.false_eq_true,ite_false,ite_true] at hlt ⊢
          have:=ht (by omega);omega
    exact a8 htm_pos a am keep gj hz len k t (by omega) ht' (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail _ =>
    have am : a ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws:=List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have gj : bin d a b ∉ ws:=fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz:=live_proper tail _ (Finset.mem_insert_self _ _)
    let ka:=decide (a ∈ U)
    let kb:=decide (b ∈ U)
    let rest:=(ws.erase a).erase b
    have er : rest.toFinset=(ws.toFinset.erase a).erase b:=by
      rw [show rest=(ws.erase a).erase b by rfl,ns (hn.erase _) b,ns hn a]
    have ke : (fw ka a (fw kb b rest)).toFinset=U:=by
      rw [kx,kx,er,he];ext j
      by_cases hja : j=a
      · subst j;by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka,kb,aa,bb,hab]
      · by_cases hjb : j=b
        · subst j;by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka,kb,aa,bb,hja]
        · by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> simp [ka,kb,aa,bb,hja,hjb]
    have rn : rest.Nodup:=(hn.erase _).erase _
    have ar : a ∉ rest:=fun h => hn.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest:=(hn.erase a).not_mem_erase
    have nk:=j4 kb b rest rn br
    have ax : a ∉ fw kb b rest:=by cases kb <;> simp [fw,ar,hab]
    have nd : (fk ws a b d ka kb).Nodup :=
      List.nodup_cons.mpr ⟨fun h => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h))),
        j4 ka a _ nk ax⟩
    have eq : (fk ws a b d ka kb).toFinset=insert (bin d a b) U:=by
      change (bin d a b :: fw ka a (fw kb b rest)).toFinset=_;simp [ke]
    have sc:=(mi tail).2
    have len : (fk ws a b d ka kb).length ≤ cap:=by rw [← List.toFinset_card_of_nodup nd,eq];omega
    have ht' : gu tm cap (fk ws a b d ka kb).length false < 3→ t ≤ gu tm cap (fk ws a b d ka kb).length false:=by
      intro hlt
      by_cases hlen : (fk ws a b d ka kb).length=cap
      · simp only [gu,hlen,beq_self_eq_true,ite_true] at hlt ⊢
        rw [← List.toFinset_card_of_nodup nd,eq] at hlen;omega
      · by_cases h3 : tm=3
        · simp [gu,hlen,h3] at hlt
        · simp only [gu,beq_eq_false_iff_ne.mpr hlen,beq_eq_false_iff_ne.mpr h3,Bool.false_eq_true,ite_false] at hlt ⊢
          exact ht hlt
    exact a9 a am b bm d ka kb hab gj hz len k t (by omega) ht' (eq.symm ▸ tail)
def n4 (a b:List Sig) : Bool:=a.length == b.length&&a.all (fun x => b.contains x)
lemma r4 {xs ys:List Sig} (hnd:xs.Nodup) (h:n4 xs ys=true) : xs.toFinset=ys.toFinset:=by
  simp only [n4,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  have hsub : xs.toFinset ⊆ ys.toFinset:=fun x hx => List.mem_toFinset.mpr (h.2 x (List.mem_toFinset.mp hx))
  have hle : ys.toFinset.card ≤ xs.toFinset.card:=by
    rw [List.toFinset_card_of_nodup hnd,h.1];exact List.toFinset_card_le ys
  exact Finset.eq_of_subset_of_card_le hsub hle
def kp (gz:List fs) (links:Nat→ List (List Sig)) (tag k:Nat)
    (rest:List Sig) (op:jw) (z:Sig) : Bool :=
  let ws:=z :: rest
  (links tag).any (n4 ws)||gz.any (fun p => gn p k rest op)
lemma nh {raw T gz links tag k tm rest op}
    (pValid:∀ p ∈ gz,jm raw T p)
    (lValid:∀ t xs,xs ∈ links t→ ImpossibleT T k tm (List.toFinset xs))
    (nd:(fb op :: rest).Nodup)
    (h:kp gz links tag k rest op (fb op)=true) :
    ImpossibleT T k tm (fb op :: rest).toFinset:=by
  simp only [kp,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [r4 nd ok];exact lValid _ _ hx
  · exact imp_to_impT (kd (pValid _ hp) nd ok)
def g7 (d:Sig) : List f9→ Nat
  | [] => 0
  | w :: ws => (f2 d w.1).toNat+2*g7 d ws
lemma mz (d:Sig) (ws:List f9) (i:Nat) (hi:i < ws.length) :
    ((g7 d ws >>> i) &&& 1)=(f2 d (ws.getD i f3).1).toNat:=by
  induction ws generalizing i with
  | nil => simp at hi
  | cons w ws ih =>
    cases i with
    | zero =>
      simp only [g7,Nat.shiftRight_zero,List.getD_cons_zero,Nat.and_one_is_mod]
      cases f2 d w.1 <;> simp <;> omega
    | succ i =>
      simp only [g7,List.getD_cons_succ];rw [show i+1=1+i by omega,Nat.shiftRight_add,Nat.shiftRight_one]
      have hdiv : ((f2 d w.1).toNat+2*g7 d ws) / 2=g7 d ws:=by
        cases f2 d w.1 <;> simp <;> omega
      rw [hdiv];exact ih i (by simpa using hi)
abbrev ln:=fs × Nat × Nat × List Sig
def g1 (ws:List f9) (k:Nat) (p:fs) : Option ln :=
  let mw:=p.wires.map (ga p.domain)
  if !(ws.all (fun w => let m:=ga p.domain w.1;m == zero||m == p.domain||mw.any (fun v => v == m))) then none else
  let cm:=ws.countP (fun w => f2 p.domain w.1)
  if k+p.paid > p.bound+cm then none else
  some (p,cm,g7 p.domain ws,mw)
def g3 (s:ln) (k:Nat) (a b:f9) (z:Sig) (un ka kb:Bool) : Bool :=
  let (p,sd,_,mw):=s
  let la:=if ka then 0 else (f2 p.domain a.1).toNat
  let lb:=if un||kb then 0 else (f2 p.domain b.1).toNat
  let lhs:=k+p.paid
  let rhs:=p.bound+(sd - la - lb)
  if lhs+1 < rhs then true
  else if lhs > rhs then false
  else
    let zm:=ga p.domain z
    let zc:=zm == zero||zm == p.domain
    if lhs == rhs then zc else zc||mw.any (fun v => v == zm)
def mq (s:ln) (k i j:Nat) (z:Sig) (un ka kb:Bool) : Bool :=
  let (p,sd,y4,mw):=s
  let la:=if ka then 0 else (y4 >>> i) &&& 1
  let lb:=if un||kb then 0 else (y4 >>> j) &&& 1
  let lhs:=k+p.paid
  let rhs:=p.bound+(sd - la - lb)
  if lhs+1 < rhs then true
  else if lhs > rhs then false
  else
    let zm:=ga p.domain z
    let zc:=zm == zero||zm == p.domain
    if lhs == rhs then zc else zc||mw.any (fun v => v == zm)
lemma ni {s k ws i j z un ka kb} (hi:i < ws.length) (hj:j < ws.length)
    (hcm:s.2.2.1=g7 s.1.domain ws) :
    mq s k i j z un ka kb =
      g3 s k (ws.getD i f3) (ws.getD j f3) z un ka kb:=by
  rcases s with ⟨p,sd,y4,mw⟩
  dsimp only at hcm;subst hcm;dsimp only [mq,g3];rw [mz p.domain ws i hi,mz p.domain ws j hj]
lemma ql {p qp k ws a b op ka kb} (ha:a ∈ ws) (hb:b ∈ ws)
    (hsum:g1 ws k p=some qp)
    (h:g3 qp k a b (fb (fl op a b)) (op == 2) ka kb=true) :
    gn p k ((jk (op == 2) ka kb a b ws).map Prod.fst) (fl op a b)=true:=by
  dsimp only [g1] at hsum
  split at hsum
  · cases hsum
  next hok =>
    have all : ws.all (fun w => ff p.domain p.wires w.1)=true:=by
      cases hall : ws.all (fun w => ff p.domain p.wires w.1)
      · exfalso;apply hok;change (!ws.all (fun w => ff p.domain p.wires w.1))=true;rw [hall];rfl
      · rfl
    split at hsum
    · cases hsum
    injection hsum with hqp;subst hqp
    let z:=fb (fl op a b)
    let lc:=fun w : f9 => f2 p.domain w.1
    let rest:=jk (op == 2) ka kb a b ws
    have ck:=vs lc ws a b (op == 2) ka kb
    change ws.countP lc - fm lc a ka - fm lc b ((op == 2)||kb) ≤ rest.countP lc at ck
    have hav:=List.all_eq_true.mp all
    have hs : (rest.map Prod.fst).all (ff p.domain p.wires)=true:=by
      apply List.all_eq_true.mpr;intro _ hm;obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm;exact hav w ((nf ws a b (op == 2) ka kb).subset hw)
    have opOK : kk p.domain p.wires (fl op a b)=true:=by simp [kk,fl,hav _ ha,hav _ hb]
    dsimp only [rest] at hs;simp only [gn,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,List.countP_map,Function.comp_def];change k+p.paid+(!ff p.domain p.wires z).toNat < p.bound+(rest.countP lc+if f2 p.domain z then 1 else 0)
    have hla : (if ka then 0 else (f2 p.domain a.1).toNat)=fm lc a ka:=by cases ka <;> simp [fm,lc]
    have hlb : (if (op == 2)||kb then 0 else (f2 p.domain b.1).toNat)=fm lc b ((op == 2)||kb):=by cases ((op == 2)||kb) <;> simp [fm,lc]
    dsimp only [g3] at h;rw [hla,hlb] at h
    set la:=fm lc a ka
    set lb:=fm lc b ((op == 2)||kb)
    set lhs:=k+p.paid
    set rhs:=p.bound+(ws.countP lc - la - lb)
    have hzc : (ga p.domain z == zero||ga p.domain z == p.domain)=f2 p.domain z:=rfl
    have hfree : ((ga p.domain z == zero||ga p.domain z == p.domain) ||
        (p.wires.map (ga p.domain)).any (fun v => v == ga p.domain z))=ff p.domain p.wires z:=rfl
    split at h
    · cases h1 : ff p.domain p.wires z <;> cases h2 : f2 p.domain z <;> simp_all <;> omega
    · split at h
      · cases h
      · split at h
        · rw [hzc] at h
          have hfa : ff p.domain p.wires z=true:=by rw [← hfree,hzc,h];rfl
          simp [h,hfa];omega
        · rw [hfree] at h;cases h2 : f2 p.domain z <;> simp_all <;> omega
abbrev s3:=Nat→ Nat→ List (List Sig)
abbrev fa :=
  Nat × Nat × Nat × List f9 × s0 × List fs × List ln × s3 × List Nat × Nat
def fu (c:fa) (i:Nat) : f9:=c.2.2.2.1.getD i f3
def g8 (c:fa) (op:Nat) (a b z:f9) (ka kb:Bool) : Bool :=
  let (cap,tm,n,ws,cov,gz,ls,lfn,_,lz):=c
  let un:=op == 2
  let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
  if len > cap then true else
    let ct:=gu tm cap len un
    let d:=ct == 0
    if (lj (n2 cov d) (g0 d a.2) (g0 d b.2) un ka kb ||| g0 d z.2) != BitVec.allOnes 768 then true else
    if !gr z.1||ws.any (fun v => v.1 == z.1) then true else
    if ls.any (fun qp => g3 qp (cap - 1) a b z.1 un ka kb) then true else
      let rest:=(jk un ka kb a b ws).map Prod.fst
      let tag:=lz - (if ka then 0 else h9 a.1) - (if un||kb then 0 else h9 b.1)+h9 z.1
      kp gz (lfn ct) tag (cap - 1) rest (fl op a b) z.1
lemma ly {raw T r s ws} {gz:List fs} {lfn:s3} {kq lz cap tm a b op ka kb}
    (qr:k6 T r s) (rl:∀ w ∈ ws,fx r s w)
    (nd:(ws.map Prod.fst).Nodup) (ha:a ∈ ws) (hb:b ∈ ws)
    (ne:(op == 2)=false→ a ≠ b) (hcap:0 < cap)
    (pv:∀ p ∈ gz,jm raw T p)
    (lv:∀ ct tag xs,xs ∈ lfn ct tag→ ImpossibleT T (cap - 1) ct (List.toFinset xs))
    (pro:proper (fc op a b).1) (gj:(fc op a b).1 ∉ ws.map Prod.fst)
    (test:g8 (cap,tm,ws.length,ws,n1 ws,gz,gz.filterMap (g1 ws (cap - 1)),lfn,kq,lz)
      op a b (fc op a b) ka kb=true) :
    ImpossibleT T (cap - 1) (gu tm cap (gl ws op a b ka kb).length (op == 2))
      (gl ws op a b ka kb).toFinset:=by
  let z:=fc op a b
  let rest:=jk (op == 2) ka kb a b ws
  let child:=z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws:=nf _ _ _ _ _ _
  have ndc : child.Nodup:=List.nodup_cons.mpr ⟨fun hm => gj ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
  have val:=qc op a b
  have fr : ws.any (fun v => v.1 == z.1)=false:=by
    apply Bool.eq_false_iff.mpr;intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact gj ((beq_iff_eq.mp he).symm ▸ List.mem_map_of_mem hx)
  have pp : gr z.1=true:=by simpa [gr,proper] using pro
  have leq : 1+(ws.length - (if ka then 0 else 1) - (if (op == 2)||kb then 0 else 1))=child.length:=by
    change _=(z.1 :: rest.map Prod.fst).length;rw [List.length_cons,List.length_map,xe _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk ht h
  have hsz:=(mi h).2
  change child.toFinset.card+t ≤ k+1 at hsz;rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap:=by omega
  unfold g8 at test;change (if 1+(ws.length - _ - _) > cap then true else _)=true at test;rw [leq,if_neg (by omega)] at test
  set ct:=gu tm cap child.length (op == 2)
  have ht0 : (ct == 0)=true→ t=0:=fun hct => by
    have hc0 : ct=0:=beq_iff_eq.mp hct
    have ht' : ct < 3→ t ≤ ct:=ht
    rw [hc0] at ht'
    have:=ht' (by decide);omega
  have sep:=sk h rfl (xb qr) (ct == 0) ht0
  let d:=ct == 0
  have g : (ft d rest).1=jg d (jp r s) (rest.map Prod.fst) :=
    xd _ _ (fun v hv => rl _ (sub.subset hv))
  have rz:=qy ha hb (op == 2) ka kb d ne
  have hf:=qd (rl _ ha) (rl _ hb) op
  change g0 d (jp r s z.1) ||| jg d (jp r s) (rest.map Prod.fst)=_ at sep;change z.2=jp r s z.1 at hf;rw [← hf,← g,rz,BitVec.or_comm] at sep
  have be : ((lj (n2 (n1 ws) d) (g0 d a.2) (g0 d b.2) (op == 2) ka kb ||| g0 d z.2) != BitVec.allOnes 768)=false:=by
    rw [sep,bne_self_eq_false]
  change (if (_ != _) then true else if !gr z.1||ws.any (fun v => v.1 == z.1) then true else if _ then true else _)=true at test;rw [be,pp,fr] at test;simp only [Bool.false_eq_true,ite_false,Bool.not_true,Bool.false_or] at test
  have nd' : (fb (fl op a b) :: rest.map Prod.fst).Nodup:=val ▸ ndc
  have h' : Live T k t (fb (fl op a b) :: rest.map Prod.fst).toFinset:=val ▸ h
  by_cases hq : (gz.filterMap (g1 ws (cap - 1))).any (fun qp => g3 qp (cap - 1) a b z.1 (op == 2) ka kb)=true
  · obtain ⟨qp,hqp,hfc⟩ := List.any_eq_true.mp hq
    obtain ⟨p,hp,hsum⟩ := List.mem_filterMap.mp hqp
    exact kd (pv p hp) nd' (ql ha hb hsum (val ▸ hfc)) k t hk h'
  · have hqf : (gz.filterMap (g1 ws (cap - 1))).any (fun qp => g3 qp (cap - 1) a b z.1 (op == 2) ka kb)=false :=
      Bool.eq_false_iff.mpr hq
    change (if ((gz.filterMap (g1 ws (cap - 1))).any fun qp => g3 qp (cap - 1) a b z.1 (op == 2) ka kb)=true then true else _)=true at test;rw [hqf] at test;simp only [Bool.false_eq_true,ite_false] at test;exact nh pv (lv ct) nd' (val ▸ test) k t hk ht h'
def j7 (c:fa) (a b:f9) (d:Bool) : Bool :=
  let op:=if d then 1 else 0
  let z:=fc op a b
  let f:=g8 c op a b z
  f false false&&f true false&&f false true&&f true true
def sx (c:fa) (a:f9) (tail:List f9) : Bool :=
  let z:=fc 2 a a
  let unOk:=if c.2.1 == 0 then true else g8 c 2 a a z false false&&g8 c 2 a a z true true
  unOk&&tail.all (fun b => j7 c a b false&&j7 c a b true)
def jf (c:fa) : List f9→ Bool
  | [] => true
  | a :: tail => sx c a tail&&jf c tail
lemma ts {c ws a} (h:jf c ws=true) (ht:c.2.1 > 0) (ha:a ∈ ws) (keep:Bool) :
    g8 c 2 a a (fc 2 a a) keep keep=true:=by
  induction ws with
  | nil => simp at ha
  | cons x tail ih =>
    simp only [jf,Bool.and_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | mt
    · have hu:=(Bool.and_eq_true _ _).mp h.1 |>.1
      have hne : (c.2.1 == 0)=false:=beq_eq_false_iff_ne.mpr (by omega)
      simp only [hne,Bool.false_eq_true,ite_false,Bool.and_eq_true] at hu
      cases keep;exact hu.1;exact hu.2
    · exact ih h.2 mt
lemma sy {c ws a b} (h:jf c ws=true) (ha:a ∈ ws) (hb:b ∈ ws)
    (ne:a ≠ b) (d:Bool) : j7 c a b d=true∨j7 c b a d=true:=by
  induction ws with
  | nil => simp at ha
  | cons x tail ih =>
    simp only [jf,Bool.and_eq_true] at h
    have row:=(Bool.and_eq_true _ _).mp h.1 |>.2
    rcases List.mem_cons.mp ha with rfl | ma <;> rcases List.mem_cons.mp hb with rfl | mb
    · exact False.elim (ne rfl)
    · left;have p:=List.all_eq_true.mp row b mb;cases d <;> simp_all
    · right;have p:=List.all_eq_true.mp row a ma;cases d <;> simp_all
    · exact ih h.2 ma mb
lemma s4 {c a b d} (h:j7 c a b d=true) (ka kb:Bool) :
    g8 c (if d then 1 else 0) a b (fc (if d then 1 else 0) a b) ka kb=true:=by
  simp only [j7,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2
lemma t0 {raw T r s ws} {gz:List fs} {lfn:s3} {kq lz cap tm}
    (qr:k6 T r s) (rl:∀ w ∈ ws,fx r s w)
    (nd:(ws.map Prod.fst).Nodup) (out:T ∉ ws.map Prod.fst)
    (pv:∀ p ∈ gz,jm raw T p)
    (lv:∀ ct tag xs,xs ∈ lfn ct tag→ ImpossibleT T (cap - 1) ct (List.toFinset xs))
    (se:cap=0∨jf (cap,tm,ws.length,ws,n1 ws,gz,gz.filterMap (g1 ws (cap - 1)),lfn,kq,lz) ws=true) :
    ImpossibleT T cap tm (ws.map Prod.fst).toFinset:=by
  rcases se with rfl | se
  · intro k t hk _ h
    have hk0 : k=0:=by omega
    subst hk0
    generalize he : (ws.map Prod.fst).toFinset=S at h
    rw [h.zeroSet] at he;exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  by_cases hc : cap=0
  · subst hc
    intro k t hk _ h
    have hk0 : k=0:=by omega
    subst hk0
    generalize he : (ws.map Prod.fst).toFinset=S at h
    rw [h.zeroSet] at he;exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0 < cap:=by omega
  apply tr nd out
  · intro htpos v hv keep gj pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf:=sq nd ha keep
    have hev:=ly (op:=2) qr rl nd ha ha (by simp) hc' pv lv pro gj (ts se htpos ha keep)
    have v4 : (gl ws 2 a a keep keep).length=(g9 (ws.map Prod.fst) a.1 keep).length:=by
      have nd1 : (gl ws 2 a a keep keep).Nodup:=by
        unfold gl;have sub:=nf ws a a true keep keep;exact List.nodup_cons.mpr ⟨fun hm => gj ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
      have nd2 : (g9 (ws.map Prod.fst) a.1 keep).Nodup:=by
        unfold g9;have na : a.1 ∉ (ws.map Prod.fst).erase a.1:=nd.not_mem_erase;refine List.nodup_cons.mpr ⟨fun hm => ?_,j4 keep a.1 _ (nd.erase _) na⟩;rw [je] at hm;rcases hm with ⟨heq,_⟩ | hm
        · exact gj (heq.symm ▸ List.mem_map_of_mem ha)
        · exact gj (List.mem_of_mem_erase hm)
      rw [← List.toFinset_card_of_nodup nd1,← List.toFinset_card_of_nodup nd2,hf]
    rw [hf,v4] at hev;exact hev
  · intro a ha b hb d ka kb ne gj pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a ≠ b:=fun e => ne (congrArg Prod.fst e)
    have one (a b:f9) (aa:a ∈ ws) (bb:b ∈ ws) (ne':a.1 ≠ b.1) (ka kb:Bool)
        (pr:proper (bin d a.1 b.1)) (fr:bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test:j7 (cap,tm,ws.length,ws,n1 ws,gz,gz.filterMap (g1 ws (cap - 1)),lfn,kq,lz) a b d=true) :
        ImpossibleT T (cap - 1) (gu tm cap (fk (ws.map Prod.fst) a.1 b.1 d ka kb).length false)
          (fk (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset:=by
      have hf:=s1 nd aa bb ne' d ka kb
      have eq : (fc (if d then 1 else 0) a b).1=bin d a.1 b.1:=by cases d <;> rfl
      have hev:=ly (op:=if d then 1 else 0) qr rl nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (s4 test ka kb)
      have v4 : (gl ws (if d then 1 else 0) a b ka kb).length=(fk (ws.map Prod.fst) a.1 b.1 d ka kb).length:=by
        have nd1 : (gl ws (if d then 1 else 0) a b ka kb).Nodup:=by
          unfold gl;have sub:=nf ws a b ((if d then 1 else 0) == 2) ka kb;exact List.nodup_cons.mpr ⟨fun hm => (eq ▸ fr) ((sub.map _).subset hm),nd.sublist (sub.map _)⟩
        have nd2 : (fk (ws.map Prod.fst) a.1 b.1 d ka kb).Nodup:=by
          unfold fk
          let r0:=((ws.map Prod.fst).erase a.1).erase b.1
          have rn : r0.Nodup:=(nd.erase _).erase _
          have ar : a.1 ∉ r0:=fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have br : b.1 ∉ r0:=(nd.erase a.1).not_mem_erase
          have nk:=j4 kb b.1 r0 rn br
          have ax : a.1 ∉ fw kb b.1 r0:=by cases kb <;> simp [fw,ar,ne']
          refine List.nodup_cons.mpr ⟨fun hm => ?_,j4 ka a.1 _ nk ax⟩;rw [je] at hm;rcases hm with ⟨heq,_⟩ | hm
          · exact fr (heq.symm ▸ List.mem_map_of_mem aa)
          · rw [je] at hm;rcases hm with ⟨heq,_⟩ | hm
            · exact fr (heq.symm ▸ List.mem_map_of_mem bb)
            · exact fr (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        rw [← List.toFinset_card_of_nodup nd1,← List.toFinset_card_of_nodup nd2,hf]
      have hbo : ((if d then 1 else 0) == 2)=false:=by cases d <;> rfl
      rw [hf,v4,hbo] at hev;exact hev
    rcases sy se haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro gj hh
    · have hsw:=qz (ws.map Prod.fst) nd a.1 b.1 d ka kb
      have hlenSw : (fk (ws.map Prod.fst) a.1 b.1 d ka kb).length=(fk (ws.map Prod.fst) b.1 a.1 d kb ka).length:=by
        have ndA : (fk (ws.map Prod.fst) a.1 b.1 d ka kb).Nodup:=by
          unfold fk;let rA:=((ws.map Prod.fst).erase a.1).erase b.1
          have rn : rA.Nodup:=(nd.erase a.1).erase b.1
          have ar : a.1 ∉ rA:=fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have br : b.1 ∉ rA:=(nd.erase a.1).not_mem_erase
          have nk:=j4 kb b.1 rA rn br
          have ax : a.1 ∉ fw kb b.1 rA:=by cases kb <;> simp [fw,ar,ne]
          refine List.nodup_cons.mpr ⟨fun hm => ?_,j4 ka a.1 _ nk ax⟩;rw [je] at hm;rcases hm with ⟨heq,_⟩ | hm
          · exact gj (heq.symm ▸ List.mem_map_of_mem haW)
          · rw [je] at hm;rcases hm with ⟨heq,_⟩ | hm
            · exact gj (heq.symm ▸ List.mem_map_of_mem hbW)
            · exact gj (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        have ndB : (fk (ws.map Prod.fst) b.1 a.1 d kb ka).Nodup:=by
          unfold fk;let rB:=((ws.map Prod.fst).erase b.1).erase a.1
          have rn : rB.Nodup:=(nd.erase b.1).erase a.1
          have br : b.1 ∉ rB:=fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
          have ar : a.1 ∉ rB:=(nd.erase b.1).not_mem_erase
          have nk:=j4 ka a.1 rB rn ar
          have bx : b.1 ∉ fw ka a.1 rB:=by cases ka <;> simp [fw,br,Ne.symm ne]
          refine List.nodup_cons.mpr ⟨fun hm => ?_,j4 kb b.1 _ nk bx⟩;rw [k4 d b.1 a.1] at hm;rw [je] at hm;rcases hm with ⟨heq,_⟩ | hm
          · exact gj (heq.symm ▸ List.mem_map_of_mem hbW)
          · rw [je] at hm;rcases hm with ⟨heq,_⟩ | hm
            · exact gj (heq.symm ▸ List.mem_map_of_mem haW)
            · exact gj (List.mem_of_mem_erase (List.mem_of_mem_erase hm))
        rw [← List.toFinset_card_of_nodup ndA,← List.toFinset_card_of_nodup ndB,hsw]
      rw [hsw,hlenSw];exact one b a hbW haW (Ne.symm ne) kb ka (k4 d a.1 b.1 ▸ pro) (k4 d a.1 b.1 ▸ gj) hh
def l5 (raw:List f9) (f1:Nat→ PT) (slot i:Nat) : Nat × List f9 × List f9 :=
  let (_,jn,_,_,data):=f1 slot
  let ow:=opW raw.length jn
  let len:=ow*jn
  let ks:=len+raw.length+jn
  let recp:=km data (i*ks) ks
  let ops:=recp &&& ((1 <<< len) - 1)
  let f5:=k0 ow jn ops raw
  (ops,f5,gw (recp >>> len) f5)
def stateSetG (g:Forest) (f1:Nat→ PT) (slot i:Nat) (base:List Sig) : List Sig :=
  let (_,jn,_,_,data):=f1 slot
  let nraw:=(vars g.mask).length
  let ow:=opW nraw jn
  let len:=ow*jn
  let ks:=len+nraw+jn
  let recp:=km data (i*ks) ks
  let ops:=recp &&& ((1 <<< len) - 1)
  gw (recp >>> len) (jl ow jn ops base)
lemma s5 (g:Forest) (f1:Nat→ PT) (slot i:Nat) :
    stateSetG g f1 slot i (vars g.mask)=(l5 (k3 g) f1 slot i).2.2.map Prod.fst:=by
  unfold stateSetG l5
  rcases f1 slot with ⟨num,jn,cw,offw,data⟩
  dsimp only;rw [← ss g,← pd g,r2,me]
lemma mv (g:Forest) (f1:Nat→ PT) (slot i:Nat) (ms:List mu) :
    stateSetG g f1 slot i ((vars g.mask).map (movedWord ms)) =
      (stateSetG g f1 slot i (vars g.mask)).map (movedWord ms):=by
  unfold stateSetG
  rcases f1 slot with ⟨num,jn,cw,offw,data⟩
  dsimp only;rw [md,me]
def l6 (f1:Nat→ PT) (k:Nat) : Nat→ Nat→ Nat→ Option (Nat × Nat)
  | 0,_,_ => none
  | f+1,ct,i =>
    let n:=(f1 (4*k+ct)).1
    if i < n then some (ct,i) else l6 f1 k f (ct+1) (i - n)
lemma qm {f1 k f ct i ct' j} (h:l6 f1 k f ct i=some (ct',j)) :
    ct ≤ ct' ∧ ct' < ct+f∧j < (f1 (4*k+ct')).1:=by
  induction f generalizing ct i with
  | zero => simp [l6] at h
  | succ f ih =>
    unfold l6 at h;dsimp only at h
    split at h
    next hlt => injection h with h1;injection h1 with hc hj;subst hc;subst hj;exact ⟨Nat.le_refl _,by omega,hlt⟩
    next =>
      obtain ⟨h1,h2,h3⟩ := ih h
      exact ⟨by omega,by omega,h3⟩
def lp (g:Forest) (f1:Nat→ PT) (f8:Nat→ Option (List Sig))
    (k ct:Nat) (pair:Nat × Nat) : Option (List Sig) :=
  (l6 f1 k (4 - ct) ct pair.1).bind fun (ct',j) =>
    (f8 pair.2).map (stateSetG g f1 (4*k+ct') j)
lemma p3 (g:Forest) (f1:Nat→ PT) (f8:Nat→ Option (List Sig)) (k ct:Nat)
    (rk:∀ x ∈ g.autos.toList,qg (graphGoal g.mask) (x.map swapRows)=true)
    (hrot:∀ p,f8 p=(g.autos[p]?).map (fun perm => (vars g.mask).map (movedWord (perm.map swapRows).reverse)))
    (earlier:∀ ct' ≤ 3,∀ j < (f1 (4*k+ct')).1,ImpossibleT (graphGoal g.mask) k ct' (stateSetG g f1 (4*k+ct') j (vars g.mask)).toFinset)
    {pair out} (h:lp g f1 f8 k ct pair=some out) :
    ImpossibleT (graphGoal g.mask) k ct out.toFinset:=by
  unfold lp at h
  cases hf : l6 f1 k (4 - ct) ct pair.1 with
  | none => simp [hf] at h
  | some cj =>
    rcases cj with ⟨ct',j⟩
    simp only [hf,Option.bind_some] at h
    obtain ⟨hle,hlt,hj⟩ := qm hf
    rw [hrot] at h
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h;rw [← h,mv];exact impT_mono hle (p2 (earlier ct' (by omega) j hj) _ (rk _ (by simpa using Array.mem_of_getElem? e)))
def s6 (g:Forest) (p:Nat) : Option (List Sig) :=
  (g.autos[p]?).map (fun perm => (vars g.mask).map (movedWord (perm.map swapRows).reverse))
def kn (g:Forest) (raw:List f9) (f1:Nat→ PT) (idx:Nat→ Nat→ Nat→ Option (Nat × Nat))
    (f8:Nat→ Option (List Sig)) (k tm i:Nat) : fa :=
  let slot:=4*k+tm
  let (num,jn,cw,offw,data):=f1 slot
  let ow:=opW raw.length jn
  let (ops,f5,ws):=l5 raw f1 slot i
  let start:=num*(ow*jn+raw.length+jn)
  let c0:=km data (start+i*offw) offw
  let c1:=km data (start+(i+1)*offw) offw
  let nr:=c1 - c0
  let st:=start+(num+1)*offw+c0*(cw+jn)
  let rules:=(sv data cw jn nr st).filterMap (fun (a,b) => p1 g ow ops jn f5 a b)
  let lfn:=fun ct tag => ((idx slot ct tag).bind (lp g f1 f8 (k - 1) ct)).toList
  let kq:=ws.map (fun w => h9 w.1)
  (k,tm,ws.length,ws,n1 ws,rules,rules.filterMap (g1 ws (k - 1)),lfn,kq,kq.foldl (· + ·) 0)
def s7 (T:Sig) (c:fa) : Bool :=
  let ws:=c.2.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
def h7 (g:Forest) (f1:Nat→ PT) (idx:Nat→ Nat→ Nat→ Option (Nat × Nat))
    (f8:Nat→ Option (List Sig)) (k tm i:Nat) : Bool :=
  let c:=kn g (k3 g) f1 idx f8 k tm i
  s7 (graphGoal g.mask) c&&(if k=0 then true else jf c c.2.2.2.1)
lemma kf (g:Forest) (f1:Nat→ PT) (idx:Nat→ Nat→ Nat→ Option (Nat × Nat))
    (f8:Nat→ Option (List Sig)) (k tm i:Nat)
    (samples:k6 (graphGoal g.mask) (lx fun j => (g.samples j).1) (lx fun j => (g.samples j).2))
    (cols:∀ ci ∈ g.cols.values,p7 (vars g.mask) (graphGoal g.mask) (kh ci.1 ci.2.1) ci.2.2.2.2)
    (rk:∀ x ∈ g.autos.toList,qg (graphGoal g.mask) (x.map swapRows)=true)
    (hrot:∀ p,f8 p=(g.autos[p]?).map (fun perm => (vars g.mask).map (movedWord (perm.map swapRows).reverse)))
    (j0:k > 0→ ∀ ct' ≤ 3,∀ j < (f1 (4*(k - 1)+ct')).1,
      ImpossibleT (graphGoal g.mask) (k - 1) ct' (stateSetG g f1 (4*(k - 1)+ct') j (vars g.mask)).toFinset)
    (po:h7 g f1 idx f8 k tm i=true) :
    ImpossibleT (graphGoal g.mask) k tm (stateSetG g f1 (4*k+tm) i (vars g.mask)).toFinset:=by
  rw [s5];simp only [h7,s7,kn,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem,decide_eq_false_iff_not] at po
  have hN:=po.1.1
  have hT : graphGoal g.mask ∉ (l5 (k3 g) f1 (4*k+tm) i).2.2.map Prod.fst:=po.1.2
  by_cases h0 : k=0
  · subst k
    intro k' t' hk' _ h
    have hk0 : k' = 0:=by omega
    subst k'
    generalize he : ((l5 (k3 g) f1 (4*0+tm) i).2.2.map Prod.fst).toFinset=S at h
    rw [h.zeroSet] at he;exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply t0 (raw:=vars g.mask) samples _ hN hT _ _ (Or.inr (by simpa only [h0,ite_false] using po.2))
  · intro v hv
    apply pg _ _ _ _ _ _ (qj g) v;exact (qk _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact ph g cols h
  · intro ct tag xs hx
    have e : ((idx (4*k+tm) ct tag).bind (lp g f1 f8 (k - 1) ct))=some xs:=by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact p3 g f1 f8 (k - 1) ct rk hrot (j0 (by omega)) h
def blockG (g:Forest) (f1:Nat→ PT) (idx:Nat→ Nat→ Nat→ Option (Nat × Nat))
    (f8:Nat→ Option (List Sig)) (k tm start:Nat) : Nat→ Bool
  | 0 => true
  | n+1 => h7 g f1 idx f8 k tm start&&blockG g f1 idx f8 k tm (start+1) n
lemma rf {g f1 idx f8 k tm start n} (h:blockG g f1 idx f8 k tm start n=true)
    (i:Nat) (lo:start ≤ i) (hi:i < start+n) : h7 g f1 idx f8 k tm i=true:=by
  induction n generalizing start with
  | zero => omega
  | succ n ih =>
    simp only [blockG,Bool.and_eq_true] at h
    by_cases eq : i=start
    · exact eq ▸ h.1
    · exact ih h.2 (by omega) (by omega)
lemma blockG_merge {g f1 idx f8 k tm start a b}
    (ha:blockG g f1 idx f8 k tm start a=true)
    (hb:blockG g f1 idx f8 k tm (start+a) b=true) :
    blockG g f1 idx f8 k tm start (a+b)=true:=by
  induction a generalizing start with
  | zero => simpa [blockG] using hb
  | succ a ih =>
    simp only [blockG,Nat.succ_add,Bool.and_eq_true] at ha ⊢
    exact ⟨ha.1,ih ha.2 (by simpa [Nat.add_assoc,Nat.add_comm 1] using hb)⟩
lemma blockG_zero {g lv idx rot k tm s n} (hn:n=0) : blockG g lv idx rot k tm s n=true:=by
  subst hn;rfl
lemma blockG_eq {g lv idx rot k tm k' tm' n n'}
    (h:blockG g lv idx rot k' tm' 0 n' = true) (hk:k=k') (ht:tm=tm') (hn:n=n') :
    blockG g lv idx rot k tm 0 n=true:=by
  subst hk;subst ht;subst hn;exact h
lemma rot_at_of {m na:Nat} {r:Nat→ Option (List Sig)} {auts:Array (List Nat)}
    (heq:(List.range na).all (fun p => match r p,auts[p]? with
      | some xs,some perm => xs == (vars m).map (movedWord (perm.map swapRows).reverse)
      | _,_ => false)=true)
    (hnone:∀ p ≥ na,r p=none) (hsz:auts.size=na) :
    ∀ p,r p=(auts[p]?).map (fun perm => (vars m).map (movedWord (perm.map swapRows).reverse)):=by
  intro p
  by_cases hp : p < na
  · have h:=List.all_eq_true.mp heq p (List.mem_range.mpr hp)
    cases h1 : r p <;> cases h2 : auts[p]? <;> simp [h1,h2] at h ⊢;exact h
  · rw [hnone p (by omega),Array.getElem?_eq_none (by omega)];rfl
def r6 (x:Nat) : Bits:=BitVec.ofNat 768 (x*0x10000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001)
lemma j3 {old m cap ci hints ko} (prev:jq old)
    (ok:(l1 m ci (boundsBefore old)&&gr (graphGoal m) &&
      g4 (graphGoal m) (vars m) (ji m hints) &&
      pj (kh ci.1 ci.2.1) ci.2.2.2.2 cap 0 (vars m) (vars m) &&
      ko.all (fun v => ml v.1 m v.2))=true)
    (all:(ji m hints).map Prod.fst=vars m)
    (nd:(vars m).Nodup) :
    jq (fp old (cap+1) ko):=by
  simp only [Bool.and_eq_true] at ok;exact gd prev (r3 (before_sound old prev) ok.1.1.1.1 ok.1.1.1.2 ok.1.1.2 all nd ok.1.2) ok.2
lemma tt {g f1 idx f8 k tm start n}
    (h:∀ i,start ≤ i→ i < start+n→ h7 g f1 idx f8 k tm i=true) :
    blockG g f1 idx f8 k tm start n=true:=by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [blockG,Bool.and_eq_true];exact ⟨h _ (by omega) (by omega),ih (fun i lo hi => h i (by omega) (by omega))⟩
def mf (c:fa) (i j op:Nat) (ka kb:Bool) : Bool :=
  let a:=fu c i
  let b:=fu c j
  g8 c op a b (fc op a b) ka kb
def qn (c:fa) (d un ka kb:Bool) (op i j:Nat) : Bits :=
  let a:=fu c i
  let b:=fu c j
  lj (n2 c.2.2.2.2.1 d) (g0 d a.2) (g0 d b.2) un ka kb ||| g0 d (fc op a b).2
def kv (c:fa) (i j op:Nat) (ka kb:Bool) : Bool :=
  let (cap,tm,n,ws,_,gz,ls,lfn,kq,lz):=c
  let a:=ws.getD i f3
  let b:=ws.getD j f3
  let un:=op == 2
  let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
  let ct:=gu tm cap len un
  let z1:=fb (fl op a b)
  if !gr z1||ws.any (fun v => v.1 == z1) then true else
  if ls.any (fun qp => mq qp (cap - 1) i j z1 un ka kb) then true else
    let rest:=(jk un ka kb a b ws).map Prod.fst
    let tag:=lz - (if ka then 0 else kq.getD i 0) - (if un||kb then 0 else kq.getD j 0)+h9 z1
    kp gz (lfn ct) tag (cap - 1) rest (fl op a b) z1
lemma mx {c i j op ka kb}
    (hi:i < c.2.2.2.1.length) (hj:j < c.2.2.2.1.length)
    (hwk:c.2.2.2.2.2.2.2.2.1=c.2.2.2.1.map (fun w => h9 w.1))
    (hcm:∀ qp ∈ c.2.2.2.2.2.2.1,qp.2.2.1=g7 qp.1.domain c.2.2.2.1)
    (hlen : ¬(1+(c.2.2.1 - (if ka then 0 else 1) - (if (op == 2)||kb then 0 else 1)) > c.1))
    (h:kv c i j op ka kb=true) :
    mf c i j op ka kb=true:=by
  rcases c with ⟨cap,tm,n,ws,cov,gz,ls,lfn,kq,lz⟩
  dsimp only at hi hj hwk hcm hlen;subst hwk;dsimp only [mf,g8,fu];rw [if_neg hlen];dsimp only [kv] at h
  have hz1 : (fc op (ws.getD i f3) (ws.getD j f3)).1 =
      fb (fl op (ws.getD i f3) (ws.getD j f3)):=qc op _ _
  have hki : (ws.map (fun w => h9 w.1)).getD i 0=h9 (ws.getD i f3).1:=by
    rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hi];rfl
  have hkj : (ws.map (fun w => h9 w.1)).getD j 0=h9 (ws.getD j f3).1:=by
    rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_eq_getElem hj];rfl
  have hfc : ls.any (fun qp => mq qp (cap - 1) i j (fb (fl op (ws.getD i f3) (ws.getD j f3))) (op == 2) ka kb) =
      ls.any (fun qp => g3 qp (cap - 1) (ws.getD i f3) (ws.getD j f3) (fb (fl op (ws.getD i f3) (ws.getD j f3))) (op == 2) ka kb):=by
    apply Bool.eq_iff_iff.mpr;simp only [List.any_eq_true]
    constructor <;> rintro ⟨qp,hqp,hok⟩ <;> refine ⟨qp,hqp,?_⟩
    · rwa [← ni hi hj (hcm qp hqp)]
    · rwa [ni hi hj (hcm qp hqp)]
  rw [hfc,hki,hkj] at h
  set len:=1+(n - (if ka then 0 else 1) - (if (op == 2)||kb then 0 else 1))
  set ct:=gu tm cap len (op == 2)
  set d:=ct == 0
  by_cases b5 : ((lj (n2 cov d) (g0 d (ws.getD i f3).2) (g0 d (ws.getD j f3).2) (op == 2) ka kb ||| g0 d (fc op (ws.getD i f3) (ws.getD j f3)).2) != BitVec.allOnes 768)=true
  · simp only [b5,ite_true]
  · simp only [b5,ite_false,hz1];exact h
def gp (k n:Nat) (xs:List fa) : rb :=
  (k,n,m9 xs.length,
    (List.range n).map (fun i => j6 (fun c => (fu c i).2) xs),
    jz (fun c => c.2.2.2.2.1.1) xs,
    jz (fun c => c.2.2.2.2.1.2) xs)
lemma nj (k n:Nat) (xs:List fa) {i:Nat} (h:i < n) :
    l4 (gp k n xs) i=j6 (fun c => (fu c i).2) xs:=by
  simp [l4,gp,List.getD_eq_getElem?_getD,h]
def lq (b:rb) (tm:Nat) (xs:List fa) (i j op:Nat) (ka kb:Bool) : Bool :=
  let (k,n,r,_,u,v):=b
  let un:=op == 2
  let len:=1+(n - (if ka then 0 else 1) - (if un||kb then 0 else 1))
  if len > k then true else
    let d:=gu tm k len un == 0
    let a:=l4 b i
    let b' := l4 b j
    let z:=mc (r*(BitVec.allOnes 768).toNat) op a b'
    let cov:=if d then v else u
    let mask:=mn r (lm cov (gm d a) (gm d b') un ka kb ||| gm d z)
    ng (fun c => kv c i j op ka kb) mask xs
lemma r5 (k tm n:Nat) (xs:List fa) {i j op:Nat} {ka kb}
    (hi:i < n) (hj:j < n) {q:Nat} (hq:q < xs.length)
    (jr:xs[q].1=k) (ht:xs[q].2.1=tm) (kr:xs[q].2.2.1=n) (hn:xs[q].2.2.2.1.length=n)
    (hwk:xs[q].2.2.2.2.2.2.2.2.1=xs[q].2.2.2.1.map (fun w => h9 w.1))
    (hcm:∀ qp ∈ xs[q].2.2.2.2.2.2.1,qp.2.2.1=g7 qp.1.domain xs[q].2.2.2.1)
    (pass:lq (gp k n xs) tm xs i j op ka kb=true) :
    mf xs[q] i j op ka kb=true:=by
  let len:=1+(n - (if ka then 0 else 1) - (if (op == 2)||kb then 0 else 1))
  let d:=gu tm k len (op == 2) == 0
  by_cases qq : len > k
  · rcases hxq : xs[q] with ⟨cap,tmm,nn,ws,cov,gz,ls,lfn,kq,lz⟩
    rw [hxq] at jr kr;dsimp only at jr kr;subst jr kr;dsimp only [mf,g8,len] at qq ⊢;rw [if_pos qq]
  · let r:=m9 xs.length
    let a:=l4 (gp k n xs) i
    let b:=l4 (gp k n xs) j
    let cov:=if d then jz (fun c:fa => c.2.2.2.2.1.2) xs
               else jz (fun c:fa => c.2.2.2.2.1.1) xs
    change (if len > k then true else ng _ (mn r
       (lm cov (gm d a) (gm d b) (op == 2) ka kb |||
        gm d (mc (r*(BitVec.allOnes 768).toNat) op a b))) xs)=true at pass
    rw [if_neg qq] at pass
    have chosen : cov=jz (fun c => n2 c.2.2.2.2.1 d) xs:=by dsimp only [cov];cases d <;> rfl
    have ca : a=_:=nj k n xs hi
    have cb : b=_:=nj k n xs hj
    dsimp only [r] at pass;rw [ca,cb,vq,ku,ku,ku,chosen,r1,qh] at pass
    by_cases hit : qn xs[q] d (op == 2) ka kb op i j=BitVec.allOnes 768
    · have hlenq : ¬(1+(xs[q].2.2.1 - (if ka then 0 else 1) - (if (op == 2)||kb then 0 else 1)) > xs[q].1):=by
        rw [jr,kr];exact qq
      apply mx (hn ▸ hi) (hn ▸ hj) hwk hcm hlenq;apply vr _ _ _ q hq _ pass;rw [yf _ _ _ hq];exact beq_iff_eq.mpr hit
    · rcases hxq : xs[q] with ⟨cap,tmm,nn,ws,cov0,gz,ls,lfn,kq,lz⟩
      rw [hxq] at jr ht kr hit;dsimp only at jr ht kr;subst jr ht kr;dsimp only [mf,g8,fu,len] at qq ⊢
      rw [if_neg qq];change (if qn (cap,tmm,nn,ws,cov0,gz,ls,lfn,kq,lz) d (op == 2) ka kb op i j != BitVec.allOnes 768 then true else _)=true;rw [if_pos (bne_iff_ne.mpr hit)]
def lr (b:rb) (tm:Nat) (xs:List fa) (i j op:Nat) : Bool :=
  let f:=lq b tm xs i j op
  f false false&&f true false&&f false true&&f true true
def p4 (b:rb) (tm:Nat) (xs:List fa) (i:Nat) (js:List Nat) : Bool :=
  let unOk:=if tm == 0 then true else lq b tm xs i i 2 false false&&lq b tm xs i i 2 true true
  unOk&&js.all (fun j => lr b tm xs i j 0&&lr b tm xs i j 1)
def k1 (b:rb) (tm:Nat) (xs:List fa) : List Nat→ Bool
  | [] => true
  | i :: js => p4 b tm xs i js&&k1 b tm xs js
lemma r7 (k tm n:Nat) (xs:List fa) {q:Nat} (hq:q < xs.length)
    (jr:xs[q].1=k) (ht:xs[q].2.1=tm) (kr:xs[q].2.2.1=n) (hn:xs[q].2.2.2.1.length=n)
    (hwk:xs[q].2.2.2.2.2.2.2.2.1=xs[q].2.2.2.1.map (fun w => h9 w.1))
    (hcm:∀ qp ∈ xs[q].2.2.2.2.2.2.1,qp.2.2.1=g7 qp.1.domain xs[q].2.2.2.1) (js:List Nat)
    (v3:∀ j ∈ js,j < n) (pq:k1 (gp k n xs) tm xs js=true) :
    jf xs[q] (js.map (fu xs[q]))=true:=by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [k1,Bool.and_eq_true,p4,List.all_eq_true] at pq;simp only [List.map_cons,jf,sx,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi:=v3 i List.mem_cons_self
    have check := @r5 k tm n xs
    have hun : (if xs[q].2.1 == 0 then true else
        g8 xs[q] 2 (fu xs[q] i) (fu xs[q] i) (fc 2 (fu xs[q] i) (fu xs[q] i)) false false &&
        g8 xs[q] 2 (fu xs[q] i) (fu xs[q] i) (fc 2 (fu xs[q] i) (fu xs[q] i)) true true)=true:=by
      rw [ht]
      cases htm : (tm == 0)
      · simp only [Bool.false_eq_true,ite_false,Bool.and_eq_true]
        have h1:=pq.1.1;simp only [htm,Bool.false_eq_true,ite_false,Bool.and_eq_true] at h1
        exact ⟨check hi hi hq jr ht kr hn hwk hcm h1.1,check hi hi hq jr ht kr hn hwk hcm h1.2⟩
      · simp
    refine ⟨⟨hun,?_⟩,ih (fun j hj => v3 j (List.mem_cons_of_mem _ hj)) pq.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := v3 j (List.mem_cons_of_mem _ hj)
    have both:=pq.1.2 j hj
    have vd (d:Bool) (pass:lr (gp k n xs) tm xs i j (if d then 1 else 0)=true) :
        j7 xs[q] (fu xs[q] i) (fu xs[q] j) d=true:=by
      simp only [lr,Bool.and_eq_true] at pass;simp only [j7,Bool.and_eq_true];exact ⟨⟨⟨check hi hj' hq jr ht kr hn hwk hcm pass.1.1.1,check hi hj' hq jr ht kr hn hwk hcm pass.1.1.2⟩,
        check hi hj' hq jr ht kr hn hwk hcm pass.1.2⟩,check hi hj' hq jr ht kr hn hwk hcm pass.2⟩
    exact ⟨vd false both.1,vd true both.2⟩
def p5 (k tm n:Nat) (xs:List fa) : Bool :=
  k1 (gp k n xs) tm xs (List.range n)
lemma s8 {k tm n} {xs:List fa} {q} (hq:q < xs.length)
    (hb:xs[q].1=k) (ht:xs[q].2.1=tm) (ha:xs[q].2.2.1=n) (hn:xs[q].2.2.2.1.length=n)
    (hwk:xs[q].2.2.2.2.2.2.2.2.1=xs[q].2.2.2.1.map (fun w => h9 w.1))
    (hcm:∀ qp ∈ xs[q].2.2.2.2.2.2.1,qp.2.2.1=g7 qp.1.domain xs[q].2.2.2.1)
    (pass:p5 k tm n xs=true) : jf xs[q] xs[q].2.2.2.1=true:=by
  have all:=r7 k tm n xs hq hb ht ha hn hwk hcm (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (fu xs[q])=xs[q].2.2.2.1:=by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2;simp [fu,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all
def rg (g:Forest) (f1:Nat→ PT) (idx:Nat→ Nat→ Nat→ Option (Nat × Nat))
    (f8:Nat→ Option (List Sig)) (k tm start n:Nat) : List fa :=
  let raw:=k3 g
  ((List.range n).map (start + ·)).map (kn g raw f1 idx f8 k tm)
def mg (g:Forest) (f1:Nat→ PT) (idx:Nat→ Nat→ Nat→ Option (Nat × Nat))
    (f8:Nat→ Option (List Sig)) (k tm start n ar:Nat) : Bool :=
  let xs:=rg g f1 idx f8 k tm start n
  xs.all (fun c => c.2.2.1 == ar&&s7 (graphGoal g.mask) c) &&
  let b:=gp k ar xs
  (List.range ar).all (fun i => p4 b tm xs i (List.range' (i+1) (ar - (i+1))))
lemma chunkBlockG {g f1 idx f8 k tm start n ar}
    (h:mg g f1 idx f8 k tm start n ar=true) :
    blockG g f1 idx f8 k tm start n=true:=by
  unfold mg at h;rw [Bool.and_eq_true] at h
  let xs:=rg g f1 idx f8 k tm start n
  have hrun : p5 k tm ar xs=true:=by
    have go (lo num:Nat) (eq:lo+num=ar) :
        k1 (gp k ar xs) tm xs (List.range' lo num)=true:=by
      induction num generalizing lo with
      | zero => rfl
      | succ num ih =>
        simp only [List.range'_succ,k1,Bool.and_eq_true];refine ⟨?_,ih (lo+1) (by omega)⟩
        have ok:=List.all_eq_true.mp h.2 lo (List.mem_range.mpr (by omega))
        simpa only [show ar - (lo+1)=num by omega] using ok
    unfold p5;rw [List.range_eq_range'];exact go 0 ar (by omega)
  apply tt;intro i lo hi
  have hm : kn g (k3 g) f1 idx f8 k tm i ∈ xs:=by
    apply List.mem_map.mpr;exact ⟨i,List.mem_map.mpr ⟨i - start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one:=List.all_eq_true.mp h.1 _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k:=by rw [e];rfl
  have ht : xs[q].2.1=tm:=by rw [e];rfl
  have ha : xs[q].2.2.1=ar:=e ▸ one.1
  have hn : xs[q].2.2.2.1.length=ar:=by rw [e];exact one.1
  have hwk : xs[q].2.2.2.2.2.2.2.2.1=xs[q].2.2.2.1.map (fun w => h9 w.1):=by rw [e];rfl
  have hcm : ∀ qp ∈ xs[q].2.2.2.2.2.2.1,qp.2.2.1=g7 qp.1.domain xs[q].2.2.2.1:=by
    rw [e];intro qp hqp;dsimp only [kn] at hqp
    obtain ⟨p,_,hsum⟩ := List.mem_filterMap.mp hqp
    dsimp only [g1] at hsum
    split at hsum
    · cases hsum
    split at hsum
    · cases hsum
    injection hsum with heq;subst heq;rfl
  simp only [h7,Bool.and_eq_true];refine ⟨one.2,?_⟩;split
  · rfl
  · exact e ▸ s8 hq hb ht ha hn hwk hcm hrun
def cellsG (g:Forest) (f1:Nat→ PT) (idx:Nat→ Nat→ Nat→ Option (Nat × Nat))
    (f8:Nat→ Option (List Sig)) (k tm start n ar:Nat) : Nat→ Prop
  | 0 => mg g f1 idx f8 k tm start n ar=true
  | d+1 => cellsG g f1 idx f8 k tm start (n / 2) ar d ∧
             cellsG g f1 idx f8 k tm (start+n / 2) (n - n / 2) ar d
lemma cellsBlockG {g f1 idx f8 k tm start n ar d}
    (h:cellsG g f1 idx f8 k tm start n ar d) :
    blockG g f1 idx f8 k tm start n=true:=by
  induction d generalizing start n with
  | zero => exact chunkBlockG h
  | succ d ih =>
    have v:=blockG_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v
lemma forestG_all (g:Forest) (f1:Nat→ PT) (idx:Nat→ Nat→ Nat→ Option (Nat × Nat))
    (f8:Nat→ Option (List Sig)) (top:Nat)
    (j0:Nat→ Nat)
    (lo:∀ m,gq (vars m) (graphGoal m) (j0 m))
    (l9:graphValid g j0=true)
    (hrot:∀ p,f8 p=(g.autos[p]?).map (fun perm => (vars g.mask).map (movedWord (perm.map swapRows).reverse)))
    (tabs:∀ k ≤ top,∀ tm ≤ 3,blockG g f1 idx f8 k tm 0 (f1 (4*k+tm)).1=true) :
    ∀ k ≤ top,∀ tm ≤ 3,∀ i < (f1 (4*k+tm)).1,
      ImpossibleT (graphGoal g.mask) k tm (stateSetG g f1 (4*k+tm) i (vars g.mask)).toFinset:=by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at l9
  have qr:=su l9.1.1.1 l9.1.1.2
  have cols : ∀ ci ∈ g.cols.values,p7 (vars g.mask) (graphGoal g.mask) (kh ci.1 ci.2.1) ci.2.2.2.2 :=
    fun ci hc => ra ci j0 lo (l9.1.2 ci hc)
  have rk:=l9.2
  intro k
  induction k with
  | zero =>
    intro hk tm htm i hi;exact kf g f1 idx f8 0 tm i qr cols rk hrot
      (fun h => False.elim (Nat.lt_irrefl 0 h))
      (rf (tabs 0 hk tm htm) i (Nat.zero_le i) (by simpa using hi))
  | succ k ih =>
    intro hk tm htm i hi;exact kf g f1 idx f8 (k+1) tm i qr cols rk hrot
      (fun _ ct' hct j hj => ih (by omega) ct' hct j hj)
      (rf (tabs (k+1) hk tm htm) i (Nat.zero_le i) (by simpa using hi))
lemma h8 {g f1 idx f8 j0 i hints}
    (low:∀ q,gq (vars q) (graphGoal q) (j0 q))
    (geom:graphValid g j0=true)
    (hrot:∀ p,f8 p=(g.autos[p]?).map (fun perm => (vars g.mask).map (movedWord (perm.map swapRows).reverse)))
    (tabs:∀ k ≤ g.cap,∀ tm ≤ 3,blockG g f1 idx f8 k tm 0 (f1 (4*k+tm)).1=true)
    (idxOk:decide (i < (f1 (4*g.cap+3)).1) &&
      sameWords (stateSetG g f1 (4*g.cap+3) i (vars g.mask)) (vars g.mask)=true)
    (hp:gr (graphGoal g.mask)=true)
    (ess:g4 (graphGoal g.mask) (vars g.mask) (ji g.mask hints)=true)
    (all:(ji g.mask hints).map Prod.fst=vars g.mask) :
    gq (vars g.mask) (graphGoal g.mask) (g.cap+1):=by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at idxOk;apply kz (j5 _ hp) _ (impT3_to_imp ?_)
  · intro a ha;apply kg ess a;rw [all];exact List.mem_toFinset.mpr ha
  · rw [← sameWords_sound idxOk.2]
    exact forestG_all g f1 idx f8 g.cap j0 low geom hrot tabs g.cap (Nat.le_refl _) 3 (by decide) i idxOk.1
def gf : Sig:=inputs.getD 0 zero
def j8 : Sig:=inputs.getD 1 zero
def gg : Sig:=inputs.getD 2 zero
def gh : Sig:=inputs.getD 3 zero
def gi : Sig:=inputs.getD 4 zero
def j1 : Sig:=inputs.getD 5 zero
def l7 : Sig:=inputs.getD 6 zero
def jt : Sig:=inputs.getD 7 zero
def l8 : Sig:=inputs.getD 8 zero
def tu : IndexTree ColumnInfo:=(.leaf [])
def xi : Array (List Nat):=Array.mk [[],[33,48]]
def s15 : Nat→ Bits × Bits
| 0 => (r6 0x59cc1f8efd67307e3bf59cc1f8efd673,r6 0x1949bb08906526ec2241949bb0890652)
| 1 => (r6 0xe1fc7ff0ff87f1ffc3fe1fc7ff0ff87f,r6 0x20a644c04882991301220a644c048829)
| 2 => (r6 0xbe73e3ff1ef9cf8ffc7be73e3ff1ef9c,r6 0x14512a24045144a890114512a2404514)
| 3 => (r6 0x3f8383ffe0fe0e0fff83f8383ffe0fe0,r6 0x2b82d59220ae0b564882b82d59220ae0)
| _ => (0,0)
def g15 : Forest:=⟨15,3,s15,tu,xi⟩
def b7 : PT:=(1,0,1,1,fun _ => 0xf)
def xj : Nat→ PT
| 15 => b7
| _ => ePT
def b2 : Nat→ Nat→ Nat→ Option (Nat × Nat)
| _,_ => fun _ => none
abbrev b8:=blockG g15 xj b2 (s6 g15)
abbrev bm15 (k tm s a b:Nat) := @blockG_merge g15 xj b2 (s6 g15) k tm s a b
set_option maxHeartbeats 0 in
lemma xk : b8 3 3 0 1=true:=chunkBlockG (ar:=4) (by decide +kernel)
lemma b9 : b8 3 3 0 1=true:=xk
lemma t15 : ∀ k ≤ 3,∀ tm ≤ 3,b8 k tm 0 (xj (4*k+tm)).1=true:=by
  intro k hk tm ht;interval_cases k <;> interval_cases tm <;> first | exact blockG_zero rfl | exact blockG_eq b9 rfl rfl rfl
set_option maxHeartbeats 0 in
lemma c2 : graphValid g15 (boundsBefore [])=true:=by
  simp only [graphValid,Bool.and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,by decide +kernel⟩,by decide +kernel⟩
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma low15 : gq (vars 15) (graphGoal 15) 4 :=
  h8 (g:=g15) (i:=0) (hints:=8449) (before_sound [] re) c2 (fun _ => rfl) t15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def c3 : List (Nat × List Nat):=[(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def pm:=fp [] 4 c3
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma v5 : jq pm:=gd re low15 (by decide +kernel)
def tv : IndexTree ColumnInfo:=(.fork 2 (.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def t1 : Array (List Nat):=Array.mk [[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def s31 : Nat→ Bits × Bits
| 0 => (r6 0xfd10fb39878078e38ee3ff1dfa21f673,r6 0x901093290e18e0c20882461120212652)
| 1 => (r6 0xff63243f8007ff03f0fc77e1fec6487f,r6 0x48622414b0a61e01c050218090c44829)
| 2 => (r6 0x1e83c7ce007f87fc00ff87fe3d078f9c,r6 0x481c28a4351a1b000a9044809038514)
| 3 => (r6 0xe0fc07f0787807ffff0007ffc1f80fe0,r6 0x205805702c2a4c4b2400032440b00ae0)
| 4 => (r6 0xfff8007f8007fffffff80001fff000,r6 0xa7680051c5132492649000014ed000)
| _ => (0,0)
def v6 : Nat→ Option (List Sig)
| 0 => some [gf,j8,gg,gh,gi]
| 1 => some [gf,gi,gh,gg,j8]
| 2 => some [j8,gf,gi,gh,gg]
| 3 => some [j8,gg,gh,gi,gf]
| 4 => some [gg,j8,gf,gi,gh]
| 5 => some [gg,gh,gi,gf,j8]
| 6 => some [gh,gg,j8,gf,gi]
| 7 => some [gh,gi,gf,j8,gg]
| 8 => some [gi,gf,j8,gg,gh]
| 9 => some [gi,gh,gg,j8,gf]
| _ => none
lemma xl : ∀ p,v6 p=(t1[p]?).map (fun perm => (vars 31).map (movedWord (perm.map swapRows).reverse)) :=
  rot_at_of (na:=10) (by decide +kernel) (fun p hp => by unfold v6;match p with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => omega | _+10 => rfl) rfl
def g31 : Forest:=⟨31,6,s31,tv,t1⟩
def c4 : PT:=(2,1,3,1,fun _ => 0xcfe27f88)
def c5 : PT:=(1,1,3,1,fun _ => 0x4be00)
def c6 : PT:=(1,0,3,3,fun _ => 0x14e51f)
def xm:=lw0 5 15 4 6 2 4 (fun _ => 0x930010209408215c04235540204)
def xn:=lw0 1 11 4 5 1 4 (fun _ => 0x48c084200a0300)
def xo : Nat→ PT
| 20 => c4
| 23 => c5
| 27 => c6
| _ => ePT
def b3 : Nat→ Nat→ Nat→ Option (Nat × Nat)
| 27,0 => xm
| 27,3 => xn
| _,_ => fun _ => none
abbrev tw:=blockG g31 xo b3 v6
abbrev bm31 (k tm s a b:Nat) := @blockG_merge g31 xo b3 v6 k tm s a b
set_option maxHeartbeats 0 in
lemma xp : tw 5 0 0 2=true:=chunkBlockG (ar:=6) (by decide +kernel)
lemma c7 : tw 5 0 0 2=true:=xp
set_option maxHeartbeats 0 in
lemma xq : tw 5 3 0 1=true:=chunkBlockG (ar:=5) (by decide +kernel)
lemma c8 : tw 5 3 0 1=true:=xq
set_option maxHeartbeats 0 in
lemma xr : tw 6 3 0 1=true:=chunkBlockG (ar:=5) (by decide +kernel)
lemma c9 : tw 6 3 0 1=true:=xr
lemma t31 : ∀ k ≤ 6,∀ tm ≤ 3,tw k tm 0 (xo (4*k+tm)).1=true:=by
  intro k hk tm ht;interval_cases k <;> interval_cases tm <;> first | exact blockG_zero rfl | exact blockG_eq c7 rfl rfl rfl | exact blockG_eq c8 rfl rfl rfl | exact blockG_eq c9 rfl rfl rfl
set_option maxHeartbeats 0 in
lemma e0 : graphValid g31 (boundsBefore pm)=true:=by
  simp only [graphValid,Bool.and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma low31 : gq (vars 31) (graphGoal 31) 7 :=
  h8 (g:=g31) (i:=0) (hints:=8449) (before_sound pm v5) e0 xl t31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def e1 : List (Nat × List Nat):=[(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def v7:=fp pm 7 e1
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma yh : jq v7:=gd v5 low31 (by decide +kernel)
def e2 : List (Nat × List Nat):=[(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def v8:=fp v7 5 e2
set_option maxHeartbeats 0 in
lemma yi : jq v8:=j3 (m:=47) (cap:=4) (ci:=(8,0,39,0,4)) (hints:=8449) yh (by decide +kernel) (by decide +kernel) (by decide +kernel)
def e3 : List (Nat × List Nat):=[(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def v9:=fp v8 5 e3
set_option maxHeartbeats 0 in
lemma yj : jq v9:=j3 (m:=55) (cap:=4) (ci:=(16,0,39,0,4)) (hints:=257) yi (by decide +kernel) (by decide +kernel) (by decide +kernel)
def e4 : List (Nat × List Nat):=[(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def pn:=fp v9 8 e4
set_option maxHeartbeats 0 in
lemma vc : jq pn:=j3 (m:=63) (cap:=7) (ci:=(32,0,31,0,7)) (hints:=8449) yj (by decide +kernel) (by decide +kernel) (by decide +kernel)
def t2 : IndexTree ColumnInfo:=(.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def vt : Array (List Nat):=Array.mk [[],[83,32]]
def s111 : Nat→ Bits × Bits
| 0 => (r6 0x4217c4d939d9b59bde7c36792839f673,r6 0x52024891291125101a30245928112652)
| 1 => (r6 0x8f8c07e1ce663fe36fbcc981ff26487f,r6 0x1348660846402424100810085244829)
| 2 => (r6 0x34687b3e0f87c67c73db0e1e31c78f9c,r6 0xf648611c0a800020220a0e1430838514)
| 3 => (r6 0x38707c3ff007f87f83e3f01fc1f80fe0,r6 0x9b61e23f007d05b00c1f00bc1780ae0)
| 5 => (r6 0xc07f803ffff8007ffc03ffe001fff000,r6 0xac7db5685440002dc403dba001eed000)
| 6 => (r6 0xff80003fffffff800003fffffe000000,r6 0xfec9409f0b8abc8000037eff7a000000)
| _ => (0,0)
def vu : Forest:=⟨111,6,s111,t2,vt⟩
def yk : PT:=(1,0,2,2,fun _ => 0x933f)
def tx : Nat→ PT
| 27 => yk
| _ => ePT
def xt : Nat→ Nat→ Nat→ Option (Nat × Nat)
| _,_ => fun _ => none
abbrev xu:=blockG vu tx xt (s6 vu)
abbrev bm111 (k tm s a b:Nat) := @blockG_merge vu tx xt (s6 vu) k tm s a b
set_option maxHeartbeats 0 in
lemma vv : xu 6 3 0 1=true:=chunkBlockG (ar:=6) (by decide +kernel)
lemma yl : xu 6 3 0 1=true:=vv
lemma t111 : ∀ k ≤ 6,∀ tm ≤ 3,xu k tm 0 (tx (4*k+tm)).1=true:=by
  intro k hk tm ht;interval_cases k <;> interval_cases tm <;> first | exact blockG_zero rfl | exact blockG_eq yl rfl rfl rfl
set_option maxHeartbeats 0 in
lemma ym : graphValid vu (boundsBefore pn)=true:=by
  simp only [graphValid,Bool.and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,by decide +kernel⟩,by decide +kernel⟩
set_option maxHeartbeats 0 in
lemma e5 : gq (vars 111) (graphGoal 111) 7 :=
  h8 (g:=vu) (i:=0) (hints:=16785665) (before_sound pn vc) ym (fun _ => rfl) t111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def yn : List (Nat × List Nat):=[(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def t3:=fp pn 7 yn
set_option maxHeartbeats 0 in
lemma xv : jq t3:=gd vc e5 (by decide +kernel)
def yo : List (Nat × List Nat):=[(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def nl:=fp t3 6 yo
set_option maxHeartbeats 0 in
lemma t4 : jq nl:=j3 (m:=119) (cap:=5) (ci:=(4,0,115,0,5)) (hints:=16777473) xv (by decide +kernel) (by decide +kernel) (by decide +kernel)
def t5 : IndexTree ColumnInfo:=(.fork 4 (.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def rh : Array (List Nat):=Array.mk [[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def s189 : Nat→ Bits × Bits
| 0 => (r6 0x1c3c16b689b913efae1121d833f4fc,r6 0xc987504a4093801450011215802a4ac)
| 2 => (r6 0x87a20798c731dfe277cb82067f2cc8cf,r6 0x92ea119006201542018a82041528c8ca)
| 3 => (r6 0xc63c7e0f83e1e7c79f31c3861cf0f0f,r6 0x2c054640d004001878601c3060870605)
| 4 => (r6 0x843f8ff003fe07f81fce03f81f00ff0,r6 0xc16288ba0030c0200080e00e81700950)
| 5 => (r6 0xf07c00ffffc0007ffe00ffc001fff000,r6 0xf26608f94b800076a200ca8001fd5000)
| 7 => (r6 0xff8000ffffffff800000fffffe000000,r6 0xd11a606b01b8a000000357bea000000)
| _ => (0,0)
def s9 : Nat→ Option (List Sig)
| 0 => some [gf,gg,gh,gi,j1,jt]
| 1 => some [gf,gg,jt,j1,gi,gh]
| 2 => some [gg,gf,gi,gh,jt,j1]
| 3 => some [gg,gf,j1,jt,gh,gi]
| 4 => some [gh,j1,gf,gi,gg,jt]
| 5 => some [gh,j1,jt,gg,gi,gf]
| 6 => some [gi,jt,gg,gh,gf,j1]
| 7 => some [gi,jt,j1,gf,gh,gg]
| 8 => some [j1,gh,gg,jt,gf,gi]
| 9 => some [j1,gh,gi,gf,jt,gg]
| 10 => some [jt,gi,gf,j1,gg,gh]
| 11 => some [jt,gi,gh,gg,j1,gf]
| _ => none
lemma vx : ∀ p,s9 p=(rh[p]?).map (fun perm => (vars 189).map (movedWord (perm.map swapRows).reverse)) :=
  rot_at_of (na:=12) (by decide +kernel) (fun p hp => by unfold s9;match p with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => omega | _+12 => rfl) rfl
def yp : Forest:=⟨189,7,s189,t5,rh⟩
def yq : PT:=(2,1,4,1,fun _ => 0x93fc4ff88)
def yr : PT:=(1,1,4,1,fun _ => 0xf7e00)
def yt : PT:=(1,0,4,3,fun _ => 0x513647c3f)
def vy:=lw0 2 15 4 6 2 4 (fun _ => 0x208960274114240d08201501)
def vz:=lw0 1 11 4 5 1 4 (fun _ => 0x50280c0200902c0)
def ty : Nat→ PT
| 24 => yq
| 27 => yr
| 31 => yt
| _ => ePT
def xw : Nat→ Nat→ Nat→ Option (Nat × Nat)
| 31,0 => vy
| 31,3 => vz
| _,_ => fun _ => none
abbrev qo:=blockG yp ty xw s9
abbrev bm189 (k tm s a b:Nat) := @blockG_merge yp ty xw s9 k tm s a b
set_option maxHeartbeats 0 in
lemma w0 : qo 6 0 0 2=true:=chunkBlockG (ar:=7) (by decide +kernel)
lemma yu : qo 6 0 0 2=true:=w0
set_option maxHeartbeats 0 in
lemma w1 : qo 6 3 0 1=true:=chunkBlockG (ar:=6) (by decide +kernel)
lemma yv : qo 6 3 0 1=true:=w1
set_option maxHeartbeats 0 in
lemma w2 : qo 7 3 0 1=true:=chunkBlockG (ar:=6) (by decide +kernel)
lemma yw : qo 7 3 0 1=true:=w2
lemma t189 : ∀ k ≤ 7,∀ tm ≤ 3,qo k tm 0 (ty (4*k+tm)).1=true:=by
  intro k hk tm ht;interval_cases k <;> interval_cases tm <;> first | exact blockG_zero rfl | exact blockG_eq yu rfl rfl rfl | exact blockG_eq yv rfl rfl rfl | exact blockG_eq yw rfl rfl rfl
set_option maxHeartbeats 0 in
lemma yx : graphValid yp (boundsBefore nl)=true:=by
  simp only [graphValid,Bool.and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces];repeat' apply And.intro;all_goals decide +kernel
set_option maxHeartbeats 0 in
lemma e6 : gq (vars 189) (graphGoal 189) 8 :=
  h8 (g:=yp) (i:=0) (hints:=536879876) (before_sound nl t4) yx vx t189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def yy : List (Nat × List Nat):=[(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def t6:=fp nl 8 yy
set_option maxHeartbeats 0 in
lemma xx : jq t6:=gd t4 e6 (by decide +kernel)
def yz : List (Nat × List Nat):=[(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def nm:=fp t6 9 yz
set_option maxHeartbeats 0 in
lemma t7 : jq nm:=j3 (m:=127) (cap:=8) (ci:=(32,0,95,0,8)) (hints:=16785665) xx (by decide +kernel) (by decide +kernel) (by decide +kernel)
def t8 : IndexTree ColumnInfo:=(.fork 19 (.fork 9 (.fork 4 (.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (.fork 2 (.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (.fork 5 (.fork 2 (.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (.fork 2 (.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (.fork 9 (.fork 4 (.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (.fork 2 (.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (.fork 5 (.fork 2 (.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (.fork 2 (.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def ri : Array (List Nat):=Array.mk [[],[84,115],[117,67,32],[116,83,32]]
def s191 : Nat→ Bits × Bits
| 0 => (r6 0xca0e419f380821075b301c73e21f673,r6 0x300400100082102532000224212652)
| 1 => (r6 0x84fe92ba0cb30c6249c366a4c8c6487f,r6 0xfcce82a804330c6248c164a488c44829)
| 2 => (r6 0x32542be2b54010038e7c8738f1078f9c,r6 0x2102000304010010028831071038514)
| 3 => (r6 0x2368ccccd903e07c0f80f83f01f80fe0,r6 0xa068c484c903e0580f80502f00b00ae0)
| 4 => (r6 0xb8f0f0f1e7c007ff000ffc001fff000,r6 0xf86080b007c0027d000afc0014ed000)
| 5 => (r6 0xcc0ff00fe07fff800000fffffe000000,r6 0x8fc1200a806a59000000fffdda000000)
| 7 => (r6 0xf00ffff0007fffffffff000000000000,r6 0x702cdb500015a6feffd7000000000000)
| _ => (0,0)
def sa : Nat→ Option (List Sig)
| 0 => some [gf,j8,gg,gh,gi,j1,jt]
| 1 => some [gf,j8,gg,jt,j1,gi,gh]
| 2 => some [gg,j8,gf,gi,gh,jt,j1]
| 3 => some [gg,j8,gf,j1,jt,gh,gi]
| _ => none
lemma w3 : ∀ p,sa p=(ri[p]?).map (fun perm => (vars 191).map (movedWord (perm.map swapRows).reverse)) :=
  rot_at_of (na:=4) (by decide +kernel) (fun p hp => by unfold sa;match p with | 0 | 1 | 2 | 3 => omega | _+4 => rfl) rfl
def z0 : Forest:=⟨191,10,s191,t8,ri⟩
def z2 : PT:=(3,4,6,1,fun _ => 0x15eacc222446fc56844488c7d09338901)
def z3 : PT:=(17,3,6,5,fun _ => 0x1c118721ed51143c26cf0b09414140985c260e8c20e5a508314a5294a4102fda507899fccc0803ed988f8eede5e6a2ff5938c8bdf6809a277d072689fea522e27fc268b89df6941e267fa50789fea962447fa0889119fc227e237da38f88fea422623fc8f8988)
def w4:=lw0 3 9 4 4 2 2 (fun _ => 0x303332313000)
def z4 : PT:=(18,3,6,4,fun _ => 0x170a08c4a0e118944a2599984322111000000009bea01e2e7da50789fe0b624477a9e8911be8222447f28911039f4ce2407f8891101ed4180c07d5050301bbaa09c03ce050400ed8180c03d6050300fc80c0803ec040100fd00c0403f8020100)
def w5:=lw0 1 2 2 4 2 2 (fun _ => 0xc)
def z5 : PT:=(32,2,6,7,fun _ => 0x1212af928e0b89869147898a09c7af92118e0a47c78991afc789c7898a20a7c0818f0a0e8a408d0b20a78504a78740a7890e91868b870f128d1189a78a278b880807408b918f05098389110511cd952234482f1cb666c57294a9109f3868c172a4c9901a2c4870a0c080ffccc77fe623bff271dff928effccc5ffe522fff3117ff938bffcbc5ffe4a2fff4113ff9a89ffcac4ffe7a27ff1913ff8e89ffc5c4ffc1e27ff2d11ffa088ffcd447fe5623ff3f11ff9088ffc6c47fe2e23ff1311ff9a00ffc6807fe3003ff1401ff0200)
def w6:=lw0 4 19 5 7 5 2 (fun _ => 0x2480d0214711224460a170110f224421100180)
def z6 : PT:=(69,2,6,8,fun _ => 0x3c4a3447024406284a284626be4a0b1f1e2014144000463e26001c02262426383e164a1e38281ebe48002800281e260002291e28261e0248281dbe14821e9e0628063828263a46342428264a142e1c261e3e2828264a40341e1c26284b021c0648242ebe4a4abe4a472a4abe473e824b3e4a47373e9f3e4b373e9f3e833e4646463ebe4a463b369f3e9f2a833e9f2a4a064a262e28471ebf1ebf369f3e9f369f3ebf3ebf494541373329231f170f0b02fcf2eee4ded6cec6b8b4aca8a2989288827e7a787674706e6a68666462605c5a5856524e4c4a484642403e3c3834302c2a281c1814100c0804017f079abf83cadfe8e32ff4519fd938cbf83c65fe8a3bdf2d1def8f8ebf83c75fe8e2eff4517f79a8bfbcac5fde322efe0f177fa089fe9344ffa2e26fe0f137fa011bfcf08dfe8622ff41117f9f88fec7c47fa2622fe0f11f79903fbca01fde600fef2607f78a03fbcb81fde480fef1207f71103fbc401ff66807fb2a03fd8e01fec580ff62407fa2203fe8e00ff45807fa2403fd1001ef0400fb81807f40403fd2c01fe9a00ff4a807f89c03fd2001fe8d00ff47807fa3003fd1401fe0200fd4488edc180fae0a07f50301f702007d80c03f40401fc0100)
def w7:=lw0 10 34 6 7 5 2 (fun _ => 0x15ae102c11108243030b2e122d63742150450110247611183800a9c1e4410c00860036d1200)
def w8:=lw0 11 38 6 7 5 2 (fun _ => 0x18c90f862c1c2259090a43b084c24302a412447124648907051910d02b0308089c10040400840c0181)
def z7 : PT:=(12,1,6,7,fun _ => 0xf010704e8f3e00083828c48f3e0019f2806f8a1e0419f277c70f064c09f8252f8f003c09f820e7df4a00b9426881831c3cfdf033cb81063cf932e49180837c7cfbe04fc1013efd29509d33568ce141620280ff9aff95ff8cff8eff8bff89ff11ff88ff00f703fd01fe00)
def w9:=lw0 14 82 7 8 6 2 (fun _ => 0x214544e0480824004623c6d64800f3c2480348064754c7c2c80191c5e5482447a35422360808081588044011933561c480a503178295438501c3f402083281145210c8058684109288017453f748080736e0c2814c00a80280000001100c0)
def wa:=lw0 36 159 8 9 7 2 (fun _ => 0x2808a21081148a9c464f4449d0c1163d2e22e9c7530100393607416d08aa64590048b4050cc18b014cf2548d11910720d1891623b707cad14140f49218b8d01161aab0e0d00d210da7c822f22cf8322e4263c76a11502e381d47917720949e707001130f6171b040008a37d42b40436cd8548a131689f4a17419148a1621ec85032de8455c429961130b21fc0e0920848b228040189461001e1162c94890f88ab90d0ac0b084be9145340f84947b01a9148ba1610300021215010339011124031c0e031107110c1b000c260651000600292b0b02010f00)
def z8 : PT:=(1,0,6,2,fun _ => 0x9efe7f)
def wb:=lw0 10 41 6 6 4 2 (fun _ => 0xc64c1c120660cca4a42822305acb31200c283309e77e0c8cc5e711a32830c001180044040100)
def tz : Nat→ PT
| 24 => z2
| 28 => z3
| 31 => z4
| 32 => z5
| 35 => z6
| 39 => z7
| 43 => z8
| _ => ePT
def xy : Nat→ Nat→ Nat→ Option (Nat × Nat)
| 28,0 => w4
| 31,0 => w5
| 32,0 => w6
| 35,0 => w7
| 35,3 => w8
| 39,0 => w9
| 39,3 => wa
| 43,3 => wb
| _,_ => fun _ => none
abbrev k7:=blockG z0 tz xy sa
abbrev b4 (k tm s a b:Nat) := @blockG_merge z0 tz xy sa k tm s a b
set_option maxHeartbeats 0 in
lemma wc : k7 6 0 0 3=true:=chunkBlockG (ar:=7) (by decide +kernel)
lemma z9 : k7 6 0 0 3=true:=wc
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma wd : k7 7 0 0 17=true:=by apply cellsBlockG (ar:=8) (d:=1);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma za : k7 7 0 0 17=true:=wd
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma we : k7 7 3 0 18=true:=by apply cellsBlockG (ar:=7) (d:=1);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma zb : k7 7 3 0 18=true:=we
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma wf : k7 8 0 0 32=true:=by apply cellsBlockG (ar:=9) (d:=2);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma zd : k7 8 0 0 32=true:=wf
set_option maxHeartbeats 0 in
lemma wg : k7 8 3 0 8=true:=chunkBlockG (ar:=7) (by decide +kernel)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma wh : k7 8 3 8 61=true:=by apply cellsBlockG (ar:=8) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma ze : k7 8 3 0 69=true:=(b4 8 3 0 8 61 wg wh)
set_option maxHeartbeats 0 in
lemma wi : k7 9 3 0 3=true:=chunkBlockG (ar:=7) (by decide +kernel)
set_option maxHeartbeats 0 in
lemma wj : k7 9 3 3 9=true:=chunkBlockG (ar:=8) (by decide +kernel)
lemma zf : k7 9 3 0 12=true:=(b4 9 3 0 3 9 wi wj)
set_option maxHeartbeats 0 in
lemma wk : k7 10 3 0 1=true:=chunkBlockG (ar:=7) (by decide +kernel)
lemma zg : k7 10 3 0 1=true:=wk
lemma t191 : ∀ k ≤ 10,∀ tm ≤ 3,k7 k tm 0 (tz (4*k+tm)).1=true:=by
  intro k hk tm ht;interval_cases k <;> interval_cases tm <;> first | exact blockG_zero rfl | exact blockG_eq z9 rfl rfl rfl | exact blockG_eq za rfl rfl rfl | exact blockG_eq zb rfl rfl rfl | exact blockG_eq zd rfl rfl rfl | exact blockG_eq ze rfl rfl rfl | exact blockG_eq zf rfl rfl rfl | exact blockG_eq zg rfl rfl rfl
set_option maxHeartbeats 0 in
lemma zh : graphValid z0 (boundsBefore nm)=true:=by
  simp only [graphValid,Bool.and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces];repeat' apply And.intro;all_goals decide +kernel
set_option maxHeartbeats 0 in
lemma e7 : gq (vars 191) (graphGoal 191) 11 :=
  h8 (g:=z0) (i:=0) (hints:=536879361) (before_sound nm t7) zh w3 t191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def zi : List (Nat × List Nat):=[(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def t9:=fp nm 11 zi
set_option maxHeartbeats 0 in
lemma xz : jq t9:=gd t7 e7 (by decide +kernel)
def zj : List (Nat × List Nat):=[(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def ta:=fp t9 8 zj
set_option maxHeartbeats 0 in
lemma y0 : jq ta:=j3 (m:=251) (cap:=7) (ci:=(8,0,243,0,7)) (hints:=1358970881) xz (by decide +kernel) (by decide +kernel) (by decide +kernel)
def zk : List (Nat × List Nat):=[(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def np:=fp ta 12 zk
set_option maxHeartbeats 0 in
lemma tb : jq np:=j3 (m:=255) (cap:=11) (ci:=(64,0,191,0,11)) (hints:=553656577) y0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
def tc : IndexTree ColumnInfo:=(.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (.fork 3 (.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (.fork 7 (.fork 3 (.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (.fork 4 (.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (.fork 4 (.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (.fork 7 (.fork 3 (.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (.fork 4 (.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def rj : Array (List Nat):=Array.mk [[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def s383 : Nat→ Bits × Bits
| 0 => (r6 0xa300881f32c48d30de90073bc47b33,r6 0xa30088153280092096900012444b12)
| 1 => (r6 0x4041a306043c332c120feda2498943f,r6 0x4041a3040414220800044d220981429)
| 2 => (r6 0x283860c17983244309c7191cc720e7dc,r6 0x283860c13982244309c5190c8720e294)
| 3 => (r6 0x40c0030181fc387c0e07e1e0f83f07e0,r6 0x40c003000068103c0402e08078160560)
| 4 => (r6 0x8f007c01fe003f800ff801ff003ff800,r6 0x8f007c01ea002f800b68017f0029b000)
| 5 => (r6 0xf0007ffe00003ffff00001ffffc00000,r6 0xf000536400003ff6d00001ffed800000)
| 6 => (r6 0xffff800000003ffffffffe0000000000,r6 0xfad2000000003ddf7fffba0000000000)
| 8 => (r6 0xffffffffffffc0000000000000000000,r6 0x52dac9bff97c0000000000000000000)
| _ => (0,0)
def sb : Nat→ Option (List Sig)
| 0 => some [gf,j8,gg,gh,gi,j1,l7,l8]
| 1 => some [gf,j8,l7,l8,j1,gi,gg,gh]
| 2 => some [j8,gf,gi,gh,gg,l7,j1,l8]
| 3 => some [j8,gf,j1,l8,l7,gg,gi,gh]
| 4 => some [gh,l8,j1,gf,gi,gg,l7,j8]
| 5 => some [gh,l8,l7,j8,gg,gi,j1,gf]
| 6 => some [l8,gh,gg,j8,l7,j1,gi,gf]
| 7 => some [l8,gh,gi,gf,j1,l7,gg,j8]
| _ => none
lemma wl : ∀ p,sb p=(rj[p]?).map (fun perm => (vars 383).map (movedWord (perm.map swapRows).reverse)) :=
  rot_at_of (na:=8) (by decide +kernel) (fun p hp => by unfold sb;match p with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => omega | _+8 => rfl) rfl
def zl : Forest:=⟨383,12,s383,tc,rj⟩
def zn : PT:=(6,5,6,3,fun _ => 0x180350640181cd64802ce89f3d193b17a74bd9e268b13c735edc84c589e9d2f680a220422ed90154050011f4c80a8c1400)
def zo : PT:=(5,4,6,2,fun _ => 0x1e30c839d54cef9eb0088bafb0aa0a610bfcbc378810bfc0aa08810df5b38c1400)
def zp : PT:=(49,4,6,6,fun _ => 0x1d0c81d09c7a47c30058e80c4310c426f40160c8323e8390c80f0e40f0e43909c3935c380e4160a5280c9ba0c917f8c1a47c2447d28ae99e79a58e181e75c6da6996175d65544d245038d30b28a28a2892482071c71c71c71c70c09f6468c9d8bf749e8c9d8bcafaab02613cb7aaaf2613bd6ba358b13df4ad358b13af6bd268b13be6b9268b13f749e268b13af6bd098b13be6b9098b13cf6bd098b13de6b9098b138fbb709a788c77b33ba710ad7ba3ba710af3b73ba710cf6a7ac28108fbbe28a610adbba28a610aebb928a610af9b628a610afab528a610df4af3788109fcbe288810afcbd288810f74a0288810bf8b7288810afcbd098810cfcbd0988108efb93c03009de0ab12f00b760aa028009fc0aad28009fab7098c009de0ab11400df4b38c1400bf40a8c14009eeb93c0300be6b93c0300be6b9350300be6b9260300f749e260300bdcba2f0100f74a0280100bf8b7280100f74070301008f6bd098b138fcbd098810)
def wm:=lw0 2 17 5 6 3 3 (fun _ => 0xe041b10851860c60013501a11803)
def zq : PT:=(9,3,6,5,fun _ => 0x180487235718d4643517aa0f426160b860311a8d4627a0e8d42979c1cb4988205ffb32d8bdff3c11177feccbe23fbc650446ffa00888bfe1340217fc268003fbd046005ffb31400)
def wo:=lw0 2 11 4 6 3 3 (fun _ => 0x584b0c44c101b1420a)
def zr : PT:=(102,3,6,9,fun _ => 0x24160e86029c7ec85871d91a25c3a1d180503e161805860140b0c12a24130281e27098a06a241c8d448351d09c747a1784c62681a25cd0340b819f4181a875d0131205860228b89c3ae818c5c3016190a43a302a8742e3a0c0bc38311305c7418180d84c0f19099f418194a068300788470181a0987418109e874251a03c3a571c84c1efa8fca01f1f1c021ae127d0284d1f078e438d713c7e50fa1035c7006130a43a2f106a074161d0c75016078e82c321d03c68341002828050b01412265b87e3e421695d34161827c34651309c482f138c66e3a191a3c6b73478d74653d15d74e33b8c974322ba68ae9f7195cd06832a7d3e650bf678e30f18741d638d45fc7d98b896511f12ca23fe32b8e8f4571d1e8ae3a3d15c74573d0a0d057ec95c5068e3f43b3e392c68d1098341200fc7cbd9e8f2783b5d6e872b85bada6bb4d9ec96330d7ebd5d2d966b0572ad50a651a7d329648a391286401f0f476399bcd86833190c4602f974b6592b150a250279389a4c259249046229087c3d1e0ec763a1c8e06e361a8d06633190c4622f178a04a220f87034170a0441c0b03802efd896c5efda52d8b9fe793d17fd8de762ffb464ec5defb0088bddf6011173feb4222f7f4e8445ebfadaa139fe134a273fed2784f5fd54f09efda59e139ff684c277bec0984efbd79309ff6ad8b13fec6b1627fda7a2c4ffb134589ff6098b139fe134f11bde9cbe227fda50444ff3ca0889ff6917113febc22227f84d3886f7b3a710dee774e21bdc269c427fda50086f7a7a0109ff6850217fab0a0437dd053086fb28a610ff95f1021ff0de2043fe5044087fc288810ff81310213fcf28002f7d81400777a02800bf75c50017f6b4a002ff5614004ff3c8c00bbf622801fd6305002ff560a005feb38b00fed1916017fabe20027f9e01807f68b03009fe780201ff2200402ff5997805fead2f00bfc7940017f8268002ff5694005feaf2d00bfc7918017face3003fb17c6007f6a08c00ff93d18017f8263002ff598a005fe3c0300fed400601fda300c03fb1e01807f6350300fec5a0601fda780c03fb1301805fe3c0100ff9180201fd80c0403fe1e00807fc2f0100ff9400201ff0a00403fe0180804efb0088b97e1354277d8262c4e7b84d3885fc098810bbd625e017bac0a003bb5014005faae2800bf95a500177ac45003fa460a007f4030100)
def wp:=lw0 1 11 4 6 3 3 (fun _ => 0x50401451431050850)
def wq:=lw0 29 110 7 9 6 3 (fun _ => 0x3118f204bcd018ad1c31169780c311897c62124d8c53c192d0b0521d18c5c8631060703e1a150c5d409518502a220b378201e0b9551631468c448e905f386020c7b0d6046098346390029c062080881c620a1383d2a02188a05e21118c48e1b4f861aaa0134290795188c46204070c463cb00c40015c1746062db50840e2160100555831404603022428004040053000081000411c)
def zt : PT:=(43,2,6,9,fun _ => 0x3405da0c0807c49a3645850a0c2418c58e4771cd7649f40cb8f1e35a0dc745c7c805f40c0685850925c5cd49ce8bde84d5c7cb5e8a2a080d4715c989de8d67d5ea0bf671c9b40838cc875dedc5ca07c80a09098815de8c8ac7ca27ea0eaa1e8589d5dea978f1da0bc7e7c9d5ce869eaa0d0595c2ae850d0205c9c9469a0587492a1967d5ee85de85892699494749cd45f1c74eb43678cc080a092545cea471f438f64c05070e89f8c5c7c778ce8c85f1f43649c60a0927e945ce89b43678f1c809ce8c87ca1eb1f8c5da07f1f8d5c09dc7f8c7d5ce95deb43678da07f1ce87de95c7da0a1351dcf65a07f438f1ca06b6555a28d967f678de95c967f436555cda0907c5c5f8c7c7ca07ca0a07e8d8f43655f8f1e7ca07f43671f8da27e391788c0df6f5783b1cae169b3190c05e2c954a24ea511c843c1c8d05b2b94496481f8ec722f1508c38190b050241004003ffa58bffcb62fff9e8bffe762fff088bffe784fff2613ffe9e23ff2f88ffe8223ff8b88ffc2223ffa010ffca043ffa000ffca003ff8c00ffc5003ff0300ffc0403fe9d8bbfc222effa513bfe9e22ff0888bfe9c43fe8b00ffa2003fe2f00ffa8003fe2800ff8b403fe8c00ff85003fe0300ff80402bfaa13fda2c4ef7a710bee9843fc8810fd80c03fc0100)
def wr:=lw0 5 19 5 7 4 3 (fun _ => 0x38440f8818912084b78414484101800186a01c00)
def wt:=lw0 66 207 8 10 7 3 (fun _ => 0x3980e03d1982b586050094201ce10ab030141586cb7b885f12d1e1089211381094dd0402debe420206617432191d28c05b0a4140a0b9c984c8e338305d1c97b3405c0048662fd1f19a5d04460210261883a89b9d70493199141424b058249704ee68551503107254443b214c390fc0316435125d64c60015c63118a40b836c8801201130240603b0494ce2198202586126c662b83307e3c0002706e18030511352e2422f4cc97064400de3d10430068130280f128be07843e482390286b005850017012171174297b823102f1581d4c82232a5811d90178488700d237401942c8489502f050ec66504c04083c06066e6eb9cdc52f005c0d03e16b9e13c86084668d736010001080200010105021300001f5f000301020b56181a1e080b980e001e0800001803002f0c2c04050c04149d0c11000041151e05080219000051090c0000285902)
def zu : PT:=(6,1,6,6,fun _ => 0x1410747e3d0c764be33e5cbbaa1671c73ea0fa82ee9447c67d1d0b31f19f89958e30603ff17ff13ffc47fc43fe01fe00)
def wu:=lw0 47 108 7 9 6 3 (fun _ => 0x2b8e49c4e018db95860c020248603059040c00cd8a82e99ce18853138a26894120c08bb22b158ac3e2b101401c58158171bda05126530d8b47b18510b4a83a158623c564e15844568a7072437080ca240e020f09443c83021d060807f2a20a02d098882b240a0562b0e09056132c88c1a53900ac202b31868283800906004800400000001c18000005000404000080000d1250002242420200084ac00005010214002)
def zv : PT:=(1,0,6,3,fun _ => 0x74198e0ff)
def wv:=lw0 10 38 6 6 3 3 (fun _ => 0x186504821c6344235d0061861460e2401c1518c19c186186186186186000040080108000)
def v0 : Nat→ PT
| 31 => zn
| 32 => zo
| 35 => zp
| 36 => zq
| 39 => zr
| 43 => zt
| 47 => zu
| 51 => zv
| _ => ePT
def y1 : Nat→ Nat→ Nat→ Option (Nat × Nat)
| 35,3 => wm
| 36,0 => wo
| 39,0 => wp
| 39,3 => wq
| 43,0 => wr
| 43,3 => wt
| 47,3 => wu
| 51,3 => wv
| _,_ => fun _ => none
abbrev j9:=blockG zl v0 y1 sb
abbrev td (k tm s a b:Nat) := @blockG_merge zl v0 y1 sb k tm s a b
set_option maxHeartbeats 0 in
lemma ww : j9 7 3 0 6=true:=chunkBlockG (ar:=7) (by decide +kernel)
lemma zw : j9 7 3 0 6=true:=ww
set_option maxHeartbeats 0 in
lemma wx : j9 8 0 0 5=true:=chunkBlockG (ar:=9) (by decide +kernel)
lemma zx : j9 8 0 0 5=true:=wx
set_option maxHeartbeats 0 in
lemma wy : j9 8 3 0 2=true:=chunkBlockG (ar:=7) (by decide +kernel)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma wz : j9 8 3 2 47=true:=by apply cellsBlockG (ar:=8) (d:=2);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma zy : j9 8 3 0 49=true:=(td 8 3 0 2 47 wy wz)
set_option maxHeartbeats 0 in
lemma x0 : j9 9 0 0 9=true:=chunkBlockG (ar:=10) (by decide +kernel)
lemma zz : j9 9 0 0 9=true:=x0
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma x1 : j9 9 3 0 13=true:=by apply cellsBlockG (ar:=8) (d:=1);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma v1 : j9 9 3 13 89=true:=by apply cellsBlockG (ar:=9) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma a2 : j9 9 3 0 102=true:=(td 9 3 0 13 89 x1 v1)
set_option maxHeartbeats 0 in
lemma x2 : j9 10 3 0 7=true:=chunkBlockG (ar:=8) (by decide +kernel)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma x3 : j9 10 3 7 16=true:=by apply cellsBlockG (ar:=9) (d:=1);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma v2 : j9 10 3 23 20=true:=by apply cellsBlockG (ar:=10) (d:=1);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma a3 : j9 10 3 0 43=true:=(td 10 3 0 7 36 x2 (td 10 3 7 16 20 x3 v2))
set_option maxHeartbeats 0 in
lemma x4 : j9 11 3 0 1=true:=chunkBlockG (ar:=8) (by decide +kernel)
set_option maxHeartbeats 0 in
lemma x5 : j9 11 3 1 5=true:=chunkBlockG (ar:=9) (by decide +kernel)
lemma a4 : j9 11 3 0 6=true:=(td 11 3 0 1 5 x4 x5)
set_option maxHeartbeats 0 in
lemma x6 : j9 12 3 0 1=true:=chunkBlockG (ar:=8) (by decide +kernel)
lemma a5 : j9 12 3 0 1=true:=x6
lemma t383 : ∀ k ≤ 12,∀ tm ≤ 3,j9 k tm 0 (v0 (4*k+tm)).1=true:=by
  intro k hk tm ht;interval_cases k <;> interval_cases tm <;> first | exact blockG_zero rfl | exact blockG_eq zw rfl rfl rfl | exact blockG_eq zx rfl rfl rfl | exact blockG_eq zy rfl rfl rfl | exact blockG_eq zz rfl rfl rfl | exact blockG_eq a2 rfl rfl rfl | exact blockG_eq a3 rfl rfl rfl | exact blockG_eq a4 rfl rfl rfl | exact blockG_eq a5 rfl rfl rfl
set_option maxHeartbeats 0 in
lemma a6 : graphValid zl (boundsBefore np)=true:=by
  simp only [graphValid,Bool.and_eq_true];refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces];repeat' apply And.intro;all_goals decide +kernel
set_option maxHeartbeats 0 in
lemma e8 : gq (vars 383) (graphGoal 383) 13 :=
  h8 (g:=zl) (i:=0) (hints:=12901687553) (before_sound np tb) a6 wl t383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def a7 : List (Nat × List Nat):=[(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383:=fp np 13 a7
set_option maxHeartbeats 0 in
lemma valid383 : jq known383:=gd tb e8 (by decide +kernel)
def deadsamples : Nat→ Bits × Bits
| 0 => (0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480)
| 1 => (0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201)
| 2 => (0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002)
| 3 => (0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028)
| 4 => (0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45)
| 5 => (0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002)
| 6 => (0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c)
| 7 => (0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54)
| 8 => (0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)
| _ => (0,0)
def deadautos : Array (List Nat):=Array.mk [[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def rotS0 : List Sig:=[gf,j8,gg,gh,gi,j1,l7,jt,l8]
def rotS1 : List Sig:=[gf,j1,l8,gh,gi,j8,jt,l7,gg]
def rotS2 : List Sig:=[j8,gf,j1,l8,l7,gg,gi,jt,gh]
def rotS3 : List Sig:=[j8,gg,gh,l8,l7,gf,jt,gi,j1]
def rotS4 : List Sig:=[gg,j8,gf,j1,jt,gh,l7,gi,l8]
def rotS5 : List Sig:=[gg,gh,l8,j1,jt,j8,gi,l7,gf]
def rotS6 : List Sig:=[gh,gg,j8,gf,gi,l8,jt,l7,j1]
def rotS7 : List Sig:=[gh,l8,j1,gf,gi,gg,l7,jt,j8]
def rotS8 : List Sig:=[j1,gf,j8,gg,jt,l8,gi,l7,gh]
def rotS9 : List Sig:=[j1,l8,gh,gg,jt,gf,l7,gi,j8]
def e9 : List Sig:=[l8,gh,gg,j8,l7,j1,gi,jt,gf]
def rotS11 : List Sig:=[l8,j1,gf,j8,l7,gh,jt,gi,gg]
def rotDS : Nat→ Option (List Sig)
  | 0 => some rotS0 | 1 => some rotS1 | 2 => some rotS2 | 3 => some rotS3
  | 4 => some rotS4 | 5 => some rotS5 | 6 => some rotS6 | 7 => some rotS7
  | 8 => some rotS8 | 9 => some rotS9 | 10 => some e9 | 11 => some rotS11
  | _ => none
lemma rotDS_at : ∀ p,rotDS p=(deadautos[p]?).map (fun perm => (vars 511).map (movedWord (perm.map swapRows).reverse)) :=
  rot_at_of (na:=12) (by decide +kernel) (fun p hp => by unfold rotDS;match p with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => omega | _+12 => rfl) rfl
def deadcolumns : IndexTree ColumnInfo := (.fork 58 (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(0,16,486,9,10),(1,0,510,0,12),(1,2,440,68,7)]) (.leaf [(1,16,486,8,9),(1,32,94,384,7),(2,0,509,0,12),(2,1,460,48,7)])) (.fork 3 (.leaf [(2,4,369,136,7),(2,64,189,256,9),(4,0,507,0,12)]) (.leaf [(4,16,482,9,7),(5,2,440,64,6),(6,0,505,0,9),(6,16,480,9,6)]))) (.fork 7 (.fork 3 (.leaf [(8,0,503,0,12),(8,16,486,1,9),(9,16,486,0,8)]) (.leaf [(10,0,501,0,8),(10,4,369,128,6),(10,16,484,1,6),(10,64,181,256,6)])) (.fork 4 (.leaf [(12,16,482,1,6),(13,16,482,0,5),(14,0,497,0,7),(14,16,480,1,5)]) (.leaf [(14,64,177,256,5),(15,16,480,0,4),(16,0,495,0,13),(17,0,494,0,11)])))) (.fork 14 (.fork 7 (.fork 3 (.leaf [(17,2,424,68,6),(18,0,493,0,9),(18,1,460,32,6)]) (.leaf [(19,0,492,0,8),(19,64,172,256,5),(21,2,424,64,5),(24,0,487,0,11)])) (.fork 3 (.leaf [(27,0,484,0,5),(31,0,480,0,4),(32,0,479,0,12)]) (.leaf [(32,1,460,18,7),(32,16,454,9,7),(34,1,460,16,6),(35,0,476,0,7)]))) (.fork 7 (.fork 3 (.leaf [(38,128,345,0,5),(40,16,454,1,6),(41,16,454,0,5)]) (.leaf [(49,0,462,0,8),(50,1,460,0,5),(64,0,447,0,13),(65,2,440,4,6)])) (.fork 4 (.leaf [(66,0,445,0,11),(69,2,440,0,5),(70,0,441,0,8),(72,16,422,1,6)]) (.leaf [(81,0,430,0,8),(83,0,428,0,7),(84,8,163,256,5),(85,2,424,0,4)]))))) (.fork 29 (.fork 14 (.fork 7 (.fork 3 (.leaf [(87,0,424,0,4),(96,1,396,18,6),(98,1,396,16,5)]) (.leaf [(114,1,396,0,4),(115,0,396,0,4),(128,0,383,0,13),(129,2,312,68,6)])) (.fork 3 (.leaf [(130,0,381,0,9),(130,1,332,48,6),(130,4,369,8,6)]) (.leaf [(132,0,379,0,11),(133,2,312,64,5),(134,0,377,0,8),(136,16,358,1,6)]))) (.fork 7 (.fork 3 (.leaf [(138,4,369,0,5),(140,16,354,1,5),(141,16,354,0,4)]) (.leaf [(144,0,367,0,11),(145,0,366,0,8),(147,0,364,0,5),(154,4,353,0,4)])) (.fork 4 (.leaf [(156,0,355,0,7),(160,0,351,0,11),(160,16,326,9,6),(162,1,332,16,5)]) (.leaf [(168,16,326,1,5),(169,16,326,0,4),(177,0,334,0,7),(178,1,332,0,4)])))) (.fork 15 (.fork 7 (.fork 3 (.leaf [(192,0,319,0,11),(193,2,312,4,5),(197,2,312,0,4)]) (.leaf [(198,0,313,0,7),(202,4,305,0,4),(256,0,255,0,12),(257,32,94,128,6)])) (.fork 4 (.leaf [(258,0,189,0,8),(258,64,189,0,8),(262,64,185,0,5),(264,16,230,1,6)]) (.leaf [(265,16,230,0,5),(270,64,177,0,4),(272,8,227,4,6),(275,64,172,0,4)]))) (.fork 7 (.fork 3 (.leaf [(276,8,227,0,5),(288,16,198,9,6),(296,16,198,1,5)]) (.leaf [(297,16,198,0,4),(320,0,191,0,11),(320,16,166,9,6),(329,16,166,0,4)])) (.fork 4 (.leaf [(339,0,172,0,4),(340,8,163,0,4),(344,0,167,0,7),(385,32,94,0,5)]) (.leaf [(400,8,99,4,5),(401,32,78,0,4),(404,8,99,0,4),(449,32,30,0,4)]))))))
def dead : Forest := ⟨511,13,deadsamples,deadcolumns,deadautos⟩
set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]; repeat' apply And.intro; all_goals decide +kernel
def qL32 : PT := (3,7,7,1,fun _ => 0x40ceee0948bd2498c8f8eef60948bd1498c8f8ee7648c8bd10b948f8e)
def qL36 : PT := (53,6,7,6,fun _ => 0xfae7a63c49e2403be017df9efcf4c040808c04424fe01f009efd10a7a65d30638f60f0e032405fc0202c3d34044f4ce05702f80500be01387471c71c71430c30c303ef3cebae38db4c30baebacb2caa89a48a28a079c69659449040e30a206102077658d8cc6318f8eff853f2b17291f1ddf86323704c63e3aff26e5145c647c77f64a3ab8b8c8f8eff49395517191f1dfb86ae9a36323e3aff26dd5c5c647c777e1cd8cc1318f8ecfcb991984631f1dff12528a2e323e3bfd24cce45c647c767ae8bd00ba58f8ebfc9b75517191f1d1dbf7433129a3e3aff26c5145c647c77fe0948b498c8f8ebfc9b95717191f1d7f9362a62e323e3bfd251ce45c647c76f6994d1498c8f8eef4b1b198a631f1dbfa2532926323e3b3b6c66885ca47c767e5cccbc2318f8ecf5b38bb33191f1dbf933e2d26323e3bbf246c65f98c7c7476f0d5d07948f8efc8f532b41571f1d7f9362722e323e3bfb255c5c64f47c77fe094a68b8c8f8efd8d57532b171f1ddf902e322e523e3bff04a464fc5c7c75fc6d8a9958b8f8eff89395317191f1d9dba2f442e523e3b7b4d5aa634647c77f644e8c8b948f8e8edfba1985291f1dff0a9a562e523e3bfb25155c5c647c77f464e958b948f8eddd329a493191f1dfb92a6ae2e323e3b2b7d96885ca47c7656fb4d10b948f8efd874f2b294d1f1df1b696ae7ad23e3bf31d055c6d347c767e6cd8b0ba68f8e)
def qH0_36 := lw0 1 5 3 6 2 4 (fun _ => 0x8600610)
def qL39 : PT := (31,6,7,5,fun _ => 0x1100133081840c20029003184381e13bc08304002cc10a0801ce82117bdce6b16b52527314a418c41084200000000019e96697666323e3bbf04585814647c777648b8cc6318f8eddc31ba493191f1ddf822e3304c63e3bbd245c6628e47c767e4cacbc2318f8efdc1161005191f1d9f92332b08c63e3bbd245c66298c7c77e648b8c07088f8e8fd9acbb33191f1d5f9384c62e323e3b7d245e824c647c777648b070b8c8f8edec917a293191f1dbb922f4926323e3bbd2458305c647c76fc4cf8b498c8f8edfc0a9178d191f1dfe122e3018163e3bb720405c5c647c777c48b050b8c8f8edec9a3169f191f1dff0016300a2e3e3bfd003460145c7c77f60078c028b8f8efe880f180b171f1dfb102230162e3e3bf9245c60303c7c77ea4088c068b8f8e)
def qH0_39 := lw0 1 5 3 6 2 4 (fun _ => 0x8618610)
def qL40 : PT := (271,5,7,9,fun _ => 0x26c18140a575c13c0a78706ff8700a837d0238078041440b81980481bb43804f014efcac81650dd2141161548234380e18040a401a87387036b87019804703e1560dec3b073804154e9b01608169ac3b6fc0138050dc1bf80402f873807017872c388df8041b804c22387002d082a15699c380a56fe88f0140890176fc8220838058140088dc6278041980480d407787002c04d0df80437d8178041cf08c9541ba0dce9b01608169804e62780401a0b802f804e9b0140080a58700a405380569a81401c0756981c6c3902281669a81462780780662402f80521408a0816c00740480b0157804369efc01f8738050218141a30716fc00a8716266278078041c407581413defe045c39eff87180019804816413c0641cc13c01e8160dd6fc04c01c01f804145870154a1407402f80569a81419387004c0f2ec037e6998160df8040038040b38041cf8066fc0ae6fc0de07180780400301608002f80419983c0a8882c3815515436921400b80583c15437ec39eff0701bf804e27014882c39ec000804b87082037f804957806c3b8078738040038701c70140f002e0ba1550df870014e25ac98141cd62402e08002d80013d6fc8dc18e08037c1ba6c037f8078078040a787269981780569a15662436b80680401c0a404b8738066980b3807807873807870efc63b8066fd81437c36b87001c0aa0bb80787001180037ce27806872871814a1400875c37c11f804157804e2701401c6ff8078040a3806cf66b258ec560af572b75aac55eab52a8d469f4da5d2a9349a3d168743a1506813d9e4ee75399c4de6f359a4ca612f974b6592a94ca24f2692c9243208f476391a8c45e2d1589c4a23108843a190a8441e0b0481c0a03007f3f5f6f97c3dde8f2783b9d6e974399cae471b85c0df6f379badb6db65aed56a351a8d268b419ece66b2d94c96431d8ec5613057ebe5f2f578bb5dae970b75aad168b4592c15ead562b156aa5429d4ca65228d44a04f27132984b2512691482391a8c452210c8441a09007e3e1ecf4793c1d8e873391c4de6e369acd46933998cc653218cc66230980be5e2e96cb4592c15caa5429948a04f271309448239148843210fc7c3d1e0e870371b0d46833190c4602e168b056291409c4c2512088401e0e870361a0c8602e15098482210070301409040180a0301003fcd8ca99c8f8ef6beba66723e3bf6dab8ca38f8effb27a2e2a3e3b76f8cc6318f8e9fbf33129e3e3bdedb493a58f8eff966932323e3b76f59c4a68f8eddbd3d3a523e3bfe695028b8f8edfb6302e9a3e3afeed2998b8f8eb7bf328ad23e3bf6d8c4e948f8ef7b6967ad23e3afeed09f8b8f8eff9a322e523e3a7efd5a9948f8eff966a32ae3e3bfe6959f8b8f8ebfb832662e3e3bbafba999c8f8edfba32fcc63e3b7edc48ca38f8edfaf3704c63e3bd6fa3aeab8f8e9fbf442e9a3e3afedd2498c8f8eebbe9aeaae3e3adefcca5b48f8efdb93a2e523e3bfe6cb958b8f8efbae529e9a3e3bfae8b9ca38f8edfb71e328e3e3bd6faba2b48f8efdb6ae327a3e3bfeaa68b948f8eff9a562e523e3a7efd20b948f8eff974236323e3bfaeaa8b9c8f8e9fbf442e523e3b7ed8dc0318f8efb9e9a569e3e3adefd0a9ae8f8eddbf093a523e3b7eec68b948f8ed7bed302a63e3be6fa6a0ab8f8edfb63306aa3e3a7efd1c2a68f8efdba7a7e2e3e3bfe695998b8f8efdb6ae328a3e3bfae8b999c8f8edfbb1e2e523e3adefd1a9ae8f8eff963422323e3b5efb4c19e8f8eff966a32523e3bd6f9f9eb48f8e9fbf302eae3e3b5efb40b948f8eff9a562e2a3e3b7ee8bc0a98f8edf3e530a8a3e3b7ee8bc1318f8edfbb1e2e2a3e3a7efcf0ba68f8eff9a322e9a3e3bfce8ba99c8f8eddbf1d3a523e3becfaba99c8f8ef5bec93a523e3bfc79495a78f8ebfbb4a7e2e3e3b7e7c695a78f8effaa9a662e3e3bcefaba9b48f8ef3be9a96d23e3beeda98cab8f8eddbeaf02823e3b7e78cc2318f8eff8e9a36323e3bcefaba9ae8f8effb22e4e963e3b7af8cc5318f8e9fbd74140a3e3bd6fa2aeab8f8eff2d32529a3e3b7ee8b0ba58f8efeb6aa32723e3b7ee0b8bab8f8eff966816323e3b5ef0baeab8f8effa6327e523e3bfe58d058c8f8ed7bf1aba723e3aeefd1a7a68f8eff968a36323e3bf6dab8a9e8f8efbae96529a3e3bfce938b948f8efdbaae2e7a3e3bfe59c8d8c8f8edfb71e32723e3b7eec78b9e8f8e9fbf342e9a3e3bfe6a6958b8f8ef9bea67aae3e3a7ef0cc1ab8f8ef6beba728e3e3bfe5948d8c8f8e9fbf47129e3e3a7ef0cc4ab8f8eff966aa6323e3b5efb40bab8f8eff9a8e562e3e3bfe6d0958b8f8edfbb022e523e3bfcd948ca28f8efd9eae36823e3becfab95a98f8eff9aae562e3e3afedd14f8c8f8ebfbb2e7e2e3e3b5efb20b948f8edfb6302e523e3bfea9f8b948f8effa65126323e3b7ee8bc4aa8f8eff973e36323e3bfe5aa8d8c8f8eff9aaa562e3e3afedcf498c8f8edfba2c2e9a3e3bfaea3998b8f8edebe3714c63e3beeea68bab8f8eff969a36323e3bfe5a98d8c8f8ed7bf16baae3e3adefd29eb48f8edfb70632723e3b5efb40ba68f8e9fbc3304c63e3bfe5ab8d8c8f8e9fbd7652ae3e3bfe5d28d8c8f8efdb64e7aae3e3bfe68c088b8f8efbae96369a3e3bdafaaae9c8f8efdb6af1a323e3b7ed0b8c9c8f8efdb6ae967a3e3bdebb494a68f8ecfbf06eaaa3e3a7ef0cc2948f8eff8e82369a3e3afebcf8da68f8edfb70632ae3e3beebab8da68f8ed7bed302523e3bfec8ba59e8f8ecfbee82e9a3e3a7ef0cc2ab8f8eb7bf4a8ad23e3bcefaba5b48f8eff2e9a4e523e3b7ed8cc1318f8ef73ed24e523e3b7ee0b8b948f8efdba8a2eae3e3b7e7a0c2948f8ef7ae527eca3e3bfe68c8bab8f8efd3e553a523e3beeea98bab8f8efbaeae669a3e3b7eec48bab8f8eff9b32562e3e3bf6ea38bab8f8eddbc2d3a523e3bdcf94a2b48f8ef5be7abaae3e3b7eec58bab8f8eff9a96562e3e3a7efcd0b948f8edfb706328a3e3b7e702c2318f8eff966a328a3e3beeb99a7a68f8edfb71e328a3e3b76fd10b948f8edbbeaf129a3e3b7e78ac2318f8edfbb1a2e723e3bfcba694a28f8eddbd670a523e3a7ef5d05a68f8e9fbf470a523e3b7ed0b8cab8f8eb7bf3e7eca3e3afedd04c8c8f8edf9e3708c63e3bf6ba64e948f8ef73e72a6ba3e3b7af02c5318f8ef7b62a7ad23e3b76fc54e948f8ef5bed13a523e3beeda68cab8f8efbba9a962e3e3bfe5318d8c8f8eff3a8a2e523e3b7eec58b948f8e9fbc330a9a3e3bd6fab9eb48f8efb9e6a9e9a3e3bfe98c99a68f8edebe2b14c63e3a7ef0cc4a68f8eff2e567e523e3b7e7cbc2318f8ef7aed27e523e3a7efccc4ab8f8efeb672328e3e3afebd29f948f8efeb63266723e3bdcf94a2b28f8e9fbc33068a3e3b7ee8abf318f8edfac3304c63e3b7eb8cc1318f8eddbe3718c63e3b7ebcbc1318f8effa632529a3e3bfcb9594a68f8efbaeae529a3e3b76f02c6318f8eddbe2b18c63e3a7efccc2318f8ebfb732a6323e3b7cf95c4a68f8ed7bed3129a3e3be6fa6a3ab8f8edf9f3308c63e3b7eb02c1318f8edfae2b04c63e3b7eb8dc1318f8eff1e8256a63e3a7efcd0bab8f8e9fbf3c2eae3e3bfe5a68c9a8f8ef9be9a7aae3e3b7ee02bf318f8edfba36fcc63e3b5efb4c1ab8f8eff9a32a62e3e3be6fa9a3ab8f8eff1e8256523e3be6fa0a9ab8f8efd9e5682ae3e3bcefaba6b48f8e9fbd74200a3e3af6fd10b948f8e9fbd7422523e3afafd04ca68f8e)
def qH0_40 := lw0 19 60 6 11 7 4 (fun _ => 0x1300d0420040d81803e0740902d05e0680802c05401c170020660780e054912150050220640142a02002e044118000101502a014026abc1200b0120ac0200e04e0300a8160520181a02803203c1882506000f504061401308c0444401de100081)
def qL43 : PT := (251,5,7,9,fun _ => 0x1017807806803805c3b805c3b80780601419816580006b871c3b8701b08401640a5c380b680063b87301780701401c01387387005981581701743b8700a586c0b580743b016017805817806627807805c398158050038078078078701b0816a178048701c40e504008b4380b287002c8400a5c380b78058177736fc04c1648428010158158401a5805003806802f7103ef400dc06b8068701b1817805a1780701405c16006b0178701668001ce8038720700a40e780743af400dc1b9814046803805c380080b4c380080b7439801814fa806b8068038068001641b80cc06804c83c197807439c3b8074380e037c0e422006b805a168028010158041cd8001ba80183c0e40b806a01786d8001c41ba8001a40c406981743b8041080e78041a2f400f006981780680180503eefee998701bb806e988701cc05c0601ba80387037c02c05e03d03ea158018158422141ba8001280800440cc068221c380cc0680440cc06b0000cc0440698028030152178703780e437e03d0de8000440080681a18001640680080f580487004d03c1641a4008152ec2f410400e70140081a404c1cc0f40bc1b81b38718001cd8001cc0f503d03d00280101701503f87022006881584022181584022006b8700501b1815841817005805a168140b78718038700481b0188009a178718000a5c380b78701b187387006c0180b78718140b581584004d03c1950018168722c806b071043071043071043071043071042042cf66b2d92c762b0d82bf5eaed72b157ab552a54fa7536994ba55268d45a25128742a0d02813f9e4ee753a9cce26f369b4d66933994ca633097cbe5d2d964ae532893c9e4f269349a47219047233188bc4a231087436190b85426090381c0600ff7f3f5fafc7cbe1eef479bc9deee76ba9d2e873b99c6e06fb7dbcdd6eb6db4d96c355a6d067b399acc65b218cc562b1186c260b017abc5d2e16eb65aac55eaf572b558ac552a54aa451a8942a04e26d30954a24d1e8e46a31188a4320902803f1ecf4773b9dcec753a1cce470369b0d2653298cc45d2d95cac54289409c4d2592c9648239188a44219088241200f8783b1c8dc6c34190c4602f170b0562a1489c4c251208c441f0e87036180b8542610078381a0b0481c0a0300803ced0108ae8f8efd8c0c081e3e3beab0206088f8ecebf1428723e3bea70803068f8effa22c08063e3bfa30203068f8eff2a2c08163e3bf270703068f8ef93c141c223e3bced0801b48f8eff90722e323e3af6bd14f028f8efb3a2c14223e3b7e58cc2318f8eff922e328e3e3b7ea8bc1318f8eff1a54162e3e3b7e68b0b958f8ede9c0f14723e3bccf0508ae8f8efb2c2008163e3bceb0208ae8f8e9dbf442e523e3b7e503c0318f8e97bd740ad23e3baeb08020a8f8ef3aed008223e3bdabae06028f8ef2bc1822ba3e3bf2e06078b8f8efea630081a3e3a7ed0cc0318f8edf9b2b08c63e3bb8fba05068f8efea8081a2e3e3bbcb5102058f8ef63c141aba3e3bdcd0501ae8f8efcac18081e3e3bdcbb202058f8efda630081e3e3bfc30302058f8edf96302e363e3bee90802018f8efe2c1808163e3bfc98c02058f8efaba2c18223e3bdcbb402058f8eedaee8081e3e3becd8c05088f8ee73d7016d23e3bec70803058f8ef9b4041c223e3bfe10302018f8edf972f08c63e3bde9ae01028f8edeb71404723e3bacf050a088f8efd341c16323e3bee50103088f8eedac1c082a3e3ba6f070a088f8eff922f12323e3afe6cd938b8f8efbb004222e3e3bfc6958b948f8edeba2f14c63e3be670307088f8ef33ed020163e3bfe48c8b948f8efb9a54222e3e3bd6d0107ae8f8ed5bebb18c63e3bfc6a9958b8f8ee9bee81c223e3b4ef5d08ae8f8ef9ac20081e3e3bf658c078d8f8eff92300a2e3e3bee30203088f8eef1d440c163e3b7ec8cbf318f8ef4bed0181e3e3bf870503068f8edf940708c63e3becd0105088f8eeb3d7014223e3bd4f0507ae8f8ebfa5531a323e3bdcb0502ae8f8edd9c0f18c63e3bfe48c9f8b8f8efd9a541e2e3e3b7ab02c5318f8eff92324e2e3e3bfc90502018f8eff3004162e3e3bfe48bc78c8f8ef5aed0081e3e3bfe18d498c8f8eff922c06563e3bf690702018f8edfb22f00c63e3b7e68bc2318f8efd38141e2e3e3b6ed080b8c8f8ecf9c2b08c63e3bd6bb202078f8efab63018223e3af6dd14f8c8f8efa3c1418223e3bee68c088b8f8ef8bc181c223e3bfe48c998b8f8ebf373d26323e3bfa58c9aaa8f8efd1c1c0c163e3bf6c01078b8f8efdaa2c081e3e3bf650703018f8efe38141a2e3e3a7edcb0b998f8edf963308723e3bf0f0506078f8efcb630181e3e3b7ad01c5318f8eff86300a363e3b3eebf0a318f8ef7a6d008063e3bbe9ba02018f8eff929a2e323e3bfc68c058b8f8e9fb73700c63e3b7ae8bc51c8f8ef5b41c06d23e3bbce5c058b8f8ecebc2b14c63e3bfe48b4f8c8f8eff92322e2a3e3bbcb05020a8f8ef6aed0081a3e3beea02088b8f8eff14040c163e3bf8d8c06058f8eff922e327a3e3bf4b0502078f8eff922d32323e3bd8fb406058f8e9dbd741e523e3bf668c078b8f8eebb6e804223e3bfe19a028c8f8eff922f1a323e3bf4d0701058f8eff922f16323e3bfe48bc18c8f8eff8a300a2e3e3afe9cb4f028f8eff869a36323e3bee58c089a8f8edfb2fc04c63e3b3ed0ac0318f8efba4200a323e3b5afb4c51c8f8eff922d26323e3afecca498c8f8e9ebc3314723e3be6e8b07088f8ebeb74126323e3af6dd1498c8f8efe9a2e541a3e3aeedd2498c8f8eed3c14281e3e3b7e90b028c8f8efe941a36323e3bee58c088d8f8ef1bc1c22ba3e3b7e50b8d8c8f8edfa40b00c63e3a7afd00ba58f8ebf974236323e3bfe295028b8f8eff902e2e323e3bfe42e8b8c8f8eddb41c2e323e3bfe49c8b8c8f8eecbee8181e3e3bfe48b088c8f8eff928a2e323e3bfe48ba58c8f8ef4bc181eba3e3bfe4a98b8c8f8eff9230162e3e3b7e68bc21c8f8eff92aa2e323e3aeafd049088f8eff92ae2e323e3b7cd050b8c8f8edeb4182e323e3bfe4318b8c8f8edf96682e323e3bfc59a058c8f8ee73d7016ba3e3bfc58c058d8f8ef7340416d23e3bd4f0705b48f8efd96681e323e3be6d8c07088f8edabc2314723e3b7ad8cc51c8f8ed7b6bb00c63e3b7e58c0b9a8f8ed7af4f04c63e3b7e58cc22e8f8ede9c0f14c63e3b7ad8cc5318f8ed6bebb14c63e3bc6fb408078f8eef341406ea3e3baebba02088f8edfa40704c63e3b5eebfae318f8edf8c0f04c63e3b3eb0ac1318f8e9fac3304c63e3b7e98cc1318f8e97bd7422ba3e3b7e68b0b8c8f8eddb40718c63e3b76b02c6318f8ecdbc2b18c63e3b76e8bc6318f8eddb63318c63e3b7eabf02318f8edf8f0808c63e3a7eecac2318f8e9f9c3308c63e3b5e7aec2318f8ed7aebb04c63e3bfa58c999a8f8ed7ad740ad23e3bd4fb207058f8edf980efcc63e3a7ed5d998c8f8efb9230222e3e3bf648c078b8f8efe92301a2e3e3bfc48c058b8f8eff82300a2e3e3b7e40b8b8c8f8e)
def qH0_43 := lw0 23 50 6 11 7 4 (fun _ => 0x2406c0f82d0600b00880d056150170100120500601e0400c4108050521500e01505e1500e80601e0201200a0680a01980404a08c2a01802c0a80981a032038110270a801c70da0000410040823c2002000002000180)
def qH3_43 := lw0 11 40 6 9 5 4 (fun _ => 0x8130f87c141508000381f0700832050f81818080c05c360f0f81c3e1f0e834160304848221e0087c341f0a0589002101000180040)
def qL44 : PT := (164,4,7,9,fun _ => 0x8e1206d0880ab0015902cc38770dfe01052a170e61c0520082a9d71beaca2a9a6c028000a8880326fc19ab21be0b30e1ea77e2220403c1be741590020a400a2a8881b56fc03ab23d4086046010a38041640804271044408c0219cc4861c380a812847043020df815c3802e1700ac02802dfbbf34c01c14e1c00404ce8088810eff0080218c6242a83306a0570e61c02600b0e0151110203683350a05e079dc8ab8040a8880338044405200f804068023120b30e1dc08f8706301d8ab6fd59208111154ebc001be6240981208a055590220520082a8475640770082c50a82010c0050a2300161cb7e05d078c608a7130e1bf00431b0084fc396fc238551101640cc081101ac010659640b04461cc028dc1e0880aa1570e21c06a37d10189c020a0ee18900e04c0900b05202f0e1d7111870c4e0108402f0e00756405d0783300eac82005550b87107a1c00eefc038331108ba07a8500e77014601400eff0e035441021171dc0de37ddf835838222041dc07837e0e0880b3020378df3b96fcc4e1c83903d5902545c698c4e01b7ea146f84db7f87142a8540036810bbfc3837c22ab2c3804c011890aa83c30dbfc38efd07e1cb7e011593bf564155dfe011680fb0e03cc3883c1f0df0092c863022c021480e8290488b860e0103a3070084002600b0e08c00587014802c380cd1b8df3898730e6010740a5dfe1c11800b0e08c005804ee015c3805405e1c02b87142e1cc3819cc4e1cc38a15593b0c380cd590df38980700e011bf2c80ea2045c6270e1dc3898701661c0040a70e068c39a1cfe77399acc6572591c7633178ac3e13017ebd5e2eb72b85b6d568b3d92c35fae56aaf54a8d3a9747a250a813e9d4de6b32974b2572892c92431e8dc66311689c4219098340e04fe7e3e5ecf4793bddaeb74b99c6e06eb6db0d76b34d9ecc64b1986bf5f2f174b75a2c960ae552a148a24f26d2c9347a35128642204fe7d3d1d8e871371acd06531180be5d2d968ae55299449c4b24114843f1e0e46e36198c45c2b14094462110074361a0c054261208838180a038140400ff7d35047c77fbe7e723e3bfdf53571f1dfefa5a68f8eff7cad347c77fbc2eae3e3bfdf272b1f1dfefc7a08f8eff7c9d5c7c77fbea68e3e3bfdf81571f1dfef8da28f8eff7a7ca47c77fbe36aa3e3bfdf33571f1dfef95ab8f8eff7ca5547c77fbe72ae3e3bfdf4b451f1dfef8ca28f8eff7ca51c7c77fbe66523e3bfde05551f1dfefa6a28f8eff7e2d5c7c77fbe56aa3e3bfdf3f551f1dfefa9a68f8eff78153c7c77fbc162a3e3bfdf41551f1dfef8dab8f8eff78118c7c77fbe9aae3e3bfdf294d1f1dfef8c318f8eff7d15547c77fbf06a63e3bfdf15451f1dfefa9948f8eff7814d47c77fbea6323e3bfdf1a631f1dfef05aa8f8eff7ccc6c7c77fbc228a3e3bfdf83571f1dfef8d9c8f8eff7ccd147c77fbf1a9a3e3bfdf14631f1dfef95028f8eff7845047c77fbe2a823e3bfdf4f451f1dfefa5ab8f8eff7cd5147c77fbe8e9a3e3bfdf19291f1dfefa58d8f8eff7c9d047c77fbe96823e3bfdf89571f1dfef99958f8eff7c55347c77fbc222a3e3bfdf1b291f1dfef9e948f8eff7e05047c77fbe2aae3e3bfdf29411f1dfefa7ab8f8eff7d4d047c77fbe368e3e3bfde39551f1dfef05a58f8eff7cad1c7c77fbf029e3e3bfdf39411f1dfef94ab8f8eff7e2d047c77fbe6a9a3e3bfde0b4d1f1dfef0ba68f8eff7c65347c77fbe4e9a3e3bfdf4f471f1dfef9ea68f8eff7e155c7c77fbf029a3e3bfdf1b4d1f1dfef99a68f8eff7e04a47c77fbe9e9a3e3bfdf854d1f1dfefc4a68f8eff78e4d47c77fbf169a3e3bfde994d1f1dfefc48d8f8eff782cd47c77fbe6aae3e3bfdf29351f1dfef9ca68f8eff7cfcd47c77fbea66a3e3bfde11291f1dfefa5a78f8eff782c6c7c77fbc2e523e3bfdf15291f1dfef089e8f8eff7c9ca47c77fbe66823e3bfdf832b1f1dfefa5948f8eff7c655c7c77fbe56523e3bfdf4f291f1dfefc2948f8eff7ce4a47c77fbf16523e3bfdf8d291f1dfefc7948f8eff7814e47c77fbf02563e3bfdf2b391f1dfefa79c8f8eff7d4ce47c77fbe367a3e3bfdf2b3d1f1dfef058c8f8eff7d3cf47c77fbea67a3e3bfde11191f1dfef8aa78f8eff7c9d3c7c77fbe669e3e3bfdf3f4f1f1dfefc1a78f8eff7cc82c7c77fbf1a9e3e3bfdf2b151f1dfefa98a8f8eff78446c7c77fbe4e363e3bfdf531b1f1dfefc58d8f8eff7e3c6c7c77fbc0aa63e3bfdf27531f1dfefa5a98f8eff7e054c7c77fbe66a63e3bfdf3f531f1dfefc5a98f8eff7e354c7c77fbe56963e3bfde0a051f1dfef08028f8eff7844fc7c77fbe567e3e3bfdf26111f1dfefc5958f8e)
def qH0_44 := lw0 66 141 8 14 10 4 (fun _ => 0xd8041420a029c088024c07151d002d008820a027c09901a807501700c001540e9008401303364d700700b503b40cb02700f7015c007010c01e00140ba002645f01340c502a00c4029001a0370081001006d01200aa03e808700580bd00900e253900b692d00fc43400e7082820a01b0097017809b00bc0d3041009208280590828014003804403440ac039400100480ee019003a01e80a001dc000042410a012404600a10d9006c00301380fd00fc00800300780258011020000d037c0be00180e152c4091002c0da031c03c0130002082807900c4089020c01802cc06302bc0b9014420a93a80a908280fb030802a02ec03601d801d040004010000000307040e00010004000100030601020a040202000006050803010e010d17060f00040405080215000002060005110101030901080b000200000d04)
def qL47 : PT := (402,4,7,11,fun _ => 0xc390830e3b080aefc6fc1096416432c010a40e42cc0f072a15dfb8980a0f06fc1077f0146f83c8210030e0df80a12805a050861504460100002ce20698018702a8540d10002c81ac390030e0070012c83661cc38050014000d98702f843017870e205205503c1e9b0c3814c1ce1c3600b30e0390051560006c00036a2f81abb96fd0283c40613b0e20081069844033c388404281106206803a85073699c48dfc388420461cc396fd001a631387207865c0283c2f855802174148598218730e285c3980507da60260482ca10b618701600bc38842dfe1c0e9804eb8650a41541ca00c38771c4c058000dc2a61c0e869b008150cb43834bd056503c32e1c06ce9a2f8da03517cc708800e0081ee1c038220361dcb4ce2502a373b87130e40f0cb0230e3dc77e8720783940102202c001b41a607c05078194ee3bf80b0001e01ac388010040806e1b30e40577f17e0861c80a37c3481e50b17c6f8554001c22f82c0ca1670e0df31d80434c01062068344000b206805989c021290040841f872ee5bf0260482ca103a00de07839800a145940f0ca0790000740a0f000054c380741e85541e0f4304b20a800800007c4183cf50558021d207859c3900142c5f37e638038040421630e61c0041a4016010de150c4e1c8018702e9a6c02194088020358722f8df0ba770039a6c398702c84ab7f870c70070086fd5906561c1482a1b01be1b2004b2c381481c843016154c70070621942a8880058702a400c398730e28580b17c2a40050b8730e01700406adf9890cf8720783908a15444002c3812a2f8310420602a85502a1970e60141f0030e200b7ec381e21084180507807564194c4e010b219405e1c4201a01e4000aa068062b20342202003cc388418720507880c2760141ee99e241006f871005a6c3804edf833420232dfe1cc021a0e206f0358730e61cc388141e20309d8700388501014c32e0f00f8802c8557b808202c00168152eb8374208150185b0002203645f96412942cb20ab03c32c08c380086f9d7c388410061cb7ea17008df01671034dea8001a02781a4460f46f85280a1502adbfc3819de203c80a0000d0070080b032859c3987001054b1312c1e2100180080d04550a0e55940f0cb17c0382c0ca1670e20f18c0e70e6010c21301ce1c8018700101a0041d02aa0f0e437f0e2101101a02a81a76187202bd781e194026010921943a0370d98730e61cc398738708807b7700984506e8430e00740a83c1ea1c0d103c2c81a811871d348507303e873c406e1a40f20002221500059034154328170300e4343d0035871ee3bf43903c1cbdc438f420783977e1a30e40f0721a1003ea0348030e3dc760f430e40f0738730e61c0168141e1c44218730e61c0843041cc00c392c911856c396c30e00c3880e70e3ea030150ee3b0b7f8701ce1cc3862700818072771d83d0c3903c1ce1c761870ee1bfc3903c1ce1c07837c1c8df0732141981a81e15659039c398706f839c020006d069838801000df34d8043488800587034e1c0180080d61c9641941b81a08303d590567b8efe0783c838068630397b8082873c481e0f607bd0c38060361dc37e0f00b81a31c2203661c03814a1183d7b8f401bc1008b438254010001d00d0000540a41ce1c0bcf4207ab2072ac81984e36011f0e03901601e02869c398730e40056401c6d01ac388830e5dc61d6fe59210c3862459065c38a160061c400acb0e61cc398046d069c39871002b2c388030e401800fa82a81ac38801595b0c398720e200400ac8ee6010000f025220c398730e5bf4381a1078394008810001ec3987107e1c41e1670e61c3b80e70e1dcc020005a0544018710061c0018701483946e8401bc100261480804506f016081ea5650430e4108bf2ca0801fc1e7a82ac5f965040f540582187208055c028dc1a80f1be1641bc05821880161ea0ab17e1bcb2821883079ea0aa0de08037821883079ea0ab17f0e60146f883079ea0aaaca086054207411be0f0167a82a868c406246f8180ab8720861c821016084058218720848582012442817030164082374218720860146f8051b8528381a02983c020aca084b24218061be1c4210720850e8218051b83782143a0841c82071202c10565040e240582117f0e61c4218051bc5fc3883d1be054218730e4058212c90840f86f8061ba1cf7fec0084738e51c235c688cb18a30c5b8ad15228c4d88f11621c3f87d0f21c43786d0ca18c2c85109211c1f83705e08c1081d02602c027fafedfd3f87e6fc5f7bea7d2fa1f3be67c8f7deebd97aef4de83ce790f1de13c0778eeddb3af758e9dd13a0736e65cab91716e29c4b8770ae11c037f6f8de9bbb766e0db1b4b656c2d7daeb576a6d45a734c68ed11a0b3e66eccd99330650c9590b1e63ac658b31561cc3585b09606c017eafb5f0bd5782ec5d4ba5742e75c8b8970ae05bab5d6aad1598b25642c6588b0d5fabc572ad5592ad554a955029e534a654c292522a3d45289510a1d432825029f13ba714dc9ad342654c89812f2594ae9552824b492915222424788d919a2f4588a51322043a8710c21642683905a0740a804fe9fa3f27e0fb9f63ea7c8f69ec3d078cf09de3b275ce91d039a728e49c437e6e8db1b435c6b4d61ab34c694d21a3340678cd99a330654c898c316628c31802fe5f4bc1772e85c8b796b2d45a4b39632c2580ae1582ae550a995129e52ca294327a4e09993025e4ac939242404708d91622643c8590a212420831032044007d8fa1ee3d87a0f31e23c0778ee1d63a8748e71cc3906f8de1b83686c8d71aa340670cd19831c630c41843045f8bd1782e45c0b31622bc558a914e2885009d1362604a09111c230458891082083f07a0ec1d03906e0d81a8330640c41802e0560a81482804e098128220420800f81e0360680c81802e0580a8140260480880f81d0340600b0140240400700d01802804006008003f9e0b4f1f1dfeb02058f8eef7ca5a47c75fbf068e3e3b7df3d751f1dfed998c8f8eff680cfc7c777beaed23e3bbdf4d691f1dfcf05a68f8eef7cfda47c777beba8a3e3afdf8e391f1dfcf052e8f8eff3cad047c77fb630ba3e3bfd605571f1dfeb02a68f8eef7d75547c77f3c16ae3e3bfce07471f1dfed8caa8f8ef778455c7c77bbe9aae3e3bbdf27691f1d7efc0a68f8efb783c647c75fbf02ae3e3bfdb18631f1ddef1cb28f8eef7d74a47c77fb404223e3bf9e0b551f1d7efc2ab8f8eff685c647c77bbe969a3e3bedf41571f1dfcf059a8f8eff3c981c7c76fbc2a523e3afdf8b411f1dfe703318f8ef77d4d5c7c76fbe9aea3e3bfce07391f1df6f07a78f8eff680d5c7c77bbc22823e3bfce06391f1dfed8ca68f8ef778452c7c77f3e56523e3bdde11291f1df6fa3ab8f8eff6c9cf47c77f3d3c163e3bbde0b691f1dfeb02a28f8ebf7e2d5c7c77fbaa62e3e3bbdf33691f1df6f95078f8eef7815947c75fbf06ae3e3afdf85551f1df6f9eab8f8ebf7e24d47c77dbc1e6a3e3bfdb27191f1dfe703aa8f8eef7845747c777be72d23e3bbde05691f1dfed01a78f8edf7855147c77dbc1eaa3e3bfdd17551f1dfaf06ab8f8eef7ca5947c77ebc1a363e3bbdf53691f1dfed01058f8efb7d155c7c76fbc2aae3e3afde17571f1dfcf95a98f8edf7c55d47c77fb630723e3bfcf1b411f1dfeb02aa8f8eff3818147c77fb632523e3b7df4b751f1dfed01318f8efd7cccd47c76fbc28c63e3bbdf5c631f1d7efc0318f8eff74598c7c777bc16ca3e3afdf82631f1dbefa3ba8f8eff5814647c77fb4069a3e3afdf894d1f1dfeda98c8f8ebf7e118c7c77fac08c63e3bfce07571f1dfaf9caa8f8ebf785c647c77f9c0e8a3e3bfd7294d1f1df6f079c8f8eff6cfc647c77fac0a523e3afdf8b291f1dfee8ba28f8eff3d3cd47c77f9c0e663e3afdf81451f1dfcf94a28f8ebf7e0d147c75fbf0a8a3e3bede0f4d1f1dfed01a08f8efe782d047c77fb4068a3e3bbdf45651f1dfed012e8f8efb78403c7c77ebc1a823e3afdf83191f1d7efc0a08f8eff5cfca47c75fbf06823e3afdf89571f1d7efc5a28f8efe78102c7c77f9c0e9a3e3bdde114d1f1dbef0aa68f8eff745d347c77f9c0c163e3bfd7334d1f1dfaf99a38f8ef77d3d347c77fba2c723e3bbdf15691f1d7efc2a68f8eef7e45347c77f9c0cba3e3bfdd4b171f1deef08a98f8edf7851747c77fb632ae3e3bfd605151f1dfe703948f8ebf7e11747c77f3e54163e3bf9e0b471f1deef95088f8ef77845147c777beba9a3e3bdde11471f1d7efc1aa8f8efb7a74a47c777bc16ba3e3bfdd17471f1ddefaea38f8ebf785cd47c777be7eca3e3bfda03531f1d7efc19a8f8eff5814d47c75fbf0a523e3bdde98111f1dfed01948f8ebf7e21747c77fba2cba3e3bfdd17391f1ddefa2b48f8efe782ca47c77ebc1a523e3bbde39691f1d7ef0b948f8eff6c65147c77fba2eae3e3afdf805d1f1dfcf93948f8eef7d2da47c75fbc2e9a3e3bbdf5d3d1f1deef9f088f8ebf7e04a47c77bbc20723e3afdf80391f1dbefbaab8f8eff5c6d347c75fbf08723e3bf9f4a0b1f1ddefa3b48f8ebf7e25547c76fbeeaaa3e3bf9e0b151f1dfeb02958f8eff5814e47c77f3c16723e3bdde11391f1d7ef0b9c8f8eff6c64e47c77bbc229e3e3bbdf5d391f1dfed028c8f8ef77844d47c77dbe7e7a3e3bfdc11171f1dbef0a1c8f8eff6a4c647c77ebe728e3e3bfdb83191f1dfed4c8c8f8eff381c547c77fb712323e3bfdb8b191f1dfedc68c8f8eff6a7c647c77bbd24223e3bfdb8f191f1dfe7039e8f8efe782cf47c77fac0a7a3e3bbdf5d571f1deef089e8f8eff58146c7c77dbc1e523e3afde173d1f1dfaf06a68f8eff745cf47c77fac0a823e3bfd6054b1f1dfed8a9e8f8eff682c647c77fb6967a3e3bf9e0b191f1deef088c8f8eff6c54647c77fb696323e3bede0f531f1df6fa5078f8ebf7e24647c77bbc22363e3afdf8a391f1d7ef0ba58f8eff3c6c647c75fbf1e323e3bfd6054f1f1dfaf06a78f8ebf785ccc7c75fbc2e9e3e3b7de14111f1dbef0aa98f8eff3cad3c7c75fbf129e3e3bede0f151f1d7ef0b8a8f8eff5c98147c77f3ea6723e3bfdd17151f1ddef9eb48f8eff70145c7c75fbf067a3e3bfdc0b171f1dfed088c8f8ebf785c6c7c77ebe6aaa3e3bfd605471f1dfee938b8f8eff74cc5c7c77fba7e2e3e3b7de5d751f1ddef93ae8f8eff381d4c7c777be96ba3e3bbdf335d1f1d7efc0a98f8eef7d4d747c77fb406363e3bf9e0b1b1f1df6f078d8f8efd7830e47c777beba2a3e3bdde04111f1deef05088f8eff745ca47c77ebe7c1a3e3bf5f33391f1deef93088f8eff6808e47c77ebc1a8a3e3bddf32111f1dfaf06a98f8eff58154c7c77f3c16a63e3afde17531f1dfed01028f8efe78402c7c77f3e64163e3bf9f3e0b1f1dfcf49058f8edf7815d47c77dbe4c1e3e3bedf320f1f1dfe703a58f8efd7830147c76fbc280a3e3bfd732051f1d7ef0ba08f8efd7828347c77ebe541a3e3bfce073f1f1dfed8c9e8f8edf7854fc7c76fbc28163e3bf9f260b1f1dfeb02088f8eff3818447c77fb6328e3e3bdde11151f1dfed93a58f8eff680cac7c75fbc2e563e3bfd698051f1dfeb4f028f8ebf785c9c7c76f3c28163e3b75e0d751f1dfe68b8c8f8eeb783da47c776bc1ad23e3bf5a0d191f1ddcf05b28f8ebf75f98c7c775bc1eca3e3b9de11691f1dbeb02ba8f8efa78382c7c77db4041e3e3bfcb19351f1ddeb02b48f8ebf3e118c7c777ac0aca3e3aedf8c631f1dbed01ba8f8eff600c5c7c75faf04c63e3bdd604111f1dfcd01058f8ebd7e298c7c777b406d23e3bece060f1f1dbcf51058f8ebf6e018c7c75ebf14723e3beda0f191f1deed088c8f8eee782da47c7773c16ba3e3bf9a0b191f1d7ed0b8c8f8eff2c6c647c76dbc281e3e3bfd205191f1deed01088f8efc78302c7c77f9a562e3e3bbda035d1f1dfe503018f8efd5810347c77f8c0c0a3e3bfd405171f1dfce058b8f8ef978303c7c77eb81a2e3e3bedc0f171f1deee088b8f8eef5815747c776bc1aba3e3bade0f5d1f1decf05088f8ef73818447c77abc18223e3bcde0e111f1daef0a088f8efe38182c7c77f2c08163e3bed6040f1f1dcef08ae8f8efd3818347c76fac082a3e3bfd204031f1dfe48b8c8f8e)
def qH0_47 := lw0 92 300 9 14 10 4 (fun _ => 0x3780f200d409600a80ca00340ec08280d0039006803e406b016005d025403d0050023011c06408280a5022e45f014c20a027020a0828021021c02800d803a01840dc082820a00d0004034c082026c20a00c80da03600cf02a00f801dc20a02680bd03640a601f00840058013009020a023803702b410903180eb0104026082810a034820a039808392d020a04140ef00cc071026420a02e401902dc0f402140ed02500b6013400f935c0f6003004602fc093023c02702f01020278011021820a00e407352c4025006805b013c0ae03f80ee02c409702340af00240b401880a2007c05602a80cd032c00e00c404b03c405e03ec0a4042003f43400e2024004502864ea041009800a420a01b00fa018c0ba00140e001ec4f803a8038022020a01b4066004820a082820a012547401fc0b013c400a019c0e30828007024405c017c02200700c1013005702cc20a03440e7436410e041c0a000740c502ec0c300f00c7024803001bc0e50310051040407e00b401b08280a7010008a03a401502e010304354e401540c0040002b00b002f020007601a403e02a407d027c0fd04180f3082810b01c805a023003b02240dd01480b203dc0480108050010c074005c0ce032410c01500d400180ac02ac01802f80db01380d601a80df012846f01d406003fc07000b80d5002c0cc02040c203d400801e80c801b80e800800e101e0010028c059007809d01940d708280f01485c4e0c000b006010705c181c000280a0a02818100b23010041e000b40201211bc020002844121503078560500800001202804082c0f8d406010000022010405406000886c1e000600804070000c283c168040000171288e00001280202208043602090140c01)
def qH3_47 := lw0 52 318 9 12 8 4 (fun _ => 0xa607504800b1c908b02b0010fb0d707a0730c90190fb0fb03d0e207f0130d40ad0be09e0760a107809a0c601116303e0fb0030680fb08206c03f0370fb0420310fb07c0fa0850890fb0fb05c0800fb0290430fb0d80590640ba07e0050270cb00c0320af0e80b70940080b00fb0fb01d0a206b0db0160fb0630a40fb0e71780f50fb0a50f109b0b80770fb0020220fb0fb0fb0fb08300d0c10860e00fb0570170e30fb0ea0fb0980fb0fb1d80cc0440880fb0bb0250fb06e0c50ef0dc0610040ec0fb04e08d01f06d0fb0390600fb0240b905e06a04f0930140ab0cf0000550740710c70d10520fb0fb0fb0fb0bd0fb0fb0df0fb0fb0d90fb0920c307b0c80b305b06502f0fb0910c00b107d07000a0a80400960fb04502c09f0ee0060fb0e10fb0ca04b0d60fb0fb01b0fb0b40840fb03504c0fb02a0fb0e90790f40f30bc06901a02e0fb0fb09506606206704a04d09d0da03b0970fb0580330180fb0de0eb0300a00810aa0f808f0fb0fb0bf0340510150b50f70a30a90380f90a704902805d02109005409c0e40d50f00f60ed01200e1af0cd06f03a0fb01005a0460410260f201c0d20200ae0530fb0070c40dd0360fb0e60fb0d007208c02d01e0e505f0fb0ac0870b200f08e0560b60230090c208a0d303c0990500ce0fb047000100236348496a0009800542d1a1ec5a06182881c0d0003000050e8100c34010000a100501c081a000783841058bc58012600002ac0082c1806)
def qL51 : PT := (40,3,7,8,fun _ => 0x771c483e1c148450dddc7400883cdf16437771c487068ac853041a66260fefe201a21c7a9dc0818983c688dc55001d011637871c4129dc6980b83e37871c4699c4014df83c450dc5f625ea03dd08de1c1a5dc7421c062b213c107718e805d0114180dda66261cefc68ac86f041dc69a017101303c450dddc699890160f6fc52114377703c6260183cdf740371a0006243306055771bf741c483e1c8dddc6998980435efcdf03c3737e01741c483dd70dc0b1a000095c4871ea1285f698007a9c483e1c8dddc14d89871d06feb213c107120f8dc550022083dea15408efe0f7a83717dea741c483dbf87237807bfac81083dc48de1c807bf83c37efc0f0de017abbf83c376fdd083dc48de1c83dd08de1c17fbf7720f8de1c015c4ac81043bbfac810873bfec010871d0ac810017bf17c0f0dc05efdeaac810faf3ece5ddd6cfc8c1b9b2aba39b928a847d746d655d54504b463e3a36322f2a24201a16120e0a0500fef938f8efef998f8efef958f8efef088f8efef058f8efef9f8f8efef028f8efefa58f8efefa98f8efef8d8f8efef8a8f8efefa78f8efef8c8f8efef9e8f8efef9c8f8efef1c8f8efef948f8efef9a8f8efefa38f8efef2e8f8efefa68f8efefa08f8efefa28f8efef318f8efefaa8f8efefab8f8efe7038f8efeb028f8efed018f8ebef0a8f8efaf068f8ef6f078f8efcf058f8eeef088f8edefae8f8efee8b8f8efed8c8f8ebefba8f8edefb28f8edefb48f8e)
def qH0_51 := lw0 82 181 8 14 10 4 (fun _ => 0x47000c041004403200ac05f005c06c08d806b00800680118236009400d006409a005000e003c08000b804c019805b010004800000580278236013c06508d803908d80760024236008c08d021002d004808e025802402200a00114060004004b021407801b405e00dc09b027006701a407e0240082016400501cc03a016802101e408601b808b022407c019003001c404a025c063020c03408d801d00d802c08d804908d8236024401f01402360138051001801a00f80a301a8031015800a024c029015007400d407f00fc092015c075022807b0098061010804300e001801e801e009c07d00cc0980174055023c09400a823608d805c011005202640a2002003b005407008d808108d809d004c072003003c0010022018801600700950284002000406f01dc08c00a002f021c01b08d803d027c007002c04d014c2360d0004000105031b05030004011b0a000000050a000000140e050101020a090b0a01000000000b09050c01000e000204080201000c0500010a0105040608011b0c1426010001010d00010402000e04030500)
def qH3_51 := lw0 206 417 9 13 9 4 (fun _ => 0x3b44600660440b180ba0750a3835c2060b901580681ec0160ad838009616b09f83883040c004b834413805e03702882641270c180b00c207c05a85d425c010013858828806908c80cc204035055832c1f617701480f011a121008820422e03a01e862c2b018105c063406017006e04e85981560bd05801d810402d82681a602406501dc1de0e80bd862828a0e307881101aa01d00101bc10013b093029029a00705d82940100fc09605380c011b067805002e05207a02740400ba05b02c42ca14306e82540d610c01f007812609404805b804a18e0a900283000a109c836425011306703c030c0c4026014c2be08c0c484141b01360b385f002602607f85b02a808705f031c1220e601a00b40a20b208a82fc11603b05485e40d007a01c84200c808a03f064023e0ae08780142d41530c204dc26211a0bf01682b2100036059007e08303d802414602105002b02de01f00701081b409259204e0166142041018c03013c0c903e00901120a0821419a02f08584501dc07600d851808a0cc0c883cc1860b709e84780f214b02e052801e11802783243100a704c83c8220078058001800818f0ae85a418202804b02f031817d02b017c0d4163099829830a04d01883a41d40230c9003008200d0c901c0324050090023832413404d815c26a10a0bf856805c12b0b305401c80370bb045809c03808682a830e07309505c425a05506802d04b61570af03ac2f0040120819c05411111c04740da06206f82a0092173032855424814906a01281ea10107e83e808e08f084848817a05900085c823815c09281181840220a402100e20ad06d835806401c03902241bc12304c027c1ee0c50b403182800e10948cec0fe07409804f806c0e7097815029e0860b6810c71a3350058054032003087039400001203e841c2a20af0b0834813c10607f03e419017402c0530020000004000e030a00000010441a0001004040e00800004c010001009818000000008240403000010e10003a80e00000cc18666b8780a0000008020200804b011200000402020009a02178c000000885014050f00000001a0000c00018188a0a010140e00048180a150302c0015138a03c2200030042c0f80426050780000060b0003e0429b441c02030005403020480000010601a000005002000300006080d0400c01000000205090140205000000004048143008548000022008000002000bc04061680c0006060000c010504c0a1101000000f02018005c00854000068800041b0106c0a00)
def qL55 : PT := (1,2,7,3,fun _ => 0x1bf078706f07ef8f8e)
def qH3_55 := lw0 10 50 6 10 6 4 (fun _ => 0x741308c27044000781b0840f094040a0160041900828070280300707c1a05c0302c050342601828080120a0080a00e0902805428024280a014040220600a0c800a00a140212)
def qLv : Nat → PT
| 32 => qL32
| 36 => qL36
| 39 => qL39
| 40 => qL40
| 43 => qL43
| 44 => qL44
| 47 => qL47
| 51 => qL51
| 55 => qL55
| _ => ePT
def qIx : Nat → Nat → Nat → Option (Nat × Nat)
| 36,0 => qH0_36
| 39,0 => qH0_39
| 40,0 => qH0_40
| 43,0 => qH0_43
| 43,3 => qH3_43
| 44,0 => qH0_44
| 47,0 => qH0_47
| 47,3 => qH3_47
| 51,0 => qH0_51
| 51,3 => qH3_51
| 55,3 => qH3_55
| _,_ => fun _ => none
abbrev qB := blockG dead qLv qIx rotDS
abbrev qM (k tm s a b : Nat) := @blockG_merge dead qLv qIx rotDS k tm s a b
set_option maxHeartbeats 0 in
lemma qc32_0 : qB 8 0 0 3=true:=chunkBlockG (ar:=9) (by decide +kernel)
lemma qa32 : qB 8 0 0 3=true:=qc32_0
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc36_0 : qB 9 0 0 53=true:=by apply cellsBlockG (ar:=10) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma qa36 : qB 9 0 0 53=true:=qc36_0
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc39_0 : qB 9 3 0 31=true:=by apply cellsBlockG (ar:=9) (d:=2);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma qa39 : qB 9 3 0 31=true:=qc39_0
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc40_0 : qB 10 0 0 96=true:=by apply cellsBlockG (ar:=11) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc40_96 : qB 10 0 96 96=true:=by apply cellsBlockG (ar:=11) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc40_192 : qB 10 0 192 79=true:=by apply cellsBlockG (ar:=11) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma qa40 : qB 10 0 0 271=true:=(qM 10 0 0 96 175 qc40_0 (qM 10 0 96 96 79 qc40_96 qc40_192))
set_option maxHeartbeats 0 in
lemma qc43_0 : qB 10 3 0 6=true:=chunkBlockG (ar:=9) (by decide +kernel)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc43_6 : qB 10 3 6 96=true:=by apply cellsBlockG (ar:=10) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc43_102 : qB 10 3 102 96=true:=by apply cellsBlockG (ar:=10) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc43_198 : qB 10 3 198 53=true:=by apply cellsBlockG (ar:=10) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma qa43 : qB 10 3 0 251=true:=(qM 10 3 0 102 149 (qM 10 3 0 6 96 qc43_0 qc43_6) (qM 10 3 102 96 53 qc43_102 qc43_198))
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc44_0 : qB 11 0 0 96=true:=by apply cellsBlockG (ar:=12) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc44_96 : qB 11 0 96 68=true:=by apply cellsBlockG (ar:=12) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma qa44 : qB 11 0 0 164=true:=(qM 11 0 0 96 68 qc44_0 qc44_96)
set_option maxHeartbeats 0 in
lemma qc47_0 : qB 11 3 0 1=true:=chunkBlockG (ar:=9) (by decide +kernel)
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc47_1 : qB 11 3 1 66=true:=by apply cellsBlockG (ar:=10) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc47_67 : qB 11 3 67 96=true:=by apply cellsBlockG (ar:=11) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc47_163 : qB 11 3 163 96=true:=by apply cellsBlockG (ar:=11) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc47_259 : qB 11 3 259 96=true:=by apply cellsBlockG (ar:=11) (d:=3);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc47_355 : qB 11 3 355 47=true:=by apply cellsBlockG (ar:=11) (d:=2);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma qa47 : qB 11 3 0 402=true:=(qM 11 3 0 163 239 (qM 11 3 0 1 162 qc47_0 (qM 11 3 1 66 96 qc47_1 qc47_67)) (qM 11 3 163 96 143 qc47_163 (qM 11 3 259 96 47 qc47_259 qc47_355)))
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc51_0 : qB 12 3 0 14=true:=by apply cellsBlockG (ar:=10) (d:=1);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
set_option maxRecDepth 16384 in set_option maxHeartbeats 0 in
lemma qc51_14 : qB 12 3 14 26=true:=by apply cellsBlockG (ar:=11) (d:=2);simp only [cellsG,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd];repeat' apply And.intro;all_goals decide +kernel
lemma qa51 : qB 12 3 0 40=true:=(qM 12 3 0 14 26 qc51_0 qc51_14)
set_option maxHeartbeats 0 in
lemma qc55_0 : qB 13 3 0 1=true:=chunkBlockG (ar:=10) (by decide +kernel)
lemma qa55 : qB 13 3 0 1=true:=qc55_0
lemma tablesq : ∀ k ≤ 13,∀ tm ≤ 3,qB k tm 0 (qLv (4*k+tm)).1=true:=by
  intro k hk tm ht;interval_cases k <;> interval_cases tm <;> first | exact blockG_zero rfl | exact blockG_eq qa32 rfl rfl rfl | exact blockG_eq qa36 rfl rfl rfl | exact blockG_eq qa39 rfl rfl rfl | exact blockG_eq qa40 rfl rfl rfl | exact blockG_eq qa43 rfl rfl rfl | exact blockG_eq qa44 rfl rfl rfl | exact blockG_eq qa47 rfl rfl rfl | exact blockG_eq qa51 rfl rfl rfl | exact blockG_eq qa55 rfl rfl rfl

def gw0 : Sig := bin true (inputs.getD 0 zero) (inputs.getD 4 zero)
def gw1 : Sig := bin true (inputs.getD 4 zero) (inputs.getD 1 zero)
def liveRoot : List Sig := inputs.take 4 ++ inputs.drop 5 ++ [gw0, gw1]
def bankRoot : List Sig := inputs.take 4 ++ [zero] ++ inputs.drop 5 ++ [gw0, gw1]

def witRoot : Nat → Row × Row
  | 0 => (⟨16, by decide⟩, ⟨17, by decide⟩)
  | 1 => (⟨20, by decide⟩, ⟨22, by decide⟩)
  | 2 => (⟨2, by decide⟩, ⟨6, by decide⟩)
  | 3 => (⟨4, by decide⟩, ⟨12, by decide⟩)
  | 4 => (⟨1, by decide⟩, ⟨33, by decide⟩)
  | 5 => (⟨2, by decide⟩, ⟨66, by decide⟩)
  | 6 => (⟨4, by decide⟩, ⟨132, by decide⟩)
  | 7 => (⟨8, by decide⟩, ⟨264, by decide⟩)
  | 8 => (⟨10, by decide⟩, ⟨26, by decide⟩)
  | 9 => (⟨1, by decide⟩, ⟨17, by decide⟩)
  | _ => (⟨0, by decide⟩, ⟨0, by decide⟩)

theorem witRoot_ok :
    (List.finRange 10).all (fun i =>
      let p := witRoot i.val
      (bit p.1 graph != bit p.2 graph) &&
      liveRoot.all (fun w => w == liveRoot.getD i.val zero || bit p.1 w == bit p.2 w)) = true := by
  decide +kernel

theorem liveRoot_len : liveRoot.length = 10 := by
  rw [liveRoot, List.length_append, List.length_append, List.length_take, List.length_drop, ← input_list, List.length_ofFn]; rfl

theorem noRoot : ImpossibleT graph 13 3 liveRoot.toFinset := by
  have hall := forestG_all dead qLv qIx rotDS 13 (boundsBefore known383)
    (before_sound known383 valid383) geomdead rotDS_at tablesq 13 (by decide) 3 (by decide) 0 (by decide)
  have htgt : graphGoal dead.mask = graph := by decide +kernel
  have hs : sameWords (stateSetG dead qLv (4 * 13 + 3) 0 (vars dead.mask)) liveRoot = true := by decide +kernel
  rw [htgt, sameWords_sound hs] at hall
  exact hall

theorem bit_gw0 (r : Row) : bit r gw0 = (sample r 0 || sample r 4) := by
  simp only [gw0, bit_bin, ite_true, sample]; rfl
theorem bit_gw1 (r : Row) : bit r gw1 = (sample r 4 || sample r 1) := by
  simp only [gw1, bit_bin, ite_true, sample]; rfl
theorem edge_list_eq (x : Fin 9 → Bool) :
    ([((0 : Fin 9), (1 : Fin 9)), ((1 : Fin 9), (2 : Fin 9)), ((2 : Fin 9), (3 : Fin 9)), ((3 : Fin 9), (4 : Fin 9)), ((4 : Fin 9), (0 : Fin 9)), ((0 : Fin 9), (5 : Fin 9)), ((1 : Fin 9), (6 : Fin 9)), ((2 : Fin 9), (7 : Fin 9)), ((3 : Fin 9), (8 : Fin 9)), ((5 : Fin 9), (7 : Fin 9)), ((6 : Fin 9), (8 : Fin 9)), ((8 : Fin 9), (5 : Fin 9))].any fun p => x p.1 && x p.2) = edge x := by
  simp [edge, Bool.or_assoc]

theorem bankRoot_map (r : Row) :
    bankRoot.map (bit r) = List.ofFn (Function.update (sample r) (4 : Fin 9) false) ++ [(sample r 0 || sample r 4), (sample r 4 || sample r 1)] := by
  have htake : (inputs.take 4).map (bit r) = (List.ofFn (sample r)).take 4 := by
    rw [List.map_take, ← sampled]
  have hdrop : (inputs.drop 5).map (bit r) = (List.ofFn (sample r)).drop 5 := by
    rw [List.map_drop, ← sampled]
  have hupd : List.ofFn (Function.update (sample r) (4 : Fin 9) false) =
      (List.ofFn (sample r)).take 4 ++ [false] ++ (List.ofFn (sample r)).drop 5 := by
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp only [List.getElem_ofFn, Function.update]
      have hi9 : i < 9 := by simpa using hi1
      interval_cases i <;> simp [List.getElem_append, List.getElem_take, List.getElem_drop]
  have hbz : bit r zero = false := BitVec.getLsbD_zero
  simp only [bankRoot, List.map_append, List.map_cons, List.map_nil, hbz, htake, hdrop, bit_gw0, bit_gw1, hupd]

theorem mainStep : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; have x2 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Gate) (x3 : ℕ) => x2.inputs[(0 : ℕ)]? = Option.some x3 ∨ x2.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x3 ∈ x2.inputs; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size = (13 : ℕ) → (∀ x6 ∈ x3.gates, ¬x2 x6 (4 : ℕ)) → (∃ (x7 : Fin x3.gates.length) (x8 : Fin x3.gates.length), x7 ≠ x8 ∧ (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (x3.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∀ (x9 : Fin x3.gates.length), x2 (x3.gates.get x9) (0 : ℕ) ↔ x9 = x7) ∧ ∀ (x9 : Fin x3.gates.length), x2 (x3.gates.get x9) (9 : ℕ) ↔ x9 = x8) → (∀ (x8 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn (Function.update x8 (4 : Fin (9 : ℕ)) Bool.false) ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)), x8 (4 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ))]) = x1 x8) → False := by
  intro x1 _ C legal hsz _ _ hcomp
  have goalEq : (execute C.gates bankRoot).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro m hm
    let r : Row := ⟨m, hm⟩
    change bit r ((execute C.gates bankRoot).getD C.output zero) = bit r graph
    rw [← b_read, execute_bits _ _ _ (fun g hg => (legal g hg).1), bankRoot_map r]
    exact (hcomp (sample r)).trans ((edge_list_eq (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute C.gates bankRoot) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  obtain ⟨k, t, S, hk, _, run, sub0⟩ := extractT C.gates bankRoot legal graph_proper targetIn
  have sub : ∀ v ∈ S, v ∈ liveRoot := by
    intro v hv
    have hm := sub0 v hv
    simp only [bankRoot, liveRoot, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hm ⊢
    rcases hm with ((h1 | rfl) | h2) | h3
    · exact Or.inl (Or.inl h1)
    · exact False.elim ((live_proper run zero hv).1 rfl)
    · exact Or.inl (Or.inr h2)
    · exact Or.inr h3
  have hreq : liveRoot.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
    have hiN : i < 10 := by rw [← liveRoot_len]; exact hi
    have hget : liveRoot[i]'hi = liveRoot.getD i zero := (List.getD_eq_getElem liveRoot zero hi).symm
    have hh := List.all_eq_true.mp witRoot_ok ⟨i, hiN⟩ (List.mem_finRange _)
    simp only [Bool.and_eq_true, bne_iff_ne] at hh
    have h2 := List.all_eq_true.mp hh.2
    have hmemS := raw_required run _ _ sub (witRoot i).1 (witRoot i).2 hh.1 (fun w hw hn => by
      have ha := h2 w hw
      have hne : (w == liveRoot.getD i zero) = false := beq_eq_false_iff_ne.mpr hn
      rw [hne] at ha; simp only [Bool.false_or] at ha; exact beq_iff_eq.mp ha)
    exact hget.symm ▸ hmemS
  have eqS : S = liveRoot.toFinset :=
    Finset.Subset.antisymm (fun v hv => List.mem_toFinset.mpr (sub v hv)) hreq
  exact noRoot k t (hk.trans hsz.le) (fun hlt => by omega) (eqS ▸ run)

end PEqualNP.Outside.L_meta_5316

theorem PEqualNP.Outside.L_meta_5316 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; have x2 : PEqualNP.CircuitLowerBounds.Gate → ℕ → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Gate) (x3 : ℕ) => x2.inputs[(0 : ℕ)]? = Option.some x3 ∨ x2.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not ∧ x3 ∈ x2.inputs; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → x3.size = (13 : ℕ) → (∀ x6 ∈ x3.gates, ¬x2 x6 (4 : ℕ)) → (∃ (x7 : Fin x3.gates.length) (x8 : Fin x3.gates.length), x7 ≠ x8 ∧ (x3.gates.get x7).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (x3.gates.get x8).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (∀ (x9 : Fin x3.gates.length), x2 (x3.gates.get x9) (0 : ℕ) ↔ x9 = x7) ∧ ∀ (x9 : Fin x3.gates.length), x2 (x3.gates.get x9) (9 : ℕ) ↔ x9 = x8) → (∀ (x8 : Fin (9 : ℕ) → Bool), x3.eval (List.ofFn (Function.update x8 (4 : Fin (9 : ℕ)) Bool.false) ++ [x8 (0 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)), x8 (4 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ))]) = x1 x8) → False :=
  PEqualNP.Outside.L_meta_5316.mainStep
